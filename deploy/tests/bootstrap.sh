#!/usr/bin/env bash
set -euo pipefail

root=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)
mkdir -p "$root/target"
fixture=$(mktemp -d "$root/target/n5-bootstrap.XXXXXX")
trap 'rm -rf -- "$fixture"' EXIT
export fixture
module="$root/deploy/terraform/logkeeper-cluster"

argument() {
    local option=$1
    shift
    while [[ $# -gt 1 ]]; do
        if [[ $1 == "$option" ]]; then
            printf '%s\n' "$2"
            return
        fi
        shift
    done
    return 1
}

# This signer uses a temporary CA and mimics the template's CSR SAN and EKU behavior.
mock_aws() {
    local template csr purpose secret version key
    case "$1/$2" in
        acm-pca/issue-certificate)
            template=$(argument --template-arn "$@")
            csr=$(argument --csr "$@")
            case "$template" in
                fixture-server) purpose=serverAuth ;;
                fixture-client) purpose=clientAuth ;;
                *) return 1 ;;
            esac
            purpose=${wrong_purpose:-$purpose}
            printf '[leaf]\nbasicConstraints=CA:FALSE\nextendedKeyUsage=%s\n' "$purpose" > "$fixture/leaf.cnf"
            if [[ -n ${wrong_san:-} ]]; then
                printf 'subjectAltName=URI:urn:logkeeper:client:wrong\n' >> "$fixture/leaf.cnf"
            fi
            openssl x509 -req -in "${csr#fileb://}" -CA "$fixture/ca.pem" -CAkey "$fixture/ca.key" \
                -set_serial 1 -days 90 -copy_extensions copy -extfile "$fixture/leaf.cnf" \
                -extensions leaf -out "$fixture/leaf.pem" 2>/dev/null
            printf 'fixture-certificate\n'
            ;;
        acm-pca/wait) ;;
        acm-pca/get-certificate) jq -n --rawfile leaf "$fixture/leaf.pem" '{Certificate: $leaf}' ;;
        secretsmanager/put-secret-value)
            secret=$(argument --secret-id "$@")
            version=$(argument --client-request-token "$@" || printf 'issued')
            key=$(argument --secret-string "$@")
            [[ ! -e "$fixture/$secret.$version" ]] || return 1
            cp "${key#file://}" "$fixture/$secret.$version"
            ;;
        secretsmanager/get-secret-value)
            secret=$(argument --secret-id "$@")
            version=$(argument --version-id "$@")
            echo "$version" >> "$fixture/lookups"
            cat "${wrong_key:-$fixture/$secret.$version}"
            ;;
        *) printf 'Unexpected mock AWS command %s %s\n' "$1" "$2" >&2; return 1 ;;
    esac
}

mkdir "$fixture/bin" "$fixture/first" "$fixture/replacement" "$fixture/runtime"
{
    printf '#!/usr/bin/env bash\nset -euo pipefail\n'
    declare -f argument mock_aws
    printf 'mock_aws "$@"\n'
} > "$fixture/bin/aws"
chmod +x "$fixture/bin/aws"
export PATH="$fixture/bin:$PATH"

openssl req -new -x509 -newkey rsa:2048 -nodes -days 120 -subj '/CN=Local test CA' \
    -addext 'basicConstraints=critical,CA:TRUE' -keyout "$fixture/ca.key" -out "$fixture/ca.pem" 2>/dev/null
cat > "$fixture/deployment.json" <<'JSON'
{
  "host": "keeper-1.fixture.internal",
  "key_secret": "keeper-key",
  "pki": {"ca_arn": "fixture-ca", "template_arn": "fixture-server", "signing_algorithm": "SHA256WITHRSA"},
  "listen": "0.0.0.0:5448",
  "zone": "eu-north-1a",
  "clients": ["urn:logkeeper:client:rtdb"],
  "writers": ["urn:logkeeper:client:ingestor"],
  "limits": {"stream_quota_bytes": 8589934592, "max_record_bytes": 33554432, "round_bytes_per_stream": 4194304, "round_requests": 64}
}
JSON

boot() {
    bash -c '
        source "$1/keeper.sh"
        source "$1/pki.sh"
        mint_keeper_id() { printf "%s\n" "$test_id"; }
        sync() { [[ $1 == -f && $2 == "$store" ]]; }
        store=$2 test_id=$3
        prepare_keeper "$store" "$fixture/runtime" "$fixture/deployment.json" "$fixture/ca.pem"
    ' bash "$module" "$1" "$2"
}

expect_failure() {
    local check=$1
    shift
    if "$@" >"$fixture/last.log" 2>&1; then
        echo "Expected failure at $check" >&2
        return 1
    fi
    if ! grep -qF "$check" "$fixture/last.log"; then
        cat "$fixture/last.log" >&2
        return 1
    fi
    printf 'Control rejected at %s\n' "$check"
}

assert_replacement() {
    local id
    id=$(jq -er '.keeper' "$fixture/runtime/keeper.json")
    if [[ $id == "$1" ]]; then
        echo "Blank disk reused the retired keeper ID" >&2
        return 1
    fi
}

first=00000000-0000-4000-8000-000000000001
replacement=00000000-0000-4000-8000-000000000002
boot "$fixture/first" "$first"
printf 'journal witness\n' > "$fixture/first/keeper/data/record"
boot "$fixture/first" "$replacement"
[[ $(jq -er '.keeper' "$fixture/runtime/keeper.json") == "$first" ]]
[[ $(cat "$fixture/first/keeper/data/record") == "journal witness" ]]
[[ $(cat "$fixture/lookups") == "$first" ]]
echo "Retained disk reused its identity, selected its exact secret version and retained its journal"

# The old config is the negative control for the blank-disk check.
expect_failure "Blank disk reused the retired keeper ID" assert_replacement "$first"
boot "$fixture/replacement" "$replacement"
assert_replacement "$first"
[[ $(jq -er '.keeper' "$fixture/runtime/keeper.json") == "$replacement" ]]
[[ $(cat "$fixture/lookups") == "$first" ]]
[[ -f "$fixture/keeper-key.$first" && -f "$fixture/keeper-key.$replacement" ]]
echo "Blank disk minted a different identity with the previous key still present"

jq -e --arg keeper "$replacement" --slurpfile host "$fixture/deployment.json" '. == {
    keeper: $keeper, listen: $host[0].listen, data: "/var/lib/logkeeper", zone: $host[0].zone,
    tls: {
        certificate: "/etc/logkeeper/certificate.pem",
        private_key: "/etc/logkeeper/private-key.pem",
        ca: "/etc/logkeeper/ca.pem"
    },
    clients: $host[0].clients, writers: $host[0].writers, limits: $host[0].limits
}' "$fixture/runtime/keeper.json" >/dev/null
echo "Keeper JSON exactly matches the deployment format"

wrong_key="$fixture/keeper-key.$replacement" \
    expect_failure "Certificate does not match its private key" boot "$fixture/first" "$first"
mv "$fixture/replacement/keeper/data" "$fixture/replacement/unbound"
expect_failure "Keeper identity exists but the journal directory is missing" boot "$fixture/replacement" "$replacement"
mv "$fixture/replacement/keeper" "$fixture/disconnected"
expect_failure "Instance store has data without a keeper identity" boot "$fixture/replacement" "$replacement"

probe_mount() {
    local devices
    devices=$(jq -cn --arg model "$1" --argjson extra "${5:-0}" '
        [{name: "/dev/nvme0n1", type: "disk", model: "Amazon Elastic Block Store"}]
        + [range(1; 2 + $extra) | {name: "/dev/nvme\(.)n1", type: "disk", model: $model}]
        | {blockdevices: .}')
    bash -c '
        source "$1/keeper.sh"
        udevadm() { :; }
        test_devices=$2 test_device=$3 test_mounted=$4 test_signature=$5
        findmnt() {
            case "$1" in
                --source) return 1 ;;
                --mountpoint) [[ $test_mounted == yes ]] ;;
                --noheadings) printf "%s xfs\n" "$test_device" ;;
            esac
        }
        lsblk() {
            case "$1" in
                --json) printf "%s\n" "$test_devices" ;;
                --noheadings)
                    [[ $4 != TYPE ]] || printf "disk\n"
                    ;;
            esac
        }
        wipefs() { printf "%s\n" "$test_signature"; }
        mkfs.xfs() {
            [[ $* == "-q -L logkeeper /dev/nvme1n1" ]] || return 1
            touch "$fixture/formatted"
        }
        blkid() { printf "logkeeper\n"; }
        mount() {
            [[ $* == "-t xfs -o nodev,nosuid,noexec /dev/nvme1n1 $fixture/mount" ]] || return 1
            test_mounted=yes
        }
        mount_instance_store "$fixture/mount"
    ' bash "$module" "$devices" "$2" "${3:-yes}" "${4:-}"
}

probe_mount "Amazon EC2 NVMe Instance Storage" /dev/nvme1n1
echo "Mounted local NVMe is accepted alongside an EBS root disk"
expect_failure "Expected exactly one EC2 NVMe instance-store disk" probe_mount "Amazon Elastic Block Store" /dev/nvme0n1
expect_failure "Expected exactly one EC2 NVMe instance-store disk" probe_mount "Amazon EC2 NVMe Instance Storage" /dev/nvme1n1 yes '' 1
expect_failure "Journal path is not the local XFS instance store" probe_mount "Amazon EC2 NVMe Instance Storage" /dev/nvme0n1
probe_mount "Amazon EC2 NVMe Instance Storage" /dev/nvme1n1 no
[[ -f "$fixture/formatted" ]]
echo "A blank local NVMe disk is formatted and mounted"
rm "$fixture/formatted"
expect_failure "Instance store has existing signatures" probe_mount "Amazon EC2 NVMe Instance Storage" /dev/nvme1n1 no gpt
[[ ! -e "$fixture/formatted" ]]

jq -n --rawfile ca "$fixture/ca.pem" '{
    ca_arn: "fixture-ca", signing_algorithm: "SHA256WITHRSA", template_arn: "fixture-client",
    region: "fixture-region", ca_certificate: $ca, key_secrets: {rtdb: "client-key"}
}' > "$fixture/issuance.json"
"$root/deploy/issue-client.sh" "$fixture/issuance.json" rtdb "$fixture/client"
cmp "$fixture/client/private-key.pem" "$fixture/client-key.issued"
echo "Client issuance delivered the matching signed key and escrowed a copy"
expect_failure "client is not allowed" "$root/deploy/issue-client.sh" "$fixture/issuance.json" unlisted "$fixture/unlisted"
wrong_san=1 expect_failure "Certificate is missing URI SAN urn:logkeeper:client:rtdb" \
    "$root/deploy/issue-client.sh" "$fixture/issuance.json" rtdb "$fixture/wrong-san"
wrong_purpose=serverAuth expect_failure "unsuitable certificate purpose" \
    "$root/deploy/issue-client.sh" "$fixture/issuance.json" rtdb "$fixture/wrong-purpose"
