#!/usr/bin/env bash
set -euo pipefail
umask 077

fail() {
    echo "$*" >&2
    exit 1
}

mount_instance_store() {
    local destination=$1 devices device filesystem signatures stage_mount
    udevadm settle
    devices=$(lsblk --json --nodeps --paths --output NAME,TYPE,MODEL)
    device=$(jq -er '
        [.blockdevices[] | select(.type == "disk" and .model == "Amazon EC2 NVMe Instance Storage") | .name]
        | select(length == 1) | .[0]' <<< "$devices") ||
        fail "Expected exactly one EC2 NVMe instance-store disk"
    [[ $device =~ ^/dev/nvme[0-9]+n[0-9]+$ ]] || fail "Unexpected instance-store device: $device"

    mkdir -p "$destination"
    if ! findmnt --mountpoint "$destination" >/dev/null; then
        if findmnt --source "$device" >/dev/null; then
            fail "Instance store is mounted elsewhere: $device"
        fi
        [[ $(lsblk --noheadings --list --output TYPE "$device") == disk ]] ||
            fail "Instance store has a partition or dependent device: $device"
        filesystem=$(lsblk --noheadings --nodeps --output FSTYPE "$device")
        if [[ -z $filesystem ]]; then
            signatures=$(wipefs --noheadings --output TYPE "$device")
            [[ -z $signatures ]] || fail "Instance store has existing signatures: $device"
            mkfs.xfs -q -L logkeeper "$device"
        fi
        [[ $(blkid -p -s LABEL -o value "$device") == logkeeper ]] ||
            fail "Instance store is missing the logkeeper filesystem label: $device"
        mount -t xfs -o nodev,nosuid,noexec "$device" "$destination"
    fi
    stage_mount=$(findmnt --noheadings --output SOURCE,FSTYPE --mountpoint "$destination")
    [[ $stage_mount == "$device xfs" ]] || fail "Journal path is not the local XFS instance store"
}

mint_keeper_id() {
    cat /proc/sys/kernel/random/uuid
}

prepare_keeper() {
    local store=$1 runtime=$2 deployment=$3 ca=$4
    local state="$store/keeper" pending="$store/.pending" id host uri pki secret existing
    local certificate="$runtime/certificate.pem" key="$runtime/private-key.pem"

    host=$(jq -er '.host' "$deployment")
    pki=$(jq -ec '.pki' "$deployment")
    secret=$(jq -er '.key_secret' "$deployment")

    if [[ ! -e $state ]]; then
        # A pending directory has never served. Everything else must be accounted for.
        existing=$(find "$store" -mindepth 1 -maxdepth 1 ! -name .pending -print -quit)
        [[ -z $existing ]] ||
            fail "Instance store has data without a keeper identity"
        mkdir -p "$pending/data"
        id=$(mint_keeper_id)
        uri="urn:logkeeper:keeper:$id"
        openssl genpkey -algorithm RSA -pkeyopt rsa_keygen_bits:2048 -out "$key" 2>/dev/null
        pki_issue "$pki" "$runtime" "$key" "$id" "URI:$uri,DNS:$host" "$certificate"
        pki_verify "$certificate" "$key" "$ca" sslserver "$uri" -verify_hostname "$host"
        aws secretsmanager put-secret-value --secret-id "$secret" \
            --client-request-token "$id" --secret-string "file://$key" >/dev/null
        printf '%s\n' "$id" > "$pending/id"
        cp "$certificate" "$pending/certificate.pem"
        mv "$pending" "$state"
    else
        [[ -d $state/data ]] || fail "Keeper identity exists but the journal directory is missing"
        read -r id < "$state/id"
        [[ $id =~ ^[0-9a-f]{8}-[0-9a-f]{4}-4[0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}$ ]] ||
            fail "Invalid persisted keeper ID"
        uri="urn:logkeeper:keeper:$id"
        # An empty disk cannot select a secret version. Never look up AWSCURRENT.
        aws secretsmanager get-secret-value --secret-id "$secret" --version-id "$id" \
            --query SecretString --output text > "$key"
        pki_verify "$state/certificate.pem" "$key" "$ca" sslserver "$uri" -verify_hostname "$host" -no_check_time
        if ! openssl x509 -in "$state/certificate.pem" -noout -checkend 2592000 >/dev/null; then
            pki_issue "$pki" "$runtime" "$key" "$id" "URI:$uri,DNS:$host" "$certificate"
            pki_verify "$certificate" "$key" "$ca" sslserver "$uri" -verify_hostname "$host"
            cp "$certificate" "$state/certificate.pem.new"
            mv -f "$state/certificate.pem.new" "$state/certificate.pem"
        fi
        cp "$state/certificate.pem" "$certificate"
    fi

    # Make the identity and its association with the journal durable before serving.
    sync -f "$store"
    cp "$ca" "$runtime/ca.pem"
    jq --arg keeper "$id" '{
        keeper: $keeper, listen, data: "/var/lib/logkeeper", zone,
        tls: {certificate: "/etc/logkeeper/certificate.pem", private_key: "/etc/logkeeper/private-key.pem", ca: "/etc/logkeeper/ca.pem"},
        clients, writers, limits
    }' "$deployment" > "$runtime/keeper.json"
    echo "Keeper $id for $host"
}

start_keeper() {
    local store=/mnt/logkeeper runtime=/run/logkeeper deployment=/etc/logkeeper/deployment.json
    local region registry parameter image auth
    # shellcheck source=deploy/terraform/logkeeper-cluster/pki.sh
    source /usr/local/lib/logkeeper/pki.sh

    region=$(jq -er '.region' "$deployment")
    export AWS_REGION="$region" AWS_DEFAULT_REGION="$region" AWS_PAGER=""
    registry=$(jq -er '.registry' "$deployment")
    parameter=$(jq -er '.image_parameter' "$deployment")
    image=$(aws ssm get-parameter --name "$parameter" --query Parameter.Value --output text)
    [[ ${image%%/*} == "$registry" && $image =~ @sha256:[0-9a-f]{64}$ ]] ||
        fail "Expected a digest-pinned image from $registry"

    if ! docker image inspect "$image" >/dev/null 2>&1; then
        auth=$(mktemp -d "$runtime/docker.XXXXXX")
        aws ecr get-login-password | docker --config "$auth" login --username AWS --password-stdin "$registry"
        docker --config "$auth" pull "$image"
        rm -rf "$auth"
    fi

    mount_instance_store "$store"
    prepare_keeper "$store" "$runtime" "$deployment" /etc/logkeeper/ca.pem
    chown 10001:10001 "$store/keeper/data"
    chgrp 10001 "$runtime" "$runtime/"{certificate.pem,private-key.pem,ca.pem,keeper.json}
    chmod 0750 "$runtime"
    chmod 0440 "$runtime/"{certificate.pem,private-key.pem,ca.pem,keeper.json}

    exec docker run --rm --name logkeeper --pull never --read-only --cap-drop ALL \
        --security-opt no-new-privileges --publish 5448:5448 \
        --mount "type=bind,source=$store/keeper/data,target=/var/lib/logkeeper" \
        --mount "type=bind,source=$runtime,target=/etc/logkeeper,readonly" "$image"
}

if [[ ${BASH_SOURCE[0]} == "$0" ]]; then
    start_keeper
fi
