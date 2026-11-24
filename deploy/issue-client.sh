#!/usr/bin/env bash
set -euo pipefail
umask 077

# shellcheck source=deploy/terraform/logkeeper-cluster/pki.sh
source "$(dirname "${BASH_SOURCE[0]}")/terraform/logkeeper-cluster/pki.sh"

if [[ $# != 3 || ! $2 =~ ^[A-Za-z0-9][A-Za-z0-9_.-]{0,62}$ ]]; then
    echo "Usage: $0 ISSUANCE_JSON CLIENT_NAME NEW_OUTPUT_DIRECTORY" >&2
    exit 2
fi

issuance=$(cat -- "$1")
name=$2
destination=$3
uri="urn:logkeeper:client:$name"
secret=$(jq -er --arg name "$name" '.key_secrets[$name] // error("client is not allowed")' <<< "$issuance")
region=$(jq -er '.region' <<< "$issuance")
export AWS_REGION="$region" AWS_DEFAULT_REGION="$region" AWS_PAGER=""

mkdir -- "$destination"
trap 'rm -rf -- "$destination"' EXIT
key="$destination/private-key.pem"
certificate="$destination/certificate.pem"
ca="$destination/ca.pem"
jq -er '.ca_certificate' <<< "$issuance" > "$ca"
openssl genpkey -algorithm RSA -pkeyopt rsa_keygen_bits:2048 -out "$key" 2>/dev/null
pki_issue "$issuance" "$destination" "$key" "$name" "URI:$uri" "$certificate"
pki_verify "$certificate" "$key" "$ca" sslclient "$uri"
aws secretsmanager put-secret-value --secret-id "$secret" --secret-string "file://$key" >/dev/null
rm -- "$destination/request.pem"
trap - EXIT
printf 'Issued %s in %s\n' "$uri" "$destination"
