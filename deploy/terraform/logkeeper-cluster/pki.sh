#!/usr/bin/env bash

pki_issue() {
    local pki=$1 work=$2 key=$3 subject=$4 san=$5 certificate=$6 arn

    openssl req -new -key "$key" -subj "/CN=$subject" \
        -addext "subjectAltName=$san" -out "$work/request.pem"
    arn=$(aws acm-pca issue-certificate \
        --certificate-authority-arn "$(jq -er '.ca_arn' <<< "$pki")" \
        --signing-algorithm "$(jq -er '.signing_algorithm' <<< "$pki")" \
        --template-arn "$(jq -er '.template_arn' <<< "$pki")" \
        --validity Value=90,Type=DAYS --csr "fileb://$work/request.pem" \
        --query CertificateArn --output text)
    aws acm-pca wait certificate-issued \
        --certificate-authority-arn "$(jq -er '.ca_arn' <<< "$pki")" --certificate-arn "$arn"
    aws acm-pca get-certificate \
        --certificate-authority-arn "$(jq -er '.ca_arn' <<< "$pki")" --certificate-arn "$arn" \
        --output json | jq -er '.Certificate, (.CertificateChain // empty)' > "$certificate"
}

pki_verify() {
    local certificate=$1 key=$2 ca=$3 purpose=$4 uri=$5 public_key certificate_key sans
    shift 5

    openssl verify -CAfile "$ca" -untrusted "$certificate" -purpose "$purpose" "$@" "$certificate" >/dev/null
    public_key=$(openssl pkey -in "$key" -pubout)
    certificate_key=$(openssl x509 -in "$certificate" -noout -pubkey)
    [[ $public_key == "$certificate_key" ]] || {
        echo "Certificate does not match its private key" >&2
        return 1
    }
    sans=$(openssl x509 -in "$certificate" -noout -ext subjectAltName)
    tr ',' '\n' <<< "$sans" | sed 's/^[[:space:]]*//' | grep -Fx "URI:$uri" >/dev/null || {
        echo "Certificate is missing URI SAN $uri" >&2
        return 1
    }
}
