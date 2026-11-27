#!/usr/bin/env bash
# Renders the Kubernetes manifests and validates them. Uses kubeconform when
# it is on PATH (or KUBECONFORM names it), and otherwise only checks that
# kustomize renders. The example JSON configs are checked by
# `cargo test --features stream --test deploy_examples`.
set -euo pipefail

here=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
# kubeconform only reads files with a YAML extension.
rendered="$scratch/rendered.yaml"

kubectl kustomize "$here/kubernetes" > "$rendered"
echo "rendered $(grep -c '^kind:' "$rendered") resources"

kubeconform=${KUBECONFORM:-$(command -v kubeconform || true)}
if [[ -n "$kubeconform" ]]; then
    "$kubeconform" -strict -summary -kubernetes-version "${KUBERNETES_VERSION:-1.31.0}" "$rendered"
else
    echo "kubeconform not found; only the kustomize render was checked" >&2
fi

if [[ "${1:-}" != --kubernetes-only ]] && command -v systemd-analyze >/dev/null; then
    systemd-analyze verify "$here/logkeeper-consensus.service"
fi
