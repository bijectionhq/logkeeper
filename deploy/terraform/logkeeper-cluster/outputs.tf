output "journal_url" {
  description = "Journal URL passed unchanged to consumers."
  value       = "logkeeper+tls://${join(",", [for slot in local.slots : "${slot.host}:${local.port}"])}"
}

output "ca_certificate" {
  description = "PEM trust bundle for client credentials."
  value       = var.pki.ca_certificate
}

output "client_issuance" {
  description = "Operator input for deploy/issue-client.sh. Attach issuer_policy_arn to the trusted issuer."
  value = merge(local.client_pki, {
    region            = local.region
    ca_certificate    = var.pki.ca_certificate
    issuer_policy_arn = aws_iam_policy.client_issuer.arn
    key_secrets       = { for name, secret in aws_secretsmanager_secret.client : name => secret.arn }
  })
}
