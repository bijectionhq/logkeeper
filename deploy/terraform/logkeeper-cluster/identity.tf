locals {
  credential_names = setunion(var.client_names, var.writer_names)
  keeper_pki = {
    ca_arn            = var.pki.ca_arn
    signing_algorithm = var.pki.signing_algorithm
    template_arn      = "arn:${local.partition}:acm-pca:::template/EndEntityServerAuthCertificate/V1"
  }
  client_pki = merge(local.keeper_pki, {
    template_arn = "arn:${local.partition}:acm-pca:::template/EndEntityClientAuthCertificate/V1"
  })
}

resource "aws_iam_role" "keeper" {
  for_each = local.slots
  name     = "${var.name}-keeper-${each.key}"
  assume_role_policy = jsonencode({
    Version = "2012-10-17"
    Statement = [{
      Effect    = "Allow"
      Action    = "sts:AssumeRole"
      Principal = { Service = "ec2.amazonaws.com" }
    }]
  })
}

resource "aws_iam_instance_profile" "keeper" {
  for_each = local.slots
  name     = aws_iam_role.keeper[each.key].name
  role     = aws_iam_role.keeper[each.key].name
}

resource "aws_iam_role_policy" "keeper" {
  for_each = local.slots
  name     = "logkeeper"
  role     = aws_iam_role.keeper[each.key].name
  policy = jsonencode({
    Version = "2012-10-17"
    Statement = [
      {
        Effect    = "Allow"
        Action    = "acm-pca:IssueCertificate"
        Resource  = var.pki.ca_arn
        Condition = { StringEquals = { "acm-pca:TemplateArn" = local.keeper_pki.template_arn } }
      },
      {
        Effect   = "Allow"
        Action   = "acm-pca:GetCertificate"
        Resource = var.pki.ca_arn
      },
      {
        Effect   = "Allow"
        Action   = ["secretsmanager:GetSecretValue", "secretsmanager:PutSecretValue"]
        Resource = aws_secretsmanager_secret.keeper[each.key].arn
      },
      {
        Effect   = "Allow"
        Action   = "ssm:GetParameter"
        Resource = aws_ssm_parameter.image[each.key].arn
      },
      {
        Effect = "Allow"
        Action = [
          "ssm:UpdateInstanceInformation",
          "ssmmessages:CreateControlChannel", "ssmmessages:CreateDataChannel",
          "ssmmessages:OpenControlChannel", "ssmmessages:OpenDataChannel",
        ]
        Resource = "*"
      },
      {
        Effect   = "Allow"
        Action   = "ecr:GetAuthorizationToken"
        Resource = "*"
      },
      {
        Effect = "Allow"
        Action = [
          "ecr:BatchCheckLayerAvailability", "ecr:BatchGetImage", "ecr:GetDownloadUrlForLayer",
        ]
        Resource = local.registry_arn
      },
    ]
  })
}

# Secret values are written by the keeper and client issuer at runtime.
resource "aws_secretsmanager_secret" "keeper" {
  for_each = local.slots
  name     = "logkeeper/${var.name}/keeper-${each.key}/key"
}

resource "aws_secretsmanager_secret" "client" {
  for_each = local.credential_names
  name     = "logkeeper/${var.name}/clients/${each.key}/key"
}

resource "aws_secretsmanager_secret_policy" "keeper" {
  for_each            = local.slots
  secret_arn          = aws_secretsmanager_secret.keeper[each.key].arn
  block_public_policy = true
  policy = jsonencode({
    Version = "2012-10-17"
    Statement = [{
      Effect    = "Deny"
      Principal = "*"
      Action    = ["secretsmanager:GetSecretValue", "secretsmanager:PutSecretValue"]
      Resource  = "*"
      Condition = { ArnNotEquals = { "aws:PrincipalArn" = aws_iam_role.keeper[each.key].arn } }
    }]
  })
}

resource "aws_secretsmanager_secret_policy" "client" {
  for_each            = local.credential_names
  secret_arn          = aws_secretsmanager_secret.client[each.key].arn
  block_public_policy = true
  policy = jsonencode({
    Version = "2012-10-17"
    Statement = [{
      Effect    = "Deny"
      Principal = "*"
      Action    = "secretsmanager:GetSecretValue"
      Resource  = "*"
      Condition = { ArnNotEquals = { "aws:PrincipalArn" = [for role in aws_iam_role.keeper : role.arn] } }
    }]
  })
}

resource "aws_iam_policy" "client_issuer" {
  name = "${var.name}-client-issuer"

  lifecycle {
    precondition {
      condition     = length(local.credential_names) > 0
      error_message = "Supply at least one client or writer identity for the issuer."
    }
  }
  policy = jsonencode({
    Version = "2012-10-17"
    Statement = [
      {
        Effect    = "Allow"
        Action    = "acm-pca:IssueCertificate"
        Resource  = var.pki.ca_arn
        Condition = { StringEquals = { "acm-pca:TemplateArn" = local.client_pki.template_arn } }
      },
      {
        Effect   = "Allow"
        Action   = "acm-pca:GetCertificate"
        Resource = var.pki.ca_arn
      },
      {
        Effect   = "Allow"
        Action   = "secretsmanager:PutSecretValue"
        Resource = [for secret in aws_secretsmanager_secret.client : secret.arn]
      },
    ]
  })
}
