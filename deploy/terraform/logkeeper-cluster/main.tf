data "aws_partition" "current" {}
data "aws_region" "current" {}
data "aws_caller_identity" "current" {}

data "aws_ec2_instance_type" "keeper" {
  instance_type = var.instance_type
}

data "aws_subnet" "keeper" {
  for_each = local.slots
  id       = each.value.subnet_id
}

locals {
  slots = {
    for index, subnet_id in var.private_subnet_ids : tostring(index + 1) => {
      subnet_id = subnet_id
      host      = "keeper-${index + 1}.${var.dns_zone_name}"
      digest    = var.image_digests[index]
    }
  }
  port         = 5448
  client_uris  = [for name in sort(tolist(var.client_names)) : "urn:logkeeper:client:${name}"]
  writer_uris  = [for name in sort(tolist(var.writer_names)) : "urn:logkeeper:client:${name}"]
  partition    = data.aws_partition.current.partition
  region       = data.aws_region.current.region
  account      = data.aws_caller_identity.current.account_id
  registry     = "${local.account}.dkr.ecr.${local.region}.${data.aws_partition.current.dns_suffix}"
  repository   = "${local.registry}/${var.image_repository_name}"
  registry_arn = "arn:${local.partition}:ecr:${local.region}:${local.account}:repository/${var.image_repository_name}"
}

resource "aws_security_group" "keeper" {
  name        = "${var.name}-keepers"
  description = "Logkeeper mTLS"
  vpc_id      = var.vpc_id

  lifecycle {
    precondition {
      condition = alltrue([
        for subnet in data.aws_subnet.keeper : subnet.vpc_id == var.vpc_id && !subnet.map_public_ip_on_launch
      ])
      error_message = "Every keeper subnet must be private and in the supplied VPC."
    }
    precondition {
      condition     = length(distinct([for subnet in data.aws_subnet.keeper : subnet.availability_zone_id])) == 3
      error_message = "Keepers must occupy three distinct availability zones."
    }
  }
}

resource "aws_vpc_security_group_ingress_rule" "client" {
  for_each                     = var.client_security_group_ids
  security_group_id            = aws_security_group.keeper.id
  referenced_security_group_id = each.key
  ip_protocol                  = "tcp"
  from_port                    = local.port
  to_port                      = local.port
}

resource "aws_vpc_security_group_egress_rule" "https" {
  security_group_id = aws_security_group.keeper.id
  cidr_ipv4         = "0.0.0.0/0"
  ip_protocol       = "tcp"
  from_port         = 443
  to_port           = 443
}

resource "aws_ssm_parameter" "image" {
  for_each = local.slots
  name     = "/logkeeper/${var.name}/keeper-${each.key}/image"
  type     = "String"
  value    = "${local.repository}@${each.value.digest}"
}

resource "aws_instance" "keeper" {
  for_each                    = local.slots
  ami                         = var.ami_id
  instance_type               = var.instance_type
  subnet_id                   = each.value.subnet_id
  vpc_security_group_ids      = [aws_security_group.keeper.id]
  associate_public_ip_address = false
  iam_instance_profile        = aws_iam_instance_profile.keeper[each.key].name
  user_data_replace_on_change = true

  metadata_options {
    http_tokens                 = "required"
    http_put_response_hop_limit = 1
  }

  root_block_device {
    encrypted = true
  }

  # Cloud-init files contain deployment data and public trust material.
  user_data_base64 = base64gzip("#cloud-config\n${yamlencode({
    packages = ["awscli2", "docker", "jq", "openssl", "xfsprogs"]
    write_files = [
      { path = "/etc/logkeeper/ca.pem", permissions = "0644", content = var.pki.ca_certificate },
      { path = "/etc/logkeeper/deployment.json", permissions = "0600", content = jsonencode({
        region          = local.region
        host            = each.value.host
        zone            = data.aws_subnet.keeper[each.key].availability_zone
        registry        = local.registry
        image_parameter = aws_ssm_parameter.image[each.key].name
        key_secret      = aws_secretsmanager_secret.keeper[each.key].arn
        pki             = local.keeper_pki
        listen          = "0.0.0.0:${local.port}"
        clients         = local.client_uris
        writers         = local.writer_uris
        limits          = var.limits
      }) },
      { path = "/usr/local/lib/logkeeper/pki.sh", permissions = "0644", content = file("${path.module}/pki.sh") },
      { path = "/usr/local/sbin/logkeeper-keeper", permissions = "0755", content = file("${path.module}/keeper.sh") },
      { path = "/etc/systemd/system/logkeeper.service", permissions = "0644", content = file("${path.module}/logkeeper.service") },
    ]
    runcmd = [
      ["systemctl", "daemon-reload"],
      ["systemctl", "enable", "--now", "logkeeper.service"],
    ]
  })}")

  tags = { Name = "${var.name}-keeper-${each.key}" }

  depends_on = [
    aws_iam_role_policy.keeper,
    aws_secretsmanager_secret_policy.keeper,
    aws_vpc_security_group_egress_rule.https,
  ]

  lifecycle {
    precondition {
      condition = (
        contains(data.aws_ec2_instance_type.keeper.supported_architectures, "x86_64") &&
        data.aws_ec2_instance_type.keeper.hypervisor == "nitro" &&
        try(one(data.aws_ec2_instance_type.keeper.instance_disks).count == 1 && one(data.aws_ec2_instance_type.keeper.instance_disks).type == "ssd", false)
      )
      error_message = "Keepers require x86_64 Nitro instances with a single local NVMe SSD."
    }
  }
}

resource "aws_route53_zone" "keeper" {
  name = var.dns_zone_name

  vpc {
    vpc_id = var.vpc_id
  }
}

resource "aws_route53_record" "keeper" {
  for_each = local.slots
  zone_id  = aws_route53_zone.keeper.zone_id
  name     = each.value.host
  type     = "A"
  ttl      = 30
  records  = [aws_instance.keeper[each.key].private_ip]
}
