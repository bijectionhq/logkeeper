mock_provider "aws" {
  override_during = plan

  mock_data "aws_partition" {
    defaults = { partition = "aws", dns_suffix = "amazonaws.com" }
  }
  mock_data "aws_region" {
    defaults = { region = "eu-north-1" }
  }
  mock_data "aws_caller_identity" {
    defaults = { account_id = "123456789012" }
  }
  mock_data "aws_ec2_instance_type" {
    defaults = {
      supported_architectures = ["arm64"]
      hypervisor              = "nitro"
      instance_disks          = [{ count = 1, size = 468, type = "ssd" }]
    }
  }
  mock_data "aws_ami" {
    defaults = { architecture = "arm64" }
  }
  mock_data "aws_subnet" {
    defaults = { vpc_id = "vpc-fixture", map_public_ip_on_launch = false }
  }
}

variables {
  name                      = "fixture"
  vpc_id                    = "vpc-fixture"
  private_subnet_ids        = ["subnet-a", "subnet-b", "subnet-c"]
  client_security_group_ids = ["sg-fixture"]
  ami_id                    = "ami-0123456789abcdef0"
  dns_zone_name             = "fixture.internal"
  image_repository_name     = "logkeeper"
  image_digests             = [for i in range(3) : "sha256:${sha256(tostring(i))}"]
  client_names              = ["rtdb"]
  writer_names              = ["ingestor"]
  pki = {
    ca_arn            = "arn:aws:acm-pca:eu-north-1:123456789012:certificate-authority/b13da2b8-a89d-4637-8e3d-395479203d17"
    signing_algorithm = "SHA256WITHRSA"
    ca_certificate    = "public trust bundle fixture"
  }
}

override_data {
  target = data.aws_subnet.keeper["1"]
  values = {
    availability_zone       = "eu-north-1a"
    availability_zone_id    = "eun1-az1"
    vpc_id                  = "vpc-fixture"
    map_public_ip_on_launch = false
  }
}

override_data {
  target = data.aws_subnet.keeper["2"]
  values = {
    availability_zone       = "eu-north-1b"
    availability_zone_id    = "eun1-az2"
    vpc_id                  = "vpc-fixture"
    map_public_ip_on_launch = false
  }
}

override_data {
  target = data.aws_subnet.keeper["3"]
  values = {
    availability_zone       = "eu-north-1c"
    availability_zone_id    = "eun1-az3"
    vpc_id                  = "vpc-fixture"
    map_public_ip_on_launch = false
  }
}

run "three_private_endpoints" {
  command = plan

  override_resource {
    target          = aws_instance.keeper["1"]
    override_during = plan
    values          = { private_ip = "10.0.1.10" }
  }

  override_resource {
    target          = aws_iam_role.keeper["1"]
    override_during = plan
    values          = { arn = "arn:aws:iam::123456789012:role/fixture-keeper-1" }
  }

  override_resource {
    target          = aws_instance.keeper["2"]
    override_during = plan
    values          = { private_ip = "10.0.2.10" }
  }

  override_resource {
    target          = aws_iam_role.keeper["2"]
    override_during = plan
    values          = { arn = "arn:aws:iam::123456789012:role/fixture-keeper-2" }
  }

  override_resource {
    target          = aws_instance.keeper["3"]
    override_during = plan
    values          = { private_ip = "10.0.3.10" }
  }

  override_resource {
    target          = aws_iam_role.keeper["3"]
    override_during = plan
    values          = { arn = "arn:aws:iam::123456789012:role/fixture-keeper-3" }
  }

  override_resource {
    target          = aws_secretsmanager_secret.client["ingestor"]
    override_during = plan
    values          = { arn = "arn:aws:secretsmanager:eu-north-1:123456789012:secret:fixture-client-ingestor-asdfgh" }
  }

  override_resource {
    target          = aws_secretsmanager_secret.client["rtdb"]
    override_during = plan
    values          = { arn = "arn:aws:secretsmanager:eu-north-1:123456789012:secret:fixture-client-rtdb-asdfgh" }
  }

  assert {
    condition     = alltrue([for keeper in aws_instance.keeper : keeper.instance_type == "i8g.large"])
    error_message = "Every keeper must default to i8g.large Graviton."
  }

  assert {
    condition     = output.journal_url == "logkeeper+tls://keeper-1.fixture.internal:5448,keeper-2.fixture.internal:5448,keeper-3.fixture.internal:5448"
    error_message = "The journal URL must list the three stable endpoints in subnet order."
  }

  assert {
    condition = alltrue([
      !aws_instance.keeper["1"].associate_public_ip_address,
      !aws_instance.keeper["2"].associate_public_ip_address,
      !aws_instance.keeper["3"].associate_public_ip_address,
      [aws_instance.keeper["1"].subnet_id, aws_instance.keeper["2"].subnet_id, aws_instance.keeper["3"].subnet_id] == var.private_subnet_ids,
      aws_route53_record.keeper["1"].records == toset([aws_instance.keeper["1"].private_ip]),
      aws_route53_record.keeper["2"].records == toset([aws_instance.keeper["2"].private_ip]),
      aws_route53_record.keeper["3"].records == toset([aws_instance.keeper["3"].private_ip]),
    ])
    error_message = "Each DNS record must address exactly its own private keeper."
  }

  assert {
    condition = alltrue([
      endswith(aws_ssm_parameter.image["1"].value, "@${var.image_digests[0]}"),
      endswith(aws_ssm_parameter.image["2"].value, "@${var.image_digests[1]}"),
      endswith(aws_ssm_parameter.image["3"].value, "@${var.image_digests[2]}"),
    ])
    error_message = "Each keeper must use its own staged image digest."
  }

  assert {
    condition = alltrue([
      for slot in [
        { policy = aws_secretsmanager_secret_policy.keeper["1"].policy, arn = aws_iam_role.keeper["1"].arn },
        { policy = aws_secretsmanager_secret_policy.keeper["2"].policy, arn = aws_iam_role.keeper["2"].arn },
        { policy = aws_secretsmanager_secret_policy.keeper["3"].policy, arn = aws_iam_role.keeper["3"].arn },
      ] :
      jsondecode(slot.policy).Statement[0].Effect == "Deny" &&
      contains(jsondecode(slot.policy).Statement[0].Action, "secretsmanager:GetSecretValue") &&
      jsondecode(slot.policy).Statement[0].Condition.ArnNotEquals["aws:PrincipalArn"] == slot.arn
    ])
    error_message = "A keeper secret's read exception must be restricted to its own slot role."
  }

  assert {
    condition = (
      local.client_uris == ["urn:logkeeper:client:rtdb"] &&
      local.writer_uris == ["urn:logkeeper:client:ingestor"] &&
      toset(keys(output.client_issuance.key_secrets)) == toset(["rtdb", "ingestor"])
    )
    error_message = "Readers and writers must keep distinct allowlists while both can receive credentials."
  }

  assert {
    condition = (
      output.ca_certificate == var.pki.ca_certificate &&
      output.client_issuance.key_secrets["rtdb"] == aws_secretsmanager_secret.client["rtdb"].arn &&
      endswith(output.client_issuance.template_arn, "/EndEntityClientAuthCertificate/V1") &&
      endswith(local.keeper_pki.template_arn, "/EndEntityServerAuthCertificate/V1") &&
      jsondecode(aws_secretsmanager_secret_policy.client["rtdb"].policy).Statement[0].Effect == "Deny" &&
      jsondecode(aws_secretsmanager_secret_policy.client["rtdb"].policy).Statement[0].Action == "secretsmanager:GetSecretValue" &&
      toset(jsondecode(aws_secretsmanager_secret_policy.client["rtdb"].policy).Statement[0].Condition.ArnNotEquals["aws:PrincipalArn"]) == toset([aws_iam_role.keeper["1"].arn, aws_iam_role.keeper["2"].arn, aws_iam_role.keeper["3"].arn]) &&
      !strcontains(aws_iam_policy.client_issuer.policy, "secretsmanager:GetSecretValue")
    )
    error_message = "Client issuance must use the client TLS template and handoff, with secret reads restricted to keeper roles."
  }
}

run "x86_64_override_is_accepted" {
  command = plan

  variables {
    instance_type = "i4i.large"
  }

  override_data {
    target = data.aws_ec2_instance_type.keeper
    values = {
      supported_architectures = ["x86_64"]
      hypervisor              = "nitro"
      instance_disks          = [{ count = 1, size = 468, type = "ssd" }]
    }
  }

  override_data {
    target = data.aws_ami.keeper
    values = { architecture = "x86_64" }
  }

  assert {
    condition     = alltrue([for keeper in aws_instance.keeper : keeper.instance_type == "i4i.large"])
    error_message = "A matching x86_64 instance type override must be used for all keepers."
  }
}

run "mismatched_ami_is_refused" {
  command = plan

  override_data {
    target = data.aws_ami.keeper
    values = { architecture = "x86_64" }
  }

  expect_failures = [aws_instance.keeper]
}

run "unsupported_architecture_is_refused" {
  command = plan

  override_data {
    target = data.aws_ec2_instance_type.keeper
    values = {
      supported_architectures = ["arm64_mac"]
      hypervisor              = "nitro"
      instance_disks          = [{ count = 1, size = 468, type = "ssd" }]
    }
  }

  override_data {
    target = data.aws_ami.keeper
    values = { architecture = "arm64_mac" }
  }

  expect_failures = [aws_instance.keeper]
}

run "duplicate_az_is_refused" {
  command = plan

  override_data {
    target = data.aws_subnet.keeper["3"]
    values = {
      availability_zone       = "eu-north-1a"
      availability_zone_id    = "eun1-az1"
      vpc_id                  = "vpc-fixture"
      map_public_ip_on_launch = false
    }
  }

  expect_failures = [aws_security_group.keeper]
}

run "public_subnet_is_refused" {
  command = plan

  override_data {
    target = data.aws_subnet.keeper["3"]
    values = {
      availability_zone       = "eu-north-1c"
      availability_zone_id    = "eun1-az3"
      map_public_ip_on_launch = true
    }
  }

  expect_failures = [aws_security_group.keeper]
}

run "ebs_only_is_refused" {
  command = plan

  override_data {
    target = data.aws_ec2_instance_type.keeper
    values = {
      supported_architectures = ["arm64"]
      hypervisor              = "nitro"
      instance_disks          = []
    }
  }

  expect_failures = [aws_instance.keeper]
}

run "multiple_disks_are_refused" {
  command = plan

  override_data {
    target = data.aws_ec2_instance_type.keeper
    values = {
      supported_architectures = ["arm64"]
      hypervisor              = "nitro"
      instance_disks          = [{ count = 2, size = 3750, type = "ssd" }]
    }
  }

  expect_failures = [aws_instance.keeper]
}

run "hard_disk_is_refused" {
  command = plan

  override_data {
    target = data.aws_ec2_instance_type.keeper
    values = {
      supported_architectures = ["arm64"]
      hypervisor              = "nitro"
      instance_disks          = [{ count = 1, size = 468, type = "hdd" }]
    }
  }

  expect_failures = [aws_instance.keeper]
}

run "non_nitro_is_refused" {
  command = plan

  override_data {
    target = data.aws_ec2_instance_type.keeper
    values = {
      supported_architectures = ["arm64"]
      hypervisor              = "xen"
      instance_disks          = [{ count = 1, size = 468, type = "ssd" }]
    }
  }

  expect_failures = [aws_instance.keeper]
}
