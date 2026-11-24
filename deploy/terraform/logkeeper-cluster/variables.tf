variable "name" {
  description = "Cluster name, unique in the AWS account."
  type        = string

  validation {
    condition     = can(regex("^[a-z][a-z0-9-]{0,30}$", var.name))
    error_message = "Use a lowercase cluster name of 1–31 characters."
  }
}

variable "vpc_id" {
  description = "VPC for the keepers and the private hosted zone."
  type        = string
}

variable "private_subnet_ids" {
  description = "Private subnets in three distinct AZs, in permanent keeper endpoint order."
  type        = tuple([string, string, string])

  validation {
    condition     = length(distinct(var.private_subnet_ids)) == 3
    error_message = "Supply three different private subnets."
  }
}

variable "client_security_group_ids" {
  description = "Security groups permitted to connect to TCP 5448, including the learner sweeper."
  type        = set(string)

  validation {
    condition     = length(var.client_security_group_ids) > 0
    error_message = "Supply at least one client security group."
  }
}

variable "instance_type" {
  description = "Qualified arm64 or x86_64 Nitro EC2 type with exactly one local NVMe SSD."
  type        = string
  default     = "i8g.large"
}

variable "ami_id" {
  description = "Qualified Amazon Linux 2023 AMI with cloud-init, matching the instance type architecture."
  type        = string
}

variable "dns_zone_name" {
  description = "Private DNS suffix dedicated to this cluster, without a trailing dot."
  type        = string

  validation {
    condition = (
      length(var.dns_zone_name) <= 244 &&
      can(regex("^([a-z0-9]([a-z0-9-]{0,61}[a-z0-9])?\\.)+[a-z0-9]([a-z0-9-]{0,61}[a-z0-9])?$", var.dns_zone_name))
    )
    error_message = "Supply a lowercase DNS suffix that leaves room for a keeper label."
  }
}

variable "image_repository_name" {
  description = "Logkeeper's private ECR repository in the AWS provider's account and region."
  type        = string
}

variable "image_digests" {
  description = "Logkeeper multi-platform image index digests for endpoints 1, 2 and 3. Change one entry at a time."
  type        = tuple([string, string, string])

  validation {
    condition     = alltrue([for digest in var.image_digests : can(regex("^sha256:[0-9a-f]{64}$", digest))])
    error_message = "Supply three immutable SHA-256 image digests."
  }
}

variable "client_names" {
  description = "NAME values in urn:logkeeper:client:NAME allowed to read and head."
  type        = set(string)

  validation {
    condition     = alltrue([for name in var.client_names : can(regex("^[A-Za-z0-9][A-Za-z0-9_.-]{0,62}$", name))])
    error_message = "Use 1–63 letters, digits, dots, underscores, or hyphens per name, starting with a letter or digit."
  }
}

variable "writer_names" {
  description = "NAME values in urn:logkeeper:client:NAME allowed to create, seal, append, trim, and delete."
  type        = set(string)

  validation {
    condition     = alltrue([for name in var.writer_names : can(regex("^[A-Za-z0-9][A-Za-z0-9_.-]{0,62}$", name))])
    error_message = "Use 1–63 letters, digits, dots, underscores, or hyphens per name, starting with a letter or digit."
  }
}

variable "pki" {
  description = "Dedicated AWS Private CA in this region, its signing algorithm and its PEM trust bundle."
  type = object({
    ca_arn            = string
    signing_algorithm = string
    ca_certificate    = string
  })
}

variable "limits" {
  description = "Keeper limits common to all three keepers."
  type = object({
    stream_quota_bytes     = number
    max_record_bytes       = number
    round_bytes_per_stream = number
    round_requests         = number
  })
  default = {
    stream_quota_bytes     = 8589934592
    max_record_bytes       = 33554432
    round_bytes_per_stream = 4194304
    round_requests         = 64
  }

  validation {
    condition = (
      alltrue([for limit in values(var.limits) : limit > 0 && floor(limit) == limit && limit <= 9007199254740991]) &&
      var.limits.max_record_bytes <= min(var.limits.stream_quota_bytes, 4294967295)
    )
    error_message = "Limits must be positive, exactly representable integers. A record must fit its stream quota and the wire's u32 limit."
  }
}
