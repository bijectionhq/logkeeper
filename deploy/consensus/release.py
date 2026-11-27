#!/usr/bin/env python3
"""Build an OCI release archive from a committed tree and record its digests."""

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import tarfile
import tempfile


REPO = Path(__file__).resolve().parents[2]
PLATFORMS = ("linux/amd64", "linux/arm64")
LABEL = "org.opencontainers.image.revision"


def sha256(stream):
    digest = hashlib.sha256()
    for block in iter(lambda: stream.read(1024 * 1024), b""):
        digest.update(block)
    return digest.hexdigest()


def blob(archive, descriptor):
    digest = descriptor["digest"]
    if not re.fullmatch(r"sha256:[0-9a-f]{64}", digest):
        raise ValueError(f"invalid OCI blob digest {digest}")
    algorithm, value = digest.split(":", 1)
    member = archive.getmember(f"blobs/{algorithm}/{value}")
    if not member.isfile() or member.size != descriptor["size"]:
        raise ValueError(f"invalid OCI blob size or type for {digest}")
    return archive.extractfile(member)


def blob_json(archive, descriptor):
    with blob(archive, descriptor) as stream:
        data = stream.read()
    if f"sha256:{hashlib.sha256(data).hexdigest()}" != descriptor["digest"]:
        raise ValueError(f"OCI blob failed digest verification: {descriptor['digest']}")
    return json.loads(data)


def image_digests(path, image_digest, commit, platforms):
    with tarfile.open(path, "r") as archive:
        with archive.extractfile("index.json") as stream:
            root = stream.read()
        descriptors = json.loads(root)["manifests"]
        if f"sha256:{hashlib.sha256(root).hexdigest()}" != image_digest:
            descriptors = [item for item in descriptors if item["digest"] == image_digest]
            if len(descriptors) != 1:
                raise ValueError("BuildKit image digest missing from OCI archive")
        images = {}
        while descriptors:
            descriptor = descriptors.pop()
            manifest = blob_json(archive, descriptor)
            if "manifests" in manifest:
                descriptors.extend(manifest["manifests"])
                continue
            config = blob_json(archive, manifest["config"])
            if config["config"]["Labels"].get(LABEL) != commit:
                raise ValueError("image does not identify the expected source commit")
            for layer in manifest["layers"]:
                with blob(archive, layer) as stream:
                    if f"sha256:{sha256(stream)}" != layer["digest"]:
                        raise ValueError(f"OCI layer failed digest verification: {layer['digest']}")
            platform = f"{config['os']}/{config['architecture']}"
            if platform in images:
                raise ValueError(f"duplicate image for {platform}")
            images[platform] = descriptor["digest"]
        if set(images) != set(platforms):
            raise ValueError(f"expected platforms {platforms}, found {sorted(images)}")
        return images


def git(*args):
    return subprocess.check_output(["git", "-C", str(REPO), *args], text=True).strip()


def build(revision, output, platforms, builder):
    commit = git("rev-parse", "--verify", "--end-of-options", f"{revision}^{{commit}}")
    epoch = int(git("show", "-s", "--format=%ct", commit))
    output = output.resolve()
    if output.exists():
        raise FileExistsError(output)
    output.parent.mkdir(parents=True, exist_ok=True)
    # Publish the local output directory only after the complete archive verifies.
    with tempfile.TemporaryDirectory(prefix="logkeeper-release-", dir=output.parent) as scratch:
        work = Path(scratch)
        bundle = work / "bundle"
        bundle.mkdir()
        source = work / "source.tar"
        archive = bundle / "logkeeper-consensus.oci.tar"
        metadata = work / "build.json"
        subprocess.run(["git", "-C", str(REPO), "archive", f"--output={source}", commit], check=True)
        command = ["docker", "buildx", "build"]
        if builder:
            command += ["--builder", builder]
        command += [
            "--platform", ",".join(platforms), "--file", "deploy/consensus/Dockerfile",
            "--provenance=false", "--sbom=false",
            "--build-arg", f"SOURCE_DATE_EPOCH={epoch}",
            "--build-arg", "BUILDKIT_MULTI_PLATFORM=1",
            "--label", f"{LABEL}={commit}", "--tag", f"logkeeper-consensus:{commit}",
            "--output", f"type=oci,dest={archive},rewrite-timestamp=true",
            "--metadata-file", str(metadata), "-",
        ]
        with source.open("rb") as stream:
            subprocess.run(command, stdin=stream, check=True)
        digest = json.loads(metadata.read_text())["containerimage.digest"]
        images = image_digests(archive, digest, commit, platforms)
        with archive.open("rb") as stream:
            archive_hash = sha256(stream)
        manifest = bundle / "release.json"
        manifest.write_text(json.dumps({
            "source_commit": commit,
            "source_date_epoch": epoch,
            "archive": archive.name,
            "archive_sha256": archive_hash,
            "image_digest": digest,
            "platform_image_digests": images,
        }, indent=2, sort_keys=True) + "\n")
        with manifest.open("rb") as stream:
            manifest_hash = sha256(stream)
        (bundle / "SHA256SUMS").write_text(f"{archive_hash}  {archive.name}\n{manifest_hash}  {manifest.name}\n")
        bundle.rename(output)
    print(f"{commit} {digest} {output}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--ref", default="HEAD", help="git ref to archive and build")
    parser.add_argument("--output", type=Path, required=True, help="new release bundle directory")
    parser.add_argument("--platform", action="append", choices=PLATFORMS, help="default: both Linux platforms")
    parser.add_argument("--builder", help="Docker Buildx builder with OCI exporter support")
    args = parser.parse_args()
    platforms = tuple(sorted(set(args.platform or PLATFORMS)))
    try:
        build(args.ref, args.output, platforms, args.builder)
    except (subprocess.CalledProcessError, OSError, ValueError, KeyError, tarfile.TarError) as error:
        parser.exit(1, f"Release build failed: {error}\n")


if __name__ == "__main__":
    main()
