#!/usr/bin/env python3
"""Verify Logkeeper's shipped Rust and check each declared negative control."""

import argparse
from collections import Counter
from hashlib import sha256
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import tempfile


AREAS = Path(__file__).resolve().parent
ROOT = AREAS.parents[1]
PATH_ATTRIBUTE = re.compile(r'#\[\s*path\s*=\s*"([^"]+)"\s*\]')
FUNCTION = re.compile(
    r"^\s*(?:pub(?:\([^)]*\))?\s+)?"
    r"(?:(?:open|closed|proof|spec|exec|const|unsafe|async)\s+)*fn\s+(\w+)\s*[<(]"
)
LOOP = re.compile(r"^\s*(?:'[a-zA-Z_]\w*:\s*)?(?:while|for|loop)\b")
ERROR = re.compile(r"^(?:error|error\[\w+\]): (.+)$", re.MULTILINE)
LOCATION = re.compile(r"^\s*--> (.+?):(\d+):\d+\s*$", re.MULTILINE)
TIMEOUT_SECONDS = 120


def write_json(path, data):
    path.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")


def snapshot(area):
    """Read the harness and transitively included source once for all cases."""
    pending = list(area.rglob("*.rs"))
    sources = {}
    while pending:
        path = pending.pop().resolve()
        relative = path.relative_to(ROOT).as_posix()
        if relative in sources:
            continue
        source = path.read_bytes()
        sources[relative] = source
        pending.extend(path.parent / name for name in PATH_ATTRIBUTE.findall(source.decode("utf-8")))
    return sources


def mutate(directory, sources, control):
    edits = control["mutate"]
    if not any(edit["file"].startswith("src/") for edit in edits):
        raise ValueError("control must edit a shipped file under src/")
    for edit in edits:
        file = edit["file"]
        if file not in sources:
            raise ValueError(f"mutation targets a file outside the harness: {file}")
        path = directory / file
        source = path.read_bytes()
        old = edit["find"].encode("utf-8")
        new = edit["replace"].encode("utf-8")
        if not old or old == new or source.count(old) != 1:
            raise ValueError(f"{file}: mutation must change exactly one occurrence")
        path.write_bytes(source.replace(old, new, 1))


def function_at(path, line):
    function = None
    in_contract = False
    for index, source in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        if source.lstrip().startswith(("#[verus_spec(", "#[cfg_attr(verus_keep_ghost, verus_spec(")):
            in_contract = True
        if match := FUNCTION.match(source):
            function = match[1]
            in_contract = False
        if in_contract and LOOP.match(source):
            # A Verus loop attribute belongs to the enclosing function.
            in_contract = False
        if index >= line and not in_contract:
            return function
    return None


def diagnostics(stderr, directory):
    errors = list(ERROR.finditer(stderr))
    observed = []
    for index, error in enumerate(errors):
        end = errors[index + 1].start() if index + 1 < len(errors) else len(stderr)
        category = error[1]
        if match := LOCATION.search(stderr, error.end(), end):
            path = (directory / match[1]).resolve()
            observed.append((path.relative_to(directory).as_posix(), function_at(path, int(match[2])), category))
        elif index != len(errors) - 1 or not re.fullmatch(r"aborting due to \d+ previous errors?(?:; .* emitted)?", category):
            raise ValueError(f"unexpected Verus diagnostic without a source location: {category}")
    return observed


def run_case(verus, config, harness, sources, evidence, name, control):
    with tempfile.TemporaryDirectory(prefix="logkeeper-verus-") as scratch:
        directory = Path(scratch).resolve()
        for file, source in sources.items():
            path = directory / file
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(source)
        if control is not None:
            mutate(directory, sources, control)
        command = [verus, "--output-json", "--multiple-errors", "5", *config["flags"], harness]
        write_json(evidence / f"{name}.command.json", {
            "command": command, "directory": str(directory), "timeout_seconds": TIMEOUT_SECONDS,
        })
        stdout = evidence / f"{name}.stdout"
        stderr = evidence / f"{name}.stderr"
        with stdout.open("wb") as out, stderr.open("wb") as err:
            with subprocess.Popen(command, cwd=directory, stdout=out, stderr=err, start_new_session=True) as process:
                try:
                    status = process.wait(timeout=TIMEOUT_SECONDS)
                except (subprocess.TimeoutExpired, KeyboardInterrupt):
                    try:
                        os.killpg(process.pid, signal.SIGKILL)
                    except ProcessLookupError:
                        pass
                    raise
        result = json.loads(stdout.read_bytes())["verification-results"]
        observed = diagnostics(stderr.read_text(encoding="utf-8"), directory)
        expected = []
        floor = config["min_verified_functions"]
        if control is not None:
            expected = [(item["file"], item["function"], item["category"]) for item in control["expect"]]
            if not expected:
                raise ValueError("control must declare an expected diagnostic")
            floor = control["min_verified_functions"]
        failed_functions = {(file, function) for file, function, _ in expected}
        if (
            status != int(control is not None)
            or result["encountered-vir-error"]
            or result["errors"] != len(failed_functions)
            or result["verified"] < floor
            or Counter(observed) != Counter(expected)
        ):
            raise ValueError(f"{result}, observed {observed}, expected {expected}, minimum verified {floor}")
        print(f"{evidence.name} {name}: {result['verified']} verified, "
              f"{len(expected)} expected diagnostic(s)", flush=True)


def verify_area(verus, manifest, evidence):
    area = manifest.parent
    config = json.loads(manifest.read_bytes())
    harness = (area / "proof.rs").relative_to(ROOT).as_posix()
    sources = snapshot(area)
    for file in (harness, (area / "laws.rs").relative_to(ROOT).as_posix()):
        if file not in sources:
            raise ValueError(f"missing {file}")
    controls = config["controls"]
    if not controls or "baseline" in controls:
        raise ValueError("declare at least one control with a name other than baseline")
    write_json(evidence / "area.json", config)
    write_json(evidence / "inputs.json", {
        file: sha256(source).hexdigest() for file, source in sorted(sources.items())
    })
    for name, control in [("baseline", None), *controls.items()]:
        if not re.fullmatch(r"[a-zA-Z0-9_-]+", name):
            raise ValueError(f"invalid control name: {name}")
        try:
            run_case(verus, config, harness, sources, evidence, name, control)
        except (OSError, ValueError, KeyError, subprocess.TimeoutExpired) as error:
            raise ValueError(f"{name}: {error}") from error


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("areas", nargs="*", metavar="AREA", help="area names (default: all areas)")
    parser.add_argument("--verus", default="verus", help="Verus executable or shared launcher")
    parser.add_argument("--evidence", type=Path, help="fresh output directory (default: .results/run-*)")
    args = parser.parse_args()
    manifests = {path.parent.name: path for path in sorted(AREAS.glob("*/area.json"))}
    unknown = set(args.areas) - manifests.keys()
    if unknown:
        parser.error(f"unknown areas: {', '.join(sorted(unknown))}")
    if not manifests:
        parser.error("no verification areas found")
    executable = shutil.which(args.verus)
    if executable is None:
        parser.error(f"Verus executable not found: {args.verus}")
    verus = str(Path(executable).resolve())
    if args.evidence is None:
        results = AREAS / ".results"
        results.mkdir(exist_ok=True)
        evidence = Path(tempfile.mkdtemp(prefix="run-", dir=results))
    else:
        evidence = args.evidence.resolve()
        evidence.mkdir(parents=True, exist_ok=False)
    print(f"Evidence: {evidence}", flush=True)
    for name in dict.fromkeys(args.areas or manifests):
        area_evidence = evidence / name
        area_evidence.mkdir()
        try:
            verify_area(verus, manifests[name], area_evidence)
        except (OSError, ValueError, KeyError) as error:
            parser.exit(1, f"{name}: {error}\nSee {area_evidence}\n")


if __name__ == "__main__":
    main()
