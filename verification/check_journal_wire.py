#!/usr/bin/env python3
"""Check the keeper protocol tables against the Rust wire types."""

from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parent.parent
TABLES = {"Request": "Requests", "Reply": "Replies", "Refusal": "Refusals"}
VARIANT = re.compile(r"^    (\w+(?:\s*\{[^}]*\}|\([^\n)]*\))?),[ \t]*$", re.MULTILINE)


def normalize(signature):
    return re.sub(r"\s+", "", signature).replace(",}", "}")


def variants(wire, name):
    body = re.search(rf"^pub enum {name} \{{\n(.*?)^\}}", wire, re.MULTILINE | re.DOTALL)[1]
    body = re.sub(r"^\s*///[^\n]*\n", "", body, flags=re.MULTILINE)
    if VARIANT.sub("", body).strip():
        raise ValueError(f"could not parse all {name} variants")
    return VARIANT.findall(body)


def table(spec, heading):
    section = spec.split(f"\n### {heading}\n", 1)[1]
    section = section.split("\n##", 1)[0]
    return re.findall(r"^\| `([^`]+)` \|", section, re.MULTILINE)


def check_promise(wire, spec):
    body = re.search(r"^pub struct StreamView \{\n(.*?)^\}", wire, re.MULTILINE | re.DOTALL)[1]
    field = re.search(r"^    pub (promised: [^\n]+),$", body, re.MULTILINE)[1]
    documented = re.findall(r"`(promised: [^`]+)`", spec)
    if normalize(field) != "promised:Option<(Epoch,Identity,u128)>" or documented != [field]:
        raise ValueError("StreamView: a promise must contain an epoch, identity and proposal ID")


def check(wire, spec):
    checked = 0
    for name, heading in TABLES.items():
        expected = {normalize(signature): signature for signature in variants(wire, name)}
        rows = [normalize(signature) for signature in table(spec, heading)]
        missing = sorted(expected.keys() - set(rows))
        extras = sorted(set(rows) - expected.keys())
        if missing:
            raise ValueError(f"{heading}: missing {', '.join(expected[key].split()[0] for key in missing)}")
        if extras or len(rows) != len(set(rows)):
            raise ValueError(f"{heading}: unexpected or duplicate rows {extras}")
        checked += len(rows)
    check_promise(wire, spec)
    return checked


def main():
    wire = (ROOT / "src/stream/wire.rs").read_text()
    spec = (ROOT / "verification/target-journal.md").read_text()
    try:
        checked = check(wire, spec)
        for heading in TABLES.values():
            for signature in table(spec, heading):
                # Remove one row from the protocol section for each possible omission.
                intro, section = spec.split(f"\n### {heading}\n", 1)
                row = f"| `{signature}` |"
                defective = f"{intro}\n### {heading}\n" + section.replace(row, "| omitted |", 1)
                try:
                    check(wire, defective)
                except ValueError as error:
                    if not str(error).startswith(f"{heading}: missing "):
                        raise
                else:
                    raise ValueError(f"{heading}: omission of {signature} went undetected")
        for old, new, message in (
            ("proposal: u128", "proposal: Option<u128>", "Requests: missing Seal"),
            ("promised: Option<(Epoch, Identity, u128)>",
             "promised: Option<(Epoch, Identity)>", "StreamView: a promise must contain"),
        ):
            try:
                check(wire, spec.replace(old, new, 1))
            except ValueError as error:
                if not str(error).startswith(message):
                    raise
            else:
                raise ValueError(f"proposal control went undetected: {new}")
    except (ValueError, TypeError, IndexError) as error:
        sys.exit(str(error))
    print(f"wire specification: {checked} variants and promise checked, "
          f"{checked} omissions and 2 missing-proposal controls rejected")


if __name__ == "__main__":
    main()
