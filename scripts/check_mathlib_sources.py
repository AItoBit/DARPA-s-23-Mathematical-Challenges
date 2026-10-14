"""Check the review snapshots against the pinned Mathlib checkout."""

import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tomllib


ROOT = Path(__file__).resolve().parents[1]
BUNDLE = ROOT / "docs" / "mathlib"


def main():
    manifest = json.loads((BUNDLE / "manifest.json").read_text(encoding="utf-8"))
    pin = manifest["commit"]
    lakefile = tomllib.loads((ROOT / "lakefile.toml").read_text(encoding="utf-8"))
    requirement = next(r for r in lakefile["require"] if r["name"] == "mathlib")
    assert requirement["rev"] == pin, "Lakefile Mathlib pin differs from snapshot"
    lake_manifest = json.loads((ROOT / "lake-manifest.json").read_text(encoding="utf-8"))
    package = next(p for p in lake_manifest["packages"] if p["name"] == "mathlib")
    assert package["rev"] == pin, "Lake manifest Mathlib pin differs from snapshot"
    upstream = Path(sys.argv[1]) if len(sys.argv) > 1 else ROOT / ".lake/packages/mathlib"
    head = subprocess.check_output(
        ["git", "-C", str(upstream), "rev-parse", "HEAD"], text=True
    ).strip()
    assert head == pin, "Mathlib checkout differs from snapshot pin"
    for entry in manifest["files"]:
        snapshot = (BUNDLE / entry["snapshot"]).read_bytes()
        assert hashlib.sha256(snapshot).hexdigest() == entry["sha256"], entry["snapshot"]
        # Read the committed Git blob, independent of checkout newline conversion.
        original = subprocess.check_output(
            ["git", "-C", str(upstream), "show", f'{pin}:{entry["path"]}']
        )
        assert snapshot == original, f'Snapshot differs from pinned blob: {entry["path"]}'
        print(f'Exact pinned source: {entry["path"]}')


if __name__ == "__main__":
    main()
