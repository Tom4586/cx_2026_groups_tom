"""Fetch only the Mathlib modules imported by the course, including dependencies."""

from pathlib import Path
import argparse
import re
import subprocess


root = Path(__file__).resolve().parent.parent
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--teacher", action="store_true", help="also fetch teacher-only imports")
args = parser.parse_args()
sources = [root / "Cx2026Groups.lean", *sorted((root / "Cx2026Groups").rglob("*.lean"))]
if args.teacher:
    sources += [root / "Cx2026GroupsTeacher.lean", *sorted((root / "Cx2026GroupsTeacher").rglob("*.lean"))]
imports = set()
for source in sources:
    imports.update(
        re.findall(
            r"^\s*(?:(?:public|private|meta)\s+)*import\s+(Mathlib(?:\.[\w']+)*)\b",
            source.read_text(encoding="utf-8"),
            re.MULTILINE,
        )
    )

if imports:
    print(f"Fetching cache for {len(imports)} Mathlib imports and their dependencies...", flush=True)
    subprocess.run(["lake", "exe", "cache", "get", *sorted(imports)], cwd=root, check=True)
else:
    print("No Mathlib imports found; skipping the Mathlib cache download.")
