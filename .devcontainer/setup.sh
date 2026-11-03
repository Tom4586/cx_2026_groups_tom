#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/.."

# Lake uses lean-toolchain and lake-manifest.json from this checkout.
# Fetch precompiled Mathlib artifacts before building the course.
lake exe cache get
lake build
