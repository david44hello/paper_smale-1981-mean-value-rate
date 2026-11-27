#!/usr/bin/env bash
# Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
set -euo pipefail
script_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
exec bash "$script_dir/check.sh" --final
