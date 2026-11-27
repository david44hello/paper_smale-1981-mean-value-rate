# Comparing the Lean statements and proofs

[SmaleRate/Challenge/Statements.lean](SmaleRate/Challenge/Statements.lean) specifies the 257 compared statements using only `SmaleRate.Defs.*` and `SmaleRate.Cited.*` (minimal mode), with every proof body left open. [comparator.json](comparator.json) lists those 257 declarations and the eight permitted axioms (Lean's three standard axioms plus the five cited axioms in `SmaleRate/Cited/`). The 34 declarations marked `OPEN` in [the audit](../lean/AUDIT.md) (listed in `../lean/OPEN_ROWS.txt`) are excluded from the comparison. Each conditional statement carries its explicit background hypotheses in its type.

Use Linux with Git, elan, and bubblewrap (`bwrap`) installed and working. From the root of a clean Git checkout, prepare a temporary copy:

```bash
set -eu
comparison_dir=$(mktemp -d)
git archive HEAD:lean | tar -x -C "$comparison_dir"
cp -R comparator/SmaleRate comparator/comparator.json "$comparison_dir/"
cd "$comparison_dir"
lake exe cache get
```

Run the comparison:

```sh
lake --no-cache comparator --config=comparator.json
```

On acceptance, Lake prints `Lean default kernel accepts the solution` and `Your solution is okay!`. To run Lean's additional proof checkers, append `--paranoid` to the same command (note that two of the additional checkers decline non-standard cited axioms by design; see [What to read](../lean/WHAT_TO_READ.md) for the full checker breakdown).

Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
