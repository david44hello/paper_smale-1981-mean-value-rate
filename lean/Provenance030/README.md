# Reused Smale-equals-4 proof modules (`Smale/`)

The 21 Lean files under `Smale/` are copied byte-for-byte from tag `v2.70` (commit `abf7f9d748ec78e71535814167f77ff185143dbd`) of `https://github.com/david44hello/paper_smale-mean-value-constant-equals-4` (`lean/`). They are the transitive source-import closure of `Smale.P030.Contract` excluding Mathlib, retaining their original namespaces, Apache 2.0 notices, definitions, and proofs unchanged. `LICENSE`, `NOTICE`, and `SOURCE_SHA256SUMS` record the original notices and SHA-256 digests.

`SmaleRate/Proofs/Public030Bridge.lean` bridges the derivative-one normalization used there to the nonzero-derivative class `IsPd` used in `SmaleRate` without adding any axiom or background hypothesis.

Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
