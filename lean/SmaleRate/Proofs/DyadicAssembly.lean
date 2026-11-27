/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
module

public import SmaleRate.Proofs.DyadicCover

set_option backward.proofsInPublic true

@[expose] public section

namespace SmaleRate.Proofs

/-- Normalize each rational midpoint separately, without expanding an entire cover at once. -/
theorem tree_all_split_at {predicate : CertifiedBoxData → Prop}
    {first second : BoxTree} {left right : ℚ} (middle : ℚ)
    (hmid : middle = (left + right) / 2)
    (hfirst : treeAll predicate first left middle)
    (hsecond : treeAll predicate second middle right) :
    treeAll predicate (.split first second) left right := by
  subst middle
  exact ⟨hfirst, hsecond⟩

end SmaleRate.Proofs

#check SmaleRate.Proofs.tree_all_split_at
#print axioms SmaleRate.Proofs.tree_all_split_at
