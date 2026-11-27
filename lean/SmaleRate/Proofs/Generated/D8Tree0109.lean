/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.DyadicAssembly
public import SmaleRate.Proofs.Generated.D8Chunk0069

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0109 : BoxTree := (.split (.leaf (2173935462319/1000000000000 : ℚ)) (.leaf (1292619632303/500000000000 : ℚ)))

theorem cover8_tree0109_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0109 (1/2 : ℚ) (1/1 : ℚ) := by
  unfold cover8_tree0109
  refine tree_all_split_at (3/4 : ℚ) (by norm_num) ?_ ?_
  · convert cover8_leaf1734_certificate hidentity using 1 <;>
      norm_num [treeAll, BoxEndpointBound]
  · convert cover8_leaf1735_certificate hidentity using 1 <;>
      norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0109_checked
#print axioms SmaleRate.Proofs.cover8_tree0109_checked
