/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.DyadicAssembly
import SmaleRate.Proofs.Generated.D7Chunk0025

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover7_tree0042 : BoxTree := (.split (.leaf (2100546246443/1000000000000 : ℚ)) (.leaf (2485547699609/1000000000000 : ℚ)))

theorem cover7_tree0042_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 7 box ∧ (2019/1000 : ℝ) < (box.lower : ℝ)) cover7_tree0042 (1/2 : ℚ) (1/1 : ℚ) := by
  unfold cover7_tree0042
  refine tree_all_split_at (3/4 : ℚ) (by norm_num) ?_ ?_
  · convert cover7_leaf0642_certificate hidentity using 1 <;>
      norm_num [treeAll, BoxEndpointBound]
  · convert cover7_leaf0643_certificate hidentity using 1 <;>
      norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover7_tree0042_checked
#print axioms SmaleRate.Proofs.cover7_tree0042_checked
