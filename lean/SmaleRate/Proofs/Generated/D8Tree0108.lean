/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.DyadicAssembly
import SmaleRate.Proofs.Generated.D8Chunk0069

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0108 : BoxTree := (.split (.split (.split (.leaf (2068986808891/1000000000000 : ℚ)) (.leaf (1048292671799/500000000000 : ℚ))) (.leaf (1046575857889/500000000000 : ℚ))) (.leaf (526216695843/250000000000 : ℚ)))

theorem cover8_tree0108_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0108 (1/4 : ℚ) (1/2 : ℚ) := by
  unfold cover8_tree0108
  refine tree_all_split_at (3/8 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (5/16 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (9/32 : ℚ) (by norm_num) ?_ ?_
      · convert cover8_leaf1730_certificate hidentity using 1 <;>
          norm_num [treeAll, BoxEndpointBound]
      · convert cover8_leaf1731_certificate hidentity using 1 <;>
          norm_num [treeAll, BoxEndpointBound]
    · convert cover8_leaf1732_certificate hidentity using 1 <;>
        norm_num [treeAll, BoxEndpointBound]
  · convert cover8_leaf1733_certificate hidentity using 1 <;>
      norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0108_checked
#print axioms SmaleRate.Proofs.cover8_tree0108_checked
