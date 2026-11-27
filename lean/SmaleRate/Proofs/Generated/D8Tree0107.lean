/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.DyadicAssembly
import SmaleRate.Proofs.Generated.D8Chunk0069

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0107 : BoxTree := (.split (.split (.split (.leaf (2058131566827/1000000000000 : ℚ)) (.leaf (103113015187/50000000000 : ℚ))) (.leaf (51382457799/25000000000 : ℚ))) (.split (.leaf (206547193537/100000000000 : ℚ)) (.leaf (2076628766069/1000000000000 : ℚ))))

theorem cover8_tree0107_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0107 (3/16 : ℚ) (1/4 : ℚ) := by
  unfold cover8_tree0107
  refine tree_all_split_at (7/32 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (13/64 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (25/128 : ℚ) (by norm_num) ?_ ?_
      · convert cover8_leaf1725_certificate hidentity using 1 <;>
          norm_num [treeAll, BoxEndpointBound]
      · convert cover8_leaf1726_certificate hidentity using 1 <;>
          norm_num [treeAll, BoxEndpointBound]
    · convert cover8_leaf1727_certificate hidentity using 1 <;>
        norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (15/64 : ℚ) (by norm_num) ?_ ?_
    · convert cover8_leaf1728_certificate hidentity using 1 <;>
        norm_num [treeAll, BoxEndpointBound]
    · convert cover8_leaf1729_certificate hidentity using 1 <;>
        norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0107_checked
#print axioms SmaleRate.Proofs.cover8_tree0107_checked
