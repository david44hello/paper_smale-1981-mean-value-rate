/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.DyadicAssembly
import SmaleRate.Proofs.Generated.D8Chunk0000

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0000 : BoxTree := (.split (.leaf (1046998702637/500000000000 : ℚ)) (.split (.leaf (2083342782629/1000000000000 : ℚ)) (.leaf (2056957656669/1000000000000 : ℚ))))

theorem cover8_tree0000_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0000 (0/1 : ℚ) (1/16 : ℚ) := by
  unfold cover8_tree0000
  refine tree_all_split_at (1/32 : ℚ) (by norm_num) ?_ ?_
  · convert cover8_leaf0000_certificate hidentity using 1 <;>
      norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (3/64 : ℚ) (by norm_num) ?_ ?_
    · convert cover8_leaf0001_certificate hidentity using 1 <;>
        norm_num [treeAll, BoxEndpointBound]
    · convert cover8_leaf0002_certificate hidentity using 1 <;>
        norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0000_checked
#print axioms SmaleRate.Proofs.cover8_tree0000_checked
