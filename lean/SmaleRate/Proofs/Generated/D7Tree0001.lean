/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.DyadicAssembly
import SmaleRate.Proofs.Generated.D7Chunk0000

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover7_tree0001 : BoxTree := (.split (.split (.leaf (508532980103/250000000000 : ℚ)) (.leaf (253245011987/125000000000 : ℚ))) (.split (.leaf (100971556171/50000000000 : ℚ)) (.split (.leaf (2024590388117/1000000000000 : ℚ)) (.leaf (2022163720493/1000000000000 : ℚ)))))

theorem cover7_tree0001_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 7 box ∧ (2019/1000 : ℝ) < (box.lower : ℝ)) cover7_tree0001 (1/16 : ℚ) (3/32 : ℚ) := by
  unfold cover7_tree0001
  refine tree_all_split_at (5/64 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (9/128 : ℚ) (by norm_num) ?_ ?_
    · convert cover7_leaf0003_certificate hidentity using 1 <;>
        norm_num [treeAll, BoxEndpointBound]
    · convert cover7_leaf0004_certificate hidentity using 1 <;>
        norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (11/128 : ℚ) (by norm_num) ?_ ?_
    · convert cover7_leaf0005_certificate hidentity using 1 <;>
        norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (23/256 : ℚ) (by norm_num) ?_ ?_
      · convert cover7_leaf0006_certificate hidentity using 1 <;>
          norm_num [treeAll, BoxEndpointBound]
      · convert cover7_leaf0007_certificate hidentity using 1 <;>
          norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover7_tree0001_checked
#print axioms SmaleRate.Proofs.cover7_tree0001_checked
