/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.DyadicAssembly
import SmaleRate.Proofs.Generated.D8Chunk0041
import SmaleRate.Proofs.Generated.D8Chunk0042

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0066 : BoxTree := (.split (.split (.split (.split (.leaf (2054902231677/1000000000000 : ℚ)) (.leaf (2054902239141/1000000000000 : ℚ))) (.split (.leaf (1027451123329/500000000000 : ℚ)) (.leaf (1027451127099/500000000000 : ℚ)))) (.split (.split (.leaf (64215695681/31250000000 : ℚ)) (.leaf (1027451134713/500000000000 : ℚ))) (.split (.leaf (2054902277081/1000000000000 : ℚ)) (.leaf (2054902284793/1000000000000 : ℚ))))) (.split (.split (.split (.leaf (2054902292541/1000000000000 : ℚ)) (.leaf (256862787541/125000000000 : ℚ))) (.split (.leaf (2054902308157/1000000000000 : ℚ)) (.leaf (1027451158009/500000000000 : ℚ)))) (.split (.split (.leaf (2054902323927/1000000000000 : ℚ)) (.leaf (1027451165933/500000000000 : ℚ))) (.split (.leaf (1027451169923/500000000000 : ℚ)) (.leaf (410980469577/200000000000 : ℚ))))))

theorem cover8_tree0066_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0066 (4195/32768 : ℚ) (1049/8192 : ℚ) := by
  unfold cover8_tree0066
  refine tree_all_split_at (8391/65536 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (16781/131072 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (33561/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (67121/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1048_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1049_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (67123/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1050_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1051_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (33563/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (67125/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1052_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1053_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (67127/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1054_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1055_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (16783/131072 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (33565/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (67129/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1056_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1057_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (67131/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1058_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1059_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (33567/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (67133/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1060_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1061_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (67135/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1062_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1063_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0066_checked
#print axioms SmaleRate.Proofs.cover8_tree0066_checked
