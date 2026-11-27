/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.DyadicAssembly
import SmaleRate.Proofs.Generated.D8Chunk0046
import SmaleRate.Proofs.Generated.D8Chunk0047

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0073 : BoxTree := (.split (.split (.split (.split (.leaf (2054903313807/1000000000000 : ℚ)) (.leaf (1027451662849/500000000000 : ℚ))) (.split (.leaf (1027451668817/500000000000 : ℚ)) (.leaf (2054903349587/1000000000000 : ℚ)))) (.split (.split (.leaf (2054903361599/1000000000000 : ℚ)) (.leaf (41098067473/20000000000 : ℚ))) (.split (.leaf (1027451692867/500000000000 : ℚ)) (.leaf (1027451698933/500000000000 : ℚ))))) (.split (.split (.split (.leaf (513725852511/250000000000 : ℚ)) (.leaf (2054903422241/1000000000000 : ℚ))) (.split (.leaf (205490343449/100000000000 : ℚ)) (.leaf (2054903446769/1000000000000 : ℚ)))) (.split (.split (.leaf (1027451729551/500000000000 : ℚ)) (.leaf (2054903471457/1000000000000 : ℚ))) (.split (.leaf (128431467741/62500000000 : ℚ)) (.leaf (513725874077/250000000000 : ℚ))))))

theorem cover8_tree0073_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0073 (2101/16384 : ℚ) (4203/32768 : ℚ) := by
  unfold cover8_tree0073
  refine tree_all_split_at (8405/65536 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (16809/131072 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (33617/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (67233/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1160_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1161_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (67235/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1162_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1163_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (33619/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (67237/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1164_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1165_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (67239/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1166_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1167_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (16811/131072 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (33621/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (67241/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1168_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1169_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (67243/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1170_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1171_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (33623/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (67245/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1172_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1173_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (67247/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1174_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1175_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0073_checked
#print axioms SmaleRate.Proofs.cover8_tree0073_checked
