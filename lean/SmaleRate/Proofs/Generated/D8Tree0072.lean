/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.DyadicAssembly
import SmaleRate.Proofs.Generated.D8Chunk0045
import SmaleRate.Proofs.Generated.D8Chunk0046

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0072 : BoxTree := (.split (.split (.split (.split (.leaf (2054903128917/1000000000000 : ℚ)) (.leaf (2054903140177/1000000000000 : ℚ))) (.split (.leaf (1027451575741/500000000000 : ℚ)) (.leaf (1027451581411/500000000000 : ℚ)))) (.split (.split (.leaf (2054903174197/1000000000000 : ℚ)) (.leaf (1027451592807/500000000000 : ℚ))) (.split (.leaf (410980639413/200000000000 : ℚ)) (.leaf (2054903208561/1000000000000 : ℚ))))) (.split (.split (.split (.leaf (2054903220093/1000000000000 : ℚ)) (.leaf (6421572599/3125000000 : ℚ))) (.split (.leaf (2054903243289/1000000000000 : ℚ)) (.leaf (1027451627469/500000000000 : ℚ)))) (.split (.split (.leaf (2054903266639/1000000000000 : ℚ)) (.leaf (513725819591/250000000000 : ℚ))) (.split (.leaf (513725822537/250000000000 : ℚ)) (.leaf (2054903301947/1000000000000 : ℚ))))))

theorem cover8_tree0072_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0072 (4201/32768 : ℚ) (2101/16384 : ℚ) := by
  unfold cover8_tree0072
  refine tree_all_split_at (8403/65536 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (16805/131072 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (33609/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (67217/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1144_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1145_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (67219/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1146_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1147_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (33611/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (67221/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1148_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1149_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (67223/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1150_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1151_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (16807/131072 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (33613/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (67225/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1152_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1153_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (67227/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1154_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1155_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (33615/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (67229/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1156_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1157_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (67231/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1158_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1159_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0072_checked
#print axioms SmaleRate.Proofs.cover8_tree0072_checked
