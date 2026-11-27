/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.DyadicAssembly
import SmaleRate.Proofs.Generated.D8Chunk0043
import SmaleRate.Proofs.Generated.D8Chunk0044

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0069 : BoxTree := (.split (.split (.split (.split (.leaf (513725658703/250000000000 : ℚ)) (.leaf (205490264419/100000000000 : ℚ))) (.split (.leaf (2054902653591/1000000000000 : ℚ)) (.leaf (1027451331517/500000000000 : ℚ)))) (.split (.split (.leaf (410980534503/200000000000 : ℚ)) (.leaf (2054902682047/1000000000000 : ℚ))) (.split (.leaf (2054902691603/1000000000000 : ℚ)) (.leaf (2054902701213/1000000000000 : ℚ))))) (.split (.split (.split (.leaf (41098054217/20000000000 : ℚ)) (.leaf (256862840067/125000000000 : ℚ))) (.split (.leaf (410980546053/200000000000 : ℚ)) (.leaf (2054902740013/1000000000000 : ℚ)))) (.split (.split (.leaf (256862843727/125000000000 : ℚ)) (.leaf (2054902759661/1000000000000 : ℚ))) (.split (.leaf (256862846193/125000000000 : ℚ)) (.leaf (256862847433/125000000000 : ℚ))))))

theorem cover8_tree0069_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0069 (2099/16384 : ℚ) (4199/32768 : ℚ) := by
  unfold cover8_tree0069
  refine tree_all_split_at (8397/65536 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (16793/131072 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (33585/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (67169/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1096_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1097_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (67171/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1098_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1099_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (33587/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (67173/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1100_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1101_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (67175/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1102_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1103_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (16795/131072 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (33589/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (67177/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1104_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1105_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (67179/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1106_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1107_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (33591/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (67181/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1108_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1109_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (67183/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1110_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1111_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0069_checked
#print axioms SmaleRate.Proofs.cover8_tree0069_checked
