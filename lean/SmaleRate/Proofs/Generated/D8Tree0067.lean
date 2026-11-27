/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.DyadicAssembly
public import SmaleRate.Proofs.Generated.D8Chunk0042
public import SmaleRate.Proofs.Generated.D8Chunk0043

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0067 : BoxTree := (.split (.split (.split (.split (.leaf (2054902355943/1000000000000 : ℚ)) (.leaf (2054902364039/1000000000000 : ℚ))) (.split (.leaf (513725593047/250000000000 : ℚ)) (.leaf (410980476073/200000000000 : ℚ)))) (.split (.split (.leaf (205490238859/100000000000 : ℚ)) (.leaf (1027451198421/500000000000 : ℚ))) (.split (.leaf (2054902405151/1000000000000 : ℚ)) (.leaf (1027451206747/500000000000 : ℚ))))) (.split (.split (.split (.leaf (2054902421877/1000000000000 : ℚ)) (.leaf (2054902430279/1000000000000 : ℚ))) (.split (.leaf (1027451219371/500000000000 : ℚ)) (.leaf (1027451223621/500000000000 : ℚ)))) (.split (.split (.leaf (1027451227889/500000000000 : ℚ)) (.leaf (1027451232179/500000000000 : ℚ))) (.split (.leaf (513725618243/250000000000 : ℚ)) (.leaf (256862810203/125000000000 : ℚ))))))

theorem cover8_tree0067_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0067 (1049/8192 : ℚ) (4197/32768 : ℚ) := by
  unfold cover8_tree0067
  refine tree_all_split_at (8393/65536 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (16785/131072 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (33569/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (67137/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1064_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1065_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (67139/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1066_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1067_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (33571/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (67141/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1068_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1069_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (67143/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1070_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1071_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (16787/131072 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (33573/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (67145/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1072_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1073_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (67147/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1074_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1075_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (33575/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (67149/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1076_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1077_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (67151/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1078_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1079_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0067_checked
#print axioms SmaleRate.Proofs.cover8_tree0067_checked
