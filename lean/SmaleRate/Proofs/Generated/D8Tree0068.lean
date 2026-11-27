/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.DyadicAssembly
public import SmaleRate.Proofs.Generated.D8Chunk0043

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0068 : BoxTree := (.split (.split (.split (.split (.leaf (205490249033/100000000000 : ℚ)) (.leaf (102745124953/50000000000 : ℚ))) (.split (.leaf (256862813479/125000000000 : ℚ)) (.leaf (2054902516657/1000000000000 : ℚ)))) (.split (.split (.leaf (2054902525499/1000000000000 : ℚ)) (.leaf (410980506877/200000000000 : ℚ))) (.split (.leaf (82196101733/40000000000 : ℚ)) (.leaf (410980510461/200000000000 : ℚ))))) (.split (.split (.split (.leaf (1027451280651/500000000000 : ℚ)) (.leaf (2054902570359/1000000000000 : ℚ))) (.split (.leaf (513725644863/250000000000 : ℚ)) (.leaf (2054902588583/1000000000000 : ℚ)))) (.split (.split (.leaf (2054902597741/1000000000000 : ℚ)) (.leaf (41098052139/20000000000 : ℚ))) (.split (.leaf (16053926689/7812500000 : ℚ)) (.leaf (1027451312743/500000000000 : ℚ))))))

theorem cover8_tree0068_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0068 (4197/32768 : ℚ) (2099/16384 : ℚ) := by
  unfold cover8_tree0068
  refine tree_all_split_at (8395/65536 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (16789/131072 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (33577/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (67153/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1080_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1081_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (67155/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1082_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1083_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (33579/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (67157/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1084_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1085_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (67159/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1086_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1087_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (16791/131072 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (33581/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (67161/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1088_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1089_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (67163/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1090_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1091_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (33583/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (67165/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1092_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1093_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (67167/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1094_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1095_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0068_checked
#print axioms SmaleRate.Proofs.cover8_tree0068_checked
