/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.DyadicAssembly
import SmaleRate.Proofs.Generated.D8Chunk0047

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0074 : BoxTree := (.split (.split (.split (.split (.leaf (2054903508791/1000000000000 : ℚ)) (.leaf (256862940163/125000000000 : ℚ))) (.split (.leaf (2054903533873/1000000000000 : ℚ)) (.leaf (2054903546477/1000000000000 : ℚ)))) (.split (.split (.leaf (1027451779551/500000000000 : ℚ)) (.leaf (102745178589/50000000000 : ℚ))) (.split (.leaf (2054903584503/1000000000000 : ℚ)) (.leaf (2054903597259/1000000000000 : ℚ))))) (.split (.split (.split (.leaf (1027451805029/500000000000 : ℚ)) (.leaf (410980724579/200000000000 : ℚ))) (.split (.leaf (1027451817883/500000000000 : ℚ)) (.leaf (410980729739/200000000000 : ℚ)))) (.split (.split (.leaf (513725915411/250000000000 : ℚ)) (.leaf (256862959329/125000000000 : ℚ))) (.split (.leaf (2054903687659/1000000000000 : ℚ)) (.leaf (256862962593/125000000000 : ℚ))))))

theorem cover8_tree0074_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0074 (4203/32768 : ℚ) (1051/8192 : ℚ) := by
  unfold cover8_tree0074
  refine tree_all_split_at (8407/65536 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (16813/131072 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (33625/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (67249/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1176_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1177_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (67251/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1178_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1179_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (33627/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (67253/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1180_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1181_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (67255/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1182_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1183_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (16815/131072 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (33629/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (67257/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1184_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1185_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (67259/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1186_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1187_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (33631/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (67261/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1188_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1189_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (67263/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1190_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1191_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0074_checked
#print axioms SmaleRate.Proofs.cover8_tree0074_checked
