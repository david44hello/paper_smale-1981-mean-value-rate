/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.DyadicAssembly
import SmaleRate.Proofs.Generated.D8Chunk0055
import SmaleRate.Proofs.Generated.D8Chunk0056

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0087 : BoxTree := (.split (.split (.split (.split (.split (.leaf (2054907758837/1000000000000 : ℚ)) (.leaf (6421586923/3125000000 : ℚ))) (.leaf (2054900090013/1000000000000 : ℚ))) (.split (.leaf (1027450102057/500000000000 : ℚ)) (.leaf (2054900318851/1000000000000 : ℚ)))) (.split (.split (.leaf (102745021711/50000000000 : ℚ)) (.leaf (513725137553/250000000000 : ℚ))) (.split (.leaf (256862583351/125000000000 : ℚ)) (.leaf (1027450392027/500000000000 : ℚ))))) (.split (.split (.split (.leaf (2054900901903/1000000000000 : ℚ)) (.leaf (513725255093/250000000000 : ℚ))) (.split (.leaf (82196045579/40000000000 : ℚ)) (.leaf (2054901259199/1000000000000 : ℚ)))) (.split (.split (.leaf (2054901379549/1000000000000 : ℚ)) (.leaf (1027450750259/500000000000 : ℚ))) (.split (.leaf (1027450811053/500000000000 : ℚ)) (.leaf (513725436081/250000000000 : ℚ))))))

theorem cover8_tree0087_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0087 (1057/8192 : ℚ) (529/4096 : ℚ) := by
  unfold cover8_tree0087
  refine tree_all_split_at (2115/16384 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (4229/32768 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (8457/65536 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (16913/131072 : ℚ) (by norm_num) ?_ ?_
        · refine tree_all_split_at (33825/262144 : ℚ) (by norm_num) ?_ ?_
          · convert cover8_leaf1392_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
          · convert cover8_leaf1393_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1394_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (16915/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1395_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1396_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (8459/65536 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (16917/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1397_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1398_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (16919/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1399_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1400_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (4231/32768 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (8461/65536 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (16921/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1401_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1402_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (16923/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1403_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1404_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (8463/65536 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (16925/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1405_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1406_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (16927/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1407_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1408_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0087_checked
#print axioms SmaleRate.Proofs.cover8_tree0087_checked
