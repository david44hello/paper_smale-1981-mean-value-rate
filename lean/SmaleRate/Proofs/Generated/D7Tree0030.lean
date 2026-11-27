/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.DyadicAssembly
import SmaleRate.Proofs.Generated.D7Chunk0018
import SmaleRate.Proofs.Generated.D7Chunk0019

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover7_tree0030 : BoxTree := (.split (.split (.split (.split (.leaf (403801775401/200000000000 : ℚ)) (.leaf (403801924011/200000000000 : ℚ))) (.split (.leaf (1009505186021/500000000000 : ℚ)) (.leaf (2019011132941/1000000000000 : ℚ)))) (.split (.split (.leaf (1009505951383/500000000000 : ℚ)) (.leaf (2019012681513/1000000000000 : ℚ))) (.split (.leaf (2019013469167/1000000000000 : ℚ)) (.leaf (2019014265733/1000000000000 : ℚ))))) (.split (.split (.split (.leaf (403803014241/200000000000 : ℚ)) (.leaf (2019015885577/1000000000000 : ℚ))) (.split (.leaf (2019016708859/1000000000000 : ℚ)) (.leaf (1009508770513/500000000000 : ℚ)))) (.split (.split (.leaf (201901838209/100000000000 : ℚ)) (.leaf (2019019232057/1000000000000 : ℚ))) (.split (.leaf (126188755681/62500000000 : ℚ)) (.leaf (2019020958617/1000000000000 : ℚ))))))

theorem cover7_tree0030_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 7 box ∧ (2019/1000 : ℝ) < (box.lower : ℝ)) cover7_tree0030 (71/512 : ℚ) (285/2048 : ℚ) := by
  unfold cover7_tree0030
  refine tree_all_split_at (569/4096 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (1137/8192 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (2273/16384 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (4545/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0465_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0466_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (4547/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0467_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0468_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (2275/16384 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (4549/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0469_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0470_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (4551/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0471_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0472_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (1139/8192 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (2277/16384 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (4553/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0473_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0474_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (4555/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0475_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0476_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (2279/16384 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (4557/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0477_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0478_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (4559/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0479_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0480_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover7_tree0030_checked
#print axioms SmaleRate.Proofs.cover7_tree0030_checked
