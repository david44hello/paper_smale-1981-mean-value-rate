/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.DyadicAssembly
import SmaleRate.Proofs.Generated.D8Chunk0038

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0060 : BoxTree := (.split (.split (.split (.split (.leaf (256862712339/125000000000 : ℚ)) (.leaf (2054901702381/1000000000000 : ℚ))) (.split (.leaf (2054901706087/1000000000000 : ℚ)) (.leaf (2054901709847/1000000000000 : ℚ)))) (.split (.split (.leaf (1027450856819/500000000000 : ℚ)) (.leaf (2054901717461/1000000000000 : ℚ))) (.split (.leaf (1027450860671/500000000000 : ℚ)) (.leaf (2054901725241/1000000000000 : ℚ))))) (.split (.split (.split (.leaf (1027450864599/500000000000 : ℚ)) (.leaf (1027450866589/500000000000 : ℚ))) (.split (.leaf (2054901737211/1000000000000 : ℚ)) (.leaf (2054901741269/1000000000000 : ℚ)))) (.split (.split (.leaf (102745087269/50000000000 : ℚ)) (.leaf (205490174953/100000000000 : ℚ))) (.split (.leaf (2054901753719/1000000000000 : ℚ)) (.leaf (2054901757949/1000000000000 : ℚ))))))

theorem cover8_tree0060_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0060 (4189/32768 : ℚ) (2095/16384 : ℚ) := by
  unfold cover8_tree0060
  refine tree_all_split_at (8379/65536 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (16757/131072 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (33513/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (67025/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0952_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0953_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (67027/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0954_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0955_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (33515/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (67029/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0956_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0957_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (67031/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0958_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0959_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (16759/131072 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (33517/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (67033/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0960_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0961_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (67035/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0962_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0963_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (33519/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (67037/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0964_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0965_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (67039/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0966_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0967_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0060_checked
#print axioms SmaleRate.Proofs.cover8_tree0060_checked
