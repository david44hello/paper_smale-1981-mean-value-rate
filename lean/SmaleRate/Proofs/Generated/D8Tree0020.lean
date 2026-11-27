/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.DyadicAssembly
import SmaleRate.Proofs.Generated.D8Chunk0012

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0020 : BoxTree := (.split (.split (.split (.split (.leaf (1027451561851/500000000000 : ℚ)) (.leaf (205490299281/100000000000 : ℚ))) (.split (.leaf (256862857823/125000000000 : ℚ)) (.leaf (513725683249/250000000000 : ℚ)))) (.split (.split (.leaf (1027451302029/500000000000 : ℚ)) (.leaf (256862809471/125000000000 : ℚ))) (.split (.leaf (513725587029/250000000000 : ℚ)) (.leaf (2054902221131/1000000000000 : ℚ))))) (.split (.split (.split (.leaf (1027451047397/500000000000 : ℚ)) (.leaf (410980393819/200000000000 : ℚ))) (.split (.leaf (2054901844043/1000000000000 : ℚ)) (.leaf (2054901719657/1000000000000 : ℚ)))) (.split (.split (.leaf (205490159591/100000000000 : ℚ)) (.leaf (513725368203/250000000000 : ℚ))) (.split (.leaf (2054901350359/1000000000000 : ℚ)) (.leaf (25686265357/12500000000 : ℚ))))))

theorem cover8_tree0020_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0020 (1033/8192 : ℚ) (517/4096 : ℚ) := by
  unfold cover8_tree0020
  refine tree_all_split_at (2067/16384 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (4133/32768 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (8265/65536 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (16529/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0302_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0303_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (16531/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0304_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0305_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (8267/65536 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (16533/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0306_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0307_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (16535/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0308_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0309_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (4135/32768 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (8269/65536 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (16537/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0310_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0311_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (16539/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0312_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0313_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (8271/65536 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (16541/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0314_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0315_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (16543/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0316_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0317_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0020_checked
#print axioms SmaleRate.Proofs.cover8_tree0020_checked
