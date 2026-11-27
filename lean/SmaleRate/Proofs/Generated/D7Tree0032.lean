/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.DyadicAssembly
import SmaleRate.Proofs.Generated.D7Chunk0019
import SmaleRate.Proofs.Generated.D7Chunk0020

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover7_tree0032 : BoxTree := (.split (.split (.split (.split (.leaf (1009518532883/500000000000 : ℚ)) (.leaf (1009519046401/500000000000 : ℚ))) (.split (.leaf (1009519564331/500000000000 : ℚ)) (.leaf (40380803467/20000000000 : ℚ)))) (.split (.split (.leaf (2019041226831/1000000000000 : ℚ)) (.leaf (1009521144567/500000000000 : ℚ))) (.split (.leaf (252380420029/125000000000 : ℚ)) (.leaf (1009522220067/500000000000 : ℚ))))) (.split (.split (.split (.leaf (504761382211/250000000000 : ℚ)) (.leaf (403809325267/200000000000 : ℚ))) (.split (.leaf (504761933157/250000000000 : ℚ)) (.leaf (1009524423849/500000000000 : ℚ)))) (.split (.split (.leaf (1009524985787/500000000000 : ℚ)) (.leaf (2019051104213/1000000000000 : ℚ))) (.split (.leaf (504763061411/250000000000 : ℚ)) (.leaf (1009526697923/500000000000 : ℚ))))))

theorem cover7_tree0032_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 7 box ∧ (2019/1000 : ℝ) < (box.lower : ℝ)) cover7_tree0032 (143/1024 : ℚ) (287/2048 : ℚ) := by
  unfold cover7_tree0032
  refine tree_all_split_at (573/4096 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (1145/8192 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (2289/16384 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (4577/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0497_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0498_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (4579/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0499_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0500_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (2291/16384 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (4581/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0501_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0502_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (4583/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0503_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0504_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (1147/8192 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (2293/16384 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (4585/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0505_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0506_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (4587/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0507_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0508_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (2295/16384 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (4589/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0509_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0510_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (4591/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0511_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0512_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover7_tree0032_checked
#print axioms SmaleRate.Proofs.cover7_tree0032_checked
