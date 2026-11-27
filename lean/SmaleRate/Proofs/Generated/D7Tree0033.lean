/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.DyadicAssembly
import SmaleRate.Proofs.Generated.D7Chunk0020

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover7_tree0033 : BoxTree := (.split (.split (.split (.split (.leaf (252381819353/125000000000 : ℚ)) (.leaf (2019055722563/1000000000000 : ℚ))) (.split (.leaf (2019056899071/1000000000000 : ℚ)) (.leaf (2019058084329/1000000000000 : ℚ)))) (.split (.split (.leaf (63095602449/31250000000 : ℚ)) (.leaf (100953024057/50000000000 : ℚ))) (.leaf (2019001296997/1000000000000 : ℚ)))) (.split (.split (.leaf (1009501881863/500000000000 : ℚ)) (.leaf (2019006265411/1000000000000 : ℚ))) (.split (.leaf (1009504401011/500000000000 : ℚ)) (.leaf (2019011373523/1000000000000 : ℚ)))))

theorem cover7_tree0033_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 7 box ∧ (2019/1000 : ℝ) < (box.lower : ℝ)) cover7_tree0033 (287/2048 : ℚ) (9/64 : ℚ) := by
  unfold cover7_tree0033
  refine tree_all_split_at (575/4096 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (1149/8192 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (2297/16384 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (4593/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0513_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0514_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (4595/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0515_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0516_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (2299/16384 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (4597/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0517_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0518_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · convert cover7_leaf0519_certificate hidentity using 1 <;>
          norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (1151/8192 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (2301/16384 : ℚ) (by norm_num) ?_ ?_
      · convert cover7_leaf0520_certificate hidentity using 1 <;>
          norm_num [treeAll, BoxEndpointBound]
      · convert cover7_leaf0521_certificate hidentity using 1 <;>
          norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (2303/16384 : ℚ) (by norm_num) ?_ ?_
      · convert cover7_leaf0522_certificate hidentity using 1 <;>
          norm_num [treeAll, BoxEndpointBound]
      · convert cover7_leaf0523_certificate hidentity using 1 <;>
          norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover7_tree0033_checked
#print axioms SmaleRate.Proofs.cover7_tree0033_checked
