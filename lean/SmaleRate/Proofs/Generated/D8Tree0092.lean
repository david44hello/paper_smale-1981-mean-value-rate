/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.DyadicAssembly
import SmaleRate.Proofs.Generated.D8Chunk0058
import SmaleRate.Proofs.Generated.D8Chunk0059

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0092 : BoxTree := (.split (.split (.split (.split (.leaf (205491102127/100000000000 : ℚ)) (.leaf (1027455592231/500000000000 : ℚ))) (.split (.leaf (1027455674133/500000000000 : ℚ)) (.leaf (1027455756339/500000000000 : ℚ)))) (.split (.split (.leaf (1027455838857/500000000000 : ℚ)) (.leaf (102745592169/50000000000 : ℚ))) (.split (.leaf (513728002413/250000000000 : ℚ)) (.leaf (2054912176547/1000000000000 : ℚ))))) (.split (.split (.split (.leaf (513728086011/250000000000 : ℚ)) (.leaf (513728128043/250000000000 : ℚ))) (.split (.leaf (513728170231/250000000000 : ℚ)) (.leaf (2054912850299/1000000000000 : ℚ)))) (.split (.split (.leaf (2054913020273/1000000000000 : ℚ)) (.leaf (128432074429/62500000000 : ℚ))) (.split (.leaf (410982672419/200000000000 : ℚ)) (.leaf (256864191741/125000000000 : ℚ))))))

theorem cover8_tree0092_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0092 (531/4096 : ℚ) (1063/8192 : ℚ) := by
  unfold cover8_tree0092
  refine tree_all_split_at (2125/16384 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (4249/32768 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (8497/65536 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (16993/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1473_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1474_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (16995/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1475_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1476_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (8499/65536 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (16997/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1477_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1478_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (16999/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1479_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1480_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (4251/32768 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (8501/65536 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (17001/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1481_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1482_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (17003/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1483_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1484_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (8503/65536 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (17005/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1485_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1486_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (17007/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1487_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1488_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0092_checked
#print axioms SmaleRate.Proofs.cover8_tree0092_checked
