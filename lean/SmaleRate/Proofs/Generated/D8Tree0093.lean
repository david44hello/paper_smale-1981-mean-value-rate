/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.DyadicAssembly
import SmaleRate.Proofs.Generated.D8Chunk0059
import SmaleRate.Proofs.Generated.D8Chunk0060

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0093 : BoxTree := (.split (.split (.split (.split (.leaf (1027456853191/500000000000 : ℚ)) (.leaf (1027456939727/500000000000 : ℚ))) (.split (.leaf (256864256643/125000000000 : ℚ)) (.leaf (2054914227437/1000000000000 : ℚ)))) (.split (.split (.leaf (2054914402369/1000000000000 : ℚ)) (.leaf (2054914577897/1000000000000 : ℚ))) (.split (.leaf (1027457377033/500000000000 : ℚ)) (.leaf (2054914930841/1000000000000 : ℚ))))) (.split (.split (.split (.leaf (513728777057/250000000000 : ℚ)) (.leaf (2054915286237/1000000000000 : ℚ))) (.split (.leaf (2054915464861/1000000000000 : ℚ)) (.leaf (1027457822053/500000000000 : ℚ)))) (.split (.leaf (2054900326747/1000000000000 : ℚ)) (.leaf (41098013791/20000000000 : ℚ)))))

theorem cover8_tree0093_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0093 (1063/8192 : ℚ) (133/1024 : ℚ) := by
  unfold cover8_tree0093
  refine tree_all_split_at (2127/16384 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (4253/32768 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (8505/65536 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (17009/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1489_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1490_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (17011/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1491_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1492_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (8507/65536 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (17013/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1493_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1494_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (17015/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1495_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1496_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (4255/32768 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (8509/65536 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (17017/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1497_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1498_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (17019/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1499_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1500_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (8511/65536 : ℚ) (by norm_num) ?_ ?_
      · convert cover8_leaf1501_certificate hidentity using 1 <;>
          norm_num [treeAll, BoxEndpointBound]
      · convert cover8_leaf1502_certificate hidentity using 1 <;>
          norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0093_checked
#print axioms SmaleRate.Proofs.cover8_tree0093_checked
