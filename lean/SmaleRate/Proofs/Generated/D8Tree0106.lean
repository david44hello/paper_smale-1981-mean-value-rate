/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.DyadicAssembly
import SmaleRate.Proofs.Generated.D8Chunk0068

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0106 : BoxTree := (.split (.split (.split (.split (.leaf (1027685540413/500000000000 : ℚ)) (.leaf (1027962336719/500000000000 : ℚ))) (.split (.leaf (1028253217047/500000000000 : ℚ)) (.leaf (1028557899233/500000000000 : ℚ)))) (.split (.split (.leaf (658480711/320000000 : ℚ)) (.leaf (2058415178463/1000000000000 : ℚ))) (.leaf (1027899759743/500000000000 : ℚ)))) (.split (.split (.leaf (1028650169761/500000000000 : ℚ)) (.leaf (2058897616073/1000000000000 : ℚ))) (.split (.leaf (2060587974927/1000000000000 : ℚ)) (.leaf (515592063189/250000000000 : ℚ)))))

theorem cover8_tree0106_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0106 (5/32 : ℚ) (3/16 : ℚ) := by
  unfold cover8_tree0106
  refine tree_all_split_at (11/64 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (21/128 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (41/256 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (81/512 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1714_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1715_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (83/512 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1716_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1717_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (43/256 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (85/512 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1718_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1719_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · convert cover8_leaf1720_certificate hidentity using 1 <;>
          norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (23/128 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (45/256 : ℚ) (by norm_num) ?_ ?_
      · convert cover8_leaf1721_certificate hidentity using 1 <;>
          norm_num [treeAll, BoxEndpointBound]
      · convert cover8_leaf1722_certificate hidentity using 1 <;>
          norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (47/256 : ℚ) (by norm_num) ?_ ?_
      · convert cover8_leaf1723_certificate hidentity using 1 <;>
          norm_num [treeAll, BoxEndpointBound]
      · convert cover8_leaf1724_certificate hidentity using 1 <;>
          norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0106_checked
#print axioms SmaleRate.Proofs.cover8_tree0106_checked
