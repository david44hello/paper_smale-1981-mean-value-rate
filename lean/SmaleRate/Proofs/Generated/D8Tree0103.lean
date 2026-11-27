/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.DyadicAssembly
import SmaleRate.Proofs.Generated.D8Chunk0066

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0103 : BoxTree := (.split (.split (.split (.split (.leaf (2054930372411/1000000000000 : ℚ)) (.leaf (2054939619537/1000000000000 : ℚ))) (.split (.leaf (2054949014213/1000000000000 : ℚ)) (.leaf (410991711237/200000000000 : ℚ)))) (.split (.split (.leaf (2054968245233/1000000000000 : ℚ)) (.leaf (2054978081131/1000000000000 : ℚ))) (.split (.leaf (1027494031821/500000000000 : ℚ)) (.leaf (513749548137/250000000000 : ℚ))))) (.split (.split (.split (.leaf (2055008467617/1000000000000 : ℚ)) (.leaf (2055018888611/1000000000000 : ℚ))) (.split (.leaf (1027514727659/500000000000 : ℚ)) (.leaf (32110002617/15625000000 : ℚ)))) (.split (.split (.leaf (1027525512461/500000000000 : ℚ)) (.leaf (16440496219/8000000000 : ℚ))) (.split (.leaf (1027536587319/500000000000 : ℚ)) (.leaf (411016893293/200000000000 : ℚ))))))

theorem cover8_tree0103_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0103 (69/512 : ℚ) (35/256 : ℚ) := by
  unfold cover8_tree0103
  refine tree_all_split_at (139/1024 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (277/2048 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (553/4096 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (1105/8192 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1655_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1656_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (1107/8192 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1657_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1658_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (555/4096 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (1109/8192 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1659_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1660_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (1111/8192 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1661_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1662_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (279/2048 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (557/4096 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (1113/8192 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1663_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1664_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (1115/8192 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1665_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1666_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (559/4096 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (1117/8192 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1667_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1668_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (1119/8192 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1669_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1670_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0103_checked
#print axioms SmaleRate.Proofs.cover8_tree0103_checked
