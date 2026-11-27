/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.DyadicAssembly
import SmaleRate.Proofs.Generated.D8Chunk0065

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0101 : BoxTree := (.split (.split (.split (.split (.leaf (2054924723413/1000000000000 : ℚ)) (.leaf (1027464047027/500000000000 : ℚ))) (.split (.leaf (2054931502587/1000000000000 : ℚ)) (.leaf (102746747449/50000000000 : ℚ)))) (.split (.split (.leaf (410987686641/200000000000 : ℚ)) (.leaf (1027470977621/500000000000 : ℚ))) (.split (.leaf (513736378763/250000000000 : ℚ)) (.leaf (1027474556301/500000000000 : ℚ))))) (.split (.split (.split (.leaf (1027476373929/500000000000 : ℚ)) (.leaf (513739105203/250000000000 : ℚ))) (.split (.leaf (1027480065709/500000000000 : ℚ)) (.leaf (1027481939821/500000000000 : ℚ)))) (.split (.split (.leaf (410993533091/200000000000 : ℚ)) (.leaf (1027485744423/500000000000 : ℚ))) (.split (.leaf (2054975349767/1000000000000 : ℚ)) (.leaf (2054979248187/1000000000000 : ℚ))))))

theorem cover8_tree0101_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0101 (17/128 : ℚ) (137/1024 : ℚ) := by
  unfold cover8_tree0101
  refine tree_all_split_at (273/2048 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (545/4096 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (1089/8192 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (2177/16384 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1626_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1627_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (2179/16384 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1628_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1629_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (1091/8192 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (2181/16384 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1630_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1631_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (2183/16384 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1632_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1633_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (547/4096 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (1093/8192 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (2185/16384 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1634_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1635_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (2187/16384 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1636_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1637_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (1095/8192 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (2189/16384 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1638_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1639_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (2191/16384 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1640_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1641_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0101_checked
#print axioms SmaleRate.Proofs.cover8_tree0101_checked
