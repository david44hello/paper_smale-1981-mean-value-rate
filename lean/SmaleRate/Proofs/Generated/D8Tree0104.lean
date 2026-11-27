/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.DyadicAssembly
import SmaleRate.Proofs.Generated.D8Chunk0066
import SmaleRate.Proofs.Generated.D8Chunk0067

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0104 : BoxTree := (.split (.split (.split (.split (.split (.leaf (1027547951327/500000000000 : ℚ)) (.leaf (2055107482971/1000000000000 : ℚ))) (.split (.leaf (256889900899/125000000000 : ℚ)) (.leaf (2055131075091/1000000000000 : ℚ)))) (.split (.leaf (1027452191471/500000000000 : ℚ)) (.leaf (256866139751/125000000000 : ℚ)))) (.split (.split (.leaf (410990884667/200000000000 : ℚ)) (.leaf (128436268573/62500000000 : ℚ))) (.split (.leaf (1027503368901/500000000000 : ℚ)) (.leaf (2055033743487/1000000000000 : ℚ))))) (.split (.split (.split (.leaf (1027530656249/500000000000 : ℚ)) (.leaf (2055089443143/1000000000000 : ℚ))) (.split (.leaf (2055118133707/1000000000000 : ℚ)) (.leaf (256893422813/125000000000 : ℚ)))) (.split (.split (.leaf (802803589/390625000 : ℚ)) (.leaf (2055207548059/1000000000000 : ℚ))) (.split (.leaf (1027619230741/500000000000 : ℚ)) (.leaf (2055269926429/1000000000000 : ℚ))))))

theorem cover8_tree0104_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0104 (35/256 : ℚ) (9/64 : ℚ) := by
  unfold cover8_tree0104
  refine tree_all_split_at (71/512 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (141/1024 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (281/2048 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (561/4096 : ℚ) (by norm_num) ?_ ?_
        · refine tree_all_split_at (1121/8192 : ℚ) (by norm_num) ?_ ?_
          · convert cover8_leaf1671_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
          · convert cover8_leaf1672_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
        · refine tree_all_split_at (1123/8192 : ℚ) (by norm_num) ?_ ?_
          · convert cover8_leaf1673_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
          · convert cover8_leaf1674_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (563/4096 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1675_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1676_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (283/2048 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (565/4096 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1677_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1678_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (567/4096 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1679_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1680_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (143/1024 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (285/2048 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (569/4096 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1681_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1682_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (571/4096 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1683_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1684_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (287/2048 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (573/4096 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1685_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1686_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (575/4096 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1687_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1688_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0104_checked
#print axioms SmaleRate.Proofs.cover8_tree0104_checked
