/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.DyadicAssembly
import SmaleRate.Proofs.Generated.D8Chunk0067
import SmaleRate.Proofs.Generated.D8Chunk0068

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0105 : BoxTree := (.split (.split (.split (.split (.split (.split (.leaf (411060388257/200000000000 : ℚ)) (.leaf (513833626099/250000000000 : ℚ))) (.split (.leaf (2055367614119/1000000000000 : ℚ)) (.leaf (51385031721/25000000000 : ℚ)))) (.split (.leaf (1027484222137/500000000000 : ℚ)) (.leaf (513759881389/250000000000 : ℚ)))) (.split (.split (.leaf (2055112754267/1000000000000 : ℚ)) (.leaf (2055188117849/1000000000000 : ℚ))) (.split (.leaf (64227050119/31250000000 : ℚ)) (.leaf (1027672599921/500000000000 : ℚ))))) (.split (.split (.split (.leaf (256928361717/125000000000 : ℚ)) (.leaf (205551067339/100000000000 : ℚ))) (.split (.leaf (1027798263423/500000000000 : ℚ)) (.leaf (2055684442221/1000000000000 : ℚ)))) (.split (.split (.leaf (2055774407803/1000000000000 : ℚ)) (.leaf (2055866411959/1000000000000 : ℚ))) (.leaf (2055052801259/1000000000000 : ℚ))))) (.split (.split (.split (.leaf (2055250800209/1000000000000 : ℚ)) (.leaf (1027728361901/500000000000 : ℚ))) (.split (.leaf (2055670484759/1000000000000 : ℚ)) (.leaf (1027945998699/500000000000 : ℚ)))) (.split (.split (.leaf (2056121177691/1000000000000 : ℚ)) (.leaf (1028178971567/500000000000 : ℚ))) (.split (.leaf (2056602212787/1000000000000 : ℚ)) (.leaf (1028426953583/500000000000 : ℚ))))))

theorem cover8_tree0105_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0105 (9/64 : ℚ) (5/32 : ℚ) := by
  unfold cover8_tree0105
  refine tree_all_split_at (19/128 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (37/256 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (73/512 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (145/1024 : ℚ) (by norm_num) ?_ ?_
        · refine tree_all_split_at (289/2048 : ℚ) (by norm_num) ?_ ?_
          · refine tree_all_split_at (577/4096 : ℚ) (by norm_num) ?_ ?_
            · convert cover8_leaf1689_certificate hidentity using 1 <;>
                norm_num [treeAll, BoxEndpointBound]
            · convert cover8_leaf1690_certificate hidentity using 1 <;>
                norm_num [treeAll, BoxEndpointBound]
          · refine tree_all_split_at (579/4096 : ℚ) (by norm_num) ?_ ?_
            · convert cover8_leaf1691_certificate hidentity using 1 <;>
                norm_num [treeAll, BoxEndpointBound]
            · convert cover8_leaf1692_certificate hidentity using 1 <;>
                norm_num [treeAll, BoxEndpointBound]
        · refine tree_all_split_at (291/2048 : ℚ) (by norm_num) ?_ ?_
          · convert cover8_leaf1693_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
          · convert cover8_leaf1694_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (147/1024 : ℚ) (by norm_num) ?_ ?_
        · refine tree_all_split_at (293/2048 : ℚ) (by norm_num) ?_ ?_
          · convert cover8_leaf1695_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
          · convert cover8_leaf1696_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
        · refine tree_all_split_at (295/2048 : ℚ) (by norm_num) ?_ ?_
          · convert cover8_leaf1697_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
          · convert cover8_leaf1698_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (75/512 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (149/1024 : ℚ) (by norm_num) ?_ ?_
        · refine tree_all_split_at (297/2048 : ℚ) (by norm_num) ?_ ?_
          · convert cover8_leaf1699_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
          · convert cover8_leaf1700_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
        · refine tree_all_split_at (299/2048 : ℚ) (by norm_num) ?_ ?_
          · convert cover8_leaf1701_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
          · convert cover8_leaf1702_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (151/1024 : ℚ) (by norm_num) ?_ ?_
        · refine tree_all_split_at (301/2048 : ℚ) (by norm_num) ?_ ?_
          · convert cover8_leaf1703_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
          · convert cover8_leaf1704_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1705_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (39/256 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (77/512 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (153/1024 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1706_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1707_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (155/1024 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1708_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1709_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (79/512 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (157/1024 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1710_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1711_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (159/1024 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1712_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1713_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0105_checked
#print axioms SmaleRate.Proofs.cover8_tree0105_checked
