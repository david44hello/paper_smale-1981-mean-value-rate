/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.DyadicAssembly
import SmaleRate.Proofs.Generated.D8Chunk0064
import SmaleRate.Proofs.Generated.D8Chunk0065

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0100 : BoxTree := (.split (.split (.split (.split (.split (.leaf (1027468658467/500000000000 : ℚ)) (.leaf (513734670661/250000000000 : ℚ))) (.split (.leaf (1027470028987/500000000000 : ℚ)) (.leaf (128433840181/62500000000 : ℚ)))) (.split (.split (.leaf (2054942837413/1000000000000 : ℚ)) (.leaf (410988848307/200000000000 : ℚ))) (.split (.leaf (2054945655239/1000000000000 : ℚ)) (.leaf (1027473539261/500000000000 : ℚ))))) (.split (.split (.split (.leaf (102747425569/50000000000 : ℚ)) (.leaf (82197998153/40000000000 : ℚ))) (.split (.leaf (2054951405841/1000000000000 : ℚ)) (.leaf (25686910843/12500000000 : ℚ)))) (.split (.split (.leaf (513738584649/250000000000 : ℚ)) (.leaf (2054955819311/1000000000000 : ℚ))) (.split (.leaf (102747865479/50000000000 : ℚ)) (.leaf (205495880941/100000000000 : ℚ)))))) (.split (.split (.split (.split (.leaf (32108754981/15625000000 : ℚ)) (.leaf (2054961837707/1000000000000 : ℚ))) (.leaf (205490219259/100000000000 : ℚ))) (.split (.leaf (513726324277/250000000000 : ℚ)) (.leaf (256863554967/125000000000 : ℚ)))) (.split (.split (.leaf (410982324087/200000000000 : ℚ)) (.leaf (256864354899/125000000000 : ℚ))) (.split (.leaf (2054918095959/1000000000000 : ℚ)) (.leaf (2054921390709/1000000000000 : ℚ))))))

theorem cover8_tree0100_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0100 (135/1024 : ℚ) (17/128 : ℚ) := by
  unfold cover8_tree0100
  refine tree_all_split_at (271/2048 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (541/4096 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (1081/8192 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (2161/16384 : ℚ) (by norm_num) ?_ ?_
        · refine tree_all_split_at (4321/32768 : ℚ) (by norm_num) ?_ ?_
          · convert cover8_leaf1601_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
          · convert cover8_leaf1602_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
        · refine tree_all_split_at (4323/32768 : ℚ) (by norm_num) ?_ ?_
          · convert cover8_leaf1603_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
          · convert cover8_leaf1604_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (2163/16384 : ℚ) (by norm_num) ?_ ?_
        · refine tree_all_split_at (4325/32768 : ℚ) (by norm_num) ?_ ?_
          · convert cover8_leaf1605_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
          · convert cover8_leaf1606_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
        · refine tree_all_split_at (4327/32768 : ℚ) (by norm_num) ?_ ?_
          · convert cover8_leaf1607_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
          · convert cover8_leaf1608_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (1083/8192 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (2165/16384 : ℚ) (by norm_num) ?_ ?_
        · refine tree_all_split_at (4329/32768 : ℚ) (by norm_num) ?_ ?_
          · convert cover8_leaf1609_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
          · convert cover8_leaf1610_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
        · refine tree_all_split_at (4331/32768 : ℚ) (by norm_num) ?_ ?_
          · convert cover8_leaf1611_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
          · convert cover8_leaf1612_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (2167/16384 : ℚ) (by norm_num) ?_ ?_
        · refine tree_all_split_at (4333/32768 : ℚ) (by norm_num) ?_ ?_
          · convert cover8_leaf1613_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
          · convert cover8_leaf1614_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
        · refine tree_all_split_at (4335/32768 : ℚ) (by norm_num) ?_ ?_
          · convert cover8_leaf1615_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
          · convert cover8_leaf1616_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (543/4096 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (1085/8192 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (2169/16384 : ℚ) (by norm_num) ?_ ?_
        · refine tree_all_split_at (4337/32768 : ℚ) (by norm_num) ?_ ?_
          · convert cover8_leaf1617_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
          · convert cover8_leaf1618_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1619_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (2171/16384 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1620_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1621_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (1087/8192 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (2173/16384 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1622_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1623_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (2175/16384 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1624_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1625_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0100_checked
#print axioms SmaleRate.Proofs.cover8_tree0100_checked
