/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.DyadicAssembly
import SmaleRate.Proofs.Generated.D8Chunk0058

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0091 : BoxTree := (.split (.split (.split (.split (.leaf (1027454247273/500000000000 : ℚ)) (.leaf (1027454323913/500000000000 : ℚ))) (.split (.leaf (513727200431/250000000000 : ℚ)) (.leaf (513727239059/250000000000 : ℚ)))) (.split (.split (.leaf (256863638921/125000000000 : ℚ)) (.leaf (2054909267127/1000000000000 : ℚ))) (.split (.leaf (2054909423503/1000000000000 : ℚ)) (.leaf (1027454790243/500000000000 : ℚ))))) (.split (.split (.split (.leaf (2054909738103/1000000000000 : ℚ)) (.leaf (513727474081/250000000000 : ℚ))) (.split (.leaf (513727513797/250000000000 : ℚ)) (.leaf (513727553663/250000000000 : ℚ)))) (.split (.split (.leaf (2054910374739/1000000000000 : ℚ)) (.leaf (410982107089/200000000000 : ℚ))) (.split (.leaf (2054910696771/1000000000000 : ℚ)) (.leaf (2054910858723/1000000000000 : ℚ))))))

theorem cover8_tree0091_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0091 (1061/8192 : ℚ) (531/4096 : ℚ) := by
  unfold cover8_tree0091
  refine tree_all_split_at (2123/16384 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (4245/32768 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (8489/65536 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (16977/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1457_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1458_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (16979/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1459_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1460_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (8491/65536 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (16981/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1461_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1462_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (16983/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1463_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1464_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (4247/32768 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (8493/65536 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (16985/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1465_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1466_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (16987/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1467_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1468_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (8495/65536 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (16989/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1469_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1470_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (16991/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1471_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1472_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0091_checked
#print axioms SmaleRate.Proofs.cover8_tree0091_checked
