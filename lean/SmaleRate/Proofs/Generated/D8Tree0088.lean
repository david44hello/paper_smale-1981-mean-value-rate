/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.DyadicAssembly
import SmaleRate.Proofs.Generated.D8Chunk0056

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0088 : BoxTree := (.split (.split (.split (.split (.leaf (2054901867157/1000000000000 : ℚ)) (.leaf (2054901990631/1000000000000 : ℚ))) (.split (.leaf (2054902114711/1000000000000 : ℚ)) (.leaf (256862779927/125000000000 : ℚ)))) (.split (.split (.leaf (2054902364741/1000000000000 : ℚ)) (.leaf (1027451245349/500000000000 : ℚ))) (.split (.leaf (2054902617271/1000000000000 : ℚ)) (.leaf (1027451372237/500000000000 : ℚ))))) (.split (.split (.split (.leaf (51372571807/25000000000 : ℚ)) (.leaf (2054903000731/1000000000000 : ℚ))) (.split (.leaf (1027451564893/500000000000 : ℚ)) (.leaf (513725814867/250000000000 : ℚ)))) (.split (.split (.leaf (2054903389787/1000000000000 : ℚ)) (.leaf (513725880179/250000000000 : ℚ))) (.split (.leaf (1027451826133/500000000000 : ℚ)) (.leaf (1027451892213/500000000000 : ℚ))))))

theorem cover8_tree0088_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0088 (529/4096 : ℚ) (1059/8192 : ℚ) := by
  unfold cover8_tree0088
  refine tree_all_split_at (2117/16384 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (4233/32768 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (8465/65536 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (16929/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1409_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1410_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (16931/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1411_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1412_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (8467/65536 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (16933/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1413_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1414_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (16935/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1415_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1416_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (4235/32768 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (8469/65536 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (16937/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1417_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1418_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (16939/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1419_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1420_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (8471/65536 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (16941/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1421_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1422_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (16943/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1423_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1424_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0088_checked
#print axioms SmaleRate.Proofs.cover8_tree0088_checked
