/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.DyadicAssembly
import SmaleRate.Proofs.Generated.D8Chunk0057

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0089 : BoxTree := (.split (.split (.split (.split (.leaf (1027451958611/500000000000 : ℚ)) (.leaf (410980810129/200000000000 : ℚ))) (.split (.leaf (513726046169/250000000000 : ℚ)) (.leaf (2054904319341/1000000000000 : ℚ)))) (.split (.split (.leaf (1027452227309/500000000000 : ℚ)) (.leaf (513726147629/250000000000 : ℚ))) (.split (.leaf (2054904727051/1000000000000 : ℚ)) (.leaf (2054904864193/1000000000000 : ℚ))))) (.split (.split (.split (.leaf (410981000393/200000000000 : ℚ)) (.leaf (2054905140337/1000000000000 : ℚ))) (.split (.leaf (2054905279351/1000000000000 : ℚ)) (.leaf (2054905418987/1000000000000 : ℚ)))) (.split (.split (.leaf (82196222369/40000000000 : ℚ)) (.leaf (205490570011/100000000000 : ℚ))) (.split (.leaf (1027452920797/500000000000 : ℚ)) (.leaf (256863247963/125000000000 : ℚ))))))

theorem cover8_tree0089_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0089 (1059/8192 : ℚ) (265/2048 : ℚ) := by
  unfold cover8_tree0089
  refine tree_all_split_at (2119/16384 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (4237/32768 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (8473/65536 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (16945/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1425_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1426_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (16947/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1427_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1428_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (8475/65536 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (16949/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1429_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1430_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (16951/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1431_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1432_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (4239/32768 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (8477/65536 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (16953/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1433_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1434_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (16955/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1435_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1436_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (8479/65536 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (16957/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1437_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1438_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (16959/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1439_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1440_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0089_checked
#print axioms SmaleRate.Proofs.cover8_tree0089_checked
