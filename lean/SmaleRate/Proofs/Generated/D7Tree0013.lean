/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.DyadicAssembly
import SmaleRate.Proofs.Generated.D7Chunk0007
import SmaleRate.Proofs.Generated.D7Chunk0008

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover7_tree0013 : BoxTree := (.split (.split (.split (.split (.leaf (2019027963057/1000000000000 : ℚ)) (.leaf (403805533961/200000000000 : ℚ))) (.split (.leaf (50475684473/25000000000 : ℚ)) (.leaf (2019027090389/1000000000000 : ℚ)))) (.split (.split (.leaf (3943411727/1953125000 : ℚ)) (.leaf (201902652041/100000000000 : ℚ))) (.split (.leaf (504756559743/250000000000 : ℚ)) (.leaf (201902595989/100000000000 : ℚ))))) (.split (.split (.split (.leaf (403805136631/200000000000 : ℚ)) (.leaf (2019025408793/1000000000000 : ℚ))) (.split (.leaf (504756284193/250000000000 : ℚ)) (.leaf (1009512433563/500000000000 : ℚ)))) (.split (.split (.leaf (2019024599827/1000000000000 : ℚ)) (.leaf (2019024334891/1000000000000 : ℚ))) (.split (.leaf (403804814463/200000000000 : ℚ)) (.leaf (2019023812089/1000000000000 : ℚ))))))

theorem cover7_tree0013_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 7 box ∧ (2019/1000 : ℝ) < (box.lower : ℝ)) cover7_tree0013 (275/2048 : ℚ) (551/4096 : ℚ) := by
  unfold cover7_tree0013
  refine tree_all_split_at (1101/8192 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (2201/16384 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (4401/32768 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (8801/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0190_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0191_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (8803/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0192_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0193_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (4403/32768 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (8805/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0194_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0195_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (8807/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0196_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0197_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (2203/16384 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (4405/32768 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (8809/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0198_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0199_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (8811/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0200_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0201_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (4407/32768 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (8813/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0202_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0203_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (8815/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0204_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0205_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover7_tree0013_checked
#print axioms SmaleRate.Proofs.cover7_tree0013_checked
