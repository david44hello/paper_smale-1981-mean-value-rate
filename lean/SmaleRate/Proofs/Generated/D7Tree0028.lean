/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.DyadicAssembly
import SmaleRate.Proofs.Generated.D7Chunk0017

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover7_tree0028 : BoxTree := (.split (.split (.split (.split (.leaf (2019024278049/1000000000000 : ℚ)) (.leaf (1009512269273/500000000000 : ℚ))) (.split (.leaf (1009512400653/500000000000 : ℚ)) (.leaf (1009512533161/500000000000 : ℚ)))) (.split (.split (.leaf (1009512666797/500000000000 : ℚ)) (.leaf (504756400777/250000000000 : ℚ))) (.split (.leaf (2019025874869/1000000000000 : ℚ)) (.leaf (2019026148893/1000000000000 : ℚ))))) (.split (.split (.split (.leaf (403805285033/200000000000 : ℚ)) (.leaf (504756675919/250000000000 : ℚ))) (.split (.leaf (252378373057/125000000000 : ℚ)) (.leaf (80761090699/40000000000 : ℚ)))) (.split (.split (.leaf (2019027552737/1000000000000 : ℚ)) (.leaf (2019027840261/1000000000000 : ℚ))) (.split (.leaf (504757032507/250000000000 : ℚ)) (.leaf (126189276377/62500000000 : ℚ))))))

theorem cover7_tree0028_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 7 box ∧ (2019/1000 : ℝ) < (box.lower : ℝ)) cover7_tree0028 (565/4096 : ℚ) (283/2048 : ℚ) := by
  unfold cover7_tree0028
  refine tree_all_split_at (1131/8192 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (2261/16384 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (4521/32768 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (9041/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0430_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0431_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (9043/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0432_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0433_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (4523/32768 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (9045/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0434_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0435_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (9047/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0436_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0437_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (2263/16384 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (4525/32768 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (9049/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0438_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0439_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (9051/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0440_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0441_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (4527/32768 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (9053/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0442_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0443_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (9055/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0444_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0445_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover7_tree0028_checked
#print axioms SmaleRate.Proofs.cover7_tree0028_checked
