/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.DyadicAssembly
import SmaleRate.Proofs.Generated.D8Chunk0002
import SmaleRate.Proofs.Generated.D8Chunk0003

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0006 : BoxTree := (.split (.split (.split (.split (.leaf (2055018530461/1000000000000 : ℚ)) (.leaf (1027507005317/500000000000 : ℚ))) (.split (.leaf (2055009535397/1000000000000 : ℚ)) (.leaf (128437819041/62500000000 : ℚ)))) (.split (.split (.leaf (2055000718413/1000000000000 : ℚ)) (.leaf (1027498188299/500000000000 : ℚ))) (.split (.leaf (2054992079207/1000000000000 : ℚ)) (.leaf (2054987826153/1000000000000 : ℚ))))) (.split (.split (.split (.leaf (2054983617429/1000000000000 : ℚ)) (.leaf (128436215813/62500000000 : ℚ))) (.split (.leaf (102748766641/50000000000 : ℚ)) (.leaf (1027485628421/500000000000 : ℚ)))) (.split (.split (.leaf (1027483612511/500000000000 : ℚ)) (.leaf (102748161867/50000000000 : ℚ))) (.split (.leaf (1027479646871/500000000000 : ℚ)) (.leaf (2054955394209/1000000000000 : ℚ))))))

theorem cover8_tree0006_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0006 (31/256 : ℚ) (125/1024 : ℚ) := by
  unfold cover8_tree0006
  refine tree_all_split_at (249/2048 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (497/4096 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (993/8192 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (1985/16384 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0074_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0075_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (1987/16384 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0076_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0077_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (995/8192 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (1989/16384 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0078_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0079_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (1991/16384 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0080_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0081_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (499/4096 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (997/8192 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (1993/16384 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0082_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0083_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (1995/16384 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0084_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0085_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (999/8192 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (1997/16384 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0086_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0087_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (1999/16384 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0088_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0089_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0006_checked
#print axioms SmaleRate.Proofs.cover8_tree0006_checked
