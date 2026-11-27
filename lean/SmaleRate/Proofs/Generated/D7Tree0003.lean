/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.DyadicAssembly
import SmaleRate.Proofs.Generated.D7Chunk0000

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover7_tree0003 : BoxTree := (.split (.split (.split (.leaf (2020803452753/1000000000000 : ℚ)) (.leaf (505127398803/250000000000 : ℚ))) (.split (.leaf (2020229231511/1000000000000 : ℚ)) (.leaf (2019962151519/1000000000000 : ℚ)))) (.split (.split (.leaf (2019708150329/1000000000000 : ℚ)) (.leaf (403893405623/200000000000 : ℚ))) (.split (.leaf (201923858993/100000000000 : ℚ)) (.leaf (252377830697/125000000000 : ℚ)))))

theorem cover7_tree0003_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 7 box ∧ (2019/1000 : ℝ) < (box.lower : ℝ)) cover7_tree0003 (7/64 : ℚ) (15/128 : ℚ) := by
  unfold cover7_tree0003
  refine tree_all_split_at (29/256 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (57/512 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (113/1024 : ℚ) (by norm_num) ?_ ?_
      · convert cover7_leaf0015_certificate hidentity using 1 <;>
          norm_num [treeAll, BoxEndpointBound]
      · convert cover7_leaf0016_certificate hidentity using 1 <;>
          norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (115/1024 : ℚ) (by norm_num) ?_ ?_
      · convert cover7_leaf0017_certificate hidentity using 1 <;>
          norm_num [treeAll, BoxEndpointBound]
      · convert cover7_leaf0018_certificate hidentity using 1 <;>
          norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (59/512 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (117/1024 : ℚ) (by norm_num) ?_ ?_
      · convert cover7_leaf0019_certificate hidentity using 1 <;>
          norm_num [treeAll, BoxEndpointBound]
      · convert cover7_leaf0020_certificate hidentity using 1 <;>
          norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (119/1024 : ℚ) (by norm_num) ?_ ?_
      · convert cover7_leaf0021_certificate hidentity using 1 <;>
          norm_num [treeAll, BoxEndpointBound]
      · convert cover7_leaf0022_certificate hidentity using 1 <;>
          norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover7_tree0003_checked
#print axioms SmaleRate.Proofs.cover7_tree0003_checked
