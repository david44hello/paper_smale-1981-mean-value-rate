/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.DyadicAssembly
import SmaleRate.Proofs.Generated.D8Chunk0000

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0002 : BoxTree := (.split (.split (.split (.leaf (102873091207/50000000000 : ℚ)) (.leaf (1028309252079/500000000000 : ℚ))) (.split (.leaf (1027921136149/500000000000 : ℚ)) (.leaf (2055130767007/1000000000000 : ℚ)))) (.split (.split (.split (.leaf (257100775511/125000000000 : ℚ)) (.leaf (514122266707/250000000000 : ℚ))) (.split (.leaf (257023379853/125000000000 : ℚ)) (.leaf (2055899866743/1000000000000 : ℚ)))) (.split (.split (.leaf (2055627304027/1000000000000 : ℚ)) (.leaf (513842277673/250000000000 : ℚ))) (.split (.leaf (2055125053007/1000000000000 : ℚ)) (.split (.leaf (2056011920677/1000000000000 : ℚ)) (.leaf (1027949257481/500000000000 : ℚ)))))))

theorem cover8_tree0002_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0002 (3/32 : ℚ) (7/64 : ℚ) := by
  unfold cover8_tree0002
  refine tree_all_split_at (13/128 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (25/256 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (49/512 : ℚ) (by norm_num) ?_ ?_
      · convert cover8_leaf0010_certificate hidentity using 1 <;>
          norm_num [treeAll, BoxEndpointBound]
      · convert cover8_leaf0011_certificate hidentity using 1 <;>
          norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (51/512 : ℚ) (by norm_num) ?_ ?_
      · convert cover8_leaf0012_certificate hidentity using 1 <;>
          norm_num [treeAll, BoxEndpointBound]
      · convert cover8_leaf0013_certificate hidentity using 1 <;>
          norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (27/256 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (53/512 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (105/1024 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0014_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0015_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (107/1024 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0016_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0017_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (55/512 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (109/1024 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0018_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0019_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (111/1024 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0020_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · refine tree_all_split_at (223/2048 : ℚ) (by norm_num) ?_ ?_
          · convert cover8_leaf0021_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
          · convert cover8_leaf0022_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0002_checked
#print axioms SmaleRate.Proofs.cover8_tree0002_checked
