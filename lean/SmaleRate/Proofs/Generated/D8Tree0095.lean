/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.DyadicAssembly
import SmaleRate.Proofs.Generated.D8Chunk0060
import SmaleRate.Proofs.Generated.D8Chunk0061

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0095 : BoxTree := (.split (.split (.split (.split (.leaf (513726808537/250000000000 : ℚ)) (.leaf (2054907641267/1000000000000 : ℚ))) (.split (.leaf (410981610169/200000000000 : ℚ)) (.leaf (2054908462887/1000000000000 : ℚ)))) (.split (.split (.leaf (2054908877377/1000000000000 : ℚ)) (.leaf (205490929433/100000000000 : ℚ))) (.split (.leaf (2054909713729/1000000000000 : ℚ)) (.leaf (256863766949/125000000000 : ℚ))))) (.split (.split (.split (.leaf (2054910559913/1000000000000 : ℚ)) (.leaf (2054910986677/1000000000000 : ℚ))) (.split (.leaf (2054911415907/1000000000000 : ℚ)) (.leaf (256863980947/125000000000 : ℚ)))) (.split (.split (.leaf (2054912281709/1000000000000 : ℚ)) (.leaf (2054912718279/1000000000000 : ℚ))) (.split (.leaf (205491315731/100000000000 : ℚ)) (.leaf (1027456799401/500000000000 : ℚ))))))

theorem cover8_tree0095_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0095 (533/4096 : ℚ) (267/2048 : ℚ) := by
  unfold cover8_tree0095
  refine tree_all_split_at (1067/8192 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (2133/16384 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (4265/32768 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (8529/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1519_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1520_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (8531/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1521_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1522_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (4267/32768 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (8533/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1523_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1524_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (8535/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1525_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1526_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (2135/16384 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (4269/32768 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (8537/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1527_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1528_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (8539/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1529_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1530_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (4271/32768 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (8541/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1531_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1532_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (8543/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1533_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1534_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0095_checked
#print axioms SmaleRate.Proofs.cover8_tree0095_checked
