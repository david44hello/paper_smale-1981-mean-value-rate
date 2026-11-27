/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.DyadicAssembly
import SmaleRate.Proofs.Generated.D8Chunk0061
import SmaleRate.Proofs.Generated.D8Chunk0062

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0096 : BoxTree := (.split (.split (.split (.split (.leaf (2054914042727/1000000000000 : ℚ)) (.leaf (513728622279/250000000000 : ℚ))) (.split (.leaf (102745746897/50000000000 : ℚ)) (.leaf (102745769461/50000000000 : ℚ)))) (.split (.split (.leaf (16054030023/7812500000 : ℚ)) (.leaf (2054916299121/1000000000000 : ℚ))) (.split (.leaf (8219667031/4000000000 : ℚ)) (.leaf (1027458609409/500000000000 : ℚ))))) (.split (.split (.split (.leaf (1027458841171/500000000000 : ℚ)) (.leaf (1027459074147/500000000000 : ℚ))) (.split (.leaf (2054918616707/1000000000000 : ℚ)) (.leaf (2054919087567/1000000000000 : ℚ)))) (.split (.split (.leaf (64216236277/31250000000 : ℚ)) (.leaf (2054920036593/1000000000000 : ℚ))) (.split (.leaf (513730128699/250000000000 : ℚ)) (.leaf (2054920995423/1000000000000 : ℚ))))))

theorem cover8_tree0096_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0096 (267/2048 : ℚ) (535/4096 : ℚ) := by
  unfold cover8_tree0096
  refine tree_all_split_at (1069/8192 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (2137/16384 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (4273/32768 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (8545/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1535_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1536_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (8547/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1537_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1538_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (4275/32768 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (8549/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1539_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1540_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (8551/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1541_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1542_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (2139/16384 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (4277/32768 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (8553/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1543_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1544_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (8555/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1545_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1546_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (4279/32768 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (8557/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1547_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1548_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (8559/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1549_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1550_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0096_checked
#print axioms SmaleRate.Proofs.cover8_tree0096_checked
