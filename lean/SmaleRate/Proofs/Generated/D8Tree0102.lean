/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.DyadicAssembly
import SmaleRate.Proofs.Generated.D8Chunk0065
import SmaleRate.Proofs.Generated.D8Chunk0066

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0102 : BoxTree := (.split (.split (.split (.split (.leaf (2054983184079/1000000000000 : ℚ)) (.leaf (513746789353/250000000000 : ℚ))) (.split (.leaf (2054991168169/1000000000000 : ℚ)) (.leaf (2054995216311/1000000000000 : ℚ)))) (.split (.split (.leaf (2054999301819/1000000000000 : ℚ)) (.leaf (2055003424633/1000000000000 : ℚ))) (.split (.leaf (1027503792379/500000000000 : ℚ)) (.leaf (4013694887/1953125000 : ℚ))))) (.split (.split (.split (.leaf (1027508008381/500000000000 : ℚ)) (.leaf (2055020288607/1000000000000 : ℚ))) (.leaf (2054903518583/1000000000000 : ℚ))) (.split (.leaf (256864040213/125000000000 : ℚ)) (.leaf (41098425461/20000000000 : ℚ)))))

theorem cover8_tree0102_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0102 (137/1024 : ℚ) (69/512 : ℚ) := by
  unfold cover8_tree0102
  refine tree_all_split_at (275/2048 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (549/4096 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (1097/8192 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (2193/16384 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1642_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1643_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (2195/16384 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1644_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1645_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (1099/8192 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (2197/16384 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1646_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1647_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (2199/16384 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1648_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1649_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (551/4096 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (1101/8192 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (2201/16384 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1650_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1651_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · convert cover8_leaf1652_certificate hidentity using 1 <;>
          norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (1103/8192 : ℚ) (by norm_num) ?_ ?_
      · convert cover8_leaf1653_certificate hidentity using 1 <;>
          norm_num [treeAll, BoxEndpointBound]
      · convert cover8_leaf1654_certificate hidentity using 1 <;>
          norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0102_checked
#print axioms SmaleRate.Proofs.cover8_tree0102_checked
