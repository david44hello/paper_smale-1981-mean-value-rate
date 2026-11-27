/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.DyadicAssembly
public import SmaleRate.Proofs.Generated.D8Chunk0040
public import SmaleRate.Proofs.Generated.D8Chunk0041

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0064 : BoxTree := (.split (.split (.split (.split (.leaf (410980402699/200000000000 : ℚ)) (.leaf (1027451009853/500000000000 : ℚ))) (.split (.leaf (1027451012979/500000000000 : ℚ)) (.leaf (1027451016121/500000000000 : ℚ)))) (.split (.split (.leaf (2054902038547/1000000000000 : ℚ)) (.leaf (2054902044917/1000000000000 : ℚ))) (.split (.leaf (2054902051321/1000000000000 : ℚ)) (.leaf (12843137861/6250000000 : ℚ))))) (.split (.split (.split (.leaf (2054902064243/1000000000000 : ℚ)) (.leaf (1027451035381/500000000000 : ℚ))) (.split (.leaf (2054902077337/1000000000000 : ℚ)) (.leaf (2054902083929/1000000000000 : ℚ)))) (.split (.split (.leaf (2054902090569/1000000000000 : ℚ)) (.leaf (2054902097259/1000000000000 : ℚ))) (.split (.leaf (513725525993/250000000000 : ℚ)) (.leaf (1027451055361/500000000000 : ℚ))))))

theorem cover8_tree0064_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0064 (4193/32768 : ℚ) (2097/16384 : ℚ) := by
  unfold cover8_tree0064
  refine tree_all_split_at (8387/65536 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (16773/131072 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (33545/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (67089/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1016_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1017_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (67091/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1018_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1019_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (33547/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (67093/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1020_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1021_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (67095/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1022_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1023_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (16775/131072 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (33549/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (67097/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1024_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1025_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (67099/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1026_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1027_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (33551/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (67101/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1028_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1029_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (67103/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf1030_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf1031_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0064_checked
#print axioms SmaleRate.Proofs.cover8_tree0064_checked
