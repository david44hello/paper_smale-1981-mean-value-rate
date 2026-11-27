/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.DyadicAssembly
public import SmaleRate.Proofs.Generated.D7Chunk0011
public import SmaleRate.Proofs.Generated.D7Chunk0012

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover7_tree0019 : BoxTree := (.split (.split (.split (.split (.leaf (1009505257721/500000000000 : ℚ)) (.leaf (252376305853/125000000000 : ℚ))) (.split (.leaf (201901038053/100000000000 : ℚ)) (.leaf (2019010316553/1000000000000 : ℚ)))) (.split (.split (.leaf (2019010254907/1000000000000 : ℚ)) (.leaf (50475254889/25000000000 : ℚ))) (.split (.leaf (2019010138521/1000000000000 : ℚ)) (.leaf (1009505041909/500000000000 : ℚ))))) (.split (.split (.split (.leaf (2019010031421/1000000000000 : ℚ)) (.leaf (504752495331/250000000000 : ℚ))) (.split (.leaf (1009504966783/500000000000 : ℚ)) (.leaf (126188118007/62500000000 : ℚ)))) (.split (.split (.leaf (504752461239/250000000000 : ℚ)) (.leaf (1009504902069/500000000000 : ℚ))) (.split (.leaf (2019009765619/1000000000000 : ℚ)) (.leaf (403801945881/200000000000 : ℚ))))))

theorem cover7_tree0019_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 7 box ∧ (2019/1000 : ℝ) < (box.lower : ℝ)) cover7_tree0019 (139/1024 : ℚ) (557/4096 : ℚ) := by
  unfold cover7_tree0019
  refine tree_all_split_at (1113/8192 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (2225/16384 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (4449/32768 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (8897/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0286_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0287_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (8899/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0288_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0289_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (4451/32768 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (8901/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0290_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0291_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (8903/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0292_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0293_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (2227/16384 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (4453/32768 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (8905/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0294_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0295_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (8907/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0296_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0297_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (4455/32768 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (8909/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0298_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0299_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (8911/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0300_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0301_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover7_tree0019_checked
#print axioms SmaleRate.Proofs.cover7_tree0019_checked
