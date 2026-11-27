/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.DyadicAssembly
public import SmaleRate.Proofs.Generated.D8Chunk0032
public import SmaleRate.Proofs.Generated.D8Chunk0033

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0052 : BoxTree := (.split (.split (.split (.split (.leaf (513725389083/250000000000 : ℚ)) (.leaf (2054901554919/1000000000000 : ℚ))) (.split (.leaf (41098031071/20000000000 : ℚ)) (.leaf (1027450776111/500000000000 : ℚ)))) (.split (.split (.leaf (128431346933/62500000000 : ℚ)) (.leaf (2054901549693/1000000000000 : ℚ))) (.split (.leaf (2054901548477/1000000000000 : ℚ)) (.leaf (2054901547303/1000000000000 : ℚ))))) (.split (.split (.split (.leaf (513725386541/250000000000 : ℚ)) (.leaf (410980309017/200000000000 : ℚ))) (.split (.leaf (205490154403/100000000000 : ℚ)) (.leaf (1027450771511/500000000000 : ℚ)))) (.split (.split (.leaf (2054901542041/1000000000000 : ℚ)) (.leaf (1027450770559/500000000000 : ℚ))) (.split (.leaf (2054901540227/1000000000000 : ℚ)) (.leaf (2054901539361/1000000000000 : ℚ))))))

theorem cover8_tree0052_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0052 (4181/32768 : ℚ) (2091/16384 : ℚ) := by
  unfold cover8_tree0052
  refine tree_all_split_at (8363/65536 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (16725/131072 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (33449/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66897/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0824_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0825_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66899/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0826_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0827_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (33451/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66901/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0828_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0829_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66903/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0830_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0831_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (16727/131072 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (33453/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66905/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0832_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0833_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66907/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0834_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0835_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (33455/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66909/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0836_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0837_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66911/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0838_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0839_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0052_checked
#print axioms SmaleRate.Proofs.cover8_tree0052_checked
