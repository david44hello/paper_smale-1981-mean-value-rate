/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.DyadicAssembly
public import SmaleRate.Proofs.Generated.D8Chunk0027
public import SmaleRate.Proofs.Generated.D8Chunk0028

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0044 : BoxTree := (.split (.split (.split (.split (.leaf (1027451032687/500000000000 : ℚ)) (.leaf (2054902058867/1000000000000 : ℚ))) (.split (.leaf (1027451026201/500000000000 : ℚ)) (.leaf (102745102299/50000000000 : ℚ)))) (.split (.split (.leaf (205490203959/100000000000 : ℚ)) (.leaf (513725508311/250000000000 : ℚ))) (.split (.leaf (2054902026939/1000000000000 : ℚ)) (.leaf (256862752583/125000000000 : ℚ))))) (.split (.split (.split (.leaf (2054902014437/1000000000000 : ℚ)) (.leaf (2054902008243/1000000000000 : ℚ))) (.split (.leaf (205490200209/100000000000 : ℚ)) (.leaf (256862749499/125000000000 : ℚ)))) (.split (.split (.leaf (2054901989919/1000000000000 : ℚ)) (.leaf (20549019839/10000000000 : ℚ))) (.split (.leaf (2054901977903/1000000000000 : ℚ)) (.leaf (2054901971959/1000000000000 : ℚ))))))

theorem cover8_tree0044_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0044 (4173/32768 : ℚ) (2087/16384 : ℚ) := by
  unfold cover8_tree0044
  refine tree_all_split_at (8347/65536 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (16693/131072 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (33385/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66769/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0696_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0697_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66771/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0698_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0699_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (33387/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66773/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0700_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0701_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66775/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0702_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0703_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (16695/131072 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (33389/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66777/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0704_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0705_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66779/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0706_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0707_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (33391/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66781/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0708_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0709_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66783/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0710_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0711_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0044_checked
#print axioms SmaleRate.Proofs.cover8_tree0044_checked
