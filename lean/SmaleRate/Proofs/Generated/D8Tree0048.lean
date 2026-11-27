/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.DyadicAssembly
public import SmaleRate.Proofs.Generated.D8Chunk0030
public import SmaleRate.Proofs.Generated.D8Chunk0031

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0048 : BoxTree := (.split (.split (.split (.split (.leaf (1027450864649/500000000000 : ℚ)) (.leaf (2054901725337/1000000000000 : ℚ))) (.split (.leaf (256862715177/125000000000 : ℚ)) (.leaf (256862714693/125000000000 : ℚ)))) (.split (.split (.leaf (256862714213/125000000000 : ℚ)) (.leaf (513725427477/250000000000 : ℚ))) (.split (.leaf (2054901706161/1000000000000 : ℚ)) (.leaf (2054901702431/1000000000000 : ℚ))))) (.split (.split (.split (.leaf (513725424689/250000000000 : ℚ)) (.leaf (25686271189/12500000000 : ℚ))) (.split (.leaf (82196067661/40000000000 : ℚ)) (.leaf (205490168797/100000000000 : ℚ)))) (.split (.split (.leaf (2054901684451/1000000000000 : ℚ)) (.leaf (2054901680971/1000000000000 : ℚ))) (.split (.leaf (2054901677531/1000000000000 : ℚ)) (.leaf (2054901674131/1000000000000 : ℚ))))))

theorem cover8_tree0048_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0048 (4177/32768 : ℚ) (2089/16384 : ℚ) := by
  unfold cover8_tree0048
  refine tree_all_split_at (8355/65536 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (16709/131072 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (33417/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66833/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0760_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0761_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66835/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0762_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0763_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (33419/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66837/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0764_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0765_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66839/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0766_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0767_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (16711/131072 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (33421/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66841/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0768_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0769_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66843/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0770_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0771_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (33423/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66845/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0772_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0773_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66847/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0774_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0775_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0048_checked
#print axioms SmaleRate.Proofs.cover8_tree0048_checked
