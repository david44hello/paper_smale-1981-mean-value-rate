/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.DyadicAssembly
public import SmaleRate.Proofs.Generated.D8Chunk0031

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0049 : BoxTree := (.split (.split (.split (.split (.leaf (205490167077/100000000000 : ℚ)) (.leaf (2054901667447/1000000000000 : ℚ))) (.split (.leaf (2054901664179/1000000000000 : ℚ)) (.leaf (2054901660933/1000000000000 : ℚ)))) (.split (.split (.leaf (2054901657729/1000000000000 : ℚ)) (.leaf (1027450827287/500000000000 : ℚ))) (.split (.leaf (1027450825723/500000000000 : ℚ)) (.leaf (2054901648373/1000000000000 : ℚ))))) (.split (.split (.split (.leaf (2054901645339/1000000000000 : ℚ)) (.leaf (513725410581/250000000000 : ℚ))) (.split (.leaf (513725409843/250000000000 : ℚ)) (.leaf (2054901636451/1000000000000 : ℚ)))) (.split (.split (.leaf (205490163357/100000000000 : ℚ)) (.leaf (2054901630733/1000000000000 : ℚ))) (.split (.leaf (1027450813967/500000000000 : ℚ)) (.leaf (2054901625171/1000000000000 : ℚ))))))

theorem cover8_tree0049_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0049 (2089/16384 : ℚ) (4179/32768 : ℚ) := by
  unfold cover8_tree0049
  refine tree_all_split_at (8357/65536 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (16713/131072 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (33425/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66849/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0776_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0777_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66851/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0778_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0779_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (33427/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66853/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0780_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0781_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66855/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0782_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0783_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (16715/131072 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (33429/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66857/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0784_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0785_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66859/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0786_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0787_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (33431/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66861/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0788_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0789_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66863/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0790_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0791_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0049_checked
#print axioms SmaleRate.Proofs.cover8_tree0049_checked
