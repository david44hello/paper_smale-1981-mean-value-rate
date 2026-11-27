/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.DyadicAssembly
public import SmaleRate.Proofs.Generated.D8Chunk0034
public import SmaleRate.Proofs.Generated.D8Chunk0035

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0055 : BoxTree := (.split (.split (.split (.split (.leaf (410980306703/200000000000 : ℚ)) (.leaf (2054901534003/1000000000000 : ℚ))) (.split (.leaf (410980306909/200000000000 : ℚ)) (.leaf (256862691891/125000000000 : ℚ)))) (.split (.split (.leaf (2054901535729/1000000000000 : ℚ)) (.leaf (205490153639/100000000000 : ℚ))) (.split (.leaf (32107836517/15625000000 : ℚ)) (.leaf (2054901537823/1000000000000 : ℚ))))) (.split (.split (.split (.leaf (2054901538597/1000000000000 : ℚ)) (.leaf (513725384853/250000000000 : ℚ))) (.split (.leaf (1027450770133/500000000000 : ℚ)) (.leaf (2054901541157/1000000000000 : ℚ)))) (.split (.split (.leaf (513725385527/250000000000 : ℚ)) (.leaf (82196061723/40000000000 : ℚ))) (.split (.leaf (2054901544081/1000000000000 : ℚ)) (.leaf (2054901545147/1000000000000 : ℚ))))))

theorem cover8_tree0055_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0055 (523/4096 : ℚ) (4185/32768 : ℚ) := by
  unfold cover8_tree0055
  refine tree_all_split_at (8369/65536 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (16737/131072 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (33473/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66945/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0872_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0873_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66947/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0874_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0875_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (33475/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66949/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0876_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0877_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66951/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0878_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0879_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (16739/131072 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (33477/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66953/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0880_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0881_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66955/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0882_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0883_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (33479/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66957/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0884_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0885_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66959/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0886_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0887_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0055_checked
#print axioms SmaleRate.Proofs.cover8_tree0055_checked
