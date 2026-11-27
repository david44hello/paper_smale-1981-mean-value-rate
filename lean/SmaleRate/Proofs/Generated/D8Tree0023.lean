/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.DyadicAssembly
public import SmaleRate.Proofs.Generated.D8Chunk0014

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0023 : BoxTree := (.split (.split (.split (.split (.leaf (2054906285591/1000000000000 : ℚ)) (.leaf (16439249863/8000000000 : ℚ))) (.split (.leaf (1027453090151/500000000000 : ℚ)) (.leaf (2054906127903/1000000000000 : ℚ)))) (.split (.split (.leaf (1027453037833/500000000000 : ℚ)) (.leaf (2054906023587/1000000000000 : ℚ))) (.split (.leaf (1027452985831/500000000000 : ℚ)) (.leaf (256863239989/125000000000 : ℚ))))) (.split (.split (.split (.leaf (410981173661/200000000000 : ℚ)) (.leaf (2054905816871/1000000000000 : ℚ))) (.split (.leaf (205490576561/100000000000 : ℚ)) (.leaf (410981142899/200000000000 : ℚ)))) (.split (.split (.leaf (41098113271/20000000000 : ℚ)) (.leaf (513726403191/250000000000 : ℚ))) (.split (.leaf (1027452781069/500000000000 : ℚ)) (.leaf (513726377917/250000000000 : ℚ))))))

theorem cover8_tree0023_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0023 (2071/16384 : ℚ) (259/2048 : ℚ) := by
  unfold cover8_tree0023
  refine tree_all_split_at (4143/32768 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (8285/65536 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (16569/131072 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (33137/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0356_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0357_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (33139/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0358_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0359_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (16571/131072 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (33141/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0360_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0361_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (33143/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0362_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0363_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (8287/65536 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (16573/131072 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (33145/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0364_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0365_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (33147/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0366_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0367_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (16575/131072 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (33149/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0368_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0369_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (33151/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0370_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0371_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0023_checked
#print axioms SmaleRate.Proofs.cover8_tree0023_checked
