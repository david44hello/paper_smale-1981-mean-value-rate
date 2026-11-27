/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.DyadicAssembly
public import SmaleRate.Proofs.Generated.D8Chunk0029

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0046 : BoxTree := (.split (.split (.split (.split (.leaf (513725469233/250000000000 : ℚ)) (.leaf (2054901871691/1000000000000 : ℚ))) (.split (.leaf (256862733313/125000000000 : ℚ)) (.leaf (25686273267/12500000000 : ℚ)))) (.split (.split (.leaf (1027450928117/500000000000 : ℚ)) (.leaf (205490185117/100000000000 : ℚ))) (.split (.leaf (2054901846137/1000000000000 : ℚ)) (.leaf (2054901841147/1000000000000 : ℚ))))) (.split (.split (.split (.leaf (513725459049/250000000000 : ℚ)) (.leaf (1027450915641/500000000000 : ℚ))) (.split (.leaf (2054901826413/1000000000000 : ℚ)) (.leaf (2054901821569/1000000000000 : ℚ)))) (.split (.split (.leaf (1027450908389/500000000000 : ℚ)) (.leaf (1027450906011/500000000000 : ℚ))) (.split (.leaf (1027450903661/500000000000 : ℚ)) (.leaf (25686272533/12500000000 : ℚ))))))

theorem cover8_tree0046_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0046 (4175/32768 : ℚ) (261/2048 : ℚ) := by
  unfold cover8_tree0046
  refine tree_all_split_at (8351/65536 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (16701/131072 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (33401/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66801/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0728_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0729_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66803/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0730_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0731_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (33403/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66805/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0732_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0733_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66807/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0734_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0735_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (16703/131072 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (33405/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66809/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0736_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0737_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66811/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0738_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0739_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (33407/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66813/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0740_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0741_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66815/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0742_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0743_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0046_checked
#print axioms SmaleRate.Proofs.cover8_tree0046_checked
