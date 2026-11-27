/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.DyadicAssembly
public import SmaleRate.Proofs.Generated.D8Chunk0010
public import SmaleRate.Proofs.Generated.D8Chunk0011

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0018 : BoxTree := (.split (.split (.split (.split (.leaf (1027453827669/500000000000 : ℚ)) (.leaf (2054907503641/1000000000000 : ℚ))) (.split (.leaf (1027453676291/500000000000 : ℚ)) (.leaf (2054907202191/1000000000000 : ℚ)))) (.split (.split (.leaf (1027453526219/500000000000 : ℚ)) (.leaf (2054906903339/1000000000000 : ℚ))) (.split (.leaf (513726688723/250000000000 : ℚ)) (.leaf (410981321423/200000000000 : ℚ))))) (.split (.split (.split (.leaf (1027453229979/500000000000 : ℚ)) (.leaf (2054906313469/1000000000000 : ℚ))) (.split (.leaf (2054906167631/1000000000000 : ℚ)) (.leaf (2054906022449/1000000000000 : ℚ)))) (.split (.split (.leaf (1027452938951/500000000000 : ℚ)) (.leaf (205490573401/100000000000 : ℚ))) (.split (.leaf (2006743741/976562500 : ℚ)) (.leaf (410981089639/200000000000 : ℚ))))))

theorem cover8_tree0018_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0018 (1031/8192 : ℚ) (129/1024 : ℚ) := by
  unfold cover8_tree0018
  refine tree_all_split_at (2063/16384 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (4125/32768 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (8249/65536 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (16497/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0270_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0271_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (16499/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0272_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0273_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (8251/65536 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (16501/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0274_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0275_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (16503/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0276_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0277_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (4127/32768 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (8253/65536 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (16505/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0278_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0279_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (16507/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0280_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0281_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (8255/65536 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (16509/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0282_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0283_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (16511/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0284_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0285_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0018_checked
#print axioms SmaleRate.Proofs.cover8_tree0018_checked
