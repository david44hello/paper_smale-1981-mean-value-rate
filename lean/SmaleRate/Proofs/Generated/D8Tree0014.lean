/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.DyadicAssembly
public import SmaleRate.Proofs.Generated.D8Chunk0008

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0014 : BoxTree := (.split (.split (.split (.split (.leaf (513726506717/250000000000 : ℚ)) (.leaf (256863202591/125000000000 : ℚ))) (.split (.leaf (513726304309/250000000000 : ℚ)) (.leaf (2054904816369/1000000000000 : ℚ)))) (.split (.split (.leaf (32107881533/15625000000 : ℚ)) (.leaf (205490402249/100000000000 : ℚ))) (.split (.leaf (1027451814749/500000000000 : ℚ)) (.leaf (256862904891/125000000000 : ℚ))))) (.split (.split (.split (.leaf (205490285139/100000000000 : ℚ)) (.leaf (2054902466261/1000000000000 : ℚ))) (.split (.leaf (410980416753/200000000000 : ℚ)) (.leaf (256862712987/125000000000 : ℚ)))) (.split (.split (.leaf (2054901326641/1000000000000 : ℚ)) (.leaf (128431309501/62500000000 : ℚ))) (.split (.leaf (2054900580003/1000000000000 : ℚ)) (.leaf (2054900210619/1000000000000 : ℚ))))))

theorem cover8_tree0014_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0014 (513/4096 : ℚ) (257/2048 : ℚ) := by
  unfold cover8_tree0014
  refine tree_all_split_at (1027/8192 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (2053/16384 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (4105/32768 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (8209/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0206_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0207_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (8211/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0208_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0209_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (4107/32768 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (8213/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0210_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0211_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (8215/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0212_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0213_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (2055/16384 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (4109/32768 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (8217/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0214_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0215_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (8219/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0216_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0217_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (4111/32768 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (8221/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0218_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0219_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (8223/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0220_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0221_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0014_checked
#print axioms SmaleRate.Proofs.cover8_tree0014_checked
