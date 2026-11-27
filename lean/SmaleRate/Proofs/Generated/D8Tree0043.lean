/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.DyadicAssembly
import SmaleRate.Proofs.Generated.D8Chunk0027

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0043 : BoxTree := (.split (.split (.split (.split (.leaf (32107846483/15625000000 : ℚ)) (.leaf (2054902167769/1000000000000 : ℚ))) (.split (.leaf (256862770083/125000000000 : ℚ)) (.leaf (2054902153599/1000000000000 : ℚ)))) (.split (.split (.leaf (205490214657/100000000000 : ℚ)) (.leaf (2054902139583/1000000000000 : ℚ))) (.split (.leaf (2054902132639/1000000000000 : ℚ)) (.leaf (128431382859/62500000000 : ℚ))))) (.split (.split (.split (.leaf (2054902118871/1000000000000 : ℚ)) (.leaf (1027451056019/500000000000 : ℚ))) (.split (.leaf (128431381579/62500000000 : ℚ)) (.leaf (2054902098511/1000000000000 : ℚ)))) (.split (.split (.leaf (2054902091811/1000000000000 : ℚ)) (.leaf (513725521283/250000000000 : ℚ))) (.split (.leaf (2054902078517/1000000000000 : ℚ)) (.leaf (2054902071913/1000000000000 : ℚ))))))

theorem cover8_tree0043_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0043 (1043/8192 : ℚ) (4173/32768 : ℚ) := by
  unfold cover8_tree0043
  refine tree_all_split_at (8345/65536 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (16689/131072 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (33377/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66753/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0680_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0681_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66755/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0682_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0683_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (33379/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66757/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0684_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0685_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66759/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0686_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0687_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (16691/131072 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (33381/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66761/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0688_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0689_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66763/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0690_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0691_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (33383/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66765/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0692_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0693_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66767/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0694_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0695_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0043_checked
#print axioms SmaleRate.Proofs.cover8_tree0043_checked
