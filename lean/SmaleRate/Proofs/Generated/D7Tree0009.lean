/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.DyadicAssembly
import SmaleRate.Proofs.Generated.D7Chunk0004
import SmaleRate.Proofs.Generated.D7Chunk0005

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover7_tree0009 : BoxTree := (.split (.split (.split (.split (.leaf (2019053763223/1000000000000 : ℚ)) (.leaf (2019052571421/1000000000000 : ℚ))) (.split (.leaf (20190513893/10000000000 : ℚ)) (.leaf (504762554219/250000000000 : ℚ)))) (.split (.split (.leaf (1009524527063/500000000000 : ℚ)) (.leaf (1009523950529/500000000000 : ℚ))) (.split (.leaf (403809351533/200000000000 : ℚ)) (.leaf (2019045623947/1000000000000 : ℚ))))) (.split (.split (.split (.leaf (201904449989/100000000000 : ℚ)) (.leaf (2019043385501/1000000000000 : ℚ))) (.split (.leaf (1009521140383/500000000000 : ℚ)) (.leaf (2019041185693/1000000000000 : ℚ)))) (.split (.split (.leaf (2019040100273/1000000000000 : ℚ)) (.leaf (2019039024493/1000000000000 : ℚ))) (.split (.leaf (1009518979183/500000000000 : ℚ)) (.leaf (100951845093/50000000000 : ℚ))))))

theorem cover7_tree0009_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 7 box ∧ (2019/1000 : ℝ) < (box.lower : ℝ)) cover7_tree0009 (271/2048 : ℚ) (17/128 : ℚ) := by
  unfold cover7_tree0009
  refine tree_all_split_at (543/4096 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (1085/8192 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (2169/16384 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (4337/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0121_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0122_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (4339/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0123_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0124_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (2171/16384 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (4341/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0125_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0126_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (4343/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0127_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0128_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (1087/8192 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (2173/16384 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (4345/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0129_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0130_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (4347/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0131_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0132_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (2175/16384 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (4349/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0133_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0134_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (4351/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0135_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0136_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover7_tree0009_checked
#print axioms SmaleRate.Proofs.cover7_tree0009_checked
