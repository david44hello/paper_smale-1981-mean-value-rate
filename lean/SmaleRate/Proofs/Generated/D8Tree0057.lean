/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.DyadicAssembly
import SmaleRate.Proofs.Generated.D8Chunk0036

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0057 : BoxTree := (.split (.split (.split (.split (.leaf (2054901569117/1000000000000 : ℚ)) (.leaf (2054901570897/1000000000000 : ℚ))) (.split (.leaf (410980314539/200000000000 : ℚ)) (.leaf (513725393639/250000000000 : ℚ)))) (.split (.split (.leaf (2054901576429/1000000000000 : ℚ)) (.leaf (1027450789181/500000000000 : ℚ))) (.split (.leaf (513725395083/250000000000 : ℚ)) (.leaf (256862697791/125000000000 : ℚ))))) (.split (.split (.split (.leaf (1027450792187/500000000000 : ℚ)) (.leaf (2054901586463/1000000000000 : ℚ))) (.split (.leaf (2054901588589/1000000000000 : ℚ)) (.leaf (410980318151/200000000000 : ℚ)))) (.split (.split (.leaf (2054901592957/1000000000000 : ℚ)) (.leaf (1284313497/625000000 : ℚ))) (.split (.leaf (51372539937/25000000000 : ℚ)) (.leaf (2054901599799/1000000000000 : ℚ))))))

theorem cover8_tree0057_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0057 (2093/16384 : ℚ) (4187/32768 : ℚ) := by
  unfold cover8_tree0057
  refine tree_all_split_at (8373/65536 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (16745/131072 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (33489/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66977/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0904_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0905_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66979/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0906_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0907_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (33491/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66981/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0908_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0909_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66983/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0910_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0911_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (16747/131072 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (33493/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66985/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0912_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0913_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66987/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0914_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0915_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (33495/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66989/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0916_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0917_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66991/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0918_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0919_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0057_checked
#print axioms SmaleRate.Proofs.cover8_tree0057_checked
