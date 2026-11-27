/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.DyadicAssembly
public import SmaleRate.Proofs.Generated.D8Chunk0002

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0005 : BoxTree := (.split (.split (.split (.split (.leaf (2055055531569/1000000000000 : ℚ)) (.leaf (2055043735717/1000000000000 : ℚ))) (.split (.leaf (256879015371/125000000000 : ℚ)) (.leaf (1027510346493/500000000000 : ℚ)))) (.split (.split (.leaf (1027504722723/500000000000 : ℚ)) (.leaf (1027499190013/500000000000 : ℚ))) (.split (.leaf (2054987496363/1000000000000 : ℚ)) (.leaf (410995358837/200000000000 : ℚ))))) (.split (.split (.split (.leaf (256870784139/125000000000 : ℚ)) (.leaf (2054955932851/1000000000000 : ℚ))) (.split (.leaf (256868221633/125000000000 : ℚ)) (.leaf (1027467896721/500000000000 : ℚ)))) (.split (.split (.leaf (2054925993647/1000000000000 : ℚ)) (.leaf (2054916373359/1000000000000 : ℚ))) (.split (.leaf (1027453466133/500000000000 : ℚ)) (.split (.leaf (2055027703923/1000000000000 : ℚ)) (.leaf (205502309487/100000000000 : ℚ)))))))

theorem cover8_tree0005_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0005 (61/512 : ℚ) (31/256 : ℚ) := by
  unfold cover8_tree0005
  refine tree_all_split_at (123/1024 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (245/2048 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (489/4096 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (977/8192 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0057_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0058_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (979/8192 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0059_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0060_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (491/4096 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (981/8192 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0061_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0062_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (983/8192 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0063_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0064_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (247/2048 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (493/4096 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (985/8192 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0065_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0066_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (987/8192 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0067_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0068_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (495/4096 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (989/8192 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0069_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0070_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (991/8192 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0071_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · refine tree_all_split_at (1983/16384 : ℚ) (by norm_num) ?_ ?_
          · convert cover8_leaf0072_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
          · convert cover8_leaf0073_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0005_checked
#print axioms SmaleRate.Proofs.cover8_tree0005_checked
