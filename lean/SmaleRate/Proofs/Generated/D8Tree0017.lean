/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.DyadicAssembly
public import SmaleRate.Proofs.Generated.D8Chunk0010

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0017 : BoxTree := (.split (.split (.split (.split (.leaf (2054910171227/1000000000000 : ℚ)) (.leaf (128431875569/62500000000 : ℚ))) (.split (.leaf (1027454923807/500000000000 : ℚ)) (.leaf (2054909686781/1000000000000 : ℚ)))) (.split (.split (.leaf (1027454763303/500000000000 : ℚ)) (.leaf (2054909367079/1000000000000 : ℚ))) (.split (.leaf (2054909208209/1000000000000 : ℚ)) (.leaf (1027454524997/500000000000 : ℚ))))) (.split (.split (.split (.leaf (1027454446207/500000000000 : ℚ)) (.leaf (2054908735509/1000000000000 : ℚ))) (.split (.leaf (1027454289617/500000000000 : ℚ)) (.leaf (2054908423619/1000000000000 : ℚ)))) (.split (.split (.leaf (410981653731/200000000000 : ℚ)) (.leaf (513727028591/250000000000 : ℚ))) (.split (.leaf (410981592141/200000000000 : ℚ)) (.leaf (410981561537/200000000000 : ℚ))))))

theorem cover8_tree0017_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0017 (515/4096 : ℚ) (1031/8192 : ℚ) := by
  unfold cover8_tree0017
  refine tree_all_split_at (2061/16384 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (4121/32768 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (8241/65536 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (16481/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0254_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0255_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (16483/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0256_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0257_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (8243/65536 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (16485/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0258_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0259_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (16487/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0260_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0261_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (4123/32768 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (8245/65536 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (16489/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0262_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0263_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (16491/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0264_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0265_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (8247/65536 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (16493/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0266_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0267_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (16495/131072 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0268_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0269_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0017_checked
#print axioms SmaleRate.Proofs.cover8_tree0017_checked
