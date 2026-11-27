/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.DyadicAssembly
public import SmaleRate.Proofs.Generated.D7Chunk0010

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover7_tree0017 : BoxTree := (.split (.split (.split (.split (.leaf (1009506968739/500000000000 : ℚ)) (.leaf (2019013794457/1000000000000 : ℚ))) (.split (.leaf (201901365377/100000000000 : ℚ)) (.leaf (2019013515407/1000000000000 : ℚ)))) (.split (.split (.leaf (1009506689699/500000000000 : ℚ)) (.leaf (504753311427/250000000000 : ℚ))) (.split (.leaf (2019013114343/1000000000000 : ℚ)) (.leaf (1009506492651/500000000000 : ℚ))))) (.split (.split (.split (.leaf (403802571721/200000000000 : ℚ)) (.leaf (12618829589/6250000000 : ℚ))) (.split (.leaf (201901261219/100000000000 : ℚ)) (.leaf (2019012492477/1000000000000 : ℚ)))) (.split (.split (.leaf (1009506187547/500000000000 : ℚ)) (.leaf (2019012260033/1000000000000 : ℚ))) (.split (.leaf (2019012147299/1000000000000 : ℚ)) (.leaf (504753009221/250000000000 : ℚ))))))

theorem cover7_tree0017_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 7 box ∧ (2019/1000 : ℝ) < (box.lower : ℝ)) cover7_tree0017 (277/2048 : ℚ) (555/4096 : ℚ) := by
  unfold cover7_tree0017
  refine tree_all_split_at (1109/8192 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (2217/16384 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (4433/32768 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (8865/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0254_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0255_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (8867/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0256_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0257_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (4435/32768 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (8869/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0258_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0259_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (8871/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0260_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0261_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (2219/16384 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (4437/32768 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (8873/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0262_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0263_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (8875/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0264_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0265_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (4439/32768 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (8877/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0266_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0267_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (8879/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0268_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0269_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover7_tree0017_checked
#print axioms SmaleRate.Proofs.cover7_tree0017_checked
