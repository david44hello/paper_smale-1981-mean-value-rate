/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.DyadicAssembly
public import SmaleRate.Proofs.Generated.D8Chunk0031
public import SmaleRate.Proofs.Generated.D8Chunk0032

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0050 : BoxTree := (.split (.split (.split (.split (.leaf (2054901622439/1000000000000 : ℚ)) (.leaf (2054901619759/1000000000000 : ℚ))) (.split (.leaf (256862702139/125000000000 : ℚ)) (.leaf (410980322901/200000000000 : ℚ)))) (.split (.split (.leaf (128431350747/62500000000 : ℚ)) (.leaf (513725402357/250000000000 : ℚ))) (.split (.leaf (2054901606951/1000000000000 : ℚ)) (.leaf (2054901604499/1000000000000 : ℚ))))) (.split (.split (.split (.leaf (1027450801049/500000000000 : ℚ)) (.leaf (1027450799863/500000000000 : ℚ))) (.split (.leaf (2054901597407/1000000000000 : ℚ)) (.leaf (256862699391/125000000000 : ℚ)))) (.split (.split (.leaf (2054901592871/1000000000000 : ℚ)) (.leaf (2054901590673/1000000000000 : ℚ))) (.split (.leaf (256862698563/125000000000 : ℚ)) (.leaf (2054901586383/1000000000000 : ℚ))))))

theorem cover8_tree0050_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0050 (4179/32768 : ℚ) (1045/8192 : ℚ) := by
  unfold cover8_tree0050
  refine tree_all_split_at (8359/65536 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (16717/131072 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (33433/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66865/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0792_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0793_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66867/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0794_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0795_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (33435/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66869/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0796_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0797_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66871/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0798_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0799_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (16719/131072 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (33437/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66873/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0800_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0801_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66875/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0802_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0803_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (33439/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66877/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0804_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0805_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66879/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0806_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0807_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0050_checked
#print axioms SmaleRate.Proofs.cover8_tree0050_checked
