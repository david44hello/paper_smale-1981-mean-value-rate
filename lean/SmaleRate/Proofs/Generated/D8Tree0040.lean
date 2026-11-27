/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.DyadicAssembly
import SmaleRate.Proofs.Generated.D8Chunk0025

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0040 : BoxTree := (.split (.split (.split (.split (.leaf (1003370393/488281250 : ℚ)) (.leaf (2054902555797/1000000000000 : ℚ))) (.split (.leaf (2054902546773/1000000000000 : ℚ)) (.leaf (1027451268891/500000000000 : ℚ)))) (.split (.split (.leaf (2054902528849/1000000000000 : ℚ)) (.leaf (256862814993/125000000000 : ℚ))) (.split (.leaf (2054902511089/1000000000000 : ℚ)) (.leaf (128431406391/62500000000 : ℚ))))) (.split (.split (.split (.leaf (2054902493481/1000000000000 : ℚ)) (.leaf (2054902484743/1000000000000 : ℚ))) (.split (.leaf (2054902476031/1000000000000 : ℚ)) (.leaf (2054902467367/1000000000000 : ℚ)))) (.split (.split (.leaf (513725614687/250000000000 : ℚ)) (.leaf (1027451225083/500000000000 : ℚ))) (.split (.leaf (2054902441629/1000000000000 : ℚ)) (.leaf (2054902433123/1000000000000 : ℚ))))))

theorem cover8_tree0040_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0040 (4169/32768 : ℚ) (2085/16384 : ℚ) := by
  unfold cover8_tree0040
  refine tree_all_split_at (8339/65536 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (16677/131072 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (33353/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66705/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0632_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0633_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66707/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0634_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0635_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (33355/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66709/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0636_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0637_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66711/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0638_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0639_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (16679/131072 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (33357/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66713/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0640_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0641_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66715/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0642_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0643_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (33359/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66717/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0644_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0645_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66719/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0646_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0647_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0040_checked
#print axioms SmaleRate.Proofs.cover8_tree0040_checked
