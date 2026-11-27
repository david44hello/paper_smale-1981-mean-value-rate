/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.DyadicAssembly
import SmaleRate.Proofs.Generated.D8Chunk0032

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0051 : BoxTree := (.split (.split (.split (.split (.leaf (2054901584297/1000000000000 : ℚ)) (.leaf (2054901582253/1000000000000 : ℚ))) (.split (.leaf (2054901580243/1000000000000 : ℚ)) (.leaf (1027450789139/500000000000 : ℚ)))) (.split (.split (.leaf (2054901576343/1000000000000 : ℚ)) (.leaf (205490157447/100000000000 : ℚ))) (.split (.leaf (256862696577/125000000000 : ℚ)) (.leaf (2054901570803/1000000000000 : ℚ))))) (.split (.split (.split (.leaf (2054901569043/1000000000000 : ℚ)) (.leaf (513725391827/250000000000 : ℚ))) (.split (.leaf (2054901565631/1000000000000 : ℚ)) (.leaf (513725390997/250000000000 : ℚ)))) (.split (.split (.leaf (205490156237/100000000000 : ℚ)) (.leaf (410980312161/200000000000 : ℚ))) (.split (.leaf (1027450779641/500000000000 : ℚ)) (.leaf (2054901557777/1000000000000 : ℚ))))))

theorem cover8_tree0051_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0051 (1045/8192 : ℚ) (4181/32768 : ℚ) := by
  unfold cover8_tree0051
  refine tree_all_split_at (8361/65536 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (16721/131072 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (33441/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66881/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0808_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0809_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66883/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0810_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0811_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (33443/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66885/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0812_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0813_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66887/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0814_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0815_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (16723/131072 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (33445/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66889/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0816_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0817_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66891/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0818_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0819_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (33447/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66893/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0820_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0821_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66895/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0822_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0823_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0051_checked
#print axioms SmaleRate.Proofs.cover8_tree0051_checked
