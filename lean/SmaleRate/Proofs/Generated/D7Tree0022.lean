/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.DyadicAssembly
public import SmaleRate.Proofs.Generated.D7Chunk0013

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover7_tree0022 : BoxTree := (.split (.split (.split (.split (.leaf (201900982851/100000000000 : ℚ)) (.leaf (252376233829/125000000000 : ℚ))) (.split (.leaf (2019009915059/1000000000000 : ℚ)) (.leaf (2019009961779/1000000000000 : ℚ)))) (.split (.split (.leaf (1009505005393/500000000000 : ℚ)) (.leaf (504752515521/250000000000 : ℚ))) (.split (.leaf (1009505057843/500000000000 : ℚ)) (.leaf (2019010171577/1000000000000 : ℚ))))) (.split (.split (.split (.leaf (2019010229769/1000000000000 : ℚ)) (.leaf (1009505145119/500000000000 : ℚ))) (.split (.leaf (2019010353009/1000000000000 : ℚ)) (.leaf (504752604519/250000000000 : ℚ)))) (.split (.split (.leaf (126188155339/62500000000 : ℚ)) (.leaf (1009505277533/500000000000 : ℚ))) (.split (.leaf (201901062701/100000000000 : ℚ)) (.leaf (2019010701227/1000000000000 : ℚ))))))

theorem cover7_tree0022_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 7 box ∧ (2019/1000 : ℝ) < (box.lower : ℝ)) cover7_tree0022 (559/4096 : ℚ) (35/256 : ℚ) := by
  unfold cover7_tree0022
  refine tree_all_split_at (1119/8192 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (2237/16384 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (4473/32768 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (8945/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0334_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0335_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (8947/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0336_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0337_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (4475/32768 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (8949/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0338_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0339_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (8951/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0340_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0341_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (2239/16384 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (4477/32768 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (8953/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0342_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0343_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (8955/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0344_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0345_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (4479/32768 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (8957/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0346_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0347_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (8959/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0348_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0349_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover7_tree0022_checked
#print axioms SmaleRate.Proofs.cover7_tree0022_checked
