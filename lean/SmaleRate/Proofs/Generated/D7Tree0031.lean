/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.DyadicAssembly
import SmaleRate.Proofs.Generated.D7Chunk0019

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover7_tree0031 : BoxTree := (.split (.split (.split (.split (.leaf (2019021835217/1000000000000 : ℚ)) (.leaf (1009511360349/500000000000 : ℚ))) (.split (.leaf (2019023615051/1000000000000 : ℚ)) (.leaf (201902451827/100000000000 : ℚ)))) (.split (.split (.leaf (16152203443/8000000000 : ℚ)) (.leaf (2019026351317/1000000000000 : ℚ))) (.split (.leaf (1009513640561/500000000000 : ℚ)) (.leaf (126189263737/62500000000 : ℚ))))) (.split (.split (.split (.leaf (2019029167323/1000000000000 : ℚ)) (.leaf (403806024737/200000000000 : ℚ))) (.split (.leaf (2019031088907/1000000000000 : ℚ)) (.leaf (504758015739/250000000000 : ℚ)))) (.split (.split (.leaf (504758261463/250000000000 : ℚ)) (.leaf (2019034037587/1000000000000 : ℚ))) (.split (.leaf (2019035038159/1000000000000 : ℚ)) (.leaf (2019036047553/1000000000000 : ℚ))))))

theorem cover7_tree0031_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 7 box ∧ (2019/1000 : ℝ) < (box.lower : ℝ)) cover7_tree0031 (285/2048 : ℚ) (143/1024 : ℚ) := by
  unfold cover7_tree0031
  refine tree_all_split_at (571/4096 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (1141/8192 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (2281/16384 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (4561/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0481_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0482_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (4563/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0483_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0484_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (2283/16384 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (4565/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0485_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0486_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (4567/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0487_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0488_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (1143/8192 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (2285/16384 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (4569/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0489_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0490_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (4571/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0491_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0492_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (2287/16384 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (4573/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0493_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0494_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (4575/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0495_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0496_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover7_tree0031_checked
#print axioms SmaleRate.Proofs.cover7_tree0031_checked
