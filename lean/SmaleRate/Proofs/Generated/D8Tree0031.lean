/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.DyadicAssembly
import SmaleRate.Proofs.Generated.D8Chunk0019

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0031 : BoxTree := (.split (.split (.split (.split (.leaf (205490084771/100000000000 : ℚ)) (.leaf (256862601951/125000000000 : ℚ))) (.split (.leaf (513725195917/250000000000 : ℚ)) (.leaf (2054900751877/1000000000000 : ℚ)))) (.split (.split (.leaf (2054900720263/1000000000000 : ℚ)) (.leaf (205490068879/100000000000 : ℚ))) (.split (.leaf (2054900657491/1000000000000 : ℚ)) (.leaf (1027450313183/500000000000 : ℚ))))) (.split (.split (.split (.leaf (128431287211/62500000000 : ℚ)) (.leaf (256862570571/125000000000 : ℚ))) (.split (.leaf (2054900533907/1000000000000 : ℚ)) (.leaf (2054900503411/1000000000000 : ℚ)))) (.split (.split (.leaf (2054900473069/1000000000000 : ℚ)) (.leaf (2054900442899/1000000000000 : ℚ))) (.split (.leaf (2054900412867/1000000000000 : ℚ)) (.leaf (513725095753/250000000000 : ℚ))))))

theorem cover8_tree0031_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0031 (2079/16384 : ℚ) (65/512 : ℚ) := by
  unfold cover8_tree0031
  refine tree_all_split_at (4159/32768 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (8317/65536 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (16633/131072 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (33265/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0484_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0485_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (33267/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0486_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0487_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (16635/131072 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (33269/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0488_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0489_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (33271/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0490_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0491_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (8319/65536 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (16637/131072 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (33273/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0492_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0493_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (33275/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0494_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0495_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (16639/131072 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (33277/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0496_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0497_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (33279/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0498_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0499_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0031_checked
#print axioms SmaleRate.Proofs.cover8_tree0031_checked
