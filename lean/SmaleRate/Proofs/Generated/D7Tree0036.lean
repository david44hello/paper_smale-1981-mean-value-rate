/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.DyadicAssembly
public import SmaleRate.Proofs.Generated.D7Chunk0022

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover7_tree0036 : BoxTree := (.split (.split (.split (.split (.split (.leaf (504778910629/250000000000 : ℚ)) (.leaf (2019119385221/1000000000000 : ℚ))) (.leaf (2019003738629/1000000000000 : ℚ))) (.split (.leaf (1009505730663/500000000000 : ℚ)) (.leaf (2019019319603/1000000000000 : ℚ)))) (.split (.split (.leaf (2019027313253/1000000000000 : ℚ)) (.leaf (1009517721051/500000000000 : ℚ))) (.split (.leaf (2019043705931/1000000000000 : ℚ)) (.leaf (504763026137/250000000000 : ℚ))))) (.split (.split (.split (.leaf (2019060637733/1000000000000 : ℚ)) (.leaf (50476732633/25000000000 : ℚ))) (.split (.leaf (403815621417/200000000000 : ℚ)) (.leaf (2019087042857/1000000000000 : ℚ)))) (.split (.split (.leaf (2019096112413/1000000000000 : ℚ)) (.leaf (126194082223/62500000000 : ℚ))) (.split (.leaf (1009557326061/500000000000 : ℚ)) (.leaf (504781030473/250000000000 : ℚ))))))

theorem cover7_tree0036_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 7 box ∧ (2019/1000 : ℝ) < (box.lower : ℝ)) cover7_tree0036 (73/512 : ℚ) (37/256 : ℚ) := by
  unfold cover7_tree0036
  refine tree_all_split_at (147/1024 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (293/2048 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (585/4096 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (1169/8192 : ℚ) (by norm_num) ?_ ?_
        · refine tree_all_split_at (2337/16384 : ℚ) (by norm_num) ?_ ?_
          · convert cover7_leaf0556_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
          · convert cover7_leaf0557_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0558_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (1171/8192 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0559_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0560_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (587/4096 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (1173/8192 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0561_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0562_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (1175/8192 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0563_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0564_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (295/2048 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (589/4096 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (1177/8192 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0565_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0566_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (1179/8192 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0567_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0568_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (591/4096 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (1181/8192 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0569_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0570_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (1183/8192 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0571_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0572_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover7_tree0036_checked
#print axioms SmaleRate.Proofs.cover7_tree0036_checked
