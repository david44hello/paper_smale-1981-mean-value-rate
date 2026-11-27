/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.DyadicAssembly
import SmaleRate.Proofs.Generated.D7Chunk0000
import SmaleRate.Proofs.Generated.D7Chunk0001

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover7_tree0004 : BoxTree := (.split (.split (.split (.split (.leaf (403981068311/200000000000 : ℚ)) (.leaf (2019805001607/1000000000000 : ℚ))) (.split (.leaf (504926923707/250000000000 : ℚ)) (.leaf (403922679791/200000000000 : ℚ)))) (.split (.split (.leaf (1972189543/976562500 : ℚ)) (.leaf (2019433752297/1000000000000 : ℚ))) (.split (.leaf (403869671663/200000000000 : ℚ)) (.leaf (2019265888837/1000000000000 : ℚ))))) (.split (.split (.split (.leaf (1009593161447/500000000000 : ℚ)) (.leaf (2019109639793/1000000000000 : ℚ))) (.split (.leaf (2019035818989/1000000000000 : ℚ)) (.split (.leaf (1009746477869/500000000000 : ℚ)) (.leaf (504864452949/250000000000 : ℚ))))) (.split (.split (.split (.leaf (126213960847/62500000000 : ℚ)) (.leaf (403877927703/200000000000 : ℚ))) (.split (.leaf (504839151057/250000000000 : ℚ)) (.leaf (1009662134103/500000000000 : ℚ)))) (.split (.split (.leaf (504823157009/250000000000 : ℚ)) (.leaf (403852336259/200000000000 : ℚ))) (.split (.leaf (2019231425551/1000000000000 : ℚ)) (.leaf (252400232303/125000000000 : ℚ)))))))

theorem cover7_tree0004_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 7 box ∧ (2019/1000 : ℝ) < (box.lower : ℝ)) cover7_tree0004 (15/128 : ℚ) (1/8 : ℚ) := by
  unfold cover7_tree0004
  refine tree_all_split_at (31/256 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (61/512 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (121/1024 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (241/2048 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0023_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0024_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (243/2048 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0025_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0026_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (123/1024 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (245/2048 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0027_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0028_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (247/2048 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0029_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0030_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (63/512 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (125/1024 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (249/2048 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0031_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0032_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (251/2048 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0033_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · refine tree_all_split_at (503/4096 : ℚ) (by norm_num) ?_ ?_
          · convert cover7_leaf0034_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
          · convert cover7_leaf0035_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (127/1024 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (253/2048 : ℚ) (by norm_num) ?_ ?_
        · refine tree_all_split_at (505/4096 : ℚ) (by norm_num) ?_ ?_
          · convert cover7_leaf0036_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
          · convert cover7_leaf0037_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
        · refine tree_all_split_at (507/4096 : ℚ) (by norm_num) ?_ ?_
          · convert cover7_leaf0038_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
          · convert cover7_leaf0039_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (255/2048 : ℚ) (by norm_num) ?_ ?_
        · refine tree_all_split_at (509/4096 : ℚ) (by norm_num) ?_ ?_
          · convert cover7_leaf0040_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
          · convert cover7_leaf0041_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
        · refine tree_all_split_at (511/4096 : ℚ) (by norm_num) ?_ ?_
          · convert cover7_leaf0042_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
          · convert cover7_leaf0043_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover7_tree0004_checked
#print axioms SmaleRate.Proofs.cover7_tree0004_checked
