/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.DyadicAssembly
public import SmaleRate.Proofs.Generated.D7Chunk0024
public import SmaleRate.Proofs.Generated.D7Chunk0025

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover7_tree0039 : BoxTree := (.split (.split (.split (.split (.split (.leaf (252384366417/125000000000 : ℚ)) (.leaf (2019257650499/1000000000000 : ℚ))) (.split (.leaf (1009723826831/500000000000 : ℚ)) (.leaf (2019644865137/1000000000000 : ℚ)))) (.split (.split (.leaf (2019849210593/1000000000000 : ℚ)) (.leaf (505015154259/250000000000 : ℚ))) (.split (.leaf (505069753191/250000000000 : ℚ)) (.leaf (1010252163653/500000000000 : ℚ))))) (.split (.split (.leaf (2019002791689/1000000000000 : ℚ)) (.leaf (2019500275557/1000000000000 : ℚ))) (.split (.leaf (101001203633/50000000000 : ℚ)) (.leaf (2020573679891/1000000000000 : ℚ))))) (.split (.split (.split (.leaf (101057430547/50000000000 : ℚ)) (.leaf (2021748395523/1000000000000 : ℚ))) (.leaf (1009536682041/500000000000 : ℚ))) (.split (.leaf (505109291273/250000000000 : ℚ)) (.leaf (505472920173/250000000000 : ℚ)))))

theorem cover7_tree0039_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 7 box ∧ (2019/1000 : ℝ) < (box.lower : ℝ)) cover7_tree0039 (5/32 : ℚ) (3/16 : ℚ) := by
  unfold cover7_tree0039
  refine tree_all_split_at (11/64 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (21/128 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (41/256 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (81/512 : ℚ) (by norm_num) ?_ ?_
        · refine tree_all_split_at (161/1024 : ℚ) (by norm_num) ?_ ?_
          · convert cover7_leaf0614_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
          · convert cover7_leaf0615_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
        · refine tree_all_split_at (163/1024 : ℚ) (by norm_num) ?_ ?_
          · convert cover7_leaf0616_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
          · convert cover7_leaf0617_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (83/512 : ℚ) (by norm_num) ?_ ?_
        · refine tree_all_split_at (165/1024 : ℚ) (by norm_num) ?_ ?_
          · convert cover7_leaf0618_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
          · convert cover7_leaf0619_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
        · refine tree_all_split_at (167/1024 : ℚ) (by norm_num) ?_ ?_
          · convert cover7_leaf0620_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
          · convert cover7_leaf0621_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (43/256 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (85/512 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0622_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0623_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (87/512 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0624_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0625_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (23/128 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (45/256 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (89/512 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0626_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0627_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · convert cover7_leaf0628_certificate hidentity using 1 <;>
          norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (47/256 : ℚ) (by norm_num) ?_ ?_
      · convert cover7_leaf0629_certificate hidentity using 1 <;>
          norm_num [treeAll, BoxEndpointBound]
      · convert cover7_leaf0630_certificate hidentity using 1 <;>
          norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover7_tree0039_checked
#print axioms SmaleRate.Proofs.cover7_tree0039_checked
