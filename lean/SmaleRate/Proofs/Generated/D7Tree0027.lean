/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.DyadicAssembly
public import SmaleRate.Proofs.Generated.D7Chunk0016
public import SmaleRate.Proofs.Generated.D7Chunk0017

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover7_tree0027 : BoxTree := (.split (.split (.split (.split (.leaf (1009510208399/500000000000 : ℚ)) (.leaf (2019020641191/1000000000000 : ℚ))) (.split (.leaf (504755216963/250000000000 : ℚ)) (.leaf (2019021096757/1000000000000 : ℚ)))) (.split (.split (.leaf (2019021327929/1000000000000 : ℚ)) (.leaf (40380431227/20000000000 : ℚ))) (.split (.leaf (504755449259/250000000000 : ℚ)) (.leaf (252377754373/125000000000 : ℚ))))) (.split (.split (.split (.leaf (1009511137597/500000000000 : ℚ)) (.leaf (252377814707/125000000000 : ℚ))) (.split (.leaf (1009511381181/500000000000 : ℚ)) (.leaf (2019023009343/1000000000000 : ℚ)))) (.split (.split (.leaf (2019023258573/1000000000000 : ℚ)) (.leaf (2019023510067/1000000000000 : ℚ))) (.split (.leaf (1009511881899/500000000000 : ℚ)) (.leaf (1009512009899/500000000000 : ℚ))))))

theorem cover7_tree0027_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 7 box ∧ (2019/1000 : ℝ) < (box.lower : ℝ)) cover7_tree0027 (141/1024 : ℚ) (565/4096 : ℚ) := by
  unfold cover7_tree0027
  refine tree_all_split_at (1129/8192 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (2257/16384 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (4513/32768 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (9025/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0414_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0415_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (9027/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0416_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0417_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (4515/32768 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (9029/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0418_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0419_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (9031/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0420_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0421_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (2259/16384 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (4517/32768 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (9033/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0422_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0423_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (9035/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0424_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0425_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (4519/32768 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (9037/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0426_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0427_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (9039/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0428_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0429_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover7_tree0027_checked
#print axioms SmaleRate.Proofs.cover7_tree0027_checked
