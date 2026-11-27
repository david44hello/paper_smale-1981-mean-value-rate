/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.DyadicAssembly
import SmaleRate.Proofs.Generated.D8Chunk0016
import SmaleRate.Proofs.Generated.D8Chunk0017

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0027 : BoxTree := (.split (.split (.split (.split (.leaf (2054903236673/1000000000000 : ℚ)) (.leaf (1027451597133/500000000000 : ℚ))) (.split (.leaf (513725788007/250000000000 : ℚ)) (.leaf (2054903109959/1000000000000 : ℚ)))) (.split (.split (.leaf (2054903068039/1000000000000 : ℚ)) (.leaf (2054903026299/1000000000000 : ℚ))) (.split (.leaf (256862873087/125000000000 : ℚ)) (.leaf (410980588653/200000000000 : ℚ))))) (.split (.split (.split (.leaf (410980580399/200000000000 : ℚ)) (.leaf (20549028609/10000000000 : ℚ))) (.split (.leaf (102745140997/50000000000 : ℚ)) (.leaf (2054902779159/1000000000000 : ℚ)))) (.split (.split (.leaf (1027451369267/500000000000 : ℚ)) (.leaf (2054902698061/1000000000000 : ℚ))) (.split (.leaf (2054902657769/1000000000000 : ℚ)) (.leaf (2054902617617/1000000000000 : ℚ))))))

theorem cover8_tree0027_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0027 (2075/16384 : ℚ) (519/4096 : ℚ) := by
  unfold cover8_tree0027
  refine tree_all_split_at (4151/32768 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (8301/65536 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (16601/131072 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (33201/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0420_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0421_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (33203/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0422_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0423_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (16603/131072 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (33205/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0424_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0425_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (33207/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0426_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0427_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (8303/65536 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (16605/131072 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (33209/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0428_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0429_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (33211/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0430_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0431_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (16607/131072 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (33213/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0432_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0433_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (33215/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0434_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0435_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0027_checked
#print axioms SmaleRate.Proofs.cover8_tree0027_checked
