/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.DyadicAssembly
public import SmaleRate.Proofs.Generated.D8Chunk0018

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0029 : BoxTree := (.split (.split (.split (.split (.leaf (2054901959827/1000000000000 : ℚ)) (.leaf (2054901922587/1000000000000 : ℚ))) (.split (.leaf (410980377101/200000000000 : ℚ)) (.leaf (2054901848579/1000000000000 : ℚ)))) (.split (.split (.leaf (2054901811807/1000000000000 : ℚ)) (.leaf (2054901775211/1000000000000 : ℚ))) (.split (.leaf (82196069551/40000000000 : ℚ)) (.leaf (513725425623/250000000000 : ℚ))))) (.split (.split (.split (.leaf (410980333273/200000000000 : ℚ)) (.leaf (410980326083/200000000000 : ℚ))) (.split (.leaf (2054901594603/1000000000000 : ℚ)) (.leaf (2054901558971/1000000000000 : ℚ)))) (.split (.split (.leaf (1027450761743/500000000000 : ℚ)) (.leaf (2054901488183/1000000000000 : ℚ))) (.split (.leaf (1027450726509/500000000000 : ℚ)) (.leaf (256862677253/125000000000 : ℚ))))))

theorem cover8_tree0029_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0029 (2077/16384 : ℚ) (1039/8192 : ℚ) := by
  unfold cover8_tree0029
  refine tree_all_split_at (4155/32768 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (8309/65536 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (16617/131072 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (33233/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0452_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0453_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (33235/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0454_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0455_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (16619/131072 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (33237/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0456_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0457_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (33239/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0458_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0459_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (8311/65536 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (16621/131072 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (33241/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0460_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0461_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (33243/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0462_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0463_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (16623/131072 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (33245/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0464_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0465_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (33247/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0466_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0467_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0029_checked
#print axioms SmaleRate.Proofs.cover8_tree0029_checked
