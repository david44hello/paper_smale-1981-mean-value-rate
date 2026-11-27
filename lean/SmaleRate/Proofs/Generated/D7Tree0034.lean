/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.DyadicAssembly
public import SmaleRate.Proofs.Generated.D7Chunk0020
public import SmaleRate.Proofs.Generated.D7Chunk0021

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover7_tree0034 : BoxTree := (.split (.split (.split (.split (.leaf (2019013979923/1000000000000 : ℚ)) (.leaf (2019016621149/1000000000000 : ℚ))) (.split (.leaf (2019019297209/1000000000000 : ℚ)) (.leaf (2019022008067/1000000000000 : ℚ)))) (.split (.split (.leaf (2019024753691/1000000000000 : ℚ)) (.leaf (126189220879/62500000000 : ℚ))) (.split (.leaf (2019030349151/1000000000000 : ℚ)) (.leaf (504758299733/250000000000 : ℚ))))) (.split (.split (.split (.leaf (16152288667/8000000000 : ℚ)) (.leaf (504759750617/250000000000 : ℚ))) (.split (.leaf (2019041956159/1000000000000 : ℚ)) (.leaf (2019044944449/1000000000000 : ℚ)))) (.split (.split (.leaf (2019047967297/1000000000000 : ℚ)) (.leaf (504762756171/250000000000 : ℚ))) (.split (.leaf (80762164663/40000000000 : ℚ)) (.leaf (1009528621477/500000000000 : ℚ))))))

theorem cover7_tree0034_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 7 box ∧ (2019/1000 : ℝ) < (box.lower : ℝ)) cover7_tree0034 (9/64 : ℚ) (145/1024 : ℚ) := by
  unfold cover7_tree0034
  refine tree_all_split_at (289/2048 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (577/4096 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (1153/8192 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (2305/16384 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0524_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0525_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (2307/16384 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0526_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0527_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (1155/8192 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (2309/16384 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0528_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0529_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (2311/16384 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0530_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0531_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (579/4096 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (1157/8192 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (2313/16384 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0532_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0533_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (2315/16384 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0534_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0535_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (1159/8192 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (2317/16384 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0536_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0537_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (2319/16384 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0538_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0539_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover7_tree0034_checked
#print axioms SmaleRate.Proofs.cover7_tree0034_checked
