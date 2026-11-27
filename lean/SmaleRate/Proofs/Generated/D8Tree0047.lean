/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.DyadicAssembly
import SmaleRate.Proofs.Generated.D8Chunk0029
import SmaleRate.Proofs.Generated.D8Chunk0030

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0047 : BoxTree := (.split (.split (.split (.split (.leaf (102745089901/50000000000 : ℚ)) (.leaf (256862724177/125000000000 : ℚ))) (.split (.leaf (205490178887/100000000000 : ℚ)) (.leaf (256862723043/125000000000 : ℚ)))) (.split (.split (.leaf (1027450889939/500000000000 : ℚ)) (.leaf (410980355087/200000000000 : ℚ))) (.split (.leaf (2054901771043/1000000000000 : ℚ)) (.leaf (1027450883347/500000000000 : ℚ))))) (.split (.split (.split (.leaf (102745088119/50000000000 : ℚ)) (.leaf (2054901758107/1000000000000 : ℚ))) (.split (.leaf (2054901753873/1000000000000 : ℚ)) (.leaf (25686271871/12500000000 : ℚ)))) (.split (.split (.leaf (1027450872761/500000000000 : ℚ)) (.leaf (2054901741401/1000000000000 : ℚ))) (.split (.leaf (51372543433/25000000000 : ℚ)) (.leaf (2054901733283/1000000000000 : ℚ))))))

theorem cover8_tree0047_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0047 (261/2048 : ℚ) (4177/32768 : ℚ) := by
  unfold cover8_tree0047
  refine tree_all_split_at (8353/65536 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (16705/131072 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (33409/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66817/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0744_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0745_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66819/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0746_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0747_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (33411/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66821/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0748_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0749_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66823/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0750_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0751_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (16707/131072 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (33413/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66825/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0752_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0753_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66827/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0754_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0755_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (33415/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66829/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0756_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0757_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66831/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0758_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0759_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0047_checked
#print axioms SmaleRate.Proofs.cover8_tree0047_checked
