/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.DyadicAssembly
public import SmaleRate.Proofs.Generated.D8Chunk0037
public import SmaleRate.Proofs.Generated.D8Chunk0038

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0059 : BoxTree := (.split (.split (.split (.split (.leaf (1027450822681/500000000000 : ℚ)) (.leaf (256862706049/125000000000 : ℚ))) (.split (.leaf (64215676609/31250000000 : ℚ)) (.leaf (2054901654599/1000000000000 : ℚ)))) (.split (.split (.leaf (128431353609/62500000000 : ℚ)) (.leaf (2054901660949/1000000000000 : ℚ))) (.split (.leaf (128431354011/62500000000 : ℚ)) (.leaf (2054901667461/1000000000000 : ℚ))))) (.split (.split (.split (.leaf (410980334153/200000000000 : ℚ)) (.leaf (1027450837061/500000000000 : ℚ))) (.split (.leaf (1027450838761/500000000000 : ℚ)) (.leaf (2054901680961/1000000000000 : ℚ)))) (.split (.split (.leaf (2054901684421/1000000000000 : ℚ)) (.leaf (1027450843967/500000000000 : ℚ))) (.split (.leaf (1027450845743/500000000000 : ℚ)) (.leaf (2054901695079/1000000000000 : ℚ))))))

theorem cover8_tree0059_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0059 (1047/8192 : ℚ) (4189/32768 : ℚ) := by
  unfold cover8_tree0059
  refine tree_all_split_at (8377/65536 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (16753/131072 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (33505/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (67009/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0936_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0937_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (67011/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0938_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0939_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (33507/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (67013/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0940_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0941_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (67015/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0942_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0943_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (16755/131072 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (33509/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (67017/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0944_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0945_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (67019/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0946_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0947_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (33511/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (67021/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0948_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0949_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (67023/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0950_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0951_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0059_checked
#print axioms SmaleRate.Proofs.cover8_tree0059_checked
