/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.DyadicAssembly
import SmaleRate.Proofs.Generated.D8Chunk0023

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0037 : BoxTree := (.split (.split (.split (.split (.leaf (1027451523433/500000000000 : ℚ)) (.leaf (1027451517949/500000000000 : ℚ))) (.split (.leaf (1027451512471/500000000000 : ℚ)) (.leaf (2054903014047/1000000000000 : ℚ)))) (.split (.split (.leaf (2054903003177/1000000000000 : ℚ)) (.leaf (1027451496179/500000000000 : ℚ))) (.split (.leaf (2054902981579/1000000000000 : ℚ)) (.leaf (410980594169/200000000000 : ℚ))))) (.split (.split (.split (.leaf (410980592029/200000000000 : ℚ)) (.leaf (2054902949483/1000000000000 : ℚ))) (.split (.leaf (2054902938863/1000000000000 : ℚ)) (.leaf (82196117131/40000000000 : ℚ)))) (.split (.split (.leaf (2054902917733/1000000000000 : ℚ)) (.leaf (82196116289/40000000000 : ℚ))) (.split (.leaf (2054902896761/1000000000000 : ℚ)) (.leaf (41098057727/20000000000 : ℚ))))))

theorem cover8_tree0037_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0037 (2083/16384 : ℚ) (4167/32768 : ℚ) := by
  unfold cover8_tree0037
  refine tree_all_split_at (8333/65536 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (16665/131072 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (33329/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66657/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0584_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0585_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66659/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0586_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0587_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (33331/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66661/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0588_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0589_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66663/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0590_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0591_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (16667/131072 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (33333/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66665/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0592_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0593_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66667/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0594_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0595_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (33335/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66669/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0596_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0597_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66671/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0598_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0599_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0037_checked
#print axioms SmaleRate.Proofs.cover8_tree0037_checked
