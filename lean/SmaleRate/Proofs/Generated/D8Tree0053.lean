/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.DyadicAssembly
public import SmaleRate.Proofs.Generated.D8Chunk0033
public import SmaleRate.Proofs.Generated.D8Chunk0034

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0053 : BoxTree := (.split (.split (.split (.split (.leaf (2054901538553/1000000000000 : ℚ)) (.leaf (1027450768891/500000000000 : ℚ))) (.split (.leaf (2054901537049/1000000000000 : ℚ)) (.leaf (64215673011/31250000000 : ℚ)))) (.split (.split (.leaf (20549015357/10000000000 : ℚ)) (.leaf (410980307017/200000000000 : ℚ))) (.split (.leaf (2054901534511/1000000000000 : ℚ)) (.leaf (2054901533969/1000000000000 : ℚ))))) (.split (.split (.split (.leaf (2054901533477/1000000000000 : ℚ)) (.leaf (2054901533031/1000000000000 : ℚ))) (.split (.leaf (410980306521/200000000000 : ℚ)) (.leaf (1027450766111/500000000000 : ℚ)))) (.split (.split (.leaf (1027450765949/500000000000 : ℚ)) (.leaf (410980306319/200000000000 : ℚ))) (.split (.leaf (1027450765671/500000000000 : ℚ)) (.leaf (410980306223/200000000000 : ℚ))))))

theorem cover8_tree0053_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0053 (2091/16384 : ℚ) (4183/32768 : ℚ) := by
  unfold cover8_tree0053
  refine tree_all_split_at (8365/65536 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (16729/131072 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (33457/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66913/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0840_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0841_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66915/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0842_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0843_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (33459/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66917/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0844_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0845_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66919/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0846_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0847_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (16731/131072 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (33461/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66921/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0848_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0849_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66923/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0850_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0851_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (33463/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66925/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0852_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0853_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66927/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0854_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0855_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0053_checked
#print axioms SmaleRate.Proofs.cover8_tree0053_checked
