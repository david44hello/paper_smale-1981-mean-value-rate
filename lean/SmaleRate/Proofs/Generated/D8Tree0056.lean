/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.DyadicAssembly
public import SmaleRate.Proofs.Generated.D8Chunk0035
public import SmaleRate.Proofs.Generated.D8Chunk0036

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0056 : BoxTree := (.split (.split (.split (.split (.leaf (2054901546231/1000000000000 : ℚ)) (.leaf (2054901547373/1000000000000 : ℚ))) (.split (.leaf (2054901548533/1000000000000 : ℚ)) (.leaf (2054901549757/1000000000000 : ℚ)))) (.split (.split (.leaf (513725387753/250000000000 : ℚ)) (.leaf (2054901552287/1000000000000 : ℚ))) (.split (.leaf (256862694203/125000000000 : ℚ)) (.leaf (1027450777499/500000000000 : ℚ))))) (.split (.split (.split (.leaf (2054901556411/1000000000000 : ℚ)) (.leaf (2054901557859/1000000000000 : ℚ))) (.split (.leaf (256862694919/125000000000 : ℚ)) (.leaf (25686269511/12500000000 : ℚ)))) (.split (.split (.leaf (2054901562447/1000000000000 : ℚ)) (.leaf (410980312811/200000000000 : ℚ))) (.split (.leaf (2054901565711/1000000000000 : ℚ)) (.leaf (2054901567397/1000000000000 : ℚ))))))

theorem cover8_tree0056_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0056 (4185/32768 : ℚ) (2093/16384 : ℚ) := by
  unfold cover8_tree0056
  refine tree_all_split_at (8371/65536 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (16741/131072 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (33481/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66961/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0888_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0889_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66963/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0890_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0891_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (33483/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66965/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0892_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0893_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66967/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0894_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0895_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (16743/131072 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (33485/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66969/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0896_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0897_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66971/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0898_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0899_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (33487/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66973/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0900_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0901_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66975/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0902_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0903_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0056_checked
#print axioms SmaleRate.Proofs.cover8_tree0056_checked
