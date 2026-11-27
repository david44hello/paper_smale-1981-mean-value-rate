/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.DyadicAssembly
public import SmaleRate.Proofs.Generated.D8Chunk0038
public import SmaleRate.Proofs.Generated.D8Chunk0039

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0061 : BoxTree := (.split (.split (.split (.split (.leaf (513725440549/250000000000 : ℚ)) (.leaf (1027450883251/500000000000 : ℚ))) (.split (.leaf (102745088543/50000000000 : ℚ)) (.leaf (1027450887621/500000000000 : ℚ)))) (.split (.split (.leaf (205490177967/100000000000 : ℚ)) (.leaf (513725446031/250000000000 : ℚ))) (.split (.leaf (128431361789/62500000000 : ℚ)) (.leaf (2054901793179/1000000000000 : ℚ))))) (.split (.split (.split (.leaf (1027450898877/500000000000 : ℚ)) (.leaf (2054901802361/1000000000000 : ℚ))) (.split (.leaf (410980361407/200000000000 : ℚ)) (.leaf (2054901811727/1000000000000 : ℚ)))) (.split (.split (.leaf (2054901816473/1000000000000 : ℚ)) (.leaf (2054901821261/1000000000000 : ℚ))) (.split (.leaf (513725456517/250000000000 : ℚ)) (.leaf (513725457733/250000000000 : ℚ))))))

theorem cover8_tree0061_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0061 (2095/16384 : ℚ) (4191/32768 : ℚ) := by
  unfold cover8_tree0061
  refine tree_all_split_at (8381/65536 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (16761/131072 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (33521/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (67041/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0968_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0969_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (67043/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0970_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0971_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (33523/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (67045/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0972_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0973_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (67047/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0974_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0975_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (16763/131072 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (33525/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (67049/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0976_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0977_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (67051/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0978_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0979_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (33527/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (67053/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0980_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0981_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (67055/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0982_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0983_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0061_checked
#print axioms SmaleRate.Proofs.cover8_tree0061_checked
