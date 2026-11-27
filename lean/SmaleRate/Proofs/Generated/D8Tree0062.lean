/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.DyadicAssembly
public import SmaleRate.Proofs.Generated.D8Chunk0039

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0062 : BoxTree := (.split (.split (.split (.split (.leaf (256862729479/125000000000 : ℚ)) (.leaf (2054901840773/1000000000000 : ℚ))) (.split (.leaf (2054901845751/1000000000000 : ℚ)) (.leaf (2054901850769/1000000000000 : ℚ)))) (.split (.split (.leaf (2054901855827/1000000000000 : ℚ)) (.leaf (513725465231/250000000000 : ℚ))) (.split (.leaf (410980373211/200000000000 : ℚ)) (.leaf (2054901871247/1000000000000 : ℚ))))) (.split (.split (.split (.leaf (410980375291/200000000000 : ℚ)) (.leaf (410980376341/200000000000 : ℚ))) (.split (.leaf (513725471753/250000000000 : ℚ)) (.leaf (2054901892339/1000000000000 : ℚ)))) (.split (.split (.leaf (256862737213/125000000000 : ℚ)) (.leaf (513725475781/250000000000 : ℚ))) (.split (.leaf (410980381717/200000000000 : ℚ)) (.leaf (2054901914063/1000000000000 : ℚ))))))

theorem cover8_tree0062_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0062 (4191/32768 : ℚ) (131/1024 : ℚ) := by
  unfold cover8_tree0062
  refine tree_all_split_at (8383/65536 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (16765/131072 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (33529/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (67057/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0984_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0985_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (67059/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0986_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0987_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (33531/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (67061/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0988_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0989_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (67063/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0990_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0991_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (16767/131072 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (33533/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (67065/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0992_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0993_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (67067/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0994_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0995_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (33535/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (67069/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0996_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0997_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (67071/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0998_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0999_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0062_checked
#print axioms SmaleRate.Proofs.cover8_tree0062_checked
