/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.DyadicAssembly
public import SmaleRate.Proofs.Generated.D7Chunk0012

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover7_tree0020 : BoxTree := (.split (.split (.split (.split (.leaf (1009504847759/500000000000 : ℚ)) (.leaf (504752415983/250000000000 : ℚ))) (.split (.leaf (2019009634651/1000000000000 : ℚ)) (.leaf (403801921539/200000000000 : ℚ)))) (.split (.split (.leaf (403801916609/200000000000 : ℚ)) (.leaf (2019009560691/1000000000000 : ℚ))) (.split (.leaf (100950477033/50000000000 : ℚ)) (.leaf (2019009522921/1000000000000 : ℚ))))) (.split (.split (.split (.leaf (1009504753753/500000000000 : ℚ)) (.leaf (2019009494387/1000000000000 : ℚ))) (.split (.leaf (2019009483581/1000000000000 : ℚ)) (.leaf (126188092193/62500000000 : ℚ)))) (.split (.split (.leaf (2019009468889/1000000000000 : ℚ)) (.leaf (2019009465001/1000000000000 : ℚ))) (.split (.leaf (504752365853/250000000000 : ℚ)) (.leaf (2019009464139/1000000000000 : ℚ))))))

theorem cover7_tree0020_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 7 box ∧ (2019/1000 : ℝ) < (box.lower : ℝ)) cover7_tree0020 (557/4096 : ℚ) (279/2048 : ℚ) := by
  unfold cover7_tree0020
  refine tree_all_split_at (1115/8192 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (2229/16384 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (4457/32768 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (8913/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0302_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0303_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (8915/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0304_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0305_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (4459/32768 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (8917/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0306_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0307_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (8919/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0308_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0309_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (2231/16384 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (4461/32768 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (8921/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0310_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0311_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (8923/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0312_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0313_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (4463/32768 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (8925/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0314_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0315_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (8927/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0316_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0317_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover7_tree0020_checked
#print axioms SmaleRate.Proofs.cover7_tree0020_checked
