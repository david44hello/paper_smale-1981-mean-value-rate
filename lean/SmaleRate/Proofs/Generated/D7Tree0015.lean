/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.DyadicAssembly
import SmaleRate.Proofs.Generated.D7Chunk0008
import SmaleRate.Proofs.Generated.D7Chunk0009

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover7_tree0015 : BoxTree := (.split (.split (.split (.split (.leaf (2019019748281/1000000000000 : ℚ)) (.leaf (1009509765193/500000000000 : ℚ))) (.split (.leaf (1009509657419/500000000000 : ℚ)) (.leaf (31547173463/15625000000 : ℚ)))) (.split (.split (.leaf (2019018890769/1000000000000 : ℚ)) (.leaf (403803736453/200000000000 : ℚ))) (.split (.leaf (201901847611/100000000000 : ℚ)) (.leaf (1009509136143/500000000000 : ℚ))))) (.split (.split (.split (.leaf (1009509035401/500000000000 : ℚ)) (.leaf (2019017871677/1000000000000 : ℚ))) (.split (.leaf (403803534977/200000000000 : ℚ)) (.leaf (504754370111/250000000000 : ℚ)))) (.split (.split (.leaf (504754322083/250000000000 : ℚ)) (.leaf (2019017098571/1000000000000 : ℚ))) (.split (.leaf (504754227789/250000000000 : ℚ)) (.leaf (2019016726071/1000000000000 : ℚ))))))

theorem cover7_tree0015_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 7 box ∧ (2019/1000 : ℝ) < (box.lower : ℝ)) cover7_tree0015 (69/512 : ℚ) (553/4096 : ℚ) := by
  unfold cover7_tree0015
  refine tree_all_split_at (1105/8192 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (2209/16384 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (4417/32768 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (8833/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0222_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0223_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (8835/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0224_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0225_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (4419/32768 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (8837/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0226_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0227_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (8839/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0228_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0229_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (2211/16384 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (4421/32768 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (8841/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0230_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0231_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (8843/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0232_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0233_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (4423/32768 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (8845/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0234_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0235_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (8847/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0236_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0237_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover7_tree0015_checked
#print axioms SmaleRate.Proofs.cover7_tree0015_checked
