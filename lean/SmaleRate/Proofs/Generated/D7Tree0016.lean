/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.DyadicAssembly
public import SmaleRate.Proofs.Generated.D7Chunk0009
public import SmaleRate.Proofs.Generated.D7Chunk0010

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover7_tree0016 : BoxTree := (.split (.split (.split (.split (.leaf (1009508271667/500000000000 : ℚ)) (.leaf (2019016362941/1000000000000 : ℚ))) (.split (.leaf (504754046219/250000000000 : ℚ)) (.leaf (403803201831/200000000000 : ℚ)))) (.split (.split (.leaf (1009507917891/500000000000 : ℚ)) (.leaf (2019015664731/1000000000000 : ℚ))) (.split (.leaf (63094234251/31250000000 : ℚ)) (.leaf (504753832417/250000000000 : ℚ))))) (.split (.split (.split (.leaf (2019015165637/1000000000000 : ℚ)) (.leaf (252376875493/125000000000 : ℚ))) (.split (.leaf (504753711147/250000000000 : ℚ)) (.leaf (2019014687559/1000000000000 : ℚ)))) (.split (.split (.leaf (504753633219/250000000000 : ℚ)) (.leaf (504753595133/250000000000 : ℚ))) (.split (.leaf (2019014230507/1000000000000 : ℚ)) (.leaf (1009507041411/500000000000 : ℚ))))))

theorem cover7_tree0016_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 7 box ∧ (2019/1000 : ℝ) < (box.lower : ℝ)) cover7_tree0016 (553/4096 : ℚ) (277/2048 : ℚ) := by
  unfold cover7_tree0016
  refine tree_all_split_at (1107/8192 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (2213/16384 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (4425/32768 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (8849/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0238_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0239_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (8851/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0240_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0241_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (4427/32768 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (8853/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0242_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0243_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (8855/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0244_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0245_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (2215/16384 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (4429/32768 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (8857/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0246_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0247_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (8859/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0248_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0249_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (4431/32768 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (8861/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0250_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0251_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (8863/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0252_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0253_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover7_tree0016_checked
#print axioms SmaleRate.Proofs.cover7_tree0016_checked
