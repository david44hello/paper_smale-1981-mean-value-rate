/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.DyadicAssembly
public import SmaleRate.Proofs.Generated.D7Chunk0006
public import SmaleRate.Proofs.Generated.D7Chunk0007

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover7_tree0012 : BoxTree := (.split (.split (.split (.split (.leaf (1009503710107/500000000000 : ℚ)) (.leaf (63093959037/31250000000 : ℚ))) (.split (.leaf (1009502983823/500000000000 : ℚ)) (.leaf (1009502627809/500000000000 : ℚ)))) (.split (.split (.leaf (2019004553081/1000000000000 : ℚ)) (.leaf (504750965013/250000000000 : ℚ))) (.split (.leaf (2019003176493/1000000000000 : ℚ)) (.leaf (2019002502437/1000000000000 : ℚ))))) (.split (.split (.split (.leaf (1009500918927/500000000000 : ℚ)) (.leaf (2019001182759/1000000000000 : ℚ))) (.split (.leaf (2019000537123/1000000000000 : ℚ)) (.split (.leaf (1009515512799/500000000000 : ℚ)) (.leaf (2019030708697/1000000000000 : ℚ))))) (.split (.split (.split (.leaf (2019030394161/1000000000000 : ℚ)) (.leaf (2019030082007/1000000000000 : ℚ))) (.split (.leaf (2019029772199/1000000000000 : ℚ)) (.leaf (2019029464763/1000000000000 : ℚ)))) (.split (.split (.leaf (126189322481/62500000000 : ℚ)) (.leaf (2019028856987/1000000000000 : ℚ))) (.split (.leaf (2019028556649/1000000000000 : ℚ)) (.leaf (2019028258679/1000000000000 : ℚ)))))))

theorem cover7_tree0012_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 7 box ∧ (2019/1000 : ℝ) < (box.lower : ℝ)) cover7_tree0012 (137/1024 : ℚ) (275/2048 : ℚ) := by
  unfold cover7_tree0012
  refine tree_all_split_at (549/4096 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (1097/8192 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (2193/16384 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (4385/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0169_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0170_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (4387/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0171_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0172_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (2195/16384 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (4389/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0173_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0174_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (4391/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0175_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0176_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (1099/8192 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (2197/16384 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (4393/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0177_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0178_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (4395/32768 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0179_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · refine tree_all_split_at (8791/65536 : ℚ) (by norm_num) ?_ ?_
          · convert cover7_leaf0180_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
          · convert cover7_leaf0181_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (2199/16384 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (4397/32768 : ℚ) (by norm_num) ?_ ?_
        · refine tree_all_split_at (8793/65536 : ℚ) (by norm_num) ?_ ?_
          · convert cover7_leaf0182_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
          · convert cover7_leaf0183_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
        · refine tree_all_split_at (8795/65536 : ℚ) (by norm_num) ?_ ?_
          · convert cover7_leaf0184_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
          · convert cover7_leaf0185_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (4399/32768 : ℚ) (by norm_num) ?_ ?_
        · refine tree_all_split_at (8797/65536 : ℚ) (by norm_num) ?_ ?_
          · convert cover7_leaf0186_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
          · convert cover7_leaf0187_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
        · refine tree_all_split_at (8799/65536 : ℚ) (by norm_num) ?_ ?_
          · convert cover7_leaf0188_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]
          · convert cover7_leaf0189_certificate hidentity using 1 <;>
              norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover7_tree0012_checked
#print axioms SmaleRate.Proofs.cover7_tree0012_checked
