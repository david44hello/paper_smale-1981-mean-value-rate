/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.DyadicAssembly
public import SmaleRate.Proofs.Generated.D7Chunk0000

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover7_tree0002 : BoxTree := (.split (.split (.leaf (252503895051/125000000000 : ℚ)) (.split (.leaf (505753958357/250000000000 : ℚ)) (.leaf (202211721393/100000000000 : ℚ)))) (.split (.split (.leaf (505320561939/250000000000 : ℚ)) (.leaf (505127193889/250000000000 : ℚ))) (.split (.leaf (1009897376417/500000000000 : ℚ)) (.leaf (3230621187/1600000000 : ℚ)))))

theorem cover7_tree0002_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 7 box ∧ (2019/1000 : ℝ) < (box.lower : ℝ)) cover7_tree0002 (3/32 : ℚ) (7/64 : ℚ) := by
  unfold cover7_tree0002
  refine tree_all_split_at (13/128 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (25/256 : ℚ) (by norm_num) ?_ ?_
    · convert cover7_leaf0008_certificate hidentity using 1 <;>
        norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (51/512 : ℚ) (by norm_num) ?_ ?_
      · convert cover7_leaf0009_certificate hidentity using 1 <;>
          norm_num [treeAll, BoxEndpointBound]
      · convert cover7_leaf0010_certificate hidentity using 1 <;>
          norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (27/256 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (53/512 : ℚ) (by norm_num) ?_ ?_
      · convert cover7_leaf0011_certificate hidentity using 1 <;>
          norm_num [treeAll, BoxEndpointBound]
      · convert cover7_leaf0012_certificate hidentity using 1 <;>
          norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (55/512 : ℚ) (by norm_num) ?_ ?_
      · convert cover7_leaf0013_certificate hidentity using 1 <;>
          norm_num [treeAll, BoxEndpointBound]
      · convert cover7_leaf0014_certificate hidentity using 1 <;>
          norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover7_tree0002_checked
#print axioms SmaleRate.Proofs.cover7_tree0002_checked
