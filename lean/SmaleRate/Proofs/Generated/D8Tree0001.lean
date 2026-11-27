/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.DyadicAssembly
public import SmaleRate.Proofs.Generated.D8Chunk0000

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0001 : BoxTree := (.split (.split (.leaf (1031897248593/500000000000 : ℚ)) (.leaf (2056455425947/1000000000000 : ℚ))) (.split (.split (.leaf (515361109157/250000000000 : ℚ)) (.leaf (2058753002269/1000000000000 : ℚ))) (.split (.leaf (411279956013/200000000000 : ℚ)) (.split (.leaf (2059359890363/1000000000000 : ℚ)) (.leaf (2058374734679/1000000000000 : ℚ))))))

theorem cover8_tree0001_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0001 (1/16 : ℚ) (3/32 : ℚ) := by
  unfold cover8_tree0001
  refine tree_all_split_at (5/64 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (9/128 : ℚ) (by norm_num) ?_ ?_
    · convert cover8_leaf0003_certificate hidentity using 1 <;>
        norm_num [treeAll, BoxEndpointBound]
    · convert cover8_leaf0004_certificate hidentity using 1 <;>
        norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (11/128 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (21/256 : ℚ) (by norm_num) ?_ ?_
      · convert cover8_leaf0005_certificate hidentity using 1 <;>
          norm_num [treeAll, BoxEndpointBound]
      · convert cover8_leaf0006_certificate hidentity using 1 <;>
          norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (23/256 : ℚ) (by norm_num) ?_ ?_
      · convert cover8_leaf0007_certificate hidentity using 1 <;>
          norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (47/512 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0008_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0009_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0001_checked
#print axioms SmaleRate.Proofs.cover8_tree0001_checked
