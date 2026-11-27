/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.DyadicAssembly
public import SmaleRate.Proofs.Generated.D7Chunk0014
public import SmaleRate.Proofs.Generated.D7Chunk0015

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover7_tree0024 : BoxTree := (.split (.split (.split (.split (.leaf (504753078253/250000000000 : ℚ)) (.leaf (1009506214189/500000000000 : ℚ))) (.split (.leaf (504753136509/250000000000 : ℚ)) (.leaf (50475316649/25000000000 : ℚ)))) (.split (.split (.leaf (2019012788171/1000000000000 : ℚ)) (.leaf (2019012912669/1000000000000 : ℚ))) (.split (.leaf (2019013039449/1000000000000 : ℚ)) (.leaf (2019013168503/1000000000000 : ℚ))))) (.split (.split (.split (.leaf (1009506649917/500000000000 : ℚ)) (.leaf (1009506716719/500000000000 : ℚ))) (.split (.leaf (126188348083/62500000000 : ℚ)) (.leaf (2019013707499/1000000000000 : ℚ)))) (.split (.split (.leaf (40380276959/20000000000 : ℚ)) (.leaf (504753497667/250000000000 : ℚ))) (.split (.leaf (1009507067833/500000000000 : ℚ)) (.leaf (403802856587/200000000000 : ℚ))))))

theorem cover7_tree0024_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 7 box ∧ (2019/1000 : ℝ) < (box.lower : ℝ)) cover7_tree0024 (561/4096 : ℚ) (281/2048 : ℚ) := by
  unfold cover7_tree0024
  refine tree_all_split_at (1123/8192 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (2245/16384 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (4489/32768 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (8977/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0366_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0367_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (8979/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0368_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0369_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (4491/32768 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (8981/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0370_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0371_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (8983/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0372_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0373_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (2247/16384 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (4493/32768 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (8985/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0374_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0375_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (8987/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0376_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0377_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (4495/32768 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (8989/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0378_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0379_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (8991/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0380_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0381_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover7_tree0024_checked
#print axioms SmaleRate.Proofs.cover7_tree0024_checked
