/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.DyadicAssembly
import SmaleRate.Proofs.Generated.D7Chunk0015

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover7_tree0025 : BoxTree := (.split (.split (.split (.split (.leaf (2019014432483/1000000000000 : ℚ)) (.leaf (2019014584307/1000000000000 : ℚ))) (.split (.leaf (2019014738399/1000000000000 : ℚ)) (.leaf (2019014894769/1000000000000 : ℚ)))) (.split (.split (.leaf (1009507526709/500000000000 : ℚ)) (.leaf (403803042867/200000000000 : ℚ))) (.split (.leaf (1009507688761/500000000000 : ℚ)) (.leaf (2019015542991/1000000000000 : ℚ))))) (.split (.split (.split (.leaf (2019015710737/1000000000000 : ℚ)) (.leaf (252376985093/125000000000 : ℚ))) (.split (.leaf (2019016053009/1000000000000 : ℚ)) (.leaf (2019016227569/1000000000000 : ℚ)))) (.split (.split (.leaf (2019016404389/1000000000000 : ℚ)) (.leaf (2019016583467/1000000000000 : ℚ))) (.split (.leaf (504754191209/250000000000 : ℚ)) (.leaf (2019016948459/1000000000000 : ℚ))))))

theorem cover7_tree0025_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 7 box ∧ (2019/1000 : ℝ) < (box.lower : ℝ)) cover7_tree0025 (281/2048 : ℚ) (563/4096 : ℚ) := by
  unfold cover7_tree0025
  refine tree_all_split_at (1125/8192 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (2249/16384 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (4497/32768 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (8993/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0382_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0383_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (8995/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0384_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0385_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (4499/32768 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (8997/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0386_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0387_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (8999/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0388_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0389_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (2251/16384 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (4501/32768 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (9001/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0390_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0391_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (9003/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0392_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0393_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (4503/32768 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (9005/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0394_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0395_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (9007/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0396_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0397_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover7_tree0025_checked
#print axioms SmaleRate.Proofs.cover7_tree0025_checked
