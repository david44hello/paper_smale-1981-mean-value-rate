/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.DyadicAssembly
import SmaleRate.Proofs.Generated.D7Chunk0014

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover7_tree0023 : BoxTree := (.split (.split (.split (.split (.leaf (2019010777739/1000000000000 : ℚ)) (.leaf (1009505428277/500000000000 : ℚ))) (.split (.leaf (2019010937639/1000000000000 : ℚ)) (.leaf (80760440841/40000000000 : ℚ)))) (.split (.split (.leaf (403802221339/200000000000 : ℚ)) (.leaf (252376399331/125000000000 : ℚ))) (.split (.leaf (2019011284891/1000000000000 : ℚ)) (.leaf (2019011377411/1000000000000 : ℚ))))) (.split (.split (.split (.leaf (1009505736121/500000000000 : ℚ)) (.leaf (31547055771/15625000000 : ℚ))) (.split (.leaf (25237645859/12500000000 : ℚ)) (.leaf (201901177039/100000000000 : ℚ)))) (.split (.split (.leaf (2019011874343/1000000000000 : ℚ)) (.leaf (2019011980593/1000000000000 : ℚ))) (.split (.leaf (2019012089111/1000000000000 : ℚ)) (.leaf (2019012199917/1000000000000 : ℚ))))))

theorem cover7_tree0023_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 7 box ∧ (2019/1000 : ℝ) < (box.lower : ℝ)) cover7_tree0023 (35/256 : ℚ) (561/4096 : ℚ) := by
  unfold cover7_tree0023
  refine tree_all_split_at (1121/8192 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (2241/16384 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (4481/32768 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (8961/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0350_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0351_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (8963/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0352_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0353_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (4483/32768 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (8965/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0354_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0355_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (8967/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0356_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0357_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (2243/16384 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (4485/32768 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (8969/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0358_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0359_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (8971/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0360_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0361_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (4487/32768 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (8973/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0362_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0363_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (8975/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0364_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0365_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover7_tree0023_checked
#print axioms SmaleRate.Proofs.cover7_tree0023_checked
