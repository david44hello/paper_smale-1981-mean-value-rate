/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.DyadicAssembly
import SmaleRate.Proofs.Generated.D7Chunk0008

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover7_tree0014 : BoxTree := (.split (.split (.split (.split (.leaf (2019023554221/1000000000000 : ℚ)) (.leaf (252377912337/125000000000 : ℚ))) (.split (.leaf (2019023045551/1000000000000 : ℚ)) (.leaf (201902279473/100000000000 : ℚ)))) (.split (.split (.leaf (2019022546289/1000000000000 : ℚ)) (.leaf (2019022300189/1000000000000 : ℚ))) (.split (.leaf (50475551411/25000000000 : ℚ)) (.leaf (126188863441/62500000000 : ℚ))))) (.split (.split (.split (.leaf (1009510788007/500000000000 : ℚ)) (.leaf (2019021339323/1000000000000 : ℚ))) (.split (.leaf (2019021104977/1000000000000 : ℚ)) (.leaf (2019020872983/1000000000000 : ℚ)))) (.split (.split (.leaf (504755160837/250000000000 : ℚ)) (.leaf (2019020416063/1000000000000 : ℚ))) (.split (.leaf (25237752389/12500000000 : ℚ)) (.leaf (2019019968519/1000000000000 : ℚ))))))

theorem cover7_tree0014_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 7 box ∧ (2019/1000 : ℝ) < (box.lower : ℝ)) cover7_tree0014 (551/4096 : ℚ) (69/512 : ℚ) := by
  unfold cover7_tree0014
  refine tree_all_split_at (1103/8192 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (2205/16384 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (4409/32768 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (8817/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0206_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0207_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (8819/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0208_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0209_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (4411/32768 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (8821/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0210_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0211_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (8823/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0212_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0213_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (2207/16384 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (4413/32768 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (8825/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0214_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0215_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (8827/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0216_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0217_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (4415/32768 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (8829/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0218_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0219_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (8831/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0220_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0221_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover7_tree0014_checked
#print axioms SmaleRate.Proofs.cover7_tree0014_checked
