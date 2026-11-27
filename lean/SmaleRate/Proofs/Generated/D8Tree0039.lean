/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.DyadicAssembly
import SmaleRate.Proofs.Generated.D8Chunk0024
import SmaleRate.Proofs.Generated.D8Chunk0025

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0039 : BoxTree := (.split (.split (.split (.split (.leaf (2054902715291/1000000000000 : ℚ)) (.leaf (410980541117/200000000000 : ℚ))) (.split (.leaf (513725673983/250000000000 : ℚ)) (.leaf (64215708947/31250000000 : ℚ)))) (.split (.split (.leaf (205490267673/100000000000 : ℚ)) (.leaf (102745133359/50000000000 : ℚ))) (.split (.leaf (2054902657681/1000000000000 : ℚ)) (.leaf (1027451324107/500000000000 : ℚ))))) (.split (.split (.split (.leaf (2054902638791/1000000000000 : ℚ)) (.leaf (1027451314707/500000000000 : ℚ))) (.split (.leaf (1027451310039/500000000000 : ℚ)) (.leaf (2054902610779/1000000000000 : ℚ)))) (.split (.split (.leaf (1027451300751/500000000000 : ℚ)) (.leaf (2054902592277/1000000000000 : ℚ))) (.split (.leaf (410980516619/200000000000 : ℚ)) (.leaf (128431410873/62500000000 : ℚ))))))

theorem cover8_tree0039_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0039 (521/4096 : ℚ) (4169/32768 : ℚ) := by
  unfold cover8_tree0039
  refine tree_all_split_at (8337/65536 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (16673/131072 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (33345/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66689/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0616_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0617_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66691/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0618_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0619_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (33347/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66693/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0620_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0621_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66695/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0622_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0623_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (16675/131072 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (33349/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66697/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0624_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0625_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66699/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0626_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0627_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (33351/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66701/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0628_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0629_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66703/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0630_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0631_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0039_checked
#print axioms SmaleRate.Proofs.cover8_tree0039_checked
