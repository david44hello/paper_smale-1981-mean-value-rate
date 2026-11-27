/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.DyadicAssembly
import SmaleRate.Proofs.Generated.D8Chunk0016

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0026 : BoxTree := (.split (.split (.split (.split (.leaf (513725984233/250000000000 : ℚ)) (.leaf (410980778391/200000000000 : ℚ))) (.split (.leaf (1027451923577/500000000000 : ℚ)) (.leaf (1027451901249/500000000000 : ℚ)))) (.split (.split (.leaf (205490375801/100000000000 : ℚ)) (.leaf (25686296421/12500000000 : ℚ))) (.split (.leaf (513725917377/250000000000 : ℚ)) (.leaf (2054903625497/1000000000000 : ℚ))))) (.split (.split (.split (.leaf (51372589541/25000000000 : ℚ)) (.leaf (410980707591/200000000000 : ℚ))) (.split (.leaf (2054903494433/1000000000000 : ℚ)) (.leaf (1027451725531/500000000000 : ℚ)))) (.split (.split (.leaf (2054903407873/1000000000000 : ℚ)) (.leaf (2054903364817/1000000000000 : ℚ))) (.split (.leaf (102745166097/50000000000 : ℚ)) (.leaf (2054903279217/1000000000000 : ℚ))))))

theorem cover8_tree0026_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0026 (1037/8192 : ℚ) (2075/16384 : ℚ) := by
  unfold cover8_tree0026
  refine tree_all_split_at (4149/32768 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (8297/65536 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (16593/131072 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (33185/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0404_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0405_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (33187/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0406_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0407_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (16595/131072 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (33189/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0408_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0409_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (33191/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0410_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0411_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (8299/65536 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (16597/131072 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (33193/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0412_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0413_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (33195/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0414_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0415_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (16599/131072 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (33197/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0416_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0417_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (33199/262144 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0418_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0419_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0026_checked
#print axioms SmaleRate.Proofs.cover8_tree0026_checked
