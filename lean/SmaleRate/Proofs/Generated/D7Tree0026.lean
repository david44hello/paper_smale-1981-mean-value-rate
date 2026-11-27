/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.DyadicAssembly
import SmaleRate.Proofs.Generated.D7Chunk0015
import SmaleRate.Proofs.Generated.D7Chunk0016

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover7_tree0026 : BoxTree := (.split (.split (.split (.split (.leaf (252377141793/125000000000 : ℚ)) (.leaf (2019017322521/1000000000000 : ℚ))) (.split (.leaf (2019017512947/1000000000000 : ℚ)) (.leaf (1009508852819/500000000000 : ℚ)))) (.split (.split (.leaf (1009508950297/500000000000 : ℚ)) (.leaf (1009509048913/500000000000 : ℚ))) (.split (.leaf (201901829733/100000000000 : ℚ)) (.leaf (1009509249543/500000000000 : ℚ))))) (.split (.split (.split (.leaf (1009509351557/500000000000 : ℚ)) (.leaf (1009509454703/500000000000 : ℚ))) (.split (.leaf (1009509558981/500000000000 : ℚ)) (.leaf (1009509664389/500000000000 : ℚ)))) (.split (.split (.leaf (504754885463/250000000000 : ℚ)) (.leaf (1009509878603/500000000000 : ℚ))) (.split (.leaf (504754993703/250000000000 : ℚ)) (.leaf (1009510097337/500000000000 : ℚ))))))

theorem cover7_tree0026_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 7 box ∧ (2019/1000 : ℝ) < (box.lower : ℝ)) cover7_tree0026 (563/4096 : ℚ) (141/1024 : ℚ) := by
  unfold cover7_tree0026
  refine tree_all_split_at (1127/8192 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (2253/16384 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (4505/32768 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (9009/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0398_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0399_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (9011/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0400_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0401_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (4507/32768 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (9013/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0402_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0403_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (9015/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0404_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0405_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (2255/16384 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (4509/32768 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (9017/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0406_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0407_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (9019/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0408_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0409_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (4511/32768 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (9021/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0410_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0411_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (9023/65536 : ℚ) (by norm_num) ?_ ?_
        · convert cover7_leaf0412_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover7_leaf0413_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover7_tree0026_checked
#print axioms SmaleRate.Proofs.cover7_tree0026_checked
