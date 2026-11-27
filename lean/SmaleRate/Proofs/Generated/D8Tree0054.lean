/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.DyadicAssembly
import SmaleRate.Proofs.Generated.D8Chunk0034

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0054 : BoxTree := (.split (.split (.split (.split (.leaf (1027450765471/500000000000 : ℚ)) (.leaf (205490153081/100000000000 : ℚ))) (.split (.leaf (1027450765357/500000000000 : ℚ)) (.leaf (25686269133/12500000000 : ℚ)))) (.split (.split (.leaf (2054901530629/1000000000000 : ℚ)) (.leaf (256862691331/125000000000 : ℚ))) (.split (.leaf (2054901530709/1000000000000 : ℚ)) (.leaf (2054901530809/1000000000000 : ℚ))))) (.split (.split (.split (.leaf (2054901530967/1000000000000 : ℚ)) (.leaf (2054901531143/1000000000000 : ℚ))) (.split (.leaf (513725382839/250000000000 : ℚ)) (.leaf (513725382903/250000000000 : ℚ)))) (.split (.split (.leaf (2054901531923/1000000000000 : ℚ)) (.leaf (2054901532251/1000000000000 : ℚ))) (.split (.leaf (102745076631/50000000000 : ℚ)) (.leaf (2054901533049/1000000000000 : ℚ))))))

theorem cover8_tree0054_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0054 (4183/32768 : ℚ) (523/4096 : ℚ) := by
  unfold cover8_tree0054
  refine tree_all_split_at (8367/65536 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (16733/131072 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (33465/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66929/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0856_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0857_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66931/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0858_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0859_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (33467/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66933/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0860_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0861_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66935/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0862_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0863_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (16735/131072 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (33469/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66937/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0864_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0865_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66939/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0866_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0867_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (33471/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66941/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0868_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0869_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66943/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0870_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0871_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0054_checked
#print axioms SmaleRate.Proofs.cover8_tree0054_checked
