/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.DyadicAssembly
import SmaleRate.Proofs.Generated.D8Chunk0028
import SmaleRate.Proofs.Generated.D8Chunk0029

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree0045 : BoxTree := (.split (.split (.split (.split (.leaf (51372549151/25000000000 : ℚ)) (.leaf (2054901960177/1000000000000 : ℚ))) (.split (.leaf (410980390871/200000000000 : ℚ)) (.leaf (2054901948547/1000000000000 : ℚ)))) (.split (.split (.leaf (410980388561/200000000000 : ℚ)) (.leaf (410980387419/200000000000 : ℚ))) (.split (.leaf (2054901931429/1000000000000 : ℚ)) (.leaf (1027450962899/500000000000 : ℚ))))) (.split (.split (.split (.leaf (128431370013/62500000000 : ℚ)) (.leaf (2054901914657/1000000000000 : ℚ))) (.split (.leaf (2054901909159/1000000000000 : ℚ)) (.leaf (513725475921/250000000000 : ℚ)))) (.split (.split (.leaf (256862737281/125000000000 : ℚ)) (.leaf (2054901892853/1000000000000 : ℚ))) (.split (.leaf (1027450943757/500000000000 : ℚ)) (.leaf (2054901882193/1000000000000 : ℚ))))))

theorem cover8_tree0045_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree0045 (2087/16384 : ℚ) (4175/32768 : ℚ) := by
  unfold cover8_tree0045
  refine tree_all_split_at (8349/65536 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (16697/131072 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (33393/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66785/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0712_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0713_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66787/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0714_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0715_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (33395/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66789/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0716_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0717_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66791/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0718_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0719_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
  · refine tree_all_split_at (16699/131072 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (33397/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66793/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0720_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0721_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66795/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0722_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0723_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
    · refine tree_all_split_at (33399/262144 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (66797/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0724_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0725_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
      · refine tree_all_split_at (66799/524288 : ℚ) (by norm_num) ?_ ?_
        · convert cover8_leaf0726_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]
        · convert cover8_leaf0727_certificate hidentity using 1 <;>
            norm_num [treeAll, BoxEndpointBound]

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_tree0045_checked
#print axioms SmaleRate.Proofs.cover8_tree0045_checked
