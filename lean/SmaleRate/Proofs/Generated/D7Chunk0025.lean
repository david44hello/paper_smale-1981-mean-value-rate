/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.AGMCertificates

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

-- Proposed record cover7_leaf0625; no trusted numerical premise.
theorem cover7_leaf0625_exp_radius : (996935508739860837/1000000000000000000 : ℝ) ≤ Real.exp ((-11/448 : ℝ)/8) ∧ Real.exp ((-11/448 : ℝ)/8) ≤ (498467754369930419/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-11/448 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0625_exp_lower : (459088952307780253/500000000000000000 : ℝ) ≤ Real.exp ((-682912890081/1000000000000 : ℝ)/8) ∧ Real.exp ((-682912890081/1000000000000 : ℝ)/8) ≤ (918177904615560507/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-682912890081/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0625_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2020573679891/1000000000000 : ℝ) ≤ 4*Real.exp (87/512 : ℝ)*Real.exp (-mu (radius 7 (11/64 : ℝ))) ∧ (2019/1000 : ℝ) < (2020573679891/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (11/64 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0625_exp_radius
  have hrNumeric : (487872707721/500000000000 : ℝ) ≤ Real.exp (-11/448 : ℝ) ∧ Real.exp (-11/448 : ℝ) ≤ (975745415443/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (487872707721/500000000000 : ℝ) ≤ (radius 7 (11/64 : ℝ)) ∧ (radius 7 (11/64 : ℝ)) ≤ (975745415443/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (11/64 : ℝ)) (487872707721/500000000000 : ℝ) (975745415443/1000000000000 : ℝ) (218908392351/1000000000000 : ℝ) (218908392357/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (11/64 : ℝ)) (487872707721/500000000000 : ℝ) (975745415443/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (11/64 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (487872707721/500000000000 : ℝ) (975745415443/1000000000000 : ℝ) (987872707721/1000000000000 : ℝ) (493936353861/500000000000 : ℝ) (987798266571/1000000000000 : ℝ) (987798266573/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (11/64 : ℝ)) 1 (987872707721/1000000000000 : ℝ) (493936353861/500000000000 : ℝ) (987798266571/1000000000000 : ℝ) (987798266573/1000000000000 : ℝ) (493917743573/500000000000 : ℝ) (246958871787/250000000000 : ℝ) (246958871611/250000000000 : ℝ) (987835486447/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (11/64 : ℝ)) 2 (493917743573/500000000000 : ℝ) (246958871787/250000000000 : ℝ) (246958871611/250000000000 : ℝ) (987835486447/1000000000000 : ℝ) (197567097359/200000000000 : ℝ) (493917743399/500000000000 : ℝ) (493917743397/500000000000 : ℝ) (493917743399/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (11/64 : ℝ)) 3 (197567097359/200000000000 : ℝ) (493917743399/500000000000 : ℝ) (493917743397/500000000000 : ℝ) (493917743399/500000000000 : ℝ) (493917743397/500000000000 : ℝ) (493917743399/500000000000 : ℝ) (493917743397/500000000000 : ℝ) (493917743399/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (11/64 : ℝ)) 4 (493917743397/500000000000 : ℝ) (493917743399/500000000000 : ℝ) (493917743397/500000000000 : ℝ) (493917743399/500000000000 : ℝ) (493917743397/500000000000 : ℝ) (493917743399/500000000000 : ℝ) (493917743397/500000000000 : ℝ) (493917743399/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (11/64 : ℝ)) 5 (493917743397/500000000000 : ℝ) (493917743399/500000000000 : ℝ) (493917743397/500000000000 : ℝ) (493917743399/500000000000 : ℝ) (493917743397/500000000000 : ℝ) (493917743399/500000000000 : ℝ) (493917743397/500000000000 : ℝ) (493917743399/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (11/64 : ℝ)) 6 (493917743397/500000000000 : ℝ) (493917743399/500000000000 : ℝ) (493917743397/500000000000 : ℝ) (493917743399/500000000000 : ℝ) (493917743397/500000000000 : ℝ) (493917743399/500000000000 : ℝ) (493917743397/500000000000 : ℝ) (493917743399/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (11/64 : ℝ)) 7 (493917743397/500000000000 : ℝ) (493917743399/500000000000 : ℝ) (493917743397/500000000000 : ℝ) (493917743399/500000000000 : ℝ) (493917743397/500000000000 : ℝ) (493917743399/500000000000 : ℝ) (493917743397/500000000000 : ℝ) (493917743399/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (11/64 : ℝ))) (218908392351/1000000000000 : ℝ) (218908392357/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (11/64 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (218908392351/1000000000000 : ℝ) (218908392357/1000000000000 : ℝ) (24378167847/40000000000 : ℝ) (609454196179/1000000000000 : ℝ) (467876471251/1000000000000 : ℝ) (467876471259/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (11/64 : ℝ))) 1 (24378167847/40000000000 : ℝ) (609454196179/1000000000000 : ℝ) (467876471251/1000000000000 : ℝ) (467876471259/1000000000000 : ℝ) (538665333713/1000000000000 : ℝ) (538665333719/1000000000000 : ℝ) (266996853303/500000000000 : ℝ) (533993706613/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (11/64 : ℝ))) 2 (538665333713/1000000000000 : ℝ) (538665333719/1000000000000 : ℝ) (266996853303/500000000000 : ℝ) (533993706613/1000000000000 : ℝ) (536329520159/1000000000000 : ℝ) (268164760083/500000000000 : ℝ) (268162216843/500000000000 : ℝ) (268162216847/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (11/64 : ℝ))) 3 (536329520159/1000000000000 : ℝ) (268164760083/500000000000 : ℝ) (268162216843/500000000000 : ℝ) (268162216847/500000000000 : ℝ) (268163488461/500000000000 : ℝ) (53632697693/100000000000 : ℝ) (134081744229/250000000000 : ℝ) (134081744231/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (11/64 : ℝ))) 4 (268163488461/500000000000 : ℝ) (53632697693/100000000000 : ℝ) (134081744229/250000000000 : ℝ) (134081744231/250000000000 : ℝ) (536326976919/1000000000000 : ℝ) (536326976927/1000000000000 : ℝ) (268163488459/500000000000 : ℝ) (536326976927/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (11/64 : ℝ))) 5 (536326976919/1000000000000 : ℝ) (536326976927/1000000000000 : ℝ) (268163488459/500000000000 : ℝ) (536326976927/1000000000000 : ℝ) (268163488459/500000000000 : ℝ) (536326976927/1000000000000 : ℝ) (268163488459/500000000000 : ℝ) (536326976927/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (11/64 : ℝ))) 6 (268163488459/500000000000 : ℝ) (536326976927/1000000000000 : ℝ) (268163488459/500000000000 : ℝ) (536326976927/1000000000000 : ℝ) (268163488459/500000000000 : ℝ) (536326976927/1000000000000 : ℝ) (268163488459/500000000000 : ℝ) (536326976927/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (11/64 : ℝ))) 7 (268163488459/500000000000 : ℝ) (536326976927/1000000000000 : ℝ) (268163488459/500000000000 : ℝ) (536326976927/1000000000000 : ℝ) (268163488459/500000000000 : ℝ) (536326976927/1000000000000 : ℝ) (268163488459/500000000000 : ℝ) (536326976927/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (11/64 : ℝ)) hmem 8 (493917743397/500000000000 : ℝ) (493917743399/500000000000 : ℝ) (493917743397/500000000000 : ℝ) (493917743399/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (11/64 : ℝ))) hcmem 8 (268163488459/500000000000 : ℝ) (536326976927/1000000000000 : ℝ) (268163488459/500000000000 : ℝ) (536326976927/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (11/64 : ℝ)) (493917743397/500000000000 : ℝ) (493917743399/500000000000 : ℝ) (268163488459/500000000000 : ℝ) (536326976927/1000000000000 : ℝ) (426417382531/500000000000 : ℝ) (852834765081/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0625_exp_lower
  have heNumeric : (2020573679891/1000000000000 : ℝ)/4 ≤ Real.exp (-682912890081/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2020573679891/1000000000000 : ℝ)/4 ≤ Real.exp ((87/512 : ℝ)-(852834765081/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (87/512 : ℝ) (11/64 : ℝ) (852834765081/1000000000000 : ℝ) (2020573679891/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0626; no trusted numerical premise.
theorem cover7_leaf0626_exp_radius : (199380147799006163/200000000000000000 : ℝ) ≤ Real.exp ((-89/3584 : ℝ)/8) ∧ Real.exp ((-89/3584 : ℝ)/8) ≤ (31153148093594713/31250000000000000 : ℝ) := by
  have h := exp_small_bounds ((-89/3584 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0626_exp_lower : (229552639418494383/250000000000000000 : ℝ) ≤ Real.exp ((-21332137251/31250000000 : ℝ)/8) ∧ Real.exp ((-21332137251/31250000000 : ℝ)/8) ≤ (918210557673977533/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21332137251/31250000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0626_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (101057430547/50000000000 : ℝ) ≤ 4*Real.exp (11/64 : ℝ)*Real.exp (-mu (radius 7 (89/512 : ℝ))) ∧ (2019/1000 : ℝ) < (101057430547/50000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (89/512 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0626_exp_radius
  have hrNumeric : (39018928121/40000000000 : ℝ) ≤ Real.exp (-89/3584 : ℝ) ∧ Real.exp (-89/3584 : ℝ) ≤ (487736601513/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (39018928121/40000000000 : ℝ) ≤ (radius 7 (89/512 : ℝ)) ∧ (radius 7 (89/512 : ℝ)) ≤ (487736601513/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (89/512 : ℝ)) (39018928121/40000000000 : ℝ) (487736601513/500000000000 : ℝ) (110059109321/500000000000 : ℝ) (220118218647/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (89/512 : ℝ)) (39018928121/40000000000 : ℝ) (487736601513/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (89/512 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (39018928121/40000000000 : ℝ) (487736601513/500000000000 : ℝ) (123467075189/125000000000 : ℝ) (987736601513/1000000000000 : ℝ) (493830234753/500000000000 : ℝ) (987660469507/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (89/512 : ℝ)) 1 (123467075189/125000000000 : ℝ) (987736601513/1000000000000 : ℝ) (493830234753/500000000000 : ℝ) (987660469507/1000000000000 : ℝ) (987698535509/1000000000000 : ℝ) (98769853551/100000000000 : ℝ) (39507941391/40000000000 : ℝ) (987698534777/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (89/512 : ℝ)) 2 (987698535509/1000000000000 : ℝ) (98769853551/100000000000 : ℝ) (39507941391/40000000000 : ℝ) (987698534777/1000000000000 : ℝ) (493849267571/500000000000 : ℝ) (123462316893/125000000000 : ℝ) (987698535141/1000000000000 : ℝ) (123462316893/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (89/512 : ℝ)) 3 (493849267571/500000000000 : ℝ) (123462316893/125000000000 : ℝ) (987698535141/1000000000000 : ℝ) (123462316893/125000000000 : ℝ) (987698535141/1000000000000 : ℝ) (123462316893/125000000000 : ℝ) (987698535141/1000000000000 : ℝ) (123462316893/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (89/512 : ℝ)) 4 (987698535141/1000000000000 : ℝ) (123462316893/125000000000 : ℝ) (987698535141/1000000000000 : ℝ) (123462316893/125000000000 : ℝ) (987698535141/1000000000000 : ℝ) (123462316893/125000000000 : ℝ) (987698535141/1000000000000 : ℝ) (123462316893/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (89/512 : ℝ)) 5 (987698535141/1000000000000 : ℝ) (123462316893/125000000000 : ℝ) (987698535141/1000000000000 : ℝ) (123462316893/125000000000 : ℝ) (987698535141/1000000000000 : ℝ) (123462316893/125000000000 : ℝ) (987698535141/1000000000000 : ℝ) (123462316893/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (89/512 : ℝ)) 6 (987698535141/1000000000000 : ℝ) (123462316893/125000000000 : ℝ) (987698535141/1000000000000 : ℝ) (123462316893/125000000000 : ℝ) (987698535141/1000000000000 : ℝ) (123462316893/125000000000 : ℝ) (987698535141/1000000000000 : ℝ) (123462316893/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (89/512 : ℝ)) 7 (987698535141/1000000000000 : ℝ) (123462316893/125000000000 : ℝ) (987698535141/1000000000000 : ℝ) (123462316893/125000000000 : ℝ) (987698535141/1000000000000 : ℝ) (123462316893/125000000000 : ℝ) (987698535141/1000000000000 : ℝ) (123462316893/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (89/512 : ℝ))) (110059109321/500000000000 : ℝ) (220118218647/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (89/512 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (110059109321/500000000000 : ℝ) (220118218647/1000000000000 : ℝ) (610059109321/1000000000000 : ℝ) (152514777331/250000000000 : ℝ) (469167580553/1000000000000 : ℝ) (469167580559/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (89/512 : ℝ))) 1 (610059109321/1000000000000 : ℝ) (152514777331/250000000000 : ℝ) (469167580553/1000000000000 : ℝ) (469167580559/1000000000000 : ℝ) (539613344937/1000000000000 : ℝ) (269806672471/500000000000 : ℝ) (267497643127/500000000000 : ℝ) (26749764313/50000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (89/512 : ℝ))) 2 (539613344937/1000000000000 : ℝ) (269806672471/500000000000 : ℝ) (267497643127/500000000000 : ℝ) (26749764313/50000000000 : ℝ) (107460863119/200000000000 : ℝ) (537304315601/1000000000000 : ℝ) (537299354123/1000000000000 : ℝ) (537299354129/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (89/512 : ℝ))) 3 (107460863119/200000000000 : ℝ) (537304315601/1000000000000 : ℝ) (537299354123/1000000000000 : ℝ) (537299354129/1000000000000 : ℝ) (537301834859/1000000000000 : ℝ) (107460366973/200000000000 : ℝ) (537301834853/1000000000000 : ℝ) (26865091743/50000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (89/512 : ℝ))) 4 (537301834859/1000000000000 : ℝ) (107460366973/200000000000 : ℝ) (537301834853/1000000000000 : ℝ) (26865091743/50000000000 : ℝ) (67162729357/125000000000 : ℝ) (537301834863/1000000000000 : ℝ) (107460366971/200000000000 : ℝ) (537301834863/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (89/512 : ℝ))) 5 (67162729357/125000000000 : ℝ) (537301834863/1000000000000 : ℝ) (107460366971/200000000000 : ℝ) (537301834863/1000000000000 : ℝ) (107460366971/200000000000 : ℝ) (537301834863/1000000000000 : ℝ) (107460366971/200000000000 : ℝ) (537301834863/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (89/512 : ℝ))) 6 (107460366971/200000000000 : ℝ) (537301834863/1000000000000 : ℝ) (107460366971/200000000000 : ℝ) (537301834863/1000000000000 : ℝ) (107460366971/200000000000 : ℝ) (537301834863/1000000000000 : ℝ) (107460366971/200000000000 : ℝ) (537301834863/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (89/512 : ℝ))) 7 (107460366971/200000000000 : ℝ) (537301834863/1000000000000 : ℝ) (107460366971/200000000000 : ℝ) (537301834863/1000000000000 : ℝ) (107460366971/200000000000 : ℝ) (537301834863/1000000000000 : ℝ) (107460366971/200000000000 : ℝ) (537301834863/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (89/512 : ℝ)) hmem 8 (987698535141/1000000000000 : ℝ) (123462316893/125000000000 : ℝ) (987698535141/1000000000000 : ℝ) (123462316893/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (89/512 : ℝ))) hcmem 8 (107460366971/200000000000 : ℝ) (537301834863/1000000000000 : ℝ) (107460366971/200000000000 : ℝ) (537301834863/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (89/512 : ℝ)) (987698535141/1000000000000 : ℝ) (123462316893/125000000000 : ℝ) (107460366971/200000000000 : ℝ) (537301834863/1000000000000 : ℝ) (53406462001/62500000000 : ℝ) (26703231001/31250000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0626_exp_lower
  have heNumeric : (101057430547/50000000000 : ℝ)/4 ≤ Real.exp (-21332137251/31250000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (101057430547/50000000000 : ℝ)/4 ≤ Real.exp ((11/64 : ℝ)-(26703231001/31250000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (11/64 : ℝ) (89/512 : ℝ) (26703231001/31250000000 : ℝ) (101057430547/50000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0627; no trusted numerical premise.
theorem cover7_leaf0627_exp_radius : (249216492615713027/250000000000000000 : ℝ) ≤ Real.exp ((-45/1792 : ℝ)/8) ∧ Real.exp ((-45/1792 : ℝ)/8) ≤ (996865970462852109/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-45/1792 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0627_exp_lower : (1147805767026931/1250000000000000 : ℝ) ≤ Real.exp ((-341165840867/500000000000 : ℝ)/8) ∧ Real.exp ((-341165840867/500000000000 : ℝ)/8) ≤ (918244613621544801/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-341165840867/500000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0627_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2021748395523/1000000000000 : ℝ) ≤ 4*Real.exp (89/512 : ℝ)*Real.exp (-mu (radius 7 (45/256 : ℝ))) ∧ (2019/1000 : ℝ) < (2021748395523/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (45/256 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0627_exp_radius
  have hrNumeric : (975201066549/1000000000000 : ℝ) ≤ Real.exp (-45/1792 : ℝ) ∧ Real.exp (-45/1792 : ℝ) ≤ (19504021331/20000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (975201066549/1000000000000 : ℝ) ≤ (radius 7 (45/256 : ℝ)) ∧ (radius 7 (45/256 : ℝ)) ≤ (19504021331/20000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (45/256 : ℝ)) (975201066549/1000000000000 : ℝ) (19504021331/20000000000 : ℝ) (110660381121/500000000000 : ℝ) (27665095281/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (45/256 : ℝ)) (975201066549/1000000000000 : ℝ) (19504021331/20000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (45/256 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (975201066549/1000000000000 : ℝ) (19504021331/20000000000 : ℝ) (493800266637/500000000000 : ℝ) (39504021331/40000000000 : ℝ) (493761345831/500000000000 : ℝ) (61720168229/62500000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (45/256 : ℝ)) 1 (493800266637/500000000000 : ℝ) (39504021331/40000000000 : ℝ) (493761345831/500000000000 : ℝ) (61720168229/62500000000 : ℝ) (246890403117/250000000000 : ℝ) (98756161247/100000000000 : ℝ) (987561611701/1000000000000 : ℝ) (987561611703/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (45/256 : ℝ)) 2 (246890403117/250000000000 : ℝ) (98756161247/100000000000 : ℝ) (987561611701/1000000000000 : ℝ) (987561611703/1000000000000 : ℝ) (246890403021/250000000000 : ℝ) (987561612087/1000000000000 : ℝ) (246890403021/250000000000 : ℝ) (987561612087/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (45/256 : ℝ)) 3 (246890403021/250000000000 : ℝ) (987561612087/1000000000000 : ℝ) (246890403021/250000000000 : ℝ) (987561612087/1000000000000 : ℝ) (246890403021/250000000000 : ℝ) (987561612087/1000000000000 : ℝ) (246890403021/250000000000 : ℝ) (987561612087/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (45/256 : ℝ)) 4 (246890403021/250000000000 : ℝ) (987561612087/1000000000000 : ℝ) (246890403021/250000000000 : ℝ) (987561612087/1000000000000 : ℝ) (246890403021/250000000000 : ℝ) (987561612087/1000000000000 : ℝ) (246890403021/250000000000 : ℝ) (987561612087/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (45/256 : ℝ)) 5 (246890403021/250000000000 : ℝ) (987561612087/1000000000000 : ℝ) (246890403021/250000000000 : ℝ) (987561612087/1000000000000 : ℝ) (246890403021/250000000000 : ℝ) (987561612087/1000000000000 : ℝ) (246890403021/250000000000 : ℝ) (987561612087/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (45/256 : ℝ)) 6 (246890403021/250000000000 : ℝ) (987561612087/1000000000000 : ℝ) (246890403021/250000000000 : ℝ) (987561612087/1000000000000 : ℝ) (246890403021/250000000000 : ℝ) (987561612087/1000000000000 : ℝ) (246890403021/250000000000 : ℝ) (987561612087/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (45/256 : ℝ)) 7 (246890403021/250000000000 : ℝ) (987561612087/1000000000000 : ℝ) (246890403021/250000000000 : ℝ) (987561612087/1000000000000 : ℝ) (246890403021/250000000000 : ℝ) (987561612087/1000000000000 : ℝ) (246890403021/250000000000 : ℝ) (987561612087/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (45/256 : ℝ))) (110660381121/500000000000 : ℝ) (27665095281/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (45/256 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (110660381121/500000000000 : ℝ) (27665095281/125000000000 : ℝ) (610660381121/1000000000000 : ℝ) (152665095281/250000000000 : ℝ) (58805925807/125000000000 : ℝ) (3675370363/7812500000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (45/256 : ℝ))) 1 (610660381121/1000000000000 : ℝ) (152665095281/250000000000 : ℝ) (58805925807/125000000000 : ℝ) (3675370363/7812500000 : ℝ) (135138473447/250000000000 : ℝ) (270276946897/500000000000 : ℝ) (66998553217/125000000000 : ℝ) (535988425743/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (45/256 : ℝ))) 2 (135138473447/250000000000 : ℝ) (270276946897/500000000000 : ℝ) (66998553217/125000000000 : ℝ) (535988425743/1000000000000 : ℝ) (269135579881/500000000000 : ℝ) (538271159769/1000000000000 : ℝ) (538266319359/1000000000000 : ℝ) (538266319367/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (45/256 : ℝ))) 3 (269135579881/500000000000 : ℝ) (538271159769/1000000000000 : ℝ) (538266319359/1000000000000 : ℝ) (538266319367/1000000000000 : ℝ) (13456718489/25000000000 : ℝ) (33641796223/62500000000 : ℝ) (107653747911/200000000000 : ℝ) (538268739563/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (45/256 : ℝ))) 4 (13456718489/25000000000 : ℝ) (33641796223/62500000000 : ℝ) (107653747911/200000000000 : ℝ) (538268739563/1000000000000 : ℝ) (538268739557/1000000000000 : ℝ) (269134369783/500000000000 : ℝ) (538268739557/1000000000000 : ℝ) (269134369783/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (45/256 : ℝ))) 5 (538268739557/1000000000000 : ℝ) (269134369783/500000000000 : ℝ) (538268739557/1000000000000 : ℝ) (269134369783/500000000000 : ℝ) (538268739557/1000000000000 : ℝ) (269134369783/500000000000 : ℝ) (538268739557/1000000000000 : ℝ) (269134369783/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (45/256 : ℝ))) 6 (538268739557/1000000000000 : ℝ) (269134369783/500000000000 : ℝ) (538268739557/1000000000000 : ℝ) (269134369783/500000000000 : ℝ) (538268739557/1000000000000 : ℝ) (269134369783/500000000000 : ℝ) (538268739557/1000000000000 : ℝ) (269134369783/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (45/256 : ℝ))) 7 (538268739557/1000000000000 : ℝ) (269134369783/500000000000 : ℝ) (538268739557/1000000000000 : ℝ) (269134369783/500000000000 : ℝ) (538268739557/1000000000000 : ℝ) (269134369783/500000000000 : ℝ) (538268739557/1000000000000 : ℝ) (269134369783/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (45/256 : ℝ)) hmem 8 (246890403021/250000000000 : ℝ) (987561612087/1000000000000 : ℝ) (246890403021/250000000000 : ℝ) (987561612087/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (45/256 : ℝ))) hcmem 8 (538268739557/1000000000000 : ℝ) (269134369783/500000000000 : ℝ) (538268739557/1000000000000 : ℝ) (269134369783/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (45/256 : ℝ)) (246890403021/250000000000 : ℝ) (987561612087/1000000000000 : ℝ) (538268739557/1000000000000 : ℝ) (269134369783/500000000000 : ℝ) (214039951679/250000000000 : ℝ) (428079903367/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0627_exp_lower
  have heNumeric : (2021748395523/1000000000000 : ℝ)/4 ≤ Real.exp (-341165840867/500000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2021748395523/1000000000000 : ℝ)/4 ≤ Real.exp ((89/512 : ℝ)-(428079903367/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (89/512 : ℝ) (45/256 : ℝ) (428079903367/500000000000 : ℝ) (2021748395523/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0628; no trusted numerical premise.
theorem cover7_leaf0628_exp_radius : (996796437036279467/1000000000000000000 : ℝ) ≤ Real.exp ((-23/896 : ℝ)/8) ∧ Real.exp ((-23/896 : ℝ)/8) ≤ (249199109259069867/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-23/896 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0628_exp_lower : (918092656268185111/1000000000000000000 : ℝ) ≤ Real.exp ((-85456960701/125000000000 : ℝ)/8) ∧ Real.exp ((-85456960701/125000000000 : ℝ)/8) ≤ (114761582033523139/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85456960701/125000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0628_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009536682041/500000000000 : ℝ) ≤ 4*Real.exp (45/256 : ℝ)*Real.exp (-mu (radius 7 (23/128 : ℝ))) ∧ (2019/1000 : ℝ) < (1009536682041/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (23/128 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0628_exp_radius
  have hrNumeric : (487328510669/500000000000 : ℝ) ≤ Real.exp (-23/896 : ℝ) ∧ Real.exp (-23/896 : ℝ) ≤ (974657021339/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (487328510669/500000000000 : ℝ) ≤ (radius 7 (23/128 : ℝ)) ∧ (radius 7 (23/128 : ℝ)) ≤ (974657021339/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (23/128 : ℝ)) (487328510669/500000000000 : ℝ) (974657021339/1000000000000 : ℝ) (111852235957/500000000000 : ℝ) (223704471919/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (23/128 : ℝ)) (487328510669/500000000000 : ℝ) (974657021339/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (23/128 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (487328510669/500000000000 : ℝ) (974657021339/1000000000000 : ℝ) (987328510669/1000000000000 : ℝ) (98732851067/100000000000 : ℝ) (987247193633/1000000000000 : ℝ) (197449438727/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (23/128 : ℝ)) 1 (987328510669/1000000000000 : ℝ) (98732851067/100000000000 : ℝ) (987247193633/1000000000000 : ℝ) (197449438727/200000000000 : ℝ) (987287852151/1000000000000 : ℝ) (987287852153/1000000000000 : ℝ) (987287851313/1000000000000 : ℝ) (246821962829/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (23/128 : ℝ)) 2 (987287852151/1000000000000 : ℝ) (987287852153/1000000000000 : ℝ) (987287851313/1000000000000 : ℝ) (246821962829/250000000000 : ℝ) (246821962933/250000000000 : ℝ) (197457570347/200000000000 : ℝ) (987287851731/1000000000000 : ℝ) (197457570347/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (23/128 : ℝ)) 3 (246821962933/250000000000 : ℝ) (197457570347/200000000000 : ℝ) (987287851731/1000000000000 : ℝ) (197457570347/200000000000 : ℝ) (987287851731/1000000000000 : ℝ) (197457570347/200000000000 : ℝ) (987287851731/1000000000000 : ℝ) (197457570347/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (23/128 : ℝ)) 4 (987287851731/1000000000000 : ℝ) (197457570347/200000000000 : ℝ) (987287851731/1000000000000 : ℝ) (197457570347/200000000000 : ℝ) (987287851731/1000000000000 : ℝ) (197457570347/200000000000 : ℝ) (987287851731/1000000000000 : ℝ) (197457570347/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (23/128 : ℝ)) 5 (987287851731/1000000000000 : ℝ) (197457570347/200000000000 : ℝ) (987287851731/1000000000000 : ℝ) (197457570347/200000000000 : ℝ) (987287851731/1000000000000 : ℝ) (197457570347/200000000000 : ℝ) (987287851731/1000000000000 : ℝ) (197457570347/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (23/128 : ℝ)) 6 (987287851731/1000000000000 : ℝ) (197457570347/200000000000 : ℝ) (987287851731/1000000000000 : ℝ) (197457570347/200000000000 : ℝ) (987287851731/1000000000000 : ℝ) (197457570347/200000000000 : ℝ) (987287851731/1000000000000 : ℝ) (197457570347/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (23/128 : ℝ)) 7 (987287851731/1000000000000 : ℝ) (197457570347/200000000000 : ℝ) (987287851731/1000000000000 : ℝ) (197457570347/200000000000 : ℝ) (987287851731/1000000000000 : ℝ) (197457570347/200000000000 : ℝ) (987287851731/1000000000000 : ℝ) (197457570347/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (23/128 : ℝ))) (111852235957/500000000000 : ℝ) (223704471919/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (23/128 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (111852235957/500000000000 : ℝ) (223704471919/1000000000000 : ℝ) (611852235957/1000000000000 : ℝ) (15296305899/25000000000 : ℝ) (11824351777/25000000000 : ℝ) (236487035543/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (23/128 : ℝ))) 1 (611852235957/1000000000000 : ℝ) (15296305899/25000000000 : ℝ) (11824351777/25000000000 : ℝ) (236487035543/500000000000 : ℝ) (271206576759/500000000000 : ℝ) (542413153523/1000000000000 : ℝ) (537950037587/1000000000000 : ℝ) (67243754699/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (23/128 : ℝ))) 2 (271206576759/500000000000 : ℝ) (542413153523/1000000000000 : ℝ) (537950037587/1000000000000 : ℝ) (67243754699/125000000000 : ℝ) (16880674861/31250000000 : ℝ) (270090797779/500000000000 : ℝ) (540176986109/1000000000000 : ℝ) (108035397223/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (23/128 : ℝ))) 3 (16880674861/31250000000 : ℝ) (270090797779/500000000000 : ℝ) (540176986109/1000000000000 : ℝ) (108035397223/200000000000 : ℝ) (54017929083/100000000000 : ℝ) (540179290837/1000000000000 : ℝ) (21607171633/40000000000 : ℝ) (33761205677/62500000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (23/128 : ℝ))) 4 (54017929083/100000000000 : ℝ) (540179290837/1000000000000 : ℝ) (21607171633/40000000000 : ℝ) (33761205677/62500000000 : ℝ) (540179290827/1000000000000 : ℝ) (108035858167/200000000000 : ℝ) (540179290827/1000000000000 : ℝ) (108035858167/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (23/128 : ℝ))) 5 (540179290827/1000000000000 : ℝ) (108035858167/200000000000 : ℝ) (540179290827/1000000000000 : ℝ) (108035858167/200000000000 : ℝ) (540179290827/1000000000000 : ℝ) (108035858167/200000000000 : ℝ) (540179290827/1000000000000 : ℝ) (108035858167/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (23/128 : ℝ))) 6 (540179290827/1000000000000 : ℝ) (108035858167/200000000000 : ℝ) (540179290827/1000000000000 : ℝ) (108035858167/200000000000 : ℝ) (540179290827/1000000000000 : ℝ) (108035858167/200000000000 : ℝ) (540179290827/1000000000000 : ℝ) (108035858167/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (23/128 : ℝ))) 7 (540179290827/1000000000000 : ℝ) (108035858167/200000000000 : ℝ) (540179290827/1000000000000 : ℝ) (108035858167/200000000000 : ℝ) (540179290827/1000000000000 : ℝ) (108035858167/200000000000 : ℝ) (540179290827/1000000000000 : ℝ) (108035858167/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (23/128 : ℝ)) hmem 8 (987287851731/1000000000000 : ℝ) (197457570347/200000000000 : ℝ) (987287851731/1000000000000 : ℝ) (197457570347/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (23/128 : ℝ))) hcmem 8 (540179290827/1000000000000 : ℝ) (108035858167/200000000000 : ℝ) (540179290827/1000000000000 : ℝ) (108035858167/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (23/128 : ℝ)) (987287851731/1000000000000 : ℝ) (197457570347/200000000000 : ℝ) (540179290827/1000000000000 : ℝ) (108035858167/200000000000 : ℝ) (859436935591/1000000000000 : ℝ) (107429616951/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0628_exp_lower
  have heNumeric : (1009536682041/500000000000 : ℝ)/4 ≤ Real.exp (-85456960701/125000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009536682041/500000000000 : ℝ)/4 ≤ Real.exp ((45/256 : ℝ)-(107429616951/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (45/256 : ℝ) (23/128 : ℝ) (107429616951/125000000000 : ℝ) (1009536682041/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0629; no trusted numerical premise.
theorem cover7_leaf0629_exp_radius : (996726908459804587/1000000000000000000 : ℝ) ≤ Real.exp ((-47/1792 : ℝ)/8) ∧ Real.exp ((-47/1792 : ℝ)/8) ≤ (249181727114951147/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-47/1792 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0629_exp_lower : (918170150098997257/1000000000000000000 : ℝ) ≤ Real.exp ((-682980454759/1000000000000 : ℝ)/8) ∧ Real.exp ((-682980454759/1000000000000 : ℝ)/8) ≤ (459085075049498629/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-682980454759/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0629_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (505109291273/250000000000 : ℝ) ≤ 4*Real.exp (23/128 : ℝ)*Real.exp (-mu (radius 7 (47/256 : ℝ))) ∧ (2019/1000 : ℝ) < (505109291273/250000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (47/256 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0629_exp_radius
  have hrNumeric : (974113279639/1000000000000 : ℝ) ≤ Real.exp (-47/1792 : ℝ) ∧ Real.exp (-47/1792 : ℝ) ≤ (24352831991/25000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (974113279639/1000000000000 : ℝ) ≤ (radius 7 (47/256 : ℝ)) ∧ (radius 7 (47/256 : ℝ)) ≤ (24352831991/25000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (47/256 : ℝ)) (974113279639/1000000000000 : ℝ) (24352831991/25000000000 : ℝ) (113030215461/500000000000 : ℝ) (14128776933/62500000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (47/256 : ℝ)) (974113279639/1000000000000 : ℝ) (24352831991/25000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (47/256 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (974113279639/1000000000000 : ℝ) (24352831991/25000000000 : ℝ) (987056639819/1000000000000 : ℝ) (49352831991/50000000000 : ℝ) (986971772463/1000000000000 : ℝ) (61685735779/62500000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (47/256 : ℝ)) 1 (987056639819/1000000000000 : ℝ) (49352831991/50000000000 : ℝ) (986971772463/1000000000000 : ℝ) (61685735779/62500000000 : ℝ) (987014206141/1000000000000 : ℝ) (493507103071/500000000000 : ℝ) (246753551307/250000000000 : ℝ) (98701420523/100000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (47/256 : ℝ)) 2 (987014206141/1000000000000 : ℝ) (493507103071/500000000000 : ℝ) (246753551307/250000000000 : ℝ) (98701420523/100000000000 : ℝ) (246753551421/250000000000 : ℝ) (493507102843/500000000000 : ℝ) (246753551421/250000000000 : ℝ) (493507102843/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (47/256 : ℝ)) 3 (246753551421/250000000000 : ℝ) (493507102843/500000000000 : ℝ) (246753551421/250000000000 : ℝ) (493507102843/500000000000 : ℝ) (246753551421/250000000000 : ℝ) (493507102843/500000000000 : ℝ) (246753551421/250000000000 : ℝ) (493507102843/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (47/256 : ℝ)) 4 (246753551421/250000000000 : ℝ) (493507102843/500000000000 : ℝ) (246753551421/250000000000 : ℝ) (493507102843/500000000000 : ℝ) (246753551421/250000000000 : ℝ) (493507102843/500000000000 : ℝ) (246753551421/250000000000 : ℝ) (493507102843/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (47/256 : ℝ)) 5 (246753551421/250000000000 : ℝ) (493507102843/500000000000 : ℝ) (246753551421/250000000000 : ℝ) (493507102843/500000000000 : ℝ) (246753551421/250000000000 : ℝ) (493507102843/500000000000 : ℝ) (246753551421/250000000000 : ℝ) (493507102843/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (47/256 : ℝ)) 6 (246753551421/250000000000 : ℝ) (493507102843/500000000000 : ℝ) (246753551421/250000000000 : ℝ) (493507102843/500000000000 : ℝ) (246753551421/250000000000 : ℝ) (493507102843/500000000000 : ℝ) (246753551421/250000000000 : ℝ) (493507102843/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (47/256 : ℝ)) 7 (246753551421/250000000000 : ℝ) (493507102843/500000000000 : ℝ) (246753551421/250000000000 : ℝ) (493507102843/500000000000 : ℝ) (246753551421/250000000000 : ℝ) (493507102843/500000000000 : ℝ) (246753551421/250000000000 : ℝ) (493507102843/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (47/256 : ℝ))) (113030215461/500000000000 : ℝ) (14128776933/62500000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (47/256 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (113030215461/500000000000 : ℝ) (14128776933/62500000000 : ℝ) (613030215461/1000000000000 : ℝ) (76628776933/125000000000 : ℝ) (475458127411/1000000000000 : ℝ) (475458127419/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (47/256 : ℝ))) 1 (613030215461/1000000000000 : ℝ) (76628776933/125000000000 : ℝ) (475458127411/1000000000000 : ℝ) (475458127419/1000000000000 : ℝ) (136061042859/250000000000 : ℝ) (272122085721/500000000000 : ℝ) (539879799853/1000000000000 : ℝ) (539879799859/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (47/256 : ℝ))) 2 (136061042859/250000000000 : ℝ) (272122085721/500000000000 : ℝ) (539879799853/1000000000000 : ℝ) (539879799859/1000000000000 : ℝ) (135515496411/250000000000 : ℝ) (542061985651/1000000000000 : ℝ) (1355143983/2500000000 : ℝ) (542057593207/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (47/256 : ℝ))) 3 (135515496411/250000000000 : ℝ) (542061985651/1000000000000 : ℝ) (1355143983/2500000000 : ℝ) (542057593207/1000000000000 : ℝ) (271029894711/500000000000 : ℝ) (542059789429/1000000000000 : ℝ) (542059789417/1000000000000 : ℝ) (21682391577/40000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (47/256 : ℝ))) 4 (271029894711/500000000000 : ℝ) (542059789429/1000000000000 : ℝ) (542059789417/1000000000000 : ℝ) (21682391577/40000000000 : ℝ) (542059789419/1000000000000 : ℝ) (542059789427/1000000000000 : ℝ) (542059789419/1000000000000 : ℝ) (542059789427/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (47/256 : ℝ))) 5 (542059789419/1000000000000 : ℝ) (542059789427/1000000000000 : ℝ) (542059789419/1000000000000 : ℝ) (542059789427/1000000000000 : ℝ) (542059789419/1000000000000 : ℝ) (542059789427/1000000000000 : ℝ) (542059789419/1000000000000 : ℝ) (542059789427/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (47/256 : ℝ))) 6 (542059789419/1000000000000 : ℝ) (542059789427/1000000000000 : ℝ) (542059789419/1000000000000 : ℝ) (542059789427/1000000000000 : ℝ) (542059789419/1000000000000 : ℝ) (542059789427/1000000000000 : ℝ) (542059789419/1000000000000 : ℝ) (542059789427/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (47/256 : ℝ))) 7 (542059789419/1000000000000 : ℝ) (542059789427/1000000000000 : ℝ) (542059789419/1000000000000 : ℝ) (542059789427/1000000000000 : ℝ) (542059789419/1000000000000 : ℝ) (542059789427/1000000000000 : ℝ) (542059789419/1000000000000 : ℝ) (542059789427/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (47/256 : ℝ)) hmem 8 (246753551421/250000000000 : ℝ) (493507102843/500000000000 : ℝ) (246753551421/250000000000 : ℝ) (493507102843/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (47/256 : ℝ))) hcmem 8 (542059789419/1000000000000 : ℝ) (542059789427/1000000000000 : ℝ) (542059789419/1000000000000 : ℝ) (542059789427/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (47/256 : ℝ)) (246753551421/250000000000 : ℝ) (493507102843/500000000000 : ℝ) (542059789419/1000000000000 : ℝ) (542059789427/1000000000000 : ℝ) (107833494343/125000000000 : ℝ) (862667954759/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0629_exp_lower
  have heNumeric : (505109291273/250000000000 : ℝ)/4 ≤ Real.exp (-682980454759/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (505109291273/250000000000 : ℝ)/4 ≤ Real.exp ((23/128 : ℝ)-(862667954759/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (23/128 : ℝ) (47/256 : ℝ) (862667954759/1000000000000 : ℝ) (505109291273/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0630; no trusted numerical premise.
theorem cover7_leaf0630_exp_radius : (996657384733089163/1000000000000000000 : ℝ) ≤ Real.exp ((-3/112 : ℝ)/8) ∧ Real.exp ((-3/112 : ℝ)/8) ≤ (249164346183272291/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-3/112 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0630_exp_lower : (183650549617589611/200000000000000000 : ℝ) ≤ Real.exp ((-42641300771/62500000000 : ℝ)/8) ∧ Real.exp ((-42641300771/62500000000 : ℝ)/8) ≤ (114781593510993507/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42641300771/62500000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0630_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (505472920173/250000000000 : ℝ) ≤ 4*Real.exp (47/256 : ℝ)*Real.exp (-mu (radius 7 (3/16 : ℝ))) ∧ (2019/1000 : ℝ) < (505472920173/250000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (3/16 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0630_exp_radius
  have hrNumeric : (486784920641/500000000000 : ℝ) ≤ Real.exp (-3/112 : ℝ) ∧ Real.exp (-3/112 : ℝ) ≤ (973569841283/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (486784920641/500000000000 : ℝ) ≤ (radius 7 (3/16 : ℝ)) ∧ (radius 7 (3/16 : ℝ)) ≤ (973569841283/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (3/16 : ℝ)) (486784920641/500000000000 : ℝ) (973569841283/1000000000000 : ℝ) (4567790019/20000000000 : ℝ) (45677900191/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (3/16 : ℝ)) (486784920641/500000000000 : ℝ) (973569841283/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (3/16 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (486784920641/500000000000 : ℝ) (973569841283/1000000000000 : ℝ) (986784920641/1000000000000 : ℝ) (493392460321/500000000000 : ℝ) (30834263379/31250000000 : ℝ) (98669642813/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (3/16 : ℝ)) 1 (986784920641/1000000000000 : ℝ) (493392460321/500000000000 : ℝ) (30834263379/31250000000 : ℝ) (98669642813/100000000000 : ℝ) (61671292149/62500000000 : ℝ) (493370337193/500000000000 : ℝ) (61671292087/62500000000 : ℝ) (493370336697/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (3/16 : ℝ)) 2 (61671292149/62500000000 : ℝ) (493370337193/500000000000 : ℝ) (61671292087/62500000000 : ℝ) (493370336697/500000000000 : ℝ) (30835646059/31250000000 : ℝ) (98674067389/100000000000 : ℝ) (986740673887/1000000000000 : ℝ) (98674067389/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (3/16 : ℝ)) 3 (30835646059/31250000000 : ℝ) (98674067389/100000000000 : ℝ) (986740673887/1000000000000 : ℝ) (98674067389/100000000000 : ℝ) (986740673887/1000000000000 : ℝ) (98674067389/100000000000 : ℝ) (986740673887/1000000000000 : ℝ) (98674067389/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (3/16 : ℝ)) 4 (986740673887/1000000000000 : ℝ) (98674067389/100000000000 : ℝ) (986740673887/1000000000000 : ℝ) (98674067389/100000000000 : ℝ) (986740673887/1000000000000 : ℝ) (98674067389/100000000000 : ℝ) (986740673887/1000000000000 : ℝ) (98674067389/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (3/16 : ℝ)) 5 (986740673887/1000000000000 : ℝ) (98674067389/100000000000 : ℝ) (986740673887/1000000000000 : ℝ) (98674067389/100000000000 : ℝ) (986740673887/1000000000000 : ℝ) (98674067389/100000000000 : ℝ) (986740673887/1000000000000 : ℝ) (98674067389/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (3/16 : ℝ)) 6 (986740673887/1000000000000 : ℝ) (98674067389/100000000000 : ℝ) (986740673887/1000000000000 : ℝ) (98674067389/100000000000 : ℝ) (986740673887/1000000000000 : ℝ) (98674067389/100000000000 : ℝ) (986740673887/1000000000000 : ℝ) (98674067389/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (3/16 : ℝ)) 7 (986740673887/1000000000000 : ℝ) (98674067389/100000000000 : ℝ) (986740673887/1000000000000 : ℝ) (98674067389/100000000000 : ℝ) (986740673887/1000000000000 : ℝ) (98674067389/100000000000 : ℝ) (986740673887/1000000000000 : ℝ) (98674067389/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (3/16 : ℝ))) (4567790019/20000000000 : ℝ) (45677900191/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (3/16 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (4567790019/20000000000 : ℝ) (45677900191/200000000000 : ℝ) (24567790019/40000000000 : ℝ) (307097375239/500000000000 : ℝ) (238950570699/500000000000 : ℝ) (119475285351/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (3/16 : ℝ))) 1 (24567790019/40000000000 : ℝ) (307097375239/500000000000 : ℝ) (238950570699/500000000000 : ℝ) (119475285351/250000000000 : ℝ) (34127996621/62500000000 : ℝ) (546047945941/1000000000000 : ℝ) (54177889613/100000000000 : ℝ) (67722362017/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (3/16 : ℝ))) 2 (34127996621/62500000000 : ℝ) (546047945941/1000000000000 : ℝ) (54177889613/100000000000 : ℝ) (67722362017/125000000000 : ℝ) (543913421033/1000000000000 : ℝ) (543913421039/1000000000000 : ℝ) (543909232669/1000000000000 : ℝ) (135977308169/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (3/16 : ℝ))) 3 (543913421033/1000000000000 : ℝ) (543913421039/1000000000000 : ℝ) (543909232669/1000000000000 : ℝ) (135977308169/250000000000 : ℝ) (543911326851/1000000000000 : ℝ) (271955663429/500000000000 : ℝ) (271955663423/500000000000 : ℝ) (271955663427/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (3/16 : ℝ))) 4 (543911326851/1000000000000 : ℝ) (271955663429/500000000000 : ℝ) (271955663423/500000000000 : ℝ) (271955663427/500000000000 : ℝ) (4249307241/7812500000 : ℝ) (67988915857/125000000000 : ℝ) (4249307241/7812500000 : ℝ) (67988915857/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (3/16 : ℝ))) 5 (4249307241/7812500000 : ℝ) (67988915857/125000000000 : ℝ) (4249307241/7812500000 : ℝ) (67988915857/125000000000 : ℝ) (4249307241/7812500000 : ℝ) (67988915857/125000000000 : ℝ) (4249307241/7812500000 : ℝ) (67988915857/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (3/16 : ℝ))) 6 (4249307241/7812500000 : ℝ) (67988915857/125000000000 : ℝ) (4249307241/7812500000 : ℝ) (67988915857/125000000000 : ℝ) (4249307241/7812500000 : ℝ) (67988915857/125000000000 : ℝ) (4249307241/7812500000 : ℝ) (67988915857/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (3/16 : ℝ))) 7 (4249307241/7812500000 : ℝ) (67988915857/125000000000 : ℝ) (4249307241/7812500000 : ℝ) (67988915857/125000000000 : ℝ) (4249307241/7812500000 : ℝ) (67988915857/125000000000 : ℝ) (4249307241/7812500000 : ℝ) (67988915857/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (3/16 : ℝ)) hmem 8 (986740673887/1000000000000 : ℝ) (98674067389/100000000000 : ℝ) (986740673887/1000000000000 : ℝ) (98674067389/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (3/16 : ℝ))) hcmem 8 (4249307241/7812500000 : ℝ) (67988915857/125000000000 : ℝ) (4249307241/7812500000 : ℝ) (67988915857/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (3/16 : ℝ)) (986740673887/1000000000000 : ℝ) (98674067389/100000000000 : ℝ) (4249307241/7812500000 : ℝ) (67988915857/125000000000 : ℝ) (10823182029/12500000000 : ℝ) (27057955073/31250000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0630_exp_lower
  have heNumeric : (505472920173/250000000000 : ℝ)/4 ≤ Real.exp (-42641300771/62500000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (505472920173/250000000000 : ℝ)/4 ≤ Real.exp ((47/256 : ℝ)-(27057955073/31250000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (47/256 : ℝ) (3/16 : ℝ) (27057955073/31250000000 : ℝ) (505472920173/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0631; no trusted numerical premise.
theorem cover7_leaf0631_exp_radius : (199317573171158983/200000000000000000 : ℝ) ≤ Real.exp ((-7/256 : ℝ)/8) ∧ Real.exp ((-7/256 : ℝ)/8) ≤ (249146966463948729/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-7/256 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0631_exp_lower : (114792533472860949/125000000000000000 : ℝ) ≤ Real.exp ((-85187294967/125000000000 : ℝ)/8) ∧ Real.exp ((-85187294967/125000000000 : ℝ)/8) ≤ (918340267782887593/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85187294967/125000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0631_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (505858466277/250000000000 : ℝ) ≤ 4*Real.exp (3/16 : ℝ)*Real.exp (-mu (radius 7 (49/256 : ℝ))) ∧ (2019/1000 : ℝ) < (505858466277/250000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (49/256 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0631_exp_radius
  have hrNumeric : (973026706099/1000000000000 : ℝ) ≤ Real.exp (-7/256 : ℝ) ∧ Real.exp (-7/256 : ℝ) ≤ (9730267061/10000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (973026706099/1000000000000 : ℝ) ≤ (radius 7 (49/256 : ℝ)) ∧ (radius 7 (49/256 : ℝ)) ≤ (9730267061/10000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (49/256 : ℝ)) (973026706099/1000000000000 : ℝ) (9730267061/10000000000 : ℝ) (115346249631/500000000000 : ℝ) (57673124817/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (49/256 : ℝ)) (973026706099/1000000000000 : ℝ) (9730267061/10000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (49/256 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (973026706099/1000000000000 : ℝ) (9730267061/10000000000 : ℝ) (986513353049/1000000000000 : ℝ) (19730267061/20000000000 : ℝ) (986421160609/1000000000000 : ℝ) (986421160611/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (49/256 : ℝ)) 1 (986513353049/1000000000000 : ℝ) (19730267061/20000000000 : ℝ) (986421160609/1000000000000 : ℝ) (986421160611/1000000000000 : ℝ) (986467256829/1000000000000 : ℝ) (986467256831/1000000000000 : ℝ) (986467255751/1000000000000 : ℝ) (493233627877/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (49/256 : ℝ)) 2 (986467256829/1000000000000 : ℝ) (986467256831/1000000000000 : ℝ) (986467255751/1000000000000 : ℝ) (493233627877/500000000000 : ℝ) (98646725629/100000000000 : ℝ) (986467256293/1000000000000 : ℝ) (986467256289/1000000000000 : ℝ) (986467256293/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (49/256 : ℝ)) 3 (98646725629/100000000000 : ℝ) (986467256293/1000000000000 : ℝ) (986467256289/1000000000000 : ℝ) (986467256293/1000000000000 : ℝ) (986467256289/1000000000000 : ℝ) (986467256293/1000000000000 : ℝ) (986467256289/1000000000000 : ℝ) (986467256293/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (49/256 : ℝ)) 4 (986467256289/1000000000000 : ℝ) (986467256293/1000000000000 : ℝ) (986467256289/1000000000000 : ℝ) (986467256293/1000000000000 : ℝ) (986467256289/1000000000000 : ℝ) (986467256293/1000000000000 : ℝ) (986467256289/1000000000000 : ℝ) (986467256293/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (49/256 : ℝ)) 5 (986467256289/1000000000000 : ℝ) (986467256293/1000000000000 : ℝ) (986467256289/1000000000000 : ℝ) (986467256293/1000000000000 : ℝ) (986467256289/1000000000000 : ℝ) (986467256293/1000000000000 : ℝ) (986467256289/1000000000000 : ℝ) (986467256293/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (49/256 : ℝ)) 6 (986467256289/1000000000000 : ℝ) (986467256293/1000000000000 : ℝ) (986467256289/1000000000000 : ℝ) (986467256293/1000000000000 : ℝ) (986467256289/1000000000000 : ℝ) (986467256293/1000000000000 : ℝ) (986467256289/1000000000000 : ℝ) (986467256293/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (49/256 : ℝ)) 7 (986467256289/1000000000000 : ℝ) (986467256293/1000000000000 : ℝ) (986467256289/1000000000000 : ℝ) (986467256293/1000000000000 : ℝ) (986467256289/1000000000000 : ℝ) (986467256293/1000000000000 : ℝ) (986467256289/1000000000000 : ℝ) (986467256293/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (49/256 : ℝ))) (115346249631/500000000000 : ℝ) (57673124817/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (49/256 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (115346249631/500000000000 : ℝ) (57673124817/250000000000 : ℝ) (615346249631/1000000000000 : ℝ) (307673124817/500000000000 : ℝ) (48030459009/100000000000 : ℝ) (480304590097/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (49/256 : ℝ))) 1 (615346249631/1000000000000 : ℝ) (307673124817/500000000000 : ℝ) (48030459009/100000000000 : ℝ) (480304590097/1000000000000 : ℝ) (27391270993/50000000000 : ℝ) (273912709933/500000000000 : ℝ) (543648441727/1000000000000 : ℝ) (543648441733/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (49/256 : ℝ))) 2 (27391270993/50000000000 : ℝ) (273912709933/500000000000 : ℝ) (543648441727/1000000000000 : ℝ) (543648441733/1000000000000 : ℝ) (545736930793/1000000000000 : ℝ) (1364342327/2500000000 : ℝ) (545732934543/1000000000000 : ℝ) (10914658691/20000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (49/256 : ℝ))) 3 (545736930793/1000000000000 : ℝ) (1364342327/2500000000 : ℝ) (545732934543/1000000000000 : ℝ) (10914658691/20000000000 : ℝ) (136433733167/250000000000 : ℝ) (21829397307/40000000000 : ℝ) (68216866583/125000000000 : ℝ) (8527108323/15625000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (49/256 : ℝ))) 4 (136433733167/250000000000 : ℝ) (21829397307/40000000000 : ℝ) (68216866583/125000000000 : ℝ) (8527108323/15625000000 : ℝ) (272867466333/500000000000 : ℝ) (272867466337/500000000000 : ℝ) (109146986533/200000000000 : ℝ) (272867466337/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (49/256 : ℝ))) 5 (272867466333/500000000000 : ℝ) (272867466337/500000000000 : ℝ) (109146986533/200000000000 : ℝ) (272867466337/500000000000 : ℝ) (109146986533/200000000000 : ℝ) (272867466337/500000000000 : ℝ) (109146986533/200000000000 : ℝ) (272867466337/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (49/256 : ℝ))) 6 (109146986533/200000000000 : ℝ) (272867466337/500000000000 : ℝ) (109146986533/200000000000 : ℝ) (272867466337/500000000000 : ℝ) (109146986533/200000000000 : ℝ) (272867466337/500000000000 : ℝ) (109146986533/200000000000 : ℝ) (272867466337/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (49/256 : ℝ))) 7 (109146986533/200000000000 : ℝ) (272867466337/500000000000 : ℝ) (109146986533/200000000000 : ℝ) (272867466337/500000000000 : ℝ) (109146986533/200000000000 : ℝ) (272867466337/500000000000 : ℝ) (109146986533/200000000000 : ℝ) (272867466337/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (49/256 : ℝ)) hmem 8 (986467256289/1000000000000 : ℝ) (986467256293/1000000000000 : ℝ) (986467256289/1000000000000 : ℝ) (986467256293/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (49/256 : ℝ))) hcmem 8 (109146986533/200000000000 : ℝ) (272867466337/500000000000 : ℝ) (109146986533/200000000000 : ℝ) (272867466337/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (49/256 : ℝ)) (986467256289/1000000000000 : ℝ) (986467256293/1000000000000 : ℝ) (109146986533/200000000000 : ℝ) (272867466337/500000000000 : ℝ) (868998359717/1000000000000 : ℝ) (108624794967/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0631_exp_lower
  have heNumeric : (505858466277/250000000000 : ℝ)/4 ≤ Real.exp (-85187294967/125000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (505858466277/250000000000 : ℝ)/4 ≤ Real.exp ((3/16 : ℝ)-(108624794967/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (3/16 : ℝ) (49/256 : ℝ) (108624794967/125000000000 : ℝ) (505858466277/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0632; no trusted numerical premise.
theorem cover7_leaf0632_exp_radius : (498259175913791793/500000000000000000 : ℝ) ≤ Real.exp ((-25/896 : ℝ)/8) ∧ Real.exp ((-25/896 : ℝ)/8) ≤ (996518351827583587/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-25/896 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0632_exp_lower : (114804067125160207/125000000000000000 : ℝ) ≤ Real.exp ((-680694608999/1000000000000 : ℝ)/8) ∧ Real.exp ((-680694608999/1000000000000 : ℝ)/8) ≤ (918432537001281657/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-680694608999/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0632_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (63283151729/31250000000 : ℝ) ≤ 4*Real.exp (49/256 : ℝ)*Real.exp (-mu (radius 7 (25/128 : ℝ))) ∧ (2019/1000 : ℝ) < (63283151729/31250000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (25/128 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0632_exp_radius
  have hrNumeric : (1519506053/1562500000 : ℝ) ≤ Real.exp (-25/896 : ℝ) ∧ Real.exp (-25/896 : ℝ) ≤ (972483873921/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (1519506053/1562500000 : ℝ) ≤ (radius 7 (25/128 : ℝ)) ∧ (radius 7 (25/128 : ℝ)) ≤ (972483873921/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (25/128 : ℝ)) (1519506053/1562500000 : ℝ) (972483873921/1000000000000 : ℝ) (232970201879/1000000000000 : ℝ) (58242550471/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (25/128 : ℝ)) (1519506053/1562500000 : ℝ) (972483873921/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (25/128 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (1519506053/1562500000 : ℝ) (972483873921/1000000000000 : ℝ) (3082006053/3125000000 : ℝ) (986241936961/1000000000000 : ℝ) (246536492471/250000000000 : ℝ) (493072984943/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (25/128 : ℝ)) 1 (3082006053/3125000000 : ℝ) (986241936961/1000000000000 : ℝ) (246536492471/250000000000 : ℝ) (493072984943/500000000000 : ℝ) (493096976711/500000000000 : ℝ) (61637122089/62500000000 : ℝ) (493096976127/500000000000 : ℝ) (986193952257/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (25/128 : ℝ)) 2 (493096976711/500000000000 : ℝ) (61637122089/62500000000 : ℝ) (493096976127/500000000000 : ℝ) (986193952257/1000000000000 : ℝ) (493096976419/500000000000 : ℝ) (986193952841/1000000000000 : ℝ) (986193952837/1000000000000 : ℝ) (986193952841/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (25/128 : ℝ)) 3 (493096976419/500000000000 : ℝ) (986193952841/1000000000000 : ℝ) (986193952837/1000000000000 : ℝ) (986193952841/1000000000000 : ℝ) (986193952837/1000000000000 : ℝ) (986193952841/1000000000000 : ℝ) (986193952837/1000000000000 : ℝ) (986193952841/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (25/128 : ℝ)) 4 (986193952837/1000000000000 : ℝ) (986193952841/1000000000000 : ℝ) (986193952837/1000000000000 : ℝ) (986193952841/1000000000000 : ℝ) (986193952837/1000000000000 : ℝ) (986193952841/1000000000000 : ℝ) (986193952837/1000000000000 : ℝ) (986193952841/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (25/128 : ℝ)) 5 (986193952837/1000000000000 : ℝ) (986193952841/1000000000000 : ℝ) (986193952837/1000000000000 : ℝ) (986193952841/1000000000000 : ℝ) (986193952837/1000000000000 : ℝ) (986193952841/1000000000000 : ℝ) (986193952837/1000000000000 : ℝ) (986193952841/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (25/128 : ℝ)) 6 (986193952837/1000000000000 : ℝ) (986193952841/1000000000000 : ℝ) (986193952837/1000000000000 : ℝ) (986193952841/1000000000000 : ℝ) (986193952837/1000000000000 : ℝ) (986193952841/1000000000000 : ℝ) (986193952837/1000000000000 : ℝ) (986193952841/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (25/128 : ℝ)) 7 (986193952837/1000000000000 : ℝ) (986193952841/1000000000000 : ℝ) (986193952837/1000000000000 : ℝ) (986193952841/1000000000000 : ℝ) (986193952837/1000000000000 : ℝ) (986193952841/1000000000000 : ℝ) (986193952837/1000000000000 : ℝ) (986193952841/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (25/128 : ℝ))) (232970201879/1000000000000 : ℝ) (58242550471/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (25/128 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (232970201879/1000000000000 : ℝ) (58242550471/250000000000 : ℝ) (616485100939/1000000000000 : ℝ) (308242550471/500000000000 : ℝ) (241334934209/500000000000 : ℝ) (60333733553/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (25/128 : ℝ))) 1 (616485100939/1000000000000 : ℝ) (308242550471/500000000000 : ℝ) (241334934209/500000000000 : ℝ) (60333733553/125000000000 : ℝ) (274788742339/500000000000 : ℝ) (549577484683/1000000000000 : ℝ) (545489488947/1000000000000 : ℝ) (68186186119/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (25/128 : ℝ))) 2 (274788742339/500000000000 : ℝ) (549577484683/1000000000000 : ℝ) (545489488947/1000000000000 : ℝ) (68186186119/125000000000 : ℝ) (136883371703/250000000000 : ℝ) (273766743409/500000000000 : ℝ) (547529671573/1000000000000 : ℝ) (547529671579/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (25/128 : ℝ))) 3 (136883371703/250000000000 : ℝ) (273766743409/500000000000 : ℝ) (547529671573/1000000000000 : ℝ) (547529671579/1000000000000 : ℝ) (68441447399/125000000000 : ℝ) (547531579199/1000000000000 : ℝ) (547531579189/1000000000000 : ℝ) (136882894799/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (25/128 : ℝ))) 4 (68441447399/125000000000 : ℝ) (547531579199/1000000000000 : ℝ) (547531579189/1000000000000 : ℝ) (136882894799/250000000000 : ℝ) (54753157919/100000000000 : ℝ) (273765789599/500000000000 : ℝ) (54753157919/100000000000 : ℝ) (273765789599/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (25/128 : ℝ))) 5 (54753157919/100000000000 : ℝ) (273765789599/500000000000 : ℝ) (54753157919/100000000000 : ℝ) (273765789599/500000000000 : ℝ) (54753157919/100000000000 : ℝ) (273765789599/500000000000 : ℝ) (54753157919/100000000000 : ℝ) (273765789599/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (25/128 : ℝ))) 6 (54753157919/100000000000 : ℝ) (273765789599/500000000000 : ℝ) (54753157919/100000000000 : ℝ) (273765789599/500000000000 : ℝ) (54753157919/100000000000 : ℝ) (273765789599/500000000000 : ℝ) (54753157919/100000000000 : ℝ) (273765789599/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (25/128 : ℝ))) 7 (54753157919/100000000000 : ℝ) (273765789599/500000000000 : ℝ) (54753157919/100000000000 : ℝ) (273765789599/500000000000 : ℝ) (54753157919/100000000000 : ℝ) (273765789599/500000000000 : ℝ) (54753157919/100000000000 : ℝ) (273765789599/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (25/128 : ℝ)) hmem 8 (986193952837/1000000000000 : ℝ) (986193952841/1000000000000 : ℝ) (986193952837/1000000000000 : ℝ) (986193952841/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (25/128 : ℝ))) hcmem 8 (54753157919/100000000000 : ℝ) (273765789599/500000000000 : ℝ) (54753157919/100000000000 : ℝ) (273765789599/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (25/128 : ℝ)) (986193952837/1000000000000 : ℝ) (986193952841/1000000000000 : ℝ) (54753157919/100000000000 : ℝ) (273765789599/500000000000 : ℝ) (436050429491/500000000000 : ℝ) (872100858999/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0632_exp_lower
  have heNumeric : (63283151729/31250000000 : ℝ)/4 ≤ Real.exp (-680694608999/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (63283151729/31250000000 : ℝ)/4 ≤ Real.exp ((49/256 : ℝ)-(872100858999/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (49/256 : ℝ) (25/128 : ℝ) (872100858999/1000000000000 : ℝ) (63283151729/31250000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0633; no trusted numerical premise.
theorem cover7_leaf0633_exp_radius : (39855173532682271/40000000000000000 : ℝ) ≤ Real.exp ((-13/448 : ℝ)/8) ∧ Real.exp ((-13/448 : ℝ)/8) ≤ (124547417289632097/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-13/448 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0633_exp_lower : (459091120716215069/500000000000000000 : ℝ) ≤ Real.exp ((-341437551941/500000000000 : ℝ)/8) ∧ Real.exp ((-341437551941/500000000000 : ℝ)/8) ≤ (918182241432430139/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-341437551941/500000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0633_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (505162507783/250000000000 : ℝ) ≤ 4*Real.exp (25/128 : ℝ)*Real.exp (-mu (radius 7 (13/64 : ℝ))) ∧ (2019/1000 : ℝ) < (505162507783/250000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (13/64 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0633_exp_radius
  have hrNumeric : (485699558949/500000000000 : ℝ) ≤ Real.exp (-13/448 : ℝ) ∧ Real.exp (-13/448 : ℝ) ≤ (971399117899/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (485699558949/500000000000 : ℝ) ≤ (radius 7 (13/64 : ℝ)) ∧ (radius 7 (13/64 : ℝ)) ≤ (971399117899/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (13/64 : ℝ)) (485699558949/500000000000 : ℝ) (971399117899/1000000000000 : ℝ) (11872631737/50000000000 : ℝ) (47490526949/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (13/64 : ℝ)) (485699558949/500000000000 : ℝ) (971399117899/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (13/64 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (485699558949/500000000000 : ℝ) (971399117899/1000000000000 : ℝ) (985699558949/1000000000000 : ℝ) (19713991179/20000000000 : ℝ) (985595818729/1000000000000 : ℝ) (985595818731/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (13/64 : ℝ)) 1 (985699558949/1000000000000 : ℝ) (19713991179/20000000000 : ℝ) (985595818729/1000000000000 : ℝ) (985595818731/1000000000000 : ℝ) (985647688839/1000000000000 : ℝ) (985647688841/1000000000000 : ℝ) (492823843737/500000000000 : ℝ) (246411921869/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (13/64 : ℝ)) 2 (985647688839/1000000000000 : ℝ) (985647688841/1000000000000 : ℝ) (492823843737/500000000000 : ℝ) (246411921869/250000000000 : ℝ) (246411922039/250000000000 : ℝ) (985647688159/1000000000000 : ℝ) (246411922039/250000000000 : ℝ) (985647688159/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (13/64 : ℝ)) 3 (246411922039/250000000000 : ℝ) (985647688159/1000000000000 : ℝ) (246411922039/250000000000 : ℝ) (985647688159/1000000000000 : ℝ) (246411922039/250000000000 : ℝ) (985647688159/1000000000000 : ℝ) (246411922039/250000000000 : ℝ) (985647688159/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (13/64 : ℝ)) 4 (246411922039/250000000000 : ℝ) (985647688159/1000000000000 : ℝ) (246411922039/250000000000 : ℝ) (985647688159/1000000000000 : ℝ) (246411922039/250000000000 : ℝ) (985647688159/1000000000000 : ℝ) (246411922039/250000000000 : ℝ) (985647688159/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (13/64 : ℝ)) 5 (246411922039/250000000000 : ℝ) (985647688159/1000000000000 : ℝ) (246411922039/250000000000 : ℝ) (985647688159/1000000000000 : ℝ) (246411922039/250000000000 : ℝ) (985647688159/1000000000000 : ℝ) (246411922039/250000000000 : ℝ) (985647688159/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (13/64 : ℝ)) 6 (246411922039/250000000000 : ℝ) (985647688159/1000000000000 : ℝ) (246411922039/250000000000 : ℝ) (985647688159/1000000000000 : ℝ) (246411922039/250000000000 : ℝ) (985647688159/1000000000000 : ℝ) (246411922039/250000000000 : ℝ) (985647688159/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (13/64 : ℝ)) 7 (246411922039/250000000000 : ℝ) (985647688159/1000000000000 : ℝ) (246411922039/250000000000 : ℝ) (985647688159/1000000000000 : ℝ) (246411922039/250000000000 : ℝ) (985647688159/1000000000000 : ℝ) (246411922039/250000000000 : ℝ) (985647688159/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (13/64 : ℝ))) (11872631737/50000000000 : ℝ) (47490526949/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (13/64 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (11872631737/50000000000 : ℝ) (47490526949/200000000000 : ℝ) (61872631737/100000000000 : ℝ) (618726317373/1000000000000 : ℝ) (97458223817/200000000000 : ℝ) (121822779773/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (13/64 : ℝ))) 1 (61872631737/100000000000 : ℝ) (618726317373/1000000000000 : ℝ) (97458223817/200000000000 : ℝ) (121822779773/250000000000 : ℝ) (553008718227/1000000000000 : ℝ) (553008718233/1000000000000 : ℝ) (54909001047/100000000000 : ℝ) (137272502619/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (13/64 : ℝ))) 2 (553008718227/1000000000000 : ℝ) (553008718233/1000000000000 : ℝ) (54909001047/100000000000 : ℝ) (137272502619/250000000000 : ℝ) (137762341087/250000000000 : ℝ) (110209872871/200000000000 : ℝ) (275522940461/500000000000 : ℝ) (551045880929/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (13/64 : ℝ))) 3 (137762341087/250000000000 : ℝ) (110209872871/200000000000 : ℝ) (275522940461/500000000000 : ℝ) (551045880929/1000000000000 : ℝ) (110209524527/200000000000 : ℝ) (275523811321/500000000000 : ℝ) (68880952829/125000000000 : ℝ) (6888095283/12500000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (13/64 : ℝ))) 4 (110209524527/200000000000 : ℝ) (275523811321/500000000000 : ℝ) (68880952829/125000000000 : ℝ) (6888095283/12500000000 : ℝ) (551047622633/1000000000000 : ℝ) (551047622641/1000000000000 : ℝ) (551047622633/1000000000000 : ℝ) (551047622641/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (13/64 : ℝ))) 5 (551047622633/1000000000000 : ℝ) (551047622641/1000000000000 : ℝ) (551047622633/1000000000000 : ℝ) (551047622641/1000000000000 : ℝ) (551047622633/1000000000000 : ℝ) (551047622641/1000000000000 : ℝ) (551047622633/1000000000000 : ℝ) (551047622641/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (13/64 : ℝ))) 6 (551047622633/1000000000000 : ℝ) (551047622641/1000000000000 : ℝ) (551047622633/1000000000000 : ℝ) (551047622641/1000000000000 : ℝ) (551047622633/1000000000000 : ℝ) (551047622641/1000000000000 : ℝ) (551047622633/1000000000000 : ℝ) (551047622641/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (13/64 : ℝ))) 7 (551047622633/1000000000000 : ℝ) (551047622641/1000000000000 : ℝ) (551047622633/1000000000000 : ℝ) (551047622641/1000000000000 : ℝ) (551047622633/1000000000000 : ℝ) (551047622641/1000000000000 : ℝ) (551047622633/1000000000000 : ℝ) (551047622641/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (13/64 : ℝ)) hmem 8 (246411922039/250000000000 : ℝ) (985647688159/1000000000000 : ℝ) (246411922039/250000000000 : ℝ) (985647688159/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (13/64 : ℝ))) hcmem 8 (551047622633/1000000000000 : ℝ) (551047622641/1000000000000 : ℝ) (551047622633/1000000000000 : ℝ) (551047622641/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (13/64 : ℝ)) (246411922039/250000000000 : ℝ) (985647688159/1000000000000 : ℝ) (551047622633/1000000000000 : ℝ) (551047622641/1000000000000 : ℝ) (439093801933/500000000000 : ℝ) (439093801941/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0633_exp_lower
  have heNumeric : (505162507783/250000000000 : ℝ)/4 ≤ Real.exp (-341437551941/500000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (505162507783/250000000000 : ℝ)/4 ≤ Real.exp ((25/128 : ℝ)-(439093801941/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (25/128 : ℝ) (13/64 : ℝ) (439093801941/500000000000 : ℝ) (505162507783/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0634; no trusted numerical premise.
theorem cover7_leaf0634_exp_radius : (199248068839760629/200000000000000000 : ℝ) ≤ Real.exp ((-27/896 : ℝ)/8) ∧ Real.exp ((-27/896 : ℝ)/8) ≤ (498120172099401573/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-27/896 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0634_exp_lower : (918397437969920149/1000000000000000000 : ℝ) ≤ Real.exp ((-681000344701/1000000000000 : ℝ)/8) ∧ Real.exp ((-681000344701/1000000000000 : ℝ)/8) ≤ (18367948759398403/20000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-681000344701/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0634_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2024441816561/1000000000000 : ℝ) ≤ 4*Real.exp (13/64 : ℝ)*Real.exp (-mu (radius 7 (27/128 : ℝ))) ∧ (2019/1000 : ℝ) < (2024441816561/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (27/128 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0634_exp_radius
  have hrNumeric : (970315571867/1000000000000 : ℝ) ≤ Real.exp (-27/896 : ℝ) ∧ Real.exp (-27/896 : ℝ) ≤ (242578892967/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (970315571867/1000000000000 : ℝ) ≤ (radius 7 (27/128 : ℝ)) ∧ (radius 7 (27/128 : ℝ)) ≤ (242578892967/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (27/128 : ℝ)) (970315571867/1000000000000 : ℝ) (242578892967/250000000000 : ℝ) (60460571341/250000000000 : ℝ) (241842285369/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (27/128 : ℝ)) (970315571867/1000000000000 : ℝ) (242578892967/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (27/128 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (970315571867/1000000000000 : ℝ) (242578892967/250000000000 : ℝ) (985157785933/1000000000000 : ℝ) (492578892967/500000000000 : ℝ) (492522987247/500000000000 : ℝ) (197009194899/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (27/128 : ℝ)) 1 (985157785933/1000000000000 : ℝ) (492578892967/500000000000 : ℝ) (492522987247/500000000000 : ℝ) (197009194899/200000000000 : ℝ) (985101880213/1000000000000 : ℝ) (197020376043/200000000000 : ℝ) (985101878627/1000000000000 : ℝ) (985101878629/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (27/128 : ℝ)) 2 (985101880213/1000000000000 : ℝ) (197020376043/200000000000 : ℝ) (985101878627/1000000000000 : ℝ) (985101878629/1000000000000 : ℝ) (49255093971/50000000000 : ℝ) (492550939711/500000000000 : ℝ) (985101879419/1000000000000 : ℝ) (492550939711/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (27/128 : ℝ)) 3 (49255093971/50000000000 : ℝ) (492550939711/500000000000 : ℝ) (985101879419/1000000000000 : ℝ) (492550939711/500000000000 : ℝ) (985101879419/1000000000000 : ℝ) (492550939711/500000000000 : ℝ) (985101879419/1000000000000 : ℝ) (492550939711/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (27/128 : ℝ)) 4 (985101879419/1000000000000 : ℝ) (492550939711/500000000000 : ℝ) (985101879419/1000000000000 : ℝ) (492550939711/500000000000 : ℝ) (985101879419/1000000000000 : ℝ) (492550939711/500000000000 : ℝ) (985101879419/1000000000000 : ℝ) (492550939711/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (27/128 : ℝ)) 5 (985101879419/1000000000000 : ℝ) (492550939711/500000000000 : ℝ) (985101879419/1000000000000 : ℝ) (492550939711/500000000000 : ℝ) (985101879419/1000000000000 : ℝ) (492550939711/500000000000 : ℝ) (985101879419/1000000000000 : ℝ) (492550939711/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (27/128 : ℝ)) 6 (985101879419/1000000000000 : ℝ) (492550939711/500000000000 : ℝ) (985101879419/1000000000000 : ℝ) (492550939711/500000000000 : ℝ) (985101879419/1000000000000 : ℝ) (492550939711/500000000000 : ℝ) (985101879419/1000000000000 : ℝ) (492550939711/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (27/128 : ℝ)) 7 (985101879419/1000000000000 : ℝ) (492550939711/500000000000 : ℝ) (985101879419/1000000000000 : ℝ) (492550939711/500000000000 : ℝ) (985101879419/1000000000000 : ℝ) (492550939711/500000000000 : ℝ) (985101879419/1000000000000 : ℝ) (492550939711/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (27/128 : ℝ))) (60460571341/250000000000 : ℝ) (241842285369/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (27/128 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (60460571341/250000000000 : ℝ) (241842285369/1000000000000 : ℝ) (310460571341/500000000000 : ℝ) (124184228537/200000000000 : ℝ) (491774628629/1000000000000 : ℝ) (98354925727/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (27/128 : ℝ))) 1 (310460571341/500000000000 : ℝ) (124184228537/200000000000 : ℝ) (491774628629/1000000000000 : ℝ) (98354925727/200000000000 : ℝ) (111269577131/200000000000 : ℝ) (27817394283/50000000000 : ℝ) (552587788817/1000000000000 : ℝ) (552587788823/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (27/128 : ℝ))) 2 (111269577131/200000000000 : ℝ) (27817394283/50000000000 : ℝ) (552587788817/1000000000000 : ℝ) (552587788823/1000000000000 : ℝ) (138616959309/250000000000 : ℝ) (277233918621/500000000000 : ℝ) (277232324931/500000000000 : ℝ) (138616162467/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (27/128 : ℝ))) 3 (138616959309/250000000000 : ℝ) (277233918621/500000000000 : ℝ) (277232324931/500000000000 : ℝ) (138616162467/250000000000 : ℝ) (554466243549/1000000000000 : ℝ) (110893248711/200000000000 : ℝ) (277233121773/500000000000 : ℝ) (554466243553/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (27/128 : ℝ))) 4 (554466243549/1000000000000 : ℝ) (110893248711/200000000000 : ℝ) (277233121773/500000000000 : ℝ) (554466243553/1000000000000 : ℝ) (554466243547/1000000000000 : ℝ) (277233121777/500000000000 : ℝ) (554466243547/1000000000000 : ℝ) (277233121777/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (27/128 : ℝ))) 5 (554466243547/1000000000000 : ℝ) (277233121777/500000000000 : ℝ) (554466243547/1000000000000 : ℝ) (277233121777/500000000000 : ℝ) (554466243547/1000000000000 : ℝ) (277233121777/500000000000 : ℝ) (554466243547/1000000000000 : ℝ) (277233121777/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (27/128 : ℝ))) 6 (554466243547/1000000000000 : ℝ) (277233121777/500000000000 : ℝ) (554466243547/1000000000000 : ℝ) (277233121777/500000000000 : ℝ) (554466243547/1000000000000 : ℝ) (277233121777/500000000000 : ℝ) (554466243547/1000000000000 : ℝ) (277233121777/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (27/128 : ℝ))) 7 (554466243547/1000000000000 : ℝ) (277233121777/500000000000 : ℝ) (554466243547/1000000000000 : ℝ) (277233121777/500000000000 : ℝ) (554466243547/1000000000000 : ℝ) (277233121777/500000000000 : ℝ) (554466243547/1000000000000 : ℝ) (277233121777/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (27/128 : ℝ)) hmem 8 (985101879419/1000000000000 : ℝ) (492550939711/500000000000 : ℝ) (985101879419/1000000000000 : ℝ) (492550939711/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (27/128 : ℝ))) hcmem 8 (554466243547/1000000000000 : ℝ) (277233121777/500000000000 : ℝ) (554466243547/1000000000000 : ℝ) (277233121777/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (27/128 : ℝ)) (985101879419/1000000000000 : ℝ) (492550939711/500000000000 : ℝ) (554466243547/1000000000000 : ℝ) (277233121777/500000000000 : ℝ) (442062672343/500000000000 : ℝ) (884125344701/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0634_exp_lower
  have heNumeric : (2024441816561/1000000000000 : ℝ)/4 ≤ Real.exp (-681000344701/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2024441816561/1000000000000 : ℝ)/4 ≤ Real.exp ((13/64 : ℝ)-(884125344701/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (13/64 : ℝ) (27/128 : ℝ) (884125344701/1000000000000 : ℝ) (2024441816561/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0635; no trusted numerical premise.
theorem cover7_leaf0635_exp_radius : (99610136947011749/100000000000000000 : ℝ) ≤ Real.exp ((-1/32 : ℝ)/8) ∧ Real.exp ((-1/32 : ℝ)/8) ≤ (996101369470117491/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1/32 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0635_exp_lower : (459314352710797233/500000000000000000 : ℝ) ≤ Real.exp ((-169746516961/250000000000 : ℝ)/8) ∧ Real.exp ((-169746516961/250000000000 : ℝ)/8) ≤ (918628705421594467/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-169746516961/250000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0635_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (405704742503/200000000000 : ℝ) ≤ 4*Real.exp (27/128 : ℝ)*Real.exp (-mu (radius 7 (7/32 : ℝ))) ∧ (2019/1000 : ℝ) < (405704742503/200000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (7/32 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0635_exp_radius
  have hrNumeric : (242308308619/250000000000 : ℝ) ≤ Real.exp (-1/32 : ℝ) ∧ Real.exp (-1/32 : ℝ) ≤ (969233234477/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (242308308619/250000000000 : ℝ) ≤ (radius 7 (7/32 : ℝ)) ∧ (radius 7 (7/32 : ℝ)) ≤ (969233234477/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (7/32 : ℝ)) (242308308619/250000000000 : ℝ) (969233234477/1000000000000 : ℝ) (246144139043/1000000000000 : ℝ) (30768017381/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (7/32 : ℝ)) (242308308619/250000000000 : ℝ) (969233234477/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (7/32 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (242308308619/250000000000 : ℝ) (969233234477/1000000000000 : ℝ) (492308308619/500000000000 : ℝ) (984616617239/1000000000000 : ℝ) (196899287401/200000000000 : ℝ) (492248218503/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (7/32 : ℝ)) 1 (492308308619/500000000000 : ℝ) (984616617239/1000000000000 : ℝ) (196899287401/200000000000 : ℝ) (492248218503/500000000000 : ℝ) (984556527121/1000000000000 : ℝ) (984556527123/1000000000000 : ℝ) (984556525287/1000000000000 : ℝ) (984556525289/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (7/32 : ℝ)) 2 (984556527121/1000000000000 : ℝ) (984556527123/1000000000000 : ℝ) (984556525287/1000000000000 : ℝ) (984556525289/1000000000000 : ℝ) (246139131551/250000000000 : ℝ) (492278263103/500000000000 : ℝ) (984556526203/1000000000000 : ℝ) (492278263103/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (7/32 : ℝ)) 3 (246139131551/250000000000 : ℝ) (492278263103/500000000000 : ℝ) (984556526203/1000000000000 : ℝ) (492278263103/500000000000 : ℝ) (984556526203/1000000000000 : ℝ) (492278263103/500000000000 : ℝ) (984556526203/1000000000000 : ℝ) (492278263103/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (7/32 : ℝ)) 4 (984556526203/1000000000000 : ℝ) (492278263103/500000000000 : ℝ) (984556526203/1000000000000 : ℝ) (492278263103/500000000000 : ℝ) (984556526203/1000000000000 : ℝ) (492278263103/500000000000 : ℝ) (984556526203/1000000000000 : ℝ) (492278263103/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (7/32 : ℝ)) 5 (984556526203/1000000000000 : ℝ) (492278263103/500000000000 : ℝ) (984556526203/1000000000000 : ℝ) (492278263103/500000000000 : ℝ) (984556526203/1000000000000 : ℝ) (492278263103/500000000000 : ℝ) (984556526203/1000000000000 : ℝ) (492278263103/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (7/32 : ℝ)) 6 (984556526203/1000000000000 : ℝ) (492278263103/500000000000 : ℝ) (984556526203/1000000000000 : ℝ) (492278263103/500000000000 : ℝ) (984556526203/1000000000000 : ℝ) (492278263103/500000000000 : ℝ) (984556526203/1000000000000 : ℝ) (492278263103/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (7/32 : ℝ)) 7 (984556526203/1000000000000 : ℝ) (492278263103/500000000000 : ℝ) (984556526203/1000000000000 : ℝ) (492278263103/500000000000 : ℝ) (984556526203/1000000000000 : ℝ) (492278263103/500000000000 : ℝ) (984556526203/1000000000000 : ℝ) (492278263103/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (7/32 : ℝ))) (246144139043/1000000000000 : ℝ) (30768017381/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (7/32 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (246144139043/1000000000000 : ℝ) (30768017381/125000000000 : ℝ) (623072069521/1000000000000 : ℝ) (155768017381/250000000000 : ℝ) (248064577803/500000000000 : ℝ) (124032288903/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (7/32 : ℝ))) 1 (623072069521/1000000000000 : ℝ) (155768017381/250000000000 : ℝ) (248064577803/500000000000 : ℝ) (124032288903/250000000000 : ℝ) (559600612563/1000000000000 : ℝ) (69950076571/125000000000 : ℝ) (555989406133/1000000000000 : ℝ) (555989406139/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (7/32 : ℝ))) 2 (559600612563/1000000000000 : ℝ) (69950076571/125000000000 : ℝ) (555989406133/1000000000000 : ℝ) (555989406139/1000000000000 : ℝ) (139448752337/250000000000 : ℝ) (278897504677/500000000000 : ℝ) (557792086937/1000000000000 : ℝ) (17431002717/31250000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (7/32 : ℝ))) 3 (139448752337/250000000000 : ℝ) (278897504677/500000000000 : ℝ) (557792086937/1000000000000 : ℝ) (17431002717/31250000000 : ℝ) (278896774071/500000000000 : ℝ) (557793548149/1000000000000 : ℝ) (27889677407/50000000000 : ℝ) (139448387037/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (7/32 : ℝ))) 4 (278896774071/500000000000 : ℝ) (557793548149/1000000000000 : ℝ) (27889677407/50000000000 : ℝ) (139448387037/250000000000 : ℝ) (557793548141/1000000000000 : ℝ) (557793548149/1000000000000 : ℝ) (27889677407/50000000000 : ℝ) (557793548149/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (7/32 : ℝ))) 5 (557793548141/1000000000000 : ℝ) (557793548149/1000000000000 : ℝ) (27889677407/50000000000 : ℝ) (557793548149/1000000000000 : ℝ) (27889677407/50000000000 : ℝ) (557793548149/1000000000000 : ℝ) (27889677407/50000000000 : ℝ) (557793548149/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (7/32 : ℝ))) 6 (27889677407/50000000000 : ℝ) (557793548149/1000000000000 : ℝ) (27889677407/50000000000 : ℝ) (557793548149/1000000000000 : ℝ) (27889677407/50000000000 : ℝ) (557793548149/1000000000000 : ℝ) (27889677407/50000000000 : ℝ) (557793548149/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (7/32 : ℝ))) 7 (27889677407/50000000000 : ℝ) (557793548149/1000000000000 : ℝ) (27889677407/50000000000 : ℝ) (557793548149/1000000000000 : ℝ) (27889677407/50000000000 : ℝ) (557793548149/1000000000000 : ℝ) (27889677407/50000000000 : ℝ) (557793548149/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (7/32 : ℝ)) hmem 8 (984556526203/1000000000000 : ℝ) (492278263103/500000000000 : ℝ) (984556526203/1000000000000 : ℝ) (492278263103/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (7/32 : ℝ))) hcmem 8 (27889677407/50000000000 : ℝ) (557793548149/1000000000000 : ℝ) (27889677407/50000000000 : ℝ) (557793548149/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (7/32 : ℝ)) (984556526203/1000000000000 : ℝ) (492278263103/500000000000 : ℝ) (27889677407/50000000000 : ℝ) (557793548149/1000000000000 : ℝ) (444961783913/500000000000 : ℝ) (222480891961/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0635_exp_lower
  have heNumeric : (405704742503/200000000000 : ℝ)/4 ≤ Real.exp (-169746516961/250000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (405704742503/200000000000 : ℝ)/4 ≤ Real.exp ((27/128 : ℝ)-(222480891961/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (27/128 : ℝ) (7/32 : ℝ) (222480891961/250000000000 : ℝ) (405704742503/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0636; no trusted numerical premise.
theorem cover7_leaf0636_exp_radius : (199164695634126233/200000000000000000 : ℝ) ≤ Real.exp ((-15/448 : ℝ)/8) ∧ Real.exp ((-15/448 : ℝ)/8) ≤ (497911739085315583/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-15/448 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0636_exp_lower : (114779812844083767/125000000000000000 : ℝ) ≤ Real.exp ((-170596230371/250000000000 : ℝ)/8) ∧ Real.exp ((-170596230371/250000000000 : ℝ)/8) ≤ (918238502752670137/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-170596230371/250000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0636_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2021640761009/1000000000000 : ℝ) ≤ 4*Real.exp (7/32 : ℝ)*Real.exp (-mu (radius 7 (15/64 : ℝ))) ∧ (2019/1000 : ℝ) < (2021640761009/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (15/64 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0636_exp_radius
  have hrNumeric : (967072180223/1000000000000 : ℝ) ≤ Real.exp (-15/448 : ℝ) ∧ Real.exp (-15/448 : ℝ) ≤ (472203213/488281250 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (967072180223/1000000000000 : ℝ) ≤ (radius 7 (15/64 : ℝ)) ∧ (radius 7 (15/64 : ℝ)) ≤ (472203213/488281250 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (15/64 : ℝ)) (967072180223/1000000000000 : ℝ) (472203213/488281250 : ℝ) (254502255857/1000000000000 : ℝ) (127251127931/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (15/64 : ℝ)) (967072180223/1000000000000 : ℝ) (472203213/488281250 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (15/64 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (967072180223/1000000000000 : ℝ) (472203213/488281250 : ℝ) (983536090111/1000000000000 : ℝ) (960484463/976562500 : ℝ) (61462392599/62500000000 : ℝ) (196679656317/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (15/64 : ℝ)) 1 (983536090111/1000000000000 : ℝ) (960484463/976562500 : ℝ) (61462392599/62500000000 : ℝ) (196679656317/200000000000 : ℝ) (983467185847/1000000000000 : ℝ) (983467185849/1000000000000 : ℝ) (983467183433/1000000000000 : ℝ) (196693436687/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (15/64 : ℝ)) 2 (983467185847/1000000000000 : ℝ) (983467185849/1000000000000 : ℝ) (983467183433/1000000000000 : ℝ) (196693436687/200000000000 : ℝ) (384166869/390625000 : ℝ) (491733592321/500000000000 : ℝ) (983467184639/1000000000000 : ℝ) (491733592321/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (15/64 : ℝ)) 3 (384166869/390625000 : ℝ) (491733592321/500000000000 : ℝ) (983467184639/1000000000000 : ℝ) (491733592321/500000000000 : ℝ) (983467184639/1000000000000 : ℝ) (491733592321/500000000000 : ℝ) (983467184639/1000000000000 : ℝ) (491733592321/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (15/64 : ℝ)) 4 (983467184639/1000000000000 : ℝ) (491733592321/500000000000 : ℝ) (983467184639/1000000000000 : ℝ) (491733592321/500000000000 : ℝ) (983467184639/1000000000000 : ℝ) (491733592321/500000000000 : ℝ) (983467184639/1000000000000 : ℝ) (491733592321/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (15/64 : ℝ)) 5 (983467184639/1000000000000 : ℝ) (491733592321/500000000000 : ℝ) (983467184639/1000000000000 : ℝ) (491733592321/500000000000 : ℝ) (983467184639/1000000000000 : ℝ) (491733592321/500000000000 : ℝ) (983467184639/1000000000000 : ℝ) (491733592321/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (15/64 : ℝ)) 6 (983467184639/1000000000000 : ℝ) (491733592321/500000000000 : ℝ) (983467184639/1000000000000 : ℝ) (491733592321/500000000000 : ℝ) (983467184639/1000000000000 : ℝ) (491733592321/500000000000 : ℝ) (983467184639/1000000000000 : ℝ) (491733592321/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (15/64 : ℝ)) 7 (983467184639/1000000000000 : ℝ) (491733592321/500000000000 : ℝ) (983467184639/1000000000000 : ℝ) (491733592321/500000000000 : ℝ) (983467184639/1000000000000 : ℝ) (491733592321/500000000000 : ℝ) (983467184639/1000000000000 : ℝ) (491733592321/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (15/64 : ℝ))) (254502255857/1000000000000 : ℝ) (127251127931/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (15/64 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (254502255857/1000000000000 : ℝ) (127251127931/500000000000 : ℝ) (78406390991/125000000000 : ℝ) (627251127931/1000000000000 : ℝ) (126120541511/250000000000 : ℝ) (10089643321/20000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (15/64 : ℝ))) 1 (78406390991/125000000000 : ℝ) (627251127931/1000000000000 : ℝ) (126120541511/250000000000 : ℝ) (10089643321/20000000000 : ℝ) (282933323493/500000000000 : ℝ) (565866646991/1000000000000 : ℝ) (562527339487/1000000000000 : ℝ) (140631834873/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (15/64 : ℝ))) 2 (282933323493/500000000000 : ℝ) (565866646991/1000000000000 : ℝ) (562527339487/1000000000000 : ℝ) (140631834873/250000000000 : ℝ) (141049248309/250000000000 : ℝ) (282098496621/500000000000 : ℝ) (56419452269/100000000000 : ℝ) (70524315337/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (15/64 : ℝ))) 3 (141049248309/250000000000 : ℝ) (282098496621/500000000000 : ℝ) (56419452269/100000000000 : ℝ) (70524315337/125000000000 : ℝ) (564195757963/1000000000000 : ℝ) (564195757969/1000000000000 : ℝ) (564195757961/1000000000000 : ℝ) (35262234873/62500000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (15/64 : ℝ))) 4 (564195757963/1000000000000 : ℝ) (564195757969/1000000000000 : ℝ) (564195757961/1000000000000 : ℝ) (35262234873/62500000000 : ℝ) (282097878981/500000000000 : ℝ) (564195757969/1000000000000 : ℝ) (564195757961/1000000000000 : ℝ) (564195757969/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (15/64 : ℝ))) 5 (282097878981/500000000000 : ℝ) (564195757969/1000000000000 : ℝ) (564195757961/1000000000000 : ℝ) (564195757969/1000000000000 : ℝ) (564195757961/1000000000000 : ℝ) (564195757969/1000000000000 : ℝ) (564195757961/1000000000000 : ℝ) (564195757969/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (15/64 : ℝ))) 6 (564195757961/1000000000000 : ℝ) (564195757969/1000000000000 : ℝ) (564195757961/1000000000000 : ℝ) (564195757969/1000000000000 : ℝ) (564195757961/1000000000000 : ℝ) (564195757969/1000000000000 : ℝ) (564195757961/1000000000000 : ℝ) (564195757969/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (15/64 : ℝ))) 7 (564195757961/1000000000000 : ℝ) (564195757969/1000000000000 : ℝ) (564195757961/1000000000000 : ℝ) (564195757969/1000000000000 : ℝ) (564195757961/1000000000000 : ℝ) (564195757969/1000000000000 : ℝ) (564195757961/1000000000000 : ℝ) (564195757969/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (15/64 : ℝ)) hmem 8 (983467184639/1000000000000 : ℝ) (491733592321/500000000000 : ℝ) (983467184639/1000000000000 : ℝ) (491733592321/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (15/64 : ℝ))) hcmem 8 (564195757961/1000000000000 : ℝ) (564195757969/1000000000000 : ℝ) (564195757961/1000000000000 : ℝ) (564195757969/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (15/64 : ℝ)) (983467184639/1000000000000 : ℝ) (491733592321/500000000000 : ℝ) (564195757961/1000000000000 : ℝ) (564195757969/1000000000000 : ℝ) (901134921467/1000000000000 : ℝ) (225283730371/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0636_exp_lower
  have heNumeric : (2021640761009/1000000000000 : ℝ)/4 ≤ Real.exp (-170596230371/250000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2021640761009/1000000000000 : ℝ)/4 ≤ Real.exp ((7/32 : ℝ)-(225283730371/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (7/32 : ℝ) (15/64 : ℝ) (225283730371/250000000000 : ℝ) (2021640761009/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0637; no trusted numerical premise.
theorem cover7_leaf0637_exp_radius : (497772832198481847/500000000000000000 : ℝ) ≤ Real.exp ((-1/28 : ℝ)/8) ∧ Real.exp ((-1/28 : ℝ)/8) ≤ (199109132879392739/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1/28 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0637_exp_lower : (45939932959172663/50000000000000000 : ℝ) ≤ Real.exp ((-84688267481/125000000000 : ℝ)/8) ∧ Real.exp ((-84688267481/125000000000 : ℝ)/8) ≤ (918798659183453261/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-84688267481/125000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0637_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2031528004067/1000000000000 : ℝ) ≤ 4*Real.exp (15/64 : ℝ)*Real.exp (-mu (radius 7 (1/4 : ℝ))) ∧ (2019/1000 : ℝ) < (2031528004067/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (1/4 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0637_exp_radius
  have hrNumeric : (241228986093/250000000000 : ℝ) ≤ Real.exp (-1/28 : ℝ) ∧ Real.exp (-1/28 : ℝ) ≤ (964915944373/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (241228986093/250000000000 : ℝ) ≤ (radius 7 (1/4 : ℝ)) ∧ (radius 7 (1/4 : ℝ)) ≤ (964915944373/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (1/4 : ℝ)) (241228986093/250000000000 : ℝ) (964915944373/1000000000000 : ℝ) (26255898441/100000000000 : ℝ) (52511796883/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (1/4 : ℝ)) (241228986093/250000000000 : ℝ) (964915944373/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (1/4 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (241228986093/250000000000 : ℝ) (964915944373/1000000000000 : ℝ) (491228986093/500000000000 : ℝ) (982457972187/1000000000000 : ℝ) (982301351099/1000000000000 : ℝ) (982301351101/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (1/4 : ℝ)) 1 (491228986093/500000000000 : ℝ) (982457972187/1000000000000 : ℝ) (982301351099/1000000000000 : ℝ) (982301351101/1000000000000 : ℝ) (491189830821/500000000000 : ℝ) (245594915411/250000000000 : ℝ) (982379658521/1000000000000 : ℝ) (982379658523/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (1/4 : ℝ)) 2 (491189830821/500000000000 : ℝ) (245594915411/250000000000 : ℝ) (982379658521/1000000000000 : ℝ) (982379658523/1000000000000 : ℝ) (982379660081/1000000000000 : ℝ) (245594915021/250000000000 : ℝ) (982379660081/1000000000000 : ℝ) (245594915021/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (1/4 : ℝ)) 3 (982379660081/1000000000000 : ℝ) (245594915021/250000000000 : ℝ) (982379660081/1000000000000 : ℝ) (245594915021/250000000000 : ℝ) (982379660081/1000000000000 : ℝ) (245594915021/250000000000 : ℝ) (982379660081/1000000000000 : ℝ) (245594915021/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (1/4 : ℝ)) 4 (982379660081/1000000000000 : ℝ) (245594915021/250000000000 : ℝ) (982379660081/1000000000000 : ℝ) (245594915021/250000000000 : ℝ) (982379660081/1000000000000 : ℝ) (245594915021/250000000000 : ℝ) (982379660081/1000000000000 : ℝ) (245594915021/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (1/4 : ℝ)) 5 (982379660081/1000000000000 : ℝ) (245594915021/250000000000 : ℝ) (982379660081/1000000000000 : ℝ) (245594915021/250000000000 : ℝ) (982379660081/1000000000000 : ℝ) (245594915021/250000000000 : ℝ) (982379660081/1000000000000 : ℝ) (245594915021/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (1/4 : ℝ)) 6 (982379660081/1000000000000 : ℝ) (245594915021/250000000000 : ℝ) (982379660081/1000000000000 : ℝ) (245594915021/250000000000 : ℝ) (982379660081/1000000000000 : ℝ) (245594915021/250000000000 : ℝ) (982379660081/1000000000000 : ℝ) (245594915021/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (1/4 : ℝ)) 7 (982379660081/1000000000000 : ℝ) (245594915021/250000000000 : ℝ) (982379660081/1000000000000 : ℝ) (245594915021/250000000000 : ℝ) (982379660081/1000000000000 : ℝ) (245594915021/250000000000 : ℝ) (982379660081/1000000000000 : ℝ) (245594915021/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (1/4 : ℝ))) (26255898441/100000000000 : ℝ) (52511796883/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (1/4 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (26255898441/100000000000 : ℝ) (52511796883/200000000000 : ℝ) (126255898441/200000000000 : ℝ) (39454968263/62500000000 : ℝ) (256202548977/500000000000 : ℝ) (12810127449/25000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (1/4 : ℝ))) 1 (126255898441/200000000000 : ℝ) (39454968263/62500000000 : ℝ) (256202548977/500000000000 : ℝ) (12810127449/25000000000 : ℝ) (571842295079/1000000000000 : ℝ) (142960573771/250000000000 : ℝ) (142186240113/250000000000 : ℝ) (568744960457/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (1/4 : ℝ))) 2 (571842295079/1000000000000 : ℝ) (142960573771/250000000000 : ℝ) (142186240113/250000000000 : ℝ) (568744960457/1000000000000 : ℝ) (114058725553/200000000000 : ℝ) (570293627771/1000000000000 : ℝ) (570291525011/1000000000000 : ℝ) (570291525017/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (1/4 : ℝ))) 3 (114058725553/200000000000 : ℝ) (570293627771/1000000000000 : ℝ) (570291525011/1000000000000 : ℝ) (570291525017/1000000000000 : ℝ) (142573144097/250000000000 : ℝ) (285146288197/500000000000 : ℝ) (570292576387/1000000000000 : ℝ) (285146288197/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (1/4 : ℝ))) 4 (142573144097/250000000000 : ℝ) (285146288197/500000000000 : ℝ) (570292576387/1000000000000 : ℝ) (285146288197/500000000000 : ℝ) (570292576387/1000000000000 : ℝ) (285146288197/500000000000 : ℝ) (570292576387/1000000000000 : ℝ) (285146288197/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (1/4 : ℝ))) 5 (570292576387/1000000000000 : ℝ) (285146288197/500000000000 : ℝ) (570292576387/1000000000000 : ℝ) (285146288197/500000000000 : ℝ) (570292576387/1000000000000 : ℝ) (285146288197/500000000000 : ℝ) (570292576387/1000000000000 : ℝ) (285146288197/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (1/4 : ℝ))) 6 (570292576387/1000000000000 : ℝ) (285146288197/500000000000 : ℝ) (570292576387/1000000000000 : ℝ) (285146288197/500000000000 : ℝ) (570292576387/1000000000000 : ℝ) (285146288197/500000000000 : ℝ) (570292576387/1000000000000 : ℝ) (285146288197/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (1/4 : ℝ))) 7 (570292576387/1000000000000 : ℝ) (285146288197/500000000000 : ℝ) (570292576387/1000000000000 : ℝ) (285146288197/500000000000 : ℝ) (570292576387/1000000000000 : ℝ) (285146288197/500000000000 : ℝ) (570292576387/1000000000000 : ℝ) (285146288197/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (1/4 : ℝ)) hmem 8 (982379660081/1000000000000 : ℝ) (245594915021/250000000000 : ℝ) (982379660081/1000000000000 : ℝ) (245594915021/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (1/4 : ℝ))) hcmem 8 (570292576387/1000000000000 : ℝ) (285146288197/500000000000 : ℝ) (570292576387/1000000000000 : ℝ) (285146288197/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (1/4 : ℝ)) (982379660081/1000000000000 : ℝ) (245594915021/250000000000 : ℝ) (570292576387/1000000000000 : ℝ) (285146288197/500000000000 : ℝ) (911881139833/1000000000000 : ℝ) (113985142481/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0637_exp_lower
  have heNumeric : (2031528004067/1000000000000 : ℝ)/4 ≤ Real.exp (-84688267481/125000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2031528004067/1000000000000 : ℝ)/4 ≤ Real.exp ((15/64 : ℝ)-(113985142481/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (15/64 : ℝ) (1/4 : ℝ) (113985142481/125000000000 : ℝ) (2031528004067/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0638; no trusted numerical premise.
theorem cover7_leaf0638_exp_radius : (994990269340579069/1000000000000000000 : ℝ) ≤ Real.exp ((-9/224 : ℝ)/8) ∧ Real.exp ((-9/224 : ℝ)/8) ≤ (99499026934057907/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-9/224 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0638_exp_lower : (459131688158737721/500000000000000000 : ℝ) ≤ Real.exp ((-682168217629/1000000000000 : ℝ)/8) ∧ Real.exp ((-682168217629/1000000000000 : ℝ)/8) ≤ (918263376317475443/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-682168217629/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0638_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (505519726457/250000000000 : ℝ) ≤ 4*Real.exp (1/4 : ℝ)*Real.exp (-mu (radius 7 (9/32 : ℝ))) ∧ (2019/1000 : ℝ) < (505519726457/250000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (9/32 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0638_exp_radius
  have hrNumeric : (960617884927/1000000000000 : ℝ) ≤ Real.exp (-9/224 : ℝ) ∧ Real.exp (-9/224 : ℝ) ≤ (3752413613/3906250000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (960617884927/1000000000000 : ℝ) ≤ (radius 7 (9/32 : ℝ)) ∧ (radius 7 (9/32 : ℝ)) ≤ (3752413613/3906250000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (9/32 : ℝ)) (960617884927/1000000000000 : ℝ) (3752413613/3906250000 : ℝ) (138936387563/500000000000 : ℝ) (27787277513/100000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (9/32 : ℝ)) (960617884927/1000000000000 : ℝ) (3752413613/3906250000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (9/32 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (960617884927/1000000000000 : ℝ) (3752413613/3906250000 : ℝ) (980308942463/1000000000000 : ℝ) (7658663613/7812500000 : ℝ) (490055579737/500000000000 : ℝ) (245027789869/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (9/32 : ℝ)) 1 (980308942463/1000000000000 : ℝ) (7658663613/7812500000 : ℝ) (490055579737/500000000000 : ℝ) (245027789869/250000000000 : ℝ) (122526256371/125000000000 : ℝ) (98021005097/100000000000 : ℝ) (49010502299/50000000000 : ℝ) (490105022991/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (9/32 : ℝ)) 2 (122526256371/125000000000 : ℝ) (98021005097/100000000000 : ℝ) (49010502299/50000000000 : ℝ) (490105022991/500000000000 : ℝ) (490105024237/500000000000 : ℝ) (245052512119/250000000000 : ℝ) (980210048473/1000000000000 : ℝ) (245052512119/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (9/32 : ℝ)) 3 (490105024237/500000000000 : ℝ) (245052512119/250000000000 : ℝ) (980210048473/1000000000000 : ℝ) (245052512119/250000000000 : ℝ) (980210048473/1000000000000 : ℝ) (245052512119/250000000000 : ℝ) (980210048473/1000000000000 : ℝ) (245052512119/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (9/32 : ℝ)) 4 (980210048473/1000000000000 : ℝ) (245052512119/250000000000 : ℝ) (980210048473/1000000000000 : ℝ) (245052512119/250000000000 : ℝ) (980210048473/1000000000000 : ℝ) (245052512119/250000000000 : ℝ) (980210048473/1000000000000 : ℝ) (245052512119/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (9/32 : ℝ)) 5 (980210048473/1000000000000 : ℝ) (245052512119/250000000000 : ℝ) (980210048473/1000000000000 : ℝ) (245052512119/250000000000 : ℝ) (980210048473/1000000000000 : ℝ) (245052512119/250000000000 : ℝ) (980210048473/1000000000000 : ℝ) (245052512119/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (9/32 : ℝ)) 6 (980210048473/1000000000000 : ℝ) (245052512119/250000000000 : ℝ) (980210048473/1000000000000 : ℝ) (245052512119/250000000000 : ℝ) (980210048473/1000000000000 : ℝ) (245052512119/250000000000 : ℝ) (980210048473/1000000000000 : ℝ) (245052512119/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (9/32 : ℝ)) 7 (980210048473/1000000000000 : ℝ) (245052512119/250000000000 : ℝ) (980210048473/1000000000000 : ℝ) (245052512119/250000000000 : ℝ) (980210048473/1000000000000 : ℝ) (245052512119/250000000000 : ℝ) (980210048473/1000000000000 : ℝ) (245052512119/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (9/32 : ℝ))) (138936387563/500000000000 : ℝ) (27787277513/100000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (9/32 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (138936387563/500000000000 : ℝ) (27787277513/100000000000 : ℝ) (638936387563/1000000000000 : ℝ) (127787277513/200000000000 : ℝ) (131784097847/250000000000 : ℝ) (527136391393/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (9/32 : ℝ))) 1 (638936387563/1000000000000 : ℝ) (127787277513/200000000000 : ℝ) (131784097847/250000000000 : ℝ) (527136391393/1000000000000 : ℝ) (23321455579/40000000000 : ℝ) (583036389479/1000000000000 : ℝ) (72543803757/125000000000 : ℝ) (29017521503/50000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (9/32 : ℝ))) 2 (23321455579/40000000000 : ℝ) (583036389479/1000000000000 : ℝ) (72543803757/125000000000 : ℝ) (29017521503/50000000000 : ℝ) (116338681953/200000000000 : ℝ) (58169340977/100000000000 : ℝ) (290845929733/500000000000 : ℝ) (581691859471/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (9/32 : ℝ))) 3 (116338681953/200000000000 : ℝ) (58169340977/100000000000 : ℝ) (290845929733/500000000000 : ℝ) (581691859471/1000000000000 : ℝ) (116338526923/200000000000 : ℝ) (581692634621/1000000000000 : ℝ) (290846317307/500000000000 : ℝ) (29084631731/50000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (9/32 : ℝ))) 4 (116338526923/200000000000 : ℝ) (581692634621/1000000000000 : ℝ) (290846317307/500000000000 : ℝ) (29084631731/50000000000 : ℝ) (290846317307/500000000000 : ℝ) (581692634621/1000000000000 : ℝ) (290846317307/500000000000 : ℝ) (581692634621/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (9/32 : ℝ))) 5 (290846317307/500000000000 : ℝ) (581692634621/1000000000000 : ℝ) (290846317307/500000000000 : ℝ) (581692634621/1000000000000 : ℝ) (290846317307/500000000000 : ℝ) (581692634621/1000000000000 : ℝ) (290846317307/500000000000 : ℝ) (581692634621/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (9/32 : ℝ))) 6 (290846317307/500000000000 : ℝ) (581692634621/1000000000000 : ℝ) (290846317307/500000000000 : ℝ) (581692634621/1000000000000 : ℝ) (290846317307/500000000000 : ℝ) (581692634621/1000000000000 : ℝ) (290846317307/500000000000 : ℝ) (581692634621/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (9/32 : ℝ))) 7 (290846317307/500000000000 : ℝ) (581692634621/1000000000000 : ℝ) (290846317307/500000000000 : ℝ) (581692634621/1000000000000 : ℝ) (290846317307/500000000000 : ℝ) (581692634621/1000000000000 : ℝ) (290846317307/500000000000 : ℝ) (581692634621/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (9/32 : ℝ)) hmem 8 (980210048473/1000000000000 : ℝ) (245052512119/250000000000 : ℝ) (980210048473/1000000000000 : ℝ) (245052512119/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (9/32 : ℝ))) hcmem 8 (290846317307/500000000000 : ℝ) (581692634621/1000000000000 : ℝ) (290846317307/500000000000 : ℝ) (581692634621/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (9/32 : ℝ)) (980210048473/1000000000000 : ℝ) (245052512119/250000000000 : ℝ) (290846317307/500000000000 : ℝ) (581692634621/1000000000000 : ℝ) (466084108807/500000000000 : ℝ) (932168217629/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0638_exp_lower
  have heNumeric : (505519726457/250000000000 : ℝ)/4 ≤ Real.exp (-682168217629/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (505519726457/250000000000 : ℝ)/4 ≤ Real.exp ((1/4 : ℝ)-(932168217629/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (1/4 : ℝ) (9/32 : ℝ) (932168217629/1000000000000 : ℝ) (505519726457/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0639; no trusted numerical premise.
theorem cover7_leaf0639_exp_radius : (497217592064005723/500000000000000000 : ℝ) ≤ Real.exp ((-5/112 : ℝ)/8) ∧ Real.exp ((-5/112 : ℝ)/8) ≤ (994435184128011447/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5/112 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0639_exp_lower : (459839437111537103/500000000000000000 : ℝ) ≤ Real.exp ((-669845757029/1000000000000 : ℝ)/8) ∧ Real.exp ((-669845757029/1000000000000 : ℝ)/8) ≤ (919678874223074207/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-669845757029/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0639_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (20471500453/10000000000 : ℝ) ≤ 4*Real.exp (9/32 : ℝ)*Real.exp (-mu (radius 7 (5/16 : ℝ))) ∧ (2019/1000 : ℝ) < (20471500453/10000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (5/16 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0639_exp_radius
  have hrNumeric : (956338970481/1000000000000 : ℝ) ≤ Real.exp (-5/112 : ℝ) ∧ Real.exp (-5/112 : ℝ) ≤ (478169485241/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (956338970481/1000000000000 : ℝ) ≤ (radius 7 (5/16 : ℝ)) ∧ (radius 7 (5/16 : ℝ)) ≤ (478169485241/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (5/16 : ℝ)) (956338970481/1000000000000 : ℝ) (478169485241/500000000000 : ℝ) (73064942661/250000000000 : ℝ) (292259770649/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (5/16 : ℝ)) (956338970481/1000000000000 : ℝ) (478169485241/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (5/16 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (956338970481/1000000000000 : ℝ) (478169485241/500000000000 : ℝ) (24454237131/25000000000 : ℝ) (978169485241/1000000000000 : ℝ) (488962925609/500000000000 : ℝ) (977925851219/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (5/16 : ℝ)) 1 (24454237131/25000000000 : ℝ) (978169485241/1000000000000 : ℝ) (488962925609/500000000000 : ℝ) (977925851219/1000000000000 : ℝ) (978047668229/1000000000000 : ℝ) (97804766823/100000000000 : ℝ) (489023830321/500000000000 : ℝ) (244511915161/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (5/16 : ℝ)) 2 (978047668229/1000000000000 : ℝ) (97804766823/100000000000 : ℝ) (489023830321/500000000000 : ℝ) (244511915161/250000000000 : ℝ) (195609532887/200000000000 : ℝ) (978047664437/1000000000000 : ℝ) (195609532887/200000000000 : ℝ) (978047664437/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (5/16 : ℝ)) 3 (195609532887/200000000000 : ℝ) (978047664437/1000000000000 : ℝ) (195609532887/200000000000 : ℝ) (978047664437/1000000000000 : ℝ) (195609532887/200000000000 : ℝ) (978047664437/1000000000000 : ℝ) (195609532887/200000000000 : ℝ) (978047664437/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (5/16 : ℝ)) 4 (195609532887/200000000000 : ℝ) (978047664437/1000000000000 : ℝ) (195609532887/200000000000 : ℝ) (978047664437/1000000000000 : ℝ) (195609532887/200000000000 : ℝ) (978047664437/1000000000000 : ℝ) (195609532887/200000000000 : ℝ) (978047664437/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (5/16 : ℝ)) 5 (195609532887/200000000000 : ℝ) (978047664437/1000000000000 : ℝ) (195609532887/200000000000 : ℝ) (978047664437/1000000000000 : ℝ) (195609532887/200000000000 : ℝ) (978047664437/1000000000000 : ℝ) (195609532887/200000000000 : ℝ) (978047664437/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (5/16 : ℝ)) 6 (195609532887/200000000000 : ℝ) (978047664437/1000000000000 : ℝ) (195609532887/200000000000 : ℝ) (978047664437/1000000000000 : ℝ) (195609532887/200000000000 : ℝ) (978047664437/1000000000000 : ℝ) (195609532887/200000000000 : ℝ) (978047664437/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (5/16 : ℝ)) 7 (195609532887/200000000000 : ℝ) (978047664437/1000000000000 : ℝ) (195609532887/200000000000 : ℝ) (978047664437/1000000000000 : ℝ) (195609532887/200000000000 : ℝ) (978047664437/1000000000000 : ℝ) (195609532887/200000000000 : ℝ) (978047664437/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (5/16 : ℝ))) (73064942661/250000000000 : ℝ) (292259770649/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (5/16 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (73064942661/250000000000 : ℝ) (292259770649/1000000000000 : ℝ) (323064942661/500000000000 : ℝ) (25845195413/40000000000 : ℝ) (540610553581/1000000000000 : ℝ) (540610553587/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (5/16 : ℝ))) 1 (323064942661/500000000000 : ℝ) (25845195413/40000000000 : ℝ) (540610553581/1000000000000 : ℝ) (540610553587/1000000000000 : ℝ) (593370219451/1000000000000 : ℝ) (9271409679/15625000000 : ℝ) (295509997711/500000000000 : ℝ) (147754998857/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (5/16 : ℝ))) 2 (593370219451/1000000000000 : ℝ) (9271409679/15625000000 : ℝ) (295509997711/500000000000 : ℝ) (147754998857/250000000000 : ℝ) (148048776859/250000000000 : ℝ) (296097553721/500000000000 : ℝ) (74024242691/125000000000 : ℝ) (118438788307/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (5/16 : ℝ))) 3 (148048776859/250000000000 : ℝ) (296097553721/500000000000 : ℝ) (74024242691/125000000000 : ℝ) (118438788307/200000000000 : ℝ) (296097262241/500000000000 : ℝ) (592194524489/1000000000000 : ℝ) (592194524481/1000000000000 : ℝ) (592194524489/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (5/16 : ℝ))) 4 (296097262241/500000000000 : ℝ) (592194524489/1000000000000 : ℝ) (592194524481/1000000000000 : ℝ) (592194524489/1000000000000 : ℝ) (592194524481/1000000000000 : ℝ) (592194524489/1000000000000 : ℝ) (592194524481/1000000000000 : ℝ) (592194524489/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (5/16 : ℝ))) 5 (592194524481/1000000000000 : ℝ) (592194524489/1000000000000 : ℝ) (592194524481/1000000000000 : ℝ) (592194524489/1000000000000 : ℝ) (592194524481/1000000000000 : ℝ) (592194524489/1000000000000 : ℝ) (592194524481/1000000000000 : ℝ) (592194524489/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (5/16 : ℝ))) 6 (592194524481/1000000000000 : ℝ) (592194524489/1000000000000 : ℝ) (592194524481/1000000000000 : ℝ) (592194524489/1000000000000 : ℝ) (592194524481/1000000000000 : ℝ) (592194524489/1000000000000 : ℝ) (592194524481/1000000000000 : ℝ) (592194524489/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (5/16 : ℝ))) 7 (592194524481/1000000000000 : ℝ) (592194524489/1000000000000 : ℝ) (592194524481/1000000000000 : ℝ) (592194524489/1000000000000 : ℝ) (592194524481/1000000000000 : ℝ) (592194524489/1000000000000 : ℝ) (592194524481/1000000000000 : ℝ) (592194524489/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (5/16 : ℝ)) hmem 8 (195609532887/200000000000 : ℝ) (978047664437/1000000000000 : ℝ) (195609532887/200000000000 : ℝ) (978047664437/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (5/16 : ℝ))) hcmem 8 (592194524481/1000000000000 : ℝ) (592194524489/1000000000000 : ℝ) (592194524481/1000000000000 : ℝ) (592194524489/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (5/16 : ℝ)) (195609532887/200000000000 : ℝ) (978047664437/1000000000000 : ℝ) (592194524481/1000000000000 : ℝ) (592194524489/1000000000000 : ℝ) (951095757013/1000000000000 : ℝ) (951095757029/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0639_exp_lower
  have heNumeric : (20471500453/10000000000 : ℝ)/4 ≤ Real.exp (-669845757029/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (20471500453/10000000000 : ℝ)/4 ≤ Real.exp ((9/32 : ℝ)-(951095757029/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (9/32 : ℝ) (5/16 : ℝ) (951095757029/1000000000000 : ℝ) (20471500453/10000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0640; no trusted numerical premise.
theorem cover7_leaf0640_exp_radius : (62082871408937557/62500000000000000 : ℝ) ≤ Real.exp ((-3/56 : ℝ)/8) ∧ Real.exp ((-3/56 : ℝ)/8) ≤ (993325942543000913/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-3/56 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0640_exp_lower : (459644946132046849/500000000000000000 : ℝ) ≤ Real.exp ((-134646021133/200000000000 : ℝ)/8) ∧ Real.exp ((-134646021133/200000000000 : ℝ)/8) ≤ (919289892264093699/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-134646021133/200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0640_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1020116743231/500000000000 : ℝ) ≤ 4*Real.exp (5/16 : ℝ)*Real.exp (-mu (radius 7 (3/8 : ℝ))) ∧ (2019/1000 : ℝ) < (1020116743231/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (3/8 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0640_exp_radius
  have hrNumeric : (473919117927/500000000000 : ℝ) ≤ Real.exp (-3/56 : ℝ) ∧ Real.exp (-3/56 : ℝ) ≤ (189567647171/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (473919117927/500000000000 : ℝ) ≤ (radius 7 (3/8 : ℝ)) ∧ (radius 7 (3/8 : ℝ)) ≤ (189567647171/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (3/8 : ℝ)) (473919117927/500000000000 : ℝ) (189567647171/200000000000 : ℝ) (15937587541/50000000000 : ℝ) (39843968853/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (3/8 : ℝ)) (473919117927/500000000000 : ℝ) (189567647171/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (3/8 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (473919117927/500000000000 : ℝ) (189567647171/200000000000 : ℝ) (973919117927/1000000000000 : ℝ) (121739889741/125000000000 : ℝ) (486784920641/500000000000 : ℝ) (973569841283/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (3/8 : ℝ)) 1 (973919117927/1000000000000 : ℝ) (121739889741/125000000000 : ℝ) (486784920641/500000000000 : ℝ) (973569841283/1000000000000 : ℝ) (243436119901/250000000000 : ℝ) (486872239803/500000000000 : ℝ) (121718057993/125000000000 : ℝ) (486872231973/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (3/8 : ℝ)) 2 (243436119901/250000000000 : ℝ) (486872239803/500000000000 : ℝ) (121718057993/125000000000 : ℝ) (486872231973/500000000000 : ℝ) (486872235887/500000000000 : ℝ) (30429514743/31250000000 : ℝ) (973744471773/1000000000000 : ℝ) (30429514743/31250000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (3/8 : ℝ)) 3 (486872235887/500000000000 : ℝ) (30429514743/31250000000 : ℝ) (973744471773/1000000000000 : ℝ) (30429514743/31250000000 : ℝ) (973744471773/1000000000000 : ℝ) (30429514743/31250000000 : ℝ) (973744471773/1000000000000 : ℝ) (30429514743/31250000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (3/8 : ℝ)) 4 (973744471773/1000000000000 : ℝ) (30429514743/31250000000 : ℝ) (973744471773/1000000000000 : ℝ) (30429514743/31250000000 : ℝ) (973744471773/1000000000000 : ℝ) (30429514743/31250000000 : ℝ) (973744471773/1000000000000 : ℝ) (30429514743/31250000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (3/8 : ℝ)) 5 (973744471773/1000000000000 : ℝ) (30429514743/31250000000 : ℝ) (973744471773/1000000000000 : ℝ) (30429514743/31250000000 : ℝ) (973744471773/1000000000000 : ℝ) (30429514743/31250000000 : ℝ) (973744471773/1000000000000 : ℝ) (30429514743/31250000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (3/8 : ℝ)) 6 (973744471773/1000000000000 : ℝ) (30429514743/31250000000 : ℝ) (973744471773/1000000000000 : ℝ) (30429514743/31250000000 : ℝ) (973744471773/1000000000000 : ℝ) (30429514743/31250000000 : ℝ) (973744471773/1000000000000 : ℝ) (30429514743/31250000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (3/8 : ℝ)) 7 (973744471773/1000000000000 : ℝ) (30429514743/31250000000 : ℝ) (973744471773/1000000000000 : ℝ) (30429514743/31250000000 : ℝ) (973744471773/1000000000000 : ℝ) (30429514743/31250000000 : ℝ) (973744471773/1000000000000 : ℝ) (30429514743/31250000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (3/8 : ℝ))) (15937587541/50000000000 : ℝ) (39843968853/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (3/8 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (15937587541/50000000000 : ℝ) (39843968853/125000000000 : ℝ) (65937587541/100000000000 : ℝ) (164843968853/250000000000 : ℝ) (564581040081/1000000000000 : ℝ) (282290520043/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (3/8 : ℝ))) 1 (65937587541/100000000000 : ℝ) (164843968853/250000000000 : ℝ) (564581040081/1000000000000 : ℝ) (282290520043/500000000000 : ℝ) (122395691549/200000000000 : ℝ) (611978457749/1000000000000 : ℝ) (610140244159/1000000000000 : ℝ) (152535061041/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (3/8 : ℝ))) 2 (122395691549/200000000000 : ℝ) (611978457749/1000000000000 : ℝ) (610140244159/1000000000000 : ℝ) (152535061041/250000000000 : ℝ) (76382418869/125000000000 : ℝ) (611059350957/1000000000000 : ℝ) (38191166233/62500000000 : ℝ) (611058659733/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (3/8 : ℝ))) 3 (76382418869/125000000000 : ℝ) (611059350957/1000000000000 : ℝ) (38191166233/62500000000 : ℝ) (611058659733/1000000000000 : ℝ) (30552950267/50000000000 : ℝ) (122211801069/200000000000 : ℝ) (611059005339/1000000000000 : ℝ) (122211801069/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (3/8 : ℝ))) 4 (30552950267/50000000000 : ℝ) (122211801069/200000000000 : ℝ) (611059005339/1000000000000 : ℝ) (122211801069/200000000000 : ℝ) (611059005339/1000000000000 : ℝ) (122211801069/200000000000 : ℝ) (611059005339/1000000000000 : ℝ) (122211801069/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (3/8 : ℝ))) 5 (611059005339/1000000000000 : ℝ) (122211801069/200000000000 : ℝ) (611059005339/1000000000000 : ℝ) (122211801069/200000000000 : ℝ) (611059005339/1000000000000 : ℝ) (122211801069/200000000000 : ℝ) (611059005339/1000000000000 : ℝ) (122211801069/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (3/8 : ℝ))) 6 (611059005339/1000000000000 : ℝ) (122211801069/200000000000 : ℝ) (611059005339/1000000000000 : ℝ) (122211801069/200000000000 : ℝ) (611059005339/1000000000000 : ℝ) (122211801069/200000000000 : ℝ) (611059005339/1000000000000 : ℝ) (122211801069/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (3/8 : ℝ))) 7 (611059005339/1000000000000 : ℝ) (122211801069/200000000000 : ℝ) (611059005339/1000000000000 : ℝ) (122211801069/200000000000 : ℝ) (611059005339/1000000000000 : ℝ) (122211801069/200000000000 : ℝ) (611059005339/1000000000000 : ℝ) (122211801069/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (3/8 : ℝ)) hmem 8 (973744471773/1000000000000 : ℝ) (30429514743/31250000000 : ℝ) (973744471773/1000000000000 : ℝ) (30429514743/31250000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (3/8 : ℝ))) hcmem 8 (611059005339/1000000000000 : ℝ) (122211801069/200000000000 : ℝ) (611059005339/1000000000000 : ℝ) (122211801069/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (3/8 : ℝ)) (973744471773/1000000000000 : ℝ) (30429514743/31250000000 : ℝ) (611059005339/1000000000000 : ℝ) (122211801069/200000000000 : ℝ) (985730105651/1000000000000 : ℝ) (197146021133/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0640_exp_lower
  have heNumeric : (1020116743231/500000000000 : ℝ)/4 ≤ Real.exp (-134646021133/200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1020116743231/500000000000 : ℝ)/4 ≤ Real.exp ((5/16 : ℝ)-(197146021133/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (5/16 : ℝ) (3/8 : ℝ) (197146021133/200000000000 : ℝ) (1020116743231/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0641; no trusted numerical premise.
theorem cover7_leaf0641_exp_radius : (495555584949795933/500000000000000000 : ℝ) ≤ Real.exp ((-1/14 : ℝ)/8) ∧ Real.exp ((-1/14 : ℝ)/8) ≤ (991111169899591867/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1/14 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0641_exp_lower : (459783555965466083/500000000000000000 : ℝ) ≤ Real.exp ((-134163600293/200000000000 : ℝ)/8) ∧ Real.exp ((-134163600293/200000000000 : ℝ)/8) ≤ (919567111930932167/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-134163600293/200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0641_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2045160682289/1000000000000 : ℝ) ≤ 4*Real.exp (3/8 : ℝ)*Real.exp (-mu (radius 7 (1/2 : ℝ))) ∧ (2019/1000 : ℝ) < (2045160682289/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (1/2 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0641_exp_radius
  have hrNumeric : (116382847463/125000000000 : ℝ) ≤ Real.exp (-1/14 : ℝ) ∧ Real.exp (-1/14 : ℝ) ≤ (186212555941/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (116382847463/125000000000 : ℝ) ≤ (radius 7 (1/2 : ℝ)) ∧ (radius 7 (1/2 : ℝ)) ≤ (186212555941/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (1/2 : ℝ)) (116382847463/125000000000 : ℝ) (186212555941/200000000000 : ℝ) (182429507103/500000000000 : ℝ) (36485901421/100000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (1/2 : ℝ)) (116382847463/125000000000 : ℝ) (186212555941/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (1/2 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (116382847463/125000000000 : ℝ) (186212555941/200000000000 : ℝ) (241382847463/250000000000 : ℝ) (965531389853/1000000000000 : ℝ) (241228986093/250000000000 : ℝ) (964915944373/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (1/2 : ℝ)) 1 (241382847463/250000000000 : ℝ) (965531389853/1000000000000 : ℝ) (241228986093/250000000000 : ℝ) (964915944373/1000000000000 : ℝ) (120652958389/125000000000 : ℝ) (965223667113/1000000000000 : ℝ) (965223618059/1000000000000 : ℝ) (965223618061/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (1/2 : ℝ)) 2 (120652958389/125000000000 : ℝ) (965223667113/1000000000000 : ℝ) (965223618059/1000000000000 : ℝ) (965223618061/1000000000000 : ℝ) (193044728517/200000000000 : ℝ) (965223642587/1000000000000 : ℝ) (193044728517/200000000000 : ℝ) (965223642587/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (1/2 : ℝ)) 3 (193044728517/200000000000 : ℝ) (965223642587/1000000000000 : ℝ) (193044728517/200000000000 : ℝ) (965223642587/1000000000000 : ℝ) (193044728517/200000000000 : ℝ) (965223642587/1000000000000 : ℝ) (193044728517/200000000000 : ℝ) (965223642587/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (1/2 : ℝ)) 4 (193044728517/200000000000 : ℝ) (965223642587/1000000000000 : ℝ) (193044728517/200000000000 : ℝ) (965223642587/1000000000000 : ℝ) (193044728517/200000000000 : ℝ) (965223642587/1000000000000 : ℝ) (193044728517/200000000000 : ℝ) (965223642587/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (1/2 : ℝ)) 5 (193044728517/200000000000 : ℝ) (965223642587/1000000000000 : ℝ) (193044728517/200000000000 : ℝ) (965223642587/1000000000000 : ℝ) (193044728517/200000000000 : ℝ) (965223642587/1000000000000 : ℝ) (193044728517/200000000000 : ℝ) (965223642587/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (1/2 : ℝ)) 6 (193044728517/200000000000 : ℝ) (965223642587/1000000000000 : ℝ) (193044728517/200000000000 : ℝ) (965223642587/1000000000000 : ℝ) (193044728517/200000000000 : ℝ) (965223642587/1000000000000 : ℝ) (193044728517/200000000000 : ℝ) (965223642587/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (1/2 : ℝ)) 7 (193044728517/200000000000 : ℝ) (965223642587/1000000000000 : ℝ) (193044728517/200000000000 : ℝ) (965223642587/1000000000000 : ℝ) (193044728517/200000000000 : ℝ) (965223642587/1000000000000 : ℝ) (193044728517/200000000000 : ℝ) (965223642587/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (1/2 : ℝ))) (182429507103/500000000000 : ℝ) (36485901421/100000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (1/2 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (182429507103/500000000000 : ℝ) (36485901421/100000000000 : ℝ) (682429507103/1000000000000 : ℝ) (136485901421/200000000000 : ℝ) (37752225421/62500000000 : ℝ) (604035606741/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (1/2 : ℝ))) 1 (682429507103/1000000000000 : ℝ) (136485901421/200000000000 : ℝ) (37752225421/62500000000 : ℝ) (604035606741/1000000000000 : ℝ) (643232556919/1000000000000 : ℝ) (643232556923/1000000000000 : ℝ) (321018582553/500000000000 : ℝ) (64203716511/100000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (1/2 : ℝ))) 2 (643232556919/1000000000000 : ℝ) (643232556923/1000000000000 : ℝ) (321018582553/500000000000 : ℝ) (64203716511/100000000000 : ℝ) (160658715253/250000000000 : ℝ) (642634861017/1000000000000 : ℝ) (321317291531/500000000000 : ℝ) (642634583067/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (1/2 : ℝ))) 3 (160658715253/250000000000 : ℝ) (642634861017/1000000000000 : ℝ) (321317291531/500000000000 : ℝ) (642634583067/1000000000000 : ℝ) (642634722037/1000000000000 : ℝ) (321317361021/500000000000 : ℝ) (160658680509/250000000000 : ℝ) (321317361021/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (1/2 : ℝ))) 4 (642634722037/1000000000000 : ℝ) (321317361021/500000000000 : ℝ) (160658680509/250000000000 : ℝ) (321317361021/500000000000 : ℝ) (160658680509/250000000000 : ℝ) (321317361021/500000000000 : ℝ) (160658680509/250000000000 : ℝ) (321317361021/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (1/2 : ℝ))) 5 (160658680509/250000000000 : ℝ) (321317361021/500000000000 : ℝ) (160658680509/250000000000 : ℝ) (321317361021/500000000000 : ℝ) (160658680509/250000000000 : ℝ) (321317361021/500000000000 : ℝ) (160658680509/250000000000 : ℝ) (321317361021/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (1/2 : ℝ))) 6 (160658680509/250000000000 : ℝ) (321317361021/500000000000 : ℝ) (160658680509/250000000000 : ℝ) (321317361021/500000000000 : ℝ) (160658680509/250000000000 : ℝ) (321317361021/500000000000 : ℝ) (160658680509/250000000000 : ℝ) (321317361021/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (1/2 : ℝ))) 7 (160658680509/250000000000 : ℝ) (321317361021/500000000000 : ℝ) (160658680509/250000000000 : ℝ) (321317361021/500000000000 : ℝ) (160658680509/250000000000 : ℝ) (321317361021/500000000000 : ℝ) (160658680509/250000000000 : ℝ) (321317361021/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (1/2 : ℝ)) hmem 8 (193044728517/200000000000 : ℝ) (965223642587/1000000000000 : ℝ) (193044728517/200000000000 : ℝ) (965223642587/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (1/2 : ℝ))) hcmem 8 (160658680509/250000000000 : ℝ) (321317361021/500000000000 : ℝ) (160658680509/250000000000 : ℝ) (321317361021/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (1/2 : ℝ)) (193044728517/200000000000 : ℝ) (965223642587/1000000000000 : ℝ) (160658680509/250000000000 : ℝ) (321317361021/500000000000 : ℝ) (261454500363/250000000000 : ℝ) (209163600293/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0641_exp_lower
  have heNumeric : (2045160682289/1000000000000 : ℝ)/4 ≤ Real.exp (-134163600293/200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2045160682289/1000000000000 : ℝ)/4 ≤ Real.exp ((3/8 : ℝ)-(209163600293/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (3/8 : ℝ) (1/2 : ℝ) (209163600293/200000000000 : ℝ) (2045160682289/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0642; no trusted numerical premise.
theorem cover7_leaf0642_exp_radius : (19733928562578823/20000000000000000 : ℝ) ≤ Real.exp ((-3/28 : ℝ)/8) ∧ Real.exp ((-3/28 : ℝ)/8) ≤ (986696428128941151/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-3/28 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0642_exp_lower : (184528744840808957/200000000000000000 : ℝ) ≤ Real.exp ((-644096932861/1000000000000 : ℝ)/8) ∧ Real.exp ((-644096932861/1000000000000 : ℝ)/8) ≤ (461321862102022393/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-644096932861/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0642_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2100546246443/1000000000000 : ℝ) ≤ 4*Real.exp (1/2 : ℝ)*Real.exp (-mu (radius 7 (3/4 : ℝ))) ∧ (2019/1000 : ℝ) < (2100546246443/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (3/4 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0642_exp_radius
  have hrNumeric : (224599330337/250000000000 : ℝ) ≤ Real.exp (-3/28 : ℝ) ∧ Real.exp (-3/28 : ℝ) ≤ (898397321349/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (224599330337/250000000000 : ℝ) ≤ (radius 7 (3/4 : ℝ)) ∧ (radius 7 (3/4 : ℝ)) ≤ (898397321349/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (3/4 : ℝ)) (224599330337/250000000000 : ℝ) (898397321349/1000000000000 : ℝ) (439183621043/1000000000000 : ℝ) (219591810523/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (3/4 : ℝ)) (224599330337/250000000000 : ℝ) (898397321349/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (3/4 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (224599330337/250000000000 : ℝ) (898397321349/1000000000000 : ℝ) (474599330337/500000000000 : ℝ) (37967946427/40000000000 : ℝ) (473919117927/500000000000 : ℝ) (59239889741/62500000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (3/4 : ℝ)) 1 (474599330337/500000000000 : ℝ) (37967946427/40000000000 : ℝ) (473919117927/500000000000 : ℝ) (59239889741/62500000000 : ℝ) (118564806033/125000000000 : ℝ) (474259224133/500000000000 : ℝ) (948518204363/1000000000000 : ℝ) (189703640873/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (3/4 : ℝ)) 2 (118564806033/125000000000 : ℝ) (474259224133/500000000000 : ℝ) (948518204363/1000000000000 : ℝ) (189703640873/200000000000 : ℝ) (948518326313/1000000000000 : ℝ) (237129581579/250000000000 : ℝ) (948518326313/1000000000000 : ℝ) (237129581579/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (3/4 : ℝ)) 3 (948518326313/1000000000000 : ℝ) (237129581579/250000000000 : ℝ) (948518326313/1000000000000 : ℝ) (237129581579/250000000000 : ℝ) (948518326313/1000000000000 : ℝ) (237129581579/250000000000 : ℝ) (948518326313/1000000000000 : ℝ) (237129581579/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (3/4 : ℝ)) 4 (948518326313/1000000000000 : ℝ) (237129581579/250000000000 : ℝ) (948518326313/1000000000000 : ℝ) (237129581579/250000000000 : ℝ) (948518326313/1000000000000 : ℝ) (237129581579/250000000000 : ℝ) (948518326313/1000000000000 : ℝ) (237129581579/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (3/4 : ℝ)) 5 (948518326313/1000000000000 : ℝ) (237129581579/250000000000 : ℝ) (948518326313/1000000000000 : ℝ) (237129581579/250000000000 : ℝ) (948518326313/1000000000000 : ℝ) (237129581579/250000000000 : ℝ) (948518326313/1000000000000 : ℝ) (237129581579/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (3/4 : ℝ)) 6 (948518326313/1000000000000 : ℝ) (237129581579/250000000000 : ℝ) (948518326313/1000000000000 : ℝ) (237129581579/250000000000 : ℝ) (948518326313/1000000000000 : ℝ) (237129581579/250000000000 : ℝ) (948518326313/1000000000000 : ℝ) (237129581579/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (3/4 : ℝ)) 7 (948518326313/1000000000000 : ℝ) (237129581579/250000000000 : ℝ) (948518326313/1000000000000 : ℝ) (237129581579/250000000000 : ℝ) (948518326313/1000000000000 : ℝ) (237129581579/250000000000 : ℝ) (948518326313/1000000000000 : ℝ) (237129581579/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (3/4 : ℝ))) (439183621043/1000000000000 : ℝ) (219591810523/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (3/4 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (439183621043/1000000000000 : ℝ) (219591810523/500000000000 : ℝ) (719591810521/1000000000000 : ℝ) (719591810523/1000000000000 : ℝ) (662709303573/1000000000000 : ℝ) (82838662947/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (3/4 : ℝ))) 1 (719591810521/1000000000000 : ℝ) (719591810523/1000000000000 : ℝ) (662709303573/1000000000000 : ℝ) (82838662947/125000000000 : ℝ) (691150557047/1000000000000 : ℝ) (13823011141/20000000000 : ℝ) (172641280479/250000000000 : ℝ) (690565121919/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (3/4 : ℝ))) 2 (691150557047/1000000000000 : ℝ) (13823011141/20000000000 : ℝ) (172641280479/250000000000 : ℝ) (690565121919/1000000000000 : ℝ) (690857839481/1000000000000 : ℝ) (138171567897/200000000000 : ℝ) (690857777469/1000000000000 : ℝ) (690857777473/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (3/4 : ℝ))) 3 (690857839481/1000000000000 : ℝ) (138171567897/200000000000 : ℝ) (690857777469/1000000000000 : ℝ) (690857777473/1000000000000 : ℝ) (27634312339/40000000000 : ℝ) (690857808479/1000000000000 : ℝ) (345428904237/500000000000 : ℝ) (690857808479/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (3/4 : ℝ))) 4 (27634312339/40000000000 : ℝ) (690857808479/1000000000000 : ℝ) (345428904237/500000000000 : ℝ) (690857808479/1000000000000 : ℝ) (345428904237/500000000000 : ℝ) (690857808479/1000000000000 : ℝ) (345428904237/500000000000 : ℝ) (690857808479/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (3/4 : ℝ))) 5 (345428904237/500000000000 : ℝ) (690857808479/1000000000000 : ℝ) (345428904237/500000000000 : ℝ) (690857808479/1000000000000 : ℝ) (345428904237/500000000000 : ℝ) (690857808479/1000000000000 : ℝ) (345428904237/500000000000 : ℝ) (690857808479/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (3/4 : ℝ))) 6 (345428904237/500000000000 : ℝ) (690857808479/1000000000000 : ℝ) (345428904237/500000000000 : ℝ) (690857808479/1000000000000 : ℝ) (345428904237/500000000000 : ℝ) (690857808479/1000000000000 : ℝ) (345428904237/500000000000 : ℝ) (690857808479/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (3/4 : ℝ))) 7 (345428904237/500000000000 : ℝ) (690857808479/1000000000000 : ℝ) (345428904237/500000000000 : ℝ) (690857808479/1000000000000 : ℝ) (345428904237/500000000000 : ℝ) (690857808479/1000000000000 : ℝ) (345428904237/500000000000 : ℝ) (690857808479/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (3/4 : ℝ)) hmem 8 (948518326313/1000000000000 : ℝ) (237129581579/250000000000 : ℝ) (948518326313/1000000000000 : ℝ) (237129581579/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (3/4 : ℝ))) hcmem 8 (345428904237/500000000000 : ℝ) (690857808479/1000000000000 : ℝ) (345428904237/500000000000 : ℝ) (690857808479/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (3/4 : ℝ)) (948518326313/1000000000000 : ℝ) (237129581579/250000000000 : ℝ) (345428904237/500000000000 : ℝ) (690857808479/1000000000000 : ℝ) (71506058303/62500000000 : ℝ) (1144096932861/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0642_exp_lower
  have heNumeric : (2100546246443/1000000000000 : ℝ)/4 ≤ Real.exp (-644096932861/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2100546246443/1000000000000 : ℝ)/4 ≤ Real.exp ((1/2 : ℝ)-(1144096932861/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (1/2 : ℝ) (3/4 : ℝ) (1144096932861/1000000000000 : ℝ) (2100546246443/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0643; no trusted numerical premise.
theorem cover7_leaf0643_exp_radius : (491150675549868827/500000000000000000 : ℝ) ≤ Real.exp ((-1/7 : ℝ)/8) ∧ Real.exp ((-1/7 : ℝ)/8) ≤ (196460270219947531/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1/7 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0643_exp_lower : (942258933877385193/1000000000000000000 : ℝ) ≤ Real.exp ((-475801323599/1000000000000 : ℝ)/8) ∧ Real.exp ((-475801323599/1000000000000 : ℝ)/8) ≤ (471129466938692597/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-475801323599/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0643_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2485547699609/1000000000000 : ℝ) ≤ 4*Real.exp (3/4 : ℝ)*Real.exp (-mu (radius 7 (1/1 : ℝ))) ∧ (2019/1000 : ℝ) < (2485547699609/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (1/1 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0643_exp_radius
  have hrNumeric : (3467511599/4000000000 : ℝ) ≤ Real.exp (-1/7 : ℝ) ∧ Real.exp (-1/7 : ℝ) ≤ (866877899751/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (3467511599/4000000000 : ℝ) ≤ (radius 7 (1/1 : ℝ)) ∧ (radius 7 (1/1 : ℝ)) ≤ (866877899751/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (1/1 : ℝ)) (3467511599/4000000000 : ℝ) (866877899751/1000000000000 : ℝ) (62315064757/125000000000 : ℝ) (498520518059/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (1/1 : ℝ)) (3467511599/4000000000 : ℝ) (866877899751/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (1/1 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (3467511599/4000000000 : ℝ) (866877899751/1000000000000 : ℝ) (7467511599/8000000000 : ℝ) (233359737469/250000000000 : ℝ) (931062779703/1000000000000 : ℝ) (186212555941/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (1/1 : ℝ)) 1 (7467511599/8000000000 : ℝ) (233359737469/250000000000 : ℝ) (931062779703/1000000000000 : ℝ) (186212555941/200000000000 : ℝ) (932250864789/1000000000000 : ℝ) (932250864791/1000000000000 : ℝ) (37290004309/40000000000 : ℝ) (932250107727/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (1/1 : ℝ)) 2 (932250864789/1000000000000 : ℝ) (932250864791/1000000000000 : ℝ) (37290004309/40000000000 : ℝ) (932250107727/1000000000000 : ℝ) (932250486257/1000000000000 : ℝ) (932250486259/1000000000000 : ℝ) (58265655391/62500000000 : ℝ) (932250486259/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (1/1 : ℝ)) 3 (932250486257/1000000000000 : ℝ) (932250486259/1000000000000 : ℝ) (58265655391/62500000000 : ℝ) (932250486259/1000000000000 : ℝ) (58265655391/62500000000 : ℝ) (932250486259/1000000000000 : ℝ) (58265655391/62500000000 : ℝ) (932250486259/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (1/1 : ℝ)) 4 (58265655391/62500000000 : ℝ) (932250486259/1000000000000 : ℝ) (58265655391/62500000000 : ℝ) (932250486259/1000000000000 : ℝ) (58265655391/62500000000 : ℝ) (932250486259/1000000000000 : ℝ) (58265655391/62500000000 : ℝ) (932250486259/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (1/1 : ℝ)) 5 (58265655391/62500000000 : ℝ) (932250486259/1000000000000 : ℝ) (58265655391/62500000000 : ℝ) (932250486259/1000000000000 : ℝ) (58265655391/62500000000 : ℝ) (932250486259/1000000000000 : ℝ) (58265655391/62500000000 : ℝ) (932250486259/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (1/1 : ℝ)) 6 (58265655391/62500000000 : ℝ) (932250486259/1000000000000 : ℝ) (58265655391/62500000000 : ℝ) (932250486259/1000000000000 : ℝ) (58265655391/62500000000 : ℝ) (932250486259/1000000000000 : ℝ) (58265655391/62500000000 : ℝ) (932250486259/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (1/1 : ℝ)) 7 (58265655391/62500000000 : ℝ) (932250486259/1000000000000 : ℝ) (58265655391/62500000000 : ℝ) (932250486259/1000000000000 : ℝ) (58265655391/62500000000 : ℝ) (932250486259/1000000000000 : ℝ) (58265655391/62500000000 : ℝ) (932250486259/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (1/1 : ℝ))) (62315064757/125000000000 : ℝ) (498520518059/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (1/1 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (62315064757/125000000000 : ℝ) (498520518059/1000000000000 : ℝ) (187315064757/250000000000 : ℝ) (74926025903/100000000000 : ℝ) (353029927221/500000000000 : ℝ) (353029927223/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (1/1 : ℝ))) 1 (187315064757/250000000000 : ℝ) (74926025903/100000000000 : ℝ) (353029927221/500000000000 : ℝ) (353029927223/500000000000 : ℝ) (145532011347/200000000000 : ℝ) (363830028369/500000000000 : ℝ) (727339390813/1000000000000 : ℝ) (727339390817/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (1/1 : ℝ))) 2 (145532011347/200000000000 : ℝ) (363830028369/500000000000 : ℝ) (727339390813/1000000000000 : ℝ) (727339390817/1000000000000 : ℝ) (363749861887/500000000000 : ℝ) (363749861889/500000000000 : ℝ) (363749853053/500000000000 : ℝ) (72749970611/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (1/1 : ℝ))) 3 (363749861887/500000000000 : ℝ) (363749861889/500000000000 : ℝ) (363749853053/500000000000 : ℝ) (72749970611/100000000000 : ℝ) (36374985747/50000000000 : ℝ) (5683591523/7812500000 : ℝ) (727499714939/1000000000000 : ℝ) (5683591523/7812500000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (1/1 : ℝ))) 4 (36374985747/50000000000 : ℝ) (5683591523/7812500000 : ℝ) (727499714939/1000000000000 : ℝ) (5683591523/7812500000 : ℝ) (727499714939/1000000000000 : ℝ) (5683591523/7812500000 : ℝ) (727499714939/1000000000000 : ℝ) (5683591523/7812500000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (1/1 : ℝ))) 5 (727499714939/1000000000000 : ℝ) (5683591523/7812500000 : ℝ) (727499714939/1000000000000 : ℝ) (5683591523/7812500000 : ℝ) (727499714939/1000000000000 : ℝ) (5683591523/7812500000 : ℝ) (727499714939/1000000000000 : ℝ) (5683591523/7812500000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (1/1 : ℝ))) 6 (727499714939/1000000000000 : ℝ) (5683591523/7812500000 : ℝ) (727499714939/1000000000000 : ℝ) (5683591523/7812500000 : ℝ) (727499714939/1000000000000 : ℝ) (5683591523/7812500000 : ℝ) (727499714939/1000000000000 : ℝ) (5683591523/7812500000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (1/1 : ℝ))) 7 (727499714939/1000000000000 : ℝ) (5683591523/7812500000 : ℝ) (727499714939/1000000000000 : ℝ) (5683591523/7812500000 : ℝ) (727499714939/1000000000000 : ℝ) (5683591523/7812500000 : ℝ) (727499714939/1000000000000 : ℝ) (5683591523/7812500000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (1/1 : ℝ)) hmem 8 (58265655391/62500000000 : ℝ) (932250486259/1000000000000 : ℝ) (58265655391/62500000000 : ℝ) (932250486259/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (1/1 : ℝ))) hcmem 8 (727499714939/1000000000000 : ℝ) (5683591523/7812500000 : ℝ) (727499714939/1000000000000 : ℝ) (5683591523/7812500000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (1/1 : ℝ)) (58265655391/62500000000 : ℝ) (932250486259/1000000000000 : ℝ) (727499714939/1000000000000 : ℝ) (5683591523/7812500000 : ℝ) (612900661793/500000000000 : ℝ) (1225801323599/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0643_exp_lower
  have heNumeric : (2485547699609/1000000000000 : ℝ)/4 ≤ Real.exp (-475801323599/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2485547699609/1000000000000 : ℝ)/4 ≤ Real.exp ((3/4 : ℝ)-(1225801323599/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (3/4 : ℝ) (1/1 : ℝ) (1225801323599/1000000000000 : ℝ) (2485547699609/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover7_leaf0625_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0625_certificate
#check SmaleRate.Proofs.cover7_leaf0626_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0626_certificate
#check SmaleRate.Proofs.cover7_leaf0627_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0627_certificate
#check SmaleRate.Proofs.cover7_leaf0628_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0628_certificate
#check SmaleRate.Proofs.cover7_leaf0629_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0629_certificate
#check SmaleRate.Proofs.cover7_leaf0630_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0630_certificate
#check SmaleRate.Proofs.cover7_leaf0631_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0631_certificate
#check SmaleRate.Proofs.cover7_leaf0632_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0632_certificate
#check SmaleRate.Proofs.cover7_leaf0633_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0633_certificate
#check SmaleRate.Proofs.cover7_leaf0634_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0634_certificate
#check SmaleRate.Proofs.cover7_leaf0635_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0635_certificate
#check SmaleRate.Proofs.cover7_leaf0636_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0636_certificate
#check SmaleRate.Proofs.cover7_leaf0637_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0637_certificate
#check SmaleRate.Proofs.cover7_leaf0638_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0638_certificate
#check SmaleRate.Proofs.cover7_leaf0639_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0639_certificate
#check SmaleRate.Proofs.cover7_leaf0640_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0640_certificate
#check SmaleRate.Proofs.cover7_leaf0641_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0641_certificate
#check SmaleRate.Proofs.cover7_leaf0642_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0642_certificate
#check SmaleRate.Proofs.cover7_leaf0643_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0643_certificate
