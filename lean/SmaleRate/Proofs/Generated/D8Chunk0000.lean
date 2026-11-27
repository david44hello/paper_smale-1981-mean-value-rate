/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.AGMCertificates

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

-- Proposed record cover8_leaf0000; no trusted numerical premise.
theorem cover8_leaf0000_exp_radius : (199902367587977873/200000000000000000 : ℝ) ≤ Real.exp ((-1/256 : ℝ)/8) ∧ Real.exp ((-1/256 : ℝ)/8) ≤ (499755918969944683/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1/256 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0000_exp_lower : (184456733752527883/200000000000000000 : ℝ) ≤ Real.exp ((-161804871949/250000000000 : ℝ)/8) ∧ Real.exp ((-161804871949/250000000000 : ℝ)/8) ≤ (115285458595329927/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-161804871949/250000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0000_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1046998702637/500000000000 : ℝ) ≤ 4*Real.exp (0/1 : ℝ)*Real.exp (-mu (radius 8 (1/32 : ℝ))) ∧ (20549/10000 : ℝ) < (1046998702637/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (1/32 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0000_exp_radius
  have hrNumeric : (99610136947/100000000000 : ℝ) ≤ Real.exp (-1/256 : ℝ) ∧ Real.exp (-1/256 : ℝ) ≤ (996101369471/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (99610136947/100000000000 : ℝ) ≤ (radius 8 (1/32 : ℝ)) ∧ (radius 8 (1/32 : ℝ)) ≤ (996101369471/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (1/32 : ℝ)) (99610136947/100000000000 : ℝ) (996101369471/1000000000000 : ℝ) (22053998699/250000000000 : ℝ) (88215994809/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (1/32 : ℝ)) (99610136947/100000000000 : ℝ) (996101369471/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (1/32 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (99610136947/100000000000 : ℝ) (996101369471/1000000000000 : ℝ) (199610136947/200000000000 : ℝ) (15594541949/15625000000 : ℝ) (998048781107/1000000000000 : ℝ) (249512195277/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (1/32 : ℝ)) 1 (199610136947/200000000000 : ℝ) (15594541949/15625000000 : ℝ) (998048781107/1000000000000 : ℝ) (249512195277/250000000000 : ℝ) (998049732921/1000000000000 : ℝ) (499024866461/500000000000 : ℝ) (24951243323/25000000000 : ℝ) (499024866461/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (1/32 : ℝ)) 2 (998049732921/1000000000000 : ℝ) (499024866461/500000000000 : ℝ) (24951243323/25000000000 : ℝ) (499024866461/500000000000 : ℝ) (24951243323/25000000000 : ℝ) (499024866461/500000000000 : ℝ) (24951243323/25000000000 : ℝ) (499024866461/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (1/32 : ℝ)) 3 (24951243323/25000000000 : ℝ) (499024866461/500000000000 : ℝ) (24951243323/25000000000 : ℝ) (499024866461/500000000000 : ℝ) (24951243323/25000000000 : ℝ) (499024866461/500000000000 : ℝ) (24951243323/25000000000 : ℝ) (499024866461/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (1/32 : ℝ)) 4 (24951243323/25000000000 : ℝ) (499024866461/500000000000 : ℝ) (24951243323/25000000000 : ℝ) (499024866461/500000000000 : ℝ) (24951243323/25000000000 : ℝ) (499024866461/500000000000 : ℝ) (24951243323/25000000000 : ℝ) (499024866461/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (1/32 : ℝ)) 5 (24951243323/25000000000 : ℝ) (499024866461/500000000000 : ℝ) (24951243323/25000000000 : ℝ) (499024866461/500000000000 : ℝ) (24951243323/25000000000 : ℝ) (499024866461/500000000000 : ℝ) (24951243323/25000000000 : ℝ) (499024866461/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (1/32 : ℝ)) 6 (24951243323/25000000000 : ℝ) (499024866461/500000000000 : ℝ) (24951243323/25000000000 : ℝ) (499024866461/500000000000 : ℝ) (24951243323/25000000000 : ℝ) (499024866461/500000000000 : ℝ) (24951243323/25000000000 : ℝ) (499024866461/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (1/32 : ℝ)) 7 (24951243323/25000000000 : ℝ) (499024866461/500000000000 : ℝ) (24951243323/25000000000 : ℝ) (499024866461/500000000000 : ℝ) (24951243323/25000000000 : ℝ) (499024866461/500000000000 : ℝ) (24951243323/25000000000 : ℝ) (499024866461/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (1/32 : ℝ))) (22053998699/250000000000 : ℝ) (88215994809/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (1/32 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (22053998699/250000000000 : ℝ) (88215994809/1000000000000 : ℝ) (272053998699/500000000000 : ℝ) (108821599481/200000000000 : ℝ) (297011775517/1000000000000 : ℝ) (14850588777/50000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (1/32 : ℝ))) 1 (272053998699/500000000000 : ℝ) (108821599481/200000000000 : ℝ) (297011775517/1000000000000 : ℝ) (14850588777/50000000000 : ℝ) (420559886457/1000000000000 : ℝ) (420559886473/1000000000000 : ℝ) (16080123501/40000000000 : ℝ) (50250385943/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (1/32 : ℝ))) 2 (420559886457/1000000000000 : ℝ) (420559886473/1000000000000 : ℝ) (16080123501/40000000000 : ℝ) (50250385943/125000000000 : ℝ) (411281486991/1000000000000 : ℝ) (411281487009/1000000000000 : ℝ) (25698550911/62500000000 : ℝ) (205588407297/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (1/32 : ℝ))) 3 (411281486991/1000000000000 : ℝ) (411281487009/1000000000000 : ℝ) (25698550911/62500000000 : ℝ) (205588407297/500000000000 : ℝ) (411229150783/1000000000000 : ℝ) (205614575401/500000000000 : ℝ) (411229147453/1000000000000 : ℝ) (25701821717/62500000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (1/32 : ℝ))) 4 (411229150783/1000000000000 : ℝ) (205614575401/500000000000 : ℝ) (411229147453/1000000000000 : ℝ) (25701821717/62500000000 : ℝ) (205614574559/500000000000 : ℝ) (411229149137/1000000000000 : ℝ) (411229149117/1000000000000 : ℝ) (411229149137/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (1/32 : ℝ))) 5 (205614574559/500000000000 : ℝ) (411229149137/1000000000000 : ℝ) (411229149117/1000000000000 : ℝ) (411229149137/1000000000000 : ℝ) (411229149117/1000000000000 : ℝ) (411229149137/1000000000000 : ℝ) (411229149117/1000000000000 : ℝ) (411229149137/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (1/32 : ℝ))) 6 (411229149117/1000000000000 : ℝ) (411229149137/1000000000000 : ℝ) (411229149117/1000000000000 : ℝ) (411229149137/1000000000000 : ℝ) (411229149117/1000000000000 : ℝ) (411229149137/1000000000000 : ℝ) (411229149117/1000000000000 : ℝ) (411229149137/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (1/32 : ℝ))) 7 (411229149117/1000000000000 : ℝ) (411229149137/1000000000000 : ℝ) (411229149117/1000000000000 : ℝ) (411229149137/1000000000000 : ℝ) (411229149117/1000000000000 : ℝ) (411229149137/1000000000000 : ℝ) (411229149117/1000000000000 : ℝ) (411229149137/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (1/32 : ℝ)) hmem 8 (24951243323/25000000000 : ℝ) (499024866461/500000000000 : ℝ) (24951243323/25000000000 : ℝ) (499024866461/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (1/32 : ℝ))) hcmem 8 (411229149117/1000000000000 : ℝ) (411229149137/1000000000000 : ℝ) (411229149117/1000000000000 : ℝ) (411229149137/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (1/32 : ℝ)) (24951243323/25000000000 : ℝ) (499024866461/500000000000 : ℝ) (411229149117/1000000000000 : ℝ) (411229149137/1000000000000 : ℝ) (647219487763/1000000000000 : ℝ) (161804871949/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0000_exp_lower
  have heNumeric : (1046998702637/500000000000 : ℝ)/4 ≤ Real.exp (-161804871949/250000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1046998702637/500000000000 : ℝ)/4 ≤ Real.exp ((0/1 : ℝ)-(161804871949/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (0/1 : ℝ) (1/32 : ℝ) (161804871949/250000000000 : ℝ) (1046998702637/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0001; no trusted numerical premise.
theorem cover8_leaf0001_exp_radius : (999267846280429859/1000000000000000000 : ℝ) ≤ Real.exp ((-3/512 : ℝ)/8) ∧ Real.exp ((-3/512 : ℝ)/8) ≤ (49963392314021493/50000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-3/512 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0001_exp_lower : (450046760913273/488281250000000 : ℝ) ≤ Real.exp ((-163080162597/250000000000 : ℝ)/8) ∧ Real.exp ((-163080162597/250000000000 : ℝ)/8) ≤ (184339153270076621/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-163080162597/250000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0001_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2083342782629/1000000000000 : ℝ) ≤ 4*Real.exp (1/32 : ℝ)*Real.exp (-mu (radius 8 (3/64 : ℝ))) ∧ (20549/10000 : ℝ) < (2083342782629/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (3/64 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0001_exp_radius
  have hrNumeric : (994157757659/1000000000000 : ℝ) ≤ Real.exp (-3/512 : ℝ) ∧ Real.exp (-3/512 : ℝ) ≤ (49707887883/50000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (994157757659/1000000000000 : ℝ) ≤ (radius 8 (3/64 : ℝ)) ∧ (radius 8 (3/64 : ℝ)) ≤ (49707887883/50000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (3/64 : ℝ)) (994157757659/1000000000000 : ℝ) (49707887883/50000000000 : ℝ) (107936800417/1000000000000 : ℝ) (26984200107/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (3/64 : ℝ)) (994157757659/1000000000000 : ℝ) (49707887883/50000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (3/64 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (994157757659/1000000000000 : ℝ) (49707887883/50000000000 : ℝ) (997078878829/1000000000000 : ℝ) (99707887883/100000000000 : ℝ) (498537299923/500000000000 : ℝ) (997074599847/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (3/64 : ℝ)) 1 (997078878829/1000000000000 : ℝ) (99707887883/100000000000 : ℝ) (498537299923/500000000000 : ℝ) (997074599847/1000000000000 : ℝ) (997076739337/1000000000000 : ℝ) (997076739339/1000000000000 : ℝ) (199415347867/200000000000 : ℝ) (997076739337/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (3/64 : ℝ)) 2 (997076739337/1000000000000 : ℝ) (997076739339/1000000000000 : ℝ) (199415347867/200000000000 : ℝ) (997076739337/1000000000000 : ℝ) (124634592417/125000000000 : ℝ) (498538369669/500000000000 : ℝ) (199415347867/200000000000 : ℝ) (498538369669/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (3/64 : ℝ)) 3 (124634592417/125000000000 : ℝ) (498538369669/500000000000 : ℝ) (199415347867/200000000000 : ℝ) (498538369669/500000000000 : ℝ) (199415347867/200000000000 : ℝ) (498538369669/500000000000 : ℝ) (199415347867/200000000000 : ℝ) (498538369669/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (3/64 : ℝ)) 4 (199415347867/200000000000 : ℝ) (498538369669/500000000000 : ℝ) (199415347867/200000000000 : ℝ) (498538369669/500000000000 : ℝ) (199415347867/200000000000 : ℝ) (498538369669/500000000000 : ℝ) (199415347867/200000000000 : ℝ) (498538369669/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (3/64 : ℝ)) 5 (199415347867/200000000000 : ℝ) (498538369669/500000000000 : ℝ) (199415347867/200000000000 : ℝ) (498538369669/500000000000 : ℝ) (199415347867/200000000000 : ℝ) (498538369669/500000000000 : ℝ) (199415347867/200000000000 : ℝ) (498538369669/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (3/64 : ℝ)) 6 (199415347867/200000000000 : ℝ) (498538369669/500000000000 : ℝ) (199415347867/200000000000 : ℝ) (498538369669/500000000000 : ℝ) (199415347867/200000000000 : ℝ) (498538369669/500000000000 : ℝ) (199415347867/200000000000 : ℝ) (498538369669/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (3/64 : ℝ)) 7 (199415347867/200000000000 : ℝ) (498538369669/500000000000 : ℝ) (199415347867/200000000000 : ℝ) (498538369669/500000000000 : ℝ) (199415347867/200000000000 : ℝ) (498538369669/500000000000 : ℝ) (199415347867/200000000000 : ℝ) (498538369669/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (3/64 : ℝ))) (107936800417/1000000000000 : ℝ) (26984200107/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (3/64 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (107936800417/1000000000000 : ℝ) (26984200107/250000000000 : ℝ) (34623025013/62500000000 : ℝ) (276984200107/500000000000 : ℝ) (20533585333/62500000000 : ℝ) (164268682673/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (3/64 : ℝ))) 1 (34623025013/62500000000 : ℝ) (276984200107/500000000000 : ℝ) (20533585333/62500000000 : ℝ) (164268682673/500000000000 : ℝ) (27578305173/62500000000 : ℝ) (22062644139/50000000000 : ℝ) (426613781633/1000000000000 : ℝ) (26663361353/62500000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (3/64 : ℝ))) 2 (27578305173/62500000000 : ℝ) (22062644139/50000000000 : ℝ) (426613781633/1000000000000 : ℝ) (26663361353/62500000000 : ℝ) (2169666661/5000000000 : ℝ) (216966666107/500000000000 : ℝ) (43387159503/100000000000 : ℝ) (108467898761/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (3/64 : ℝ))) 3 (2169666661/5000000000 : ℝ) (216966666107/500000000000 : ℝ) (43387159503/100000000000 : ℝ) (108467898761/250000000000 : ℝ) (86780492723/200000000000 : ℝ) (433902463629/1000000000000 : ℝ) (108475615629/250000000000 : ℝ) (433902462531/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (3/64 : ℝ))) 4 (86780492723/200000000000 : ℝ) (433902463629/1000000000000 : ℝ) (108475615629/250000000000 : ℝ) (433902462531/1000000000000 : ℝ) (86780492613/200000000000 : ℝ) (10847561577/25000000000 : ℝ) (86780492613/200000000000 : ℝ) (10847561577/25000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (3/64 : ℝ))) 5 (86780492613/200000000000 : ℝ) (10847561577/25000000000 : ℝ) (86780492613/200000000000 : ℝ) (10847561577/25000000000 : ℝ) (86780492613/200000000000 : ℝ) (10847561577/25000000000 : ℝ) (86780492613/200000000000 : ℝ) (10847561577/25000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (3/64 : ℝ))) 6 (86780492613/200000000000 : ℝ) (10847561577/25000000000 : ℝ) (86780492613/200000000000 : ℝ) (10847561577/25000000000 : ℝ) (86780492613/200000000000 : ℝ) (10847561577/25000000000 : ℝ) (86780492613/200000000000 : ℝ) (10847561577/25000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (3/64 : ℝ))) 7 (86780492613/200000000000 : ℝ) (10847561577/25000000000 : ℝ) (86780492613/200000000000 : ℝ) (10847561577/25000000000 : ℝ) (86780492613/200000000000 : ℝ) (10847561577/25000000000 : ℝ) (86780492613/200000000000 : ℝ) (10847561577/25000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (3/64 : ℝ)) hmem 8 (199415347867/200000000000 : ℝ) (498538369669/500000000000 : ℝ) (199415347867/200000000000 : ℝ) (498538369669/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (3/64 : ℝ))) hcmem 8 (86780492613/200000000000 : ℝ) (10847561577/25000000000 : ℝ) (86780492613/200000000000 : ℝ) (10847561577/25000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (3/64 : ℝ)) (199415347867/200000000000 : ℝ) (498538369669/500000000000 : ℝ) (86780492613/200000000000 : ℝ) (10847561577/25000000000 : ℝ) (683570650361/1000000000000 : ℝ) (170892662597/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0001_exp_lower
  have heNumeric : (2083342782629/1000000000000 : ℝ)/4 ≤ Real.exp (-163080162597/250000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2083342782629/1000000000000 : ℝ)/4 ≤ Real.exp ((1/32 : ℝ)-(170892662597/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (1/32 : ℝ) (3/64 : ℝ) (170892662597/250000000000 : ℝ) (2083342782629/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0002; no trusted numerical premise.
theorem cover8_leaf0002_exp_radius : (499511957090987831/500000000000000000 : ℝ) ≤ Real.exp ((-1/128 : ℝ)/8) ∧ Real.exp ((-1/128 : ℝ)/8) ≤ (999023914181975663/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1/128 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0002_exp_lower : (3594642499962007/3906250000000000 : ℝ) ≤ Real.exp ((-332533167827/500000000000 : ℝ)/8) ∧ Real.exp ((-332533167827/500000000000 : ℝ)/8) ≤ (920228479990273793/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-332533167827/500000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0002_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2056957656669/1000000000000 : ℝ) ≤ 4*Real.exp (3/64 : ℝ)*Real.exp (-mu (radius 8 (1/16 : ℝ))) ∧ (20549/10000 : ℝ) < (2056957656669/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (1/16 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0002_exp_radius
  have hrNumeric : (49610896913/50000000000 : ℝ) ≤ Real.exp (-1/128 : ℝ) ∧ Real.exp (-1/128 : ℝ) ≤ (992217938261/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (49610896913/50000000000 : ℝ) ≤ (radius 8 (1/16 : ℝ)) ∧ (radius 8 (1/16 : ℝ)) ≤ (992217938261/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (1/16 : ℝ)) (49610896913/50000000000 : ℝ) (992217938261/1000000000000 : ℝ) (62256652241/500000000000 : ℝ) (124513304491/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (1/16 : ℝ)) (49610896913/50000000000 : ℝ) (992217938261/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (1/16 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (49610896913/50000000000 : ℝ) (992217938261/1000000000000 : ℝ) (99610896913/100000000000 : ℝ) (996108969131/1000000000000 : ℝ) (996101369469/1000000000000 : ℝ) (996101369471/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (1/16 : ℝ)) 1 (99610896913/100000000000 : ℝ) (996108969131/1000000000000 : ℝ) (996101369469/1000000000000 : ℝ) (996101369471/1000000000000 : ℝ) (996105169299/1000000000000 : ℝ) (996105169301/1000000000000 : ℝ) (249026292323/250000000000 : ℝ) (498052584647/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (1/16 : ℝ)) 2 (996105169299/1000000000000 : ℝ) (996105169301/1000000000000 : ℝ) (249026292323/250000000000 : ℝ) (498052584647/500000000000 : ℝ) (199221033859/200000000000 : ℝ) (498052584649/500000000000 : ℝ) (199221033859/200000000000 : ℝ) (498052584649/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (1/16 : ℝ)) 3 (199221033859/200000000000 : ℝ) (498052584649/500000000000 : ℝ) (199221033859/200000000000 : ℝ) (498052584649/500000000000 : ℝ) (199221033859/200000000000 : ℝ) (498052584649/500000000000 : ℝ) (199221033859/200000000000 : ℝ) (498052584649/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (1/16 : ℝ)) 4 (199221033859/200000000000 : ℝ) (498052584649/500000000000 : ℝ) (199221033859/200000000000 : ℝ) (498052584649/500000000000 : ℝ) (199221033859/200000000000 : ℝ) (498052584649/500000000000 : ℝ) (199221033859/200000000000 : ℝ) (498052584649/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (1/16 : ℝ)) 5 (199221033859/200000000000 : ℝ) (498052584649/500000000000 : ℝ) (199221033859/200000000000 : ℝ) (498052584649/500000000000 : ℝ) (199221033859/200000000000 : ℝ) (498052584649/500000000000 : ℝ) (199221033859/200000000000 : ℝ) (498052584649/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (1/16 : ℝ)) 6 (199221033859/200000000000 : ℝ) (498052584649/500000000000 : ℝ) (199221033859/200000000000 : ℝ) (498052584649/500000000000 : ℝ) (199221033859/200000000000 : ℝ) (498052584649/500000000000 : ℝ) (199221033859/200000000000 : ℝ) (498052584649/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (1/16 : ℝ)) 7 (199221033859/200000000000 : ℝ) (498052584649/500000000000 : ℝ) (199221033859/200000000000 : ℝ) (498052584649/500000000000 : ℝ) (199221033859/200000000000 : ℝ) (498052584649/500000000000 : ℝ) (199221033859/200000000000 : ℝ) (498052584649/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (1/16 : ℝ))) (62256652241/500000000000 : ℝ) (124513304491/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (1/16 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (62256652241/500000000000 : ℝ) (124513304491/1000000000000 : ℝ) (562256652241/1000000000000 : ℝ) (281128326123/500000000000 : ℝ) (176432213953/500000000000 : ℝ) (4410805349/12500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (1/16 : ℝ))) 1 (562256652241/1000000000000 : ℝ) (281128326123/500000000000 : ℝ) (176432213953/500000000000 : ℝ) (4410805349/12500000000 : ℝ) (457560540073/1000000000000 : ℝ) (457560540083/1000000000000 : ℝ) (445421566529/1000000000000 : ℝ) (445421566541/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (1/16 : ℝ))) 2 (457560540073/1000000000000 : ℝ) (457560540083/1000000000000 : ℝ) (445421566529/1000000000000 : ℝ) (445421566541/1000000000000 : ℝ) (451491053301/1000000000000 : ℝ) (1763636927/3906250000 : ℝ) (22572512739/50000000000 : ℝ) (56431281849/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (1/16 : ℝ))) 3 (451491053301/1000000000000 : ℝ) (1763636927/3906250000 : ℝ) (22572512739/50000000000 : ℝ) (56431281849/125000000000 : ℝ) (11286766351/25000000000 : ℝ) (112867663513/250000000000 : ℝ) (451470653579/1000000000000 : ℝ) (56433831699/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (1/16 : ℝ))) 4 (11286766351/25000000000 : ℝ) (112867663513/250000000000 : ℝ) (451470653579/1000000000000 : ℝ) (56433831699/125000000000 : ℝ) (451470653809/1000000000000 : ℝ) (225735326911/500000000000 : ℝ) (451470653809/1000000000000 : ℝ) (225735326911/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (1/16 : ℝ))) 5 (451470653809/1000000000000 : ℝ) (225735326911/500000000000 : ℝ) (451470653809/1000000000000 : ℝ) (225735326911/500000000000 : ℝ) (451470653809/1000000000000 : ℝ) (225735326911/500000000000 : ℝ) (451470653809/1000000000000 : ℝ) (225735326911/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (1/16 : ℝ))) 6 (451470653809/1000000000000 : ℝ) (225735326911/500000000000 : ℝ) (451470653809/1000000000000 : ℝ) (225735326911/500000000000 : ℝ) (451470653809/1000000000000 : ℝ) (225735326911/500000000000 : ℝ) (451470653809/1000000000000 : ℝ) (225735326911/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (1/16 : ℝ))) 7 (451470653809/1000000000000 : ℝ) (225735326911/500000000000 : ℝ) (451470653809/1000000000000 : ℝ) (225735326911/500000000000 : ℝ) (451470653809/1000000000000 : ℝ) (225735326911/500000000000 : ℝ) (451470653809/1000000000000 : ℝ) (225735326911/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (1/16 : ℝ)) hmem 8 (199221033859/200000000000 : ℝ) (498052584649/500000000000 : ℝ) (199221033859/200000000000 : ℝ) (498052584649/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (1/16 : ℝ))) hcmem 8 (451470653809/1000000000000 : ℝ) (225735326911/500000000000 : ℝ) (451470653809/1000000000000 : ℝ) (225735326911/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (1/16 : ℝ)) (199221033859/200000000000 : ℝ) (498052584649/500000000000 : ℝ) (451470653809/1000000000000 : ℝ) (225735326911/500000000000 : ℝ) (71194133563/100000000000 : ℝ) (355970667827/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0002_exp_lower
  have heNumeric : (2056957656669/1000000000000 : ℝ)/4 ≤ Real.exp (-332533167827/500000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2056957656669/1000000000000 : ℝ)/4 ≤ Real.exp ((3/64 : ℝ)-(355970667827/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (3/64 : ℝ) (1/16 : ℝ) (355970667827/500000000000 : ℝ) (2056957656669/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0003; no trusted numerical premise.
theorem cover8_leaf0003_exp_radius : (499450985231790913/500000000000000000 : ℝ) ≤ Real.exp ((-9/1024 : ℝ)/8) ∧ Real.exp ((-9/1024 : ℝ)/8) ≤ (998901970463581827/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-9/1024 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0003_exp_lower : (460305126448218229/500000000000000000 : ℝ) ≤ Real.exp ((-330874041887/500000000000 : ℝ)/8) ∧ Real.exp ((-330874041887/500000000000 : ℝ)/8) ≤ (920610252896436459/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-330874041887/500000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0003_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1031897248593/500000000000 : ℝ) ≤ 4*Real.exp (1/16 : ℝ)*Real.exp (-mu (radius 8 (9/128 : ℝ))) ∧ (20549/10000 : ℝ) < (1031897248593/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (9/128 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0003_exp_radius
  have hrNumeric : (495624724201/500000000000 : ℝ) ≤ Real.exp (-9/1024 : ℝ) ∧ Real.exp (-9/1024 : ℝ) ≤ (991249448403/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (495624724201/500000000000 : ℝ) ≤ (radius 8 (9/128 : ℝ)) ∧ (radius 8 (9/128 : ℝ)) ≤ (991249448403/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (9/128 : ℝ)) (495624724201/500000000000 : ℝ) (991249448403/1000000000000 : ℝ) (66001005751/500000000000 : ℝ) (132002011511/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (9/128 : ℝ)) (495624724201/500000000000 : ℝ) (991249448403/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (9/128 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (495624724201/500000000000 : ℝ) (991249448403/1000000000000 : ℝ) (995624724201/1000000000000 : ℝ) (497812362101/500000000000 : ℝ) (995615110573/1000000000000 : ℝ) (497807555287/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (9/128 : ℝ)) 1 (995624724201/1000000000000 : ℝ) (497812362101/500000000000 : ℝ) (995615110573/1000000000000 : ℝ) (497807555287/500000000000 : ℝ) (995619917387/1000000000000 : ℝ) (248904979347/250000000000 : ℝ) (7964959339/8000000000 : ℝ) (995619917377/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (9/128 : ℝ)) 2 (995619917387/1000000000000 : ℝ) (248904979347/250000000000 : ℝ) (7964959339/8000000000 : ℝ) (995619917377/1000000000000 : ℝ) (995619917381/1000000000000 : ℝ) (995619917383/1000000000000 : ℝ) (49780995869/50000000000 : ℝ) (995619917383/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (9/128 : ℝ)) 3 (995619917381/1000000000000 : ℝ) (995619917383/1000000000000 : ℝ) (49780995869/50000000000 : ℝ) (995619917383/1000000000000 : ℝ) (49780995869/50000000000 : ℝ) (995619917383/1000000000000 : ℝ) (49780995869/50000000000 : ℝ) (995619917383/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (9/128 : ℝ)) 4 (49780995869/50000000000 : ℝ) (995619917383/1000000000000 : ℝ) (49780995869/50000000000 : ℝ) (995619917383/1000000000000 : ℝ) (49780995869/50000000000 : ℝ) (995619917383/1000000000000 : ℝ) (49780995869/50000000000 : ℝ) (995619917383/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (9/128 : ℝ)) 5 (49780995869/50000000000 : ℝ) (995619917383/1000000000000 : ℝ) (49780995869/50000000000 : ℝ) (995619917383/1000000000000 : ℝ) (49780995869/50000000000 : ℝ) (995619917383/1000000000000 : ℝ) (49780995869/50000000000 : ℝ) (995619917383/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (9/128 : ℝ)) 6 (49780995869/50000000000 : ℝ) (995619917383/1000000000000 : ℝ) (49780995869/50000000000 : ℝ) (995619917383/1000000000000 : ℝ) (49780995869/50000000000 : ℝ) (995619917383/1000000000000 : ℝ) (49780995869/50000000000 : ℝ) (995619917383/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (9/128 : ℝ)) 7 (49780995869/50000000000 : ℝ) (995619917383/1000000000000 : ℝ) (49780995869/50000000000 : ℝ) (995619917383/1000000000000 : ℝ) (49780995869/50000000000 : ℝ) (995619917383/1000000000000 : ℝ) (49780995869/50000000000 : ℝ) (995619917383/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (9/128 : ℝ))) (66001005751/500000000000 : ℝ) (132002011511/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (9/128 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (66001005751/500000000000 : ℝ) (132002011511/1000000000000 : ℝ) (566001005751/1000000000000 : ℝ) (141500251439/250000000000 : ℝ) (363320810719/1000000000000 : ℝ) (363320810733/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (9/128 : ℝ))) 1 (566001005751/1000000000000 : ℝ) (141500251439/250000000000 : ℝ) (363320810719/1000000000000 : ℝ) (363320810733/1000000000000 : ℝ) (92932181647/200000000000 : ℝ) (92932181649/200000000000 : ℝ) (226737703237/500000000000 : ℝ) (226737703243/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (9/128 : ℝ))) 2 (92932181647/200000000000 : ℝ) (92932181649/200000000000 : ℝ) (226737703237/500000000000 : ℝ) (226737703243/500000000000 : ℝ) (229534078677/500000000000 : ℝ) (229534078683/500000000000 : ℝ) (229517044157/500000000000 : ℝ) (229517044163/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (9/128 : ℝ))) 3 (229534078677/500000000000 : ℝ) (229534078683/500000000000 : ℝ) (229517044157/500000000000 : ℝ) (229517044163/500000000000 : ℝ) (229525561417/500000000000 : ℝ) (229525561423/500000000000 : ℝ) (459051122517/1000000000000 : ℝ) (45905112253/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (9/128 : ℝ))) 4 (229525561417/500000000000 : ℝ) (229525561423/500000000000 : ℝ) (459051122517/1000000000000 : ℝ) (45905112253/100000000000 : ℝ) (18362044907/40000000000 : ℝ) (112073028/244140625 : ℝ) (18362044907/40000000000 : ℝ) (112073028/244140625 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (9/128 : ℝ))) 5 (18362044907/40000000000 : ℝ) (112073028/244140625 : ℝ) (18362044907/40000000000 : ℝ) (112073028/244140625 : ℝ) (18362044907/40000000000 : ℝ) (112073028/244140625 : ℝ) (18362044907/40000000000 : ℝ) (112073028/244140625 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (9/128 : ℝ))) 6 (18362044907/40000000000 : ℝ) (112073028/244140625 : ℝ) (18362044907/40000000000 : ℝ) (112073028/244140625 : ℝ) (18362044907/40000000000 : ℝ) (112073028/244140625 : ℝ) (18362044907/40000000000 : ℝ) (112073028/244140625 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (9/128 : ℝ))) 7 (18362044907/40000000000 : ℝ) (112073028/244140625 : ℝ) (18362044907/40000000000 : ℝ) (112073028/244140625 : ℝ) (18362044907/40000000000 : ℝ) (112073028/244140625 : ℝ) (18362044907/40000000000 : ℝ) (112073028/244140625 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (9/128 : ℝ)) hmem 8 (49780995869/50000000000 : ℝ) (995619917383/1000000000000 : ℝ) (49780995869/50000000000 : ℝ) (995619917383/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (9/128 : ℝ))) hcmem 8 (18362044907/40000000000 : ℝ) (112073028/244140625 : ℝ) (18362044907/40000000000 : ℝ) (112073028/244140625 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (9/128 : ℝ)) (49780995869/50000000000 : ℝ) (995619917383/1000000000000 : ℝ) (18362044907/40000000000 : ℝ) (112073028/244140625 : ℝ) (579398467/800000000 : ℝ) (362124041887/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0003_exp_lower
  have heNumeric : (1031897248593/500000000000 : ℝ)/4 ≤ Real.exp (-330874041887/500000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1031897248593/500000000000 : ℝ)/4 ≤ Real.exp ((1/16 : ℝ)-(362124041887/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (1/16 : ℝ) (9/128 : ℝ) (362124041887/500000000000 : ℝ) (1031897248593/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0004; no trusted numerical premise.
theorem cover8_leaf0004_exp_radius : (998780041629987287/1000000000000000000 : ℝ) ≤ Real.exp ((-5/512 : ℝ)/8) ∧ Real.exp ((-5/512 : ℝ)/8) ≤ (124847505203748411/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5/512 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0004_exp_lower : (184040078279225633/200000000000000000 : ℝ) ≤ Real.exp ((-332655263691/500000000000 : ℝ)/8) ∧ Real.exp ((-332655263691/500000000000 : ℝ)/8) ≤ (460100195698064083/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-332655263691/500000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0004_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2056455425947/1000000000000 : ℝ) ≤ 4*Real.exp (9/128 : ℝ)*Real.exp (-mu (radius 8 (5/64 : ℝ))) ∧ (20549/10000 : ℝ) < (2056455425947/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (5/64 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0004_exp_radius
  have hrNumeric : (990281903873/1000000000000 : ℝ) ≤ Real.exp (-5/512 : ℝ) ∧ Real.exp (-5/512 : ℝ) ≤ (495140951937/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (990281903873/1000000000000 : ℝ) ≤ (radius 8 (5/64 : ℝ)) ∧ (radius 8 (5/64 : ℝ)) ≤ (495140951937/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (5/64 : ℝ)) (990281903873/1000000000000 : ℝ) (495140951937/500000000000 : ℝ) (139074623349/1000000000000 : ℝ) (139074623357/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (5/64 : ℝ)) (990281903873/1000000000000 : ℝ) (495140951937/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (5/64 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (990281903873/1000000000000 : ℝ) (495140951937/500000000000 : ℝ) (7774538687/7812500000 : ℝ) (995140951937/1000000000000 : ℝ) (995129089049/1000000000000 : ℝ) (995129089051/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (5/64 : ℝ)) 1 (7774538687/7812500000 : ℝ) (995140951937/1000000000000 : ℝ) (995129089049/1000000000000 : ℝ) (995129089051/1000000000000 : ℝ) (248783755123/250000000000 : ℝ) (497567510247/500000000000 : ℝ) (497567510237/500000000000 : ℝ) (995135020477/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (5/64 : ℝ)) 2 (248783755123/250000000000 : ℝ) (497567510247/500000000000 : ℝ) (497567510237/500000000000 : ℝ) (995135020477/1000000000000 : ℝ) (995135020483/1000000000000 : ℝ) (497567510243/500000000000 : ℝ) (497567510241/500000000000 : ℝ) (497567510243/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (5/64 : ℝ)) 3 (995135020483/1000000000000 : ℝ) (497567510243/500000000000 : ℝ) (497567510241/500000000000 : ℝ) (497567510243/500000000000 : ℝ) (497567510241/500000000000 : ℝ) (497567510243/500000000000 : ℝ) (497567510241/500000000000 : ℝ) (497567510243/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (5/64 : ℝ)) 4 (497567510241/500000000000 : ℝ) (497567510243/500000000000 : ℝ) (497567510241/500000000000 : ℝ) (497567510243/500000000000 : ℝ) (497567510241/500000000000 : ℝ) (497567510243/500000000000 : ℝ) (497567510241/500000000000 : ℝ) (497567510243/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (5/64 : ℝ)) 5 (497567510241/500000000000 : ℝ) (497567510243/500000000000 : ℝ) (497567510241/500000000000 : ℝ) (497567510243/500000000000 : ℝ) (497567510241/500000000000 : ℝ) (497567510243/500000000000 : ℝ) (497567510241/500000000000 : ℝ) (497567510243/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (5/64 : ℝ)) 6 (497567510241/500000000000 : ℝ) (497567510243/500000000000 : ℝ) (497567510241/500000000000 : ℝ) (497567510243/500000000000 : ℝ) (497567510241/500000000000 : ℝ) (497567510243/500000000000 : ℝ) (497567510241/500000000000 : ℝ) (497567510243/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (5/64 : ℝ)) 7 (497567510241/500000000000 : ℝ) (497567510243/500000000000 : ℝ) (497567510241/500000000000 : ℝ) (497567510243/500000000000 : ℝ) (497567510241/500000000000 : ℝ) (497567510243/500000000000 : ℝ) (497567510241/500000000000 : ℝ) (497567510243/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (5/64 : ℝ))) (139074623349/1000000000000 : ℝ) (139074623357/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (5/64 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (139074623349/1000000000000 : ℝ) (139074623357/1000000000000 : ℝ) (284768655837/500000000000 : ℝ) (569537311679/1000000000000 : ℝ) (372927101923/1000000000000 : ℝ) (74585420387/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (5/64 : ℝ))) 1 (284768655837/500000000000 : ℝ) (569537311679/1000000000000 : ℝ) (372927101923/1000000000000 : ℝ) (74585420387/200000000000 : ℝ) (235616103399/500000000000 : ℝ) (471232206807/1000000000000 : ℝ) (46086429573/100000000000 : ℝ) (460864295741/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (5/64 : ℝ))) 2 (235616103399/500000000000 : ℝ) (471232206807/1000000000000 : ℝ) (46086429573/100000000000 : ℝ) (460864295741/1000000000000 : ℝ) (3641001963/7812500000 : ℝ) (233024125637/500000000000 : ℝ) (233009709621/500000000000 : ℝ) (466019419253/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (5/64 : ℝ))) 3 (3641001963/7812500000 : ℝ) (233024125637/500000000000 : ℝ) (233009709621/500000000000 : ℝ) (466019419253/1000000000000 : ℝ) (466033835253/1000000000000 : ℝ) (1820444669/3906250000 : ℝ) (46603383503/100000000000 : ℝ) (466033835041/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (5/64 : ℝ))) 4 (466033835253/1000000000000 : ℝ) (1820444669/3906250000 : ℝ) (46603383503/100000000000 : ℝ) (466033835041/1000000000000 : ℝ) (466033835141/1000000000000 : ℝ) (466033835153/1000000000000 : ℝ) (466033835141/1000000000000 : ℝ) (466033835153/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (5/64 : ℝ))) 5 (466033835141/1000000000000 : ℝ) (466033835153/1000000000000 : ℝ) (466033835141/1000000000000 : ℝ) (466033835153/1000000000000 : ℝ) (466033835141/1000000000000 : ℝ) (466033835153/1000000000000 : ℝ) (466033835141/1000000000000 : ℝ) (466033835153/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (5/64 : ℝ))) 6 (466033835141/1000000000000 : ℝ) (466033835153/1000000000000 : ℝ) (466033835141/1000000000000 : ℝ) (466033835153/1000000000000 : ℝ) (466033835141/1000000000000 : ℝ) (466033835153/1000000000000 : ℝ) (466033835141/1000000000000 : ℝ) (466033835153/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (5/64 : ℝ))) 7 (466033835141/1000000000000 : ℝ) (466033835153/1000000000000 : ℝ) (466033835141/1000000000000 : ℝ) (466033835153/1000000000000 : ℝ) (466033835141/1000000000000 : ℝ) (466033835153/1000000000000 : ℝ) (466033835141/1000000000000 : ℝ) (466033835153/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (5/64 : ℝ)) hmem 8 (497567510241/500000000000 : ℝ) (497567510243/500000000000 : ℝ) (497567510241/500000000000 : ℝ) (497567510243/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (5/64 : ℝ))) hcmem 8 (466033835141/1000000000000 : ℝ) (466033835153/1000000000000 : ℝ) (466033835141/1000000000000 : ℝ) (466033835153/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (5/64 : ℝ)) (497567510241/500000000000 : ℝ) (497567510243/500000000000 : ℝ) (466033835141/1000000000000 : ℝ) (466033835153/1000000000000 : ℝ) (735623027359/1000000000000 : ℝ) (367811513691/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0004_exp_lower
  have heNumeric : (2056455425947/1000000000000 : ℝ)/4 ≤ Real.exp (-332655263691/500000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2056455425947/1000000000000 : ℝ)/4 ≤ Real.exp ((9/128 : ℝ)-(367811513691/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (9/128 : ℝ) (5/64 : ℝ) (367811513691/500000000000 : ℝ) (2056455425947/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0005; no trusted numerical premise.
theorem cover8_leaf0005_exp_radius : (99871908279442197/100000000000000000 : ℝ) ≤ Real.exp ((-21/2048 : ℝ)/8) ∧ Real.exp ((-21/2048 : ℝ)/8) ≤ (998719082794421971/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21/2048 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0005_exp_lower : (36819165968646947/40000000000000000 : ℝ) ≤ Real.exp ((-662887441203/1000000000000 : ℝ)/8) ∧ Real.exp ((-662887441203/1000000000000 : ℝ)/8) ≤ (230119787304043419/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-662887441203/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0005_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (515361109157/250000000000 : ℝ) ≤ 4*Real.exp (5/64 : ℝ)*Real.exp (-mu (radius 8 (21/256 : ℝ))) ∧ (20549/10000 : ℝ) < (515361109157/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (21/256 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0005_exp_radius
  have hrNumeric : (989798485819/1000000000000 : ℝ) ≤ Real.exp (-21/2048 : ℝ) ∧ Real.exp (-21/2048 : ℝ) ≤ (49489924291/50000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (989798485819/1000000000000 : ℝ) ≤ (radius 8 (21/256 : ℝ)) ∧ (radius 8 (21/256 : ℝ)) ≤ (49489924291/50000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (21/256 : ℝ)) (989798485819/1000000000000 : ℝ) (49489924291/50000000000 : ℝ) (8904650617/62500000000 : ℝ) (3561860247/25000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (21/256 : ℝ)) (989798485819/1000000000000 : ℝ) (49489924291/50000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (21/256 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (989798485819/1000000000000 : ℝ) (49489924291/50000000000 : ℝ) (994899242909/1000000000000 : ℝ) (99489924291/100000000000 : ℝ) (497443083633/500000000000 : ℝ) (248721541817/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (21/256 : ℝ)) 1 (994899242909/1000000000000 : ℝ) (99489924291/100000000000 : ℝ) (497443083633/500000000000 : ℝ) (248721541817/250000000000 : ℝ) (994892705087/1000000000000 : ℝ) (994892705089/1000000000000 : ℝ) (497446352533/500000000000 : ℝ) (248723176267/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (21/256 : ℝ)) 2 (994892705087/1000000000000 : ℝ) (994892705089/1000000000000 : ℝ) (497446352533/500000000000 : ℝ) (248723176267/250000000000 : ℝ) (248723176269/250000000000 : ℝ) (994892705079/1000000000000 : ℝ) (248723176269/250000000000 : ℝ) (994892705079/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (21/256 : ℝ)) 3 (248723176269/250000000000 : ℝ) (994892705079/1000000000000 : ℝ) (248723176269/250000000000 : ℝ) (994892705079/1000000000000 : ℝ) (248723176269/250000000000 : ℝ) (994892705079/1000000000000 : ℝ) (248723176269/250000000000 : ℝ) (994892705079/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (21/256 : ℝ)) 4 (248723176269/250000000000 : ℝ) (994892705079/1000000000000 : ℝ) (248723176269/250000000000 : ℝ) (994892705079/1000000000000 : ℝ) (248723176269/250000000000 : ℝ) (994892705079/1000000000000 : ℝ) (248723176269/250000000000 : ℝ) (994892705079/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (21/256 : ℝ)) 5 (248723176269/250000000000 : ℝ) (994892705079/1000000000000 : ℝ) (248723176269/250000000000 : ℝ) (994892705079/1000000000000 : ℝ) (248723176269/250000000000 : ℝ) (994892705079/1000000000000 : ℝ) (248723176269/250000000000 : ℝ) (994892705079/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (21/256 : ℝ)) 6 (248723176269/250000000000 : ℝ) (994892705079/1000000000000 : ℝ) (248723176269/250000000000 : ℝ) (994892705079/1000000000000 : ℝ) (248723176269/250000000000 : ℝ) (994892705079/1000000000000 : ℝ) (248723176269/250000000000 : ℝ) (994892705079/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (21/256 : ℝ)) 7 (248723176269/250000000000 : ℝ) (994892705079/1000000000000 : ℝ) (248723176269/250000000000 : ℝ) (994892705079/1000000000000 : ℝ) (248723176269/250000000000 : ℝ) (994892705079/1000000000000 : ℝ) (248723176269/250000000000 : ℝ) (994892705079/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (21/256 : ℝ))) (8904650617/62500000000 : ℝ) (3561860247/25000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (21/256 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (8904650617/62500000000 : ℝ) (3561860247/25000000000 : ℝ) (71404650617/125000000000 : ℝ) (28561860247/50000000000 : ℝ) (377457825289/1000000000000 : ℝ) (3774578253/10000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (21/256 : ℝ))) 1 (71404650617/125000000000 : ℝ) (28561860247/50000000000 : ℝ) (377457825289/1000000000000 : ℝ) (3774578253/10000000000 : ℝ) (59293439389/125000000000 : ℝ) (5929343939/12500000000 : ℝ) (92869360523/200000000000 : ℝ) (7255418791/15625000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (21/256 : ℝ))) 2 (59293439389/125000000000 : ℝ) (5929343939/12500000000 : ℝ) (92869360523/200000000000 : ℝ) (7255418791/15625000000 : ℝ) (469347158863/1000000000000 : ℝ) (58668394859/125000000000 : ℝ) (234660260787/500000000000 : ℝ) (469320521583/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (21/256 : ℝ))) 3 (469347158863/1000000000000 : ℝ) (58668394859/125000000000 : ℝ) (234660260787/500000000000 : ℝ) (469320521583/1000000000000 : ℝ) (234666920109/500000000000 : ℝ) (117333460057/250000000000 : ℝ) (469333840029/1000000000000 : ℝ) (469333840039/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (21/256 : ℝ))) 4 (234666920109/500000000000 : ℝ) (117333460057/250000000000 : ℝ) (469333840029/1000000000000 : ℝ) (469333840039/1000000000000 : ℝ) (469333840123/1000000000000 : ℝ) (234666920067/500000000000 : ℝ) (469333840123/1000000000000 : ℝ) (234666920067/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (21/256 : ℝ))) 5 (469333840123/1000000000000 : ℝ) (234666920067/500000000000 : ℝ) (469333840123/1000000000000 : ℝ) (234666920067/500000000000 : ℝ) (469333840123/1000000000000 : ℝ) (234666920067/500000000000 : ℝ) (469333840123/1000000000000 : ℝ) (234666920067/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (21/256 : ℝ))) 6 (469333840123/1000000000000 : ℝ) (234666920067/500000000000 : ℝ) (469333840123/1000000000000 : ℝ) (234666920067/500000000000 : ℝ) (469333840123/1000000000000 : ℝ) (234666920067/500000000000 : ℝ) (469333840123/1000000000000 : ℝ) (234666920067/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (21/256 : ℝ))) 7 (469333840123/1000000000000 : ℝ) (234666920067/500000000000 : ℝ) (469333840123/1000000000000 : ℝ) (234666920067/500000000000 : ℝ) (469333840123/1000000000000 : ℝ) (234666920067/500000000000 : ℝ) (469333840123/1000000000000 : ℝ) (234666920067/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (21/256 : ℝ)) hmem 8 (248723176269/250000000000 : ℝ) (994892705079/1000000000000 : ℝ) (248723176269/250000000000 : ℝ) (994892705079/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (21/256 : ℝ))) hcmem 8 (469333840123/1000000000000 : ℝ) (234666920067/500000000000 : ℝ) (469333840123/1000000000000 : ℝ) (234666920067/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (21/256 : ℝ)) (248723176269/250000000000 : ℝ) (994892705079/1000000000000 : ℝ) (469333840123/1000000000000 : ℝ) (234666920067/500000000000 : ℝ) (741012441183/1000000000000 : ℝ) (741012441203/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0005_exp_lower
  have heNumeric : (515361109157/250000000000 : ℝ)/4 ≤ Real.exp (-662887441203/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (515361109157/250000000000 : ℝ)/4 ≤ Real.exp ((5/64 : ℝ)-(741012441203/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (5/64 : ℝ) (21/256 : ℝ) (741012441203/1000000000000 : ℝ) (515361109157/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0006; no trusted numerical premise.
theorem cover8_leaf0006_exp_radius : (199731625535875033/200000000000000000 : ℝ) ≤ Real.exp ((-11/1024 : ℝ)/8) ∧ Real.exp ((-11/1024 : ℝ)/8) ≤ (499329063839687583/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-11/1024 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0006_exp_lower : (184065768088680391/200000000000000000 : ℝ) ≤ Real.exp ((-332096950157/500000000000 : ℝ)/8) ∧ Real.exp ((-332096950157/500000000000 : ℝ)/8) ≤ (230082210110850489/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-332096950157/500000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0006_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2058753002269/1000000000000 : ℝ) ≤ 4*Real.exp (21/256 : ℝ)*Real.exp (-mu (radius 8 (11/128 : ℝ))) ∧ (20549/10000 : ℝ) < (2058753002269/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (11/128 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0006_exp_radius
  have hrNumeric : (989315303751/1000000000000 : ℝ) ≤ Real.exp (-11/1024 : ℝ) ∧ Real.exp (-11/1024 : ℝ) ≤ (123664412969/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (989315303751/1000000000000 : ℝ) ≤ (radius 8 (11/128 : ℝ)) ∧ (radius 8 (11/128 : ℝ)) ≤ (123664412969/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (11/128 : ℝ)) (989315303751/1000000000000 : ℝ) (123664412969/125000000000 : ℝ) (145791734203/1000000000000 : ℝ) (145791734211/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (11/128 : ℝ)) (989315303751/1000000000000 : ℝ) (123664412969/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (11/128 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (989315303751/1000000000000 : ℝ) (123664412969/125000000000 : ℝ) (1591452243/1600000000 : ℝ) (248664412969/250000000000 : ℝ) (994643304783/1000000000000 : ℝ) (198928660957/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (11/128 : ℝ)) 1 (1591452243/1600000000 : ℝ) (248664412969/250000000000 : ℝ) (994643304783/1000000000000 : ℝ) (198928660957/200000000000 : ℝ) (994650478329/1000000000000 : ℝ) (994650478331/1000000000000 : ℝ) (994650478303/1000000000000 : ℝ) (198930095661/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (11/128 : ℝ)) 2 (994650478329/1000000000000 : ℝ) (994650478331/1000000000000 : ℝ) (994650478303/1000000000000 : ℝ) (198930095661/200000000000 : ℝ) (248662619579/250000000000 : ℝ) (497325239159/500000000000 : ℝ) (198930095663/200000000000 : ℝ) (497325239159/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (11/128 : ℝ)) 3 (248662619579/250000000000 : ℝ) (497325239159/500000000000 : ℝ) (198930095663/200000000000 : ℝ) (497325239159/500000000000 : ℝ) (198930095663/200000000000 : ℝ) (497325239159/500000000000 : ℝ) (198930095663/200000000000 : ℝ) (497325239159/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (11/128 : ℝ)) 4 (198930095663/200000000000 : ℝ) (497325239159/500000000000 : ℝ) (198930095663/200000000000 : ℝ) (497325239159/500000000000 : ℝ) (198930095663/200000000000 : ℝ) (497325239159/500000000000 : ℝ) (198930095663/200000000000 : ℝ) (497325239159/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (11/128 : ℝ)) 5 (198930095663/200000000000 : ℝ) (497325239159/500000000000 : ℝ) (198930095663/200000000000 : ℝ) (497325239159/500000000000 : ℝ) (198930095663/200000000000 : ℝ) (497325239159/500000000000 : ℝ) (198930095663/200000000000 : ℝ) (497325239159/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (11/128 : ℝ)) 6 (198930095663/200000000000 : ℝ) (497325239159/500000000000 : ℝ) (198930095663/200000000000 : ℝ) (497325239159/500000000000 : ℝ) (198930095663/200000000000 : ℝ) (497325239159/500000000000 : ℝ) (198930095663/200000000000 : ℝ) (497325239159/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (11/128 : ℝ)) 7 (198930095663/200000000000 : ℝ) (497325239159/500000000000 : ℝ) (198930095663/200000000000 : ℝ) (497325239159/500000000000 : ℝ) (198930095663/200000000000 : ℝ) (497325239159/500000000000 : ℝ) (198930095663/200000000000 : ℝ) (497325239159/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (11/128 : ℝ))) (145791734203/1000000000000 : ℝ) (145791734211/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (11/128 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (145791734203/1000000000000 : ℝ) (145791734211/1000000000000 : ℝ) (572895867101/1000000000000 : ℝ) (286447933553/500000000000 : ℝ) (381826837981/1000000000000 : ℝ) (381826837993/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (11/128 : ℝ))) 1 (572895867101/1000000000000 : ℝ) (286447933553/500000000000 : ℝ) (381826837981/1000000000000 : ℝ) (381826837993/1000000000000 : ℝ) (477361352541/1000000000000 : ℝ) (9547227051/20000000000 : ℝ) (467703984831/1000000000000 : ℝ) (233851992421/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (11/128 : ℝ))) 2 (477361352541/1000000000000 : ℝ) (9547227051/20000000000 : ℝ) (467703984831/1000000000000 : ℝ) (233851992421/500000000000 : ℝ) (236266334343/500000000000 : ℝ) (59066583587/125000000000 : ℝ) (472507996533/1000000000000 : ℝ) (3691468723/7812500000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (11/128 : ℝ))) 3 (236266334343/500000000000 : ℝ) (59066583587/125000000000 : ℝ) (472507996533/1000000000000 : ℝ) (3691468723/7812500000 : ℝ) (472520332609/1000000000000 : ℝ) (23626016631/50000000000 : ℝ) (14766260389/31250000000 : ℝ) (472520332459/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (11/128 : ℝ))) 4 (472520332609/1000000000000 : ℝ) (23626016631/50000000000 : ℝ) (14766260389/31250000000 : ℝ) (472520332459/1000000000000 : ℝ) (29532520783/62500000000 : ℝ) (23626016627/50000000000 : ℝ) (29532520783/62500000000 : ℝ) (23626016627/50000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (11/128 : ℝ))) 5 (29532520783/62500000000 : ℝ) (23626016627/50000000000 : ℝ) (29532520783/62500000000 : ℝ) (23626016627/50000000000 : ℝ) (29532520783/62500000000 : ℝ) (23626016627/50000000000 : ℝ) (29532520783/62500000000 : ℝ) (23626016627/50000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (11/128 : ℝ))) 6 (29532520783/62500000000 : ℝ) (23626016627/50000000000 : ℝ) (29532520783/62500000000 : ℝ) (23626016627/50000000000 : ℝ) (29532520783/62500000000 : ℝ) (23626016627/50000000000 : ℝ) (29532520783/62500000000 : ℝ) (23626016627/50000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (11/128 : ℝ))) 7 (29532520783/62500000000 : ℝ) (23626016627/50000000000 : ℝ) (29532520783/62500000000 : ℝ) (23626016627/50000000000 : ℝ) (29532520783/62500000000 : ℝ) (23626016627/50000000000 : ℝ) (29532520783/62500000000 : ℝ) (23626016627/50000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (11/128 : ℝ)) hmem 8 (198930095663/200000000000 : ℝ) (497325239159/500000000000 : ℝ) (198930095663/200000000000 : ℝ) (497325239159/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (11/128 : ℝ))) hcmem 8 (29532520783/62500000000 : ℝ) (23626016627/50000000000 : ℝ) (29532520783/62500000000 : ℝ) (23626016627/50000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (11/128 : ℝ)) (198930095663/200000000000 : ℝ) (497325239159/500000000000 : ℝ) (29532520783/62500000000 : ℝ) (23626016627/50000000000 : ℝ) (186556287573/250000000000 : ℝ) (373112575157/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0006_exp_lower
  have heNumeric : (2058753002269/1000000000000 : ℝ)/4 ≤ Real.exp (-332096950157/500000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2058753002269/1000000000000 : ℝ)/4 ≤ Real.exp ((21/256 : ℝ)-(373112575157/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (21/256 : ℝ) (11/128 : ℝ) (373112575157/500000000000 : ℝ) (2058753002269/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0007; no trusted numerical premise.
theorem cover8_leaf0007_exp_radius : (199719435256923959/200000000000000000 : ℝ) ≤ Real.exp ((-23/2048 : ℝ)/8) ∧ Real.exp ((-23/2048 : ℝ)/8) ≤ (249649294071154949/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-23/2048 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0007_exp_lower : (184039455776446197/200000000000000000 : ℝ) ≤ Real.exp ((-83167198359/125000000000 : ℝ)/8) ∧ Real.exp ((-83167198359/125000000000 : ℝ)/8) ≤ (460098639441115493/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-83167198359/125000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0007_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (411279956013/200000000000 : ℝ) ≤ 4*Real.exp (11/128 : ℝ)*Real.exp (-mu (radius 8 (23/256 : ℝ))) ∧ (20549/10000 : ℝ) < (411279956013/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (23/256 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0007_exp_radius
  have hrNumeric : (494416178777/500000000000 : ℝ) ≤ Real.exp (-23/2048 : ℝ) ∧ Real.exp (-23/2048 : ℝ) ≤ (197766471511/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (494416178777/500000000000 : ℝ) ≤ (radius 8 (23/256 : ℝ)) ∧ (radius 8 (23/256 : ℝ)) ≤ (197766471511/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (23/256 : ℝ)) (494416178777/500000000000 : ℝ) (197766471511/200000000000 : ℝ) (1164313329/7812500000 : ℝ) (149032106119/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (23/256 : ℝ)) (494416178777/500000000000 : ℝ) (197766471511/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (23/256 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (494416178777/500000000000 : ℝ) (197766471511/200000000000 : ℝ) (994416178777/1000000000000 : ℝ) (497208089389/500000000000 : ℝ) (198880100317/200000000000 : ℝ) (994400501587/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (23/256 : ℝ)) 1 (994416178777/1000000000000 : ℝ) (497208089389/500000000000 : ℝ) (198880100317/200000000000 : ℝ) (994400501587/1000000000000 : ℝ) (994408340181/1000000000000 : ℝ) (994408340183/1000000000000 : ℝ) (19888166803/20000000000 : ℝ) (124301042519/125000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (23/256 : ℝ)) 2 (994408340181/1000000000000 : ℝ) (994408340183/1000000000000 : ℝ) (19888166803/20000000000 : ℝ) (124301042519/125000000000 : ℝ) (198881668033/200000000000 : ℝ) (124301042521/125000000000 : ℝ) (198881668033/200000000000 : ℝ) (124301042521/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (23/256 : ℝ)) 3 (198881668033/200000000000 : ℝ) (124301042521/125000000000 : ℝ) (198881668033/200000000000 : ℝ) (124301042521/125000000000 : ℝ) (198881668033/200000000000 : ℝ) (124301042521/125000000000 : ℝ) (198881668033/200000000000 : ℝ) (124301042521/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (23/256 : ℝ)) 4 (198881668033/200000000000 : ℝ) (124301042521/125000000000 : ℝ) (198881668033/200000000000 : ℝ) (124301042521/125000000000 : ℝ) (198881668033/200000000000 : ℝ) (124301042521/125000000000 : ℝ) (198881668033/200000000000 : ℝ) (124301042521/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (23/256 : ℝ)) 5 (198881668033/200000000000 : ℝ) (124301042521/125000000000 : ℝ) (198881668033/200000000000 : ℝ) (124301042521/125000000000 : ℝ) (198881668033/200000000000 : ℝ) (124301042521/125000000000 : ℝ) (198881668033/200000000000 : ℝ) (124301042521/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (23/256 : ℝ)) 6 (198881668033/200000000000 : ℝ) (124301042521/125000000000 : ℝ) (198881668033/200000000000 : ℝ) (124301042521/125000000000 : ℝ) (198881668033/200000000000 : ℝ) (124301042521/125000000000 : ℝ) (198881668033/200000000000 : ℝ) (124301042521/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (23/256 : ℝ)) 7 (198881668033/200000000000 : ℝ) (124301042521/125000000000 : ℝ) (198881668033/200000000000 : ℝ) (124301042521/125000000000 : ℝ) (198881668033/200000000000 : ℝ) (124301042521/125000000000 : ℝ) (198881668033/200000000000 : ℝ) (124301042521/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (23/256 : ℝ))) (1164313329/7812500000 : ℝ) (149032106119/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (23/256 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (1164313329/7812500000 : ℝ) (149032106119/1000000000000 : ℝ) (8976813329/15625000000 : ℝ) (28725802653/50000000000 : ℝ) (193023383371/500000000000 : ℝ) (12063961461/31250000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (23/256 : ℝ))) 1 (8976813329/15625000000 : ℝ) (28725802653/50000000000 : ℝ) (193023383371/500000000000 : ℝ) (12063961461/31250000000 : ℝ) (480281409899/1000000000000 : ℝ) (240140704953/500000000000 : ℝ) (470945925477/1000000000000 : ℝ) (235472962743/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (23/256 : ℝ))) 2 (480281409899/1000000000000 : ℝ) (240140704953/500000000000 : ℝ) (470945925477/1000000000000 : ℝ) (235472962743/500000000000 : ℝ) (59451708461/125000000000 : ℝ) (29725854231/62500000000 : ℝ) (475590762183/1000000000000 : ℝ) (29724422637/62500000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (23/256 : ℝ))) 3 (59451708461/125000000000 : ℝ) (29725854231/62500000000 : ℝ) (475590762183/1000000000000 : ℝ) (29724422637/62500000000 : ℝ) (95120442987/200000000000 : ℝ) (14862569217/31250000000 : ℝ) (475602214797/1000000000000 : ℝ) (475602214807/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (23/256 : ℝ))) 4 (95120442987/200000000000 : ℝ) (14862569217/31250000000 : ℝ) (475602214797/1000000000000 : ℝ) (475602214807/1000000000000 : ℝ) (237801107433/500000000000 : ℝ) (118900553719/250000000000 : ℝ) (95120442973/200000000000 : ℝ) (118900553719/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (23/256 : ℝ))) 5 (237801107433/500000000000 : ℝ) (118900553719/250000000000 : ℝ) (95120442973/200000000000 : ℝ) (118900553719/250000000000 : ℝ) (95120442973/200000000000 : ℝ) (118900553719/250000000000 : ℝ) (95120442973/200000000000 : ℝ) (118900553719/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (23/256 : ℝ))) 6 (95120442973/200000000000 : ℝ) (118900553719/250000000000 : ℝ) (95120442973/200000000000 : ℝ) (118900553719/250000000000 : ℝ) (95120442973/200000000000 : ℝ) (118900553719/250000000000 : ℝ) (95120442973/200000000000 : ℝ) (118900553719/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (23/256 : ℝ))) 7 (95120442973/200000000000 : ℝ) (118900553719/250000000000 : ℝ) (95120442973/200000000000 : ℝ) (118900553719/250000000000 : ℝ) (95120442973/200000000000 : ℝ) (118900553719/250000000000 : ℝ) (95120442973/200000000000 : ℝ) (118900553719/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (23/256 : ℝ)) hmem 8 (198881668033/200000000000 : ℝ) (124301042521/125000000000 : ℝ) (198881668033/200000000000 : ℝ) (124301042521/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (23/256 : ℝ))) hcmem 8 (95120442973/200000000000 : ℝ) (118900553719/250000000000 : ℝ) (95120442973/200000000000 : ℝ) (118900553719/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (23/256 : ℝ)) (198881668033/200000000000 : ℝ) (124301042521/125000000000 : ℝ) (95120442973/200000000000 : ℝ) (118900553719/250000000000 : ℝ) (751275086851/1000000000000 : ℝ) (93909385859/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0007_exp_lower
  have heNumeric : (411279956013/200000000000 : ℝ)/4 ≤ Real.exp (-83167198359/125000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (411279956013/200000000000 : ℝ)/4 ≤ Real.exp ((11/128 : ℝ)-(93909385859/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (11/128 : ℝ) (23/256 : ℝ) (93909385859/125000000000 : ℝ) (411279956013/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0008; no trusted numerical premise.
theorem cover8_leaf0008_exp_radius : (998566701982280441/1000000000000000000 : ℝ) ≤ Real.exp ((-47/4096 : ℝ)/8) ∧ Real.exp ((-47/4096 : ℝ)/8) ≤ (499283350991140221/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-47/4096 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0008_exp_lower : (230090687095997907/250000000000000000 : ℝ) ≤ Real.exp ((-663899159439/1000000000000 : ℝ)/8) ∧ Real.exp ((-663899159439/1000000000000 : ℝ)/8) ≤ (920362748383991629/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-663899159439/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0008_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2059359890363/1000000000000 : ℝ) ≤ 4*Real.exp (23/256 : ℝ)*Real.exp (-mu (radius 8 (47/512 : ℝ))) ∧ (20549/10000 : ℝ) < (2059359890363/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (47/512 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0008_exp_radius
  have hrNumeric : (988590972871/1000000000000 : ℝ) ≤ Real.exp (-47/4096 : ℝ) ∧ Real.exp (-47/4096 : ℝ) ≤ (123573871609/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (988590972871/1000000000000 : ℝ) ≤ (radius 8 (47/512 : ℝ)) ∧ (radius 8 (47/512 : ℝ)) ≤ (123573871609/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (47/512 : ℝ)) (988590972871/1000000000000 : ℝ) (123573871609/125000000000 : ℝ) (37656248117/250000000000 : ℝ) (6024999699/40000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (47/512 : ℝ)) (988590972871/1000000000000 : ℝ) (123573871609/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (47/512 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (988590972871/1000000000000 : ℝ) (123573871609/125000000000 : ℝ) (198859097287/200000000000 : ℝ) (248573871609/250000000000 : ℝ) (497139561107/500000000000 : ℝ) (198855824443/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (47/512 : ℝ)) 1 (198859097287/200000000000 : ℝ) (248573871609/250000000000 : ℝ) (497139561107/500000000000 : ℝ) (198855824443/200000000000 : ℝ) (248571826081/250000000000 : ℝ) (497143652163/500000000000 : ℝ) (99428730429/100000000000 : ℝ) (248571826073/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (47/512 : ℝ)) 2 (248571826081/250000000000 : ℝ) (497143652163/500000000000 : ℝ) (99428730429/100000000000 : ℝ) (248571826073/250000000000 : ℝ) (994287304307/1000000000000 : ℝ) (994287304309/1000000000000 : ℝ) (497143652153/500000000000 : ℝ) (994287304309/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (47/512 : ℝ)) 3 (994287304307/1000000000000 : ℝ) (994287304309/1000000000000 : ℝ) (497143652153/500000000000 : ℝ) (994287304309/1000000000000 : ℝ) (497143652153/500000000000 : ℝ) (994287304309/1000000000000 : ℝ) (497143652153/500000000000 : ℝ) (994287304309/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (47/512 : ℝ)) 4 (497143652153/500000000000 : ℝ) (994287304309/1000000000000 : ℝ) (497143652153/500000000000 : ℝ) (994287304309/1000000000000 : ℝ) (497143652153/500000000000 : ℝ) (994287304309/1000000000000 : ℝ) (497143652153/500000000000 : ℝ) (994287304309/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (47/512 : ℝ)) 5 (497143652153/500000000000 : ℝ) (994287304309/1000000000000 : ℝ) (497143652153/500000000000 : ℝ) (994287304309/1000000000000 : ℝ) (497143652153/500000000000 : ℝ) (994287304309/1000000000000 : ℝ) (497143652153/500000000000 : ℝ) (994287304309/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (47/512 : ℝ)) 6 (497143652153/500000000000 : ℝ) (994287304309/1000000000000 : ℝ) (497143652153/500000000000 : ℝ) (994287304309/1000000000000 : ℝ) (497143652153/500000000000 : ℝ) (994287304309/1000000000000 : ℝ) (497143652153/500000000000 : ℝ) (994287304309/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (47/512 : ℝ)) 7 (497143652153/500000000000 : ℝ) (994287304309/1000000000000 : ℝ) (497143652153/500000000000 : ℝ) (994287304309/1000000000000 : ℝ) (497143652153/500000000000 : ℝ) (994287304309/1000000000000 : ℝ) (497143652153/500000000000 : ℝ) (994287304309/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (47/512 : ℝ))) (37656248117/250000000000 : ℝ) (6024999699/40000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (47/512 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (37656248117/250000000000 : ℝ) (6024999699/40000000000 : ℝ) (287656248117/500000000000 : ℝ) (287656248119/500000000000 : ℝ) (194052178851/500000000000 : ℝ) (24256522357/62500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (47/512 : ℝ))) 1 (287656248117/500000000000 : ℝ) (287656248119/500000000000 : ℝ) (194052178851/500000000000 : ℝ) (24256522357/62500000000 : ℝ) (60213553371/125000000000 : ℝ) (19268337079/40000000000 : ℝ) (59065811657/125000000000 : ℝ) (29532905829/62500000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (47/512 : ℝ))) 2 (60213553371/125000000000 : ℝ) (19268337079/40000000000 : ℝ) (59065811657/125000000000 : ℝ) (29532905829/62500000000 : ℝ) (29819841257/62500000000 : ℝ) (11927936503/25000000000 : ℝ) (119273842943/250000000000 : ℝ) (477095371781/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (47/512 : ℝ))) 3 (29819841257/62500000000 : ℝ) (11927936503/25000000000 : ℝ) (119273842943/250000000000 : ℝ) (477095371781/1000000000000 : ℝ) (238553207971/500000000000 : ℝ) (477106415951/1000000000000 : ℝ) (238553207907/500000000000 : ℝ) (477106415823/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (47/512 : ℝ))) 4 (238553207971/500000000000 : ℝ) (477106415951/1000000000000 : ℝ) (238553207907/500000000000 : ℝ) (477106415823/1000000000000 : ℝ) (238553207939/500000000000 : ℝ) (477106415887/1000000000000 : ℝ) (477106415877/1000000000000 : ℝ) (477106415887/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (47/512 : ℝ))) 5 (238553207939/500000000000 : ℝ) (477106415887/1000000000000 : ℝ) (477106415877/1000000000000 : ℝ) (477106415887/1000000000000 : ℝ) (477106415877/1000000000000 : ℝ) (477106415887/1000000000000 : ℝ) (477106415877/1000000000000 : ℝ) (477106415887/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (47/512 : ℝ))) 6 (477106415877/1000000000000 : ℝ) (477106415887/1000000000000 : ℝ) (477106415877/1000000000000 : ℝ) (477106415887/1000000000000 : ℝ) (477106415877/1000000000000 : ℝ) (477106415887/1000000000000 : ℝ) (477106415877/1000000000000 : ℝ) (477106415887/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (47/512 : ℝ))) 7 (477106415877/1000000000000 : ℝ) (477106415887/1000000000000 : ℝ) (477106415877/1000000000000 : ℝ) (477106415887/1000000000000 : ℝ) (477106415877/1000000000000 : ℝ) (477106415887/1000000000000 : ℝ) (477106415877/1000000000000 : ℝ) (477106415887/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (47/512 : ℝ)) hmem 8 (497143652153/500000000000 : ℝ) (994287304309/1000000000000 : ℝ) (497143652153/500000000000 : ℝ) (994287304309/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (47/512 : ℝ))) hcmem 8 (477106415877/1000000000000 : ℝ) (477106415887/1000000000000 : ℝ) (477106415877/1000000000000 : ℝ) (477106415887/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (47/512 : ℝ)) (497143652153/500000000000 : ℝ) (994287304309/1000000000000 : ℝ) (477106415877/1000000000000 : ℝ) (477106415887/1000000000000 : ℝ) (37687145471/50000000000 : ℝ) (753742909439/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0008_exp_lower
  have heNumeric : (2059359890363/1000000000000 : ℝ)/4 ≤ Real.exp (-663899159439/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2059359890363/1000000000000 : ℝ)/4 ≤ Real.exp ((23/256 : ℝ)-(753742909439/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (23/256 : ℝ) (47/512 : ℝ) (753742909439/1000000000000 : ℝ) (2059359890363/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0009; no trusted numerical premise.
theorem cover8_leaf0009_exp_radius : (998536228609928799/1000000000000000000 : ℝ) ≤ Real.exp ((-3/256 : ℝ)/8) ∧ Real.exp ((-3/256 : ℝ)/8) ≤ (1248170285762411/1250000000000000 : ℝ) := by
  have h := exp_small_bounds ((-3/256 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0009_exp_lower : (920307701520971023/1000000000000000000 : ℝ) ≤ Real.exp ((-332188826731/500000000000 : ℝ)/8) ∧ Real.exp ((-332188826731/500000000000 : ℝ)/8) ≤ (57519231345060689/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-332188826731/500000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0009_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2058374734679/1000000000000 : ℝ) ≤ 4*Real.exp (47/512 : ℝ)*Real.exp (-mu (radius 8 (3/32 : ℝ))) ∧ (20549/10000 : ℝ) < (2058374734679/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (3/32 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0009_exp_radius
  have hrNumeric : (988349647113/1000000000000 : ℝ) ≤ Real.exp (-3/256 : ℝ) ∧ Real.exp (-3/256 : ℝ) ≤ (494174823557/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (988349647113/1000000000000 : ℝ) ≤ (radius 8 (3/32 : ℝ)) ∧ (radius 8 (3/32 : ℝ)) ≤ (494174823557/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (3/32 : ℝ)) (988349647113/1000000000000 : ℝ) (494174823557/500000000000 : ℝ) (152200443657/1000000000000 : ℝ) (30440088733/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (3/32 : ℝ)) (988349647113/1000000000000 : ℝ) (494174823557/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (3/32 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (988349647113/1000000000000 : ℝ) (494174823557/500000000000 : ℝ) (248543705889/250000000000 : ℝ) (994174823557/1000000000000 : ℝ) (497078878829/500000000000 : ℝ) (49707887883/50000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (3/32 : ℝ)) 1 (248543705889/250000000000 : ℝ) (994174823557/1000000000000 : ℝ) (497078878829/500000000000 : ℝ) (49707887883/50000000000 : ℝ) (994166290607/1000000000000 : ℝ) (994166290609/1000000000000 : ℝ) (99416629057/100000000000 : ℝ) (248541572643/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (3/32 : ℝ)) 2 (994166290607/1000000000000 : ℝ) (994166290609/1000000000000 : ℝ) (99416629057/100000000000 : ℝ) (248541572643/250000000000 : ℝ) (248541572647/250000000000 : ℝ) (994166290591/1000000000000 : ℝ) (248541572647/250000000000 : ℝ) (994166290591/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (3/32 : ℝ)) 3 (248541572647/250000000000 : ℝ) (994166290591/1000000000000 : ℝ) (248541572647/250000000000 : ℝ) (994166290591/1000000000000 : ℝ) (248541572647/250000000000 : ℝ) (994166290591/1000000000000 : ℝ) (248541572647/250000000000 : ℝ) (994166290591/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (3/32 : ℝ)) 4 (248541572647/250000000000 : ℝ) (994166290591/1000000000000 : ℝ) (248541572647/250000000000 : ℝ) (994166290591/1000000000000 : ℝ) (248541572647/250000000000 : ℝ) (994166290591/1000000000000 : ℝ) (248541572647/250000000000 : ℝ) (994166290591/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (3/32 : ℝ)) 5 (248541572647/250000000000 : ℝ) (994166290591/1000000000000 : ℝ) (248541572647/250000000000 : ℝ) (994166290591/1000000000000 : ℝ) (248541572647/250000000000 : ℝ) (994166290591/1000000000000 : ℝ) (248541572647/250000000000 : ℝ) (994166290591/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (3/32 : ℝ)) 6 (248541572647/250000000000 : ℝ) (994166290591/1000000000000 : ℝ) (248541572647/250000000000 : ℝ) (994166290591/1000000000000 : ℝ) (248541572647/250000000000 : ℝ) (994166290591/1000000000000 : ℝ) (248541572647/250000000000 : ℝ) (994166290591/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (3/32 : ℝ)) 7 (248541572647/250000000000 : ℝ) (994166290591/1000000000000 : ℝ) (248541572647/250000000000 : ℝ) (994166290591/1000000000000 : ℝ) (248541572647/250000000000 : ℝ) (994166290591/1000000000000 : ℝ) (248541572647/250000000000 : ℝ) (994166290591/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (3/32 : ℝ))) (152200443657/1000000000000 : ℝ) (30440088733/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (3/32 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (152200443657/1000000000000 : ℝ) (30440088733/200000000000 : ℝ) (144025055457/250000000000 : ℝ) (576100221833/1000000000000 : ℝ) (195064376333/500000000000 : ℝ) (390128752677/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (3/32 : ℝ))) 1 (144025055457/250000000000 : ℝ) (576100221833/1000000000000 : ℝ) (195064376333/500000000000 : ℝ) (390128752677/1000000000000 : ℝ) (483114487247/1000000000000 : ℝ) (96622897451/200000000000 : ℝ) (474081491889/1000000000000 : ℝ) (474081491899/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (3/32 : ℝ))) 2 (483114487247/1000000000000 : ℝ) (96622897451/200000000000 : ℝ) (474081491889/1000000000000 : ℝ) (474081491899/1000000000000 : ℝ) (7478093587/15625000000 : ℝ) (478597989577/1000000000000 : ℝ) (119644169537/250000000000 : ℝ) (239288339079/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (3/32 : ℝ))) 3 (7478093587/15625000000 : ℝ) (478597989577/1000000000000 : ℝ) (119644169537/250000000000 : ℝ) (239288339079/500000000000 : ℝ) (239293666929/500000000000 : ℝ) (119646833467/250000000000 : ℝ) (478587333739/1000000000000 : ℝ) (478587333749/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (3/32 : ℝ))) 4 (239293666929/500000000000 : ℝ) (119646833467/250000000000 : ℝ) (478587333739/1000000000000 : ℝ) (478587333749/1000000000000 : ℝ) (239293666899/500000000000 : ℝ) (478587333809/1000000000000 : ℝ) (239293666899/500000000000 : ℝ) (478587333809/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (3/32 : ℝ))) 5 (239293666899/500000000000 : ℝ) (478587333809/1000000000000 : ℝ) (239293666899/500000000000 : ℝ) (478587333809/1000000000000 : ℝ) (239293666899/500000000000 : ℝ) (478587333809/1000000000000 : ℝ) (239293666899/500000000000 : ℝ) (478587333809/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (3/32 : ℝ))) 6 (239293666899/500000000000 : ℝ) (478587333809/1000000000000 : ℝ) (239293666899/500000000000 : ℝ) (478587333809/1000000000000 : ℝ) (239293666899/500000000000 : ℝ) (478587333809/1000000000000 : ℝ) (239293666899/500000000000 : ℝ) (478587333809/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (3/32 : ℝ))) 7 (239293666899/500000000000 : ℝ) (478587333809/1000000000000 : ℝ) (239293666899/500000000000 : ℝ) (478587333809/1000000000000 : ℝ) (239293666899/500000000000 : ℝ) (478587333809/1000000000000 : ℝ) (239293666899/500000000000 : ℝ) (478587333809/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (3/32 : ℝ)) hmem 8 (248541572647/250000000000 : ℝ) (994166290591/1000000000000 : ℝ) (248541572647/250000000000 : ℝ) (994166290591/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (3/32 : ℝ))) hcmem 8 (239293666899/500000000000 : ℝ) (478587333809/1000000000000 : ℝ) (239293666899/500000000000 : ℝ) (478587333809/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (3/32 : ℝ)) (248541572647/250000000000 : ℝ) (994166290591/1000000000000 : ℝ) (239293666899/500000000000 : ℝ) (478587333809/1000000000000 : ℝ) (756174528441/1000000000000 : ℝ) (378087264231/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0009_exp_lower
  have heNumeric : (2058374734679/1000000000000 : ℝ)/4 ≤ Real.exp (-332188826731/500000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2058374734679/1000000000000 : ℝ)/4 ≤ Real.exp ((47/512 : ℝ)-(378087264231/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (47/512 : ℝ) (3/32 : ℝ) (378087264231/500000000000 : ℝ) (2058374734679/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0010; no trusted numerical premise.
theorem cover8_leaf0010_exp_radius : (124813219520942061/125000000000000000 : ℝ) ≤ Real.exp ((-49/4096 : ℝ)/8) ∧ Real.exp ((-49/4096 : ℝ)/8) ≤ (998505756167536489/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-49/4096 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0010_exp_lower : (230064167716829007/250000000000000000 : ℝ) ≤ Real.exp ((-664821262211/1000000000000 : ℝ)/8) ∧ Real.exp ((-664821262211/1000000000000 : ℝ)/8) ≤ (920256670867316029/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-664821262211/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0010_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (102873091207/50000000000 : ℝ) ≤ 4*Real.exp (3/32 : ℝ)*Real.exp (-mu (radius 8 (49/512 : ℝ))) ∧ (20549/10000 : ℝ) < (102873091207/50000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (49/512 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0010_exp_radius
  have hrNumeric : (197621676053/200000000000 : ℝ) ≤ Real.exp (-49/4096 : ℝ) ∧ Real.exp (-49/4096 : ℝ) ≤ (494054190133/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (197621676053/200000000000 : ℝ) ≤ (radius 8 (49/512 : ℝ)) ∧ (radius 8 (49/512 : ℝ)) ≤ (494054190133/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (49/512 : ℝ)) (197621676053/200000000000 : ℝ) (494054190133/500000000000 : ℝ) (15375899599/100000000000 : ℝ) (76879497999/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (49/512 : ℝ)) (197621676053/200000000000 : ℝ) (494054190133/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (49/512 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (197621676053/200000000000 : ℝ) (494054190133/500000000000 : ℝ) (248513547533/250000000000 : ℝ) (994054190133/1000000000000 : ℝ) (994036407917/1000000000000 : ℝ) (497018203959/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (49/512 : ℝ)) 1 (248513547533/250000000000 : ℝ) (994054190133/1000000000000 : ℝ) (994036407917/1000000000000 : ℝ) (497018203959/500000000000 : ℝ) (62127831189/62500000000 : ℝ) (497022649513/500000000000 : ℝ) (124255662373/125000000000 : ℝ) (497022649493/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (49/512 : ℝ)) 2 (62127831189/62500000000 : ℝ) (497022649513/500000000000 : ℝ) (124255662373/125000000000 : ℝ) (497022649493/500000000000 : ℝ) (248511324751/250000000000 : ℝ) (497022649503/500000000000 : ℝ) (994045299003/1000000000000 : ℝ) (497022649503/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (49/512 : ℝ)) 3 (248511324751/250000000000 : ℝ) (497022649503/500000000000 : ℝ) (994045299003/1000000000000 : ℝ) (497022649503/500000000000 : ℝ) (994045299003/1000000000000 : ℝ) (497022649503/500000000000 : ℝ) (994045299003/1000000000000 : ℝ) (497022649503/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (49/512 : ℝ)) 4 (994045299003/1000000000000 : ℝ) (497022649503/500000000000 : ℝ) (994045299003/1000000000000 : ℝ) (497022649503/500000000000 : ℝ) (994045299003/1000000000000 : ℝ) (497022649503/500000000000 : ℝ) (994045299003/1000000000000 : ℝ) (497022649503/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (49/512 : ℝ)) 5 (994045299003/1000000000000 : ℝ) (497022649503/500000000000 : ℝ) (994045299003/1000000000000 : ℝ) (497022649503/500000000000 : ℝ) (994045299003/1000000000000 : ℝ) (497022649503/500000000000 : ℝ) (994045299003/1000000000000 : ℝ) (497022649503/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (49/512 : ℝ)) 6 (994045299003/1000000000000 : ℝ) (497022649503/500000000000 : ℝ) (994045299003/1000000000000 : ℝ) (497022649503/500000000000 : ℝ) (994045299003/1000000000000 : ℝ) (497022649503/500000000000 : ℝ) (994045299003/1000000000000 : ℝ) (497022649503/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (49/512 : ℝ)) 7 (994045299003/1000000000000 : ℝ) (497022649503/500000000000 : ℝ) (994045299003/1000000000000 : ℝ) (497022649503/500000000000 : ℝ) (994045299003/1000000000000 : ℝ) (497022649503/500000000000 : ℝ) (994045299003/1000000000000 : ℝ) (497022649503/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (49/512 : ℝ))) (15375899599/100000000000 : ℝ) (76879497999/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (49/512 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (15375899599/100000000000 : ℝ) (76879497999/500000000000 : ℝ) (115375899599/200000000000 : ℝ) (576879497999/1000000000000 : ℝ) (392121149633/1000000000000 : ℝ) (98030287411/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (49/512 : ℝ))) 1 (115375899599/200000000000 : ℝ) (576879497999/1000000000000 : ℝ) (392121149633/1000000000000 : ℝ) (98030287411/250000000000 : ℝ) (242250161907/500000000000 : ℝ) (242250161911/500000000000 : ℝ) (475611871123/1000000000000 : ℝ) (118902967783/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (49/512 : ℝ))) 2 (242250161907/500000000000 : ℝ) (242250161911/500000000000 : ℝ) (475611871123/1000000000000 : ℝ) (118902967783/250000000000 : ℝ) (120014024367/250000000000 : ℝ) (480056097477/1000000000000 : ℝ) (480035525319/1000000000000 : ℝ) (480035525329/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (49/512 : ℝ))) 3 (120014024367/250000000000 : ℝ) (480056097477/1000000000000 : ℝ) (480035525319/1000000000000 : ℝ) (480035525329/1000000000000 : ℝ) (480045811393/1000000000000 : ℝ) (480045811403/1000000000000 : ℝ) (480045811283/1000000000000 : ℝ) (480045811293/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (49/512 : ℝ))) 4 (480045811393/1000000000000 : ℝ) (480045811403/1000000000000 : ℝ) (480045811283/1000000000000 : ℝ) (480045811293/1000000000000 : ℝ) (240022905669/500000000000 : ℝ) (120011452837/250000000000 : ℝ) (480045811337/1000000000000 : ℝ) (120011452837/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (49/512 : ℝ))) 5 (240022905669/500000000000 : ℝ) (120011452837/250000000000 : ℝ) (480045811337/1000000000000 : ℝ) (120011452837/250000000000 : ℝ) (480045811337/1000000000000 : ℝ) (120011452837/250000000000 : ℝ) (480045811337/1000000000000 : ℝ) (120011452837/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (49/512 : ℝ))) 6 (480045811337/1000000000000 : ℝ) (120011452837/250000000000 : ℝ) (480045811337/1000000000000 : ℝ) (120011452837/250000000000 : ℝ) (480045811337/1000000000000 : ℝ) (120011452837/250000000000 : ℝ) (480045811337/1000000000000 : ℝ) (120011452837/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (49/512 : ℝ))) 7 (480045811337/1000000000000 : ℝ) (120011452837/250000000000 : ℝ) (480045811337/1000000000000 : ℝ) (120011452837/250000000000 : ℝ) (480045811337/1000000000000 : ℝ) (120011452837/250000000000 : ℝ) (480045811337/1000000000000 : ℝ) (120011452837/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (49/512 : ℝ)) hmem 8 (994045299003/1000000000000 : ℝ) (497022649503/500000000000 : ℝ) (994045299003/1000000000000 : ℝ) (497022649503/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (49/512 : ℝ))) hcmem 8 (480045811337/1000000000000 : ℝ) (120011452837/250000000000 : ℝ) (480045811337/1000000000000 : ℝ) (120011452837/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (49/512 : ℝ)) (994045299003/1000000000000 : ℝ) (497022649503/500000000000 : ℝ) (480045811337/1000000000000 : ℝ) (120011452837/250000000000 : ℝ) (75857126219/100000000000 : ℝ) (758571262211/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0010_exp_lower
  have heNumeric : (102873091207/50000000000 : ℝ)/4 ≤ Real.exp (-664821262211/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (102873091207/50000000000 : ℝ)/4 ≤ Real.exp ((3/32 : ℝ)-(758571262211/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (3/32 : ℝ) (49/512 : ℝ) (758571262211/1000000000000 : ℝ) (102873091207/50000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0011; no trusted numerical premise.
theorem cover8_leaf0011_exp_radius : (998475284655075129/1000000000000000000 : ℝ) ≤ Real.exp ((-25/2048 : ℝ)/8) ∧ Real.exp ((-25/2048 : ℝ)/8) ≤ (99847528465507513/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-25/2048 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0011_exp_lower : (230052378159635139/250000000000000000 : ℝ) ≤ Real.exp ((-83153903737/125000000000 : ℝ)/8) ∧ Real.exp ((-83153903737/125000000000 : ℝ)/8) ≤ (920209512638540557/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-83153903737/125000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0011_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1028309252079/500000000000 : ℝ) ≤ 4*Real.exp (49/512 : ℝ)*Real.exp (-mu (radius 8 (25/256 : ℝ))) ∧ (20549/10000 : ℝ) < (1028309252079/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (25/256 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0011_exp_radius
  have hrNumeric : (493933586157/500000000000 : ℝ) ≤ Real.exp (-25/2048 : ℝ) ∧ Real.exp (-25/2048 : ℝ) ≤ (197573434463/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (493933586157/500000000000 : ℝ) ≤ (radius 8 (25/256 : ℝ)) ∧ (radius 8 (25/256 : ℝ)) ≤ (197573434463/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (25/256 : ℝ)) (493933586157/500000000000 : ℝ) (197573434463/200000000000 : ℝ) (155301158599/1000000000000 : ℝ) (77650579303/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (25/256 : ℝ)) (493933586157/500000000000 : ℝ) (197573434463/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (25/256 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (493933586157/500000000000 : ℝ) (197573434463/200000000000 : ℝ) (993933586157/1000000000000 : ℝ) (496966793079/500000000000 : ℝ) (248478768247/250000000000 : ℝ) (99391507299/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (25/256 : ℝ)) 1 (993933586157/1000000000000 : ℝ) (496966793079/500000000000 : ℝ) (248478768247/250000000000 : ℝ) (99391507299/100000000000 : ℝ) (248481082393/250000000000 : ℝ) (496962164787/500000000000 : ℝ) (993924329529/1000000000000 : ℝ) (993924329531/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (25/256 : ℝ)) 2 (248481082393/250000000000 : ℝ) (496962164787/500000000000 : ℝ) (993924329529/1000000000000 : ℝ) (993924329531/1000000000000 : ℝ) (19878486591/20000000000 : ℝ) (993924329553/1000000000000 : ℝ) (19878486591/20000000000 : ℝ) (993924329553/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (25/256 : ℝ)) 3 (19878486591/20000000000 : ℝ) (993924329553/1000000000000 : ℝ) (19878486591/20000000000 : ℝ) (993924329553/1000000000000 : ℝ) (19878486591/20000000000 : ℝ) (993924329553/1000000000000 : ℝ) (19878486591/20000000000 : ℝ) (993924329553/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (25/256 : ℝ)) 4 (19878486591/20000000000 : ℝ) (993924329553/1000000000000 : ℝ) (19878486591/20000000000 : ℝ) (993924329553/1000000000000 : ℝ) (19878486591/20000000000 : ℝ) (993924329553/1000000000000 : ℝ) (19878486591/20000000000 : ℝ) (993924329553/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (25/256 : ℝ)) 5 (19878486591/20000000000 : ℝ) (993924329553/1000000000000 : ℝ) (19878486591/20000000000 : ℝ) (993924329553/1000000000000 : ℝ) (19878486591/20000000000 : ℝ) (993924329553/1000000000000 : ℝ) (19878486591/20000000000 : ℝ) (993924329553/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (25/256 : ℝ)) 6 (19878486591/20000000000 : ℝ) (993924329553/1000000000000 : ℝ) (19878486591/20000000000 : ℝ) (993924329553/1000000000000 : ℝ) (19878486591/20000000000 : ℝ) (993924329553/1000000000000 : ℝ) (19878486591/20000000000 : ℝ) (993924329553/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (25/256 : ℝ)) 7 (19878486591/20000000000 : ℝ) (993924329553/1000000000000 : ℝ) (19878486591/20000000000 : ℝ) (993924329553/1000000000000 : ℝ) (19878486591/20000000000 : ℝ) (993924329553/1000000000000 : ℝ) (19878486591/20000000000 : ℝ) (993924329553/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (25/256 : ℝ))) (155301158599/1000000000000 : ℝ) (77650579303/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (25/256 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (155301158599/1000000000000 : ℝ) (77650579303/500000000000 : ℝ) (577650579299/1000000000000 : ℝ) (577650579303/1000000000000 : ℝ) (197041339951/500000000000 : ℝ) (49260334989/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (25/256 : ℝ))) 1 (577650579299/1000000000000 : ℝ) (577650579303/1000000000000 : ℝ) (197041339951/500000000000 : ℝ) (49260334989/125000000000 : ℝ) (607333287/1250000000 : ℝ) (60733328701/125000000000 : ℝ) (477118526507/1000000000000 : ℝ) (119279631629/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (25/256 : ℝ))) 2 (607333287/1250000000 : ℝ) (60733328701/125000000000 : ℝ) (477118526507/1000000000000 : ℝ) (119279631629/250000000000 : ℝ) (481492578053/1000000000000 : ℝ) (240746289031/500000000000 : ℝ) (96294541983/200000000000 : ℝ) (19258908397/40000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (25/256 : ℝ))) 3 (481492578053/1000000000000 : ℝ) (240746289031/500000000000 : ℝ) (96294541983/200000000000 : ℝ) (19258908397/40000000000 : ℝ) (30092665249/62500000000 : ℝ) (240741321997/500000000000 : ℝ) (481482643881/1000000000000 : ℝ) (120370660973/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (25/256 : ℝ))) 4 (30092665249/62500000000 : ℝ) (240741321997/500000000000 : ℝ) (481482643881/1000000000000 : ℝ) (120370660973/250000000000 : ℝ) (120370660983/250000000000 : ℝ) (481482643943/1000000000000 : ℝ) (120370660983/250000000000 : ℝ) (481482643943/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (25/256 : ℝ))) 5 (120370660983/250000000000 : ℝ) (481482643943/1000000000000 : ℝ) (120370660983/250000000000 : ℝ) (481482643943/1000000000000 : ℝ) (120370660983/250000000000 : ℝ) (481482643943/1000000000000 : ℝ) (120370660983/250000000000 : ℝ) (481482643943/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (25/256 : ℝ))) 6 (120370660983/250000000000 : ℝ) (481482643943/1000000000000 : ℝ) (120370660983/250000000000 : ℝ) (481482643943/1000000000000 : ℝ) (120370660983/250000000000 : ℝ) (481482643943/1000000000000 : ℝ) (120370660983/250000000000 : ℝ) (481482643943/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (25/256 : ℝ))) 7 (120370660983/250000000000 : ℝ) (481482643943/1000000000000 : ℝ) (120370660983/250000000000 : ℝ) (481482643943/1000000000000 : ℝ) (120370660983/250000000000 : ℝ) (481482643943/1000000000000 : ℝ) (120370660983/250000000000 : ℝ) (481482643943/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (25/256 : ℝ)) hmem 8 (19878486591/20000000000 : ℝ) (993924329553/1000000000000 : ℝ) (19878486591/20000000000 : ℝ) (993924329553/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (25/256 : ℝ))) hcmem 8 (120370660983/250000000000 : ℝ) (481482643943/1000000000000 : ℝ) (120370660983/250000000000 : ℝ) (481482643943/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (25/256 : ℝ)) (19878486591/20000000000 : ℝ) (993924329553/1000000000000 : ℝ) (120370660983/250000000000 : ℝ) (481482643943/1000000000000 : ℝ) (6087474839/8000000000 : ℝ) (47558397181/62500000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0011_exp_lower
  have heNumeric : (1028309252079/500000000000 : ℝ)/4 ≤ Real.exp (-83153903737/125000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1028309252079/500000000000 : ℝ)/4 ≤ Real.exp ((49/512 : ℝ)-(47558397181/62500000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (49/512 : ℝ) (25/256 : ℝ) (47558397181/62500000000 : ℝ) (1028309252079/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0012; no trusted numerical premise.
theorem cover8_leaf0012_exp_radius : (998444814072516343/1000000000000000000 : ℝ) ≤ Real.exp ((-51/4096 : ℝ)/8) ∧ Real.exp ((-51/4096 : ℝ)/8) ≤ (124805601759064543/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-51/4096 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0012_exp_lower : (184033218200532857/200000000000000000 : ℝ) ≤ Real.exp ((-332804366139/500000000000 : ℝ)/8) ∧ Real.exp ((-332804366139/500000000000 : ℝ)/8) ≤ (460083045501332143/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-332804366139/500000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0012_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027921136149/500000000000 : ℝ) ≤ 4*Real.exp (25/256 : ℝ)*Real.exp (-mu (radius 8 (51/512 : ℝ))) ∧ (20549/10000 : ℝ) < (1027921136149/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (51/512 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0012_exp_radius
  have hrNumeric : (987626023243/1000000000000 : ℝ) ≤ Real.exp (-51/4096 : ℝ) ∧ Real.exp (-51/4096 : ℝ) ≤ (246906505811/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (987626023243/1000000000000 : ℝ) ≤ (radius 8 (51/512 : ℝ)) ∧ (radius 8 (51/512 : ℝ)) ≤ (246906505811/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (51/512 : ℝ)) (987626023243/1000000000000 : ℝ) (246906505811/250000000000 : ℝ) (19603426921/125000000000 : ℝ) (9801713461/62500000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (51/512 : ℝ)) (987626023243/1000000000000 : ℝ) (246906505811/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (51/512 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (987626023243/1000000000000 : ℝ) (246906505811/250000000000 : ℝ) (993813011621/1000000000000 : ℝ) (496906505811/500000000000 : ℝ) (993793752869/1000000000000 : ℝ) (993793752871/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (51/512 : ℝ)) 1 (993813011621/1000000000000 : ℝ) (496906505811/500000000000 : ℝ) (993793752869/1000000000000 : ℝ) (993793752871/1000000000000 : ℝ) (198760676449/200000000000 : ℝ) (993803382247/1000000000000 : ℝ) (496901691099/500000000000 : ℝ) (4969016911/5000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (51/512 : ℝ)) 2 (198760676449/200000000000 : ℝ) (993803382247/1000000000000 : ℝ) (496901691099/500000000000 : ℝ) (4969016911/5000000000 : ℝ) (993803382221/1000000000000 : ℝ) (62112711389/62500000000 : ℝ) (993803382221/1000000000000 : ℝ) (62112711389/62500000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (51/512 : ℝ)) 3 (993803382221/1000000000000 : ℝ) (62112711389/62500000000 : ℝ) (993803382221/1000000000000 : ℝ) (62112711389/62500000000 : ℝ) (993803382221/1000000000000 : ℝ) (62112711389/62500000000 : ℝ) (993803382221/1000000000000 : ℝ) (62112711389/62500000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (51/512 : ℝ)) 4 (993803382221/1000000000000 : ℝ) (62112711389/62500000000 : ℝ) (993803382221/1000000000000 : ℝ) (62112711389/62500000000 : ℝ) (993803382221/1000000000000 : ℝ) (62112711389/62500000000 : ℝ) (993803382221/1000000000000 : ℝ) (62112711389/62500000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (51/512 : ℝ)) 5 (993803382221/1000000000000 : ℝ) (62112711389/62500000000 : ℝ) (993803382221/1000000000000 : ℝ) (62112711389/62500000000 : ℝ) (993803382221/1000000000000 : ℝ) (62112711389/62500000000 : ℝ) (993803382221/1000000000000 : ℝ) (62112711389/62500000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (51/512 : ℝ)) 6 (993803382221/1000000000000 : ℝ) (62112711389/62500000000 : ℝ) (993803382221/1000000000000 : ℝ) (62112711389/62500000000 : ℝ) (993803382221/1000000000000 : ℝ) (62112711389/62500000000 : ℝ) (993803382221/1000000000000 : ℝ) (62112711389/62500000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (51/512 : ℝ)) 7 (993803382221/1000000000000 : ℝ) (62112711389/62500000000 : ℝ) (993803382221/1000000000000 : ℝ) (62112711389/62500000000 : ℝ) (993803382221/1000000000000 : ℝ) (62112711389/62500000000 : ℝ) (993803382221/1000000000000 : ℝ) (62112711389/62500000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (51/512 : ℝ))) (19603426921/125000000000 : ℝ) (9801713461/62500000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (51/512 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (19603426921/125000000000 : ℝ) (9801713461/62500000000 : ℝ) (144603426921/250000000000 : ℝ) (72301713461/125000000000 : ℝ) (396014413081/1000000000000 : ℝ) (99003603273/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (51/512 : ℝ))) 1 (144603426921/250000000000 : ℝ) (72301713461/125000000000 : ℝ) (396014413081/1000000000000 : ℝ) (99003603273/250000000000 : ℝ) (243607030191/500000000000 : ℝ) (48721406039/100000000000 : ℝ) (478602303553/1000000000000 : ℝ) (239301151781/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (51/512 : ℝ))) 2 (243607030191/500000000000 : ℝ) (48721406039/100000000000 : ℝ) (478602303553/1000000000000 : ℝ) (239301151781/500000000000 : ℝ) (482908181967/1000000000000 : ℝ) (60363522747/125000000000 : ℝ) (24144449239/50000000000 : ℝ) (482888984789/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (51/512 : ℝ))) 3 (482908181967/1000000000000 : ℝ) (60363522747/125000000000 : ℝ) (24144449239/50000000000 : ℝ) (482888984789/1000000000000 : ℝ) (482898583373/1000000000000 : ℝ) (482898583383/1000000000000 : ℝ) (241449291639/500000000000 : ℝ) (60362322911/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (51/512 : ℝ))) 4 (482898583373/1000000000000 : ℝ) (482898583383/1000000000000 : ℝ) (241449291639/500000000000 : ℝ) (60362322911/125000000000 : ℝ) (19315943333/40000000000 : ℝ) (60362322917/125000000000 : ℝ) (19315943333/40000000000 : ℝ) (60362322917/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (51/512 : ℝ))) 5 (19315943333/40000000000 : ℝ) (60362322917/125000000000 : ℝ) (19315943333/40000000000 : ℝ) (60362322917/125000000000 : ℝ) (19315943333/40000000000 : ℝ) (60362322917/125000000000 : ℝ) (19315943333/40000000000 : ℝ) (60362322917/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (51/512 : ℝ))) 6 (19315943333/40000000000 : ℝ) (60362322917/125000000000 : ℝ) (19315943333/40000000000 : ℝ) (60362322917/125000000000 : ℝ) (19315943333/40000000000 : ℝ) (60362322917/125000000000 : ℝ) (19315943333/40000000000 : ℝ) (60362322917/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (51/512 : ℝ))) 7 (19315943333/40000000000 : ℝ) (60362322917/125000000000 : ℝ) (19315943333/40000000000 : ℝ) (60362322917/125000000000 : ℝ) (19315943333/40000000000 : ℝ) (60362322917/125000000000 : ℝ) (19315943333/40000000000 : ℝ) (60362322917/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (51/512 : ℝ)) hmem 8 (993803382221/1000000000000 : ℝ) (62112711389/62500000000 : ℝ) (993803382221/1000000000000 : ℝ) (62112711389/62500000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (51/512 : ℝ))) hcmem 8 (19315943333/40000000000 : ℝ) (60362322917/125000000000 : ℝ) (19315943333/40000000000 : ℝ) (60362322917/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (51/512 : ℝ)) (993803382221/1000000000000 : ℝ) (62112711389/62500000000 : ℝ) (19315943333/40000000000 : ℝ) (60362322917/125000000000 : ℝ) (381632491129/500000000000 : ℝ) (381632491139/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0012_exp_lower
  have heNumeric : (1027921136149/500000000000 : ℝ)/4 ≤ Real.exp (-332804366139/500000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027921136149/500000000000 : ℝ)/4 ≤ Real.exp ((25/256 : ℝ)-(381632491139/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (25/256 : ℝ) (51/512 : ℝ) (381632491139/500000000000 : ℝ) (1027921136149/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0013; no trusted numerical premise.
theorem cover8_leaf0013_exp_radius : (124801793052478969/125000000000000000 : ℝ) ≤ Real.exp ((-13/1024 : ℝ)/8) ∧ Real.exp ((-13/1024 : ℝ)/8) ≤ (998414344419831753/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-13/1024 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0013_exp_lower : (920126277503602691/1000000000000000000 : ℝ) ≤ Real.exp ((-41622180101/62500000000 : ℝ)/8) ∧ Real.exp ((-41622180101/62500000000 : ℝ)/8) ≤ (230031569375900673/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-41622180101/62500000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0013_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2055130767007/1000000000000 : ℝ) ≤ 4*Real.exp (51/512 : ℝ)*Real.exp (-mu (radius 8 (13/128 : ℝ))) ∧ (20549/10000 : ℝ) < (2055130767007/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (13/128 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0013_exp_radius
  have hrNumeric : (12342311663/12500000000 : ℝ) ≤ Real.exp (-13/1024 : ℝ) ∧ Real.exp (-13/1024 : ℝ) ≤ (987384933041/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (12342311663/12500000000 : ℝ) ≤ (radius 8 (13/128 : ℝ)) ∧ (radius 8 (13/128 : ℝ)) ≤ (987384933041/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (13/128 : ℝ)) (12342311663/12500000000 : ℝ) (987384933041/1000000000000 : ℝ) (79169113301/500000000000 : ℝ) (158338226609/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (13/128 : ℝ)) (12342311663/12500000000 : ℝ) (987384933041/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (13/128 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (12342311663/12500000000 : ℝ) (987384933041/1000000000000 : ℝ) (24842311663/25000000000 : ℝ) (993692466521/1000000000000 : ℝ) (24841811189/25000000000 : ℝ) (993672447561/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (13/128 : ℝ)) 1 (24842311663/25000000000 : ℝ) (993692466521/1000000000000 : ℝ) (24841811189/25000000000 : ℝ) (993672447561/1000000000000 : ℝ) (12421030713/12500000000 : ℝ) (993682457041/1000000000000 : ℝ) (993682456989/1000000000000 : ℝ) (993682456991/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (13/128 : ℝ)) 2 (12421030713/12500000000 : ℝ) (993682457041/1000000000000 : ℝ) (993682456989/1000000000000 : ℝ) (993682456991/1000000000000 : ℝ) (496841228507/500000000000 : ℝ) (124210307127/125000000000 : ℝ) (496841228507/500000000000 : ℝ) (124210307127/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (13/128 : ℝ)) 3 (496841228507/500000000000 : ℝ) (124210307127/125000000000 : ℝ) (496841228507/500000000000 : ℝ) (124210307127/125000000000 : ℝ) (496841228507/500000000000 : ℝ) (124210307127/125000000000 : ℝ) (496841228507/500000000000 : ℝ) (124210307127/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (13/128 : ℝ)) 4 (496841228507/500000000000 : ℝ) (124210307127/125000000000 : ℝ) (496841228507/500000000000 : ℝ) (124210307127/125000000000 : ℝ) (496841228507/500000000000 : ℝ) (124210307127/125000000000 : ℝ) (496841228507/500000000000 : ℝ) (124210307127/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (13/128 : ℝ)) 5 (496841228507/500000000000 : ℝ) (124210307127/125000000000 : ℝ) (496841228507/500000000000 : ℝ) (124210307127/125000000000 : ℝ) (496841228507/500000000000 : ℝ) (124210307127/125000000000 : ℝ) (496841228507/500000000000 : ℝ) (124210307127/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (13/128 : ℝ)) 6 (496841228507/500000000000 : ℝ) (124210307127/125000000000 : ℝ) (496841228507/500000000000 : ℝ) (124210307127/125000000000 : ℝ) (496841228507/500000000000 : ℝ) (124210307127/125000000000 : ℝ) (496841228507/500000000000 : ℝ) (124210307127/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (13/128 : ℝ)) 7 (496841228507/500000000000 : ℝ) (124210307127/125000000000 : ℝ) (496841228507/500000000000 : ℝ) (124210307127/125000000000 : ℝ) (496841228507/500000000000 : ℝ) (124210307127/125000000000 : ℝ) (496841228507/500000000000 : ℝ) (124210307127/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (13/128 : ℝ))) (79169113301/500000000000 : ℝ) (158338226609/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (13/128 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (79169113301/500000000000 : ℝ) (158338226609/1000000000000 : ℝ) (579169113301/1000000000000 : ℝ) (115833822661/200000000000 : ℝ) (397917361523/1000000000000 : ℝ) (397917361533/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (13/128 : ℝ))) 1 (579169113301/1000000000000 : ℝ) (115833822661/200000000000 : ℝ) (397917361523/1000000000000 : ℝ) (397917361533/1000000000000 : ℝ) (122135809353/250000000000 : ℝ) (488543237419/1000000000000 : ℝ) (2400320007/5000000000 : ℝ) (3750500011/7812500000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (13/128 : ℝ))) 2 (122135809353/250000000000 : ℝ) (488543237419/1000000000000 : ℝ) (2400320007/5000000000 : ℝ) (3750500011/7812500000 : ℝ) (242151809703/500000000000 : ℝ) (242151809707/500000000000 : ℝ) (60535632767/125000000000 : ℝ) (96857012429/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (13/128 : ℝ))) 3 (242151809703/500000000000 : ℝ) (242151809707/500000000000 : ℝ) (60535632767/125000000000 : ℝ) (96857012429/200000000000 : ℝ) (484294340771/1000000000000 : ℝ) (24214717039/50000000000 : ℝ) (242147170341/500000000000 : ℝ) (484294340691/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (13/128 : ℝ))) 4 (484294340771/1000000000000 : ℝ) (24214717039/50000000000 : ℝ) (242147170341/500000000000 : ℝ) (484294340691/1000000000000 : ℝ) (242147170363/500000000000 : ℝ) (3783549537/7812500000 : ℝ) (242147170363/500000000000 : ℝ) (3783549537/7812500000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (13/128 : ℝ))) 5 (242147170363/500000000000 : ℝ) (3783549537/7812500000 : ℝ) (242147170363/500000000000 : ℝ) (3783549537/7812500000 : ℝ) (242147170363/500000000000 : ℝ) (3783549537/7812500000 : ℝ) (242147170363/500000000000 : ℝ) (3783549537/7812500000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (13/128 : ℝ))) 6 (242147170363/500000000000 : ℝ) (3783549537/7812500000 : ℝ) (242147170363/500000000000 : ℝ) (3783549537/7812500000 : ℝ) (242147170363/500000000000 : ℝ) (3783549537/7812500000 : ℝ) (242147170363/500000000000 : ℝ) (3783549537/7812500000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (13/128 : ℝ))) 7 (242147170363/500000000000 : ℝ) (3783549537/7812500000 : ℝ) (242147170363/500000000000 : ℝ) (3783549537/7812500000 : ℝ) (242147170363/500000000000 : ℝ) (3783549537/7812500000 : ℝ) (242147170363/500000000000 : ℝ) (3783549537/7812500000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (13/128 : ℝ)) hmem 8 (496841228507/500000000000 : ℝ) (124210307127/125000000000 : ℝ) (496841228507/500000000000 : ℝ) (124210307127/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (13/128 : ℝ))) hcmem 8 (242147170363/500000000000 : ℝ) (3783549537/7812500000 : ℝ) (242147170363/500000000000 : ℝ) (3783549537/7812500000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (13/128 : ℝ)) (496841228507/500000000000 : ℝ) (124210307127/125000000000 : ℝ) (242147170363/500000000000 : ℝ) (3783549537/7812500000 : ℝ) (382782128299/500000000000 : ℝ) (95695532077/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0013_exp_lower
  have heNumeric : (2055130767007/1000000000000 : ℝ)/4 ≤ Real.exp (-41622180101/62500000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2055130767007/1000000000000 : ℝ)/4 ≤ Real.exp ((51/512 : ℝ)-(95695532077/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (51/512 : ℝ) (13/128 : ℝ) (95695532077/125000000000 : ℝ) (2055130767007/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0014; no trusted numerical premise.
theorem cover8_leaf0014_exp_radius : (998399109942183411/1000000000000000000 : ℝ) ≤ Real.exp ((-105/8192 : ℝ)/8) ∧ Real.exp ((-105/8192 : ℝ)/8) ≤ (249599777485545853/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-105/8192 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0014_exp_lower : (230055002558072107/250000000000000000 : ℝ) ≤ Real.exp ((-20785623993/31250000000 : ℝ)/8) ∧ Real.exp ((-20785623993/31250000000 : ℝ)/8) ≤ (920220010232288429/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-20785623993/31250000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0014_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (257100775511/125000000000 : ℝ) ≤ 4*Real.exp (13/128 : ℝ)*Real.exp (-mu (radius 8 (105/1024 : ℝ))) ∧ (20549/10000 : ℝ) < (257100775511/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (105/1024 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0014_exp_radius
  have hrNumeric : (987264410009/1000000000000 : ℝ) ≤ Real.exp (-105/8192 : ℝ) ∧ Real.exp (-105/8192 : ℝ) ≤ (98726441001/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (987264410009/1000000000000 : ℝ) ≤ (radius 8 (105/1024 : ℝ)) ∧ (radius 8 (105/1024 : ℝ)) ≤ (98726441001/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (105/1024 : ℝ)) (987264410009/1000000000000 : ℝ) (98726441001/100000000000 : ℝ) (39771994487/250000000000 : ℝ) (31817595591/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (105/1024 : ℝ)) (987264410009/1000000000000 : ℝ) (98726441001/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (105/1024 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (987264410009/1000000000000 : ℝ) (98726441001/100000000000 : ℝ) (248408051251/250000000000 : ℝ) (198726441001/200000000000 : ℝ) (993611800457/1000000000000 : ℝ) (993611800459/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (105/1024 : ℝ)) 1 (248408051251/250000000000 : ℝ) (198726441001/200000000000 : ℝ) (993611800457/1000000000000 : ℝ) (993611800459/1000000000000 : ℝ) (99362200273/100000000000 : ℝ) (248405500683/250000000000 : ℝ) (496811001339/500000000000 : ℝ) (24840550067/25000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (105/1024 : ℝ)) 2 (99362200273/100000000000 : ℝ) (248405500683/250000000000 : ℝ) (496811001339/500000000000 : ℝ) (24840550067/25000000000 : ℝ) (62101375169/62500000000 : ℝ) (496811001353/500000000000 : ℝ) (993622002703/1000000000000 : ℝ) (496811001353/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (105/1024 : ℝ)) 3 (62101375169/62500000000 : ℝ) (496811001353/500000000000 : ℝ) (993622002703/1000000000000 : ℝ) (496811001353/500000000000 : ℝ) (993622002703/1000000000000 : ℝ) (496811001353/500000000000 : ℝ) (993622002703/1000000000000 : ℝ) (496811001353/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (105/1024 : ℝ)) 4 (993622002703/1000000000000 : ℝ) (496811001353/500000000000 : ℝ) (993622002703/1000000000000 : ℝ) (496811001353/500000000000 : ℝ) (993622002703/1000000000000 : ℝ) (496811001353/500000000000 : ℝ) (993622002703/1000000000000 : ℝ) (496811001353/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (105/1024 : ℝ)) 5 (993622002703/1000000000000 : ℝ) (496811001353/500000000000 : ℝ) (993622002703/1000000000000 : ℝ) (496811001353/500000000000 : ℝ) (993622002703/1000000000000 : ℝ) (496811001353/500000000000 : ℝ) (993622002703/1000000000000 : ℝ) (496811001353/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (105/1024 : ℝ)) 6 (993622002703/1000000000000 : ℝ) (496811001353/500000000000 : ℝ) (993622002703/1000000000000 : ℝ) (496811001353/500000000000 : ℝ) (993622002703/1000000000000 : ℝ) (496811001353/500000000000 : ℝ) (993622002703/1000000000000 : ℝ) (496811001353/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (105/1024 : ℝ)) 7 (993622002703/1000000000000 : ℝ) (496811001353/500000000000 : ℝ) (993622002703/1000000000000 : ℝ) (496811001353/500000000000 : ℝ) (993622002703/1000000000000 : ℝ) (496811001353/500000000000 : ℝ) (993622002703/1000000000000 : ℝ) (496811001353/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (105/1024 : ℝ))) (39771994487/250000000000 : ℝ) (31817595591/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (105/1024 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (39771994487/250000000000 : ℝ) (31817595591/200000000000 : ℝ) (289771994487/500000000000 : ℝ) (289771994489/500000000000 : ℝ) (398858343209/1000000000000 : ℝ) (398858343219/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (105/1024 : ℝ))) 1 (289771994487/500000000000 : ℝ) (289771994489/500000000000 : ℝ) (398858343209/1000000000000 : ℝ) (398858343219/1000000000000 : ℝ) (489201166091/1000000000000 : ℝ) (489201166099/1000000000000 : ℝ) (120196702133/250000000000 : ℝ) (480786808541/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (105/1024 : ℝ))) 2 (489201166091/1000000000000 : ℝ) (489201166099/1000000000000 : ℝ) (120196702133/250000000000 : ℝ) (480786808541/1000000000000 : ℝ) (484993987311/1000000000000 : ℝ) (12124849683/25000000000 : ℝ) (96995147791/200000000000 : ℝ) (121243934741/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (105/1024 : ℝ))) 3 (484993987311/1000000000000 : ℝ) (12124849683/25000000000 : ℝ) (96995147791/200000000000 : ℝ) (121243934741/250000000000 : ℝ) (484984863133/1000000000000 : ℝ) (242492431571/500000000000 : ℝ) (484984863047/1000000000000 : ℝ) (484984863057/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (105/1024 : ℝ))) 4 (484984863133/1000000000000 : ℝ) (242492431571/500000000000 : ℝ) (484984863047/1000000000000 : ℝ) (484984863057/1000000000000 : ℝ) (48498486309/100000000000 : ℝ) (4849848631/10000000000 : ℝ) (484984863089/1000000000000 : ℝ) (4849848631/10000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (105/1024 : ℝ))) 5 (48498486309/100000000000 : ℝ) (4849848631/10000000000 : ℝ) (484984863089/1000000000000 : ℝ) (4849848631/10000000000 : ℝ) (484984863089/1000000000000 : ℝ) (4849848631/10000000000 : ℝ) (484984863089/1000000000000 : ℝ) (4849848631/10000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (105/1024 : ℝ))) 6 (484984863089/1000000000000 : ℝ) (4849848631/10000000000 : ℝ) (484984863089/1000000000000 : ℝ) (4849848631/10000000000 : ℝ) (484984863089/1000000000000 : ℝ) (4849848631/10000000000 : ℝ) (484984863089/1000000000000 : ℝ) (4849848631/10000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (105/1024 : ℝ))) 7 (484984863089/1000000000000 : ℝ) (4849848631/10000000000 : ℝ) (484984863089/1000000000000 : ℝ) (4849848631/10000000000 : ℝ) (484984863089/1000000000000 : ℝ) (4849848631/10000000000 : ℝ) (484984863089/1000000000000 : ℝ) (4849848631/10000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (105/1024 : ℝ)) hmem 8 (993622002703/1000000000000 : ℝ) (496811001353/500000000000 : ℝ) (993622002703/1000000000000 : ℝ) (496811001353/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (105/1024 : ℝ))) hcmem 8 (484984863089/1000000000000 : ℝ) (4849848631/10000000000 : ℝ) (484984863089/1000000000000 : ℝ) (4849848631/10000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (105/1024 : ℝ)) (993622002703/1000000000000 : ℝ) (496811001353/500000000000 : ℝ) (484984863089/1000000000000 : ℝ) (4849848631/10000000000 : ℝ) (153340493551/200000000000 : ℝ) (11979726059/15625000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0014_exp_lower
  have heNumeric : (257100775511/125000000000 : ℝ)/4 ≤ Real.exp (-20785623993/31250000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (257100775511/125000000000 : ℝ)/4 ≤ Real.exp ((13/128 : ℝ)-(11979726059/15625000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (13/128 : ℝ) (105/1024 : ℝ) (11979726059/15625000000 : ℝ) (257100775511/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0015; no trusted numerical premise.
theorem cover8_leaf0015_exp_radius : (499191937848496489/500000000000000000 : ℝ) ≤ Real.exp ((-53/4096 : ℝ)/8) ∧ Real.exp ((-53/4096 : ℝ)/8) ≤ (998383875696992979/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-53/4096 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0015_exp_lower : (920202273039800781/1000000000000000000 : ℝ) ≤ Real.exp ((-665294168843/1000000000000 : ℝ)/8) ∧ Real.exp ((-665294168843/1000000000000 : ℝ)/8) ≤ (460101136519900391/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-665294168843/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0015_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (514122266707/250000000000 : ℝ) ≤ 4*Real.exp (105/1024 : ℝ)*Real.exp (-mu (radius 8 (53/512 : ℝ))) ∧ (20549/10000 : ℝ) < (514122266707/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (53/512 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0015_exp_radius
  have hrNumeric : (987143901689/1000000000000 : ℝ) ≤ Real.exp (-53/4096 : ℝ) ∧ Real.exp (-53/4096 : ℝ) ≤ (98714390169/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (987143901689/1000000000000 : ℝ) ≤ (radius 8 (53/512 : ℝ)) ∧ (radius 8 (53/512 : ℝ)) ≤ (98714390169/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (53/512 : ℝ)) (987143901689/1000000000000 : ℝ) (98714390169/100000000000 : ℝ) (159834030657/1000000000000 : ℝ) (19979253833/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (53/512 : ℝ)) (987143901689/1000000000000 : ℝ) (98714390169/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (53/512 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (987143901689/1000000000000 : ℝ) (98714390169/100000000000 : ℝ) (248392987711/250000000000 : ℝ) (198714390169/200000000000 : ℝ) (15524236829/15625000000 : ℝ) (496775578529/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (53/512 : ℝ)) 1 (248392987711/250000000000 : ℝ) (198714390169/200000000000 : ℝ) (15524236829/15625000000 : ℝ) (496775578529/500000000000 : ℝ) (19871231079/20000000000 : ℝ) (31048798561/31250000000 : ℝ) (198712310779/200000000000 : ℝ) (496780776949/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (53/512 : ℝ)) 2 (19871231079/20000000000 : ℝ) (31048798561/31250000000 : ℝ) (198712310779/200000000000 : ℝ) (496780776949/500000000000 : ℝ) (496780776961/500000000000 : ℝ) (39742462157/40000000000 : ℝ) (496780776961/500000000000 : ℝ) (39742462157/40000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (53/512 : ℝ)) 3 (496780776961/500000000000 : ℝ) (39742462157/40000000000 : ℝ) (496780776961/500000000000 : ℝ) (39742462157/40000000000 : ℝ) (496780776961/500000000000 : ℝ) (39742462157/40000000000 : ℝ) (496780776961/500000000000 : ℝ) (39742462157/40000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (53/512 : ℝ)) 4 (496780776961/500000000000 : ℝ) (39742462157/40000000000 : ℝ) (496780776961/500000000000 : ℝ) (39742462157/40000000000 : ℝ) (496780776961/500000000000 : ℝ) (39742462157/40000000000 : ℝ) (496780776961/500000000000 : ℝ) (39742462157/40000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (53/512 : ℝ)) 5 (496780776961/500000000000 : ℝ) (39742462157/40000000000 : ℝ) (496780776961/500000000000 : ℝ) (39742462157/40000000000 : ℝ) (496780776961/500000000000 : ℝ) (39742462157/40000000000 : ℝ) (496780776961/500000000000 : ℝ) (39742462157/40000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (53/512 : ℝ)) 6 (496780776961/500000000000 : ℝ) (39742462157/40000000000 : ℝ) (496780776961/500000000000 : ℝ) (39742462157/40000000000 : ℝ) (496780776961/500000000000 : ℝ) (39742462157/40000000000 : ℝ) (496780776961/500000000000 : ℝ) (39742462157/40000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (53/512 : ℝ)) 7 (496780776961/500000000000 : ℝ) (39742462157/40000000000 : ℝ) (496780776961/500000000000 : ℝ) (39742462157/40000000000 : ℝ) (496780776961/500000000000 : ℝ) (39742462157/40000000000 : ℝ) (496780776961/500000000000 : ℝ) (39742462157/40000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (53/512 : ℝ))) (159834030657/1000000000000 : ℝ) (19979253833/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (53/512 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (159834030657/1000000000000 : ℝ) (19979253833/125000000000 : ℝ) (18122406729/31250000000 : ℝ) (144979253833/250000000000 : ℝ) (99948121123/250000000000 : ℝ) (199896242251/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (53/512 : ℝ))) 1 (18122406729/31250000000 : ℝ) (144979253833/250000000000 : ℝ) (99948121123/250000000000 : ℝ) (199896242251/500000000000 : ℝ) (48985474991/100000000000 : ℝ) (489854749917/1000000000000 : ℝ) (481504376259/1000000000000 : ℝ) (120376094067/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (53/512 : ℝ))) 2 (48985474991/100000000000 : ℝ) (489854749917/1000000000000 : ℝ) (481504376259/1000000000000 : ℝ) (120376094067/250000000000 : ℝ) (121419890771/250000000000 : ℝ) (485679563093/1000000000000 : ℝ) (485661616573/1000000000000 : ℝ) (242830808291/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (53/512 : ℝ))) 3 (121419890771/250000000000 : ℝ) (485679563093/1000000000000 : ℝ) (485661616573/1000000000000 : ℝ) (242830808291/500000000000 : ℝ) (121417647457/250000000000 : ℝ) (242835294919/500000000000 : ℝ) (97134117949/200000000000 : ℝ) (97134117951/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (53/512 : ℝ))) 4 (121417647457/250000000000 : ℝ) (242835294919/500000000000 : ℝ) (97134117949/200000000000 : ℝ) (97134117951/200000000000 : ℝ) (242835294893/500000000000 : ℝ) (485670589797/1000000000000 : ℝ) (242835294893/500000000000 : ℝ) (485670589797/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (53/512 : ℝ))) 5 (242835294893/500000000000 : ℝ) (485670589797/1000000000000 : ℝ) (242835294893/500000000000 : ℝ) (485670589797/1000000000000 : ℝ) (242835294893/500000000000 : ℝ) (485670589797/1000000000000 : ℝ) (242835294893/500000000000 : ℝ) (485670589797/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (53/512 : ℝ))) 6 (242835294893/500000000000 : ℝ) (485670589797/1000000000000 : ℝ) (242835294893/500000000000 : ℝ) (485670589797/1000000000000 : ℝ) (242835294893/500000000000 : ℝ) (485670589797/1000000000000 : ℝ) (242835294893/500000000000 : ℝ) (485670589797/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (53/512 : ℝ))) 7 (242835294893/500000000000 : ℝ) (485670589797/1000000000000 : ℝ) (242835294893/500000000000 : ℝ) (485670589797/1000000000000 : ℝ) (242835294893/500000000000 : ℝ) (485670589797/1000000000000 : ℝ) (242835294893/500000000000 : ℝ) (485670589797/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (53/512 : ℝ)) hmem 8 (496780776961/500000000000 : ℝ) (39742462157/40000000000 : ℝ) (496780776961/500000000000 : ℝ) (39742462157/40000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (53/512 : ℝ))) hcmem 8 (242835294893/500000000000 : ℝ) (485670589797/1000000000000 : ℝ) (242835294893/500000000000 : ℝ) (485670589797/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (53/512 : ℝ)) (496780776961/500000000000 : ℝ) (39742462157/40000000000 : ℝ) (242835294893/500000000000 : ℝ) (485670589797/1000000000000 : ℝ) (383916615661/500000000000 : ℝ) (767833231343/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0015_exp_lower
  have heNumeric : (514122266707/250000000000 : ℝ)/4 ≤ Real.exp (-665294168843/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (514122266707/250000000000 : ℝ)/4 ≤ Real.exp ((105/1024 : ℝ)-(767833231343/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (105/1024 : ℝ) (53/512 : ℝ) (767833231343/1000000000000 : ℝ) (514122266707/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0016; no trusted numerical premise.
theorem cover8_leaf0016_exp_radius : (499184320842128453/500000000000000000 : ℝ) ≤ Real.exp ((-107/8192 : ℝ)/8) ∧ Real.exp ((-107/8192 : ℝ)/8) ≤ (998368641684256907/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-107/8192 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0016_exp_lower : (920185378668675197/1000000000000000000 : ℝ) ≤ Real.exp ((-332720522737/500000000000 : ℝ)/8) ∧ Real.exp ((-332720522737/500000000000 : ℝ)/8) ≤ (460092689334337599/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-332720522737/500000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0016_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (257023379853/125000000000 : ℝ) ≤ 4*Real.exp (53/512 : ℝ)*Real.exp (-mu (radius 8 (107/1024 : ℝ))) ∧ (20549/10000 : ℝ) < (257023379853/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (107/1024 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0016_exp_radius
  have hrNumeric : (987023408079/1000000000000 : ℝ) ≤ Real.exp (-107/8192 : ℝ) ∧ Real.exp (-107/8192 : ℝ) ≤ (12337792601/12500000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (987023408079/1000000000000 : ℝ) ≤ (radius 8 (107/1024 : ℝ)) ∧ (radius 8 (107/1024 : ℝ)) ≤ (12337792601/12500000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (107/1024 : ℝ)) (987023408079/1000000000000 : ℝ) (12337792601/12500000000 : ℝ) (80288218161/500000000000 : ℝ) (160576436329/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (107/1024 : ℝ)) (987023408079/1000000000000 : ℝ) (12337792601/12500000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (107/1024 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (987023408079/1000000000000 : ℝ) (12337792601/12500000000 : ℝ) (993511704039/1000000000000 : ℝ) (24837792601/25000000000 : ℝ) (993490517357/1000000000000 : ℝ) (496745258679/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (107/1024 : ℝ)) 1 (993511704039/1000000000000 : ℝ) (24837792601/25000000000 : ℝ) (993490517357/1000000000000 : ℝ) (496745258679/500000000000 : ℝ) (496750555349/500000000000 : ℝ) (993501110699/1000000000000 : ℝ) (993501110641/1000000000000 : ℝ) (993501110643/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (107/1024 : ℝ)) 2 (496750555349/500000000000 : ℝ) (993501110699/1000000000000 : ℝ) (993501110641/1000000000000 : ℝ) (993501110643/1000000000000 : ℝ) (993501110669/1000000000000 : ℝ) (993501110671/1000000000000 : ℝ) (993501110669/1000000000000 : ℝ) (993501110671/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (107/1024 : ℝ)) 3 (993501110669/1000000000000 : ℝ) (993501110671/1000000000000 : ℝ) (993501110669/1000000000000 : ℝ) (993501110671/1000000000000 : ℝ) (993501110669/1000000000000 : ℝ) (993501110671/1000000000000 : ℝ) (993501110669/1000000000000 : ℝ) (993501110671/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (107/1024 : ℝ)) 4 (993501110669/1000000000000 : ℝ) (993501110671/1000000000000 : ℝ) (993501110669/1000000000000 : ℝ) (993501110671/1000000000000 : ℝ) (993501110669/1000000000000 : ℝ) (993501110671/1000000000000 : ℝ) (993501110669/1000000000000 : ℝ) (993501110671/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (107/1024 : ℝ)) 5 (993501110669/1000000000000 : ℝ) (993501110671/1000000000000 : ℝ) (993501110669/1000000000000 : ℝ) (993501110671/1000000000000 : ℝ) (993501110669/1000000000000 : ℝ) (993501110671/1000000000000 : ℝ) (993501110669/1000000000000 : ℝ) (993501110671/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (107/1024 : ℝ)) 6 (993501110669/1000000000000 : ℝ) (993501110671/1000000000000 : ℝ) (993501110669/1000000000000 : ℝ) (993501110671/1000000000000 : ℝ) (993501110669/1000000000000 : ℝ) (993501110671/1000000000000 : ℝ) (993501110669/1000000000000 : ℝ) (993501110671/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (107/1024 : ℝ)) 7 (993501110669/1000000000000 : ℝ) (993501110671/1000000000000 : ℝ) (993501110669/1000000000000 : ℝ) (993501110671/1000000000000 : ℝ) (993501110669/1000000000000 : ℝ) (993501110671/1000000000000 : ℝ) (993501110669/1000000000000 : ℝ) (993501110671/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (107/1024 : ℝ))) (80288218161/500000000000 : ℝ) (160576436329/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (107/1024 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (80288218161/500000000000 : ℝ) (160576436329/1000000000000 : ℝ) (580288218161/1000000000000 : ℝ) (116057643633/200000000000 : ℝ) (200359948793/500000000000 : ℝ) (100179974399/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (107/1024 : ℝ))) 1 (580288218161/1000000000000 : ℝ) (116057643633/200000000000 : ℝ) (200359948793/500000000000 : ℝ) (100179974399/250000000000 : ℝ) (490504057873/1000000000000 : ℝ) (490504057881/1000000000000 : ℝ) (7534637389/15625000000 : ℝ) (96443358581/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (107/1024 : ℝ))) 2 (490504057873/1000000000000 : ℝ) (490504057881/1000000000000 : ℝ) (7534637389/15625000000 : ℝ) (96443358581/200000000000 : ℝ) (60795053173/125000000000 : ℝ) (486360425393/1000000000000 : ℝ) (60792846733/125000000000 : ℝ) (486342773873/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (107/1024 : ℝ))) 3 (60795053173/125000000000 : ℝ) (486360425393/1000000000000 : ℝ) (60792846733/125000000000 : ℝ) (486342773873/1000000000000 : ℝ) (60793949953/125000000000 : ℝ) (486351599633/1000000000000 : ℝ) (486351599543/1000000000000 : ℝ) (486351599553/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (107/1024 : ℝ))) 4 (60793949953/125000000000 : ℝ) (486351599633/1000000000000 : ℝ) (486351599543/1000000000000 : ℝ) (486351599553/1000000000000 : ℝ) (486351599583/1000000000000 : ℝ) (486351599593/1000000000000 : ℝ) (486351599583/1000000000000 : ℝ) (486351599593/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (107/1024 : ℝ))) 5 (486351599583/1000000000000 : ℝ) (486351599593/1000000000000 : ℝ) (486351599583/1000000000000 : ℝ) (486351599593/1000000000000 : ℝ) (486351599583/1000000000000 : ℝ) (486351599593/1000000000000 : ℝ) (486351599583/1000000000000 : ℝ) (486351599593/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (107/1024 : ℝ))) 6 (486351599583/1000000000000 : ℝ) (486351599593/1000000000000 : ℝ) (486351599583/1000000000000 : ℝ) (486351599593/1000000000000 : ℝ) (486351599583/1000000000000 : ℝ) (486351599593/1000000000000 : ℝ) (486351599583/1000000000000 : ℝ) (486351599593/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (107/1024 : ℝ))) 7 (486351599583/1000000000000 : ℝ) (486351599593/1000000000000 : ℝ) (486351599583/1000000000000 : ℝ) (486351599593/1000000000000 : ℝ) (486351599583/1000000000000 : ℝ) (486351599593/1000000000000 : ℝ) (486351599583/1000000000000 : ℝ) (486351599593/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (107/1024 : ℝ)) hmem 8 (993501110669/1000000000000 : ℝ) (993501110671/1000000000000 : ℝ) (993501110669/1000000000000 : ℝ) (993501110671/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (107/1024 : ℝ))) hcmem 8 (486351599583/1000000000000 : ℝ) (486351599593/1000000000000 : ℝ) (486351599583/1000000000000 : ℝ) (486351599593/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (107/1024 : ℝ)) (993501110669/1000000000000 : ℝ) (993501110671/1000000000000 : ℝ) (486351599583/1000000000000 : ℝ) (486351599593/1000000000000 : ℝ) (153791334091/200000000000 : ℝ) (384478335237/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0016_exp_lower
  have heNumeric : (257023379853/125000000000 : ℝ)/4 ≤ Real.exp (-332720522737/500000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (257023379853/125000000000 : ℝ)/4 ≤ Real.exp ((53/512 : ℝ)-(384478335237/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (53/512 : ℝ) (107/1024 : ℝ) (384478335237/500000000000 : ℝ) (257023379853/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0017; no trusted numerical premise.
theorem cover8_leaf0017_exp_radius : (499176703951985823/500000000000000000 : ℝ) ≤ Real.exp ((-27/2048 : ℝ)/8) ∧ Real.exp ((-27/2048 : ℝ)/8) ≤ (998353407903971647/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-27/2048 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0017_exp_lower : (1797205689982643/1953125000000000 : ℝ) ≤ Real.exp ((-665580717659/1000000000000 : ℝ)/8) ∧ Real.exp ((-665580717659/1000000000000 : ℝ)/8) ≤ (920169313271113217/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-665580717659/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0017_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2055899866743/1000000000000 : ℝ) ≤ 4*Real.exp (107/1024 : ℝ)*Real.exp (-mu (radius 8 (27/256 : ℝ))) ∧ (20549/10000 : ℝ) < (2055899866743/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (27/256 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0017_exp_radius
  have hrNumeric : (986902929177/1000000000000 : ℝ) ≤ Real.exp (-27/2048 : ℝ) ∧ Real.exp (-27/2048 : ℝ) ≤ (493451464589/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (986902929177/1000000000000 : ℝ) ≤ (radius 8 (27/256 : ℝ)) ∧ (radius 8 (27/256 : ℝ)) ≤ (493451464589/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (27/256 : ℝ)) (986902929177/1000000000000 : ℝ) (493451464589/500000000000 : ℝ) (80657622671/500000000000 : ℝ) (161315245349/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (27/256 : ℝ)) (986902929177/1000000000000 : ℝ) (493451464589/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (27/256 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (986902929177/1000000000000 : ℝ) (493451464589/500000000000 : ℝ) (248362866147/250000000000 : ℝ) (993451464589/1000000000000 : ℝ) (993429881359/1000000000000 : ℝ) (12417873517/12500000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (27/256 : ℝ)) 1 (248362866147/250000000000 : ℝ) (993451464589/1000000000000 : ℝ) (993429881359/1000000000000 : ℝ) (12417873517/12500000000 : ℝ) (993440672973/1000000000000 : ℝ) (39737626919/40000000000 : ℝ) (496720336457/500000000000 : ℝ) (248360168229/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (27/256 : ℝ)) 2 (993440672973/1000000000000 : ℝ) (39737626919/40000000000 : ℝ) (496720336457/500000000000 : ℝ) (248360168229/250000000000 : ℝ) (993440672943/1000000000000 : ℝ) (496720336473/500000000000 : ℝ) (993440672943/1000000000000 : ℝ) (496720336473/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (27/256 : ℝ)) 3 (993440672943/1000000000000 : ℝ) (496720336473/500000000000 : ℝ) (993440672943/1000000000000 : ℝ) (496720336473/500000000000 : ℝ) (993440672943/1000000000000 : ℝ) (496720336473/500000000000 : ℝ) (993440672943/1000000000000 : ℝ) (496720336473/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (27/256 : ℝ)) 4 (993440672943/1000000000000 : ℝ) (496720336473/500000000000 : ℝ) (993440672943/1000000000000 : ℝ) (496720336473/500000000000 : ℝ) (993440672943/1000000000000 : ℝ) (496720336473/500000000000 : ℝ) (993440672943/1000000000000 : ℝ) (496720336473/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (27/256 : ℝ)) 5 (993440672943/1000000000000 : ℝ) (496720336473/500000000000 : ℝ) (993440672943/1000000000000 : ℝ) (496720336473/500000000000 : ℝ) (993440672943/1000000000000 : ℝ) (496720336473/500000000000 : ℝ) (993440672943/1000000000000 : ℝ) (496720336473/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (27/256 : ℝ)) 6 (993440672943/1000000000000 : ℝ) (496720336473/500000000000 : ℝ) (993440672943/1000000000000 : ℝ) (496720336473/500000000000 : ℝ) (993440672943/1000000000000 : ℝ) (496720336473/500000000000 : ℝ) (993440672943/1000000000000 : ℝ) (496720336473/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (27/256 : ℝ)) 7 (993440672943/1000000000000 : ℝ) (496720336473/500000000000 : ℝ) (993440672943/1000000000000 : ℝ) (496720336473/500000000000 : ℝ) (993440672943/1000000000000 : ℝ) (496720336473/500000000000 : ℝ) (993440672943/1000000000000 : ℝ) (496720336473/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (27/256 : ℝ))) (80657622671/500000000000 : ℝ) (161315245349/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (27/256 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (80657622671/500000000000 : ℝ) (161315245349/1000000000000 : ℝ) (580657622671/1000000000000 : ℝ) (23226304907/40000000000 : ℝ) (627563581/1562500000 : ℝ) (8032813837/20000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (27/256 : ℝ))) 1 (580657622671/1000000000000 : ℝ) (23226304907/40000000000 : ℝ) (627563581/1562500000 : ℝ) (8032813837/20000000000 : ℝ) (98229831451/200000000000 : ℝ) (491149157263/1000000000000 : ℝ) (7545689757/15625000000 : ℝ) (482924144457/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (27/256 : ℝ))) 2 (98229831451/200000000000 : ℝ) (491149157263/1000000000000 : ℝ) (7545689757/15625000000 : ℝ) (482924144457/1000000000000 : ℝ) (487036650851/1000000000000 : ℝ) (24351832543/50000000000 : ℝ) (487019287671/1000000000000 : ℝ) (760967637/1562500000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (27/256 : ℝ))) 3 (487036650851/1000000000000 : ℝ) (24351832543/50000000000 : ℝ) (487019287671/1000000000000 : ℝ) (760967637/1562500000 : ℝ) (487027969261/1000000000000 : ℝ) (48702796927/100000000000 : ℝ) (487027969183/1000000000000 : ℝ) (487027969193/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (27/256 : ℝ))) 4 (487027969261/1000000000000 : ℝ) (48702796927/100000000000 : ℝ) (487027969183/1000000000000 : ℝ) (487027969193/1000000000000 : ℝ) (243513984611/500000000000 : ℝ) (30439248077/62500000000 : ℝ) (487027969221/1000000000000 : ℝ) (30439248077/62500000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (27/256 : ℝ))) 5 (243513984611/500000000000 : ℝ) (30439248077/62500000000 : ℝ) (487027969221/1000000000000 : ℝ) (30439248077/62500000000 : ℝ) (487027969221/1000000000000 : ℝ) (30439248077/62500000000 : ℝ) (487027969221/1000000000000 : ℝ) (30439248077/62500000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (27/256 : ℝ))) 6 (487027969221/1000000000000 : ℝ) (30439248077/62500000000 : ℝ) (487027969221/1000000000000 : ℝ) (30439248077/62500000000 : ℝ) (487027969221/1000000000000 : ℝ) (30439248077/62500000000 : ℝ) (487027969221/1000000000000 : ℝ) (30439248077/62500000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (27/256 : ℝ))) 7 (487027969221/1000000000000 : ℝ) (30439248077/62500000000 : ℝ) (487027969221/1000000000000 : ℝ) (30439248077/62500000000 : ℝ) (487027969221/1000000000000 : ℝ) (30439248077/62500000000 : ℝ) (487027969221/1000000000000 : ℝ) (30439248077/62500000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (27/256 : ℝ)) hmem 8 (993440672943/1000000000000 : ℝ) (496720336473/500000000000 : ℝ) (993440672943/1000000000000 : ℝ) (496720336473/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (27/256 : ℝ))) hcmem 8 (487027969221/1000000000000 : ℝ) (30439248077/62500000000 : ℝ) (487027969221/1000000000000 : ℝ) (30439248077/62500000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (27/256 : ℝ)) (993440672943/1000000000000 : ℝ) (496720336473/500000000000 : ℝ) (487027969221/1000000000000 : ℝ) (30439248077/62500000000 : ℝ) (385036452569/500000000000 : ℝ) (770072905159/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0017_exp_lower
  have heNumeric : (2055899866743/1000000000000 : ℝ)/4 ≤ Real.exp (-665580717659/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2055899866743/1000000000000 : ℝ)/4 ≤ Real.exp ((107/1024 : ℝ)-(770072905159/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (107/1024 : ℝ) (27/256 : ℝ) (770072905159/1000000000000 : ℝ) (2055899866743/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0018; no trusted numerical premise.
theorem cover8_leaf0018_exp_radius : (499169087178066827/500000000000000000 : ℝ) ≤ Real.exp ((-109/8192 : ℝ)/8) ∧ Real.exp ((-109/8192 : ℝ)/8) ≤ (199667634871226731/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-109/8192 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0018_exp_lower : (920154063355539809/1000000000000000000 : ℝ) ≤ Real.exp ((-665713302319/1000000000000 : ℝ)/8) ∧ Real.exp ((-665713302319/1000000000000 : ℝ)/8) ≤ (92015406335553981/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-665713302319/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0018_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2055627304027/1000000000000 : ℝ) ≤ 4*Real.exp (27/256 : ℝ)*Real.exp (-mu (radius 8 (109/1024 : ℝ))) ∧ (20549/10000 : ℝ) < (2055627304027/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (109/1024 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0018_exp_radius
  have hrNumeric : (49339123249/50000000000 : ℝ) ≤ Real.exp (-109/8192 : ℝ) ∧ Real.exp (-109/8192 : ℝ) ≤ (986782464981/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (49339123249/50000000000 : ℝ) ≤ (radius 8 (109/1024 : ℝ)) ∧ (radius 8 (109/1024 : ℝ)) ≤ (986782464981/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (109/1024 : ℝ)) (49339123249/50000000000 : ℝ) (986782464981/1000000000000 : ℝ) (2025631337/12500000000 : ℝ) (162050506967/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (109/1024 : ℝ)) (49339123249/50000000000 : ℝ) (986782464981/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (109/1024 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (49339123249/50000000000 : ℝ) (986782464981/1000000000000 : ℝ) (99339123249/100000000000 : ℝ) (993391232491/1000000000000 : ℝ) (49668462453/50000000000 : ℝ) (496684624531/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (109/1024 : ℝ)) 1 (99339123249/100000000000 : ℝ) (993391232491/1000000000000 : ℝ) (49668462453/50000000000 : ℝ) (496684624531/500000000000 : ℝ) (39735209631/40000000000 : ℝ) (993380240777/1000000000000 : ℝ) (496690120357/500000000000 : ℝ) (248345060179/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (109/1024 : ℝ)) 2 (39735209631/40000000000 : ℝ) (993380240777/1000000000000 : ℝ) (496690120357/500000000000 : ℝ) (248345060179/250000000000 : ℝ) (124172530093/125000000000 : ℝ) (993380240747/1000000000000 : ℝ) (124172530093/125000000000 : ℝ) (993380240747/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (109/1024 : ℝ)) 3 (124172530093/125000000000 : ℝ) (993380240747/1000000000000 : ℝ) (124172530093/125000000000 : ℝ) (993380240747/1000000000000 : ℝ) (124172530093/125000000000 : ℝ) (993380240747/1000000000000 : ℝ) (124172530093/125000000000 : ℝ) (993380240747/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (109/1024 : ℝ)) 4 (124172530093/125000000000 : ℝ) (993380240747/1000000000000 : ℝ) (124172530093/125000000000 : ℝ) (993380240747/1000000000000 : ℝ) (124172530093/125000000000 : ℝ) (993380240747/1000000000000 : ℝ) (124172530093/125000000000 : ℝ) (993380240747/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (109/1024 : ℝ)) 5 (124172530093/125000000000 : ℝ) (993380240747/1000000000000 : ℝ) (124172530093/125000000000 : ℝ) (993380240747/1000000000000 : ℝ) (124172530093/125000000000 : ℝ) (993380240747/1000000000000 : ℝ) (124172530093/125000000000 : ℝ) (993380240747/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (109/1024 : ℝ)) 6 (124172530093/125000000000 : ℝ) (993380240747/1000000000000 : ℝ) (124172530093/125000000000 : ℝ) (993380240747/1000000000000 : ℝ) (124172530093/125000000000 : ℝ) (993380240747/1000000000000 : ℝ) (124172530093/125000000000 : ℝ) (993380240747/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (109/1024 : ℝ)) 7 (124172530093/125000000000 : ℝ) (993380240747/1000000000000 : ℝ) (124172530093/125000000000 : ℝ) (993380240747/1000000000000 : ℝ) (124172530093/125000000000 : ℝ) (993380240747/1000000000000 : ℝ) (124172530093/125000000000 : ℝ) (993380240747/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (109/1024 : ℝ))) (2025631337/12500000000 : ℝ) (162050506967/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (109/1024 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (2025631337/12500000000 : ℝ) (162050506967/1000000000000 : ℝ) (14525631337/25000000000 : ℝ) (145256313371/250000000000 : ℝ) (80510994767/200000000000 : ℝ) (80510994769/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (109/1024 : ℝ))) 1 (14525631337/25000000000 : ℝ) (145256313371/250000000000 : ℝ) (80510994767/200000000000 : ℝ) (80510994769/200000000000 : ℝ) (491790113657/1000000000000 : ℝ) (98358022733/200000000000 : ℝ) (48362651469/100000000000 : ℝ) (483626514699/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (109/1024 : ℝ))) 2 (491790113657/1000000000000 : ℝ) (98358022733/200000000000 : ℝ) (48362651469/100000000000 : ℝ) (483626514699/1000000000000 : ℝ) (487708314173/1000000000000 : ℝ) (243854157091/500000000000 : ℝ) (243845616439/500000000000 : ℝ) (60961404111/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (109/1024 : ℝ))) 3 (487708314173/1000000000000 : ℝ) (243854157091/500000000000 : ℝ) (243845616439/500000000000 : ℝ) (60961404111/125000000000 : ℝ) (19507990941/40000000000 : ℝ) (97539954707/200000000000 : ℝ) (9753995469/20000000000 : ℝ) (487699773461/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (109/1024 : ℝ))) 4 (19507990941/40000000000 : ℝ) (97539954707/200000000000 : ℝ) (9753995469/20000000000 : ℝ) (487699773461/1000000000000 : ℝ) (487699773487/1000000000000 : ℝ) (243849886749/500000000000 : ℝ) (487699773487/1000000000000 : ℝ) (243849886749/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (109/1024 : ℝ))) 5 (487699773487/1000000000000 : ℝ) (243849886749/500000000000 : ℝ) (487699773487/1000000000000 : ℝ) (243849886749/500000000000 : ℝ) (487699773487/1000000000000 : ℝ) (243849886749/500000000000 : ℝ) (487699773487/1000000000000 : ℝ) (243849886749/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (109/1024 : ℝ))) 6 (487699773487/1000000000000 : ℝ) (243849886749/500000000000 : ℝ) (487699773487/1000000000000 : ℝ) (243849886749/500000000000 : ℝ) (487699773487/1000000000000 : ℝ) (243849886749/500000000000 : ℝ) (487699773487/1000000000000 : ℝ) (243849886749/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (109/1024 : ℝ))) 7 (487699773487/1000000000000 : ℝ) (243849886749/500000000000 : ℝ) (487699773487/1000000000000 : ℝ) (243849886749/500000000000 : ℝ) (487699773487/1000000000000 : ℝ) (243849886749/500000000000 : ℝ) (487699773487/1000000000000 : ℝ) (243849886749/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (109/1024 : ℝ)) hmem 8 (124172530093/125000000000 : ℝ) (993380240747/1000000000000 : ℝ) (124172530093/125000000000 : ℝ) (993380240747/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (109/1024 : ℝ))) hcmem 8 (487699773487/1000000000000 : ℝ) (243849886749/500000000000 : ℝ) (487699773487/1000000000000 : ℝ) (243849886749/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (109/1024 : ℝ)) (124172530093/125000000000 : ℝ) (993380240747/1000000000000 : ℝ) (487699773487/1000000000000 : ℝ) (243849886749/500000000000 : ℝ) (385591026149/500000000000 : ℝ) (771182052319/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0018_exp_lower
  have heNumeric : (2055627304027/1000000000000 : ℝ)/4 ≤ Real.exp (-665713302319/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2055627304027/1000000000000 : ℝ)/4 ≤ Real.exp ((27/256 : ℝ)-(771182052319/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (27/256 : ℝ) (109/1024 : ℝ) (771182052319/1000000000000 : ℝ) (2055627304027/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0019; no trusted numerical premise.
theorem cover8_leaf0019_exp_radius : (998322941040739381/1000000000000000000 : ℝ) ≤ Real.exp ((-55/4096 : ℝ)/8) ∧ Real.exp ((-55/4096 : ℝ)/8) ≤ (499161470520369691/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-55/4096 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0019_exp_lower : (460069807888280337/500000000000000000 : ℝ) ≤ Real.exp ((-41614932087/62500000000 : ℝ)/8) ∧ Real.exp ((-41614932087/62500000000 : ℝ)/8) ≤ (36805584631062427/40000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-41614932087/62500000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0019_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513842277673/250000000000 : ℝ) ≤ 4*Real.exp (109/1024 : ℝ)*Real.exp (-mu (radius 8 (55/512 : ℝ))) ∧ (20549/10000 : ℝ) < (513842277673/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (55/512 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0019_exp_radius
  have hrNumeric : (1927074249/1953125000 : ℝ) ≤ Real.exp (-55/4096 : ℝ) ∧ Real.exp (-55/4096 : ℝ) ≤ (986662015489/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (1927074249/1953125000 : ℝ) ≤ (radius 8 (55/512 : ℝ)) ∧ (radius 8 (55/512 : ℝ)) ≤ (986662015489/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (55/512 : ℝ)) (1927074249/1953125000 : ℝ) (986662015489/1000000000000 : ℝ) (162782269277/1000000000000 : ℝ) (40695567321/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (55/512 : ℝ)) (1927074249/1953125000 : ℝ) (986662015489/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (55/512 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (1927074249/1953125000 : ℝ) (986662015489/1000000000000 : ℝ) (3880199249/3906250000 : ℝ) (198666201549/200000000000 : ℝ) (993308620463/1000000000000 : ℝ) (198661724093/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (55/512 : ℝ)) 1 (3880199249/3906250000 : ℝ) (198666201549/200000000000 : ℝ) (993308620463/1000000000000 : ℝ) (198661724093/200000000000 : ℝ) (993319814103/1000000000000 : ℝ) (198663962821/200000000000 : ℝ) (24832995351/25000000000 : ℝ) (496659907021/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (55/512 : ℝ)) 2 (993319814103/1000000000000 : ℝ) (198663962821/200000000000 : ℝ) (24832995351/25000000000 : ℝ) (496659907021/500000000000 : ℝ) (993319814071/1000000000000 : ℝ) (496659907037/500000000000 : ℝ) (993319814071/1000000000000 : ℝ) (496659907037/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (55/512 : ℝ)) 3 (993319814071/1000000000000 : ℝ) (496659907037/500000000000 : ℝ) (993319814071/1000000000000 : ℝ) (496659907037/500000000000 : ℝ) (993319814071/1000000000000 : ℝ) (496659907037/500000000000 : ℝ) (993319814071/1000000000000 : ℝ) (496659907037/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (55/512 : ℝ)) 4 (993319814071/1000000000000 : ℝ) (496659907037/500000000000 : ℝ) (993319814071/1000000000000 : ℝ) (496659907037/500000000000 : ℝ) (993319814071/1000000000000 : ℝ) (496659907037/500000000000 : ℝ) (993319814071/1000000000000 : ℝ) (496659907037/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (55/512 : ℝ)) 5 (993319814071/1000000000000 : ℝ) (496659907037/500000000000 : ℝ) (993319814071/1000000000000 : ℝ) (496659907037/500000000000 : ℝ) (993319814071/1000000000000 : ℝ) (496659907037/500000000000 : ℝ) (993319814071/1000000000000 : ℝ) (496659907037/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (55/512 : ℝ)) 6 (993319814071/1000000000000 : ℝ) (496659907037/500000000000 : ℝ) (993319814071/1000000000000 : ℝ) (496659907037/500000000000 : ℝ) (993319814071/1000000000000 : ℝ) (496659907037/500000000000 : ℝ) (993319814071/1000000000000 : ℝ) (496659907037/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (55/512 : ℝ)) 7 (993319814071/1000000000000 : ℝ) (496659907037/500000000000 : ℝ) (993319814071/1000000000000 : ℝ) (496659907037/500000000000 : ℝ) (993319814071/1000000000000 : ℝ) (496659907037/500000000000 : ℝ) (993319814071/1000000000000 : ℝ) (496659907037/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (55/512 : ℝ))) (162782269277/1000000000000 : ℝ) (40695567321/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (55/512 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (162782269277/1000000000000 : ℝ) (40695567321/250000000000 : ℝ) (290695567319/500000000000 : ℝ) (290695567321/500000000000 : ℝ) (80692569491/200000000000 : ℝ) (80692569493/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (55/512 : ℝ))) 1 (290695567319/500000000000 : ℝ) (290695567321/500000000000 : ℝ) (80692569491/200000000000 : ℝ) (80692569493/200000000000 : ℝ) (246213495523/500000000000 : ℝ) (246213495527/500000000000 : ℝ) (242161992613/500000000000 : ℝ) (96864797047/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (55/512 : ℝ))) 2 (246213495523/500000000000 : ℝ) (246213495527/500000000000 : ℝ) (242161992613/500000000000 : ℝ) (96864797047/200000000000 : ℝ) (61046936017/125000000000 : ℝ) (97675097629/200000000000 : ℝ) (244179341231/500000000000 : ℝ) (488358682471/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (55/512 : ℝ))) 3 (61046936017/125000000000 : ℝ) (97675097629/200000000000 : ℝ) (244179341231/500000000000 : ℝ) (488358682471/1000000000000 : ℝ) (488367085299/1000000000000 : ℝ) (122091771327/250000000000 : ℝ) (244183542613/500000000000 : ℝ) (122091771309/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (55/512 : ℝ))) 4 (488367085299/1000000000000 : ℝ) (122091771327/250000000000 : ℝ) (244183542613/500000000000 : ℝ) (122091771309/250000000000 : ℝ) (244183542631/500000000000 : ℝ) (61045885659/125000000000 : ℝ) (244183542631/500000000000 : ℝ) (61045885659/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (55/512 : ℝ))) 5 (244183542631/500000000000 : ℝ) (61045885659/125000000000 : ℝ) (244183542631/500000000000 : ℝ) (61045885659/125000000000 : ℝ) (244183542631/500000000000 : ℝ) (61045885659/125000000000 : ℝ) (244183542631/500000000000 : ℝ) (61045885659/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (55/512 : ℝ))) 6 (244183542631/500000000000 : ℝ) (61045885659/125000000000 : ℝ) (244183542631/500000000000 : ℝ) (61045885659/125000000000 : ℝ) (244183542631/500000000000 : ℝ) (61045885659/125000000000 : ℝ) (244183542631/500000000000 : ℝ) (61045885659/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (55/512 : ℝ))) 7 (244183542631/500000000000 : ℝ) (61045885659/125000000000 : ℝ) (244183542631/500000000000 : ℝ) (61045885659/125000000000 : ℝ) (244183542631/500000000000 : ℝ) (61045885659/125000000000 : ℝ) (244183542631/500000000000 : ℝ) (61045885659/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (55/512 : ℝ)) hmem 8 (993319814071/1000000000000 : ℝ) (496659907037/500000000000 : ℝ) (993319814071/1000000000000 : ℝ) (496659907037/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (55/512 : ℝ))) hcmem 8 (244183542631/500000000000 : ℝ) (61045885659/125000000000 : ℝ) (244183542631/500000000000 : ℝ) (61045885659/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (55/512 : ℝ)) (993319814071/1000000000000 : ℝ) (496659907037/500000000000 : ℝ) (244183542631/500000000000 : ℝ) (61045885659/125000000000 : ℝ) (772284225873/1000000000000 : ℝ) (193071056473/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0019_exp_lower
  have heNumeric : (513842277673/250000000000 : ℝ)/4 ≤ Real.exp (-41614932087/62500000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513842277673/250000000000 : ℝ)/4 ≤ Real.exp ((109/1024 : ℝ)-(193071056473/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (109/1024 : ℝ) (55/512 : ℝ) (193071056473/250000000000 : ℝ) (513842277673/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0020; no trusted numerical premise.
theorem cover8_leaf0020_exp_radius : (998307707957785281/1000000000000000000 : ℝ) ≤ Real.exp ((-111/8192 : ℝ)/8) ∧ Real.exp ((-111/8192 : ℝ)/8) ≤ (499153853978892641/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-111/8192 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0020_exp_lower : (460062978859070557/500000000000000000 : ℝ) ≤ Real.exp ((-332978830989/500000000000 : ℝ)/8) ∧ Real.exp ((-332978830989/500000000000 : ℝ)/8) ≤ (184025191543628223/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-332978830989/500000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0020_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2055125053007/1000000000000 : ℝ) ≤ 4*Real.exp (55/512 : ℝ)*Real.exp (-mu (radius 8 (111/1024 : ℝ))) ∧ (20549/10000 : ℝ) < (2055125053007/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (111/1024 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0020_exp_radius
  have hrNumeric : (986541580699/1000000000000 : ℝ) ≤ Real.exp (-111/8192 : ℝ) ∧ Real.exp (-111/8192 : ℝ) ≤ (9865415807/10000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (986541580699/1000000000000 : ℝ) ≤ (radius 8 (111/1024 : ℝ)) ∧ (radius 8 (111/1024 : ℝ)) ≤ (9865415807/10000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (111/1024 : ℝ)) (986541580699/1000000000000 : ℝ) (9865415807/10000000000 : ℝ) (163510579321/1000000000000 : ℝ) (1277426401/7812500000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (111/1024 : ℝ)) (986541580699/1000000000000 : ℝ) (9865415807/10000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (111/1024 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (986541580699/1000000000000 : ℝ) (9865415807/10000000000 : ℝ) (993270790349/1000000000000 : ℝ) (19865415807/20000000000 : ℝ) (993247995567/1000000000000 : ℝ) (993247995569/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (111/1024 : ℝ)) 1 (993270790349/1000000000000 : ℝ) (19865415807/20000000000 : ℝ) (993247995567/1000000000000 : ℝ) (993247995569/1000000000000 : ℝ) (496629696479/500000000000 : ℝ) (3103935603/3125000000 : ℝ) (248314848223/250000000000 : ℝ) (198651878579/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (111/1024 : ℝ)) 2 (496629696479/500000000000 : ℝ) (3103935603/3125000000 : ℝ) (248314848223/250000000000 : ℝ) (198651878579/200000000000 : ℝ) (39730375717/40000000000 : ℝ) (31039356029/31250000000 : ℝ) (248314848231/250000000000 : ℝ) (31039356029/31250000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (111/1024 : ℝ)) 3 (39730375717/40000000000 : ℝ) (31039356029/31250000000 : ℝ) (248314848231/250000000000 : ℝ) (31039356029/31250000000 : ℝ) (248314848231/250000000000 : ℝ) (31039356029/31250000000 : ℝ) (248314848231/250000000000 : ℝ) (31039356029/31250000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (111/1024 : ℝ)) 4 (248314848231/250000000000 : ℝ) (31039356029/31250000000 : ℝ) (248314848231/250000000000 : ℝ) (31039356029/31250000000 : ℝ) (248314848231/250000000000 : ℝ) (31039356029/31250000000 : ℝ) (248314848231/250000000000 : ℝ) (31039356029/31250000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (111/1024 : ℝ)) 5 (248314848231/250000000000 : ℝ) (31039356029/31250000000 : ℝ) (248314848231/250000000000 : ℝ) (31039356029/31250000000 : ℝ) (248314848231/250000000000 : ℝ) (31039356029/31250000000 : ℝ) (248314848231/250000000000 : ℝ) (31039356029/31250000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (111/1024 : ℝ)) 6 (248314848231/250000000000 : ℝ) (31039356029/31250000000 : ℝ) (248314848231/250000000000 : ℝ) (31039356029/31250000000 : ℝ) (248314848231/250000000000 : ℝ) (31039356029/31250000000 : ℝ) (248314848231/250000000000 : ℝ) (31039356029/31250000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (111/1024 : ℝ)) 7 (248314848231/250000000000 : ℝ) (31039356029/31250000000 : ℝ) (248314848231/250000000000 : ℝ) (31039356029/31250000000 : ℝ) (248314848231/250000000000 : ℝ) (31039356029/31250000000 : ℝ) (248314848231/250000000000 : ℝ) (31039356029/31250000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (111/1024 : ℝ))) (163510579321/1000000000000 : ℝ) (1277426401/7812500000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (111/1024 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (163510579321/1000000000000 : ℝ) (1277426401/7812500000 : ℝ) (29087764483/50000000000 : ℝ) (9089926401/15625000000 : ℝ) (202182207007/500000000000 : ℝ) (404364414023/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (111/1024 : ℝ))) 1 (29087764483/50000000000 : ℝ) (9089926401/15625000000 : ℝ) (202182207007/500000000000 : ℝ) (404364414023/1000000000000 : ℝ) (493059851837/1000000000000 : ℝ) (123264962961/250000000000 : ℝ) (485016635593/1000000000000 : ℝ) (242508317801/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (111/1024 : ℝ))) 2 (493059851837/1000000000000 : ℝ) (123264962961/250000000000 : ℝ) (485016635593/1000000000000 : ℝ) (242508317801/500000000000 : ℝ) (97807648743/200000000000 : ℝ) (489038243723/1000000000000 : ℝ) (489021707579/1000000000000 : ℝ) (122255426897/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (111/1024 : ℝ))) 3 (97807648743/200000000000 : ℝ) (489038243723/1000000000000 : ℝ) (489021707579/1000000000000 : ℝ) (122255426897/250000000000 : ℝ) (489029975647/1000000000000 : ℝ) (61128746957/125000000000 : ℝ) (489029975577/1000000000000 : ℝ) (244514987793/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (111/1024 : ℝ))) 4 (489029975647/1000000000000 : ℝ) (61128746957/125000000000 : ℝ) (489029975577/1000000000000 : ℝ) (244514987793/500000000000 : ℝ) (122257493903/250000000000 : ℝ) (489029975621/1000000000000 : ℝ) (489029975611/1000000000000 : ℝ) (489029975621/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (111/1024 : ℝ))) 5 (122257493903/250000000000 : ℝ) (489029975621/1000000000000 : ℝ) (489029975611/1000000000000 : ℝ) (489029975621/1000000000000 : ℝ) (489029975611/1000000000000 : ℝ) (489029975621/1000000000000 : ℝ) (489029975611/1000000000000 : ℝ) (489029975621/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (111/1024 : ℝ))) 6 (489029975611/1000000000000 : ℝ) (489029975621/1000000000000 : ℝ) (489029975611/1000000000000 : ℝ) (489029975621/1000000000000 : ℝ) (489029975611/1000000000000 : ℝ) (489029975621/1000000000000 : ℝ) (489029975611/1000000000000 : ℝ) (489029975621/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (111/1024 : ℝ))) 7 (489029975611/1000000000000 : ℝ) (489029975621/1000000000000 : ℝ) (489029975611/1000000000000 : ℝ) (489029975621/1000000000000 : ℝ) (489029975611/1000000000000 : ℝ) (489029975621/1000000000000 : ℝ) (489029975611/1000000000000 : ℝ) (489029975621/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (111/1024 : ℝ)) hmem 8 (248314848231/250000000000 : ℝ) (31039356029/31250000000 : ℝ) (248314848231/250000000000 : ℝ) (31039356029/31250000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (111/1024 : ℝ))) hcmem 8 (489029975611/1000000000000 : ℝ) (489029975621/1000000000000 : ℝ) (489029975611/1000000000000 : ℝ) (489029975621/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (111/1024 : ℝ)) (248314848231/250000000000 : ℝ) (31039356029/31250000000 : ℝ) (489029975611/1000000000000 : ℝ) (489029975621/1000000000000 : ℝ) (386689768479/500000000000 : ℝ) (386689768489/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0020_exp_lower
  have heNumeric : (2055125053007/1000000000000 : ℝ)/4 ≤ Real.exp (-332978830989/500000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2055125053007/1000000000000 : ℝ)/4 ≤ Real.exp ((55/512 : ℝ)-(386689768489/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (55/512 : ℝ) (111/1024 : ℝ) (386689768489/500000000000 : ℝ) (2055125053007/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0021; no trusted numerical premise.
theorem cover8_leaf0021_exp_radius : (249575022875868047/250000000000000000 : ℝ) ≤ Real.exp ((-223/16384 : ℝ)/8) ∧ Real.exp ((-223/16384 : ℝ)/8) ≤ (998300091503472189/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-223/16384 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0021_exp_lower : (460087791094304417/500000000000000000 : ℝ) ≤ Real.exp ((-665526215549/1000000000000 : ℝ)/8) ∧ Real.exp ((-665526215549/1000000000000 : ℝ)/8) ≤ (184035116437721767/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-665526215549/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0021_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2056011920677/1000000000000 : ℝ) ≤ 4*Real.exp (111/1024 : ℝ)*Real.exp (-mu (radius 8 (223/2048 : ℝ))) ∧ (20549/10000 : ℝ) < (2056011920677/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (223/2048 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0021_exp_radius
  have hrNumeric : (986481368817/1000000000000 : ℝ) ≤ Real.exp (-223/16384 : ℝ) ∧ Real.exp (-223/16384 : ℝ) ≤ (493240684409/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (986481368817/1000000000000 : ℝ) ≤ (radius 8 (223/2048 : ℝ)) ∧ (radius 8 (223/2048 : ℝ)) ≤ (493240684409/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (223/2048 : ℝ)) (986481368817/1000000000000 : ℝ) (493240684409/500000000000 : ℝ) (163873454149/1000000000000 : ℝ) (40968363539/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (223/2048 : ℝ)) (986481368817/1000000000000 : ℝ) (493240684409/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (223/2048 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (986481368817/1000000000000 : ℝ) (493240684409/500000000000 : ℝ) (124155085551/125000000000 : ℝ) (993240684409/1000000000000 : ℝ) (496608842253/500000000000 : ℝ) (248304421127/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (223/2048 : ℝ)) 1 (124155085551/125000000000 : ℝ) (993240684409/1000000000000 : ℝ) (496608842253/500000000000 : ℝ) (248304421127/250000000000 : ℝ) (993229184457/1000000000000 : ℝ) (993229184459/1000000000000 : ℝ) (99322918439/100000000000 : ℝ) (124153648049/125000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (223/2048 : ℝ)) 2 (993229184457/1000000000000 : ℝ) (993229184459/1000000000000 : ℝ) (99322918439/100000000000 : ℝ) (124153648049/125000000000 : ℝ) (993229184423/1000000000000 : ℝ) (496614592213/500000000000 : ℝ) (993229184423/1000000000000 : ℝ) (496614592213/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (223/2048 : ℝ)) 3 (993229184423/1000000000000 : ℝ) (496614592213/500000000000 : ℝ) (993229184423/1000000000000 : ℝ) (496614592213/500000000000 : ℝ) (993229184423/1000000000000 : ℝ) (496614592213/500000000000 : ℝ) (993229184423/1000000000000 : ℝ) (496614592213/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (223/2048 : ℝ)) 4 (993229184423/1000000000000 : ℝ) (496614592213/500000000000 : ℝ) (993229184423/1000000000000 : ℝ) (496614592213/500000000000 : ℝ) (993229184423/1000000000000 : ℝ) (496614592213/500000000000 : ℝ) (993229184423/1000000000000 : ℝ) (496614592213/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (223/2048 : ℝ)) 5 (993229184423/1000000000000 : ℝ) (496614592213/500000000000 : ℝ) (993229184423/1000000000000 : ℝ) (496614592213/500000000000 : ℝ) (993229184423/1000000000000 : ℝ) (496614592213/500000000000 : ℝ) (993229184423/1000000000000 : ℝ) (496614592213/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (223/2048 : ℝ)) 6 (993229184423/1000000000000 : ℝ) (496614592213/500000000000 : ℝ) (993229184423/1000000000000 : ℝ) (496614592213/500000000000 : ℝ) (993229184423/1000000000000 : ℝ) (496614592213/500000000000 : ℝ) (993229184423/1000000000000 : ℝ) (496614592213/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (223/2048 : ℝ)) 7 (993229184423/1000000000000 : ℝ) (496614592213/500000000000 : ℝ) (993229184423/1000000000000 : ℝ) (496614592213/500000000000 : ℝ) (993229184423/1000000000000 : ℝ) (496614592213/500000000000 : ℝ) (993229184423/1000000000000 : ℝ) (496614592213/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (223/2048 : ℝ))) (163873454149/1000000000000 : ℝ) (40968363539/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (223/2048 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (163873454149/1000000000000 : ℝ) (40968363539/250000000000 : ℝ) (290968363537/500000000000 : ℝ) (290968363539/500000000000 : ℝ) (404812863121/1000000000000 : ℝ) (404812863131/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (223/2048 : ℝ))) 1 (290968363537/500000000000 : ℝ) (290968363539/500000000000 : ℝ) (404812863121/1000000000000 : ℝ) (404812863131/1000000000000 : ℝ) (493374795097/1000000000000 : ℝ) (98674959021/200000000000 : ℝ) (242680588759/500000000000 : ℝ) (485361177527/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (223/2048 : ℝ))) 2 (493374795097/1000000000000 : ℝ) (98674959021/200000000000 : ℝ) (242680588759/500000000000 : ℝ) (485361177527/1000000000000 : ℝ) (489367986307/1000000000000 : ℝ) (122341996579/250000000000 : ℝ) (97870316543/200000000000 : ℝ) (122337895681/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (223/2048 : ℝ))) 3 (489367986307/1000000000000 : ℝ) (122341996579/250000000000 : ℝ) (97870316543/200000000000 : ℝ) (122337895681/250000000000 : ℝ) (489359784511/1000000000000 : ℝ) (12233994613/25000000000 : ℝ) (244679892221/500000000000 : ℝ) (122339946113/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (223/2048 : ℝ))) 4 (489359784511/1000000000000 : ℝ) (12233994613/25000000000 : ℝ) (244679892221/500000000000 : ℝ) (122339946113/250000000000 : ℝ) (122339946119/250000000000 : ℝ) (244679892243/500000000000 : ℝ) (122339946119/250000000000 : ℝ) (244679892243/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (223/2048 : ℝ))) 5 (122339946119/250000000000 : ℝ) (244679892243/500000000000 : ℝ) (122339946119/250000000000 : ℝ) (244679892243/500000000000 : ℝ) (122339946119/250000000000 : ℝ) (244679892243/500000000000 : ℝ) (122339946119/250000000000 : ℝ) (244679892243/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (223/2048 : ℝ))) 6 (122339946119/250000000000 : ℝ) (244679892243/500000000000 : ℝ) (122339946119/250000000000 : ℝ) (244679892243/500000000000 : ℝ) (122339946119/250000000000 : ℝ) (244679892243/500000000000 : ℝ) (122339946119/250000000000 : ℝ) (244679892243/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (223/2048 : ℝ))) 7 (122339946119/250000000000 : ℝ) (244679892243/500000000000 : ℝ) (122339946119/250000000000 : ℝ) (244679892243/500000000000 : ℝ) (122339946119/250000000000 : ℝ) (244679892243/500000000000 : ℝ) (122339946119/250000000000 : ℝ) (244679892243/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (223/2048 : ℝ)) hmem 8 (993229184423/1000000000000 : ℝ) (496614592213/500000000000 : ℝ) (993229184423/1000000000000 : ℝ) (496614592213/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (223/2048 : ℝ))) hcmem 8 (122339946119/250000000000 : ℝ) (244679892243/500000000000 : ℝ) (122339946119/250000000000 : ℝ) (244679892243/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (223/2048 : ℝ)) (993229184423/1000000000000 : ℝ) (496614592213/500000000000 : ℝ) (122339946119/250000000000 : ℝ) (244679892243/500000000000 : ℝ) (773924653029/1000000000000 : ℝ) (773924653049/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0021_exp_lower
  have heNumeric : (2056011920677/1000000000000 : ℝ)/4 ≤ Real.exp (-665526215549/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2056011920677/1000000000000 : ℝ)/4 ≤ Real.exp ((111/1024 : ℝ)-(773924653049/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (111/1024 : ℝ) (223/2048 : ℝ) (773924653049/1000000000000 : ℝ) (2056011920677/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0022; no trusted numerical premise.
theorem cover8_leaf0022_exp_radius : (998292475107267807/1000000000000000000 : ℝ) ≤ Real.exp ((-7/512 : ℝ)/8) ∧ Real.exp ((-7/512 : ℝ)/8) ≤ (31196639847102119/31250000000000000 : ℝ) := by
  have h := exp_small_bounds ((-7/512 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0022_exp_lower : (460084618821602807/500000000000000000 : ℝ) ≤ Real.exp ((-166395343793/250000000000 : ℝ)/8) ∧ Real.exp ((-166395343793/250000000000 : ℝ)/8) ≤ (184033847528641123/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-166395343793/250000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0022_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027949257481/500000000000 : ℝ) ≤ 4*Real.exp (223/2048 : ℝ)*Real.exp (-mu (radius 8 (7/64 : ℝ))) ∧ (20549/10000 : ℝ) < (1027949257481/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (7/64 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0022_exp_radius
  have hrNumeric : (986421160609/1000000000000 : ℝ) ≤ Real.exp (-7/512 : ℝ) ∧ Real.exp (-7/512 : ℝ) ≤ (98642116061/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (986421160609/1000000000000 : ℝ) ≤ (radius 8 (7/64 : ℝ)) ∧ (radius 8 (7/64 : ℝ)) ≤ (98642116061/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (7/64 : ℝ)) (986421160609/1000000000000 : ℝ) (98642116061/100000000000 : ℝ) (82117741537/500000000000 : ℝ) (164235483081/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (7/64 : ℝ)) (986421160609/1000000000000 : ℝ) (98642116061/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (7/64 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (986421160609/1000000000000 : ℝ) (98642116061/100000000000 : ℝ) (62075661269/62500000000 : ℝ) (198642116061/200000000000 : ℝ) (99318737437/100000000000 : ℝ) (248296843593/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (7/64 : ℝ)) 1 (62075661269/62500000000 : ℝ) (198642116061/200000000000 : ℝ) (99318737437/100000000000 : ℝ) (248296843593/250000000000 : ℝ) (993198977337/1000000000000 : ℝ) (993198977339/1000000000000 : ℝ) (993198977269/1000000000000 : ℝ) (993198977271/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (7/64 : ℝ)) 2 (993198977337/1000000000000 : ℝ) (993198977339/1000000000000 : ℝ) (993198977269/1000000000000 : ℝ) (993198977271/1000000000000 : ℝ) (993198977303/1000000000000 : ℝ) (198639795461/200000000000 : ℝ) (496599488651/500000000000 : ℝ) (198639795461/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (7/64 : ℝ)) 3 (993198977303/1000000000000 : ℝ) (198639795461/200000000000 : ℝ) (496599488651/500000000000 : ℝ) (198639795461/200000000000 : ℝ) (496599488651/500000000000 : ℝ) (198639795461/200000000000 : ℝ) (496599488651/500000000000 : ℝ) (198639795461/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (7/64 : ℝ)) 4 (496599488651/500000000000 : ℝ) (198639795461/200000000000 : ℝ) (496599488651/500000000000 : ℝ) (198639795461/200000000000 : ℝ) (496599488651/500000000000 : ℝ) (198639795461/200000000000 : ℝ) (496599488651/500000000000 : ℝ) (198639795461/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (7/64 : ℝ)) 5 (496599488651/500000000000 : ℝ) (198639795461/200000000000 : ℝ) (496599488651/500000000000 : ℝ) (198639795461/200000000000 : ℝ) (496599488651/500000000000 : ℝ) (198639795461/200000000000 : ℝ) (496599488651/500000000000 : ℝ) (198639795461/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (7/64 : ℝ)) 6 (496599488651/500000000000 : ℝ) (198639795461/200000000000 : ℝ) (496599488651/500000000000 : ℝ) (198639795461/200000000000 : ℝ) (496599488651/500000000000 : ℝ) (198639795461/200000000000 : ℝ) (496599488651/500000000000 : ℝ) (198639795461/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (7/64 : ℝ)) 7 (496599488651/500000000000 : ℝ) (198639795461/200000000000 : ℝ) (496599488651/500000000000 : ℝ) (198639795461/200000000000 : ℝ) (496599488651/500000000000 : ℝ) (198639795461/200000000000 : ℝ) (496599488651/500000000000 : ℝ) (198639795461/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (7/64 : ℝ))) (82117741537/500000000000 : ℝ) (164235483081/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (7/64 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (82117741537/500000000000 : ℝ) (164235483081/1000000000000 : ℝ) (582117741537/1000000000000 : ℝ) (582117741541/1000000000000 : ℝ) (25328735771/62500000000 : ℝ) (81051954469/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (7/64 : ℝ))) 1 (582117741537/1000000000000 : ℝ) (582117741541/1000000000000 : ℝ) (25328735771/62500000000 : ℝ) (81051954469/200000000000 : ℝ) (61711094617/125000000000 : ℝ) (493688756943/1000000000000 : ℝ) (242852271663/500000000000 : ℝ) (242852271667/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (7/64 : ℝ))) 2 (61711094617/125000000000 : ℝ) (493688756943/1000000000000 : ℝ) (242852271663/500000000000 : ℝ) (242852271667/500000000000 : ℝ) (489696650131/1000000000000 : ℝ) (489696650139/1000000000000 : ℝ) (244840188813/500000000000 : ℝ) (97936075527/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (7/64 : ℝ))) 3 (489696650131/1000000000000 : ℝ) (489696650139/1000000000000 : ℝ) (244840188813/500000000000 : ℝ) (97936075527/200000000000 : ℝ) (244844256939/500000000000 : ℝ) (489688513887/1000000000000 : ℝ) (48968851381/100000000000 : ℝ) (24484425691/50000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (7/64 : ℝ))) 4 (244844256939/500000000000 : ℝ) (489688513887/1000000000000 : ℝ) (48968851381/100000000000 : ℝ) (24484425691/50000000000 : ℝ) (122422128461/250000000000 : ℝ) (244844256927/500000000000 : ℝ) (489688513843/1000000000000 : ℝ) (244844256927/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (7/64 : ℝ))) 5 (122422128461/250000000000 : ℝ) (244844256927/500000000000 : ℝ) (489688513843/1000000000000 : ℝ) (244844256927/500000000000 : ℝ) (489688513843/1000000000000 : ℝ) (244844256927/500000000000 : ℝ) (489688513843/1000000000000 : ℝ) (244844256927/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (7/64 : ℝ))) 6 (489688513843/1000000000000 : ℝ) (244844256927/500000000000 : ℝ) (489688513843/1000000000000 : ℝ) (244844256927/500000000000 : ℝ) (489688513843/1000000000000 : ℝ) (244844256927/500000000000 : ℝ) (489688513843/1000000000000 : ℝ) (244844256927/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (7/64 : ℝ))) 7 (489688513843/1000000000000 : ℝ) (244844256927/500000000000 : ℝ) (489688513843/1000000000000 : ℝ) (244844256927/500000000000 : ℝ) (489688513843/1000000000000 : ℝ) (244844256927/500000000000 : ℝ) (489688513843/1000000000000 : ℝ) (244844256927/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (7/64 : ℝ)) hmem 8 (496599488651/500000000000 : ℝ) (198639795461/200000000000 : ℝ) (496599488651/500000000000 : ℝ) (198639795461/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (7/64 : ℝ))) hcmem 8 (489688513843/1000000000000 : ℝ) (244844256927/500000000000 : ℝ) (489688513843/1000000000000 : ℝ) (244844256927/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (7/64 : ℝ)) (496599488651/500000000000 : ℝ) (198639795461/200000000000 : ℝ) (489688513843/1000000000000 : ℝ) (244844256927/500000000000 : ℝ) (774468093901/1000000000000 : ℝ) (387234046961/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0022_exp_lower
  have heNumeric : (1027949257481/500000000000 : ℝ)/4 ≤ Real.exp (-166395343793/250000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027949257481/500000000000 : ℝ)/4 ≤ Real.exp ((223/2048 : ℝ)-(387234046961/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (223/2048 : ℝ) (7/64 : ℝ) (387234046961/500000000000 : ℝ) (1027949257481/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0023; no trusted numerical premise.
theorem cover8_leaf0023_exp_radius : (998284858769171697/1000000000000000000 : ℝ) ≤ Real.exp ((-225/16384 : ℝ)/8) ∧ Real.exp ((-225/16384 : ℝ)/8) ≤ (499142429384585849/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-225/16384 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0023_exp_lower : (920163084316450449/1000000000000000000 : ℝ) ≤ Real.exp ((-665634872699/1000000000000 : ℝ)/8) ∧ Real.exp ((-665634872699/1000000000000 : ℝ)/8) ≤ (18403261686329009/20000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-665634872699/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0023_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027894266209/500000000000 : ℝ) ≤ 4*Real.exp (7/64 : ℝ)*Real.exp (-mu (radius 8 (225/2048 : ℝ))) ∧ (20549/10000 : ℝ) < (1027894266209/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (225/2048 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0023_exp_radius
  have hrNumeric : (986360956077/1000000000000 : ℝ) ≤ Real.exp (-225/16384 : ℝ) ∧ Real.exp (-225/16384 : ℝ) ≤ (493180478039/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (986360956077/1000000000000 : ℝ) ≤ (radius 8 (225/2048 : ℝ)) ∧ (radius 8 (225/2048 : ℝ)) ≤ (493180478039/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (225/2048 : ℝ)) (986360956077/1000000000000 : ℝ) (493180478039/500000000000 : ℝ) (16459667167/100000000000 : ℝ) (164596671677/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (225/2048 : ℝ)) (986360956077/1000000000000 : ℝ) (493180478039/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (225/2048 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (986360956077/1000000000000 : ℝ) (493180478039/500000000000 : ℝ) (496590239019/500000000000 : ℝ) (993180478039/1000000000000 : ℝ) (993157065159/1000000000000 : ℝ) (993157065161/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (225/2048 : ℝ)) 1 (496590239019/500000000000 : ℝ) (993180478039/1000000000000 : ℝ) (993157065159/1000000000000 : ℝ) (993157065161/1000000000000 : ℝ) (496584385799/500000000000 : ℝ) (2482921929/2500000000 : ℝ) (993168771529/1000000000000 : ℝ) (248292192883/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (225/2048 : ℝ)) 2 (496584385799/500000000000 : ℝ) (2482921929/2500000000 : ℝ) (993168771529/1000000000000 : ℝ) (248292192883/250000000000 : ℝ) (993168771563/1000000000000 : ℝ) (496584385783/500000000000 : ℝ) (993168771563/1000000000000 : ℝ) (496584385783/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (225/2048 : ℝ)) 3 (993168771563/1000000000000 : ℝ) (496584385783/500000000000 : ℝ) (993168771563/1000000000000 : ℝ) (496584385783/500000000000 : ℝ) (993168771563/1000000000000 : ℝ) (496584385783/500000000000 : ℝ) (993168771563/1000000000000 : ℝ) (496584385783/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (225/2048 : ℝ)) 4 (993168771563/1000000000000 : ℝ) (496584385783/500000000000 : ℝ) (993168771563/1000000000000 : ℝ) (496584385783/500000000000 : ℝ) (993168771563/1000000000000 : ℝ) (496584385783/500000000000 : ℝ) (993168771563/1000000000000 : ℝ) (496584385783/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (225/2048 : ℝ)) 5 (993168771563/1000000000000 : ℝ) (496584385783/500000000000 : ℝ) (993168771563/1000000000000 : ℝ) (496584385783/500000000000 : ℝ) (993168771563/1000000000000 : ℝ) (496584385783/500000000000 : ℝ) (993168771563/1000000000000 : ℝ) (496584385783/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (225/2048 : ℝ)) 6 (993168771563/1000000000000 : ℝ) (496584385783/500000000000 : ℝ) (993168771563/1000000000000 : ℝ) (496584385783/500000000000 : ℝ) (993168771563/1000000000000 : ℝ) (496584385783/500000000000 : ℝ) (993168771563/1000000000000 : ℝ) (496584385783/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (225/2048 : ℝ)) 7 (993168771563/1000000000000 : ℝ) (496584385783/500000000000 : ℝ) (993168771563/1000000000000 : ℝ) (496584385783/500000000000 : ℝ) (993168771563/1000000000000 : ℝ) (496584385783/500000000000 : ℝ) (993168771563/1000000000000 : ℝ) (496584385783/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (225/2048 : ℝ))) (16459667167/100000000000 : ℝ) (164596671677/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (225/2048 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (16459667167/100000000000 : ℝ) (164596671677/1000000000000 : ℝ) (116459667167/200000000000 : ℝ) (582298335839/1000000000000 : ℝ) (81141030723/200000000000 : ℝ) (50713144203/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (225/2048 : ℝ))) 1 (116459667167/200000000000 : ℝ) (582298335839/1000000000000 : ℝ) (81141030723/200000000000 : ℝ) (50713144203/125000000000 : ℝ) (19760069789/40000000000 : ℝ) (123500436183/250000000000 : ℝ) (486046742391/1000000000000 : ℝ) (486046742399/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (225/2048 : ℝ))) 2 (19760069789/40000000000 : ℝ) (123500436183/250000000000 : ℝ) (486046742391/1000000000000 : ℝ) (486046742399/1000000000000 : ℝ) (245012121779/500000000000 : ℝ) (245012121783/500000000000 : ℝ) (490008100707/1000000000000 : ℝ) (122502025179/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (225/2048 : ℝ))) 3 (245012121779/500000000000 : ℝ) (245012121783/500000000000 : ℝ) (490008100707/1000000000000 : ℝ) (122502025179/250000000000 : ℝ) (122504043033/250000000000 : ℝ) (490016172141/1000000000000 : ℝ) (245008086033/500000000000 : ℝ) (19600646883/40000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (225/2048 : ℝ))) 4 (122504043033/250000000000 : ℝ) (490016172141/1000000000000 : ℝ) (245008086033/500000000000 : ℝ) (19600646883/40000000000 : ℝ) (490016172099/1000000000000 : ℝ) (122504043027/250000000000 : ℝ) (245008086049/500000000000 : ℝ) (122504043027/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (225/2048 : ℝ))) 5 (490016172099/1000000000000 : ℝ) (122504043027/250000000000 : ℝ) (245008086049/500000000000 : ℝ) (122504043027/250000000000 : ℝ) (245008086049/500000000000 : ℝ) (122504043027/250000000000 : ℝ) (245008086049/500000000000 : ℝ) (122504043027/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (225/2048 : ℝ))) 6 (245008086049/500000000000 : ℝ) (122504043027/250000000000 : ℝ) (245008086049/500000000000 : ℝ) (122504043027/250000000000 : ℝ) (245008086049/500000000000 : ℝ) (122504043027/250000000000 : ℝ) (245008086049/500000000000 : ℝ) (122504043027/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (225/2048 : ℝ))) 7 (245008086049/500000000000 : ℝ) (122504043027/250000000000 : ℝ) (245008086049/500000000000 : ℝ) (122504043027/250000000000 : ℝ) (245008086049/500000000000 : ℝ) (122504043027/250000000000 : ℝ) (245008086049/500000000000 : ℝ) (122504043027/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (225/2048 : ℝ)) hmem 8 (993168771563/1000000000000 : ℝ) (496584385783/500000000000 : ℝ) (993168771563/1000000000000 : ℝ) (496584385783/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (225/2048 : ℝ))) hcmem 8 (245008086049/500000000000 : ℝ) (122504043027/250000000000 : ℝ) (245008086049/500000000000 : ℝ) (122504043027/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (225/2048 : ℝ)) (993168771563/1000000000000 : ℝ) (496584385783/500000000000 : ℝ) (245008086049/500000000000 : ℝ) (122504043027/250000000000 : ℝ) (19375246817/25000000000 : ℝ) (775009872699/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0023_exp_lower
  have heNumeric : (1027894266209/500000000000 : ℝ)/4 ≤ Real.exp (-665634872699/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027894266209/500000000000 : ℝ)/4 ≤ Real.exp ((7/64 : ℝ)-(775009872699/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (7/64 : ℝ) (225/2048 : ℝ) (775009872699/1000000000000 : ℝ) (1027894266209/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0024; no trusted numerical premise.
theorem cover8_leaf0024_exp_radius : (998277242489183413/1000000000000000000 : ℝ) ≤ Real.exp ((-113/8192 : ℝ)/8) ∧ Real.exp ((-113/8192 : ℝ)/8) ≤ (499138621244591707/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-113/8192 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0024_exp_lower : (920157120711552851/1000000000000000000 : ℝ) ≤ Real.exp ((-66568672111/100000000000 : ℝ)/8) ∧ Real.exp ((-66568672111/100000000000 : ℝ)/8) ≤ (230039280177888213/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66568672111/100000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0024_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513920486453/250000000000 : ℝ) ≤ 4*Real.exp (225/2048 : ℝ)*Real.exp (-mu (radius 8 (113/1024 : ℝ))) ∧ (20549/10000 : ℝ) < (513920486453/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (113/1024 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0024_exp_radius
  have hrNumeric : (986300755219/1000000000000 : ℝ) ≤ Real.exp (-113/8192 : ℝ) ∧ Real.exp (-113/8192 : ℝ) ≤ (49315037761/50000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (986300755219/1000000000000 : ℝ) ≤ (radius 8 (113/1024 : ℝ)) ∧ (radius 8 (113/1024 : ℝ)) ≤ (49315037761/50000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (113/1024 : ℝ)) (986300755219/1000000000000 : ℝ) (49315037761/50000000000 : ℝ) (164957025471/1000000000000 : ℝ) (82478512739/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (113/1024 : ℝ)) (986300755219/1000000000000 : ℝ) (49315037761/50000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (113/1024 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (986300755219/1000000000000 : ℝ) (49315037761/50000000000 : ℝ) (993150377609/1000000000000 : ℝ) (99315037761/100000000000 : ℝ) (993126756873/1000000000000 : ℝ) (1589002811/1600000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (113/1024 : ℝ)) 1 (993150377609/1000000000000 : ℝ) (99315037761/100000000000 : ℝ) (993126756873/1000000000000 : ℝ) (1589002811/1600000000 : ℝ) (993138567241/1000000000000 : ℝ) (993138567243/1000000000000 : ℝ) (99313856717/100000000000 : ℝ) (993138567173/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (113/1024 : ℝ)) 2 (993138567241/1000000000000 : ℝ) (993138567243/1000000000000 : ℝ) (99313856717/100000000000 : ℝ) (993138567173/1000000000000 : ℝ) (198627713441/200000000000 : ℝ) (124142320901/125000000000 : ℝ) (198627713441/200000000000 : ℝ) (124142320901/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (113/1024 : ℝ)) 3 (198627713441/200000000000 : ℝ) (124142320901/125000000000 : ℝ) (198627713441/200000000000 : ℝ) (124142320901/125000000000 : ℝ) (198627713441/200000000000 : ℝ) (124142320901/125000000000 : ℝ) (198627713441/200000000000 : ℝ) (124142320901/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (113/1024 : ℝ)) 4 (198627713441/200000000000 : ℝ) (124142320901/125000000000 : ℝ) (198627713441/200000000000 : ℝ) (124142320901/125000000000 : ℝ) (198627713441/200000000000 : ℝ) (124142320901/125000000000 : ℝ) (198627713441/200000000000 : ℝ) (124142320901/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (113/1024 : ℝ)) 5 (198627713441/200000000000 : ℝ) (124142320901/125000000000 : ℝ) (198627713441/200000000000 : ℝ) (124142320901/125000000000 : ℝ) (198627713441/200000000000 : ℝ) (124142320901/125000000000 : ℝ) (198627713441/200000000000 : ℝ) (124142320901/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (113/1024 : ℝ)) 6 (198627713441/200000000000 : ℝ) (124142320901/125000000000 : ℝ) (198627713441/200000000000 : ℝ) (124142320901/125000000000 : ℝ) (198627713441/200000000000 : ℝ) (124142320901/125000000000 : ℝ) (198627713441/200000000000 : ℝ) (124142320901/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (113/1024 : ℝ)) 7 (198627713441/200000000000 : ℝ) (124142320901/125000000000 : ℝ) (198627713441/200000000000 : ℝ) (124142320901/125000000000 : ℝ) (198627713441/200000000000 : ℝ) (124142320901/125000000000 : ℝ) (198627713441/200000000000 : ℝ) (124142320901/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (113/1024 : ℝ))) (164957025471/1000000000000 : ℝ) (82478512739/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (113/1024 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (164957025471/1000000000000 : ℝ) (82478512739/500000000000 : ℝ) (116495702547/200000000000 : ℝ) (582478512739/1000000000000 : ℝ) (203074509399/500000000000 : ℝ) (50768627351/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (113/1024 : ℝ))) 1 (116495702547/200000000000 : ℝ) (582478512739/1000000000000 : ℝ) (203074509399/500000000000 : ℝ) (50768627351/125000000000 : ℝ) (247156882883/500000000000 : ℝ) (247156882887/500000000000 : ℝ) (486387783993/1000000000000 : ℝ) (243193892001/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (113/1024 : ℝ))) 2 (247156882883/500000000000 : ℝ) (247156882887/500000000000 : ℝ) (486387783993/1000000000000 : ℝ) (243193892001/500000000000 : ℝ) (490350774879/1000000000000 : ℝ) (61293846861/125000000000 : ℝ) (490334760269/1000000000000 : ℝ) (245167380139/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (113/1024 : ℝ))) 3 (490350774879/1000000000000 : ℝ) (61293846861/125000000000 : ℝ) (490334760269/1000000000000 : ℝ) (245167380139/500000000000 : ℝ) (245171383787/500000000000 : ℝ) (490342767583/1000000000000 : ℝ) (122585691877/250000000000 : ℝ) (245171383759/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (113/1024 : ℝ))) 4 (245171383787/500000000000 : ℝ) (490342767583/1000000000000 : ℝ) (122585691877/250000000000 : ℝ) (245171383759/500000000000 : ℝ) (490342767541/1000000000000 : ℝ) (490342767551/1000000000000 : ℝ) (24517138377/50000000000 : ℝ) (490342767551/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (113/1024 : ℝ))) 5 (490342767541/1000000000000 : ℝ) (490342767551/1000000000000 : ℝ) (24517138377/50000000000 : ℝ) (490342767551/1000000000000 : ℝ) (24517138377/50000000000 : ℝ) (490342767551/1000000000000 : ℝ) (24517138377/50000000000 : ℝ) (490342767551/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (113/1024 : ℝ))) 6 (24517138377/50000000000 : ℝ) (490342767551/1000000000000 : ℝ) (24517138377/50000000000 : ℝ) (490342767551/1000000000000 : ℝ) (24517138377/50000000000 : ℝ) (490342767551/1000000000000 : ℝ) (24517138377/50000000000 : ℝ) (490342767551/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (113/1024 : ℝ))) 7 (24517138377/50000000000 : ℝ) (490342767551/1000000000000 : ℝ) (24517138377/50000000000 : ℝ) (490342767551/1000000000000 : ℝ) (24517138377/50000000000 : ℝ) (490342767551/1000000000000 : ℝ) (24517138377/50000000000 : ℝ) (490342767551/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (113/1024 : ℝ)) hmem 8 (198627713441/200000000000 : ℝ) (124142320901/125000000000 : ℝ) (198627713441/200000000000 : ℝ) (124142320901/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (113/1024 : ℝ))) hcmem 8 (24517138377/50000000000 : ℝ) (490342767551/1000000000000 : ℝ) (24517138377/50000000000 : ℝ) (490342767551/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (113/1024 : ℝ)) (198627713441/200000000000 : ℝ) (124142320901/125000000000 : ℝ) (24517138377/50000000000 : ℝ) (490342767551/1000000000000 : ℝ) (38777500117/50000000000 : ℝ) (19388750059/25000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0024_exp_lower
  have heNumeric : (513920486453/250000000000 : ℝ)/4 ≤ Real.exp (-66568672111/100000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513920486453/250000000000 : ℝ)/4 ≤ Real.exp ((225/2048 : ℝ)-(19388750059/25000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (225/2048 : ℝ) (113/1024 : ℝ) (19388750059/25000000000 : ℝ) (513920486453/250000000000 : ℝ) hmu.2 heBox
  · norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_leaf0000_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0000_certificate
#check SmaleRate.Proofs.cover8_leaf0001_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0001_certificate
#check SmaleRate.Proofs.cover8_leaf0002_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0002_certificate
#check SmaleRate.Proofs.cover8_leaf0003_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0003_certificate
#check SmaleRate.Proofs.cover8_leaf0004_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0004_certificate
#check SmaleRate.Proofs.cover8_leaf0005_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0005_certificate
#check SmaleRate.Proofs.cover8_leaf0006_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0006_certificate
#check SmaleRate.Proofs.cover8_leaf0007_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0007_certificate
#check SmaleRate.Proofs.cover8_leaf0008_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0008_certificate
#check SmaleRate.Proofs.cover8_leaf0009_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0009_certificate
#check SmaleRate.Proofs.cover8_leaf0010_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0010_certificate
#check SmaleRate.Proofs.cover8_leaf0011_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0011_certificate
#check SmaleRate.Proofs.cover8_leaf0012_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0012_certificate
#check SmaleRate.Proofs.cover8_leaf0013_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0013_certificate
#check SmaleRate.Proofs.cover8_leaf0014_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0014_certificate
#check SmaleRate.Proofs.cover8_leaf0015_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0015_certificate
#check SmaleRate.Proofs.cover8_leaf0016_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0016_certificate
#check SmaleRate.Proofs.cover8_leaf0017_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0017_certificate
#check SmaleRate.Proofs.cover8_leaf0018_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0018_certificate
#check SmaleRate.Proofs.cover8_leaf0019_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0019_certificate
#check SmaleRate.Proofs.cover8_leaf0020_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0020_certificate
#check SmaleRate.Proofs.cover8_leaf0021_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0021_certificate
#check SmaleRate.Proofs.cover8_leaf0022_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0022_certificate
#check SmaleRate.Proofs.cover8_leaf0023_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0023_certificate
#check SmaleRate.Proofs.cover8_leaf0024_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0024_certificate
