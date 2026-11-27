/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.AGMCertificates

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

-- Proposed record cover8_leaf1175; no trusted numerical premise.
theorem cover8_leaf1175_exp_radius : (997997860384849419/1000000000000000000 : ℝ) ≤ Real.exp ((-4203/262144 : ℝ)/8) ∧ Real.exp ((-4203/262144 : ℝ)/8) ≤ (49899893019242471/50000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4203/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1175_exp_lower : (460056778820118179/500000000000000000 : ℝ) ≤ Real.exp ((-85256380762657/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256380762657/128000000000000 : ℝ)/8) ≤ (920113557640236359/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256380762657/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1175_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513725874077/250000000000 : ℝ) ≤ 4*Real.exp (67247/524288 : ℝ)*Real.exp (-mu (radius 8 (4203/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (513725874077/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4203/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1175_exp_radius
  have hrNumeric : (984094674527/1000000000000 : ℝ) ≤ Real.exp (-4203/262144 : ℝ) ∧ Real.exp (-4203/262144 : ℝ) ≤ (30752958579/31250000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984094674527/1000000000000 : ℝ) ≤ (radius 8 (4203/32768 : ℝ)) ∧ (radius 8 (4203/32768 : ℝ)) ≤ (30752958579/31250000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4203/32768 : ℝ)) (984094674527/1000000000000 : ℝ) (30752958579/31250000000 : ℝ) (88822395213/500000000000 : ℝ) (5551399701/31250000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4203/32768 : ℝ)) (984094674527/1000000000000 : ℝ) (30752958579/31250000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4203/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984094674527/1000000000000 : ℝ) (30752958579/31250000000 : ℝ) (992047337263/1000000000000 : ℝ) (62002958579/62500000000 : ℝ) (99201546083/100000000000 : ℝ) (31000483151/31250000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4203/32768 : ℝ)) 1 (992047337263/1000000000000 : ℝ) (62002958579/62500000000 : ℝ) (99201546083/100000000000 : ℝ) (31000483151/31250000000 : ℝ) (496015699523/500000000000 : ℝ) (124003924881/125000000000 : ℝ) (496015699459/500000000000 : ℝ) (24800784973/25000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4203/32768 : ℝ)) 2 (496015699523/500000000000 : ℝ) (124003924881/125000000000 : ℝ) (496015699459/500000000000 : ℝ) (24800784973/25000000000 : ℝ) (496015699491/500000000000 : ℝ) (124003924873/125000000000 : ℝ) (992031398981/1000000000000 : ℝ) (124003924873/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4203/32768 : ℝ)) 3 (496015699491/500000000000 : ℝ) (124003924873/125000000000 : ℝ) (992031398981/1000000000000 : ℝ) (124003924873/125000000000 : ℝ) (992031398981/1000000000000 : ℝ) (124003924873/125000000000 : ℝ) (992031398981/1000000000000 : ℝ) (124003924873/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4203/32768 : ℝ)) 4 (992031398981/1000000000000 : ℝ) (124003924873/125000000000 : ℝ) (992031398981/1000000000000 : ℝ) (124003924873/125000000000 : ℝ) (992031398981/1000000000000 : ℝ) (124003924873/125000000000 : ℝ) (992031398981/1000000000000 : ℝ) (124003924873/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4203/32768 : ℝ)) 5 (992031398981/1000000000000 : ℝ) (124003924873/125000000000 : ℝ) (992031398981/1000000000000 : ℝ) (124003924873/125000000000 : ℝ) (992031398981/1000000000000 : ℝ) (124003924873/125000000000 : ℝ) (992031398981/1000000000000 : ℝ) (124003924873/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4203/32768 : ℝ)) 6 (992031398981/1000000000000 : ℝ) (124003924873/125000000000 : ℝ) (992031398981/1000000000000 : ℝ) (124003924873/125000000000 : ℝ) (992031398981/1000000000000 : ℝ) (124003924873/125000000000 : ℝ) (992031398981/1000000000000 : ℝ) (124003924873/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4203/32768 : ℝ)) 7 (992031398981/1000000000000 : ℝ) (124003924873/125000000000 : ℝ) (992031398981/1000000000000 : ℝ) (124003924873/125000000000 : ℝ) (992031398981/1000000000000 : ℝ) (124003924873/125000000000 : ℝ) (992031398981/1000000000000 : ℝ) (124003924873/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4203/32768 : ℝ))) (88822395213/500000000000 : ℝ) (5551399701/31250000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4203/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88822395213/500000000000 : ℝ) (5551399701/31250000000 : ℝ) (588822395213/1000000000000 : ℝ) (36801399701/62500000000 : ℝ) (105369822063/250000000000 : ℝ) (21073964413/50000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4203/32768 : ℝ))) 1 (588822395213/1000000000000 : ℝ) (36801399701/62500000000 : ℝ) (105369822063/250000000000 : ℝ) (21073964413/50000000000 : ℝ) (126287710433/250000000000 : ℝ) (252575420869/500000000000 : ℝ) (498173106501/1000000000000 : ℝ) (124543276627/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4203/32768 : ℝ))) 2 (126287710433/250000000000 : ℝ) (252575420869/500000000000 : ℝ) (498173106501/1000000000000 : ℝ) (124543276627/250000000000 : ℝ) (125415493529/250000000000 : ℝ) (501661974123/1000000000000 : ℝ) (250824921049/500000000000 : ℝ) (100329968421/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4203/32768 : ℝ))) 3 (125415493529/250000000000 : ℝ) (501661974123/1000000000000 : ℝ) (250824921049/500000000000 : ℝ) (100329968421/200000000000 : ℝ) (501655908107/1000000000000 : ℝ) (250827954057/500000000000 : ℝ) (50165590807/100000000000 : ℝ) (250827954039/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4203/32768 : ℝ))) 4 (501655908107/1000000000000 : ℝ) (250827954057/500000000000 : ℝ) (50165590807/100000000000 : ℝ) (250827954039/500000000000 : ℝ) (62706988511/125000000000 : ℝ) (1959593391/3906250000 : ℝ) (62706988511/125000000000 : ℝ) (1959593391/3906250000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4203/32768 : ℝ))) 5 (62706988511/125000000000 : ℝ) (1959593391/3906250000 : ℝ) (62706988511/125000000000 : ℝ) (1959593391/3906250000 : ℝ) (62706988511/125000000000 : ℝ) (1959593391/3906250000 : ℝ) (62706988511/125000000000 : ℝ) (1959593391/3906250000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4203/32768 : ℝ))) 6 (62706988511/125000000000 : ℝ) (1959593391/3906250000 : ℝ) (62706988511/125000000000 : ℝ) (1959593391/3906250000 : ℝ) (62706988511/125000000000 : ℝ) (1959593391/3906250000 : ℝ) (62706988511/125000000000 : ℝ) (1959593391/3906250000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4203/32768 : ℝ))) 7 (62706988511/125000000000 : ℝ) (1959593391/3906250000 : ℝ) (62706988511/125000000000 : ℝ) (1959593391/3906250000 : ℝ) (62706988511/125000000000 : ℝ) (1959593391/3906250000 : ℝ) (62706988511/125000000000 : ℝ) (1959593391/3906250000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4203/32768 : ℝ)) hmem 8 (992031398981/1000000000000 : ℝ) (124003924873/125000000000 : ℝ) (992031398981/1000000000000 : ℝ) (124003924873/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4203/32768 : ℝ))) hcmem 8 (62706988511/125000000000 : ℝ) (1959593391/3906250000 : ℝ) (62706988511/125000000000 : ℝ) (1959593391/3906250000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4203/32768 : ℝ)) (992031398981/1000000000000 : ℝ) (124003924873/125000000000 : ℝ) (62706988511/125000000000 : ℝ) (1959593391/3906250000 : ℝ) (794328948203/1000000000000 : ℝ) (794328948219/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1175_exp_lower
  have heNumeric : (513725874077/250000000000 : ℝ)/4 ≤ Real.exp (-85256380762657/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513725874077/250000000000 : ℝ)/4 ≤ Real.exp ((67247/524288 : ℝ)-(794328948219/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67247/524288 : ℝ) (4203/32768 : ℝ) (794328948219/1000000000000 : ℝ) (513725874077/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1176; no trusted numerical premise.
theorem cover8_leaf1176_exp_radius : (249499457660548971/250000000000000000 : ℝ) ≤ Real.exp ((-67249/4194304 : ℝ)/8) ∧ Real.exp ((-67249/4194304 : ℝ)/8) ≤ (199599566128439177/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67249/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1176_exp_lower : (920113558338905359/1000000000000000000 : ℝ) ≤ Real.exp ((-5328523749069/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328523749069/8000000000000 : ℝ)/8) ≤ (11501419479236317/12500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328523749069/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1176_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054903508791/1000000000000 : ℝ) ≤ 4*Real.exp (4203/32768 : ℝ)*Real.exp (-mu (radius 8 (67249/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054903508791/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67249/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1176_exp_radius
  have hrNumeric : (984094439901/1000000000000 : ℝ) ≤ Real.exp (-67249/4194304 : ℝ) ∧ Real.exp (-67249/4194304 : ℝ) ≤ (492047219951/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984094439901/1000000000000 : ℝ) ≤ (radius 8 (67249/524288 : ℝ)) ∧ (radius 8 (67249/524288 : ℝ)) ≤ (492047219951/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67249/524288 : ℝ)) (984094439901/1000000000000 : ℝ) (492047219951/500000000000 : ℝ) (177646090173/1000000000000 : ℝ) (8882304509/50000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67249/524288 : ℝ)) (984094439901/1000000000000 : ℝ) (492047219951/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67249/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984094439901/1000000000000 : ℝ) (492047219951/500000000000 : ℝ) (19840944399/20000000000 : ℝ) (992047219951/1000000000000 : ℝ) (992015342573/1000000000000 : ℝ) (496007671287/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67249/524288 : ℝ)) 1 (19840944399/20000000000 : ℝ) (992047219951/1000000000000 : ℝ) (992015342573/1000000000000 : ℝ) (496007671287/500000000000 : ℝ) (992031281261/1000000000000 : ℝ) (992031281263/1000000000000 : ℝ) (992031281133/1000000000000 : ℝ) (198406256227/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67249/524288 : ℝ)) 2 (992031281261/1000000000000 : ℝ) (992031281263/1000000000000 : ℝ) (992031281133/1000000000000 : ℝ) (198406256227/200000000000 : ℝ) (992031281197/1000000000000 : ℝ) (992031281199/1000000000000 : ℝ) (248007820299/250000000000 : ℝ) (992031281199/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67249/524288 : ℝ)) 3 (992031281197/1000000000000 : ℝ) (992031281199/1000000000000 : ℝ) (248007820299/250000000000 : ℝ) (992031281199/1000000000000 : ℝ) (248007820299/250000000000 : ℝ) (992031281199/1000000000000 : ℝ) (248007820299/250000000000 : ℝ) (992031281199/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67249/524288 : ℝ)) 4 (248007820299/250000000000 : ℝ) (992031281199/1000000000000 : ℝ) (248007820299/250000000000 : ℝ) (992031281199/1000000000000 : ℝ) (248007820299/250000000000 : ℝ) (992031281199/1000000000000 : ℝ) (248007820299/250000000000 : ℝ) (992031281199/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67249/524288 : ℝ)) 5 (248007820299/250000000000 : ℝ) (992031281199/1000000000000 : ℝ) (248007820299/250000000000 : ℝ) (992031281199/1000000000000 : ℝ) (248007820299/250000000000 : ℝ) (992031281199/1000000000000 : ℝ) (248007820299/250000000000 : ℝ) (992031281199/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67249/524288 : ℝ)) 6 (248007820299/250000000000 : ℝ) (992031281199/1000000000000 : ℝ) (248007820299/250000000000 : ℝ) (992031281199/1000000000000 : ℝ) (248007820299/250000000000 : ℝ) (992031281199/1000000000000 : ℝ) (248007820299/250000000000 : ℝ) (992031281199/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67249/524288 : ℝ)) 7 (248007820299/250000000000 : ℝ) (992031281199/1000000000000 : ℝ) (248007820299/250000000000 : ℝ) (992031281199/1000000000000 : ℝ) (248007820299/250000000000 : ℝ) (992031281199/1000000000000 : ℝ) (248007820299/250000000000 : ℝ) (992031281199/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67249/524288 : ℝ))) (177646090173/1000000000000 : ℝ) (8882304509/50000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67249/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177646090173/1000000000000 : ℝ) (8882304509/50000000000 : ℝ) (294411522543/500000000000 : ℝ) (58882304509/100000000000 : ℝ) (421480830137/1000000000000 : ℝ) (210740415073/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67249/524288 : ℝ))) 1 (294411522543/500000000000 : ℝ) (58882304509/100000000000 : ℝ) (421480830137/1000000000000 : ℝ) (210740415073/500000000000 : ℝ) (505151937611/1000000000000 : ℝ) (252575968809/500000000000 : ℝ) (498174292639/1000000000000 : ℝ) (498174292647/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67249/524288 : ℝ))) 2 (505151937611/1000000000000 : ℝ) (252575968809/500000000000 : ℝ) (498174292639/1000000000000 : ℝ) (498174292647/1000000000000 : ℝ) (4013304921/8000000000 : ℝ) (501663115133/1000000000000 : ℝ) (62706372931/125000000000 : ℝ) (15676593233/31250000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67249/524288 : ℝ))) 3 (4013304921/8000000000 : ℝ) (501663115133/1000000000000 : ℝ) (62706372931/125000000000 : ℝ) (15676593233/31250000000 : ℝ) (250828524643/500000000000 : ℝ) (100331409859/200000000000 : ℝ) (501657049249/1000000000000 : ℝ) (250828524629/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67249/524288 : ℝ))) 4 (250828524643/500000000000 : ℝ) (100331409859/200000000000 : ℝ) (501657049249/1000000000000 : ℝ) (250828524629/500000000000 : ℝ) (501657049267/1000000000000 : ℝ) (501657049277/1000000000000 : ℝ) (501657049267/1000000000000 : ℝ) (501657049277/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67249/524288 : ℝ))) 5 (501657049267/1000000000000 : ℝ) (501657049277/1000000000000 : ℝ) (501657049267/1000000000000 : ℝ) (501657049277/1000000000000 : ℝ) (501657049267/1000000000000 : ℝ) (501657049277/1000000000000 : ℝ) (501657049267/1000000000000 : ℝ) (501657049277/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67249/524288 : ℝ))) 6 (501657049267/1000000000000 : ℝ) (501657049277/1000000000000 : ℝ) (501657049267/1000000000000 : ℝ) (501657049277/1000000000000 : ℝ) (501657049267/1000000000000 : ℝ) (501657049277/1000000000000 : ℝ) (501657049267/1000000000000 : ℝ) (501657049277/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67249/524288 : ℝ))) 7 (501657049267/1000000000000 : ℝ) (501657049277/1000000000000 : ℝ) (501657049267/1000000000000 : ℝ) (501657049277/1000000000000 : ℝ) (501657049267/1000000000000 : ℝ) (501657049277/1000000000000 : ℝ) (501657049267/1000000000000 : ℝ) (501657049277/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67249/524288 : ℝ)) hmem 8 (248007820299/250000000000 : ℝ) (992031281199/1000000000000 : ℝ) (248007820299/250000000000 : ℝ) (992031281199/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67249/524288 : ℝ))) hcmem 8 (501657049267/1000000000000 : ℝ) (501657049277/1000000000000 : ℝ) (501657049267/1000000000000 : ℝ) (501657049277/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67249/524288 : ℝ)) (248007820299/250000000000 : ℝ) (992031281199/1000000000000 : ℝ) (501657049267/1000000000000 : ℝ) (501657049277/1000000000000 : ℝ) (794330849473/1000000000000 : ℝ) (794330849493/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1176_exp_lower
  have heNumeric : (2054903508791/1000000000000 : ℝ)/4 ≤ Real.exp (-5328523749069/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054903508791/1000000000000 : ℝ)/4 ≤ Real.exp ((4203/32768 : ℝ)-(794330849493/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4203/32768 : ℝ) (67249/524288 : ℝ) (794330849493/1000000000000 : ℝ) (2054903508791/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1177; no trusted numerical premise.
theorem cover8_leaf1177_exp_radius : (997997800899543237/1000000000000000000 : ℝ) ≤ Real.exp ((-33625/2097152 : ℝ)/8) ∧ Real.exp ((-33625/2097152 : ℝ)/8) ≤ (498998900449771619/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33625/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1177_exp_lower : (460056779519649787/500000000000000000 : ℝ) ≤ Real.exp ((-85256379205631/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256379205631/128000000000000 : ℝ)/8) ≤ (36804542361571983/40000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256379205631/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1177_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256862940163/125000000000 : ℝ) ≤ 4*Real.exp (67249/524288 : ℝ)*Real.exp (-mu (radius 8 (33625/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (256862940163/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33625/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1177_exp_radius
  have hrNumeric : (492047102637/500000000000 : ℝ) ≤ Real.exp (-33625/2097152 : ℝ) ∧ Real.exp (-33625/2097152 : ℝ) ≤ (39363768211/40000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492047102637/500000000000 : ℝ) ≤ (radius 8 (33625/262144 : ℝ)) ∧ (radius 8 (33625/262144 : ℝ)) ≤ (39363768211/40000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33625/262144 : ℝ)) (492047102637/500000000000 : ℝ) (39363768211/40000000000 : ℝ) (44411847479/250000000000 : ℝ) (177647389923/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33625/262144 : ℝ)) (492047102637/500000000000 : ℝ) (39363768211/40000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33625/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492047102637/500000000000 : ℝ) (39363768211/40000000000 : ℝ) (992047102637/1000000000000 : ℝ) (496023551319/500000000000 : ℝ) (198403044863/200000000000 : ℝ) (992015224317/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33625/262144 : ℝ)) 1 (992047102637/1000000000000 : ℝ) (496023551319/500000000000 : ℝ) (198403044863/200000000000 : ℝ) (992015224317/1000000000000 : ℝ) (248007790869/250000000000 : ℝ) (496015581739/500000000000 : ℝ) (992031163347/1000000000000 : ℝ) (19840623267/20000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33625/262144 : ℝ)) 2 (248007790869/250000000000 : ℝ) (496015581739/500000000000 : ℝ) (992031163347/1000000000000 : ℝ) (19840623267/20000000000 : ℝ) (992031163411/1000000000000 : ℝ) (496015581707/500000000000 : ℝ) (992031163411/1000000000000 : ℝ) (496015581707/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33625/262144 : ℝ)) 3 (992031163411/1000000000000 : ℝ) (496015581707/500000000000 : ℝ) (992031163411/1000000000000 : ℝ) (496015581707/500000000000 : ℝ) (992031163411/1000000000000 : ℝ) (496015581707/500000000000 : ℝ) (992031163411/1000000000000 : ℝ) (496015581707/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33625/262144 : ℝ)) 4 (992031163411/1000000000000 : ℝ) (496015581707/500000000000 : ℝ) (992031163411/1000000000000 : ℝ) (496015581707/500000000000 : ℝ) (992031163411/1000000000000 : ℝ) (496015581707/500000000000 : ℝ) (992031163411/1000000000000 : ℝ) (496015581707/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33625/262144 : ℝ)) 5 (992031163411/1000000000000 : ℝ) (496015581707/500000000000 : ℝ) (992031163411/1000000000000 : ℝ) (496015581707/500000000000 : ℝ) (992031163411/1000000000000 : ℝ) (496015581707/500000000000 : ℝ) (992031163411/1000000000000 : ℝ) (496015581707/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33625/262144 : ℝ)) 6 (992031163411/1000000000000 : ℝ) (496015581707/500000000000 : ℝ) (992031163411/1000000000000 : ℝ) (496015581707/500000000000 : ℝ) (992031163411/1000000000000 : ℝ) (496015581707/500000000000 : ℝ) (992031163411/1000000000000 : ℝ) (496015581707/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33625/262144 : ℝ)) 7 (992031163411/1000000000000 : ℝ) (496015581707/500000000000 : ℝ) (992031163411/1000000000000 : ℝ) (496015581707/500000000000 : ℝ) (992031163411/1000000000000 : ℝ) (496015581707/500000000000 : ℝ) (992031163411/1000000000000 : ℝ) (496015581707/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33625/262144 : ℝ))) (44411847479/250000000000 : ℝ) (177647389923/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33625/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44411847479/250000000000 : ℝ) (177647389923/1000000000000 : ℝ) (294411847479/500000000000 : ℝ) (294411847481/500000000000 : ℝ) (42148237201/100000000000 : ℝ) (21074118601/50000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33625/262144 : ℝ))) 1 (294411847479/500000000000 : ℝ) (294411847481/500000000000 : ℝ) (42148237201/100000000000 : ℝ) (21074118601/50000000000 : ℝ) (126288258371/250000000000 : ℝ) (505153033491/1000000000000 : ℝ) (31135967423/62500000000 : ℝ) (498175478777/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33625/262144 : ℝ))) 2 (126288258371/250000000000 : ℝ) (505153033491/1000000000000 : ℝ) (31135967423/62500000000 : ℝ) (498175478777/1000000000000 : ℝ) (250832128063/500000000000 : ℝ) (250832128067/500000000000 : ℝ) (50165212479/100000000000 : ℝ) (501652124799/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33625/262144 : ℝ))) 3 (250832128063/500000000000 : ℝ) (250832128067/500000000000 : ℝ) (50165212479/100000000000 : ℝ) (501652124799/1000000000000 : ℝ) (250829095229/500000000000 : ℝ) (501658190467/1000000000000 : ℝ) (501658190421/1000000000000 : ℝ) (50165819043/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33625/262144 : ℝ))) 4 (250829095229/500000000000 : ℝ) (501658190467/1000000000000 : ℝ) (501658190421/1000000000000 : ℝ) (50165819043/100000000000 : ℝ) (501658190439/1000000000000 : ℝ) (501658190449/1000000000000 : ℝ) (501658190439/1000000000000 : ℝ) (501658190449/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33625/262144 : ℝ))) 5 (501658190439/1000000000000 : ℝ) (501658190449/1000000000000 : ℝ) (501658190439/1000000000000 : ℝ) (501658190449/1000000000000 : ℝ) (501658190439/1000000000000 : ℝ) (501658190449/1000000000000 : ℝ) (501658190439/1000000000000 : ℝ) (501658190449/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33625/262144 : ℝ))) 6 (501658190439/1000000000000 : ℝ) (501658190449/1000000000000 : ℝ) (501658190439/1000000000000 : ℝ) (501658190449/1000000000000 : ℝ) (501658190439/1000000000000 : ℝ) (501658190449/1000000000000 : ℝ) (501658190439/1000000000000 : ℝ) (501658190449/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33625/262144 : ℝ))) 7 (501658190439/1000000000000 : ℝ) (501658190449/1000000000000 : ℝ) (501658190439/1000000000000 : ℝ) (501658190449/1000000000000 : ℝ) (501658190439/1000000000000 : ℝ) (501658190449/1000000000000 : ℝ) (501658190439/1000000000000 : ℝ) (501658190449/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33625/262144 : ℝ)) hmem 8 (992031163411/1000000000000 : ℝ) (496015581707/500000000000 : ℝ) (992031163411/1000000000000 : ℝ) (496015581707/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33625/262144 : ℝ))) hcmem 8 (501658190439/1000000000000 : ℝ) (501658190449/1000000000000 : ℝ) (501658190439/1000000000000 : ℝ) (501658190449/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33625/262144 : ℝ)) (992031163411/1000000000000 : ℝ) (496015581707/500000000000 : ℝ) (501658190439/1000000000000 : ℝ) (501658190449/1000000000000 : ℝ) (794332750733/1000000000000 : ℝ) (24822898461/31250000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1177_exp_lower
  have heNumeric : (256862940163/125000000000 : ℝ)/4 ≤ Real.exp (-85256379205631/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256862940163/125000000000 : ℝ)/4 ≤ Real.exp ((67249/524288 : ℝ)-(24822898461/31250000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67249/524288 : ℝ) (33625/262144 : ℝ) (24822898461/31250000000 : ℝ) (256862940163/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1178; no trusted numerical premise.
theorem cover8_leaf1178_exp_radius : (39919910846275659/40000000000000000 : ℝ) ≤ Real.exp ((-67251/4194304 : ℝ)/8) ∧ Real.exp ((-67251/4194304 : ℝ)/8) ≤ (249499442789222869/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67251/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1178_exp_lower : (920113559742799173/1000000000000000000 : ℝ) ≤ Real.exp ((-42628189211351/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628189211351/64000000000000 : ℝ)/8) ≤ (460056779871399587/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628189211351/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1178_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054903533873/1000000000000 : ℝ) ≤ 4*Real.exp (33625/262144 : ℝ)*Real.exp (-mu (radius 8 (67251/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054903533873/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67251/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1178_exp_radius
  have hrNumeric : (123011746331/125000000000 : ℝ) ≤ Real.exp (-67251/4194304 : ℝ) ∧ Real.exp (-67251/4194304 : ℝ) ≤ (984093970649/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (123011746331/125000000000 : ℝ) ≤ (radius 8 (67251/524288 : ℝ)) ∧ (radius 8 (67251/524288 : ℝ)) ≤ (984093970649/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67251/524288 : ℝ)) (123011746331/125000000000 : ℝ) (984093970649/1000000000000 : ℝ) (44412172411/250000000000 : ℝ) (3552973793/20000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67251/524288 : ℝ)) (123011746331/125000000000 : ℝ) (984093970649/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67251/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (123011746331/125000000000 : ℝ) (984093970649/1000000000000 : ℝ) (248011746331/250000000000 : ℝ) (39681879413/40000000000 : ℝ) (496007553029/500000000000 : ℝ) (992015106059/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67251/524288 : ℝ)) 1 (248011746331/250000000000 : ℝ) (39681879413/40000000000 : ℝ) (496007553029/500000000000 : ℝ) (992015106059/1000000000000 : ℝ) (992031045691/1000000000000 : ℝ) (248007761423/250000000000 : ℝ) (496015522781/500000000000 : ℝ) (248007761391/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67251/524288 : ℝ)) 2 (992031045691/1000000000000 : ℝ) (248007761423/250000000000 : ℝ) (496015522781/500000000000 : ℝ) (248007761391/250000000000 : ℝ) (496015522813/500000000000 : ℝ) (248007761407/250000000000 : ℝ) (496015522813/500000000000 : ℝ) (248007761407/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67251/524288 : ℝ)) 3 (496015522813/500000000000 : ℝ) (248007761407/250000000000 : ℝ) (496015522813/500000000000 : ℝ) (248007761407/250000000000 : ℝ) (496015522813/500000000000 : ℝ) (248007761407/250000000000 : ℝ) (496015522813/500000000000 : ℝ) (248007761407/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67251/524288 : ℝ)) 4 (496015522813/500000000000 : ℝ) (248007761407/250000000000 : ℝ) (496015522813/500000000000 : ℝ) (248007761407/250000000000 : ℝ) (496015522813/500000000000 : ℝ) (248007761407/250000000000 : ℝ) (496015522813/500000000000 : ℝ) (248007761407/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67251/524288 : ℝ)) 5 (496015522813/500000000000 : ℝ) (248007761407/250000000000 : ℝ) (496015522813/500000000000 : ℝ) (248007761407/250000000000 : ℝ) (496015522813/500000000000 : ℝ) (248007761407/250000000000 : ℝ) (496015522813/500000000000 : ℝ) (248007761407/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67251/524288 : ℝ)) 6 (496015522813/500000000000 : ℝ) (248007761407/250000000000 : ℝ) (496015522813/500000000000 : ℝ) (248007761407/250000000000 : ℝ) (496015522813/500000000000 : ℝ) (248007761407/250000000000 : ℝ) (496015522813/500000000000 : ℝ) (248007761407/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67251/524288 : ℝ)) 7 (496015522813/500000000000 : ℝ) (248007761407/250000000000 : ℝ) (496015522813/500000000000 : ℝ) (248007761407/250000000000 : ℝ) (496015522813/500000000000 : ℝ) (248007761407/250000000000 : ℝ) (496015522813/500000000000 : ℝ) (248007761407/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67251/524288 : ℝ))) (44412172411/250000000000 : ℝ) (3552973793/20000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67251/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44412172411/250000000000 : ℝ) (3552973793/20000000000 : ℝ) (294412172411/500000000000 : ℝ) (23552973793/40000000000 : ℝ) (421483913861/1000000000000 : ℝ) (421483913869/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67251/524288 : ℝ))) 1 (294412172411/500000000000 : ℝ) (23552973793/40000000000 : ℝ) (421483913861/1000000000000 : ℝ) (421483913869/1000000000000 : ℝ) (505154129341/1000000000000 : ℝ) (505154129347/1000000000000 : ℝ) (498176664881/1000000000000 : ℝ) (62272083111/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67251/524288 : ℝ))) 2 (505154129341/1000000000000 : ℝ) (505154129347/1000000000000 : ℝ) (498176664881/1000000000000 : ℝ) (62272083111/125000000000 : ℝ) (501665397111/1000000000000 : ℝ) (250832698559/500000000000 : ℝ) (501653266117/1000000000000 : ℝ) (125413316531/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67251/524288 : ℝ))) 3 (501665397111/1000000000000 : ℝ) (250832698559/500000000000 : ℝ) (501653266117/1000000000000 : ℝ) (125413316531/250000000000 : ℝ) (250829665807/500000000000 : ℝ) (501659331621/1000000000000 : ℝ) (501659331577/1000000000000 : ℝ) (100331866317/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67251/524288 : ℝ))) 4 (250829665807/500000000000 : ℝ) (501659331621/1000000000000 : ℝ) (501659331577/1000000000000 : ℝ) (100331866317/200000000000 : ℝ) (100331866319/200000000000 : ℝ) (501659331603/1000000000000 : ℝ) (100331866319/200000000000 : ℝ) (501659331603/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67251/524288 : ℝ))) 5 (100331866319/200000000000 : ℝ) (501659331603/1000000000000 : ℝ) (100331866319/200000000000 : ℝ) (501659331603/1000000000000 : ℝ) (100331866319/200000000000 : ℝ) (501659331603/1000000000000 : ℝ) (100331866319/200000000000 : ℝ) (501659331603/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67251/524288 : ℝ))) 6 (100331866319/200000000000 : ℝ) (501659331603/1000000000000 : ℝ) (100331866319/200000000000 : ℝ) (501659331603/1000000000000 : ℝ) (100331866319/200000000000 : ℝ) (501659331603/1000000000000 : ℝ) (100331866319/200000000000 : ℝ) (501659331603/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67251/524288 : ℝ))) 7 (100331866319/200000000000 : ℝ) (501659331603/1000000000000 : ℝ) (100331866319/200000000000 : ℝ) (501659331603/1000000000000 : ℝ) (100331866319/200000000000 : ℝ) (501659331603/1000000000000 : ℝ) (100331866319/200000000000 : ℝ) (501659331603/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67251/524288 : ℝ)) hmem 8 (496015522813/500000000000 : ℝ) (248007761407/250000000000 : ℝ) (496015522813/500000000000 : ℝ) (248007761407/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67251/524288 : ℝ))) hcmem 8 (100331866319/200000000000 : ℝ) (501659331603/1000000000000 : ℝ) (100331866319/200000000000 : ℝ) (501659331603/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67251/524288 : ℝ)) (496015522813/500000000000 : ℝ) (248007761407/250000000000 : ℝ) (100331866319/200000000000 : ℝ) (501659331603/1000000000000 : ℝ) (794334651969/1000000000000 : ℝ) (49645915749/62500000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1178_exp_lower
  have heNumeric : (2054903533873/1000000000000 : ℝ)/4 ≤ Real.exp (-42628189211351/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054903533873/1000000000000 : ℝ)/4 ≤ Real.exp ((33625/262144 : ℝ)-(49645915749/62500000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33625/262144 : ℝ) (67251/524288 : ℝ) (49645915749/62500000000 : ℝ) (2054903533873/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1179; no trusted numerical premise.
theorem cover8_leaf1179_exp_radius : (4989988707071203/5000000000000000 : ℝ) ≤ Real.exp ((-16813/1048576 : ℝ)/8) ∧ Real.exp ((-16813/1048576 : ℝ)/8) ≤ (997997741414240601/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16813/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1179_exp_lower : (920113560448254013/1000000000000000000 : ℝ) ≤ Real.exp ((-85256377637597/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256377637597/128000000000000 : ℝ)/8) ≤ (460056780224127007/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256377637597/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1179_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054903546477/1000000000000 : ℝ) ≤ 4*Real.exp (67251/524288 : ℝ)*Real.exp (-mu (radius 8 (16813/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054903546477/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16813/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1179_exp_radius
  have hrNumeric : (492046868011/500000000000 : ℝ) ≤ Real.exp (-16813/1048576 : ℝ) ∧ Real.exp (-16813/1048576 : ℝ) ≤ (984093736023/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492046868011/500000000000 : ℝ) ≤ (radius 8 (16813/131072 : ℝ)) ∧ (radius 8 (16813/131072 : ℝ)) ≤ (984093736023/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16813/131072 : ℝ)) (492046868011/500000000000 : ℝ) (984093736023/1000000000000 : ℝ) (177649989361/1000000000000 : ℝ) (22206248671/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16813/131072 : ℝ)) (492046868011/500000000000 : ℝ) (984093736023/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16813/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492046868011/500000000000 : ℝ) (984093736023/1000000000000 : ℝ) (992046868011/1000000000000 : ℝ) (248011717003/250000000000 : ℝ) (992014987801/1000000000000 : ℝ) (496007493901/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16813/131072 : ℝ)) 1 (992046868011/1000000000000 : ℝ) (248011717003/250000000000 : ℝ) (992014987801/1000000000000 : ℝ) (496007493901/500000000000 : ℝ) (496015463953/500000000000 : ℝ) (992030927907/1000000000000 : ℝ) (992030927777/1000000000000 : ℝ) (992030927779/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16813/131072 : ℝ)) 2 (496015463953/500000000000 : ℝ) (992030927907/1000000000000 : ℝ) (992030927777/1000000000000 : ℝ) (992030927779/1000000000000 : ℝ) (992030927841/1000000000000 : ℝ) (992030927843/1000000000000 : ℝ) (992030927841/1000000000000 : ℝ) (992030927843/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16813/131072 : ℝ)) 3 (992030927841/1000000000000 : ℝ) (992030927843/1000000000000 : ℝ) (992030927841/1000000000000 : ℝ) (992030927843/1000000000000 : ℝ) (992030927841/1000000000000 : ℝ) (992030927843/1000000000000 : ℝ) (992030927841/1000000000000 : ℝ) (992030927843/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16813/131072 : ℝ)) 4 (992030927841/1000000000000 : ℝ) (992030927843/1000000000000 : ℝ) (992030927841/1000000000000 : ℝ) (992030927843/1000000000000 : ℝ) (992030927841/1000000000000 : ℝ) (992030927843/1000000000000 : ℝ) (992030927841/1000000000000 : ℝ) (992030927843/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16813/131072 : ℝ)) 5 (992030927841/1000000000000 : ℝ) (992030927843/1000000000000 : ℝ) (992030927841/1000000000000 : ℝ) (992030927843/1000000000000 : ℝ) (992030927841/1000000000000 : ℝ) (992030927843/1000000000000 : ℝ) (992030927841/1000000000000 : ℝ) (992030927843/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16813/131072 : ℝ)) 6 (992030927841/1000000000000 : ℝ) (992030927843/1000000000000 : ℝ) (992030927841/1000000000000 : ℝ) (992030927843/1000000000000 : ℝ) (992030927841/1000000000000 : ℝ) (992030927843/1000000000000 : ℝ) (992030927841/1000000000000 : ℝ) (992030927843/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16813/131072 : ℝ)) 7 (992030927841/1000000000000 : ℝ) (992030927843/1000000000000 : ℝ) (992030927841/1000000000000 : ℝ) (992030927843/1000000000000 : ℝ) (992030927841/1000000000000 : ℝ) (992030927843/1000000000000 : ℝ) (992030927841/1000000000000 : ℝ) (992030927843/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16813/131072 : ℝ))) (177649989361/1000000000000 : ℝ) (22206248671/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16813/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177649989361/1000000000000 : ℝ) (22206248671/125000000000 : ℝ) (14720624867/25000000000 : ℝ) (147206248671/250000000000 : ℝ) (421485455693/1000000000000 : ℝ) (210742727851/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16813/131072 : ℝ))) 1 (14720624867/25000000000 : ℝ) (147206248671/250000000000 : ℝ) (421485455693/1000000000000 : ℝ) (210742727851/500000000000 : ℝ) (252577612593/500000000000 : ℝ) (505155225193/1000000000000 : ℝ) (498177850979/1000000000000 : ℝ) (498177850987/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16813/131072 : ℝ))) 2 (252577612593/500000000000 : ℝ) (505155225193/1000000000000 : ℝ) (498177850979/1000000000000 : ℝ) (498177850987/1000000000000 : ℝ) (250833269041/500000000000 : ℝ) (50166653809/100000000000 : ℝ) (50165440743/100000000000 : ℝ) (250827203719/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16813/131072 : ℝ))) 3 (250833269041/500000000000 : ℝ) (50166653809/100000000000 : ℝ) (50165440743/100000000000 : ℝ) (250827203719/500000000000 : ℝ) (125415118189/250000000000 : ℝ) (125415118191/250000000000 : ℝ) (501660472719/1000000000000 : ℝ) (62707559091/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16813/131072 : ℝ))) 4 (125415118189/250000000000 : ℝ) (125415118191/250000000000 : ℝ) (501660472719/1000000000000 : ℝ) (62707559091/125000000000 : ℝ) (501660472737/1000000000000 : ℝ) (250830236373/500000000000 : ℝ) (501660472737/1000000000000 : ℝ) (250830236373/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16813/131072 : ℝ))) 5 (501660472737/1000000000000 : ℝ) (250830236373/500000000000 : ℝ) (501660472737/1000000000000 : ℝ) (250830236373/500000000000 : ℝ) (501660472737/1000000000000 : ℝ) (250830236373/500000000000 : ℝ) (501660472737/1000000000000 : ℝ) (250830236373/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16813/131072 : ℝ))) 6 (501660472737/1000000000000 : ℝ) (250830236373/500000000000 : ℝ) (501660472737/1000000000000 : ℝ) (250830236373/500000000000 : ℝ) (501660472737/1000000000000 : ℝ) (250830236373/500000000000 : ℝ) (501660472737/1000000000000 : ℝ) (250830236373/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16813/131072 : ℝ))) 7 (501660472737/1000000000000 : ℝ) (250830236373/500000000000 : ℝ) (501660472737/1000000000000 : ℝ) (250830236373/500000000000 : ℝ) (501660472737/1000000000000 : ℝ) (250830236373/500000000000 : ℝ) (501660472737/1000000000000 : ℝ) (250830236373/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16813/131072 : ℝ)) hmem 8 (992030927841/1000000000000 : ℝ) (992030927843/1000000000000 : ℝ) (992030927841/1000000000000 : ℝ) (992030927843/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16813/131072 : ℝ))) hcmem 8 (501660472737/1000000000000 : ℝ) (250830236373/500000000000 : ℝ) (501660472737/1000000000000 : ℝ) (250830236373/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16813/131072 : ℝ)) (992030927841/1000000000000 : ℝ) (992030927843/1000000000000 : ℝ) (501660472737/1000000000000 : ℝ) (250830236373/500000000000 : ℝ) (397168276591/500000000000 : ℝ) (794336553199/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1179_exp_lower
  have heNumeric : (2054903546477/1000000000000 : ℝ)/4 ≤ Real.exp (-85256377637597/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054903546477/1000000000000 : ℝ)/4 ≤ Real.exp ((67251/524288 : ℝ)-(794336553199/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67251/524288 : ℝ) (16813/131072 : ℝ) (794336553199/1000000000000 : ℝ) (2054903546477/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1180; no trusted numerical premise.
theorem cover8_leaf1180_exp_radius : (249499427917897653/250000000000000000 : ℝ) ≤ Real.exp ((-67253/4194304 : ℝ)/8) ∧ Real.exp ((-67253/4194304 : ℝ)/8) ≤ (997997711671590613/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67253/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1180_exp_lower : (230028390288714749/250000000000000000 : ℝ) ≤ Real.exp ((-21314094212803/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314094212803/32000000000000 : ℝ)/8) ≤ (920113561154858997/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314094212803/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1180_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451779551/500000000000 : ℝ) ≤ 4*Real.exp (16813/131072 : ℝ)*Real.exp (-mu (radius 8 (67253/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451779551/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67253/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1180_exp_radius
  have hrNumeric : (196818700279/200000000000 : ℝ) ≤ Real.exp (-67253/4194304 : ℝ) ∧ Real.exp (-67253/4194304 : ℝ) ≤ (246023375349/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196818700279/200000000000 : ℝ) ≤ (radius 8 (67253/524288 : ℝ)) ∧ (radius 8 (67253/524288 : ℝ)) ≤ (246023375349/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67253/524288 : ℝ)) (196818700279/200000000000 : ℝ) (246023375349/250000000000 : ℝ) (7106051563/40000000000 : ℝ) (177651289081/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67253/524288 : ℝ)) (196818700279/200000000000 : ℝ) (246023375349/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67253/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196818700279/200000000000 : ℝ) (246023375349/250000000000 : ℝ) (992046750697/1000000000000 : ℝ) (496023375349/500000000000 : ℝ) (992014869543/1000000000000 : ℝ) (124001858693/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67253/524288 : ℝ)) 1 (992046750697/1000000000000 : ℝ) (496023375349/500000000000 : ℝ) (992014869543/1000000000000 : ℝ) (124001858693/125000000000 : ℝ) (24800770253/25000000000 : ℝ) (992030810121/1000000000000 : ℝ) (992030809991/1000000000000 : ℝ) (992030809993/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67253/524288 : ℝ)) 2 (24800770253/25000000000 : ℝ) (992030810121/1000000000000 : ℝ) (992030809991/1000000000000 : ℝ) (992030809993/1000000000000 : ℝ) (198406162011/200000000000 : ℝ) (992030810057/1000000000000 : ℝ) (198406162011/200000000000 : ℝ) (992030810057/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67253/524288 : ℝ)) 3 (198406162011/200000000000 : ℝ) (992030810057/1000000000000 : ℝ) (198406162011/200000000000 : ℝ) (992030810057/1000000000000 : ℝ) (198406162011/200000000000 : ℝ) (992030810057/1000000000000 : ℝ) (198406162011/200000000000 : ℝ) (992030810057/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67253/524288 : ℝ)) 4 (198406162011/200000000000 : ℝ) (992030810057/1000000000000 : ℝ) (198406162011/200000000000 : ℝ) (992030810057/1000000000000 : ℝ) (198406162011/200000000000 : ℝ) (992030810057/1000000000000 : ℝ) (198406162011/200000000000 : ℝ) (992030810057/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67253/524288 : ℝ)) 5 (198406162011/200000000000 : ℝ) (992030810057/1000000000000 : ℝ) (198406162011/200000000000 : ℝ) (992030810057/1000000000000 : ℝ) (198406162011/200000000000 : ℝ) (992030810057/1000000000000 : ℝ) (198406162011/200000000000 : ℝ) (992030810057/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67253/524288 : ℝ)) 6 (198406162011/200000000000 : ℝ) (992030810057/1000000000000 : ℝ) (198406162011/200000000000 : ℝ) (992030810057/1000000000000 : ℝ) (198406162011/200000000000 : ℝ) (992030810057/1000000000000 : ℝ) (198406162011/200000000000 : ℝ) (992030810057/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67253/524288 : ℝ)) 7 (198406162011/200000000000 : ℝ) (992030810057/1000000000000 : ℝ) (198406162011/200000000000 : ℝ) (992030810057/1000000000000 : ℝ) (198406162011/200000000000 : ℝ) (992030810057/1000000000000 : ℝ) (198406162011/200000000000 : ℝ) (992030810057/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67253/524288 : ℝ))) (7106051563/40000000000 : ℝ) (177651289081/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67253/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (7106051563/40000000000 : ℝ) (177651289081/1000000000000 : ℝ) (588825644537/1000000000000 : ℝ) (588825644541/1000000000000 : ℝ) (84297399503/200000000000 : ℝ) (105371749381/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67253/524288 : ℝ))) 1 (588825644537/1000000000000 : ℝ) (588825644541/1000000000000 : ℝ) (84297399503/200000000000 : ℝ) (105371749381/250000000000 : ℝ) (252578160513/500000000000 : ℝ) (505156321033/1000000000000 : ℝ) (498179037069/1000000000000 : ℝ) (498179037077/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67253/524288 : ℝ))) 2 (252578160513/500000000000 : ℝ) (505156321033/1000000000000 : ℝ) (498179037069/1000000000000 : ℝ) (498179037077/1000000000000 : ℝ) (501667679047/1000000000000 : ℝ) (100333535811/200000000000 : ℝ) (7838367949/15625000000 : ℝ) (62706943593/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67253/524288 : ℝ))) 3 (501667679047/1000000000000 : ℝ) (100333535811/200000000000 : ℝ) (7838367949/15625000000 : ℝ) (62706943593/125000000000 : ℝ) (501661613891/1000000000000 : ℝ) (5016616139/10000000000 : ℝ) (250830806927/500000000000 : ℝ) (501661613863/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67253/524288 : ℝ))) 4 (501661613891/1000000000000 : ℝ) (5016616139/10000000000 : ℝ) (250830806927/500000000000 : ℝ) (501661613863/1000000000000 : ℝ) (31353850867/62500000000 : ℝ) (250830806941/500000000000 : ℝ) (31353850867/62500000000 : ℝ) (250830806941/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67253/524288 : ℝ))) 5 (31353850867/62500000000 : ℝ) (250830806941/500000000000 : ℝ) (31353850867/62500000000 : ℝ) (250830806941/500000000000 : ℝ) (31353850867/62500000000 : ℝ) (250830806941/500000000000 : ℝ) (31353850867/62500000000 : ℝ) (250830806941/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67253/524288 : ℝ))) 6 (31353850867/62500000000 : ℝ) (250830806941/500000000000 : ℝ) (31353850867/62500000000 : ℝ) (250830806941/500000000000 : ℝ) (31353850867/62500000000 : ℝ) (250830806941/500000000000 : ℝ) (31353850867/62500000000 : ℝ) (250830806941/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67253/524288 : ℝ))) 7 (31353850867/62500000000 : ℝ) (250830806941/500000000000 : ℝ) (31353850867/62500000000 : ℝ) (250830806941/500000000000 : ℝ) (31353850867/62500000000 : ℝ) (250830806941/500000000000 : ℝ) (31353850867/62500000000 : ℝ) (250830806941/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67253/524288 : ℝ)) hmem 8 (198406162011/200000000000 : ℝ) (992030810057/1000000000000 : ℝ) (198406162011/200000000000 : ℝ) (992030810057/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67253/524288 : ℝ))) hcmem 8 (31353850867/62500000000 : ℝ) (250830806941/500000000000 : ℝ) (31353850867/62500000000 : ℝ) (250830806941/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67253/524288 : ℝ)) (198406162011/200000000000 : ℝ) (992030810057/1000000000000 : ℝ) (31353850867/62500000000 : ℝ) (250830806941/500000000000 : ℝ) (397169227193/500000000000 : ℝ) (198584613601/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1180_exp_lower
  have heNumeric : (1027451779551/500000000000 : ℝ)/4 ≤ Real.exp (-21314094212803/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451779551/500000000000 : ℝ)/4 ≤ Real.exp ((16813/131072 : ℝ)-(198584613601/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16813/131072 : ℝ) (67253/524288 : ℝ) (198584613601/250000000000 : ℝ) (1027451779551/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1181; no trusted numerical premise.
theorem cover8_leaf1181_exp_radius : (997997681928941509/1000000000000000000 : ℝ) ≤ Real.exp ((-33627/2097152 : ℝ)/8) ∧ Real.exp ((-33627/2097152 : ℝ)/8) ≤ (99799768192894151/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33627/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1181_exp_lower : (230028390466113587/250000000000000000 : ℝ) ≤ Real.exp ((-85256376061499/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256376061499/128000000000000 : ℝ)/8) ≤ (920113561864454349/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256376061499/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1181_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (102745178589/50000000000 : ℝ) ≤ 4*Real.exp (67253/524288 : ℝ)*Real.exp (-mu (radius 8 (33627/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (102745178589/50000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33627/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1181_exp_radius
  have hrNumeric : (984093266769/1000000000000 : ℝ) ≤ Real.exp (-33627/2097152 : ℝ) ∧ Real.exp (-33627/2097152 : ℝ) ≤ (98409326677/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984093266769/1000000000000 : ℝ) ≤ (radius 8 (33627/262144 : ℝ)) ∧ (radius 8 (33627/262144 : ℝ)) ≤ (98409326677/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33627/262144 : ℝ)) (984093266769/1000000000000 : ℝ) (98409326677/100000000000 : ℝ) (177652588773/1000000000000 : ℝ) (8882629439/50000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33627/262144 : ℝ)) (984093266769/1000000000000 : ℝ) (98409326677/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33627/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984093266769/1000000000000 : ℝ) (98409326677/100000000000 : ℝ) (124005829173/125000000000 : ℝ) (198409326677/200000000000 : ℝ) (198402950257/200000000000 : ℝ) (992014751287/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33627/262144 : ℝ)) 1 (124005829173/125000000000 : ℝ) (198409326677/200000000000 : ℝ) (198402950257/200000000000 : ℝ) (992014751287/1000000000000 : ℝ) (496015346167/500000000000 : ℝ) (62001918271/62500000000 : ℝ) (496015346103/500000000000 : ℝ) (62001918263/62500000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33627/262144 : ℝ)) 2 (496015346167/500000000000 : ℝ) (62001918271/62500000000 : ℝ) (496015346103/500000000000 : ℝ) (62001918263/62500000000 : ℝ) (99203069227/100000000000 : ℝ) (62001918267/62500000000 : ℝ) (992030692269/1000000000000 : ℝ) (62001918267/62500000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33627/262144 : ℝ)) 3 (99203069227/100000000000 : ℝ) (62001918267/62500000000 : ℝ) (992030692269/1000000000000 : ℝ) (62001918267/62500000000 : ℝ) (992030692269/1000000000000 : ℝ) (62001918267/62500000000 : ℝ) (992030692269/1000000000000 : ℝ) (62001918267/62500000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33627/262144 : ℝ)) 4 (992030692269/1000000000000 : ℝ) (62001918267/62500000000 : ℝ) (992030692269/1000000000000 : ℝ) (62001918267/62500000000 : ℝ) (992030692269/1000000000000 : ℝ) (62001918267/62500000000 : ℝ) (992030692269/1000000000000 : ℝ) (62001918267/62500000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33627/262144 : ℝ)) 5 (992030692269/1000000000000 : ℝ) (62001918267/62500000000 : ℝ) (992030692269/1000000000000 : ℝ) (62001918267/62500000000 : ℝ) (992030692269/1000000000000 : ℝ) (62001918267/62500000000 : ℝ) (992030692269/1000000000000 : ℝ) (62001918267/62500000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33627/262144 : ℝ)) 6 (992030692269/1000000000000 : ℝ) (62001918267/62500000000 : ℝ) (992030692269/1000000000000 : ℝ) (62001918267/62500000000 : ℝ) (992030692269/1000000000000 : ℝ) (62001918267/62500000000 : ℝ) (992030692269/1000000000000 : ℝ) (62001918267/62500000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33627/262144 : ℝ)) 7 (992030692269/1000000000000 : ℝ) (62001918267/62500000000 : ℝ) (992030692269/1000000000000 : ℝ) (62001918267/62500000000 : ℝ) (992030692269/1000000000000 : ℝ) (62001918267/62500000000 : ℝ) (992030692269/1000000000000 : ℝ) (62001918267/62500000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33627/262144 : ℝ))) (177652588773/1000000000000 : ℝ) (8882629439/50000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33627/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177652588773/1000000000000 : ℝ) (8882629439/50000000000 : ℝ) (294413147193/500000000000 : ℝ) (58882629439/100000000000 : ℝ) (421488539313/1000000000000 : ℝ) (421488539323/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33627/262144 : ℝ))) 1 (294413147193/500000000000 : ℝ) (58882629439/100000000000 : ℝ) (421488539313/1000000000000 : ℝ) (421488539323/1000000000000 : ℝ) (505157416849/1000000000000 : ℝ) (505157416857/1000000000000 : ℝ) (249090111571/500000000000 : ℝ) (9963604463/20000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33627/262144 : ℝ))) 2 (505157416849/1000000000000 : ℝ) (505157416857/1000000000000 : ℝ) (249090111571/500000000000 : ℝ) (9963604463/20000000000 : ℝ) (100333763999/200000000000 : ℝ) (125417205001/250000000000 : ℝ) (20066267601/40000000000 : ℝ) (250828345017/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33627/262144 : ℝ))) 3 (100333763999/200000000000 : ℝ) (125417205001/250000000000 : ℝ) (20066267601/40000000000 : ℝ) (250828345017/500000000000 : ℝ) (50166275501/100000000000 : ℝ) (501662755019/1000000000000 : ℝ) (501662754973/1000000000000 : ℝ) (501662754983/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33627/262144 : ℝ))) 4 (50166275501/100000000000 : ℝ) (501662755019/1000000000000 : ℝ) (501662754973/1000000000000 : ℝ) (501662754983/1000000000000 : ℝ) (501662754991/1000000000000 : ℝ) (501662755001/1000000000000 : ℝ) (501662754991/1000000000000 : ℝ) (501662755001/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33627/262144 : ℝ))) 5 (501662754991/1000000000000 : ℝ) (501662755001/1000000000000 : ℝ) (501662754991/1000000000000 : ℝ) (501662755001/1000000000000 : ℝ) (501662754991/1000000000000 : ℝ) (501662755001/1000000000000 : ℝ) (501662754991/1000000000000 : ℝ) (501662755001/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33627/262144 : ℝ))) 6 (501662754991/1000000000000 : ℝ) (501662755001/1000000000000 : ℝ) (501662754991/1000000000000 : ℝ) (501662755001/1000000000000 : ℝ) (501662754991/1000000000000 : ℝ) (501662755001/1000000000000 : ℝ) (501662754991/1000000000000 : ℝ) (501662755001/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33627/262144 : ℝ))) 7 (501662754991/1000000000000 : ℝ) (501662755001/1000000000000 : ℝ) (501662754991/1000000000000 : ℝ) (501662755001/1000000000000 : ℝ) (501662754991/1000000000000 : ℝ) (501662755001/1000000000000 : ℝ) (501662754991/1000000000000 : ℝ) (501662755001/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33627/262144 : ℝ)) hmem 8 (992030692269/1000000000000 : ℝ) (62001918267/62500000000 : ℝ) (992030692269/1000000000000 : ℝ) (62001918267/62500000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33627/262144 : ℝ))) hcmem 8 (501662754991/1000000000000 : ℝ) (501662755001/1000000000000 : ℝ) (501662754991/1000000000000 : ℝ) (501662755001/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33627/262144 : ℝ)) (992030692269/1000000000000 : ℝ) (62001918267/62500000000 : ℝ) (501662754991/1000000000000 : ℝ) (501662755001/1000000000000 : ℝ) (794340355563/1000000000000 : ℝ) (794340355583/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1181_exp_lower
  have heNumeric : (102745178589/50000000000 : ℝ)/4 ≤ Real.exp (-85256376061499/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (102745178589/50000000000 : ℝ)/4 ≤ Real.exp ((67253/524288 : ℝ)-(794340355583/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67253/524288 : ℝ) (33627/262144 : ℝ) (794340355583/1000000000000 : ℝ) (102745178589/50000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1182; no trusted numerical premise.
theorem cover8_leaf1182_exp_radius : (498998826093146647/500000000000000000 : ℝ) ≤ Real.exp ((-67255/4194304 : ℝ)/8) ∧ Real.exp ((-67255/4194304 : ℝ)/8) ≤ (199599530437258659/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67255/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1182_exp_lower : (460056781288290007/500000000000000000 : ℝ) ≤ Real.exp ((-8525637526897/12800000000000 : ℝ)/8) ∧ Real.exp ((-8525637526897/12800000000000 : ℝ)/8) ≤ (184022712515316003/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8525637526897/12800000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1182_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054903584503/1000000000000 : ℝ) ≤ 4*Real.exp (33627/262144 : ℝ)*Real.exp (-mu (radius 8 (67255/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054903584503/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67255/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1182_exp_radius
  have hrNumeric : (984093032143/1000000000000 : ℝ) ≤ Real.exp (-67255/4194304 : ℝ) ∧ Real.exp (-67255/4194304 : ℝ) ≤ (61505814509/62500000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984093032143/1000000000000 : ℝ) ≤ (radius 8 (67255/524288 : ℝ)) ∧ (radius 8 (67255/524288 : ℝ)) ≤ (61505814509/62500000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67255/524288 : ℝ)) (984093032143/1000000000000 : ℝ) (61505814509/62500000000 : ℝ) (177653888461/1000000000000 : ℝ) (44413472117/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67255/524288 : ℝ)) (984093032143/1000000000000 : ℝ) (61505814509/62500000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67255/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984093032143/1000000000000 : ℝ) (61505814509/62500000000 : ℝ) (992046516071/1000000000000 : ℝ) (124005814509/125000000000 : ℝ) (248003658257/250000000000 : ℝ) (99201463303/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67255/524288 : ℝ)) 1 (992046516071/1000000000000 : ℝ) (124005814509/125000000000 : ℝ) (248003658257/250000000000 : ℝ) (99201463303/100000000000 : ℝ) (992030574549/1000000000000 : ℝ) (992030574551/1000000000000 : ℝ) (992030574421/1000000000000 : ℝ) (992030574423/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67255/524288 : ℝ)) 2 (992030574549/1000000000000 : ℝ) (992030574551/1000000000000 : ℝ) (992030574421/1000000000000 : ℝ) (992030574423/1000000000000 : ℝ) (198406114897/200000000000 : ℝ) (992030574487/1000000000000 : ℝ) (248007643621/250000000000 : ℝ) (992030574487/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67255/524288 : ℝ)) 3 (198406114897/200000000000 : ℝ) (992030574487/1000000000000 : ℝ) (248007643621/250000000000 : ℝ) (992030574487/1000000000000 : ℝ) (248007643621/250000000000 : ℝ) (992030574487/1000000000000 : ℝ) (248007643621/250000000000 : ℝ) (992030574487/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67255/524288 : ℝ)) 4 (248007643621/250000000000 : ℝ) (992030574487/1000000000000 : ℝ) (248007643621/250000000000 : ℝ) (992030574487/1000000000000 : ℝ) (248007643621/250000000000 : ℝ) (992030574487/1000000000000 : ℝ) (248007643621/250000000000 : ℝ) (992030574487/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67255/524288 : ℝ)) 5 (248007643621/250000000000 : ℝ) (992030574487/1000000000000 : ℝ) (248007643621/250000000000 : ℝ) (992030574487/1000000000000 : ℝ) (248007643621/250000000000 : ℝ) (992030574487/1000000000000 : ℝ) (248007643621/250000000000 : ℝ) (992030574487/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67255/524288 : ℝ)) 6 (248007643621/250000000000 : ℝ) (992030574487/1000000000000 : ℝ) (248007643621/250000000000 : ℝ) (992030574487/1000000000000 : ℝ) (248007643621/250000000000 : ℝ) (992030574487/1000000000000 : ℝ) (248007643621/250000000000 : ℝ) (992030574487/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67255/524288 : ℝ)) 7 (248007643621/250000000000 : ℝ) (992030574487/1000000000000 : ℝ) (248007643621/250000000000 : ℝ) (992030574487/1000000000000 : ℝ) (248007643621/250000000000 : ℝ) (992030574487/1000000000000 : ℝ) (248007643621/250000000000 : ℝ) (992030574487/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67255/524288 : ℝ))) (177653888461/1000000000000 : ℝ) (44413472117/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67255/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177653888461/1000000000000 : ℝ) (44413472117/250000000000 : ℝ) (58882694423/100000000000 : ℝ) (294413472117/500000000000 : ℝ) (210745040547/500000000000 : ℝ) (421490081103/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67255/524288 : ℝ))) 1 (58882694423/100000000000 : ℝ) (294413472117/500000000000 : ℝ) (210745040547/500000000000 : ℝ) (421490081103/1000000000000 : ℝ) (252579256331/500000000000 : ℝ) (505158512669/1000000000000 : ℝ) (498181409201/1000000000000 : ℝ) (498181409209/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67255/524288 : ℝ))) 2 (252579256331/500000000000 : ℝ) (505158512669/1000000000000 : ℝ) (498181409201/1000000000000 : ℝ) (498181409209/1000000000000 : ℝ) (501669960931/1000000000000 : ℝ) (501669960939/1000000000000 : ℝ) (501657831303/1000000000000 : ℝ) (501657831311/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67255/524288 : ℝ))) 3 (501669960931/1000000000000 : ℝ) (501669960939/1000000000000 : ℝ) (501657831303/1000000000000 : ℝ) (501657831311/1000000000000 : ℝ) (501663896117/1000000000000 : ℝ) (4013311169/8000000000 : ℝ) (6270798701/12500000000 : ℝ) (501663896089/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67255/524288 : ℝ))) 4 (501663896117/1000000000000 : ℝ) (4013311169/8000000000 : ℝ) (6270798701/12500000000 : ℝ) (501663896089/1000000000000 : ℝ) (250831948049/500000000000 : ℝ) (501663896107/1000000000000 : ℝ) (250831948049/500000000000 : ℝ) (501663896107/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67255/524288 : ℝ))) 5 (250831948049/500000000000 : ℝ) (501663896107/1000000000000 : ℝ) (250831948049/500000000000 : ℝ) (501663896107/1000000000000 : ℝ) (250831948049/500000000000 : ℝ) (501663896107/1000000000000 : ℝ) (250831948049/500000000000 : ℝ) (501663896107/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67255/524288 : ℝ))) 6 (250831948049/500000000000 : ℝ) (501663896107/1000000000000 : ℝ) (250831948049/500000000000 : ℝ) (501663896107/1000000000000 : ℝ) (250831948049/500000000000 : ℝ) (501663896107/1000000000000 : ℝ) (250831948049/500000000000 : ℝ) (501663896107/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67255/524288 : ℝ))) 7 (250831948049/500000000000 : ℝ) (501663896107/1000000000000 : ℝ) (250831948049/500000000000 : ℝ) (501663896107/1000000000000 : ℝ) (250831948049/500000000000 : ℝ) (501663896107/1000000000000 : ℝ) (250831948049/500000000000 : ℝ) (501663896107/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67255/524288 : ℝ)) hmem 8 (248007643621/250000000000 : ℝ) (992030574487/1000000000000 : ℝ) (248007643621/250000000000 : ℝ) (992030574487/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67255/524288 : ℝ))) hcmem 8 (250831948049/500000000000 : ℝ) (501663896107/1000000000000 : ℝ) (250831948049/500000000000 : ℝ) (501663896107/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67255/524288 : ℝ)) (248007643621/250000000000 : ℝ) (992030574487/1000000000000 : ℝ) (250831948049/500000000000 : ℝ) (501663896107/1000000000000 : ℝ) (794342256723/1000000000000 : ℝ) (39717112837/50000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1182_exp_lower
  have heNumeric : (2054903584503/1000000000000 : ℝ)/4 ≤ Real.exp (-8525637526897/12800000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054903584503/1000000000000 : ℝ)/4 ≤ Real.exp ((33627/262144 : ℝ)-(39717112837/50000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33627/262144 : ℝ) (67255/524288 : ℝ) (39717112837/50000000000 : ℝ) (2054903584503/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1183; no trusted numerical premise.
theorem cover8_leaf1183_exp_radius : (249499405610911491/250000000000000000 : ℝ) ≤ Real.exp ((-8407/524288 : ℝ)/8) ∧ Real.exp ((-8407/524288 : ℝ)/8) ≤ (199599524488729193/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8407/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1183_exp_lower : (920113563290545907/1000000000000000000 : ℝ) ≤ Real.exp ((-85256374474393/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256374474393/128000000000000 : ℝ)/8) ≤ (230028390822636477/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256374474393/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1183_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054903597259/1000000000000 : ℝ) ≤ 4*Real.exp (67255/524288 : ℝ)*Real.exp (-mu (radius 8 (8407/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (2054903597259/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8407/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1183_exp_radius
  have hrNumeric : (984092797517/1000000000000 : ℝ) ≤ Real.exp (-8407/524288 : ℝ) ∧ Real.exp (-8407/524288 : ℝ) ≤ (492046398759/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984092797517/1000000000000 : ℝ) ≤ (radius 8 (8407/65536 : ℝ)) ∧ (radius 8 (8407/65536 : ℝ)) ≤ (492046398759/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8407/65536 : ℝ)) (984092797517/1000000000000 : ℝ) (492046398759/500000000000 : ℝ) (8882759407/50000000000 : ℝ) (88827594073/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8407/65536 : ℝ)) (984092797517/1000000000000 : ℝ) (492046398759/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8407/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984092797517/1000000000000 : ℝ) (492046398759/500000000000 : ℝ) (496023199379/500000000000 : ℝ) (992046398759/1000000000000 : ℝ) (992014514771/1000000000000 : ℝ) (248003628693/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8407/65536 : ℝ)) 1 (496023199379/500000000000 : ℝ) (992046398759/1000000000000 : ℝ) (992014514771/1000000000000 : ℝ) (248003628693/250000000000 : ℝ) (248007614191/250000000000 : ℝ) (496015228383/500000000000 : ℝ) (248007614159/250000000000 : ℝ) (496015228319/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8407/65536 : ℝ)) 2 (248007614191/250000000000 : ℝ) (496015228383/500000000000 : ℝ) (248007614159/250000000000 : ℝ) (496015228319/500000000000 : ℝ) (9920304567/10000000000 : ℝ) (496015228351/500000000000 : ℝ) (992030456699/1000000000000 : ℝ) (496015228351/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8407/65536 : ℝ)) 3 (9920304567/10000000000 : ℝ) (496015228351/500000000000 : ℝ) (992030456699/1000000000000 : ℝ) (496015228351/500000000000 : ℝ) (992030456699/1000000000000 : ℝ) (496015228351/500000000000 : ℝ) (992030456699/1000000000000 : ℝ) (496015228351/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8407/65536 : ℝ)) 4 (992030456699/1000000000000 : ℝ) (496015228351/500000000000 : ℝ) (992030456699/1000000000000 : ℝ) (496015228351/500000000000 : ℝ) (992030456699/1000000000000 : ℝ) (496015228351/500000000000 : ℝ) (992030456699/1000000000000 : ℝ) (496015228351/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8407/65536 : ℝ)) 5 (992030456699/1000000000000 : ℝ) (496015228351/500000000000 : ℝ) (992030456699/1000000000000 : ℝ) (496015228351/500000000000 : ℝ) (992030456699/1000000000000 : ℝ) (496015228351/500000000000 : ℝ) (992030456699/1000000000000 : ℝ) (496015228351/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8407/65536 : ℝ)) 6 (992030456699/1000000000000 : ℝ) (496015228351/500000000000 : ℝ) (992030456699/1000000000000 : ℝ) (496015228351/500000000000 : ℝ) (992030456699/1000000000000 : ℝ) (496015228351/500000000000 : ℝ) (992030456699/1000000000000 : ℝ) (496015228351/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8407/65536 : ℝ)) 7 (992030456699/1000000000000 : ℝ) (496015228351/500000000000 : ℝ) (992030456699/1000000000000 : ℝ) (496015228351/500000000000 : ℝ) (992030456699/1000000000000 : ℝ) (496015228351/500000000000 : ℝ) (992030456699/1000000000000 : ℝ) (496015228351/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8407/65536 : ℝ))) (8882759407/50000000000 : ℝ) (88827594073/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8407/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (8882759407/50000000000 : ℝ) (88827594073/500000000000 : ℝ) (58882759407/100000000000 : ℝ) (588827594073/1000000000000 : ℝ) (210745811429/500000000000 : ℝ) (210745811433/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8407/65536 : ℝ))) 1 (58882759407/100000000000 : ℝ) (588827594073/1000000000000 : ℝ) (210745811429/500000000000 : ℝ) (210745811433/500000000000 : ℝ) (31572475529/62500000000 : ℝ) (50515960847/100000000000 : ℝ) (31136412203/62500000000 : ℝ) (99636519051/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8407/65536 : ℝ))) 2 (31572475529/62500000000 : ℝ) (50515960847/100000000000 : ℝ) (31136412203/62500000000 : ℝ) (99636519051/200000000000 : ℝ) (15677221933/31250000000 : ℝ) (501671101863/1000000000000 : ℝ) (501658972569/1000000000000 : ℝ) (15676842893/31250000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8407/65536 : ℝ))) 3 (15677221933/31250000000 : ℝ) (501671101863/1000000000000 : ℝ) (501658972569/1000000000000 : ℝ) (15676842893/31250000000 : ℝ) (125416259303/250000000000 : ℝ) (25083251861/50000000000 : ℝ) (20066601487/40000000000 : ℝ) (501665037183/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8407/65536 : ℝ))) 4 (125416259303/250000000000 : ℝ) (25083251861/50000000000 : ℝ) (20066601487/40000000000 : ℝ) (501665037183/1000000000000 : ℝ) (501665037193/1000000000000 : ℝ) (250832518601/500000000000 : ℝ) (501665037193/1000000000000 : ℝ) (250832518601/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8407/65536 : ℝ))) 5 (501665037193/1000000000000 : ℝ) (250832518601/500000000000 : ℝ) (501665037193/1000000000000 : ℝ) (250832518601/500000000000 : ℝ) (501665037193/1000000000000 : ℝ) (250832518601/500000000000 : ℝ) (501665037193/1000000000000 : ℝ) (250832518601/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8407/65536 : ℝ))) 6 (501665037193/1000000000000 : ℝ) (250832518601/500000000000 : ℝ) (501665037193/1000000000000 : ℝ) (250832518601/500000000000 : ℝ) (501665037193/1000000000000 : ℝ) (250832518601/500000000000 : ℝ) (501665037193/1000000000000 : ℝ) (250832518601/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8407/65536 : ℝ))) 7 (501665037193/1000000000000 : ℝ) (250832518601/500000000000 : ℝ) (501665037193/1000000000000 : ℝ) (250832518601/500000000000 : ℝ) (501665037193/1000000000000 : ℝ) (250832518601/500000000000 : ℝ) (501665037193/1000000000000 : ℝ) (250832518601/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8407/65536 : ℝ)) hmem 8 (992030456699/1000000000000 : ℝ) (496015228351/500000000000 : ℝ) (992030456699/1000000000000 : ℝ) (496015228351/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8407/65536 : ℝ))) hcmem 8 (501665037193/1000000000000 : ℝ) (250832518601/500000000000 : ℝ) (501665037193/1000000000000 : ℝ) (250832518601/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8407/65536 : ℝ)) (992030456699/1000000000000 : ℝ) (496015228351/500000000000 : ℝ) (501665037193/1000000000000 : ℝ) (250832518601/500000000000 : ℝ) (794344157863/1000000000000 : ℝ) (794344157881/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1183_exp_lower
  have heNumeric : (2054903597259/1000000000000 : ℝ)/4 ≤ Real.exp (-85256374474393/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054903597259/1000000000000 : ℝ)/4 ≤ Real.exp ((67255/524288 : ℝ)-(794344157881/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67255/524288 : ℝ) (8407/65536 : ℝ) (794344157881/1000000000000 : ℝ) (2054903597259/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1184; no trusted numerical premise.
theorem cover8_leaf1184_exp_radius : (997997592700999521/1000000000000000000 : ℝ) ≤ Real.exp ((-67257/4194304 : ℝ)/8) ∧ Real.exp ((-67257/4194304 : ℝ)/8) ≤ (498998796350499761/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67257/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1184_exp_lower : (920113564006927099/1000000000000000000 : ℝ) ≤ Real.exp ((-10657046709641/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657046709641/16000000000000 : ℝ)/8) ≤ (9201135640069271/10000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657046709641/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1184_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451805029/500000000000 : ℝ) ≤ 4*Real.exp (8407/65536 : ℝ)*Real.exp (-mu (radius 8 (67257/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451805029/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67257/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1184_exp_radius
  have hrNumeric : (984092562891/1000000000000 : ℝ) ≤ Real.exp (-67257/4194304 : ℝ) ∧ Real.exp (-67257/4194304 : ℝ) ≤ (246023140723/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984092562891/1000000000000 : ℝ) ≤ (radius 8 (67257/524288 : ℝ)) ∧ (radius 8 (67257/524288 : ℝ)) ≤ (246023140723/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67257/524288 : ℝ)) (984092562891/1000000000000 : ℝ) (246023140723/250000000000 : ℝ) (177656487809/1000000000000 : ℝ) (35531297563/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67257/524288 : ℝ)) (984092562891/1000000000000 : ℝ) (246023140723/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67257/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984092562891/1000000000000 : ℝ) (246023140723/250000000000 : ℝ) (198409256289/200000000000 : ℝ) (496023140723/500000000000 : ℝ) (992014396513/1000000000000 : ℝ) (198402879303/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67257/524288 : ℝ)) 1 (198409256289/200000000000 : ℝ) (496023140723/500000000000 : ℝ) (992014396513/1000000000000 : ℝ) (198402879303/200000000000 : ℝ) (992030338979/1000000000000 : ℝ) (992030338981/1000000000000 : ℝ) (19840606777/20000000000 : ℝ) (992030338853/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67257/524288 : ℝ)) 2 (992030338979/1000000000000 : ℝ) (992030338981/1000000000000 : ℝ) (19840606777/20000000000 : ℝ) (992030338853/1000000000000 : ℝ) (496015169457/500000000000 : ℝ) (992030338917/1000000000000 : ℝ) (496015169457/500000000000 : ℝ) (992030338917/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67257/524288 : ℝ)) 3 (496015169457/500000000000 : ℝ) (992030338917/1000000000000 : ℝ) (496015169457/500000000000 : ℝ) (992030338917/1000000000000 : ℝ) (496015169457/500000000000 : ℝ) (992030338917/1000000000000 : ℝ) (496015169457/500000000000 : ℝ) (992030338917/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67257/524288 : ℝ)) 4 (496015169457/500000000000 : ℝ) (992030338917/1000000000000 : ℝ) (496015169457/500000000000 : ℝ) (992030338917/1000000000000 : ℝ) (496015169457/500000000000 : ℝ) (992030338917/1000000000000 : ℝ) (496015169457/500000000000 : ℝ) (992030338917/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67257/524288 : ℝ)) 5 (496015169457/500000000000 : ℝ) (992030338917/1000000000000 : ℝ) (496015169457/500000000000 : ℝ) (992030338917/1000000000000 : ℝ) (496015169457/500000000000 : ℝ) (992030338917/1000000000000 : ℝ) (496015169457/500000000000 : ℝ) (992030338917/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67257/524288 : ℝ)) 6 (496015169457/500000000000 : ℝ) (992030338917/1000000000000 : ℝ) (496015169457/500000000000 : ℝ) (992030338917/1000000000000 : ℝ) (496015169457/500000000000 : ℝ) (992030338917/1000000000000 : ℝ) (496015169457/500000000000 : ℝ) (992030338917/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67257/524288 : ℝ)) 7 (496015169457/500000000000 : ℝ) (992030338917/1000000000000 : ℝ) (496015169457/500000000000 : ℝ) (992030338917/1000000000000 : ℝ) (496015169457/500000000000 : ℝ) (992030338917/1000000000000 : ℝ) (496015169457/500000000000 : ℝ) (992030338917/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67257/524288 : ℝ))) (177656487809/1000000000000 : ℝ) (35531297563/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67257/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177656487809/1000000000000 : ℝ) (35531297563/200000000000 : ℝ) (9200441311/15625000000 : ℝ) (147207060977/250000000000 : ℝ) (84298632921/200000000000 : ℝ) (421493164613/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67257/524288 : ℝ))) 1 (9200441311/15625000000 : ℝ) (147207060977/250000000000 : ℝ) (84298632921/200000000000 : ℝ) (421493164613/1000000000000 : ℝ) (252580352127/500000000000 : ℝ) (505160704261/1000000000000 : ℝ) (498183781281/1000000000000 : ℝ) (62272972661/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67257/524288 : ℝ))) 2 (252580352127/500000000000 : ℝ) (505160704261/1000000000000 : ℝ) (498183781281/1000000000000 : ℝ) (62272972661/125000000000 : ℝ) (501672242767/1000000000000 : ℝ) (20066889711/40000000000 : ℝ) (501660113821/1000000000000 : ℝ) (501660113829/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67257/524288 : ℝ))) 3 (501672242767/1000000000000 : ℝ) (20066889711/40000000000 : ℝ) (501660113821/1000000000000 : ℝ) (501660113829/1000000000000 : ℝ) (250833089147/500000000000 : ℝ) (250833089151/500000000000 : ℝ) (501666178257/1000000000000 : ℝ) (250833089133/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67257/524288 : ℝ))) 4 (250833089147/500000000000 : ℝ) (250833089151/500000000000 : ℝ) (501666178257/1000000000000 : ℝ) (250833089133/500000000000 : ℝ) (20066647131/40000000000 : ℝ) (125416544571/250000000000 : ℝ) (20066647131/40000000000 : ℝ) (125416544571/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67257/524288 : ℝ))) 5 (20066647131/40000000000 : ℝ) (125416544571/250000000000 : ℝ) (20066647131/40000000000 : ℝ) (125416544571/250000000000 : ℝ) (20066647131/40000000000 : ℝ) (125416544571/250000000000 : ℝ) (20066647131/40000000000 : ℝ) (125416544571/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67257/524288 : ℝ))) 6 (20066647131/40000000000 : ℝ) (125416544571/250000000000 : ℝ) (20066647131/40000000000 : ℝ) (125416544571/250000000000 : ℝ) (20066647131/40000000000 : ℝ) (125416544571/250000000000 : ℝ) (20066647131/40000000000 : ℝ) (125416544571/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67257/524288 : ℝ))) 7 (20066647131/40000000000 : ℝ) (125416544571/250000000000 : ℝ) (20066647131/40000000000 : ℝ) (125416544571/250000000000 : ℝ) (20066647131/40000000000 : ℝ) (125416544571/250000000000 : ℝ) (20066647131/40000000000 : ℝ) (125416544571/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67257/524288 : ℝ)) hmem 8 (496015169457/500000000000 : ℝ) (992030338917/1000000000000 : ℝ) (496015169457/500000000000 : ℝ) (992030338917/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67257/524288 : ℝ))) hcmem 8 (20066647131/40000000000 : ℝ) (125416544571/250000000000 : ℝ) (20066647131/40000000000 : ℝ) (125416544571/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67257/524288 : ℝ)) (496015169457/500000000000 : ℝ) (992030338917/1000000000000 : ℝ) (20066647131/40000000000 : ℝ) (125416544571/250000000000 : ℝ) (99293257373/125000000000 : ℝ) (794346059001/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1184_exp_lower
  have heNumeric : (1027451805029/500000000000 : ℝ)/4 ≤ Real.exp (-10657046709641/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451805029/500000000000 : ℝ)/4 ≤ Real.exp ((8407/65536 : ℝ)-(794346059001/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8407/65536 : ℝ) (67257/524288 : ℝ) (794346059001/1000000000000 : ℝ) (1027451805029/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1185; no trusted numerical premise.
theorem cover8_leaf1185_exp_radius : (199599512591670793/200000000000000000 : ℝ) ≤ Real.exp ((-33629/2097152 : ℝ)/8) ∧ Real.exp ((-33629/2097152 : ℝ)/8) ≤ (498998781479176983/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33629/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1185_exp_lower : (460056782362689273/500000000000000000 : ℝ) ≤ Real.exp ((-85256372877559/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256372877559/128000000000000 : ℝ)/8) ≤ (920113564725378547/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256372877559/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1185_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410980724579/200000000000 : ℝ) ≤ 4*Real.exp (67257/524288 : ℝ)*Real.exp (-mu (radius 8 (33629/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (410980724579/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33629/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1185_exp_radius
  have hrNumeric : (196818465653/200000000000 : ℝ) ≤ Real.exp (-33629/2097152 : ℝ) ∧ Real.exp (-33629/2097152 : ℝ) ≤ (492046164133/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196818465653/200000000000 : ℝ) ≤ (radius 8 (33629/262144 : ℝ)) ∧ (radius 8 (33629/262144 : ℝ)) ≤ (492046164133/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33629/262144 : ℝ)) (196818465653/200000000000 : ℝ) (492046164133/500000000000 : ℝ) (177657787467/1000000000000 : ℝ) (88828893737/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33629/262144 : ℝ)) (196818465653/200000000000 : ℝ) (492046164133/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33629/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196818465653/200000000000 : ℝ) (492046164133/500000000000 : ℝ) (248011541033/250000000000 : ℝ) (992046164133/1000000000000 : ℝ) (62000892391/62500000000 : ℝ) (496007139129/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33629/262144 : ℝ)) 1 (248011541033/250000000000 : ℝ) (992046164133/1000000000000 : ℝ) (62000892391/62500000000 : ℝ) (496007139129/500000000000 : ℝ) (496015110597/500000000000 : ℝ) (248007555299/250000000000 : ℝ) (198406044213/200000000000 : ℝ) (248007555267/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33629/262144 : ℝ)) 2 (496015110597/500000000000 : ℝ) (248007555299/250000000000 : ℝ) (198406044213/200000000000 : ℝ) (248007555267/250000000000 : ℝ) (992030221129/1000000000000 : ℝ) (248007555283/250000000000 : ℝ) (992030221129/1000000000000 : ℝ) (248007555283/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33629/262144 : ℝ)) 3 (992030221129/1000000000000 : ℝ) (248007555283/250000000000 : ℝ) (992030221129/1000000000000 : ℝ) (248007555283/250000000000 : ℝ) (992030221129/1000000000000 : ℝ) (248007555283/250000000000 : ℝ) (992030221129/1000000000000 : ℝ) (248007555283/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33629/262144 : ℝ)) 4 (992030221129/1000000000000 : ℝ) (248007555283/250000000000 : ℝ) (992030221129/1000000000000 : ℝ) (248007555283/250000000000 : ℝ) (992030221129/1000000000000 : ℝ) (248007555283/250000000000 : ℝ) (992030221129/1000000000000 : ℝ) (248007555283/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33629/262144 : ℝ)) 5 (992030221129/1000000000000 : ℝ) (248007555283/250000000000 : ℝ) (992030221129/1000000000000 : ℝ) (248007555283/250000000000 : ℝ) (992030221129/1000000000000 : ℝ) (248007555283/250000000000 : ℝ) (992030221129/1000000000000 : ℝ) (248007555283/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33629/262144 : ℝ)) 6 (992030221129/1000000000000 : ℝ) (248007555283/250000000000 : ℝ) (992030221129/1000000000000 : ℝ) (248007555283/250000000000 : ℝ) (992030221129/1000000000000 : ℝ) (248007555283/250000000000 : ℝ) (992030221129/1000000000000 : ℝ) (248007555283/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33629/262144 : ℝ)) 7 (992030221129/1000000000000 : ℝ) (248007555283/250000000000 : ℝ) (992030221129/1000000000000 : ℝ) (248007555283/250000000000 : ℝ) (992030221129/1000000000000 : ℝ) (248007555283/250000000000 : ℝ) (992030221129/1000000000000 : ℝ) (248007555283/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33629/262144 : ℝ))) (177657787467/1000000000000 : ℝ) (88828893737/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33629/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177657787467/1000000000000 : ℝ) (88828893737/500000000000 : ℝ) (588828893733/1000000000000 : ℝ) (588828893737/1000000000000 : ℝ) (421494706333/1000000000000 : ℝ) (210747353171/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33629/262144 : ℝ))) 1 (588828893733/1000000000000 : ℝ) (588828893737/1000000000000 : ℝ) (421494706333/1000000000000 : ℝ) (210747353171/500000000000 : ℝ) (505161800033/1000000000000 : ℝ) (12629045001/25000000000 : ℝ) (4981849673/10000000000 : ℝ) (124546241827/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33629/262144 : ℝ))) 2 (505161800033/1000000000000 : ℝ) (12629045001/25000000000 : ℝ) (4981849673/10000000000 : ℝ) (124546241827/250000000000 : ℝ) (250836691833/500000000000 : ℝ) (250836691837/500000000000 : ℝ) (250830627531/500000000000 : ℝ) (50166125507/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33629/262144 : ℝ))) 3 (250836691833/500000000000 : ℝ) (250836691837/500000000000 : ℝ) (250830627531/500000000000 : ℝ) (50166125507/100000000000 : ℝ) (125416829841/250000000000 : ℝ) (125416829843/250000000000 : ℝ) (501667319327/1000000000000 : ℝ) (62708414917/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33629/262144 : ℝ))) 4 (125416829841/250000000000 : ℝ) (125416829843/250000000000 : ℝ) (501667319327/1000000000000 : ℝ) (62708414917/125000000000 : ℝ) (100333463869/200000000000 : ℝ) (250833659677/500000000000 : ℝ) (100333463869/200000000000 : ℝ) (250833659677/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33629/262144 : ℝ))) 5 (100333463869/200000000000 : ℝ) (250833659677/500000000000 : ℝ) (100333463869/200000000000 : ℝ) (250833659677/500000000000 : ℝ) (100333463869/200000000000 : ℝ) (250833659677/500000000000 : ℝ) (100333463869/200000000000 : ℝ) (250833659677/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33629/262144 : ℝ))) 6 (100333463869/200000000000 : ℝ) (250833659677/500000000000 : ℝ) (100333463869/200000000000 : ℝ) (250833659677/500000000000 : ℝ) (100333463869/200000000000 : ℝ) (250833659677/500000000000 : ℝ) (100333463869/200000000000 : ℝ) (250833659677/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33629/262144 : ℝ))) 7 (100333463869/200000000000 : ℝ) (250833659677/500000000000 : ℝ) (100333463869/200000000000 : ℝ) (250833659677/500000000000 : ℝ) (100333463869/200000000000 : ℝ) (250833659677/500000000000 : ℝ) (100333463869/200000000000 : ℝ) (250833659677/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33629/262144 : ℝ)) hmem 8 (992030221129/1000000000000 : ℝ) (248007555283/250000000000 : ℝ) (992030221129/1000000000000 : ℝ) (248007555283/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33629/262144 : ℝ))) hcmem 8 (100333463869/200000000000 : ℝ) (250833659677/500000000000 : ℝ) (100333463869/200000000000 : ℝ) (250833659677/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33629/262144 : ℝ)) (992030221129/1000000000000 : ℝ) (248007555283/250000000000 : ℝ) (100333463869/200000000000 : ℝ) (250833659677/500000000000 : ℝ) (397173980043/500000000000 : ℝ) (794347960103/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1185_exp_lower
  have heNumeric : (410980724579/200000000000 : ℝ)/4 ≤ Real.exp (-85256372877559/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410980724579/200000000000 : ℝ)/4 ≤ Real.exp ((67257/524288 : ℝ)-(794347960103/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67257/524288 : ℝ) (33629/262144 : ℝ) (794347960103/1000000000000 : ℝ) (410980724579/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1186; no trusted numerical premise.
theorem cover8_leaf1186_exp_radius : (498998766607854647/500000000000000000 : ℝ) ≤ Real.exp ((-67259/4194304 : ℝ)/8) ∧ Real.exp ((-67259/4194304 : ℝ)/8) ≤ (199599506643141859/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67259/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1186_exp_lower : (230028391361446309/250000000000000000 : ℝ) ≤ Real.exp ((-42628186037907/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628186037907/64000000000000 : ℝ)/8) ≤ (920113565445785237/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628186037907/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1186_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451817883/500000000000 : ℝ) ≤ 4*Real.exp (33629/262144 : ℝ)*Real.exp (-mu (radius 8 (67259/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451817883/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67259/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1186_exp_radius
  have hrNumeric : (984092093639/1000000000000 : ℝ) ≤ Real.exp (-67259/4194304 : ℝ) ∧ Real.exp (-67259/4194304 : ℝ) ≤ (24602302341/25000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984092093639/1000000000000 : ℝ) ≤ (radius 8 (67259/524288 : ℝ)) ∧ (radius 8 (67259/524288 : ℝ)) ≤ (24602302341/25000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67259/524288 : ℝ)) (984092093639/1000000000000 : ℝ) (24602302341/25000000000 : ℝ) (44414771779/250000000000 : ℝ) (177659087123/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67259/524288 : ℝ)) (984092093639/1000000000000 : ℝ) (24602302341/25000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67259/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984092093639/1000000000000 : ℝ) (24602302341/25000000000 : ℝ) (992046046819/1000000000000 : ℝ) (49602302341/50000000000 : ℝ) (992014159999/1000000000000 : ℝ) (12400177/12500000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67259/524288 : ℝ)) 1 (992046046819/1000000000000 : ℝ) (49602302341/50000000000 : ℝ) (992014159999/1000000000000 : ℝ) (12400177/12500000 : ℝ) (992030103409/1000000000000 : ℝ) (99203010341/100000000000 : ℝ) (12400376291/12500000000 : ℝ) (496015051641/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67259/524288 : ℝ)) 2 (992030103409/1000000000000 : ℝ) (99203010341/100000000000 : ℝ) (12400376291/12500000000 : ℝ) (496015051641/500000000000 : ℝ) (62001881459/62500000000 : ℝ) (496015051673/500000000000 : ℝ) (62001881459/62500000000 : ℝ) (496015051673/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67259/524288 : ℝ)) 3 (62001881459/62500000000 : ℝ) (496015051673/500000000000 : ℝ) (62001881459/62500000000 : ℝ) (496015051673/500000000000 : ℝ) (62001881459/62500000000 : ℝ) (496015051673/500000000000 : ℝ) (62001881459/62500000000 : ℝ) (496015051673/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67259/524288 : ℝ)) 4 (62001881459/62500000000 : ℝ) (496015051673/500000000000 : ℝ) (62001881459/62500000000 : ℝ) (496015051673/500000000000 : ℝ) (62001881459/62500000000 : ℝ) (496015051673/500000000000 : ℝ) (62001881459/62500000000 : ℝ) (496015051673/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67259/524288 : ℝ)) 5 (62001881459/62500000000 : ℝ) (496015051673/500000000000 : ℝ) (62001881459/62500000000 : ℝ) (496015051673/500000000000 : ℝ) (62001881459/62500000000 : ℝ) (496015051673/500000000000 : ℝ) (62001881459/62500000000 : ℝ) (496015051673/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67259/524288 : ℝ)) 6 (62001881459/62500000000 : ℝ) (496015051673/500000000000 : ℝ) (62001881459/62500000000 : ℝ) (496015051673/500000000000 : ℝ) (62001881459/62500000000 : ℝ) (496015051673/500000000000 : ℝ) (62001881459/62500000000 : ℝ) (496015051673/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67259/524288 : ℝ)) 7 (62001881459/62500000000 : ℝ) (496015051673/500000000000 : ℝ) (62001881459/62500000000 : ℝ) (496015051673/500000000000 : ℝ) (62001881459/62500000000 : ℝ) (496015051673/500000000000 : ℝ) (62001881459/62500000000 : ℝ) (496015051673/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67259/524288 : ℝ))) (44414771779/250000000000 : ℝ) (177659087123/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67259/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44414771779/250000000000 : ℝ) (177659087123/1000000000000 : ℝ) (294414771779/500000000000 : ℝ) (294414771781/500000000000 : ℝ) (105374062011/250000000000 : ℝ) (210748124027/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67259/524288 : ℝ))) 1 (294414771779/500000000000 : ℝ) (294414771781/500000000000 : ℝ) (105374062011/250000000000 : ℝ) (210748124027/500000000000 : ℝ) (505162895801/1000000000000 : ℝ) (7893170247/15625000000 : ℝ) (498186153307/1000000000000 : ℝ) (99637230663/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67259/524288 : ℝ))) 2 (505162895801/1000000000000 : ℝ) (7893170247/15625000000 : ℝ) (498186153307/1000000000000 : ℝ) (99637230663/200000000000 : ℝ) (250837262277/500000000000 : ℝ) (250837262281/500000000000 : ℝ) (501662396291/1000000000000 : ℝ) (501662396299/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67259/524288 : ℝ))) 3 (250837262277/500000000000 : ℝ) (250837262281/500000000000 : ℝ) (501662396291/1000000000000 : ℝ) (501662396299/1000000000000 : ℝ) (250834230211/500000000000 : ℝ) (501668460431/1000000000000 : ℝ) (100333692077/200000000000 : ℝ) (250834230197/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67259/524288 : ℝ))) 4 (250834230211/500000000000 : ℝ) (501668460431/1000000000000 : ℝ) (100333692077/200000000000 : ℝ) (250834230197/500000000000 : ℝ) (501668460403/1000000000000 : ℝ) (501668460413/1000000000000 : ℝ) (501668460403/1000000000000 : ℝ) (501668460413/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67259/524288 : ℝ))) 5 (501668460403/1000000000000 : ℝ) (501668460413/1000000000000 : ℝ) (501668460403/1000000000000 : ℝ) (501668460413/1000000000000 : ℝ) (501668460403/1000000000000 : ℝ) (501668460413/1000000000000 : ℝ) (501668460403/1000000000000 : ℝ) (501668460413/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67259/524288 : ℝ))) 6 (501668460403/1000000000000 : ℝ) (501668460413/1000000000000 : ℝ) (501668460403/1000000000000 : ℝ) (501668460413/1000000000000 : ℝ) (501668460403/1000000000000 : ℝ) (501668460413/1000000000000 : ℝ) (501668460403/1000000000000 : ℝ) (501668460413/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67259/524288 : ℝ))) 7 (501668460403/1000000000000 : ℝ) (501668460413/1000000000000 : ℝ) (501668460403/1000000000000 : ℝ) (501668460413/1000000000000 : ℝ) (501668460403/1000000000000 : ℝ) (501668460413/1000000000000 : ℝ) (501668460403/1000000000000 : ℝ) (501668460413/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67259/524288 : ℝ)) hmem 8 (62001881459/62500000000 : ℝ) (496015051673/500000000000 : ℝ) (62001881459/62500000000 : ℝ) (496015051673/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67259/524288 : ℝ))) hcmem 8 (501668460403/1000000000000 : ℝ) (501668460413/1000000000000 : ℝ) (501668460403/1000000000000 : ℝ) (501668460413/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67259/524288 : ℝ)) (62001881459/62500000000 : ℝ) (496015051673/500000000000 : ℝ) (501668460403/1000000000000 : ℝ) (501668460413/1000000000000 : ℝ) (79434986117/100000000000 : ℝ) (198587465297/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1186_exp_lower
  have heNumeric : (1027451817883/500000000000 : ℝ)/4 ≤ Real.exp (-42628186037907/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451817883/500000000000 : ℝ)/4 ≤ Real.exp ((33629/262144 : ℝ)-(198587465297/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33629/262144 : ℝ) (67259/524288 : ℝ) (198587465297/250000000000 : ℝ) (1027451817883/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1187; no trusted numerical premise.
theorem cover8_leaf1187_exp_radius : (99799750347306551/100000000000000000 : ℝ) ≤ Real.exp ((-16815/1048576 : ℝ)/8) ∧ Real.exp ((-16815/1048576 : ℝ)/8) ≤ (997997503473065511/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16815/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1187_exp_lower : (230028391542353081/250000000000000000 : ℝ) ≤ Real.exp ((-17051274254097/25600000000000 : ℝ)/8) ∧ Real.exp ((-17051274254097/25600000000000 : ℝ)/8) ≤ (36804542646776493/40000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-17051274254097/25600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1187_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410980729739/200000000000 : ℝ) ≤ 4*Real.exp (67259/524288 : ℝ)*Real.exp (-mu (radius 8 (16815/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (410980729739/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16815/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1187_exp_radius
  have hrNumeric : (492045929507/500000000000 : ℝ) ≤ Real.exp (-16815/1048576 : ℝ) ∧ Real.exp (-16815/1048576 : ℝ) ≤ (196818371803/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492045929507/500000000000 : ℝ) ≤ (radius 8 (16815/131072 : ℝ)) ∧ (radius 8 (16815/131072 : ℝ)) ≤ (196818371803/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16815/131072 : ℝ)) (492045929507/500000000000 : ℝ) (196818371803/200000000000 : ℝ) (710641547/4000000000 : ℝ) (177660386757/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16815/131072 : ℝ)) (492045929507/500000000000 : ℝ) (196818371803/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16815/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492045929507/500000000000 : ℝ) (196818371803/200000000000 : ℝ) (992045929507/1000000000000 : ℝ) (248011482377/250000000000 : ℝ) (496007020871/500000000000 : ℝ) (992014041743/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16815/131072 : ℝ)) 1 (992045929507/1000000000000 : ℝ) (248011482377/250000000000 : ℝ) (496007020871/500000000000 : ℝ) (992014041743/1000000000000 : ℝ) (124003748203/125000000000 : ℝ) (496014992813/500000000000 : ℝ) (124003748187/125000000000 : ℝ) (496014992749/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16815/131072 : ℝ)) 2 (124003748203/125000000000 : ℝ) (496014992813/500000000000 : ℝ) (124003748187/125000000000 : ℝ) (496014992749/500000000000 : ℝ) (24800749639/25000000000 : ℝ) (496014992781/500000000000 : ℝ) (992029985559/1000000000000 : ℝ) (496014992781/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16815/131072 : ℝ)) 3 (24800749639/25000000000 : ℝ) (496014992781/500000000000 : ℝ) (992029985559/1000000000000 : ℝ) (496014992781/500000000000 : ℝ) (992029985559/1000000000000 : ℝ) (496014992781/500000000000 : ℝ) (992029985559/1000000000000 : ℝ) (496014992781/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16815/131072 : ℝ)) 4 (992029985559/1000000000000 : ℝ) (496014992781/500000000000 : ℝ) (992029985559/1000000000000 : ℝ) (496014992781/500000000000 : ℝ) (992029985559/1000000000000 : ℝ) (496014992781/500000000000 : ℝ) (992029985559/1000000000000 : ℝ) (496014992781/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16815/131072 : ℝ)) 5 (992029985559/1000000000000 : ℝ) (496014992781/500000000000 : ℝ) (992029985559/1000000000000 : ℝ) (496014992781/500000000000 : ℝ) (992029985559/1000000000000 : ℝ) (496014992781/500000000000 : ℝ) (992029985559/1000000000000 : ℝ) (496014992781/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16815/131072 : ℝ)) 6 (992029985559/1000000000000 : ℝ) (496014992781/500000000000 : ℝ) (992029985559/1000000000000 : ℝ) (496014992781/500000000000 : ℝ) (992029985559/1000000000000 : ℝ) (496014992781/500000000000 : ℝ) (992029985559/1000000000000 : ℝ) (496014992781/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16815/131072 : ℝ)) 7 (992029985559/1000000000000 : ℝ) (496014992781/500000000000 : ℝ) (992029985559/1000000000000 : ℝ) (496014992781/500000000000 : ℝ) (992029985559/1000000000000 : ℝ) (496014992781/500000000000 : ℝ) (992029985559/1000000000000 : ℝ) (496014992781/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16815/131072 : ℝ))) (710641547/4000000000 : ℝ) (177660386757/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16815/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (710641547/4000000000 : ℝ) (177660386757/1000000000000 : ℝ) (4710641547/8000000000 : ℝ) (588830193379/1000000000000 : ℝ) (421497789733/1000000000000 : ℝ) (210748894871/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16815/131072 : ℝ))) 1 (4710641547/8000000000 : ℝ) (588830193379/1000000000000 : ℝ) (421497789733/1000000000000 : ℝ) (210748894871/500000000000 : ℝ) (252581995777/500000000000 : ℝ) (505163991561/1000000000000 : ℝ) (15568354353/31250000000 : ℝ) (62273417413/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16815/131072 : ℝ))) 2 (252581995777/500000000000 : ℝ) (505163991561/1000000000000 : ℝ) (15568354353/31250000000 : ℝ) (62273417413/125000000000 : ℝ) (20067026617/40000000000 : ℝ) (501675665433/1000000000000 : ℝ) (501663537503/1000000000000 : ℝ) (501663537511/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16815/131072 : ℝ))) 3 (20067026617/40000000000 : ℝ) (501675665433/1000000000000 : ℝ) (501663537503/1000000000000 : ℝ) (501663537511/1000000000000 : ℝ) (62708700183/125000000000 : ℝ) (7838587523/15625000000 : ℝ) (501669601427/1000000000000 : ℝ) (125417400359/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16815/131072 : ℝ))) 4 (62708700183/125000000000 : ℝ) (7838587523/15625000000 : ℝ) (501669601427/1000000000000 : ℝ) (125417400359/250000000000 : ℝ) (100333920289/200000000000 : ℝ) (250834800727/500000000000 : ℝ) (100333920289/200000000000 : ℝ) (250834800727/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16815/131072 : ℝ))) 5 (100333920289/200000000000 : ℝ) (250834800727/500000000000 : ℝ) (100333920289/200000000000 : ℝ) (250834800727/500000000000 : ℝ) (100333920289/200000000000 : ℝ) (250834800727/500000000000 : ℝ) (100333920289/200000000000 : ℝ) (250834800727/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16815/131072 : ℝ))) 6 (100333920289/200000000000 : ℝ) (250834800727/500000000000 : ℝ) (100333920289/200000000000 : ℝ) (250834800727/500000000000 : ℝ) (100333920289/200000000000 : ℝ) (250834800727/500000000000 : ℝ) (100333920289/200000000000 : ℝ) (250834800727/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16815/131072 : ℝ))) 7 (100333920289/200000000000 : ℝ) (250834800727/500000000000 : ℝ) (100333920289/200000000000 : ℝ) (250834800727/500000000000 : ℝ) (100333920289/200000000000 : ℝ) (250834800727/500000000000 : ℝ) (100333920289/200000000000 : ℝ) (250834800727/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16815/131072 : ℝ)) hmem 8 (992029985559/1000000000000 : ℝ) (496014992781/500000000000 : ℝ) (992029985559/1000000000000 : ℝ) (496014992781/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16815/131072 : ℝ))) hcmem 8 (100333920289/200000000000 : ℝ) (250834800727/500000000000 : ℝ) (100333920289/200000000000 : ℝ) (250834800727/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16815/131072 : ℝ)) (992029985559/1000000000000 : ℝ) (496014992781/500000000000 : ℝ) (100333920289/200000000000 : ℝ) (250834800727/500000000000 : ℝ) (198587940557/250000000000 : ℝ) (158870352449/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1187_exp_lower
  have heNumeric : (410980729739/200000000000 : ℝ)/4 ≤ Real.exp (-17051274254097/25600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410980729739/200000000000 : ℝ)/4 ≤ Real.exp ((67259/524288 : ℝ)-(158870352449/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67259/524288 : ℝ) (16815/131072 : ℝ) (158870352449/200000000000 : ℝ) (410980729739/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1188; no trusted numerical premise.
theorem cover8_leaf1188_exp_radius : (997997473730422613/1000000000000000000 : ℝ) ≤ Real.exp ((-67261/4194304 : ℝ)/8) ∧ Real.exp ((-67261/4194304 : ℝ)/8) ≤ (498998736865211307/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67261/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1188_exp_lower : (460056783447094777/500000000000000000 : ℝ) ≤ Real.exp ((-21314092615969/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314092615969/32000000000000 : ℝ)/8) ≤ (184022713378837911/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314092615969/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1188_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513725915411/250000000000 : ℝ) ≤ 4*Real.exp (16815/131072 : ℝ)*Real.exp (-mu (radius 8 (67261/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (513725915411/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67261/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1188_exp_radius
  have hrNumeric : (246022906097/250000000000 : ℝ) ≤ Real.exp (-67261/4194304 : ℝ) ∧ Real.exp (-67261/4194304 : ℝ) ≤ (984091624389/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246022906097/250000000000 : ℝ) ≤ (radius 8 (67261/524288 : ℝ)) ∧ (radius 8 (67261/524288 : ℝ)) ≤ (984091624389/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67261/524288 : ℝ)) (246022906097/250000000000 : ℝ) (984091624389/1000000000000 : ℝ) (8883084319/50000000000 : ℝ) (88830843193/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67261/524288 : ℝ)) (246022906097/250000000000 : ℝ) (984091624389/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67261/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246022906097/250000000000 : ℝ) (984091624389/1000000000000 : ℝ) (496022906097/500000000000 : ℝ) (198409162439/200000000000 : ℝ) (248003480871/250000000000 : ℝ) (496006961743/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67261/524288 : ℝ)) 1 (496022906097/500000000000 : ℝ) (198409162439/200000000000 : ℝ) (248003480871/250000000000 : ℝ) (496006961743/500000000000 : ℝ) (992029867839/1000000000000 : ℝ) (992029867841/1000000000000 : ℝ) (99202986771/100000000000 : ℝ) (992029867713/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67261/524288 : ℝ)) 2 (992029867839/1000000000000 : ℝ) (992029867841/1000000000000 : ℝ) (99202986771/100000000000 : ℝ) (992029867713/1000000000000 : ℝ) (496014933887/500000000000 : ℝ) (992029867777/1000000000000 : ℝ) (496014933887/500000000000 : ℝ) (992029867777/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67261/524288 : ℝ)) 3 (496014933887/500000000000 : ℝ) (992029867777/1000000000000 : ℝ) (496014933887/500000000000 : ℝ) (992029867777/1000000000000 : ℝ) (496014933887/500000000000 : ℝ) (992029867777/1000000000000 : ℝ) (496014933887/500000000000 : ℝ) (992029867777/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67261/524288 : ℝ)) 4 (496014933887/500000000000 : ℝ) (992029867777/1000000000000 : ℝ) (496014933887/500000000000 : ℝ) (992029867777/1000000000000 : ℝ) (496014933887/500000000000 : ℝ) (992029867777/1000000000000 : ℝ) (496014933887/500000000000 : ℝ) (992029867777/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67261/524288 : ℝ)) 5 (496014933887/500000000000 : ℝ) (992029867777/1000000000000 : ℝ) (496014933887/500000000000 : ℝ) (992029867777/1000000000000 : ℝ) (496014933887/500000000000 : ℝ) (992029867777/1000000000000 : ℝ) (496014933887/500000000000 : ℝ) (992029867777/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67261/524288 : ℝ)) 6 (496014933887/500000000000 : ℝ) (992029867777/1000000000000 : ℝ) (496014933887/500000000000 : ℝ) (992029867777/1000000000000 : ℝ) (496014933887/500000000000 : ℝ) (992029867777/1000000000000 : ℝ) (496014933887/500000000000 : ℝ) (992029867777/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67261/524288 : ℝ)) 7 (496014933887/500000000000 : ℝ) (992029867777/1000000000000 : ℝ) (496014933887/500000000000 : ℝ) (992029867777/1000000000000 : ℝ) (496014933887/500000000000 : ℝ) (992029867777/1000000000000 : ℝ) (496014933887/500000000000 : ℝ) (992029867777/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67261/524288 : ℝ))) (8883084319/50000000000 : ℝ) (88830843193/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67261/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (8883084319/50000000000 : ℝ) (88830843193/500000000000 : ℝ) (58883084319/100000000000 : ℝ) (588830843193/1000000000000 : ℝ) (421499331411/1000000000000 : ℝ) (421499331419/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67261/524288 : ℝ))) 1 (58883084319/100000000000 : ℝ) (588830843193/1000000000000 : ℝ) (421499331411/1000000000000 : ℝ) (421499331419/1000000000000 : ℝ) (5051650873/10000000000 : ℝ) (252582543653/500000000000 : ℝ) (249094262639/500000000000 : ℝ) (99637705057/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67261/524288 : ℝ))) 2 (5051650873/10000000000 : ℝ) (252582543653/500000000000 : ℝ) (249094262639/500000000000 : ℝ) (99637705057/200000000000 : ℝ) (501676806289/1000000000000 : ℝ) (62709600787/125000000000 : ℝ) (125416169677/250000000000 : ℝ) (125416169679/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67261/524288 : ℝ))) 3 (501676806289/1000000000000 : ℝ) (62709600787/125000000000 : ℝ) (125416169677/250000000000 : ℝ) (125416169679/250000000000 : ℝ) (250835371249/500000000000 : ℝ) (250835371253/500000000000 : ℝ) (501670742461/1000000000000 : ℝ) (50167074247/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67261/524288 : ℝ))) 4 (250835371249/500000000000 : ℝ) (250835371253/500000000000 : ℝ) (501670742461/1000000000000 : ℝ) (50167074247/100000000000 : ℝ) (501670742479/1000000000000 : ℝ) (62708842811/125000000000 : ℝ) (501670742479/1000000000000 : ℝ) (62708842811/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67261/524288 : ℝ))) 5 (501670742479/1000000000000 : ℝ) (62708842811/125000000000 : ℝ) (501670742479/1000000000000 : ℝ) (62708842811/125000000000 : ℝ) (501670742479/1000000000000 : ℝ) (62708842811/125000000000 : ℝ) (501670742479/1000000000000 : ℝ) (62708842811/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67261/524288 : ℝ))) 6 (501670742479/1000000000000 : ℝ) (62708842811/125000000000 : ℝ) (501670742479/1000000000000 : ℝ) (62708842811/125000000000 : ℝ) (501670742479/1000000000000 : ℝ) (62708842811/125000000000 : ℝ) (501670742479/1000000000000 : ℝ) (62708842811/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67261/524288 : ℝ))) 7 (501670742479/1000000000000 : ℝ) (62708842811/125000000000 : ℝ) (501670742479/1000000000000 : ℝ) (62708842811/125000000000 : ℝ) (501670742479/1000000000000 : ℝ) (62708842811/125000000000 : ℝ) (501670742479/1000000000000 : ℝ) (62708842811/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67261/524288 : ℝ)) hmem 8 (496014933887/500000000000 : ℝ) (992029867777/1000000000000 : ℝ) (496014933887/500000000000 : ℝ) (992029867777/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67261/524288 : ℝ))) hcmem 8 (501670742479/1000000000000 : ℝ) (62708842811/125000000000 : ℝ) (501670742479/1000000000000 : ℝ) (62708842811/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67261/524288 : ℝ)) (496014933887/500000000000 : ℝ) (992029867777/1000000000000 : ℝ) (501670742479/1000000000000 : ℝ) (62708842811/125000000000 : ℝ) (397176831637/500000000000 : ℝ) (198588415823/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1188_exp_lower
  have heNumeric : (513725915411/250000000000 : ℝ)/4 ≤ Real.exp (-21314092615969/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513725915411/250000000000 : ℝ)/4 ≤ Real.exp ((16815/131072 : ℝ)-(198588415823/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16815/131072 : ℝ) (67261/524288 : ℝ) (198588415823/250000000000 : ℝ) (513725915411/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1189; no trusted numerical premise.
theorem cover8_leaf1189_exp_radius : (498998721993890301/500000000000000000 : ℝ) ≤ Real.exp ((-33631/2097152 : ℝ)/8) ∧ Real.exp ((-33631/2097152 : ℝ)/8) ≤ (997997443987780603/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33631/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1189_exp_lower : (184022713524230411/200000000000000000 : ℝ) ≤ Real.exp ((-17051273930967/25600000000000 : ℝ)/8) ∧ Real.exp ((-17051273930967/25600000000000 : ℝ)/8) ≤ (115014195952644007/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-17051273930967/25600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1189_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256862959329/125000000000 : ℝ) ≤ 4*Real.exp (67261/524288 : ℝ)*Real.exp (-mu (radius 8 (33631/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (256862959329/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33631/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1189_exp_radius
  have hrNumeric : (492045694881/500000000000 : ℝ) ≤ Real.exp (-33631/2097152 : ℝ) ∧ Real.exp (-33631/2097152 : ℝ) ≤ (984091389763/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492045694881/500000000000 : ℝ) ≤ (radius 8 (33631/262144 : ℝ)) ∧ (radius 8 (33631/262144 : ℝ)) ≤ (984091389763/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33631/262144 : ℝ)) (492045694881/500000000000 : ℝ) (984091389763/1000000000000 : ℝ) (177662985999/1000000000000 : ℝ) (88831493003/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33631/262144 : ℝ)) (492045694881/500000000000 : ℝ) (984091389763/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33631/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492045694881/500000000000 : ℝ) (984091389763/1000000000000 : ℝ) (992045694881/1000000000000 : ℝ) (496022847441/500000000000 : ℝ) (992013805227/1000000000000 : ℝ) (992013805229/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33631/262144 : ℝ)) 1 (992045694881/1000000000000 : ℝ) (496022847441/500000000000 : ℝ) (992013805227/1000000000000 : ℝ) (992013805229/1000000000000 : ℝ) (496014875027/500000000000 : ℝ) (124003718757/125000000000 : ℝ) (39681189997/40000000000 : ℝ) (124003718741/125000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33631/262144 : ℝ)) 2 (496014875027/500000000000 : ℝ) (124003718757/125000000000 : ℝ) (39681189997/40000000000 : ℝ) (124003718741/125000000000 : ℝ) (992029749989/1000000000000 : ℝ) (124003718749/125000000000 : ℝ) (992029749989/1000000000000 : ℝ) (124003718749/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33631/262144 : ℝ)) 3 (992029749989/1000000000000 : ℝ) (124003718749/125000000000 : ℝ) (992029749989/1000000000000 : ℝ) (124003718749/125000000000 : ℝ) (992029749989/1000000000000 : ℝ) (124003718749/125000000000 : ℝ) (992029749989/1000000000000 : ℝ) (124003718749/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33631/262144 : ℝ)) 4 (992029749989/1000000000000 : ℝ) (124003718749/125000000000 : ℝ) (992029749989/1000000000000 : ℝ) (124003718749/125000000000 : ℝ) (992029749989/1000000000000 : ℝ) (124003718749/125000000000 : ℝ) (992029749989/1000000000000 : ℝ) (124003718749/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33631/262144 : ℝ)) 5 (992029749989/1000000000000 : ℝ) (124003718749/125000000000 : ℝ) (992029749989/1000000000000 : ℝ) (124003718749/125000000000 : ℝ) (992029749989/1000000000000 : ℝ) (124003718749/125000000000 : ℝ) (992029749989/1000000000000 : ℝ) (124003718749/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33631/262144 : ℝ)) 6 (992029749989/1000000000000 : ℝ) (124003718749/125000000000 : ℝ) (992029749989/1000000000000 : ℝ) (124003718749/125000000000 : ℝ) (992029749989/1000000000000 : ℝ) (124003718749/125000000000 : ℝ) (992029749989/1000000000000 : ℝ) (124003718749/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33631/262144 : ℝ)) 7 (992029749989/1000000000000 : ℝ) (124003718749/125000000000 : ℝ) (992029749989/1000000000000 : ℝ) (124003718749/125000000000 : ℝ) (992029749989/1000000000000 : ℝ) (124003718749/125000000000 : ℝ) (992029749989/1000000000000 : ℝ) (124003718749/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33631/262144 : ℝ))) (177662985999/1000000000000 : ℝ) (88831493003/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33631/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177662985999/1000000000000 : ℝ) (88831493003/500000000000 : ℝ) (588831492999/1000000000000 : ℝ) (588831493003/1000000000000 : ℝ) (42150087307/100000000000 : ℝ) (421500873079/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33631/262144 : ℝ))) 1 (588831492999/1000000000000 : ℝ) (588831493003/1000000000000 : ℝ) (42150087307/100000000000 : ℝ) (421500873079/1000000000000 : ℝ) (252583091517/500000000000 : ℝ) (505166183041/1000000000000 : ℝ) (124547427811/250000000000 : ℝ) (124547427813/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33631/262144 : ℝ))) 2 (252583091517/500000000000 : ℝ) (505166183041/1000000000000 : ℝ) (124547427811/250000000000 : ℝ) (124547427813/250000000000 : ℝ) (501677947139/1000000000000 : ℝ) (501677947147/1000000000000 : ℝ) (5016658199/10000000000 : ℝ) (125416454977/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33631/262144 : ℝ))) 3 (501677947139/1000000000000 : ℝ) (501677947147/1000000000000 : ℝ) (5016658199/10000000000 : ℝ) (125416454977/250000000000 : ℝ) (501671883519/1000000000000 : ℝ) (62708985441/125000000000 : ℝ) (250835941741/500000000000 : ℝ) (501671883491/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33631/262144 : ℝ))) 4 (501671883519/1000000000000 : ℝ) (62708985441/125000000000 : ℝ) (250835941741/500000000000 : ℝ) (501671883491/1000000000000 : ℝ) (1003343767/2000000000 : ℝ) (50167188351/100000000000 : ℝ) (1003343767/2000000000 : ℝ) (50167188351/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33631/262144 : ℝ))) 5 (1003343767/2000000000 : ℝ) (50167188351/100000000000 : ℝ) (1003343767/2000000000 : ℝ) (50167188351/100000000000 : ℝ) (1003343767/2000000000 : ℝ) (50167188351/100000000000 : ℝ) (1003343767/2000000000 : ℝ) (50167188351/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33631/262144 : ℝ))) 6 (1003343767/2000000000 : ℝ) (50167188351/100000000000 : ℝ) (1003343767/2000000000 : ℝ) (50167188351/100000000000 : ℝ) (1003343767/2000000000 : ℝ) (50167188351/100000000000 : ℝ) (1003343767/2000000000 : ℝ) (50167188351/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33631/262144 : ℝ))) 7 (1003343767/2000000000 : ℝ) (50167188351/100000000000 : ℝ) (1003343767/2000000000 : ℝ) (50167188351/100000000000 : ℝ) (1003343767/2000000000 : ℝ) (50167188351/100000000000 : ℝ) (1003343767/2000000000 : ℝ) (50167188351/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33631/262144 : ℝ)) hmem 8 (992029749989/1000000000000 : ℝ) (124003718749/125000000000 : ℝ) (992029749989/1000000000000 : ℝ) (124003718749/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33631/262144 : ℝ))) hcmem 8 (1003343767/2000000000 : ℝ) (50167188351/100000000000 : ℝ) (1003343767/2000000000 : ℝ) (50167188351/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33631/262144 : ℝ)) (992029749989/1000000000000 : ℝ) (124003718749/125000000000 : ℝ) (1003343767/2000000000 : ℝ) (50167188351/100000000000 : ℝ) (7943555643/10000000000 : ℝ) (4964722277/6250000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1189_exp_lower
  have heNumeric : (256862959329/125000000000 : ℝ)/4 ≤ Real.exp (-17051273930967/25600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256862959329/125000000000 : ℝ)/4 ≤ Real.exp ((67261/524288 : ℝ)-(4964722277/6250000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67261/524288 : ℝ) (33631/262144 : ℝ) (4964722277/6250000000 : ℝ) (256862959329/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1190; no trusted numerical premise.
theorem cover8_leaf1190_exp_radius : (997997414245139477/1000000000000000000 : ℝ) ≤ Real.exp ((-67263/4194304 : ℝ)/8) ∧ Real.exp ((-67263/4194304 : ℝ)/8) ≤ (498998707122569739/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67263/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1190_exp_lower : (36804542734011993/40000000000000000 : ℝ) ≤ Real.exp ((-42628184421681/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628184421681/64000000000000 : ℝ)/8) ≤ (460056784175149913/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628184421681/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1190_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054903687659/1000000000000 : ℝ) ≤ 4*Real.exp (33631/262144 : ℝ)*Real.exp (-mu (radius 8 (67263/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054903687659/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67263/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1190_exp_radius
  have hrNumeric : (15376424299/15625000000 : ℝ) ≤ Real.exp (-67263/4194304 : ℝ) ∧ Real.exp (-67263/4194304 : ℝ) ≤ (984091155137/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (15376424299/15625000000 : ℝ) ≤ (radius 8 (67263/524288 : ℝ)) ∧ (radius 8 (67263/524288 : ℝ)) ≤ (984091155137/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67263/524288 : ℝ)) (15376424299/15625000000 : ℝ) (984091155137/1000000000000 : ℝ) (177664285609/1000000000000 : ℝ) (11104017851/62500000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67263/524288 : ℝ)) (15376424299/15625000000 : ℝ) (984091155137/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67263/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (15376424299/15625000000 : ℝ) (984091155137/1000000000000 : ℝ) (31001424299/31250000000 : ℝ) (992045577569/1000000000000 : ℝ) (99201368697/100000000000 : ℝ) (992013686971/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67263/524288 : ℝ)) 1 (31001424299/31250000000 : ℝ) (992045577569/1000000000000 : ℝ) (99201368697/100000000000 : ℝ) (992013686971/1000000000000 : ℝ) (992029632269/1000000000000 : ℝ) (99202963227/100000000000 : ℝ) (49601481607/50000000000 : ℝ) (496014816071/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67263/524288 : ℝ)) 2 (992029632269/1000000000000 : ℝ) (99202963227/100000000000 : ℝ) (49601481607/50000000000 : ℝ) (496014816071/500000000000 : ℝ) (248007408051/250000000000 : ℝ) (496014816103/500000000000 : ℝ) (248007408051/250000000000 : ℝ) (496014816103/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67263/524288 : ℝ)) 3 (248007408051/250000000000 : ℝ) (496014816103/500000000000 : ℝ) (248007408051/250000000000 : ℝ) (496014816103/500000000000 : ℝ) (248007408051/250000000000 : ℝ) (496014816103/500000000000 : ℝ) (248007408051/250000000000 : ℝ) (496014816103/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67263/524288 : ℝ)) 4 (248007408051/250000000000 : ℝ) (496014816103/500000000000 : ℝ) (248007408051/250000000000 : ℝ) (496014816103/500000000000 : ℝ) (248007408051/250000000000 : ℝ) (496014816103/500000000000 : ℝ) (248007408051/250000000000 : ℝ) (496014816103/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67263/524288 : ℝ)) 5 (248007408051/250000000000 : ℝ) (496014816103/500000000000 : ℝ) (248007408051/250000000000 : ℝ) (496014816103/500000000000 : ℝ) (248007408051/250000000000 : ℝ) (496014816103/500000000000 : ℝ) (248007408051/250000000000 : ℝ) (496014816103/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67263/524288 : ℝ)) 6 (248007408051/250000000000 : ℝ) (496014816103/500000000000 : ℝ) (248007408051/250000000000 : ℝ) (496014816103/500000000000 : ℝ) (248007408051/250000000000 : ℝ) (496014816103/500000000000 : ℝ) (248007408051/250000000000 : ℝ) (496014816103/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67263/524288 : ℝ)) 7 (248007408051/250000000000 : ℝ) (496014816103/500000000000 : ℝ) (248007408051/250000000000 : ℝ) (496014816103/500000000000 : ℝ) (248007408051/250000000000 : ℝ) (496014816103/500000000000 : ℝ) (248007408051/250000000000 : ℝ) (496014816103/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67263/524288 : ℝ))) (177664285609/1000000000000 : ℝ) (11104017851/62500000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67263/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177664285609/1000000000000 : ℝ) (11104017851/62500000000 : ℝ) (147208035701/250000000000 : ℝ) (73604017851/125000000000 : ℝ) (421502414713/1000000000000 : ℝ) (210751207361/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67263/524288 : ℝ))) 1 (147208035701/250000000000 : ℝ) (73604017851/125000000000 : ℝ) (421502414713/1000000000000 : ℝ) (210751207361/500000000000 : ℝ) (252583639379/500000000000 : ℝ) (101033455753/200000000000 : ℝ) (498190897199/1000000000000 : ℝ) (498190897207/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67263/524288 : ℝ))) 2 (252583639379/500000000000 : ℝ) (101033455753/200000000000 : ℝ) (498190897199/1000000000000 : ℝ) (498190897207/1000000000000 : ℝ) (250839543989/500000000000 : ℝ) (250839543993/500000000000 : ℝ) (12541674027/25000000000 : ℝ) (501666961089/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67263/524288 : ℝ))) 3 (250839543989/500000000000 : ℝ) (250839543993/500000000000 : ℝ) (12541674027/25000000000 : ℝ) (501666961089/1000000000000 : ℝ) (501673024529/1000000000000 : ℝ) (250836512269/500000000000 : ℝ) (125418256123/250000000000 : ℝ) (501673024501/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67263/524288 : ℝ))) 4 (501673024529/1000000000000 : ℝ) (250836512269/500000000000 : ℝ) (125418256123/250000000000 : ℝ) (501673024501/1000000000000 : ℝ) (50167302451/100000000000 : ℝ) (12541825613/25000000000 : ℝ) (50167302451/100000000000 : ℝ) (12541825613/25000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67263/524288 : ℝ))) 5 (50167302451/100000000000 : ℝ) (12541825613/25000000000 : ℝ) (50167302451/100000000000 : ℝ) (12541825613/25000000000 : ℝ) (50167302451/100000000000 : ℝ) (12541825613/25000000000 : ℝ) (50167302451/100000000000 : ℝ) (12541825613/25000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67263/524288 : ℝ))) 6 (50167302451/100000000000 : ℝ) (12541825613/25000000000 : ℝ) (50167302451/100000000000 : ℝ) (12541825613/25000000000 : ℝ) (50167302451/100000000000 : ℝ) (12541825613/25000000000 : ℝ) (50167302451/100000000000 : ℝ) (12541825613/25000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67263/524288 : ℝ))) 7 (50167302451/100000000000 : ℝ) (12541825613/25000000000 : ℝ) (50167302451/100000000000 : ℝ) (12541825613/25000000000 : ℝ) (50167302451/100000000000 : ℝ) (12541825613/25000000000 : ℝ) (50167302451/100000000000 : ℝ) (12541825613/25000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67263/524288 : ℝ)) hmem 8 (248007408051/250000000000 : ℝ) (496014816103/500000000000 : ℝ) (248007408051/250000000000 : ℝ) (496014816103/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67263/524288 : ℝ))) hcmem 8 (50167302451/100000000000 : ℝ) (12541825613/25000000000 : ℝ) (50167302451/100000000000 : ℝ) (12541825613/25000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67263/524288 : ℝ)) (248007408051/250000000000 : ℝ) (496014816103/500000000000 : ℝ) (50167302451/100000000000 : ℝ) (12541825613/25000000000 : ℝ) (79435746531/100000000000 : ℝ) (794357465329/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1190_exp_lower
  have heNumeric : (2054903687659/1000000000000 : ℝ)/4 ≤ Real.exp (-42628184421681/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054903687659/1000000000000 : ℝ)/4 ≤ Real.exp ((33631/262144 : ℝ)-(794357465329/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33631/262144 : ℝ) (67263/524288 : ℝ) (794357465329/1000000000000 : ℝ) (2054903687659/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1191; no trusted numerical premise.
theorem cover8_leaf1191_exp_radius : (997997384502499239/1000000000000000000 : ℝ) ≤ Real.exp ((-1051/65536 : ℝ)/8) ∧ Real.exp ((-1051/65536 : ℝ)/8) ≤ (24949934612562481/25000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1051/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1191_exp_lower : (460056784541333997/500000000000000000 : ℝ) ≤ Real.exp ((-17051273605661/25600000000000 : ℝ)/8) ∧ Real.exp ((-17051273605661/25600000000000 : ℝ)/8) ≤ (184022713816533599/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-17051273605661/25600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1191_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256862962593/125000000000 : ℝ) ≤ 4*Real.exp (67263/524288 : ℝ)*Real.exp (-mu (radius 8 (1051/8192 : ℝ))) ∧ (20549/10000 : ℝ) < (256862962593/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (1051/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1191_exp_radius
  have hrNumeric : (984090920511/1000000000000 : ℝ) ≤ Real.exp (-1051/65536 : ℝ) ∧ Real.exp (-1051/65536 : ℝ) ≤ (15376420633/15625000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984090920511/1000000000000 : ℝ) ≤ (radius 8 (1051/8192 : ℝ)) ∧ (radius 8 (1051/8192 : ℝ)) ≤ (15376420633/15625000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (1051/8192 : ℝ)) (984090920511/1000000000000 : ℝ) (15376420633/15625000000 : ℝ) (177665585203/1000000000000 : ℝ) (17766558521/100000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (1051/8192 : ℝ)) (984090920511/1000000000000 : ℝ) (15376420633/15625000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (1051/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984090920511/1000000000000 : ℝ) (15376420633/15625000000 : ℝ) (198409092051/200000000000 : ℝ) (31001420633/31250000000 : ℝ) (992013568713/1000000000000 : ℝ) (496006784357/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (1051/8192 : ℝ)) 1 (198409092051/200000000000 : ℝ) (31001420633/31250000000 : ℝ) (992013568713/1000000000000 : ℝ) (496006784357/500000000000 : ℝ) (248007378621/250000000000 : ℝ) (198405902897/200000000000 : ℝ) (198405902871/200000000000 : ℝ) (992029514357/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (1051/8192 : ℝ)) 2 (248007378621/250000000000 : ℝ) (198405902897/200000000000 : ℝ) (198405902871/200000000000 : ℝ) (992029514357/1000000000000 : ℝ) (992029514419/1000000000000 : ℝ) (992029514421/1000000000000 : ℝ) (992029514419/1000000000000 : ℝ) (992029514421/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (1051/8192 : ℝ)) 3 (992029514419/1000000000000 : ℝ) (992029514421/1000000000000 : ℝ) (992029514419/1000000000000 : ℝ) (992029514421/1000000000000 : ℝ) (992029514419/1000000000000 : ℝ) (992029514421/1000000000000 : ℝ) (992029514419/1000000000000 : ℝ) (992029514421/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (1051/8192 : ℝ)) 4 (992029514419/1000000000000 : ℝ) (992029514421/1000000000000 : ℝ) (992029514419/1000000000000 : ℝ) (992029514421/1000000000000 : ℝ) (992029514419/1000000000000 : ℝ) (992029514421/1000000000000 : ℝ) (992029514419/1000000000000 : ℝ) (992029514421/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (1051/8192 : ℝ)) 5 (992029514419/1000000000000 : ℝ) (992029514421/1000000000000 : ℝ) (992029514419/1000000000000 : ℝ) (992029514421/1000000000000 : ℝ) (992029514419/1000000000000 : ℝ) (992029514421/1000000000000 : ℝ) (992029514419/1000000000000 : ℝ) (992029514421/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (1051/8192 : ℝ)) 6 (992029514419/1000000000000 : ℝ) (992029514421/1000000000000 : ℝ) (992029514419/1000000000000 : ℝ) (992029514421/1000000000000 : ℝ) (992029514419/1000000000000 : ℝ) (992029514421/1000000000000 : ℝ) (992029514419/1000000000000 : ℝ) (992029514421/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (1051/8192 : ℝ)) 7 (992029514419/1000000000000 : ℝ) (992029514421/1000000000000 : ℝ) (992029514419/1000000000000 : ℝ) (992029514421/1000000000000 : ℝ) (992029514419/1000000000000 : ℝ) (992029514421/1000000000000 : ℝ) (992029514419/1000000000000 : ℝ) (992029514421/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (1051/8192 : ℝ))) (177665585203/1000000000000 : ℝ) (17766558521/100000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (1051/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177665585203/1000000000000 : ℝ) (17766558521/100000000000 : ℝ) (588832792601/1000000000000 : ℝ) (117766558521/200000000000 : ℝ) (421503956331/1000000000000 : ℝ) (21075197817/50000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (1051/8192 : ℝ))) 1 (588832792601/1000000000000 : ℝ) (117766558521/200000000000 : ℝ) (421503956331/1000000000000 : ℝ) (21075197817/50000000000 : ℝ) (252584187233/500000000000 : ℝ) (505168374473/1000000000000 : ℝ) (99638416627/200000000000 : ℝ) (498192083143/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (1051/8192 : ℝ))) 2 (252584187233/500000000000 : ℝ) (505168374473/1000000000000 : ℝ) (99638416627/200000000000 : ℝ) (498192083143/1000000000000 : ℝ) (313550143/625000000 : ℝ) (62710028601/125000000000 : ℝ) (125417025561/250000000000 : ℝ) (125417025563/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (1051/8192 : ℝ))) 3 (313550143/625000000 : ℝ) (62710028601/125000000000 : ℝ) (125417025561/250000000000 : ℝ) (125417025563/250000000000 : ℝ) (250837082761/500000000000 : ℝ) (50167416553/100000000000 : ℝ) (100334833097/200000000000 : ℝ) (250837082747/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (1051/8192 : ℝ))) 4 (250837082761/500000000000 : ℝ) (50167416553/100000000000 : ℝ) (100334833097/200000000000 : ℝ) (250837082747/500000000000 : ℝ) (501674165503/1000000000000 : ℝ) (62709270689/125000000000 : ℝ) (501674165503/1000000000000 : ℝ) (62709270689/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (1051/8192 : ℝ))) 5 (501674165503/1000000000000 : ℝ) (62709270689/125000000000 : ℝ) (501674165503/1000000000000 : ℝ) (62709270689/125000000000 : ℝ) (501674165503/1000000000000 : ℝ) (62709270689/125000000000 : ℝ) (501674165503/1000000000000 : ℝ) (62709270689/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (1051/8192 : ℝ))) 6 (501674165503/1000000000000 : ℝ) (62709270689/125000000000 : ℝ) (501674165503/1000000000000 : ℝ) (62709270689/125000000000 : ℝ) (501674165503/1000000000000 : ℝ) (62709270689/125000000000 : ℝ) (501674165503/1000000000000 : ℝ) (62709270689/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (1051/8192 : ℝ))) 7 (501674165503/1000000000000 : ℝ) (62709270689/125000000000 : ℝ) (501674165503/1000000000000 : ℝ) (62709270689/125000000000 : ℝ) (501674165503/1000000000000 : ℝ) (62709270689/125000000000 : ℝ) (501674165503/1000000000000 : ℝ) (62709270689/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (1051/8192 : ℝ)) hmem 8 (992029514419/1000000000000 : ℝ) (992029514421/1000000000000 : ℝ) (992029514419/1000000000000 : ℝ) (992029514421/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (1051/8192 : ℝ))) hcmem 8 (501674165503/1000000000000 : ℝ) (62709270689/125000000000 : ℝ) (501674165503/1000000000000 : ℝ) (62709270689/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (1051/8192 : ℝ)) (992029514419/1000000000000 : ℝ) (992029514421/1000000000000 : ℝ) (501674165503/1000000000000 : ℝ) (62709270689/125000000000 : ℝ) (794359366293/1000000000000 : ℝ) (79435936631/100000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1191_exp_lower
  have heNumeric : (256862962593/125000000000 : ℝ)/4 ≤ Real.exp (-17051273605661/25600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256862962593/125000000000 : ℝ)/4 ≤ Real.exp ((67263/524288 : ℝ)-(79435936631/100000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67263/524288 : ℝ) (1051/8192 : ℝ) (79435936631/100000000000 : ℝ) (256862962593/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1192; no trusted numerical premise.
theorem cover8_leaf1192_exp_radius : (997997354759859887/1000000000000000000 : ℝ) ≤ Real.exp ((-67265/4194304 : ℝ)/8) ∧ Real.exp ((-67265/4194304 : ℝ)/8) ≤ (62374834672491243/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67265/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1192_exp_lower : (920113569815956277/1000000000000000000 : ℝ) ≤ Real.exp ((-1332130737691/2000000000000 : ℝ)/8) ∧ Real.exp ((-1332130737691/2000000000000 : ℝ)/8) ≤ (460056784907978139/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1332130737691/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1192_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451856923/500000000000 : ℝ) ≤ 4*Real.exp (1051/8192 : ℝ)*Real.exp (-mu (radius 8 (67265/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451856923/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67265/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1192_exp_radius
  have hrNumeric : (196818137177/200000000000 : ℝ) ≤ Real.exp (-67265/4194304 : ℝ) ∧ Real.exp (-67265/4194304 : ℝ) ≤ (492045342943/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196818137177/200000000000 : ℝ) ≤ (radius 8 (67265/524288 : ℝ)) ∧ (radius 8 (67265/524288 : ℝ)) ≤ (492045342943/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67265/524288 : ℝ)) (196818137177/200000000000 : ℝ) (492045342943/500000000000 : ℝ) (88833442397/500000000000 : ℝ) (111041803/625000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67265/524288 : ℝ)) (196818137177/200000000000 : ℝ) (492045342943/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67265/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196818137177/200000000000 : ℝ) (492045342943/500000000000 : ℝ) (496022671471/500000000000 : ℝ) (992045342943/1000000000000 : ℝ) (198402690091/200000000000 : ℝ) (992013450457/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67265/524288 : ℝ)) 1 (496022671471/500000000000 : ℝ) (992045342943/1000000000000 : ℝ) (198402690091/200000000000 : ℝ) (992013450457/1000000000000 : ℝ) (496014698349/500000000000 : ℝ) (9920293967/10000000000 : ℝ) (99202939657/100000000000 : ℝ) (248007349143/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67265/524288 : ℝ)) 2 (496014698349/500000000000 : ℝ) (9920293967/10000000000 : ℝ) (99202939657/100000000000 : ℝ) (248007349143/250000000000 : ℝ) (496014698317/500000000000 : ℝ) (248007349159/250000000000 : ℝ) (992029396633/1000000000000 : ℝ) (248007349159/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67265/524288 : ℝ)) 3 (496014698317/500000000000 : ℝ) (248007349159/250000000000 : ℝ) (992029396633/1000000000000 : ℝ) (248007349159/250000000000 : ℝ) (992029396633/1000000000000 : ℝ) (248007349159/250000000000 : ℝ) (992029396633/1000000000000 : ℝ) (248007349159/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67265/524288 : ℝ)) 4 (992029396633/1000000000000 : ℝ) (248007349159/250000000000 : ℝ) (992029396633/1000000000000 : ℝ) (248007349159/250000000000 : ℝ) (992029396633/1000000000000 : ℝ) (248007349159/250000000000 : ℝ) (992029396633/1000000000000 : ℝ) (248007349159/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67265/524288 : ℝ)) 5 (992029396633/1000000000000 : ℝ) (248007349159/250000000000 : ℝ) (992029396633/1000000000000 : ℝ) (248007349159/250000000000 : ℝ) (992029396633/1000000000000 : ℝ) (248007349159/250000000000 : ℝ) (992029396633/1000000000000 : ℝ) (248007349159/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67265/524288 : ℝ)) 6 (992029396633/1000000000000 : ℝ) (248007349159/250000000000 : ℝ) (992029396633/1000000000000 : ℝ) (248007349159/250000000000 : ℝ) (992029396633/1000000000000 : ℝ) (248007349159/250000000000 : ℝ) (992029396633/1000000000000 : ℝ) (248007349159/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67265/524288 : ℝ)) 7 (992029396633/1000000000000 : ℝ) (248007349159/250000000000 : ℝ) (992029396633/1000000000000 : ℝ) (248007349159/250000000000 : ℝ) (992029396633/1000000000000 : ℝ) (248007349159/250000000000 : ℝ) (992029396633/1000000000000 : ℝ) (248007349159/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67265/524288 : ℝ))) (88833442397/500000000000 : ℝ) (111041803/625000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67265/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88833442397/500000000000 : ℝ) (111041803/625000000 : ℝ) (588833442397/1000000000000 : ℝ) (736041803/1250000000 : ℝ) (21075274897/50000000000 : ℝ) (105376374487/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67265/524288 : ℝ))) 1 (588833442397/1000000000000 : ℝ) (736041803/1250000000 : ℝ) (21075274897/50000000000 : ℝ) (105376374487/250000000000 : ℝ) (63146183771/125000000000 : ℝ) (252584735087/500000000000 : ℝ) (62274158633/125000000000 : ℝ) (498193269071/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67265/524288 : ℝ))) 2 (63146183771/125000000000 : ℝ) (252584735087/500000000000 : ℝ) (62274158633/125000000000 : ℝ) (498193269071/1000000000000 : ℝ) (31355085601/62500000000 : ℝ) (501681369623/1000000000000 : ℝ) (2508346217/5000000000 : ℝ) (31354327713/62500000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67265/524288 : ℝ))) 3 (31355085601/62500000000 : ℝ) (501681369623/1000000000000 : ℝ) (2508346217/5000000000 : ℝ) (31354327713/62500000000 : ℝ) (125418826627/250000000000 : ℝ) (125418826629/250000000000 : ℝ) (501675306471/1000000000000 : ℝ) (501675306479/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67265/524288 : ℝ))) 4 (125418826627/250000000000 : ℝ) (125418826629/250000000000 : ℝ) (501675306471/1000000000000 : ℝ) (501675306479/1000000000000 : ℝ) (501675306489/1000000000000 : ℝ) (250837653249/500000000000 : ℝ) (501675306489/1000000000000 : ℝ) (250837653249/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67265/524288 : ℝ))) 5 (501675306489/1000000000000 : ℝ) (250837653249/500000000000 : ℝ) (501675306489/1000000000000 : ℝ) (250837653249/500000000000 : ℝ) (501675306489/1000000000000 : ℝ) (250837653249/500000000000 : ℝ) (501675306489/1000000000000 : ℝ) (250837653249/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67265/524288 : ℝ))) 6 (501675306489/1000000000000 : ℝ) (250837653249/500000000000 : ℝ) (501675306489/1000000000000 : ℝ) (250837653249/500000000000 : ℝ) (501675306489/1000000000000 : ℝ) (250837653249/500000000000 : ℝ) (501675306489/1000000000000 : ℝ) (250837653249/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67265/524288 : ℝ))) 7 (501675306489/1000000000000 : ℝ) (250837653249/500000000000 : ℝ) (501675306489/1000000000000 : ℝ) (250837653249/500000000000 : ℝ) (501675306489/1000000000000 : ℝ) (250837653249/500000000000 : ℝ) (501675306489/1000000000000 : ℝ) (250837653249/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67265/524288 : ℝ)) hmem 8 (992029396633/1000000000000 : ℝ) (248007349159/250000000000 : ℝ) (992029396633/1000000000000 : ℝ) (248007349159/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67265/524288 : ℝ))) hcmem 8 (501675306489/1000000000000 : ℝ) (250837653249/500000000000 : ℝ) (501675306489/1000000000000 : ℝ) (250837653249/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67265/524288 : ℝ)) (992029396633/1000000000000 : ℝ) (248007349159/250000000000 : ℝ) (501675306489/1000000000000 : ℝ) (250837653249/500000000000 : ℝ) (158872253453/200000000000 : ℝ) (794361267283/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1192_exp_lower
  have heNumeric : (1027451856923/500000000000 : ℝ)/4 ≤ Real.exp (-1332130737691/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451856923/500000000000 : ℝ)/4 ≤ Real.exp ((1051/8192 : ℝ)-(794361267283/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (1051/8192 : ℝ) (67265/524288 : ℝ) (794361267283/1000000000000 : ℝ) (1027451856923/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1193; no trusted numerical premise.
theorem cover8_leaf1193_exp_radius : (498998662508610711/500000000000000000 : ℝ) ≤ Real.exp ((-33633/2097152 : ℝ)/8) ∧ Real.exp ((-33633/2097152 : ℝ)/8) ≤ (997997325017221423/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33633/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1193_exp_lower : (920113570552694987/1000000000000000000 : ℝ) ≤ Real.exp ((-85256366392303/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256366392303/128000000000000 : ℝ)/8) ≤ (230028392638173747/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256366392303/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1193_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054903727009/1000000000000 : ℝ) ≤ 4*Real.exp (67265/524288 : ℝ)*Real.exp (-mu (radius 8 (33633/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054903727009/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33633/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1193_exp_radius
  have hrNumeric : (49204522563/50000000000 : ℝ) ≤ Real.exp (-33633/2097152 : ℝ) ∧ Real.exp (-33633/2097152 : ℝ) ≤ (984090451261/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (49204522563/50000000000 : ℝ) ≤ (radius 8 (33633/262144 : ℝ)) ∧ (radius 8 (33633/262144 : ℝ)) ≤ (984090451261/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33633/262144 : ℝ)) (49204522563/50000000000 : ℝ) (984090451261/1000000000000 : ℝ) (11104261523/62500000000 : ℝ) (56853819/320000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33633/262144 : ℝ)) (49204522563/50000000000 : ℝ) (984090451261/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33633/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (49204522563/50000000000 : ℝ) (984090451261/1000000000000 : ℝ) (99204522563/100000000000 : ℝ) (992045225631/1000000000000 : ℝ) (496006666099/500000000000 : ℝ) (4960066661/5000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33633/262144 : ℝ)) 1 (99204522563/100000000000 : ℝ) (992045225631/1000000000000 : ℝ) (496006666099/500000000000 : ℝ) (4960066661/5000000000 : ℝ) (496014639457/500000000000 : ℝ) (248007319729/250000000000 : ℝ) (198405855757/200000000000 : ℝ) (248007319697/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33633/262144 : ℝ)) 2 (496014639457/500000000000 : ℝ) (248007319729/250000000000 : ℝ) (198405855757/200000000000 : ℝ) (248007319697/250000000000 : ℝ) (992029278849/1000000000000 : ℝ) (248007319713/250000000000 : ℝ) (992029278849/1000000000000 : ℝ) (248007319713/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33633/262144 : ℝ)) 3 (992029278849/1000000000000 : ℝ) (248007319713/250000000000 : ℝ) (992029278849/1000000000000 : ℝ) (248007319713/250000000000 : ℝ) (992029278849/1000000000000 : ℝ) (248007319713/250000000000 : ℝ) (992029278849/1000000000000 : ℝ) (248007319713/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33633/262144 : ℝ)) 4 (992029278849/1000000000000 : ℝ) (248007319713/250000000000 : ℝ) (992029278849/1000000000000 : ℝ) (248007319713/250000000000 : ℝ) (992029278849/1000000000000 : ℝ) (248007319713/250000000000 : ℝ) (992029278849/1000000000000 : ℝ) (248007319713/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33633/262144 : ℝ)) 5 (992029278849/1000000000000 : ℝ) (248007319713/250000000000 : ℝ) (992029278849/1000000000000 : ℝ) (248007319713/250000000000 : ℝ) (992029278849/1000000000000 : ℝ) (248007319713/250000000000 : ℝ) (992029278849/1000000000000 : ℝ) (248007319713/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33633/262144 : ℝ)) 6 (992029278849/1000000000000 : ℝ) (248007319713/250000000000 : ℝ) (992029278849/1000000000000 : ℝ) (248007319713/250000000000 : ℝ) (992029278849/1000000000000 : ℝ) (248007319713/250000000000 : ℝ) (992029278849/1000000000000 : ℝ) (248007319713/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33633/262144 : ℝ)) 7 (992029278849/1000000000000 : ℝ) (248007319713/250000000000 : ℝ) (992029278849/1000000000000 : ℝ) (248007319713/250000000000 : ℝ) (992029278849/1000000000000 : ℝ) (248007319713/250000000000 : ℝ) (992029278849/1000000000000 : ℝ) (248007319713/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33633/262144 : ℝ))) (11104261523/62500000000 : ℝ) (56853819/320000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33633/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (11104261523/62500000000 : ℝ) (56853819/320000000 : ℝ) (73604261523/125000000000 : ℝ) (147208523047/250000000000 : ℝ) (421507039523/1000000000000 : ℝ) (105376759883/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33633/262144 : ℝ))) 1 (73604261523/125000000000 : ℝ) (147208523047/250000000000 : ℝ) (421507039523/1000000000000 : ℝ) (105376759883/250000000000 : ℝ) (505170565853/1000000000000 : ℝ) (25258528293/50000000000 : ℝ) (498194454973/1000000000000 : ℝ) (498194454981/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33633/262144 : ℝ))) 2 (505170565853/1000000000000 : ℝ) (25258528293/50000000000 : ℝ) (498194454973/1000000000000 : ℝ) (498194454981/1000000000000 : ℝ) (501682510413/1000000000000 : ℝ) (501682510421/1000000000000 : ℝ) (501670384539/1000000000000 : ℝ) (501670384547/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33633/262144 : ℝ))) 3 (501682510413/1000000000000 : ℝ) (501682510421/1000000000000 : ℝ) (501670384539/1000000000000 : ℝ) (501670384547/1000000000000 : ℝ) (125419111869/250000000000 : ℝ) (125419111871/250000000000 : ℝ) (501676447439/1000000000000 : ℝ) (62709555931/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33633/262144 : ℝ))) 4 (125419111869/250000000000 : ℝ) (125419111871/250000000000 : ℝ) (501676447439/1000000000000 : ℝ) (62709555931/125000000000 : ℝ) (501676447457/1000000000000 : ℝ) (250838223733/500000000000 : ℝ) (501676447457/1000000000000 : ℝ) (250838223733/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33633/262144 : ℝ))) 5 (501676447457/1000000000000 : ℝ) (250838223733/500000000000 : ℝ) (501676447457/1000000000000 : ℝ) (250838223733/500000000000 : ℝ) (501676447457/1000000000000 : ℝ) (250838223733/500000000000 : ℝ) (501676447457/1000000000000 : ℝ) (250838223733/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33633/262144 : ℝ))) 6 (501676447457/1000000000000 : ℝ) (250838223733/500000000000 : ℝ) (501676447457/1000000000000 : ℝ) (250838223733/500000000000 : ℝ) (501676447457/1000000000000 : ℝ) (250838223733/500000000000 : ℝ) (501676447457/1000000000000 : ℝ) (250838223733/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33633/262144 : ℝ))) 7 (501676447457/1000000000000 : ℝ) (250838223733/500000000000 : ℝ) (501676447457/1000000000000 : ℝ) (250838223733/500000000000 : ℝ) (501676447457/1000000000000 : ℝ) (250838223733/500000000000 : ℝ) (501676447457/1000000000000 : ℝ) (250838223733/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33633/262144 : ℝ)) hmem 8 (992029278849/1000000000000 : ℝ) (248007319713/250000000000 : ℝ) (992029278849/1000000000000 : ℝ) (248007319713/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33633/262144 : ℝ))) hcmem 8 (501676447457/1000000000000 : ℝ) (250838223733/500000000000 : ℝ) (501676447457/1000000000000 : ℝ) (250838223733/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33633/262144 : ℝ)) (992029278849/1000000000000 : ℝ) (248007319713/250000000000 : ℝ) (501676447457/1000000000000 : ℝ) (250838223733/500000000000 : ℝ) (794363168209/1000000000000 : ℝ) (397181584113/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1193_exp_lower
  have heNumeric : (2054903727009/1000000000000 : ℝ)/4 ≤ Real.exp (-85256366392303/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054903727009/1000000000000 : ℝ)/4 ≤ Real.exp ((67265/524288 : ℝ)-(397181584113/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67265/524288 : ℝ) (33633/262144 : ℝ) (397181584113/500000000000 : ℝ) (2054903727009/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1194; no trusted numerical premise.
theorem cover8_leaf1194_exp_radius : (997997295274583843/1000000000000000000 : ℝ) ≤ Real.exp ((-67267/4194304 : ℝ)/8) ∧ Real.exp ((-67267/4194304 : ℝ)/8) ≤ (249499323818645961/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67267/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1194_exp_lower : (36804542851618753/40000000000000000 : ℝ) ≤ Real.exp ((-8525636557123/12800000000000 : ℝ)/8) ∧ Real.exp ((-8525636557123/12800000000000 : ℝ)/8) ≤ (460056785645234413/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8525636557123/12800000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1194_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (205490374019/100000000000 : ℝ) ≤ 4*Real.exp (33633/262144 : ℝ)*Real.exp (-mu (radius 8 (67267/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (205490374019/100000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67267/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1194_exp_radius
  have hrNumeric : (492045108317/500000000000 : ℝ) ≤ Real.exp (-67267/4194304 : ℝ) ∧ Real.exp (-67267/4194304 : ℝ) ≤ (196818043327/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492045108317/500000000000 : ℝ) ≤ (radius 8 (67267/524288 : ℝ)) ∧ (radius 8 (67267/524288 : ℝ)) ≤ (196818043327/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67267/524288 : ℝ)) (492045108317/500000000000 : ℝ) (196818043327/200000000000 : ℝ) (177669483939/1000000000000 : ℝ) (35533896789/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67267/524288 : ℝ)) (492045108317/500000000000 : ℝ) (196818043327/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67267/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492045108317/500000000000 : ℝ) (196818043327/200000000000 : ℝ) (992045108317/1000000000000 : ℝ) (496022554159/500000000000 : ℝ) (992013213941/1000000000000 : ℝ) (496006606971/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67267/524288 : ℝ)) 1 (992045108317/1000000000000 : ℝ) (496022554159/500000000000 : ℝ) (992013213941/1000000000000 : ℝ) (496006606971/500000000000 : ℝ) (992029161129/1000000000000 : ℝ) (99202916113/100000000000 : ℝ) (992029161/1000000000 : ℝ) (496014580501/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67267/524288 : ℝ)) 2 (992029161129/1000000000000 : ℝ) (99202916113/100000000000 : ℝ) (992029161/1000000000 : ℝ) (496014580501/500000000000 : ℝ) (124003645133/125000000000 : ℝ) (496014580533/500000000000 : ℝ) (124003645133/125000000000 : ℝ) (496014580533/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67267/524288 : ℝ)) 3 (124003645133/125000000000 : ℝ) (496014580533/500000000000 : ℝ) (124003645133/125000000000 : ℝ) (496014580533/500000000000 : ℝ) (124003645133/125000000000 : ℝ) (496014580533/500000000000 : ℝ) (124003645133/125000000000 : ℝ) (496014580533/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67267/524288 : ℝ)) 4 (124003645133/125000000000 : ℝ) (496014580533/500000000000 : ℝ) (124003645133/125000000000 : ℝ) (496014580533/500000000000 : ℝ) (124003645133/125000000000 : ℝ) (496014580533/500000000000 : ℝ) (124003645133/125000000000 : ℝ) (496014580533/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67267/524288 : ℝ)) 5 (124003645133/125000000000 : ℝ) (496014580533/500000000000 : ℝ) (124003645133/125000000000 : ℝ) (496014580533/500000000000 : ℝ) (124003645133/125000000000 : ℝ) (496014580533/500000000000 : ℝ) (124003645133/125000000000 : ℝ) (496014580533/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67267/524288 : ℝ)) 6 (124003645133/125000000000 : ℝ) (496014580533/500000000000 : ℝ) (124003645133/125000000000 : ℝ) (496014580533/500000000000 : ℝ) (124003645133/125000000000 : ℝ) (496014580533/500000000000 : ℝ) (124003645133/125000000000 : ℝ) (496014580533/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67267/524288 : ℝ)) 7 (124003645133/125000000000 : ℝ) (496014580533/500000000000 : ℝ) (124003645133/125000000000 : ℝ) (496014580533/500000000000 : ℝ) (124003645133/125000000000 : ℝ) (496014580533/500000000000 : ℝ) (124003645133/125000000000 : ℝ) (496014580533/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67267/524288 : ℝ))) (177669483939/1000000000000 : ℝ) (35533896789/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67267/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177669483939/1000000000000 : ℝ) (35533896789/200000000000 : ℝ) (588834741969/1000000000000 : ℝ) (588834741973/1000000000000 : ℝ) (421508581097/1000000000000 : ℝ) (84301716221/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67267/524288 : ℝ))) 1 (588834741969/1000000000000 : ℝ) (588834741973/1000000000000 : ℝ) (421508581097/1000000000000 : ℝ) (84301716221/200000000000 : ℝ) (505171661533/1000000000000 : ℝ) (505171661539/1000000000000 : ℝ) (124548910219/250000000000 : ℝ) (498195640883/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67267/524288 : ℝ))) 2 (505171661533/1000000000000 : ℝ) (505171661539/1000000000000 : ℝ) (124548910219/250000000000 : ℝ) (498195640883/1000000000000 : ℝ) (125420912801/250000000000 : ℝ) (501683651211/1000000000000 : ℝ) (501671525671/1000000000000 : ℝ) (501671525679/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67267/524288 : ℝ))) 3 (125420912801/250000000000 : ℝ) (501683651211/1000000000000 : ℝ) (501671525671/1000000000000 : ℝ) (501671525679/1000000000000 : ℝ) (501677588437/1000000000000 : ℝ) (100335517689/200000000000 : ℝ) (1254193971/2500000000 : ℝ) (501677588409/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67267/524288 : ℝ))) 4 (501677588437/1000000000000 : ℝ) (100335517689/200000000000 : ℝ) (1254193971/2500000000 : ℝ) (501677588409/1000000000000 : ℝ) (250838794209/500000000000 : ℝ) (501677588427/1000000000000 : ℝ) (250838794209/500000000000 : ℝ) (501677588427/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67267/524288 : ℝ))) 5 (250838794209/500000000000 : ℝ) (501677588427/1000000000000 : ℝ) (250838794209/500000000000 : ℝ) (501677588427/1000000000000 : ℝ) (250838794209/500000000000 : ℝ) (501677588427/1000000000000 : ℝ) (250838794209/500000000000 : ℝ) (501677588427/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67267/524288 : ℝ))) 6 (250838794209/500000000000 : ℝ) (501677588427/1000000000000 : ℝ) (250838794209/500000000000 : ℝ) (501677588427/1000000000000 : ℝ) (250838794209/500000000000 : ℝ) (501677588427/1000000000000 : ℝ) (250838794209/500000000000 : ℝ) (501677588427/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67267/524288 : ℝ))) 7 (250838794209/500000000000 : ℝ) (501677588427/1000000000000 : ℝ) (250838794209/500000000000 : ℝ) (501677588427/1000000000000 : ℝ) (250838794209/500000000000 : ℝ) (501677588427/1000000000000 : ℝ) (250838794209/500000000000 : ℝ) (501677588427/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67267/524288 : ℝ)) hmem 8 (124003645133/125000000000 : ℝ) (496014580533/500000000000 : ℝ) (124003645133/125000000000 : ℝ) (496014580533/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67267/524288 : ℝ))) hcmem 8 (250838794209/500000000000 : ℝ) (501677588427/1000000000000 : ℝ) (250838794209/500000000000 : ℝ) (501677588427/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67267/524288 : ℝ)) (124003645133/125000000000 : ℝ) (496014580533/500000000000 : ℝ) (250838794209/500000000000 : ℝ) (501677588427/1000000000000 : ℝ) (794365069143/1000000000000 : ℝ) (19859126729/25000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1194_exp_lower
  have heNumeric : (205490374019/100000000000 : ℝ)/4 ≤ Real.exp (-8525636557123/12800000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (205490374019/100000000000 : ℝ)/4 ≤ Real.exp ((33633/262144 : ℝ)-(19859126729/25000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33633/262144 : ℝ) (67267/524288 : ℝ) (19859126729/25000000000 : ℝ) (205490374019/100000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1195; no trusted numerical premise.
theorem cover8_leaf1195_exp_radius : (19959945310638943/20000000000000000 : ℝ) ≤ Real.exp ((-16817/1048576 : ℝ)/8) ∧ Real.exp ((-16817/1048576 : ℝ)/8) ≤ (997997265531947151/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16817/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1195_exp_lower : (230028393007750751/250000000000000000 : ℝ) ≤ Real.exp ((-17051272949417/25600000000000 : ℝ)/8) ∧ Real.exp ((-17051272949417/25600000000000 : ℝ)/8) ≤ (184022714406200601/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-17051272949417/25600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1195_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054903753421/1000000000000 : ℝ) ≤ 4*Real.exp (67267/524288 : ℝ)*Real.exp (-mu (radius 8 (16817/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054903753421/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16817/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1195_exp_radius
  have hrNumeric : (984089982009/1000000000000 : ℝ) ≤ Real.exp (-16817/1048576 : ℝ) ∧ Real.exp (-16817/1048576 : ℝ) ≤ (98408998201/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984089982009/1000000000000 : ℝ) ≤ (radius 8 (16817/131072 : ℝ)) ∧ (radius 8 (16817/131072 : ℝ)) ≤ (98408998201/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16817/131072 : ℝ)) (984089982009/1000000000000 : ℝ) (98408998201/100000000000 : ℝ) (88835391747/500000000000 : ℝ) (177670783501/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16817/131072 : ℝ)) (984089982009/1000000000000 : ℝ) (98408998201/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16817/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984089982009/1000000000000 : ℝ) (98408998201/100000000000 : ℝ) (248011247751/250000000000 : ℝ) (198408998201/200000000000 : ℝ) (248003273921/250000000000 : ℝ) (198402619137/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16817/131072 : ℝ)) 1 (248011247751/250000000000 : ℝ) (198408998201/200000000000 : ℝ) (248003273921/250000000000 : ℝ) (198402619137/200000000000 : ℝ) (62001815209/62500000000 : ℝ) (198405808669/200000000000 : ℝ) (198405808643/200000000000 : ℝ) (992029043217/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16817/131072 : ℝ)) 2 (62001815209/62500000000 : ℝ) (198405808669/200000000000 : ℝ) (198405808643/200000000000 : ℝ) (992029043217/1000000000000 : ℝ) (992029043279/1000000000000 : ℝ) (992029043281/1000000000000 : ℝ) (992029043279/1000000000000 : ℝ) (992029043281/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16817/131072 : ℝ)) 3 (992029043279/1000000000000 : ℝ) (992029043281/1000000000000 : ℝ) (992029043279/1000000000000 : ℝ) (992029043281/1000000000000 : ℝ) (992029043279/1000000000000 : ℝ) (992029043281/1000000000000 : ℝ) (992029043279/1000000000000 : ℝ) (992029043281/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16817/131072 : ℝ)) 4 (992029043279/1000000000000 : ℝ) (992029043281/1000000000000 : ℝ) (992029043279/1000000000000 : ℝ) (992029043281/1000000000000 : ℝ) (992029043279/1000000000000 : ℝ) (992029043281/1000000000000 : ℝ) (992029043279/1000000000000 : ℝ) (992029043281/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16817/131072 : ℝ)) 5 (992029043279/1000000000000 : ℝ) (992029043281/1000000000000 : ℝ) (992029043279/1000000000000 : ℝ) (992029043281/1000000000000 : ℝ) (992029043279/1000000000000 : ℝ) (992029043281/1000000000000 : ℝ) (992029043279/1000000000000 : ℝ) (992029043281/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16817/131072 : ℝ)) 6 (992029043279/1000000000000 : ℝ) (992029043281/1000000000000 : ℝ) (992029043279/1000000000000 : ℝ) (992029043281/1000000000000 : ℝ) (992029043279/1000000000000 : ℝ) (992029043281/1000000000000 : ℝ) (992029043279/1000000000000 : ℝ) (992029043281/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16817/131072 : ℝ)) 7 (992029043279/1000000000000 : ℝ) (992029043281/1000000000000 : ℝ) (992029043279/1000000000000 : ℝ) (992029043281/1000000000000 : ℝ) (992029043279/1000000000000 : ℝ) (992029043281/1000000000000 : ℝ) (992029043279/1000000000000 : ℝ) (992029043281/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16817/131072 : ℝ))) (88835391747/500000000000 : ℝ) (177670783501/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16817/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88835391747/500000000000 : ℝ) (177670783501/1000000000000 : ℝ) (588835391747/1000000000000 : ℝ) (588835391751/1000000000000 : ℝ) (421510122647/1000000000000 : ℝ) (13172191333/31250000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16817/131072 : ℝ))) 1 (588835391747/1000000000000 : ℝ) (588835391751/1000000000000 : ℝ) (421510122647/1000000000000 : ℝ) (13172191333/31250000000 : ℝ) (505172757197/1000000000000 : ℝ) (126293189301/250000000000 : ℝ) (12454920669/25000000000 : ℝ) (31137301673/62500000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16817/131072 : ℝ))) 2 (505172757197/1000000000000 : ℝ) (126293189301/250000000000 : ℝ) (12454920669/25000000000 : ℝ) (31137301673/62500000000 : ℝ) (250842395989/500000000000 : ℝ) (250842395993/500000000000 : ℝ) (250836333393/500000000000 : ℝ) (100334533359/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16817/131072 : ℝ))) 3 (250842395989/500000000000 : ℝ) (250842395993/500000000000 : ℝ) (250836333393/500000000000 : ℝ) (100334533359/200000000000 : ℝ) (250839364691/500000000000 : ℝ) (501678729391/1000000000000 : ℝ) (100335745869/200000000000 : ℝ) (250839364677/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16817/131072 : ℝ))) 4 (250839364691/500000000000 : ℝ) (501678729391/1000000000000 : ℝ) (100335745869/200000000000 : ℝ) (250839364677/500000000000 : ℝ) (501678729363/1000000000000 : ℝ) (501678729373/1000000000000 : ℝ) (501678729363/1000000000000 : ℝ) (501678729373/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16817/131072 : ℝ))) 5 (501678729363/1000000000000 : ℝ) (501678729373/1000000000000 : ℝ) (501678729363/1000000000000 : ℝ) (501678729373/1000000000000 : ℝ) (501678729363/1000000000000 : ℝ) (501678729373/1000000000000 : ℝ) (501678729363/1000000000000 : ℝ) (501678729373/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16817/131072 : ℝ))) 6 (501678729363/1000000000000 : ℝ) (501678729373/1000000000000 : ℝ) (501678729363/1000000000000 : ℝ) (501678729373/1000000000000 : ℝ) (501678729363/1000000000000 : ℝ) (501678729373/1000000000000 : ℝ) (501678729363/1000000000000 : ℝ) (501678729373/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16817/131072 : ℝ))) 7 (501678729363/1000000000000 : ℝ) (501678729373/1000000000000 : ℝ) (501678729363/1000000000000 : ℝ) (501678729373/1000000000000 : ℝ) (501678729363/1000000000000 : ℝ) (501678729373/1000000000000 : ℝ) (501678729363/1000000000000 : ℝ) (501678729373/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16817/131072 : ℝ)) hmem 8 (992029043279/1000000000000 : ℝ) (992029043281/1000000000000 : ℝ) (992029043279/1000000000000 : ℝ) (992029043281/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16817/131072 : ℝ))) hcmem 8 (501678729363/1000000000000 : ℝ) (501678729373/1000000000000 : ℝ) (501678729363/1000000000000 : ℝ) (501678729373/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16817/131072 : ℝ)) (992029043279/1000000000000 : ℝ) (992029043281/1000000000000 : ℝ) (501678729363/1000000000000 : ℝ) (501678729373/1000000000000 : ℝ) (794366970051/1000000000000 : ℝ) (79436697007/100000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1195_exp_lower
  have heNumeric : (2054903753421/1000000000000 : ℝ)/4 ≤ Real.exp (-17051272949417/25600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054903753421/1000000000000 : ℝ)/4 ≤ Real.exp ((67267/524288 : ℝ)-(79436697007/100000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67267/524288 : ℝ) (16817/131072 : ℝ) (79436697007/100000000000 : ℝ) (2054903753421/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1196; no trusted numerical premise.
theorem cover8_leaf1196_exp_radius : (62374827236831959/62500000000000000 : ℝ) ≤ Real.exp ((-67269/4194304 : ℝ)/8) ∧ Real.exp ((-67269/4194304 : ℝ)/8) ≤ (199599447157862269/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67269/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1196_exp_lower : (92011357277418251/100000000000000000 : ℝ) ≤ Real.exp ((-21314090979999/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314090979999/32000000000000 : ℝ)/8) ≤ (920113572774182511/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314090979999/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1196_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054903766699/1000000000000 : ℝ) ≤ 4*Real.exp (16817/131072 : ℝ)*Real.exp (-mu (radius 8 (67269/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054903766699/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67269/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1196_exp_radius
  have hrNumeric : (123011218423/125000000000 : ℝ) ≤ Real.exp (-67269/4194304 : ℝ) ∧ Real.exp (-67269/4194304 : ℝ) ≤ (196817949477/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (123011218423/125000000000 : ℝ) ≤ (radius 8 (67269/524288 : ℝ)) ∧ (radius 8 (67269/524288 : ℝ)) ≤ (196817949477/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67269/524288 : ℝ)) (123011218423/125000000000 : ℝ) (196817949477/200000000000 : ℝ) (177672083039/1000000000000 : ℝ) (88836041523/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67269/524288 : ℝ)) (123011218423/125000000000 : ℝ) (196817949477/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67269/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (123011218423/125000000000 : ℝ) (196817949477/200000000000 : ℝ) (248011218423/250000000000 : ℝ) (992044873693/1000000000000 : ℝ) (992012977427/1000000000000 : ℝ) (248003244357/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67269/524288 : ℝ)) 1 (248011218423/250000000000 : ℝ) (992044873693/1000000000000 : ℝ) (992012977427/1000000000000 : ℝ) (248003244357/250000000000 : ℝ) (992028925559/1000000000000 : ℝ) (992028925561/1000000000000 : ℝ) (992028925431/1000000000000 : ℝ) (992028925433/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67269/524288 : ℝ)) 2 (992028925559/1000000000000 : ℝ) (992028925561/1000000000000 : ℝ) (992028925431/1000000000000 : ℝ) (992028925433/1000000000000 : ℝ) (198405785099/200000000000 : ℝ) (992028925497/1000000000000 : ℝ) (496014462747/500000000000 : ℝ) (992028925497/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67269/524288 : ℝ)) 3 (198405785099/200000000000 : ℝ) (992028925497/1000000000000 : ℝ) (496014462747/500000000000 : ℝ) (992028925497/1000000000000 : ℝ) (496014462747/500000000000 : ℝ) (992028925497/1000000000000 : ℝ) (496014462747/500000000000 : ℝ) (992028925497/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67269/524288 : ℝ)) 4 (496014462747/500000000000 : ℝ) (992028925497/1000000000000 : ℝ) (496014462747/500000000000 : ℝ) (992028925497/1000000000000 : ℝ) (496014462747/500000000000 : ℝ) (992028925497/1000000000000 : ℝ) (496014462747/500000000000 : ℝ) (992028925497/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67269/524288 : ℝ)) 5 (496014462747/500000000000 : ℝ) (992028925497/1000000000000 : ℝ) (496014462747/500000000000 : ℝ) (992028925497/1000000000000 : ℝ) (496014462747/500000000000 : ℝ) (992028925497/1000000000000 : ℝ) (496014462747/500000000000 : ℝ) (992028925497/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67269/524288 : ℝ)) 6 (496014462747/500000000000 : ℝ) (992028925497/1000000000000 : ℝ) (496014462747/500000000000 : ℝ) (992028925497/1000000000000 : ℝ) (496014462747/500000000000 : ℝ) (992028925497/1000000000000 : ℝ) (496014462747/500000000000 : ℝ) (992028925497/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67269/524288 : ℝ)) 7 (496014462747/500000000000 : ℝ) (992028925497/1000000000000 : ℝ) (496014462747/500000000000 : ℝ) (992028925497/1000000000000 : ℝ) (496014462747/500000000000 : ℝ) (992028925497/1000000000000 : ℝ) (496014462747/500000000000 : ℝ) (992028925497/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67269/524288 : ℝ))) (177672083039/1000000000000 : ℝ) (88836041523/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67269/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177672083039/1000000000000 : ℝ) (88836041523/500000000000 : ℝ) (588836041519/1000000000000 : ℝ) (588836041523/1000000000000 : ℝ) (421511664179/1000000000000 : ℝ) (105377916047/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67269/524288 : ℝ))) 1 (588836041519/1000000000000 : ℝ) (588836041523/1000000000000 : ℝ) (421511664179/1000000000000 : ℝ) (105377916047/250000000000 : ℝ) (505173852849/1000000000000 : ℝ) (63146731607/125000000000 : ℝ) (49819801263/100000000000 : ℝ) (249099006319/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67269/524288 : ℝ))) 2 (505173852849/1000000000000 : ℝ) (63146731607/125000000000 : ℝ) (49819801263/100000000000 : ℝ) (249099006319/500000000000 : ℝ) (501685932739/1000000000000 : ℝ) (501685932747/1000000000000 : ℝ) (501673807889/1000000000000 : ℝ) (501673807897/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67269/524288 : ℝ))) 3 (501685932739/1000000000000 : ℝ) (501685932747/1000000000000 : ℝ) (501673807889/1000000000000 : ℝ) (501673807897/1000000000000 : ℝ) (250839935157/500000000000 : ℝ) (250839935161/500000000000 : ℝ) (501679870277/1000000000000 : ℝ) (250839935143/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67269/524288 : ℝ))) 4 (250839935157/500000000000 : ℝ) (250839935161/500000000000 : ℝ) (501679870277/1000000000000 : ℝ) (250839935143/500000000000 : ℝ) (100335974059/200000000000 : ℝ) (15677495947/31250000000 : ℝ) (100335974059/200000000000 : ℝ) (15677495947/31250000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67269/524288 : ℝ))) 5 (100335974059/200000000000 : ℝ) (15677495947/31250000000 : ℝ) (100335974059/200000000000 : ℝ) (15677495947/31250000000 : ℝ) (100335974059/200000000000 : ℝ) (15677495947/31250000000 : ℝ) (100335974059/200000000000 : ℝ) (15677495947/31250000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67269/524288 : ℝ))) 6 (100335974059/200000000000 : ℝ) (15677495947/31250000000 : ℝ) (100335974059/200000000000 : ℝ) (15677495947/31250000000 : ℝ) (100335974059/200000000000 : ℝ) (15677495947/31250000000 : ℝ) (100335974059/200000000000 : ℝ) (15677495947/31250000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67269/524288 : ℝ))) 7 (100335974059/200000000000 : ℝ) (15677495947/31250000000 : ℝ) (100335974059/200000000000 : ℝ) (15677495947/31250000000 : ℝ) (100335974059/200000000000 : ℝ) (15677495947/31250000000 : ℝ) (100335974059/200000000000 : ℝ) (15677495947/31250000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67269/524288 : ℝ)) hmem 8 (496014462747/500000000000 : ℝ) (992028925497/1000000000000 : ℝ) (496014462747/500000000000 : ℝ) (992028925497/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67269/524288 : ℝ))) hcmem 8 (100335974059/200000000000 : ℝ) (15677495947/31250000000 : ℝ) (100335974059/200000000000 : ℝ) (15677495947/31250000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67269/524288 : ℝ)) (496014462747/500000000000 : ℝ) (992028925497/1000000000000 : ℝ) (100335974059/200000000000 : ℝ) (15677495947/31250000000 : ℝ) (794368870939/1000000000000 : ℝ) (794368870957/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1196_exp_lower
  have heNumeric : (2054903766699/1000000000000 : ℝ)/4 ≤ Real.exp (-21314090979999/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054903766699/1000000000000 : ℝ)/4 ≤ Real.exp ((16817/131072 : ℝ)-(794368870957/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16817/131072 : ℝ) (67269/524288 : ℝ) (794368870957/1000000000000 : ℝ) (2054903766699/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1197; no trusted numerical premise.
theorem cover8_leaf1197_exp_radius : (124749650755834553/125000000000000000 : ℝ) ≤ Real.exp ((-33635/2097152 : ℝ)/8) ∧ Real.exp ((-33635/2097152 : ℝ)/8) ≤ (39919888241867057/40000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33635/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1197_exp_lower : (920113573519432273/1000000000000000000 : ℝ) ≤ Real.exp ((-85256363090603/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256363090603/128000000000000 : ℝ)/8) ≤ (460056786759716137/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256363090603/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1197_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451890007/500000000000 : ℝ) ≤ 4*Real.exp (67269/524288 : ℝ)*Real.exp (-mu (radius 8 (33635/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451890007/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33635/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1197_exp_radius
  have hrNumeric : (984089512759/1000000000000 : ℝ) ≤ Real.exp (-33635/2097152 : ℝ) ∧ Real.exp (-33635/2097152 : ℝ) ≤ (24602237819/25000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984089512759/1000000000000 : ℝ) ≤ (radius 8 (33635/262144 : ℝ)) ∧ (radius 8 (33635/262144 : ℝ)) ≤ (24602237819/25000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33635/262144 : ℝ)) (984089512759/1000000000000 : ℝ) (24602237819/25000000000 : ℝ) (7106935303/40000000000 : ℝ) (177673382581/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33635/262144 : ℝ)) (984089512759/1000000000000 : ℝ) (24602237819/25000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33635/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984089512759/1000000000000 : ℝ) (24602237819/25000000000 : ℝ) (992044756379/1000000000000 : ℝ) (49602237819/50000000000 : ℝ) (99201285917/100000000000 : ℝ) (992012859171/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33635/262144 : ℝ)) 1 (992044756379/1000000000000 : ℝ) (49602237819/50000000000 : ℝ) (99201285917/100000000000 : ℝ) (992012859171/1000000000000 : ℝ) (496014403887/500000000000 : ℝ) (31000900243/31250000000 : ℝ) (496014403823/500000000000 : ℝ) (31000900239/31250000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33635/262144 : ℝ)) 2 (496014403887/500000000000 : ℝ) (31000900243/31250000000 : ℝ) (496014403823/500000000000 : ℝ) (31000900239/31250000000 : ℝ) (99202880771/100000000000 : ℝ) (31000900241/31250000000 : ℝ) (992028807709/1000000000000 : ℝ) (31000900241/31250000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33635/262144 : ℝ)) 3 (99202880771/100000000000 : ℝ) (31000900241/31250000000 : ℝ) (992028807709/1000000000000 : ℝ) (31000900241/31250000000 : ℝ) (992028807709/1000000000000 : ℝ) (31000900241/31250000000 : ℝ) (992028807709/1000000000000 : ℝ) (31000900241/31250000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33635/262144 : ℝ)) 4 (992028807709/1000000000000 : ℝ) (31000900241/31250000000 : ℝ) (992028807709/1000000000000 : ℝ) (31000900241/31250000000 : ℝ) (992028807709/1000000000000 : ℝ) (31000900241/31250000000 : ℝ) (992028807709/1000000000000 : ℝ) (31000900241/31250000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33635/262144 : ℝ)) 5 (992028807709/1000000000000 : ℝ) (31000900241/31250000000 : ℝ) (992028807709/1000000000000 : ℝ) (31000900241/31250000000 : ℝ) (992028807709/1000000000000 : ℝ) (31000900241/31250000000 : ℝ) (992028807709/1000000000000 : ℝ) (31000900241/31250000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33635/262144 : ℝ)) 6 (992028807709/1000000000000 : ℝ) (31000900241/31250000000 : ℝ) (992028807709/1000000000000 : ℝ) (31000900241/31250000000 : ℝ) (992028807709/1000000000000 : ℝ) (31000900241/31250000000 : ℝ) (992028807709/1000000000000 : ℝ) (31000900241/31250000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33635/262144 : ℝ)) 7 (992028807709/1000000000000 : ℝ) (31000900241/31250000000 : ℝ) (992028807709/1000000000000 : ℝ) (31000900241/31250000000 : ℝ) (992028807709/1000000000000 : ℝ) (31000900241/31250000000 : ℝ) (992028807709/1000000000000 : ℝ) (31000900241/31250000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33635/262144 : ℝ))) (7106935303/40000000000 : ℝ) (177673382581/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33635/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (7106935303/40000000000 : ℝ) (177673382581/1000000000000 : ℝ) (588836691287/1000000000000 : ℝ) (588836691291/1000000000000 : ℝ) (210756602847/500000000000 : ℝ) (210756602851/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33635/262144 : ℝ))) 1 (588836691287/1000000000000 : ℝ) (588836691291/1000000000000 : ℝ) (210756602847/500000000000 : ℝ) (210756602851/500000000000 : ℝ) (50517494849/100000000000 : ℝ) (505174948497/1000000000000 : ℝ) (62274899811/125000000000 : ℝ) (99639839699/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33635/262144 : ℝ))) 2 (50517494849/100000000000 : ℝ) (505174948497/1000000000000 : ℝ) (62274899811/125000000000 : ℝ) (99639839699/200000000000 : ℝ) (501687073489/1000000000000 : ℝ) (62710884187/125000000000 : ℝ) (501674948979/1000000000000 : ℝ) (501674948987/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33635/262144 : ℝ))) 3 (501687073489/1000000000000 : ℝ) (62710884187/125000000000 : ℝ) (501674948979/1000000000000 : ℝ) (501674948987/1000000000000 : ℝ) (250840505617/500000000000 : ℝ) (250840505621/500000000000 : ℝ) (501681011197/1000000000000 : ℝ) (100336202241/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33635/262144 : ℝ))) 4 (250840505617/500000000000 : ℝ) (250840505621/500000000000 : ℝ) (501681011197/1000000000000 : ℝ) (100336202241/200000000000 : ℝ) (100336202243/200000000000 : ℝ) (62710126403/125000000000 : ℝ) (100336202243/200000000000 : ℝ) (62710126403/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33635/262144 : ℝ))) 5 (100336202243/200000000000 : ℝ) (62710126403/125000000000 : ℝ) (100336202243/200000000000 : ℝ) (62710126403/125000000000 : ℝ) (100336202243/200000000000 : ℝ) (62710126403/125000000000 : ℝ) (100336202243/200000000000 : ℝ) (62710126403/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33635/262144 : ℝ))) 6 (100336202243/200000000000 : ℝ) (62710126403/125000000000 : ℝ) (100336202243/200000000000 : ℝ) (62710126403/125000000000 : ℝ) (100336202243/200000000000 : ℝ) (62710126403/125000000000 : ℝ) (100336202243/200000000000 : ℝ) (62710126403/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33635/262144 : ℝ))) 7 (100336202243/200000000000 : ℝ) (62710126403/125000000000 : ℝ) (100336202243/200000000000 : ℝ) (62710126403/125000000000 : ℝ) (100336202243/200000000000 : ℝ) (62710126403/125000000000 : ℝ) (100336202243/200000000000 : ℝ) (62710126403/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33635/262144 : ℝ)) hmem 8 (992028807709/1000000000000 : ℝ) (31000900241/31250000000 : ℝ) (992028807709/1000000000000 : ℝ) (31000900241/31250000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33635/262144 : ℝ))) hcmem 8 (100336202243/200000000000 : ℝ) (62710126403/125000000000 : ℝ) (100336202243/200000000000 : ℝ) (62710126403/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33635/262144 : ℝ)) (992028807709/1000000000000 : ℝ) (31000900241/31250000000 : ℝ) (100336202243/200000000000 : ℝ) (62710126403/125000000000 : ℝ) (794370771809/1000000000000 : ℝ) (397185385913/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1197_exp_lower
  have heNumeric : (1027451890007/500000000000 : ℝ)/4 ≤ Real.exp (-85256363090603/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451890007/500000000000 : ℝ)/4 ≤ Real.exp ((67269/524288 : ℝ)-(397185385913/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67269/524288 : ℝ) (33635/262144 : ℝ) (397185385913/500000000000 : ℝ) (1027451890007/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1198; no trusted numerical premise.
theorem cover8_leaf1198_exp_radius : (997997176304042391/1000000000000000000 : ℝ) ≤ Real.exp ((-67271/4194304 : ℝ)/8) ∧ Real.exp ((-67271/4194304 : ℝ)/8) ≤ (124749647038005299/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67271/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1198_exp_lower : (18402271485312043/20000000000000000 : ℝ) ≤ Real.exp ((-42628181130093/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628181130093/64000000000000 : ℝ)/8) ≤ (920113574265602151/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628181130093/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1198_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410980758669/200000000000 : ℝ) ≤ 4*Real.exp (33635/262144 : ℝ)*Real.exp (-mu (radius 8 (67271/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (410980758669/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67271/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1198_exp_radius
  have hrNumeric : (984089278133/1000000000000 : ℝ) ≤ Real.exp (-67271/4194304 : ℝ) ∧ Real.exp (-67271/4194304 : ℝ) ≤ (492044639067/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984089278133/1000000000000 : ℝ) ≤ (radius 8 (67271/524288 : ℝ)) ∧ (radius 8 (67271/524288 : ℝ)) ≤ (492044639067/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67271/524288 : ℝ)) (984089278133/1000000000000 : ℝ) (492044639067/500000000000 : ℝ) (88837341053/500000000000 : ℝ) (177674682113/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67271/524288 : ℝ)) (984089278133/1000000000000 : ℝ) (492044639067/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67271/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984089278133/1000000000000 : ℝ) (492044639067/500000000000 : ℝ) (496022319533/500000000000 : ℝ) (992044639067/1000000000000 : ℝ) (62000796307/62500000000 : ℝ) (496006370457/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67271/524288 : ℝ)) 1 (496022319533/500000000000 : ℝ) (992044639067/1000000000000 : ℝ) (62000796307/62500000000 : ℝ) (496006370457/500000000000 : ℝ) (992028689989/1000000000000 : ℝ) (992028689991/1000000000000 : ℝ) (49601434493/50000000000 : ℝ) (992028689863/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67271/524288 : ℝ)) 2 (992028689989/1000000000000 : ℝ) (992028689991/1000000000000 : ℝ) (49601434493/50000000000 : ℝ) (992028689863/1000000000000 : ℝ) (248007172481/250000000000 : ℝ) (992028689927/1000000000000 : ℝ) (248007172481/250000000000 : ℝ) (992028689927/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67271/524288 : ℝ)) 3 (248007172481/250000000000 : ℝ) (992028689927/1000000000000 : ℝ) (248007172481/250000000000 : ℝ) (992028689927/1000000000000 : ℝ) (248007172481/250000000000 : ℝ) (992028689927/1000000000000 : ℝ) (248007172481/250000000000 : ℝ) (992028689927/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67271/524288 : ℝ)) 4 (248007172481/250000000000 : ℝ) (992028689927/1000000000000 : ℝ) (248007172481/250000000000 : ℝ) (992028689927/1000000000000 : ℝ) (248007172481/250000000000 : ℝ) (992028689927/1000000000000 : ℝ) (248007172481/250000000000 : ℝ) (992028689927/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67271/524288 : ℝ)) 5 (248007172481/250000000000 : ℝ) (992028689927/1000000000000 : ℝ) (248007172481/250000000000 : ℝ) (992028689927/1000000000000 : ℝ) (248007172481/250000000000 : ℝ) (992028689927/1000000000000 : ℝ) (248007172481/250000000000 : ℝ) (992028689927/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67271/524288 : ℝ)) 6 (248007172481/250000000000 : ℝ) (992028689927/1000000000000 : ℝ) (248007172481/250000000000 : ℝ) (992028689927/1000000000000 : ℝ) (248007172481/250000000000 : ℝ) (992028689927/1000000000000 : ℝ) (248007172481/250000000000 : ℝ) (992028689927/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67271/524288 : ℝ)) 7 (248007172481/250000000000 : ℝ) (992028689927/1000000000000 : ℝ) (248007172481/250000000000 : ℝ) (992028689927/1000000000000 : ℝ) (248007172481/250000000000 : ℝ) (992028689927/1000000000000 : ℝ) (248007172481/250000000000 : ℝ) (992028689927/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67271/524288 : ℝ))) (88837341053/500000000000 : ℝ) (177674682113/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67271/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88837341053/500000000000 : ℝ) (177674682113/1000000000000 : ℝ) (588837341053/1000000000000 : ℝ) (588837341057/1000000000000 : ℝ) (210757373599/500000000000 : ℝ) (52689343401/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67271/524288 : ℝ))) 1 (588837341053/1000000000000 : ℝ) (588837341057/1000000000000 : ℝ) (210757373599/500000000000 : ℝ) (52689343401/125000000000 : ℝ) (4041408353/8000000000 : ℝ) (505176044133/1000000000000 : ℝ) (249100192169/500000000000 : ℝ) (249100192173/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67271/524288 : ℝ))) 2 (4041408353/8000000000 : ℝ) (505176044133/1000000000000 : ℝ) (249100192169/500000000000 : ℝ) (249100192173/500000000000 : ℝ) (501688214231/1000000000000 : ℝ) (3135551339/6250000000 : ℝ) (501676090063/1000000000000 : ℝ) (62709511259/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67271/524288 : ℝ))) 3 (501688214231/1000000000000 : ℝ) (3135551339/6250000000 : ℝ) (501676090063/1000000000000 : ℝ) (62709511259/125000000000 : ℝ) (501682152147/1000000000000 : ℝ) (125420538039/250000000000 : ℝ) (50168215211/100000000000 : ℝ) (12542053803/25000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67271/524288 : ℝ))) 4 (501682152147/1000000000000 : ℝ) (125420538039/250000000000 : ℝ) (50168215211/100000000000 : ℝ) (12542053803/25000000000 : ℝ) (7838783627/15625000000 : ℝ) (250841076069/500000000000 : ℝ) (7838783627/15625000000 : ℝ) (250841076069/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67271/524288 : ℝ))) 5 (7838783627/15625000000 : ℝ) (250841076069/500000000000 : ℝ) (7838783627/15625000000 : ℝ) (250841076069/500000000000 : ℝ) (7838783627/15625000000 : ℝ) (250841076069/500000000000 : ℝ) (7838783627/15625000000 : ℝ) (250841076069/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67271/524288 : ℝ))) 6 (7838783627/15625000000 : ℝ) (250841076069/500000000000 : ℝ) (7838783627/15625000000 : ℝ) (250841076069/500000000000 : ℝ) (7838783627/15625000000 : ℝ) (250841076069/500000000000 : ℝ) (7838783627/15625000000 : ℝ) (250841076069/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67271/524288 : ℝ))) 7 (7838783627/15625000000 : ℝ) (250841076069/500000000000 : ℝ) (7838783627/15625000000 : ℝ) (250841076069/500000000000 : ℝ) (7838783627/15625000000 : ℝ) (250841076069/500000000000 : ℝ) (7838783627/15625000000 : ℝ) (250841076069/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67271/524288 : ℝ)) hmem 8 (248007172481/250000000000 : ℝ) (992028689927/1000000000000 : ℝ) (248007172481/250000000000 : ℝ) (992028689927/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67271/524288 : ℝ))) hcmem 8 (7838783627/15625000000 : ℝ) (250841076069/500000000000 : ℝ) (7838783627/15625000000 : ℝ) (250841076069/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67271/524288 : ℝ)) (248007172481/250000000000 : ℝ) (992028689927/1000000000000 : ℝ) (7838783627/15625000000 : ℝ) (250841076069/500000000000 : ℝ) (198593168167/250000000000 : ℝ) (794372672687/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1198_exp_lower
  have heNumeric : (410980758669/200000000000 : ℝ)/4 ≤ Real.exp (-42628181130093/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410980758669/200000000000 : ℝ)/4 ≤ Real.exp ((33635/262144 : ℝ)-(794372672687/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33635/262144 : ℝ) (67271/524288 : ℝ) (794372672687/1000000000000 : ℝ) (410980758669/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1199; no trusted numerical premise.
theorem cover8_leaf1199_exp_radius : (249499286640352311/250000000000000000 : ℝ) ≤ Real.exp ((-8409/524288 : ℝ)/8) ∧ Real.exp ((-8409/524288 : ℝ)/8) ≤ (199599429312281849/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8409/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1199_exp_lower : (115014196876874053/125000000000000000 : ℝ) ≤ Real.exp ((-17051272285237/25600000000000 : ℝ)/8) ∧ Real.exp ((-17051272285237/25600000000000 : ℝ)/8) ≤ (36804543000599697/40000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-17051272285237/25600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1199_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451903367/500000000000 : ℝ) ≤ 4*Real.exp (67271/524288 : ℝ)*Real.exp (-mu (radius 8 (8409/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451903367/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8409/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1199_exp_radius
  have hrNumeric : (246022260877/250000000000 : ℝ) ≤ Real.exp (-8409/524288 : ℝ) ∧ Real.exp (-8409/524288 : ℝ) ≤ (984089043509/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246022260877/250000000000 : ℝ) ≤ (radius 8 (8409/65536 : ℝ)) ∧ (radius 8 (8409/65536 : ℝ)) ≤ (984089043509/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8409/65536 : ℝ)) (246022260877/250000000000 : ℝ) (984089043509/1000000000000 : ℝ) (88837990811/500000000000 : ℝ) (177675981629/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8409/65536 : ℝ)) (246022260877/250000000000 : ℝ) (984089043509/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8409/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246022260877/250000000000 : ℝ) (984089043509/1000000000000 : ℝ) (496022260877/500000000000 : ℝ) (198408904351/200000000000 : ℝ) (198402524531/200000000000 : ℝ) (992012622657/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8409/65536 : ℝ)) 1 (496022260877/500000000000 : ℝ) (198408904351/200000000000 : ℝ) (198402524531/200000000000 : ℝ) (992012622657/1000000000000 : ℝ) (248007143051/250000000000 : ℝ) (496014286103/500000000000 : ℝ) (248007143019/250000000000 : ℝ) (496014286039/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8409/65536 : ℝ)) 2 (248007143051/250000000000 : ℝ) (496014286103/500000000000 : ℝ) (248007143019/250000000000 : ℝ) (496014286039/500000000000 : ℝ) (49601428607/50000000000 : ℝ) (496014286071/500000000000 : ℝ) (992028572139/1000000000000 : ℝ) (496014286071/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8409/65536 : ℝ)) 3 (49601428607/50000000000 : ℝ) (496014286071/500000000000 : ℝ) (992028572139/1000000000000 : ℝ) (496014286071/500000000000 : ℝ) (992028572139/1000000000000 : ℝ) (496014286071/500000000000 : ℝ) (992028572139/1000000000000 : ℝ) (496014286071/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8409/65536 : ℝ)) 4 (992028572139/1000000000000 : ℝ) (496014286071/500000000000 : ℝ) (992028572139/1000000000000 : ℝ) (496014286071/500000000000 : ℝ) (992028572139/1000000000000 : ℝ) (496014286071/500000000000 : ℝ) (992028572139/1000000000000 : ℝ) (496014286071/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8409/65536 : ℝ)) 5 (992028572139/1000000000000 : ℝ) (496014286071/500000000000 : ℝ) (992028572139/1000000000000 : ℝ) (496014286071/500000000000 : ℝ) (992028572139/1000000000000 : ℝ) (496014286071/500000000000 : ℝ) (992028572139/1000000000000 : ℝ) (496014286071/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8409/65536 : ℝ)) 6 (992028572139/1000000000000 : ℝ) (496014286071/500000000000 : ℝ) (992028572139/1000000000000 : ℝ) (496014286071/500000000000 : ℝ) (992028572139/1000000000000 : ℝ) (496014286071/500000000000 : ℝ) (992028572139/1000000000000 : ℝ) (496014286071/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8409/65536 : ℝ)) 7 (992028572139/1000000000000 : ℝ) (496014286071/500000000000 : ℝ) (992028572139/1000000000000 : ℝ) (496014286071/500000000000 : ℝ) (992028572139/1000000000000 : ℝ) (496014286071/500000000000 : ℝ) (992028572139/1000000000000 : ℝ) (496014286071/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8409/65536 : ℝ))) (88837990811/500000000000 : ℝ) (177675981629/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8409/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88837990811/500000000000 : ℝ) (177675981629/1000000000000 : ℝ) (588837990811/1000000000000 : ℝ) (117767598163/200000000000 : ℝ) (421516288679/1000000000000 : ℝ) (26344768043/62500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8409/65536 : ℝ))) 1 (588837990811/1000000000000 : ℝ) (117767598163/200000000000 : ℝ) (421516288679/1000000000000 : ℝ) (26344768043/62500000000 : ℝ) (101035427949/200000000000 : ℝ) (63147142469/125000000000 : ℝ) (498201570169/1000000000000 : ℝ) (249100785089/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8409/65536 : ℝ))) 2 (101035427949/200000000000 : ℝ) (63147142469/125000000000 : ℝ) (498201570169/1000000000000 : ℝ) (249100785089/500000000000 : ℝ) (501689354957/1000000000000 : ℝ) (100337870993/200000000000 : ℝ) (50167723113/100000000000 : ℝ) (501677231139/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8409/65536 : ℝ))) 3 (501689354957/1000000000000 : ℝ) (100337870993/200000000000 : ℝ) (50167723113/100000000000 : ℝ) (501677231139/1000000000000 : ℝ) (501683293043/1000000000000 : ℝ) (125420823263/250000000000 : ℝ) (250841646503/500000000000 : ℝ) (62710411627/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8409/65536 : ℝ))) 4 (501683293043/1000000000000 : ℝ) (125420823263/250000000000 : ℝ) (250841646503/500000000000 : ℝ) (62710411627/125000000000 : ℝ) (15677602907/31250000000 : ℝ) (250841646517/500000000000 : ℝ) (15677602907/31250000000 : ℝ) (250841646517/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8409/65536 : ℝ))) 5 (15677602907/31250000000 : ℝ) (250841646517/500000000000 : ℝ) (15677602907/31250000000 : ℝ) (250841646517/500000000000 : ℝ) (15677602907/31250000000 : ℝ) (250841646517/500000000000 : ℝ) (15677602907/31250000000 : ℝ) (250841646517/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8409/65536 : ℝ))) 6 (15677602907/31250000000 : ℝ) (250841646517/500000000000 : ℝ) (15677602907/31250000000 : ℝ) (250841646517/500000000000 : ℝ) (15677602907/31250000000 : ℝ) (250841646517/500000000000 : ℝ) (15677602907/31250000000 : ℝ) (250841646517/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8409/65536 : ℝ))) 7 (15677602907/31250000000 : ℝ) (250841646517/500000000000 : ℝ) (15677602907/31250000000 : ℝ) (250841646517/500000000000 : ℝ) (15677602907/31250000000 : ℝ) (250841646517/500000000000 : ℝ) (15677602907/31250000000 : ℝ) (250841646517/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8409/65536 : ℝ)) hmem 8 (992028572139/1000000000000 : ℝ) (496014286071/500000000000 : ℝ) (992028572139/1000000000000 : ℝ) (496014286071/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8409/65536 : ℝ))) hcmem 8 (15677602907/31250000000 : ℝ) (250841646517/500000000000 : ℝ) (15677602907/31250000000 : ℝ) (250841646517/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8409/65536 : ℝ)) (992028572139/1000000000000 : ℝ) (496014286071/500000000000 : ℝ) (15677602907/31250000000 : ℝ) (250841646517/500000000000 : ℝ) (794374573501/1000000000000 : ℝ) (9929682169/12500000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1199_exp_lower
  have heNumeric : (1027451903367/500000000000 : ℝ)/4 ≤ Real.exp (-17051272285237/25600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451903367/500000000000 : ℝ)/4 ≤ Real.exp ((67271/524288 : ℝ)-(9929682169/12500000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67271/524288 : ℝ) (8409/65536 : ℝ) (9929682169/12500000000 : ℝ) (1027451903367/500000000000 : ℝ) hmu.2 heBox
  · norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_leaf1175_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1175_certificate
#check SmaleRate.Proofs.cover8_leaf1176_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1176_certificate
#check SmaleRate.Proofs.cover8_leaf1177_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1177_certificate
#check SmaleRate.Proofs.cover8_leaf1178_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1178_certificate
#check SmaleRate.Proofs.cover8_leaf1179_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1179_certificate
#check SmaleRate.Proofs.cover8_leaf1180_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1180_certificate
#check SmaleRate.Proofs.cover8_leaf1181_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1181_certificate
#check SmaleRate.Proofs.cover8_leaf1182_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1182_certificate
#check SmaleRate.Proofs.cover8_leaf1183_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1183_certificate
#check SmaleRate.Proofs.cover8_leaf1184_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1184_certificate
#check SmaleRate.Proofs.cover8_leaf1185_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1185_certificate
#check SmaleRate.Proofs.cover8_leaf1186_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1186_certificate
#check SmaleRate.Proofs.cover8_leaf1187_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1187_certificate
#check SmaleRate.Proofs.cover8_leaf1188_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1188_certificate
#check SmaleRate.Proofs.cover8_leaf1189_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1189_certificate
#check SmaleRate.Proofs.cover8_leaf1190_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1190_certificate
#check SmaleRate.Proofs.cover8_leaf1191_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1191_certificate
#check SmaleRate.Proofs.cover8_leaf1192_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1192_certificate
#check SmaleRate.Proofs.cover8_leaf1193_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1193_certificate
#check SmaleRate.Proofs.cover8_leaf1194_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1194_certificate
#check SmaleRate.Proofs.cover8_leaf1195_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1195_certificate
#check SmaleRate.Proofs.cover8_leaf1196_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1196_certificate
#check SmaleRate.Proofs.cover8_leaf1197_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1197_certificate
#check SmaleRate.Proofs.cover8_leaf1198_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1198_certificate
#check SmaleRate.Proofs.cover8_leaf1199_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1199_certificate
