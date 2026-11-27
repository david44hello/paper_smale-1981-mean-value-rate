/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.AGMCertificates

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

-- Proposed record cover8_leaf0400; no trusted numerical premise.
theorem cover8_leaf0400_exp_radius : (199604842544837353/200000000000000000 : ℝ) ≤ Real.exp ((-33181/2097152 : ℝ)/8) ∧ Real.exp ((-33181/2097152 : ℝ)/8) ≤ (499012106362093383/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33181/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0400_exp_lower : (460056796231352331/500000000000000000 : ℝ) ≤ Real.exp ((-2131408550213/3200000000000 : ℝ)/8) ∧ Real.exp ((-2131408550213/3200000000000 : ℝ)/8) ≤ (920113592462704663/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2131408550213/3200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0400_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (32107876851/15625000000 : ℝ) ≤ 4*Real.exp (8295/65536 : ℝ)*Real.exp (-mu (radius 8 (33181/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (32107876851/15625000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33181/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0400_exp_radius
  have hrNumeric : (984302575523/1000000000000 : ℝ) ≤ Real.exp (-33181/2097152 : ℝ) ∧ Real.exp (-33181/2097152 : ℝ) ≤ (246075643881/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984302575523/1000000000000 : ℝ) ≤ (radius 8 (33181/262144 : ℝ)) ∧ (radius 8 (33181/262144 : ℝ)) ≤ (246075643881/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33181/262144 : ℝ)) (984302575523/1000000000000 : ℝ) (246075643881/250000000000 : ℝ) (176489205949/1000000000000 : ℝ) (44122301489/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33181/262144 : ℝ)) (984302575523/1000000000000 : ℝ) (246075643881/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33181/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984302575523/1000000000000 : ℝ) (246075643881/250000000000 : ℝ) (992151287761/1000000000000 : ℝ) (496075643881/500000000000 : ℝ) (124015030309/125000000000 : ℝ) (992120242473/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33181/262144 : ℝ)) 1 (992151287761/1000000000000 : ℝ) (496075643881/500000000000 : ℝ) (124015030309/125000000000 : ℝ) (992120242473/1000000000000 : ℝ) (248033941279/250000000000 : ℝ) (496067882559/500000000000 : ℝ) (198427152999/200000000000 : ℝ) (992135764997/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33181/262144 : ℝ)) 2 (248033941279/250000000000 : ℝ) (496067882559/500000000000 : ℝ) (198427152999/200000000000 : ℝ) (992135764997/1000000000000 : ℝ) (198427153011/200000000000 : ℝ) (496067882529/500000000000 : ℝ) (198427153011/200000000000 : ℝ) (496067882529/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33181/262144 : ℝ)) 3 (198427153011/200000000000 : ℝ) (496067882529/500000000000 : ℝ) (198427153011/200000000000 : ℝ) (496067882529/500000000000 : ℝ) (198427153011/200000000000 : ℝ) (496067882529/500000000000 : ℝ) (198427153011/200000000000 : ℝ) (496067882529/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33181/262144 : ℝ)) 4 (198427153011/200000000000 : ℝ) (496067882529/500000000000 : ℝ) (198427153011/200000000000 : ℝ) (496067882529/500000000000 : ℝ) (198427153011/200000000000 : ℝ) (496067882529/500000000000 : ℝ) (198427153011/200000000000 : ℝ) (496067882529/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33181/262144 : ℝ)) 5 (198427153011/200000000000 : ℝ) (496067882529/500000000000 : ℝ) (198427153011/200000000000 : ℝ) (496067882529/500000000000 : ℝ) (198427153011/200000000000 : ℝ) (496067882529/500000000000 : ℝ) (198427153011/200000000000 : ℝ) (496067882529/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33181/262144 : ℝ)) 6 (198427153011/200000000000 : ℝ) (496067882529/500000000000 : ℝ) (198427153011/200000000000 : ℝ) (496067882529/500000000000 : ℝ) (198427153011/200000000000 : ℝ) (496067882529/500000000000 : ℝ) (198427153011/200000000000 : ℝ) (496067882529/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33181/262144 : ℝ)) 7 (198427153011/200000000000 : ℝ) (496067882529/500000000000 : ℝ) (198427153011/200000000000 : ℝ) (496067882529/500000000000 : ℝ) (198427153011/200000000000 : ℝ) (496067882529/500000000000 : ℝ) (198427153011/200000000000 : ℝ) (496067882529/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33181/262144 : ℝ))) (176489205949/1000000000000 : ℝ) (44122301489/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33181/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176489205949/1000000000000 : ℝ) (44122301489/250000000000 : ℝ) (294122301487/500000000000 : ℝ) (294122301489/500000000000 : ℝ) (84021236827/200000000000 : ℝ) (26256636509/62500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33181/262144 : ℝ))) 1 (294122301487/500000000000 : ℝ) (294122301489/500000000000 : ℝ) (84021236827/200000000000 : ℝ) (26256636509/62500000000 : ℝ) (252087696777/500000000000 : ℝ) (504175393561/1000000000000 : ℝ) (49711688313/100000000000 : ℝ) (248558441569/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33181/262144 : ℝ))) 2 (252087696777/500000000000 : ℝ) (504175393561/1000000000000 : ℝ) (49711688313/100000000000 : ℝ) (248558441569/500000000000 : ℝ) (250323069171/500000000000 : ℝ) (10012922767/20000000000 : ℝ) (25031684931/50000000000 : ℝ) (125158424657/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33181/262144 : ℝ))) 3 (250323069171/500000000000 : ℝ) (10012922767/20000000000 : ℝ) (25031684931/50000000000 : ℝ) (125158424657/250000000000 : ℝ) (500639918481/1000000000000 : ℝ) (500639918489/1000000000000 : ℝ) (250319959221/500000000000 : ℝ) (500639918451/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33181/262144 : ℝ))) 4 (500639918481/1000000000000 : ℝ) (500639918489/1000000000000 : ℝ) (250319959221/500000000000 : ℝ) (500639918451/1000000000000 : ℝ) (500639918461/1000000000000 : ℝ) (50063991847/100000000000 : ℝ) (500639918461/1000000000000 : ℝ) (50063991847/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33181/262144 : ℝ))) 5 (500639918461/1000000000000 : ℝ) (50063991847/100000000000 : ℝ) (500639918461/1000000000000 : ℝ) (50063991847/100000000000 : ℝ) (500639918461/1000000000000 : ℝ) (50063991847/100000000000 : ℝ) (500639918461/1000000000000 : ℝ) (50063991847/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33181/262144 : ℝ))) 6 (500639918461/1000000000000 : ℝ) (50063991847/100000000000 : ℝ) (500639918461/1000000000000 : ℝ) (50063991847/100000000000 : ℝ) (500639918461/1000000000000 : ℝ) (50063991847/100000000000 : ℝ) (500639918461/1000000000000 : ℝ) (50063991847/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33181/262144 : ℝ))) 7 (500639918461/1000000000000 : ℝ) (50063991847/100000000000 : ℝ) (500639918461/1000000000000 : ℝ) (50063991847/100000000000 : ℝ) (500639918461/1000000000000 : ℝ) (50063991847/100000000000 : ℝ) (500639918461/1000000000000 : ℝ) (50063991847/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33181/262144 : ℝ)) hmem 8 (198427153011/200000000000 : ℝ) (496067882529/500000000000 : ℝ) (198427153011/200000000000 : ℝ) (496067882529/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33181/262144 : ℝ))) hcmem 8 (500639918461/1000000000000 : ℝ) (50063991847/100000000000 : ℝ) (500639918461/1000000000000 : ℝ) (50063991847/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33181/262144 : ℝ)) (198427153011/200000000000 : ℝ) (496067882529/500000000000 : ℝ) (500639918461/1000000000000 : ℝ) (50063991847/100000000000 : ℝ) (396318413599/500000000000 : ℝ) (158527365443/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0400_exp_lower
  have heNumeric : (32107876851/15625000000 : ℝ)/4 ≤ Real.exp (-2131408550213/3200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (32107876851/15625000000 : ℝ)/4 ≤ Real.exp ((8295/65536 : ℝ)-(158527365443/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8295/65536 : ℝ) (33181/262144 : ℝ) (158527365443/200000000000 : ℝ) (32107876851/15625000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0401; no trusted numerical premise.
theorem cover8_leaf0401_exp_radius : (499012076618654931/500000000000000000 : ℝ) ≤ Real.exp ((-16591/1048576 : ℝ)/8) ∧ Real.exp ((-16591/1048576 : ℝ)/8) ≤ (998024153237309863/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16591/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0401_exp_lower : (46005679495447997/50000000000000000 : ℝ) ≤ Real.exp ((-42628172425299/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628172425299/64000000000000 : ℝ)/8) ≤ (920113589908959941/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628172425299/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0401_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027452036419/500000000000 : ℝ) ≤ 4*Real.exp (33181/262144 : ℝ)*Real.exp (-mu (radius 8 (16591/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (1027452036419/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16591/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0401_exp_radius
  have hrNumeric : (984302106171/1000000000000 : ℝ) ≤ Real.exp (-16591/1048576 : ℝ) ∧ Real.exp (-16591/1048576 : ℝ) ≤ (246075526543/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984302106171/1000000000000 : ℝ) ≤ (radius 8 (16591/131072 : ℝ)) ∧ (radius 8 (16591/131072 : ℝ)) ≤ (246075526543/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16591/131072 : ℝ)) (984302106171/1000000000000 : ℝ) (246075526543/250000000000 : ℝ) (35298364713/200000000000 : ℝ) (176491823571/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16591/131072 : ℝ)) (984302106171/1000000000000 : ℝ) (246075526543/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16591/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984302106171/1000000000000 : ℝ) (246075526543/250000000000 : ℝ) (198430210617/200000000000 : ℝ) (496075526543/500000000000 : ℝ) (248030001483/250000000000 : ℝ) (992120005933/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16591/131072 : ℝ)) 1 (198430210617/200000000000 : ℝ) (496075526543/500000000000 : ℝ) (248030001483/250000000000 : ℝ) (992120005933/1000000000000 : ℝ) (248033882377/250000000000 : ℝ) (99213552951/100000000000 : ℝ) (992135529387/1000000000000 : ℝ) (992135529389/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16591/131072 : ℝ)) 2 (248033882377/250000000000 : ℝ) (99213552951/100000000000 : ℝ) (992135529387/1000000000000 : ℝ) (992135529389/1000000000000 : ℝ) (992135529447/1000000000000 : ℝ) (19842710589/20000000000 : ℝ) (992135529447/1000000000000 : ℝ) (19842710589/20000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16591/131072 : ℝ)) 3 (992135529447/1000000000000 : ℝ) (19842710589/20000000000 : ℝ) (992135529447/1000000000000 : ℝ) (19842710589/20000000000 : ℝ) (992135529447/1000000000000 : ℝ) (19842710589/20000000000 : ℝ) (992135529447/1000000000000 : ℝ) (19842710589/20000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16591/131072 : ℝ)) 4 (992135529447/1000000000000 : ℝ) (19842710589/20000000000 : ℝ) (992135529447/1000000000000 : ℝ) (19842710589/20000000000 : ℝ) (992135529447/1000000000000 : ℝ) (19842710589/20000000000 : ℝ) (992135529447/1000000000000 : ℝ) (19842710589/20000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16591/131072 : ℝ)) 5 (992135529447/1000000000000 : ℝ) (19842710589/20000000000 : ℝ) (992135529447/1000000000000 : ℝ) (19842710589/20000000000 : ℝ) (992135529447/1000000000000 : ℝ) (19842710589/20000000000 : ℝ) (992135529447/1000000000000 : ℝ) (19842710589/20000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16591/131072 : ℝ)) 6 (992135529447/1000000000000 : ℝ) (19842710589/20000000000 : ℝ) (992135529447/1000000000000 : ℝ) (19842710589/20000000000 : ℝ) (992135529447/1000000000000 : ℝ) (19842710589/20000000000 : ℝ) (992135529447/1000000000000 : ℝ) (19842710589/20000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16591/131072 : ℝ)) 7 (992135529447/1000000000000 : ℝ) (19842710589/20000000000 : ℝ) (992135529447/1000000000000 : ℝ) (19842710589/20000000000 : ℝ) (992135529447/1000000000000 : ℝ) (19842710589/20000000000 : ℝ) (992135529447/1000000000000 : ℝ) (19842710589/20000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16591/131072 : ℝ))) (35298364713/200000000000 : ℝ) (176491823571/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16591/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35298364713/200000000000 : ℝ) (176491823571/1000000000000 : ℝ) (294122955891/500000000000 : ℝ) (294122955893/500000000000 : ℝ) (84021859909/200000000000 : ℝ) (210054649777/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16591/131072 : ℝ))) 1 (294122955891/500000000000 : ℝ) (294122955893/500000000000 : ℝ) (84021859909/200000000000 : ℝ) (210054649777/500000000000 : ℝ) (504177605663/1000000000000 : ℝ) (50417760567/100000000000 : ℝ) (497119279407/1000000000000 : ℝ) (99423855883/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16591/131072 : ℝ))) 2 (504177605663/1000000000000 : ℝ) (50417760567/100000000000 : ℝ) (497119279407/1000000000000 : ℝ) (99423855883/200000000000 : ℝ) (100129688507/200000000000 : ℝ) (500648442543/1000000000000 : ℝ) (500636003519/1000000000000 : ℝ) (62579500441/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16591/131072 : ℝ))) 3 (100129688507/200000000000 : ℝ) (500648442543/1000000000000 : ℝ) (500636003519/1000000000000 : ℝ) (62579500441/125000000000 : ℝ) (500642223027/1000000000000 : ℝ) (125160555759/250000000000 : ℝ) (125160555747/250000000000 : ℝ) (500642222997/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16591/131072 : ℝ))) 4 (500642223027/1000000000000 : ℝ) (125160555759/250000000000 : ℝ) (125160555747/250000000000 : ℝ) (500642222997/1000000000000 : ℝ) (500642223007/1000000000000 : ℝ) (500642223017/1000000000000 : ℝ) (500642223007/1000000000000 : ℝ) (500642223017/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16591/131072 : ℝ))) 5 (500642223007/1000000000000 : ℝ) (500642223017/1000000000000 : ℝ) (500642223007/1000000000000 : ℝ) (500642223017/1000000000000 : ℝ) (500642223007/1000000000000 : ℝ) (500642223017/1000000000000 : ℝ) (500642223007/1000000000000 : ℝ) (500642223017/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16591/131072 : ℝ))) 6 (500642223007/1000000000000 : ℝ) (500642223017/1000000000000 : ℝ) (500642223007/1000000000000 : ℝ) (500642223017/1000000000000 : ℝ) (500642223007/1000000000000 : ℝ) (500642223017/1000000000000 : ℝ) (500642223007/1000000000000 : ℝ) (500642223017/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16591/131072 : ℝ))) 7 (500642223007/1000000000000 : ℝ) (500642223017/1000000000000 : ℝ) (500642223007/1000000000000 : ℝ) (500642223017/1000000000000 : ℝ) (500642223007/1000000000000 : ℝ) (500642223017/1000000000000 : ℝ) (500642223007/1000000000000 : ℝ) (500642223017/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16591/131072 : ℝ)) hmem 8 (992135529447/1000000000000 : ℝ) (19842710589/20000000000 : ℝ) (992135529447/1000000000000 : ℝ) (19842710589/20000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16591/131072 : ℝ))) hcmem 8 (500642223007/1000000000000 : ℝ) (500642223017/1000000000000 : ℝ) (500642223007/1000000000000 : ℝ) (500642223017/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16591/131072 : ℝ)) (992135529447/1000000000000 : ℝ) (19842710589/20000000000 : ℝ) (500642223007/1000000000000 : ℝ) (500642223017/1000000000000 : ℝ) (792640664097/1000000000000 : ℝ) (198160166029/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0401_exp_lower
  have heNumeric : (1027452036419/500000000000 : ℝ)/4 ≤ Real.exp (-42628172425299/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027452036419/500000000000 : ℝ)/4 ≤ Real.exp ((33181/262144 : ℝ)-(198160166029/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33181/262144 : ℝ) (16591/131072 : ℝ) (198160166029/250000000000 : ℝ) (1027452036419/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0402; no trusted numerical premise.
theorem cover8_leaf0402_exp_radius : (124753011718804563/125000000000000000 : ℝ) ≤ Real.exp ((-33183/2097152 : ℝ)/8) ∧ Real.exp ((-33183/2097152 : ℝ)/8) ≤ (199604818750087301/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33183/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0402_exp_lower : (920113587364301347/1000000000000000000 : ℝ) ≤ Real.exp ((-21314086920641/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314086920641/32000000000000 : ℝ)/8) ≤ (230028396841075337/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314086920641/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0402_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027452013687/500000000000 : ℝ) ≤ 4*Real.exp (16591/131072 : ℝ)*Real.exp (-mu (radius 8 (33183/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (1027452013687/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33183/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0402_exp_radius
  have hrNumeric : (984301636819/1000000000000 : ℝ) ≤ Real.exp (-33183/2097152 : ℝ) ∧ Real.exp (-33183/2097152 : ℝ) ≤ (49215081841/50000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984301636819/1000000000000 : ℝ) ≤ (radius 8 (33183/262144 : ℝ)) ∧ (radius 8 (33183/262144 : ℝ)) ≤ (49215081841/50000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33183/262144 : ℝ)) (984301636819/1000000000000 : ℝ) (49215081841/50000000000 : ℝ) (8824722057/50000000000 : ℝ) (88247220573/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33183/262144 : ℝ)) (984301636819/1000000000000 : ℝ) (49215081841/50000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33183/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984301636819/1000000000000 : ℝ) (49215081841/50000000000 : ℝ) (992150818409/1000000000000 : ℝ) (99215081841/100000000000 : ℝ) (62007485587/62500000000 : ℝ) (992119769393/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33183/262144 : ℝ)) 1 (992150818409/1000000000000 : ℝ) (99215081841/100000000000 : ℝ) (62007485587/62500000000 : ℝ) (992119769393/1000000000000 : ℝ) (9921352939/10000000000 : ℝ) (496067646951/500000000000 : ℝ) (992135293779/1000000000000 : ℝ) (992135293781/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33183/262144 : ℝ)) 2 (9921352939/10000000000 : ℝ) (496067646951/500000000000 : ℝ) (992135293779/1000000000000 : ℝ) (992135293781/1000000000000 : ℝ) (992135293839/1000000000000 : ℝ) (496067646921/500000000000 : ℝ) (992135293839/1000000000000 : ℝ) (496067646921/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33183/262144 : ℝ)) 3 (992135293839/1000000000000 : ℝ) (496067646921/500000000000 : ℝ) (992135293839/1000000000000 : ℝ) (496067646921/500000000000 : ℝ) (992135293839/1000000000000 : ℝ) (496067646921/500000000000 : ℝ) (992135293839/1000000000000 : ℝ) (496067646921/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33183/262144 : ℝ)) 4 (992135293839/1000000000000 : ℝ) (496067646921/500000000000 : ℝ) (992135293839/1000000000000 : ℝ) (496067646921/500000000000 : ℝ) (992135293839/1000000000000 : ℝ) (496067646921/500000000000 : ℝ) (992135293839/1000000000000 : ℝ) (496067646921/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33183/262144 : ℝ)) 5 (992135293839/1000000000000 : ℝ) (496067646921/500000000000 : ℝ) (992135293839/1000000000000 : ℝ) (496067646921/500000000000 : ℝ) (992135293839/1000000000000 : ℝ) (496067646921/500000000000 : ℝ) (992135293839/1000000000000 : ℝ) (496067646921/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33183/262144 : ℝ)) 6 (992135293839/1000000000000 : ℝ) (496067646921/500000000000 : ℝ) (992135293839/1000000000000 : ℝ) (496067646921/500000000000 : ℝ) (992135293839/1000000000000 : ℝ) (496067646921/500000000000 : ℝ) (992135293839/1000000000000 : ℝ) (496067646921/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33183/262144 : ℝ)) 7 (992135293839/1000000000000 : ℝ) (496067646921/500000000000 : ℝ) (992135293839/1000000000000 : ℝ) (496067646921/500000000000 : ℝ) (992135293839/1000000000000 : ℝ) (496067646921/500000000000 : ℝ) (992135293839/1000000000000 : ℝ) (496067646921/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33183/262144 : ℝ))) (8824722057/50000000000 : ℝ) (88247220573/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33183/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (8824722057/50000000000 : ℝ) (88247220573/500000000000 : ℝ) (58824722057/100000000000 : ℝ) (588247220573/1000000000000 : ℝ) (105028103721/250000000000 : ℝ) (105028103723/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33183/262144 : ℝ))) 1 (58824722057/100000000000 : ℝ) (588247220573/1000000000000 : ℝ) (105028103721/250000000000 : ℝ) (105028103723/250000000000 : ℝ) (504179817727/1000000000000 : ℝ) (504179817733/1000000000000 : ℝ) (497121675631/1000000000000 : ℝ) (248560837819/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33183/262144 : ℝ))) 2 (504179817727/1000000000000 : ℝ) (504179817733/1000000000000 : ℝ) (497121675631/1000000000000 : ℝ) (248560837819/500000000000 : ℝ) (500650746679/1000000000000 : ℝ) (250325373343/500000000000 : ℝ) (50063830837/100000000000 : ℝ) (500638308377/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33183/262144 : ℝ))) 3 (500650746679/1000000000000 : ℝ) (250325373343/500000000000 : ℝ) (50063830837/100000000000 : ℝ) (500638308377/1000000000000 : ℝ) (125161131881/250000000000 : ℝ) (125161131883/250000000000 : ℝ) (100128905497/200000000000 : ℝ) (500644527493/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33183/262144 : ℝ))) 4 (125161131881/250000000000 : ℝ) (125161131883/250000000000 : ℝ) (100128905497/200000000000 : ℝ) (500644527493/1000000000000 : ℝ) (31290282969/62500000000 : ℝ) (500644527513/1000000000000 : ℝ) (31290282969/62500000000 : ℝ) (500644527513/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33183/262144 : ℝ))) 5 (31290282969/62500000000 : ℝ) (500644527513/1000000000000 : ℝ) (31290282969/62500000000 : ℝ) (500644527513/1000000000000 : ℝ) (31290282969/62500000000 : ℝ) (500644527513/1000000000000 : ℝ) (31290282969/62500000000 : ℝ) (500644527513/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33183/262144 : ℝ))) 6 (31290282969/62500000000 : ℝ) (500644527513/1000000000000 : ℝ) (31290282969/62500000000 : ℝ) (500644527513/1000000000000 : ℝ) (31290282969/62500000000 : ℝ) (500644527513/1000000000000 : ℝ) (31290282969/62500000000 : ℝ) (500644527513/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33183/262144 : ℝ))) 7 (31290282969/62500000000 : ℝ) (500644527513/1000000000000 : ℝ) (31290282969/62500000000 : ℝ) (500644527513/1000000000000 : ℝ) (31290282969/62500000000 : ℝ) (500644527513/1000000000000 : ℝ) (31290282969/62500000000 : ℝ) (500644527513/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33183/262144 : ℝ)) hmem 8 (992135293839/1000000000000 : ℝ) (496067646921/500000000000 : ℝ) (992135293839/1000000000000 : ℝ) (496067646921/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33183/262144 : ℝ))) hcmem 8 (31290282969/62500000000 : ℝ) (500644527513/1000000000000 : ℝ) (31290282969/62500000000 : ℝ) (500644527513/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33183/262144 : ℝ)) (992135293839/1000000000000 : ℝ) (496067646921/500000000000 : ℝ) (31290282969/62500000000 : ℝ) (500644527513/1000000000000 : ℝ) (19816112523/25000000000 : ℝ) (396322250469/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0402_exp_lower
  have heNumeric : (1027452013687/500000000000 : ℝ)/4 ≤ Real.exp (-21314086920641/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027452013687/500000000000 : ℝ)/4 ≤ Real.exp ((16591/131072 : ℝ)-(396322250469/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16591/131072 : ℝ) (33183/262144 : ℝ) (396322250469/500000000000 : ℝ) (1027452013687/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0403; no trusted numerical premise.
theorem cover8_leaf0403_exp_radius : (998024034263566691/1000000000000000000 : ℝ) ≤ Real.exp ((-1037/65536 : ℝ)/8) ∧ Real.exp ((-1037/65536 : ℝ)/8) ≤ (249506008565891673/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1037/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0403_exp_lower : (460056792414651977/500000000000000000 : ℝ) ≤ Real.exp ((-42628175251889/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628175251889/64000000000000 : ℝ)/8) ≤ (184022716965860791/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628175251889/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0403_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451991041/500000000000 : ℝ) ≤ 4*Real.exp (33183/262144 : ℝ)*Real.exp (-mu (radius 8 (1037/8192 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451991041/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (1037/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0403_exp_radius
  have hrNumeric : (246075291867/250000000000 : ℝ) ≤ Real.exp (-1037/65536 : ℝ) ∧ Real.exp (-1037/65536 : ℝ) ≤ (984301167469/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246075291867/250000000000 : ℝ) ≤ (radius 8 (1037/8192 : ℝ)) ∧ (radius 8 (1037/8192 : ℝ)) ≤ (984301167469/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (1037/8192 : ℝ)) (246075291867/250000000000 : ℝ) (984301167469/1000000000000 : ℝ) (17649705867/100000000000 : ℝ) (44124264669/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (1037/8192 : ℝ)) (246075291867/250000000000 : ℝ) (984301167469/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (1037/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246075291867/250000000000 : ℝ) (984301167469/1000000000000 : ℝ) (496075291867/500000000000 : ℝ) (198430116747/200000000000 : ℝ) (248029883213/250000000000 : ℝ) (496059766427/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (1037/8192 : ℝ)) 1 (496075291867/500000000000 : ℝ) (198430116747/200000000000 : ℝ) (248029883213/250000000000 : ℝ) (496059766427/500000000000 : ℝ) (992135058293/1000000000000 : ℝ) (198427011659/200000000000 : ℝ) (992135058171/1000000000000 : ℝ) (496067529087/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (1037/8192 : ℝ)) 2 (992135058293/1000000000000 : ℝ) (198427011659/200000000000 : ℝ) (992135058171/1000000000000 : ℝ) (496067529087/500000000000 : ℝ) (124016882279/125000000000 : ℝ) (198427011647/200000000000 : ℝ) (992135058231/1000000000000 : ℝ) (198427011647/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (1037/8192 : ℝ)) 3 (124016882279/125000000000 : ℝ) (198427011647/200000000000 : ℝ) (992135058231/1000000000000 : ℝ) (198427011647/200000000000 : ℝ) (992135058231/1000000000000 : ℝ) (198427011647/200000000000 : ℝ) (992135058231/1000000000000 : ℝ) (198427011647/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (1037/8192 : ℝ)) 4 (992135058231/1000000000000 : ℝ) (198427011647/200000000000 : ℝ) (992135058231/1000000000000 : ℝ) (198427011647/200000000000 : ℝ) (992135058231/1000000000000 : ℝ) (198427011647/200000000000 : ℝ) (992135058231/1000000000000 : ℝ) (198427011647/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (1037/8192 : ℝ)) 5 (992135058231/1000000000000 : ℝ) (198427011647/200000000000 : ℝ) (992135058231/1000000000000 : ℝ) (198427011647/200000000000 : ℝ) (992135058231/1000000000000 : ℝ) (198427011647/200000000000 : ℝ) (992135058231/1000000000000 : ℝ) (198427011647/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (1037/8192 : ℝ)) 6 (992135058231/1000000000000 : ℝ) (198427011647/200000000000 : ℝ) (992135058231/1000000000000 : ℝ) (198427011647/200000000000 : ℝ) (992135058231/1000000000000 : ℝ) (198427011647/200000000000 : ℝ) (992135058231/1000000000000 : ℝ) (198427011647/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (1037/8192 : ℝ)) 7 (992135058231/1000000000000 : ℝ) (198427011647/200000000000 : ℝ) (992135058231/1000000000000 : ℝ) (198427011647/200000000000 : ℝ) (992135058231/1000000000000 : ℝ) (198427011647/200000000000 : ℝ) (992135058231/1000000000000 : ℝ) (198427011647/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (1037/8192 : ℝ))) (17649705867/100000000000 : ℝ) (44124264669/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (1037/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (17649705867/100000000000 : ℝ) (44124264669/250000000000 : ℝ) (117649705867/200000000000 : ℝ) (294124264669/500000000000 : ℝ) (210057765073/500000000000 : ℝ) (210057765077/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (1037/8192 : ℝ))) 1 (117649705867/200000000000 : ℝ) (294124264669/500000000000 : ℝ) (210057765073/500000000000 : ℝ) (210057765077/500000000000 : ℝ) (25209101487/50000000000 : ℝ) (252091014873/500000000000 : ℝ) (124281017949/250000000000 : ℝ) (497124071803/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (1037/8192 : ℝ))) 2 (25209101487/50000000000 : ℝ) (252091014873/500000000000 : ℝ) (124281017949/250000000000 : ℝ) (497124071803/1000000000000 : ℝ) (31290815673/62500000000 : ℝ) (20026122031/40000000000 : ℝ) (100128122633/200000000000 : ℝ) (125160153293/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (1037/8192 : ℝ))) 3 (31290815673/62500000000 : ℝ) (20026122031/40000000000 : ℝ) (100128122633/200000000000 : ℝ) (125160153293/250000000000 : ℝ) (250323415983/500000000000 : ℝ) (250323415987/500000000000 : ℝ) (500646831927/1000000000000 : ℝ) (100129366387/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (1037/8192 : ℝ))) 4 (250323415983/500000000000 : ℝ) (250323415987/500000000000 : ℝ) (500646831927/1000000000000 : ℝ) (100129366387/200000000000 : ℝ) (250323415973/500000000000 : ℝ) (100129366391/200000000000 : ℝ) (250323415973/500000000000 : ℝ) (100129366391/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (1037/8192 : ℝ))) 5 (250323415973/500000000000 : ℝ) (100129366391/200000000000 : ℝ) (250323415973/500000000000 : ℝ) (100129366391/200000000000 : ℝ) (250323415973/500000000000 : ℝ) (100129366391/200000000000 : ℝ) (250323415973/500000000000 : ℝ) (100129366391/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (1037/8192 : ℝ))) 6 (250323415973/500000000000 : ℝ) (100129366391/200000000000 : ℝ) (250323415973/500000000000 : ℝ) (100129366391/200000000000 : ℝ) (250323415973/500000000000 : ℝ) (100129366391/200000000000 : ℝ) (250323415973/500000000000 : ℝ) (100129366391/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (1037/8192 : ℝ))) 7 (250323415973/500000000000 : ℝ) (100129366391/200000000000 : ℝ) (250323415973/500000000000 : ℝ) (100129366391/200000000000 : ℝ) (250323415973/500000000000 : ℝ) (100129366391/200000000000 : ℝ) (250323415973/500000000000 : ℝ) (100129366391/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (1037/8192 : ℝ)) hmem 8 (992135058231/1000000000000 : ℝ) (198427011647/200000000000 : ℝ) (992135058231/1000000000000 : ℝ) (198427011647/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (1037/8192 : ℝ))) hcmem 8 (250323415973/500000000000 : ℝ) (100129366391/200000000000 : ℝ) (250323415973/500000000000 : ℝ) (100129366391/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (1037/8192 : ℝ)) (992135058231/1000000000000 : ℝ) (198427011647/200000000000 : ℝ) (250323415973/500000000000 : ℝ) (100129366391/200000000000 : ℝ) (396324168829/500000000000 : ℝ) (198162084419/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0403_exp_lower
  have heNumeric : (1027451991041/500000000000 : ℝ)/4 ≤ Real.exp (-42628175251889/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451991041/500000000000 : ℝ)/4 ≤ Real.exp ((33183/262144 : ℝ)-(198162084419/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33183/262144 : ℝ) (1037/8192 : ℝ) (198162084419/250000000000 : ℝ) (1027451991041/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0404; no trusted numerical premise.
theorem cover8_leaf0404_exp_radius : (124752996847087553/125000000000000000 : ℝ) ≤ Real.exp ((-33185/2097152 : ℝ)/8) ∧ Real.exp ((-33185/2097152 : ℝ)/8) ≤ (39920958991068017/40000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33185/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0404_exp_lower : (920113582302242547/1000000000000000000 : ℝ) ≤ Real.exp ((-266426104113/400000000000 : ℝ)/8) ∧ Real.exp ((-266426104113/400000000000 : ℝ)/8) ≤ (230028395575560637/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-266426104113/400000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0404_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513725984233/250000000000 : ℝ) ≤ 4*Real.exp (1037/8192 : ℝ)*Real.exp (-mu (radius 8 (33185/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (513725984233/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33185/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0404_exp_radius
  have hrNumeric : (246075174529/250000000000 : ℝ) ≤ Real.exp (-33185/2097152 : ℝ) ∧ Real.exp (-33185/2097152 : ℝ) ≤ (984300698117/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246075174529/250000000000 : ℝ) ≤ (radius 8 (33185/262144 : ℝ)) ∧ (radius 8 (33185/262144 : ℝ)) ≤ (984300698117/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33185/262144 : ℝ)) (246075174529/250000000000 : ℝ) (984300698117/1000000000000 : ℝ) (35299935233/200000000000 : ℝ) (176499676171/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33185/262144 : ℝ)) (246075174529/250000000000 : ℝ) (984300698117/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33185/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246075174529/250000000000 : ℝ) (984300698117/1000000000000 : ℝ) (496075174529/500000000000 : ℝ) (992150349059/1000000000000 : ℝ) (124014912039/125000000000 : ℝ) (496059648157/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33185/262144 : ℝ)) 1 (496075174529/500000000000 : ℝ) (992150349059/1000000000000 : ℝ) (124014912039/125000000000 : ℝ) (496059648157/500000000000 : ℝ) (198426964537/200000000000 : ℝ) (992134822687/1000000000000 : ℝ) (992134822563/1000000000000 : ℝ) (496067411283/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33185/262144 : ℝ)) 2 (198426964537/200000000000 : ℝ) (992134822687/1000000000000 : ℝ) (992134822563/1000000000000 : ℝ) (496067411283/500000000000 : ℝ) (31004213207/31250000000 : ℝ) (992134822627/1000000000000 : ℝ) (992134822623/1000000000000 : ℝ) (992134822627/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33185/262144 : ℝ)) 3 (31004213207/31250000000 : ℝ) (992134822627/1000000000000 : ℝ) (992134822623/1000000000000 : ℝ) (992134822627/1000000000000 : ℝ) (992134822623/1000000000000 : ℝ) (992134822627/1000000000000 : ℝ) (992134822623/1000000000000 : ℝ) (992134822627/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33185/262144 : ℝ)) 4 (992134822623/1000000000000 : ℝ) (992134822627/1000000000000 : ℝ) (992134822623/1000000000000 : ℝ) (992134822627/1000000000000 : ℝ) (992134822623/1000000000000 : ℝ) (992134822627/1000000000000 : ℝ) (992134822623/1000000000000 : ℝ) (992134822627/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33185/262144 : ℝ)) 5 (992134822623/1000000000000 : ℝ) (992134822627/1000000000000 : ℝ) (992134822623/1000000000000 : ℝ) (992134822627/1000000000000 : ℝ) (992134822623/1000000000000 : ℝ) (992134822627/1000000000000 : ℝ) (992134822623/1000000000000 : ℝ) (992134822627/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33185/262144 : ℝ)) 6 (992134822623/1000000000000 : ℝ) (992134822627/1000000000000 : ℝ) (992134822623/1000000000000 : ℝ) (992134822627/1000000000000 : ℝ) (992134822623/1000000000000 : ℝ) (992134822627/1000000000000 : ℝ) (992134822623/1000000000000 : ℝ) (992134822627/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33185/262144 : ℝ)) 7 (992134822623/1000000000000 : ℝ) (992134822627/1000000000000 : ℝ) (992134822623/1000000000000 : ℝ) (992134822627/1000000000000 : ℝ) (992134822623/1000000000000 : ℝ) (992134822627/1000000000000 : ℝ) (992134822623/1000000000000 : ℝ) (992134822627/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33185/262144 : ℝ))) (35299935233/200000000000 : ℝ) (176499676171/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33185/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35299935233/200000000000 : ℝ) (176499676171/1000000000000 : ℝ) (294124919041/500000000000 : ℝ) (294124919043/500000000000 : ℝ) (420118645343/1000000000000 : ℝ) (420118645351/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33185/262144 : ℝ))) 1 (294124919041/500000000000 : ℝ) (294124919043/500000000000 : ℝ) (420118645343/1000000000000 : ℝ) (420118645351/1000000000000 : ℝ) (31511515107/62500000000 : ℝ) (504184241719/1000000000000 : ℝ) (497126467911/1000000000000 : ℝ) (497126467919/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33185/262144 : ℝ))) 2 (31511515107/62500000000 : ℝ) (504184241719/1000000000000 : ℝ) (497126467911/1000000000000 : ℝ) (497126467919/1000000000000 : ℝ) (500655354811/1000000000000 : ℝ) (500655354819/1000000000000 : ℝ) (100128583583/200000000000 : ℝ) (500642917923/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33185/262144 : ℝ))) 3 (500655354811/1000000000000 : ℝ) (500655354819/1000000000000 : ℝ) (100128583583/200000000000 : ℝ) (500642917923/1000000000000 : ℝ) (500649136363/1000000000000 : ℝ) (500649136371/1000000000000 : ℝ) (125162284081/250000000000 : ℝ) (500649136333/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33185/262144 : ℝ))) 4 (500649136363/1000000000000 : ℝ) (500649136371/1000000000000 : ℝ) (125162284081/250000000000 : ℝ) (500649136333/1000000000000 : ℝ) (500649136343/1000000000000 : ℝ) (15645285511/31250000000 : ℝ) (500649136343/1000000000000 : ℝ) (15645285511/31250000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33185/262144 : ℝ))) 5 (500649136343/1000000000000 : ℝ) (15645285511/31250000000 : ℝ) (500649136343/1000000000000 : ℝ) (15645285511/31250000000 : ℝ) (500649136343/1000000000000 : ℝ) (15645285511/31250000000 : ℝ) (500649136343/1000000000000 : ℝ) (15645285511/31250000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33185/262144 : ℝ))) 6 (500649136343/1000000000000 : ℝ) (15645285511/31250000000 : ℝ) (500649136343/1000000000000 : ℝ) (15645285511/31250000000 : ℝ) (500649136343/1000000000000 : ℝ) (15645285511/31250000000 : ℝ) (500649136343/1000000000000 : ℝ) (15645285511/31250000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33185/262144 : ℝ))) 7 (500649136343/1000000000000 : ℝ) (15645285511/31250000000 : ℝ) (500649136343/1000000000000 : ℝ) (15645285511/31250000000 : ℝ) (500649136343/1000000000000 : ℝ) (15645285511/31250000000 : ℝ) (500649136343/1000000000000 : ℝ) (15645285511/31250000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33185/262144 : ℝ)) hmem 8 (992134822623/1000000000000 : ℝ) (992134822627/1000000000000 : ℝ) (992134822623/1000000000000 : ℝ) (992134822627/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33185/262144 : ℝ))) hcmem 8 (500649136343/1000000000000 : ℝ) (15645285511/31250000000 : ℝ) (500649136343/1000000000000 : ℝ) (15645285511/31250000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33185/262144 : ℝ)) (992134822623/1000000000000 : ℝ) (992134822627/1000000000000 : ℝ) (500649136343/1000000000000 : ℝ) (15645285511/31250000000 : ℝ) (396326087163/500000000000 : ℝ) (158530434869/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0404_exp_lower
  have heNumeric : (513725984233/250000000000 : ℝ)/4 ≤ Real.exp (-266426104113/400000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513725984233/250000000000 : ℝ)/4 ≤ Real.exp ((1037/8192 : ℝ)-(158530434869/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (1037/8192 : ℝ) (33185/262144 : ℝ) (158530434869/200000000000 : ℝ) (513725984233/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0405; no trusted numerical premise.
theorem cover8_leaf0405_exp_radius : (998023915289837703/1000000000000000000 : ℝ) ≤ Real.exp ((-16593/1048576 : ℝ)/8) ∧ Real.exp ((-16593/1048576 : ℝ)/8) ≤ (124752989411229713/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16593/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0405_exp_lower : (46005678989242117/50000000000000000 : ℝ) ≤ Real.exp ((-8525635611779/12800000000000 : ℝ)/8) ∧ Real.exp ((-8525635611779/12800000000000 : ℝ)/8) ≤ (920113579784842341/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8525635611779/12800000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0405_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410980778391/200000000000 : ℝ) ≤ 4*Real.exp (33185/262144 : ℝ)*Real.exp (-mu (radius 8 (16593/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (410980778391/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16593/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0405_exp_radius
  have hrNumeric : (196860045753/200000000000 : ℝ) ≤ Real.exp (-16593/1048576 : ℝ) ∧ Real.exp (-16593/1048576 : ℝ) ≤ (492150114383/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196860045753/200000000000 : ℝ) ≤ (radius 8 (16593/131072 : ℝ)) ∧ (radius 8 (16593/131072 : ℝ)) ≤ (492150114383/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16593/131072 : ℝ)) (196860045753/200000000000 : ℝ) (492150114383/500000000000 : ℝ) (88251146807/500000000000 : ℝ) (176502293621/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16593/131072 : ℝ)) (196860045753/200000000000 : ℝ) (492150114383/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16593/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196860045753/200000000000 : ℝ) (492150114383/500000000000 : ℝ) (496075057191/500000000000 : ℝ) (992150114383/1000000000000 : ℝ) (992119059773/1000000000000 : ℝ) (496059529887/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16593/131072 : ℝ)) 1 (496075057191/500000000000 : ℝ) (992150114383/1000000000000 : ℝ) (992119059773/1000000000000 : ℝ) (496059529887/500000000000 : ℝ) (992134587077/1000000000000 : ℝ) (992134587079/1000000000000 : ℝ) (198426917391/200000000000 : ℝ) (992134586957/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16593/131072 : ℝ)) 2 (992134587077/1000000000000 : ℝ) (992134587079/1000000000000 : ℝ) (198426917391/200000000000 : ℝ) (992134586957/1000000000000 : ℝ) (124016823377/125000000000 : ℝ) (496067293509/500000000000 : ℝ) (198426917403/200000000000 : ℝ) (496067293509/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16593/131072 : ℝ)) 3 (124016823377/125000000000 : ℝ) (496067293509/500000000000 : ℝ) (198426917403/200000000000 : ℝ) (496067293509/500000000000 : ℝ) (198426917403/200000000000 : ℝ) (496067293509/500000000000 : ℝ) (198426917403/200000000000 : ℝ) (496067293509/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16593/131072 : ℝ)) 4 (198426917403/200000000000 : ℝ) (496067293509/500000000000 : ℝ) (198426917403/200000000000 : ℝ) (496067293509/500000000000 : ℝ) (198426917403/200000000000 : ℝ) (496067293509/500000000000 : ℝ) (198426917403/200000000000 : ℝ) (496067293509/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16593/131072 : ℝ)) 5 (198426917403/200000000000 : ℝ) (496067293509/500000000000 : ℝ) (198426917403/200000000000 : ℝ) (496067293509/500000000000 : ℝ) (198426917403/200000000000 : ℝ) (496067293509/500000000000 : ℝ) (198426917403/200000000000 : ℝ) (496067293509/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16593/131072 : ℝ)) 6 (198426917403/200000000000 : ℝ) (496067293509/500000000000 : ℝ) (198426917403/200000000000 : ℝ) (496067293509/500000000000 : ℝ) (198426917403/200000000000 : ℝ) (496067293509/500000000000 : ℝ) (198426917403/200000000000 : ℝ) (496067293509/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16593/131072 : ℝ)) 7 (198426917403/200000000000 : ℝ) (496067293509/500000000000 : ℝ) (198426917403/200000000000 : ℝ) (496067293509/500000000000 : ℝ) (198426917403/200000000000 : ℝ) (496067293509/500000000000 : ℝ) (198426917403/200000000000 : ℝ) (496067293509/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16593/131072 : ℝ))) (88251146807/500000000000 : ℝ) (176502293621/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16593/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88251146807/500000000000 : ℝ) (176502293621/1000000000000 : ℝ) (588251146807/1000000000000 : ℝ) (588251146811/1000000000000 : ℝ) (210060880231/500000000000 : ℝ) (420121760471/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16593/131072 : ℝ))) 1 (588251146807/1000000000000 : ℝ) (588251146811/1000000000000 : ℝ) (210060880231/500000000000 : ℝ) (420121760471/1000000000000 : ℝ) (252093226817/500000000000 : ℝ) (504186453641/1000000000000 : ℝ) (15535276999/31250000000 : ℝ) (62141107997/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16593/131072 : ℝ))) 2 (252093226817/500000000000 : ℝ) (504186453641/1000000000000 : ℝ) (15535276999/31250000000 : ℝ) (62141107997/125000000000 : ℝ) (500657658801/1000000000000 : ℝ) (500657658809/1000000000000 : ℝ) (50064522261/100000000000 : ℝ) (500645222619/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16593/131072 : ℝ))) 3 (500657658801/1000000000000 : ℝ) (500657658809/1000000000000 : ℝ) (50064522261/100000000000 : ℝ) (500645222619/1000000000000 : ℝ) (100130288141/200000000000 : ℝ) (250325720357/500000000000 : ℝ) (250325720333/500000000000 : ℝ) (125162860169/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16593/131072 : ℝ))) 4 (100130288141/200000000000 : ℝ) (250325720357/500000000000 : ℝ) (250325720333/500000000000 : ℝ) (125162860169/250000000000 : ℝ) (100130288137/200000000000 : ℝ) (100130288139/200000000000 : ℝ) (100130288137/200000000000 : ℝ) (100130288139/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16593/131072 : ℝ))) 5 (100130288137/200000000000 : ℝ) (100130288139/200000000000 : ℝ) (100130288137/200000000000 : ℝ) (100130288139/200000000000 : ℝ) (100130288137/200000000000 : ℝ) (100130288139/200000000000 : ℝ) (100130288137/200000000000 : ℝ) (100130288139/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16593/131072 : ℝ))) 6 (100130288137/200000000000 : ℝ) (100130288139/200000000000 : ℝ) (100130288137/200000000000 : ℝ) (100130288139/200000000000 : ℝ) (100130288137/200000000000 : ℝ) (100130288139/200000000000 : ℝ) (100130288137/200000000000 : ℝ) (100130288139/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16593/131072 : ℝ))) 7 (100130288137/200000000000 : ℝ) (100130288139/200000000000 : ℝ) (100130288137/200000000000 : ℝ) (100130288139/200000000000 : ℝ) (100130288137/200000000000 : ℝ) (100130288139/200000000000 : ℝ) (100130288137/200000000000 : ℝ) (100130288139/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16593/131072 : ℝ)) hmem 8 (198426917403/200000000000 : ℝ) (496067293509/500000000000 : ℝ) (198426917403/200000000000 : ℝ) (496067293509/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16593/131072 : ℝ))) hcmem 8 (100130288137/200000000000 : ℝ) (100130288139/200000000000 : ℝ) (100130288137/200000000000 : ℝ) (100130288139/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16593/131072 : ℝ)) (198426917403/200000000000 : ℝ) (496067293509/500000000000 : ℝ) (100130288137/200000000000 : ℝ) (100130288139/200000000000 : ℝ) (792656010911/1000000000000 : ℝ) (79265601093/100000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0405_exp_lower
  have heNumeric : (410980778391/200000000000 : ℝ)/4 ≤ Real.exp (-8525635611779/12800000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410980778391/200000000000 : ℝ)/4 ≤ Real.exp ((33185/262144 : ℝ)-(79265601093/100000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33185/262144 : ℝ) (16593/131072 : ℝ) (79265601093/100000000000 : ℝ) (410980778391/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0406; no trusted numerical premise.
theorem cover8_leaf0406_exp_radius : (31188245493843079/31250000000000000 : ℝ) ≤ Real.exp ((-33187/2097152 : ℝ)/8) ∧ Real.exp ((-33187/2097152 : ℝ)/8) ≤ (998023855802978529/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33187/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0406_exp_lower : (920113577277333361/1000000000000000000 : ℝ) ≤ Real.exp ((-21314089727103/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314089727103/32000000000000 : ℝ)/8) ≤ (460056788638666681/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314089727103/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0406_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451923577/500000000000 : ℝ) ≤ 4*Real.exp (16593/131072 : ℝ)*Real.exp (-mu (radius 8 (33187/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451923577/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33187/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0406_exp_radius
  have hrNumeric : (196859951883/200000000000 : ℝ) ≤ Real.exp (-33187/2097152 : ℝ) ∧ Real.exp (-33187/2097152 : ℝ) ≤ (123037469927/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196859951883/200000000000 : ℝ) ≤ (radius 8 (33187/262144 : ℝ)) ∧ (radius 8 (33187/262144 : ℝ)) ≤ (123037469927/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33187/262144 : ℝ)) (196859951883/200000000000 : ℝ) (123037469927/125000000000 : ℝ) (88252455509/500000000000 : ℝ) (11031556939/62500000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33187/262144 : ℝ)) (196859951883/200000000000 : ℝ) (123037469927/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33187/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196859951883/200000000000 : ℝ) (123037469927/125000000000 : ℝ) (992149879707/1000000000000 : ℝ) (248037469927/250000000000 : ℝ) (992118823233/1000000000000 : ℝ) (198423764647/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33187/262144 : ℝ)) 1 (992149879707/1000000000000 : ℝ) (248037469927/250000000000 : ℝ) (992118823233/1000000000000 : ℝ) (198423764647/200000000000 : ℝ) (99213435147/100000000000 : ℝ) (62008396967/62500000000 : ℝ) (248033587837/250000000000 : ℝ) (19842687027/20000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33187/262144 : ℝ)) 2 (99213435147/100000000000 : ℝ) (62008396967/62500000000 : ℝ) (248033587837/250000000000 : ℝ) (19842687027/20000000000 : ℝ) (992134351409/1000000000000 : ℝ) (992134351411/1000000000000 : ℝ) (62008396963/62500000000 : ℝ) (992134351411/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33187/262144 : ℝ)) 3 (992134351409/1000000000000 : ℝ) (992134351411/1000000000000 : ℝ) (62008396963/62500000000 : ℝ) (992134351411/1000000000000 : ℝ) (62008396963/62500000000 : ℝ) (992134351411/1000000000000 : ℝ) (62008396963/62500000000 : ℝ) (992134351411/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33187/262144 : ℝ)) 4 (62008396963/62500000000 : ℝ) (992134351411/1000000000000 : ℝ) (62008396963/62500000000 : ℝ) (992134351411/1000000000000 : ℝ) (62008396963/62500000000 : ℝ) (992134351411/1000000000000 : ℝ) (62008396963/62500000000 : ℝ) (992134351411/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33187/262144 : ℝ)) 5 (62008396963/62500000000 : ℝ) (992134351411/1000000000000 : ℝ) (62008396963/62500000000 : ℝ) (992134351411/1000000000000 : ℝ) (62008396963/62500000000 : ℝ) (992134351411/1000000000000 : ℝ) (62008396963/62500000000 : ℝ) (992134351411/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33187/262144 : ℝ)) 6 (62008396963/62500000000 : ℝ) (992134351411/1000000000000 : ℝ) (62008396963/62500000000 : ℝ) (992134351411/1000000000000 : ℝ) (62008396963/62500000000 : ℝ) (992134351411/1000000000000 : ℝ) (62008396963/62500000000 : ℝ) (992134351411/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33187/262144 : ℝ)) 7 (62008396963/62500000000 : ℝ) (992134351411/1000000000000 : ℝ) (62008396963/62500000000 : ℝ) (992134351411/1000000000000 : ℝ) (62008396963/62500000000 : ℝ) (992134351411/1000000000000 : ℝ) (62008396963/62500000000 : ℝ) (992134351411/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33187/262144 : ℝ))) (88252455509/500000000000 : ℝ) (11031556939/62500000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33187/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88252455509/500000000000 : ℝ) (11031556939/62500000000 : ℝ) (588252455509/1000000000000 : ℝ) (73531556939/125000000000 : ℝ) (26257804719/62500000000 : ℝ) (420124875513/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33187/262144 : ℝ))) 1 (588252455509/1000000000000 : ℝ) (73531556939/125000000000 : ℝ) (26257804719/62500000000 : ℝ) (420124875513/1000000000000 : ℝ) (252094332753/500000000000 : ℝ) (504188665513/1000000000000 : ℝ) (248565629983/500000000000 : ℝ) (497131259973/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33187/262144 : ℝ))) 2 (252094332753/500000000000 : ℝ) (504188665513/1000000000000 : ℝ) (248565629983/500000000000 : ℝ) (497131259973/1000000000000 : ℝ) (31291247671/62500000000 : ℝ) (500659962743/1000000000000 : ℝ) (125161881813/250000000000 : ℝ) (25032376363/50000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33187/262144 : ℝ))) 3 (31291247671/62500000000 : ℝ) (500659962743/1000000000000 : ℝ) (125161881813/250000000000 : ℝ) (25032376363/50000000000 : ℝ) (250326872497/500000000000 : ℝ) (250326872501/500000000000 : ℝ) (100130748991/200000000000 : ℝ) (500653744963/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33187/262144 : ℝ))) 4 (250326872497/500000000000 : ℝ) (250326872501/500000000000 : ℝ) (100130748991/200000000000 : ℝ) (500653744963/1000000000000 : ℝ) (250326872487/500000000000 : ℝ) (500653744983/1000000000000 : ℝ) (250326872487/500000000000 : ℝ) (500653744983/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33187/262144 : ℝ))) 5 (250326872487/500000000000 : ℝ) (500653744983/1000000000000 : ℝ) (250326872487/500000000000 : ℝ) (500653744983/1000000000000 : ℝ) (250326872487/500000000000 : ℝ) (500653744983/1000000000000 : ℝ) (250326872487/500000000000 : ℝ) (500653744983/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33187/262144 : ℝ))) 6 (250326872487/500000000000 : ℝ) (500653744983/1000000000000 : ℝ) (250326872487/500000000000 : ℝ) (500653744983/1000000000000 : ℝ) (250326872487/500000000000 : ℝ) (500653744983/1000000000000 : ℝ) (250326872487/500000000000 : ℝ) (500653744983/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33187/262144 : ℝ))) 7 (250326872487/500000000000 : ℝ) (500653744983/1000000000000 : ℝ) (250326872487/500000000000 : ℝ) (500653744983/1000000000000 : ℝ) (250326872487/500000000000 : ℝ) (500653744983/1000000000000 : ℝ) (250326872487/500000000000 : ℝ) (500653744983/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33187/262144 : ℝ)) hmem 8 (62008396963/62500000000 : ℝ) (992134351411/1000000000000 : ℝ) (62008396963/62500000000 : ℝ) (992134351411/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33187/262144 : ℝ))) hcmem 8 (250326872487/500000000000 : ℝ) (500653744983/1000000000000 : ℝ) (250326872487/500000000000 : ℝ) (500653744983/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33187/262144 : ℝ)) (62008396963/62500000000 : ℝ) (992134351411/1000000000000 : ℝ) (250326872487/500000000000 : ℝ) (500653744983/1000000000000 : ℝ) (792659847411/1000000000000 : ℝ) (792659847429/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0406_exp_lower
  have heNumeric : (1027451923577/500000000000 : ℝ)/4 ≤ Real.exp (-21314089727103/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451923577/500000000000 : ℝ)/4 ≤ Real.exp ((16593/131072 : ℝ)-(792659847429/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16593/131072 : ℝ) (33187/262144 : ℝ) (792659847429/1000000000000 : ℝ) (1027451923577/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0407; no trusted numerical premise.
theorem cover8_leaf0407_exp_radius : (499011898158061449/500000000000000000 : ℝ) ≤ Real.exp ((-8297/524288 : ℝ)/8) ∧ Real.exp ((-8297/524288 : ℝ)/8) ≤ (998023796316122899/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8297/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0407_exp_lower : (460056787388937691/500000000000000000 : ℝ) ≤ Real.exp ((-42628180845037/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628180845037/64000000000000 : ℝ)/8) ≤ (920113574777875383/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628180845037/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0407_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451901249/500000000000 : ℝ) ≤ 4*Real.exp (33187/262144 : ℝ)*Real.exp (-mu (radius 8 (8297/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451901249/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8297/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0407_exp_radius
  have hrNumeric : (61518705629/62500000000 : ℝ) ≤ Real.exp (-8297/524288 : ℝ) ∧ Real.exp (-8297/524288 : ℝ) ≤ (196859858013/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (61518705629/62500000000 : ℝ) ≤ (radius 8 (8297/65536 : ℝ)) ∧ (radius 8 (8297/65536 : ℝ)) ≤ (196859858013/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8297/65536 : ℝ)) (61518705629/62500000000 : ℝ) (196859858013/200000000000 : ℝ) (176507528387/1000000000000 : ℝ) (88253764197/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8297/65536 : ℝ)) (61518705629/62500000000 : ℝ) (196859858013/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8297/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (61518705629/62500000000 : ℝ) (196859858013/200000000000 : ℝ) (124018705629/125000000000 : ℝ) (992149645033/1000000000000 : ℝ) (496059293347/500000000000 : ℝ) (198423717339/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8297/65536 : ℝ)) 1 (124018705629/125000000000 : ℝ) (992149645033/1000000000000 : ℝ) (496059293347/500000000000 : ℝ) (198423717339/200000000000 : ℝ) (992134115863/1000000000000 : ℝ) (124016764483/125000000000 : ℝ) (992134115741/1000000000000 : ℝ) (992134115743/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8297/65536 : ℝ)) 2 (992134115863/1000000000000 : ℝ) (124016764483/125000000000 : ℝ) (992134115741/1000000000000 : ℝ) (992134115743/1000000000000 : ℝ) (496067057901/500000000000 : ℝ) (248033528951/250000000000 : ℝ) (992134115801/1000000000000 : ℝ) (248033528951/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8297/65536 : ℝ)) 3 (496067057901/500000000000 : ℝ) (248033528951/250000000000 : ℝ) (992134115801/1000000000000 : ℝ) (248033528951/250000000000 : ℝ) (992134115801/1000000000000 : ℝ) (248033528951/250000000000 : ℝ) (992134115801/1000000000000 : ℝ) (248033528951/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8297/65536 : ℝ)) 4 (992134115801/1000000000000 : ℝ) (248033528951/250000000000 : ℝ) (992134115801/1000000000000 : ℝ) (248033528951/250000000000 : ℝ) (992134115801/1000000000000 : ℝ) (248033528951/250000000000 : ℝ) (992134115801/1000000000000 : ℝ) (248033528951/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8297/65536 : ℝ)) 5 (992134115801/1000000000000 : ℝ) (248033528951/250000000000 : ℝ) (992134115801/1000000000000 : ℝ) (248033528951/250000000000 : ℝ) (992134115801/1000000000000 : ℝ) (248033528951/250000000000 : ℝ) (992134115801/1000000000000 : ℝ) (248033528951/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8297/65536 : ℝ)) 6 (992134115801/1000000000000 : ℝ) (248033528951/250000000000 : ℝ) (992134115801/1000000000000 : ℝ) (248033528951/250000000000 : ℝ) (992134115801/1000000000000 : ℝ) (248033528951/250000000000 : ℝ) (992134115801/1000000000000 : ℝ) (248033528951/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8297/65536 : ℝ)) 7 (992134115801/1000000000000 : ℝ) (248033528951/250000000000 : ℝ) (992134115801/1000000000000 : ℝ) (248033528951/250000000000 : ℝ) (992134115801/1000000000000 : ℝ) (248033528951/250000000000 : ℝ) (992134115801/1000000000000 : ℝ) (248033528951/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8297/65536 : ℝ))) (176507528387/1000000000000 : ℝ) (88253764197/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8297/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176507528387/1000000000000 : ℝ) (88253764197/500000000000 : ℝ) (588253764193/1000000000000 : ℝ) (588253764197/1000000000000 : ℝ) (210063995241/500000000000 : ℝ) (420127990491/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8297/65536 : ℝ))) 1 (588253764193/1000000000000 : ℝ) (588253764197/1000000000000 : ℝ) (210063995241/500000000000 : ℝ) (420127990491/1000000000000 : ℝ) (504190877337/1000000000000 : ℝ) (15755964917/31250000000 : ℝ) (99426731183/200000000000 : ℝ) (497133655923/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8297/65536 : ℝ))) 2 (504190877337/1000000000000 : ℝ) (15755964917/31250000000 : ℝ) (99426731183/200000000000 : ℝ) (497133655923/1000000000000 : ℝ) (250331133313/500000000000 : ℝ) (250331133317/500000000000 : ℝ) (62581228981/125000000000 : ℝ) (31290614491/62500000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8297/65536 : ℝ))) 3 (250331133313/500000000000 : ℝ) (250331133317/500000000000 : ℝ) (62581228981/125000000000 : ℝ) (31290614491/62500000000 : ℝ) (500656049237/1000000000000 : ℝ) (100131209849/200000000000 : ℝ) (250328024599/500000000000 : ℝ) (500656049207/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8297/65536 : ℝ))) 4 (500656049237/1000000000000 : ℝ) (100131209849/200000000000 : ℝ) (250328024599/500000000000 : ℝ) (500656049207/1000000000000 : ℝ) (500656049217/1000000000000 : ℝ) (250328024613/500000000000 : ℝ) (500656049217/1000000000000 : ℝ) (250328024613/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8297/65536 : ℝ))) 5 (500656049217/1000000000000 : ℝ) (250328024613/500000000000 : ℝ) (500656049217/1000000000000 : ℝ) (250328024613/500000000000 : ℝ) (500656049217/1000000000000 : ℝ) (250328024613/500000000000 : ℝ) (500656049217/1000000000000 : ℝ) (250328024613/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8297/65536 : ℝ))) 6 (500656049217/1000000000000 : ℝ) (250328024613/500000000000 : ℝ) (500656049217/1000000000000 : ℝ) (250328024613/500000000000 : ℝ) (500656049217/1000000000000 : ℝ) (250328024613/500000000000 : ℝ) (500656049217/1000000000000 : ℝ) (250328024613/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8297/65536 : ℝ))) 7 (500656049217/1000000000000 : ℝ) (250328024613/500000000000 : ℝ) (500656049217/1000000000000 : ℝ) (250328024613/500000000000 : ℝ) (500656049217/1000000000000 : ℝ) (250328024613/500000000000 : ℝ) (500656049217/1000000000000 : ℝ) (250328024613/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8297/65536 : ℝ)) hmem 8 (992134115801/1000000000000 : ℝ) (248033528951/250000000000 : ℝ) (992134115801/1000000000000 : ℝ) (248033528951/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8297/65536 : ℝ))) hcmem 8 (500656049217/1000000000000 : ℝ) (250328024613/500000000000 : ℝ) (500656049217/1000000000000 : ℝ) (250328024613/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8297/65536 : ℝ)) (992134115801/1000000000000 : ℝ) (248033528951/250000000000 : ℝ) (500656049217/1000000000000 : ℝ) (250328024613/500000000000 : ℝ) (792663683841/1000000000000 : ℝ) (396331841929/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0407_exp_lower
  have heNumeric : (1027451901249/500000000000 : ℝ)/4 ≤ Real.exp (-42628180845037/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451901249/500000000000 : ℝ)/4 ≤ Real.exp ((33187/262144 : ℝ)-(396331841929/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33187/262144 : ℝ) (8297/65536 : ℝ) (396331841929/500000000000 : ℝ) (1027451901249/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0408; no trusted numerical premise.
theorem cover8_leaf0408_exp_radius : (499011868414635407/500000000000000000 : ℝ) ≤ Real.exp ((-33189/2097152 : ℝ)/8) ∧ Real.exp ((-33189/2097152 : ℝ)/8) ≤ (199604747365854163/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33189/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0408_exp_lower : (460056786143924287/500000000000000000 : ℝ) ≤ Real.exp ((-2131409111531/3200000000000 : ℝ)/8) ∧ Real.exp ((-2131409111531/3200000000000 : ℝ)/8) ≤ (36804542891513943/40000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2131409111531/3200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0408_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (205490375801/100000000000 : ℝ) ≤ 4*Real.exp (8297/65536 : ℝ)*Real.exp (-mu (radius 8 (33189/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (205490375801/100000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33189/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0408_exp_radius
  have hrNumeric : (492149410357/500000000000 : ℝ) ≤ Real.exp (-33189/2097152 : ℝ) ∧ Real.exp (-33189/2097152 : ℝ) ≤ (196859764143/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492149410357/500000000000 : ℝ) ≤ (radius 8 (33189/262144 : ℝ)) ∧ (radius 8 (33189/262144 : ℝ)) ≤ (196859764143/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33189/262144 : ℝ)) (492149410357/500000000000 : ℝ) (196859764143/200000000000 : ℝ) (176510145711/1000000000000 : ℝ) (176510145717/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33189/262144 : ℝ)) (492149410357/500000000000 : ℝ) (196859764143/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33189/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492149410357/500000000000 : ℝ) (196859764143/200000000000 : ℝ) (992149410357/1000000000000 : ℝ) (496074705179/500000000000 : ℝ) (496059175077/500000000000 : ℝ) (248029587539/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33189/262144 : ℝ)) 1 (992149410357/1000000000000 : ℝ) (496074705179/500000000000 : ℝ) (496059175077/500000000000 : ℝ) (248029587539/250000000000 : ℝ) (198426776051/200000000000 : ℝ) (992133880257/1000000000000 : ℝ) (992133880133/1000000000000 : ℝ) (124016735017/125000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33189/262144 : ℝ)) 2 (198426776051/200000000000 : ℝ) (992133880257/1000000000000 : ℝ) (992133880133/1000000000000 : ℝ) (124016735017/125000000000 : ℝ) (496066940097/500000000000 : ℝ) (992133880197/1000000000000 : ℝ) (992133880193/1000000000000 : ℝ) (992133880197/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33189/262144 : ℝ)) 3 (496066940097/500000000000 : ℝ) (992133880197/1000000000000 : ℝ) (992133880193/1000000000000 : ℝ) (992133880197/1000000000000 : ℝ) (992133880193/1000000000000 : ℝ) (992133880197/1000000000000 : ℝ) (992133880193/1000000000000 : ℝ) (992133880197/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33189/262144 : ℝ)) 4 (992133880193/1000000000000 : ℝ) (992133880197/1000000000000 : ℝ) (992133880193/1000000000000 : ℝ) (992133880197/1000000000000 : ℝ) (992133880193/1000000000000 : ℝ) (992133880197/1000000000000 : ℝ) (992133880193/1000000000000 : ℝ) (992133880197/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33189/262144 : ℝ)) 5 (992133880193/1000000000000 : ℝ) (992133880197/1000000000000 : ℝ) (992133880193/1000000000000 : ℝ) (992133880197/1000000000000 : ℝ) (992133880193/1000000000000 : ℝ) (992133880197/1000000000000 : ℝ) (992133880193/1000000000000 : ℝ) (992133880197/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33189/262144 : ℝ)) 6 (992133880193/1000000000000 : ℝ) (992133880197/1000000000000 : ℝ) (992133880193/1000000000000 : ℝ) (992133880197/1000000000000 : ℝ) (992133880193/1000000000000 : ℝ) (992133880197/1000000000000 : ℝ) (992133880193/1000000000000 : ℝ) (992133880197/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33189/262144 : ℝ)) 7 (992133880193/1000000000000 : ℝ) (992133880197/1000000000000 : ℝ) (992133880193/1000000000000 : ℝ) (992133880197/1000000000000 : ℝ) (992133880193/1000000000000 : ℝ) (992133880197/1000000000000 : ℝ) (992133880193/1000000000000 : ℝ) (992133880197/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33189/262144 : ℝ))) (176510145711/1000000000000 : ℝ) (176510145717/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33189/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176510145711/1000000000000 : ℝ) (176510145717/1000000000000 : ℝ) (117651014571/200000000000 : ℝ) (588255072859/1000000000000 : ℝ) (420131105383/1000000000000 : ℝ) (420131105391/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33189/262144 : ℝ))) 1 (117651014571/200000000000 : ℝ) (588255072859/1000000000000 : ℝ) (420131105383/1000000000000 : ℝ) (420131105391/1000000000000 : ℝ) (504193089119/1000000000000 : ℝ) (4033544713/8000000000 : ℝ) (248568025903/500000000000 : ℝ) (497136051813/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33189/262144 : ℝ))) 2 (504193089119/1000000000000 : ℝ) (4033544713/8000000000 : ℝ) (248568025903/500000000000 : ℝ) (497136051813/1000000000000 : ℝ) (250332285231/500000000000 : ℝ) (500664570469/1000000000000 : ℝ) (50065213639/100000000000 : ℝ) (250326068199/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33189/262144 : ℝ))) 3 (250332285231/500000000000 : ℝ) (500664570469/1000000000000 : ℝ) (50065213639/100000000000 : ℝ) (250326068199/500000000000 : ℝ) (250329176713/500000000000 : ℝ) (250329176717/500000000000 : ℝ) (500658353387/1000000000000 : ℝ) (100131670679/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33189/262144 : ℝ))) 4 (250329176713/500000000000 : ℝ) (250329176717/500000000000 : ℝ) (500658353387/1000000000000 : ℝ) (100131670679/200000000000 : ℝ) (250329176703/500000000000 : ℝ) (100131670683/200000000000 : ℝ) (250329176703/500000000000 : ℝ) (100131670683/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33189/262144 : ℝ))) 5 (250329176703/500000000000 : ℝ) (100131670683/200000000000 : ℝ) (250329176703/500000000000 : ℝ) (100131670683/200000000000 : ℝ) (250329176703/500000000000 : ℝ) (100131670683/200000000000 : ℝ) (250329176703/500000000000 : ℝ) (100131670683/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33189/262144 : ℝ))) 6 (250329176703/500000000000 : ℝ) (100131670683/200000000000 : ℝ) (250329176703/500000000000 : ℝ) (100131670683/200000000000 : ℝ) (250329176703/500000000000 : ℝ) (100131670683/200000000000 : ℝ) (250329176703/500000000000 : ℝ) (100131670683/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33189/262144 : ℝ))) 7 (250329176703/500000000000 : ℝ) (100131670683/200000000000 : ℝ) (250329176703/500000000000 : ℝ) (100131670683/200000000000 : ℝ) (250329176703/500000000000 : ℝ) (100131670683/200000000000 : ℝ) (250329176703/500000000000 : ℝ) (100131670683/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33189/262144 : ℝ)) hmem 8 (992133880193/1000000000000 : ℝ) (992133880197/1000000000000 : ℝ) (992133880193/1000000000000 : ℝ) (992133880197/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33189/262144 : ℝ))) hcmem 8 (250329176703/500000000000 : ℝ) (100131670683/200000000000 : ℝ) (250329176703/500000000000 : ℝ) (100131670683/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33189/262144 : ℝ)) (992133880193/1000000000000 : ℝ) (992133880197/1000000000000 : ℝ) (250329176703/500000000000 : ℝ) (100131670683/200000000000 : ℝ) (792667520187/1000000000000 : ℝ) (158533504041/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0408_exp_lower
  have heNumeric : (205490375801/100000000000 : ℝ)/4 ≤ Real.exp (-2131409111531/3200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (205490375801/100000000000 : ℝ)/4 ≤ Real.exp ((8297/65536 : ℝ)-(158533504041/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8297/65536 : ℝ) (33189/262144 : ℝ) (158533504041/200000000000 : ℝ) (205490375801/100000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0409; no trusted numerical premise.
theorem cover8_leaf0409_exp_radius : (249505919335605569/250000000000000000 : ℝ) ≤ Real.exp ((-16595/1048576 : ℝ)/8) ∧ Real.exp ((-16595/1048576 : ℝ)/8) ≤ (998023677342422277/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16595/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0409_exp_lower : (920113569806677867/1000000000000000000 : ℝ) ≤ Real.exp ((-1705127344451/2560000000000 : ℝ)/8) ∧ Real.exp ((-1705127344451/2560000000000 : ℝ)/8) ≤ (230028392451669467/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1705127344451/2560000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0409_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (25686296421/12500000000 : ℝ) ≤ 4*Real.exp (33189/262144 : ℝ)*Real.exp (-mu (radius 8 (16595/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (25686296421/12500000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16595/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0409_exp_radius
  have hrNumeric : (246074587841/250000000000 : ℝ) ≤ Real.exp (-16595/1048576 : ℝ) ∧ Real.exp (-16595/1048576 : ℝ) ≤ (196859670273/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246074587841/250000000000 : ℝ) ≤ (radius 8 (16595/131072 : ℝ)) ∧ (radius 8 (16595/131072 : ℝ)) ≤ (196859670273/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16595/131072 : ℝ)) (246074587841/250000000000 : ℝ) (196859670273/200000000000 : ℝ) (35302552599/200000000000 : ℝ) (176512763001/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16595/131072 : ℝ)) (246074587841/250000000000 : ℝ) (196859670273/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16595/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246074587841/250000000000 : ℝ) (196859670273/200000000000 : ℝ) (496074587841/500000000000 : ℝ) (992149175683/1000000000000 : ℝ) (198423622723/200000000000 : ℝ) (992118113617/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16595/131072 : ℝ)) 1 (496074587841/500000000000 : ℝ) (992149175683/1000000000000 : ℝ) (198423622723/200000000000 : ℝ) (992118113617/1000000000000 : ℝ) (124016705581/125000000000 : ℝ) (19842672893/20000000000 : ℝ) (496066822263/500000000000 : ℝ) (992133644529/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16595/131072 : ℝ)) 2 (124016705581/125000000000 : ℝ) (19842672893/20000000000 : ℝ) (496066822263/500000000000 : ℝ) (992133644529/1000000000000 : ℝ) (992133644587/1000000000000 : ℝ) (99213364459/100000000000 : ℝ) (496066822293/500000000000 : ℝ) (99213364459/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16595/131072 : ℝ)) 3 (992133644587/1000000000000 : ℝ) (99213364459/100000000000 : ℝ) (496066822293/500000000000 : ℝ) (99213364459/100000000000 : ℝ) (496066822293/500000000000 : ℝ) (99213364459/100000000000 : ℝ) (496066822293/500000000000 : ℝ) (99213364459/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16595/131072 : ℝ)) 4 (496066822293/500000000000 : ℝ) (99213364459/100000000000 : ℝ) (496066822293/500000000000 : ℝ) (99213364459/100000000000 : ℝ) (496066822293/500000000000 : ℝ) (99213364459/100000000000 : ℝ) (496066822293/500000000000 : ℝ) (99213364459/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16595/131072 : ℝ)) 5 (496066822293/500000000000 : ℝ) (99213364459/100000000000 : ℝ) (496066822293/500000000000 : ℝ) (99213364459/100000000000 : ℝ) (496066822293/500000000000 : ℝ) (99213364459/100000000000 : ℝ) (496066822293/500000000000 : ℝ) (99213364459/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16595/131072 : ℝ)) 6 (496066822293/500000000000 : ℝ) (99213364459/100000000000 : ℝ) (496066822293/500000000000 : ℝ) (99213364459/100000000000 : ℝ) (496066822293/500000000000 : ℝ) (99213364459/100000000000 : ℝ) (496066822293/500000000000 : ℝ) (99213364459/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16595/131072 : ℝ)) 7 (496066822293/500000000000 : ℝ) (99213364459/100000000000 : ℝ) (496066822293/500000000000 : ℝ) (99213364459/100000000000 : ℝ) (496066822293/500000000000 : ℝ) (99213364459/100000000000 : ℝ) (496066822293/500000000000 : ℝ) (99213364459/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16595/131072 : ℝ))) (35302552599/200000000000 : ℝ) (176512763001/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16595/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35302552599/200000000000 : ℝ) (176512763001/1000000000000 : ℝ) (588256381497/1000000000000 : ℝ) (588256381501/1000000000000 : ℝ) (210067110107/500000000000 : ℝ) (210067110111/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16595/131072 : ℝ))) 1 (588256381497/1000000000000 : ℝ) (588256381501/1000000000000 : ℝ) (210067110107/500000000000 : ℝ) (210067110111/500000000000 : ℝ) (100839060171/200000000000 : ℝ) (252097650431/500000000000 : ℝ) (124284611911/250000000000 : ℝ) (497138447651/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16595/131072 : ℝ))) 2 (100839060171/200000000000 : ℝ) (252097650431/500000000000 : ℝ) (124284611911/250000000000 : ℝ) (497138447651/1000000000000 : ℝ) (500666874249/1000000000000 : ℝ) (500666874257/1000000000000 : ℝ) (500654440883/1000000000000 : ℝ) (500654440891/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16595/131072 : ℝ))) 3 (500666874249/1000000000000 : ℝ) (500666874257/1000000000000 : ℝ) (500654440883/1000000000000 : ℝ) (500654440891/1000000000000 : ℝ) (250330328783/500000000000 : ℝ) (250330328787/500000000000 : ℝ) (500660657527/1000000000000 : ℝ) (3911411387/7812500000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16595/131072 : ℝ))) 4 (250330328783/500000000000 : ℝ) (250330328787/500000000000 : ℝ) (500660657527/1000000000000 : ℝ) (3911411387/7812500000 : ℝ) (250330328773/500000000000 : ℝ) (100132131511/200000000000 : ℝ) (250330328773/500000000000 : ℝ) (100132131511/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16595/131072 : ℝ))) 5 (250330328773/500000000000 : ℝ) (100132131511/200000000000 : ℝ) (250330328773/500000000000 : ℝ) (100132131511/200000000000 : ℝ) (250330328773/500000000000 : ℝ) (100132131511/200000000000 : ℝ) (250330328773/500000000000 : ℝ) (100132131511/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16595/131072 : ℝ))) 6 (250330328773/500000000000 : ℝ) (100132131511/200000000000 : ℝ) (250330328773/500000000000 : ℝ) (100132131511/200000000000 : ℝ) (250330328773/500000000000 : ℝ) (100132131511/200000000000 : ℝ) (250330328773/500000000000 : ℝ) (100132131511/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16595/131072 : ℝ))) 7 (250330328773/500000000000 : ℝ) (100132131511/200000000000 : ℝ) (250330328773/500000000000 : ℝ) (100132131511/200000000000 : ℝ) (250330328773/500000000000 : ℝ) (100132131511/200000000000 : ℝ) (250330328773/500000000000 : ℝ) (100132131511/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16595/131072 : ℝ)) hmem 8 (496066822293/500000000000 : ℝ) (99213364459/100000000000 : ℝ) (496066822293/500000000000 : ℝ) (99213364459/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16595/131072 : ℝ))) hcmem 8 (250330328773/500000000000 : ℝ) (100132131511/200000000000 : ℝ) (250330328773/500000000000 : ℝ) (100132131511/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16595/131072 : ℝ)) (496066822293/500000000000 : ℝ) (99213364459/100000000000 : ℝ) (250330328773/500000000000 : ℝ) (100132131511/200000000000 : ℝ) (792671356457/1000000000000 : ℝ) (31706854259/40000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0409_exp_lower
  have heNumeric : (25686296421/12500000000 : ℝ)/4 ≤ Real.exp (-1705127344451/2560000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (25686296421/12500000000 : ℝ)/4 ≤ Real.exp ((33189/262144 : ℝ)-(31706854259/40000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33189/262144 : ℝ) (16595/131072 : ℝ) (31706854259/40000000000 : ℝ) (25686296421/12500000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0410; no trusted numerical premise.
theorem cover8_leaf0410_exp_radius : (249505904463894321/250000000000000000 : ℝ) ≤ Real.exp ((-33191/2097152 : ℝ)/8) ∧ Real.exp ((-33191/2097152 : ℝ)/8) ≤ (199604723571115457/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33191/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0410_exp_lower : (920113567334363259/1000000000000000000 : ℝ) ≤ Real.exp ((-21314092493501/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314092493501/32000000000000 : ℝ)/8) ≤ (46005678366718163/50000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314092493501/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0410_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513725917377/250000000000 : ℝ) ≤ 4*Real.exp (16595/131072 : ℝ)*Real.exp (-mu (radius 8 (33191/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (513725917377/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33191/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0410_exp_radius
  have hrNumeric : (492148941007/500000000000 : ℝ) ≤ Real.exp (-33191/2097152 : ℝ) ∧ Real.exp (-33191/2097152 : ℝ) ≤ (196859576403/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492148941007/500000000000 : ℝ) ≤ (radius 8 (33191/262144 : ℝ)) ∧ (radius 8 (33191/262144 : ℝ)) ≤ (196859576403/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33191/262144 : ℝ)) (492148941007/500000000000 : ℝ) (196859576403/200000000000 : ℝ) (88257690119/500000000000 : ℝ) (35303076049/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33191/262144 : ℝ)) (492148941007/500000000000 : ℝ) (196859576403/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33191/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492148941007/500000000000 : ℝ) (196859576403/200000000000 : ℝ) (992148941007/1000000000000 : ℝ) (62009308813/62500000000 : ℝ) (248029469269/250000000000 : ℝ) (992117877077/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33191/262144 : ℝ)) 1 (992148941007/1000000000000 : ℝ) (62009308813/62500000000 : ℝ) (248029469269/250000000000 : ℝ) (992117877077/1000000000000 : ℝ) (992133409041/1000000000000 : ℝ) (992133409043/1000000000000 : ℝ) (992133408919/1000000000000 : ℝ) (992133408921/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33191/262144 : ℝ)) 2 (992133409041/1000000000000 : ℝ) (992133409043/1000000000000 : ℝ) (992133408919/1000000000000 : ℝ) (992133408921/1000000000000 : ℝ) (49606670449/50000000000 : ℝ) (496066704491/500000000000 : ℝ) (992133408979/1000000000000 : ℝ) (496066704491/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33191/262144 : ℝ)) 3 (49606670449/50000000000 : ℝ) (496066704491/500000000000 : ℝ) (992133408979/1000000000000 : ℝ) (496066704491/500000000000 : ℝ) (992133408979/1000000000000 : ℝ) (496066704491/500000000000 : ℝ) (992133408979/1000000000000 : ℝ) (496066704491/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33191/262144 : ℝ)) 4 (992133408979/1000000000000 : ℝ) (496066704491/500000000000 : ℝ) (992133408979/1000000000000 : ℝ) (496066704491/500000000000 : ℝ) (992133408979/1000000000000 : ℝ) (496066704491/500000000000 : ℝ) (992133408979/1000000000000 : ℝ) (496066704491/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33191/262144 : ℝ)) 5 (992133408979/1000000000000 : ℝ) (496066704491/500000000000 : ℝ) (992133408979/1000000000000 : ℝ) (496066704491/500000000000 : ℝ) (992133408979/1000000000000 : ℝ) (496066704491/500000000000 : ℝ) (992133408979/1000000000000 : ℝ) (496066704491/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33191/262144 : ℝ)) 6 (992133408979/1000000000000 : ℝ) (496066704491/500000000000 : ℝ) (992133408979/1000000000000 : ℝ) (496066704491/500000000000 : ℝ) (992133408979/1000000000000 : ℝ) (496066704491/500000000000 : ℝ) (992133408979/1000000000000 : ℝ) (496066704491/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33191/262144 : ℝ)) 7 (992133408979/1000000000000 : ℝ) (496066704491/500000000000 : ℝ) (992133408979/1000000000000 : ℝ) (496066704491/500000000000 : ℝ) (992133408979/1000000000000 : ℝ) (496066704491/500000000000 : ℝ) (992133408979/1000000000000 : ℝ) (496066704491/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33191/262144 : ℝ))) (88257690119/500000000000 : ℝ) (35303076049/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33191/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88257690119/500000000000 : ℝ) (35303076049/200000000000 : ℝ) (588257690119/1000000000000 : ℝ) (588257690123/1000000000000 : ℝ) (105034333743/250000000000 : ℝ) (210068667491/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33191/262144 : ℝ))) 1 (588257690119/1000000000000 : ℝ) (588257690123/1000000000000 : ℝ) (105034333743/250000000000 : ℝ) (210068667491/500000000000 : ℝ) (100839502509/200000000000 : ℝ) (504197512553/1000000000000 : ℝ) (497140843427/1000000000000 : ℝ) (99428168687/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33191/262144 : ℝ))) 2 (100839502509/200000000000 : ℝ) (504197512553/1000000000000 : ℝ) (497140843427/1000000000000 : ℝ) (99428168687/200000000000 : ℝ) (250334588993/500000000000 : ℝ) (250334588997/500000000000 : ℝ) (20026269813/40000000000 : ℝ) (250328372667/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33191/262144 : ℝ))) 3 (250334588993/500000000000 : ℝ) (250334588997/500000000000 : ℝ) (20026269813/40000000000 : ℝ) (250328372667/500000000000 : ℝ) (100132592331/200000000000 : ℝ) (977857347/1953125000 : ℝ) (31291435101/62500000000 : ℝ) (250331480813/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33191/262144 : ℝ))) 4 (100132592331/200000000000 : ℝ) (977857347/1953125000 : ℝ) (31291435101/62500000000 : ℝ) (250331480813/500000000000 : ℝ) (100132592327/200000000000 : ℝ) (100132592329/200000000000 : ℝ) (100132592327/200000000000 : ℝ) (100132592329/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33191/262144 : ℝ))) 5 (100132592327/200000000000 : ℝ) (100132592329/200000000000 : ℝ) (100132592327/200000000000 : ℝ) (100132592329/200000000000 : ℝ) (100132592327/200000000000 : ℝ) (100132592329/200000000000 : ℝ) (100132592327/200000000000 : ℝ) (100132592329/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33191/262144 : ℝ))) 6 (100132592327/200000000000 : ℝ) (100132592329/200000000000 : ℝ) (100132592327/200000000000 : ℝ) (100132592329/200000000000 : ℝ) (100132592327/200000000000 : ℝ) (100132592329/200000000000 : ℝ) (100132592327/200000000000 : ℝ) (100132592329/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33191/262144 : ℝ))) 7 (100132592327/200000000000 : ℝ) (100132592329/200000000000 : ℝ) (100132592327/200000000000 : ℝ) (100132592329/200000000000 : ℝ) (100132592327/200000000000 : ℝ) (100132592329/200000000000 : ℝ) (100132592327/200000000000 : ℝ) (100132592329/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33191/262144 : ℝ)) hmem 8 (992133408979/1000000000000 : ℝ) (496066704491/500000000000 : ℝ) (992133408979/1000000000000 : ℝ) (496066704491/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33191/262144 : ℝ))) hcmem 8 (100132592327/200000000000 : ℝ) (100132592329/200000000000 : ℝ) (100132592327/200000000000 : ℝ) (100132592329/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33191/262144 : ℝ)) (992133408979/1000000000000 : ℝ) (496066704491/500000000000 : ℝ) (100132592327/200000000000 : ℝ) (100132592329/200000000000 : ℝ) (792675192649/1000000000000 : ℝ) (198168798167/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0410_exp_lower
  have heNumeric : (513725917377/250000000000 : ℝ)/4 ≤ Real.exp (-21314092493501/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513725917377/250000000000 : ℝ)/4 ≤ Real.exp ((16595/131072 : ℝ)-(198168798167/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16595/131072 : ℝ) (33191/262144 : ℝ) (198168798167/250000000000 : ℝ) (513725917377/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0411; no trusted numerical premise.
theorem cover8_leaf0411_exp_radius : (998023558368735837/1000000000000000000 : ℝ) ≤ Real.exp ((-4149/262144 : ℝ)/8) ∧ Real.exp ((-4149/262144 : ℝ)/8) ≤ (499011779184367919/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4149/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0411_exp_lower : (230028391217754941/250000000000000000 : ℝ) ≤ Real.exp ((-42628186357737/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628186357737/64000000000000 : ℝ)/8) ≤ (184022712974203953/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628186357737/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0411_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054903625497/1000000000000 : ℝ) ≤ 4*Real.exp (33191/262144 : ℝ)*Real.exp (-mu (radius 8 (4149/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (2054903625497/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4149/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0411_exp_radius
  have hrNumeric : (123037176583/125000000000 : ℝ) ≤ Real.exp (-4149/262144 : ℝ) ∧ Real.exp (-4149/262144 : ℝ) ≤ (196859482533/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (123037176583/125000000000 : ℝ) ≤ (radius 8 (4149/32768 : ℝ)) ∧ (radius 8 (4149/32768 : ℝ)) ≤ (196859482533/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4149/32768 : ℝ)) (123037176583/125000000000 : ℝ) (196859482533/200000000000 : ℝ) (88258998721/500000000000 : ℝ) (22064749681/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4149/32768 : ℝ)) (123037176583/125000000000 : ℝ) (196859482533/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4149/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (123037176583/125000000000 : ℝ) (196859482533/200000000000 : ℝ) (248037176583/250000000000 : ℝ) (992148706333/1000000000000 : ℝ) (124014705067/125000000000 : ℝ) (496058820269/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4149/32768 : ℝ)) 1 (248037176583/250000000000 : ℝ) (992148706333/1000000000000 : ℝ) (124014705067/125000000000 : ℝ) (496058820269/500000000000 : ℝ) (496066586717/500000000000 : ℝ) (248033293359/250000000000 : ℝ) (15502080833/15625000000 : ℝ) (496066586657/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4149/32768 : ℝ)) 2 (496066586717/500000000000 : ℝ) (248033293359/250000000000 : ℝ) (15502080833/15625000000 : ℝ) (496066586657/500000000000 : ℝ) (992133173373/1000000000000 : ℝ) (7937065387/8000000000 : ℝ) (248033293343/250000000000 : ℝ) (7937065387/8000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4149/32768 : ℝ)) 3 (992133173373/1000000000000 : ℝ) (7937065387/8000000000 : ℝ) (248033293343/250000000000 : ℝ) (7937065387/8000000000 : ℝ) (248033293343/250000000000 : ℝ) (7937065387/8000000000 : ℝ) (248033293343/250000000000 : ℝ) (7937065387/8000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4149/32768 : ℝ)) 4 (248033293343/250000000000 : ℝ) (7937065387/8000000000 : ℝ) (248033293343/250000000000 : ℝ) (7937065387/8000000000 : ℝ) (248033293343/250000000000 : ℝ) (7937065387/8000000000 : ℝ) (248033293343/250000000000 : ℝ) (7937065387/8000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4149/32768 : ℝ)) 5 (248033293343/250000000000 : ℝ) (7937065387/8000000000 : ℝ) (248033293343/250000000000 : ℝ) (7937065387/8000000000 : ℝ) (248033293343/250000000000 : ℝ) (7937065387/8000000000 : ℝ) (248033293343/250000000000 : ℝ) (7937065387/8000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4149/32768 : ℝ)) 6 (248033293343/250000000000 : ℝ) (7937065387/8000000000 : ℝ) (248033293343/250000000000 : ℝ) (7937065387/8000000000 : ℝ) (248033293343/250000000000 : ℝ) (7937065387/8000000000 : ℝ) (248033293343/250000000000 : ℝ) (7937065387/8000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4149/32768 : ℝ)) 7 (248033293343/250000000000 : ℝ) (7937065387/8000000000 : ℝ) (248033293343/250000000000 : ℝ) (7937065387/8000000000 : ℝ) (248033293343/250000000000 : ℝ) (7937065387/8000000000 : ℝ) (248033293343/250000000000 : ℝ) (7937065387/8000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4149/32768 : ℝ))) (88258998721/500000000000 : ℝ) (22064749681/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4149/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88258998721/500000000000 : ℝ) (22064749681/125000000000 : ℝ) (588258998721/1000000000000 : ℝ) (147064749681/250000000000 : ℝ) (420140449661/1000000000000 : ℝ) (420140449669/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4149/32768 : ℝ))) 1 (588258998721/1000000000000 : ℝ) (147064749681/250000000000 : ℝ) (420140449661/1000000000000 : ℝ) (420140449669/1000000000000 : ℝ) (504199724191/1000000000000 : ℝ) (504199724197/1000000000000 : ℝ) (497143239157/1000000000000 : ℝ) (124285809791/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4149/32768 : ℝ))) 2 (504199724191/1000000000000 : ℝ) (504199724197/1000000000000 : ℝ) (497143239157/1000000000000 : ℝ) (124285809791/250000000000 : ℝ) (250335740837/500000000000 : ℝ) (500671481681/1000000000000 : ℝ) (500659049719/1000000000000 : ℝ) (500659049727/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4149/32768 : ℝ))) 3 (250335740837/500000000000 : ℝ) (500671481681/1000000000000 : ℝ) (500659049719/1000000000000 : ℝ) (500659049727/1000000000000 : ℝ) (15645789553/31250000000 : ℝ) (62583158213/125000000000 : ℝ) (500665265657/1000000000000 : ℝ) (250332632833/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4149/32768 : ℝ))) 4 (15645789553/31250000000 : ℝ) (62583158213/125000000000 : ℝ) (500665265657/1000000000000 : ℝ) (250332632833/500000000000 : ℝ) (125166316419/250000000000 : ℝ) (100133053137/200000000000 : ℝ) (125166316419/250000000000 : ℝ) (100133053137/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4149/32768 : ℝ))) 5 (125166316419/250000000000 : ℝ) (100133053137/200000000000 : ℝ) (125166316419/250000000000 : ℝ) (100133053137/200000000000 : ℝ) (125166316419/250000000000 : ℝ) (100133053137/200000000000 : ℝ) (125166316419/250000000000 : ℝ) (100133053137/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4149/32768 : ℝ))) 6 (125166316419/250000000000 : ℝ) (100133053137/200000000000 : ℝ) (125166316419/250000000000 : ℝ) (100133053137/200000000000 : ℝ) (125166316419/250000000000 : ℝ) (100133053137/200000000000 : ℝ) (125166316419/250000000000 : ℝ) (100133053137/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4149/32768 : ℝ))) 7 (125166316419/250000000000 : ℝ) (100133053137/200000000000 : ℝ) (125166316419/250000000000 : ℝ) (100133053137/200000000000 : ℝ) (125166316419/250000000000 : ℝ) (100133053137/200000000000 : ℝ) (125166316419/250000000000 : ℝ) (100133053137/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4149/32768 : ℝ)) hmem 8 (248033293343/250000000000 : ℝ) (7937065387/8000000000 : ℝ) (248033293343/250000000000 : ℝ) (7937065387/8000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4149/32768 : ℝ))) hcmem 8 (125166316419/250000000000 : ℝ) (100133053137/200000000000 : ℝ) (125166316419/250000000000 : ℝ) (100133053137/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4149/32768 : ℝ)) (248033293343/250000000000 : ℝ) (7937065387/8000000000 : ℝ) (125166316419/250000000000 : ℝ) (100133053137/200000000000 : ℝ) (396339514383/500000000000 : ℝ) (792679028783/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0411_exp_lower
  have heNumeric : (2054903625497/1000000000000 : ℝ)/4 ≤ Real.exp (-42628186357737/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054903625497/1000000000000 : ℝ)/4 ≤ Real.exp ((33191/262144 : ℝ)-(792679028783/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33191/262144 : ℝ) (4149/32768 : ℝ) (792679028783/1000000000000 : ℝ) (2054903625497/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0412; no trusted numerical premise.
theorem cover8_leaf0412_exp_radius : (199604699776379587/200000000000000000 : ℝ) ≤ Real.exp ((-33193/2097152 : ℝ)/8) ∧ Real.exp ((-33193/2097152 : ℝ)/8) ≤ (62376468680118621/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33193/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0412_exp_lower : (920113562416302341/1000000000000000000 : ℝ) ≤ Real.exp ((-5328523465459/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328523465459/8000000000000 : ℝ)/8) ≤ (460056781208151171/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328523465459/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0412_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (51372589541/25000000000 : ℝ) ≤ 4*Real.exp (4149/32768 : ℝ)*Real.exp (-mu (radius 8 (33193/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (51372589541/25000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33193/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0412_exp_radius
  have hrNumeric : (492148471657/500000000000 : ℝ) ≤ Real.exp (-33193/2097152 : ℝ) ∧ Real.exp (-33193/2097152 : ℝ) ≤ (196859388663/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492148471657/500000000000 : ℝ) ≤ (radius 8 (33193/262144 : ℝ)) ∧ (radius 8 (33193/262144 : ℝ)) ≤ (196859388663/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33193/262144 : ℝ)) (492148471657/500000000000 : ℝ) (196859388663/200000000000 : ℝ) (35304122921/200000000000 : ℝ) (44130153653/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33193/262144 : ℝ)) (492148471657/500000000000 : ℝ) (196859388663/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33193/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492148471657/500000000000 : ℝ) (196859388663/200000000000 : ℝ) (992148471657/1000000000000 : ℝ) (496074235829/500000000000 : ℝ) (992117403997/1000000000000 : ℝ) (496058701999/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33193/262144 : ℝ)) 1 (992148471657/1000000000000 : ℝ) (496074235829/500000000000 : ℝ) (992117403997/1000000000000 : ℝ) (496058701999/500000000000 : ℝ) (992132937827/1000000000000 : ℝ) (248033234457/250000000000 : ℝ) (198426587541/200000000000 : ℝ) (992132937707/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33193/262144 : ℝ)) 2 (992132937827/1000000000000 : ℝ) (248033234457/250000000000 : ℝ) (198426587541/200000000000 : ℝ) (992132937707/1000000000000 : ℝ) (496066468883/500000000000 : ℝ) (124016617221/125000000000 : ℝ) (198426587553/200000000000 : ℝ) (124016617221/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33193/262144 : ℝ)) 3 (496066468883/500000000000 : ℝ) (124016617221/125000000000 : ℝ) (198426587553/200000000000 : ℝ) (124016617221/125000000000 : ℝ) (198426587553/200000000000 : ℝ) (124016617221/125000000000 : ℝ) (198426587553/200000000000 : ℝ) (124016617221/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33193/262144 : ℝ)) 4 (198426587553/200000000000 : ℝ) (124016617221/125000000000 : ℝ) (198426587553/200000000000 : ℝ) (124016617221/125000000000 : ℝ) (198426587553/200000000000 : ℝ) (124016617221/125000000000 : ℝ) (198426587553/200000000000 : ℝ) (124016617221/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33193/262144 : ℝ)) 5 (198426587553/200000000000 : ℝ) (124016617221/125000000000 : ℝ) (198426587553/200000000000 : ℝ) (124016617221/125000000000 : ℝ) (198426587553/200000000000 : ℝ) (124016617221/125000000000 : ℝ) (198426587553/200000000000 : ℝ) (124016617221/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33193/262144 : ℝ)) 6 (198426587553/200000000000 : ℝ) (124016617221/125000000000 : ℝ) (198426587553/200000000000 : ℝ) (124016617221/125000000000 : ℝ) (198426587553/200000000000 : ℝ) (124016617221/125000000000 : ℝ) (198426587553/200000000000 : ℝ) (124016617221/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33193/262144 : ℝ)) 7 (198426587553/200000000000 : ℝ) (124016617221/125000000000 : ℝ) (198426587553/200000000000 : ℝ) (124016617221/125000000000 : ℝ) (198426587553/200000000000 : ℝ) (124016617221/125000000000 : ℝ) (198426587553/200000000000 : ℝ) (124016617221/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33193/262144 : ℝ))) (35304122921/200000000000 : ℝ) (44130153653/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33193/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35304122921/200000000000 : ℝ) (44130153653/250000000000 : ℝ) (294130153651/500000000000 : ℝ) (294130153653/500000000000 : ℝ) (210071782139/500000000000 : ℝ) (820592899/1953125000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33193/262144 : ℝ))) 1 (294130153651/500000000000 : ℝ) (294130153653/500000000000 : ℝ) (210071782139/500000000000 : ℝ) (820592899/1953125000 : ℝ) (50420193579/100000000000 : ℝ) (504201935797/1000000000000 : ℝ) (31071602177/62500000000 : ℝ) (497145634841/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33193/262144 : ℝ))) 2 (50420193579/100000000000 : ℝ) (504201935797/1000000000000 : ℝ) (31071602177/62500000000 : ℝ) (497145634841/1000000000000 : ℝ) (500673785311/1000000000000 : ℝ) (500673785319/1000000000000 : ℝ) (250330677031/500000000000 : ℝ) (500661354071/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33193/262144 : ℝ))) 3 (500673785311/1000000000000 : ℝ) (500673785319/1000000000000 : ℝ) (250330677031/500000000000 : ℝ) (500661354071/1000000000000 : ℝ) (250333784843/500000000000 : ℝ) (100133513939/200000000000 : ℝ) (500667569647/1000000000000 : ℝ) (500667569657/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33193/262144 : ℝ))) 4 (250333784843/500000000000 : ℝ) (100133513939/200000000000 : ℝ) (500667569647/1000000000000 : ℝ) (500667569657/1000000000000 : ℝ) (250333784833/500000000000 : ℝ) (125166892419/250000000000 : ℝ) (250333784833/500000000000 : ℝ) (125166892419/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33193/262144 : ℝ))) 5 (250333784833/500000000000 : ℝ) (125166892419/250000000000 : ℝ) (250333784833/500000000000 : ℝ) (125166892419/250000000000 : ℝ) (250333784833/500000000000 : ℝ) (125166892419/250000000000 : ℝ) (250333784833/500000000000 : ℝ) (125166892419/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33193/262144 : ℝ))) 6 (250333784833/500000000000 : ℝ) (125166892419/250000000000 : ℝ) (250333784833/500000000000 : ℝ) (125166892419/250000000000 : ℝ) (250333784833/500000000000 : ℝ) (125166892419/250000000000 : ℝ) (250333784833/500000000000 : ℝ) (125166892419/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33193/262144 : ℝ))) 7 (250333784833/500000000000 : ℝ) (125166892419/250000000000 : ℝ) (250333784833/500000000000 : ℝ) (125166892419/250000000000 : ℝ) (250333784833/500000000000 : ℝ) (125166892419/250000000000 : ℝ) (250333784833/500000000000 : ℝ) (125166892419/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33193/262144 : ℝ)) hmem 8 (198426587553/200000000000 : ℝ) (124016617221/125000000000 : ℝ) (198426587553/200000000000 : ℝ) (124016617221/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33193/262144 : ℝ))) hcmem 8 (250333784833/500000000000 : ℝ) (125166892419/250000000000 : ℝ) (250333784833/500000000000 : ℝ) (125166892419/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33193/262144 : ℝ)) (198426587553/200000000000 : ℝ) (124016617221/125000000000 : ℝ) (250333784833/500000000000 : ℝ) (125166892419/250000000000 : ℝ) (198170716201/250000000000 : ℝ) (792682864823/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0412_exp_lower
  have heNumeric : (51372589541/25000000000 : ℝ)/4 ≤ Real.exp (-5328523465459/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (51372589541/25000000000 : ℝ)/4 ≤ Real.exp ((4149/32768 : ℝ)-(792682864823/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4149/32768 : ℝ) (33193/262144 : ℝ) (792682864823/1000000000000 : ℝ) (51372589541/25000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0413; no trusted numerical premise.
theorem cover8_leaf0413_exp_radius : (49901171969753179/50000000000000000 : ℝ) ≤ Real.exp ((-16597/1048576 : ℝ)/8) ∧ Real.exp ((-16597/1048576 : ℝ)/8) ≤ (998023439395063581/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16597/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0413_exp_lower : (920113559971246117/1000000000000000000 : ℝ) ≤ Real.exp ((-42628189084231/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628189084231/64000000000000 : ℝ)/8) ≤ (460056779985623059/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628189084231/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0413_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410980707591/200000000000 : ℝ) ≤ 4*Real.exp (33193/262144 : ℝ)*Real.exp (-mu (radius 8 (16597/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (410980707591/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16597/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0413_exp_radius
  have hrNumeric : (196859294793/200000000000 : ℝ) ≤ Real.exp (-16597/1048576 : ℝ) ∧ Real.exp (-16597/1048576 : ℝ) ≤ (492148236983/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196859294793/200000000000 : ℝ) ≤ (radius 8 (16597/131072 : ℝ)) ∧ (radius 8 (16597/131072 : ℝ)) ≤ (492148236983/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16597/131072 : ℝ)) (196859294793/200000000000 : ℝ) (492148236983/500000000000 : ℝ) (176523231723/1000000000000 : ℝ) (17652323173/100000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16597/131072 : ℝ)) (196859294793/200000000000 : ℝ) (492148236983/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16597/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196859294793/200000000000 : ℝ) (492148236983/500000000000 : ℝ) (496074118491/500000000000 : ℝ) (992148236983/1000000000000 : ℝ) (496058583729/500000000000 : ℝ) (992117167459/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16597/131072 : ℝ)) 1 (496074118491/500000000000 : ℝ) (992148236983/1000000000000 : ℝ) (496058583729/500000000000 : ℝ) (992117167459/1000000000000 : ℝ) (49606635111/50000000000 : ℝ) (992132702221/1000000000000 : ℝ) (496066351049/500000000000 : ℝ) (9921327021/10000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16597/131072 : ℝ)) 2 (49606635111/50000000000 : ℝ) (992132702221/1000000000000 : ℝ) (496066351049/500000000000 : ℝ) (9921327021/10000000000 : ℝ) (992132702159/1000000000000 : ℝ) (992132702161/1000000000000 : ℝ) (496066351079/500000000000 : ℝ) (992132702161/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16597/131072 : ℝ)) 3 (992132702159/1000000000000 : ℝ) (992132702161/1000000000000 : ℝ) (496066351079/500000000000 : ℝ) (992132702161/1000000000000 : ℝ) (496066351079/500000000000 : ℝ) (992132702161/1000000000000 : ℝ) (496066351079/500000000000 : ℝ) (992132702161/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16597/131072 : ℝ)) 4 (496066351079/500000000000 : ℝ) (992132702161/1000000000000 : ℝ) (496066351079/500000000000 : ℝ) (992132702161/1000000000000 : ℝ) (496066351079/500000000000 : ℝ) (992132702161/1000000000000 : ℝ) (496066351079/500000000000 : ℝ) (992132702161/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16597/131072 : ℝ)) 5 (496066351079/500000000000 : ℝ) (992132702161/1000000000000 : ℝ) (496066351079/500000000000 : ℝ) (992132702161/1000000000000 : ℝ) (496066351079/500000000000 : ℝ) (992132702161/1000000000000 : ℝ) (496066351079/500000000000 : ℝ) (992132702161/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16597/131072 : ℝ)) 6 (496066351079/500000000000 : ℝ) (992132702161/1000000000000 : ℝ) (496066351079/500000000000 : ℝ) (992132702161/1000000000000 : ℝ) (496066351079/500000000000 : ℝ) (992132702161/1000000000000 : ℝ) (496066351079/500000000000 : ℝ) (992132702161/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16597/131072 : ℝ)) 7 (496066351079/500000000000 : ℝ) (992132702161/1000000000000 : ℝ) (496066351079/500000000000 : ℝ) (992132702161/1000000000000 : ℝ) (496066351079/500000000000 : ℝ) (992132702161/1000000000000 : ℝ) (496066351079/500000000000 : ℝ) (992132702161/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16597/131072 : ℝ))) (176523231723/1000000000000 : ℝ) (17652323173/100000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16597/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176523231723/1000000000000 : ℝ) (17652323173/100000000000 : ℝ) (588261615861/1000000000000 : ℝ) (117652323173/200000000000 : ℝ) (420146678819/1000000000000 : ℝ) (105036669707/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16597/131072 : ℝ))) 1 (588261615861/1000000000000 : ℝ) (117652323173/200000000000 : ℝ) (420146678819/1000000000000 : ℝ) (105036669707/250000000000 : ℝ) (25210207367/50000000000 : ℝ) (504204147347/1000000000000 : ℝ) (9942960609/20000000000 : ℝ) (248574015229/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16597/131072 : ℝ))) 2 (25210207367/50000000000 : ℝ) (504204147347/1000000000000 : ℝ) (9942960609/20000000000 : ℝ) (248574015229/500000000000 : ℝ) (100135217779/200000000000 : ℝ) (500676088903/1000000000000 : ℝ) (31291478647/62500000000 : ℝ) (12516591459/25000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16597/131072 : ℝ))) 3 (100135217779/200000000000 : ℝ) (500676088903/1000000000000 : ℝ) (31291478647/62500000000 : ℝ) (12516591459/25000000000 : ℝ) (500669873623/1000000000000 : ℝ) (15645933551/31250000000 : ℝ) (31291867099/62500000000 : ℝ) (500669873593/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16597/131072 : ℝ))) 4 (500669873623/1000000000000 : ℝ) (15645933551/31250000000 : ℝ) (31291867099/62500000000 : ℝ) (500669873593/1000000000000 : ℝ) (500669873603/1000000000000 : ℝ) (500669873613/1000000000000 : ℝ) (500669873603/1000000000000 : ℝ) (500669873613/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16597/131072 : ℝ))) 5 (500669873603/1000000000000 : ℝ) (500669873613/1000000000000 : ℝ) (500669873603/1000000000000 : ℝ) (500669873613/1000000000000 : ℝ) (500669873603/1000000000000 : ℝ) (500669873613/1000000000000 : ℝ) (500669873603/1000000000000 : ℝ) (500669873613/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16597/131072 : ℝ))) 6 (500669873603/1000000000000 : ℝ) (500669873613/1000000000000 : ℝ) (500669873603/1000000000000 : ℝ) (500669873613/1000000000000 : ℝ) (500669873603/1000000000000 : ℝ) (500669873613/1000000000000 : ℝ) (500669873603/1000000000000 : ℝ) (500669873613/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16597/131072 : ℝ))) 7 (500669873603/1000000000000 : ℝ) (500669873613/1000000000000 : ℝ) (500669873603/1000000000000 : ℝ) (500669873613/1000000000000 : ℝ) (500669873603/1000000000000 : ℝ) (500669873613/1000000000000 : ℝ) (500669873603/1000000000000 : ℝ) (500669873613/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16597/131072 : ℝ)) hmem 8 (496066351079/500000000000 : ℝ) (992132702161/1000000000000 : ℝ) (496066351079/500000000000 : ℝ) (992132702161/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16597/131072 : ℝ))) hcmem 8 (500669873603/1000000000000 : ℝ) (500669873613/1000000000000 : ℝ) (500669873603/1000000000000 : ℝ) (500669873613/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16597/131072 : ℝ)) (496066351079/500000000000 : ℝ) (992132702161/1000000000000 : ℝ) (500669873603/1000000000000 : ℝ) (500669873613/1000000000000 : ℝ) (19817167519/25000000000 : ℝ) (792686700779/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0413_exp_lower
  have heNumeric : (410980707591/200000000000 : ℝ)/4 ≤ Real.exp (-42628189084231/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410980707591/200000000000 : ℝ)/4 ≤ Real.exp ((33193/262144 : ℝ)-(792686700779/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33193/262144 : ℝ) (16597/131072 : ℝ) (792686700779/1000000000000 : ℝ) (410980707591/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0414; no trusted numerical premise.
theorem cover8_leaf0414_exp_radius : (99802337990823277/100000000000000000 : ℝ) ≤ Real.exp ((-33195/2097152 : ℝ)/8) ∧ Real.exp ((-33195/2097152 : ℝ)/8) ≤ (998023379908232771/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33195/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0414_exp_lower : (920113557535276021/1000000000000000000 : ℝ) ≤ Real.exp ((-21314095219867/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314095219867/32000000000000 : ℝ)/8) ≤ (460056778767638011/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314095219867/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0414_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054903494433/1000000000000 : ℝ) ≤ 4*Real.exp (16597/131072 : ℝ)*Real.exp (-mu (radius 8 (33195/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054903494433/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33195/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0414_exp_radius
  have hrNumeric : (123037000577/125000000000 : ℝ) ≤ Real.exp (-33195/2097152 : ℝ) ∧ Real.exp (-33195/2097152 : ℝ) ≤ (984296004617/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (123037000577/125000000000 : ℝ) ≤ (radius 8 (33195/262144 : ℝ)) ∧ (radius 8 (33195/262144 : ℝ)) ≤ (984296004617/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33195/262144 : ℝ)) (123037000577/125000000000 : ℝ) (984296004617/1000000000000 : ℝ) (176525848801/1000000000000 : ℝ) (176525848807/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33195/262144 : ℝ)) (123037000577/125000000000 : ℝ) (984296004617/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33195/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (123037000577/125000000000 : ℝ) (984296004617/1000000000000 : ℝ) (248037000577/250000000000 : ℝ) (992148002309/1000000000000 : ℝ) (496058465459/500000000000 : ℝ) (24802923273/25000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33195/262144 : ℝ)) 1 (248037000577/250000000000 : ℝ) (992148002309/1000000000000 : ℝ) (496058465459/500000000000 : ℝ) (24802923273/25000000000 : ℝ) (992132466613/1000000000000 : ℝ) (198426493323/200000000000 : ℝ) (992132466491/1000000000000 : ℝ) (992132466493/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33195/262144 : ℝ)) 2 (992132466613/1000000000000 : ℝ) (198426493323/200000000000 : ℝ) (992132466491/1000000000000 : ℝ) (992132466493/1000000000000 : ℝ) (124016558319/125000000000 : ℝ) (496066233277/500000000000 : ℝ) (992132466551/1000000000000 : ℝ) (496066233277/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33195/262144 : ℝ)) 3 (124016558319/125000000000 : ℝ) (496066233277/500000000000 : ℝ) (992132466551/1000000000000 : ℝ) (496066233277/500000000000 : ℝ) (992132466551/1000000000000 : ℝ) (496066233277/500000000000 : ℝ) (992132466551/1000000000000 : ℝ) (496066233277/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33195/262144 : ℝ)) 4 (992132466551/1000000000000 : ℝ) (496066233277/500000000000 : ℝ) (992132466551/1000000000000 : ℝ) (496066233277/500000000000 : ℝ) (992132466551/1000000000000 : ℝ) (496066233277/500000000000 : ℝ) (992132466551/1000000000000 : ℝ) (496066233277/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33195/262144 : ℝ)) 5 (992132466551/1000000000000 : ℝ) (496066233277/500000000000 : ℝ) (992132466551/1000000000000 : ℝ) (496066233277/500000000000 : ℝ) (992132466551/1000000000000 : ℝ) (496066233277/500000000000 : ℝ) (992132466551/1000000000000 : ℝ) (496066233277/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33195/262144 : ℝ)) 6 (992132466551/1000000000000 : ℝ) (496066233277/500000000000 : ℝ) (992132466551/1000000000000 : ℝ) (496066233277/500000000000 : ℝ) (992132466551/1000000000000 : ℝ) (496066233277/500000000000 : ℝ) (992132466551/1000000000000 : ℝ) (496066233277/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33195/262144 : ℝ)) 7 (992132466551/1000000000000 : ℝ) (496066233277/500000000000 : ℝ) (992132466551/1000000000000 : ℝ) (496066233277/500000000000 : ℝ) (992132466551/1000000000000 : ℝ) (496066233277/500000000000 : ℝ) (992132466551/1000000000000 : ℝ) (496066233277/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33195/262144 : ℝ))) (176525848801/1000000000000 : ℝ) (176525848807/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33195/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176525848801/1000000000000 : ℝ) (176525848807/1000000000000 : ℝ) (1470657311/2500000000 : ℝ) (147065731101/250000000000 : ℝ) (420149793289/1000000000000 : ℝ) (420149793297/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33195/262144 : ℝ))) 1 (1470657311/2500000000 : ℝ) (147065731101/250000000000 : ℝ) (420149793289/1000000000000 : ℝ) (420149793297/1000000000000 : ℝ) (126051589711/250000000000 : ℝ) (504206358851/1000000000000 : ℝ) (248575213007/500000000000 : ℝ) (497150426021/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33195/262144 : ℝ))) 2 (126051589711/250000000000 : ℝ) (504206358851/1000000000000 : ℝ) (248575213007/500000000000 : ℝ) (497150426021/1000000000000 : ℝ) (500678392429/1000000000000 : ℝ) (125169598109/250000000000 : ℝ) (15645811331/31250000000 : ℝ) (2503329813/5000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33195/262144 : ℝ))) 3 (500678392429/1000000000000 : ℝ) (125169598109/250000000000 : ℝ) (15645811331/31250000000 : ℝ) (2503329813/5000000000 : ℝ) (50067217751/100000000000 : ℝ) (250336088759/500000000000 : ℝ) (500672177471/1000000000000 : ℝ) (12516804437/25000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33195/262144 : ℝ))) 4 (50067217751/100000000000 : ℝ) (250336088759/500000000000 : ℝ) (500672177471/1000000000000 : ℝ) (12516804437/25000000000 : ℝ) (50067217749/100000000000 : ℝ) (500672177499/1000000000000 : ℝ) (50067217749/100000000000 : ℝ) (500672177499/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33195/262144 : ℝ))) 5 (50067217749/100000000000 : ℝ) (500672177499/1000000000000 : ℝ) (50067217749/100000000000 : ℝ) (500672177499/1000000000000 : ℝ) (50067217749/100000000000 : ℝ) (500672177499/1000000000000 : ℝ) (50067217749/100000000000 : ℝ) (500672177499/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33195/262144 : ℝ))) 6 (50067217749/100000000000 : ℝ) (500672177499/1000000000000 : ℝ) (50067217749/100000000000 : ℝ) (500672177499/1000000000000 : ℝ) (50067217749/100000000000 : ℝ) (500672177499/1000000000000 : ℝ) (50067217749/100000000000 : ℝ) (500672177499/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33195/262144 : ℝ))) 7 (50067217749/100000000000 : ℝ) (500672177499/1000000000000 : ℝ) (50067217749/100000000000 : ℝ) (500672177499/1000000000000 : ℝ) (50067217749/100000000000 : ℝ) (500672177499/1000000000000 : ℝ) (50067217749/100000000000 : ℝ) (500672177499/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33195/262144 : ℝ)) hmem 8 (992132466551/1000000000000 : ℝ) (496066233277/500000000000 : ℝ) (992132466551/1000000000000 : ℝ) (496066233277/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33195/262144 : ℝ))) hcmem 8 (50067217749/100000000000 : ℝ) (500672177499/1000000000000 : ℝ) (50067217749/100000000000 : ℝ) (500672177499/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33195/262144 : ℝ)) (992132466551/1000000000000 : ℝ) (496066233277/500000000000 : ℝ) (50067217749/100000000000 : ℝ) (500672177499/1000000000000 : ℝ) (792690536639/1000000000000 : ℝ) (49543158541/62500000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0414_exp_lower
  have heNumeric : (2054903494433/1000000000000 : ℝ)/4 ≤ Real.exp (-21314095219867/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054903494433/1000000000000 : ℝ)/4 ≤ Real.exp ((16597/131072 : ℝ)-(49543158541/62500000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16597/131072 : ℝ) (33195/262144 : ℝ) (49543158541/62500000000 : ℝ) (2054903494433/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0415; no trusted numerical premise.
theorem cover8_leaf0415_exp_radius : (499011660210702753/500000000000000000 : ℝ) ≤ Real.exp ((-8299/524288 : ℝ)/8) ∧ Real.exp ((-8299/524288 : ℝ)/8) ≤ (998023320421405507/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8299/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0415_exp_lower : (460056777553908491/500000000000000000 : ℝ) ≤ Real.exp ((-42628191790501/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628191790501/64000000000000 : ℝ)/8) ≤ (920113555107816983/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628191790501/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0415_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451725531/500000000000 : ℝ) ≤ 4*Real.exp (33195/262144 : ℝ)*Real.exp (-mu (radius 8 (8299/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451725531/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8299/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0415_exp_radius
  have hrNumeric : (984295535267/1000000000000 : ℝ) ≤ Real.exp (-8299/524288 : ℝ) ∧ Real.exp (-8299/524288 : ℝ) ≤ (246073883817/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984295535267/1000000000000 : ℝ) ≤ (radius 8 (8299/65536 : ℝ)) ∧ (radius 8 (8299/65536 : ℝ)) ≤ (246073883817/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8299/65536 : ℝ)) (984295535267/1000000000000 : ℝ) (246073883817/250000000000 : ℝ) (176528465839/1000000000000 : ℝ) (35305693169/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8299/65536 : ℝ)) (984295535267/1000000000000 : ℝ) (246073883817/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8299/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984295535267/1000000000000 : ℝ) (246073883817/250000000000 : ℝ) (992147767633/1000000000000 : ℝ) (496073883817/500000000000 : ℝ) (992116694379/1000000000000 : ℝ) (992116694381/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8299/65536 : ℝ)) 1 (992147767633/1000000000000 : ℝ) (496073883817/500000000000 : ℝ) (992116694379/1000000000000 : ℝ) (992116694381/1000000000000 : ℝ) (496066115503/500000000000 : ℝ) (31004132219/31250000000 : ℝ) (248033057721/250000000000 : ℝ) (496066115443/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8299/65536 : ℝ)) 2 (496066115503/500000000000 : ℝ) (31004132219/31250000000 : ℝ) (248033057721/250000000000 : ℝ) (496066115443/500000000000 : ℝ) (198426446189/200000000000 : ℝ) (992132230947/1000000000000 : ℝ) (31004132217/31250000000 : ℝ) (992132230947/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8299/65536 : ℝ)) 3 (198426446189/200000000000 : ℝ) (992132230947/1000000000000 : ℝ) (31004132217/31250000000 : ℝ) (992132230947/1000000000000 : ℝ) (31004132217/31250000000 : ℝ) (992132230947/1000000000000 : ℝ) (31004132217/31250000000 : ℝ) (992132230947/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8299/65536 : ℝ)) 4 (31004132217/31250000000 : ℝ) (992132230947/1000000000000 : ℝ) (31004132217/31250000000 : ℝ) (992132230947/1000000000000 : ℝ) (31004132217/31250000000 : ℝ) (992132230947/1000000000000 : ℝ) (31004132217/31250000000 : ℝ) (992132230947/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8299/65536 : ℝ)) 5 (31004132217/31250000000 : ℝ) (992132230947/1000000000000 : ℝ) (31004132217/31250000000 : ℝ) (992132230947/1000000000000 : ℝ) (31004132217/31250000000 : ℝ) (992132230947/1000000000000 : ℝ) (31004132217/31250000000 : ℝ) (992132230947/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8299/65536 : ℝ)) 6 (31004132217/31250000000 : ℝ) (992132230947/1000000000000 : ℝ) (31004132217/31250000000 : ℝ) (992132230947/1000000000000 : ℝ) (31004132217/31250000000 : ℝ) (992132230947/1000000000000 : ℝ) (31004132217/31250000000 : ℝ) (992132230947/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8299/65536 : ℝ)) 7 (31004132217/31250000000 : ℝ) (992132230947/1000000000000 : ℝ) (31004132217/31250000000 : ℝ) (992132230947/1000000000000 : ℝ) (31004132217/31250000000 : ℝ) (992132230947/1000000000000 : ℝ) (31004132217/31250000000 : ℝ) (992132230947/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8299/65536 : ℝ))) (176528465839/1000000000000 : ℝ) (35305693169/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8299/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176528465839/1000000000000 : ℝ) (35305693169/200000000000 : ℝ) (588264232919/1000000000000 : ℝ) (588264232923/1000000000000 : ℝ) (52519113461/125000000000 : ℝ) (26259556731/62500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8299/65536 : ℝ))) 1 (588264232919/1000000000000 : ℝ) (588264232923/1000000000000 : ℝ) (52519113461/125000000000 : ℝ) (26259556731/62500000000 : ℝ) (504208570303/1000000000000 : ℝ) (50420857031/100000000000 : ℝ) (124288205381/250000000000 : ℝ) (497152821531/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8299/65536 : ℝ))) 2 (504208570303/1000000000000 : ℝ) (50420857031/100000000000 : ℝ) (124288205381/250000000000 : ℝ) (497152821531/1000000000000 : ℝ) (500680695913/1000000000000 : ℝ) (500680695921/1000000000000 : ℝ) (250334133391/500000000000 : ℝ) (50066826679/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8299/65536 : ℝ))) 3 (500680695913/1000000000000 : ℝ) (500680695921/1000000000000 : ℝ) (250334133391/500000000000 : ℝ) (50066826679/100000000000 : ℝ) (500674481347/1000000000000 : ℝ) (125168620339/250000000000 : ℝ) (125168620327/250000000000 : ℝ) (500674481317/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8299/65536 : ℝ))) 4 (500674481347/1000000000000 : ℝ) (125168620339/250000000000 : ℝ) (125168620327/250000000000 : ℝ) (500674481317/1000000000000 : ℝ) (500674481327/1000000000000 : ℝ) (500674481337/1000000000000 : ℝ) (500674481327/1000000000000 : ℝ) (500674481337/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8299/65536 : ℝ))) 5 (500674481327/1000000000000 : ℝ) (500674481337/1000000000000 : ℝ) (500674481327/1000000000000 : ℝ) (500674481337/1000000000000 : ℝ) (500674481327/1000000000000 : ℝ) (500674481337/1000000000000 : ℝ) (500674481327/1000000000000 : ℝ) (500674481337/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8299/65536 : ℝ))) 6 (500674481327/1000000000000 : ℝ) (500674481337/1000000000000 : ℝ) (500674481327/1000000000000 : ℝ) (500674481337/1000000000000 : ℝ) (500674481327/1000000000000 : ℝ) (500674481337/1000000000000 : ℝ) (500674481327/1000000000000 : ℝ) (500674481337/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8299/65536 : ℝ))) 7 (500674481327/1000000000000 : ℝ) (500674481337/1000000000000 : ℝ) (500674481327/1000000000000 : ℝ) (500674481337/1000000000000 : ℝ) (500674481327/1000000000000 : ℝ) (500674481337/1000000000000 : ℝ) (500674481327/1000000000000 : ℝ) (500674481337/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8299/65536 : ℝ)) hmem 8 (31004132217/31250000000 : ℝ) (992132230947/1000000000000 : ℝ) (31004132217/31250000000 : ℝ) (992132230947/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8299/65536 : ℝ))) hcmem 8 (500674481327/1000000000000 : ℝ) (500674481337/1000000000000 : ℝ) (500674481327/1000000000000 : ℝ) (500674481337/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8299/65536 : ℝ)) (31004132217/31250000000 : ℝ) (992132230947/1000000000000 : ℝ) (500674481327/1000000000000 : ℝ) (500674481337/1000000000000 : ℝ) (19817359311/25000000000 : ℝ) (792694372459/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0415_exp_lower
  have heNumeric : (1027451725531/500000000000 : ℝ)/4 ≤ Real.exp (-42628191790501/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451725531/500000000000 : ℝ)/4 ≤ Real.exp ((33195/262144 : ℝ)-(792694372459/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33195/262144 : ℝ) (8299/65536 : ℝ) (792694372459/1000000000000 : ℝ) (1027451725531/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0416; no trusted numerical premise.
theorem cover8_leaf0416_exp_radius : (249505815233645447/250000000000000000 : ℝ) ≤ Real.exp ((-33197/2097152 : ℝ)/8) ∧ Real.exp ((-33197/2097152 : ℝ)/8) ≤ (998023260934581789/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33197/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0416_exp_lower : (460056776345239599/500000000000000000 : ℝ) ≤ Real.exp ((-10657048283909/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657048283909/16000000000000 : ℝ)/8) ≤ (920113552690479199/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657048283909/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0416_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054903407873/1000000000000 : ℝ) ≤ 4*Real.exp (8299/65536 : ℝ)*Real.exp (-mu (radius 8 (33197/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054903407873/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33197/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0416_exp_radius
  have hrNumeric : (984295065919/1000000000000 : ℝ) ≤ Real.exp (-33197/2097152 : ℝ) ∧ Real.exp (-33197/2097152 : ℝ) ≤ (3075922081/3125000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984295065919/1000000000000 : ℝ) ≤ (radius 8 (33197/262144 : ℝ)) ∧ (radius 8 (33197/262144 : ℝ)) ≤ (3075922081/3125000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33197/262144 : ℝ)) (984295065919/1000000000000 : ℝ) (3075922081/3125000000 : ℝ) (176531082831/1000000000000 : ℝ) (176531082837/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33197/262144 : ℝ)) (984295065919/1000000000000 : ℝ) (3075922081/3125000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33197/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984295065919/1000000000000 : ℝ) (3075922081/3125000000 : ℝ) (992147532959/1000000000000 : ℝ) (6200922081/6250000000 : ℝ) (992116457841/1000000000000 : ℝ) (496058228921/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33197/262144 : ℝ)) 1 (992147532959/1000000000000 : ℝ) (6200922081/6250000000 : ℝ) (992116457841/1000000000000 : ℝ) (496058228921/500000000000 : ℝ) (4960659977/5000000000 : ℝ) (992131995401/1000000000000 : ℝ) (496065997639/500000000000 : ℝ) (12401649941/12500000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33197/262144 : ℝ)) 2 (4960659977/5000000000 : ℝ) (992131995401/1000000000000 : ℝ) (496065997639/500000000000 : ℝ) (12401649941/12500000000 : ℝ) (992131995339/1000000000000 : ℝ) (992131995341/1000000000000 : ℝ) (496065997669/500000000000 : ℝ) (992131995341/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33197/262144 : ℝ)) 3 (992131995339/1000000000000 : ℝ) (992131995341/1000000000000 : ℝ) (496065997669/500000000000 : ℝ) (992131995341/1000000000000 : ℝ) (496065997669/500000000000 : ℝ) (992131995341/1000000000000 : ℝ) (496065997669/500000000000 : ℝ) (992131995341/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33197/262144 : ℝ)) 4 (496065997669/500000000000 : ℝ) (992131995341/1000000000000 : ℝ) (496065997669/500000000000 : ℝ) (992131995341/1000000000000 : ℝ) (496065997669/500000000000 : ℝ) (992131995341/1000000000000 : ℝ) (496065997669/500000000000 : ℝ) (992131995341/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33197/262144 : ℝ)) 5 (496065997669/500000000000 : ℝ) (992131995341/1000000000000 : ℝ) (496065997669/500000000000 : ℝ) (992131995341/1000000000000 : ℝ) (496065997669/500000000000 : ℝ) (992131995341/1000000000000 : ℝ) (496065997669/500000000000 : ℝ) (992131995341/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33197/262144 : ℝ)) 6 (496065997669/500000000000 : ℝ) (992131995341/1000000000000 : ℝ) (496065997669/500000000000 : ℝ) (992131995341/1000000000000 : ℝ) (496065997669/500000000000 : ℝ) (992131995341/1000000000000 : ℝ) (496065997669/500000000000 : ℝ) (992131995341/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33197/262144 : ℝ)) 7 (496065997669/500000000000 : ℝ) (992131995341/1000000000000 : ℝ) (496065997669/500000000000 : ℝ) (992131995341/1000000000000 : ℝ) (496065997669/500000000000 : ℝ) (992131995341/1000000000000 : ℝ) (496065997669/500000000000 : ℝ) (992131995341/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33197/262144 : ℝ))) (176531082831/1000000000000 : ℝ) (176531082837/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33197/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176531082831/1000000000000 : ℝ) (176531082837/1000000000000 : ℝ) (117653108283/200000000000 : ℝ) (588265541419/1000000000000 : ℝ) (420156022009/1000000000000 : ℝ) (420156022017/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33197/262144 : ℝ))) 1 (117653108283/200000000000 : ℝ) (588265541419/1000000000000 : ℝ) (420156022009/1000000000000 : ℝ) (420156022017/1000000000000 : ℝ) (31513173857/62500000000 : ℝ) (252105390859/500000000000 : ℝ) (19886208679/40000000000 : ℝ) (248577608491/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33197/262144 : ℝ))) 2 (31513173857/62500000000 : ℝ) (252105390859/500000000000 : ℝ) (19886208679/40000000000 : ℝ) (248577608491/500000000000 : ℝ) (500682999343/1000000000000 : ℝ) (10013659987/20000000000 : ℝ) (500670570917/1000000000000 : ℝ) (20026822837/40000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33197/262144 : ℝ))) 3 (500682999343/1000000000000 : ℝ) (10013659987/20000000000 : ℝ) (500670570917/1000000000000 : ℝ) (20026822837/40000000000 : ℝ) (50067678513/100000000000 : ℝ) (250338392569/500000000000 : ℝ) (500676785091/1000000000000 : ℝ) (500676785099/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33197/262144 : ℝ))) 4 (50067678513/100000000000 : ℝ) (250338392569/500000000000 : ℝ) (500676785091/1000000000000 : ℝ) (500676785099/1000000000000 : ℝ) (50067678511/100000000000 : ℝ) (500676785119/1000000000000 : ℝ) (50067678511/100000000000 : ℝ) (500676785119/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33197/262144 : ℝ))) 5 (50067678511/100000000000 : ℝ) (500676785119/1000000000000 : ℝ) (50067678511/100000000000 : ℝ) (500676785119/1000000000000 : ℝ) (50067678511/100000000000 : ℝ) (500676785119/1000000000000 : ℝ) (50067678511/100000000000 : ℝ) (500676785119/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33197/262144 : ℝ))) 6 (50067678511/100000000000 : ℝ) (500676785119/1000000000000 : ℝ) (50067678511/100000000000 : ℝ) (500676785119/1000000000000 : ℝ) (50067678511/100000000000 : ℝ) (500676785119/1000000000000 : ℝ) (50067678511/100000000000 : ℝ) (500676785119/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33197/262144 : ℝ))) 7 (50067678511/100000000000 : ℝ) (500676785119/1000000000000 : ℝ) (50067678511/100000000000 : ℝ) (500676785119/1000000000000 : ℝ) (50067678511/100000000000 : ℝ) (500676785119/1000000000000 : ℝ) (50067678511/100000000000 : ℝ) (500676785119/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33197/262144 : ℝ)) hmem 8 (496065997669/500000000000 : ℝ) (992131995341/1000000000000 : ℝ) (496065997669/500000000000 : ℝ) (992131995341/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33197/262144 : ℝ))) hcmem 8 (50067678511/100000000000 : ℝ) (500676785119/1000000000000 : ℝ) (50067678511/100000000000 : ℝ) (500676785119/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33197/262144 : ℝ)) (496065997669/500000000000 : ℝ) (992131995341/1000000000000 : ℝ) (50067678511/100000000000 : ℝ) (500676785119/1000000000000 : ℝ) (792698208157/1000000000000 : ℝ) (396349104087/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0416_exp_lower
  have heNumeric : (2054903407873/1000000000000 : ℝ)/4 ≤ Real.exp (-10657048283909/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054903407873/1000000000000 : ℝ)/4 ≤ Real.exp ((8299/65536 : ℝ)-(396349104087/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8299/65536 : ℝ) (33197/262144 : ℝ) (396349104087/500000000000 : ℝ) (2054903407873/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0417; no trusted numerical premise.
theorem cover8_leaf0417_exp_radius : (199604640289552323/200000000000000000 : ℝ) ≤ Real.exp ((-16599/1048576 : ℝ)/8) ∧ Real.exp ((-16599/1048576 : ℝ)/8) ≤ (62376450090485101/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16599/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0417_exp_lower : (920113550280617343/1000000000000000000 : ℝ) ≤ Real.exp ((-42628194476611/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628194476611/64000000000000 : ℝ)/8) ≤ (7188387111567323/7812500000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628194476611/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0417_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054903364817/1000000000000 : ℝ) ≤ 4*Real.exp (33197/262144 : ℝ)*Real.exp (-mu (radius 8 (16599/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054903364817/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16599/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0417_exp_radius
  have hrNumeric : (98429459657/100000000000 : ℝ) ≤ Real.exp (-16599/1048576 : ℝ) ∧ Real.exp (-16599/1048576 : ℝ) ≤ (984294596571/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (98429459657/100000000000 : ℝ) ≤ (radius 8 (16599/131072 : ℝ)) ∧ (radius 8 (16599/131072 : ℝ)) ≤ (984294596571/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16599/131072 : ℝ)) (98429459657/100000000000 : ℝ) (984294596571/1000000000000 : ℝ) (44133424947/250000000000 : ℝ) (35306739959/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16599/131072 : ℝ)) (98429459657/100000000000 : ℝ) (984294596571/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16599/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (98429459657/100000000000 : ℝ) (984294596571/1000000000000 : ℝ) (198429459657/200000000000 : ℝ) (496073649143/500000000000 : ℝ) (992116221301/1000000000000 : ℝ) (992116221303/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16599/131072 : ℝ)) 1 (198429459657/200000000000 : ℝ) (496073649143/500000000000 : ℝ) (992116221301/1000000000000 : ℝ) (992116221303/1000000000000 : ℝ) (992131759793/1000000000000 : ℝ) (198426351959/200000000000 : ℝ) (992131759671/1000000000000 : ℝ) (992131759673/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16599/131072 : ℝ)) 2 (992131759793/1000000000000 : ℝ) (198426351959/200000000000 : ℝ) (992131759671/1000000000000 : ℝ) (992131759673/1000000000000 : ℝ) (248032939933/250000000000 : ℝ) (496065879867/500000000000 : ℝ) (992131759731/1000000000000 : ℝ) (496065879867/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16599/131072 : ℝ)) 3 (248032939933/250000000000 : ℝ) (496065879867/500000000000 : ℝ) (992131759731/1000000000000 : ℝ) (496065879867/500000000000 : ℝ) (992131759731/1000000000000 : ℝ) (496065879867/500000000000 : ℝ) (992131759731/1000000000000 : ℝ) (496065879867/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16599/131072 : ℝ)) 4 (992131759731/1000000000000 : ℝ) (496065879867/500000000000 : ℝ) (992131759731/1000000000000 : ℝ) (496065879867/500000000000 : ℝ) (992131759731/1000000000000 : ℝ) (496065879867/500000000000 : ℝ) (992131759731/1000000000000 : ℝ) (496065879867/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16599/131072 : ℝ)) 5 (992131759731/1000000000000 : ℝ) (496065879867/500000000000 : ℝ) (992131759731/1000000000000 : ℝ) (496065879867/500000000000 : ℝ) (992131759731/1000000000000 : ℝ) (496065879867/500000000000 : ℝ) (992131759731/1000000000000 : ℝ) (496065879867/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16599/131072 : ℝ)) 6 (992131759731/1000000000000 : ℝ) (496065879867/500000000000 : ℝ) (992131759731/1000000000000 : ℝ) (496065879867/500000000000 : ℝ) (992131759731/1000000000000 : ℝ) (496065879867/500000000000 : ℝ) (992131759731/1000000000000 : ℝ) (496065879867/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16599/131072 : ℝ)) 7 (992131759731/1000000000000 : ℝ) (496065879867/500000000000 : ℝ) (992131759731/1000000000000 : ℝ) (496065879867/500000000000 : ℝ) (992131759731/1000000000000 : ℝ) (496065879867/500000000000 : ℝ) (992131759731/1000000000000 : ℝ) (496065879867/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16599/131072 : ℝ))) (44133424947/250000000000 : ℝ) (35306739959/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16599/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44133424947/250000000000 : ℝ) (35306739959/200000000000 : ℝ) (294133424947/500000000000 : ℝ) (294133424949/500000000000 : ℝ) (210079568133/500000000000 : ℝ) (16806365451/40000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16599/131072 : ℝ))) 1 (294133424947/500000000000 : ℝ) (294133424949/500000000000 : ℝ) (210079568133/500000000000 : ℝ) (16806365451/40000000000 : ℝ) (12605324827/25000000000 : ℝ) (504212993087/1000000000000 : ℝ) (497157612377/1000000000000 : ℝ) (248578806193/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16599/131072 : ℝ))) 2 (12605324827/25000000000 : ℝ) (504212993087/1000000000000 : ℝ) (497157612377/1000000000000 : ℝ) (248578806193/500000000000 : ℝ) (62585662841/125000000000 : ℝ) (500685302737/1000000000000 : ℝ) (977876709/1953125000 : ℝ) (500672875017/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16599/131072 : ℝ))) 3 (62585662841/125000000000 : ℝ) (500685302737/1000000000000 : ℝ) (977876709/1953125000 : ℝ) (500672875017/1000000000000 : ℝ) (125169772217/250000000000 : ℝ) (500679088877/1000000000000 : ℝ) (500679088829/1000000000000 : ℝ) (500679088839/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16599/131072 : ℝ))) 4 (125169772217/250000000000 : ℝ) (500679088877/1000000000000 : ℝ) (500679088829/1000000000000 : ℝ) (500679088839/1000000000000 : ℝ) (31292443053/62500000000 : ℝ) (250339544429/500000000000 : ℝ) (31292443053/62500000000 : ℝ) (250339544429/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16599/131072 : ℝ))) 5 (31292443053/62500000000 : ℝ) (250339544429/500000000000 : ℝ) (31292443053/62500000000 : ℝ) (250339544429/500000000000 : ℝ) (31292443053/62500000000 : ℝ) (250339544429/500000000000 : ℝ) (31292443053/62500000000 : ℝ) (250339544429/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16599/131072 : ℝ))) 6 (31292443053/62500000000 : ℝ) (250339544429/500000000000 : ℝ) (31292443053/62500000000 : ℝ) (250339544429/500000000000 : ℝ) (31292443053/62500000000 : ℝ) (250339544429/500000000000 : ℝ) (31292443053/62500000000 : ℝ) (250339544429/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16599/131072 : ℝ))) 7 (31292443053/62500000000 : ℝ) (250339544429/500000000000 : ℝ) (31292443053/62500000000 : ℝ) (250339544429/500000000000 : ℝ) (31292443053/62500000000 : ℝ) (250339544429/500000000000 : ℝ) (31292443053/62500000000 : ℝ) (250339544429/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16599/131072 : ℝ)) hmem 8 (992131759731/1000000000000 : ℝ) (496065879867/500000000000 : ℝ) (992131759731/1000000000000 : ℝ) (496065879867/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16599/131072 : ℝ))) hcmem 8 (31292443053/62500000000 : ℝ) (250339544429/500000000000 : ℝ) (31292443053/62500000000 : ℝ) (250339544429/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16599/131072 : ℝ)) (992131759731/1000000000000 : ℝ) (496065879867/500000000000 : ℝ) (31292443053/62500000000 : ℝ) (250339544429/500000000000 : ℝ) (158540408761/200000000000 : ℝ) (49543877739/62500000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0417_exp_lower
  have heNumeric : (2054903364817/1000000000000 : ℝ)/4 ≤ Real.exp (-42628194476611/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054903364817/1000000000000 : ℝ)/4 ≤ Real.exp ((33197/262144 : ℝ)-(49543877739/62500000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33197/262144 : ℝ) (16599/131072 : ℝ) (49543877739/62500000000 : ℝ) (2054903364817/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0418; no trusted numerical premise.
theorem cover8_leaf0418_exp_radius : (249505785490236247/250000000000000000 : ℝ) ≤ Real.exp ((-33199/2097152 : ℝ)/8) ∧ Real.exp ((-33199/2097152 : ℝ)/8) ≤ (998023141960944989/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33199/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0418_exp_lower : (920113547880761729/1000000000000000000 : ℝ) ≤ Real.exp ((-21314097906009/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314097906009/32000000000000 : ℝ)/8) ≤ (92011354788076173/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314097906009/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0418_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (102745166097/50000000000 : ℝ) ≤ 4*Real.exp (16599/131072 : ℝ)*Real.exp (-mu (radius 8 (33199/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (102745166097/50000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33199/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0418_exp_radius
  have hrNumeric : (492147063611/500000000000 : ℝ) ≤ Real.exp (-33199/2097152 : ℝ) ∧ Real.exp (-33199/2097152 : ℝ) ≤ (984294127223/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492147063611/500000000000 : ℝ) ≤ (radius 8 (33199/262144 : ℝ)) ∧ (radius 8 (33199/262144 : ℝ)) ≤ (984294127223/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33199/262144 : ℝ)) (492147063611/500000000000 : ℝ) (984294127223/1000000000000 : ℝ) (1765363167/10000000000 : ℝ) (176536316707/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33199/262144 : ℝ)) (492147063611/500000000000 : ℝ) (984294127223/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33199/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492147063611/500000000000 : ℝ) (984294127223/1000000000000 : ℝ) (992147063611/1000000000000 : ℝ) (248036765903/250000000000 : ℝ) (496057992381/500000000000 : ℝ) (248028996191/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33199/262144 : ℝ)) 1 (992147063611/1000000000000 : ℝ) (248036765903/250000000000 : ℝ) (496057992381/500000000000 : ℝ) (248028996191/250000000000 : ℝ) (496065762093/500000000000 : ℝ) (248032881047/250000000000 : ℝ) (31004110127/31250000000 : ℝ) (992131524067/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33199/262144 : ℝ)) 2 (496065762093/500000000000 : ℝ) (248032881047/250000000000 : ℝ) (31004110127/31250000000 : ℝ) (992131524067/1000000000000 : ℝ) (7937052193/8000000000 : ℝ) (31004110129/31250000000 : ℝ) (248032881031/250000000000 : ℝ) (31004110129/31250000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33199/262144 : ℝ)) 3 (7937052193/8000000000 : ℝ) (31004110129/31250000000 : ℝ) (248032881031/250000000000 : ℝ) (31004110129/31250000000 : ℝ) (248032881031/250000000000 : ℝ) (31004110129/31250000000 : ℝ) (248032881031/250000000000 : ℝ) (31004110129/31250000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33199/262144 : ℝ)) 4 (248032881031/250000000000 : ℝ) (31004110129/31250000000 : ℝ) (248032881031/250000000000 : ℝ) (31004110129/31250000000 : ℝ) (248032881031/250000000000 : ℝ) (31004110129/31250000000 : ℝ) (248032881031/250000000000 : ℝ) (31004110129/31250000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33199/262144 : ℝ)) 5 (248032881031/250000000000 : ℝ) (31004110129/31250000000 : ℝ) (248032881031/250000000000 : ℝ) (31004110129/31250000000 : ℝ) (248032881031/250000000000 : ℝ) (31004110129/31250000000 : ℝ) (248032881031/250000000000 : ℝ) (31004110129/31250000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33199/262144 : ℝ)) 6 (248032881031/250000000000 : ℝ) (31004110129/31250000000 : ℝ) (248032881031/250000000000 : ℝ) (31004110129/31250000000 : ℝ) (248032881031/250000000000 : ℝ) (31004110129/31250000000 : ℝ) (248032881031/250000000000 : ℝ) (31004110129/31250000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33199/262144 : ℝ)) 7 (248032881031/250000000000 : ℝ) (31004110129/31250000000 : ℝ) (248032881031/250000000000 : ℝ) (31004110129/31250000000 : ℝ) (248032881031/250000000000 : ℝ) (31004110129/31250000000 : ℝ) (248032881031/250000000000 : ℝ) (31004110129/31250000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33199/262144 : ℝ))) (1765363167/10000000000 : ℝ) (176536316707/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33199/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (1765363167/10000000000 : ℝ) (176536316707/1000000000000 : ℝ) (11765363167/20000000000 : ℝ) (294134079177/500000000000 : ℝ) (210081125223/500000000000 : ℝ) (84032450091/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33199/262144 : ℝ))) 1 (11765363167/20000000000 : ℝ) (294134079177/500000000000 : ℝ) (210081125223/500000000000 : ℝ) (84032450091/200000000000 : ℝ) (252107602199/500000000000 : ℝ) (100843040881/200000000000 : ℝ) (497160007721/1000000000000 : ℝ) (497160007729/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33199/262144 : ℝ))) 2 (252107602199/500000000000 : ℝ) (100843040881/200000000000 : ℝ) (497160007721/1000000000000 : ℝ) (497160007729/1000000000000 : ℝ) (500687606059/1000000000000 : ℝ) (500687606067/1000000000000 : ℝ) (125168794761/250000000000 : ℝ) (500675179053/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33199/262144 : ℝ))) 3 (500687606059/1000000000000 : ℝ) (500687606067/1000000000000 : ℝ) (125168794761/250000000000 : ℝ) (500675179053/1000000000000 : ℝ) (500681392551/1000000000000 : ℝ) (6258517407/12500000000 : ℝ) (3911573379/7812500000 : ℝ) (250340696261/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33199/262144 : ℝ))) 4 (500681392551/1000000000000 : ℝ) (6258517407/12500000000 : ℝ) (3911573379/7812500000 : ℝ) (250340696261/500000000000 : ℝ) (500681392531/1000000000000 : ℝ) (500681392541/1000000000000 : ℝ) (500681392531/1000000000000 : ℝ) (500681392541/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33199/262144 : ℝ))) 5 (500681392531/1000000000000 : ℝ) (500681392541/1000000000000 : ℝ) (500681392531/1000000000000 : ℝ) (500681392541/1000000000000 : ℝ) (500681392531/1000000000000 : ℝ) (500681392541/1000000000000 : ℝ) (500681392531/1000000000000 : ℝ) (500681392541/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33199/262144 : ℝ))) 6 (500681392531/1000000000000 : ℝ) (500681392541/1000000000000 : ℝ) (500681392531/1000000000000 : ℝ) (500681392541/1000000000000 : ℝ) (500681392531/1000000000000 : ℝ) (500681392541/1000000000000 : ℝ) (500681392531/1000000000000 : ℝ) (500681392541/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33199/262144 : ℝ))) 7 (500681392531/1000000000000 : ℝ) (500681392541/1000000000000 : ℝ) (500681392531/1000000000000 : ℝ) (500681392541/1000000000000 : ℝ) (500681392531/1000000000000 : ℝ) (500681392541/1000000000000 : ℝ) (500681392531/1000000000000 : ℝ) (500681392541/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33199/262144 : ℝ)) hmem 8 (248032881031/250000000000 : ℝ) (31004110129/31250000000 : ℝ) (248032881031/250000000000 : ℝ) (31004110129/31250000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33199/262144 : ℝ))) hcmem 8 (500681392531/1000000000000 : ℝ) (500681392541/1000000000000 : ℝ) (500681392531/1000000000000 : ℝ) (500681392541/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33199/262144 : ℝ)) (248032881031/250000000000 : ℝ) (31004110129/31250000000 : ℝ) (500681392531/1000000000000 : ℝ) (500681392541/1000000000000 : ℝ) (792705879367/1000000000000 : ℝ) (792705879387/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0418_exp_lower
  have heNumeric : (102745166097/50000000000 : ℝ)/4 ≤ Real.exp (-21314097906009/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (102745166097/50000000000 : ℝ)/4 ≤ Real.exp ((16599/131072 : ℝ)-(792705879387/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16599/131072 : ℝ) (33199/262144 : ℝ) (792705879387/1000000000000 : ℝ) (102745166097/50000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0419; no trusted numerical premise.
theorem cover8_leaf0419_exp_radius : (499011541237065953/500000000000000000 : ℝ) ≤ Real.exp ((-2075/131072 : ℝ)/8) ∧ Real.exp ((-2075/131072 : ℝ)/8) ≤ (998023082474131907/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2075/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0419_exp_lower : (460056772744766093/500000000000000000 : ℝ) ≤ Real.exp ((-341025577141/512000000000 : ℝ)/8) ∧ Real.exp ((-341025577141/512000000000 : ℝ)/8) ≤ (920113545489532187/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-341025577141/512000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0419_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054903279217/1000000000000 : ℝ) ≤ 4*Real.exp (33199/262144 : ℝ)*Real.exp (-mu (radius 8 (2075/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (2054903279217/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2075/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0419_exp_radius
  have hrNumeric : (492146828937/500000000000 : ℝ) ≤ Real.exp (-2075/131072 : ℝ) ∧ Real.exp (-2075/131072 : ℝ) ≤ (7874349263/8000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492146828937/500000000000 : ℝ) ≤ (radius 8 (2075/16384 : ℝ)) ∧ (radius 8 (2075/16384 : ℝ)) ≤ (7874349263/8000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2075/16384 : ℝ)) (492146828937/500000000000 : ℝ) (7874349263/8000000000 : ℝ) (44134733393/250000000000 : ℝ) (176538933579/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2075/16384 : ℝ)) (492146828937/500000000000 : ℝ) (7874349263/8000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2075/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492146828937/500000000000 : ℝ) (7874349263/8000000000 : ℝ) (992146828937/1000000000000 : ℝ) (496073414469/500000000000 : ℝ) (992115748223/1000000000000 : ℝ) (39684629929/40000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2075/16384 : ℝ)) 1 (992146828937/1000000000000 : ℝ) (496073414469/500000000000 : ℝ) (992115748223/1000000000000 : ℝ) (39684629929/40000000000 : ℝ) (49606564429/50000000000 : ℝ) (496065644291/500000000000 : ℝ) (496065644229/500000000000 : ℝ) (49606564423/50000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2075/16384 : ℝ)) 2 (49606564429/50000000000 : ℝ) (496065644291/500000000000 : ℝ) (496065644229/500000000000 : ℝ) (49606564423/50000000000 : ℝ) (992131288519/1000000000000 : ℝ) (992131288521/1000000000000 : ℝ) (496065644259/500000000000 : ℝ) (992131288521/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2075/16384 : ℝ)) 3 (992131288519/1000000000000 : ℝ) (992131288521/1000000000000 : ℝ) (496065644259/500000000000 : ℝ) (992131288521/1000000000000 : ℝ) (496065644259/500000000000 : ℝ) (992131288521/1000000000000 : ℝ) (496065644259/500000000000 : ℝ) (992131288521/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2075/16384 : ℝ)) 4 (496065644259/500000000000 : ℝ) (992131288521/1000000000000 : ℝ) (496065644259/500000000000 : ℝ) (992131288521/1000000000000 : ℝ) (496065644259/500000000000 : ℝ) (992131288521/1000000000000 : ℝ) (496065644259/500000000000 : ℝ) (992131288521/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2075/16384 : ℝ)) 5 (496065644259/500000000000 : ℝ) (992131288521/1000000000000 : ℝ) (496065644259/500000000000 : ℝ) (992131288521/1000000000000 : ℝ) (496065644259/500000000000 : ℝ) (992131288521/1000000000000 : ℝ) (496065644259/500000000000 : ℝ) (992131288521/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2075/16384 : ℝ)) 6 (496065644259/500000000000 : ℝ) (992131288521/1000000000000 : ℝ) (496065644259/500000000000 : ℝ) (992131288521/1000000000000 : ℝ) (496065644259/500000000000 : ℝ) (992131288521/1000000000000 : ℝ) (496065644259/500000000000 : ℝ) (992131288521/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2075/16384 : ℝ)) 7 (496065644259/500000000000 : ℝ) (992131288521/1000000000000 : ℝ) (496065644259/500000000000 : ℝ) (992131288521/1000000000000 : ℝ) (496065644259/500000000000 : ℝ) (992131288521/1000000000000 : ℝ) (496065644259/500000000000 : ℝ) (992131288521/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2075/16384 : ℝ))) (44134733393/250000000000 : ℝ) (176538933579/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2075/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44134733393/250000000000 : ℝ) (176538933579/1000000000000 : ℝ) (294134733393/500000000000 : ℝ) (58826946679/100000000000 : ℝ) (84033072911/200000000000 : ℝ) (105041341141/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2075/16384 : ℝ))) 1 (294134733393/500000000000 : ℝ) (58826946679/100000000000 : ℝ) (84033072911/200000000000 : ℝ) (105041341141/250000000000 : ℝ) (50421741567/100000000000 : ℝ) (504217415677/1000000000000 : ℝ) (124290600753/250000000000 : ℝ) (24858120151/50000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2075/16384 : ℝ))) 2 (50421741567/100000000000 : ℝ) (504217415677/1000000000000 : ℝ) (124290600753/250000000000 : ℝ) (24858120151/50000000000 : ℝ) (500689909341/1000000000000 : ℝ) (500689909349/1000000000000 : ℝ) (500677483031/1000000000000 : ℝ) (3129234269/6250000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2075/16384 : ℝ))) 3 (500689909341/1000000000000 : ℝ) (500689909349/1000000000000 : ℝ) (500677483031/1000000000000 : ℝ) (3129234269/6250000000 : ℝ) (250341848093/500000000000 : ℝ) (100136739239/200000000000 : ℝ) (500683696147/1000000000000 : ℝ) (125170924039/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2075/16384 : ℝ))) 4 (250341848093/500000000000 : ℝ) (100136739239/200000000000 : ℝ) (500683696147/1000000000000 : ℝ) (125170924039/250000000000 : ℝ) (250341848083/500000000000 : ℝ) (31292731011/62500000000 : ℝ) (250341848083/500000000000 : ℝ) (31292731011/62500000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2075/16384 : ℝ))) 5 (250341848083/500000000000 : ℝ) (31292731011/62500000000 : ℝ) (250341848083/500000000000 : ℝ) (31292731011/62500000000 : ℝ) (250341848083/500000000000 : ℝ) (31292731011/62500000000 : ℝ) (250341848083/500000000000 : ℝ) (31292731011/62500000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2075/16384 : ℝ))) 6 (250341848083/500000000000 : ℝ) (31292731011/62500000000 : ℝ) (250341848083/500000000000 : ℝ) (31292731011/62500000000 : ℝ) (250341848083/500000000000 : ℝ) (31292731011/62500000000 : ℝ) (250341848083/500000000000 : ℝ) (31292731011/62500000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2075/16384 : ℝ))) 7 (250341848083/500000000000 : ℝ) (31292731011/62500000000 : ℝ) (250341848083/500000000000 : ℝ) (31292731011/62500000000 : ℝ) (250341848083/500000000000 : ℝ) (31292731011/62500000000 : ℝ) (250341848083/500000000000 : ℝ) (31292731011/62500000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2075/16384 : ℝ)) hmem 8 (496065644259/500000000000 : ℝ) (992131288521/1000000000000 : ℝ) (496065644259/500000000000 : ℝ) (992131288521/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2075/16384 : ℝ))) hcmem 8 (250341848083/500000000000 : ℝ) (31292731011/62500000000 : ℝ) (250341848083/500000000000 : ℝ) (31292731011/62500000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2075/16384 : ℝ)) (496065644259/500000000000 : ℝ) (992131288521/1000000000000 : ℝ) (250341848083/500000000000 : ℝ) (31292731011/62500000000 : ℝ) (99088714357/125000000000 : ℝ) (6341677719/8000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0419_exp_lower
  have heNumeric : (2054903279217/1000000000000 : ℝ)/4 ≤ Real.exp (-341025577141/512000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054903279217/1000000000000 : ℝ)/4 ≤ Real.exp ((33199/262144 : ℝ)-(6341677719/8000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33199/262144 : ℝ) (2075/16384 : ℝ) (6341677719/8000000000 : ℝ) (2054903279217/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0420; no trusted numerical premise.
theorem cover8_leaf0420_exp_radius : (998023022987322371/1000000000000000000 : ℝ) ≤ Real.exp ((-33201/2097152 : ℝ)/8) ∧ Real.exp ((-33201/2097152 : ℝ)/8) ≤ (249505755746830593/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33201/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0420_exp_lower : (230028385777077221/250000000000000000 : ℝ) ≤ Real.exp ((-2664262404229/4000000000000 : ℝ)/8) ∧ Real.exp ((-2664262404229/4000000000000 : ℝ)/8) ≤ (184022708621661777/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2664262404229/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0420_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054903236673/1000000000000 : ℝ) ≤ 4*Real.exp (2075/16384 : ℝ)*Real.exp (-mu (radius 8 (33201/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054903236673/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33201/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0420_exp_radius
  have hrNumeric : (984293188527/1000000000000 : ℝ) ≤ Real.exp (-33201/2097152 : ℝ) ∧ Real.exp (-33201/2097152 : ℝ) ≤ (61518324283/62500000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984293188527/1000000000000 : ℝ) ≤ (radius 8 (33201/262144 : ℝ)) ∧ (radius 8 (33201/262144 : ℝ)) ≤ (61518324283/62500000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33201/262144 : ℝ)) (984293188527/1000000000000 : ℝ) (61518324283/62500000000 : ℝ) (176541550399/1000000000000 : ℝ) (35308310081/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33201/262144 : ℝ)) (984293188527/1000000000000 : ℝ) (61518324283/62500000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33201/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984293188527/1000000000000 : ℝ) (61518324283/62500000000 : ℝ) (992146594263/1000000000000 : ℝ) (124018324283/125000000000 : ℝ) (198423102337/200000000000 : ℝ) (992115511687/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33201/262144 : ℝ)) 1 (992146594263/1000000000000 : ℝ) (124018324283/125000000000 : ℝ) (198423102337/200000000000 : ℝ) (992115511687/1000000000000 : ℝ) (496065526487/500000000000 : ℝ) (62008190811/62500000000 : ℝ) (248032763213/250000000000 : ℝ) (496065526427/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33201/262144 : ℝ)) 2 (496065526487/500000000000 : ℝ) (62008190811/62500000000 : ℝ) (248032763213/250000000000 : ℝ) (496065526427/500000000000 : ℝ) (992131052913/1000000000000 : ℝ) (198426210583/200000000000 : ℝ) (62008190807/62500000000 : ℝ) (198426210583/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33201/262144 : ℝ)) 3 (992131052913/1000000000000 : ℝ) (198426210583/200000000000 : ℝ) (62008190807/62500000000 : ℝ) (198426210583/200000000000 : ℝ) (62008190807/62500000000 : ℝ) (198426210583/200000000000 : ℝ) (62008190807/62500000000 : ℝ) (198426210583/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33201/262144 : ℝ)) 4 (62008190807/62500000000 : ℝ) (198426210583/200000000000 : ℝ) (62008190807/62500000000 : ℝ) (198426210583/200000000000 : ℝ) (62008190807/62500000000 : ℝ) (198426210583/200000000000 : ℝ) (62008190807/62500000000 : ℝ) (198426210583/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33201/262144 : ℝ)) 5 (62008190807/62500000000 : ℝ) (198426210583/200000000000 : ℝ) (62008190807/62500000000 : ℝ) (198426210583/200000000000 : ℝ) (62008190807/62500000000 : ℝ) (198426210583/200000000000 : ℝ) (62008190807/62500000000 : ℝ) (198426210583/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33201/262144 : ℝ)) 6 (62008190807/62500000000 : ℝ) (198426210583/200000000000 : ℝ) (62008190807/62500000000 : ℝ) (198426210583/200000000000 : ℝ) (62008190807/62500000000 : ℝ) (198426210583/200000000000 : ℝ) (62008190807/62500000000 : ℝ) (198426210583/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33201/262144 : ℝ)) 7 (62008190807/62500000000 : ℝ) (198426210583/200000000000 : ℝ) (62008190807/62500000000 : ℝ) (198426210583/200000000000 : ℝ) (62008190807/62500000000 : ℝ) (198426210583/200000000000 : ℝ) (62008190807/62500000000 : ℝ) (198426210583/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33201/262144 : ℝ))) (176541550399/1000000000000 : ℝ) (35308310081/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33201/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176541550399/1000000000000 : ℝ) (35308310081/200000000000 : ℝ) (588270775199/1000000000000 : ℝ) (588270775203/1000000000000 : ℝ) (105042119647/250000000000 : ℝ) (105042119649/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33201/262144 : ℝ))) 1 (588270775199/1000000000000 : ℝ) (588270775203/1000000000000 : ℝ) (105042119647/250000000000 : ℝ) (105042119649/250000000000 : ℝ) (504219626893/1000000000000 : ℝ) (5042196269/10000000000 : ℝ) (124291199561/250000000000 : ℝ) (497164798251/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33201/262144 : ℝ))) 2 (504219626893/1000000000000 : ℝ) (5042196269/10000000000 : ℝ) (124291199561/250000000000 : ℝ) (497164798251/1000000000000 : ℝ) (62586526571/125000000000 : ℝ) (15646631643/31250000000 : ℝ) (125169946741/250000000000 : ℝ) (125169946743/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33201/262144 : ℝ))) 3 (62586526571/125000000000 : ℝ) (15646631643/31250000000 : ℝ) (125169946741/250000000000 : ℝ) (125169946743/250000000000 : ℝ) (250342999883/500000000000 : ℝ) (250342999887/500000000000 : ℝ) (500685999727/1000000000000 : ℝ) (62585749967/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33201/262144 : ℝ))) 4 (250342999883/500000000000 : ℝ) (250342999887/500000000000 : ℝ) (500685999727/1000000000000 : ℝ) (62585749967/125000000000 : ℝ) (250342999873/500000000000 : ℝ) (100137199951/200000000000 : ℝ) (250342999873/500000000000 : ℝ) (100137199951/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33201/262144 : ℝ))) 5 (250342999873/500000000000 : ℝ) (100137199951/200000000000 : ℝ) (250342999873/500000000000 : ℝ) (100137199951/200000000000 : ℝ) (250342999873/500000000000 : ℝ) (100137199951/200000000000 : ℝ) (250342999873/500000000000 : ℝ) (100137199951/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33201/262144 : ℝ))) 6 (250342999873/500000000000 : ℝ) (100137199951/200000000000 : ℝ) (250342999873/500000000000 : ℝ) (100137199951/200000000000 : ℝ) (250342999873/500000000000 : ℝ) (100137199951/200000000000 : ℝ) (250342999873/500000000000 : ℝ) (100137199951/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33201/262144 : ℝ))) 7 (250342999873/500000000000 : ℝ) (100137199951/200000000000 : ℝ) (250342999873/500000000000 : ℝ) (100137199951/200000000000 : ℝ) (250342999873/500000000000 : ℝ) (100137199951/200000000000 : ℝ) (250342999873/500000000000 : ℝ) (100137199951/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33201/262144 : ℝ)) hmem 8 (62008190807/62500000000 : ℝ) (198426210583/200000000000 : ℝ) (62008190807/62500000000 : ℝ) (198426210583/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33201/262144 : ℝ))) hcmem 8 (250342999873/500000000000 : ℝ) (100137199951/200000000000 : ℝ) (250342999873/500000000000 : ℝ) (100137199951/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33201/262144 : ℝ)) (62008190807/62500000000 : ℝ) (198426210583/200000000000 : ℝ) (250342999873/500000000000 : ℝ) (100137199951/200000000000 : ℝ) (792713550259/1000000000000 : ℝ) (198178387569/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0420_exp_lower
  have heNumeric : (2054903236673/1000000000000 : ℝ)/4 ≤ Real.exp (-2664262404229/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054903236673/1000000000000 : ℝ)/4 ≤ Real.exp ((2075/16384 : ℝ)-(198178387569/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2075/16384 : ℝ) (33201/262144 : ℝ) (198178387569/250000000000 : ℝ) (2054903236673/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0421; no trusted numerical premise.
theorem cover8_leaf0421_exp_radius : (998022963500516381/1000000000000000000 : ℝ) ≤ Real.exp ((-16601/1048576 : ℝ)/8) ∧ Real.exp ((-16601/1048576 : ℝ)/8) ≤ (499011481750258191/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16601/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0421_exp_lower : (920113540734791539/1000000000000000000 : ℝ) ≤ Real.exp ((-8525639957683/12800000000000 : ℝ)/8) ∧ Real.exp ((-8525639957683/12800000000000 : ℝ)/8) ≤ (46005677036739577/50000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8525639957683/12800000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0421_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451597133/500000000000 : ℝ) ≤ 4*Real.exp (33201/262144 : ℝ)*Real.exp (-mu (radius 8 (16601/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451597133/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16601/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0421_exp_radius
  have hrNumeric : (984292719179/1000000000000 : ℝ) ≤ Real.exp (-16601/1048576 : ℝ) ∧ Real.exp (-16601/1048576 : ℝ) ≤ (49214635959/50000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984292719179/1000000000000 : ℝ) ≤ (radius 8 (16601/131072 : ℝ)) ∧ (radius 8 (16601/131072 : ℝ)) ≤ (49214635959/50000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16601/131072 : ℝ)) (984292719179/1000000000000 : ℝ) (49214635959/50000000000 : ℝ) (176544167191/1000000000000 : ℝ) (176544167197/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16601/131072 : ℝ)) (984292719179/1000000000000 : ℝ) (49214635959/50000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16601/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984292719179/1000000000000 : ℝ) (49214635959/50000000000 : ℝ) (992146359589/1000000000000 : ℝ) (99214635959/100000000000 : ℝ) (496057637573/500000000000 : ℝ) (992115275147/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16601/131072 : ℝ)) 1 (992146359589/1000000000000 : ℝ) (99214635959/100000000000 : ℝ) (496057637573/500000000000 : ℝ) (992115275147/1000000000000 : ℝ) (992130817367/1000000000000 : ℝ) (992130817369/1000000000000 : ℝ) (198426163449/200000000000 : ℝ) (992130817247/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16601/131072 : ℝ)) 2 (992130817367/1000000000000 : ℝ) (992130817369/1000000000000 : ℝ) (198426163449/200000000000 : ℝ) (992130817247/1000000000000 : ℝ) (496065408653/500000000000 : ℝ) (248032704327/250000000000 : ℝ) (198426163461/200000000000 : ℝ) (248032704327/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16601/131072 : ℝ)) 3 (496065408653/500000000000 : ℝ) (248032704327/250000000000 : ℝ) (198426163461/200000000000 : ℝ) (248032704327/250000000000 : ℝ) (198426163461/200000000000 : ℝ) (248032704327/250000000000 : ℝ) (198426163461/200000000000 : ℝ) (248032704327/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16601/131072 : ℝ)) 4 (198426163461/200000000000 : ℝ) (248032704327/250000000000 : ℝ) (198426163461/200000000000 : ℝ) (248032704327/250000000000 : ℝ) (198426163461/200000000000 : ℝ) (248032704327/250000000000 : ℝ) (198426163461/200000000000 : ℝ) (248032704327/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16601/131072 : ℝ)) 5 (198426163461/200000000000 : ℝ) (248032704327/250000000000 : ℝ) (198426163461/200000000000 : ℝ) (248032704327/250000000000 : ℝ) (198426163461/200000000000 : ℝ) (248032704327/250000000000 : ℝ) (198426163461/200000000000 : ℝ) (248032704327/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16601/131072 : ℝ)) 6 (198426163461/200000000000 : ℝ) (248032704327/250000000000 : ℝ) (198426163461/200000000000 : ℝ) (248032704327/250000000000 : ℝ) (198426163461/200000000000 : ℝ) (248032704327/250000000000 : ℝ) (198426163461/200000000000 : ℝ) (248032704327/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16601/131072 : ℝ)) 7 (198426163461/200000000000 : ℝ) (248032704327/250000000000 : ℝ) (198426163461/200000000000 : ℝ) (248032704327/250000000000 : ℝ) (198426163461/200000000000 : ℝ) (248032704327/250000000000 : ℝ) (198426163461/200000000000 : ℝ) (248032704327/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16601/131072 : ℝ))) (176544167191/1000000000000 : ℝ) (176544167197/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16601/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176544167191/1000000000000 : ℝ) (176544167197/1000000000000 : ℝ) (117654416719/200000000000 : ℝ) (588272083599/1000000000000 : ℝ) (84034318511/200000000000 : ℝ) (105042898141/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16601/131072 : ℝ))) 1 (117654416719/200000000000 : ℝ) (588272083599/1000000000000 : ℝ) (84034318511/200000000000 : ℝ) (105042898141/250000000000 : ℝ) (20168873523/40000000000 : ℝ) (252110919041/500000000000 : ℝ) (248583596713/500000000000 : ℝ) (248583596717/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16601/131072 : ℝ))) 2 (20168873523/40000000000 : ℝ) (252110919041/500000000000 : ℝ) (248583596713/500000000000 : ℝ) (248583596717/500000000000 : ℝ) (2002778063/4000000000 : ℝ) (250347257879/500000000000 : ℝ) (500682090851/1000000000000 : ℝ) (25034104543/50000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16601/131072 : ℝ))) 3 (2002778063/4000000000 : ℝ) (250347257879/500000000000 : ℝ) (500682090851/1000000000000 : ℝ) (25034104543/50000000000 : ℝ) (5006883033/10000000000 : ℝ) (500688303309/1000000000000 : ℝ) (500688303261/1000000000000 : ℝ) (500688303271/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16601/131072 : ℝ))) 4 (5006883033/10000000000 : ℝ) (500688303309/1000000000000 : ℝ) (500688303261/1000000000000 : ℝ) (500688303271/1000000000000 : ℝ) (6258603791/12500000000 : ℝ) (50068830329/100000000000 : ℝ) (6258603791/12500000000 : ℝ) (50068830329/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16601/131072 : ℝ))) 5 (6258603791/12500000000 : ℝ) (50068830329/100000000000 : ℝ) (6258603791/12500000000 : ℝ) (50068830329/100000000000 : ℝ) (6258603791/12500000000 : ℝ) (50068830329/100000000000 : ℝ) (6258603791/12500000000 : ℝ) (50068830329/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16601/131072 : ℝ))) 6 (6258603791/12500000000 : ℝ) (50068830329/100000000000 : ℝ) (6258603791/12500000000 : ℝ) (50068830329/100000000000 : ℝ) (6258603791/12500000000 : ℝ) (50068830329/100000000000 : ℝ) (6258603791/12500000000 : ℝ) (50068830329/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16601/131072 : ℝ))) 7 (6258603791/12500000000 : ℝ) (50068830329/100000000000 : ℝ) (6258603791/12500000000 : ℝ) (50068830329/100000000000 : ℝ) (6258603791/12500000000 : ℝ) (50068830329/100000000000 : ℝ) (6258603791/12500000000 : ℝ) (50068830329/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16601/131072 : ℝ)) hmem 8 (198426163461/200000000000 : ℝ) (248032704327/250000000000 : ℝ) (198426163461/200000000000 : ℝ) (248032704327/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16601/131072 : ℝ))) hcmem 8 (6258603791/12500000000 : ℝ) (50068830329/100000000000 : ℝ) (6258603791/12500000000 : ℝ) (50068830329/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16601/131072 : ℝ)) (198426163461/200000000000 : ℝ) (248032704327/250000000000 : ℝ) (6258603791/12500000000 : ℝ) (50068830329/100000000000 : ℝ) (792717385591/1000000000000 : ℝ) (79271738561/100000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0421_exp_lower
  have heNumeric : (1027451597133/500000000000 : ℝ)/4 ≤ Real.exp (-8525639957683/12800000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451597133/500000000000 : ℝ)/4 ≤ Real.exp ((33201/262144 : ℝ)-(79271738561/100000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33201/262144 : ℝ) (16601/131072 : ℝ) (79271738561/100000000000 : ℝ) (1027451597133/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0422; no trusted numerical premise.
theorem cover8_leaf0422_exp_radius : (998022904013713937/1000000000000000000 : ℝ) ≤ Real.exp ((-33203/2097152 : ℝ)/8) ∧ Real.exp ((-33203/2097152 : ℝ)/8) ≤ (499011452006856969/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33203/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0422_exp_lower : (230028384592676341/250000000000000000 : ℝ) ≤ Real.exp ((-21314100551959/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314100551959/32000000000000 : ℝ)/8) ≤ (184022707674141073/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314100551959/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0422_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513725788007/250000000000 : ℝ) ≤ 4*Real.exp (16601/131072 : ℝ)*Real.exp (-mu (radius 8 (33203/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (513725788007/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33203/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0422_exp_radius
  have hrNumeric : (123036531229/125000000000 : ℝ) ≤ Real.exp (-33203/2097152 : ℝ) ∧ Real.exp (-33203/2097152 : ℝ) ≤ (984292249833/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (123036531229/125000000000 : ℝ) ≤ (radius 8 (33203/262144 : ℝ)) ∧ (radius 8 (33203/262144 : ℝ)) ≤ (984292249833/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33203/262144 : ℝ)) (123036531229/125000000000 : ℝ) (984292249833/1000000000000 : ℝ) (176546783937/1000000000000 : ℝ) (22068347993/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33203/262144 : ℝ)) (123036531229/125000000000 : ℝ) (984292249833/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33203/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (123036531229/125000000000 : ℝ) (984292249833/1000000000000 : ℝ) (248036531229/250000000000 : ℝ) (992146124917/1000000000000 : ℝ) (992115038607/1000000000000 : ℝ) (992115038609/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33203/262144 : ℝ)) 1 (248036531229/250000000000 : ℝ) (992146124917/1000000000000 : ℝ) (992115038607/1000000000000 : ℝ) (992115038609/1000000000000 : ℝ) (992130581761/1000000000000 : ℝ) (992130581763/1000000000000 : ℝ) (992130581639/1000000000000 : ℝ) (496065290821/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33203/262144 : ℝ)) 2 (992130581761/1000000000000 : ℝ) (992130581763/1000000000000 : ℝ) (992130581639/1000000000000 : ℝ) (496065290821/500000000000 : ℝ) (9921305817/10000000000 : ℝ) (992130581703/1000000000000 : ℝ) (992130581699/1000000000000 : ℝ) (992130581703/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33203/262144 : ℝ)) 3 (9921305817/10000000000 : ℝ) (992130581703/1000000000000 : ℝ) (992130581699/1000000000000 : ℝ) (992130581703/1000000000000 : ℝ) (992130581699/1000000000000 : ℝ) (992130581703/1000000000000 : ℝ) (992130581699/1000000000000 : ℝ) (992130581703/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33203/262144 : ℝ)) 4 (992130581699/1000000000000 : ℝ) (992130581703/1000000000000 : ℝ) (992130581699/1000000000000 : ℝ) (992130581703/1000000000000 : ℝ) (992130581699/1000000000000 : ℝ) (992130581703/1000000000000 : ℝ) (992130581699/1000000000000 : ℝ) (992130581703/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33203/262144 : ℝ)) 5 (992130581699/1000000000000 : ℝ) (992130581703/1000000000000 : ℝ) (992130581699/1000000000000 : ℝ) (992130581703/1000000000000 : ℝ) (992130581699/1000000000000 : ℝ) (992130581703/1000000000000 : ℝ) (992130581699/1000000000000 : ℝ) (992130581703/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33203/262144 : ℝ)) 6 (992130581699/1000000000000 : ℝ) (992130581703/1000000000000 : ℝ) (992130581699/1000000000000 : ℝ) (992130581703/1000000000000 : ℝ) (992130581699/1000000000000 : ℝ) (992130581703/1000000000000 : ℝ) (992130581699/1000000000000 : ℝ) (992130581703/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33203/262144 : ℝ)) 7 (992130581699/1000000000000 : ℝ) (992130581703/1000000000000 : ℝ) (992130581699/1000000000000 : ℝ) (992130581703/1000000000000 : ℝ) (992130581699/1000000000000 : ℝ) (992130581703/1000000000000 : ℝ) (992130581699/1000000000000 : ℝ) (992130581703/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33203/262144 : ℝ))) (176546783937/1000000000000 : ℝ) (22068347993/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33203/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176546783937/1000000000000 : ℝ) (22068347993/125000000000 : ℝ) (18383543499/31250000000 : ℝ) (147068347993/250000000000 : ℝ) (210087353223/500000000000 : ℝ) (84034941291/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33203/262144 : ℝ))) 1 (18383543499/31250000000 : ℝ) (147068347993/250000000000 : ℝ) (210087353223/500000000000 : ℝ) (84034941291/200000000000 : ℝ) (504224049207/1000000000000 : ℝ) (252112024607/500000000000 : ℝ) (497169588551/1000000000000 : ℝ) (497169588559/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33203/262144 : ℝ))) 2 (504224049207/1000000000000 : ℝ) (252112024607/500000000000 : ℝ) (497169588551/1000000000000 : ℝ) (497169588559/1000000000000 : ℝ) (500696818879/1000000000000 : ℝ) (500696818887/1000000000000 : ℝ) (100136878937/200000000000 : ℝ) (250342197347/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33203/262144 : ℝ))) 3 (500696818879/1000000000000 : ℝ) (500696818887/1000000000000 : ℝ) (100136878937/200000000000 : ℝ) (250342197347/500000000000 : ℝ) (250345303391/500000000000 : ℝ) (500690606791/1000000000000 : ℝ) (500690606743/1000000000000 : ℝ) (15646581461/31250000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33203/262144 : ℝ))) 4 (250345303391/500000000000 : ℝ) (500690606791/1000000000000 : ℝ) (500690606743/1000000000000 : ℝ) (15646581461/31250000000 : ℝ) (250345303381/500000000000 : ℝ) (125172651693/250000000000 : ℝ) (250345303381/500000000000 : ℝ) (125172651693/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33203/262144 : ℝ))) 5 (250345303381/500000000000 : ℝ) (125172651693/250000000000 : ℝ) (250345303381/500000000000 : ℝ) (125172651693/250000000000 : ℝ) (250345303381/500000000000 : ℝ) (125172651693/250000000000 : ℝ) (250345303381/500000000000 : ℝ) (125172651693/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33203/262144 : ℝ))) 6 (250345303381/500000000000 : ℝ) (125172651693/250000000000 : ℝ) (250345303381/500000000000 : ℝ) (125172651693/250000000000 : ℝ) (250345303381/500000000000 : ℝ) (125172651693/250000000000 : ℝ) (250345303381/500000000000 : ℝ) (125172651693/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33203/262144 : ℝ))) 7 (250345303381/500000000000 : ℝ) (125172651693/250000000000 : ℝ) (250345303381/500000000000 : ℝ) (125172651693/250000000000 : ℝ) (250345303381/500000000000 : ℝ) (125172651693/250000000000 : ℝ) (250345303381/500000000000 : ℝ) (125172651693/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33203/262144 : ℝ)) hmem 8 (992130581699/1000000000000 : ℝ) (992130581703/1000000000000 : ℝ) (992130581699/1000000000000 : ℝ) (992130581703/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33203/262144 : ℝ))) hcmem 8 (250345303381/500000000000 : ℝ) (125172651693/250000000000 : ℝ) (250345303381/500000000000 : ℝ) (125172651693/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33203/262144 : ℝ)) (992130581699/1000000000000 : ℝ) (992130581703/1000000000000 : ℝ) (250345303381/500000000000 : ℝ) (125172651693/250000000000 : ℝ) (396360610421/500000000000 : ℝ) (396360610431/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0422_exp_lower
  have heNumeric : (513725788007/250000000000 : ℝ)/4 ≤ Real.exp (-21314100551959/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513725788007/250000000000 : ℝ)/4 ≤ Real.exp ((16601/131072 : ℝ)-(396360610431/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16601/131072 : ℝ) (33203/262144 : ℝ) (396360610431/500000000000 : ℝ) (513725788007/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0423; no trusted numerical premise.
theorem cover8_leaf0423_exp_radius : (499011422263457519/500000000000000000 : ℝ) ≤ Real.exp ((-8301/524288 : ℝ)/8) ∧ Real.exp ((-8301/524288 : ℝ)/8) ≤ (998022844526915039/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8301/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0423_exp_lower : (920113536016050359/1000000000000000000 : ℝ) ≤ Real.exp ((-42628202414173/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628202414173/64000000000000 : ℝ)/8) ≤ (23002838400401259/25000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628202414173/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0423_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054903109959/1000000000000 : ℝ) ≤ 4*Real.exp (33203/262144 : ℝ)*Real.exp (-mu (radius 8 (8301/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (2054903109959/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8301/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0423_exp_radius
  have hrNumeric : (196858356097/200000000000 : ℝ) ≤ Real.exp (-8301/524288 : ℝ) ∧ Real.exp (-8301/524288 : ℝ) ≤ (492145890243/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196858356097/200000000000 : ℝ) ≤ (radius 8 (8301/65536 : ℝ)) ∧ (radius 8 (8301/65536 : ℝ)) ≤ (492145890243/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8301/65536 : ℝ)) (196858356097/200000000000 : ℝ) (492145890243/500000000000 : ℝ) (176549400643/1000000000000 : ℝ) (3530988013/20000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8301/65536 : ℝ)) (196858356097/200000000000 : ℝ) (492145890243/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8301/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196858356097/200000000000 : ℝ) (492145890243/500000000000 : ℝ) (496072945121/500000000000 : ℝ) (992145890243/1000000000000 : ℝ) (992114802069/1000000000000 : ℝ) (99211480207/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8301/65536 : ℝ)) 1 (496072945121/500000000000 : ℝ) (992145890243/1000000000000 : ℝ) (992114802069/1000000000000 : ℝ) (99211480207/100000000000 : ℝ) (198426069231/200000000000 : ℝ) (992130346157/1000000000000 : ℝ) (992130346033/1000000000000 : ℝ) (198426069207/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8301/65536 : ℝ)) 2 (198426069231/200000000000 : ℝ) (992130346157/1000000000000 : ℝ) (992130346033/1000000000000 : ℝ) (198426069207/200000000000 : ℝ) (496065173047/500000000000 : ℝ) (62008146631/62500000000 : ℝ) (992130346093/1000000000000 : ℝ) (62008146631/62500000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8301/65536 : ℝ)) 3 (496065173047/500000000000 : ℝ) (62008146631/62500000000 : ℝ) (992130346093/1000000000000 : ℝ) (62008146631/62500000000 : ℝ) (992130346093/1000000000000 : ℝ) (62008146631/62500000000 : ℝ) (992130346093/1000000000000 : ℝ) (62008146631/62500000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8301/65536 : ℝ)) 4 (992130346093/1000000000000 : ℝ) (62008146631/62500000000 : ℝ) (992130346093/1000000000000 : ℝ) (62008146631/62500000000 : ℝ) (992130346093/1000000000000 : ℝ) (62008146631/62500000000 : ℝ) (992130346093/1000000000000 : ℝ) (62008146631/62500000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8301/65536 : ℝ)) 5 (992130346093/1000000000000 : ℝ) (62008146631/62500000000 : ℝ) (992130346093/1000000000000 : ℝ) (62008146631/62500000000 : ℝ) (992130346093/1000000000000 : ℝ) (62008146631/62500000000 : ℝ) (992130346093/1000000000000 : ℝ) (62008146631/62500000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8301/65536 : ℝ)) 6 (992130346093/1000000000000 : ℝ) (62008146631/62500000000 : ℝ) (992130346093/1000000000000 : ℝ) (62008146631/62500000000 : ℝ) (992130346093/1000000000000 : ℝ) (62008146631/62500000000 : ℝ) (992130346093/1000000000000 : ℝ) (62008146631/62500000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8301/65536 : ℝ)) 7 (992130346093/1000000000000 : ℝ) (62008146631/62500000000 : ℝ) (992130346093/1000000000000 : ℝ) (62008146631/62500000000 : ℝ) (992130346093/1000000000000 : ℝ) (62008146631/62500000000 : ℝ) (992130346093/1000000000000 : ℝ) (62008146631/62500000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8301/65536 : ℝ))) (176549400643/1000000000000 : ℝ) (3530988013/20000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8301/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176549400643/1000000000000 : ℝ) (3530988013/20000000000 : ℝ) (588274700321/1000000000000 : ℝ) (23530988013/40000000000 : ℝ) (84035564053/200000000000 : ℝ) (210088910137/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8301/65536 : ℝ))) 1 (588274700321/1000000000000 : ℝ) (23530988013/40000000000 : ℝ) (84035564053/200000000000 : ℝ) (210088910137/500000000000 : ℝ) (504226260293/1000000000000 : ℝ) (5042262603/10000000000 : ℝ) (497171983621/1000000000000 : ℝ) (497171983629/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8301/65536 : ℝ))) 2 (504226260293/1000000000000 : ℝ) (5042262603/10000000000 : ℝ) (497171983621/1000000000000 : ℝ) (497171983629/1000000000000 : ℝ) (500699121957/1000000000000 : ℝ) (100139824393/200000000000 : ℝ) (125171674617/250000000000 : ℝ) (500686698477/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8301/65536 : ℝ))) 3 (500699121957/1000000000000 : ℝ) (100139824393/200000000000 : ℝ) (125171674617/250000000000 : ℝ) (500686698477/1000000000000 : ℝ) (125173227553/250000000000 : ℝ) (500692910221/1000000000000 : ℝ) (500692910173/1000000000000 : ℝ) (500692910183/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8301/65536 : ℝ))) 4 (125173227553/250000000000 : ℝ) (500692910221/1000000000000 : ℝ) (500692910173/1000000000000 : ℝ) (500692910183/1000000000000 : ℝ) (31293306887/62500000000 : ℝ) (250346455101/500000000000 : ℝ) (31293306887/62500000000 : ℝ) (250346455101/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8301/65536 : ℝ))) 5 (31293306887/62500000000 : ℝ) (250346455101/500000000000 : ℝ) (31293306887/62500000000 : ℝ) (250346455101/500000000000 : ℝ) (31293306887/62500000000 : ℝ) (250346455101/500000000000 : ℝ) (31293306887/62500000000 : ℝ) (250346455101/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8301/65536 : ℝ))) 6 (31293306887/62500000000 : ℝ) (250346455101/500000000000 : ℝ) (31293306887/62500000000 : ℝ) (250346455101/500000000000 : ℝ) (31293306887/62500000000 : ℝ) (250346455101/500000000000 : ℝ) (31293306887/62500000000 : ℝ) (250346455101/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8301/65536 : ℝ))) 7 (31293306887/62500000000 : ℝ) (250346455101/500000000000 : ℝ) (31293306887/62500000000 : ℝ) (250346455101/500000000000 : ℝ) (31293306887/62500000000 : ℝ) (250346455101/500000000000 : ℝ) (31293306887/62500000000 : ℝ) (250346455101/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8301/65536 : ℝ)) hmem 8 (992130346093/1000000000000 : ℝ) (62008146631/62500000000 : ℝ) (992130346093/1000000000000 : ℝ) (62008146631/62500000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8301/65536 : ℝ))) hcmem 8 (31293306887/62500000000 : ℝ) (250346455101/500000000000 : ℝ) (31293306887/62500000000 : ℝ) (250346455101/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8301/65536 : ℝ)) (992130346093/1000000000000 : ℝ) (62008146631/62500000000 : ℝ) (31293306887/62500000000 : ℝ) (250346455101/500000000000 : ℝ) (792725056013/1000000000000 : ℝ) (24772658001/31250000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0423_exp_lower
  have heNumeric : (2054903109959/1000000000000 : ℝ)/4 ≤ Real.exp (-42628202414173/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054903109959/1000000000000 : ℝ)/4 ≤ Real.exp ((33203/262144 : ℝ)-(24772658001/31250000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33203/262144 : ℝ) (8301/65536 : ℝ) (24772658001/31250000000 : ℝ) (2054903109959/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0424; no trusted numerical premise.
theorem cover8_leaf0424_exp_radius : (199604557008023937/200000000000000000 : ℝ) ≤ Real.exp ((-33205/2097152 : ℝ)/8) ∧ Real.exp ((-33205/2097152 : ℝ)/8) ≤ (499011392520059843/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33205/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0424_exp_lower : (230028383417447849/250000000000000000 : ℝ) ≤ Real.exp ((-10657050929939/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657050929939/16000000000000 : ℝ)/8) ≤ (920113533669791397/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657050929939/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0424_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054903068039/1000000000000 : ℝ) ≤ 4*Real.exp (8301/65536 : ℝ)*Real.exp (-mu (radius 8 (33205/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054903068039/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33205/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0424_exp_radius
  have hrNumeric : (492145655569/500000000000 : ℝ) ≤ Real.exp (-33205/2097152 : ℝ) ∧ Real.exp (-33205/2097152 : ℝ) ≤ (984291311139/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492145655569/500000000000 : ℝ) ≤ (radius 8 (33205/262144 : ℝ)) ∧ (radius 8 (33205/262144 : ℝ)) ≤ (984291311139/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33205/262144 : ℝ)) (492145655569/500000000000 : ℝ) (984291311139/1000000000000 : ℝ) (17655201731/100000000000 : ℝ) (44138004329/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33205/262144 : ℝ)) (492145655569/500000000000 : ℝ) (984291311139/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33205/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492145655569/500000000000 : ℝ) (984291311139/1000000000000 : ℝ) (992145655569/1000000000000 : ℝ) (99214565557/100000000000 : ℝ) (99211456553/100000000000 : ℝ) (248028641383/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33205/262144 : ℝ)) 1 (992145655569/1000000000000 : ℝ) (99214565557/100000000000 : ℝ) (99211456553/100000000000 : ℝ) (248028641383/250000000000 : ℝ) (992130110549/1000000000000 : ℝ) (992130110551/1000000000000 : ℝ) (992130110427/1000000000000 : ℝ) (99213011043/100000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33205/262144 : ℝ)) 2 (992130110549/1000000000000 : ℝ) (992130110551/1000000000000 : ℝ) (992130110427/1000000000000 : ℝ) (99213011043/100000000000 : ℝ) (124016263811/125000000000 : ℝ) (992130110491/1000000000000 : ℝ) (992130110487/1000000000000 : ℝ) (992130110491/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33205/262144 : ℝ)) 3 (124016263811/125000000000 : ℝ) (992130110491/1000000000000 : ℝ) (992130110487/1000000000000 : ℝ) (992130110491/1000000000000 : ℝ) (992130110487/1000000000000 : ℝ) (992130110491/1000000000000 : ℝ) (992130110487/1000000000000 : ℝ) (992130110491/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33205/262144 : ℝ)) 4 (992130110487/1000000000000 : ℝ) (992130110491/1000000000000 : ℝ) (992130110487/1000000000000 : ℝ) (992130110491/1000000000000 : ℝ) (992130110487/1000000000000 : ℝ) (992130110491/1000000000000 : ℝ) (992130110487/1000000000000 : ℝ) (992130110491/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33205/262144 : ℝ)) 5 (992130110487/1000000000000 : ℝ) (992130110491/1000000000000 : ℝ) (992130110487/1000000000000 : ℝ) (992130110491/1000000000000 : ℝ) (992130110487/1000000000000 : ℝ) (992130110491/1000000000000 : ℝ) (992130110487/1000000000000 : ℝ) (992130110491/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33205/262144 : ℝ)) 6 (992130110487/1000000000000 : ℝ) (992130110491/1000000000000 : ℝ) (992130110487/1000000000000 : ℝ) (992130110491/1000000000000 : ℝ) (992130110487/1000000000000 : ℝ) (992130110491/1000000000000 : ℝ) (992130110487/1000000000000 : ℝ) (992130110491/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33205/262144 : ℝ)) 7 (992130110487/1000000000000 : ℝ) (992130110491/1000000000000 : ℝ) (992130110487/1000000000000 : ℝ) (992130110491/1000000000000 : ℝ) (992130110487/1000000000000 : ℝ) (992130110491/1000000000000 : ℝ) (992130110487/1000000000000 : ℝ) (992130110491/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33205/262144 : ℝ))) (17655201731/100000000000 : ℝ) (44138004329/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33205/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (17655201731/100000000000 : ℝ) (44138004329/250000000000 : ℝ) (117655201731/200000000000 : ℝ) (294138004329/500000000000 : ℝ) (84036186803/200000000000 : ℝ) (420180934023/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33205/262144 : ℝ))) 1 (117655201731/200000000000 : ℝ) (294138004329/500000000000 : ℝ) (84036186803/200000000000 : ℝ) (420180934023/1000000000000 : ℝ) (100845694267/200000000000 : ℝ) (504228471341/1000000000000 : ℝ) (497174378639/1000000000000 : ℝ) (248587189323/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33205/262144 : ℝ))) 2 (100845694267/200000000000 : ℝ) (504228471341/1000000000000 : ℝ) (497174378639/1000000000000 : ℝ) (248587189323/500000000000 : ℝ) (500701424987/1000000000000 : ℝ) (250350712497/500000000000 : ℝ) (125172250551/250000000000 : ℝ) (500689002211/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33205/262144 : ℝ))) 3 (500701424987/1000000000000 : ℝ) (250350712497/500000000000 : ℝ) (125172250551/250000000000 : ℝ) (500689002211/1000000000000 : ℝ) (100139042719/200000000000 : ℝ) (500695213603/1000000000000 : ℝ) (125173803389/250000000000 : ℝ) (125173803391/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33205/262144 : ℝ))) 4 (100139042719/200000000000 : ℝ) (500695213603/1000000000000 : ℝ) (125173803389/250000000000 : ℝ) (125173803391/250000000000 : ℝ) (20027808543/40000000000 : ℝ) (31293450849/62500000000 : ℝ) (20027808543/40000000000 : ℝ) (31293450849/62500000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33205/262144 : ℝ))) 5 (20027808543/40000000000 : ℝ) (31293450849/62500000000 : ℝ) (20027808543/40000000000 : ℝ) (31293450849/62500000000 : ℝ) (20027808543/40000000000 : ℝ) (31293450849/62500000000 : ℝ) (20027808543/40000000000 : ℝ) (31293450849/62500000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33205/262144 : ℝ))) 6 (20027808543/40000000000 : ℝ) (31293450849/62500000000 : ℝ) (20027808543/40000000000 : ℝ) (31293450849/62500000000 : ℝ) (20027808543/40000000000 : ℝ) (31293450849/62500000000 : ℝ) (20027808543/40000000000 : ℝ) (31293450849/62500000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33205/262144 : ℝ))) 7 (20027808543/40000000000 : ℝ) (31293450849/62500000000 : ℝ) (20027808543/40000000000 : ℝ) (31293450849/62500000000 : ℝ) (20027808543/40000000000 : ℝ) (31293450849/62500000000 : ℝ) (20027808543/40000000000 : ℝ) (31293450849/62500000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33205/262144 : ℝ)) hmem 8 (992130110487/1000000000000 : ℝ) (992130110491/1000000000000 : ℝ) (992130110487/1000000000000 : ℝ) (992130110491/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33205/262144 : ℝ))) hcmem 8 (20027808543/40000000000 : ℝ) (31293450849/62500000000 : ℝ) (20027808543/40000000000 : ℝ) (31293450849/62500000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33205/262144 : ℝ)) (992130110487/1000000000000 : ℝ) (992130110491/1000000000000 : ℝ) (20027808543/40000000000 : ℝ) (31293450849/62500000000 : ℝ) (792728891111/1000000000000 : ℝ) (792728891129/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0424_exp_lower
  have heNumeric : (2054903068039/1000000000000 : ℝ)/4 ≤ Real.exp (-10657050929939/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054903068039/1000000000000 : ℝ)/4 ≤ Real.exp ((8301/65536 : ℝ)-(792728891129/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8301/65536 : ℝ) (33205/262144 : ℝ) (792728891129/1000000000000 : ℝ) (2054903068039/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_leaf0400_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0400_certificate
#check SmaleRate.Proofs.cover8_leaf0401_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0401_certificate
#check SmaleRate.Proofs.cover8_leaf0402_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0402_certificate
#check SmaleRate.Proofs.cover8_leaf0403_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0403_certificate
#check SmaleRate.Proofs.cover8_leaf0404_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0404_certificate
#check SmaleRate.Proofs.cover8_leaf0405_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0405_certificate
#check SmaleRate.Proofs.cover8_leaf0406_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0406_certificate
#check SmaleRate.Proofs.cover8_leaf0407_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0407_certificate
#check SmaleRate.Proofs.cover8_leaf0408_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0408_certificate
#check SmaleRate.Proofs.cover8_leaf0409_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0409_certificate
#check SmaleRate.Proofs.cover8_leaf0410_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0410_certificate
#check SmaleRate.Proofs.cover8_leaf0411_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0411_certificate
#check SmaleRate.Proofs.cover8_leaf0412_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0412_certificate
#check SmaleRate.Proofs.cover8_leaf0413_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0413_certificate
#check SmaleRate.Proofs.cover8_leaf0414_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0414_certificate
#check SmaleRate.Proofs.cover8_leaf0415_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0415_certificate
#check SmaleRate.Proofs.cover8_leaf0416_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0416_certificate
#check SmaleRate.Proofs.cover8_leaf0417_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0417_certificate
#check SmaleRate.Proofs.cover8_leaf0418_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0418_certificate
#check SmaleRate.Proofs.cover8_leaf0419_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0419_certificate
#check SmaleRate.Proofs.cover8_leaf0420_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0420_certificate
#check SmaleRate.Proofs.cover8_leaf0421_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0421_certificate
#check SmaleRate.Proofs.cover8_leaf0422_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0422_certificate
#check SmaleRate.Proofs.cover8_leaf0423_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0423_certificate
#check SmaleRate.Proofs.cover8_leaf0424_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0424_certificate
