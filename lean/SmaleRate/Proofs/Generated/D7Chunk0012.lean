/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.AGMCertificates

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

-- Proposed record cover7_leaf0300; no trusted numerical premise.
theorem cover7_leaf0300_exp_radius : (199514978106242057/200000000000000000 : ℝ) ≤ Real.exp ((-1273/65536 : ℝ)/8) ∧ Real.exp ((-1273/65536 : ℝ)/8) ≤ (498787445265605143/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1273/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0300_exp_lower : (183617808272399877/200000000000000000 : ℝ) ≤ Real.exp ((-5469497479529/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469497479529/8000000000000 : ℝ)/8) ≤ (459044520680999693/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469497479529/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0300_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019009765619/1000000000000 : ℝ) ≤ 4*Real.exp (4455/32768 : ℝ)*Real.exp (-mu (radius 7 (8911/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (2019009765619/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8911/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0300_exp_radius
  have hrNumeric : (196152600067/200000000000 : ℝ) ≤ Real.exp (-1273/65536 : ℝ) ∧ Real.exp (-1273/65536 : ℝ) ≤ (61297687521/62500000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196152600067/200000000000 : ℝ) ≤ (radius 7 (8911/65536 : ℝ)) ∧ (radius 7 (8911/65536 : ℝ)) ≤ (61297687521/62500000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8911/65536 : ℝ)) (196152600067/200000000000 : ℝ) (61297687521/62500000000 : ℝ) (19520229807/100000000000 : ℝ) (48800574519/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8911/65536 : ℝ)) (196152600067/200000000000 : ℝ) (61297687521/62500000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8911/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196152600067/200000000000 : ℝ) (61297687521/62500000000 : ℝ) (990381500167/1000000000000 : ℝ) (123797687521/125000000000 : ℝ) (198066958409/200000000000 : ℝ) (495167396023/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8911/65536 : ℝ)) 1 (990381500167/1000000000000 : ℝ) (123797687521/125000000000 : ℝ) (198066958409/200000000000 : ℝ) (495167396023/500000000000 : ℝ) (495179073053/500000000000 : ℝ) (990358146107/1000000000000 : ℝ) (99035814583/100000000000 : ℝ) (123794768229/125000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8911/65536 : ℝ)) 2 (495179073053/500000000000 : ℝ) (990358146107/1000000000000 : ℝ) (99035814583/100000000000 : ℝ) (123794768229/125000000000 : ℝ) (61897384123/62500000000 : ℝ) (99035814597/100000000000 : ℝ) (990358145967/1000000000000 : ℝ) (99035814597/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8911/65536 : ℝ)) 3 (61897384123/62500000000 : ℝ) (99035814597/100000000000 : ℝ) (990358145967/1000000000000 : ℝ) (99035814597/100000000000 : ℝ) (990358145967/1000000000000 : ℝ) (99035814597/100000000000 : ℝ) (990358145967/1000000000000 : ℝ) (99035814597/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8911/65536 : ℝ)) 4 (990358145967/1000000000000 : ℝ) (99035814597/100000000000 : ℝ) (990358145967/1000000000000 : ℝ) (99035814597/100000000000 : ℝ) (990358145967/1000000000000 : ℝ) (99035814597/100000000000 : ℝ) (990358145967/1000000000000 : ℝ) (99035814597/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8911/65536 : ℝ)) 5 (990358145967/1000000000000 : ℝ) (99035814597/100000000000 : ℝ) (990358145967/1000000000000 : ℝ) (99035814597/100000000000 : ℝ) (990358145967/1000000000000 : ℝ) (99035814597/100000000000 : ℝ) (990358145967/1000000000000 : ℝ) (99035814597/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8911/65536 : ℝ)) 6 (990358145967/1000000000000 : ℝ) (99035814597/100000000000 : ℝ) (990358145967/1000000000000 : ℝ) (99035814597/100000000000 : ℝ) (990358145967/1000000000000 : ℝ) (99035814597/100000000000 : ℝ) (990358145967/1000000000000 : ℝ) (99035814597/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8911/65536 : ℝ)) 7 (990358145967/1000000000000 : ℝ) (99035814597/100000000000 : ℝ) (990358145967/1000000000000 : ℝ) (99035814597/100000000000 : ℝ) (990358145967/1000000000000 : ℝ) (99035814597/100000000000 : ℝ) (990358145967/1000000000000 : ℝ) (99035814597/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8911/65536 : ℝ))) (19520229807/100000000000 : ℝ) (48800574519/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8911/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (19520229807/100000000000 : ℝ) (48800574519/250000000000 : ℝ) (119520229807/200000000000 : ℝ) (298800574519/500000000000 : ℝ) (220908520699/500000000000 : ℝ) (220908520703/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8911/65536 : ℝ))) 1 (119520229807/200000000000 : ℝ) (298800574519/500000000000 : ℝ) (220908520699/500000000000 : ℝ) (220908520703/500000000000 : ℝ) (32481818451/62500000000 : ℝ) (259854547611/500000000000 : ℝ) (256919428811/500000000000 : ℝ) (513838857629/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8911/65536 : ℝ))) 2 (32481818451/62500000000 : ℝ) (259854547611/500000000000 : ℝ) (256919428811/500000000000 : ℝ) (513838857629/1000000000000 : ℝ) (516773976419/1000000000000 : ℝ) (258386988213/500000000000 : ℝ) (516765641061/1000000000000 : ℝ) (129191410267/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8911/65536 : ℝ))) 3 (516773976419/1000000000000 : ℝ) (258386988213/500000000000 : ℝ) (516765641061/1000000000000 : ℝ) (129191410267/250000000000 : ℝ) (25838490437/50000000000 : ℝ) (516769808747/1000000000000 : ℝ) (516769808723/1000000000000 : ℝ) (516769808731/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8911/65536 : ℝ))) 4 (25838490437/50000000000 : ℝ) (516769808747/1000000000000 : ℝ) (516769808723/1000000000000 : ℝ) (516769808731/1000000000000 : ℝ) (516769808731/1000000000000 : ℝ) (516769808739/1000000000000 : ℝ) (516769808731/1000000000000 : ℝ) (516769808739/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8911/65536 : ℝ))) 5 (516769808731/1000000000000 : ℝ) (516769808739/1000000000000 : ℝ) (516769808731/1000000000000 : ℝ) (516769808739/1000000000000 : ℝ) (516769808731/1000000000000 : ℝ) (516769808739/1000000000000 : ℝ) (516769808731/1000000000000 : ℝ) (516769808739/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8911/65536 : ℝ))) 6 (516769808731/1000000000000 : ℝ) (516769808739/1000000000000 : ℝ) (516769808731/1000000000000 : ℝ) (516769808739/1000000000000 : ℝ) (516769808731/1000000000000 : ℝ) (516769808739/1000000000000 : ℝ) (516769808731/1000000000000 : ℝ) (516769808739/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8911/65536 : ℝ))) 7 (516769808731/1000000000000 : ℝ) (516769808739/1000000000000 : ℝ) (516769808731/1000000000000 : ℝ) (516769808739/1000000000000 : ℝ) (516769808731/1000000000000 : ℝ) (516769808739/1000000000000 : ℝ) (516769808731/1000000000000 : ℝ) (516769808739/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8911/65536 : ℝ)) hmem 8 (990358145967/1000000000000 : ℝ) (99035814597/100000000000 : ℝ) (990358145967/1000000000000 : ℝ) (99035814597/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8911/65536 : ℝ))) hcmem 8 (516769808731/1000000000000 : ℝ) (516769808739/1000000000000 : ℝ) (516769808731/1000000000000 : ℝ) (516769808739/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8911/65536 : ℝ)) (990358145967/1000000000000 : ℝ) (99035814597/100000000000 : ℝ) (516769808731/1000000000000 : ℝ) (516769808739/1000000000000 : ℝ) (51227687217/62500000000 : ℝ) (25613843609/31250000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0300_exp_lower
  have heNumeric : (2019009765619/1000000000000 : ℝ)/4 ≤ Real.exp (-5469497479529/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019009765619/1000000000000 : ℝ)/4 ≤ Real.exp ((4455/32768 : ℝ)-(25613843609/31250000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4455/32768 : ℝ) (8911/65536 : ℝ) (25613843609/31250000000 : ℝ) (2019009765619/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0301; no trusted numerical premise.
theorem cover7_leaf0301_exp_radius : (997574618713661091/1000000000000000000 : ℝ) ≤ Real.exp ((-557/28672 : ℝ)/8) ∧ Real.exp ((-557/28672 : ℝ)/8) ≤ (249393654678415273/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-557/28672 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0301_exp_lower : (114761129912942021/125000000000000000 : ℝ) ≤ Real.exp ((-10938995246049/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938995246049/16000000000000 : ℝ)/8) ≤ (918089039303536169/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938995246049/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0301_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (403801945881/200000000000 : ℝ) ≤ 4*Real.exp (8911/65536 : ℝ)*Real.exp (-mu (radius 7 (557/4096 : ℝ))) ∧ (2019/1000 : ℝ) < (403801945881/200000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (557/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0301_exp_radius
  have hrNumeric : (980760862443/1000000000000 : ℝ) ≤ Real.exp (-557/28672 : ℝ) ∧ Real.exp (-557/28672 : ℝ) ≤ (245190215611/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980760862443/1000000000000 : ℝ) ≤ (radius 7 (557/4096 : ℝ)) ∧ (radius 7 (557/4096 : ℝ)) ≤ (245190215611/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (557/4096 : ℝ)) (980760862443/1000000000000 : ℝ) (245190215611/250000000000 : ℝ) (97606519631/500000000000 : ℝ) (48803259817/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (557/4096 : ℝ)) (980760862443/1000000000000 : ℝ) (245190215611/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (557/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980760862443/1000000000000 : ℝ) (245190215611/250000000000 : ℝ) (990380431221/1000000000000 : ℝ) (495190215611/500000000000 : ℝ) (495166856333/500000000000 : ℝ) (990333712667/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (557/4096 : ℝ)) 1 (990380431221/1000000000000 : ℝ) (495190215611/500000000000 : ℝ) (495166856333/500000000000 : ℝ) (990333712667/1000000000000 : ℝ) (990357071943/1000000000000 : ℝ) (198071414389/200000000000 : ℝ) (247589267917/250000000000 : ℝ) (99035707167/100000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (557/4096 : ℝ)) 2 (990357071943/1000000000000 : ℝ) (198071414389/200000000000 : ℝ) (247589267917/250000000000 : ℝ) (99035707167/100000000000 : ℝ) (198071414361/200000000000 : ℝ) (15474329247/15625000000 : ℝ) (198071414361/200000000000 : ℝ) (15474329247/15625000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (557/4096 : ℝ)) 3 (198071414361/200000000000 : ℝ) (15474329247/15625000000 : ℝ) (198071414361/200000000000 : ℝ) (15474329247/15625000000 : ℝ) (198071414361/200000000000 : ℝ) (15474329247/15625000000 : ℝ) (198071414361/200000000000 : ℝ) (15474329247/15625000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (557/4096 : ℝ)) 4 (198071414361/200000000000 : ℝ) (15474329247/15625000000 : ℝ) (198071414361/200000000000 : ℝ) (15474329247/15625000000 : ℝ) (198071414361/200000000000 : ℝ) (15474329247/15625000000 : ℝ) (198071414361/200000000000 : ℝ) (15474329247/15625000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (557/4096 : ℝ)) 5 (198071414361/200000000000 : ℝ) (15474329247/15625000000 : ℝ) (198071414361/200000000000 : ℝ) (15474329247/15625000000 : ℝ) (198071414361/200000000000 : ℝ) (15474329247/15625000000 : ℝ) (198071414361/200000000000 : ℝ) (15474329247/15625000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (557/4096 : ℝ)) 6 (198071414361/200000000000 : ℝ) (15474329247/15625000000 : ℝ) (198071414361/200000000000 : ℝ) (15474329247/15625000000 : ℝ) (198071414361/200000000000 : ℝ) (15474329247/15625000000 : ℝ) (198071414361/200000000000 : ℝ) (15474329247/15625000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (557/4096 : ℝ)) 7 (198071414361/200000000000 : ℝ) (15474329247/15625000000 : ℝ) (198071414361/200000000000 : ℝ) (15474329247/15625000000 : ℝ) (198071414361/200000000000 : ℝ) (15474329247/15625000000 : ℝ) (198071414361/200000000000 : ℝ) (15474329247/15625000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (557/4096 : ℝ))) (97606519631/500000000000 : ℝ) (48803259817/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (557/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (97606519631/500000000000 : ℝ) (48803259817/250000000000 : ℝ) (597606519631/1000000000000 : ℝ) (298803259817/500000000000 : ℝ) (110457299233/250000000000 : ℝ) (22091459847/50000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (557/4096 : ℝ))) 1 (597606519631/1000000000000 : ℝ) (298803259817/500000000000 : ℝ) (110457299233/250000000000 : ℝ) (22091459847/50000000000 : ℝ) (519717858281/1000000000000 : ℝ) (519717858287/1000000000000 : ℝ) (128462058759/250000000000 : ℝ) (513848235043/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (557/4096 : ℝ))) 2 (519717858281/1000000000000 : ℝ) (519717858287/1000000000000 : ℝ) (128462058759/250000000000 : ℝ) (513848235043/1000000000000 : ℝ) (258391523329/500000000000 : ℝ) (103356609333/200000000000 : ℝ) (516774713191/1000000000000 : ℝ) (516774713199/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (557/4096 : ℝ))) 3 (258391523329/500000000000 : ℝ) (103356609333/200000000000 : ℝ) (516774713191/1000000000000 : ℝ) (516774713199/1000000000000 : ℝ) (129194719981/250000000000 : ℝ) (129194719983/250000000000 : ℝ) (516778879907/1000000000000 : ℝ) (129194719979/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (557/4096 : ℝ))) 4 (129194719981/250000000000 : ℝ) (129194719983/250000000000 : ℝ) (516778879907/1000000000000 : ℝ) (129194719979/250000000000 : ℝ) (103355775983/200000000000 : ℝ) (129194719981/250000000000 : ℝ) (103355775983/200000000000 : ℝ) (129194719981/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (557/4096 : ℝ))) 5 (103355775983/200000000000 : ℝ) (129194719981/250000000000 : ℝ) (103355775983/200000000000 : ℝ) (129194719981/250000000000 : ℝ) (103355775983/200000000000 : ℝ) (129194719981/250000000000 : ℝ) (103355775983/200000000000 : ℝ) (129194719981/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (557/4096 : ℝ))) 6 (103355775983/200000000000 : ℝ) (129194719981/250000000000 : ℝ) (103355775983/200000000000 : ℝ) (129194719981/250000000000 : ℝ) (103355775983/200000000000 : ℝ) (129194719981/250000000000 : ℝ) (103355775983/200000000000 : ℝ) (129194719981/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (557/4096 : ℝ))) 7 (103355775983/200000000000 : ℝ) (129194719981/250000000000 : ℝ) (103355775983/200000000000 : ℝ) (129194719981/250000000000 : ℝ) (103355775983/200000000000 : ℝ) (129194719981/250000000000 : ℝ) (103355775983/200000000000 : ℝ) (129194719981/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (557/4096 : ℝ)) hmem 8 (198071414361/200000000000 : ℝ) (15474329247/15625000000 : ℝ) (198071414361/200000000000 : ℝ) (15474329247/15625000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (557/4096 : ℝ))) hcmem 8 (103355775983/200000000000 : ℝ) (129194719981/250000000000 : ℝ) (103355775983/200000000000 : ℝ) (129194719981/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (557/4096 : ℝ)) (198071414361/200000000000 : ℝ) (15474329247/15625000000 : ℝ) (103355775983/200000000000 : ℝ) (129194719981/250000000000 : ℝ) (204914568049/250000000000 : ℝ) (409829136107/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0301_exp_lower
  have heNumeric : (403801945881/200000000000 : ℝ)/4 ≤ Real.exp (-10938995246049/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (403801945881/200000000000 : ℝ)/4 ≤ Real.exp ((8911/65536 : ℝ)-(409829136107/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8911/65536 : ℝ) (557/4096 : ℝ) (409829136107/500000000000 : ℝ) (403801945881/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0302; no trusted numerical premise.
theorem cover7_leaf0302_exp_radius : (997574346896185961/1000000000000000000 : ℝ) ≤ Real.exp ((-8913/458752 : ℝ)/8) ∧ Real.exp ((-8913/458752 : ℝ)/8) ≤ (498787173448092981/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8913/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0302_exp_lower : (918089037377392539/1000000000000000000 : ℝ) ≤ Real.exp ((-341843609831/500000000000 : ℝ)/8) ∧ Real.exp ((-341843609831/500000000000 : ℝ)/8) ≤ (45904451868869627/50000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-341843609831/500000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0302_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009504847759/500000000000 : ℝ) ≤ 4*Real.exp (557/4096 : ℝ)*Real.exp (-mu (radius 7 (8913/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (1009504847759/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8913/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0302_exp_radius
  have hrNumeric : (980758724557/1000000000000 : ℝ) ≤ Real.exp (-8913/458752 : ℝ) ∧ Real.exp (-8913/458752 : ℝ) ≤ (490379362279/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980758724557/1000000000000 : ℝ) ≤ (radius 7 (8913/65536 : ℝ)) ∧ (radius 7 (8913/65536 : ℝ)) ≤ (490379362279/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8913/65536 : ℝ)) (980758724557/1000000000000 : ℝ) (490379362279/500000000000 : ℝ) (19522377981/100000000000 : ℝ) (24402972477/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8913/65536 : ℝ)) (980758724557/1000000000000 : ℝ) (490379362279/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8913/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980758724557/1000000000000 : ℝ) (490379362279/500000000000 : ℝ) (495189681139/500000000000 : ℝ) (990379362279/1000000000000 : ℝ) (123791579161/125000000000 : ℝ) (99033263329/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8913/65536 : ℝ)) 1 (495189681139/500000000000 : ℝ) (990379362279/1000000000000 : ℝ) (123791579161/125000000000 : ℝ) (99033263329/100000000000 : ℝ) (990355997783/1000000000000 : ℝ) (198071199557/200000000000 : ℝ) (990355997507/1000000000000 : ℝ) (990355997509/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8913/65536 : ℝ)) 2 (990355997783/1000000000000 : ℝ) (198071199557/200000000000 : ℝ) (990355997507/1000000000000 : ℝ) (990355997509/1000000000000 : ℝ) (198071199529/200000000000 : ℝ) (990355997647/1000000000000 : ℝ) (247588999411/250000000000 : ℝ) (990355997647/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8913/65536 : ℝ)) 3 (198071199529/200000000000 : ℝ) (990355997647/1000000000000 : ℝ) (247588999411/250000000000 : ℝ) (990355997647/1000000000000 : ℝ) (247588999411/250000000000 : ℝ) (990355997647/1000000000000 : ℝ) (247588999411/250000000000 : ℝ) (990355997647/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8913/65536 : ℝ)) 4 (247588999411/250000000000 : ℝ) (990355997647/1000000000000 : ℝ) (247588999411/250000000000 : ℝ) (990355997647/1000000000000 : ℝ) (247588999411/250000000000 : ℝ) (990355997647/1000000000000 : ℝ) (247588999411/250000000000 : ℝ) (990355997647/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8913/65536 : ℝ)) 5 (247588999411/250000000000 : ℝ) (990355997647/1000000000000 : ℝ) (247588999411/250000000000 : ℝ) (990355997647/1000000000000 : ℝ) (247588999411/250000000000 : ℝ) (990355997647/1000000000000 : ℝ) (247588999411/250000000000 : ℝ) (990355997647/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8913/65536 : ℝ)) 6 (247588999411/250000000000 : ℝ) (990355997647/1000000000000 : ℝ) (247588999411/250000000000 : ℝ) (990355997647/1000000000000 : ℝ) (247588999411/250000000000 : ℝ) (990355997647/1000000000000 : ℝ) (247588999411/250000000000 : ℝ) (990355997647/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8913/65536 : ℝ)) 7 (247588999411/250000000000 : ℝ) (990355997647/1000000000000 : ℝ) (247588999411/250000000000 : ℝ) (990355997647/1000000000000 : ℝ) (247588999411/250000000000 : ℝ) (990355997647/1000000000000 : ℝ) (247588999411/250000000000 : ℝ) (990355997647/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8913/65536 : ℝ))) (19522377981/100000000000 : ℝ) (24402972477/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8913/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (19522377981/100000000000 : ℝ) (24402972477/125000000000 : ℝ) (119522377981/200000000000 : ℝ) (149402972477/250000000000 : ℝ) (441841351403/1000000000000 : ℝ) (441841351411/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8913/65536 : ℝ))) 1 (119522377981/200000000000 : ℝ) (149402972477/250000000000 : ℝ) (441841351403/1000000000000 : ℝ) (441841351411/1000000000000 : ℝ) (259863310327/500000000000 : ℝ) (25986331033/50000000000 : ℝ) (513857611649/1000000000000 : ℝ) (64232201457/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8913/65536 : ℝ))) 2 (259863310327/500000000000 : ℝ) (25986331033/50000000000 : ℝ) (513857611649/1000000000000 : ℝ) (64232201457/125000000000 : ℝ) (516792116151/1000000000000 : ℝ) (258396058079/500000000000 : ℝ) (20671351383/40000000000 : ℝ) (258391892291/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8913/65536 : ℝ))) 3 (516792116151/1000000000000 : ℝ) (258396058079/500000000000 : ℝ) (20671351383/40000000000 : ℝ) (258391892291/500000000000 : ℝ) (516787950363/1000000000000 : ℝ) (51678795037/100000000000 : ℝ) (258393975173/500000000000 : ℝ) (258393975177/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8913/65536 : ℝ))) 4 (516787950363/1000000000000 : ℝ) (51678795037/100000000000 : ℝ) (258393975173/500000000000 : ℝ) (258393975177/500000000000 : ℝ) (258393975177/500000000000 : ℝ) (258393975181/500000000000 : ℝ) (258393975177/500000000000 : ℝ) (258393975181/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8913/65536 : ℝ))) 5 (258393975177/500000000000 : ℝ) (258393975181/500000000000 : ℝ) (258393975177/500000000000 : ℝ) (258393975181/500000000000 : ℝ) (258393975177/500000000000 : ℝ) (258393975181/500000000000 : ℝ) (258393975177/500000000000 : ℝ) (258393975181/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8913/65536 : ℝ))) 6 (258393975177/500000000000 : ℝ) (258393975181/500000000000 : ℝ) (258393975177/500000000000 : ℝ) (258393975181/500000000000 : ℝ) (258393975177/500000000000 : ℝ) (258393975181/500000000000 : ℝ) (258393975177/500000000000 : ℝ) (258393975181/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8913/65536 : ℝ))) 7 (258393975177/500000000000 : ℝ) (258393975181/500000000000 : ℝ) (258393975177/500000000000 : ℝ) (258393975181/500000000000 : ℝ) (258393975177/500000000000 : ℝ) (258393975181/500000000000 : ℝ) (258393975177/500000000000 : ℝ) (258393975181/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8913/65536 : ℝ)) hmem 8 (247588999411/250000000000 : ℝ) (990355997647/1000000000000 : ℝ) (247588999411/250000000000 : ℝ) (990355997647/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8913/65536 : ℝ))) hcmem 8 (258393975177/500000000000 : ℝ) (258393975181/500000000000 : ℝ) (258393975177/500000000000 : ℝ) (258393975181/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8913/65536 : ℝ)) (247588999411/250000000000 : ℝ) (990355997647/1000000000000 : ℝ) (258393975177/500000000000 : ℝ) (258393975181/500000000000 : ℝ) (819673547771/1000000000000 : ℝ) (819673547787/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0302_exp_lower
  have heNumeric : (1009504847759/500000000000 : ℝ)/4 ≤ Real.exp (-341843609831/500000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009504847759/500000000000 : ℝ)/4 ≤ Real.exp ((557/4096 : ℝ)-(819673547787/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (557/4096 : ℝ) (8913/65536 : ℝ) (819673547787/1000000000000 : ℝ) (1009504847759/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0303; no trusted numerical premise.
theorem cover7_leaf0303_exp_radius : (7793547461553007/7812500000000000 : ℝ) ≤ Real.exp ((-4457/229376 : ℝ)/8) ∧ Real.exp ((-4457/229376 : ℝ)/8) ≤ (997574075078784897/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4457/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0303_exp_lower : (4590445177910383/5000000000000000 : ℝ) ≤ Real.exp ((-2187799152979/3200000000000 : ℝ)/8) ∧ Real.exp ((-2187799152979/3200000000000 : ℝ)/8) ≤ (918089035582076601/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2187799152979/3200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0303_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (504752415983/250000000000 : ℝ) ≤ 4*Real.exp (8913/65536 : ℝ)*Real.exp (-mu (radius 7 (4457/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (504752415983/250000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4457/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0303_exp_radius
  have hrNumeric : (39230263467/40000000000 : ℝ) ≤ Real.exp (-4457/229376 : ℝ) ∧ Real.exp (-4457/229376 : ℝ) ≤ (245189146669/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (39230263467/40000000000 : ℝ) ≤ (radius 7 (4457/32768 : ℝ)) ∧ (radius 7 (4457/32768 : ℝ)) ≤ (245189146669/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4457/32768 : ℝ)) (39230263467/40000000000 : ℝ) (245189146669/250000000000 : ℝ) (195234519723/1000000000000 : ℝ) (195234519729/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4457/32768 : ℝ)) (39230263467/40000000000 : ℝ) (245189146669/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4457/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (39230263467/40000000000 : ℝ) (245189146669/250000000000 : ℝ) (990378293337/1000000000000 : ℝ) (495189146669/500000000000 : ℝ) (123791444239/125000000000 : ℝ) (495165776957/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4457/32768 : ℝ)) 1 (990378293337/1000000000000 : ℝ) (495189146669/500000000000 : ℝ) (123791444239/125000000000 : ℝ) (495165776957/500000000000 : ℝ) (123794365453/125000000000 : ℝ) (495177461813/500000000000 : ℝ) (247588730837/250000000000 : ℝ) (990354923351/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4457/32768 : ℝ)) 2 (123794365453/125000000000 : ℝ) (495177461813/500000000000 : ℝ) (247588730837/250000000000 : ℝ) (990354923351/1000000000000 : ℝ) (495177461743/500000000000 : ℝ) (990354923489/1000000000000 : ℝ) (198070984697/200000000000 : ℝ) (990354923489/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4457/32768 : ℝ)) 3 (495177461743/500000000000 : ℝ) (990354923489/1000000000000 : ℝ) (198070984697/200000000000 : ℝ) (990354923489/1000000000000 : ℝ) (198070984697/200000000000 : ℝ) (990354923489/1000000000000 : ℝ) (198070984697/200000000000 : ℝ) (990354923489/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4457/32768 : ℝ)) 4 (198070984697/200000000000 : ℝ) (990354923489/1000000000000 : ℝ) (198070984697/200000000000 : ℝ) (990354923489/1000000000000 : ℝ) (198070984697/200000000000 : ℝ) (990354923489/1000000000000 : ℝ) (198070984697/200000000000 : ℝ) (990354923489/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4457/32768 : ℝ)) 5 (198070984697/200000000000 : ℝ) (990354923489/1000000000000 : ℝ) (198070984697/200000000000 : ℝ) (990354923489/1000000000000 : ℝ) (198070984697/200000000000 : ℝ) (990354923489/1000000000000 : ℝ) (198070984697/200000000000 : ℝ) (990354923489/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4457/32768 : ℝ)) 6 (198070984697/200000000000 : ℝ) (990354923489/1000000000000 : ℝ) (198070984697/200000000000 : ℝ) (990354923489/1000000000000 : ℝ) (198070984697/200000000000 : ℝ) (990354923489/1000000000000 : ℝ) (198070984697/200000000000 : ℝ) (990354923489/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4457/32768 : ℝ)) 7 (198070984697/200000000000 : ℝ) (990354923489/1000000000000 : ℝ) (198070984697/200000000000 : ℝ) (990354923489/1000000000000 : ℝ) (198070984697/200000000000 : ℝ) (990354923489/1000000000000 : ℝ) (198070984697/200000000000 : ℝ) (990354923489/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4457/32768 : ℝ))) (195234519723/1000000000000 : ℝ) (195234519729/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4457/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (195234519723/1000000000000 : ℝ) (195234519729/1000000000000 : ℝ) (597617259861/1000000000000 : ℝ) (119523451973/200000000000 : ℝ) (441853504821/1000000000000 : ℝ) (441853504829/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4457/32768 : ℝ))) 1 (597617259861/1000000000000 : ℝ) (119523451973/200000000000 : ℝ) (441853504821/1000000000000 : ℝ) (441853504829/1000000000000 : ℝ) (519735382341/1000000000000 : ℝ) (519735382347/1000000000000 : ℝ) (513866987469/1000000000000 : ℝ) (128466746869/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4457/32768 : ℝ))) 2 (519735382341/1000000000000 : ℝ) (519735382347/1000000000000 : ℝ) (513866987469/1000000000000 : ℝ) (128466746869/250000000000 : ℝ) (103360236981/200000000000 : ℝ) (32300074057/62500000000 : ℝ) (258396427609/500000000000 : ℝ) (20671714209/40000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4457/32768 : ℝ))) 3 (103360236981/200000000000 : ℝ) (32300074057/62500000000 : ℝ) (258396427609/500000000000 : ℝ) (20671714209/40000000000 : ℝ) (516797020061/1000000000000 : ℝ) (516797020069/1000000000000 : ℝ) (129199255011/250000000000 : ℝ) (129199255013/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4457/32768 : ℝ))) 4 (516797020061/1000000000000 : ℝ) (516797020069/1000000000000 : ℝ) (129199255011/250000000000 : ℝ) (129199255013/250000000000 : ℝ) (129199255013/250000000000 : ℝ) (516797020061/1000000000000 : ℝ) (129199255013/250000000000 : ℝ) (516797020061/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4457/32768 : ℝ))) 5 (129199255013/250000000000 : ℝ) (516797020061/1000000000000 : ℝ) (129199255013/250000000000 : ℝ) (516797020061/1000000000000 : ℝ) (129199255013/250000000000 : ℝ) (516797020061/1000000000000 : ℝ) (129199255013/250000000000 : ℝ) (516797020061/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4457/32768 : ℝ))) 6 (129199255013/250000000000 : ℝ) (516797020061/1000000000000 : ℝ) (129199255013/250000000000 : ℝ) (516797020061/1000000000000 : ℝ) (129199255013/250000000000 : ℝ) (516797020061/1000000000000 : ℝ) (129199255013/250000000000 : ℝ) (516797020061/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4457/32768 : ℝ))) 7 (129199255013/250000000000 : ℝ) (516797020061/1000000000000 : ℝ) (129199255013/250000000000 : ℝ) (516797020061/1000000000000 : ℝ) (129199255013/250000000000 : ℝ) (516797020061/1000000000000 : ℝ) (129199255013/250000000000 : ℝ) (516797020061/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4457/32768 : ℝ)) hmem 8 (198070984697/200000000000 : ℝ) (990354923489/1000000000000 : ℝ) (198070984697/200000000000 : ℝ) (990354923489/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4457/32768 : ℝ))) hcmem 8 (129199255013/250000000000 : ℝ) (516797020061/1000000000000 : ℝ) (129199255013/250000000000 : ℝ) (516797020061/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4457/32768 : ℝ)) (198070984697/200000000000 : ℝ) (990354923489/1000000000000 : ℝ) (129199255013/250000000000 : ℝ) (516797020061/1000000000000 : ℝ) (819688822201/1000000000000 : ℝ) (40984441111/50000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0303_exp_lower
  have heNumeric : (504752415983/250000000000 : ℝ)/4 ≤ Real.exp (-2187799152979/3200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (504752415983/250000000000 : ℝ)/4 ≤ Real.exp ((8913/65536 : ℝ)-(40984441111/50000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8913/65536 : ℝ) (4457/32768 : ℝ) (40984441111/50000000000 : ℝ) (504752415983/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0304; no trusted numerical premise.
theorem cover7_leaf0304_exp_radius : (199514760652291579/200000000000000000 : ℝ) ≤ Real.exp ((-8915/458752 : ℝ)/8) ∧ Real.exp ((-8915/458752 : ℝ)/8) ≤ (124696725407682237/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8915/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0304_exp_lower : (459044516958851557/500000000000000000 : ℝ) ≤ Real.exp ((-5469497998471/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469497998471/8000000000000 : ℝ)/8) ≤ (183617806783540623/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469497998471/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0304_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019009634651/1000000000000 : ℝ) ≤ 4*Real.exp (4457/32768 : ℝ)*Real.exp (-mu (radius 7 (8915/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (2019009634651/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8915/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0304_exp_radius
  have hrNumeric : (980754448797/1000000000000 : ℝ) ≤ Real.exp (-8915/458752 : ℝ) ∧ Real.exp (-8915/458752 : ℝ) ≤ (490377224399/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980754448797/1000000000000 : ℝ) ≤ (radius 7 (8915/65536 : ℝ)) ∧ (radius 7 (8915/65536 : ℝ)) ≤ (490377224399/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8915/65536 : ℝ)) (980754448797/1000000000000 : ℝ) (490377224399/500000000000 : ℝ) (97622629501/500000000000 : ℝ) (762676793/3906250000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8915/65536 : ℝ)) (980754448797/1000000000000 : ℝ) (490377224399/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8915/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980754448797/1000000000000 : ℝ) (490377224399/500000000000 : ℝ) (495188612199/500000000000 : ℝ) (990377224399/1000000000000 : ℝ) (990330474537/1000000000000 : ℝ) (495165237269/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8915/65536 : ℝ)) 1 (495188612199/500000000000 : ℝ) (990377224399/1000000000000 : ℝ) (990330474537/1000000000000 : ℝ) (495165237269/500000000000 : ℝ) (990353849467/1000000000000 : ℝ) (990353849469/1000000000000 : ℝ) (990353849191/1000000000000 : ℝ) (990353849193/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8915/65536 : ℝ)) 2 (990353849467/1000000000000 : ℝ) (990353849469/1000000000000 : ℝ) (990353849191/1000000000000 : ℝ) (990353849193/1000000000000 : ℝ) (990353849329/1000000000000 : ℝ) (990353849331/1000000000000 : ℝ) (61897115583/62500000000 : ℝ) (990353849331/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8915/65536 : ℝ)) 3 (990353849329/1000000000000 : ℝ) (990353849331/1000000000000 : ℝ) (61897115583/62500000000 : ℝ) (990353849331/1000000000000 : ℝ) (61897115583/62500000000 : ℝ) (990353849331/1000000000000 : ℝ) (61897115583/62500000000 : ℝ) (990353849331/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8915/65536 : ℝ)) 4 (61897115583/62500000000 : ℝ) (990353849331/1000000000000 : ℝ) (61897115583/62500000000 : ℝ) (990353849331/1000000000000 : ℝ) (61897115583/62500000000 : ℝ) (990353849331/1000000000000 : ℝ) (61897115583/62500000000 : ℝ) (990353849331/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8915/65536 : ℝ)) 5 (61897115583/62500000000 : ℝ) (990353849331/1000000000000 : ℝ) (61897115583/62500000000 : ℝ) (990353849331/1000000000000 : ℝ) (61897115583/62500000000 : ℝ) (990353849331/1000000000000 : ℝ) (61897115583/62500000000 : ℝ) (990353849331/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8915/65536 : ℝ)) 6 (61897115583/62500000000 : ℝ) (990353849331/1000000000000 : ℝ) (61897115583/62500000000 : ℝ) (990353849331/1000000000000 : ℝ) (61897115583/62500000000 : ℝ) (990353849331/1000000000000 : ℝ) (61897115583/62500000000 : ℝ) (990353849331/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8915/65536 : ℝ)) 7 (61897115583/62500000000 : ℝ) (990353849331/1000000000000 : ℝ) (61897115583/62500000000 : ℝ) (990353849331/1000000000000 : ℝ) (61897115583/62500000000 : ℝ) (990353849331/1000000000000 : ℝ) (61897115583/62500000000 : ℝ) (990353849331/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8915/65536 : ℝ))) (97622629501/500000000000 : ℝ) (762676793/3906250000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8915/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (97622629501/500000000000 : ℝ) (762676793/3906250000 : ℝ) (597622629501/1000000000000 : ℝ) (4668926793/7812500000 : ℝ) (441865657187/1000000000000 : ℝ) (88373131439/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8915/65536 : ℝ))) 1 (597622629501/1000000000000 : ℝ) (4668926793/7812500000 : ℝ) (441865657187/1000000000000 : ℝ) (88373131439/200000000000 : ℝ) (32484008959/62500000000 : ℝ) (10394882867/20000000000 : ℝ) (256938181249/500000000000 : ℝ) (102775272501/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8915/65536 : ℝ))) 2 (32484008959/62500000000 : ℝ) (10394882867/20000000000 : ℝ) (256938181249/500000000000 : ℝ) (102775272501/200000000000 : ℝ) (516810252921/1000000000000 : ℝ) (4037580101/7812500000 : ℝ) (516801925123/1000000000000 : ℝ) (51680192513/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8915/65536 : ℝ))) 3 (516810252921/1000000000000 : ℝ) (4037580101/7812500000 : ℝ) (516801925123/1000000000000 : ℝ) (51680192513/100000000000 : ℝ) (258403044511/500000000000 : ℝ) (516806089029/1000000000000 : ℝ) (103361217801/200000000000 : ℝ) (516806089013/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8915/65536 : ℝ))) 4 (258403044511/500000000000 : ℝ) (516806089029/1000000000000 : ℝ) (103361217801/200000000000 : ℝ) (516806089013/1000000000000 : ℝ) (516806089013/1000000000000 : ℝ) (516806089021/1000000000000 : ℝ) (516806089013/1000000000000 : ℝ) (516806089021/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8915/65536 : ℝ))) 5 (516806089013/1000000000000 : ℝ) (516806089021/1000000000000 : ℝ) (516806089013/1000000000000 : ℝ) (516806089021/1000000000000 : ℝ) (516806089013/1000000000000 : ℝ) (516806089021/1000000000000 : ℝ) (516806089013/1000000000000 : ℝ) (516806089021/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8915/65536 : ℝ))) 6 (516806089013/1000000000000 : ℝ) (516806089021/1000000000000 : ℝ) (516806089013/1000000000000 : ℝ) (516806089021/1000000000000 : ℝ) (516806089013/1000000000000 : ℝ) (516806089021/1000000000000 : ℝ) (516806089013/1000000000000 : ℝ) (516806089021/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8915/65536 : ℝ))) 7 (516806089013/1000000000000 : ℝ) (516806089021/1000000000000 : ℝ) (516806089013/1000000000000 : ℝ) (516806089021/1000000000000 : ℝ) (516806089013/1000000000000 : ℝ) (516806089021/1000000000000 : ℝ) (516806089013/1000000000000 : ℝ) (516806089021/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8915/65536 : ℝ)) hmem 8 (61897115583/62500000000 : ℝ) (990353849331/1000000000000 : ℝ) (61897115583/62500000000 : ℝ) (990353849331/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8915/65536 : ℝ))) hcmem 8 (516806089013/1000000000000 : ℝ) (516806089021/1000000000000 : ℝ) (516806089013/1000000000000 : ℝ) (516806089021/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8915/65536 : ℝ)) (61897115583/62500000000 : ℝ) (990353849331/1000000000000 : ℝ) (516806089013/1000000000000 : ℝ) (516806089021/1000000000000 : ℝ) (102463011937/125000000000 : ℝ) (102463011939/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0304_exp_lower
  have heNumeric : (2019009634651/1000000000000 : ℝ)/4 ≤ Real.exp (-5469497998471/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019009634651/1000000000000 : ℝ)/4 ≤ Real.exp ((4457/32768 : ℝ)-(102463011939/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4457/32768 : ℝ) (8915/65536 : ℝ) (102463011939/125000000000 : ℝ) (2019009634651/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0305; no trusted numerical premise.
theorem cover7_leaf0305_exp_radius : (997573531444204959/1000000000000000000 : ℝ) ≤ Real.exp ((-2229/114688 : ℝ)/8) ∧ Real.exp ((-2229/114688 : ℝ)/8) ≤ (6234834571526281/6250000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2229/114688 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0305_exp_lower : (918089032385534451/1000000000000000000 : ℝ) ≤ Real.exp ((-10938996210557/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938996210557/16000000000000 : ℝ)/8) ≤ (229522258096383613/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938996210557/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0305_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (403801921539/200000000000 : ℝ) ≤ 4*Real.exp (8915/65536 : ℝ)*Real.exp (-mu (radius 7 (2229/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (403801921539/200000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2229/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0305_exp_radius
  have hrNumeric : (39230092437/40000000000 : ℝ) ≤ Real.exp (-2229/114688 : ℝ) ∧ Real.exp (-2229/114688 : ℝ) ≤ (490376155463/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (39230092437/40000000000 : ℝ) ≤ (radius 7 (2229/16384 : ℝ)) ∧ (radius 7 (2229/16384 : ℝ)) ≤ (490376155463/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2229/16384 : ℝ)) (39230092437/40000000000 : ℝ) (490376155463/500000000000 : ℝ) (195255997637/1000000000000 : ℝ) (195255997643/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2229/16384 : ℝ)) (39230092437/40000000000 : ℝ) (490376155463/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2229/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (39230092437/40000000000 : ℝ) (490376155463/500000000000 : ℝ) (495188077731/500000000000 : ℝ) (990376155463/1000000000000 : ℝ) (990329395163/1000000000000 : ℝ) (198065879033/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2229/16384 : ℝ)) 1 (495188077731/500000000000 : ℝ) (990376155463/1000000000000 : ℝ) (990329395163/1000000000000 : ℝ) (198065879033/200000000000 : ℝ) (61897048457/62500000000 : ℝ) (495176387657/500000000000 : ℝ) (247588193759/250000000000 : ℝ) (990352775039/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2229/16384 : ℝ)) 2 (61897048457/62500000000 : ℝ) (495176387657/500000000000 : ℝ) (247588193759/250000000000 : ℝ) (990352775039/1000000000000 : ℝ) (495176387587/500000000000 : ℝ) (990352775177/1000000000000 : ℝ) (990352775173/1000000000000 : ℝ) (990352775177/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2229/16384 : ℝ)) 3 (495176387587/500000000000 : ℝ) (990352775177/1000000000000 : ℝ) (990352775173/1000000000000 : ℝ) (990352775177/1000000000000 : ℝ) (990352775173/1000000000000 : ℝ) (990352775177/1000000000000 : ℝ) (990352775173/1000000000000 : ℝ) (990352775177/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2229/16384 : ℝ)) 4 (990352775173/1000000000000 : ℝ) (990352775177/1000000000000 : ℝ) (990352775173/1000000000000 : ℝ) (990352775177/1000000000000 : ℝ) (990352775173/1000000000000 : ℝ) (990352775177/1000000000000 : ℝ) (990352775173/1000000000000 : ℝ) (990352775177/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2229/16384 : ℝ)) 5 (990352775173/1000000000000 : ℝ) (990352775177/1000000000000 : ℝ) (990352775173/1000000000000 : ℝ) (990352775177/1000000000000 : ℝ) (990352775173/1000000000000 : ℝ) (990352775177/1000000000000 : ℝ) (990352775173/1000000000000 : ℝ) (990352775177/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2229/16384 : ℝ)) 6 (990352775173/1000000000000 : ℝ) (990352775177/1000000000000 : ℝ) (990352775173/1000000000000 : ℝ) (990352775177/1000000000000 : ℝ) (990352775173/1000000000000 : ℝ) (990352775177/1000000000000 : ℝ) (990352775173/1000000000000 : ℝ) (990352775177/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2229/16384 : ℝ)) 7 (990352775173/1000000000000 : ℝ) (990352775177/1000000000000 : ℝ) (990352775173/1000000000000 : ℝ) (990352775177/1000000000000 : ℝ) (990352775173/1000000000000 : ℝ) (990352775177/1000000000000 : ℝ) (990352775173/1000000000000 : ℝ) (990352775177/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2229/16384 : ℝ))) (195255997637/1000000000000 : ℝ) (195255997643/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2229/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (195255997637/1000000000000 : ℝ) (195255997643/1000000000000 : ℝ) (298813999409/500000000000 : ℝ) (298813999411/500000000000 : ℝ) (441877808491/1000000000000 : ℝ) (441877808499/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2229/16384 : ℝ))) 1 (298813999409/500000000000 : ℝ) (298813999411/500000000000 : ℝ) (441877808491/1000000000000 : ℝ) (441877808499/1000000000000 : ℝ) (259876451827/500000000000 : ℝ) (519752903661/1000000000000 : ℝ) (256942868363/500000000000 : ℝ) (513885736733/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2229/16384 : ℝ))) 2 (259876451827/500000000000 : ℝ) (519752903661/1000000000000 : ℝ) (256942868363/500000000000 : ℝ) (513885736733/1000000000000 : ℝ) (51681932019/100000000000 : ℝ) (516819320197/1000000000000 : ℝ) (12920274857/25000000000 : ℝ) (32300687143/62500000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2229/16384 : ℝ))) 3 (51681932019/100000000000 : ℝ) (516819320197/1000000000000 : ℝ) (12920274857/25000000000 : ℝ) (32300687143/62500000000 : ℝ) (103363031447/200000000000 : ℝ) (516815157243/1000000000000 : ℝ) (258407578609/500000000000 : ℝ) (258407578613/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2229/16384 : ℝ))) 4 (103363031447/200000000000 : ℝ) (516815157243/1000000000000 : ℝ) (258407578609/500000000000 : ℝ) (258407578613/500000000000 : ℝ) (258407578613/500000000000 : ℝ) (103363031447/200000000000 : ℝ) (258407578613/500000000000 : ℝ) (103363031447/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2229/16384 : ℝ))) 5 (258407578613/500000000000 : ℝ) (103363031447/200000000000 : ℝ) (258407578613/500000000000 : ℝ) (103363031447/200000000000 : ℝ) (258407578613/500000000000 : ℝ) (103363031447/200000000000 : ℝ) (258407578613/500000000000 : ℝ) (103363031447/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2229/16384 : ℝ))) 6 (258407578613/500000000000 : ℝ) (103363031447/200000000000 : ℝ) (258407578613/500000000000 : ℝ) (103363031447/200000000000 : ℝ) (258407578613/500000000000 : ℝ) (103363031447/200000000000 : ℝ) (258407578613/500000000000 : ℝ) (103363031447/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2229/16384 : ℝ))) 7 (258407578613/500000000000 : ℝ) (103363031447/200000000000 : ℝ) (258407578613/500000000000 : ℝ) (103363031447/200000000000 : ℝ) (258407578613/500000000000 : ℝ) (103363031447/200000000000 : ℝ) (258407578613/500000000000 : ℝ) (103363031447/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2229/16384 : ℝ)) hmem 8 (990352775173/1000000000000 : ℝ) (990352775177/1000000000000 : ℝ) (990352775173/1000000000000 : ℝ) (990352775177/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2229/16384 : ℝ))) hcmem 8 (258407578613/500000000000 : ℝ) (103363031447/200000000000 : ℝ) (258407578613/500000000000 : ℝ) (103363031447/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2229/16384 : ℝ)) (990352775173/1000000000000 : ℝ) (990352775177/1000000000000 : ℝ) (258407578613/500000000000 : ℝ) (103363031447/200000000000 : ℝ) (819719367633/1000000000000 : ℝ) (204929841913/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0305_exp_lower
  have heNumeric : (403801921539/200000000000 : ℝ)/4 ≤ Real.exp (-10938996210557/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (403801921539/200000000000 : ℝ)/4 ≤ Real.exp ((8915/65536 : ℝ)-(204929841913/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8915/65536 : ℝ) (2229/16384 : ℝ) (204929841913/250000000000 : ℝ) (403801921539/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0306; no trusted numerical premise.
theorem cover7_leaf0306_exp_radius : (997573259627026087/1000000000000000000 : ℝ) ≤ Real.exp ((-8917/458752 : ℝ)/8) ∧ Real.exp ((-8917/458752 : ℝ)/8) ≤ (124696657453378261/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8917/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0306_exp_lower : (918089030984423/1000000000000000 : ℝ) ≤ Real.exp ((-109389964059/160000000000 : ℝ)/8) ∧ Real.exp ((-109389964059/160000000000 : ℝ)/8) ≤ (918089030984423001/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-109389964059/160000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0306_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (403801916609/200000000000 : ℝ) ≤ 4*Real.exp (2229/16384 : ℝ)*Real.exp (-mu (radius 7 (8917/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (403801916609/200000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8917/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0306_exp_radius
  have hrNumeric : (980750173057/1000000000000 : ℝ) ≤ Real.exp (-8917/458752 : ℝ) ∧ Real.exp (-8917/458752 : ℝ) ≤ (490375086529/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980750173057/1000000000000 : ℝ) ≤ (radius 7 (8917/65536 : ℝ)) ∧ (radius 7 (8917/65536 : ℝ)) ≤ (490375086529/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8917/65536 : ℝ)) (980750173057/1000000000000 : ℝ) (490375086529/500000000000 : ℝ) (195266735637/1000000000000 : ℝ) (195266735643/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8917/65536 : ℝ)) (980750173057/1000000000000 : ℝ) (490375086529/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8917/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980750173057/1000000000000 : ℝ) (490375086529/500000000000 : ℝ) (15474610727/15625000000 : ℝ) (990375086529/1000000000000 : ℝ) (99032831579/100000000000 : ℝ) (61895519737/62500000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8917/65536 : ℝ)) 1 (15474610727/15625000000 : ℝ) (990375086529/1000000000000 : ℝ) (99032831579/100000000000 : ℝ) (61895519737/62500000000 : ℝ) (990351701159/1000000000000 : ℝ) (990351701161/1000000000000 : ℝ) (495175850441/500000000000 : ℝ) (198070340177/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8917/65536 : ℝ)) 2 (990351701159/1000000000000 : ℝ) (990351701161/1000000000000 : ℝ) (495175850441/500000000000 : ℝ) (198070340177/200000000000 : ℝ) (49517585051/50000000000 : ℝ) (990351701023/1000000000000 : ℝ) (49517585051/50000000000 : ℝ) (990351701023/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8917/65536 : ℝ)) 3 (49517585051/50000000000 : ℝ) (990351701023/1000000000000 : ℝ) (49517585051/50000000000 : ℝ) (990351701023/1000000000000 : ℝ) (49517585051/50000000000 : ℝ) (990351701023/1000000000000 : ℝ) (49517585051/50000000000 : ℝ) (990351701023/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8917/65536 : ℝ)) 4 (49517585051/50000000000 : ℝ) (990351701023/1000000000000 : ℝ) (49517585051/50000000000 : ℝ) (990351701023/1000000000000 : ℝ) (49517585051/50000000000 : ℝ) (990351701023/1000000000000 : ℝ) (49517585051/50000000000 : ℝ) (990351701023/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8917/65536 : ℝ)) 5 (49517585051/50000000000 : ℝ) (990351701023/1000000000000 : ℝ) (49517585051/50000000000 : ℝ) (990351701023/1000000000000 : ℝ) (49517585051/50000000000 : ℝ) (990351701023/1000000000000 : ℝ) (49517585051/50000000000 : ℝ) (990351701023/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8917/65536 : ℝ)) 6 (49517585051/50000000000 : ℝ) (990351701023/1000000000000 : ℝ) (49517585051/50000000000 : ℝ) (990351701023/1000000000000 : ℝ) (49517585051/50000000000 : ℝ) (990351701023/1000000000000 : ℝ) (49517585051/50000000000 : ℝ) (990351701023/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8917/65536 : ℝ)) 7 (49517585051/50000000000 : ℝ) (990351701023/1000000000000 : ℝ) (49517585051/50000000000 : ℝ) (990351701023/1000000000000 : ℝ) (49517585051/50000000000 : ℝ) (990351701023/1000000000000 : ℝ) (49517585051/50000000000 : ℝ) (990351701023/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8917/65536 : ℝ))) (195266735637/1000000000000 : ℝ) (195266735643/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8917/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (195266735637/1000000000000 : ℝ) (195266735643/1000000000000 : ℝ) (298816683909/500000000000 : ℝ) (298816683911/500000000000 : ℝ) (441889958741/1000000000000 : ℝ) (441889958749/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8917/65536 : ℝ))) 1 (298816683909/500000000000 : ℝ) (298816683911/500000000000 : ℝ) (441889958741/1000000000000 : ℝ) (441889958749/1000000000000 : ℝ) (519761663279/1000000000000 : ℝ) (259880831643/500000000000 : ℝ) (6423688877/12500000000 : ℝ) (64236888771/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8917/65536 : ℝ))) 2 (519761663279/1000000000000 : ℝ) (259880831643/500000000000 : ℝ) (6423688877/12500000000 : ℝ) (64236888771/125000000000 : ℝ) (516828386719/1000000000000 : ℝ) (516828386727/1000000000000 : ℝ) (258410031349/500000000000 : ℝ) (516820062707/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8917/65536 : ℝ))) 3 (516828386719/1000000000000 : ℝ) (516828386727/1000000000000 : ℝ) (258410031349/500000000000 : ℝ) (516820062707/1000000000000 : ℝ) (129206056177/250000000000 : ℝ) (516824224717/1000000000000 : ℝ) (516824224691/1000000000000 : ℝ) (516824224701/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8917/65536 : ℝ))) 4 (129206056177/250000000000 : ℝ) (516824224717/1000000000000 : ℝ) (516824224691/1000000000000 : ℝ) (516824224701/1000000000000 : ℝ) (516824224699/1000000000000 : ℝ) (516824224709/1000000000000 : ℝ) (516824224699/1000000000000 : ℝ) (516824224709/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8917/65536 : ℝ))) 5 (516824224699/1000000000000 : ℝ) (516824224709/1000000000000 : ℝ) (516824224699/1000000000000 : ℝ) (516824224709/1000000000000 : ℝ) (516824224699/1000000000000 : ℝ) (516824224709/1000000000000 : ℝ) (516824224699/1000000000000 : ℝ) (516824224709/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8917/65536 : ℝ))) 6 (516824224699/1000000000000 : ℝ) (516824224709/1000000000000 : ℝ) (516824224699/1000000000000 : ℝ) (516824224709/1000000000000 : ℝ) (516824224699/1000000000000 : ℝ) (516824224709/1000000000000 : ℝ) (516824224699/1000000000000 : ℝ) (516824224709/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8917/65536 : ℝ))) 7 (516824224699/1000000000000 : ℝ) (516824224709/1000000000000 : ℝ) (516824224699/1000000000000 : ℝ) (516824224709/1000000000000 : ℝ) (516824224699/1000000000000 : ℝ) (516824224709/1000000000000 : ℝ) (516824224699/1000000000000 : ℝ) (516824224709/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8917/65536 : ℝ)) hmem 8 (49517585051/50000000000 : ℝ) (990351701023/1000000000000 : ℝ) (49517585051/50000000000 : ℝ) (990351701023/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8917/65536 : ℝ))) hcmem 8 (516824224699/1000000000000 : ℝ) (516824224709/1000000000000 : ℝ) (516824224699/1000000000000 : ℝ) (516824224709/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8917/65536 : ℝ)) (49517585051/50000000000 : ℝ) (990351701023/1000000000000 : ℝ) (516824224699/1000000000000 : ℝ) (516824224709/1000000000000 : ℝ) (819734638631/1000000000000 : ℝ) (16394692773/20000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0306_exp_lower
  have heNumeric : (403801916609/200000000000 : ℝ)/4 ≤ Real.exp (-109389964059/160000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (403801916609/200000000000 : ℝ)/4 ≤ Real.exp ((2229/16384 : ℝ)-(16394692773/20000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2229/16384 : ℝ) (8917/65536 : ℝ) (16394692773/20000000000 : ℝ) (403801916609/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0307; no trusted numerical premise.
theorem cover7_leaf0307_exp_radius : (997572987809921279/1000000000000000000 : ℝ) ≤ Real.exp ((-637/32768 : ℝ)/8) ∧ Real.exp ((-637/32768 : ℝ)/8) ≤ (779353896726501/781250000000000 : ℝ) := by
  have h := exp_small_bounds ((-637/32768 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0307_exp_lower : (183617805942758991/200000000000000000 : ℝ) ≤ Real.exp ((-10938996583051/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938996583051/16000000000000 : ℝ)/8) ≤ (229522257428448739/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938996583051/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0307_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019009560691/1000000000000 : ℝ) ≤ 4*Real.exp (8917/65536 : ℝ)*Real.exp (-mu (radius 7 (4459/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (2019009560691/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4459/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0307_exp_radius
  have hrNumeric : (980748035193/1000000000000 : ℝ) ≤ Real.exp (-637/32768 : ℝ) ∧ Real.exp (-637/32768 : ℝ) ≤ (490374017597/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980748035193/1000000000000 : ℝ) ≤ (radius 7 (4459/32768 : ℝ)) ∧ (radius 7 (4459/32768 : ℝ)) ≤ (490374017597/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4459/32768 : ℝ)) (980748035193/1000000000000 : ℝ) (490374017597/500000000000 : ℝ) (48819368251/250000000000 : ℝ) (19527747301/100000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4459/32768 : ℝ)) (980748035193/1000000000000 : ℝ) (490374017597/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4459/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980748035193/1000000000000 : ℝ) (490374017597/500000000000 : ℝ) (247593504399/250000000000 : ℝ) (990374017597/1000000000000 : ℝ) (495163618209/500000000000 : ℝ) (49516361821/50000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4459/32768 : ℝ)) 1 (247593504399/250000000000 : ℝ) (990374017597/1000000000000 : ℝ) (495163618209/500000000000 : ℝ) (49516361821/50000000000 : ℝ) (990350627007/1000000000000 : ℝ) (990350627009/1000000000000 : ℝ) (99035062673/100000000000 : ℝ) (990350626733/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4459/32768 : ℝ)) 2 (990350627007/1000000000000 : ℝ) (990350627009/1000000000000 : ℝ) (99035062673/100000000000 : ℝ) (990350626733/1000000000000 : ℝ) (247587656717/250000000000 : ℝ) (990350626871/1000000000000 : ℝ) (247587656717/250000000000 : ℝ) (990350626871/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4459/32768 : ℝ)) 3 (247587656717/250000000000 : ℝ) (990350626871/1000000000000 : ℝ) (247587656717/250000000000 : ℝ) (990350626871/1000000000000 : ℝ) (247587656717/250000000000 : ℝ) (990350626871/1000000000000 : ℝ) (247587656717/250000000000 : ℝ) (990350626871/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4459/32768 : ℝ)) 4 (247587656717/250000000000 : ℝ) (990350626871/1000000000000 : ℝ) (247587656717/250000000000 : ℝ) (990350626871/1000000000000 : ℝ) (247587656717/250000000000 : ℝ) (990350626871/1000000000000 : ℝ) (247587656717/250000000000 : ℝ) (990350626871/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4459/32768 : ℝ)) 5 (247587656717/250000000000 : ℝ) (990350626871/1000000000000 : ℝ) (247587656717/250000000000 : ℝ) (990350626871/1000000000000 : ℝ) (247587656717/250000000000 : ℝ) (990350626871/1000000000000 : ℝ) (247587656717/250000000000 : ℝ) (990350626871/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4459/32768 : ℝ)) 6 (247587656717/250000000000 : ℝ) (990350626871/1000000000000 : ℝ) (247587656717/250000000000 : ℝ) (990350626871/1000000000000 : ℝ) (247587656717/250000000000 : ℝ) (990350626871/1000000000000 : ℝ) (247587656717/250000000000 : ℝ) (990350626871/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4459/32768 : ℝ)) 7 (247587656717/250000000000 : ℝ) (990350626871/1000000000000 : ℝ) (247587656717/250000000000 : ℝ) (990350626871/1000000000000 : ℝ) (247587656717/250000000000 : ℝ) (990350626871/1000000000000 : ℝ) (247587656717/250000000000 : ℝ) (990350626871/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4459/32768 : ℝ))) (48819368251/250000000000 : ℝ) (19527747301/100000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4459/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (48819368251/250000000000 : ℝ) (19527747301/100000000000 : ℝ) (298819368251/500000000000 : ℝ) (119527747301/200000000000 : ℝ) (220951053971/500000000000 : ℝ) (8838042159/20000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4459/32768 : ℝ))) 1 (298819368251/500000000000 : ℝ) (119527747301/200000000000 : ℝ) (220951053971/500000000000 : ℝ) (8838042159/20000000000 : ℝ) (259885211111/500000000000 : ℝ) (129942605557/250000000000 : ℝ) (102780896561/200000000000 : ℝ) (128476120703/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4459/32768 : ℝ))) 2 (259885211111/500000000000 : ℝ) (129942605557/250000000000 : ℝ) (102780896561/200000000000 : ℝ) (128476120703/250000000000 : ℝ) (516837452513/1000000000000 : ℝ) (12920936313/25000000000 : ℝ) (516829130379/1000000000000 : ℝ) (516829130387/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4459/32768 : ℝ))) 3 (516837452513/1000000000000 : ℝ) (12920936313/25000000000 : ℝ) (516829130379/1000000000000 : ℝ) (516829130387/1000000000000 : ℝ) (258416645723/500000000000 : ℝ) (258416645727/500000000000 : ℝ) (516833291429/1000000000000 : ℝ) (516833291437/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4459/32768 : ℝ))) 4 (258416645723/500000000000 : ℝ) (258416645727/500000000000 : ℝ) (516833291429/1000000000000 : ℝ) (516833291437/1000000000000 : ℝ) (516833291437/1000000000000 : ℝ) (258416645723/500000000000 : ℝ) (516833291437/1000000000000 : ℝ) (258416645723/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4459/32768 : ℝ))) 5 (516833291437/1000000000000 : ℝ) (258416645723/500000000000 : ℝ) (516833291437/1000000000000 : ℝ) (258416645723/500000000000 : ℝ) (516833291437/1000000000000 : ℝ) (258416645723/500000000000 : ℝ) (516833291437/1000000000000 : ℝ) (258416645723/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4459/32768 : ℝ))) 6 (516833291437/1000000000000 : ℝ) (258416645723/500000000000 : ℝ) (516833291437/1000000000000 : ℝ) (258416645723/500000000000 : ℝ) (516833291437/1000000000000 : ℝ) (258416645723/500000000000 : ℝ) (516833291437/1000000000000 : ℝ) (258416645723/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4459/32768 : ℝ))) 7 (516833291437/1000000000000 : ℝ) (258416645723/500000000000 : ℝ) (516833291437/1000000000000 : ℝ) (258416645723/500000000000 : ℝ) (516833291437/1000000000000 : ℝ) (258416645723/500000000000 : ℝ) (516833291437/1000000000000 : ℝ) (258416645723/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4459/32768 : ℝ)) hmem 8 (247587656717/250000000000 : ℝ) (990350626871/1000000000000 : ℝ) (247587656717/250000000000 : ℝ) (990350626871/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4459/32768 : ℝ))) hcmem 8 (516833291437/1000000000000 : ℝ) (258416645723/500000000000 : ℝ) (516833291437/1000000000000 : ℝ) (258416645723/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4459/32768 : ℝ)) (247587656717/250000000000 : ℝ) (990350626871/1000000000000 : ℝ) (516833291437/1000000000000 : ℝ) (258416645723/500000000000 : ℝ) (409874954247/500000000000 : ℝ) (819749908511/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0307_exp_lower
  have heNumeric : (2019009560691/1000000000000 : ℝ)/4 ≤ Real.exp (-10938996583051/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019009560691/1000000000000 : ℝ)/4 ≤ Real.exp ((8917/65536 : ℝ)-(819749908511/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8917/65536 : ℝ) (4459/32768 : ℝ) (819749908511/1000000000000 : ℝ) (2019009560691/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0308; no trusted numerical premise.
theorem cover7_leaf0308_exp_radius : (199514543198578107/200000000000000000 : ℝ) ≤ Real.exp ((-8919/458752 : ℝ)/8) ∧ Real.exp ((-8919/458752 : ℝ)/8) ≤ (124696589499111317/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8919/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0308_exp_lower : (91808902857525697/100000000000000000 : ℝ) ≤ Real.exp ((-5469498370893/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469498370893/8000000000000 : ℝ)/8) ≤ (918089028575256971/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469498370893/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0308_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (100950477033/50000000000 : ℝ) ≤ 4*Real.exp (4459/32768 : ℝ)*Real.exp (-mu (radius 7 (8919/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (100950477033/50000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8919/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0308_exp_radius
  have hrNumeric : (196149179467/200000000000 : ℝ) ≤ Real.exp (-8919/458752 : ℝ) ∧ Real.exp (-8919/458752 : ℝ) ≤ (122593237167/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196149179467/200000000000 : ℝ) ≤ (radius 7 (8919/65536 : ℝ)) ∧ (radius 7 (8919/65536 : ℝ)) ≤ (122593237167/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8919/65536 : ℝ)) (196149179467/200000000000 : ℝ) (122593237167/125000000000 : ℝ) (195288209727/1000000000000 : ℝ) (195288209733/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8919/65536 : ℝ)) (196149179467/200000000000 : ℝ) (122593237167/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8919/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196149179467/200000000000 : ℝ) (122593237167/125000000000 : ℝ) (990372948667/1000000000000 : ℝ) (247593237167/250000000000 : ℝ) (123790769631/125000000000 : ℝ) (19806523141/20000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8919/65536 : ℝ)) 1 (990372948667/1000000000000 : ℝ) (247593237167/250000000000 : ℝ) (123790769631/125000000000 : ℝ) (19806523141/20000000000 : ℝ) (990349552857/1000000000000 : ℝ) (990349552859/1000000000000 : ℝ) (990349552581/1000000000000 : ℝ) (990349552583/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8919/65536 : ℝ)) 2 (990349552857/1000000000000 : ℝ) (990349552859/1000000000000 : ℝ) (990349552581/1000000000000 : ℝ) (990349552583/1000000000000 : ℝ) (990349552719/1000000000000 : ℝ) (990349552721/1000000000000 : ℝ) (495174776359/500000000000 : ℝ) (990349552721/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8919/65536 : ℝ)) 3 (990349552719/1000000000000 : ℝ) (990349552721/1000000000000 : ℝ) (495174776359/500000000000 : ℝ) (990349552721/1000000000000 : ℝ) (495174776359/500000000000 : ℝ) (990349552721/1000000000000 : ℝ) (495174776359/500000000000 : ℝ) (990349552721/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8919/65536 : ℝ)) 4 (495174776359/500000000000 : ℝ) (990349552721/1000000000000 : ℝ) (495174776359/500000000000 : ℝ) (990349552721/1000000000000 : ℝ) (495174776359/500000000000 : ℝ) (990349552721/1000000000000 : ℝ) (495174776359/500000000000 : ℝ) (990349552721/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8919/65536 : ℝ)) 5 (495174776359/500000000000 : ℝ) (990349552721/1000000000000 : ℝ) (495174776359/500000000000 : ℝ) (990349552721/1000000000000 : ℝ) (495174776359/500000000000 : ℝ) (990349552721/1000000000000 : ℝ) (495174776359/500000000000 : ℝ) (990349552721/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8919/65536 : ℝ)) 6 (495174776359/500000000000 : ℝ) (990349552721/1000000000000 : ℝ) (495174776359/500000000000 : ℝ) (990349552721/1000000000000 : ℝ) (495174776359/500000000000 : ℝ) (990349552721/1000000000000 : ℝ) (495174776359/500000000000 : ℝ) (990349552721/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8919/65536 : ℝ)) 7 (495174776359/500000000000 : ℝ) (990349552721/1000000000000 : ℝ) (495174776359/500000000000 : ℝ) (990349552721/1000000000000 : ℝ) (495174776359/500000000000 : ℝ) (990349552721/1000000000000 : ℝ) (495174776359/500000000000 : ℝ) (990349552721/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8919/65536 : ℝ))) (195288209727/1000000000000 : ℝ) (195288209733/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8919/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (195288209727/1000000000000 : ℝ) (195288209733/1000000000000 : ℝ) (597644104863/1000000000000 : ℝ) (597644104867/1000000000000 : ℝ) (5523928201/12500000000 : ℝ) (55239282011/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8919/65536 : ℝ))) 1 (597644104863/1000000000000 : ℝ) (597644104867/1000000000000 : ℝ) (5523928201/12500000000 : ℝ) (55239282011/125000000000 : ℝ) (519779180471/1000000000000 : ℝ) (259889590239/500000000000 : ℝ) (513913854649/1000000000000 : ℝ) (513913854657/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8919/65536 : ℝ))) 2 (519779180471/1000000000000 : ℝ) (259889590239/500000000000 : ℝ) (513913854649/1000000000000 : ℝ) (513913854657/1000000000000 : ℝ) (12921162939/25000000000 : ℝ) (8075726837/15625000000 : ℝ) (516838197313/1000000000000 : ℝ) (516838197321/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8919/65536 : ℝ))) 3 (12921162939/25000000000 : ℝ) (8075726837/15625000000 : ℝ) (516838197313/1000000000000 : ℝ) (516838197321/1000000000000 : ℝ) (129210589359/250000000000 : ℝ) (103368471489/200000000000 : ℝ) (516842357419/1000000000000 : ℝ) (129210589357/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8919/65536 : ℝ))) 4 (129210589359/250000000000 : ℝ) (103368471489/200000000000 : ℝ) (516842357419/1000000000000 : ℝ) (129210589357/250000000000 : ℝ) (516842357427/1000000000000 : ℝ) (516842357437/1000000000000 : ℝ) (516842357427/1000000000000 : ℝ) (516842357437/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8919/65536 : ℝ))) 5 (516842357427/1000000000000 : ℝ) (516842357437/1000000000000 : ℝ) (516842357427/1000000000000 : ℝ) (516842357437/1000000000000 : ℝ) (516842357427/1000000000000 : ℝ) (516842357437/1000000000000 : ℝ) (516842357427/1000000000000 : ℝ) (516842357437/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8919/65536 : ℝ))) 6 (516842357427/1000000000000 : ℝ) (516842357437/1000000000000 : ℝ) (516842357427/1000000000000 : ℝ) (516842357437/1000000000000 : ℝ) (516842357427/1000000000000 : ℝ) (516842357437/1000000000000 : ℝ) (516842357427/1000000000000 : ℝ) (516842357437/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8919/65536 : ℝ))) 7 (516842357427/1000000000000 : ℝ) (516842357437/1000000000000 : ℝ) (516842357427/1000000000000 : ℝ) (516842357437/1000000000000 : ℝ) (516842357427/1000000000000 : ℝ) (516842357437/1000000000000 : ℝ) (516842357427/1000000000000 : ℝ) (516842357437/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8919/65536 : ℝ)) hmem 8 (495174776359/500000000000 : ℝ) (990349552721/1000000000000 : ℝ) (495174776359/500000000000 : ℝ) (990349552721/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8919/65536 : ℝ))) hcmem 8 (516842357427/1000000000000 : ℝ) (516842357437/1000000000000 : ℝ) (516842357427/1000000000000 : ℝ) (516842357437/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8919/65536 : ℝ)) (495174776359/500000000000 : ℝ) (990349552721/1000000000000 : ℝ) (516842357427/1000000000000 : ℝ) (516842357437/1000000000000 : ℝ) (409882588601/500000000000 : ℝ) (819765177221/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0308_exp_lower
  have heNumeric : (100950477033/50000000000 : ℝ)/4 ≤ Real.exp (-5469498370893/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (100950477033/50000000000 : ℝ)/4 ≤ Real.exp ((4459/32768 : ℝ)-(819765177221/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4459/32768 : ℝ) (8919/65536 : ℝ) (819765177221/1000000000000 : ℝ) (100950477033/50000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0309; no trusted numerical premise.
theorem cover7_leaf0309_exp_radius : (31174138880497933/31250000000000000 : ℝ) ≤ Real.exp ((-1115/57344 : ℝ)/8) ∧ Real.exp ((-1115/57344 : ℝ)/8) ≤ (997572444175933857/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1115/57344 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0309_exp_lower : (229522256891743217/250000000000000000 : ℝ) ≤ Real.exp ((-10938996882361/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938996882361/16000000000000 : ℝ)/8) ≤ (918089027566972869/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938996882361/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0309_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019009522921/1000000000000 : ℝ) ≤ 4*Real.exp (8919/65536 : ℝ)*Real.exp (-mu (radius 7 (1115/8192 : ℝ))) ∧ (2019/1000 : ℝ) < (2019009522921/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (1115/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0309_exp_radius
  have hrNumeric : (24518593987/25000000000 : ℝ) ≤ Real.exp (-1115/57344 : ℝ) ∧ Real.exp (-1115/57344 : ℝ) ≤ (980743759481/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (24518593987/25000000000 : ℝ) ≤ (radius 7 (1115/8192 : ℝ)) ∧ (radius 7 (1115/8192 : ℝ)) ≤ (980743759481/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (1115/8192 : ℝ)) (24518593987/25000000000 : ℝ) (980743759481/1000000000000 : ℝ) (195298945821/1000000000000 : ℝ) (195298945827/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (1115/8192 : ℝ)) (24518593987/25000000000 : ℝ) (980743759481/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (1115/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (24518593987/25000000000 : ℝ) (980743759481/1000000000000 : ℝ) (49518593987/50000000000 : ℝ) (990371879741/1000000000000 : ℝ) (990325077679/1000000000000 : ℝ) (12379063471/12500000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (1115/8192 : ℝ)) 1 (49518593987/50000000000 : ℝ) (990371879741/1000000000000 : ℝ) (990325077679/1000000000000 : ℝ) (12379063471/12500000000 : ℝ) (990348478709/1000000000000 : ℝ) (990348478711/1000000000000 : ℝ) (990348478433/1000000000000 : ℝ) (198069695687/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (1115/8192 : ℝ)) 2 (990348478709/1000000000000 : ℝ) (990348478711/1000000000000 : ℝ) (990348478433/1000000000000 : ℝ) (198069695687/200000000000 : ℝ) (990348478571/1000000000000 : ℝ) (990348478573/1000000000000 : ℝ) (99034847857/100000000000 : ℝ) (990348478573/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (1115/8192 : ℝ)) 3 (990348478571/1000000000000 : ℝ) (990348478573/1000000000000 : ℝ) (99034847857/100000000000 : ℝ) (990348478573/1000000000000 : ℝ) (99034847857/100000000000 : ℝ) (990348478573/1000000000000 : ℝ) (99034847857/100000000000 : ℝ) (990348478573/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (1115/8192 : ℝ)) 4 (99034847857/100000000000 : ℝ) (990348478573/1000000000000 : ℝ) (99034847857/100000000000 : ℝ) (990348478573/1000000000000 : ℝ) (99034847857/100000000000 : ℝ) (990348478573/1000000000000 : ℝ) (99034847857/100000000000 : ℝ) (990348478573/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (1115/8192 : ℝ)) 5 (99034847857/100000000000 : ℝ) (990348478573/1000000000000 : ℝ) (99034847857/100000000000 : ℝ) (990348478573/1000000000000 : ℝ) (99034847857/100000000000 : ℝ) (990348478573/1000000000000 : ℝ) (99034847857/100000000000 : ℝ) (990348478573/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (1115/8192 : ℝ)) 6 (99034847857/100000000000 : ℝ) (990348478573/1000000000000 : ℝ) (99034847857/100000000000 : ℝ) (990348478573/1000000000000 : ℝ) (99034847857/100000000000 : ℝ) (990348478573/1000000000000 : ℝ) (99034847857/100000000000 : ℝ) (990348478573/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (1115/8192 : ℝ)) 7 (99034847857/100000000000 : ℝ) (990348478573/1000000000000 : ℝ) (99034847857/100000000000 : ℝ) (990348478573/1000000000000 : ℝ) (99034847857/100000000000 : ℝ) (990348478573/1000000000000 : ℝ) (99034847857/100000000000 : ℝ) (990348478573/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (1115/8192 : ℝ))) (195298945821/1000000000000 : ℝ) (195298945827/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (1115/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (195298945821/1000000000000 : ℝ) (195298945827/1000000000000 : ℝ) (59764947291/100000000000 : ℝ) (298824736457/500000000000 : ℝ) (110481600793/250000000000 : ℝ) (22096320159/50000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (1115/8192 : ℝ))) 1 (59764947291/100000000000 : ℝ) (298824736457/500000000000 : ℝ) (110481600793/250000000000 : ℝ) (22096320159/50000000000 : ℝ) (519787938041/1000000000000 : ℝ) (519787938047/1000000000000 : ℝ) (256961612853/500000000000 : ℝ) (256961612857/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (1115/8192 : ℝ))) 2 (519787938041/1000000000000 : ℝ) (519787938047/1000000000000 : ℝ) (256961612853/500000000000 : ℝ) (256961612857/500000000000 : ℝ) (516855581873/1000000000000 : ℝ) (516855581881/1000000000000 : ℝ) (516847263513/1000000000000 : ℝ) (516847263521/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (1115/8192 : ℝ))) 3 (516855581873/1000000000000 : ℝ) (516855581881/1000000000000 : ℝ) (516847263513/1000000000000 : ℝ) (516847263521/1000000000000 : ℝ) (516851422693/1000000000000 : ℝ) (516851422701/1000000000000 : ℝ) (129212855669/250000000000 : ℝ) (103370284537/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (1115/8192 : ℝ))) 4 (516851422693/1000000000000 : ℝ) (516851422701/1000000000000 : ℝ) (129212855669/250000000000 : ℝ) (103370284537/200000000000 : ℝ) (129212855671/250000000000 : ℝ) (516851422693/1000000000000 : ℝ) (129212855671/250000000000 : ℝ) (516851422693/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (1115/8192 : ℝ))) 5 (129212855671/250000000000 : ℝ) (516851422693/1000000000000 : ℝ) (129212855671/250000000000 : ℝ) (516851422693/1000000000000 : ℝ) (129212855671/250000000000 : ℝ) (516851422693/1000000000000 : ℝ) (129212855671/250000000000 : ℝ) (516851422693/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (1115/8192 : ℝ))) 6 (129212855671/250000000000 : ℝ) (516851422693/1000000000000 : ℝ) (129212855671/250000000000 : ℝ) (516851422693/1000000000000 : ℝ) (129212855671/250000000000 : ℝ) (516851422693/1000000000000 : ℝ) (129212855671/250000000000 : ℝ) (516851422693/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (1115/8192 : ℝ))) 7 (129212855671/250000000000 : ℝ) (516851422693/1000000000000 : ℝ) (129212855671/250000000000 : ℝ) (516851422693/1000000000000 : ℝ) (129212855671/250000000000 : ℝ) (516851422693/1000000000000 : ℝ) (129212855671/250000000000 : ℝ) (516851422693/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (1115/8192 : ℝ)) hmem 8 (99034847857/100000000000 : ℝ) (990348478573/1000000000000 : ℝ) (99034847857/100000000000 : ℝ) (990348478573/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (1115/8192 : ℝ))) hcmem 8 (129212855671/250000000000 : ℝ) (516851422693/1000000000000 : ℝ) (129212855671/250000000000 : ℝ) (516851422693/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (1115/8192 : ℝ)) (99034847857/100000000000 : ℝ) (990348478573/1000000000000 : ℝ) (129212855671/250000000000 : ℝ) (516851422693/1000000000000 : ℝ) (409890222389/500000000000 : ℝ) (204945111199/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0309_exp_lower
  have heNumeric : (2019009522921/1000000000000 : ℝ)/4 ≤ Real.exp (-10938996882361/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019009522921/1000000000000 : ℝ)/4 ≤ Real.exp ((8919/65536 : ℝ)-(204945111199/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8919/65536 : ℝ) (1115/8192 : ℝ) (204945111199/250000000000 : ℝ) (2019009522921/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0310; no trusted numerical premise.
theorem cover7_leaf0310_exp_radius : (997572172359051241/1000000000000000000 : ℝ) ≤ Real.exp ((-8921/458752 : ℝ)/8) ∧ Real.exp ((-8921/458752 : ℝ)/8) ≤ (498786086179525621/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8921/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0310_exp_lower : (36723561067631153/40000000000000000 : ℝ) ≤ Real.exp ((-273474925113/400000000000 : ℝ)/8) ∧ Real.exp ((-273474925113/400000000000 : ℝ)/8) ≤ (459044513345389413/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-273474925113/400000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0310_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009504753753/500000000000 : ℝ) ≤ 4*Real.exp (1115/8192 : ℝ)*Real.exp (-mu (radius 7 (8921/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (1009504753753/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8921/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0310_exp_radius
  have hrNumeric : (980741621631/1000000000000 : ℝ) ≤ Real.exp (-8921/458752 : ℝ) ∧ Real.exp (-8921/458752 : ℝ) ≤ (7662043919/7812500000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980741621631/1000000000000 : ℝ) ≤ (radius 7 (8921/65536 : ℝ)) ∧ (radius 7 (8921/65536 : ℝ)) ≤ (7662043919/7812500000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8921/65536 : ℝ)) (980741621631/1000000000000 : ℝ) (7662043919/7812500000 : ℝ) (24413710159/125000000000 : ℝ) (97654840639/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8921/65536 : ℝ)) (980741621631/1000000000000 : ℝ) (7662043919/7812500000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8921/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980741621631/1000000000000 : ℝ) (7662043919/7812500000 : ℝ) (198074162163/200000000000 : ℝ) (15474543919/15625000000 : ℝ) (990323998311/1000000000000 : ℝ) (123790499789/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8921/65536 : ℝ)) 1 (198074162163/200000000000 : ℝ) (15474543919/15625000000 : ℝ) (990323998311/1000000000000 : ℝ) (123790499789/125000000000 : ℝ) (990347404563/1000000000000 : ℝ) (247586851141/250000000000 : ℝ) (495173702143/500000000000 : ℝ) (967136137/976562500 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8921/65536 : ℝ)) 2 (990347404563/1000000000000 : ℝ) (247586851141/250000000000 : ℝ) (495173702143/500000000000 : ℝ) (967136137/976562500 : ℝ) (123793425553/125000000000 : ℝ) (495173702213/500000000000 : ℝ) (123793425553/125000000000 : ℝ) (495173702213/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8921/65536 : ℝ)) 3 (123793425553/125000000000 : ℝ) (495173702213/500000000000 : ℝ) (123793425553/125000000000 : ℝ) (495173702213/500000000000 : ℝ) (123793425553/125000000000 : ℝ) (495173702213/500000000000 : ℝ) (123793425553/125000000000 : ℝ) (495173702213/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8921/65536 : ℝ)) 4 (123793425553/125000000000 : ℝ) (495173702213/500000000000 : ℝ) (123793425553/125000000000 : ℝ) (495173702213/500000000000 : ℝ) (123793425553/125000000000 : ℝ) (495173702213/500000000000 : ℝ) (123793425553/125000000000 : ℝ) (495173702213/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8921/65536 : ℝ)) 5 (123793425553/125000000000 : ℝ) (495173702213/500000000000 : ℝ) (123793425553/125000000000 : ℝ) (495173702213/500000000000 : ℝ) (123793425553/125000000000 : ℝ) (495173702213/500000000000 : ℝ) (123793425553/125000000000 : ℝ) (495173702213/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8921/65536 : ℝ)) 6 (123793425553/125000000000 : ℝ) (495173702213/500000000000 : ℝ) (123793425553/125000000000 : ℝ) (495173702213/500000000000 : ℝ) (123793425553/125000000000 : ℝ) (495173702213/500000000000 : ℝ) (123793425553/125000000000 : ℝ) (495173702213/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8921/65536 : ℝ)) 7 (123793425553/125000000000 : ℝ) (495173702213/500000000000 : ℝ) (123793425553/125000000000 : ℝ) (495173702213/500000000000 : ℝ) (123793425553/125000000000 : ℝ) (495173702213/500000000000 : ℝ) (123793425553/125000000000 : ℝ) (495173702213/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8921/65536 : ℝ))) (24413710159/125000000000 : ℝ) (97654840639/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8921/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (24413710159/125000000000 : ℝ) (97654840639/500000000000 : ℝ) (149413710159/250000000000 : ℝ) (597654840639/1000000000000 : ℝ) (441938549203/1000000000000 : ℝ) (441938549211/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8921/65536 : ℝ))) 1 (149413710159/250000000000 : ℝ) (597654840639/1000000000000 : ℝ) (441938549203/1000000000000 : ℝ) (441938549211/1000000000000 : ℝ) (519796694919/1000000000000 : ℝ) (20791867797/40000000000 : ℝ) (128483148991/250000000000 : ℝ) (513932595971/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8921/65536 : ℝ))) 2 (519796694919/1000000000000 : ℝ) (20791867797/40000000000 : ℝ) (128483148991/250000000000 : ℝ) (513932595971/1000000000000 : ℝ) (516864645441/1000000000000 : ℝ) (64608080681/125000000000 : ℝ) (258428164483/500000000000 : ℝ) (258428164487/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8921/65536 : ℝ))) 3 (516864645441/1000000000000 : ℝ) (64608080681/125000000000 : ℝ) (258428164483/500000000000 : ℝ) (258428164487/500000000000 : ℝ) (516860487203/1000000000000 : ℝ) (516860487211/1000000000000 : ℝ) (258430243593/500000000000 : ℝ) (103372097439/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8921/65536 : ℝ))) 4 (516860487203/1000000000000 : ℝ) (516860487211/1000000000000 : ℝ) (258430243593/500000000000 : ℝ) (103372097439/200000000000 : ℝ) (258430243597/500000000000 : ℝ) (516860487203/1000000000000 : ℝ) (258430243597/500000000000 : ℝ) (516860487203/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8921/65536 : ℝ))) 5 (258430243597/500000000000 : ℝ) (516860487203/1000000000000 : ℝ) (258430243597/500000000000 : ℝ) (516860487203/1000000000000 : ℝ) (258430243597/500000000000 : ℝ) (516860487203/1000000000000 : ℝ) (258430243597/500000000000 : ℝ) (516860487203/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8921/65536 : ℝ))) 6 (258430243597/500000000000 : ℝ) (516860487203/1000000000000 : ℝ) (258430243597/500000000000 : ℝ) (516860487203/1000000000000 : ℝ) (258430243597/500000000000 : ℝ) (516860487203/1000000000000 : ℝ) (258430243597/500000000000 : ℝ) (516860487203/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8921/65536 : ℝ))) 7 (258430243597/500000000000 : ℝ) (516860487203/1000000000000 : ℝ) (258430243597/500000000000 : ℝ) (516860487203/1000000000000 : ℝ) (258430243597/500000000000 : ℝ) (516860487203/1000000000000 : ℝ) (258430243597/500000000000 : ℝ) (516860487203/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8921/65536 : ℝ)) hmem 8 (123793425553/125000000000 : ℝ) (495173702213/500000000000 : ℝ) (123793425553/125000000000 : ℝ) (495173702213/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8921/65536 : ℝ))) hcmem 8 (258430243597/500000000000 : ℝ) (516860487203/1000000000000 : ℝ) (258430243597/500000000000 : ℝ) (516860487203/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8921/65536 : ℝ)) (123793425553/125000000000 : ℝ) (495173702213/500000000000 : ℝ) (258430243597/500000000000 : ℝ) (516860487203/1000000000000 : ℝ) (819795711203/1000000000000 : ℝ) (40989785561/50000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0310_exp_lower
  have heNumeric : (1009504753753/500000000000 : ℝ)/4 ≤ Real.exp (-273474925113/400000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009504753753/500000000000 : ℝ)/4 ≤ Real.exp ((1115/8192 : ℝ)-(40989785561/50000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (1115/8192 : ℝ) (8921/65536 : ℝ) (40989785561/50000000000 : ℝ) (1009504753753/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0311; no trusted numerical premise.
theorem cover7_leaf0311_exp_radius : (99757190054224269/100000000000000000 : ℝ) ≤ Real.exp ((-4461/229376 : ℝ)/8) ∧ Real.exp ((-4461/229376 : ℝ)/8) ≤ (997571900542242691/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4461/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0311_exp_lower : (459044512972534093/500000000000000000 : ℝ) ≤ Real.exp ((-10938997108487/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938997108487/16000000000000 : ℝ)/8) ≤ (918089025945068187/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938997108487/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0311_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019009494387/1000000000000 : ℝ) ≤ 4*Real.exp (8921/65536 : ℝ)*Real.exp (-mu (radius 7 (4461/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (2019009494387/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4461/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0311_exp_radius
  have hrNumeric : (490369741893/500000000000 : ℝ) ≤ Real.exp (-4461/229376 : ℝ) ∧ Real.exp (-4461/229376 : ℝ) ≤ (980739483787/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490369741893/500000000000 : ℝ) ≤ (radius 7 (4461/32768 : ℝ)) ∧ (radius 7 (4461/32768 : ℝ)) ≤ (980739483787/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4461/32768 : ℝ)) (490369741893/500000000000 : ℝ) (980739483787/1000000000000 : ℝ) (195320416089/1000000000000 : ℝ) (39064083219/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4461/32768 : ℝ)) (490369741893/500000000000 : ℝ) (980739483787/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4461/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490369741893/500000000000 : ℝ) (980739483787/1000000000000 : ℝ) (990369741893/1000000000000 : ℝ) (495184870947/500000000000 : ℝ) (30947591217/31250000000 : ℝ) (198064583789/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4461/32768 : ℝ)) 1 (990369741893/1000000000000 : ℝ) (495184870947/500000000000 : ℝ) (30947591217/31250000000 : ℝ) (198064583789/200000000000 : ℝ) (495173165209/500000000000 : ℝ) (49517316521/50000000000 : ℝ) (990346330141/1000000000000 : ℝ) (990346330143/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4461/32768 : ℝ)) 2 (495173165209/500000000000 : ℝ) (49517316521/50000000000 : ℝ) (990346330141/1000000000000 : ℝ) (990346330143/1000000000000 : ℝ) (990346330279/1000000000000 : ℝ) (495173165141/500000000000 : ℝ) (990346330279/1000000000000 : ℝ) (495173165141/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4461/32768 : ℝ)) 3 (990346330279/1000000000000 : ℝ) (495173165141/500000000000 : ℝ) (990346330279/1000000000000 : ℝ) (495173165141/500000000000 : ℝ) (990346330279/1000000000000 : ℝ) (495173165141/500000000000 : ℝ) (990346330279/1000000000000 : ℝ) (495173165141/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4461/32768 : ℝ)) 4 (990346330279/1000000000000 : ℝ) (495173165141/500000000000 : ℝ) (990346330279/1000000000000 : ℝ) (495173165141/500000000000 : ℝ) (990346330279/1000000000000 : ℝ) (495173165141/500000000000 : ℝ) (990346330279/1000000000000 : ℝ) (495173165141/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4461/32768 : ℝ)) 5 (990346330279/1000000000000 : ℝ) (495173165141/500000000000 : ℝ) (990346330279/1000000000000 : ℝ) (495173165141/500000000000 : ℝ) (990346330279/1000000000000 : ℝ) (495173165141/500000000000 : ℝ) (990346330279/1000000000000 : ℝ) (495173165141/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4461/32768 : ℝ)) 6 (990346330279/1000000000000 : ℝ) (495173165141/500000000000 : ℝ) (990346330279/1000000000000 : ℝ) (495173165141/500000000000 : ℝ) (990346330279/1000000000000 : ℝ) (495173165141/500000000000 : ℝ) (990346330279/1000000000000 : ℝ) (495173165141/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4461/32768 : ℝ)) 7 (990346330279/1000000000000 : ℝ) (495173165141/500000000000 : ℝ) (990346330279/1000000000000 : ℝ) (495173165141/500000000000 : ℝ) (990346330279/1000000000000 : ℝ) (495173165141/500000000000 : ℝ) (990346330279/1000000000000 : ℝ) (495173165141/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4461/32768 : ℝ))) (195320416089/1000000000000 : ℝ) (39064083219/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4461/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (195320416089/1000000000000 : ℝ) (39064083219/200000000000 : ℝ) (149415052011/250000000000 : ℝ) (37353763003/62500000000 : ℝ) (441950694183/1000000000000 : ℝ) (44195069419/100000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4461/32768 : ℝ))) 1 (149415052011/250000000000 : ℝ) (37353763003/62500000000 : ℝ) (441950694183/1000000000000 : ℝ) (44195069419/100000000000 : ℝ) (519805451113/1000000000000 : ℝ) (519805451119/1000000000000 : ℝ) (51394196543/100000000000 : ℝ) (513941965437/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4461/32768 : ℝ))) 2 (519805451113/1000000000000 : ℝ) (519805451119/1000000000000 : ℝ) (51394196543/100000000000 : ℝ) (513941965437/1000000000000 : ℝ) (516873708271/1000000000000 : ℝ) (258436854139/500000000000 : ℝ) (258432696841/500000000000 : ℝ) (516865393689/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4461/32768 : ℝ))) 3 (516873708271/1000000000000 : ℝ) (258436854139/500000000000 : ℝ) (258432696841/500000000000 : ℝ) (516865393689/1000000000000 : ℝ) (4038043367/7812500000 : ℝ) (64608693873/125000000000 : ℝ) (516869550959/1000000000000 : ℝ) (516869550967/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4461/32768 : ℝ))) 4 (4038043367/7812500000 : ℝ) (64608693873/125000000000 : ℝ) (516869550959/1000000000000 : ℝ) (516869550967/1000000000000 : ℝ) (516869550967/1000000000000 : ℝ) (4038043367/7812500000 : ℝ) (516869550967/1000000000000 : ℝ) (4038043367/7812500000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4461/32768 : ℝ))) 5 (516869550967/1000000000000 : ℝ) (4038043367/7812500000 : ℝ) (516869550967/1000000000000 : ℝ) (4038043367/7812500000 : ℝ) (516869550967/1000000000000 : ℝ) (4038043367/7812500000 : ℝ) (516869550967/1000000000000 : ℝ) (4038043367/7812500000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4461/32768 : ℝ))) 6 (516869550967/1000000000000 : ℝ) (4038043367/7812500000 : ℝ) (516869550967/1000000000000 : ℝ) (4038043367/7812500000 : ℝ) (516869550967/1000000000000 : ℝ) (4038043367/7812500000 : ℝ) (516869550967/1000000000000 : ℝ) (4038043367/7812500000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4461/32768 : ℝ))) 7 (516869550967/1000000000000 : ℝ) (4038043367/7812500000 : ℝ) (516869550967/1000000000000 : ℝ) (4038043367/7812500000 : ℝ) (516869550967/1000000000000 : ℝ) (4038043367/7812500000 : ℝ) (516869550967/1000000000000 : ℝ) (4038043367/7812500000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4461/32768 : ℝ)) hmem 8 (990346330279/1000000000000 : ℝ) (495173165141/500000000000 : ℝ) (990346330279/1000000000000 : ℝ) (495173165141/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4461/32768 : ℝ))) hcmem 8 (516869550967/1000000000000 : ℝ) (4038043367/7812500000 : ℝ) (516869550967/1000000000000 : ℝ) (4038043367/7812500000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4461/32768 : ℝ)) (990346330279/1000000000000 : ℝ) (495173165141/500000000000 : ℝ) (516869550967/1000000000000 : ℝ) (4038043367/7812500000 : ℝ) (819810976489/1000000000000 : ℝ) (819810976507/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0311_exp_lower
  have heNumeric : (2019009494387/1000000000000 : ℝ)/4 ≤ Real.exp (-10938997108487/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019009494387/1000000000000 : ℝ)/4 ≤ Real.exp ((8921/65536 : ℝ)-(819810976507/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8921/65536 : ℝ) (4461/32768 : ℝ) (819810976507/1000000000000 : ℝ) (2019009494387/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0312; no trusted numerical premise.
theorem cover7_leaf0312_exp_radius : (997571628725508203/1000000000000000000 : ℝ) ≤ Real.exp ((-8923/458752 : ℝ)/8) ∧ Real.exp ((-8923/458752 : ℝ)/8) ≤ (249392907181377051/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8923/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0312_exp_lower : (4590445126654369/5000000000000000 : ℝ) ≤ Real.exp ((-5469498597059/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469498597059/8000000000000 : ℝ)/8) ≤ (918089025330873801/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469498597059/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0312_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019009483581/1000000000000 : ℝ) ≤ 4*Real.exp (4461/32768 : ℝ)*Real.exp (-mu (radius 7 (8923/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (2019009483581/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8923/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0312_exp_radius
  have hrNumeric : (490368672973/500000000000 : ℝ) ≤ Real.exp (-8923/458752 : ℝ) ∧ Real.exp (-8923/458752 : ℝ) ≤ (980737345947/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490368672973/500000000000 : ℝ) ≤ (radius 7 (8923/65536 : ℝ)) ∧ (radius 7 (8923/65536 : ℝ)) ≤ (980737345947/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8923/65536 : ℝ)) (490368672973/500000000000 : ℝ) (980737345947/1000000000000 : ℝ) (195331150267/1000000000000 : ℝ) (195331150273/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8923/65536 : ℝ)) (490368672973/500000000000 : ℝ) (980737345947/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8923/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490368672973/500000000000 : ℝ) (980737345947/1000000000000 : ℝ) (990368672973/1000000000000 : ℝ) (495184336487/500000000000 : ℝ) (495160919789/500000000000 : ℝ) (990321839579/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8923/65536 : ℝ)) 1 (990368672973/1000000000000 : ℝ) (495184336487/500000000000 : ℝ) (495160919789/500000000000 : ℝ) (990321839579/1000000000000 : ℝ) (39613810251/40000000000 : ℝ) (990345256277/1000000000000 : ℝ) (495172627999/500000000000 : ℝ) (123793157/125000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8923/65536 : ℝ)) 2 (39613810251/40000000000 : ℝ) (990345256277/1000000000000 : ℝ) (495172627999/500000000000 : ℝ) (123793157/125000000 : ℝ) (123793157017/125000000000 : ℝ) (990345256139/1000000000000 : ℝ) (123793157017/125000000000 : ℝ) (990345256139/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8923/65536 : ℝ)) 3 (123793157017/125000000000 : ℝ) (990345256139/1000000000000 : ℝ) (123793157017/125000000000 : ℝ) (990345256139/1000000000000 : ℝ) (123793157017/125000000000 : ℝ) (990345256139/1000000000000 : ℝ) (123793157017/125000000000 : ℝ) (990345256139/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8923/65536 : ℝ)) 4 (123793157017/125000000000 : ℝ) (990345256139/1000000000000 : ℝ) (123793157017/125000000000 : ℝ) (990345256139/1000000000000 : ℝ) (123793157017/125000000000 : ℝ) (990345256139/1000000000000 : ℝ) (123793157017/125000000000 : ℝ) (990345256139/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8923/65536 : ℝ)) 5 (123793157017/125000000000 : ℝ) (990345256139/1000000000000 : ℝ) (123793157017/125000000000 : ℝ) (990345256139/1000000000000 : ℝ) (123793157017/125000000000 : ℝ) (990345256139/1000000000000 : ℝ) (123793157017/125000000000 : ℝ) (990345256139/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8923/65536 : ℝ)) 6 (123793157017/125000000000 : ℝ) (990345256139/1000000000000 : ℝ) (123793157017/125000000000 : ℝ) (990345256139/1000000000000 : ℝ) (123793157017/125000000000 : ℝ) (990345256139/1000000000000 : ℝ) (123793157017/125000000000 : ℝ) (990345256139/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8923/65536 : ℝ)) 7 (123793157017/125000000000 : ℝ) (990345256139/1000000000000 : ℝ) (123793157017/125000000000 : ℝ) (990345256139/1000000000000 : ℝ) (123793157017/125000000000 : ℝ) (990345256139/1000000000000 : ℝ) (123793157017/125000000000 : ℝ) (990345256139/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8923/65536 : ℝ))) (195331150267/1000000000000 : ℝ) (195331150273/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8923/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (195331150267/1000000000000 : ℝ) (195331150273/1000000000000 : ℝ) (597665575133/1000000000000 : ℝ) (597665575137/1000000000000 : ℝ) (220981419053/500000000000 : ℝ) (220981419057/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8923/65536 : ℝ))) 1 (597665575133/1000000000000 : ℝ) (597665575137/1000000000000 : ℝ) (220981419053/500000000000 : ℝ) (220981419057/500000000000 : ℝ) (519814206619/1000000000000 : ℝ) (259907103313/500000000000 : ℝ) (5139513341/10000000000 : ℝ) (128487833527/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8923/65536 : ℝ))) 2 (519814206619/1000000000000 : ℝ) (259907103313/500000000000 : ℝ) (5139513341/10000000000 : ℝ) (128487833527/250000000000 : ℝ) (516882770359/1000000000000 : ℝ) (516882770367/1000000000000 : ℝ) (258437228827/500000000000 : ℝ) (516874457663/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8923/65536 : ℝ))) 3 (516882770359/1000000000000 : ℝ) (516882770367/1000000000000 : ℝ) (258437228827/500000000000 : ℝ) (516874457663/1000000000000 : ℝ) (258439307003/500000000000 : ℝ) (103375722803/200000000000 : ℝ) (516878613989/1000000000000 : ℝ) (516878613999/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8923/65536 : ℝ))) 4 (258439307003/500000000000 : ℝ) (103375722803/200000000000 : ℝ) (516878613989/1000000000000 : ℝ) (516878613999/1000000000000 : ℝ) (516878613997/1000000000000 : ℝ) (516878614007/1000000000000 : ℝ) (516878613997/1000000000000 : ℝ) (516878614007/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8923/65536 : ℝ))) 5 (516878613997/1000000000000 : ℝ) (516878614007/1000000000000 : ℝ) (516878613997/1000000000000 : ℝ) (516878614007/1000000000000 : ℝ) (516878613997/1000000000000 : ℝ) (516878614007/1000000000000 : ℝ) (516878613997/1000000000000 : ℝ) (516878614007/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8923/65536 : ℝ))) 6 (516878613997/1000000000000 : ℝ) (516878614007/1000000000000 : ℝ) (516878613997/1000000000000 : ℝ) (516878614007/1000000000000 : ℝ) (516878613997/1000000000000 : ℝ) (516878614007/1000000000000 : ℝ) (516878613997/1000000000000 : ℝ) (516878614007/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8923/65536 : ℝ))) 7 (516878613997/1000000000000 : ℝ) (516878614007/1000000000000 : ℝ) (516878613997/1000000000000 : ℝ) (516878614007/1000000000000 : ℝ) (516878613997/1000000000000 : ℝ) (516878614007/1000000000000 : ℝ) (516878613997/1000000000000 : ℝ) (516878614007/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8923/65536 : ℝ)) hmem 8 (123793157017/125000000000 : ℝ) (990345256139/1000000000000 : ℝ) (123793157017/125000000000 : ℝ) (990345256139/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8923/65536 : ℝ))) hcmem 8 (516878613997/1000000000000 : ℝ) (516878614007/1000000000000 : ℝ) (516878613997/1000000000000 : ℝ) (516878614007/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8923/65536 : ℝ)) (123793157017/125000000000 : ℝ) (990345256139/1000000000000 : ℝ) (516878613997/1000000000000 : ℝ) (516878614007/1000000000000 : ℝ) (819826240629/1000000000000 : ℝ) (102478280081/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0312_exp_lower
  have heNumeric : (2019009483581/1000000000000 : ℝ)/4 ≤ Real.exp (-5469498597059/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019009483581/1000000000000 : ℝ)/4 ≤ Real.exp ((4461/32768 : ℝ)-(102478280081/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4461/32768 : ℝ) (8923/65536 : ℝ) (102478280081/125000000000 : ℝ) (2019009483581/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0313; no trusted numerical premise.
theorem cover7_leaf0313_exp_radius : (997571356908847781/1000000000000000000 : ℝ) ≤ Real.exp ((-2231/114688 : ℝ)/8) ∧ Real.exp ((-2231/114688 : ℝ)/8) ≤ (498785678454423891/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2231/114688 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0313_exp_lower : (918089024848080907/1000000000000000000 : ℝ) ≤ Real.exp ((-10938997261429/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938997261429/16000000000000 : ℝ)/8) ≤ (229522256212020227/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938997261429/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0313_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (126188092193/62500000000 : ℝ) ≤ 4*Real.exp (8923/65536 : ℝ)*Real.exp (-mu (radius 7 (2231/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (126188092193/62500000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2231/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0313_exp_radius
  have hrNumeric : (980735208111/1000000000000 : ℝ) ≤ Real.exp (-2231/114688 : ℝ) ∧ Real.exp (-2231/114688 : ℝ) ≤ (61295950507/62500000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980735208111/1000000000000 : ℝ) ≤ (radius 7 (2231/16384 : ℝ)) ∧ (radius 7 (2231/16384 : ℝ)) ≤ (61295950507/62500000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2231/16384 : ℝ)) (980735208111/1000000000000 : ℝ) (61295950507/62500000000 : ℝ) (195341883807/1000000000000 : ℝ) (195341883813/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2231/16384 : ℝ)) (980735208111/1000000000000 : ℝ) (61295950507/62500000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2231/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980735208111/1000000000000 : ℝ) (61295950507/62500000000 : ℝ) (198073520811/200000000000 : ℝ) (123795950507/125000000000 : ℝ) (495160380107/500000000000 : ℝ) (198064152043/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2231/16384 : ℝ)) 1 (198073520811/200000000000 : ℝ) (123795950507/125000000000 : ℝ) (495160380107/500000000000 : ℝ) (198064152043/200000000000 : ℝ) (495172091067/500000000000 : ℝ) (123793022767/125000000000 : ℝ) (990344181857/1000000000000 : ℝ) (990344181859/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2231/16384 : ℝ)) 2 (495172091067/500000000000 : ℝ) (123793022767/125000000000 : ℝ) (990344181857/1000000000000 : ℝ) (990344181859/1000000000000 : ℝ) (198068836399/200000000000 : ℝ) (495172090999/500000000000 : ℝ) (198068836399/200000000000 : ℝ) (495172090999/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2231/16384 : ℝ)) 3 (198068836399/200000000000 : ℝ) (495172090999/500000000000 : ℝ) (198068836399/200000000000 : ℝ) (495172090999/500000000000 : ℝ) (198068836399/200000000000 : ℝ) (495172090999/500000000000 : ℝ) (198068836399/200000000000 : ℝ) (495172090999/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2231/16384 : ℝ)) 4 (198068836399/200000000000 : ℝ) (495172090999/500000000000 : ℝ) (198068836399/200000000000 : ℝ) (495172090999/500000000000 : ℝ) (198068836399/200000000000 : ℝ) (495172090999/500000000000 : ℝ) (198068836399/200000000000 : ℝ) (495172090999/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2231/16384 : ℝ)) 5 (198068836399/200000000000 : ℝ) (495172090999/500000000000 : ℝ) (198068836399/200000000000 : ℝ) (495172090999/500000000000 : ℝ) (198068836399/200000000000 : ℝ) (495172090999/500000000000 : ℝ) (198068836399/200000000000 : ℝ) (495172090999/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2231/16384 : ℝ)) 6 (198068836399/200000000000 : ℝ) (495172090999/500000000000 : ℝ) (198068836399/200000000000 : ℝ) (495172090999/500000000000 : ℝ) (198068836399/200000000000 : ℝ) (495172090999/500000000000 : ℝ) (198068836399/200000000000 : ℝ) (495172090999/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2231/16384 : ℝ)) 7 (198068836399/200000000000 : ℝ) (495172090999/500000000000 : ℝ) (198068836399/200000000000 : ℝ) (495172090999/500000000000 : ℝ) (198068836399/200000000000 : ℝ) (495172090999/500000000000 : ℝ) (198068836399/200000000000 : ℝ) (495172090999/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2231/16384 : ℝ))) (195341883807/1000000000000 : ℝ) (195341883813/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2231/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (195341883807/1000000000000 : ℝ) (195341883813/1000000000000 : ℝ) (597670941903/1000000000000 : ℝ) (597670941907/1000000000000 : ℝ) (220987490487/500000000000 : ℝ) (441974980981/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2231/16384 : ℝ))) 1 (597670941903/1000000000000 : ℝ) (597670941907/1000000000000 : ℝ) (220987490487/500000000000 : ℝ) (441974980981/1000000000000 : ℝ) (259911480719/500000000000 : ℝ) (129955740361/250000000000 : ℝ) (64245087747/125000000000 : ℝ) (513960701983/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2231/16384 : ℝ))) 2 (259911480719/500000000000 : ℝ) (129955740361/250000000000 : ℝ) (64245087747/125000000000 : ℝ) (513960701983/1000000000000 : ℝ) (516891831707/1000000000000 : ℝ) (258445915857/500000000000 : ℝ) (258441760443/500000000000 : ℝ) (516883520893/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2231/16384 : ℝ))) 3 (516891831707/1000000000000 : ℝ) (258445915857/500000000000 : ℝ) (258441760443/500000000000 : ℝ) (516883520893/1000000000000 : ℝ) (64610959537/125000000000 : ℝ) (32305479769/62500000000 : ℝ) (516887676279/1000000000000 : ℝ) (516887676287/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2231/16384 : ℝ))) 4 (64610959537/125000000000 : ℝ) (32305479769/62500000000 : ℝ) (516887676279/1000000000000 : ℝ) (516887676287/1000000000000 : ℝ) (516887676287/1000000000000 : ℝ) (64610959537/125000000000 : ℝ) (516887676287/1000000000000 : ℝ) (64610959537/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2231/16384 : ℝ))) 5 (516887676287/1000000000000 : ℝ) (64610959537/125000000000 : ℝ) (516887676287/1000000000000 : ℝ) (64610959537/125000000000 : ℝ) (516887676287/1000000000000 : ℝ) (64610959537/125000000000 : ℝ) (516887676287/1000000000000 : ℝ) (64610959537/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2231/16384 : ℝ))) 6 (516887676287/1000000000000 : ℝ) (64610959537/125000000000 : ℝ) (516887676287/1000000000000 : ℝ) (64610959537/125000000000 : ℝ) (516887676287/1000000000000 : ℝ) (64610959537/125000000000 : ℝ) (516887676287/1000000000000 : ℝ) (64610959537/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2231/16384 : ℝ))) 7 (516887676287/1000000000000 : ℝ) (64610959537/125000000000 : ℝ) (516887676287/1000000000000 : ℝ) (64610959537/125000000000 : ℝ) (516887676287/1000000000000 : ℝ) (64610959537/125000000000 : ℝ) (516887676287/1000000000000 : ℝ) (64610959537/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2231/16384 : ℝ)) hmem 8 (198068836399/200000000000 : ℝ) (495172090999/500000000000 : ℝ) (198068836399/200000000000 : ℝ) (495172090999/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2231/16384 : ℝ))) hcmem 8 (516887676287/1000000000000 : ℝ) (64610959537/125000000000 : ℝ) (516887676287/1000000000000 : ℝ) (64610959537/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2231/16384 : ℝ)) (198068836399/200000000000 : ℝ) (495172090999/500000000000 : ℝ) (516887676287/1000000000000 : ℝ) (64610959537/125000000000 : ℝ) (409920751813/500000000000 : ℝ) (204960375911/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0313_exp_lower
  have heNumeric : (126188092193/62500000000 : ℝ)/4 ≤ Real.exp (-10938997261429/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (126188092193/62500000000 : ℝ)/4 ≤ Real.exp ((8923/65536 : ℝ)-(204960375911/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8923/65536 : ℝ) (2231/16384 : ℝ) (204960375911/250000000000 : ℝ) (126188092193/62500000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0314; no trusted numerical premise.
theorem cover7_leaf0314_exp_radius : (997571085092261423/1000000000000000000 : ℝ) ≤ Real.exp ((-1275/65536 : ℝ)/8) ∧ Real.exp ((-1275/65536 : ℝ)/8) ≤ (62348192818266339/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1275/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0314_exp_lower : (114761128061971427/125000000000000000 : ℝ) ≤ Real.exp ((-2734749327637/4000000000000 : ℝ)/8) ∧ Real.exp ((-2734749327637/4000000000000 : ℝ)/8) ≤ (918089024495771417/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2734749327637/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0314_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019009468889/1000000000000 : ℝ) ≤ 4*Real.exp (2231/16384 : ℝ)*Real.exp (-mu (radius 7 (8925/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (2019009468889/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8925/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0314_exp_radius
  have hrNumeric : (24518326757/25000000000 : ℝ) ≤ Real.exp (-1275/65536 : ℝ) ∧ Real.exp (-1275/65536 : ℝ) ≤ (980733070281/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (24518326757/25000000000 : ℝ) ≤ (radius 7 (8925/65536 : ℝ)) ∧ (radius 7 (8925/65536 : ℝ)) ≤ (980733070281/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8925/65536 : ℝ)) (24518326757/25000000000 : ℝ) (980733070281/1000000000000 : ℝ) (97676308357/500000000000 : ℝ) (2441907709/12500000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8925/65536 : ℝ)) (24518326757/25000000000 : ℝ) (980733070281/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8925/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (24518326757/25000000000 : ℝ) (980733070281/1000000000000 : ℝ) (49518326757/50000000000 : ℝ) (990366535141/1000000000000 : ℝ) (19806393617/20000000000 : ℝ) (247579920213/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8925/65536 : ℝ)) 1 (49518326757/50000000000 : ℝ) (990366535141/1000000000000 : ℝ) (19806393617/20000000000 : ℝ) (247579920213/250000000000 : ℝ) (198068621599/200000000000 : ℝ) (990343107997/1000000000000 : ℝ) (990343107717/1000000000000 : ℝ) (24758577693/25000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8925/65536 : ℝ)) 2 (198068621599/200000000000 : ℝ) (990343107997/1000000000000 : ℝ) (990343107717/1000000000000 : ℝ) (24758577693/25000000000 : ℝ) (61896444241/62500000000 : ℝ) (990343107859/1000000000000 : ℝ) (198068621571/200000000000 : ℝ) (990343107859/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8925/65536 : ℝ)) 3 (61896444241/62500000000 : ℝ) (990343107859/1000000000000 : ℝ) (198068621571/200000000000 : ℝ) (990343107859/1000000000000 : ℝ) (198068621571/200000000000 : ℝ) (990343107859/1000000000000 : ℝ) (198068621571/200000000000 : ℝ) (990343107859/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8925/65536 : ℝ)) 4 (198068621571/200000000000 : ℝ) (990343107859/1000000000000 : ℝ) (198068621571/200000000000 : ℝ) (990343107859/1000000000000 : ℝ) (198068621571/200000000000 : ℝ) (990343107859/1000000000000 : ℝ) (198068621571/200000000000 : ℝ) (990343107859/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8925/65536 : ℝ)) 5 (198068621571/200000000000 : ℝ) (990343107859/1000000000000 : ℝ) (198068621571/200000000000 : ℝ) (990343107859/1000000000000 : ℝ) (198068621571/200000000000 : ℝ) (990343107859/1000000000000 : ℝ) (198068621571/200000000000 : ℝ) (990343107859/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8925/65536 : ℝ)) 6 (198068621571/200000000000 : ℝ) (990343107859/1000000000000 : ℝ) (198068621571/200000000000 : ℝ) (990343107859/1000000000000 : ℝ) (198068621571/200000000000 : ℝ) (990343107859/1000000000000 : ℝ) (198068621571/200000000000 : ℝ) (990343107859/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8925/65536 : ℝ)) 7 (198068621571/200000000000 : ℝ) (990343107859/1000000000000 : ℝ) (198068621571/200000000000 : ℝ) (990343107859/1000000000000 : ℝ) (198068621571/200000000000 : ℝ) (990343107859/1000000000000 : ℝ) (198068621571/200000000000 : ℝ) (990343107859/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8925/65536 : ℝ))) (97676308357/500000000000 : ℝ) (2441907709/12500000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8925/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (97676308357/500000000000 : ℝ) (2441907709/12500000000 : ℝ) (597676308357/1000000000000 : ℝ) (14941907709/25000000000 : ℝ) (55248390349/125000000000 : ℝ) (441987122799/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8925/65536 : ℝ))) 1 (597676308357/1000000000000 : ℝ) (14941907709/25000000000 : ℝ) (55248390349/125000000000 : ℝ) (441987122799/1000000000000 : ℝ) (259915857787/500000000000 : ℝ) (25991585779/50000000000 : ℝ) (256985034531/500000000000 : ℝ) (128492517267/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8925/65536 : ℝ))) 2 (259915857787/500000000000 : ℝ) (25991585779/50000000000 : ℝ) (256985034531/500000000000 : ℝ) (128492517267/250000000000 : ℝ) (258450446159/500000000000 : ℝ) (129225223081/250000000000 : ℝ) (25844629169/50000000000 : ℝ) (516892583387/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8925/65536 : ℝ))) 3 (258450446159/500000000000 : ℝ) (129225223081/250000000000 : ℝ) (25844629169/50000000000 : ℝ) (516892583387/1000000000000 : ℝ) (516896737849/1000000000000 : ℝ) (8076511529/15625000000 : ℝ) (64612092229/125000000000 : ℝ) (516896737839/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8925/65536 : ℝ))) 4 (516896737849/1000000000000 : ℝ) (8076511529/15625000000 : ℝ) (64612092229/125000000000 : ℝ) (516896737839/1000000000000 : ℝ) (6461209223/12500000000 : ℝ) (64612092231/125000000000 : ℝ) (6461209223/12500000000 : ℝ) (64612092231/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8925/65536 : ℝ))) 5 (6461209223/12500000000 : ℝ) (64612092231/125000000000 : ℝ) (6461209223/12500000000 : ℝ) (64612092231/125000000000 : ℝ) (6461209223/12500000000 : ℝ) (64612092231/125000000000 : ℝ) (6461209223/12500000000 : ℝ) (64612092231/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8925/65536 : ℝ))) 6 (6461209223/12500000000 : ℝ) (64612092231/125000000000 : ℝ) (6461209223/12500000000 : ℝ) (64612092231/125000000000 : ℝ) (6461209223/12500000000 : ℝ) (64612092231/125000000000 : ℝ) (6461209223/12500000000 : ℝ) (64612092231/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8925/65536 : ℝ))) 7 (6461209223/12500000000 : ℝ) (64612092231/125000000000 : ℝ) (6461209223/12500000000 : ℝ) (64612092231/125000000000 : ℝ) (6461209223/12500000000 : ℝ) (64612092231/125000000000 : ℝ) (6461209223/12500000000 : ℝ) (64612092231/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8925/65536 : ℝ)) hmem 8 (198068621571/200000000000 : ℝ) (990343107859/1000000000000 : ℝ) (198068621571/200000000000 : ℝ) (990343107859/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8925/65536 : ℝ))) hcmem 8 (6461209223/12500000000 : ℝ) (64612092231/125000000000 : ℝ) (6461209223/12500000000 : ℝ) (64612092231/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8925/65536 : ℝ)) (198068621571/200000000000 : ℝ) (990343107859/1000000000000 : ℝ) (6461209223/12500000000 : ℝ) (64612092231/125000000000 : ℝ) (409928382743/500000000000 : ℝ) (819856765503/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0314_exp_lower
  have heNumeric : (2019009468889/1000000000000 : ℝ)/4 ≤ Real.exp (-2734749327637/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019009468889/1000000000000 : ℝ)/4 ≤ Real.exp ((2231/16384 : ℝ)-(819856765503/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2231/16384 : ℝ) (8925/65536 : ℝ) (819856765503/1000000000000 : ℝ) (2019009468889/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0315; no trusted numerical premise.
theorem cover7_leaf0315_exp_radius : (124696351659468641/125000000000000000 : ℝ) ≤ Real.exp ((-4463/229376 : ℝ)/8) ∧ Real.exp ((-4463/229376 : ℝ)/8) ≤ (997570813275749129/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4463/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0315_exp_lower : (57380564017171791/62500000000000000 : ℝ) ≤ Real.exp ((-10938997341363/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938997341363/16000000000000 : ℝ)/8) ≤ (918089024274748657/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938997341363/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0315_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019009465001/1000000000000 : ℝ) ≤ 4*Real.exp (8925/65536 : ℝ)*Real.exp (-mu (radius 7 (4463/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (2019009465001/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4463/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0315_exp_radius
  have hrNumeric : (490365466227/500000000000 : ℝ) ≤ Real.exp (-4463/229376 : ℝ) ∧ Real.exp (-4463/229376 : ℝ) ≤ (196146186491/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490365466227/500000000000 : ℝ) ≤ (radius 7 (4463/32768 : ℝ)) ∧ (radius 7 (4463/32768 : ℝ)) ≤ (196146186491/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4463/32768 : ℝ)) (490365466227/500000000000 : ℝ) (196146186491/200000000000 : ℝ) (195363348983/1000000000000 : ℝ) (195363348989/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4463/32768 : ℝ)) (490365466227/500000000000 : ℝ) (196146186491/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4463/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490365466227/500000000000 : ℝ) (196146186491/200000000000 : ℝ) (990365466227/1000000000000 : ℝ) (247591366557/250000000000 : ℝ) (61894912593/62500000000 : ℝ) (990318601489/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4463/32768 : ℝ)) 1 (990365466227/1000000000000 : ℝ) (247591366557/250000000000 : ℝ) (61894912593/62500000000 : ℝ) (990318601489/1000000000000 : ℝ) (990342033857/1000000000000 : ℝ) (990342033859/1000000000000 : ℝ) (49517101679/50000000000 : ℝ) (495171016791/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4463/32768 : ℝ)) 2 (990342033857/1000000000000 : ℝ) (990342033859/1000000000000 : ℝ) (49517101679/50000000000 : ℝ) (495171016791/500000000000 : ℝ) (495171016859/500000000000 : ℝ) (990342033721/1000000000000 : ℝ) (495171016859/500000000000 : ℝ) (990342033721/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4463/32768 : ℝ)) 3 (495171016859/500000000000 : ℝ) (990342033721/1000000000000 : ℝ) (495171016859/500000000000 : ℝ) (990342033721/1000000000000 : ℝ) (495171016859/500000000000 : ℝ) (990342033721/1000000000000 : ℝ) (495171016859/500000000000 : ℝ) (990342033721/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4463/32768 : ℝ)) 4 (495171016859/500000000000 : ℝ) (990342033721/1000000000000 : ℝ) (495171016859/500000000000 : ℝ) (990342033721/1000000000000 : ℝ) (495171016859/500000000000 : ℝ) (990342033721/1000000000000 : ℝ) (495171016859/500000000000 : ℝ) (990342033721/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4463/32768 : ℝ)) 5 (495171016859/500000000000 : ℝ) (990342033721/1000000000000 : ℝ) (495171016859/500000000000 : ℝ) (990342033721/1000000000000 : ℝ) (495171016859/500000000000 : ℝ) (990342033721/1000000000000 : ℝ) (495171016859/500000000000 : ℝ) (990342033721/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4463/32768 : ℝ)) 6 (495171016859/500000000000 : ℝ) (990342033721/1000000000000 : ℝ) (495171016859/500000000000 : ℝ) (990342033721/1000000000000 : ℝ) (495171016859/500000000000 : ℝ) (990342033721/1000000000000 : ℝ) (495171016859/500000000000 : ℝ) (990342033721/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4463/32768 : ℝ)) 7 (495171016859/500000000000 : ℝ) (990342033721/1000000000000 : ℝ) (495171016859/500000000000 : ℝ) (990342033721/1000000000000 : ℝ) (495171016859/500000000000 : ℝ) (990342033721/1000000000000 : ℝ) (495171016859/500000000000 : ℝ) (990342033721/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4463/32768 : ℝ))) (195363348983/1000000000000 : ℝ) (195363348989/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4463/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (195363348983/1000000000000 : ℝ) (195363348989/1000000000000 : ℝ) (597681674491/1000000000000 : ℝ) (119536334899/200000000000 : ℝ) (220999631777/500000000000 : ℝ) (220999631781/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4463/32768 : ℝ))) 1 (597681674491/1000000000000 : ℝ) (119536334899/200000000000 : ℝ) (220999631777/500000000000 : ℝ) (220999631781/500000000000 : ℝ) (259920234511/500000000000 : ℝ) (519840469029/1000000000000 : ℝ) (513979435351/1000000000000 : ℝ) (513979435359/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4463/32768 : ℝ))) 2 (259920234511/500000000000 : ℝ) (519840469029/1000000000000 : ℝ) (513979435351/1000000000000 : ℝ) (513979435359/1000000000000 : ℝ) (258454976093/500000000000 : ℝ) (258454976097/500000000000 : ℝ) (129225411283/250000000000 : ℝ) (25845082257/50000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4463/32768 : ℝ))) 3 (258454976093/500000000000 : ℝ) (258454976097/500000000000 : ℝ) (129225411283/250000000000 : ℝ) (25845082257/50000000000 : ℝ) (516905798659/1000000000000 : ℝ) (516905798667/1000000000000 : ℝ) (258452899321/500000000000 : ℝ) (516905798651/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4463/32768 : ℝ))) 4 (516905798659/1000000000000 : ℝ) (516905798667/1000000000000 : ℝ) (258452899321/500000000000 : ℝ) (516905798651/1000000000000 : ℝ) (10338115973/20000000000 : ℝ) (516905798659/1000000000000 : ℝ) (10338115973/20000000000 : ℝ) (516905798659/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4463/32768 : ℝ))) 5 (10338115973/20000000000 : ℝ) (516905798659/1000000000000 : ℝ) (10338115973/20000000000 : ℝ) (516905798659/1000000000000 : ℝ) (10338115973/20000000000 : ℝ) (516905798659/1000000000000 : ℝ) (10338115973/20000000000 : ℝ) (516905798659/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4463/32768 : ℝ))) 6 (10338115973/20000000000 : ℝ) (516905798659/1000000000000 : ℝ) (10338115973/20000000000 : ℝ) (516905798659/1000000000000 : ℝ) (10338115973/20000000000 : ℝ) (516905798659/1000000000000 : ℝ) (10338115973/20000000000 : ℝ) (516905798659/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4463/32768 : ℝ))) 7 (10338115973/20000000000 : ℝ) (516905798659/1000000000000 : ℝ) (10338115973/20000000000 : ℝ) (516905798659/1000000000000 : ℝ) (10338115973/20000000000 : ℝ) (516905798659/1000000000000 : ℝ) (10338115973/20000000000 : ℝ) (516905798659/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4463/32768 : ℝ)) hmem 8 (495171016859/500000000000 : ℝ) (990342033721/1000000000000 : ℝ) (495171016859/500000000000 : ℝ) (990342033721/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4463/32768 : ℝ))) hcmem 8 (10338115973/20000000000 : ℝ) (516905798659/1000000000000 : ℝ) (10338115973/20000000000 : ℝ) (516905798659/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4463/32768 : ℝ)) (495171016859/500000000000 : ℝ) (990342033721/1000000000000 : ℝ) (10338115973/20000000000 : ℝ) (516905798659/1000000000000 : ℝ) (4099360131/5000000000 : ℝ) (409936013109/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0315_exp_lower
  have heNumeric : (2019009465001/1000000000000 : ℝ)/4 ≤ Real.exp (-10938997341363/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019009465001/1000000000000 : ℝ)/4 ≤ Real.exp ((8925/65536 : ℝ)-(409936013109/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8925/65536 : ℝ) (4463/32768 : ℝ) (409936013109/500000000000 : ℝ) (2019009465001/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0316; no trusted numerical premise.
theorem cover7_leaf0316_exp_radius : (498785270729655449/500000000000000000 : ℝ) ≤ Real.exp ((-8927/458752 : ℝ)/8) ∧ Real.exp ((-8927/458752 : ℝ)/8) ≤ (997570541459310899/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8927/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0316_exp_lower : (918089024184438821/1000000000000000000 : ℝ) ≤ Real.exp ((-5469498676977/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469498676977/8000000000000 : ℝ)/8) ≤ (459044512092219411/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469498676977/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0316_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (504752365853/250000000000 : ℝ) ≤ 4*Real.exp (4463/32768 : ℝ)*Real.exp (-mu (radius 7 (8927/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (504752365853/250000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8927/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0316_exp_radius
  have hrNumeric : (122591099329/125000000000 : ℝ) ≤ Real.exp (-8927/458752 : ℝ) ∧ Real.exp (-8927/458752 : ℝ) ≤ (980728794633/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (122591099329/125000000000 : ℝ) ≤ (radius 7 (8927/65536 : ℝ)) ∧ (radius 7 (8927/65536 : ℝ)) ≤ (980728794633/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8927/65536 : ℝ)) (122591099329/125000000000 : ℝ) (980728794633/1000000000000 : ℝ) (97687040309/500000000000 : ℝ) (12210880039/62500000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8927/65536 : ℝ)) (122591099329/125000000000 : ℝ) (980728794633/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8927/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (122591099329/125000000000 : ℝ) (980728794633/1000000000000 : ℝ) (247591099329/250000000000 : ℝ) (990364397317/1000000000000 : ℝ) (990317522127/1000000000000 : ℝ) (61894845133/62500000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8927/65536 : ℝ)) 1 (247591099329/250000000000 : ℝ) (990364397317/1000000000000 : ℝ) (990317522127/1000000000000 : ℝ) (61894845133/62500000000 : ℝ) (990340959721/1000000000000 : ℝ) (990340959723/1000000000000 : ℝ) (247585239861/250000000000 : ℝ) (495170479723/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8927/65536 : ℝ)) 2 (990340959721/1000000000000 : ℝ) (990340959723/1000000000000 : ℝ) (247585239861/250000000000 : ℝ) (495170479723/500000000000 : ℝ) (495170479791/500000000000 : ℝ) (198068191917/200000000000 : ℝ) (495170479791/500000000000 : ℝ) (198068191917/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8927/65536 : ℝ)) 3 (495170479791/500000000000 : ℝ) (198068191917/200000000000 : ℝ) (495170479791/500000000000 : ℝ) (198068191917/200000000000 : ℝ) (495170479791/500000000000 : ℝ) (198068191917/200000000000 : ℝ) (495170479791/500000000000 : ℝ) (198068191917/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8927/65536 : ℝ)) 4 (495170479791/500000000000 : ℝ) (198068191917/200000000000 : ℝ) (495170479791/500000000000 : ℝ) (198068191917/200000000000 : ℝ) (495170479791/500000000000 : ℝ) (198068191917/200000000000 : ℝ) (495170479791/500000000000 : ℝ) (198068191917/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8927/65536 : ℝ)) 5 (495170479791/500000000000 : ℝ) (198068191917/200000000000 : ℝ) (495170479791/500000000000 : ℝ) (198068191917/200000000000 : ℝ) (495170479791/500000000000 : ℝ) (198068191917/200000000000 : ℝ) (495170479791/500000000000 : ℝ) (198068191917/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8927/65536 : ℝ)) 6 (495170479791/500000000000 : ℝ) (198068191917/200000000000 : ℝ) (495170479791/500000000000 : ℝ) (198068191917/200000000000 : ℝ) (495170479791/500000000000 : ℝ) (198068191917/200000000000 : ℝ) (495170479791/500000000000 : ℝ) (198068191917/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8927/65536 : ℝ)) 7 (495170479791/500000000000 : ℝ) (198068191917/200000000000 : ℝ) (495170479791/500000000000 : ℝ) (198068191917/200000000000 : ℝ) (495170479791/500000000000 : ℝ) (198068191917/200000000000 : ℝ) (495170479791/500000000000 : ℝ) (198068191917/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8927/65536 : ℝ))) (97687040309/500000000000 : ℝ) (12210880039/62500000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8927/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (97687040309/500000000000 : ℝ) (12210880039/62500000000 : ℝ) (597687040309/1000000000000 : ℝ) (74710880039/125000000000 : ℝ) (221005701633/500000000000 : ℝ) (221005701637/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8927/65536 : ℝ))) 1 (597687040309/1000000000000 : ℝ) (74710880039/125000000000 : ℝ) (221005701633/500000000000 : ℝ) (221005701637/500000000000 : ℝ) (519849221787/1000000000000 : ℝ) (519849221793/1000000000000 : ℝ) (513988800851/1000000000000 : ℝ) (256994400429/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8927/65536 : ℝ))) 2 (519849221787/1000000000000 : ℝ) (519849221793/1000000000000 : ℝ) (513988800851/1000000000000 : ℝ) (256994400429/500000000000 : ℝ) (516919011319/1000000000000 : ℝ) (258459505663/500000000000 : ℝ) (516910706147/1000000000000 : ℝ) (258455353077/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8927/65536 : ℝ))) 3 (516919011319/1000000000000 : ℝ) (258459505663/500000000000 : ℝ) (516910706147/1000000000000 : ℝ) (258455353077/500000000000 : ℝ) (516914858733/1000000000000 : ℝ) (25845742937/50000000000 : ℝ) (129228714679/250000000000 : ℝ) (129228714681/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8927/65536 : ℝ))) 4 (516914858733/1000000000000 : ℝ) (25845742937/50000000000 : ℝ) (129228714679/250000000000 : ℝ) (129228714681/250000000000 : ℝ) (129228714681/250000000000 : ℝ) (129228714683/250000000000 : ℝ) (129228714681/250000000000 : ℝ) (129228714683/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8927/65536 : ℝ))) 5 (129228714681/250000000000 : ℝ) (129228714683/250000000000 : ℝ) (129228714681/250000000000 : ℝ) (129228714683/250000000000 : ℝ) (129228714681/250000000000 : ℝ) (129228714683/250000000000 : ℝ) (129228714681/250000000000 : ℝ) (129228714683/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8927/65536 : ℝ))) 6 (129228714681/250000000000 : ℝ) (129228714683/250000000000 : ℝ) (129228714681/250000000000 : ℝ) (129228714683/250000000000 : ℝ) (129228714681/250000000000 : ℝ) (129228714683/250000000000 : ℝ) (129228714681/250000000000 : ℝ) (129228714683/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8927/65536 : ℝ))) 7 (129228714681/250000000000 : ℝ) (129228714683/250000000000 : ℝ) (129228714681/250000000000 : ℝ) (129228714683/250000000000 : ℝ) (129228714681/250000000000 : ℝ) (129228714683/250000000000 : ℝ) (129228714681/250000000000 : ℝ) (129228714683/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8927/65536 : ℝ)) hmem 8 (495170479791/500000000000 : ℝ) (198068191917/200000000000 : ℝ) (495170479791/500000000000 : ℝ) (198068191917/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8927/65536 : ℝ))) hcmem 8 (129228714681/250000000000 : ℝ) (129228714683/250000000000 : ℝ) (129228714681/250000000000 : ℝ) (129228714683/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8927/65536 : ℝ)) (495170479791/500000000000 : ℝ) (198068191917/200000000000 : ℝ) (129228714681/250000000000 : ℝ) (129228714683/250000000000 : ℝ) (409943642889/500000000000 : ℝ) (409943642897/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0316_exp_lower
  have heNumeric : (504752365853/250000000000 : ℝ)/4 ≤ Real.exp (-5469498676977/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (504752365853/250000000000 : ℝ)/4 ≤ Real.exp ((4463/32768 : ℝ)-(409943642897/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4463/32768 : ℝ) (8927/65536 : ℝ) (409943642897/500000000000 : ℝ) (504752365853/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0317; no trusted numerical premise.
theorem cover7_leaf0317_exp_radius : (249392567410736683/250000000000000000 : ℝ) ≤ Real.exp ((-279/14336 : ℝ)/8) ∧ Real.exp ((-279/14336 : ℝ)/8) ≤ (997570269642946733/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-279/14336 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0317_exp_lower : (5738056401411/6250000000000 : ℝ) ≤ Real.exp ((-10938997348193/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938997348193/16000000000000 : ℝ)/8) ≤ (918089024225760001/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938997348193/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0317_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019009464139/1000000000000 : ℝ) ≤ 4*Real.exp (8927/65536 : ℝ)*Real.exp (-mu (radius 7 (279/2048 : ℝ))) ∧ (2019/1000 : ℝ) < (2019009464139/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (279/2048 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0317_exp_radius
  have hrNumeric : (61295416051/62500000000 : ℝ) ≤ Real.exp (-279/14336 : ℝ) ∧ Real.exp (-279/14336 : ℝ) ≤ (980726656817/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (61295416051/62500000000 : ℝ) ≤ (radius 7 (279/2048 : ℝ)) ∧ (radius 7 (279/2048 : ℝ)) ≤ (980726656817/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (279/2048 : ℝ)) (61295416051/62500000000 : ℝ) (980726656817/1000000000000 : ℝ) (195384811611/1000000000000 : ℝ) (195384811617/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (279/2048 : ℝ)) (61295416051/62500000000 : ℝ) (980726656817/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (279/2048 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (61295416051/62500000000 : ℝ) (980726656817/1000000000000 : ℝ) (123795416051/125000000000 : ℝ) (990363328409/1000000000000 : ℝ) (990316442767/1000000000000 : ℝ) (990316442769/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (279/2048 : ℝ)) 1 (123795416051/125000000000 : ℝ) (990363328409/1000000000000 : ℝ) (990316442767/1000000000000 : ℝ) (990316442769/1000000000000 : ℝ) (990339885587/1000000000000 : ℝ) (990339885589/1000000000000 : ℝ) (99033988531/100000000000 : ℝ) (3868515177/3906250000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (279/2048 : ℝ)) 2 (990339885587/1000000000000 : ℝ) (990339885589/1000000000000 : ℝ) (99033988531/100000000000 : ℝ) (3868515177/3906250000 : ℝ) (123792485681/125000000000 : ℝ) (990339885451/1000000000000 : ℝ) (123792485681/125000000000 : ℝ) (990339885451/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (279/2048 : ℝ)) 3 (123792485681/125000000000 : ℝ) (990339885451/1000000000000 : ℝ) (123792485681/125000000000 : ℝ) (990339885451/1000000000000 : ℝ) (123792485681/125000000000 : ℝ) (990339885451/1000000000000 : ℝ) (123792485681/125000000000 : ℝ) (990339885451/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (279/2048 : ℝ)) 4 (123792485681/125000000000 : ℝ) (990339885451/1000000000000 : ℝ) (123792485681/125000000000 : ℝ) (990339885451/1000000000000 : ℝ) (123792485681/125000000000 : ℝ) (990339885451/1000000000000 : ℝ) (123792485681/125000000000 : ℝ) (990339885451/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (279/2048 : ℝ)) 5 (123792485681/125000000000 : ℝ) (990339885451/1000000000000 : ℝ) (123792485681/125000000000 : ℝ) (990339885451/1000000000000 : ℝ) (123792485681/125000000000 : ℝ) (990339885451/1000000000000 : ℝ) (123792485681/125000000000 : ℝ) (990339885451/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (279/2048 : ℝ)) 6 (123792485681/125000000000 : ℝ) (990339885451/1000000000000 : ℝ) (123792485681/125000000000 : ℝ) (990339885451/1000000000000 : ℝ) (123792485681/125000000000 : ℝ) (990339885451/1000000000000 : ℝ) (123792485681/125000000000 : ℝ) (990339885451/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (279/2048 : ℝ)) 7 (123792485681/125000000000 : ℝ) (990339885451/1000000000000 : ℝ) (123792485681/125000000000 : ℝ) (990339885451/1000000000000 : ℝ) (123792485681/125000000000 : ℝ) (990339885451/1000000000000 : ℝ) (123792485681/125000000000 : ℝ) (990339885451/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (279/2048 : ℝ))) (195384811611/1000000000000 : ℝ) (195384811617/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (279/2048 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (195384811611/1000000000000 : ℝ) (195384811617/1000000000000 : ℝ) (119538481161/200000000000 : ℝ) (597692405809/1000000000000 : ℝ) (442023541919/1000000000000 : ℝ) (442023541927/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (279/2048 : ℝ))) 1 (119538481161/200000000000 : ℝ) (597692405809/1000000000000 : ℝ) (442023541919/1000000000000 : ℝ) (442023541927/1000000000000 : ℝ) (259928986931/500000000000 : ℝ) (129964493467/250000000000 : ℝ) (513998165553/1000000000000 : ℝ) (12849954139/25000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (279/2048 : ℝ))) 2 (259928986931/500000000000 : ℝ) (129964493467/250000000000 : ℝ) (513998165553/1000000000000 : ℝ) (12849954139/25000000000 : ℝ) (516928069707/1000000000000 : ℝ) (258464034857/500000000000 : ℝ) (516919766417/1000000000000 : ℝ) (20676790657/40000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (279/2048 : ℝ))) 3 (516928069707/1000000000000 : ℝ) (258464034857/500000000000 : ℝ) (516919766417/1000000000000 : ℝ) (20676790657/40000000000 : ℝ) (258461959031/500000000000 : ℝ) (51692391807/100000000000 : ℝ) (103384783609/200000000000 : ℝ) (516923918053/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (279/2048 : ℝ))) 4 (258461959031/500000000000 : ℝ) (51692391807/100000000000 : ℝ) (103384783609/200000000000 : ℝ) (516923918053/1000000000000 : ℝ) (516923918053/1000000000000 : ℝ) (258461959031/500000000000 : ℝ) (516923918053/1000000000000 : ℝ) (258461959031/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (279/2048 : ℝ))) 5 (516923918053/1000000000000 : ℝ) (258461959031/500000000000 : ℝ) (516923918053/1000000000000 : ℝ) (258461959031/500000000000 : ℝ) (516923918053/1000000000000 : ℝ) (258461959031/500000000000 : ℝ) (516923918053/1000000000000 : ℝ) (258461959031/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (279/2048 : ℝ))) 6 (516923918053/1000000000000 : ℝ) (258461959031/500000000000 : ℝ) (516923918053/1000000000000 : ℝ) (258461959031/500000000000 : ℝ) (516923918053/1000000000000 : ℝ) (258461959031/500000000000 : ℝ) (516923918053/1000000000000 : ℝ) (258461959031/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (279/2048 : ℝ))) 7 (516923918053/1000000000000 : ℝ) (258461959031/500000000000 : ℝ) (516923918053/1000000000000 : ℝ) (258461959031/500000000000 : ℝ) (516923918053/1000000000000 : ℝ) (258461959031/500000000000 : ℝ) (516923918053/1000000000000 : ℝ) (258461959031/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (279/2048 : ℝ)) hmem 8 (123792485681/125000000000 : ℝ) (990339885451/1000000000000 : ℝ) (123792485681/125000000000 : ℝ) (990339885451/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (279/2048 : ℝ))) hcmem 8 (516923918053/1000000000000 : ℝ) (258461959031/500000000000 : ℝ) (516923918053/1000000000000 : ℝ) (258461959031/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (279/2048 : ℝ)) (123792485681/125000000000 : ℝ) (990339885451/1000000000000 : ℝ) (516923918053/1000000000000 : ℝ) (258461959031/500000000000 : ℝ) (409951272103/500000000000 : ℝ) (819902544223/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0317_exp_lower
  have heNumeric : (2019009464139/1000000000000 : ℝ)/4 ≤ Real.exp (-10938997348193/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019009464139/1000000000000 : ℝ)/4 ≤ Real.exp ((8927/65536 : ℝ)-(819902544223/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8927/65536 : ℝ) (279/2048 : ℝ) (819902544223/1000000000000 : ℝ) (2019009464139/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0318; no trusted numerical premise.
theorem cover7_leaf0318_exp_radius : (99756999782665663/100000000000000000 : ℝ) ≤ Real.exp ((-8929/458752 : ℝ)/8) ∧ Real.exp ((-8929/458752 : ℝ)/8) ≤ (997569997826656631/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8929/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0318_exp_lower : (459044512198839671/500000000000000000 : ℝ) ≤ Real.exp ((-170921833191/250000000000 : ℝ)/8) ∧ Real.exp ((-170921833191/250000000000 : ℝ)/8) ≤ (918089024397679343/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-170921833191/250000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0318_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (504752366791/250000000000 : ℝ) ≤ 4*Real.exp (279/2048 : ℝ)*Real.exp (-mu (radius 7 (8929/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (504752366791/250000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8929/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0318_exp_radius
  have hrNumeric : (245181129751/250000000000 : ℝ) ≤ Real.exp (-8929/458752 : ℝ) ∧ Real.exp (-8929/458752 : ℝ) ≤ (196144903801/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (245181129751/250000000000 : ℝ) ≤ (radius 7 (8929/65536 : ℝ)) ∧ (radius 7 (8929/65536 : ℝ)) ≤ (196144903801/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8929/65536 : ℝ)) (245181129751/250000000000 : ℝ) (196144903801/200000000000 : ℝ) (195395541971/1000000000000 : ℝ) (195395541977/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8929/65536 : ℝ)) (245181129751/250000000000 : ℝ) (196144903801/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8929/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (245181129751/250000000000 : ℝ) (196144903801/200000000000 : ℝ) (495181129751/500000000000 : ℝ) (990362259503/1000000000000 : ℝ) (990315363409/1000000000000 : ℝ) (99031536341/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8929/65536 : ℝ)) 1 (495181129751/500000000000 : ℝ) (990362259503/1000000000000 : ℝ) (990315363409/1000000000000 : ℝ) (99031536341/100000000000 : ℝ) (198067762291/200000000000 : ℝ) (990338811457/1000000000000 : ℝ) (990338811177/1000000000000 : ℝ) (990338811179/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8929/65536 : ℝ)) 2 (198067762291/200000000000 : ℝ) (990338811457/1000000000000 : ℝ) (990338811177/1000000000000 : ℝ) (990338811179/1000000000000 : ℝ) (247584702829/250000000000 : ℝ) (495169405659/500000000000 : ℝ) (198067762263/200000000000 : ℝ) (495169405659/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8929/65536 : ℝ)) 3 (247584702829/250000000000 : ℝ) (495169405659/500000000000 : ℝ) (198067762263/200000000000 : ℝ) (495169405659/500000000000 : ℝ) (198067762263/200000000000 : ℝ) (495169405659/500000000000 : ℝ) (198067762263/200000000000 : ℝ) (495169405659/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8929/65536 : ℝ)) 4 (198067762263/200000000000 : ℝ) (495169405659/500000000000 : ℝ) (198067762263/200000000000 : ℝ) (495169405659/500000000000 : ℝ) (198067762263/200000000000 : ℝ) (495169405659/500000000000 : ℝ) (198067762263/200000000000 : ℝ) (495169405659/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8929/65536 : ℝ)) 5 (198067762263/200000000000 : ℝ) (495169405659/500000000000 : ℝ) (198067762263/200000000000 : ℝ) (495169405659/500000000000 : ℝ) (198067762263/200000000000 : ℝ) (495169405659/500000000000 : ℝ) (198067762263/200000000000 : ℝ) (495169405659/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8929/65536 : ℝ)) 6 (198067762263/200000000000 : ℝ) (495169405659/500000000000 : ℝ) (198067762263/200000000000 : ℝ) (495169405659/500000000000 : ℝ) (198067762263/200000000000 : ℝ) (495169405659/500000000000 : ℝ) (198067762263/200000000000 : ℝ) (495169405659/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8929/65536 : ℝ)) 7 (198067762263/200000000000 : ℝ) (495169405659/500000000000 : ℝ) (198067762263/200000000000 : ℝ) (495169405659/500000000000 : ℝ) (198067762263/200000000000 : ℝ) (495169405659/500000000000 : ℝ) (198067762263/200000000000 : ℝ) (495169405659/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8929/65536 : ℝ))) (195395541971/1000000000000 : ℝ) (195395541977/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8929/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (195395541971/1000000000000 : ℝ) (195395541977/1000000000000 : ℝ) (119539554197/200000000000 : ℝ) (597697770989/1000000000000 : ℝ) (221017839761/500000000000 : ℝ) (44203567953/100000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8929/65536 : ℝ))) 1 (119539554197/200000000000 : ℝ) (597697770989/1000000000000 : ℝ) (221017839761/500000000000 : ℝ) (44203567953/100000000000 : ℝ) (519866725253/1000000000000 : ℝ) (25993336263/50000000000 : ℝ) (64250941183/125000000000 : ℝ) (514007529471/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8929/65536 : ℝ))) 2 (519866725253/1000000000000 : ℝ) (25993336263/50000000000 : ℝ) (64250941183/125000000000 : ℝ) (514007529471/1000000000000 : ℝ) (258468563679/500000000000 : ℝ) (258468563683/500000000000 : ℝ) (516928825949/1000000000000 : ℝ) (516928825957/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8929/65536 : ℝ))) 3 (258468563679/500000000000 : ℝ) (258468563683/500000000000 : ℝ) (516928825949/1000000000000 : ℝ) (516928825957/1000000000000 : ℝ) (516932976653/1000000000000 : ℝ) (258466488331/500000000000 : ℝ) (129233244159/250000000000 : ℝ) (103386595329/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8929/65536 : ℝ))) 4 (516932976653/1000000000000 : ℝ) (258466488331/500000000000 : ℝ) (129233244159/250000000000 : ℝ) (103386595329/200000000000 : ℝ) (129233244161/250000000000 : ℝ) (258466488327/500000000000 : ℝ) (129233244161/250000000000 : ℝ) (258466488327/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8929/65536 : ℝ))) 5 (129233244161/250000000000 : ℝ) (258466488327/500000000000 : ℝ) (129233244161/250000000000 : ℝ) (258466488327/500000000000 : ℝ) (129233244161/250000000000 : ℝ) (258466488327/500000000000 : ℝ) (129233244161/250000000000 : ℝ) (258466488327/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8929/65536 : ℝ))) 6 (129233244161/250000000000 : ℝ) (258466488327/500000000000 : ℝ) (129233244161/250000000000 : ℝ) (258466488327/500000000000 : ℝ) (129233244161/250000000000 : ℝ) (258466488327/500000000000 : ℝ) (129233244161/250000000000 : ℝ) (258466488327/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8929/65536 : ℝ))) 7 (129233244161/250000000000 : ℝ) (258466488327/500000000000 : ℝ) (129233244161/250000000000 : ℝ) (258466488327/500000000000 : ℝ) (129233244161/250000000000 : ℝ) (258466488327/500000000000 : ℝ) (129233244161/250000000000 : ℝ) (258466488327/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8929/65536 : ℝ)) hmem 8 (198067762263/200000000000 : ℝ) (495169405659/500000000000 : ℝ) (198067762263/200000000000 : ℝ) (495169405659/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8929/65536 : ℝ))) hcmem 8 (129233244161/250000000000 : ℝ) (258466488327/500000000000 : ℝ) (129233244161/250000000000 : ℝ) (258466488327/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8929/65536 : ℝ)) (198067762263/200000000000 : ℝ) (495169405659/500000000000 : ℝ) (129233244161/250000000000 : ℝ) (258466488327/500000000000 : ℝ) (163983560299/200000000000 : ℝ) (409958900757/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0318_exp_lower
  have heNumeric : (504752366791/250000000000 : ℝ)/4 ≤ Real.exp (-170921833191/250000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (504752366791/250000000000 : ℝ)/4 ≤ Real.exp ((279/2048 : ℝ)-(409958900757/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (279/2048 : ℝ) (8929/65536 : ℝ) (409958900757/500000000000 : ℝ) (504752366791/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0319; no trusted numerical premise.
theorem cover7_leaf0319_exp_radius : (62348107875652537/62500000000000000 : ℝ) ≤ Real.exp ((-4465/229376 : ℝ)/8) ∧ Real.exp ((-4465/229376 : ℝ)/8) ≤ (997569726010440593/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4465/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0319_exp_lower : (918089024700311609/1000000000000000000 : ℝ) ≤ Real.exp ((-10938997282031/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938997282031/16000000000000 : ℝ)/8) ≤ (91808902470031161/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938997282031/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0319_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (252376184061/125000000000 : ℝ) ≤ 4*Real.exp (8929/65536 : ℝ)*Real.exp (-mu (radius 7 (4465/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (252376184061/125000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4465/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0319_exp_radius
  have hrNumeric : (245180595299/250000000000 : ℝ) ≤ Real.exp (-4465/229376 : ℝ) ∧ Real.exp (-4465/229376 : ℝ) ≤ (980722381197/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (245180595299/250000000000 : ℝ) ≤ (radius 7 (4465/32768 : ℝ)) ∧ (radius 7 (4465/32768 : ℝ)) ≤ (980722381197/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4465/32768 : ℝ)) (245180595299/250000000000 : ℝ) (980722381197/1000000000000 : ℝ) (97703135849/500000000000 : ℝ) (24425783963/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4465/32768 : ℝ)) (245180595299/250000000000 : ℝ) (980722381197/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4465/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (245180595299/250000000000 : ℝ) (980722381197/1000000000000 : ℝ) (495180595299/500000000000 : ℝ) (990361190599/1000000000000 : ℝ) (990314284051/1000000000000 : ℝ) (247578571013/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4465/32768 : ℝ)) 1 (495180595299/500000000000 : ℝ) (990361190599/1000000000000 : ℝ) (990314284051/1000000000000 : ℝ) (247578571013/250000000000 : ℝ) (247584434331/250000000000 : ℝ) (495168868663/500000000000 : ℝ) (495168868523/500000000000 : ℝ) (123792217131/125000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4465/32768 : ℝ)) 2 (247584434331/250000000000 : ℝ) (495168868663/500000000000 : ℝ) (495168868523/500000000000 : ℝ) (123792217131/125000000000 : ℝ) (198067547437/200000000000 : ℝ) (990337737187/1000000000000 : ℝ) (30948054287/31250000000 : ℝ) (990337737187/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4465/32768 : ℝ)) 3 (198067547437/200000000000 : ℝ) (990337737187/1000000000000 : ℝ) (30948054287/31250000000 : ℝ) (990337737187/1000000000000 : ℝ) (30948054287/31250000000 : ℝ) (990337737187/1000000000000 : ℝ) (30948054287/31250000000 : ℝ) (990337737187/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4465/32768 : ℝ)) 4 (30948054287/31250000000 : ℝ) (990337737187/1000000000000 : ℝ) (30948054287/31250000000 : ℝ) (990337737187/1000000000000 : ℝ) (30948054287/31250000000 : ℝ) (990337737187/1000000000000 : ℝ) (30948054287/31250000000 : ℝ) (990337737187/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4465/32768 : ℝ)) 5 (30948054287/31250000000 : ℝ) (990337737187/1000000000000 : ℝ) (30948054287/31250000000 : ℝ) (990337737187/1000000000000 : ℝ) (30948054287/31250000000 : ℝ) (990337737187/1000000000000 : ℝ) (30948054287/31250000000 : ℝ) (990337737187/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4465/32768 : ℝ)) 6 (30948054287/31250000000 : ℝ) (990337737187/1000000000000 : ℝ) (30948054287/31250000000 : ℝ) (990337737187/1000000000000 : ℝ) (30948054287/31250000000 : ℝ) (990337737187/1000000000000 : ℝ) (30948054287/31250000000 : ℝ) (990337737187/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4465/32768 : ℝ)) 7 (30948054287/31250000000 : ℝ) (990337737187/1000000000000 : ℝ) (30948054287/31250000000 : ℝ) (990337737187/1000000000000 : ℝ) (30948054287/31250000000 : ℝ) (990337737187/1000000000000 : ℝ) (30948054287/31250000000 : ℝ) (990337737187/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4465/32768 : ℝ))) (97703135849/500000000000 : ℝ) (24425783963/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4465/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (97703135849/500000000000 : ℝ) (24425783963/125000000000 : ℝ) (597703135849/1000000000000 : ℝ) (149425783963/250000000000 : ℝ) (110511954019/250000000000 : ℝ) (110511954021/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4465/32768 : ℝ))) 1 (597703135849/1000000000000 : ℝ) (149425783963/250000000000 : ℝ) (110511954019/250000000000 : ℝ) (110511954021/250000000000 : ℝ) (259937737981/500000000000 : ℝ) (1015381789/1953125000 : ℝ) (257008446293/500000000000 : ℝ) (32126055787/62500000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4465/32768 : ℝ))) 2 (259937737981/500000000000 : ℝ) (1015381789/1953125000 : ℝ) (257008446293/500000000000 : ℝ) (32126055787/62500000000 : ℝ) (258473092137/500000000000 : ℝ) (12923654607/25000000000 : ℝ) (103387576949/200000000000 : ℝ) (32308617797/62500000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4465/32768 : ℝ))) 3 (258473092137/500000000000 : ℝ) (12923654607/25000000000 : ℝ) (103387576949/200000000000 : ℝ) (32308617797/62500000000 : ℝ) (516942034509/1000000000000 : ℝ) (129235508629/250000000000 : ℝ) (129235508623/250000000000 : ℝ) (1033884069/2000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4465/32768 : ℝ))) 4 (516942034509/1000000000000 : ℝ) (129235508629/250000000000 : ℝ) (129235508623/250000000000 : ℝ) (1033884069/2000000000 : ℝ) (1033884069/2000000000 : ℝ) (129235508627/250000000000 : ℝ) (1033884069/2000000000 : ℝ) (129235508627/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4465/32768 : ℝ))) 5 (1033884069/2000000000 : ℝ) (129235508627/250000000000 : ℝ) (1033884069/2000000000 : ℝ) (129235508627/250000000000 : ℝ) (1033884069/2000000000 : ℝ) (129235508627/250000000000 : ℝ) (1033884069/2000000000 : ℝ) (129235508627/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4465/32768 : ℝ))) 6 (1033884069/2000000000 : ℝ) (129235508627/250000000000 : ℝ) (1033884069/2000000000 : ℝ) (129235508627/250000000000 : ℝ) (1033884069/2000000000 : ℝ) (129235508627/250000000000 : ℝ) (1033884069/2000000000 : ℝ) (129235508627/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4465/32768 : ℝ))) 7 (1033884069/2000000000 : ℝ) (129235508627/250000000000 : ℝ) (1033884069/2000000000 : ℝ) (129235508627/250000000000 : ℝ) (1033884069/2000000000 : ℝ) (129235508627/250000000000 : ℝ) (1033884069/2000000000 : ℝ) (129235508627/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4465/32768 : ℝ)) hmem 8 (30948054287/31250000000 : ℝ) (990337737187/1000000000000 : ℝ) (30948054287/31250000000 : ℝ) (990337737187/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4465/32768 : ℝ))) hcmem 8 (1033884069/2000000000 : ℝ) (129235508627/250000000000 : ℝ) (1033884069/2000000000 : ℝ) (129235508627/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4465/32768 : ℝ)) (30948054287/31250000000 : ℝ) (990337737187/1000000000000 : ℝ) (1033884069/2000000000 : ℝ) (129235508627/250000000000 : ℝ) (16398661153/20000000000 : ℝ) (409966528833/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0319_exp_lower
  have heNumeric : (252376184061/125000000000 : ℝ)/4 ≤ Real.exp (-10938997282031/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (252376184061/125000000000 : ℝ)/4 ≤ Real.exp ((8929/65536 : ℝ)-(409966528833/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8929/65536 : ℝ) (4465/32768 : ℝ) (409966528833/500000000000 : ℝ) (252376184061/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0320; no trusted numerical premise.
theorem cover7_leaf0320_exp_radius : (997569454194298619/1000000000000000000 : ℝ) ≤ Real.exp ((-8931/458752 : ℝ)/8) ∧ Real.exp ((-8931/458752 : ℝ)/8) ≤ (49878472709714931/50000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8931/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0320_exp_lower : (459044512566828401/500000000000000000 : ℝ) ≤ Real.exp ((-5469498610807/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469498610807/8000000000000 : ℝ)/8) ≤ (918089025133656803/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469498610807/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0320_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (126188092507/62500000000 : ℝ) ≤ 4*Real.exp (4465/32768 : ℝ)*Real.exp (-mu (radius 7 (8931/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (126188092507/62500000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8931/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0320_exp_radius
  have hrNumeric : (980720243393/1000000000000 : ℝ) ≤ Real.exp (-8931/458752 : ℝ) ∧ Real.exp (-8931/458752 : ℝ) ≤ (490360121697/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980720243393/1000000000000 : ℝ) ≤ (radius 7 (8931/65536 : ℝ)) ∧ (radius 7 (8931/65536 : ℝ)) ≤ (490360121697/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8931/65536 : ℝ)) (980720243393/1000000000000 : ℝ) (490360121697/500000000000 : ℝ) (48854250197/250000000000 : ℝ) (97708500397/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8931/65536 : ℝ)) (980720243393/1000000000000 : ℝ) (490360121697/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8931/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980720243393/1000000000000 : ℝ) (490360121697/500000000000 : ℝ) (30948753803/31250000000 : ℝ) (990360121697/1000000000000 : ℝ) (495156602347/500000000000 : ℝ) (123789150587/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8931/65536 : ℝ)) 1 (30948753803/31250000000 : ℝ) (990360121697/1000000000000 : ℝ) (495156602347/500000000000 : ℝ) (123789150587/125000000000 : ℝ) (198067332639/200000000000 : ℝ) (990336663197/1000000000000 : ℝ) (990336662917/1000000000000 : ℝ) (990336662919/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8931/65536 : ℝ)) 2 (198067332639/200000000000 : ℝ) (990336663197/1000000000000 : ℝ) (990336662917/1000000000000 : ℝ) (990336662919/1000000000000 : ℝ) (61896041441/62500000000 : ℝ) (495168331529/500000000000 : ℝ) (198067332611/200000000000 : ℝ) (495168331529/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8931/65536 : ℝ)) 3 (61896041441/62500000000 : ℝ) (495168331529/500000000000 : ℝ) (198067332611/200000000000 : ℝ) (495168331529/500000000000 : ℝ) (198067332611/200000000000 : ℝ) (495168331529/500000000000 : ℝ) (198067332611/200000000000 : ℝ) (495168331529/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8931/65536 : ℝ)) 4 (198067332611/200000000000 : ℝ) (495168331529/500000000000 : ℝ) (198067332611/200000000000 : ℝ) (495168331529/500000000000 : ℝ) (198067332611/200000000000 : ℝ) (495168331529/500000000000 : ℝ) (198067332611/200000000000 : ℝ) (495168331529/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8931/65536 : ℝ)) 5 (198067332611/200000000000 : ℝ) (495168331529/500000000000 : ℝ) (198067332611/200000000000 : ℝ) (495168331529/500000000000 : ℝ) (198067332611/200000000000 : ℝ) (495168331529/500000000000 : ℝ) (198067332611/200000000000 : ℝ) (495168331529/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8931/65536 : ℝ)) 6 (198067332611/200000000000 : ℝ) (495168331529/500000000000 : ℝ) (198067332611/200000000000 : ℝ) (495168331529/500000000000 : ℝ) (198067332611/200000000000 : ℝ) (495168331529/500000000000 : ℝ) (198067332611/200000000000 : ℝ) (495168331529/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8931/65536 : ℝ)) 7 (198067332611/200000000000 : ℝ) (495168331529/500000000000 : ℝ) (198067332611/200000000000 : ℝ) (495168331529/500000000000 : ℝ) (198067332611/200000000000 : ℝ) (495168331529/500000000000 : ℝ) (198067332611/200000000000 : ℝ) (495168331529/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8931/65536 : ℝ))) (48854250197/250000000000 : ℝ) (97708500397/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8931/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (48854250197/250000000000 : ℝ) (97708500397/500000000000 : ℝ) (298854250197/500000000000 : ℝ) (597708500397/1000000000000 : ℝ) (55257493947/125000000000 : ℝ) (13814373487/31250000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8931/65536 : ℝ))) 1 (298854250197/500000000000 : ℝ) (597708500397/1000000000000 : ℝ) (55257493947/125000000000 : ℝ) (13814373487/31250000000 : ℝ) (103976845197/200000000000 : ℝ) (519884225991/1000000000000 : ℝ) (514026254913/1000000000000 : ℝ) (12850656373/25000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8931/65536 : ℝ))) 2 (103976845197/200000000000 : ℝ) (519884225991/1000000000000 : ℝ) (514026254913/1000000000000 : ℝ) (12850656373/25000000000 : ℝ) (516955240449/1000000000000 : ℝ) (64619405057/125000000000 : ℝ) (516946942801/1000000000000 : ℝ) (64618367851/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8931/65536 : ℝ))) 3 (516955240449/1000000000000 : ℝ) (64619405057/125000000000 : ℝ) (516946942801/1000000000000 : ℝ) (64618367851/125000000000 : ℝ) (4135608733/8000000000 : ℝ) (32309443227/62500000000 : ℝ) (64618886451/125000000000 : ℝ) (16154721613/31250000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8931/65536 : ℝ))) 4 (4135608733/8000000000 : ℝ) (32309443227/62500000000 : ℝ) (64618886451/125000000000 : ℝ) (16154721613/31250000000 : ℝ) (16154721613/31250000000 : ℝ) (64618886453/125000000000 : ℝ) (16154721613/31250000000 : ℝ) (64618886453/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8931/65536 : ℝ))) 5 (16154721613/31250000000 : ℝ) (64618886453/125000000000 : ℝ) (16154721613/31250000000 : ℝ) (64618886453/125000000000 : ℝ) (16154721613/31250000000 : ℝ) (64618886453/125000000000 : ℝ) (16154721613/31250000000 : ℝ) (64618886453/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8931/65536 : ℝ))) 6 (16154721613/31250000000 : ℝ) (64618886453/125000000000 : ℝ) (16154721613/31250000000 : ℝ) (64618886453/125000000000 : ℝ) (16154721613/31250000000 : ℝ) (64618886453/125000000000 : ℝ) (16154721613/31250000000 : ℝ) (64618886453/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8931/65536 : ℝ))) 7 (16154721613/31250000000 : ℝ) (64618886453/125000000000 : ℝ) (16154721613/31250000000 : ℝ) (64618886453/125000000000 : ℝ) (16154721613/31250000000 : ℝ) (64618886453/125000000000 : ℝ) (16154721613/31250000000 : ℝ) (64618886453/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8931/65536 : ℝ)) hmem 8 (198067332611/200000000000 : ℝ) (495168331529/500000000000 : ℝ) (198067332611/200000000000 : ℝ) (495168331529/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8931/65536 : ℝ))) hcmem 8 (16154721613/31250000000 : ℝ) (64618886453/125000000000 : ℝ) (16154721613/31250000000 : ℝ) (64618886453/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8931/65536 : ℝ)) (198067332611/200000000000 : ℝ) (495168331529/500000000000 : ℝ) (16154721613/31250000000 : ℝ) (64618886453/125000000000 : ℝ) (819948312663/1000000000000 : ℝ) (819948312679/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0320_exp_lower
  have heNumeric : (126188092507/62500000000 : ℝ)/4 ≤ Real.exp (-5469498610807/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (126188092507/62500000000 : ℝ)/4 ≤ Real.exp ((4465/32768 : ℝ)-(819948312679/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4465/32768 : ℝ) (8931/65536 : ℝ) (819948312679/1000000000000 : ℝ) (126188092507/62500000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0321; no trusted numerical premise.
theorem cover7_leaf0321_exp_radius : (997569182378230709/1000000000000000000 : ℝ) ≤ Real.exp ((-319/16384 : ℝ)/8) ∧ Real.exp ((-319/16384 : ℝ)/8) ≤ (99756918237823071/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-319/16384 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0321_exp_lower : (918089025698518247/1000000000000000000 : ℝ) ≤ Real.exp ((-10938997142861/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938997142861/16000000000000 : ℝ)/8) ≤ (114761128212314781/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938997142861/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0321_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019009490049/1000000000000 : ℝ) ≤ 4*Real.exp (8931/65536 : ℝ)*Real.exp (-mu (radius 7 (2233/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (2019009490049/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2233/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0321_exp_radius
  have hrNumeric : (196143621119/200000000000 : ℝ) ≤ Real.exp (-319/16384 : ℝ) ∧ Real.exp (-319/16384 : ℝ) ≤ (245179526399/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196143621119/200000000000 : ℝ) ≤ (radius 7 (2233/16384 : ℝ)) ∧ (radius 7 (2233/16384 : ℝ)) ≤ (245179526399/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2233/16384 : ℝ)) (196143621119/200000000000 : ℝ) (245179526399/250000000000 : ℝ) (4885693231/25000000000 : ℝ) (97713864623/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2233/16384 : ℝ)) (196143621119/200000000000 : ℝ) (245179526399/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2233/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196143621119/200000000000 : ℝ) (245179526399/250000000000 : ℝ) (990359052797/1000000000000 : ℝ) (495179526399/500000000000 : ℝ) (990312125339/1000000000000 : ℝ) (990312125341/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2233/16384 : ℝ)) 1 (990359052797/1000000000000 : ℝ) (495179526399/500000000000 : ℝ) (990312125339/1000000000000 : ℝ) (990312125341/1000000000000 : ℝ) (247583897267/250000000000 : ℝ) (99033558907/100000000000 : ℝ) (99033558879/100000000000 : ℝ) (123791948599/125000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2233/16384 : ℝ)) 2 (247583897267/250000000000 : ℝ) (99033558907/100000000000 : ℝ) (99033558879/100000000000 : ℝ) (123791948599/125000000000 : ℝ) (990335588929/1000000000000 : ℝ) (990335588931/1000000000000 : ℝ) (15473993577/15625000000 : ℝ) (990335588931/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2233/16384 : ℝ)) 3 (990335588929/1000000000000 : ℝ) (990335588931/1000000000000 : ℝ) (15473993577/15625000000 : ℝ) (990335588931/1000000000000 : ℝ) (15473993577/15625000000 : ℝ) (990335588931/1000000000000 : ℝ) (15473993577/15625000000 : ℝ) (990335588931/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2233/16384 : ℝ)) 4 (15473993577/15625000000 : ℝ) (990335588931/1000000000000 : ℝ) (15473993577/15625000000 : ℝ) (990335588931/1000000000000 : ℝ) (15473993577/15625000000 : ℝ) (990335588931/1000000000000 : ℝ) (15473993577/15625000000 : ℝ) (990335588931/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2233/16384 : ℝ)) 5 (15473993577/15625000000 : ℝ) (990335588931/1000000000000 : ℝ) (15473993577/15625000000 : ℝ) (990335588931/1000000000000 : ℝ) (15473993577/15625000000 : ℝ) (990335588931/1000000000000 : ℝ) (15473993577/15625000000 : ℝ) (990335588931/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2233/16384 : ℝ)) 6 (15473993577/15625000000 : ℝ) (990335588931/1000000000000 : ℝ) (15473993577/15625000000 : ℝ) (990335588931/1000000000000 : ℝ) (15473993577/15625000000 : ℝ) (990335588931/1000000000000 : ℝ) (15473993577/15625000000 : ℝ) (990335588931/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2233/16384 : ℝ)) 7 (15473993577/15625000000 : ℝ) (990335588931/1000000000000 : ℝ) (15473993577/15625000000 : ℝ) (990335588931/1000000000000 : ℝ) (15473993577/15625000000 : ℝ) (990335588931/1000000000000 : ℝ) (15473993577/15625000000 : ℝ) (990335588931/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2233/16384 : ℝ))) (4885693231/25000000000 : ℝ) (97713864623/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2233/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (4885693231/25000000000 : ℝ) (97713864623/500000000000 : ℝ) (29885693231/50000000000 : ℝ) (597713864623/1000000000000 : ℝ) (221036043011/500000000000 : ℝ) (442072086029/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2233/16384 : ℝ))) 1 (29885693231/50000000000 : ℝ) (597713864623/1000000000000 : ℝ) (221036043011/500000000000 : ℝ) (442072086029/1000000000000 : ℝ) (519892975321/1000000000000 : ℝ) (259946487663/500000000000 : ℝ) (514035616447/1000000000000 : ℝ) (257017808227/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2233/16384 : ℝ))) 2 (519892975321/1000000000000 : ℝ) (259946487663/500000000000 : ℝ) (514035616447/1000000000000 : ℝ) (257017808227/500000000000 : ℝ) (129241073971/250000000000 : ℝ) (51696429589/100000000000 : ℝ) (103391200023/200000000000 : ℝ) (258478000061/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2233/16384 : ℝ))) 3 (129241073971/250000000000 : ℝ) (51696429589/100000000000 : ℝ) (103391200023/200000000000 : ℝ) (258478000061/500000000000 : ℝ) (516960147999/1000000000000 : ℝ) (258480074003/500000000000 : ℝ) (258480073991/500000000000 : ℝ) (51696014799/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2233/16384 : ℝ))) 4 (516960147999/1000000000000 : ℝ) (258480074003/500000000000 : ℝ) (258480073991/500000000000 : ℝ) (51696014799/100000000000 : ℝ) (51696014799/100000000000 : ℝ) (258480073999/500000000000 : ℝ) (51696014799/100000000000 : ℝ) (258480073999/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2233/16384 : ℝ))) 5 (51696014799/100000000000 : ℝ) (258480073999/500000000000 : ℝ) (51696014799/100000000000 : ℝ) (258480073999/500000000000 : ℝ) (51696014799/100000000000 : ℝ) (258480073999/500000000000 : ℝ) (51696014799/100000000000 : ℝ) (258480073999/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2233/16384 : ℝ))) 6 (51696014799/100000000000 : ℝ) (258480073999/500000000000 : ℝ) (51696014799/100000000000 : ℝ) (258480073999/500000000000 : ℝ) (51696014799/100000000000 : ℝ) (258480073999/500000000000 : ℝ) (51696014799/100000000000 : ℝ) (258480073999/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2233/16384 : ℝ))) 7 (51696014799/100000000000 : ℝ) (258480073999/500000000000 : ℝ) (51696014799/100000000000 : ℝ) (258480073999/500000000000 : ℝ) (51696014799/100000000000 : ℝ) (258480073999/500000000000 : ℝ) (51696014799/100000000000 : ℝ) (258480073999/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2233/16384 : ℝ)) hmem 8 (15473993577/15625000000 : ℝ) (990335588931/1000000000000 : ℝ) (15473993577/15625000000 : ℝ) (990335588931/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2233/16384 : ℝ))) hcmem 8 (51696014799/100000000000 : ℝ) (258480073999/500000000000 : ℝ) (51696014799/100000000000 : ℝ) (258480073999/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2233/16384 : ℝ)) (15473993577/15625000000 : ℝ) (990335588931/1000000000000 : ℝ) (51696014799/100000000000 : ℝ) (258480073999/500000000000 : ℝ) (81996356653/100000000000 : ℝ) (409981783273/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0321_exp_lower
  have heNumeric : (2019009490049/1000000000000 : ℝ)/4 ≤ Real.exp (-10938997142861/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019009490049/1000000000000 : ℝ)/4 ≤ Real.exp ((8931/65536 : ℝ)-(409981783273/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8931/65536 : ℝ) (2233/16384 : ℝ) (409981783273/500000000000 : ℝ) (2019009490049/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0322; no trusted numerical premise.
theorem cover7_leaf0322_exp_radius : (997568910562236863/1000000000000000000 : ℝ) ≤ Real.exp ((-8933/458752 : ℝ)/8) ∧ Real.exp ((-8933/458752 : ℝ)/8) ≤ (15587014227534951/15625000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8933/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0322_exp_lower : (918089026394207379/1000000000000000000 : ℝ) ≤ Real.exp ((-2734749261467/4000000000000 : ℝ)/8) ∧ Real.exp ((-2734749261467/4000000000000 : ℝ)/8) ≤ (45904451319710369/50000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2734749261467/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0322_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019009502289/1000000000000 : ℝ) ≤ 4*Real.exp (2233/16384 : ℝ)*Real.exp (-mu (radius 7 (8933/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (2019009502289/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8933/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0322_exp_radius
  have hrNumeric : (490357983901/500000000000 : ℝ) ≤ Real.exp (-8933/458752 : ℝ) ∧ Real.exp (-8933/458752 : ℝ) ≤ (980715967803/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490357983901/500000000000 : ℝ) ≤ (radius 7 (8933/65536 : ℝ)) ∧ (radius 7 (8933/65536 : ℝ)) ≤ (980715967803/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8933/65536 : ℝ)) (490357983901/500000000000 : ℝ) (980715967803/1000000000000 : ℝ) (39087691411/200000000000 : ℝ) (195438457061/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8933/65536 : ℝ)) (490357983901/500000000000 : ℝ) (980715967803/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8933/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490357983901/500000000000 : ℝ) (980715967803/1000000000000 : ℝ) (990357983901/1000000000000 : ℝ) (495178991951/500000000000 : ℝ) (495155522993/500000000000 : ℝ) (990311045987/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8933/65536 : ℝ)) 1 (990357983901/1000000000000 : ℝ) (495178991951/500000000000 : ℝ) (495155522993/500000000000 : ℝ) (990311045987/1000000000000 : ℝ) (990334514943/1000000000000 : ℝ) (198066902989/200000000000 : ℝ) (198066902933/200000000000 : ℝ) (990334514667/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8933/65536 : ℝ)) 2 (990334514943/1000000000000 : ℝ) (198066902989/200000000000 : ℝ) (198066902933/200000000000 : ℝ) (990334514667/1000000000000 : ℝ) (247583628701/250000000000 : ℝ) (495167257403/500000000000 : ℝ) (990334514803/1000000000000 : ℝ) (495167257403/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8933/65536 : ℝ)) 3 (247583628701/250000000000 : ℝ) (495167257403/500000000000 : ℝ) (990334514803/1000000000000 : ℝ) (495167257403/500000000000 : ℝ) (990334514803/1000000000000 : ℝ) (495167257403/500000000000 : ℝ) (990334514803/1000000000000 : ℝ) (495167257403/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8933/65536 : ℝ)) 4 (990334514803/1000000000000 : ℝ) (495167257403/500000000000 : ℝ) (990334514803/1000000000000 : ℝ) (495167257403/500000000000 : ℝ) (990334514803/1000000000000 : ℝ) (495167257403/500000000000 : ℝ) (990334514803/1000000000000 : ℝ) (495167257403/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8933/65536 : ℝ)) 5 (990334514803/1000000000000 : ℝ) (495167257403/500000000000 : ℝ) (990334514803/1000000000000 : ℝ) (495167257403/500000000000 : ℝ) (990334514803/1000000000000 : ℝ) (495167257403/500000000000 : ℝ) (990334514803/1000000000000 : ℝ) (495167257403/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8933/65536 : ℝ)) 6 (990334514803/1000000000000 : ℝ) (495167257403/500000000000 : ℝ) (990334514803/1000000000000 : ℝ) (495167257403/500000000000 : ℝ) (990334514803/1000000000000 : ℝ) (495167257403/500000000000 : ℝ) (990334514803/1000000000000 : ℝ) (495167257403/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8933/65536 : ℝ)) 7 (990334514803/1000000000000 : ℝ) (495167257403/500000000000 : ℝ) (990334514803/1000000000000 : ℝ) (495167257403/500000000000 : ℝ) (990334514803/1000000000000 : ℝ) (495167257403/500000000000 : ℝ) (990334514803/1000000000000 : ℝ) (495167257403/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8933/65536 : ℝ))) (39087691411/200000000000 : ℝ) (195438457061/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8933/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (39087691411/200000000000 : ℝ) (195438457061/1000000000000 : ℝ) (597719228527/1000000000000 : ℝ) (597719228531/1000000000000 : ℝ) (221042109707/500000000000 : ℝ) (442084219421/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8933/65536 : ℝ))) 1 (597719228527/1000000000000 : ℝ) (597719228531/1000000000000 : ℝ) (221042109707/500000000000 : ℝ) (442084219421/1000000000000 : ℝ) (51990172397/100000000000 : ℝ) (64987715497/125000000000 : ℝ) (514044977187/1000000000000 : ℝ) (257022488597/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8933/65536 : ℝ))) 2 (51990172397/100000000000 : ℝ) (64987715497/125000000000 : ℝ) (514044977187/1000000000000 : ℝ) (257022488597/500000000000 : ℝ) (258486675289/500000000000 : ℝ) (103394670117/200000000000 : ℝ) (516965056689/1000000000000 : ℝ) (64620632087/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8933/65536 : ℝ))) 3 (258486675289/500000000000 : ℝ) (103394670117/200000000000 : ℝ) (516965056689/1000000000000 : ℝ) (64620632087/125000000000 : ℝ) (516969203633/1000000000000 : ℝ) (516969203641/1000000000000 : ℝ) (16155287613/31250000000 : ℝ) (64621150453/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8933/65536 : ℝ))) 4 (516969203633/1000000000000 : ℝ) (516969203641/1000000000000 : ℝ) (16155287613/31250000000 : ℝ) (64621150453/125000000000 : ℝ) (64621150453/125000000000 : ℝ) (516969203633/1000000000000 : ℝ) (64621150453/125000000000 : ℝ) (516969203633/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8933/65536 : ℝ))) 5 (64621150453/125000000000 : ℝ) (516969203633/1000000000000 : ℝ) (64621150453/125000000000 : ℝ) (516969203633/1000000000000 : ℝ) (64621150453/125000000000 : ℝ) (516969203633/1000000000000 : ℝ) (64621150453/125000000000 : ℝ) (516969203633/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8933/65536 : ℝ))) 6 (64621150453/125000000000 : ℝ) (516969203633/1000000000000 : ℝ) (64621150453/125000000000 : ℝ) (516969203633/1000000000000 : ℝ) (64621150453/125000000000 : ℝ) (516969203633/1000000000000 : ℝ) (64621150453/125000000000 : ℝ) (516969203633/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8933/65536 : ℝ))) 7 (64621150453/125000000000 : ℝ) (516969203633/1000000000000 : ℝ) (64621150453/125000000000 : ℝ) (516969203633/1000000000000 : ℝ) (64621150453/125000000000 : ℝ) (516969203633/1000000000000 : ℝ) (64621150453/125000000000 : ℝ) (516969203633/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8933/65536 : ℝ)) hmem 8 (990334514803/1000000000000 : ℝ) (495167257403/500000000000 : ℝ) (990334514803/1000000000000 : ℝ) (495167257403/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8933/65536 : ℝ))) hcmem 8 (64621150453/125000000000 : ℝ) (516969203633/1000000000000 : ℝ) (64621150453/125000000000 : ℝ) (516969203633/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8933/65536 : ℝ)) (990334514803/1000000000000 : ℝ) (495167257403/500000000000 : ℝ) (64621150453/125000000000 : ℝ) (516969203633/1000000000000 : ℝ) (163995763851/200000000000 : ℝ) (819978819273/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0322_exp_lower
  have heNumeric : (2019009502289/1000000000000 : ℝ)/4 ≤ Real.exp (-2734749261467/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019009502289/1000000000000 : ℝ)/4 ≤ Real.exp ((2233/16384 : ℝ)-(819978819273/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2233/16384 : ℝ) (8933/65536 : ℝ) (819978819273/1000000000000 : ℝ) (2019009502289/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0323; no trusted numerical premise.
theorem cover7_leaf0323_exp_radius : (997568638746317081/1000000000000000000 : ℝ) ≤ Real.exp ((-4467/229376 : ℝ)/8) ∧ Real.exp ((-4467/229376 : ℝ)/8) ≤ (498784319373158541/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4467/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0323_exp_lower : (183617805444075983/200000000000000000 : ℝ) ≤ Real.exp ((-10938996930683/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938996930683/16000000000000 : ℝ)/8) ≤ (229522256805094979/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938996930683/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0323_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (252376189603/125000000000 : ℝ) ≤ 4*Real.exp (8933/65536 : ℝ)*Real.exp (-mu (radius 7 (4467/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (252376189603/125000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4467/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0323_exp_radius
  have hrNumeric : (980713830013/1000000000000 : ℝ) ≤ Real.exp (-4467/229376 : ℝ) ∧ Real.exp (-4467/229376 : ℝ) ≤ (490356915007/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980713830013/1000000000000 : ℝ) ≤ (radius 7 (4467/32768 : ℝ)) ∧ (radius 7 (4467/32768 : ℝ)) ≤ (490356915007/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4467/32768 : ℝ)) (980713830013/1000000000000 : ℝ) (490356915007/500000000000 : ℝ) (195449184237/1000000000000 : ℝ) (195449184243/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4467/32768 : ℝ)) (980713830013/1000000000000 : ℝ) (490356915007/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4467/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980713830013/1000000000000 : ℝ) (490356915007/500000000000 : ℝ) (495178457503/500000000000 : ℝ) (990356915007/1000000000000 : ℝ) (990309966633/1000000000000 : ℝ) (495154983317/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4467/32768 : ℝ)) 1 (495178457503/500000000000 : ℝ) (990356915007/1000000000000 : ℝ) (990309966633/1000000000000 : ℝ) (495154983317/500000000000 : ℝ) (990333440819/1000000000000 : ℝ) (990333440821/1000000000000 : ℝ) (990333440541/1000000000000 : ℝ) (990333440543/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4467/32768 : ℝ)) 2 (990333440819/1000000000000 : ℝ) (990333440821/1000000000000 : ℝ) (990333440541/1000000000000 : ℝ) (990333440543/1000000000000 : ℝ) (24758336017/25000000000 : ℝ) (495166720341/500000000000 : ℝ) (990333440679/1000000000000 : ℝ) (495166720341/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4467/32768 : ℝ)) 3 (24758336017/25000000000 : ℝ) (495166720341/500000000000 : ℝ) (990333440679/1000000000000 : ℝ) (495166720341/500000000000 : ℝ) (990333440679/1000000000000 : ℝ) (495166720341/500000000000 : ℝ) (990333440679/1000000000000 : ℝ) (495166720341/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4467/32768 : ℝ)) 4 (990333440679/1000000000000 : ℝ) (495166720341/500000000000 : ℝ) (990333440679/1000000000000 : ℝ) (495166720341/500000000000 : ℝ) (990333440679/1000000000000 : ℝ) (495166720341/500000000000 : ℝ) (990333440679/1000000000000 : ℝ) (495166720341/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4467/32768 : ℝ)) 5 (990333440679/1000000000000 : ℝ) (495166720341/500000000000 : ℝ) (990333440679/1000000000000 : ℝ) (495166720341/500000000000 : ℝ) (990333440679/1000000000000 : ℝ) (495166720341/500000000000 : ℝ) (990333440679/1000000000000 : ℝ) (495166720341/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4467/32768 : ℝ)) 6 (990333440679/1000000000000 : ℝ) (495166720341/500000000000 : ℝ) (990333440679/1000000000000 : ℝ) (495166720341/500000000000 : ℝ) (990333440679/1000000000000 : ℝ) (495166720341/500000000000 : ℝ) (990333440679/1000000000000 : ℝ) (495166720341/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4467/32768 : ℝ)) 7 (990333440679/1000000000000 : ℝ) (495166720341/500000000000 : ℝ) (990333440679/1000000000000 : ℝ) (495166720341/500000000000 : ℝ) (990333440679/1000000000000 : ℝ) (495166720341/500000000000 : ℝ) (990333440679/1000000000000 : ℝ) (495166720341/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4467/32768 : ℝ))) (195449184237/1000000000000 : ℝ) (195449184243/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4467/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (195449184237/1000000000000 : ℝ) (195449184243/1000000000000 : ℝ) (298862296059/500000000000 : ℝ) (298862296061/500000000000 : ℝ) (442096351757/1000000000000 : ℝ) (110524087941/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4467/32768 : ℝ))) 1 (298862296059/500000000000 : ℝ) (298862296061/500000000000 : ℝ) (442096351757/1000000000000 : ℝ) (110524087941/250000000000 : ℝ) (519910471937/1000000000000 : ℝ) (519910471943/1000000000000 : ℝ) (257027168569/500000000000 : ℝ) (102810867429/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4467/32768 : ℝ))) 2 (519910471937/1000000000000 : ℝ) (519910471943/1000000000000 : ℝ) (257027168569/500000000000 : ℝ) (102810867429/200000000000 : ℝ) (516982404537/1000000000000 : ℝ) (8077850071/15625000000 : ℝ) (258487056263/500000000000 : ℝ) (258487056267/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4467/32768 : ℝ))) 3 (516982404537/1000000000000 : ℝ) (8077850071/15625000000 : ℝ) (258487056263/500000000000 : ℝ) (258487056267/500000000000 : ℝ) (516978258531/1000000000000 : ℝ) (516978258539/1000000000000 : ℝ) (258489129257/500000000000 : ℝ) (516978258523/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4467/32768 : ℝ))) 4 (516978258531/1000000000000 : ℝ) (516978258539/1000000000000 : ℝ) (258489129257/500000000000 : ℝ) (516978258523/1000000000000 : ℝ) (258489129261/500000000000 : ℝ) (516978258531/1000000000000 : ℝ) (258489129261/500000000000 : ℝ) (516978258531/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4467/32768 : ℝ))) 5 (258489129261/500000000000 : ℝ) (516978258531/1000000000000 : ℝ) (258489129261/500000000000 : ℝ) (516978258531/1000000000000 : ℝ) (258489129261/500000000000 : ℝ) (516978258531/1000000000000 : ℝ) (258489129261/500000000000 : ℝ) (516978258531/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4467/32768 : ℝ))) 6 (258489129261/500000000000 : ℝ) (516978258531/1000000000000 : ℝ) (258489129261/500000000000 : ℝ) (516978258531/1000000000000 : ℝ) (258489129261/500000000000 : ℝ) (516978258531/1000000000000 : ℝ) (258489129261/500000000000 : ℝ) (516978258531/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4467/32768 : ℝ))) 7 (258489129261/500000000000 : ℝ) (516978258531/1000000000000 : ℝ) (258489129261/500000000000 : ℝ) (516978258531/1000000000000 : ℝ) (258489129261/500000000000 : ℝ) (516978258531/1000000000000 : ℝ) (258489129261/500000000000 : ℝ) (516978258531/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4467/32768 : ℝ)) hmem 8 (990333440679/1000000000000 : ℝ) (495166720341/500000000000 : ℝ) (990333440679/1000000000000 : ℝ) (495166720341/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4467/32768 : ℝ))) hcmem 8 (258489129261/500000000000 : ℝ) (516978258531/1000000000000 : ℝ) (258489129261/500000000000 : ℝ) (516978258531/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4467/32768 : ℝ)) (990333440679/1000000000000 : ℝ) (495166720341/500000000000 : ℝ) (258489129261/500000000000 : ℝ) (516978258531/1000000000000 : ℝ) (163998814169/200000000000 : ℝ) (819994070863/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0323_exp_lower
  have heNumeric : (252376189603/125000000000 : ℝ)/4 ≤ Real.exp (-10938996930683/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (252376189603/125000000000 : ℝ)/4 ≤ Real.exp ((8933/65536 : ℝ)-(819994070863/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8933/65536 : ℝ) (4467/32768 : ℝ) (819994070863/1000000000000 : ℝ) (252376189603/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0324; no trusted numerical premise.
theorem cover7_leaf0324_exp_radius : (997568366930471363/1000000000000000000 : ℝ) ≤ Real.exp ((-8935/458752 : ℝ)/8) ∧ Real.exp ((-8935/458752 : ℝ)/8) ≤ (249392091732617841/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8935/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0324_exp_lower : (918089028177494899/1000000000000000000 : ℝ) ≤ Real.exp ((-5469498398621/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469498398621/8000000000000 : ℝ)/8) ≤ (9180890281774949/10000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469498398621/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0324_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009504766831/500000000000 : ℝ) ≤ 4*Real.exp (4467/32768 : ℝ)*Real.exp (-mu (radius 7 (8935/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (1009504766831/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8935/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0324_exp_radius
  have hrNumeric : (980711692229/1000000000000 : ℝ) ≤ Real.exp (-8935/458752 : ℝ) ∧ Real.exp (-8935/458752 : ℝ) ≤ (98071169223/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980711692229/1000000000000 : ℝ) ≤ (radius 7 (8935/65536 : ℝ)) ∧ (radius 7 (8935/65536 : ℝ)) ≤ (98071169223/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8935/65536 : ℝ)) (980711692229/1000000000000 : ℝ) (98071169223/100000000000 : ℝ) (195459910783/1000000000000 : ℝ) (195459910789/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8935/65536 : ℝ)) (980711692229/1000000000000 : ℝ) (98071169223/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8935/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980711692229/1000000000000 : ℝ) (98071169223/100000000000 : ℝ) (495177923057/500000000000 : ℝ) (198071169223/200000000000 : ℝ) (990308887281/1000000000000 : ℝ) (990308887283/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8935/65536 : ℝ)) 1 (495177923057/500000000000 : ℝ) (198071169223/200000000000 : ℝ) (990308887281/1000000000000 : ℝ) (990308887283/1000000000000 : ℝ) (990332366697/1000000000000 : ℝ) (990332366699/1000000000000 : ℝ) (990332366419/1000000000000 : ℝ) (990332366421/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8935/65536 : ℝ)) 2 (990332366697/1000000000000 : ℝ) (990332366699/1000000000000 : ℝ) (990332366419/1000000000000 : ℝ) (990332366421/1000000000000 : ℝ) (495166183279/500000000000 : ℝ) (6189577291/6250000000 : ℝ) (990332366557/1000000000000 : ℝ) (6189577291/6250000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8935/65536 : ℝ)) 3 (495166183279/500000000000 : ℝ) (6189577291/6250000000 : ℝ) (990332366557/1000000000000 : ℝ) (6189577291/6250000000 : ℝ) (990332366557/1000000000000 : ℝ) (6189577291/6250000000 : ℝ) (990332366557/1000000000000 : ℝ) (6189577291/6250000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8935/65536 : ℝ)) 4 (990332366557/1000000000000 : ℝ) (6189577291/6250000000 : ℝ) (990332366557/1000000000000 : ℝ) (6189577291/6250000000 : ℝ) (990332366557/1000000000000 : ℝ) (6189577291/6250000000 : ℝ) (990332366557/1000000000000 : ℝ) (6189577291/6250000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8935/65536 : ℝ)) 5 (990332366557/1000000000000 : ℝ) (6189577291/6250000000 : ℝ) (990332366557/1000000000000 : ℝ) (6189577291/6250000000 : ℝ) (990332366557/1000000000000 : ℝ) (6189577291/6250000000 : ℝ) (990332366557/1000000000000 : ℝ) (6189577291/6250000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8935/65536 : ℝ)) 6 (990332366557/1000000000000 : ℝ) (6189577291/6250000000 : ℝ) (990332366557/1000000000000 : ℝ) (6189577291/6250000000 : ℝ) (990332366557/1000000000000 : ℝ) (6189577291/6250000000 : ℝ) (990332366557/1000000000000 : ℝ) (6189577291/6250000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8935/65536 : ℝ)) 7 (990332366557/1000000000000 : ℝ) (6189577291/6250000000 : ℝ) (990332366557/1000000000000 : ℝ) (6189577291/6250000000 : ℝ) (990332366557/1000000000000 : ℝ) (6189577291/6250000000 : ℝ) (990332366557/1000000000000 : ℝ) (6189577291/6250000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8935/65536 : ℝ))) (195459910783/1000000000000 : ℝ) (195459910789/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8935/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (195459910783/1000000000000 : ℝ) (195459910789/1000000000000 : ℝ) (597729955391/1000000000000 : ℝ) (119545991079/200000000000 : ℝ) (442108483047/1000000000000 : ℝ) (88421696611/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8935/65536 : ℝ))) 1 (597729955391/1000000000000 : ℝ) (119545991079/200000000000 : ℝ) (442108483047/1000000000000 : ℝ) (88421696611/200000000000 : ℝ) (519919219219/1000000000000 : ℝ) (20796768769/40000000000 : ℝ) (64257962037/125000000000 : ℝ) (514063696303/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8935/65536 : ℝ))) 2 (519919219219/1000000000000 : ℝ) (20796768769/40000000000 : ℝ) (64257962037/125000000000 : ℝ) (514063696303/1000000000000 : ℝ) (516991457757/1000000000000 : ℝ) (129247864441/250000000000 : ℝ) (64622895953/125000000000 : ℝ) (516983167631/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8935/65536 : ℝ))) 3 (516991457757/1000000000000 : ℝ) (129247864441/250000000000 : ℝ) (64622895953/125000000000 : ℝ) (516983167631/1000000000000 : ℝ) (51698731269/100000000000 : ℝ) (258493656349/500000000000 : ℝ) (516987312673/1000000000000 : ℝ) (516987312681/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8935/65536 : ℝ))) 4 (51698731269/100000000000 : ℝ) (258493656349/500000000000 : ℝ) (516987312673/1000000000000 : ℝ) (516987312681/1000000000000 : ℝ) (516987312681/1000000000000 : ℝ) (51698731269/100000000000 : ℝ) (516987312681/1000000000000 : ℝ) (51698731269/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8935/65536 : ℝ))) 5 (516987312681/1000000000000 : ℝ) (51698731269/100000000000 : ℝ) (516987312681/1000000000000 : ℝ) (51698731269/100000000000 : ℝ) (516987312681/1000000000000 : ℝ) (51698731269/100000000000 : ℝ) (516987312681/1000000000000 : ℝ) (51698731269/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8935/65536 : ℝ))) 6 (516987312681/1000000000000 : ℝ) (51698731269/100000000000 : ℝ) (516987312681/1000000000000 : ℝ) (51698731269/100000000000 : ℝ) (516987312681/1000000000000 : ℝ) (51698731269/100000000000 : ℝ) (516987312681/1000000000000 : ℝ) (51698731269/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8935/65536 : ℝ))) 7 (516987312681/1000000000000 : ℝ) (51698731269/100000000000 : ℝ) (516987312681/1000000000000 : ℝ) (51698731269/100000000000 : ℝ) (516987312681/1000000000000 : ℝ) (51698731269/100000000000 : ℝ) (516987312681/1000000000000 : ℝ) (51698731269/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8935/65536 : ℝ)) hmem 8 (990332366557/1000000000000 : ℝ) (6189577291/6250000000 : ℝ) (990332366557/1000000000000 : ℝ) (6189577291/6250000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8935/65536 : ℝ))) hcmem 8 (516987312681/1000000000000 : ℝ) (51698731269/100000000000 : ℝ) (516987312681/1000000000000 : ℝ) (51698731269/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8935/65536 : ℝ)) (990332366557/1000000000000 : ℝ) (6189577291/6250000000 : ℝ) (516987312681/1000000000000 : ℝ) (51698731269/100000000000 : ℝ) (410004660647/500000000000 : ℝ) (25625291291/31250000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0324_exp_lower
  have heNumeric : (1009504766831/500000000000 : ℝ)/4 ≤ Real.exp (-5469498398621/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009504766831/500000000000 : ℝ)/4 ≤ Real.exp ((4467/32768 : ℝ)-(25625291291/31250000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4467/32768 : ℝ) (8935/65536 : ℝ) (25625291291/31250000000 : ℝ) (1009504766831/500000000000 : ℝ) hmu.2 heBox
  · norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover7_leaf0300_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0300_certificate
#check SmaleRate.Proofs.cover7_leaf0301_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0301_certificate
#check SmaleRate.Proofs.cover7_leaf0302_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0302_certificate
#check SmaleRate.Proofs.cover7_leaf0303_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0303_certificate
#check SmaleRate.Proofs.cover7_leaf0304_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0304_certificate
#check SmaleRate.Proofs.cover7_leaf0305_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0305_certificate
#check SmaleRate.Proofs.cover7_leaf0306_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0306_certificate
#check SmaleRate.Proofs.cover7_leaf0307_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0307_certificate
#check SmaleRate.Proofs.cover7_leaf0308_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0308_certificate
#check SmaleRate.Proofs.cover7_leaf0309_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0309_certificate
#check SmaleRate.Proofs.cover7_leaf0310_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0310_certificate
#check SmaleRate.Proofs.cover7_leaf0311_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0311_certificate
#check SmaleRate.Proofs.cover7_leaf0312_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0312_certificate
#check SmaleRate.Proofs.cover7_leaf0313_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0313_certificate
#check SmaleRate.Proofs.cover7_leaf0314_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0314_certificate
#check SmaleRate.Proofs.cover7_leaf0315_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0315_certificate
#check SmaleRate.Proofs.cover7_leaf0316_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0316_certificate
#check SmaleRate.Proofs.cover7_leaf0317_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0317_certificate
#check SmaleRate.Proofs.cover7_leaf0318_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0318_certificate
#check SmaleRate.Proofs.cover7_leaf0319_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0319_certificate
#check SmaleRate.Proofs.cover7_leaf0320_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0320_certificate
#check SmaleRate.Proofs.cover7_leaf0321_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0321_certificate
#check SmaleRate.Proofs.cover7_leaf0322_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0322_certificate
#check SmaleRate.Proofs.cover7_leaf0323_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0323_certificate
#check SmaleRate.Proofs.cover7_leaf0324_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0324_certificate
