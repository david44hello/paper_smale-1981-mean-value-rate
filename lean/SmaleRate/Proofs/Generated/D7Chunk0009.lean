/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.AGMCertificates

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

-- Proposed record cover7_leaf0225; no trusted numerical premise.
theorem cover7_leaf0225_exp_radius : (249398819264621207/250000000000000000 : ℝ) ≤ Real.exp ((-2209/114688 : ℝ)/8) ∧ Real.exp ((-2209/114688 : ℝ)/8) ≤ (997595277058484829/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2209/114688 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0225_exp_lower : (114761196502838001/125000000000000000 : ℝ) ≤ Real.exp ((-10938920974349/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938920974349/16000000000000 : ℝ)/8) ≤ (918089572022704009/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938920974349/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0225_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (31547173463/15625000000 : ℝ) ≤ 4*Real.exp (8835/65536 : ℝ)*Real.exp (-mu (radius 7 (2209/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (31547173463/15625000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2209/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0225_exp_radius
  have hrNumeric : (245230838867/250000000000 : ℝ) ≤ Real.exp (-2209/114688 : ℝ) ∧ Real.exp (-2209/114688 : ℝ) ≤ (980923355469/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (245230838867/250000000000 : ℝ) ≤ (radius 7 (2209/16384 : ℝ)) ∧ (radius 7 (2209/16384 : ℝ)) ≤ (980923355469/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2209/16384 : ℝ)) (245230838867/250000000000 : ℝ) (980923355469/1000000000000 : ℝ) (12149680213/62500000000 : ℝ) (97197441707/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2209/16384 : ℝ)) (245230838867/250000000000 : ℝ) (980923355469/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2209/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (245230838867/250000000000 : ℝ) (980923355469/1000000000000 : ℝ) (495230838867/500000000000 : ℝ) (198092335547/200000000000 : ℝ) (495207874399/500000000000 : ℝ) (990415748799/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2209/16384 : ℝ)) 1 (495230838867/500000000000 : ℝ) (198092335547/200000000000 : ℝ) (495207874399/500000000000 : ℝ) (990415748799/1000000000000 : ℝ) (495219356633/500000000000 : ℝ) (990438713267/1000000000000 : ℝ) (990438712999/1000000000000 : ℝ) (990438713001/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2209/16384 : ℝ)) 2 (495219356633/500000000000 : ℝ) (990438713267/1000000000000 : ℝ) (990438712999/1000000000000 : ℝ) (990438713001/1000000000000 : ℝ) (247609678283/250000000000 : ℝ) (495219356567/500000000000 : ℝ) (247609678283/250000000000 : ℝ) (495219356567/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2209/16384 : ℝ)) 3 (247609678283/250000000000 : ℝ) (495219356567/500000000000 : ℝ) (247609678283/250000000000 : ℝ) (495219356567/500000000000 : ℝ) (247609678283/250000000000 : ℝ) (495219356567/500000000000 : ℝ) (247609678283/250000000000 : ℝ) (495219356567/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2209/16384 : ℝ)) 4 (247609678283/250000000000 : ℝ) (495219356567/500000000000 : ℝ) (247609678283/250000000000 : ℝ) (495219356567/500000000000 : ℝ) (247609678283/250000000000 : ℝ) (495219356567/500000000000 : ℝ) (247609678283/250000000000 : ℝ) (495219356567/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2209/16384 : ℝ)) 5 (247609678283/250000000000 : ℝ) (495219356567/500000000000 : ℝ) (247609678283/250000000000 : ℝ) (495219356567/500000000000 : ℝ) (247609678283/250000000000 : ℝ) (495219356567/500000000000 : ℝ) (247609678283/250000000000 : ℝ) (495219356567/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2209/16384 : ℝ)) 6 (247609678283/250000000000 : ℝ) (495219356567/500000000000 : ℝ) (247609678283/250000000000 : ℝ) (495219356567/500000000000 : ℝ) (247609678283/250000000000 : ℝ) (495219356567/500000000000 : ℝ) (247609678283/250000000000 : ℝ) (495219356567/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2209/16384 : ℝ)) 7 (247609678283/250000000000 : ℝ) (495219356567/500000000000 : ℝ) (247609678283/250000000000 : ℝ) (495219356567/500000000000 : ℝ) (247609678283/250000000000 : ℝ) (495219356567/500000000000 : ℝ) (247609678283/250000000000 : ℝ) (495219356567/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2209/16384 : ℝ))) (12149680213/62500000000 : ℝ) (97197441707/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2209/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (12149680213/62500000000 : ℝ) (97197441707/500000000000 : ℝ) (74649680213/125000000000 : ℝ) (597197441707/1000000000000 : ℝ) (440902351329/1000000000000 : ℝ) (440902351337/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2209/16384 : ℝ))) 1 (74649680213/125000000000 : ℝ) (597197441707/1000000000000 : ℝ) (440902351329/1000000000000 : ℝ) (440902351337/1000000000000 : ℝ) (129762474129/250000000000 : ℝ) (259524948261/500000000000 : ℝ) (102626654677/200000000000 : ℝ) (32070829587/62500000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2209/16384 : ℝ))) 2 (129762474129/250000000000 : ℝ) (259524948261/500000000000 : ℝ) (102626654677/200000000000 : ℝ) (32070829587/62500000000 : ℝ) (10321831699/20000000000 : ℝ) (516091584957/1000000000000 : ℝ) (258041553073/500000000000 : ℝ) (516083106153/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2209/16384 : ℝ))) 3 (10321831699/20000000000 : ℝ) (516091584957/1000000000000 : ℝ) (258041553073/500000000000 : ℝ) (516083106153/1000000000000 : ℝ) (129021836387/250000000000 : ℝ) (103217469111/200000000000 : ℝ) (51608734553/100000000000 : ℝ) (258043672769/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2209/16384 : ℝ))) 4 (129021836387/250000000000 : ℝ) (103217469111/200000000000 : ℝ) (51608734553/100000000000 : ℝ) (258043672769/500000000000 : ℝ) (516087345539/1000000000000 : ℝ) (516087345547/1000000000000 : ℝ) (258043672769/500000000000 : ℝ) (516087345547/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2209/16384 : ℝ))) 5 (516087345539/1000000000000 : ℝ) (516087345547/1000000000000 : ℝ) (258043672769/500000000000 : ℝ) (516087345547/1000000000000 : ℝ) (258043672769/500000000000 : ℝ) (516087345547/1000000000000 : ℝ) (258043672769/500000000000 : ℝ) (516087345547/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2209/16384 : ℝ))) 6 (258043672769/500000000000 : ℝ) (516087345547/1000000000000 : ℝ) (258043672769/500000000000 : ℝ) (516087345547/1000000000000 : ℝ) (258043672769/500000000000 : ℝ) (516087345547/1000000000000 : ℝ) (258043672769/500000000000 : ℝ) (516087345547/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2209/16384 : ℝ))) 7 (258043672769/500000000000 : ℝ) (516087345547/1000000000000 : ℝ) (258043672769/500000000000 : ℝ) (516087345547/1000000000000 : ℝ) (258043672769/500000000000 : ℝ) (516087345547/1000000000000 : ℝ) (258043672769/500000000000 : ℝ) (516087345547/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2209/16384 : ℝ)) hmem 8 (247609678283/250000000000 : ℝ) (495219356567/500000000000 : ℝ) (247609678283/250000000000 : ℝ) (495219356567/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2209/16384 : ℝ))) hcmem 8 (258043672769/500000000000 : ℝ) (516087345547/1000000000000 : ℝ) (258043672769/500000000000 : ℝ) (516087345547/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2209/16384 : ℝ)) (247609678283/250000000000 : ℝ) (495219356567/500000000000 : ℝ) (258043672769/500000000000 : ℝ) (516087345547/1000000000000 : ℝ) (818493962247/1000000000000 : ℝ) (102311745283/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0225_exp_lower
  have heNumeric : (31547173463/15625000000 : ℝ)/4 ≤ Real.exp (-10938920974349/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (31547173463/15625000000 : ℝ)/4 ≤ Real.exp ((8835/65536 : ℝ)-(102311745283/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8835/65536 : ℝ) (2209/16384 : ℝ) (102311745283/125000000000 : ℝ) (31547173463/15625000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0226; no trusted numerical premise.
theorem cover7_leaf0226_exp_radius : (997595005235380747/1000000000000000000 : ℝ) ≤ Real.exp ((-8837/458752 : ℝ)/8) ∧ Real.exp ((-8837/458752 : ℝ)/8) ≤ (249398751308845187/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8837/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0226_exp_lower : (459044780018640709/500000000000000000 : ℝ) ≤ Real.exp ((-2734730661339/4000000000000 : ℝ)/8) ∧ Real.exp ((-2734730661339/4000000000000 : ℝ)/8) ≤ (918089560037281419/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2734730661339/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0226_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019018890769/1000000000000 : ℝ) ≤ 4*Real.exp (2209/16384 : ℝ)*Real.exp (-mu (radius 7 (8837/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (2019018890769/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8837/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0226_exp_radius
  have hrNumeric : (980921217227/1000000000000 : ℝ) ≤ Real.exp (-8837/458752 : ℝ) ∧ Real.exp (-8837/458752 : ℝ) ≤ (245230304307/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980921217227/1000000000000 : ℝ) ≤ (radius 7 (8837/65536 : ℝ)) ∧ (radius 7 (8837/65536 : ℝ)) ≤ (245230304307/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8837/65536 : ℝ)) (980921217227/1000000000000 : ℝ) (245230304307/250000000000 : ℝ) (6075177273/31250000000 : ℝ) (97202836371/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8837/65536 : ℝ)) (980921217227/1000000000000 : ℝ) (245230304307/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8837/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980921217227/1000000000000 : ℝ) (245230304307/250000000000 : ℝ) (990460608613/1000000000000 : ℝ) (495230304307/500000000000 : ℝ) (990414669331/1000000000000 : ℝ) (247603667333/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8837/65536 : ℝ)) 1 (990460608613/1000000000000 : ℝ) (495230304307/500000000000 : ℝ) (990414669331/1000000000000 : ℝ) (247603667333/250000000000 : ℝ) (247609409743/250000000000 : ℝ) (990437638973/1000000000000 : ℝ) (198087527741/200000000000 : ℝ) (990437638707/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8837/65536 : ℝ)) 2 (247609409743/250000000000 : ℝ) (990437638973/1000000000000 : ℝ) (198087527741/200000000000 : ℝ) (990437638707/1000000000000 : ℝ) (495218819419/500000000000 : ℝ) (24760940971/25000000000 : ℝ) (495218819419/500000000000 : ℝ) (24760940971/25000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8837/65536 : ℝ)) 3 (495218819419/500000000000 : ℝ) (24760940971/25000000000 : ℝ) (495218819419/500000000000 : ℝ) (24760940971/25000000000 : ℝ) (495218819419/500000000000 : ℝ) (24760940971/25000000000 : ℝ) (495218819419/500000000000 : ℝ) (24760940971/25000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8837/65536 : ℝ)) 4 (495218819419/500000000000 : ℝ) (24760940971/25000000000 : ℝ) (495218819419/500000000000 : ℝ) (24760940971/25000000000 : ℝ) (495218819419/500000000000 : ℝ) (24760940971/25000000000 : ℝ) (495218819419/500000000000 : ℝ) (24760940971/25000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8837/65536 : ℝ)) 5 (495218819419/500000000000 : ℝ) (24760940971/25000000000 : ℝ) (495218819419/500000000000 : ℝ) (24760940971/25000000000 : ℝ) (495218819419/500000000000 : ℝ) (24760940971/25000000000 : ℝ) (495218819419/500000000000 : ℝ) (24760940971/25000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8837/65536 : ℝ)) 6 (495218819419/500000000000 : ℝ) (24760940971/25000000000 : ℝ) (495218819419/500000000000 : ℝ) (24760940971/25000000000 : ℝ) (495218819419/500000000000 : ℝ) (24760940971/25000000000 : ℝ) (495218819419/500000000000 : ℝ) (24760940971/25000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8837/65536 : ℝ)) 7 (495218819419/500000000000 : ℝ) (24760940971/25000000000 : ℝ) (495218819419/500000000000 : ℝ) (24760940971/25000000000 : ℝ) (495218819419/500000000000 : ℝ) (24760940971/25000000000 : ℝ) (495218819419/500000000000 : ℝ) (24760940971/25000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8837/65536 : ℝ))) (6075177273/31250000000 : ℝ) (97202836371/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8837/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (6075177273/31250000000 : ℝ) (97202836371/500000000000 : ℝ) (37325177273/62500000000 : ℝ) (597202836371/1000000000000 : ℝ) (440914586667/1000000000000 : ℝ) (17636583467/40000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8837/65536 : ℝ))) 1 (37325177273/62500000000 : ℝ) (597202836371/1000000000000 : ℝ) (440914586667/1000000000000 : ℝ) (17636583467/40000000000 : ℝ) (519058711517/1000000000000 : ℝ) (519058711523/1000000000000 : ℝ) (513142710903/1000000000000 : ℝ) (51314271091/100000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8837/65536 : ℝ))) 2 (519058711517/1000000000000 : ℝ) (519058711523/1000000000000 : ℝ) (513142710903/1000000000000 : ℝ) (51314271091/100000000000 : ℝ) (51610071121/100000000000 : ℝ) (516100711217/1000000000000 : ℝ) (516092234339/1000000000000 : ℝ) (516092234347/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8837/65536 : ℝ))) 3 (51610071121/100000000000 : ℝ) (516100711217/1000000000000 : ℝ) (516092234339/1000000000000 : ℝ) (516092234347/1000000000000 : ℝ) (258048236387/500000000000 : ℝ) (258048236391/500000000000 : ℝ) (516096472757/1000000000000 : ℝ) (103219294553/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8837/65536 : ℝ))) 4 (258048236387/500000000000 : ℝ) (258048236391/500000000000 : ℝ) (516096472757/1000000000000 : ℝ) (103219294553/200000000000 : ℝ) (103219294553/200000000000 : ℝ) (258048236387/500000000000 : ℝ) (103219294553/200000000000 : ℝ) (258048236387/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8837/65536 : ℝ))) 5 (103219294553/200000000000 : ℝ) (258048236387/500000000000 : ℝ) (103219294553/200000000000 : ℝ) (258048236387/500000000000 : ℝ) (103219294553/200000000000 : ℝ) (258048236387/500000000000 : ℝ) (103219294553/200000000000 : ℝ) (258048236387/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8837/65536 : ℝ))) 6 (103219294553/200000000000 : ℝ) (258048236387/500000000000 : ℝ) (103219294553/200000000000 : ℝ) (258048236387/500000000000 : ℝ) (103219294553/200000000000 : ℝ) (258048236387/500000000000 : ℝ) (103219294553/200000000000 : ℝ) (258048236387/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8837/65536 : ℝ))) 7 (103219294553/200000000000 : ℝ) (258048236387/500000000000 : ℝ) (103219294553/200000000000 : ℝ) (258048236387/500000000000 : ℝ) (103219294553/200000000000 : ℝ) (258048236387/500000000000 : ℝ) (103219294553/200000000000 : ℝ) (258048236387/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8837/65536 : ℝ)) hmem 8 (495218819419/500000000000 : ℝ) (24760940971/25000000000 : ℝ) (495218819419/500000000000 : ℝ) (24760940971/25000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8837/65536 : ℝ))) hcmem 8 (103219294553/200000000000 : ℝ) (258048236387/500000000000 : ℝ) (103219294553/200000000000 : ℝ) (258048236387/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8837/65536 : ℝ)) (495218819419/500000000000 : ℝ) (24760940971/25000000000 : ℝ) (103219294553/200000000000 : ℝ) (258048236387/500000000000 : ℝ) (409254662737/500000000000 : ℝ) (818509325491/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0226_exp_lower
  have heNumeric : (2019018890769/1000000000000 : ℝ)/4 ≤ Real.exp (-2734730661339/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019018890769/1000000000000 : ℝ)/4 ≤ Real.exp ((2209/16384 : ℝ)-(818509325491/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2209/16384 : ℝ) (8837/65536 : ℝ) (818509325491/1000000000000 : ℝ) (2019018890769/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0227; no trusted numerical premise.
theorem cover7_leaf0227_exp_radius : (249398683353087683/250000000000000000 : ℝ) ≤ Real.exp ((-4419/229376 : ℝ)/8) ∧ Real.exp ((-4419/229376 : ℝ)/8) ≤ (997594733412350733/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4419/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0227_exp_lower : (918089548185900059/1000000000000000000 : ℝ) ≤ Real.exp ((-437556971907/640000000000 : ℝ)/8) ∧ Real.exp ((-437556971907/640000000000 : ℝ)/8) ≤ (45904477409295003/50000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-437556971907/640000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0227_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (403803736453/200000000000 : ℝ) ≤ 4*Real.exp (8837/65536 : ℝ)*Real.exp (-mu (radius 7 (4419/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (403803736453/200000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4419/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0227_exp_radius
  have hrNumeric : (980919078991/1000000000000 : ℝ) ≤ Real.exp (-4419/229376 : ℝ) ∧ Real.exp (-4419/229376 : ℝ) ≤ (61307442437/62500000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980919078991/1000000000000 : ℝ) ≤ (radius 7 (4419/32768 : ℝ)) ∧ (radius 7 (4419/32768 : ℝ)) ≤ (61307442437/62500000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4419/32768 : ℝ)) (980919078991/1000000000000 : ℝ) (61307442437/62500000000 : ℝ) (38883292283/200000000000 : ℝ) (194416461421/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4419/32768 : ℝ)) (980919078991/1000000000000 : ℝ) (61307442437/62500000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4419/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980919078991/1000000000000 : ℝ) (61307442437/62500000000 : ℝ) (198091907899/200000000000 : ℝ) (123807442437/125000000000 : ℝ) (198082717973/200000000000 : ℝ) (990413589867/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4419/32768 : ℝ)) 1 (198091907899/200000000000 : ℝ) (123807442437/125000000000 : ℝ) (198082717973/200000000000 : ℝ) (990413589867/1000000000000 : ℝ) (24760914117/25000000000 : ℝ) (495218282341/500000000000 : ℝ) (990436564413/1000000000000 : ℝ) (15475571319/15625000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4419/32768 : ℝ)) 2 (24760914117/25000000000 : ℝ) (495218282341/500000000000 : ℝ) (990436564413/1000000000000 : ℝ) (15475571319/15625000000 : ℝ) (495218282273/500000000000 : ℝ) (990436564549/1000000000000 : ℝ) (495218282273/500000000000 : ℝ) (990436564549/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4419/32768 : ℝ)) 3 (495218282273/500000000000 : ℝ) (990436564549/1000000000000 : ℝ) (495218282273/500000000000 : ℝ) (990436564549/1000000000000 : ℝ) (495218282273/500000000000 : ℝ) (990436564549/1000000000000 : ℝ) (495218282273/500000000000 : ℝ) (990436564549/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4419/32768 : ℝ)) 4 (495218282273/500000000000 : ℝ) (990436564549/1000000000000 : ℝ) (495218282273/500000000000 : ℝ) (990436564549/1000000000000 : ℝ) (495218282273/500000000000 : ℝ) (990436564549/1000000000000 : ℝ) (495218282273/500000000000 : ℝ) (990436564549/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4419/32768 : ℝ)) 5 (495218282273/500000000000 : ℝ) (990436564549/1000000000000 : ℝ) (495218282273/500000000000 : ℝ) (990436564549/1000000000000 : ℝ) (495218282273/500000000000 : ℝ) (990436564549/1000000000000 : ℝ) (495218282273/500000000000 : ℝ) (990436564549/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4419/32768 : ℝ)) 6 (495218282273/500000000000 : ℝ) (990436564549/1000000000000 : ℝ) (495218282273/500000000000 : ℝ) (990436564549/1000000000000 : ℝ) (495218282273/500000000000 : ℝ) (990436564549/1000000000000 : ℝ) (495218282273/500000000000 : ℝ) (990436564549/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4419/32768 : ℝ)) 7 (495218282273/500000000000 : ℝ) (990436564549/1000000000000 : ℝ) (495218282273/500000000000 : ℝ) (990436564549/1000000000000 : ℝ) (495218282273/500000000000 : ℝ) (990436564549/1000000000000 : ℝ) (495218282273/500000000000 : ℝ) (990436564549/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4419/32768 : ℝ))) (38883292283/200000000000 : ℝ) (194416461421/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4419/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (38883292283/200000000000 : ℝ) (194416461421/1000000000000 : ℝ) (597208230707/1000000000000 : ℝ) (597208230711/1000000000000 : ℝ) (440926820929/1000000000000 : ℝ) (440926820937/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4419/32768 : ℝ))) 1 (597208230707/1000000000000 : ℝ) (597208230711/1000000000000 : ℝ) (440926820929/1000000000000 : ℝ) (440926820937/1000000000000 : ℝ) (259533762909/500000000000 : ℝ) (8110430091/15625000000 : ℝ) (513152147611/1000000000000 : ℝ) (256576073809/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4419/32768 : ℝ))) 2 (259533762909/500000000000 : ℝ) (8110430091/15625000000 : ℝ) (513152147611/1000000000000 : ℝ) (256576073809/500000000000 : ℝ) (258054918357/500000000000 : ℝ) (516109836721/1000000000000 : ℝ) (516101361777/1000000000000 : ℝ) (103220272357/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4419/32768 : ℝ))) 3 (258054918357/500000000000 : ℝ) (516109836721/1000000000000 : ℝ) (516101361777/1000000000000 : ℝ) (103220272357/200000000000 : ℝ) (103221119849/200000000000 : ℝ) (516105599253/1000000000000 : ℝ) (129026399807/250000000000 : ℝ) (129026399809/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4419/32768 : ℝ))) 4 (103221119849/200000000000 : ℝ) (516105599253/1000000000000 : ℝ) (129026399807/250000000000 : ℝ) (129026399809/250000000000 : ℝ) (129026399809/250000000000 : ℝ) (103221119849/200000000000 : ℝ) (129026399809/250000000000 : ℝ) (103221119849/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4419/32768 : ℝ))) 5 (129026399809/250000000000 : ℝ) (103221119849/200000000000 : ℝ) (129026399809/250000000000 : ℝ) (103221119849/200000000000 : ℝ) (129026399809/250000000000 : ℝ) (103221119849/200000000000 : ℝ) (129026399809/250000000000 : ℝ) (103221119849/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4419/32768 : ℝ))) 6 (129026399809/250000000000 : ℝ) (103221119849/200000000000 : ℝ) (129026399809/250000000000 : ℝ) (103221119849/200000000000 : ℝ) (129026399809/250000000000 : ℝ) (103221119849/200000000000 : ℝ) (129026399809/250000000000 : ℝ) (103221119849/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4419/32768 : ℝ))) 7 (129026399809/250000000000 : ℝ) (103221119849/200000000000 : ℝ) (129026399809/250000000000 : ℝ) (103221119849/200000000000 : ℝ) (129026399809/250000000000 : ℝ) (103221119849/200000000000 : ℝ) (129026399809/250000000000 : ℝ) (103221119849/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4419/32768 : ℝ)) hmem 8 (495218282273/500000000000 : ℝ) (990436564549/1000000000000 : ℝ) (495218282273/500000000000 : ℝ) (990436564549/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4419/32768 : ℝ))) hcmem 8 (129026399809/250000000000 : ℝ) (103221119849/200000000000 : ℝ) (129026399809/250000000000 : ℝ) (103221119849/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4419/32768 : ℝ)) (495218282273/500000000000 : ℝ) (990436564549/1000000000000 : ℝ) (129026399809/250000000000 : ℝ) (103221119849/200000000000 : ℝ) (204631171883/250000000000 : ℝ) (16370493751/20000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0227_exp_lower
  have heNumeric : (403803736453/200000000000 : ℝ)/4 ≤ Real.exp (-437556971907/640000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (403803736453/200000000000 : ℝ)/4 ≤ Real.exp ((8837/65536 : ℝ)-(16370493751/20000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8837/65536 : ℝ) (4419/32768 : ℝ) (16370493751/20000000000 : ℝ) (403803736453/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0228; no trusted numerical premise.
theorem cover7_leaf0228_exp_radius : (997594461589394783/1000000000000000000 : ℝ) ≤ Real.exp ((-8839/458752 : ℝ)/8) ∧ Real.exp ((-8839/458752 : ℝ)/8) ≤ (31174826924668587/31250000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8839/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0228_exp_lower : (918089536467986119/1000000000000000000 : ℝ) ≤ Real.exp ((-5469462965693/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469462965693/8000000000000 : ℝ)/8) ≤ (22952238411699653/25000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469462965693/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0228_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (201901847611/100000000000 : ℝ) ≤ 4*Real.exp (4419/32768 : ℝ)*Real.exp (-mu (radius 7 (8839/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (201901847611/100000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8839/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0228_exp_radius
  have hrNumeric : (24522923519/25000000000 : ℝ) ≤ Real.exp (-8839/458752 : ℝ) ∧ Real.exp (-8839/458752 : ℝ) ≤ (980916940761/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (24522923519/25000000000 : ℝ) ≤ (radius 7 (8839/65536 : ℝ)) ∧ (radius 7 (8839/65536 : ℝ)) ≤ (980916940761/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8839/65536 : ℝ)) (24522923519/25000000000 : ℝ) (980916940761/1000000000000 : ℝ) (24303406181/125000000000 : ℝ) (97213624727/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8839/65536 : ℝ)) (24522923519/25000000000 : ℝ) (980916940761/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8839/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (24522923519/25000000000 : ℝ) (980916940761/1000000000000 : ℝ) (49522923519/50000000000 : ℝ) (990458470381/1000000000000 : ℝ) (990412510401/1000000000000 : ℝ) (990412510403/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8839/65536 : ℝ)) 1 (49522923519/50000000000 : ℝ) (990458470381/1000000000000 : ℝ) (990412510401/1000000000000 : ℝ) (990412510403/1000000000000 : ℝ) (99043549039/100000000000 : ℝ) (123804436299/125000000000 : ℝ) (990435490123/1000000000000 : ℝ) (495217745063/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8839/65536 : ℝ)) 2 (99043549039/100000000000 : ℝ) (123804436299/125000000000 : ℝ) (990435490123/1000000000000 : ℝ) (495217745063/500000000000 : ℝ) (61902218141/62500000000 : ℝ) (990435490259/1000000000000 : ℝ) (61902218141/62500000000 : ℝ) (990435490259/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8839/65536 : ℝ)) 3 (61902218141/62500000000 : ℝ) (990435490259/1000000000000 : ℝ) (61902218141/62500000000 : ℝ) (990435490259/1000000000000 : ℝ) (61902218141/62500000000 : ℝ) (990435490259/1000000000000 : ℝ) (61902218141/62500000000 : ℝ) (990435490259/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8839/65536 : ℝ)) 4 (61902218141/62500000000 : ℝ) (990435490259/1000000000000 : ℝ) (61902218141/62500000000 : ℝ) (990435490259/1000000000000 : ℝ) (61902218141/62500000000 : ℝ) (990435490259/1000000000000 : ℝ) (61902218141/62500000000 : ℝ) (990435490259/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8839/65536 : ℝ)) 5 (61902218141/62500000000 : ℝ) (990435490259/1000000000000 : ℝ) (61902218141/62500000000 : ℝ) (990435490259/1000000000000 : ℝ) (61902218141/62500000000 : ℝ) (990435490259/1000000000000 : ℝ) (61902218141/62500000000 : ℝ) (990435490259/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8839/65536 : ℝ)) 6 (61902218141/62500000000 : ℝ) (990435490259/1000000000000 : ℝ) (61902218141/62500000000 : ℝ) (990435490259/1000000000000 : ℝ) (61902218141/62500000000 : ℝ) (990435490259/1000000000000 : ℝ) (61902218141/62500000000 : ℝ) (990435490259/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8839/65536 : ℝ)) 7 (61902218141/62500000000 : ℝ) (990435490259/1000000000000 : ℝ) (61902218141/62500000000 : ℝ) (990435490259/1000000000000 : ℝ) (61902218141/62500000000 : ℝ) (990435490259/1000000000000 : ℝ) (61902218141/62500000000 : ℝ) (990435490259/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8839/65536 : ℝ))) (24303406181/125000000000 : ℝ) (97213624727/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8839/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (24303406181/125000000000 : ℝ) (97213624727/500000000000 : ℝ) (149303406181/250000000000 : ℝ) (597213624727/1000000000000 : ℝ) (440939054119/1000000000000 : ℝ) (440939054127/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8839/65536 : ℝ))) 1 (149303406181/250000000000 : ℝ) (597213624727/1000000000000 : ℝ) (440939054119/1000000000000 : ℝ) (440939054127/1000000000000 : ℝ) (519076339421/1000000000000 : ℝ) (519076339427/1000000000000 : ℝ) (64145197939/125000000000 : ℝ) (513161583519/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8839/65536 : ℝ))) 2 (519076339421/1000000000000 : ℝ) (519076339427/1000000000000 : ℝ) (64145197939/125000000000 : ℝ) (513161583519/1000000000000 : ℝ) (258059480733/500000000000 : ℝ) (516118961473/1000000000000 : ℝ) (258055244231/500000000000 : ℝ) (516110488469/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8839/65536 : ℝ))) 3 (258059480733/500000000000 : ℝ) (516118961473/1000000000000 : ℝ) (258055244231/500000000000 : ℝ) (516110488469/1000000000000 : ℝ) (129028681241/250000000000 : ℝ) (516114724971/1000000000000 : ℝ) (258057362473/500000000000 : ℝ) (258057362477/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8839/65536 : ℝ))) 4 (129028681241/250000000000 : ℝ) (516114724971/1000000000000 : ℝ) (258057362473/500000000000 : ℝ) (258057362477/500000000000 : ℝ) (103222944991/200000000000 : ℝ) (516114724963/1000000000000 : ℝ) (258057362477/500000000000 : ℝ) (516114724963/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8839/65536 : ℝ))) 5 (103222944991/200000000000 : ℝ) (516114724963/1000000000000 : ℝ) (258057362477/500000000000 : ℝ) (516114724963/1000000000000 : ℝ) (258057362477/500000000000 : ℝ) (516114724963/1000000000000 : ℝ) (258057362477/500000000000 : ℝ) (516114724963/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8839/65536 : ℝ))) 6 (258057362477/500000000000 : ℝ) (516114724963/1000000000000 : ℝ) (258057362477/500000000000 : ℝ) (516114724963/1000000000000 : ℝ) (258057362477/500000000000 : ℝ) (516114724963/1000000000000 : ℝ) (258057362477/500000000000 : ℝ) (516114724963/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8839/65536 : ℝ))) 7 (258057362477/500000000000 : ℝ) (516114724963/1000000000000 : ℝ) (258057362477/500000000000 : ℝ) (516114724963/1000000000000 : ℝ) (258057362477/500000000000 : ℝ) (516114724963/1000000000000 : ℝ) (258057362477/500000000000 : ℝ) (516114724963/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8839/65536 : ℝ)) hmem 8 (61902218141/62500000000 : ℝ) (990435490259/1000000000000 : ℝ) (61902218141/62500000000 : ℝ) (990435490259/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8839/65536 : ℝ))) hcmem 8 (258057362477/500000000000 : ℝ) (516114724963/1000000000000 : ℝ) (258057362477/500000000000 : ℝ) (516114724963/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8839/65536 : ℝ)) (61902218141/62500000000 : ℝ) (990435490259/1000000000000 : ℝ) (258057362477/500000000000 : ℝ) (516114724963/1000000000000 : ℝ) (818540048429/1000000000000 : ℝ) (409270024223/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0228_exp_lower
  have heNumeric : (201901847611/100000000000 : ℝ)/4 ≤ Real.exp (-5469462965693/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (201901847611/100000000000 : ℝ)/4 ≤ Real.exp ((4419/32768 : ℝ)-(409270024223/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4419/32768 : ℝ) (8839/65536 : ℝ) (409270024223/500000000000 : ℝ) (201901847611/100000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0229; no trusted numerical premise.
theorem cover7_leaf0229_exp_radius : (997594189766512899/1000000000000000000 : ℝ) ≤ Real.exp ((-1105/57344 : ℝ)/8) ∧ Real.exp ((-1105/57344 : ℝ)/8) ≤ (9975941897665129/10000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1105/57344 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0229_exp_lower : (14345148826290961/15625000000000000 : ℝ) ≤ Real.exp ((-10938927546617/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938927546617/16000000000000 : ℝ)/8) ≤ (183617904976524301/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938927546617/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0229_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009509136143/500000000000 : ℝ) ≤ 4*Real.exp (8839/65536 : ℝ)*Real.exp (-mu (radius 7 (1105/8192 : ℝ))) ∧ (2019/1000 : ℝ) < (1009509136143/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (1105/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0229_exp_radius
  have hrNumeric : (980914802533/1000000000000 : ℝ) ≤ Real.exp (-1105/57344 : ℝ) ∧ Real.exp (-1105/57344 : ℝ) ≤ (490457401267/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980914802533/1000000000000 : ℝ) ≤ (radius 7 (1105/8192 : ℝ)) ∧ (radius 7 (1105/8192 : ℝ)) ≤ (490457401267/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (1105/8192 : ℝ)) (980914802533/1000000000000 : ℝ) (490457401267/500000000000 : ℝ) (97219018419/500000000000 : ℝ) (48609509211/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (1105/8192 : ℝ)) (980914802533/1000000000000 : ℝ) (490457401267/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (1105/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980914802533/1000000000000 : ℝ) (490457401267/500000000000 : ℝ) (495228700633/500000000000 : ℝ) (990457401267/1000000000000 : ℝ) (495205715469/500000000000 : ℝ) (990411430939/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (1105/8192 : ℝ)) 1 (495228700633/500000000000 : ℝ) (990457401267/1000000000000 : ℝ) (495205715469/500000000000 : ℝ) (990411430939/1000000000000 : ℝ) (495217208051/500000000000 : ℝ) (990434416103/1000000000000 : ℝ) (198086883167/200000000000 : ℝ) (990434415837/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (1105/8192 : ℝ)) 2 (495217208051/500000000000 : ℝ) (990434416103/1000000000000 : ℝ) (198086883167/200000000000 : ℝ) (990434415837/1000000000000 : ℝ) (30951075499/31250000000 : ℝ) (99043441597/100000000000 : ℝ) (30951075499/31250000000 : ℝ) (99043441597/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (1105/8192 : ℝ)) 3 (30951075499/31250000000 : ℝ) (99043441597/100000000000 : ℝ) (30951075499/31250000000 : ℝ) (99043441597/100000000000 : ℝ) (30951075499/31250000000 : ℝ) (99043441597/100000000000 : ℝ) (30951075499/31250000000 : ℝ) (99043441597/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (1105/8192 : ℝ)) 4 (30951075499/31250000000 : ℝ) (99043441597/100000000000 : ℝ) (30951075499/31250000000 : ℝ) (99043441597/100000000000 : ℝ) (30951075499/31250000000 : ℝ) (99043441597/100000000000 : ℝ) (30951075499/31250000000 : ℝ) (99043441597/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (1105/8192 : ℝ)) 5 (30951075499/31250000000 : ℝ) (99043441597/100000000000 : ℝ) (30951075499/31250000000 : ℝ) (99043441597/100000000000 : ℝ) (30951075499/31250000000 : ℝ) (99043441597/100000000000 : ℝ) (30951075499/31250000000 : ℝ) (99043441597/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (1105/8192 : ℝ)) 6 (30951075499/31250000000 : ℝ) (99043441597/100000000000 : ℝ) (30951075499/31250000000 : ℝ) (99043441597/100000000000 : ℝ) (30951075499/31250000000 : ℝ) (99043441597/100000000000 : ℝ) (30951075499/31250000000 : ℝ) (99043441597/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (1105/8192 : ℝ)) 7 (30951075499/31250000000 : ℝ) (99043441597/100000000000 : ℝ) (30951075499/31250000000 : ℝ) (99043441597/100000000000 : ℝ) (30951075499/31250000000 : ℝ) (99043441597/100000000000 : ℝ) (30951075499/31250000000 : ℝ) (99043441597/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (1105/8192 : ℝ))) (97219018419/500000000000 : ℝ) (48609509211/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (1105/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (97219018419/500000000000 : ℝ) (48609509211/250000000000 : ℝ) (597219018419/1000000000000 : ℝ) (298609509211/500000000000 : ℝ) (440951286241/1000000000000 : ℝ) (440951286249/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (1105/8192 : ℝ))) 1 (597219018419/1000000000000 : ℝ) (298609509211/500000000000 : ℝ) (440951286241/1000000000000 : ℝ) (440951286249/1000000000000 : ℝ) (51908515233/100000000000 : ℝ) (32442822021/62500000000 : ℝ) (32073188663/62500000000 : ℝ) (102634203723/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (1105/8192 : ℝ))) 2 (51908515233/100000000000 : ℝ) (32442822021/62500000000 : ℝ) (32073188663/62500000000 : ℝ) (102634203723/200000000000 : ℝ) (516128085469/1000000000000 : ℝ) (129032021369/250000000000 : ℝ) (516119614397/1000000000000 : ℝ) (129029903601/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (1105/8192 : ℝ))) 3 (516128085469/1000000000000 : ℝ) (129032021369/250000000000 : ℝ) (516119614397/1000000000000 : ℝ) (129029903601/250000000000 : ℝ) (516123849933/1000000000000 : ℝ) (25806192497/50000000000 : ℝ) (103224769983/200000000000 : ℝ) (516123849923/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (1105/8192 : ℝ))) 4 (516123849933/1000000000000 : ℝ) (25806192497/50000000000 : ℝ) (103224769983/200000000000 : ℝ) (516123849923/1000000000000 : ℝ) (129030962481/250000000000 : ℝ) (129030962483/250000000000 : ℝ) (516123849923/1000000000000 : ℝ) (129030962483/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (1105/8192 : ℝ))) 5 (129030962481/250000000000 : ℝ) (129030962483/250000000000 : ℝ) (516123849923/1000000000000 : ℝ) (129030962483/250000000000 : ℝ) (516123849923/1000000000000 : ℝ) (129030962483/250000000000 : ℝ) (516123849923/1000000000000 : ℝ) (129030962483/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (1105/8192 : ℝ))) 6 (516123849923/1000000000000 : ℝ) (129030962483/250000000000 : ℝ) (516123849923/1000000000000 : ℝ) (129030962483/250000000000 : ℝ) (516123849923/1000000000000 : ℝ) (129030962483/250000000000 : ℝ) (516123849923/1000000000000 : ℝ) (129030962483/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (1105/8192 : ℝ))) 7 (516123849923/1000000000000 : ℝ) (129030962483/250000000000 : ℝ) (516123849923/1000000000000 : ℝ) (129030962483/250000000000 : ℝ) (516123849923/1000000000000 : ℝ) (129030962483/250000000000 : ℝ) (516123849923/1000000000000 : ℝ) (129030962483/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (1105/8192 : ℝ)) hmem 8 (30951075499/31250000000 : ℝ) (99043441597/100000000000 : ℝ) (30951075499/31250000000 : ℝ) (99043441597/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (1105/8192 : ℝ))) hcmem 8 (516123849923/1000000000000 : ℝ) (129030962483/250000000000 : ℝ) (516123849923/1000000000000 : ℝ) (129030962483/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (1105/8192 : ℝ)) (30951075499/31250000000 : ℝ) (99043441597/100000000000 : ℝ) (516123849923/1000000000000 : ℝ) (129030962483/250000000000 : ℝ) (81855540817/100000000000 : ℝ) (818555408187/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0229_exp_lower
  have heNumeric : (1009509136143/500000000000 : ℝ)/4 ≤ Real.exp (-10938927546617/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009509136143/500000000000 : ℝ)/4 ≤ Real.exp ((8839/65536 : ℝ)-(818555408187/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8839/65536 : ℝ) (1105/8192 : ℝ) (818555408187/1000000000000 : ℝ) (1009509136143/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0230; no trusted numerical premise.
theorem cover7_leaf0230_exp_radius : (498796958971852541/500000000000000000 : ℝ) ≤ Real.exp ((-1263/65536 : ℝ)/8) ∧ Real.exp ((-1263/65536 : ℝ)/8) ≤ (997593917943705083/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1263/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0230_exp_lower : (459044756715132627/500000000000000000 : ℝ) ≤ Real.exp ((-1367366142913/2000000000000 : ℝ)/8) ∧ Real.exp ((-1367366142913/2000000000000 : ℝ)/8) ≤ (183617902686053051/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1367366142913/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0230_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009509035401/500000000000 : ℝ) ≤ 4*Real.exp (1105/8192 : ℝ)*Real.exp (-mu (radius 7 (8841/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (1009509035401/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8841/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0230_exp_radius
  have hrNumeric : (98091266431/100000000000 : ℝ) ≤ Real.exp (-1263/65536 : ℝ) ∧ Real.exp (-1263/65536 : ℝ) ≤ (980912664311/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (98091266431/100000000000 : ℝ) ≤ (radius 7 (8841/65536 : ℝ)) ∧ (radius 7 (8841/65536 : ℝ)) ≤ (980912664311/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8841/65536 : ℝ)) (98091266431/100000000000 : ℝ) (980912664311/1000000000000 : ℝ) (97224411793/500000000000 : ℝ) (24306102949/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8841/65536 : ℝ)) (98091266431/100000000000 : ℝ) (980912664311/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8841/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (98091266431/100000000000 : ℝ) (980912664311/1000000000000 : ℝ) (198091266431/200000000000 : ℝ) (247614083039/250000000000 : ℝ) (39616414059/40000000000 : ℝ) (990410351477/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8841/65536 : ℝ)) 1 (198091266431/200000000000 : ℝ) (247614083039/250000000000 : ℝ) (39616414059/40000000000 : ℝ) (990410351477/1000000000000 : ℝ) (198086668363/200000000000 : ℝ) (990433341817/1000000000000 : ℝ) (247608335387/250000000000 : ℝ) (19808666831/20000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8841/65536 : ℝ)) 2 (198086668363/200000000000 : ℝ) (990433341817/1000000000000 : ℝ) (247608335387/250000000000 : ℝ) (19808666831/20000000000 : ℝ) (990433341681/1000000000000 : ℝ) (247608335421/250000000000 : ℝ) (990433341681/1000000000000 : ℝ) (247608335421/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8841/65536 : ℝ)) 3 (990433341681/1000000000000 : ℝ) (247608335421/250000000000 : ℝ) (990433341681/1000000000000 : ℝ) (247608335421/250000000000 : ℝ) (990433341681/1000000000000 : ℝ) (247608335421/250000000000 : ℝ) (990433341681/1000000000000 : ℝ) (247608335421/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8841/65536 : ℝ)) 4 (990433341681/1000000000000 : ℝ) (247608335421/250000000000 : ℝ) (990433341681/1000000000000 : ℝ) (247608335421/250000000000 : ℝ) (990433341681/1000000000000 : ℝ) (247608335421/250000000000 : ℝ) (990433341681/1000000000000 : ℝ) (247608335421/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8841/65536 : ℝ)) 5 (990433341681/1000000000000 : ℝ) (247608335421/250000000000 : ℝ) (990433341681/1000000000000 : ℝ) (247608335421/250000000000 : ℝ) (990433341681/1000000000000 : ℝ) (247608335421/250000000000 : ℝ) (990433341681/1000000000000 : ℝ) (247608335421/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8841/65536 : ℝ)) 6 (990433341681/1000000000000 : ℝ) (247608335421/250000000000 : ℝ) (990433341681/1000000000000 : ℝ) (247608335421/250000000000 : ℝ) (990433341681/1000000000000 : ℝ) (247608335421/250000000000 : ℝ) (990433341681/1000000000000 : ℝ) (247608335421/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8841/65536 : ℝ)) 7 (990433341681/1000000000000 : ℝ) (247608335421/250000000000 : ℝ) (990433341681/1000000000000 : ℝ) (247608335421/250000000000 : ℝ) (990433341681/1000000000000 : ℝ) (247608335421/250000000000 : ℝ) (990433341681/1000000000000 : ℝ) (247608335421/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8841/65536 : ℝ))) (97224411793/500000000000 : ℝ) (24306102949/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8841/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (97224411793/500000000000 : ℝ) (24306102949/125000000000 : ℝ) (597224411793/1000000000000 : ℝ) (149306102949/250000000000 : ℝ) (88192703459/200000000000 : ℝ) (440963517303/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8841/65536 : ℝ))) 1 (597224411793/1000000000000 : ℝ) (149306102949/250000000000 : ℝ) (88192703459/200000000000 : ℝ) (440963517303/1000000000000 : ℝ) (2027710799/3906250000 : ℝ) (10381879291/20000000000 : ℝ) (5131804529/10000000000 : ℝ) (256590226453/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8841/65536 : ℝ))) 2 (2027710799/3906250000 : ℝ) (10381879291/20000000000 : ℝ) (5131804529/10000000000 : ℝ) (256590226453/500000000000 : ℝ) (258068604361/500000000000 : ℝ) (64517151091/125000000000 : ℝ) (516128739581/1000000000000 : ℝ) (129032184897/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8841/65536 : ℝ))) 3 (258068604361/500000000000 : ℝ) (64517151091/125000000000 : ℝ) (516128739581/1000000000000 : ℝ) (129032184897/250000000000 : ℝ) (516132974151/1000000000000 : ℝ) (258066487079/500000000000 : ℝ) (258066487067/500000000000 : ℝ) (516132974141/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8841/65536 : ℝ))) 4 (516132974151/1000000000000 : ℝ) (258066487079/500000000000 : ℝ) (258066487067/500000000000 : ℝ) (516132974141/1000000000000 : ℝ) (258066487071/500000000000 : ℝ) (10322659483/20000000000 : ℝ) (258066487071/500000000000 : ℝ) (10322659483/20000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8841/65536 : ℝ))) 5 (258066487071/500000000000 : ℝ) (10322659483/20000000000 : ℝ) (258066487071/500000000000 : ℝ) (10322659483/20000000000 : ℝ) (258066487071/500000000000 : ℝ) (10322659483/20000000000 : ℝ) (258066487071/500000000000 : ℝ) (10322659483/20000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8841/65536 : ℝ))) 6 (258066487071/500000000000 : ℝ) (10322659483/20000000000 : ℝ) (258066487071/500000000000 : ℝ) (10322659483/20000000000 : ℝ) (258066487071/500000000000 : ℝ) (10322659483/20000000000 : ℝ) (258066487071/500000000000 : ℝ) (10322659483/20000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8841/65536 : ℝ))) 7 (258066487071/500000000000 : ℝ) (10322659483/20000000000 : ℝ) (258066487071/500000000000 : ℝ) (10322659483/20000000000 : ℝ) (258066487071/500000000000 : ℝ) (10322659483/20000000000 : ℝ) (258066487071/500000000000 : ℝ) (10322659483/20000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8841/65536 : ℝ)) hmem 8 (990433341681/1000000000000 : ℝ) (247608335421/250000000000 : ℝ) (990433341681/1000000000000 : ℝ) (247608335421/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8841/65536 : ℝ))) hcmem 8 (258066487071/500000000000 : ℝ) (10322659483/20000000000 : ℝ) (258066487071/500000000000 : ℝ) (10322659483/20000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8841/65536 : ℝ)) (990433341681/1000000000000 : ℝ) (247608335421/250000000000 : ℝ) (258066487071/500000000000 : ℝ) (10322659483/20000000000 : ℝ) (25580336461/31250000000 : ℝ) (818570766769/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0230_exp_lower
  have heNumeric : (1009509035401/500000000000 : ℝ)/4 ≤ Real.exp (-1367366142913/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009509035401/500000000000 : ℝ)/4 ≤ Real.exp ((1105/8192 : ℝ)-(818570766769/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (1105/8192 : ℝ) (8841/65536 : ℝ) (818570766769/1000000000000 : ℝ) (1009509035401/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0231; no trusted numerical premise.
theorem cover7_leaf0231_exp_radius : (99759364612097133/100000000000000000 : ℝ) ≤ Real.exp ((-4421/229376 : ℝ)/8) ∧ Real.exp ((-4421/229376 : ℝ)/8) ≤ (997593646120971331/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4421/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0231_exp_lower : (918089502111950213/1000000000000000000 : ℝ) ≤ Real.exp ((-10938930721303/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938930721303/16000000000000 : ℝ)/8) ≤ (459044751055975107/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938930721303/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0231_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019017871677/1000000000000 : ℝ) ≤ 4*Real.exp (8841/65536 : ℝ)*Real.exp (-mu (radius 7 (4421/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (2019017871677/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4421/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0231_exp_radius
  have hrNumeric : (980910526093/1000000000000 : ℝ) ≤ Real.exp (-4421/229376 : ℝ) ∧ Real.exp (-4421/229376 : ℝ) ≤ (490455263047/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980910526093/1000000000000 : ℝ) ≤ (radius 7 (4421/32768 : ℝ)) ∧ (radius 7 (4421/32768 : ℝ)) ≤ (490455263047/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4421/32768 : ℝ)) (980910526093/1000000000000 : ℝ) (490455263047/500000000000 : ℝ) (97229804841/500000000000 : ℝ) (24307451211/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4421/32768 : ℝ)) (980910526093/1000000000000 : ℝ) (490455263047/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4421/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980910526093/1000000000000 : ℝ) (490455263047/500000000000 : ℝ) (495227631523/500000000000 : ℝ) (990455263047/1000000000000 : ℝ) (495204636007/500000000000 : ℝ) (61900579501/62500000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4421/32768 : ℝ)) 1 (495227631523/500000000000 : ℝ) (990455263047/1000000000000 : ℝ) (495204636007/500000000000 : ℝ) (61900579501/62500000000 : ℝ) (99043226753/100000000000 : ℝ) (247608066883/250000000000 : ℝ) (990432267263/1000000000000 : ℝ) (198086453453/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4421/32768 : ℝ)) 2 (99043226753/100000000000 : ℝ) (247608066883/250000000000 : ℝ) (990432267263/1000000000000 : ℝ) (198086453453/200000000000 : ℝ) (247608066849/250000000000 : ℝ) (990432267399/1000000000000 : ℝ) (247608066849/250000000000 : ℝ) (990432267399/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4421/32768 : ℝ)) 3 (247608066849/250000000000 : ℝ) (990432267399/1000000000000 : ℝ) (247608066849/250000000000 : ℝ) (990432267399/1000000000000 : ℝ) (247608066849/250000000000 : ℝ) (990432267399/1000000000000 : ℝ) (247608066849/250000000000 : ℝ) (990432267399/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4421/32768 : ℝ)) 4 (247608066849/250000000000 : ℝ) (990432267399/1000000000000 : ℝ) (247608066849/250000000000 : ℝ) (990432267399/1000000000000 : ℝ) (247608066849/250000000000 : ℝ) (990432267399/1000000000000 : ℝ) (247608066849/250000000000 : ℝ) (990432267399/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4421/32768 : ℝ)) 5 (247608066849/250000000000 : ℝ) (990432267399/1000000000000 : ℝ) (247608066849/250000000000 : ℝ) (990432267399/1000000000000 : ℝ) (247608066849/250000000000 : ℝ) (990432267399/1000000000000 : ℝ) (247608066849/250000000000 : ℝ) (990432267399/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4421/32768 : ℝ)) 6 (247608066849/250000000000 : ℝ) (990432267399/1000000000000 : ℝ) (247608066849/250000000000 : ℝ) (990432267399/1000000000000 : ℝ) (247608066849/250000000000 : ℝ) (990432267399/1000000000000 : ℝ) (247608066849/250000000000 : ℝ) (990432267399/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4421/32768 : ℝ)) 7 (247608066849/250000000000 : ℝ) (990432267399/1000000000000 : ℝ) (247608066849/250000000000 : ℝ) (990432267399/1000000000000 : ℝ) (247608066849/250000000000 : ℝ) (990432267399/1000000000000 : ℝ) (247608066849/250000000000 : ℝ) (990432267399/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4421/32768 : ℝ))) (97229804841/500000000000 : ℝ) (24307451211/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4421/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (97229804841/500000000000 : ℝ) (24307451211/125000000000 : ℝ) (597229804841/1000000000000 : ℝ) (149307451211/250000000000 : ℝ) (440975747271/1000000000000 : ℝ) (440975747279/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4421/32768 : ℝ))) 1 (597229804841/1000000000000 : ℝ) (149307451211/250000000000 : ℝ) (440975747271/1000000000000 : ℝ) (440975747279/1000000000000 : ℝ) (64887847007/125000000000 : ℝ) (259551388031/500000000000 : ℝ) (513189886379/1000000000000 : ℝ) (256594943193/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4421/32768 : ℝ))) 2 (64887847007/125000000000 : ℝ) (259551388031/500000000000 : ℝ) (513189886379/1000000000000 : ℝ) (256594943193/500000000000 : ℝ) (516146331217/1000000000000 : ℝ) (64518291403/125000000000 : ℝ) (64517233001/125000000000 : ℝ) (103227572803/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4421/32768 : ℝ))) 3 (516146331217/1000000000000 : ℝ) (64518291403/125000000000 : ℝ) (64517233001/125000000000 : ℝ) (103227572803/200000000000 : ℝ) (129035524403/250000000000 : ℝ) (25807104881/50000000000 : ℝ) (103228419519/200000000000 : ℝ) (516142097603/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4421/32768 : ℝ))) 4 (129035524403/250000000000 : ℝ) (25807104881/50000000000 : ℝ) (103228419519/200000000000 : ℝ) (516142097603/1000000000000 : ℝ) (516142097603/1000000000000 : ℝ) (129035524403/250000000000 : ℝ) (516142097603/1000000000000 : ℝ) (129035524403/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4421/32768 : ℝ))) 5 (516142097603/1000000000000 : ℝ) (129035524403/250000000000 : ℝ) (516142097603/1000000000000 : ℝ) (129035524403/250000000000 : ℝ) (516142097603/1000000000000 : ℝ) (129035524403/250000000000 : ℝ) (516142097603/1000000000000 : ℝ) (129035524403/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4421/32768 : ℝ))) 6 (516142097603/1000000000000 : ℝ) (129035524403/250000000000 : ℝ) (516142097603/1000000000000 : ℝ) (129035524403/250000000000 : ℝ) (516142097603/1000000000000 : ℝ) (129035524403/250000000000 : ℝ) (516142097603/1000000000000 : ℝ) (129035524403/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4421/32768 : ℝ))) 7 (516142097603/1000000000000 : ℝ) (129035524403/250000000000 : ℝ) (516142097603/1000000000000 : ℝ) (129035524403/250000000000 : ℝ) (516142097603/1000000000000 : ℝ) (129035524403/250000000000 : ℝ) (516142097603/1000000000000 : ℝ) (129035524403/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4421/32768 : ℝ)) hmem 8 (247608066849/250000000000 : ℝ) (990432267399/1000000000000 : ℝ) (247608066849/250000000000 : ℝ) (990432267399/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4421/32768 : ℝ))) hcmem 8 (516142097603/1000000000000 : ℝ) (129035524403/250000000000 : ℝ) (516142097603/1000000000000 : ℝ) (129035524403/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4421/32768 : ℝ)) (247608066849/250000000000 : ℝ) (990432267399/1000000000000 : ℝ) (516142097603/1000000000000 : ℝ) (129035524403/250000000000 : ℝ) (163717224833/200000000000 : ℝ) (818586124183/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0231_exp_lower
  have heNumeric : (2019017871677/1000000000000 : ℝ)/4 ≤ Real.exp (-10938930721303/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019017871677/1000000000000 : ℝ)/4 ≤ Real.exp ((8841/65536 : ℝ)-(818586124183/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8841/65536 : ℝ) (4421/32768 : ℝ) (818586124183/1000000000000 : ℝ) (2019017871677/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0232; no trusted numerical premise.
theorem cover7_leaf0232_exp_radius : (249398343574577911/250000000000000000 : ℝ) ≤ Real.exp ((-8843/458752 : ℝ)/8) ∧ Real.exp ((-8843/458752 : ℝ)/8) ≤ (199518674859662329/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8843/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0232_exp_lower : (229522372731574811/250000000000000000 : ℝ) ≤ Real.exp ((-5469466140403/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469466140403/8000000000000 : ℝ)/8) ≤ (183617898185259849/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469466140403/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0232_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (403803534977/200000000000 : ℝ) ≤ 4*Real.exp (4421/32768 : ℝ)*Real.exp (-mu (radius 7 (8843/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (403803534977/200000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8843/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0232_exp_radius
  have hrNumeric : (24522709697/25000000000 : ℝ) ≤ Real.exp (-8843/458752 : ℝ) ∧ Real.exp (-8843/458752 : ℝ) ≤ (980908387881/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (24522709697/25000000000 : ℝ) ≤ (radius 7 (8843/65536 : ℝ)) ∧ (radius 7 (8843/65536 : ℝ)) ≤ (980908387881/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8843/65536 : ℝ)) (24522709697/25000000000 : ℝ) (980908387881/1000000000000 : ℝ) (759649981/3906250000 : ℝ) (97235197571/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8843/65536 : ℝ)) (24522709697/25000000000 : ℝ) (980908387881/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8843/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (24522709697/25000000000 : ℝ) (980908387881/1000000000000 : ℝ) (49522709697/50000000000 : ℝ) (990454193941/1000000000000 : ℝ) (495204096277/500000000000 : ℝ) (247602048139/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8843/65536 : ℝ)) 1 (49522709697/50000000000 : ℝ) (990454193941/1000000000000 : ℝ) (495204096277/500000000000 : ℝ) (247602048139/250000000000 : ℝ) (990431193247/1000000000000 : ℝ) (990431193249/1000000000000 : ℝ) (990431192979/1000000000000 : ℝ) (495215596491/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8843/65536 : ℝ)) 2 (990431193247/1000000000000 : ℝ) (990431193249/1000000000000 : ℝ) (990431192979/1000000000000 : ℝ) (495215596491/500000000000 : ℝ) (990431193113/1000000000000 : ℝ) (247607798279/250000000000 : ℝ) (123803899139/125000000000 : ℝ) (247607798279/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8843/65536 : ℝ)) 3 (990431193113/1000000000000 : ℝ) (247607798279/250000000000 : ℝ) (123803899139/125000000000 : ℝ) (247607798279/250000000000 : ℝ) (123803899139/125000000000 : ℝ) (247607798279/250000000000 : ℝ) (123803899139/125000000000 : ℝ) (247607798279/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8843/65536 : ℝ)) 4 (123803899139/125000000000 : ℝ) (247607798279/250000000000 : ℝ) (123803899139/125000000000 : ℝ) (247607798279/250000000000 : ℝ) (123803899139/125000000000 : ℝ) (247607798279/250000000000 : ℝ) (123803899139/125000000000 : ℝ) (247607798279/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8843/65536 : ℝ)) 5 (123803899139/125000000000 : ℝ) (247607798279/250000000000 : ℝ) (123803899139/125000000000 : ℝ) (247607798279/250000000000 : ℝ) (123803899139/125000000000 : ℝ) (247607798279/250000000000 : ℝ) (123803899139/125000000000 : ℝ) (247607798279/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8843/65536 : ℝ)) 6 (123803899139/125000000000 : ℝ) (247607798279/250000000000 : ℝ) (123803899139/125000000000 : ℝ) (247607798279/250000000000 : ℝ) (123803899139/125000000000 : ℝ) (247607798279/250000000000 : ℝ) (123803899139/125000000000 : ℝ) (247607798279/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8843/65536 : ℝ)) 7 (123803899139/125000000000 : ℝ) (247607798279/250000000000 : ℝ) (123803899139/125000000000 : ℝ) (247607798279/250000000000 : ℝ) (123803899139/125000000000 : ℝ) (247607798279/250000000000 : ℝ) (123803899139/125000000000 : ℝ) (247607798279/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8843/65536 : ℝ))) (759649981/3906250000 : ℝ) (97235197571/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8843/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (759649981/3906250000 : ℝ) (97235197571/500000000000 : ℝ) (4665899981/7812500000 : ℝ) (597235197571/1000000000000 : ℝ) (22049398809/50000000000 : ℝ) (110246994047/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8843/65536 : ℝ))) 1 (4665899981/7812500000 : ℝ) (597235197571/1000000000000 : ℝ) (22049398809/50000000000 : ℝ) (110246994047/250000000000 : ℝ) (259555793437/500000000000 : ℝ) (1622223709/3125000000 : ℝ) (102639863811/200000000000 : ℝ) (256599659531/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8843/65536 : ℝ))) 2 (259555793437/500000000000 : ℝ) (1622223709/3125000000 : ℝ) (102639863811/200000000000 : ℝ) (256599659531/500000000000 : ℝ) (129038863241/250000000000 : ℝ) (516155452971/1000000000000 : ℝ) (103229397537/200000000000 : ℝ) (516146987693/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8843/65536 : ℝ))) 3 (129038863241/250000000000 : ℝ) (516155452971/1000000000000 : ℝ) (103229397537/200000000000 : ℝ) (516146987693/1000000000000 : ℝ) (129037805081/250000000000 : ℝ) (129037805083/250000000000 : ℝ) (516151220307/1000000000000 : ℝ) (103230244063/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8843/65536 : ℝ))) 4 (129037805081/250000000000 : ℝ) (129037805083/250000000000 : ℝ) (516151220307/1000000000000 : ℝ) (103230244063/200000000000 : ℝ) (103230244063/200000000000 : ℝ) (129037805081/250000000000 : ℝ) (103230244063/200000000000 : ℝ) (129037805081/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8843/65536 : ℝ))) 5 (103230244063/200000000000 : ℝ) (129037805081/250000000000 : ℝ) (103230244063/200000000000 : ℝ) (129037805081/250000000000 : ℝ) (103230244063/200000000000 : ℝ) (129037805081/250000000000 : ℝ) (103230244063/200000000000 : ℝ) (129037805081/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8843/65536 : ℝ))) 6 (103230244063/200000000000 : ℝ) (129037805081/250000000000 : ℝ) (103230244063/200000000000 : ℝ) (129037805081/250000000000 : ℝ) (103230244063/200000000000 : ℝ) (129037805081/250000000000 : ℝ) (103230244063/200000000000 : ℝ) (129037805081/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8843/65536 : ℝ))) 7 (103230244063/200000000000 : ℝ) (129037805081/250000000000 : ℝ) (103230244063/200000000000 : ℝ) (129037805081/250000000000 : ℝ) (103230244063/200000000000 : ℝ) (129037805081/250000000000 : ℝ) (103230244063/200000000000 : ℝ) (129037805081/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8843/65536 : ℝ)) hmem 8 (123803899139/125000000000 : ℝ) (247607798279/250000000000 : ℝ) (123803899139/125000000000 : ℝ) (247607798279/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8843/65536 : ℝ))) hcmem 8 (103230244063/200000000000 : ℝ) (129037805081/250000000000 : ℝ) (103230244063/200000000000 : ℝ) (129037805081/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8843/65536 : ℝ)) (123803899139/125000000000 : ℝ) (247607798279/250000000000 : ℝ) (103230244063/200000000000 : ℝ) (129037805081/250000000000 : ℝ) (409300740211/500000000000 : ℝ) (818601480441/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0232_exp_lower
  have heNumeric : (403803534977/200000000000 : ℝ)/4 ≤ Real.exp (-5469466140403/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (403803534977/200000000000 : ℝ)/4 ≤ Real.exp ((4421/32768 : ℝ)-(818601480441/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4421/32768 : ℝ) (8843/65536 : ℝ) (818601480441/1000000000000 : ℝ) (403803534977/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0233; no trusted numerical premise.
theorem cover7_leaf0233_exp_radius : (124699137809465753/125000000000000000 : ℝ) ≤ Real.exp ((-2211/114688 : ℝ)/8) ∧ Real.exp ((-2211/114688 : ℝ)/8) ≤ (39903724099029041/40000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2211/114688 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0233_exp_lower : (91808947987423043/100000000000000000 : ℝ) ≤ Real.exp ((-2187786764337/3200000000000 : ℝ)/8) ∧ Real.exp ((-2187786764337/3200000000000 : ℝ)/8) ≤ (918089479874230431/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2187786764337/3200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0233_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (504754370111/250000000000 : ℝ) ≤ 4*Real.exp (8843/65536 : ℝ)*Real.exp (-mu (radius 7 (2211/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (504754370111/250000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2211/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0233_exp_radius
  have hrNumeric : (122613281209/125000000000 : ℝ) ≤ Real.exp (-2211/114688 : ℝ) ∧ Real.exp (-2211/114688 : ℝ) ≤ (980906249673/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (122613281209/125000000000 : ℝ) ≤ (radius 7 (2211/16384 : ℝ)) ∧ (radius 7 (2211/16384 : ℝ)) ≤ (980906249673/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2211/16384 : ℝ)) (122613281209/125000000000 : ℝ) (980906249673/1000000000000 : ℝ) (24310147493/125000000000 : ℝ) (3889623599/20000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2211/16384 : ℝ)) (122613281209/125000000000 : ℝ) (980906249673/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2211/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (122613281209/125000000000 : ℝ) (980906249673/1000000000000 : ℝ) (247613281209/250000000000 : ℝ) (990453124837/1000000000000 : ℝ) (123800889137/125000000000 : ℝ) (990407113097/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2211/16384 : ℝ)) 1 (247613281209/250000000000 : ℝ) (990453124837/1000000000000 : ℝ) (123800889137/125000000000 : ℝ) (990407113097/1000000000000 : ℝ) (495215059483/500000000000 : ℝ) (990430118967/1000000000000 : ℝ) (495215059349/500000000000 : ℝ) (9904301187/10000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2211/16384 : ℝ)) 2 (495215059483/500000000000 : ℝ) (990430118967/1000000000000 : ℝ) (495215059349/500000000000 : ℝ) (9904301187/10000000000 : ℝ) (61901882427/62500000000 : ℝ) (495215059417/500000000000 : ℝ) (990430118831/1000000000000 : ℝ) (495215059417/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2211/16384 : ℝ)) 3 (61901882427/62500000000 : ℝ) (495215059417/500000000000 : ℝ) (990430118831/1000000000000 : ℝ) (495215059417/500000000000 : ℝ) (990430118831/1000000000000 : ℝ) (495215059417/500000000000 : ℝ) (990430118831/1000000000000 : ℝ) (495215059417/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2211/16384 : ℝ)) 4 (990430118831/1000000000000 : ℝ) (495215059417/500000000000 : ℝ) (990430118831/1000000000000 : ℝ) (495215059417/500000000000 : ℝ) (990430118831/1000000000000 : ℝ) (495215059417/500000000000 : ℝ) (990430118831/1000000000000 : ℝ) (495215059417/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2211/16384 : ℝ)) 5 (990430118831/1000000000000 : ℝ) (495215059417/500000000000 : ℝ) (990430118831/1000000000000 : ℝ) (495215059417/500000000000 : ℝ) (990430118831/1000000000000 : ℝ) (495215059417/500000000000 : ℝ) (990430118831/1000000000000 : ℝ) (495215059417/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2211/16384 : ℝ)) 6 (990430118831/1000000000000 : ℝ) (495215059417/500000000000 : ℝ) (990430118831/1000000000000 : ℝ) (495215059417/500000000000 : ℝ) (990430118831/1000000000000 : ℝ) (495215059417/500000000000 : ℝ) (990430118831/1000000000000 : ℝ) (495215059417/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2211/16384 : ℝ)) 7 (990430118831/1000000000000 : ℝ) (495215059417/500000000000 : ℝ) (990430118831/1000000000000 : ℝ) (495215059417/500000000000 : ℝ) (990430118831/1000000000000 : ℝ) (495215059417/500000000000 : ℝ) (990430118831/1000000000000 : ℝ) (495215059417/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2211/16384 : ℝ))) (24310147493/125000000000 : ℝ) (3889623599/20000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2211/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (24310147493/125000000000 : ℝ) (3889623599/20000000000 : ℝ) (149310147493/250000000000 : ℝ) (23889623599/40000000000 : ℝ) (220500102009/500000000000 : ℝ) (17640008161/40000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2211/16384 : ℝ))) 1 (149310147493/250000000000 : ℝ) (23889623599/40000000000 : ℝ) (220500102009/500000000000 : ℝ) (17640008161/40000000000 : ℝ) (103824079399/200000000000 : ℝ) (519120397/1000000000 : ℝ) (128302187731/250000000000 : ℝ) (51320875093/100000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2211/16384 : ℝ))) 2 (103824079399/200000000000 : ℝ) (519120397/1000000000 : ℝ) (128302187731/250000000000 : ℝ) (51320875093/100000000000 : ℝ) (516164573959/1000000000000 : ℝ) (103232914793/200000000000 : ℝ) (51615611061/100000000000 : ℝ) (516156110617/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2211/16384 : ℝ))) 3 (516164573959/1000000000000 : ℝ) (103232914793/200000000000 : ℝ) (51615611061/100000000000 : ℝ) (516156110617/1000000000000 : ℝ) (129040085571/250000000000 : ℝ) (516160342291/1000000000000 : ℝ) (516160342267/1000000000000 : ℝ) (258080171137/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2211/16384 : ℝ))) 4 (129040085571/250000000000 : ℝ) (516160342291/1000000000000 : ℝ) (516160342267/1000000000000 : ℝ) (258080171137/500000000000 : ℝ) (20646413691/40000000000 : ℝ) (516160342283/1000000000000 : ℝ) (20646413691/40000000000 : ℝ) (516160342283/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2211/16384 : ℝ))) 5 (20646413691/40000000000 : ℝ) (516160342283/1000000000000 : ℝ) (20646413691/40000000000 : ℝ) (516160342283/1000000000000 : ℝ) (20646413691/40000000000 : ℝ) (516160342283/1000000000000 : ℝ) (20646413691/40000000000 : ℝ) (516160342283/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2211/16384 : ℝ))) 6 (20646413691/40000000000 : ℝ) (516160342283/1000000000000 : ℝ) (20646413691/40000000000 : ℝ) (516160342283/1000000000000 : ℝ) (20646413691/40000000000 : ℝ) (516160342283/1000000000000 : ℝ) (20646413691/40000000000 : ℝ) (516160342283/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2211/16384 : ℝ))) 7 (20646413691/40000000000 : ℝ) (516160342283/1000000000000 : ℝ) (20646413691/40000000000 : ℝ) (516160342283/1000000000000 : ℝ) (20646413691/40000000000 : ℝ) (516160342283/1000000000000 : ℝ) (20646413691/40000000000 : ℝ) (516160342283/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2211/16384 : ℝ)) hmem 8 (990430118831/1000000000000 : ℝ) (495215059417/500000000000 : ℝ) (990430118831/1000000000000 : ℝ) (495215059417/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2211/16384 : ℝ))) hcmem 8 (20646413691/40000000000 : ℝ) (516160342283/1000000000000 : ℝ) (20646413691/40000000000 : ℝ) (516160342283/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2211/16384 : ℝ)) (990430118831/1000000000000 : ℝ) (495215059417/500000000000 : ℝ) (20646413691/40000000000 : ℝ) (516160342283/1000000000000 : ℝ) (818616835519/1000000000000 : ℝ) (163723367107/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0233_exp_lower
  have heNumeric : (504754370111/250000000000 : ℝ)/4 ≤ Real.exp (-2187786764337/3200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (504754370111/250000000000 : ℝ)/4 ≤ Real.exp ((8843/65536 : ℝ)-(163723367107/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8843/65536 : ℝ) (2211/16384 : ℝ) (163723367107/200000000000 : ℝ) (504754370111/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0234; no trusted numerical premise.
theorem cover7_leaf0234_exp_radius : (99759283065321447/100000000000000000 : ℝ) ≤ Real.exp ((-8845/458752 : ℝ)/8) ∧ Real.exp ((-8845/458752 : ℝ)/8) ≤ (997592830653214471/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8845/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0234_exp_lower : (183617893790919231/200000000000000000 : ℝ) ≤ Real.exp ((-109389353441/160000000000 : ℝ)/8) ∧ Real.exp ((-109389353441/160000000000 : ℝ)/8) ≤ (229522367238649039/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-109389353441/160000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0234_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (504754322083/250000000000 : ℝ) ≤ 4*Real.exp (2211/16384 : ℝ)*Real.exp (-mu (radius 7 (8845/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (504754322083/250000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8845/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0234_exp_radius
  have hrNumeric : (245226027867/250000000000 : ℝ) ≤ Real.exp (-8845/458752 : ℝ) ∧ Real.exp (-8845/458752 : ℝ) ≤ (980904111469/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (245226027867/250000000000 : ℝ) ≤ (radius 7 (8845/65536 : ℝ)) ∧ (radius 7 (8845/65536 : ℝ)) ≤ (980904111469/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8845/65536 : ℝ)) (245226027867/250000000000 : ℝ) (980904111469/1000000000000 : ℝ) (194491964109/1000000000000 : ℝ) (38898392823/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8845/65536 : ℝ)) (245226027867/250000000000 : ℝ) (980904111469/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8845/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (245226027867/250000000000 : ℝ) (980904111469/1000000000000 : ℝ) (495226027867/500000000000 : ℝ) (198090411147/200000000000 : ℝ) (495203016819/500000000000 : ℝ) (24760150841/25000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8845/65536 : ℝ)) 1 (495226027867/500000000000 : ℝ) (198090411147/200000000000 : ℝ) (495203016819/500000000000 : ℝ) (24760150841/25000000000 : ℝ) (495214522343/500000000000 : ℝ) (61901815293/62500000000 : ℝ) (495214522209/500000000000 : ℝ) (990429044421/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8845/65536 : ℝ)) 2 (495214522343/500000000000 : ℝ) (61901815293/62500000000 : ℝ) (495214522209/500000000000 : ℝ) (990429044421/1000000000000 : ℝ) (123803630569/125000000000 : ℝ) (198085808911/200000000000 : ℝ) (990429044551/1000000000000 : ℝ) (198085808911/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8845/65536 : ℝ)) 3 (123803630569/125000000000 : ℝ) (198085808911/200000000000 : ℝ) (990429044551/1000000000000 : ℝ) (198085808911/200000000000 : ℝ) (990429044551/1000000000000 : ℝ) (198085808911/200000000000 : ℝ) (990429044551/1000000000000 : ℝ) (198085808911/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8845/65536 : ℝ)) 4 (990429044551/1000000000000 : ℝ) (198085808911/200000000000 : ℝ) (990429044551/1000000000000 : ℝ) (198085808911/200000000000 : ℝ) (990429044551/1000000000000 : ℝ) (198085808911/200000000000 : ℝ) (990429044551/1000000000000 : ℝ) (198085808911/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8845/65536 : ℝ)) 5 (990429044551/1000000000000 : ℝ) (198085808911/200000000000 : ℝ) (990429044551/1000000000000 : ℝ) (198085808911/200000000000 : ℝ) (990429044551/1000000000000 : ℝ) (198085808911/200000000000 : ℝ) (990429044551/1000000000000 : ℝ) (198085808911/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8845/65536 : ℝ)) 6 (990429044551/1000000000000 : ℝ) (198085808911/200000000000 : ℝ) (990429044551/1000000000000 : ℝ) (198085808911/200000000000 : ℝ) (990429044551/1000000000000 : ℝ) (198085808911/200000000000 : ℝ) (990429044551/1000000000000 : ℝ) (198085808911/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8845/65536 : ℝ)) 7 (990429044551/1000000000000 : ℝ) (198085808911/200000000000 : ℝ) (990429044551/1000000000000 : ℝ) (198085808911/200000000000 : ℝ) (990429044551/1000000000000 : ℝ) (198085808911/200000000000 : ℝ) (990429044551/1000000000000 : ℝ) (198085808911/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8845/65536 : ℝ))) (194491964109/1000000000000 : ℝ) (38898392823/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8845/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (194491964109/1000000000000 : ℝ) (38898392823/200000000000 : ℝ) (298622991027/500000000000 : ℝ) (298622991029/500000000000 : ℝ) (441012430787/1000000000000 : ℝ) (88202486159/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8845/65536 : ℝ))) 1 (298622991027/500000000000 : ℝ) (298622991029/500000000000 : ℝ) (441012430787/1000000000000 : ℝ) (88202486159/200000000000 : ℝ) (25956460321/50000000000 : ℝ) (519129206427/1000000000000 : ℝ) (128304545497/250000000000 : ℝ) (102643636399/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8845/65536 : ℝ))) 2 (25956460321/50000000000 : ℝ) (519129206427/1000000000000 : ℝ) (128304545497/250000000000 : ℝ) (102643636399/200000000000 : ℝ) (129043423551/250000000000 : ℝ) (516173694211/1000000000000 : ℝ) (32260327049/62500000000 : ℝ) (64520654099/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8845/65536 : ℝ))) 3 (129043423551/250000000000 : ℝ) (516173694211/1000000000000 : ℝ) (32260327049/62500000000 : ℝ) (64520654099/125000000000 : ℝ) (258084731747/500000000000 : ℝ) (258084731751/500000000000 : ℝ) (129042365869/250000000000 : ℝ) (103233892697/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8845/65536 : ℝ))) 4 (258084731747/500000000000 : ℝ) (258084731751/500000000000 : ℝ) (129042365869/250000000000 : ℝ) (103233892697/200000000000 : ℝ) (103233892697/200000000000 : ℝ) (258084731747/500000000000 : ℝ) (129042365871/250000000000 : ℝ) (258084731747/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8845/65536 : ℝ))) 5 (103233892697/200000000000 : ℝ) (258084731747/500000000000 : ℝ) (129042365871/250000000000 : ℝ) (258084731747/500000000000 : ℝ) (129042365871/250000000000 : ℝ) (258084731747/500000000000 : ℝ) (129042365871/250000000000 : ℝ) (258084731747/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8845/65536 : ℝ))) 6 (129042365871/250000000000 : ℝ) (258084731747/500000000000 : ℝ) (129042365871/250000000000 : ℝ) (258084731747/500000000000 : ℝ) (129042365871/250000000000 : ℝ) (258084731747/500000000000 : ℝ) (129042365871/250000000000 : ℝ) (258084731747/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8845/65536 : ℝ))) 7 (129042365871/250000000000 : ℝ) (258084731747/500000000000 : ℝ) (129042365871/250000000000 : ℝ) (258084731747/500000000000 : ℝ) (129042365871/250000000000 : ℝ) (258084731747/500000000000 : ℝ) (129042365871/250000000000 : ℝ) (258084731747/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8845/65536 : ℝ)) hmem 8 (990429044551/1000000000000 : ℝ) (198085808911/200000000000 : ℝ) (990429044551/1000000000000 : ℝ) (198085808911/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8845/65536 : ℝ))) hcmem 8 (129042365871/250000000000 : ℝ) (258084731747/500000000000 : ℝ) (129042365871/250000000000 : ℝ) (258084731747/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8845/65536 : ℝ)) (990429044551/1000000000000 : ℝ) (198085808911/200000000000 : ℝ) (129042365871/250000000000 : ℝ) (258084731747/500000000000 : ℝ) (163726437891/200000000000 : ℝ) (32745287579/40000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0234_exp_lower
  have heNumeric : (504754322083/250000000000 : ℝ)/4 ≤ Real.exp (-109389353441/160000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (504754322083/250000000000 : ℝ)/4 ≤ Real.exp ((2211/16384 : ℝ)-(32745287579/40000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2211/16384 : ℝ) (8845/65536 : ℝ) (32745287579/40000000000 : ℝ) (504754322083/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0235; no trusted numerical premise.
theorem cover7_leaf0235_exp_radius : (997592558830776981/1000000000000000000 : ℝ) ≤ Real.exp ((-4423/229376 : ℝ)/8) ∧ Real.exp ((-4423/229376 : ℝ)/8) ≤ (498796279415388491/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4423/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0235_exp_lower : (459044729084272013/500000000000000000 : ℝ) ≤ Real.exp ((-10938936847891/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938936847891/16000000000000 : ℝ)/8) ≤ (918089458168544027/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938936847891/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0235_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019017098571/1000000000000 : ℝ) ≤ 4*Real.exp (8845/65536 : ℝ)*Real.exp (-mu (radius 7 (4423/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (2019017098571/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4423/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0235_exp_radius
  have hrNumeric : (980901973269/1000000000000 : ℝ) ≤ Real.exp (-4423/229376 : ℝ) ∧ Real.exp (-4423/229376 : ℝ) ≤ (98090197327/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980901973269/1000000000000 : ℝ) ≤ (radius 7 (4423/32768 : ℝ)) ∧ (radius 7 (4423/32768 : ℝ)) ≤ (98090197327/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4423/32768 : ℝ)) (980901973269/1000000000000 : ℝ) (98090197327/100000000000 : ℝ) (48625686907/250000000000 : ℝ) (97251373817/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4423/32768 : ℝ)) (980901973269/1000000000000 : ℝ) (98090197327/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4423/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980901973269/1000000000000 : ℝ) (98090197327/100000000000 : ℝ) (495225493317/500000000000 : ℝ) (198090197327/200000000000 : ℝ) (495202477091/500000000000 : ℝ) (990404954183/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4423/32768 : ℝ)) 1 (495225493317/500000000000 : ℝ) (198090197327/200000000000 : ℝ) (495202477091/500000000000 : ℝ) (990404954183/1000000000000 : ℝ) (123803496301/125000000000 : ℝ) (990427970409/1000000000000 : ℝ) (49521398507/50000000000 : ℝ) (495213985071/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4423/32768 : ℝ)) 2 (123803496301/125000000000 : ℝ) (990427970409/1000000000000 : ℝ) (49521398507/50000000000 : ℝ) (495213985071/500000000000 : ℝ) (495213985137/500000000000 : ℝ) (247606992569/250000000000 : ℝ) (990427970273/1000000000000 : ℝ) (247606992569/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4423/32768 : ℝ)) 3 (495213985137/500000000000 : ℝ) (247606992569/250000000000 : ℝ) (990427970273/1000000000000 : ℝ) (247606992569/250000000000 : ℝ) (990427970273/1000000000000 : ℝ) (247606992569/250000000000 : ℝ) (990427970273/1000000000000 : ℝ) (247606992569/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4423/32768 : ℝ)) 4 (990427970273/1000000000000 : ℝ) (247606992569/250000000000 : ℝ) (990427970273/1000000000000 : ℝ) (247606992569/250000000000 : ℝ) (990427970273/1000000000000 : ℝ) (247606992569/250000000000 : ℝ) (990427970273/1000000000000 : ℝ) (247606992569/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4423/32768 : ℝ)) 5 (990427970273/1000000000000 : ℝ) (247606992569/250000000000 : ℝ) (990427970273/1000000000000 : ℝ) (247606992569/250000000000 : ℝ) (990427970273/1000000000000 : ℝ) (247606992569/250000000000 : ℝ) (990427970273/1000000000000 : ℝ) (247606992569/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4423/32768 : ℝ)) 6 (990427970273/1000000000000 : ℝ) (247606992569/250000000000 : ℝ) (990427970273/1000000000000 : ℝ) (247606992569/250000000000 : ℝ) (990427970273/1000000000000 : ℝ) (247606992569/250000000000 : ℝ) (990427970273/1000000000000 : ℝ) (247606992569/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4423/32768 : ℝ)) 7 (990427970273/1000000000000 : ℝ) (247606992569/250000000000 : ℝ) (990427970273/1000000000000 : ℝ) (247606992569/250000000000 : ℝ) (990427970273/1000000000000 : ℝ) (247606992569/250000000000 : ℝ) (990427970273/1000000000000 : ℝ) (247606992569/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4423/32768 : ℝ))) (48625686907/250000000000 : ℝ) (97251373817/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4423/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (48625686907/250000000000 : ℝ) (97251373817/500000000000 : ℝ) (298625686907/500000000000 : ℝ) (597251373817/1000000000000 : ℝ) (88204931297/200000000000 : ℝ) (441024656493/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4423/32768 : ℝ))) 1 (298625686907/500000000000 : ℝ) (597251373817/1000000000000 : ℝ) (88204931297/200000000000 : ℝ) (441024656493/1000000000000 : ℝ) (519138015149/1000000000000 : ℝ) (103827603031/200000000000 : ℝ) (102645522449/200000000000 : ℝ) (128306903063/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4423/32768 : ℝ))) 2 (519138015149/1000000000000 : ℝ) (103827603031/200000000000 : ℝ) (102645522449/200000000000 : ℝ) (128306903063/250000000000 : ℝ) (516182813697/1000000000000 : ℝ) (64522851713/125000000000 : ℝ) (258087177103/500000000000 : ℝ) (258087177107/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4423/32768 : ℝ))) 3 (516182813697/1000000000000 : ℝ) (64522851713/125000000000 : ℝ) (258087177103/500000000000 : ℝ) (258087177107/500000000000 : ℝ) (516178583951/1000000000000 : ℝ) (516178583959/1000000000000 : ℝ) (258089291967/500000000000 : ℝ) (258089291971/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4423/32768 : ℝ))) 4 (516178583951/1000000000000 : ℝ) (516178583959/1000000000000 : ℝ) (258089291967/500000000000 : ℝ) (258089291971/500000000000 : ℝ) (258089291971/500000000000 : ℝ) (516178583951/1000000000000 : ℝ) (258089291971/500000000000 : ℝ) (516178583951/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4423/32768 : ℝ))) 5 (258089291971/500000000000 : ℝ) (516178583951/1000000000000 : ℝ) (258089291971/500000000000 : ℝ) (516178583951/1000000000000 : ℝ) (258089291971/500000000000 : ℝ) (516178583951/1000000000000 : ℝ) (258089291971/500000000000 : ℝ) (516178583951/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4423/32768 : ℝ))) 6 (258089291971/500000000000 : ℝ) (516178583951/1000000000000 : ℝ) (258089291971/500000000000 : ℝ) (516178583951/1000000000000 : ℝ) (258089291971/500000000000 : ℝ) (516178583951/1000000000000 : ℝ) (258089291971/500000000000 : ℝ) (516178583951/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4423/32768 : ℝ))) 7 (258089291971/500000000000 : ℝ) (516178583951/1000000000000 : ℝ) (258089291971/500000000000 : ℝ) (516178583951/1000000000000 : ℝ) (258089291971/500000000000 : ℝ) (516178583951/1000000000000 : ℝ) (258089291971/500000000000 : ℝ) (516178583951/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4423/32768 : ℝ)) hmem 8 (990427970273/1000000000000 : ℝ) (247606992569/250000000000 : ℝ) (990427970273/1000000000000 : ℝ) (247606992569/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4423/32768 : ℝ))) hcmem 8 (258089291971/500000000000 : ℝ) (516178583951/1000000000000 : ℝ) (258089291971/500000000000 : ℝ) (516178583951/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4423/32768 : ℝ)) (990427970273/1000000000000 : ℝ) (247606992569/250000000000 : ℝ) (258089291971/500000000000 : ℝ) (516178583951/1000000000000 : ℝ) (409323771117/500000000000 : ℝ) (818647542251/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0235_exp_lower
  have heNumeric : (2019017098571/1000000000000 : ℝ)/4 ≤ Real.exp (-10938936847891/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019017098571/1000000000000 : ℝ)/4 ≤ Real.exp ((8845/65536 : ℝ)-(818647542251/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8845/65536 : ℝ) (4423/32768 : ℝ) (818647542251/1000000000000 : ℝ) (2019017098571/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0236; no trusted numerical premise.
theorem cover7_leaf0236_exp_radius : (997592287008413559/1000000000000000000 : ℝ) ≤ Real.exp ((-8847/458752 : ℝ)/8) ∧ Real.exp ((-8847/458752 : ℝ)/8) ≤ (24939807175210339/25000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8847/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0236_exp_lower : (229522361878961129/250000000000000000 : ℝ) ≤ Real.exp ((-1093893833309/1600000000000 : ℝ)/8) ∧ Real.exp ((-1093893833309/1600000000000 : ℝ)/8) ≤ (918089447515844517/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1093893833309/1600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0236_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (504754227789/250000000000 : ℝ) ≤ 4*Real.exp (4423/32768 : ℝ)*Real.exp (-mu (radius 7 (8847/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (504754227789/250000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8847/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0236_exp_radius
  have hrNumeric : (39235993403/40000000000 : ℝ) ≤ Real.exp (-8847/458752 : ℝ) ∧ Real.exp (-8847/458752 : ℝ) ≤ (245224958769/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (39235993403/40000000000 : ℝ) ≤ (radius 7 (8847/65536 : ℝ)) ∧ (radius 7 (8847/65536 : ℝ)) ≤ (245224958769/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8847/65536 : ℝ)) (39235993403/40000000000 : ℝ) (245224958769/250000000000 : ℝ) (389027061/2000000000 : ℝ) (97256765253/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8847/65536 : ℝ)) (39235993403/40000000000 : ℝ) (245224958769/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8847/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (39235993403/40000000000 : ℝ) (245224958769/250000000000 : ℝ) (990449917537/1000000000000 : ℝ) (495224958769/500000000000 : ℝ) (990403874727/1000000000000 : ℝ) (123800484341/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8847/65536 : ℝ)) 1 (990449917537/1000000000000 : ℝ) (495224958769/500000000000 : ℝ) (990403874727/1000000000000 : ℝ) (123800484341/125000000000 : ℝ) (247606724033/250000000000 : ℝ) (990426896133/1000000000000 : ℝ) (123803361983/125000000000 : ℝ) (495213447933/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8847/65536 : ℝ)) 2 (247606724033/250000000000 : ℝ) (990426896133/1000000000000 : ℝ) (123803361983/125000000000 : ℝ) (495213447933/500000000000 : ℝ) (495213447999/500000000000 : ℝ) (61901681/62500000 : ℝ) (990426895997/1000000000000 : ℝ) (61901681/62500000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8847/65536 : ℝ)) 3 (495213447999/500000000000 : ℝ) (61901681/62500000 : ℝ) (990426895997/1000000000000 : ℝ) (61901681/62500000 : ℝ) (990426895997/1000000000000 : ℝ) (61901681/62500000 : ℝ) (990426895997/1000000000000 : ℝ) (61901681/62500000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8847/65536 : ℝ)) 4 (990426895997/1000000000000 : ℝ) (61901681/62500000 : ℝ) (990426895997/1000000000000 : ℝ) (61901681/62500000 : ℝ) (990426895997/1000000000000 : ℝ) (61901681/62500000 : ℝ) (990426895997/1000000000000 : ℝ) (61901681/62500000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8847/65536 : ℝ)) 5 (990426895997/1000000000000 : ℝ) (61901681/62500000 : ℝ) (990426895997/1000000000000 : ℝ) (61901681/62500000 : ℝ) (990426895997/1000000000000 : ℝ) (61901681/62500000 : ℝ) (990426895997/1000000000000 : ℝ) (61901681/62500000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8847/65536 : ℝ)) 6 (990426895997/1000000000000 : ℝ) (61901681/62500000 : ℝ) (990426895997/1000000000000 : ℝ) (61901681/62500000 : ℝ) (990426895997/1000000000000 : ℝ) (61901681/62500000 : ℝ) (990426895997/1000000000000 : ℝ) (61901681/62500000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8847/65536 : ℝ)) 7 (990426895997/1000000000000 : ℝ) (61901681/62500000 : ℝ) (990426895997/1000000000000 : ℝ) (61901681/62500000 : ℝ) (990426895997/1000000000000 : ℝ) (61901681/62500000 : ℝ) (990426895997/1000000000000 : ℝ) (61901681/62500000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8847/65536 : ℝ))) (389027061/2000000000 : ℝ) (97256765253/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8847/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (389027061/2000000000 : ℝ) (97256765253/500000000000 : ℝ) (2389027061/4000000000 : ℝ) (597256765253/1000000000000 : ℝ) (44103688111/100000000000 : ℝ) (220518440559/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8847/65536 : ℝ))) 1 (2389027061/4000000000 : ℝ) (597256765253/1000000000000 : ℝ) (44103688111/100000000000 : ℝ) (220518440559/500000000000 : ℝ) (25957341159/50000000000 : ℝ) (259573411593/500000000000 : ℝ) (256618520847/500000000000 : ℝ) (513237041701/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8847/65536 : ℝ))) 2 (25957341159/50000000000 : ℝ) (259573411593/500000000000 : ℝ) (256618520847/500000000000 : ℝ) (513237041701/1000000000000 : ℝ) (516191932437/1000000000000 : ℝ) (129047983111/250000000000 : ℝ) (258091737437/500000000000 : ℝ) (258091737441/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8847/65536 : ℝ))) 3 (516191932437/1000000000000 : ℝ) (129047983111/250000000000 : ℝ) (258091737437/500000000000 : ℝ) (258091737441/500000000000 : ℝ) (103237540731/200000000000 : ℝ) (516187703663/1000000000000 : ℝ) (258093851819/500000000000 : ℝ) (258093851823/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8847/65536 : ℝ))) 4 (103237540731/200000000000 : ℝ) (516187703663/1000000000000 : ℝ) (258093851819/500000000000 : ℝ) (258093851823/500000000000 : ℝ) (258093851823/500000000000 : ℝ) (103237540731/200000000000 : ℝ) (258093851823/500000000000 : ℝ) (103237540731/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8847/65536 : ℝ))) 5 (258093851823/500000000000 : ℝ) (103237540731/200000000000 : ℝ) (258093851823/500000000000 : ℝ) (103237540731/200000000000 : ℝ) (258093851823/500000000000 : ℝ) (103237540731/200000000000 : ℝ) (258093851823/500000000000 : ℝ) (103237540731/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8847/65536 : ℝ))) 6 (258093851823/500000000000 : ℝ) (103237540731/200000000000 : ℝ) (258093851823/500000000000 : ℝ) (103237540731/200000000000 : ℝ) (258093851823/500000000000 : ℝ) (103237540731/200000000000 : ℝ) (258093851823/500000000000 : ℝ) (103237540731/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8847/65536 : ℝ))) 7 (258093851823/500000000000 : ℝ) (103237540731/200000000000 : ℝ) (258093851823/500000000000 : ℝ) (103237540731/200000000000 : ℝ) (258093851823/500000000000 : ℝ) (103237540731/200000000000 : ℝ) (258093851823/500000000000 : ℝ) (103237540731/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8847/65536 : ℝ)) hmem 8 (990426895997/1000000000000 : ℝ) (61901681/62500000 : ℝ) (990426895997/1000000000000 : ℝ) (61901681/62500000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8847/65536 : ℝ))) hcmem 8 (258093851823/500000000000 : ℝ) (103237540731/200000000000 : ℝ) (258093851823/500000000000 : ℝ) (103237540731/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8847/65536 : ℝ)) (990426895997/1000000000000 : ℝ) (61901681/62500000 : ℝ) (258093851823/500000000000 : ℝ) (103237540731/200000000000 : ℝ) (818662893847/1000000000000 : ℝ) (163732578773/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0236_exp_lower
  have heNumeric : (504754227789/250000000000 : ℝ)/4 ≤ Real.exp (-1093893833309/1600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (504754227789/250000000000 : ℝ)/4 ≤ Real.exp ((4423/32768 : ℝ)-(163732578773/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4423/32768 : ℝ) (8847/65536 : ℝ) (163732578773/200000000000 : ℝ) (504754227789/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0237; no trusted numerical premise.
theorem cover7_leaf0237_exp_radius : (997592015186124201/1000000000000000000 : ℝ) ≤ Real.exp ((-79/4096 : ℝ)/8) ∧ Real.exp ((-79/4096 : ℝ)/8) ≤ (498796007593062101/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-79/4096 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0237_exp_lower : (918089436995579531/1000000000000000000 : ℝ) ≤ Real.exp ((-437557591993/640000000000 : ℝ)/8) ∧ Real.exp ((-437557591993/640000000000 : ℝ)/8) ≤ (229522359248894883/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-437557591993/640000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0237_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019016726071/1000000000000 : ℝ) ≤ 4*Real.exp (8847/65536 : ℝ)*Real.exp (-mu (radius 7 (553/4096 : ℝ))) ∧ (2019/1000 : ℝ) < (2019016726071/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (553/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0237_exp_radius
  have hrNumeric : (196179539377/200000000000 : ℝ) ≤ Real.exp (-79/4096 : ℝ) ∧ Real.exp (-79/4096 : ℝ) ≤ (490448848443/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196179539377/200000000000 : ℝ) ≤ (radius 7 (553/4096 : ℝ)) ∧ (radius 7 (553/4096 : ℝ)) ≤ (490448848443/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (553/4096 : ℝ)) (196179539377/200000000000 : ℝ) (490448848443/500000000000 : ℝ) (194524312731/1000000000000 : ℝ) (194524312737/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (553/4096 : ℝ)) (196179539377/200000000000 : ℝ) (490448848443/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (553/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196179539377/200000000000 : ℝ) (490448848443/500000000000 : ℝ) (495224424221/500000000000 : ℝ) (990448848443/1000000000000 : ℝ) (990402795273/1000000000000 : ℝ) (495201397637/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (553/4096 : ℝ)) 1 (495224424221/500000000000 : ℝ) (990448848443/1000000000000 : ℝ) (990402795273/1000000000000 : ℝ) (495201397637/500000000000 : ℝ) (990425821857/1000000000000 : ℝ) (990425821859/1000000000000 : ℝ) (990425821589/1000000000000 : ℝ) (990425821591/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (553/4096 : ℝ)) 2 (990425821857/1000000000000 : ℝ) (990425821859/1000000000000 : ℝ) (990425821589/1000000000000 : ℝ) (990425821591/1000000000000 : ℝ) (990425821723/1000000000000 : ℝ) (39617032869/40000000000 : ℝ) (495212910861/500000000000 : ℝ) (39617032869/40000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (553/4096 : ℝ)) 3 (990425821723/1000000000000 : ℝ) (39617032869/40000000000 : ℝ) (495212910861/500000000000 : ℝ) (39617032869/40000000000 : ℝ) (495212910861/500000000000 : ℝ) (39617032869/40000000000 : ℝ) (495212910861/500000000000 : ℝ) (39617032869/40000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (553/4096 : ℝ)) 4 (495212910861/500000000000 : ℝ) (39617032869/40000000000 : ℝ) (495212910861/500000000000 : ℝ) (39617032869/40000000000 : ℝ) (495212910861/500000000000 : ℝ) (39617032869/40000000000 : ℝ) (495212910861/500000000000 : ℝ) (39617032869/40000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (553/4096 : ℝ)) 5 (495212910861/500000000000 : ℝ) (39617032869/40000000000 : ℝ) (495212910861/500000000000 : ℝ) (39617032869/40000000000 : ℝ) (495212910861/500000000000 : ℝ) (39617032869/40000000000 : ℝ) (495212910861/500000000000 : ℝ) (39617032869/40000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (553/4096 : ℝ)) 6 (495212910861/500000000000 : ℝ) (39617032869/40000000000 : ℝ) (495212910861/500000000000 : ℝ) (39617032869/40000000000 : ℝ) (495212910861/500000000000 : ℝ) (39617032869/40000000000 : ℝ) (495212910861/500000000000 : ℝ) (39617032869/40000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (553/4096 : ℝ)) 7 (495212910861/500000000000 : ℝ) (39617032869/40000000000 : ℝ) (495212910861/500000000000 : ℝ) (39617032869/40000000000 : ℝ) (495212910861/500000000000 : ℝ) (39617032869/40000000000 : ℝ) (495212910861/500000000000 : ℝ) (39617032869/40000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (553/4096 : ℝ))) (194524312731/1000000000000 : ℝ) (194524312737/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (553/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (194524312731/1000000000000 : ℝ) (194524312737/1000000000000 : ℝ) (119452431273/200000000000 : ℝ) (597262156369/1000000000000 : ℝ) (44104910467/100000000000 : ℝ) (220524552339/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (553/4096 : ℝ))) 1 (119452431273/200000000000 : ℝ) (597262156369/1000000000000 : ℝ) (44104910467/100000000000 : ℝ) (220524552339/500000000000 : ℝ) (519155630517/1000000000000 : ℝ) (129788907631/250000000000 : ℝ) (513246470341/1000000000000 : ℝ) (128311617587/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (553/4096 : ℝ))) 2 (519155630517/1000000000000 : ℝ) (129788907631/250000000000 : ℝ) (513246470341/1000000000000 : ℝ) (128311617587/250000000000 : ℝ) (516201050429/1000000000000 : ℝ) (129050262609/250000000000 : ℝ) (258096297397/500000000000 : ℝ) (258096297401/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (553/4096 : ℝ))) 3 (516201050429/1000000000000 : ℝ) (129050262609/250000000000 : ℝ) (258096297397/500000000000 : ℝ) (258096297401/500000000000 : ℝ) (516196822611/1000000000000 : ℝ) (516196822619/1000000000000 : ℝ) (258098411297/500000000000 : ℝ) (258098411301/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (553/4096 : ℝ))) 4 (516196822611/1000000000000 : ℝ) (516196822619/1000000000000 : ℝ) (258098411297/500000000000 : ℝ) (258098411301/500000000000 : ℝ) (258098411301/500000000000 : ℝ) (516196822611/1000000000000 : ℝ) (258098411301/500000000000 : ℝ) (516196822611/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (553/4096 : ℝ))) 5 (258098411301/500000000000 : ℝ) (516196822611/1000000000000 : ℝ) (258098411301/500000000000 : ℝ) (516196822611/1000000000000 : ℝ) (258098411301/500000000000 : ℝ) (516196822611/1000000000000 : ℝ) (258098411301/500000000000 : ℝ) (516196822611/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (553/4096 : ℝ))) 6 (258098411301/500000000000 : ℝ) (516196822611/1000000000000 : ℝ) (258098411301/500000000000 : ℝ) (516196822611/1000000000000 : ℝ) (258098411301/500000000000 : ℝ) (516196822611/1000000000000 : ℝ) (258098411301/500000000000 : ℝ) (516196822611/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (553/4096 : ℝ))) 7 (258098411301/500000000000 : ℝ) (516196822611/1000000000000 : ℝ) (258098411301/500000000000 : ℝ) (516196822611/1000000000000 : ℝ) (258098411301/500000000000 : ℝ) (516196822611/1000000000000 : ℝ) (258098411301/500000000000 : ℝ) (516196822611/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (553/4096 : ℝ)) hmem 8 (495212910861/500000000000 : ℝ) (39617032869/40000000000 : ℝ) (495212910861/500000000000 : ℝ) (39617032869/40000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (553/4096 : ℝ))) hcmem 8 (258098411301/500000000000 : ℝ) (516196822611/1000000000000 : ℝ) (258098411301/500000000000 : ℝ) (516196822611/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (553/4096 : ℝ)) (495212910861/500000000000 : ℝ) (39617032869/40000000000 : ℝ) (258098411301/500000000000 : ℝ) (516196822611/1000000000000 : ℝ) (818678244307/1000000000000 : ℝ) (32747129773/40000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0237_exp_lower
  have heNumeric : (2019016726071/1000000000000 : ℝ)/4 ≤ Real.exp (-437557591993/640000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019016726071/1000000000000 : ℝ)/4 ≤ Real.exp ((8847/65536 : ℝ)-(32747129773/40000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8847/65536 : ℝ) (553/4096 : ℝ) (32747129773/40000000000 : ℝ) (2019016726071/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0238; no trusted numerical premise.
theorem cover7_leaf0238_exp_radius : (99759174336390891/100000000000000000 : ℝ) ≤ Real.exp ((-8849/458752 : ℝ)/8) ∧ Real.exp ((-8849/458752 : ℝ)/8) ≤ (997591743363908911/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8849/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0238_exp_lower : (918089426608781917/1000000000000000000 : ℝ) ≤ Real.exp ((-683683827997/1000000000000 : ℝ)/8) ∧ Real.exp ((-683683827997/1000000000000 : ℝ)/8) ≤ (459044713304390959/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-683683827997/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0238_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009508271667/500000000000 : ℝ) ≤ 4*Real.exp (553/4096 : ℝ)*Real.exp (-mu (radius 7 (8849/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (1009508271667/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8849/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0238_exp_radius
  have hrNumeric : (9808955587/10000000000 : ℝ) ≤ Real.exp (-8849/458752 : ℝ) ∧ Real.exp (-8849/458752 : ℝ) ≤ (980895558701/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (9808955587/10000000000 : ℝ) ≤ (radius 7 (8849/65536 : ℝ)) ∧ (radius 7 (8849/65536 : ℝ)) ≤ (980895558701/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8849/65536 : ℝ)) (9808955587/10000000000 : ℝ) (980895558701/1000000000000 : ℝ) (48633773579/250000000000 : ℝ) (97267547161/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8849/65536 : ℝ)) (9808955587/10000000000 : ℝ) (980895558701/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8849/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (9808955587/10000000000 : ℝ) (980895558701/1000000000000 : ℝ) (19808955587/20000000000 : ℝ) (990447779351/1000000000000 : ℝ) (49520085791/50000000000 : ℝ) (990401715821/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8849/65536 : ℝ)) 1 (19808955587/20000000000 : ℝ) (990447779351/1000000000000 : ℝ) (49520085791/50000000000 : ℝ) (990401715821/1000000000000 : ℝ) (198084949517/200000000000 : ℝ) (495212373793/500000000000 : ℝ) (990424747317/1000000000000 : ℝ) (990424747319/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8849/65536 : ℝ)) 2 (198084949517/200000000000 : ℝ) (495212373793/500000000000 : ℝ) (990424747317/1000000000000 : ℝ) (990424747319/1000000000000 : ℝ) (990424747451/1000000000000 : ℝ) (990424747453/1000000000000 : ℝ) (19808494949/20000000000 : ℝ) (990424747453/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8849/65536 : ℝ)) 3 (990424747451/1000000000000 : ℝ) (990424747453/1000000000000 : ℝ) (19808494949/20000000000 : ℝ) (990424747453/1000000000000 : ℝ) (19808494949/20000000000 : ℝ) (990424747453/1000000000000 : ℝ) (19808494949/20000000000 : ℝ) (990424747453/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8849/65536 : ℝ)) 4 (19808494949/20000000000 : ℝ) (990424747453/1000000000000 : ℝ) (19808494949/20000000000 : ℝ) (990424747453/1000000000000 : ℝ) (19808494949/20000000000 : ℝ) (990424747453/1000000000000 : ℝ) (19808494949/20000000000 : ℝ) (990424747453/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8849/65536 : ℝ)) 5 (19808494949/20000000000 : ℝ) (990424747453/1000000000000 : ℝ) (19808494949/20000000000 : ℝ) (990424747453/1000000000000 : ℝ) (19808494949/20000000000 : ℝ) (990424747453/1000000000000 : ℝ) (19808494949/20000000000 : ℝ) (990424747453/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8849/65536 : ℝ)) 6 (19808494949/20000000000 : ℝ) (990424747453/1000000000000 : ℝ) (19808494949/20000000000 : ℝ) (990424747453/1000000000000 : ℝ) (19808494949/20000000000 : ℝ) (990424747453/1000000000000 : ℝ) (19808494949/20000000000 : ℝ) (990424747453/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8849/65536 : ℝ)) 7 (19808494949/20000000000 : ℝ) (990424747453/1000000000000 : ℝ) (19808494949/20000000000 : ℝ) (990424747453/1000000000000 : ℝ) (19808494949/20000000000 : ℝ) (990424747453/1000000000000 : ℝ) (19808494949/20000000000 : ℝ) (990424747453/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8849/65536 : ℝ))) (48633773579/250000000000 : ℝ) (97267547161/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8849/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (48633773579/250000000000 : ℝ) (97267547161/500000000000 : ℝ) (298633773579/500000000000 : ℝ) (597267547161/1000000000000 : ℝ) (441061327159/1000000000000 : ℝ) (441061327167/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8849/65536 : ℝ))) 1 (298633773579/500000000000 : ℝ) (597267547161/1000000000000 : ℝ) (441061327159/1000000000000 : ℝ) (441061327167/1000000000000 : ℝ) (259582218579/500000000000 : ℝ) (129791109291/250000000000 : ℝ) (513255898181/1000000000000 : ℝ) (128313974547/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8849/65536 : ℝ))) 2 (259582218579/500000000000 : ℝ) (129791109291/250000000000 : ℝ) (513255898181/1000000000000 : ℝ) (128313974547/250000000000 : ℝ) (516210167669/1000000000000 : ℝ) (129052541919/250000000000 : ℝ) (516201713961/1000000000000 : ℝ) (516201713969/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8849/65536 : ℝ))) 3 (516210167669/1000000000000 : ℝ) (129052541919/250000000000 : ℝ) (516201713961/1000000000000 : ℝ) (516201713969/1000000000000 : ℝ) (103241188163/200000000000 : ℝ) (516205940823/1000000000000 : ℝ) (516205940797/1000000000000 : ℝ) (258102970403/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8849/65536 : ℝ))) 4 (103241188163/200000000000 : ℝ) (516205940823/1000000000000 : ℝ) (516205940797/1000000000000 : ℝ) (258102970403/500000000000 : ℝ) (258102970403/500000000000 : ℝ) (103241188163/200000000000 : ℝ) (103241188161/200000000000 : ℝ) (103241188163/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8849/65536 : ℝ))) 5 (258102970403/500000000000 : ℝ) (103241188163/200000000000 : ℝ) (103241188161/200000000000 : ℝ) (103241188163/200000000000 : ℝ) (103241188161/200000000000 : ℝ) (103241188163/200000000000 : ℝ) (103241188161/200000000000 : ℝ) (103241188163/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8849/65536 : ℝ))) 6 (103241188161/200000000000 : ℝ) (103241188163/200000000000 : ℝ) (103241188161/200000000000 : ℝ) (103241188163/200000000000 : ℝ) (103241188161/200000000000 : ℝ) (103241188163/200000000000 : ℝ) (103241188161/200000000000 : ℝ) (103241188163/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8849/65536 : ℝ))) 7 (103241188161/200000000000 : ℝ) (103241188163/200000000000 : ℝ) (103241188161/200000000000 : ℝ) (103241188163/200000000000 : ℝ) (103241188161/200000000000 : ℝ) (103241188163/200000000000 : ℝ) (103241188161/200000000000 : ℝ) (103241188163/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8849/65536 : ℝ)) hmem 8 (19808494949/20000000000 : ℝ) (990424747453/1000000000000 : ℝ) (19808494949/20000000000 : ℝ) (990424747453/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8849/65536 : ℝ))) hcmem 8 (103241188161/200000000000 : ℝ) (103241188163/200000000000 : ℝ) (103241188161/200000000000 : ℝ) (103241188163/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8849/65536 : ℝ)) (19808494949/20000000000 : ℝ) (990424747453/1000000000000 : ℝ) (103241188161/200000000000 : ℝ) (103241188163/200000000000 : ℝ) (818693593603/1000000000000 : ℝ) (409346796811/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0238_exp_lower
  have heNumeric : (1009508271667/500000000000 : ℝ)/4 ≤ Real.exp (-683683827997/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009508271667/500000000000 : ℝ)/4 ≤ Real.exp ((553/4096 : ℝ)-(409346796811/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (553/4096 : ℝ) (8849/65536 : ℝ) (409346796811/500000000000 : ℝ) (1009508271667/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0239; no trusted numerical premise.
theorem cover7_leaf0239_exp_radius : (249397867885441921/250000000000000000 : ℝ) ≤ Real.exp ((-4425/229376 : ℝ)/8) ∧ Real.exp ((-4425/229376 : ℝ)/8) ≤ (199518294308353537/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4425/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0239_exp_lower : (918089416355222147/1000000000000000000 : ℝ) ≤ Real.exp ((-10938942677503/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938942677503/16000000000000 : ℝ)/8) ≤ (229522354088805537/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938942677503/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0239_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019016362941/1000000000000 : ℝ) ≤ 4*Real.exp (8849/65536 : ℝ)*Real.exp (-mu (radius 7 (4425/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (2019016362941/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4425/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0239_exp_radius
  have hrNumeric : (24522335513/25000000000 : ℝ) ≤ Real.exp (-4425/229376 : ℝ) ∧ Real.exp (-4425/229376 : ℝ) ≤ (980893420521/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (24522335513/25000000000 : ℝ) ≤ (radius 7 (4425/32768 : ℝ)) ∧ (radius 7 (4425/32768 : ℝ)) ≤ (980893420521/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4425/32768 : ℝ)) (24522335513/25000000000 : ℝ) (980893420521/1000000000000 : ℝ) (97272937627/500000000000 : ℝ) (9727293763/50000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4425/32768 : ℝ)) (24522335513/25000000000 : ℝ) (980893420521/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4425/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (24522335513/25000000000 : ℝ) (980893420521/1000000000000 : ℝ) (49522335513/50000000000 : ℝ) (990446710261/1000000000000 : ℝ) (61900039773/62500000000 : ℝ) (99040063637/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4425/32768 : ℝ)) 1 (49522335513/50000000000 : ℝ) (990446710261/1000000000000 : ℝ) (61900039773/62500000000 : ℝ) (99040063637/100000000000 : ℝ) (495211836657/500000000000 : ℝ) (247605918329/250000000000 : ℝ) (495211836523/500000000000 : ℝ) (123802959131/125000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4425/32768 : ℝ)) 2 (495211836657/500000000000 : ℝ) (247605918329/250000000000 : ℝ) (495211836523/500000000000 : ℝ) (123802959131/125000000000 : ℝ) (49521183659/50000000000 : ℝ) (495211836591/500000000000 : ℝ) (990423673179/1000000000000 : ℝ) (495211836591/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4425/32768 : ℝ)) 3 (49521183659/50000000000 : ℝ) (495211836591/500000000000 : ℝ) (990423673179/1000000000000 : ℝ) (495211836591/500000000000 : ℝ) (990423673179/1000000000000 : ℝ) (495211836591/500000000000 : ℝ) (990423673179/1000000000000 : ℝ) (495211836591/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4425/32768 : ℝ)) 4 (990423673179/1000000000000 : ℝ) (495211836591/500000000000 : ℝ) (990423673179/1000000000000 : ℝ) (495211836591/500000000000 : ℝ) (990423673179/1000000000000 : ℝ) (495211836591/500000000000 : ℝ) (990423673179/1000000000000 : ℝ) (495211836591/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4425/32768 : ℝ)) 5 (990423673179/1000000000000 : ℝ) (495211836591/500000000000 : ℝ) (990423673179/1000000000000 : ℝ) (495211836591/500000000000 : ℝ) (990423673179/1000000000000 : ℝ) (495211836591/500000000000 : ℝ) (990423673179/1000000000000 : ℝ) (495211836591/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4425/32768 : ℝ)) 6 (990423673179/1000000000000 : ℝ) (495211836591/500000000000 : ℝ) (990423673179/1000000000000 : ℝ) (495211836591/500000000000 : ℝ) (990423673179/1000000000000 : ℝ) (495211836591/500000000000 : ℝ) (990423673179/1000000000000 : ℝ) (495211836591/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4425/32768 : ℝ)) 7 (990423673179/1000000000000 : ℝ) (495211836591/500000000000 : ℝ) (990423673179/1000000000000 : ℝ) (495211836591/500000000000 : ℝ) (990423673179/1000000000000 : ℝ) (495211836591/500000000000 : ℝ) (990423673179/1000000000000 : ℝ) (495211836591/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4425/32768 : ℝ))) (97272937627/500000000000 : ℝ) (9727293763/50000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4425/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (97272937627/500000000000 : ℝ) (9727293763/50000000000 : ℝ) (597272937627/1000000000000 : ℝ) (59727293763/100000000000 : ℝ) (13783548393/31250000000 : ℝ) (55134193573/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4425/32768 : ℝ))) 1 (597272937627/1000000000000 : ℝ) (59727293763/100000000000 : ℝ) (13783548393/31250000000 : ℝ) (55134193573/125000000000 : ℝ) (519173243101/1000000000000 : ℝ) (519173243107/1000000000000 : ℝ) (256632662607/500000000000 : ℝ) (513265325221/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4425/32768 : ℝ))) 2 (519173243101/1000000000000 : ℝ) (519173243107/1000000000000 : ℝ) (256632662607/500000000000 : ℝ) (513265325221/1000000000000 : ℝ) (516219284157/1000000000000 : ℝ) (129054821041/250000000000 : ℝ) (64526354047/125000000000 : ℝ) (516210832383/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4425/32768 : ℝ))) 3 (516219284157/1000000000000 : ℝ) (129054821041/250000000000 : ℝ) (64526354047/125000000000 : ℝ) (516210832383/1000000000000 : ℝ) (258107529133/500000000000 : ℝ) (258107529137/500000000000 : ℝ) (516215058249/1000000000000 : ℝ) (516215058257/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4425/32768 : ℝ))) 4 (258107529133/500000000000 : ℝ) (258107529137/500000000000 : ℝ) (516215058249/1000000000000 : ℝ) (516215058257/1000000000000 : ℝ) (516215058257/1000000000000 : ℝ) (258107529133/500000000000 : ℝ) (516215058257/1000000000000 : ℝ) (258107529133/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4425/32768 : ℝ))) 5 (516215058257/1000000000000 : ℝ) (258107529133/500000000000 : ℝ) (516215058257/1000000000000 : ℝ) (258107529133/500000000000 : ℝ) (516215058257/1000000000000 : ℝ) (258107529133/500000000000 : ℝ) (516215058257/1000000000000 : ℝ) (258107529133/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4425/32768 : ℝ))) 6 (516215058257/1000000000000 : ℝ) (258107529133/500000000000 : ℝ) (516215058257/1000000000000 : ℝ) (258107529133/500000000000 : ℝ) (516215058257/1000000000000 : ℝ) (258107529133/500000000000 : ℝ) (516215058257/1000000000000 : ℝ) (258107529133/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4425/32768 : ℝ))) 7 (516215058257/1000000000000 : ℝ) (258107529133/500000000000 : ℝ) (516215058257/1000000000000 : ℝ) (258107529133/500000000000 : ℝ) (516215058257/1000000000000 : ℝ) (258107529133/500000000000 : ℝ) (516215058257/1000000000000 : ℝ) (258107529133/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4425/32768 : ℝ)) hmem 8 (990423673179/1000000000000 : ℝ) (495211836591/500000000000 : ℝ) (990423673179/1000000000000 : ℝ) (495211836591/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4425/32768 : ℝ))) hcmem 8 (516215058257/1000000000000 : ℝ) (258107529133/500000000000 : ℝ) (516215058257/1000000000000 : ℝ) (258107529133/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4425/32768 : ℝ)) (990423673179/1000000000000 : ℝ) (495211836591/500000000000 : ℝ) (516215058257/1000000000000 : ℝ) (258107529133/500000000000 : ℝ) (818708941741/1000000000000 : ℝ) (409354470879/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0239_exp_lower
  have heNumeric : (2019016362941/1000000000000 : ℝ)/4 ≤ Real.exp (-10938942677503/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019016362941/1000000000000 : ℝ)/4 ≤ Real.exp ((8849/65536 : ℝ)-(409354470879/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8849/65536 : ℝ) (4425/32768 : ℝ) (409354470879/500000000000 : ℝ) (2019016362941/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0240; no trusted numerical premise.
theorem cover7_leaf0240_exp_radius : (249397799929925131/250000000000000000 : ℝ) ≤ Real.exp ((-8851/458752 : ℝ)/8) ∧ Real.exp ((-8851/458752 : ℝ)/8) ≤ (39903647988788021/40000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8851/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0240_exp_lower : (918089406233982127/1000000000000000000 : ℝ) ≤ Real.exp ((-5469472044303/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469472044303/8000000000000 : ℝ)/8) ≤ (57380587889623883/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469472044303/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0240_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (504754046219/250000000000 : ℝ) ≤ 4*Real.exp (4425/32768 : ℝ)*Real.exp (-mu (radius 7 (8851/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (504754046219/250000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8851/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0240_exp_radius
  have hrNumeric : (122611410293/125000000000 : ℝ) ≤ Real.exp (-8851/458752 : ℝ) ∧ Real.exp (-8851/458752 : ℝ) ≤ (196178256469/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (122611410293/125000000000 : ℝ) ≤ (radius 7 (8851/65536 : ℝ)) ∧ (radius 7 (8851/65536 : ℝ)) ≤ (196178256469/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8851/65536 : ℝ)) (122611410293/125000000000 : ℝ) (196178256469/200000000000 : ℝ) (3039947743/15625000000 : ℝ) (97278327779/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8851/65536 : ℝ)) (122611410293/125000000000 : ℝ) (196178256469/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8851/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (122611410293/125000000000 : ℝ) (196178256469/200000000000 : ℝ) (247611410293/250000000000 : ℝ) (990445641173/1000000000000 : ℝ) (495199778459/500000000000 : ℝ) (990399556919/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8851/65536 : ℝ)) 1 (247611410293/250000000000 : ℝ) (990445641173/1000000000000 : ℝ) (495199778459/500000000000 : ℝ) (990399556919/1000000000000 : ℝ) (198084519809/200000000000 : ℝ) (495211299523/500000000000 : ℝ) (123802824847/125000000000 : ℝ) (495211299389/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8851/65536 : ℝ)) 2 (198084519809/200000000000 : ℝ) (495211299523/500000000000 : ℝ) (123802824847/125000000000 : ℝ) (495211299389/500000000000 : ℝ) (99042259891/100000000000 : ℝ) (3868838277/3906250000 : ℝ) (99042259891/100000000000 : ℝ) (3868838277/3906250000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8851/65536 : ℝ)) 3 (99042259891/100000000000 : ℝ) (3868838277/3906250000 : ℝ) (99042259891/100000000000 : ℝ) (3868838277/3906250000 : ℝ) (99042259891/100000000000 : ℝ) (3868838277/3906250000 : ℝ) (99042259891/100000000000 : ℝ) (3868838277/3906250000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8851/65536 : ℝ)) 4 (99042259891/100000000000 : ℝ) (3868838277/3906250000 : ℝ) (99042259891/100000000000 : ℝ) (3868838277/3906250000 : ℝ) (99042259891/100000000000 : ℝ) (3868838277/3906250000 : ℝ) (99042259891/100000000000 : ℝ) (3868838277/3906250000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8851/65536 : ℝ)) 5 (99042259891/100000000000 : ℝ) (3868838277/3906250000 : ℝ) (99042259891/100000000000 : ℝ) (3868838277/3906250000 : ℝ) (99042259891/100000000000 : ℝ) (3868838277/3906250000 : ℝ) (99042259891/100000000000 : ℝ) (3868838277/3906250000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8851/65536 : ℝ)) 6 (99042259891/100000000000 : ℝ) (3868838277/3906250000 : ℝ) (99042259891/100000000000 : ℝ) (3868838277/3906250000 : ℝ) (99042259891/100000000000 : ℝ) (3868838277/3906250000 : ℝ) (99042259891/100000000000 : ℝ) (3868838277/3906250000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8851/65536 : ℝ)) 7 (99042259891/100000000000 : ℝ) (3868838277/3906250000 : ℝ) (99042259891/100000000000 : ℝ) (3868838277/3906250000 : ℝ) (99042259891/100000000000 : ℝ) (3868838277/3906250000 : ℝ) (99042259891/100000000000 : ℝ) (3868838277/3906250000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8851/65536 : ℝ))) (3039947743/15625000000 : ℝ) (97278327779/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8851/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (3039947743/15625000000 : ℝ) (97278327779/500000000000 : ℝ) (18664947743/31250000000 : ℝ) (597278327779/1000000000000 : ℝ) (441085768929/1000000000000 : ℝ) (441085768937/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8851/65536 : ℝ))) 1 (18664947743/31250000000 : ℝ) (597278327779/1000000000000 : ℝ) (441085768929/1000000000000 : ℝ) (441085768937/1000000000000 : ℝ) (16224439011/31250000000 : ℝ) (259591024179/500000000000 : ℝ) (102654950289/200000000000 : ℝ) (128318687863/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8851/65536 : ℝ))) 2 (16224439011/31250000000 : ℝ) (259591024179/500000000000 : ℝ) (102654950289/200000000000 : ℝ) (128318687863/250000000000 : ℝ) (258114199949/500000000000 : ℝ) (103245679981/200000000000 : ℝ) (516219950043/1000000000000 : ℝ) (10324399001/20000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8851/65536 : ℝ))) 3 (258114199949/500000000000 : ℝ) (103245679981/200000000000 : ℝ) (516219950043/1000000000000 : ℝ) (10324399001/20000000000 : ℝ) (51622417497/100000000000 : ℝ) (258112087489/500000000000 : ℝ) (516224174953/1000000000000 : ℝ) (516224174961/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8851/65536 : ℝ))) 4 (51622417497/100000000000 : ℝ) (258112087489/500000000000 : ℝ) (516224174953/1000000000000 : ℝ) (516224174961/1000000000000 : ℝ) (516224174961/1000000000000 : ℝ) (51622417497/100000000000 : ℝ) (516224174961/1000000000000 : ℝ) (51622417497/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8851/65536 : ℝ))) 5 (516224174961/1000000000000 : ℝ) (51622417497/100000000000 : ℝ) (516224174961/1000000000000 : ℝ) (51622417497/100000000000 : ℝ) (516224174961/1000000000000 : ℝ) (51622417497/100000000000 : ℝ) (516224174961/1000000000000 : ℝ) (51622417497/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8851/65536 : ℝ))) 6 (516224174961/1000000000000 : ℝ) (51622417497/100000000000 : ℝ) (516224174961/1000000000000 : ℝ) (51622417497/100000000000 : ℝ) (516224174961/1000000000000 : ℝ) (51622417497/100000000000 : ℝ) (516224174961/1000000000000 : ℝ) (51622417497/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8851/65536 : ℝ))) 7 (516224174961/1000000000000 : ℝ) (51622417497/100000000000 : ℝ) (516224174961/1000000000000 : ℝ) (51622417497/100000000000 : ℝ) (516224174961/1000000000000 : ℝ) (51622417497/100000000000 : ℝ) (516224174961/1000000000000 : ℝ) (51622417497/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8851/65536 : ℝ)) hmem 8 (99042259891/100000000000 : ℝ) (3868838277/3906250000 : ℝ) (99042259891/100000000000 : ℝ) (3868838277/3906250000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8851/65536 : ℝ))) hcmem 8 (516224174961/1000000000000 : ℝ) (51622417497/100000000000 : ℝ) (516224174961/1000000000000 : ℝ) (51622417497/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8851/65536 : ℝ)) (99042259891/100000000000 : ℝ) (3868838277/3906250000 : ℝ) (516224174961/1000000000000 : ℝ) (51622417497/100000000000 : ℝ) (32748971549/40000000000 : ℝ) (818724288741/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0240_exp_lower
  have heNumeric : (504754046219/250000000000 : ℝ)/4 ≤ Real.exp (-5469472044303/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (504754046219/250000000000 : ℝ)/4 ≤ Real.exp ((4425/32768 : ℝ)-(818724288741/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4425/32768 : ℝ) (8851/65536 : ℝ) (818724288741/1000000000000 : ℝ) (504754046219/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0241; no trusted numerical premise.
theorem cover7_leaf0241_exp_radius : (99759092789770743/100000000000000000 : ℝ) ≤ Real.exp ((-2213/114688 : ℝ)/8) ∧ Real.exp ((-2213/114688 : ℝ)/8) ≤ (997590927897707431/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2213/114688 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0241_exp_lower : (459044698122989971/500000000000000000 : ℝ) ≤ Real.exp ((-10938945481133/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938945481133/16000000000000 : ℝ)/8) ≤ (918089396245979943/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938945481133/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0241_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (403803201831/200000000000 : ℝ) ≤ 4*Real.exp (8851/65536 : ℝ)*Real.exp (-mu (radius 7 (2213/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (403803201831/200000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2213/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0241_exp_radius
  have hrNumeric : (980889144173/1000000000000 : ℝ) ≤ Real.exp (-2213/114688 : ℝ) ∧ Real.exp (-2213/114688 : ℝ) ≤ (490444572087/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980889144173/1000000000000 : ℝ) ≤ (radius 7 (2213/16384 : ℝ)) ∧ (radius 7 (2213/16384 : ℝ)) ≤ (490444572087/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2213/16384 : ℝ)) (980889144173/1000000000000 : ℝ) (490444572087/500000000000 : ℝ) (194567435203/1000000000000 : ℝ) (194567435209/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2213/16384 : ℝ)) (980889144173/1000000000000 : ℝ) (490444572087/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2213/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980889144173/1000000000000 : ℝ) (490444572087/500000000000 : ℝ) (495222286043/500000000000 : ℝ) (990444572087/1000000000000 : ℝ) (990398477469/1000000000000 : ℝ) (99039847747/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2213/16384 : ℝ)) 1 (495222286043/500000000000 : ℝ) (990444572087/1000000000000 : ℝ) (990398477469/1000000000000 : ℝ) (99039847747/100000000000 : ℝ) (990421524777/1000000000000 : ℝ) (990421524779/1000000000000 : ℝ) (990421524509/1000000000000 : ℝ) (990421524511/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2213/16384 : ℝ)) 2 (990421524777/1000000000000 : ℝ) (990421524779/1000000000000 : ℝ) (990421524509/1000000000000 : ℝ) (990421524511/1000000000000 : ℝ) (990421524643/1000000000000 : ℝ) (198084304929/200000000000 : ℝ) (495210762321/500000000000 : ℝ) (198084304929/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2213/16384 : ℝ)) 3 (990421524643/1000000000000 : ℝ) (198084304929/200000000000 : ℝ) (495210762321/500000000000 : ℝ) (198084304929/200000000000 : ℝ) (495210762321/500000000000 : ℝ) (198084304929/200000000000 : ℝ) (495210762321/500000000000 : ℝ) (198084304929/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2213/16384 : ℝ)) 4 (495210762321/500000000000 : ℝ) (198084304929/200000000000 : ℝ) (495210762321/500000000000 : ℝ) (198084304929/200000000000 : ℝ) (495210762321/500000000000 : ℝ) (198084304929/200000000000 : ℝ) (495210762321/500000000000 : ℝ) (198084304929/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2213/16384 : ℝ)) 5 (495210762321/500000000000 : ℝ) (198084304929/200000000000 : ℝ) (495210762321/500000000000 : ℝ) (198084304929/200000000000 : ℝ) (495210762321/500000000000 : ℝ) (198084304929/200000000000 : ℝ) (495210762321/500000000000 : ℝ) (198084304929/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2213/16384 : ℝ)) 6 (495210762321/500000000000 : ℝ) (198084304929/200000000000 : ℝ) (495210762321/500000000000 : ℝ) (198084304929/200000000000 : ℝ) (495210762321/500000000000 : ℝ) (198084304929/200000000000 : ℝ) (495210762321/500000000000 : ℝ) (198084304929/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2213/16384 : ℝ)) 7 (495210762321/500000000000 : ℝ) (198084304929/200000000000 : ℝ) (495210762321/500000000000 : ℝ) (198084304929/200000000000 : ℝ) (495210762321/500000000000 : ℝ) (198084304929/200000000000 : ℝ) (495210762321/500000000000 : ℝ) (198084304929/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2213/16384 : ℝ))) (194567435203/1000000000000 : ℝ) (194567435209/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2213/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (194567435203/1000000000000 : ℝ) (194567435209/1000000000000 : ℝ) (597283717601/1000000000000 : ℝ) (119456743521/200000000000 : ℝ) (44109798821/100000000000 : ℝ) (441097988217/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2213/16384 : ℝ))) 1 (597283717601/1000000000000 : ℝ) (119456743521/200000000000 : ℝ) (44109798821/100000000000 : ℝ) (441097988217/1000000000000 : ℝ) (103838170581/200000000000 : ℝ) (519190852911/1000000000000 : ℝ) (513284176869/1000000000000 : ℝ) (128321044219/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2213/16384 : ℝ))) 2 (103838170581/200000000000 : ℝ) (519190852911/1000000000000 : ℝ) (513284176869/1000000000000 : ℝ) (128321044219/250000000000 : ℝ) (516237514887/1000000000000 : ℝ) (258118757447/500000000000 : ℝ) (129057266739/250000000000 : ℝ) (129057266741/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2213/16384 : ℝ))) 3 (516237514887/1000000000000 : ℝ) (258118757447/500000000000 : ℝ) (129057266739/250000000000 : ℝ) (129057266741/250000000000 : ℝ) (516233290921/1000000000000 : ℝ) (516233290929/1000000000000 : ℝ) (64529161363/125000000000 : ℝ) (16132290341/31250000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2213/16384 : ℝ))) 4 (516233290921/1000000000000 : ℝ) (516233290929/1000000000000 : ℝ) (64529161363/125000000000 : ℝ) (16132290341/31250000000 : ℝ) (16132290341/31250000000 : ℝ) (516233290921/1000000000000 : ℝ) (16132290341/31250000000 : ℝ) (516233290921/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2213/16384 : ℝ))) 5 (16132290341/31250000000 : ℝ) (516233290921/1000000000000 : ℝ) (16132290341/31250000000 : ℝ) (516233290921/1000000000000 : ℝ) (16132290341/31250000000 : ℝ) (516233290921/1000000000000 : ℝ) (16132290341/31250000000 : ℝ) (516233290921/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2213/16384 : ℝ))) 6 (16132290341/31250000000 : ℝ) (516233290921/1000000000000 : ℝ) (16132290341/31250000000 : ℝ) (516233290921/1000000000000 : ℝ) (16132290341/31250000000 : ℝ) (516233290921/1000000000000 : ℝ) (16132290341/31250000000 : ℝ) (516233290921/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2213/16384 : ℝ))) 7 (16132290341/31250000000 : ℝ) (516233290921/1000000000000 : ℝ) (16132290341/31250000000 : ℝ) (516233290921/1000000000000 : ℝ) (16132290341/31250000000 : ℝ) (516233290921/1000000000000 : ℝ) (16132290341/31250000000 : ℝ) (516233290921/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2213/16384 : ℝ)) hmem 8 (495210762321/500000000000 : ℝ) (198084304929/200000000000 : ℝ) (495210762321/500000000000 : ℝ) (198084304929/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2213/16384 : ℝ))) hcmem 8 (16132290341/31250000000 : ℝ) (516233290921/1000000000000 : ℝ) (16132290341/31250000000 : ℝ) (516233290921/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2213/16384 : ℝ)) (495210762321/500000000000 : ℝ) (198084304929/200000000000 : ℝ) (16132290341/31250000000 : ℝ) (516233290921/1000000000000 : ℝ) (163747926909/200000000000 : ℝ) (818739634563/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0241_exp_lower
  have heNumeric : (403803201831/200000000000 : ℝ)/4 ≤ Real.exp (-10938945481133/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (403803201831/200000000000 : ℝ)/4 ≤ Real.exp ((8851/65536 : ℝ)-(818739634563/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8851/65536 : ℝ) (2213/16384 : ℝ) (818739634563/1000000000000 : ℝ) (403803201831/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0242; no trusted numerical premise.
theorem cover7_leaf0242_exp_radius : (997590656075788401/1000000000000000000 : ℝ) ≤ Real.exp ((-8853/458752 : ℝ)/8) ∧ Real.exp ((-8853/458752 : ℝ)/8) ≤ (498795328037894201/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8853/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0242_exp_lower : (918089386391445111/1000000000000000000 : ℝ) ≤ Real.exp ((-2734736713763/4000000000000 : ℝ)/8) ∧ Real.exp ((-2734736713763/4000000000000 : ℝ)/8) ≤ (114761173298930639/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2734736713763/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0242_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009507917891/500000000000 : ℝ) ≤ 4*Real.exp (2213/16384 : ℝ)*Real.exp (-mu (radius 7 (8853/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (1009507917891/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8853/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0242_exp_radius
  have hrNumeric : (980887006007/1000000000000 : ℝ) ≤ Real.exp (-8853/458752 : ℝ) ∧ Real.exp (-8853/458752 : ℝ) ≤ (122610875751/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980887006007/1000000000000 : ℝ) ≤ (radius 7 (8853/65536 : ℝ)) ∧ (radius 7 (8853/65536 : ℝ)) ≤ (122610875751/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8853/65536 : ℝ)) (980887006007/1000000000000 : ℝ) (122610875751/125000000000 : ℝ) (3040284597/15625000000 : ℝ) (97289107107/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8853/65536 : ℝ)) (980887006007/1000000000000 : ℝ) (122610875751/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8853/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980887006007/1000000000000 : ℝ) (122610875751/125000000000 : ℝ) (990443503003/1000000000000 : ℝ) (247610875751/250000000000 : ℝ) (990397398021/1000000000000 : ℝ) (495198699011/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8853/65536 : ℝ)) 1 (990443503003/1000000000000 : ℝ) (247610875751/250000000000 : ℝ) (990397398021/1000000000000 : ℝ) (495198699011/500000000000 : ℝ) (61901278157/62500000000 : ℝ) (990420450513/1000000000000 : ℝ) (990420450243/1000000000000 : ℝ) (198084090049/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8853/65536 : ℝ)) 2 (61901278157/62500000000 : ℝ) (990420450513/1000000000000 : ℝ) (990420450243/1000000000000 : ℝ) (198084090049/200000000000 : ℝ) (990420450377/1000000000000 : ℝ) (990420450379/1000000000000 : ℝ) (990420450377/1000000000000 : ℝ) (990420450379/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8853/65536 : ℝ)) 3 (990420450377/1000000000000 : ℝ) (990420450379/1000000000000 : ℝ) (990420450377/1000000000000 : ℝ) (990420450379/1000000000000 : ℝ) (990420450377/1000000000000 : ℝ) (990420450379/1000000000000 : ℝ) (990420450377/1000000000000 : ℝ) (990420450379/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8853/65536 : ℝ)) 4 (990420450377/1000000000000 : ℝ) (990420450379/1000000000000 : ℝ) (990420450377/1000000000000 : ℝ) (990420450379/1000000000000 : ℝ) (990420450377/1000000000000 : ℝ) (990420450379/1000000000000 : ℝ) (990420450377/1000000000000 : ℝ) (990420450379/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8853/65536 : ℝ)) 5 (990420450377/1000000000000 : ℝ) (990420450379/1000000000000 : ℝ) (990420450377/1000000000000 : ℝ) (990420450379/1000000000000 : ℝ) (990420450377/1000000000000 : ℝ) (990420450379/1000000000000 : ℝ) (990420450377/1000000000000 : ℝ) (990420450379/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8853/65536 : ℝ)) 6 (990420450377/1000000000000 : ℝ) (990420450379/1000000000000 : ℝ) (990420450377/1000000000000 : ℝ) (990420450379/1000000000000 : ℝ) (990420450377/1000000000000 : ℝ) (990420450379/1000000000000 : ℝ) (990420450377/1000000000000 : ℝ) (990420450379/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8853/65536 : ℝ)) 7 (990420450377/1000000000000 : ℝ) (990420450379/1000000000000 : ℝ) (990420450377/1000000000000 : ℝ) (990420450379/1000000000000 : ℝ) (990420450377/1000000000000 : ℝ) (990420450379/1000000000000 : ℝ) (990420450377/1000000000000 : ℝ) (990420450379/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8853/65536 : ℝ))) (3040284597/15625000000 : ℝ) (97289107107/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8853/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (3040284597/15625000000 : ℝ) (97289107107/500000000000 : ℝ) (18665284597/31250000000 : ℝ) (597289107107/1000000000000 : ℝ) (22055510321/50000000000 : ℝ) (441110206427/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8853/65536 : ℝ))) 1 (18665284597/31250000000 : ℝ) (597289107107/1000000000000 : ℝ) (22055510321/50000000000 : ℝ) (441110206427/1000000000000 : ℝ) (259599828381/500000000000 : ℝ) (519199656767/1000000000000 : ℝ) (256646800743/500000000000 : ℝ) (128323400373/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8853/65536 : ℝ))) 2 (259599828381/500000000000 : ℝ) (519199656767/1000000000000 : ℝ) (256646800743/500000000000 : ℝ) (128323400373/250000000000 : ℝ) (129061657281/250000000000 : ℝ) (51624662913/100000000000 : ℝ) (258119091559/500000000000 : ℝ) (825981093/1600000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8853/65536 : ℝ))) 3 (129061657281/250000000000 : ℝ) (51624662913/100000000000 : ℝ) (258119091559/500000000000 : ℝ) (825981093/1600000000 : ℝ) (516242406121/1000000000000 : ℝ) (32265150383/62500000000 : ℝ) (516242406103/1000000000000 : ℝ) (516242406111/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8853/65536 : ℝ))) 4 (516242406121/1000000000000 : ℝ) (32265150383/62500000000 : ℝ) (516242406103/1000000000000 : ℝ) (516242406111/1000000000000 : ℝ) (16132575191/31250000000 : ℝ) (12906060153/25000000000 : ℝ) (516242406111/1000000000000 : ℝ) (12906060153/25000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8853/65536 : ℝ))) 5 (16132575191/31250000000 : ℝ) (12906060153/25000000000 : ℝ) (516242406111/1000000000000 : ℝ) (12906060153/25000000000 : ℝ) (516242406111/1000000000000 : ℝ) (12906060153/25000000000 : ℝ) (516242406111/1000000000000 : ℝ) (12906060153/25000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8853/65536 : ℝ))) 6 (516242406111/1000000000000 : ℝ) (12906060153/25000000000 : ℝ) (516242406111/1000000000000 : ℝ) (12906060153/25000000000 : ℝ) (516242406111/1000000000000 : ℝ) (12906060153/25000000000 : ℝ) (516242406111/1000000000000 : ℝ) (12906060153/25000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8853/65536 : ℝ))) 7 (516242406111/1000000000000 : ℝ) (12906060153/25000000000 : ℝ) (516242406111/1000000000000 : ℝ) (12906060153/25000000000 : ℝ) (516242406111/1000000000000 : ℝ) (12906060153/25000000000 : ℝ) (516242406111/1000000000000 : ℝ) (12906060153/25000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8853/65536 : ℝ)) hmem 8 (990420450377/1000000000000 : ℝ) (990420450379/1000000000000 : ℝ) (990420450377/1000000000000 : ℝ) (990420450379/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8853/65536 : ℝ))) hcmem 8 (516242406111/1000000000000 : ℝ) (12906060153/25000000000 : ℝ) (516242406111/1000000000000 : ℝ) (12906060153/25000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8853/65536 : ℝ)) (990420450377/1000000000000 : ℝ) (990420450379/1000000000000 : ℝ) (516242406111/1000000000000 : ℝ) (12906060153/25000000000 : ℝ) (163750995841/200000000000 : ℝ) (409377489611/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0242_exp_lower
  have heNumeric : (1009507917891/500000000000 : ℝ)/4 ≤ Real.exp (-2734736713763/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009507917891/500000000000 : ℝ)/4 ≤ Real.exp ((2213/16384 : ℝ)-(409377489611/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2213/16384 : ℝ) (8853/65536 : ℝ) (409377489611/500000000000 : ℝ) (1009507917891/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0243; no trusted numerical premise.
theorem cover7_leaf0243_exp_radius : (997590384253943437/1000000000000000000 : ℝ) ≤ Real.exp ((-4427/229376 : ℝ)/8) ∧ Real.exp ((-4427/229376 : ℝ)/8) ≤ (498795192126971719/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4427/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0243_exp_lower : (918089376668885733/1000000000000000000 : ℝ) ≤ Real.exp ((-10938948210571/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938948210571/16000000000000 : ℝ)/8) ≤ (459044688334442867/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938948210571/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0243_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019015664731/1000000000000 : ℝ) ≤ 4*Real.exp (8853/65536 : ℝ)*Real.exp (-mu (radius 7 (4427/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (2019015664731/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4427/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0243_exp_radius
  have hrNumeric : (196176973569/200000000000 : ℝ) ≤ Real.exp (-4427/229376 : ℝ) ∧ Real.exp (-4427/229376 : ℝ) ≤ (490442433923/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196176973569/200000000000 : ℝ) ≤ (radius 7 (4427/32768 : ℝ)) ∧ (radius 7 (4427/32768 : ℝ)) ≤ (490442433923/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4427/32768 : ℝ)) (196176973569/200000000000 : ℝ) (490442433923/500000000000 : ℝ) (194588992573/1000000000000 : ℝ) (194588992579/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4427/32768 : ℝ)) (196176973569/200000000000 : ℝ) (490442433923/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4427/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196176973569/200000000000 : ℝ) (490442433923/500000000000 : ℝ) (495221216961/500000000000 : ℝ) (990442433923/1000000000000 : ℝ) (495198159287/500000000000 : ℝ) (39615852743/40000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4427/32768 : ℝ)) 1 (495221216961/500000000000 : ℝ) (990442433923/1000000000000 : ℝ) (495198159287/500000000000 : ℝ) (39615852743/40000000000 : ℝ) (123802422031/125000000000 : ℝ) (990419376249/1000000000000 : ℝ) (990419375979/1000000000000 : ℝ) (990419375981/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4427/32768 : ℝ)) 2 (123802422031/125000000000 : ℝ) (990419376249/1000000000000 : ℝ) (990419375979/1000000000000 : ℝ) (990419375981/1000000000000 : ℝ) (990419376113/1000000000000 : ℝ) (198083875223/200000000000 : ℝ) (990419376113/1000000000000 : ℝ) (198083875223/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4427/32768 : ℝ)) 3 (990419376113/1000000000000 : ℝ) (198083875223/200000000000 : ℝ) (990419376113/1000000000000 : ℝ) (198083875223/200000000000 : ℝ) (990419376113/1000000000000 : ℝ) (198083875223/200000000000 : ℝ) (990419376113/1000000000000 : ℝ) (198083875223/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4427/32768 : ℝ)) 4 (990419376113/1000000000000 : ℝ) (198083875223/200000000000 : ℝ) (990419376113/1000000000000 : ℝ) (198083875223/200000000000 : ℝ) (990419376113/1000000000000 : ℝ) (198083875223/200000000000 : ℝ) (990419376113/1000000000000 : ℝ) (198083875223/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4427/32768 : ℝ)) 5 (990419376113/1000000000000 : ℝ) (198083875223/200000000000 : ℝ) (990419376113/1000000000000 : ℝ) (198083875223/200000000000 : ℝ) (990419376113/1000000000000 : ℝ) (198083875223/200000000000 : ℝ) (990419376113/1000000000000 : ℝ) (198083875223/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4427/32768 : ℝ)) 6 (990419376113/1000000000000 : ℝ) (198083875223/200000000000 : ℝ) (990419376113/1000000000000 : ℝ) (198083875223/200000000000 : ℝ) (990419376113/1000000000000 : ℝ) (198083875223/200000000000 : ℝ) (990419376113/1000000000000 : ℝ) (198083875223/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4427/32768 : ℝ)) 7 (990419376113/1000000000000 : ℝ) (198083875223/200000000000 : ℝ) (990419376113/1000000000000 : ℝ) (198083875223/200000000000 : ℝ) (990419376113/1000000000000 : ℝ) (198083875223/200000000000 : ℝ) (990419376113/1000000000000 : ℝ) (198083875223/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4427/32768 : ℝ))) (194588992573/1000000000000 : ℝ) (194588992579/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4427/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (194588992573/1000000000000 : ℝ) (194588992579/1000000000000 : ℝ) (298647248143/500000000000 : ℝ) (59729449629/100000000000 : ℝ) (220561211783/500000000000 : ℝ) (220561211787/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4427/32768 : ℝ))) 1 (298647248143/500000000000 : ℝ) (59729449629/100000000000 : ℝ) (220561211783/500000000000 : ℝ) (220561211787/500000000000 : ℝ) (259604229963/500000000000 : ℝ) (129802114983/250000000000 : ℝ) (256651512651/500000000000 : ℝ) (513303025309/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4427/32768 : ℝ))) 2 (259604229963/500000000000 : ℝ) (129802114983/250000000000 : ℝ) (256651512651/500000000000 : ℝ) (513303025309/1000000000000 : ℝ) (258127871307/500000000000 : ℝ) (516255742621/1000000000000 : ℝ) (129061824633/250000000000 : ℝ) (25812364927/50000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4427/32768 : ℝ))) 3 (258127871307/500000000000 : ℝ) (516255742621/1000000000000 : ℝ) (129061824633/250000000000 : ℝ) (25812364927/50000000000 : ℝ) (516251520573/1000000000000 : ℝ) (516251520581/1000000000000 : ℝ) (103250304111/200000000000 : ℝ) (129062880141/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4427/32768 : ℝ))) 4 (516251520573/1000000000000 : ℝ) (516251520581/1000000000000 : ℝ) (103250304111/200000000000 : ℝ) (129062880141/250000000000 : ℝ) (129062880141/250000000000 : ℝ) (516251520573/1000000000000 : ℝ) (516251520563/1000000000000 : ℝ) (516251520573/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4427/32768 : ℝ))) 5 (129062880141/250000000000 : ℝ) (516251520573/1000000000000 : ℝ) (516251520563/1000000000000 : ℝ) (516251520573/1000000000000 : ℝ) (516251520563/1000000000000 : ℝ) (516251520573/1000000000000 : ℝ) (516251520563/1000000000000 : ℝ) (516251520573/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4427/32768 : ℝ))) 6 (516251520563/1000000000000 : ℝ) (516251520573/1000000000000 : ℝ) (516251520563/1000000000000 : ℝ) (516251520573/1000000000000 : ℝ) (516251520563/1000000000000 : ℝ) (516251520573/1000000000000 : ℝ) (516251520563/1000000000000 : ℝ) (516251520573/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4427/32768 : ℝ))) 7 (516251520563/1000000000000 : ℝ) (516251520573/1000000000000 : ℝ) (516251520563/1000000000000 : ℝ) (516251520573/1000000000000 : ℝ) (516251520563/1000000000000 : ℝ) (516251520573/1000000000000 : ℝ) (516251520563/1000000000000 : ℝ) (516251520573/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4427/32768 : ℝ)) hmem 8 (990419376113/1000000000000 : ℝ) (198083875223/200000000000 : ℝ) (990419376113/1000000000000 : ℝ) (198083875223/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4427/32768 : ℝ))) hcmem 8 (516251520563/1000000000000 : ℝ) (516251520573/1000000000000 : ℝ) (516251520563/1000000000000 : ℝ) (516251520573/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4427/32768 : ℝ)) (990419376113/1000000000000 : ℝ) (198083875223/200000000000 : ℝ) (516251520563/1000000000000 : ℝ) (516251520573/1000000000000 : ℝ) (102346290339/125000000000 : ℝ) (818770322731/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0243_exp_lower
  have heNumeric : (2019015664731/1000000000000 : ℝ)/4 ≤ Real.exp (-10938948210571/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019015664731/1000000000000 : ℝ)/4 ≤ Real.exp ((8853/65536 : ℝ)-(818770322731/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8853/65536 : ℝ) (4427/32768 : ℝ) (818770322731/1000000000000 : ℝ) (2019015664731/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0244; no trusted numerical premise.
theorem cover7_leaf0244_exp_radius : (49879505621608627/50000000000000000 : ℝ) ≤ Real.exp ((-1265/65536 : ℝ)/8) ∧ Real.exp ((-1265/65536 : ℝ)/8) ≤ (997590112432172541/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1265/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0244_exp_lower : (459044683540011611/500000000000000000 : ℝ) ≤ Real.exp ((-218778990949/320000000000 : ℝ)/8) ∧ Real.exp ((-218778990949/320000000000 : ℝ)/8) ≤ (918089367080023223/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-218778990949/320000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0244_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (63094234251/31250000000 : ℝ) ≤ 4*Real.exp (4427/32768 : ℝ)*Real.exp (-mu (radius 7 (8855/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (63094234251/31250000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8855/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0244_exp_radius
  have hrNumeric : (122610341211/125000000000 : ℝ) ≤ Real.exp (-1265/65536 : ℝ) ∧ Real.exp (-1265/65536 : ℝ) ≤ (980882729689/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (122610341211/125000000000 : ℝ) ≤ (radius 7 (8855/65536 : ℝ)) ∧ (radius 7 (8855/65536 : ℝ)) ≤ (980882729689/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8855/65536 : ℝ)) (122610341211/125000000000 : ℝ) (980882729689/1000000000000 : ℝ) (48649942573/250000000000 : ℝ) (97299885149/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8855/65536 : ℝ)) (122610341211/125000000000 : ℝ) (980882729689/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8855/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (122610341211/125000000000 : ℝ) (980882729689/1000000000000 : ℝ) (247610341211/250000000000 : ℝ) (198088272969/200000000000 : ℝ) (123799404891/125000000000 : ℝ) (990395239129/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8855/65536 : ℝ)) 1 (247610341211/250000000000 : ℝ) (198088272969/200000000000 : ℝ) (123799404891/125000000000 : ℝ) (990395239129/1000000000000 : ℝ) (495209150993/500000000000 : ℝ) (990418301987/1000000000000 : ℝ) (990418301717/1000000000000 : ℝ) (990418301719/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8855/65536 : ℝ)) 2 (495209150993/500000000000 : ℝ) (990418301987/1000000000000 : ℝ) (990418301717/1000000000000 : ℝ) (990418301719/1000000000000 : ℝ) (990418301851/1000000000000 : ℝ) (990418301853/1000000000000 : ℝ) (990418301851/1000000000000 : ℝ) (990418301853/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8855/65536 : ℝ)) 3 (990418301851/1000000000000 : ℝ) (990418301853/1000000000000 : ℝ) (990418301851/1000000000000 : ℝ) (990418301853/1000000000000 : ℝ) (990418301851/1000000000000 : ℝ) (990418301853/1000000000000 : ℝ) (990418301851/1000000000000 : ℝ) (990418301853/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8855/65536 : ℝ)) 4 (990418301851/1000000000000 : ℝ) (990418301853/1000000000000 : ℝ) (990418301851/1000000000000 : ℝ) (990418301853/1000000000000 : ℝ) (990418301851/1000000000000 : ℝ) (990418301853/1000000000000 : ℝ) (990418301851/1000000000000 : ℝ) (990418301853/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8855/65536 : ℝ)) 5 (990418301851/1000000000000 : ℝ) (990418301853/1000000000000 : ℝ) (990418301851/1000000000000 : ℝ) (990418301853/1000000000000 : ℝ) (990418301851/1000000000000 : ℝ) (990418301853/1000000000000 : ℝ) (990418301851/1000000000000 : ℝ) (990418301853/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8855/65536 : ℝ)) 6 (990418301851/1000000000000 : ℝ) (990418301853/1000000000000 : ℝ) (990418301851/1000000000000 : ℝ) (990418301853/1000000000000 : ℝ) (990418301851/1000000000000 : ℝ) (990418301853/1000000000000 : ℝ) (990418301851/1000000000000 : ℝ) (990418301853/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8855/65536 : ℝ)) 7 (990418301851/1000000000000 : ℝ) (990418301853/1000000000000 : ℝ) (990418301851/1000000000000 : ℝ) (990418301853/1000000000000 : ℝ) (990418301851/1000000000000 : ℝ) (990418301853/1000000000000 : ℝ) (990418301851/1000000000000 : ℝ) (990418301853/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8855/65536 : ℝ))) (48649942573/250000000000 : ℝ) (97299885149/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8855/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (48649942573/250000000000 : ℝ) (97299885149/500000000000 : ℝ) (298649942573/500000000000 : ℝ) (597299885149/1000000000000 : ℝ) (441134639641/1000000000000 : ℝ) (441134639649/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8855/65536 : ℝ))) 1 (298649942573/500000000000 : ℝ) (597299885149/1000000000000 : ℝ) (441134639641/1000000000000 : ℝ) (441134639649/1000000000000 : ℝ) (519217262393/1000000000000 : ℝ) (519217262399/1000000000000 : ℝ) (513312448311/1000000000000 : ℝ) (256656224159/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8855/65536 : ℝ))) 2 (519217262393/1000000000000 : ℝ) (519217262399/1000000000000 : ℝ) (513312448311/1000000000000 : ℝ) (256656224159/500000000000 : ℝ) (64533106919/125000000000 : ℝ) (516264855359/1000000000000 : ℝ) (258128206597/500000000000 : ℝ) (516256413201/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8855/65536 : ℝ))) 3 (64533106919/125000000000 : ℝ) (516264855359/1000000000000 : ℝ) (258128206597/500000000000 : ℝ) (516256413201/1000000000000 : ℝ) (516260634273/1000000000000 : ℝ) (12906515857/25000000000 : ℝ) (103252126851/200000000000 : ℝ) (516260634263/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8855/65536 : ℝ))) 4 (516260634273/1000000000000 : ℝ) (12906515857/25000000000 : ℝ) (103252126851/200000000000 : ℝ) (516260634263/1000000000000 : ℝ) (64532579283/125000000000 : ℝ) (16133144821/31250000000 : ℝ) (516260634263/1000000000000 : ℝ) (16133144821/31250000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8855/65536 : ℝ))) 5 (64532579283/125000000000 : ℝ) (16133144821/31250000000 : ℝ) (516260634263/1000000000000 : ℝ) (16133144821/31250000000 : ℝ) (516260634263/1000000000000 : ℝ) (16133144821/31250000000 : ℝ) (516260634263/1000000000000 : ℝ) (16133144821/31250000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8855/65536 : ℝ))) 6 (516260634263/1000000000000 : ℝ) (16133144821/31250000000 : ℝ) (516260634263/1000000000000 : ℝ) (16133144821/31250000000 : ℝ) (516260634263/1000000000000 : ℝ) (16133144821/31250000000 : ℝ) (516260634263/1000000000000 : ℝ) (16133144821/31250000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8855/65536 : ℝ))) 7 (516260634263/1000000000000 : ℝ) (16133144821/31250000000 : ℝ) (516260634263/1000000000000 : ℝ) (16133144821/31250000000 : ℝ) (516260634263/1000000000000 : ℝ) (16133144821/31250000000 : ℝ) (516260634263/1000000000000 : ℝ) (16133144821/31250000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8855/65536 : ℝ)) hmem 8 (990418301851/1000000000000 : ℝ) (990418301853/1000000000000 : ℝ) (990418301851/1000000000000 : ℝ) (990418301853/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8855/65536 : ℝ))) hcmem 8 (516260634263/1000000000000 : ℝ) (16133144821/31250000000 : ℝ) (516260634263/1000000000000 : ℝ) (16133144821/31250000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8855/65536 : ℝ)) (990418301851/1000000000000 : ℝ) (990418301853/1000000000000 : ℝ) (516260634263/1000000000000 : ℝ) (16133144821/31250000000 : ℝ) (409392832529/500000000000 : ℝ) (32751426603/40000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0244_exp_lower
  have heNumeric : (63094234251/31250000000 : ℝ)/4 ≤ Real.exp (-218778990949/320000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (63094234251/31250000000 : ℝ)/4 ≤ Real.exp ((4427/32768 : ℝ)-(32751426603/40000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4427/32768 : ℝ) (8855/65536 : ℝ) (32751426603/40000000000 : ℝ) (63094234251/31250000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0245; no trusted numerical premise.
theorem cover7_leaf0245_exp_radius : (997589840610475707/1000000000000000000 : ℝ) ≤ Real.exp ((-1107/57344 : ℝ)/8) ∧ Real.exp ((-1107/57344 : ℝ)/8) ≤ (249397460152618927/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1107/57344 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0245_exp_lower : (229522339405956181/250000000000000000 : ℝ) ≤ Real.exp ((-10938950865833/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938950865833/16000000000000 : ℝ)/8) ≤ (36723574304952989/40000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938950865833/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0245_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (504753832417/250000000000 : ℝ) ≤ 4*Real.exp (8855/65536 : ℝ)*Real.exp (-mu (radius 7 (1107/8192 : ℝ))) ∧ (2019/1000 : ℝ) < (504753832417/250000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (1107/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0245_exp_radius
  have hrNumeric : (61305036971/62500000000 : ℝ) ≤ Real.exp (-1107/57344 : ℝ) ∧ Real.exp (-1107/57344 : ℝ) ≤ (980880591537/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (61305036971/62500000000 : ℝ) ≤ (radius 7 (1107/8192 : ℝ)) ∧ (radius 7 (1107/8192 : ℝ)) ≤ (980880591537/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (1107/8192 : ℝ)) (61305036971/62500000000 : ℝ) (980880591537/1000000000000 : ℝ) (38922109473/200000000000 : ℝ) (194610547371/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (1107/8192 : ℝ)) (61305036971/62500000000 : ℝ) (980880591537/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (1107/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (61305036971/62500000000 : ℝ) (980880591537/1000000000000 : ℝ) (123805036971/125000000000 : ℝ) (990440295769/1000000000000 : ℝ) (990394159683/1000000000000 : ℝ) (198078831937/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (1107/8192 : ℝ)) 1 (123805036971/125000000000 : ℝ) (990440295769/1000000000000 : ℝ) (990394159683/1000000000000 : ℝ) (198078831937/200000000000 : ℝ) (39616689109/40000000000 : ℝ) (990417227727/1000000000000 : ℝ) (15475269179/15625000000 : ℝ) (990417227459/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (1107/8192 : ℝ)) 2 (39616689109/40000000000 : ℝ) (990417227727/1000000000000 : ℝ) (15475269179/15625000000 : ℝ) (990417227459/1000000000000 : ℝ) (99041722759/100000000000 : ℝ) (990417227593/1000000000000 : ℝ) (99041722759/100000000000 : ℝ) (990417227593/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (1107/8192 : ℝ)) 3 (99041722759/100000000000 : ℝ) (990417227593/1000000000000 : ℝ) (99041722759/100000000000 : ℝ) (990417227593/1000000000000 : ℝ) (99041722759/100000000000 : ℝ) (990417227593/1000000000000 : ℝ) (99041722759/100000000000 : ℝ) (990417227593/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (1107/8192 : ℝ)) 4 (99041722759/100000000000 : ℝ) (990417227593/1000000000000 : ℝ) (99041722759/100000000000 : ℝ) (990417227593/1000000000000 : ℝ) (99041722759/100000000000 : ℝ) (990417227593/1000000000000 : ℝ) (99041722759/100000000000 : ℝ) (990417227593/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (1107/8192 : ℝ)) 5 (99041722759/100000000000 : ℝ) (990417227593/1000000000000 : ℝ) (99041722759/100000000000 : ℝ) (990417227593/1000000000000 : ℝ) (99041722759/100000000000 : ℝ) (990417227593/1000000000000 : ℝ) (99041722759/100000000000 : ℝ) (990417227593/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (1107/8192 : ℝ)) 6 (99041722759/100000000000 : ℝ) (990417227593/1000000000000 : ℝ) (99041722759/100000000000 : ℝ) (990417227593/1000000000000 : ℝ) (99041722759/100000000000 : ℝ) (990417227593/1000000000000 : ℝ) (99041722759/100000000000 : ℝ) (990417227593/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (1107/8192 : ℝ)) 7 (99041722759/100000000000 : ℝ) (990417227593/1000000000000 : ℝ) (99041722759/100000000000 : ℝ) (990417227593/1000000000000 : ℝ) (99041722759/100000000000 : ℝ) (990417227593/1000000000000 : ℝ) (99041722759/100000000000 : ℝ) (990417227593/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (1107/8192 : ℝ))) (38922109473/200000000000 : ℝ) (194610547371/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (1107/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (38922109473/200000000000 : ℝ) (194610547371/1000000000000 : ℝ) (298652636841/500000000000 : ℝ) (298652636843/500000000000 : ℝ) (441146854647/1000000000000 : ℝ) (220573427327/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (1107/8192 : ℝ))) 1 (298652636841/500000000000 : ℝ) (298652636843/500000000000 : ℝ) (441146854647/1000000000000 : ℝ) (220573427327/500000000000 : ℝ) (129806516041/250000000000 : ℝ) (51922606417/100000000000 : ℝ) (256660935257/500000000000 : ℝ) (513321870521/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (1107/8192 : ℝ))) 2 (129806516041/250000000000 : ℝ) (51922606417/100000000000 : ℝ) (256660935257/500000000000 : ℝ) (513321870521/1000000000000 : ℝ) (516273967339/1000000000000 : ℝ) (258136983673/500000000000 : ℝ) (8066648861/15625000000 : ℝ) (516265527111/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (1107/8192 : ℝ))) 3 (516273967339/1000000000000 : ℝ) (258136983673/500000000000 : ℝ) (8066648861/15625000000 : ℝ) (516265527111/1000000000000 : ℝ) (516269747221/1000000000000 : ℝ) (516269747229/1000000000000 : ℝ) (129067436801/250000000000 : ℝ) (129067436803/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (1107/8192 : ℝ))) 4 (516269747221/1000000000000 : ℝ) (516269747229/1000000000000 : ℝ) (129067436801/250000000000 : ℝ) (129067436803/250000000000 : ℝ) (129067436803/250000000000 : ℝ) (516269747221/1000000000000 : ℝ) (129067436803/250000000000 : ℝ) (516269747221/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (1107/8192 : ℝ))) 5 (129067436803/250000000000 : ℝ) (516269747221/1000000000000 : ℝ) (129067436803/250000000000 : ℝ) (516269747221/1000000000000 : ℝ) (129067436803/250000000000 : ℝ) (516269747221/1000000000000 : ℝ) (129067436803/250000000000 : ℝ) (516269747221/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (1107/8192 : ℝ))) 6 (129067436803/250000000000 : ℝ) (516269747221/1000000000000 : ℝ) (129067436803/250000000000 : ℝ) (516269747221/1000000000000 : ℝ) (129067436803/250000000000 : ℝ) (516269747221/1000000000000 : ℝ) (129067436803/250000000000 : ℝ) (516269747221/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (1107/8192 : ℝ))) 7 (129067436803/250000000000 : ℝ) (516269747221/1000000000000 : ℝ) (129067436803/250000000000 : ℝ) (516269747221/1000000000000 : ℝ) (129067436803/250000000000 : ℝ) (516269747221/1000000000000 : ℝ) (129067436803/250000000000 : ℝ) (516269747221/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (1107/8192 : ℝ)) hmem 8 (99041722759/100000000000 : ℝ) (990417227593/1000000000000 : ℝ) (99041722759/100000000000 : ℝ) (990417227593/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (1107/8192 : ℝ))) hcmem 8 (129067436803/250000000000 : ℝ) (516269747221/1000000000000 : ℝ) (129067436803/250000000000 : ℝ) (516269747221/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (1107/8192 : ℝ)) (99041722759/100000000000 : ℝ) (990417227593/1000000000000 : ℝ) (129067436803/250000000000 : ℝ) (516269747221/1000000000000 : ℝ) (163760201249/200000000000 : ℝ) (818801006263/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0245_exp_lower
  have heNumeric : (504753832417/250000000000 : ℝ)/4 ≤ Real.exp (-10938950865833/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (504753832417/250000000000 : ℝ)/4 ≤ Real.exp ((8855/65536 : ℝ)-(818801006263/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8855/65536 : ℝ) (1107/8192 : ℝ) (818801006263/1000000000000 : ℝ) (504753832417/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0246; no trusted numerical premise.
theorem cover7_leaf0246_exp_radius : (997589568788852941/1000000000000000000 : ℝ) ≤ Real.exp ((-8857/458752 : ℝ)/8) ∧ Real.exp ((-8857/458752 : ℝ)/8) ≤ (498794784394426471/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8857/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0246_exp_lower : (918089348300290233/1000000000000000000 : ℝ) ≤ Real.exp ((-273473804143/400000000000 : ℝ)/8) ∧ Real.exp ((-273473804143/400000000000 : ℝ)/8) ≤ (459044674150145117/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-273473804143/400000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0246_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019015165637/1000000000000 : ℝ) ≤ 4*Real.exp (1107/8192 : ℝ)*Real.exp (-mu (radius 7 (8857/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (2019015165637/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8857/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0246_exp_radius
  have hrNumeric : (245219613347/250000000000 : ℝ) ≤ Real.exp (-8857/458752 : ℝ) ∧ Real.exp (-8857/458752 : ℝ) ≤ (980878453389/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (245219613347/250000000000 : ℝ) ≤ (radius 7 (8857/65536 : ℝ)) ∧ (radius 7 (8857/65536 : ℝ)) ≤ (980878453389/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8857/65536 : ℝ)) (245219613347/250000000000 : ℝ) (980878453389/1000000000000 : ℝ) (97310661899/500000000000 : ℝ) (48655330951/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8857/65536 : ℝ)) (245219613347/250000000000 : ℝ) (980878453389/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8857/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (245219613347/250000000000 : ℝ) (980878453389/1000000000000 : ℝ) (495219613347/500000000000 : ℝ) (198087845339/200000000000 : ℝ) (12379913503/12500000000 : ℝ) (990393080241/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8857/65536 : ℝ)) 1 (495219613347/500000000000 : ℝ) (198087845339/200000000000 : ℝ) (12379913503/12500000000 : ℝ) (990393080241/1000000000000 : ℝ) (990416153467/1000000000000 : ℝ) (247604038367/250000000000 : ℝ) (495208076599/500000000000 : ℝ) (2476040383/2500000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8857/65536 : ℝ)) 2 (990416153467/1000000000000 : ℝ) (247604038367/250000000000 : ℝ) (495208076599/500000000000 : ℝ) (2476040383/2500000000 : ℝ) (247604038333/250000000000 : ℝ) (495208076667/500000000000 : ℝ) (247604038333/250000000000 : ℝ) (495208076667/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8857/65536 : ℝ)) 3 (247604038333/250000000000 : ℝ) (495208076667/500000000000 : ℝ) (247604038333/250000000000 : ℝ) (495208076667/500000000000 : ℝ) (247604038333/250000000000 : ℝ) (495208076667/500000000000 : ℝ) (247604038333/250000000000 : ℝ) (495208076667/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8857/65536 : ℝ)) 4 (247604038333/250000000000 : ℝ) (495208076667/500000000000 : ℝ) (247604038333/250000000000 : ℝ) (495208076667/500000000000 : ℝ) (247604038333/250000000000 : ℝ) (495208076667/500000000000 : ℝ) (247604038333/250000000000 : ℝ) (495208076667/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8857/65536 : ℝ)) 5 (247604038333/250000000000 : ℝ) (495208076667/500000000000 : ℝ) (247604038333/250000000000 : ℝ) (495208076667/500000000000 : ℝ) (247604038333/250000000000 : ℝ) (495208076667/500000000000 : ℝ) (247604038333/250000000000 : ℝ) (495208076667/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8857/65536 : ℝ)) 6 (247604038333/250000000000 : ℝ) (495208076667/500000000000 : ℝ) (247604038333/250000000000 : ℝ) (495208076667/500000000000 : ℝ) (247604038333/250000000000 : ℝ) (495208076667/500000000000 : ℝ) (247604038333/250000000000 : ℝ) (495208076667/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8857/65536 : ℝ)) 7 (247604038333/250000000000 : ℝ) (495208076667/500000000000 : ℝ) (247604038333/250000000000 : ℝ) (495208076667/500000000000 : ℝ) (247604038333/250000000000 : ℝ) (495208076667/500000000000 : ℝ) (247604038333/250000000000 : ℝ) (495208076667/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8857/65536 : ℝ))) (97310661899/500000000000 : ℝ) (48655330951/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8857/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (97310661899/500000000000 : ℝ) (48655330951/250000000000 : ℝ) (597310661899/1000000000000 : ℝ) (298655330951/500000000000 : ℝ) (110289767147/250000000000 : ℝ) (110289767149/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8857/65536 : ℝ))) 1 (597310661899/1000000000000 : ℝ) (298655330951/500000000000 : ℝ) (110289767147/250000000000 : ℝ) (110289767149/250000000000 : ℝ) (519234865243/1000000000000 : ℝ) (519234865249/1000000000000 : ℝ) (128332822979/250000000000 : ℝ) (513331291923/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8857/65536 : ℝ))) 2 (519234865243/1000000000000 : ℝ) (519234865249/1000000000000 : ℝ) (128332822979/250000000000 : ℝ) (513331291923/1000000000000 : ℝ) (516283078579/1000000000000 : ℝ) (258141539293/500000000000 : ℝ) (516274640267/1000000000000 : ℝ) (258137320137/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8857/65536 : ℝ))) 3 (516283078579/1000000000000 : ℝ) (258141539293/500000000000 : ℝ) (516274640267/1000000000000 : ℝ) (258137320137/500000000000 : ℝ) (516278859423/1000000000000 : ℝ) (51627885943/100000000000 : ℝ) (103255771881/200000000000 : ℝ) (516278859413/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8857/65536 : ℝ))) 4 (516278859423/1000000000000 : ℝ) (51627885943/100000000000 : ℝ) (103255771881/200000000000 : ℝ) (516278859413/1000000000000 : ℝ) (258139429707/500000000000 : ℝ) (258139429711/500000000000 : ℝ) (516278859413/1000000000000 : ℝ) (258139429711/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8857/65536 : ℝ))) 5 (258139429707/500000000000 : ℝ) (258139429711/500000000000 : ℝ) (516278859413/1000000000000 : ℝ) (258139429711/500000000000 : ℝ) (516278859413/1000000000000 : ℝ) (258139429711/500000000000 : ℝ) (516278859413/1000000000000 : ℝ) (258139429711/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8857/65536 : ℝ))) 6 (516278859413/1000000000000 : ℝ) (258139429711/500000000000 : ℝ) (516278859413/1000000000000 : ℝ) (258139429711/500000000000 : ℝ) (516278859413/1000000000000 : ℝ) (258139429711/500000000000 : ℝ) (516278859413/1000000000000 : ℝ) (258139429711/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8857/65536 : ℝ))) 7 (516278859413/1000000000000 : ℝ) (258139429711/500000000000 : ℝ) (516278859413/1000000000000 : ℝ) (258139429711/500000000000 : ℝ) (516278859413/1000000000000 : ℝ) (258139429711/500000000000 : ℝ) (516278859413/1000000000000 : ℝ) (258139429711/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8857/65536 : ℝ)) hmem 8 (247604038333/250000000000 : ℝ) (495208076667/500000000000 : ℝ) (247604038333/250000000000 : ℝ) (495208076667/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8857/65536 : ℝ))) hcmem 8 (516278859413/1000000000000 : ℝ) (258139429711/500000000000 : ℝ) (516278859413/1000000000000 : ℝ) (258139429711/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8857/65536 : ℝ)) (247604038333/250000000000 : ℝ) (495208076667/500000000000 : ℝ) (516278859413/1000000000000 : ℝ) (258139429711/500000000000 : ℝ) (409408173139/500000000000 : ℝ) (163763269259/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0246_exp_lower
  have heNumeric : (2019015165637/1000000000000 : ℝ)/4 ≤ Real.exp (-273473804143/400000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019015165637/1000000000000 : ℝ)/4 ≤ Real.exp ((1107/8192 : ℝ)-(163763269259/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (1107/8192 : ℝ) (8857/65536 : ℝ) (163763269259/200000000000 : ℝ) (2019015165637/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0247; no trusted numerical premise.
theorem cover7_leaf0247_exp_radius : (12469866212091303/12500000000000000 : ℝ) ≤ Real.exp ((-4429/229376 : ℝ)/8) ∧ Real.exp ((-4429/229376 : ℝ)/8) ≤ (997589296967304241/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4429/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0247_exp_lower : (91808933910964927/100000000000000000 : ℝ) ≤ Real.exp ((-10938953447079/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938953447079/16000000000000 : ℝ)/8) ≤ (918089339109649271/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938953447079/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0247_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (252376875493/125000000000 : ℝ) ≤ 4*Real.exp (8857/65536 : ℝ)*Real.exp (-mu (radius 7 (4429/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (252376875493/125000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4429/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0247_exp_radius
  have hrNumeric : (196175263049/200000000000 : ℝ) ≤ Real.exp (-4429/229376 : ℝ) ∧ Real.exp (-4429/229376 : ℝ) ≤ (490438157623/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196175263049/200000000000 : ℝ) ≤ (radius 7 (4429/32768 : ℝ)) ∧ (radius 7 (4429/32768 : ℝ)) ≤ (490438157623/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4429/32768 : ℝ)) (196175263049/200000000000 : ℝ) (490438157623/500000000000 : ℝ) (97316049793/500000000000 : ℝ) (24329012449/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4429/32768 : ℝ)) (196175263049/200000000000 : ℝ) (490438157623/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4429/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196175263049/200000000000 : ℝ) (490438157623/500000000000 : ℝ) (495219078811/500000000000 : ℝ) (990438157623/1000000000000 : ℝ) (495196000399/500000000000 : ℝ) (990392000799/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4429/32768 : ℝ)) 1 (495219078811/500000000000 : ℝ) (990438157623/1000000000000 : ℝ) (495196000399/500000000000 : ℝ) (990392000799/1000000000000 : ℝ) (99041507921/100000000000 : ℝ) (990415079211/1000000000000 : ℝ) (990415078941/1000000000000 : ℝ) (990415078943/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4429/32768 : ℝ)) 2 (99041507921/100000000000 : ℝ) (990415079211/1000000000000 : ℝ) (990415078941/1000000000000 : ℝ) (990415078943/1000000000000 : ℝ) (39616603163/40000000000 : ℝ) (990415079077/1000000000000 : ℝ) (39616603163/40000000000 : ℝ) (990415079077/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4429/32768 : ℝ)) 3 (39616603163/40000000000 : ℝ) (990415079077/1000000000000 : ℝ) (39616603163/40000000000 : ℝ) (990415079077/1000000000000 : ℝ) (39616603163/40000000000 : ℝ) (990415079077/1000000000000 : ℝ) (39616603163/40000000000 : ℝ) (990415079077/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4429/32768 : ℝ)) 4 (39616603163/40000000000 : ℝ) (990415079077/1000000000000 : ℝ) (39616603163/40000000000 : ℝ) (990415079077/1000000000000 : ℝ) (39616603163/40000000000 : ℝ) (990415079077/1000000000000 : ℝ) (39616603163/40000000000 : ℝ) (990415079077/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4429/32768 : ℝ)) 5 (39616603163/40000000000 : ℝ) (990415079077/1000000000000 : ℝ) (39616603163/40000000000 : ℝ) (990415079077/1000000000000 : ℝ) (39616603163/40000000000 : ℝ) (990415079077/1000000000000 : ℝ) (39616603163/40000000000 : ℝ) (990415079077/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4429/32768 : ℝ)) 6 (39616603163/40000000000 : ℝ) (990415079077/1000000000000 : ℝ) (39616603163/40000000000 : ℝ) (990415079077/1000000000000 : ℝ) (39616603163/40000000000 : ℝ) (990415079077/1000000000000 : ℝ) (39616603163/40000000000 : ℝ) (990415079077/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4429/32768 : ℝ)) 7 (39616603163/40000000000 : ℝ) (990415079077/1000000000000 : ℝ) (39616603163/40000000000 : ℝ) (990415079077/1000000000000 : ℝ) (39616603163/40000000000 : ℝ) (990415079077/1000000000000 : ℝ) (39616603163/40000000000 : ℝ) (990415079077/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4429/32768 : ℝ))) (97316049793/500000000000 : ℝ) (24329012449/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4429/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (97316049793/500000000000 : ℝ) (24329012449/125000000000 : ℝ) (597316049793/1000000000000 : ℝ) (149329012449/250000000000 : ℝ) (441171281461/1000000000000 : ℝ) (110292820367/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4429/32768 : ℝ))) 1 (597316049793/1000000000000 : ℝ) (149329012449/250000000000 : ℝ) (441171281461/1000000000000 : ℝ) (110292820367/250000000000 : ℝ) (519243665627/1000000000000 : ℝ) (16226364551/31250000000 : ℝ) (256670356257/500000000000 : ℝ) (12833517813/25000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4429/32768 : ℝ))) 2 (519243665627/1000000000000 : ℝ) (16226364551/31250000000 : ℝ) (256670356257/500000000000 : ℝ) (12833517813/25000000000 : ℝ) (51629218907/100000000000 : ℝ) (129073047269/250000000000 : ℝ) (12907093817/25000000000 : ℝ) (258141876343/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4429/32768 : ℝ))) 3 (51629218907/100000000000 : ℝ) (129073047269/250000000000 : ℝ) (12907093817/25000000000 : ℝ) (258141876343/500000000000 : ℝ) (4130303767/8000000000 : ℝ) (516287970881/1000000000000 : ℝ) (516287970857/1000000000000 : ℝ) (32267998179/62500000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4429/32768 : ℝ))) 4 (4130303767/8000000000 : ℝ) (516287970881/1000000000000 : ℝ) (516287970857/1000000000000 : ℝ) (32267998179/62500000000 : ℝ) (258143985433/500000000000 : ℝ) (516287970873/1000000000000 : ℝ) (103257594173/200000000000 : ℝ) (516287970873/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4429/32768 : ℝ))) 5 (258143985433/500000000000 : ℝ) (516287970873/1000000000000 : ℝ) (103257594173/200000000000 : ℝ) (516287970873/1000000000000 : ℝ) (103257594173/200000000000 : ℝ) (516287970873/1000000000000 : ℝ) (103257594173/200000000000 : ℝ) (516287970873/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4429/32768 : ℝ))) 6 (103257594173/200000000000 : ℝ) (516287970873/1000000000000 : ℝ) (103257594173/200000000000 : ℝ) (516287970873/1000000000000 : ℝ) (103257594173/200000000000 : ℝ) (516287970873/1000000000000 : ℝ) (103257594173/200000000000 : ℝ) (516287970873/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4429/32768 : ℝ))) 7 (103257594173/200000000000 : ℝ) (516287970873/1000000000000 : ℝ) (103257594173/200000000000 : ℝ) (516287970873/1000000000000 : ℝ) (103257594173/200000000000 : ℝ) (516287970873/1000000000000 : ℝ) (103257594173/200000000000 : ℝ) (516287970873/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4429/32768 : ℝ)) hmem 8 (39616603163/40000000000 : ℝ) (990415079077/1000000000000 : ℝ) (39616603163/40000000000 : ℝ) (990415079077/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4429/32768 : ℝ))) hcmem 8 (103257594173/200000000000 : ℝ) (516287970873/1000000000000 : ℝ) (103257594173/200000000000 : ℝ) (516287970873/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4429/32768 : ℝ)) (39616603163/40000000000 : ℝ) (990415079077/1000000000000 : ℝ) (103257594173/200000000000 : ℝ) (516287970873/1000000000000 : ℝ) (409415842577/500000000000 : ℝ) (818831685169/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0247_exp_lower
  have heNumeric : (252376875493/125000000000 : ℝ)/4 ≤ Real.exp (-10938953447079/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (252376875493/125000000000 : ℝ)/4 ≤ Real.exp ((8857/65536 : ℝ)-(818831685169/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8857/65536 : ℝ) (4429/32768 : ℝ) (818831685169/1000000000000 : ℝ) (252376875493/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0248; no trusted numerical premise.
theorem cover7_leaf0248_exp_radius : (249397256286457401/250000000000000000 : ℝ) ≤ Real.exp ((-8859/458752 : ℝ)/8) ∧ Real.exp ((-8859/458752 : ℝ)/8) ≤ (199517805029165921/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8859/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0248_exp_lower : (918089330051787067/1000000000000000000 : ℝ) ≤ Real.exp ((-5469477354963/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469477354963/8000000000000 : ℝ)/8) ≤ (229522332512946767/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469477354963/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0248_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (504753711147/250000000000 : ℝ) ≤ 4*Real.exp (4429/32768 : ℝ)*Real.exp (-mu (radius 7 (8859/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (504753711147/250000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8859/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0248_exp_radius
  have hrNumeric : (980874177107/1000000000000 : ℝ) ≤ Real.exp (-8859/458752 : ℝ) ∧ Real.exp (-8859/458752 : ℝ) ≤ (245218544277/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980874177107/1000000000000 : ℝ) ≤ (radius 7 (8859/65536 : ℝ)) ∧ (radius 7 (8859/65536 : ℝ)) ≤ (245218544277/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8859/65536 : ℝ)) (980874177107/1000000000000 : ℝ) (245218544277/250000000000 : ℝ) (24330359341/125000000000 : ℝ) (97321437367/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8859/65536 : ℝ)) (980874177107/1000000000000 : ℝ) (245218544277/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8859/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980874177107/1000000000000 : ℝ) (245218544277/250000000000 : ℝ) (990437088553/1000000000000 : ℝ) (495218544277/500000000000 : ℝ) (990390921357/1000000000000 : ℝ) (495195460679/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8859/65536 : ℝ)) 1 (990437088553/1000000000000 : ℝ) (495218544277/500000000000 : ℝ) (990390921357/1000000000000 : ℝ) (495195460679/500000000000 : ℝ) (198082800991/200000000000 : ℝ) (247603501239/250000000000 : ℝ) (198082800937/200000000000 : ℝ) (990414004687/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8859/65536 : ℝ)) 2 (198082800991/200000000000 : ℝ) (247603501239/250000000000 : ℝ) (198082800937/200000000000 : ℝ) (990414004687/1000000000000 : ℝ) (49520700241/50000000000 : ℝ) (495207002411/500000000000 : ℝ) (990414004819/1000000000000 : ℝ) (495207002411/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8859/65536 : ℝ)) 3 (49520700241/50000000000 : ℝ) (495207002411/500000000000 : ℝ) (990414004819/1000000000000 : ℝ) (495207002411/500000000000 : ℝ) (990414004819/1000000000000 : ℝ) (495207002411/500000000000 : ℝ) (990414004819/1000000000000 : ℝ) (495207002411/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8859/65536 : ℝ)) 4 (990414004819/1000000000000 : ℝ) (495207002411/500000000000 : ℝ) (990414004819/1000000000000 : ℝ) (495207002411/500000000000 : ℝ) (990414004819/1000000000000 : ℝ) (495207002411/500000000000 : ℝ) (990414004819/1000000000000 : ℝ) (495207002411/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8859/65536 : ℝ)) 5 (990414004819/1000000000000 : ℝ) (495207002411/500000000000 : ℝ) (990414004819/1000000000000 : ℝ) (495207002411/500000000000 : ℝ) (990414004819/1000000000000 : ℝ) (495207002411/500000000000 : ℝ) (990414004819/1000000000000 : ℝ) (495207002411/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8859/65536 : ℝ)) 6 (990414004819/1000000000000 : ℝ) (495207002411/500000000000 : ℝ) (990414004819/1000000000000 : ℝ) (495207002411/500000000000 : ℝ) (990414004819/1000000000000 : ℝ) (495207002411/500000000000 : ℝ) (990414004819/1000000000000 : ℝ) (495207002411/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8859/65536 : ℝ)) 7 (990414004819/1000000000000 : ℝ) (495207002411/500000000000 : ℝ) (990414004819/1000000000000 : ℝ) (495207002411/500000000000 : ℝ) (990414004819/1000000000000 : ℝ) (495207002411/500000000000 : ℝ) (990414004819/1000000000000 : ℝ) (495207002411/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8859/65536 : ℝ))) (24330359341/125000000000 : ℝ) (97321437367/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8859/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (24330359341/125000000000 : ℝ) (97321437367/500000000000 : ℝ) (149330359341/250000000000 : ℝ) (597321437367/1000000000000 : ℝ) (441183493263/1000000000000 : ℝ) (441183493271/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8859/65536 : ℝ))) 1 (149330359341/250000000000 : ℝ) (597321437367/1000000000000 : ℝ) (441183493263/1000000000000 : ℝ) (441183493271/1000000000000 : ℝ) (519252465313/1000000000000 : ℝ) (519252465319/1000000000000 : ℝ) (32084383269/62500000000 : ℝ) (513350132311/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8859/65536 : ℝ))) 2 (519252465313/1000000000000 : ℝ) (519252465319/1000000000000 : ℝ) (32084383269/62500000000 : ℝ) (513350132311/1000000000000 : ℝ) (64537662351/125000000000 : ℝ) (103260259763/200000000000 : ℝ) (516292864339/1000000000000 : ℝ) (258146432173/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8859/65536 : ℝ))) 3 (64537662351/125000000000 : ℝ) (103260259763/200000000000 : ℝ) (516292864339/1000000000000 : ℝ) (258146432173/500000000000 : ℝ) (516297081573/1000000000000 : ℝ) (516297081581/1000000000000 : ℝ) (129074270389/250000000000 : ℝ) (129074270391/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8859/65536 : ℝ))) 4 (516297081573/1000000000000 : ℝ) (516297081581/1000000000000 : ℝ) (129074270389/250000000000 : ℝ) (129074270391/250000000000 : ℝ) (129074270391/250000000000 : ℝ) (516297081573/1000000000000 : ℝ) (129074270391/250000000000 : ℝ) (516297081573/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8859/65536 : ℝ))) 5 (129074270391/250000000000 : ℝ) (516297081573/1000000000000 : ℝ) (129074270391/250000000000 : ℝ) (516297081573/1000000000000 : ℝ) (129074270391/250000000000 : ℝ) (516297081573/1000000000000 : ℝ) (129074270391/250000000000 : ℝ) (516297081573/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8859/65536 : ℝ))) 6 (129074270391/250000000000 : ℝ) (516297081573/1000000000000 : ℝ) (129074270391/250000000000 : ℝ) (516297081573/1000000000000 : ℝ) (129074270391/250000000000 : ℝ) (516297081573/1000000000000 : ℝ) (129074270391/250000000000 : ℝ) (516297081573/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8859/65536 : ℝ))) 7 (129074270391/250000000000 : ℝ) (516297081573/1000000000000 : ℝ) (129074270391/250000000000 : ℝ) (516297081573/1000000000000 : ℝ) (129074270391/250000000000 : ℝ) (516297081573/1000000000000 : ℝ) (129074270391/250000000000 : ℝ) (516297081573/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8859/65536 : ℝ)) hmem 8 (990414004819/1000000000000 : ℝ) (495207002411/500000000000 : ℝ) (990414004819/1000000000000 : ℝ) (495207002411/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8859/65536 : ℝ))) hcmem 8 (129074270391/250000000000 : ℝ) (516297081573/1000000000000 : ℝ) (129074270391/250000000000 : ℝ) (516297081573/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8859/65536 : ℝ)) (990414004819/1000000000000 : ℝ) (495207002411/500000000000 : ℝ) (129074270391/250000000000 : ℝ) (516297081573/1000000000000 : ℝ) (204711755717/250000000000 : ℝ) (409423511443/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0248_exp_lower
  have heNumeric : (504753711147/250000000000 : ℝ)/4 ≤ Real.exp (-5469477354963/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (504753711147/250000000000 : ℝ)/4 ≤ Real.exp ((4429/32768 : ℝ)-(409423511443/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4429/32768 : ℝ) (8859/65536 : ℝ) (409423511443/500000000000 : ℝ) (504753711147/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0249; no trusted numerical premise.
theorem cover7_leaf0249_exp_radius : (498794376662214517/500000000000000000 : ℝ) ≤ Real.exp ((-2215/114688 : ℝ)/8) ∧ Real.exp ((-2215/114688 : ℝ)/8) ≤ (199517750664885807/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2215/114688 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0249_exp_lower : (459044660563122289/500000000000000000 : ℝ) ≤ Real.exp ((-437558238173/640000000000 : ℝ)/8) ∧ Real.exp ((-437558238173/640000000000 : ℝ)/8) ≤ (918089321126244579/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-437558238173/640000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0249_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019014687559/1000000000000 : ℝ) ≤ 4*Real.exp (8859/65536 : ℝ)*Real.exp (-mu (radius 7 (2215/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (2019014687559/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2215/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0249_exp_radius
  have hrNumeric : (980872038973/1000000000000 : ℝ) ≤ Real.exp (-2215/114688 : ℝ) ∧ Real.exp (-2215/114688 : ℝ) ≤ (490436019487/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980872038973/1000000000000 : ℝ) ≤ (radius 7 (2215/16384 : ℝ)) ∧ (radius 7 (2215/16384 : ℝ)) ≤ (490436019487/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2215/16384 : ℝ)) (980872038973/1000000000000 : ℝ) (490436019487/500000000000 : ℝ) (194653649231/1000000000000 : ℝ) (194653649237/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2215/16384 : ℝ)) (980872038973/1000000000000 : ℝ) (490436019487/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2215/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980872038973/1000000000000 : ℝ) (490436019487/500000000000 : ℝ) (495218009743/500000000000 : ℝ) (990436019487/1000000000000 : ℝ) (990389841917/1000000000000 : ℝ) (495194920959/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2215/16384 : ℝ)) 1 (495218009743/500000000000 : ℝ) (990436019487/1000000000000 : ℝ) (990389841917/1000000000000 : ℝ) (495194920959/500000000000 : ℝ) (990412930701/1000000000000 : ℝ) (990412930703/1000000000000 : ℝ) (7737601019/7812500000 : ℝ) (495206465217/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2215/16384 : ℝ)) 2 (990412930701/1000000000000 : ℝ) (990412930703/1000000000000 : ℝ) (7737601019/7812500000 : ℝ) (495206465217/500000000000 : ℝ) (495206465283/500000000000 : ℝ) (990412930569/1000000000000 : ℝ) (495206465283/500000000000 : ℝ) (990412930569/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2215/16384 : ℝ)) 3 (495206465283/500000000000 : ℝ) (990412930569/1000000000000 : ℝ) (495206465283/500000000000 : ℝ) (990412930569/1000000000000 : ℝ) (495206465283/500000000000 : ℝ) (990412930569/1000000000000 : ℝ) (495206465283/500000000000 : ℝ) (990412930569/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2215/16384 : ℝ)) 4 (495206465283/500000000000 : ℝ) (990412930569/1000000000000 : ℝ) (495206465283/500000000000 : ℝ) (990412930569/1000000000000 : ℝ) (495206465283/500000000000 : ℝ) (990412930569/1000000000000 : ℝ) (495206465283/500000000000 : ℝ) (990412930569/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2215/16384 : ℝ)) 5 (495206465283/500000000000 : ℝ) (990412930569/1000000000000 : ℝ) (495206465283/500000000000 : ℝ) (990412930569/1000000000000 : ℝ) (495206465283/500000000000 : ℝ) (990412930569/1000000000000 : ℝ) (495206465283/500000000000 : ℝ) (990412930569/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2215/16384 : ℝ)) 6 (495206465283/500000000000 : ℝ) (990412930569/1000000000000 : ℝ) (495206465283/500000000000 : ℝ) (990412930569/1000000000000 : ℝ) (495206465283/500000000000 : ℝ) (990412930569/1000000000000 : ℝ) (495206465283/500000000000 : ℝ) (990412930569/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2215/16384 : ℝ)) 7 (495206465283/500000000000 : ℝ) (990412930569/1000000000000 : ℝ) (495206465283/500000000000 : ℝ) (990412930569/1000000000000 : ℝ) (495206465283/500000000000 : ℝ) (990412930569/1000000000000 : ℝ) (495206465283/500000000000 : ℝ) (990412930569/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2215/16384 : ℝ))) (194653649231/1000000000000 : ℝ) (194653649237/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2215/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (194653649231/1000000000000 : ℝ) (194653649237/1000000000000 : ℝ) (119465364923/200000000000 : ℝ) (597326824619/1000000000000 : ℝ) (441195704003/1000000000000 : ℝ) (441195704011/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2215/16384 : ℝ))) 1 (119465364923/200000000000 : ℝ) (597326824619/1000000000000 : ℝ) (441195704003/1000000000000 : ℝ) (441195704011/1000000000000 : ℝ) (519261264309/1000000000000 : ℝ) (103852252863/200000000000 : ℝ) (102671910259/200000000000 : ℝ) (256679775651/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2215/16384 : ℝ))) 2 (519261264309/1000000000000 : ℝ) (103852252863/200000000000 : ℝ) (102671910259/200000000000 : ℝ) (256679775651/500000000000 : ℝ) (258155203901/500000000000 : ℝ) (516310407809/1000000000000 : ℝ) (516301975253/1000000000000 : ℝ) (25815098763/50000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2215/16384 : ℝ))) 3 (258155203901/500000000000 : ℝ) (516310407809/1000000000000 : ℝ) (516301975253/1000000000000 : ℝ) (25815098763/50000000000 : ℝ) (516306191527/1000000000000 : ℝ) (103261238307/200000000000 : ℝ) (51630619151/100000000000 : ℝ) (258153095759/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2215/16384 : ℝ))) 4 (516306191527/1000000000000 : ℝ) (103261238307/200000000000 : ℝ) (51630619151/100000000000 : ℝ) (258153095759/500000000000 : ℝ) (258153095759/500000000000 : ℝ) (516306191527/1000000000000 : ℝ) (258153095759/500000000000 : ℝ) (516306191527/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2215/16384 : ℝ))) 5 (258153095759/500000000000 : ℝ) (516306191527/1000000000000 : ℝ) (258153095759/500000000000 : ℝ) (516306191527/1000000000000 : ℝ) (258153095759/500000000000 : ℝ) (516306191527/1000000000000 : ℝ) (258153095759/500000000000 : ℝ) (516306191527/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2215/16384 : ℝ))) 6 (258153095759/500000000000 : ℝ) (516306191527/1000000000000 : ℝ) (258153095759/500000000000 : ℝ) (516306191527/1000000000000 : ℝ) (258153095759/500000000000 : ℝ) (516306191527/1000000000000 : ℝ) (258153095759/500000000000 : ℝ) (516306191527/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2215/16384 : ℝ))) 7 (258153095759/500000000000 : ℝ) (516306191527/1000000000000 : ℝ) (258153095759/500000000000 : ℝ) (516306191527/1000000000000 : ℝ) (258153095759/500000000000 : ℝ) (516306191527/1000000000000 : ℝ) (258153095759/500000000000 : ℝ) (516306191527/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2215/16384 : ℝ)) hmem 8 (495206465283/500000000000 : ℝ) (990412930569/1000000000000 : ℝ) (495206465283/500000000000 : ℝ) (990412930569/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2215/16384 : ℝ))) hcmem 8 (258153095759/500000000000 : ℝ) (516306191527/1000000000000 : ℝ) (258153095759/500000000000 : ℝ) (516306191527/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2215/16384 : ℝ)) (495206465283/500000000000 : ℝ) (990412930569/1000000000000 : ℝ) (258153095759/500000000000 : ℝ) (516306191527/1000000000000 : ℝ) (102357794929/125000000000 : ℝ) (16377247189/20000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0249_exp_lower
  have heNumeric : (2019014687559/1000000000000 : ℝ)/4 ≤ Real.exp (-437558238173/640000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019014687559/1000000000000 : ℝ)/4 ≤ Real.exp ((8859/65536 : ℝ)-(16377247189/20000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8859/65536 : ℝ) (2215/16384 : ℝ) (16377247189/20000000000 : ℝ) (2019014687559/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover7_leaf0225_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0225_certificate
#check SmaleRate.Proofs.cover7_leaf0226_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0226_certificate
#check SmaleRate.Proofs.cover7_leaf0227_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0227_certificate
#check SmaleRate.Proofs.cover7_leaf0228_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0228_certificate
#check SmaleRate.Proofs.cover7_leaf0229_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0229_certificate
#check SmaleRate.Proofs.cover7_leaf0230_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0230_certificate
#check SmaleRate.Proofs.cover7_leaf0231_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0231_certificate
#check SmaleRate.Proofs.cover7_leaf0232_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0232_certificate
#check SmaleRate.Proofs.cover7_leaf0233_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0233_certificate
#check SmaleRate.Proofs.cover7_leaf0234_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0234_certificate
#check SmaleRate.Proofs.cover7_leaf0235_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0235_certificate
#check SmaleRate.Proofs.cover7_leaf0236_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0236_certificate
#check SmaleRate.Proofs.cover7_leaf0237_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0237_certificate
#check SmaleRate.Proofs.cover7_leaf0238_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0238_certificate
#check SmaleRate.Proofs.cover7_leaf0239_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0239_certificate
#check SmaleRate.Proofs.cover7_leaf0240_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0240_certificate
#check SmaleRate.Proofs.cover7_leaf0241_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0241_certificate
#check SmaleRate.Proofs.cover7_leaf0242_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0242_certificate
#check SmaleRate.Proofs.cover7_leaf0243_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0243_certificate
#check SmaleRate.Proofs.cover7_leaf0244_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0244_certificate
#check SmaleRate.Proofs.cover7_leaf0245_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0245_certificate
#check SmaleRate.Proofs.cover7_leaf0246_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0246_certificate
#check SmaleRate.Proofs.cover7_leaf0247_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0247_certificate
#check SmaleRate.Proofs.cover7_leaf0248_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0248_certificate
#check SmaleRate.Proofs.cover7_leaf0249_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0249_certificate
