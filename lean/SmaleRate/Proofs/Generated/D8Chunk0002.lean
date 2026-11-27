/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.AGMCertificates

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

-- Proposed record cover8_leaf0050; no trusted numerical premise.
theorem cover8_leaf0050_exp_radius : (499075791129149751/500000000000000000 : ℝ) ≤ Real.exp ((-485/32768 : ℝ)/8) ∧ Real.exp ((-485/32768 : ℝ)/8) ≤ (998151582258299503/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-485/32768 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0050_exp_lower : (57507936032999957/62500000000000000 : ℝ) ≤ Real.exp ((-1331897607959/2000000000000 : ℝ)/8) ∧ Real.exp ((-1331897607959/2000000000000 : ℝ)/8) ≤ (920126976527999313/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1331897607959/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0050_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2055143257383/1000000000000 : ℝ) ≤ 4*Real.exp (969/8192 : ℝ)*Real.exp (-mu (radius 8 (485/4096 : ℝ))) ∧ (20549/10000 : ℝ) < (2055143257383/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (485/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0050_exp_radius
  have hrNumeric : (123163496421/125000000000 : ℝ) ≤ Real.exp (-485/32768 : ℝ) ∧ Real.exp (-485/32768 : ℝ) ≤ (985307971369/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (123163496421/125000000000 : ℝ) ≤ (radius 8 (485/4096 : ℝ)) ∧ (radius 8 (485/4096 : ℝ)) ≤ (985307971369/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (485/4096 : ℝ)) (123163496421/125000000000 : ℝ) (985307971369/1000000000000 : ℝ) (42696751601/250000000000 : ℝ) (170787006411/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (485/4096 : ℝ)) (123163496421/125000000000 : ℝ) (985307971369/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (485/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (123163496421/125000000000 : ℝ) (985307971369/1000000000000 : ℝ) (248163496421/250000000000 : ℝ) (198530797137/200000000000 : ℝ) (992626803671/1000000000000 : ℝ) (992626803673/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (485/4096 : ℝ)) 1 (248163496421/250000000000 : ℝ) (198530797137/200000000000 : ℝ) (992626803671/1000000000000 : ℝ) (992626803673/1000000000000 : ℝ) (992640394677/1000000000000 : ℝ) (992640394679/1000000000000 : ℝ) (124080049323/125000000000 : ℝ) (496320197293/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (485/4096 : ℝ)) 2 (992640394677/1000000000000 : ℝ) (992640394679/1000000000000 : ℝ) (124080049323/125000000000 : ℝ) (496320197293/500000000000 : ℝ) (99264039463/100000000000 : ℝ) (992640394633/1000000000000 : ℝ) (99264039463/100000000000 : ℝ) (992640394633/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (485/4096 : ℝ)) 3 (99264039463/100000000000 : ℝ) (992640394633/1000000000000 : ℝ) (99264039463/100000000000 : ℝ) (992640394633/1000000000000 : ℝ) (99264039463/100000000000 : ℝ) (992640394633/1000000000000 : ℝ) (99264039463/100000000000 : ℝ) (992640394633/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (485/4096 : ℝ)) 4 (99264039463/100000000000 : ℝ) (992640394633/1000000000000 : ℝ) (99264039463/100000000000 : ℝ) (992640394633/1000000000000 : ℝ) (99264039463/100000000000 : ℝ) (992640394633/1000000000000 : ℝ) (99264039463/100000000000 : ℝ) (992640394633/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (485/4096 : ℝ)) 5 (99264039463/100000000000 : ℝ) (992640394633/1000000000000 : ℝ) (99264039463/100000000000 : ℝ) (992640394633/1000000000000 : ℝ) (99264039463/100000000000 : ℝ) (992640394633/1000000000000 : ℝ) (99264039463/100000000000 : ℝ) (992640394633/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (485/4096 : ℝ)) 6 (99264039463/100000000000 : ℝ) (992640394633/1000000000000 : ℝ) (99264039463/100000000000 : ℝ) (992640394633/1000000000000 : ℝ) (99264039463/100000000000 : ℝ) (992640394633/1000000000000 : ℝ) (99264039463/100000000000 : ℝ) (992640394633/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (485/4096 : ℝ)) 7 (99264039463/100000000000 : ℝ) (992640394633/1000000000000 : ℝ) (99264039463/100000000000 : ℝ) (992640394633/1000000000000 : ℝ) (99264039463/100000000000 : ℝ) (992640394633/1000000000000 : ℝ) (99264039463/100000000000 : ℝ) (992640394633/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (485/4096 : ℝ))) (42696751601/250000000000 : ℝ) (170787006411/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (485/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (42696751601/250000000000 : ℝ) (170787006411/1000000000000 : ℝ) (292696751601/500000000000 : ℝ) (292696751603/500000000000 : ℝ) (413263845991/1000000000000 : ℝ) (413263846001/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (485/4096 : ℝ))) 1 (292696751601/500000000000 : ℝ) (292696751603/500000000000 : ℝ) (413263845991/1000000000000 : ℝ) (413263846001/1000000000000 : ℝ) (124832168649/250000000000 : ℝ) (124832168651/250000000000 : ℝ) (9837112799/20000000000 : ℝ) (491855639959/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (485/4096 : ℝ))) 2 (124832168649/250000000000 : ℝ) (124832168651/250000000000 : ℝ) (9837112799/20000000000 : ℝ) (491855639959/1000000000000 : ℝ) (495592157273/1000000000000 : ℝ) (247796078641/500000000000 : ℝ) (99115614267/200000000000 : ℝ) (99115614269/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (485/4096 : ℝ))) 3 (495592157273/1000000000000 : ℝ) (247796078641/500000000000 : ℝ) (99115614267/200000000000 : ℝ) (99115614269/200000000000 : ℝ) (7743517411/15625000000 : ℝ) (247792557157/500000000000 : ℝ) (495585114253/1000000000000 : ℝ) (61948139283/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (485/4096 : ℝ))) 4 (7743517411/15625000000 : ℝ) (247792557157/500000000000 : ℝ) (495585114253/1000000000000 : ℝ) (61948139283/125000000000 : ℝ) (247792557139/500000000000 : ℝ) (495585114289/1000000000000 : ℝ) (247792557139/500000000000 : ℝ) (495585114289/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (485/4096 : ℝ))) 5 (247792557139/500000000000 : ℝ) (495585114289/1000000000000 : ℝ) (247792557139/500000000000 : ℝ) (495585114289/1000000000000 : ℝ) (247792557139/500000000000 : ℝ) (495585114289/1000000000000 : ℝ) (247792557139/500000000000 : ℝ) (495585114289/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (485/4096 : ℝ))) 6 (247792557139/500000000000 : ℝ) (495585114289/1000000000000 : ℝ) (247792557139/500000000000 : ℝ) (495585114289/1000000000000 : ℝ) (247792557139/500000000000 : ℝ) (495585114289/1000000000000 : ℝ) (247792557139/500000000000 : ℝ) (495585114289/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (485/4096 : ℝ))) 7 (247792557139/500000000000 : ℝ) (495585114289/1000000000000 : ℝ) (247792557139/500000000000 : ℝ) (495585114289/1000000000000 : ℝ) (247792557139/500000000000 : ℝ) (495585114289/1000000000000 : ℝ) (247792557139/500000000000 : ℝ) (495585114289/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (485/4096 : ℝ)) hmem 8 (99264039463/100000000000 : ℝ) (992640394633/1000000000000 : ℝ) (99264039463/100000000000 : ℝ) (992640394633/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (485/4096 : ℝ))) hcmem 8 (247792557139/500000000000 : ℝ) (495585114289/1000000000000 : ℝ) (247792557139/500000000000 : ℝ) (495585114289/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (485/4096 : ℝ)) (99264039463/100000000000 : ℝ) (992640394633/1000000000000 : ℝ) (247792557139/500000000000 : ℝ) (495585114289/1000000000000 : ℝ) (784234936771/1000000000000 : ℝ) (98029367099/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0050_exp_lower
  have heNumeric : (2055143257383/1000000000000 : ℝ)/4 ≤ Real.exp (-1331897607959/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2055143257383/1000000000000 : ℝ)/4 ≤ Real.exp ((969/8192 : ℝ)-(98029367099/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (969/8192 : ℝ) (485/4096 : ℝ) (98029367099/125000000000 : ℝ) (2055143257383/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0051; no trusted numerical premise.
theorem cover8_leaf0051_exp_radius : (124768709804632421/125000000000000000 : ℝ) ≤ Real.exp ((-971/65536 : ℝ)/8) ∧ Real.exp ((-971/65536 : ℝ)/8) ≤ (998149678437059369/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-971/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0051_exp_lower : (36805049764718859/40000000000000000 : ℝ) ≤ Real.exp ((-332977585943/500000000000 : ℝ)/8) ∧ Real.exp ((-332977585943/500000000000 : ℝ)/8) ≤ (230031561029492869/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-332977585943/500000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0051_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (64222817827/31250000000 : ℝ) ≤ 4*Real.exp (485/4096 : ℝ)*Real.exp (-mu (radius 8 (971/8192 : ℝ))) ∧ (20549/10000 : ℝ) < (64222817827/31250000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (971/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0051_exp_radius
  have hrNumeric : (246323234219/250000000000 : ℝ) ≤ Real.exp (-971/65536 : ℝ) ∧ Real.exp (-971/65536 : ℝ) ≤ (985292936877/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246323234219/250000000000 : ℝ) ≤ (radius 8 (971/8192 : ℝ)) ∧ (radius 8 (971/8192 : ℝ)) ≤ (985292936877/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (971/8192 : ℝ)) (246323234219/250000000000 : ℝ) (985292936877/1000000000000 : ℝ) (85436860517/500000000000 : ℝ) (170873721041/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (971/8192 : ℝ)) (246323234219/250000000000 : ℝ) (985292936877/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (971/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246323234219/250000000000 : ℝ) (985292936877/1000000000000 : ℝ) (496323234219/500000000000 : ℝ) (992646468439/1000000000000 : ℝ) (992619230559/1000000000000 : ℝ) (6203870191/6250000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (971/8192 : ℝ)) 1 (496323234219/500000000000 : ℝ) (992646468439/1000000000000 : ℝ) (992619230559/1000000000000 : ℝ) (6203870191/6250000000 : ℝ) (496316424749/500000000000 : ℝ) (1985265699/2000000000 : ℝ) (198526569881/200000000000 : ℝ) (992632849407/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (971/8192 : ℝ)) 2 (496316424749/500000000000 : ℝ) (1985265699/2000000000 : ℝ) (198526569881/200000000000 : ℝ) (992632849407/1000000000000 : ℝ) (992632849451/1000000000000 : ℝ) (496316424727/500000000000 : ℝ) (992632849451/1000000000000 : ℝ) (496316424727/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (971/8192 : ℝ)) 3 (992632849451/1000000000000 : ℝ) (496316424727/500000000000 : ℝ) (992632849451/1000000000000 : ℝ) (496316424727/500000000000 : ℝ) (992632849451/1000000000000 : ℝ) (496316424727/500000000000 : ℝ) (992632849451/1000000000000 : ℝ) (496316424727/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (971/8192 : ℝ)) 4 (992632849451/1000000000000 : ℝ) (496316424727/500000000000 : ℝ) (992632849451/1000000000000 : ℝ) (496316424727/500000000000 : ℝ) (992632849451/1000000000000 : ℝ) (496316424727/500000000000 : ℝ) (992632849451/1000000000000 : ℝ) (496316424727/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (971/8192 : ℝ)) 5 (992632849451/1000000000000 : ℝ) (496316424727/500000000000 : ℝ) (992632849451/1000000000000 : ℝ) (496316424727/500000000000 : ℝ) (992632849451/1000000000000 : ℝ) (496316424727/500000000000 : ℝ) (992632849451/1000000000000 : ℝ) (496316424727/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (971/8192 : ℝ)) 6 (992632849451/1000000000000 : ℝ) (496316424727/500000000000 : ℝ) (992632849451/1000000000000 : ℝ) (496316424727/500000000000 : ℝ) (992632849451/1000000000000 : ℝ) (496316424727/500000000000 : ℝ) (992632849451/1000000000000 : ℝ) (496316424727/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (971/8192 : ℝ)) 7 (992632849451/1000000000000 : ℝ) (496316424727/500000000000 : ℝ) (992632849451/1000000000000 : ℝ) (496316424727/500000000000 : ℝ) (992632849451/1000000000000 : ℝ) (496316424727/500000000000 : ℝ) (992632849451/1000000000000 : ℝ) (496316424727/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (971/8192 : ℝ))) (85436860517/500000000000 : ℝ) (170873721041/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (971/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (85436860517/500000000000 : ℝ) (170873721041/1000000000000 : ℝ) (585436860517/1000000000000 : ℝ) (585436860521/1000000000000 : ℝ) (82673749409/200000000000 : ℝ) (82673749411/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (971/8192 : ℝ))) 1 (585436860517/1000000000000 : ℝ) (585436860521/1000000000000 : ℝ) (82673749409/200000000000 : ℝ) (82673749411/200000000000 : ℝ) (499402803781/1000000000000 : ℝ) (124850700947/250000000000 : ℝ) (491936277891/1000000000000 : ℝ) (4919362779/10000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (971/8192 : ℝ))) 2 (499402803781/1000000000000 : ℝ) (124850700947/250000000000 : ℝ) (491936277891/1000000000000 : ℝ) (4919362779/10000000000 : ℝ) (123917385209/250000000000 : ℝ) (123917385211/250000000000 : ℝ) (24782774081/50000000000 : ℝ) (495655481629/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (971/8192 : ℝ))) 3 (123917385209/250000000000 : ℝ) (123917385211/250000000000 : ℝ) (24782774081/50000000000 : ℝ) (495655481629/1000000000000 : ℝ) (123915627807/250000000000 : ℝ) (495662511237/1000000000000 : ℝ) (247831255589/500000000000 : ℝ) (495662511187/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (971/8192 : ℝ))) 4 (123915627807/250000000000 : ℝ) (495662511237/1000000000000 : ℝ) (247831255589/500000000000 : ℝ) (495662511187/1000000000000 : ℝ) (495662511203/1000000000000 : ℝ) (123915627803/250000000000 : ℝ) (247831255601/500000000000 : ℝ) (123915627803/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (971/8192 : ℝ))) 5 (495662511203/1000000000000 : ℝ) (123915627803/250000000000 : ℝ) (247831255601/500000000000 : ℝ) (123915627803/250000000000 : ℝ) (247831255601/500000000000 : ℝ) (123915627803/250000000000 : ℝ) (247831255601/500000000000 : ℝ) (123915627803/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (971/8192 : ℝ))) 6 (247831255601/500000000000 : ℝ) (123915627803/250000000000 : ℝ) (247831255601/500000000000 : ℝ) (123915627803/250000000000 : ℝ) (247831255601/500000000000 : ℝ) (123915627803/250000000000 : ℝ) (247831255601/500000000000 : ℝ) (123915627803/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (971/8192 : ℝ))) 7 (247831255601/500000000000 : ℝ) (123915627803/250000000000 : ℝ) (247831255601/500000000000 : ℝ) (123915627803/250000000000 : ℝ) (247831255601/500000000000 : ℝ) (123915627803/250000000000 : ℝ) (247831255601/500000000000 : ℝ) (123915627803/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (971/8192 : ℝ)) hmem 8 (992632849451/1000000000000 : ℝ) (496316424727/500000000000 : ℝ) (992632849451/1000000000000 : ℝ) (496316424727/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (971/8192 : ℝ))) hcmem 8 (247831255601/500000000000 : ℝ) (123915627803/250000000000 : ℝ) (247831255601/500000000000 : ℝ) (123915627803/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (971/8192 : ℝ)) (992632849451/1000000000000 : ℝ) (496316424727/500000000000 : ℝ) (247831255601/500000000000 : ℝ) (123915627803/250000000000 : ℝ) (49022710937/62500000000 : ℝ) (784363375011/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0051_exp_lower
  have heNumeric : (64222817827/31250000000 : ℝ)/4 ≤ Real.exp (-332977585943/500000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (64222817827/31250000000 : ℝ)/4 ≤ Real.exp ((485/4096 : ℝ)-(784363375011/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (485/4096 : ℝ) (971/8192 : ℝ) (784363375011/1000000000000 : ℝ) (64222817827/31250000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0052; no trusted numerical premise.
theorem cover8_leaf0052_exp_radius : (499073887309725241/500000000000000000 : ℝ) ≤ Real.exp ((-243/16384 : ℝ)/8) ∧ Real.exp ((-243/16384 : ℝ)/8) ≤ (998147774619450483/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-243/16384 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0052_exp_lower : (92012552208294183/100000000000000000 : ℝ) ≤ Real.exp ((-266384579837/400000000000 : ℝ)/8) ∧ Real.exp ((-266384579837/400000000000 : ℝ)/8) ≤ (920125522082941831/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-266384579837/400000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0052_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2055117269001/1000000000000 : ℝ) ≤ 4*Real.exp (971/8192 : ℝ)*Real.exp (-mu (radius 8 (243/2048 : ℝ))) ∧ (20549/10000 : ℝ) < (2055117269001/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (243/2048 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0052_exp_radius
  have hrNumeric : (492638951307/500000000000 : ℝ) ≤ Real.exp (-243/16384 : ℝ) ∧ Real.exp (-243/16384 : ℝ) ≤ (197055580523/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492638951307/500000000000 : ℝ) ≤ (radius 8 (243/2048 : ℝ)) ∧ (radius 8 (243/2048 : ℝ)) ≤ (197055580523/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (243/2048 : ℝ)) (492638951307/500000000000 : ℝ) (197055580523/200000000000 : ℝ) (170960389033/1000000000000 : ℝ) (2137004863/12500000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (243/2048 : ℝ)) (492638951307/500000000000 : ℝ) (197055580523/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (243/2048 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492638951307/500000000000 : ℝ) (197055580523/200000000000 : ℝ) (992638951307/1000000000000 : ℝ) (248159737827/250000000000 : ℝ) (31019114297/31250000000 : ℝ) (496305828753/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (243/2048 : ℝ)) 1 (992638951307/1000000000000 : ℝ) (248159737827/250000000000 : ℝ) (31019114297/31250000000 : ℝ) (496305828753/500000000000 : ℝ) (198525060881/200000000000 : ℝ) (992625304407/1000000000000 : ℝ) (992625304311/1000000000000 : ℝ) (496312652157/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (243/2048 : ℝ)) 2 (198525060881/200000000000 : ℝ) (992625304407/1000000000000 : ℝ) (992625304311/1000000000000 : ℝ) (496312652157/500000000000 : ℝ) (496312652179/500000000000 : ℝ) (992625304361/1000000000000 : ℝ) (992625304357/1000000000000 : ℝ) (992625304361/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (243/2048 : ℝ)) 3 (496312652179/500000000000 : ℝ) (992625304361/1000000000000 : ℝ) (992625304357/1000000000000 : ℝ) (992625304361/1000000000000 : ℝ) (992625304357/1000000000000 : ℝ) (992625304361/1000000000000 : ℝ) (992625304357/1000000000000 : ℝ) (992625304361/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (243/2048 : ℝ)) 4 (992625304357/1000000000000 : ℝ) (992625304361/1000000000000 : ℝ) (992625304357/1000000000000 : ℝ) (992625304361/1000000000000 : ℝ) (992625304357/1000000000000 : ℝ) (992625304361/1000000000000 : ℝ) (992625304357/1000000000000 : ℝ) (992625304361/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (243/2048 : ℝ)) 5 (992625304357/1000000000000 : ℝ) (992625304361/1000000000000 : ℝ) (992625304357/1000000000000 : ℝ) (992625304361/1000000000000 : ℝ) (992625304357/1000000000000 : ℝ) (992625304361/1000000000000 : ℝ) (992625304357/1000000000000 : ℝ) (992625304361/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (243/2048 : ℝ)) 6 (992625304357/1000000000000 : ℝ) (992625304361/1000000000000 : ℝ) (992625304357/1000000000000 : ℝ) (992625304361/1000000000000 : ℝ) (992625304357/1000000000000 : ℝ) (992625304361/1000000000000 : ℝ) (992625304357/1000000000000 : ℝ) (992625304361/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (243/2048 : ℝ)) 7 (992625304357/1000000000000 : ℝ) (992625304361/1000000000000 : ℝ) (992625304357/1000000000000 : ℝ) (992625304361/1000000000000 : ℝ) (992625304357/1000000000000 : ℝ) (992625304361/1000000000000 : ℝ) (992625304357/1000000000000 : ℝ) (992625304361/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (243/2048 : ℝ))) (170960389033/1000000000000 : ℝ) (2137004863/12500000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (243/2048 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (170960389033/1000000000000 : ℝ) (2137004863/12500000000 : ℝ) (146370048629/250000000000 : ℝ) (14637004863/25000000000 : ℝ) (82694713019/200000000000 : ℝ) (82694713021/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (243/2048 : ℝ))) 1 (146370048629/250000000000 : ℝ) (14637004863/25000000000 : ℝ) (82694713019/200000000000 : ℝ) (82694713021/200000000000 : ℝ) (99895375961/200000000000 : ℝ) (499476879813/1000000000000 : ℝ) (492016852677/1000000000000 : ℝ) (246008426343/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (243/2048 : ℝ))) 2 (99895375961/200000000000 : ℝ) (499476879813/1000000000000 : ℝ) (492016852677/1000000000000 : ℝ) (246008426343/500000000000 : ℝ) (495746866241/1000000000000 : ℝ) (396597493/800000000 : ℝ) (247866416839/500000000000 : ℝ) (495732833687/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (243/2048 : ℝ))) 3 (495746866241/1000000000000 : ℝ) (396597493/800000000 : ℝ) (247866416839/500000000000 : ℝ) (495732833687/1000000000000 : ℝ) (495739849959/1000000000000 : ℝ) (495739849969/1000000000000 : ℝ) (495739849909/1000000000000 : ℝ) (495739849919/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (243/2048 : ℝ))) 4 (495739849959/1000000000000 : ℝ) (495739849969/1000000000000 : ℝ) (495739849909/1000000000000 : ℝ) (495739849919/1000000000000 : ℝ) (247869924967/500000000000 : ℝ) (61967481243/125000000000 : ℝ) (495739849933/1000000000000 : ℝ) (61967481243/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (243/2048 : ℝ))) 5 (247869924967/500000000000 : ℝ) (61967481243/125000000000 : ℝ) (495739849933/1000000000000 : ℝ) (61967481243/125000000000 : ℝ) (495739849933/1000000000000 : ℝ) (61967481243/125000000000 : ℝ) (495739849933/1000000000000 : ℝ) (61967481243/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (243/2048 : ℝ))) 6 (495739849933/1000000000000 : ℝ) (61967481243/125000000000 : ℝ) (495739849933/1000000000000 : ℝ) (61967481243/125000000000 : ℝ) (495739849933/1000000000000 : ℝ) (61967481243/125000000000 : ℝ) (495739849933/1000000000000 : ℝ) (61967481243/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (243/2048 : ℝ))) 7 (495739849933/1000000000000 : ℝ) (61967481243/125000000000 : ℝ) (495739849933/1000000000000 : ℝ) (61967481243/125000000000 : ℝ) (495739849933/1000000000000 : ℝ) (61967481243/125000000000 : ℝ) (495739849933/1000000000000 : ℝ) (61967481243/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (243/2048 : ℝ)) hmem 8 (992625304357/1000000000000 : ℝ) (992625304361/1000000000000 : ℝ) (992625304357/1000000000000 : ℝ) (992625304361/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (243/2048 : ℝ))) hcmem 8 (495739849933/1000000000000 : ℝ) (61967481243/125000000000 : ℝ) (495739849933/1000000000000 : ℝ) (61967481243/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (243/2048 : ℝ)) (992625304357/1000000000000 : ℝ) (992625304361/1000000000000 : ℝ) (495739849933/1000000000000 : ℝ) (61967481243/125000000000 : ℝ) (784491723009/1000000000000 : ℝ) (78449172303/100000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0052_exp_lower
  have heNumeric : (2055117269001/1000000000000 : ℝ)/4 ≤ Real.exp (-266384579837/400000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2055117269001/1000000000000 : ℝ)/4 ≤ Real.exp ((971/8192 : ℝ)-(78449172303/100000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (971/8192 : ℝ) (243/2048 : ℝ) (78449172303/100000000000 : ℝ) (2055117269001/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0053; no trusted numerical premise.
theorem cover8_leaf0053_exp_radius : (199629174161094567/200000000000000000 : ℝ) ≤ Real.exp ((-973/65536 : ℝ)/8) ∧ Real.exp ((-973/65536 : ℝ)/8) ≤ (249536467701368209/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-973/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0053_exp_lower : (920124810403218287/1000000000000000000 : ℝ) ≤ Real.exp ((-66596763727/100000000000 : ℝ)/8) ∧ Real.exp ((-66596763727/100000000000 : ℝ)/8) ≤ (57507800650201143/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66596763727/100000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0053_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2055104552637/1000000000000 : ℝ) ≤ 4*Real.exp (243/2048 : ℝ)*Real.exp (-mu (radius 8 (973/8192 : ℝ))) ∧ (20549/10000 : ℝ) < (2055104552637/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (973/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0053_exp_radius
  have hrNumeric : (985262868581/1000000000000 : ℝ) ≤ Real.exp (-973/65536 : ℝ) ∧ Real.exp (-973/65536 : ℝ) ≤ (492631434291/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (985262868581/1000000000000 : ℝ) ≤ (radius 8 (973/8192 : ℝ)) ∧ (radius 8 (973/8192 : ℝ)) ≤ (492631434291/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (973/8192 : ℝ)) (985262868581/1000000000000 : ℝ) (492631434291/500000000000 : ℝ) (85523505239/500000000000 : ℝ) (34209402097/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (973/8192 : ℝ)) (985262868581/1000000000000 : ℝ) (492631434291/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (973/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (985262868581/1000000000000 : ℝ) (492631434291/500000000000 : ℝ) (99263143429/100000000000 : ℝ) (992631434291/1000000000000 : ℝ) (992604084507/1000000000000 : ℝ) (992604084509/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (973/8192 : ℝ)) 1 (99263143429/100000000000 : ℝ) (992631434291/1000000000000 : ℝ) (992604084507/1000000000000 : ℝ) (992604084509/1000000000000 : ℝ) (496308879699/500000000000 : ℝ) (4963088797/5000000000 : ℝ) (124077219913/125000000000 : ℝ) (496308879653/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (973/8192 : ℝ)) 2 (496308879699/500000000000 : ℝ) (4963088797/5000000000 : ℝ) (124077219913/125000000000 : ℝ) (496308879653/500000000000 : ℝ) (992617759351/1000000000000 : ℝ) (992617759353/1000000000000 : ℝ) (19852355187/20000000000 : ℝ) (992617759353/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (973/8192 : ℝ)) 3 (992617759351/1000000000000 : ℝ) (992617759353/1000000000000 : ℝ) (19852355187/20000000000 : ℝ) (992617759353/1000000000000 : ℝ) (19852355187/20000000000 : ℝ) (992617759353/1000000000000 : ℝ) (19852355187/20000000000 : ℝ) (992617759353/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (973/8192 : ℝ)) 4 (19852355187/20000000000 : ℝ) (992617759353/1000000000000 : ℝ) (19852355187/20000000000 : ℝ) (992617759353/1000000000000 : ℝ) (19852355187/20000000000 : ℝ) (992617759353/1000000000000 : ℝ) (19852355187/20000000000 : ℝ) (992617759353/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (973/8192 : ℝ)) 5 (19852355187/20000000000 : ℝ) (992617759353/1000000000000 : ℝ) (19852355187/20000000000 : ℝ) (992617759353/1000000000000 : ℝ) (19852355187/20000000000 : ℝ) (992617759353/1000000000000 : ℝ) (19852355187/20000000000 : ℝ) (992617759353/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (973/8192 : ℝ)) 6 (19852355187/20000000000 : ℝ) (992617759353/1000000000000 : ℝ) (19852355187/20000000000 : ℝ) (992617759353/1000000000000 : ℝ) (19852355187/20000000000 : ℝ) (992617759353/1000000000000 : ℝ) (19852355187/20000000000 : ℝ) (992617759353/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (973/8192 : ℝ)) 7 (19852355187/20000000000 : ℝ) (992617759353/1000000000000 : ℝ) (19852355187/20000000000 : ℝ) (992617759353/1000000000000 : ℝ) (19852355187/20000000000 : ℝ) (992617759353/1000000000000 : ℝ) (19852355187/20000000000 : ℝ) (992617759353/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (973/8192 : ℝ))) (85523505239/500000000000 : ℝ) (34209402097/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (973/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (85523505239/500000000000 : ℝ) (34209402097/200000000000 : ℝ) (585523505239/1000000000000 : ℝ) (585523505243/1000000000000 : ℝ) (206789150149/500000000000 : ℝ) (103394575077/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (973/8192 : ℝ))) 1 (585523505239/1000000000000 : ℝ) (585523505243/1000000000000 : ℝ) (206789150149/500000000000 : ℝ) (103394575077/250000000000 : ℝ) (31221931423/62500000000 : ℝ) (62443862847/125000000000 : ℝ) (30756085277/62500000000 : ℝ) (12302434111/25000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (973/8192 : ℝ))) 2 (31221931423/62500000000 : ℝ) (62443862847/125000000000 : ℝ) (30756085277/62500000000 : ℝ) (12302434111/25000000000 : ℝ) (619780167/1250000000 : ℝ) (61978016701/125000000000 : ℝ) (495810127621/1000000000000 : ℝ) (49581012763/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (973/8192 : ℝ))) 3 (619780167/1250000000 : ℝ) (61978016701/125000000000 : ℝ) (495810127621/1000000000000 : ℝ) (49581012763/100000000000 : ℝ) (49581713061/100000000000 : ℝ) (495817130619/1000000000000 : ℝ) (495817130561/1000000000000 : ℝ) (49581713057/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (973/8192 : ℝ))) 4 (49581713061/100000000000 : ℝ) (495817130619/1000000000000 : ℝ) (495817130561/1000000000000 : ℝ) (49581713057/100000000000 : ℝ) (99163426117/200000000000 : ℝ) (99163426119/200000000000 : ℝ) (99163426117/200000000000 : ℝ) (99163426119/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (973/8192 : ℝ))) 5 (99163426117/200000000000 : ℝ) (99163426119/200000000000 : ℝ) (99163426117/200000000000 : ℝ) (99163426119/200000000000 : ℝ) (99163426117/200000000000 : ℝ) (99163426119/200000000000 : ℝ) (99163426117/200000000000 : ℝ) (99163426119/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (973/8192 : ℝ))) 6 (99163426117/200000000000 : ℝ) (99163426119/200000000000 : ℝ) (99163426117/200000000000 : ℝ) (99163426119/200000000000 : ℝ) (99163426117/200000000000 : ℝ) (99163426119/200000000000 : ℝ) (99163426117/200000000000 : ℝ) (99163426119/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (973/8192 : ℝ))) 7 (99163426117/200000000000 : ℝ) (99163426119/200000000000 : ℝ) (99163426117/200000000000 : ℝ) (99163426119/200000000000 : ℝ) (99163426117/200000000000 : ℝ) (99163426119/200000000000 : ℝ) (99163426117/200000000000 : ℝ) (99163426119/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (973/8192 : ℝ)) hmem 8 (19852355187/20000000000 : ℝ) (992617759353/1000000000000 : ℝ) (19852355187/20000000000 : ℝ) (992617759353/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (973/8192 : ℝ))) hcmem 8 (99163426117/200000000000 : ℝ) (99163426119/200000000000 : ℝ) (99163426117/200000000000 : ℝ) (99163426119/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (973/8192 : ℝ)) (19852355187/20000000000 : ℝ) (992617759353/1000000000000 : ℝ) (99163426117/200000000000 : ℝ) (99163426119/200000000000 : ℝ) (784619981001/1000000000000 : ℝ) (39230999051/50000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0053_exp_lower
  have heNumeric : (2055104552637/1000000000000 : ℝ)/4 ≤ Real.exp (-66596763727/100000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2055104552637/1000000000000 : ℝ)/4 ≤ Real.exp ((243/2048 : ℝ)-(39230999051/50000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (243/2048 : ℝ) (973/8192 : ℝ) (39230999051/50000000000 : ℝ) (2055104552637/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0054; no trusted numerical premise.
theorem cover8_leaf0054_exp_radius : (998143966995126423/1000000000000000000 : ℝ) ≤ Real.exp ((-487/32768 : ℝ)/8) ∧ Real.exp ((-487/32768 : ℝ)/8) ≤ (124767995874390803/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-487/32768 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0054_exp_lower : (920124109060604367/1000000000000000000 : ℝ) ≤ Real.exp ((-1331947470153/2000000000000 : ℝ)/8) ∧ Real.exp ((-1331947470153/2000000000000 : ℝ)/8) ≤ (57507756816287773/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1331947470153/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0054_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (411018404209/200000000000 : ℝ) ≤ 4*Real.exp (973/8192 : ℝ)*Real.exp (-mu (radius 8 (487/4096 : ℝ))) ∧ (20549/10000 : ℝ) < (411018404209/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (487/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0054_exp_radius
  have hrNumeric : (985247834777/1000000000000 : ℝ) ≤ Real.exp (-487/32768 : ℝ) ∧ Real.exp (-487/32768 : ℝ) ≤ (492623917389/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (985247834777/1000000000000 : ℝ) ≤ (radius 8 (487/4096 : ℝ)) ∧ (radius 8 (487/4096 : ℝ)) ≤ (492623917389/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (487/4096 : ℝ)) (985247834777/1000000000000 : ℝ) (492623917389/500000000000 : ℝ) (171133585439/1000000000000 : ℝ) (34226717089/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (487/4096 : ℝ)) (985247834777/1000000000000 : ℝ) (492623917389/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (487/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (985247834777/1000000000000 : ℝ) (492623917389/500000000000 : ℝ) (248155979347/250000000000 : ℝ) (992623917389/1000000000000 : ℝ) (62037281973/62500000000 : ℝ) (992596511569/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (487/4096 : ℝ)) 1 (248155979347/250000000000 : ℝ) (992623917389/1000000000000 : ℝ) (62037281973/62500000000 : ℝ) (992596511569/1000000000000 : ℝ) (496305107239/500000000000 : ℝ) (992610214479/1000000000000 : ℝ) (992610214383/1000000000000 : ℝ) (198522042877/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (487/4096 : ℝ)) 2 (496305107239/500000000000 : ℝ) (992610214479/1000000000000 : ℝ) (992610214383/1000000000000 : ℝ) (198522042877/200000000000 : ℝ) (99261021443/100000000000 : ℝ) (31019069201/31250000000 : ℝ) (99261021443/100000000000 : ℝ) (31019069201/31250000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (487/4096 : ℝ)) 3 (99261021443/100000000000 : ℝ) (31019069201/31250000000 : ℝ) (99261021443/100000000000 : ℝ) (31019069201/31250000000 : ℝ) (99261021443/100000000000 : ℝ) (31019069201/31250000000 : ℝ) (99261021443/100000000000 : ℝ) (31019069201/31250000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (487/4096 : ℝ)) 4 (99261021443/100000000000 : ℝ) (31019069201/31250000000 : ℝ) (99261021443/100000000000 : ℝ) (31019069201/31250000000 : ℝ) (99261021443/100000000000 : ℝ) (31019069201/31250000000 : ℝ) (99261021443/100000000000 : ℝ) (31019069201/31250000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (487/4096 : ℝ)) 5 (99261021443/100000000000 : ℝ) (31019069201/31250000000 : ℝ) (99261021443/100000000000 : ℝ) (31019069201/31250000000 : ℝ) (99261021443/100000000000 : ℝ) (31019069201/31250000000 : ℝ) (99261021443/100000000000 : ℝ) (31019069201/31250000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (487/4096 : ℝ)) 6 (99261021443/100000000000 : ℝ) (31019069201/31250000000 : ℝ) (99261021443/100000000000 : ℝ) (31019069201/31250000000 : ℝ) (99261021443/100000000000 : ℝ) (31019069201/31250000000 : ℝ) (99261021443/100000000000 : ℝ) (31019069201/31250000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (487/4096 : ℝ)) 7 (99261021443/100000000000 : ℝ) (31019069201/31250000000 : ℝ) (99261021443/100000000000 : ℝ) (31019069201/31250000000 : ℝ) (99261021443/100000000000 : ℝ) (31019069201/31250000000 : ℝ) (99261021443/100000000000 : ℝ) (31019069201/31250000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (487/4096 : ℝ))) (171133585439/1000000000000 : ℝ) (34226717089/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (487/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (171133585439/1000000000000 : ℝ) (34226717089/200000000000 : ℝ) (585566792719/1000000000000 : ℝ) (585566792723/1000000000000 : ℝ) (206841476401/500000000000 : ℝ) (41368295281/100000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (487/4096 : ℝ))) 1 (585566792719/1000000000000 : ℝ) (585566792723/1000000000000 : ℝ) (206841476401/500000000000 : ℝ) (41368295281/100000000000 : ℝ) (12490621819/25000000000 : ℝ) (499624872767/1000000000000 : ℝ) (492177813269/1000000000000 : ℝ) (123044453319/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (487/4096 : ℝ))) 2 (12490621819/25000000000 : ℝ) (499624872767/1000000000000 : ℝ) (492177813269/1000000000000 : ℝ) (123044453319/250000000000 : ℝ) (247950671507/500000000000 : ℝ) (247950671511/500000000000 : ℝ) (495887363551/1000000000000 : ℝ) (495887363559/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (487/4096 : ℝ))) 3 (247950671507/500000000000 : ℝ) (247950671511/500000000000 : ℝ) (495887363551/1000000000000 : ℝ) (495887363559/1000000000000 : ℝ) (247947176641/500000000000 : ℝ) (495894353291/1000000000000 : ℝ) (495894353233/1000000000000 : ℝ) (247947176621/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (487/4096 : ℝ))) 4 (247947176641/500000000000 : ℝ) (495894353291/1000000000000 : ℝ) (495894353233/1000000000000 : ℝ) (247947176621/500000000000 : ℝ) (495894353257/1000000000000 : ℝ) (495894353267/1000000000000 : ℝ) (495894353257/1000000000000 : ℝ) (495894353267/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (487/4096 : ℝ))) 5 (495894353257/1000000000000 : ℝ) (495894353267/1000000000000 : ℝ) (495894353257/1000000000000 : ℝ) (495894353267/1000000000000 : ℝ) (495894353257/1000000000000 : ℝ) (495894353267/1000000000000 : ℝ) (495894353257/1000000000000 : ℝ) (495894353267/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (487/4096 : ℝ))) 6 (495894353257/1000000000000 : ℝ) (495894353267/1000000000000 : ℝ) (495894353257/1000000000000 : ℝ) (495894353267/1000000000000 : ℝ) (495894353257/1000000000000 : ℝ) (495894353267/1000000000000 : ℝ) (495894353257/1000000000000 : ℝ) (495894353267/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (487/4096 : ℝ))) 7 (495894353257/1000000000000 : ℝ) (495894353267/1000000000000 : ℝ) (495894353257/1000000000000 : ℝ) (495894353267/1000000000000 : ℝ) (495894353257/1000000000000 : ℝ) (495894353267/1000000000000 : ℝ) (495894353257/1000000000000 : ℝ) (495894353267/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (487/4096 : ℝ)) hmem 8 (99261021443/100000000000 : ℝ) (31019069201/31250000000 : ℝ) (99261021443/100000000000 : ℝ) (31019069201/31250000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (487/4096 : ℝ))) hcmem 8 (495894353257/1000000000000 : ℝ) (495894353267/1000000000000 : ℝ) (495894353257/1000000000000 : ℝ) (495894353267/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (487/4096 : ℝ)) (99261021443/100000000000 : ℝ) (31019069201/31250000000 : ℝ) (495894353257/1000000000000 : ℝ) (495894353267/1000000000000 : ℝ) (784748149121/1000000000000 : ℝ) (784748149139/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0054_exp_lower
  have heNumeric : (411018404209/200000000000 : ℝ)/4 ≤ Real.exp (-1331947470153/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (411018404209/200000000000 : ℝ)/4 ≤ Real.exp ((973/8192 : ℝ)-(784748149139/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (973/8192 : ℝ) (487/4096 : ℝ) (784748149139/1000000000000 : ℝ) (411018404209/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0055; no trusted numerical premise.
theorem cover8_leaf0055_exp_radius : (998142063188411237/1000000000000000000 : ℝ) ≤ Real.exp ((-975/65536 : ℝ)/8) ∧ Real.exp ((-975/65536 : ℝ)/8) ≤ (499071031594205619/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-975/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0055_exp_lower : (184024683607380799/200000000000000000 : ℝ) ≤ Real.exp ((-66597974317/100000000000 : ℝ)/8) ∧ Real.exp ((-66597974317/100000000000 : ℝ)/8) ≤ (230030854509225999/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66597974317/100000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0055_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2055079673897/1000000000000 : ℝ) ≤ 4*Real.exp (487/4096 : ℝ)*Real.exp (-mu (radius 8 (975/8192 : ℝ))) ∧ (20549/10000 : ℝ) < (2055079673897/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (975/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0055_exp_radius
  have hrNumeric : (985232801203/1000000000000 : ℝ) ≤ Real.exp (-975/65536 : ℝ) ∧ Real.exp (-975/65536 : ℝ) ≤ (246308200301/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (985232801203/1000000000000 : ℝ) ≤ (radius 8 (975/8192 : ℝ)) ∧ (radius 8 (975/8192 : ℝ)) ≤ (246308200301/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (975/8192 : ℝ)) (985232801203/1000000000000 : ℝ) (246308200301/250000000000 : ℝ) (171220113981/1000000000000 : ℝ) (171220113987/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (975/8192 : ℝ)) (985232801203/1000000000000 : ℝ) (246308200301/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (975/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (985232801203/1000000000000 : ℝ) (246308200301/250000000000 : ℝ) (992616400601/1000000000000 : ℝ) (496308200301/500000000000 : ℝ) (496294469343/500000000000 : ℝ) (15509202167/15625000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (975/8192 : ℝ)) 1 (992616400601/1000000000000 : ℝ) (496308200301/500000000000 : ℝ) (496294469343/500000000000 : ℝ) (15509202167/15625000000 : ℝ) (992602669643/1000000000000 : ℝ) (198520533929/200000000000 : ℝ) (248150667387/250000000000 : ℝ) (992602669551/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (975/8192 : ℝ)) 2 (992602669643/1000000000000 : ℝ) (198520533929/200000000000 : ℝ) (248150667387/250000000000 : ℝ) (992602669551/1000000000000 : ℝ) (198520533919/200000000000 : ℝ) (496301334799/500000000000 : ℝ) (198520533919/200000000000 : ℝ) (496301334799/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (975/8192 : ℝ)) 3 (198520533919/200000000000 : ℝ) (496301334799/500000000000 : ℝ) (198520533919/200000000000 : ℝ) (496301334799/500000000000 : ℝ) (198520533919/200000000000 : ℝ) (496301334799/500000000000 : ℝ) (198520533919/200000000000 : ℝ) (496301334799/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (975/8192 : ℝ)) 4 (198520533919/200000000000 : ℝ) (496301334799/500000000000 : ℝ) (198520533919/200000000000 : ℝ) (496301334799/500000000000 : ℝ) (198520533919/200000000000 : ℝ) (496301334799/500000000000 : ℝ) (198520533919/200000000000 : ℝ) (496301334799/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (975/8192 : ℝ)) 5 (198520533919/200000000000 : ℝ) (496301334799/500000000000 : ℝ) (198520533919/200000000000 : ℝ) (496301334799/500000000000 : ℝ) (198520533919/200000000000 : ℝ) (496301334799/500000000000 : ℝ) (198520533919/200000000000 : ℝ) (496301334799/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (975/8192 : ℝ)) 6 (198520533919/200000000000 : ℝ) (496301334799/500000000000 : ℝ) (198520533919/200000000000 : ℝ) (496301334799/500000000000 : ℝ) (198520533919/200000000000 : ℝ) (496301334799/500000000000 : ℝ) (198520533919/200000000000 : ℝ) (496301334799/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (975/8192 : ℝ)) 7 (198520533919/200000000000 : ℝ) (496301334799/500000000000 : ℝ) (198520533919/200000000000 : ℝ) (496301334799/500000000000 : ℝ) (198520533919/200000000000 : ℝ) (496301334799/500000000000 : ℝ) (198520533919/200000000000 : ℝ) (496301334799/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (975/8192 : ℝ))) (171220113981/1000000000000 : ℝ) (171220113987/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (975/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (171220113981/1000000000000 : ℝ) (171220113987/1000000000000 : ℝ) (58561005699/100000000000 : ℝ) (292805028497/500000000000 : ℝ) (206893761373/500000000000 : ℝ) (82757504551/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (975/8192 : ℝ))) 1 (58561005699/100000000000 : ℝ) (292805028497/500000000000 : ℝ) (206893761373/500000000000 : ℝ) (82757504551/200000000000 : ℝ) (124924697467/250000000000 : ℝ) (3997590319/8000000000 : ℝ) (246129099649/500000000000 : ℝ) (246129099653/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (975/8192 : ℝ))) 2 (124924697467/250000000000 : ℝ) (3997590319/8000000000 : ℝ) (246129099649/500000000000 : ℝ) (246129099653/500000000000 : ℝ) (495978494583/1000000000000 : ℝ) (495978494591/1000000000000 : ℝ) (495964541567/1000000000000 : ℝ) (19838581663/40000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (975/8192 : ℝ))) 3 (495978494583/1000000000000 : ℝ) (495978494591/1000000000000 : ℝ) (495964541567/1000000000000 : ℝ) (19838581663/40000000000 : ℝ) (19838860723/40000000000 : ℝ) (495971518083/1000000000000 : ℝ) (19838860721/40000000000 : ℝ) (247985759017/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (975/8192 : ℝ))) 4 (19838860723/40000000000 : ℝ) (495971518083/1000000000000 : ℝ) (19838860721/40000000000 : ℝ) (247985759017/500000000000 : ℝ) (9919430361/20000000000 : ℝ) (495971518059/1000000000000 : ℝ) (495971518049/1000000000000 : ℝ) (495971518059/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (975/8192 : ℝ))) 5 (9919430361/20000000000 : ℝ) (495971518059/1000000000000 : ℝ) (495971518049/1000000000000 : ℝ) (495971518059/1000000000000 : ℝ) (495971518049/1000000000000 : ℝ) (495971518059/1000000000000 : ℝ) (495971518049/1000000000000 : ℝ) (495971518059/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (975/8192 : ℝ))) 6 (495971518049/1000000000000 : ℝ) (495971518059/1000000000000 : ℝ) (495971518049/1000000000000 : ℝ) (495971518059/1000000000000 : ℝ) (495971518049/1000000000000 : ℝ) (495971518059/1000000000000 : ℝ) (495971518049/1000000000000 : ℝ) (495971518059/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (975/8192 : ℝ))) 7 (495971518049/1000000000000 : ℝ) (495971518059/1000000000000 : ℝ) (495971518049/1000000000000 : ℝ) (495971518059/1000000000000 : ℝ) (495971518049/1000000000000 : ℝ) (495971518059/1000000000000 : ℝ) (495971518049/1000000000000 : ℝ) (495971518059/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (975/8192 : ℝ)) hmem 8 (198520533919/200000000000 : ℝ) (496301334799/500000000000 : ℝ) (198520533919/200000000000 : ℝ) (496301334799/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (975/8192 : ℝ))) hcmem 8 (495971518049/1000000000000 : ℝ) (495971518059/1000000000000 : ℝ) (495971518049/1000000000000 : ℝ) (495971518059/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (975/8192 : ℝ)) (198520533919/200000000000 : ℝ) (496301334799/500000000000 : ℝ) (495971518049/1000000000000 : ℝ) (495971518059/1000000000000 : ℝ) (31395049101/40000000000 : ℝ) (156975245509/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0055_exp_lower
  have heNumeric : (2055079673897/1000000000000 : ℝ)/4 ≤ Real.exp (-66597974317/100000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2055079673897/1000000000000 : ℝ)/4 ≤ Real.exp ((487/4096 : ℝ)-(156975245509/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (487/4096 : ℝ) (975/8192 : ℝ) (156975245509/200000000000 : ℝ) (2055079673897/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0056; no trusted numerical premise.
theorem cover8_leaf0056_exp_radius : (99814015938532727/100000000000000000 : ℝ) ≤ Real.exp ((-61/4096 : ℝ)/8) ∧ Real.exp ((-61/4096 : ℝ)/8) ≤ (998140159385327271/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-61/4096 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0056_exp_lower : (230030684328135329/250000000000000000 : ℝ) ≤ Real.exp ((-1331971323441/2000000000000 : ℝ)/8) ∧ Real.exp ((-1331971323441/2000000000000 : ℝ)/8) ≤ (920122737312541317/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1331971323441/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0056_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2055067510841/1000000000000 : ℝ) ≤ 4*Real.exp (975/8192 : ℝ)*Real.exp (-mu (radius 8 (61/512 : ℝ))) ∧ (20549/10000 : ℝ) < (2055067510841/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (61/512 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0056_exp_radius
  have hrNumeric : (492608883929/500000000000 : ℝ) ≤ Real.exp (-61/4096 : ℝ) ∧ Real.exp (-61/4096 : ℝ) ≤ (985217767859/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492608883929/500000000000 : ℝ) ≤ (radius 8 (61/512 : ℝ)) ∧ (radius 8 (61/512 : ℝ)) ≤ (985217767859/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (61/512 : ℝ)) (492608883929/500000000000 : ℝ) (985217767859/1000000000000 : ℝ) (8565329809/50000000000 : ℝ) (171306596187/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (61/512 : ℝ)) (492608883929/500000000000 : ℝ) (985217767859/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (61/512 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492608883929/500000000000 : ℝ) (985217767859/1000000000000 : ℝ) (992608883929/1000000000000 : ℝ) (99260888393/100000000000 : ℝ) (496290682931/500000000000 : ℝ) (124072670733/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (61/512 : ℝ)) 1 (992608883929/1000000000000 : ℝ) (99260888393/100000000000 : ℝ) (496290682931/500000000000 : ℝ) (124072670733/125000000000 : ℝ) (198519024979/200000000000 : ℝ) (992595124897/1000000000000 : ℝ) (620371953/625000000 : ℝ) (496297562401/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (61/512 : ℝ)) 2 (198519024979/200000000000 : ℝ) (992595124897/1000000000000 : ℝ) (620371953/625000000 : ℝ) (496297562401/500000000000 : ℝ) (992595124847/1000000000000 : ℝ) (19851902497/20000000000 : ℝ) (992595124847/1000000000000 : ℝ) (19851902497/20000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (61/512 : ℝ)) 3 (992595124847/1000000000000 : ℝ) (19851902497/20000000000 : ℝ) (992595124847/1000000000000 : ℝ) (19851902497/20000000000 : ℝ) (992595124847/1000000000000 : ℝ) (19851902497/20000000000 : ℝ) (992595124847/1000000000000 : ℝ) (19851902497/20000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (61/512 : ℝ)) 4 (992595124847/1000000000000 : ℝ) (19851902497/20000000000 : ℝ) (992595124847/1000000000000 : ℝ) (19851902497/20000000000 : ℝ) (992595124847/1000000000000 : ℝ) (19851902497/20000000000 : ℝ) (992595124847/1000000000000 : ℝ) (19851902497/20000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (61/512 : ℝ)) 5 (992595124847/1000000000000 : ℝ) (19851902497/20000000000 : ℝ) (992595124847/1000000000000 : ℝ) (19851902497/20000000000 : ℝ) (992595124847/1000000000000 : ℝ) (19851902497/20000000000 : ℝ) (992595124847/1000000000000 : ℝ) (19851902497/20000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (61/512 : ℝ)) 6 (992595124847/1000000000000 : ℝ) (19851902497/20000000000 : ℝ) (992595124847/1000000000000 : ℝ) (19851902497/20000000000 : ℝ) (992595124847/1000000000000 : ℝ) (19851902497/20000000000 : ℝ) (992595124847/1000000000000 : ℝ) (19851902497/20000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (61/512 : ℝ)) 7 (992595124847/1000000000000 : ℝ) (19851902497/20000000000 : ℝ) (992595124847/1000000000000 : ℝ) (19851902497/20000000000 : ℝ) (992595124847/1000000000000 : ℝ) (19851902497/20000000000 : ℝ) (992595124847/1000000000000 : ℝ) (19851902497/20000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (61/512 : ℝ))) (8565329809/50000000000 : ℝ) (171306596187/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (61/512 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (8565329809/50000000000 : ℝ) (171306596187/1000000000000 : ℝ) (58565329809/100000000000 : ℝ) (292826649047/500000000000 : ℝ) (413892010287/1000000000000 : ℝ) (413892010297/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (61/512 : ℝ))) 1 (58565329809/100000000000 : ℝ) (292826649047/500000000000 : ℝ) (413892010287/1000000000000 : ℝ) (413892010297/1000000000000 : ℝ) (124943163547/250000000000 : ℝ) (124943163549/250000000000 : ℝ) (246169261321/500000000000 : ℝ) (492338522651/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (61/512 : ℝ))) 2 (124943163547/250000000000 : ℝ) (124943163549/250000000000 : ℝ) (246169261321/500000000000 : ℝ) (492338522651/1000000000000 : ℝ) (99211117683/200000000000 : ℝ) (62006948553/125000000000 : ℝ) (248020830889/500000000000 : ℝ) (496041661787/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (61/512 : ℝ))) 3 (99211117683/200000000000 : ℝ) (62006948553/125000000000 : ℝ) (248020830889/500000000000 : ℝ) (496041661787/1000000000000 : ℝ) (62006078137/125000000000 : ℝ) (248024312553/500000000000 : ℝ) (496048625047/1000000000000 : ℝ) (496048625057/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (61/512 : ℝ))) 4 (62006078137/125000000000 : ℝ) (248024312553/500000000000 : ℝ) (496048625047/1000000000000 : ℝ) (496048625057/1000000000000 : ℝ) (496048625071/1000000000000 : ℝ) (248024312541/500000000000 : ℝ) (496048625071/1000000000000 : ℝ) (248024312541/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (61/512 : ℝ))) 5 (496048625071/1000000000000 : ℝ) (248024312541/500000000000 : ℝ) (496048625071/1000000000000 : ℝ) (248024312541/500000000000 : ℝ) (496048625071/1000000000000 : ℝ) (248024312541/500000000000 : ℝ) (496048625071/1000000000000 : ℝ) (248024312541/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (61/512 : ℝ))) 6 (496048625071/1000000000000 : ℝ) (248024312541/500000000000 : ℝ) (496048625071/1000000000000 : ℝ) (248024312541/500000000000 : ℝ) (496048625071/1000000000000 : ℝ) (248024312541/500000000000 : ℝ) (496048625071/1000000000000 : ℝ) (248024312541/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (61/512 : ℝ))) 7 (496048625071/1000000000000 : ℝ) (248024312541/500000000000 : ℝ) (496048625071/1000000000000 : ℝ) (248024312541/500000000000 : ℝ) (496048625071/1000000000000 : ℝ) (248024312541/500000000000 : ℝ) (496048625071/1000000000000 : ℝ) (248024312541/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (61/512 : ℝ)) hmem 8 (992595124847/1000000000000 : ℝ) (19851902497/20000000000 : ℝ) (992595124847/1000000000000 : ℝ) (19851902497/20000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (61/512 : ℝ))) hcmem 8 (496048625071/1000000000000 : ℝ) (248024312541/500000000000 : ℝ) (496048625071/1000000000000 : ℝ) (248024312541/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (61/512 : ℝ)) (992595124847/1000000000000 : ℝ) (19851902497/20000000000 : ℝ) (496048625071/1000000000000 : ℝ) (248024312541/500000000000 : ℝ) (785004216387/1000000000000 : ℝ) (98125527051/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0056_exp_lower
  have heNumeric : (2055067510841/1000000000000 : ℝ)/4 ≤ Real.exp (-1331971323441/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2055067510841/1000000000000 : ℝ)/4 ≤ Real.exp ((975/8192 : ℝ)-(98125527051/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (975/8192 : ℝ) (61/512 : ℝ) (98125527051/125000000000 : ℝ) (2055067510841/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0057; no trusted numerical premise.
theorem cover8_leaf0057_exp_radius : (998138255585874517/1000000000000000000 : ℝ) ≤ Real.exp ((-977/65536 : ℝ)/8) ∧ Real.exp ((-977/65536 : ℝ)/8) ≤ (499069127792937259/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-977/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0057_exp_lower : (230030516717646557/250000000000000000 : ℝ) ≤ Real.exp ((-5327931927/8000000000 : ℝ)/8) ∧ Real.exp ((-5327931927/8000000000 : ℝ)/8) ≤ (920122066870586229/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5327931927/8000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0057_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2055055531569/1000000000000 : ℝ) ≤ 4*Real.exp (61/512 : ℝ)*Real.exp (-mu (radius 8 (977/8192 : ℝ))) ∧ (20549/10000 : ℝ) < (2055055531569/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (977/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0057_exp_radius
  have hrNumeric : (985202734743/1000000000000 : ℝ) ≤ Real.exp (-977/65536 : ℝ) ∧ Real.exp (-977/65536 : ℝ) ≤ (123150341843/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (985202734743/1000000000000 : ℝ) ≤ (radius 8 (977/8192 : ℝ)) ∧ (radius 8 (977/8192 : ℝ)) ≤ (123150341843/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (977/8192 : ℝ)) (985202734743/1000000000000 : ℝ) (123150341843/125000000000 : ℝ) (171393032101/1000000000000 : ℝ) (42848258027/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (977/8192 : ℝ)) (985202734743/1000000000000 : ℝ) (123150341843/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (977/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (985202734743/1000000000000 : ℝ) (123150341843/125000000000 : ℝ) (992601367371/1000000000000 : ℝ) (248150341843/250000000000 : ℝ) (992573793097/1000000000000 : ℝ) (496286896549/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (977/8192 : ℝ)) 1 (992601367371/1000000000000 : ℝ) (248150341843/250000000000 : ℝ) (992573793097/1000000000000 : ℝ) (496286896549/500000000000 : ℝ) (496293790117/500000000000 : ℝ) (198517516047/200000000000 : ℝ) (496293790069/500000000000 : ℝ) (49629379007/50000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (977/8192 : ℝ)) 2 (496293790117/500000000000 : ℝ) (198517516047/200000000000 : ℝ) (496293790069/500000000000 : ℝ) (49629379007/50000000000 : ℝ) (496293790093/500000000000 : ℝ) (248146895047/250000000000 : ℝ) (198517516037/200000000000 : ℝ) (248146895047/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (977/8192 : ℝ)) 3 (496293790093/500000000000 : ℝ) (248146895047/250000000000 : ℝ) (198517516037/200000000000 : ℝ) (248146895047/250000000000 : ℝ) (198517516037/200000000000 : ℝ) (248146895047/250000000000 : ℝ) (198517516037/200000000000 : ℝ) (248146895047/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (977/8192 : ℝ)) 4 (198517516037/200000000000 : ℝ) (248146895047/250000000000 : ℝ) (198517516037/200000000000 : ℝ) (248146895047/250000000000 : ℝ) (198517516037/200000000000 : ℝ) (248146895047/250000000000 : ℝ) (198517516037/200000000000 : ℝ) (248146895047/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (977/8192 : ℝ)) 5 (198517516037/200000000000 : ℝ) (248146895047/250000000000 : ℝ) (198517516037/200000000000 : ℝ) (248146895047/250000000000 : ℝ) (198517516037/200000000000 : ℝ) (248146895047/250000000000 : ℝ) (198517516037/200000000000 : ℝ) (248146895047/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (977/8192 : ℝ)) 6 (198517516037/200000000000 : ℝ) (248146895047/250000000000 : ℝ) (198517516037/200000000000 : ℝ) (248146895047/250000000000 : ℝ) (198517516037/200000000000 : ℝ) (248146895047/250000000000 : ℝ) (198517516037/200000000000 : ℝ) (248146895047/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (977/8192 : ℝ)) 7 (198517516037/200000000000 : ℝ) (248146895047/250000000000 : ℝ) (198517516037/200000000000 : ℝ) (248146895047/250000000000 : ℝ) (198517516037/200000000000 : ℝ) (248146895047/250000000000 : ℝ) (198517516037/200000000000 : ℝ) (248146895047/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (977/8192 : ℝ))) (171393032101/1000000000000 : ℝ) (42848258027/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (977/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (171393032101/1000000000000 : ℝ) (42848258027/250000000000 : ℝ) (11713930321/20000000000 : ℝ) (292848258027/500000000000 : ℝ) (82799283113/200000000000 : ℝ) (206998207787/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (977/8192 : ℝ))) 1 (11713930321/20000000000 : ℝ) (292848258027/500000000000 : ℝ) (82799283113/200000000000 : ℝ) (206998207787/500000000000 : ℝ) (499846465807/1000000000000 : ℝ) (249923232907/500000000000 : ℝ) (30776173963/62500000000 : ℝ) (61552347927/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (977/8192 : ℝ))) 2 (499846465807/1000000000000 : ℝ) (249923232907/500000000000 : ℝ) (30776173963/62500000000 : ℝ) (61552347927/125000000000 : ℝ) (496132624607/1000000000000 : ℝ) (99226524923/200000000000 : ℝ) (248059362141/500000000000 : ℝ) (49611872429/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (977/8192 : ℝ))) 3 (496132624607/1000000000000 : ℝ) (99226524923/200000000000 : ℝ) (248059362141/500000000000 : ℝ) (49611872429/100000000000 : ℝ) (124031418611/250000000000 : ℝ) (496125674453/1000000000000 : ℝ) (99225134879/200000000000 : ℝ) (124031418601/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (977/8192 : ℝ))) 4 (124031418611/250000000000 : ℝ) (496125674453/1000000000000 : ℝ) (99225134879/200000000000 : ℝ) (124031418601/250000000000 : ℝ) (496125674419/1000000000000 : ℝ) (496125674429/1000000000000 : ℝ) (496125674419/1000000000000 : ℝ) (496125674429/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (977/8192 : ℝ))) 5 (496125674419/1000000000000 : ℝ) (496125674429/1000000000000 : ℝ) (496125674419/1000000000000 : ℝ) (496125674429/1000000000000 : ℝ) (496125674419/1000000000000 : ℝ) (496125674429/1000000000000 : ℝ) (496125674419/1000000000000 : ℝ) (496125674429/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (977/8192 : ℝ))) 6 (496125674419/1000000000000 : ℝ) (496125674429/1000000000000 : ℝ) (496125674419/1000000000000 : ℝ) (496125674429/1000000000000 : ℝ) (496125674419/1000000000000 : ℝ) (496125674429/1000000000000 : ℝ) (496125674419/1000000000000 : ℝ) (496125674429/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (977/8192 : ℝ))) 7 (496125674419/1000000000000 : ℝ) (496125674429/1000000000000 : ℝ) (496125674419/1000000000000 : ℝ) (496125674429/1000000000000 : ℝ) (496125674419/1000000000000 : ℝ) (496125674429/1000000000000 : ℝ) (496125674419/1000000000000 : ℝ) (496125674429/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (977/8192 : ℝ)) hmem 8 (198517516037/200000000000 : ℝ) (248146895047/250000000000 : ℝ) (198517516037/200000000000 : ℝ) (248146895047/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (977/8192 : ℝ))) hcmem 8 (496125674419/1000000000000 : ℝ) (496125674429/1000000000000 : ℝ) (496125674419/1000000000000 : ℝ) (496125674429/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (977/8192 : ℝ)) (198517516037/200000000000 : ℝ) (248146895047/250000000000 : ℝ) (496125674419/1000000000000 : ℝ) (496125674429/1000000000000 : ℝ) (49070757241/62500000000 : ℝ) (6281056927/8000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0057_exp_lower
  have heNumeric : (2055055531569/1000000000000 : ℝ)/4 ≤ Real.exp (-5327931927/8000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2055055531569/1000000000000 : ℝ)/4 ≤ Real.exp ((61/512 : ℝ)-(6281056927/8000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (61/512 : ℝ) (977/8192 : ℝ) (6281056927/8000000000 : ℝ) (2055055531569/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0058; no trusted numerical premise.
theorem cover8_leaf0058_exp_radius : (998136351790052969/1000000000000000000 : ℝ) ≤ Real.exp ((-489/32768 : ℝ)/8) ∧ Real.exp ((-489/32768 : ℝ)/8) ≤ (99813635179005297/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-489/32768 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0058_exp_lower : (92012140669065857/100000000000000000 : ℝ) ≤ Real.exp ((-1331994461621/2000000000000 : ℝ)/8) ∧ Real.exp ((-1331994461621/2000000000000 : ℝ)/8) ≤ (920121406690658571/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1331994461621/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0058_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2055043735717/1000000000000 : ℝ) ≤ 4*Real.exp (977/8192 : ℝ)*Real.exp (-mu (radius 8 (489/4096 : ℝ))) ∧ (20549/10000 : ℝ) < (2055043735717/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (489/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0058_exp_radius
  have hrNumeric : (985187701857/1000000000000 : ℝ) ≤ Real.exp (-489/32768 : ℝ) ∧ Real.exp (-489/32768 : ℝ) ≤ (492593850929/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (985187701857/1000000000000 : ℝ) ≤ (radius 8 (489/4096 : ℝ)) ∧ (radius 8 (489/4096 : ℝ)) ≤ (492593850929/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (489/4096 : ℝ)) (985187701857/1000000000000 : ℝ) (492593850929/500000000000 : ℝ) (8573971091/50000000000 : ℝ) (85739710913/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (489/4096 : ℝ)) (985187701857/1000000000000 : ℝ) (492593850929/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (489/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (985187701857/1000000000000 : ℝ) (492593850929/500000000000 : ℝ) (62037115683/62500000000 : ℝ) (992593850929/1000000000000 : ℝ) (248141555097/250000000000 : ℝ) (99256622039/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (489/4096 : ℝ)) 1 (62037115683/62500000000 : ℝ) (992593850929/1000000000000 : ℝ) (248141555097/250000000000 : ℝ) (99256622039/100000000000 : ℝ) (496290017829/500000000000 : ℝ) (49629001783/50000000000 : ℝ) (992580035561/1000000000000 : ℝ) (248145008891/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (489/4096 : ℝ)) 2 (496290017829/500000000000 : ℝ) (49629001783/50000000000 : ℝ) (992580035561/1000000000000 : ℝ) (248145008891/250000000000 : ℝ) (992580035609/1000000000000 : ℝ) (248145008903/250000000000 : ℝ) (992580035609/1000000000000 : ℝ) (248145008903/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (489/4096 : ℝ)) 3 (992580035609/1000000000000 : ℝ) (248145008903/250000000000 : ℝ) (992580035609/1000000000000 : ℝ) (248145008903/250000000000 : ℝ) (992580035609/1000000000000 : ℝ) (248145008903/250000000000 : ℝ) (992580035609/1000000000000 : ℝ) (248145008903/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (489/4096 : ℝ)) 4 (992580035609/1000000000000 : ℝ) (248145008903/250000000000 : ℝ) (992580035609/1000000000000 : ℝ) (248145008903/250000000000 : ℝ) (992580035609/1000000000000 : ℝ) (248145008903/250000000000 : ℝ) (992580035609/1000000000000 : ℝ) (248145008903/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (489/4096 : ℝ)) 5 (992580035609/1000000000000 : ℝ) (248145008903/250000000000 : ℝ) (992580035609/1000000000000 : ℝ) (248145008903/250000000000 : ℝ) (992580035609/1000000000000 : ℝ) (248145008903/250000000000 : ℝ) (992580035609/1000000000000 : ℝ) (248145008903/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (489/4096 : ℝ)) 6 (992580035609/1000000000000 : ℝ) (248145008903/250000000000 : ℝ) (992580035609/1000000000000 : ℝ) (248145008903/250000000000 : ℝ) (992580035609/1000000000000 : ℝ) (248145008903/250000000000 : ℝ) (992580035609/1000000000000 : ℝ) (248145008903/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (489/4096 : ℝ)) 7 (992580035609/1000000000000 : ℝ) (248145008903/250000000000 : ℝ) (992580035609/1000000000000 : ℝ) (248145008903/250000000000 : ℝ) (992580035609/1000000000000 : ℝ) (248145008903/250000000000 : ℝ) (992580035609/1000000000000 : ℝ) (248145008903/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (489/4096 : ℝ))) (8573971091/50000000000 : ℝ) (85739710913/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (489/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (8573971091/50000000000 : ℝ) (85739710913/500000000000 : ℝ) (58573971091/100000000000 : ℝ) (585739710913/1000000000000 : ℝ) (414100738733/1000000000000 : ℝ) (207050369371/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (489/4096 : ℝ))) 1 (58573971091/100000000000 : ℝ) (585739710913/1000000000000 : ℝ) (414100738733/1000000000000 : ℝ) (207050369371/500000000000 : ℝ) (499920224821/1000000000000 : ℝ) (124980056207/250000000000 : ℝ) (492498981717/1000000000000 : ℝ) (19699959269/40000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (489/4096 : ℝ))) 2 (499920224821/1000000000000 : ℝ) (124980056207/250000000000 : ℝ) (492498981717/1000000000000 : ℝ) (19699959269/40000000000 : ℝ) (496209603269/1000000000000 : ℝ) (496209603277/1000000000000 : ℝ) (496195729187/1000000000000 : ℝ) (124048932299/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (489/4096 : ℝ))) 3 (496209603269/1000000000000 : ℝ) (496209603277/1000000000000 : ℝ) (496195729187/1000000000000 : ℝ) (124048932299/250000000000 : ℝ) (124050666557/250000000000 : ℝ) (496202666237/1000000000000 : ℝ) (496202666179/1000000000000 : ℝ) (496202666189/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (489/4096 : ℝ))) 4 (124050666557/250000000000 : ℝ) (496202666237/1000000000000 : ℝ) (496202666179/1000000000000 : ℝ) (496202666189/1000000000000 : ℝ) (496202666203/1000000000000 : ℝ) (496202666213/1000000000000 : ℝ) (496202666203/1000000000000 : ℝ) (496202666213/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (489/4096 : ℝ))) 5 (496202666203/1000000000000 : ℝ) (496202666213/1000000000000 : ℝ) (496202666203/1000000000000 : ℝ) (496202666213/1000000000000 : ℝ) (496202666203/1000000000000 : ℝ) (496202666213/1000000000000 : ℝ) (496202666203/1000000000000 : ℝ) (496202666213/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (489/4096 : ℝ))) 6 (496202666203/1000000000000 : ℝ) (496202666213/1000000000000 : ℝ) (496202666203/1000000000000 : ℝ) (496202666213/1000000000000 : ℝ) (496202666203/1000000000000 : ℝ) (496202666213/1000000000000 : ℝ) (496202666203/1000000000000 : ℝ) (496202666213/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (489/4096 : ℝ))) 7 (496202666203/1000000000000 : ℝ) (496202666213/1000000000000 : ℝ) (496202666203/1000000000000 : ℝ) (496202666213/1000000000000 : ℝ) (496202666203/1000000000000 : ℝ) (496202666213/1000000000000 : ℝ) (496202666203/1000000000000 : ℝ) (496202666213/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (489/4096 : ℝ)) hmem 8 (992580035609/1000000000000 : ℝ) (248145008903/250000000000 : ℝ) (992580035609/1000000000000 : ℝ) (248145008903/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (489/4096 : ℝ))) hcmem 8 (496202666203/1000000000000 : ℝ) (496202666213/1000000000000 : ℝ) (496202666203/1000000000000 : ℝ) (496202666213/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (489/4096 : ℝ)) (992580035609/1000000000000 : ℝ) (248145008903/250000000000 : ℝ) (496202666203/1000000000000 : ℝ) (496202666213/1000000000000 : ℝ) (98157490763/125000000000 : ℝ) (785259926123/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0058_exp_lower
  have heNumeric : (2055043735717/1000000000000 : ℝ)/4 ≤ Real.exp (-1331994461621/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2055043735717/1000000000000 : ℝ)/4 ≤ Real.exp ((977/8192 : ℝ)-(785259926123/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (977/8192 : ℝ) (489/4096 : ℝ) (785259926123/1000000000000 : ℝ) (2055043735717/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0059; no trusted numerical premise.
theorem cover8_leaf0059_exp_radius : (49906722399893131/50000000000000000 : ℝ) ≤ Real.exp ((-979/65536 : ℝ)/8) ∧ Real.exp ((-979/65536 : ℝ)/8) ≤ (998134447997862621/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-979/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0059_exp_lower : (460060378377626979/500000000000000000 : ℝ) ≤ Real.exp ((-666002881679/1000000000000 : ℝ)/8) ∧ Real.exp ((-666002881679/1000000000000 : ℝ)/8) ≤ (920120756755253959/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-666002881679/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0059_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256879015371/125000000000 : ℝ) ≤ 4*Real.exp (489/4096 : ℝ)*Real.exp (-mu (radius 8 (979/8192 : ℝ))) ∧ (20549/10000 : ℝ) < (256879015371/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (979/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0059_exp_radius
  have hrNumeric : (2462931673/2500000000 : ℝ) ≤ Real.exp (-979/65536 : ℝ) ∧ Real.exp (-979/65536 : ℝ) ≤ (985172669201/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (2462931673/2500000000 : ℝ) ≤ (radius 8 (979/8192 : ℝ)) ∧ (radius 8 (979/8192 : ℝ)) ≤ (985172669201/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (979/8192 : ℝ)) (2462931673/2500000000 : ℝ) (985172669201/1000000000000 : ℝ) (85782882703/500000000000 : ℝ) (42891441353/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (979/8192 : ℝ)) (2462931673/2500000000 : ℝ) (985172669201/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (979/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (2462931673/2500000000 : ℝ) (985172669201/1000000000000 : ℝ) (4962931673/5000000000 : ℝ) (992586334601/1000000000000 : ℝ) (496279323869/500000000000 : ℝ) (992558647739/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (979/8192 : ℝ)) 1 (4962931673/5000000000 : ℝ) (992586334601/1000000000000 : ℝ) (496279323869/500000000000 : ℝ) (992558647739/1000000000000 : ℝ) (992572491169/1000000000000 : ℝ) (99257249117/100000000000 : ℝ) (15508945173/15625000000 : ℝ) (496286245537/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (979/8192 : ℝ)) 2 (992572491169/1000000000000 : ℝ) (99257249117/100000000000 : ℝ) (15508945173/15625000000 : ℝ) (496286245537/500000000000 : ℝ) (12407156139/12500000000 : ℝ) (496286245561/500000000000 : ℝ) (12407156139/12500000000 : ℝ) (496286245561/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (979/8192 : ℝ)) 3 (12407156139/12500000000 : ℝ) (496286245561/500000000000 : ℝ) (12407156139/12500000000 : ℝ) (496286245561/500000000000 : ℝ) (12407156139/12500000000 : ℝ) (496286245561/500000000000 : ℝ) (12407156139/12500000000 : ℝ) (496286245561/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (979/8192 : ℝ)) 4 (12407156139/12500000000 : ℝ) (496286245561/500000000000 : ℝ) (12407156139/12500000000 : ℝ) (496286245561/500000000000 : ℝ) (12407156139/12500000000 : ℝ) (496286245561/500000000000 : ℝ) (12407156139/12500000000 : ℝ) (496286245561/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (979/8192 : ℝ)) 5 (12407156139/12500000000 : ℝ) (496286245561/500000000000 : ℝ) (12407156139/12500000000 : ℝ) (496286245561/500000000000 : ℝ) (12407156139/12500000000 : ℝ) (496286245561/500000000000 : ℝ) (12407156139/12500000000 : ℝ) (496286245561/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (979/8192 : ℝ)) 6 (12407156139/12500000000 : ℝ) (496286245561/500000000000 : ℝ) (12407156139/12500000000 : ℝ) (496286245561/500000000000 : ℝ) (12407156139/12500000000 : ℝ) (496286245561/500000000000 : ℝ) (12407156139/12500000000 : ℝ) (496286245561/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (979/8192 : ℝ)) 7 (12407156139/12500000000 : ℝ) (496286245561/500000000000 : ℝ) (12407156139/12500000000 : ℝ) (496286245561/500000000000 : ℝ) (12407156139/12500000000 : ℝ) (496286245561/500000000000 : ℝ) (12407156139/12500000000 : ℝ) (496286245561/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (979/8192 : ℝ))) (85782882703/500000000000 : ℝ) (42891441353/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (979/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (85782882703/500000000000 : ℝ) (42891441353/250000000000 : ℝ) (585782882703/1000000000000 : ℝ) (292891441353/500000000000 : ℝ) (207102489969/500000000000 : ℝ) (207102489973/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (979/8192 : ℝ))) 1 (585782882703/1000000000000 : ℝ) (292891441353/500000000000 : ℝ) (207102489969/500000000000 : ℝ) (207102489973/500000000000 : ℝ) (12499848283/25000000000 : ℝ) (249996965663/500000000000 : ℝ) (492579117683/1000000000000 : ℝ) (49257911769/100000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (979/8192 : ℝ))) 2 (12499848283/25000000000 : ℝ) (249996965663/500000000000 : ℝ) (492579117683/1000000000000 : ℝ) (49257911769/100000000000 : ℝ) (496286524501/1000000000000 : ℝ) (124071631127/250000000000 : ℝ) (124068169149/250000000000 : ℝ) (124068169151/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (979/8192 : ℝ))) 3 (496286524501/1000000000000 : ℝ) (124071631127/250000000000 : ℝ) (124068169149/250000000000 : ℝ) (124068169151/250000000000 : ℝ) (124069900137/250000000000 : ℝ) (124069900139/250000000000 : ℝ) (992559201/2000000000 : ℝ) (124069900127/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (979/8192 : ℝ))) 4 (124069900137/250000000000 : ℝ) (124069900139/250000000000 : ℝ) (992559201/2000000000 : ℝ) (124069900127/250000000000 : ℝ) (124069900131/250000000000 : ℝ) (124069900133/250000000000 : ℝ) (496279600523/1000000000000 : ℝ) (124069900133/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (979/8192 : ℝ))) 5 (124069900131/250000000000 : ℝ) (124069900133/250000000000 : ℝ) (496279600523/1000000000000 : ℝ) (124069900133/250000000000 : ℝ) (496279600523/1000000000000 : ℝ) (124069900133/250000000000 : ℝ) (496279600523/1000000000000 : ℝ) (124069900133/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (979/8192 : ℝ))) 6 (496279600523/1000000000000 : ℝ) (124069900133/250000000000 : ℝ) (496279600523/1000000000000 : ℝ) (124069900133/250000000000 : ℝ) (496279600523/1000000000000 : ℝ) (124069900133/250000000000 : ℝ) (496279600523/1000000000000 : ℝ) (124069900133/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (979/8192 : ℝ))) 7 (496279600523/1000000000000 : ℝ) (124069900133/250000000000 : ℝ) (496279600523/1000000000000 : ℝ) (124069900133/250000000000 : ℝ) (496279600523/1000000000000 : ℝ) (124069900133/250000000000 : ℝ) (496279600523/1000000000000 : ℝ) (124069900133/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (979/8192 : ℝ)) hmem 8 (12407156139/12500000000 : ℝ) (496286245561/500000000000 : ℝ) (12407156139/12500000000 : ℝ) (496286245561/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (979/8192 : ℝ))) hcmem 8 (496279600523/1000000000000 : ℝ) (124069900133/250000000000 : ℝ) (496279600523/1000000000000 : ℝ) (124069900133/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (979/8192 : ℝ)) (12407156139/12500000000 : ℝ) (496286245561/500000000000 : ℝ) (496279600523/1000000000000 : ℝ) (124069900133/250000000000 : ℝ) (785387647287/1000000000000 : ℝ) (98173455913/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0059_exp_lower
  have heNumeric : (256879015371/125000000000 : ℝ)/4 ≤ Real.exp (-666002881679/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256879015371/125000000000 : ℝ)/4 ≤ Real.exp ((489/4096 : ℝ)-(98173455913/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (489/4096 : ℝ) (979/8192 : ℝ) (98173455913/125000000000 : ℝ) (256879015371/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0060; no trusted numerical premise.
theorem cover8_leaf0060_exp_radius : (998132544209303463/1000000000000000000 : ℝ) ≤ Real.exp ((-245/16384 : ℝ)/8) ∧ Real.exp ((-245/16384 : ℝ)/8) ≤ (124766568026162933/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-245/16384 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0060_exp_lower : (230030029261429563/250000000000000000 : ℝ) ≤ Real.exp ((-266403377457/400000000000 : ℝ)/8) ∧ Real.exp ((-266403377457/400000000000 : ℝ)/8) ≤ (920120117045718253/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-266403377457/400000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0060_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027510346493/500000000000 : ℝ) ≤ 4*Real.exp (979/8192 : ℝ)*Real.exp (-mu (radius 8 (245/2048 : ℝ))) ∧ (20549/10000 : ℝ) < (1027510346493/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (245/2048 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0060_exp_radius
  have hrNumeric : (985157636773/1000000000000 : ℝ) ≤ Real.exp (-245/16384 : ℝ) ∧ Real.exp (-245/16384 : ℝ) ≤ (492578818387/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (985157636773/1000000000000 : ℝ) ≤ (radius 8 (245/2048 : ℝ)) ∧ (radius 8 (245/2048 : ℝ)) ≤ (492578818387/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (245/2048 : ℝ)) (985157636773/1000000000000 : ℝ) (492578818387/500000000000 : ℝ) (171652062923/1000000000000 : ℝ) (17165206293/100000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (245/2048 : ℝ)) (985157636773/1000000000000 : ℝ) (492578818387/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (245/2048 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (985157636773/1000000000000 : ℝ) (492578818387/500000000000 : ℝ) (496289409193/500000000000 : ℝ) (992578818387/1000000000000 : ℝ) (198510215029/200000000000 : ℝ) (992551075147/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (245/2048 : ℝ)) 1 (496289409193/500000000000 : ℝ) (992578818387/1000000000000 : ℝ) (198510215029/200000000000 : ℝ) (992551075147/1000000000000 : ℝ) (198512989353/200000000000 : ℝ) (992564946767/1000000000000 : ℝ) (248141236667/250000000000 : ℝ) (992564946671/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (245/2048 : ℝ)) 2 (198512989353/200000000000 : ℝ) (992564946767/1000000000000 : ℝ) (248141236667/250000000000 : ℝ) (992564946671/1000000000000 : ℝ) (248141236679/250000000000 : ℝ) (992564946719/1000000000000 : ℝ) (248141236679/250000000000 : ℝ) (992564946719/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (245/2048 : ℝ)) 3 (248141236679/250000000000 : ℝ) (992564946719/1000000000000 : ℝ) (248141236679/250000000000 : ℝ) (992564946719/1000000000000 : ℝ) (248141236679/250000000000 : ℝ) (992564946719/1000000000000 : ℝ) (248141236679/250000000000 : ℝ) (992564946719/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (245/2048 : ℝ)) 4 (248141236679/250000000000 : ℝ) (992564946719/1000000000000 : ℝ) (248141236679/250000000000 : ℝ) (992564946719/1000000000000 : ℝ) (248141236679/250000000000 : ℝ) (992564946719/1000000000000 : ℝ) (248141236679/250000000000 : ℝ) (992564946719/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (245/2048 : ℝ)) 5 (248141236679/250000000000 : ℝ) (992564946719/1000000000000 : ℝ) (248141236679/250000000000 : ℝ) (992564946719/1000000000000 : ℝ) (248141236679/250000000000 : ℝ) (992564946719/1000000000000 : ℝ) (248141236679/250000000000 : ℝ) (992564946719/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (245/2048 : ℝ)) 6 (248141236679/250000000000 : ℝ) (992564946719/1000000000000 : ℝ) (248141236679/250000000000 : ℝ) (992564946719/1000000000000 : ℝ) (248141236679/250000000000 : ℝ) (992564946719/1000000000000 : ℝ) (248141236679/250000000000 : ℝ) (992564946719/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (245/2048 : ℝ)) 7 (248141236679/250000000000 : ℝ) (992564946719/1000000000000 : ℝ) (248141236679/250000000000 : ℝ) (992564946719/1000000000000 : ℝ) (248141236679/250000000000 : ℝ) (992564946719/1000000000000 : ℝ) (248141236679/250000000000 : ℝ) (992564946719/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (245/2048 : ℝ))) (171652062923/1000000000000 : ℝ) (17165206293/100000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (245/2048 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (171652062923/1000000000000 : ℝ) (17165206293/100000000000 : ℝ) (585826031461/1000000000000 : ℝ) (117165206293/200000000000 : ℝ) (207154569659/500000000000 : ℝ) (3236790151/7812500000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (245/2048 : ℝ))) 1 (585826031461/1000000000000 : ℝ) (117165206293/200000000000 : ℝ) (207154569659/500000000000 : ℝ) (3236790151/7812500000 : ℝ) (500067585389/1000000000000 : ℝ) (500067585397/1000000000000 : ℝ) (492659191413/1000000000000 : ℝ) (246329595711/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (245/2048 : ℝ))) 2 (500067585389/1000000000000 : ℝ) (500067585397/1000000000000 : ℝ) (492659191413/1000000000000 : ℝ) (246329595711/500000000000 : ℝ) (496363388401/1000000000000 : ℝ) (49636338841/100000000000 : ℝ) (99269913321/200000000000 : ℝ) (99269913323/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (245/2048 : ℝ))) 3 (496363388401/1000000000000 : ℝ) (49636338841/100000000000 : ℝ) (99269913321/200000000000 : ℝ) (99269913323/200000000000 : ℝ) (496356477503/1000000000000 : ℝ) (496356477513/1000000000000 : ℝ) (248178238727/500000000000 : ℝ) (99271295493/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (245/2048 : ℝ))) 4 (496356477503/1000000000000 : ℝ) (496356477513/1000000000000 : ℝ) (248178238727/500000000000 : ℝ) (99271295493/200000000000 : ℝ) (248178238739/500000000000 : ℝ) (496356477489/1000000000000 : ℝ) (248178238739/500000000000 : ℝ) (496356477489/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (245/2048 : ℝ))) 5 (248178238739/500000000000 : ℝ) (496356477489/1000000000000 : ℝ) (248178238739/500000000000 : ℝ) (496356477489/1000000000000 : ℝ) (248178238739/500000000000 : ℝ) (496356477489/1000000000000 : ℝ) (248178238739/500000000000 : ℝ) (496356477489/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (245/2048 : ℝ))) 6 (248178238739/500000000000 : ℝ) (496356477489/1000000000000 : ℝ) (248178238739/500000000000 : ℝ) (496356477489/1000000000000 : ℝ) (248178238739/500000000000 : ℝ) (496356477489/1000000000000 : ℝ) (248178238739/500000000000 : ℝ) (496356477489/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (245/2048 : ℝ))) 7 (248178238739/500000000000 : ℝ) (496356477489/1000000000000 : ℝ) (248178238739/500000000000 : ℝ) (496356477489/1000000000000 : ℝ) (248178238739/500000000000 : ℝ) (496356477489/1000000000000 : ℝ) (248178238739/500000000000 : ℝ) (496356477489/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (245/2048 : ℝ)) hmem 8 (248141236679/250000000000 : ℝ) (992564946719/1000000000000 : ℝ) (248141236679/250000000000 : ℝ) (992564946719/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (245/2048 : ℝ))) hcmem 8 (248178238739/500000000000 : ℝ) (496356477489/1000000000000 : ℝ) (248178238739/500000000000 : ℝ) (496356477489/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (245/2048 : ℝ)) (248141236679/250000000000 : ℝ) (992564946719/1000000000000 : ℝ) (248178238739/500000000000 : ℝ) (496356477489/1000000000000 : ℝ) (785515279559/1000000000000 : ℝ) (39275763979/50000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0060_exp_lower
  have heNumeric : (1027510346493/500000000000 : ℝ)/4 ≤ Real.exp (-266403377457/400000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027510346493/500000000000 : ℝ)/4 ≤ Real.exp ((979/8192 : ℝ)-(39275763979/50000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (979/8192 : ℝ) (245/2048 : ℝ) (39275763979/50000000000 : ℝ) (1027510346493/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0061; no trusted numerical premise.
theorem cover8_leaf0061_exp_radius : (998130640424375491/1000000000000000000 : ℝ) ≤ Real.exp ((-981/65536 : ℝ)/8) ∧ Real.exp ((-981/65536 : ℝ)/8) ≤ (249532660106093873/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-981/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0061_exp_lower : (46005974377198639/50000000000000000 : ℝ) ≤ Real.exp ((-333006958429/500000000000 : ℝ)/8) ∧ Real.exp ((-333006958429/500000000000 : ℝ)/8) ≤ (920119487543972781/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-333006958429/500000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0061_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027504722723/500000000000 : ℝ) ≤ 4*Real.exp (245/2048 : ℝ)*Real.exp (-mu (radius 8 (981/8192 : ℝ))) ∧ (20549/10000 : ℝ) < (1027504722723/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (981/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0061_exp_radius
  have hrNumeric : (39405704183/40000000000 : ℝ) ≤ Real.exp (-981/65536 : ℝ) ∧ Real.exp (-981/65536 : ℝ) ≤ (30785706393/31250000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (39405704183/40000000000 : ℝ) ≤ (radius 8 (981/8192 : ℝ)) ∧ (radius 8 (981/8192 : ℝ)) ≤ (30785706393/31250000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (981/8192 : ℝ)) (39405704183/40000000000 : ℝ) (30785706393/31250000000 : ℝ) (171738314447/1000000000000 : ℝ) (85869157227/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (981/8192 : ℝ)) (39405704183/40000000000 : ℝ) (30785706393/31250000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (981/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (39405704183/40000000000 : ℝ) (30785706393/31250000000 : ℝ) (992571302287/1000000000000 : ℝ) (62035706393/62500000000 : ℝ) (99254350261/100000000000 : ℝ) (248135875653/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (981/8192 : ℝ)) 1 (992571302287/1000000000000 : ℝ) (62035706393/62500000000 : ℝ) (99254350261/100000000000 : ℝ) (248135875653/250000000000 : ℝ) (62034837653/62500000000 : ℝ) (19851148049/20000000000 : ℝ) (992557402351/1000000000000 : ℝ) (992557402353/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (981/8192 : ℝ)) 2 (62034837653/62500000000 : ℝ) (19851148049/20000000000 : ℝ) (992557402351/1000000000000 : ℝ) (992557402353/1000000000000 : ℝ) (992557402399/1000000000000 : ℝ) (496278701201/500000000000 : ℝ) (992557402399/1000000000000 : ℝ) (496278701201/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (981/8192 : ℝ)) 3 (992557402399/1000000000000 : ℝ) (496278701201/500000000000 : ℝ) (992557402399/1000000000000 : ℝ) (496278701201/500000000000 : ℝ) (992557402399/1000000000000 : ℝ) (496278701201/500000000000 : ℝ) (992557402399/1000000000000 : ℝ) (496278701201/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (981/8192 : ℝ)) 4 (992557402399/1000000000000 : ℝ) (496278701201/500000000000 : ℝ) (992557402399/1000000000000 : ℝ) (496278701201/500000000000 : ℝ) (992557402399/1000000000000 : ℝ) (496278701201/500000000000 : ℝ) (992557402399/1000000000000 : ℝ) (496278701201/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (981/8192 : ℝ)) 5 (992557402399/1000000000000 : ℝ) (496278701201/500000000000 : ℝ) (992557402399/1000000000000 : ℝ) (496278701201/500000000000 : ℝ) (992557402399/1000000000000 : ℝ) (496278701201/500000000000 : ℝ) (992557402399/1000000000000 : ℝ) (496278701201/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (981/8192 : ℝ)) 6 (992557402399/1000000000000 : ℝ) (496278701201/500000000000 : ℝ) (992557402399/1000000000000 : ℝ) (496278701201/500000000000 : ℝ) (992557402399/1000000000000 : ℝ) (496278701201/500000000000 : ℝ) (992557402399/1000000000000 : ℝ) (496278701201/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (981/8192 : ℝ)) 7 (992557402399/1000000000000 : ℝ) (496278701201/500000000000 : ℝ) (992557402399/1000000000000 : ℝ) (496278701201/500000000000 : ℝ) (992557402399/1000000000000 : ℝ) (496278701201/500000000000 : ℝ) (992557402399/1000000000000 : ℝ) (496278701201/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (981/8192 : ℝ))) (171738314447/1000000000000 : ℝ) (85869157227/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (981/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (171738314447/1000000000000 : ℝ) (85869157227/500000000000 : ℝ) (585869157223/1000000000000 : ℝ) (585869157227/1000000000000 : ℝ) (414413217027/1000000000000 : ℝ) (103603304259/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (981/8192 : ℝ))) 1 (585869157223/1000000000000 : ℝ) (585869157227/1000000000000 : ℝ) (414413217027/1000000000000 : ℝ) (103603304259/250000000000 : ℝ) (4001129497/8000000000 : ℝ) (125035296783/250000000000 : ℝ) (492739203029/1000000000000 : ℝ) (492739203037/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (981/8192 : ℝ))) 2 (4001129497/8000000000 : ℝ) (125035296783/250000000000 : ℝ) (492739203029/1000000000000 : ℝ) (492739203037/1000000000000 : ℝ) (496440195077/1000000000000 : ℝ) (99288039017/200000000000 : ℝ) (124106599831/250000000000 : ℝ) (124106599833/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (981/8192 : ℝ))) 3 (496440195077/1000000000000 : ℝ) (99288039017/200000000000 : ℝ) (124106599831/250000000000 : ℝ) (124106599833/250000000000 : ℝ) (1241083243/2500000000 : ℝ) (496433297209/1000000000000 : ℝ) (1939192567/3906250000 : ℝ) (496433297161/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (981/8192 : ℝ))) 4 (1241083243/2500000000 : ℝ) (496433297209/1000000000000 : ℝ) (1939192567/3906250000 : ℝ) (496433297161/1000000000000 : ℝ) (62054162147/125000000000 : ℝ) (99286659437/200000000000 : ℝ) (19857331887/40000000000 : ℝ) (99286659437/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (981/8192 : ℝ))) 5 (62054162147/125000000000 : ℝ) (99286659437/200000000000 : ℝ) (19857331887/40000000000 : ℝ) (99286659437/200000000000 : ℝ) (19857331887/40000000000 : ℝ) (99286659437/200000000000 : ℝ) (19857331887/40000000000 : ℝ) (99286659437/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (981/8192 : ℝ))) 6 (19857331887/40000000000 : ℝ) (99286659437/200000000000 : ℝ) (19857331887/40000000000 : ℝ) (99286659437/200000000000 : ℝ) (19857331887/40000000000 : ℝ) (99286659437/200000000000 : ℝ) (19857331887/40000000000 : ℝ) (99286659437/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (981/8192 : ℝ))) 7 (19857331887/40000000000 : ℝ) (99286659437/200000000000 : ℝ) (19857331887/40000000000 : ℝ) (99286659437/200000000000 : ℝ) (19857331887/40000000000 : ℝ) (99286659437/200000000000 : ℝ) (19857331887/40000000000 : ℝ) (99286659437/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (981/8192 : ℝ)) hmem 8 (992557402399/1000000000000 : ℝ) (496278701201/500000000000 : ℝ) (992557402399/1000000000000 : ℝ) (496278701201/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (981/8192 : ℝ))) hcmem 8 (19857331887/40000000000 : ℝ) (99286659437/200000000000 : ℝ) (19857331887/40000000000 : ℝ) (99286659437/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (981/8192 : ℝ)) (992557402399/1000000000000 : ℝ) (496278701201/500000000000 : ℝ) (19857331887/40000000000 : ℝ) (99286659437/200000000000 : ℝ) (785642823089/1000000000000 : ℝ) (196410705777/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0061_exp_lower
  have heNumeric : (1027504722723/500000000000 : ℝ)/4 ≤ Real.exp (-333006958429/500000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027504722723/500000000000 : ℝ)/4 ≤ Real.exp ((245/2048 : ℝ)-(196410705777/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (245/2048 : ℝ) (981/8192 : ℝ) (196410705777/250000000000 : ℝ) (1027504722723/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0062; no trusted numerical premise.
theorem cover8_leaf0062_exp_radius : (998128736643078697/1000000000000000000 : ℝ) ≤ Real.exp ((-491/32768 : ℝ)/8) ∧ Real.exp ((-491/32768 : ℝ)/8) ≤ (499064368321539349/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-491/32768 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0062_exp_lower : (115014858529021161/125000000000000000 : ℝ) ≤ Real.exp ((-1332038602961/2000000000000 : ℝ)/8) ∧ Real.exp ((-1332038602961/2000000000000 : ℝ)/8) ≤ (920118868232169289/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1332038602961/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0062_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027499190013/500000000000 : ℝ) ≤ 4*Real.exp (981/8192 : ℝ)*Real.exp (-mu (radius 8 (491/4096 : ℝ))) ∧ (20549/10000 : ℝ) < (1027499190013/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (491/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0062_exp_radius
  have hrNumeric : (985127572607/1000000000000 : ℝ) ≤ Real.exp (-491/32768 : ℝ) ∧ Real.exp (-491/32768 : ℝ) ≤ (7696309161/7812500000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (985127572607/1000000000000 : ℝ) ≤ (radius 8 (491/4096 : ℝ)) ∧ (radius 8 (491/4096 : ℝ)) ≤ (7696309161/7812500000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (491/4096 : ℝ)) (985127572607/1000000000000 : ℝ) (7696309161/7812500000 : ℝ) (171824520041/1000000000000 : ℝ) (10739032503/62500000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (491/4096 : ℝ)) (985127572607/1000000000000 : ℝ) (7696309161/7812500000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (491/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (985127572607/1000000000000 : ℝ) (7696309161/7812500000 : ℝ) (992563786303/1000000000000 : ℝ) (15508809161/15625000000 : ℝ) (496267965067/500000000000 : ℝ) (198507186027/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (491/4096 : ℝ)) 1 (992563786303/1000000000000 : ℝ) (15508809161/15625000000 : ℝ) (496267965067/500000000000 : ℝ) (198507186027/200000000000 : ℝ) (496274929109/500000000000 : ℝ) (49627492911/50000000000 : ℝ) (24813746453/25000000000 : ℝ) (496274929061/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (491/4096 : ℝ)) 2 (496274929109/500000000000 : ℝ) (49627492911/50000000000 : ℝ) (24813746453/25000000000 : ℝ) (496274929061/500000000000 : ℝ) (992549858169/1000000000000 : ℝ) (992549858171/1000000000000 : ℝ) (124068732271/125000000000 : ℝ) (992549858171/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (491/4096 : ℝ)) 3 (992549858169/1000000000000 : ℝ) (992549858171/1000000000000 : ℝ) (124068732271/125000000000 : ℝ) (992549858171/1000000000000 : ℝ) (124068732271/125000000000 : ℝ) (992549858171/1000000000000 : ℝ) (124068732271/125000000000 : ℝ) (992549858171/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (491/4096 : ℝ)) 4 (124068732271/125000000000 : ℝ) (992549858171/1000000000000 : ℝ) (124068732271/125000000000 : ℝ) (992549858171/1000000000000 : ℝ) (124068732271/125000000000 : ℝ) (992549858171/1000000000000 : ℝ) (124068732271/125000000000 : ℝ) (992549858171/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (491/4096 : ℝ)) 5 (124068732271/125000000000 : ℝ) (992549858171/1000000000000 : ℝ) (124068732271/125000000000 : ℝ) (992549858171/1000000000000 : ℝ) (124068732271/125000000000 : ℝ) (992549858171/1000000000000 : ℝ) (124068732271/125000000000 : ℝ) (992549858171/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (491/4096 : ℝ)) 6 (124068732271/125000000000 : ℝ) (992549858171/1000000000000 : ℝ) (124068732271/125000000000 : ℝ) (992549858171/1000000000000 : ℝ) (124068732271/125000000000 : ℝ) (992549858171/1000000000000 : ℝ) (124068732271/125000000000 : ℝ) (992549858171/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (491/4096 : ℝ)) 7 (124068732271/125000000000 : ℝ) (992549858171/1000000000000 : ℝ) (124068732271/125000000000 : ℝ) (992549858171/1000000000000 : ℝ) (124068732271/125000000000 : ℝ) (992549858171/1000000000000 : ℝ) (124068732271/125000000000 : ℝ) (992549858171/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (491/4096 : ℝ))) (171824520041/1000000000000 : ℝ) (10739032503/62500000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (491/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (171824520041/1000000000000 : ℝ) (10739032503/62500000000 : ℝ) (29295613001/50000000000 : ℝ) (73239032503/125000000000 : ℝ) (207258606601/500000000000 : ℝ) (414517213211/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (491/4096 : ℝ))) 1 (29295613001/50000000000 : ℝ) (73239032503/125000000000 : ℝ) (207258606601/500000000000 : ℝ) (414517213211/1000000000000 : ℝ) (500214736611/1000000000000 : ℝ) (250107368309/500000000000 : ℝ) (98563830527/200000000000 : ℝ) (492819152643/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (491/4096 : ℝ))) 2 (500214736611/1000000000000 : ℝ) (250107368309/500000000000 : ℝ) (98563830527/200000000000 : ℝ) (492819152643/1000000000000 : ℝ) (496516944623/1000000000000 : ℝ) (496516944631/1000000000000 : ℝ) (248251587423/500000000000 : ℝ) (248251587427/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (491/4096 : ℝ))) 3 (496516944623/1000000000000 : ℝ) (496516944631/1000000000000 : ℝ) (248251587423/500000000000 : ℝ) (248251587427/500000000000 : ℝ) (248255029867/500000000000 : ℝ) (496510059743/1000000000000 : ℝ) (248255029843/500000000000 : ℝ) (99302011939/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (491/4096 : ℝ))) 4 (248255029867/500000000000 : ℝ) (496510059743/1000000000000 : ℝ) (248255029843/500000000000 : ℝ) (99302011939/200000000000 : ℝ) (49651005971/100000000000 : ℝ) (496510059719/1000000000000 : ℝ) (496510059709/1000000000000 : ℝ) (496510059719/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (491/4096 : ℝ))) 5 (49651005971/100000000000 : ℝ) (496510059719/1000000000000 : ℝ) (496510059709/1000000000000 : ℝ) (496510059719/1000000000000 : ℝ) (496510059709/1000000000000 : ℝ) (496510059719/1000000000000 : ℝ) (496510059709/1000000000000 : ℝ) (496510059719/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (491/4096 : ℝ))) 6 (496510059709/1000000000000 : ℝ) (496510059719/1000000000000 : ℝ) (496510059709/1000000000000 : ℝ) (496510059719/1000000000000 : ℝ) (496510059709/1000000000000 : ℝ) (496510059719/1000000000000 : ℝ) (496510059709/1000000000000 : ℝ) (496510059719/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (491/4096 : ℝ))) 7 (496510059709/1000000000000 : ℝ) (496510059719/1000000000000 : ℝ) (496510059709/1000000000000 : ℝ) (496510059719/1000000000000 : ℝ) (496510059709/1000000000000 : ℝ) (496510059719/1000000000000 : ℝ) (496510059709/1000000000000 : ℝ) (496510059719/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (491/4096 : ℝ)) hmem 8 (124068732271/125000000000 : ℝ) (992549858171/1000000000000 : ℝ) (124068732271/125000000000 : ℝ) (992549858171/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (491/4096 : ℝ))) hcmem 8 (496510059709/1000000000000 : ℝ) (496510059719/1000000000000 : ℝ) (496510059709/1000000000000 : ℝ) (496510059719/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (491/4096 : ℝ)) (124068732271/125000000000 : ℝ) (992549858171/1000000000000 : ℝ) (496510059709/1000000000000 : ℝ) (496510059719/1000000000000 : ℝ) (785770278023/1000000000000 : ℝ) (785770278043/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0062_exp_lower
  have heNumeric : (1027499190013/500000000000 : ℝ)/4 ≤ Real.exp (-1332038602961/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027499190013/500000000000 : ℝ)/4 ≤ Real.exp ((981/8192 : ℝ)-(785770278043/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (981/8192 : ℝ) (491/4096 : ℝ) (785770278043/1000000000000 : ℝ) (1027499190013/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0063; no trusted numerical premise.
theorem cover8_leaf0063_exp_radius : (39925073314616523/40000000000000000 : ℝ) ≤ Real.exp ((-983/65536 : ℝ)/8) ∧ Real.exp ((-983/65536 : ℝ)/8) ≤ (249531708216353269/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-983/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0063_exp_lower : (460059129545079807/500000000000000000 : ℝ) ≤ Real.exp ((-133204919537/200000000000 : ℝ)/8) ∧ Real.exp ((-133204919537/200000000000 : ℝ)/8) ≤ (184023651818031923/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-133204919537/200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0063_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054987496363/1000000000000 : ℝ) ≤ 4*Real.exp (491/4096 : ℝ)*Real.exp (-mu (radius 8 (983/8192 : ℝ))) ∧ (20549/10000 : ℝ) < (2054987496363/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (983/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0063_exp_radius
  have hrNumeric : (985112540867/1000000000000 : ℝ) ≤ Real.exp (-983/65536 : ℝ) ∧ Real.exp (-983/65536 : ℝ) ≤ (246278135217/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (985112540867/1000000000000 : ℝ) ≤ (radius 8 (983/8192 : ℝ)) ∧ (radius 8 (983/8192 : ℝ)) ≤ (246278135217/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (983/8192 : ℝ)) (985112540867/1000000000000 : ℝ) (246278135217/250000000000 : ℝ) (85955339893/500000000000 : ℝ) (171910679793/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (983/8192 : ℝ)) (985112540867/1000000000000 : ℝ) (246278135217/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (983/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (985112540867/1000000000000 : ℝ) (246278135217/250000000000 : ℝ) (992556270433/1000000000000 : ℝ) (496278135217/500000000000 : ℝ) (496264178857/500000000000 : ℝ) (198505671543/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (983/8192 : ℝ)) 1 (992556270433/1000000000000 : ℝ) (496278135217/500000000000 : ℝ) (496264178857/500000000000 : ℝ) (198505671543/200000000000 : ℝ) (992542314073/1000000000000 : ℝ) (39701692563/40000000000 : ℝ) (39701692559/40000000000 : ℝ) (992542313977/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (983/8192 : ℝ)) 2 (992542314073/1000000000000 : ℝ) (39701692563/40000000000 : ℝ) (39701692559/40000000000 : ℝ) (992542313977/1000000000000 : ℝ) (124067789253/125000000000 : ℝ) (496271157013/500000000000 : ℝ) (992542314023/1000000000000 : ℝ) (496271157013/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (983/8192 : ℝ)) 3 (124067789253/125000000000 : ℝ) (496271157013/500000000000 : ℝ) (992542314023/1000000000000 : ℝ) (496271157013/500000000000 : ℝ) (992542314023/1000000000000 : ℝ) (496271157013/500000000000 : ℝ) (992542314023/1000000000000 : ℝ) (496271157013/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (983/8192 : ℝ)) 4 (992542314023/1000000000000 : ℝ) (496271157013/500000000000 : ℝ) (992542314023/1000000000000 : ℝ) (496271157013/500000000000 : ℝ) (992542314023/1000000000000 : ℝ) (496271157013/500000000000 : ℝ) (992542314023/1000000000000 : ℝ) (496271157013/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (983/8192 : ℝ)) 5 (992542314023/1000000000000 : ℝ) (496271157013/500000000000 : ℝ) (992542314023/1000000000000 : ℝ) (496271157013/500000000000 : ℝ) (992542314023/1000000000000 : ℝ) (496271157013/500000000000 : ℝ) (992542314023/1000000000000 : ℝ) (496271157013/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (983/8192 : ℝ)) 6 (992542314023/1000000000000 : ℝ) (496271157013/500000000000 : ℝ) (992542314023/1000000000000 : ℝ) (496271157013/500000000000 : ℝ) (992542314023/1000000000000 : ℝ) (496271157013/500000000000 : ℝ) (992542314023/1000000000000 : ℝ) (496271157013/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (983/8192 : ℝ)) 7 (992542314023/1000000000000 : ℝ) (496271157013/500000000000 : ℝ) (992542314023/1000000000000 : ℝ) (496271157013/500000000000 : ℝ) (992542314023/1000000000000 : ℝ) (496271157013/500000000000 : ℝ) (992542314023/1000000000000 : ℝ) (496271157013/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (983/8192 : ℝ))) (85955339893/500000000000 : ℝ) (171910679793/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (983/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (85955339893/500000000000 : ℝ) (171910679793/1000000000000 : ℝ) (585955339893/1000000000000 : ℝ) (585955339897/1000000000000 : ℝ) (207310564001/500000000000 : ℝ) (414621128011/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (983/8192 : ℝ))) 1 (585955339893/1000000000000 : ℝ) (585955339897/1000000000000 : ℝ) (207310564001/500000000000 : ℝ) (414621128011/1000000000000 : ℝ) (500288233947/1000000000000 : ℝ) (250144116977/500000000000 : ℝ) (492899040357/1000000000000 : ℝ) (98579808073/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (983/8192 : ℝ))) 2 (500288233947/1000000000000 : ℝ) (250144116977/500000000000 : ℝ) (492899040357/1000000000000 : ℝ) (98579808073/200000000000 : ℝ) (15518551161/31250000000 : ℝ) (12414840929/25000000000 : ℝ) (124144973321/250000000000 : ℝ) (124144973323/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (983/8192 : ℝ))) 3 (15518551161/31250000000 : ℝ) (12414840929/25000000000 : ℝ) (124144973321/250000000000 : ℝ) (124144973323/250000000000 : ℝ) (248293382609/500000000000 : ℝ) (248293382613/500000000000 : ℝ) (49658676517/100000000000 : ℝ) (496586765179/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (983/8192 : ℝ))) 4 (248293382609/500000000000 : ℝ) (248293382613/500000000000 : ℝ) (49658676517/100000000000 : ℝ) (496586765179/1000000000000 : ℝ) (248293382597/500000000000 : ℝ) (496586765203/1000000000000 : ℝ) (496586765193/1000000000000 : ℝ) (496586765203/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (983/8192 : ℝ))) 5 (248293382597/500000000000 : ℝ) (496586765203/1000000000000 : ℝ) (496586765193/1000000000000 : ℝ) (496586765203/1000000000000 : ℝ) (496586765193/1000000000000 : ℝ) (496586765203/1000000000000 : ℝ) (496586765193/1000000000000 : ℝ) (496586765203/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (983/8192 : ℝ))) 6 (496586765193/1000000000000 : ℝ) (496586765203/1000000000000 : ℝ) (496586765193/1000000000000 : ℝ) (496586765203/1000000000000 : ℝ) (496586765193/1000000000000 : ℝ) (496586765203/1000000000000 : ℝ) (496586765193/1000000000000 : ℝ) (496586765203/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (983/8192 : ℝ))) 7 (496586765193/1000000000000 : ℝ) (496586765203/1000000000000 : ℝ) (496586765193/1000000000000 : ℝ) (496586765203/1000000000000 : ℝ) (496586765193/1000000000000 : ℝ) (496586765203/1000000000000 : ℝ) (496586765193/1000000000000 : ℝ) (496586765203/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (983/8192 : ℝ)) hmem 8 (992542314023/1000000000000 : ℝ) (496271157013/500000000000 : ℝ) (992542314023/1000000000000 : ℝ) (496271157013/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (983/8192 : ℝ))) hcmem 8 (496586765193/1000000000000 : ℝ) (496586765203/1000000000000 : ℝ) (496586765193/1000000000000 : ℝ) (496586765203/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (983/8192 : ℝ)) (992542314023/1000000000000 : ℝ) (496271157013/500000000000 : ℝ) (496586765193/1000000000000 : ℝ) (496586765203/1000000000000 : ℝ) (39294882227/50000000000 : ℝ) (9823720557/12500000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0063_exp_lower
  have heNumeric : (2054987496363/1000000000000 : ℝ)/4 ≤ Real.exp (-133204919537/200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054987496363/1000000000000 : ℝ)/4 ≤ Real.exp ((491/4096 : ℝ)-(9823720557/12500000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (491/4096 : ℝ) (983/8192 : ℝ) (9823720557/12500000000 : ℝ) (2054987496363/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0064; no trusted numerical premise.
theorem cover8_leaf0064_exp_radius : (124765616136422327/125000000000000000 : ℝ) ≤ Real.exp ((-123/8192 : ℝ)/8) ∧ Real.exp ((-123/8192 : ℝ)/8) ≤ (998124929091378617/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-123/8192 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0064_exp_lower : (920117660102856633/1000000000000000000 : ℝ) ≤ Real.exp ((-266411922241/400000000000 : ℝ)/8) ∧ Real.exp ((-266411922241/400000000000 : ℝ)/8) ≤ (460058830051428317/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-266411922241/400000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0064_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410995358837/200000000000 : ℝ) ≤ 4*Real.exp (983/8192 : ℝ)*Real.exp (-mu (radius 8 (123/1024 : ℝ))) ∧ (20549/10000 : ℝ) < (410995358837/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (123/1024 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0064_exp_radius
  have hrNumeric : (492548754679/500000000000 : ℝ) ≤ Real.exp (-123/8192 : ℝ) ∧ Real.exp (-123/8192 : ℝ) ≤ (985097509359/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492548754679/500000000000 : ℝ) ≤ (radius 8 (123/1024 : ℝ)) ∧ (radius 8 (123/1024 : ℝ)) ≤ (985097509359/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (123/1024 : ℝ)) (492548754679/500000000000 : ℝ) (985097509359/1000000000000 : ℝ) (171996793733/1000000000000 : ℝ) (8599839687/50000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (123/1024 : ℝ)) (492548754679/500000000000 : ℝ) (985097509359/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (123/1024 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492548754679/500000000000 : ℝ) (985097509359/1000000000000 : ℝ) (992548754679/1000000000000 : ℝ) (24813718867/25000000000 : ℝ) (992520785353/1000000000000 : ℝ) (496260392677/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (123/1024 : ℝ)) 1 (992548754679/1000000000000 : ℝ) (24813718867/25000000000 : ℝ) (992520785353/1000000000000 : ℝ) (496260392677/500000000000 : ℝ) (31016711563/31250000000 : ℝ) (992534770017/1000000000000 : ℝ) (992534769917/1000000000000 : ℝ) (992534769919/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (123/1024 : ℝ)) 2 (31016711563/31250000000 : ℝ) (992534770017/1000000000000 : ℝ) (992534769917/1000000000000 : ℝ) (992534769919/1000000000000 : ℝ) (496267384983/500000000000 : ℝ) (62033423123/62500000000 : ℝ) (496267384983/500000000000 : ℝ) (62033423123/62500000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (123/1024 : ℝ)) 3 (496267384983/500000000000 : ℝ) (62033423123/62500000000 : ℝ) (496267384983/500000000000 : ℝ) (62033423123/62500000000 : ℝ) (496267384983/500000000000 : ℝ) (62033423123/62500000000 : ℝ) (496267384983/500000000000 : ℝ) (62033423123/62500000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (123/1024 : ℝ)) 4 (496267384983/500000000000 : ℝ) (62033423123/62500000000 : ℝ) (496267384983/500000000000 : ℝ) (62033423123/62500000000 : ℝ) (496267384983/500000000000 : ℝ) (62033423123/62500000000 : ℝ) (496267384983/500000000000 : ℝ) (62033423123/62500000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (123/1024 : ℝ)) 5 (496267384983/500000000000 : ℝ) (62033423123/62500000000 : ℝ) (496267384983/500000000000 : ℝ) (62033423123/62500000000 : ℝ) (496267384983/500000000000 : ℝ) (62033423123/62500000000 : ℝ) (496267384983/500000000000 : ℝ) (62033423123/62500000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (123/1024 : ℝ)) 6 (496267384983/500000000000 : ℝ) (62033423123/62500000000 : ℝ) (496267384983/500000000000 : ℝ) (62033423123/62500000000 : ℝ) (496267384983/500000000000 : ℝ) (62033423123/62500000000 : ℝ) (496267384983/500000000000 : ℝ) (62033423123/62500000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (123/1024 : ℝ)) 7 (496267384983/500000000000 : ℝ) (62033423123/62500000000 : ℝ) (496267384983/500000000000 : ℝ) (62033423123/62500000000 : ℝ) (496267384983/500000000000 : ℝ) (62033423123/62500000000 : ℝ) (496267384983/500000000000 : ℝ) (62033423123/62500000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (123/1024 : ℝ))) (171996793733/1000000000000 : ℝ) (8599839687/50000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (123/1024 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (171996793733/1000000000000 : ℝ) (8599839687/50000000000 : ℝ) (292999198433/500000000000 : ℝ) (58599839687/100000000000 : ℝ) (8294499231/20000000000 : ℝ) (414724961559/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (123/1024 : ℝ))) 1 (292999198433/500000000000 : ℝ) (58599839687/100000000000 : ℝ) (8294499231/20000000000 : ℝ) (414724961559/1000000000000 : ℝ) (62545209901/125000000000 : ℝ) (100072335843/200000000000 : ℝ) (49297886629/100000000000 : ℝ) (246489433149/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (123/1024 : ℝ))) 2 (62545209901/125000000000 : ℝ) (100072335843/200000000000 : ℝ) (49297886629/100000000000 : ℝ) (246489433149/500000000000 : ℝ) (496670272749/1000000000000 : ℝ) (496670272757/1000000000000 : ℝ) (124164138681/250000000000 : ℝ) (496656554733/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (123/1024 : ℝ))) 3 (496670272749/1000000000000 : ℝ) (496670272757/1000000000000 : ℝ) (124164138681/250000000000 : ℝ) (496656554733/1000000000000 : ℝ) (62082926717/125000000000 : ℝ) (99332682749/200000000000 : ℝ) (496663413689/1000000000000 : ℝ) (248331706849/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (123/1024 : ℝ))) 4 (62082926717/125000000000 : ℝ) (99332682749/200000000000 : ℝ) (496663413689/1000000000000 : ℝ) (248331706849/500000000000 : ℝ) (31041463357/62500000000 : ℝ) (248331706861/500000000000 : ℝ) (31041463357/62500000000 : ℝ) (248331706861/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (123/1024 : ℝ))) 5 (31041463357/62500000000 : ℝ) (248331706861/500000000000 : ℝ) (31041463357/62500000000 : ℝ) (248331706861/500000000000 : ℝ) (31041463357/62500000000 : ℝ) (248331706861/500000000000 : ℝ) (31041463357/62500000000 : ℝ) (248331706861/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (123/1024 : ℝ))) 6 (31041463357/62500000000 : ℝ) (248331706861/500000000000 : ℝ) (31041463357/62500000000 : ℝ) (248331706861/500000000000 : ℝ) (31041463357/62500000000 : ℝ) (248331706861/500000000000 : ℝ) (31041463357/62500000000 : ℝ) (248331706861/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (123/1024 : ℝ))) 7 (31041463357/62500000000 : ℝ) (248331706861/500000000000 : ℝ) (31041463357/62500000000 : ℝ) (248331706861/500000000000 : ℝ) (31041463357/62500000000 : ℝ) (248331706861/500000000000 : ℝ) (31041463357/62500000000 : ℝ) (248331706861/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (123/1024 : ℝ)) hmem 8 (496267384983/500000000000 : ℝ) (62033423123/62500000000 : ℝ) (496267384983/500000000000 : ℝ) (62033423123/62500000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (123/1024 : ℝ))) hcmem 8 (31041463357/62500000000 : ℝ) (248331706861/500000000000 : ℝ) (31041463357/62500000000 : ℝ) (248331706861/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (123/1024 : ℝ)) (496267384983/500000000000 : ℝ) (62033423123/62500000000 : ℝ) (31041463357/62500000000 : ℝ) (248331706861/500000000000 : ℝ) (786024922771/1000000000000 : ℝ) (78602492279/100000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0064_exp_lower
  have heNumeric : (410995358837/200000000000 : ℝ)/4 ≤ Real.exp (-266411922241/400000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410995358837/200000000000 : ℝ)/4 ≤ Real.exp ((983/8192 : ℝ)-(78602492279/100000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (983/8192 : ℝ) (123/1024 : ℝ) (78602492279/100000000000 : ℝ) (410995358837/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0065; no trusted numerical premise.
theorem cover8_leaf0065_exp_radius : (199624605064195063/200000000000000000 : ℝ) ≤ Real.exp ((-985/65536 : ℝ)/8) ∧ Real.exp ((-985/65536 : ℝ)/8) ≤ (249530756330243829/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-985/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0065_exp_lower : (460058535624538911/500000000000000000 : ℝ) ≤ Real.exp ((-666034925417/1000000000000 : ℝ)/8) ∧ Real.exp ((-666034925417/1000000000000 : ℝ)/8) ≤ (920117071249077823/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-666034925417/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0065_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256870784139/125000000000 : ℝ) ≤ 4*Real.exp (123/1024 : ℝ)*Real.exp (-mu (radius 8 (985/8192 : ℝ))) ∧ (20549/10000 : ℝ) < (256870784139/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (985/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0065_exp_radius
  have hrNumeric : (985082478077/1000000000000 : ℝ) ≤ Real.exp (-985/65536 : ℝ) ∧ Real.exp (-985/65536 : ℝ) ≤ (492541239039/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (985082478077/1000000000000 : ℝ) ≤ (radius 8 (985/8192 : ℝ)) ∧ (radius 8 (985/8192 : ℝ)) ≤ (492541239039/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (985/8192 : ℝ)) (985082478077/1000000000000 : ℝ) (492541239039/500000000000 : ℝ) (172082861969/1000000000000 : ℝ) (21510357747/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (985/8192 : ℝ)) (985082478077/1000000000000 : ℝ) (492541239039/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (985/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (985082478077/1000000000000 : ℝ) (492541239039/500000000000 : ℝ) (496270619519/500000000000 : ℝ) (992541239039/1000000000000 : ℝ) (992513213049/1000000000000 : ℝ) (19850264261/20000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (985/8192 : ℝ)) 1 (496270619519/500000000000 : ℝ) (992541239039/1000000000000 : ℝ) (992513213049/1000000000000 : ℝ) (19850264261/20000000000 : ℝ) (992527226043/1000000000000 : ℝ) (198505445209/200000000000 : ℝ) (124065903243/125000000000 : ℝ) (496263612973/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (985/8192 : ℝ)) 2 (992527226043/1000000000000 : ℝ) (198505445209/200000000000 : ℝ) (124065903243/125000000000 : ℝ) (496263612973/500000000000 : ℝ) (992527225993/1000000000000 : ℝ) (248131806499/250000000000 : ℝ) (992527225993/1000000000000 : ℝ) (248131806499/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (985/8192 : ℝ)) 3 (992527225993/1000000000000 : ℝ) (248131806499/250000000000 : ℝ) (992527225993/1000000000000 : ℝ) (248131806499/250000000000 : ℝ) (992527225993/1000000000000 : ℝ) (248131806499/250000000000 : ℝ) (992527225993/1000000000000 : ℝ) (248131806499/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (985/8192 : ℝ)) 4 (992527225993/1000000000000 : ℝ) (248131806499/250000000000 : ℝ) (992527225993/1000000000000 : ℝ) (248131806499/250000000000 : ℝ) (992527225993/1000000000000 : ℝ) (248131806499/250000000000 : ℝ) (992527225993/1000000000000 : ℝ) (248131806499/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (985/8192 : ℝ)) 5 (992527225993/1000000000000 : ℝ) (248131806499/250000000000 : ℝ) (992527225993/1000000000000 : ℝ) (248131806499/250000000000 : ℝ) (992527225993/1000000000000 : ℝ) (248131806499/250000000000 : ℝ) (992527225993/1000000000000 : ℝ) (248131806499/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (985/8192 : ℝ)) 6 (992527225993/1000000000000 : ℝ) (248131806499/250000000000 : ℝ) (992527225993/1000000000000 : ℝ) (248131806499/250000000000 : ℝ) (992527225993/1000000000000 : ℝ) (248131806499/250000000000 : ℝ) (992527225993/1000000000000 : ℝ) (248131806499/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (985/8192 : ℝ)) 7 (992527225993/1000000000000 : ℝ) (248131806499/250000000000 : ℝ) (992527225993/1000000000000 : ℝ) (248131806499/250000000000 : ℝ) (992527225993/1000000000000 : ℝ) (248131806499/250000000000 : ℝ) (992527225993/1000000000000 : ℝ) (248131806499/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (985/8192 : ℝ))) (172082861969/1000000000000 : ℝ) (21510357747/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (985/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (172082861969/1000000000000 : ℝ) (21510357747/125000000000 : ℝ) (73255178873/125000000000 : ℝ) (146510357747/250000000000 : ℝ) (103707178503/250000000000 : ℝ) (414828714021/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (985/8192 : ℝ))) 1 (73255178873/125000000000 : ℝ) (146510357747/250000000000 : ℝ) (103707178503/250000000000 : ℝ) (414828714021/1000000000000 : ℝ) (250217536249/500000000000 : ℝ) (100087014501/200000000000 : ℝ) (493058630563/1000000000000 : ℝ) (493058630571/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (985/8192 : ℝ))) 2 (250217536249/500000000000 : ℝ) (100087014501/200000000000 : ℝ) (493058630563/1000000000000 : ℝ) (493058630571/1000000000000 : ℝ) (49674685153/100000000000 : ℝ) (248373425769/500000000000 : ℝ) (496733159283/1000000000000 : ℝ) (496733159291/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (985/8192 : ℝ))) 3 (49674685153/100000000000 : ℝ) (248373425769/500000000000 : ℝ) (496733159283/1000000000000 : ℝ) (496733159291/1000000000000 : ℝ) (248370002703/500000000000 : ℝ) (99348001083/200000000000 : ℝ) (496740005359/1000000000000 : ℝ) (62092500671/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (985/8192 : ℝ))) 4 (248370002703/500000000000 : ℝ) (99348001083/200000000000 : ℝ) (496740005359/1000000000000 : ℝ) (62092500671/125000000000 : ℝ) (248370002691/500000000000 : ℝ) (31046250337/62500000000 : ℝ) (248370002691/500000000000 : ℝ) (31046250337/62500000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (985/8192 : ℝ))) 5 (248370002691/500000000000 : ℝ) (31046250337/62500000000 : ℝ) (248370002691/500000000000 : ℝ) (31046250337/62500000000 : ℝ) (248370002691/500000000000 : ℝ) (31046250337/62500000000 : ℝ) (248370002691/500000000000 : ℝ) (31046250337/62500000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (985/8192 : ℝ))) 6 (248370002691/500000000000 : ℝ) (31046250337/62500000000 : ℝ) (248370002691/500000000000 : ℝ) (31046250337/62500000000 : ℝ) (248370002691/500000000000 : ℝ) (31046250337/62500000000 : ℝ) (248370002691/500000000000 : ℝ) (31046250337/62500000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (985/8192 : ℝ))) 7 (248370002691/500000000000 : ℝ) (31046250337/62500000000 : ℝ) (248370002691/500000000000 : ℝ) (31046250337/62500000000 : ℝ) (248370002691/500000000000 : ℝ) (31046250337/62500000000 : ℝ) (248370002691/500000000000 : ℝ) (31046250337/62500000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (985/8192 : ℝ)) hmem 8 (992527225993/1000000000000 : ℝ) (248131806499/250000000000 : ℝ) (992527225993/1000000000000 : ℝ) (248131806499/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (985/8192 : ℝ))) hcmem 8 (248370002691/500000000000 : ℝ) (31046250337/62500000000 : ℝ) (248370002691/500000000000 : ℝ) (31046250337/62500000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (985/8192 : ℝ)) (992527225993/1000000000000 : ℝ) (248131806499/250000000000 : ℝ) (248370002691/500000000000 : ℝ) (31046250337/62500000000 : ℝ) (393076056449/500000000000 : ℝ) (786152112917/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0065_exp_lower
  have heNumeric : (256870784139/125000000000 : ℝ)/4 ≤ Real.exp (-666034925417/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256870784139/125000000000 : ℝ)/4 ≤ Real.exp ((123/1024 : ℝ)-(786152112917/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (123/1024 : ℝ) (985/8192 : ℝ) (786152112917/1000000000000 : ℝ) (256870784139/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0066; no trusted numerical premise.
theorem cover8_leaf0066_exp_radius : (199624224310840633/200000000000000000 : ℝ) ≤ Real.exp ((-493/32768 : ℝ)/8) ∧ Real.exp ((-493/32768 : ℝ)/8) ≤ (499060560777101583/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-493/32768 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0066_exp_lower : (57507280782036667/62500000000000000 : ℝ) ≤ Real.exp ((-1332079914539/2000000000000 : ℝ)/8) ∧ Real.exp ((-1332079914539/2000000000000 : ℝ)/8) ≤ (920116492512586673/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1332079914539/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0066_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054955932851/1000000000000 : ℝ) ≤ 4*Real.exp (985/8192 : ℝ)*Real.exp (-mu (radius 8 (493/4096 : ℝ))) ∧ (20549/10000 : ℝ) < (2054955932851/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (493/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0066_exp_radius
  have hrNumeric : (492533723513/500000000000 : ℝ) ≤ Real.exp (-493/32768 : ℝ) ∧ Real.exp (-493/32768 : ℝ) ≤ (985067447027/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492533723513/500000000000 : ℝ) ≤ (radius 8 (493/4096 : ℝ)) ∧ (radius 8 (493/4096 : ℝ)) ≤ (985067447027/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (493/4096 : ℝ)) (492533723513/500000000000 : ℝ) (985067447027/1000000000000 : ℝ) (172168884551/1000000000000 : ℝ) (86084442279/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (493/4096 : ℝ)) (492533723513/500000000000 : ℝ) (985067447027/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (493/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492533723513/500000000000 : ℝ) (985067447027/1000000000000 : ℝ) (992533723513/1000000000000 : ℝ) (496266861757/500000000000 : ℝ) (992505640803/1000000000000 : ℝ) (248126410201/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (493/4096 : ℝ)) 1 (992533723513/1000000000000 : ℝ) (496266861757/500000000000 : ℝ) (992505640803/1000000000000 : ℝ) (248126410201/250000000000 : ℝ) (496259841079/500000000000 : ℝ) (992519682159/1000000000000 : ℝ) (496259841029/500000000000 : ℝ) (49625984103/50000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (493/4096 : ℝ)) 2 (496259841079/500000000000 : ℝ) (992519682159/1000000000000 : ℝ) (496259841029/500000000000 : ℝ) (49625984103/50000000000 : ℝ) (248129920527/250000000000 : ℝ) (99251968211/100000000000 : ℝ) (992519682107/1000000000000 : ℝ) (99251968211/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (493/4096 : ℝ)) 3 (248129920527/250000000000 : ℝ) (99251968211/100000000000 : ℝ) (992519682107/1000000000000 : ℝ) (99251968211/100000000000 : ℝ) (992519682107/1000000000000 : ℝ) (99251968211/100000000000 : ℝ) (992519682107/1000000000000 : ℝ) (99251968211/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (493/4096 : ℝ)) 4 (992519682107/1000000000000 : ℝ) (99251968211/100000000000 : ℝ) (992519682107/1000000000000 : ℝ) (99251968211/100000000000 : ℝ) (992519682107/1000000000000 : ℝ) (99251968211/100000000000 : ℝ) (992519682107/1000000000000 : ℝ) (99251968211/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (493/4096 : ℝ)) 5 (992519682107/1000000000000 : ℝ) (99251968211/100000000000 : ℝ) (992519682107/1000000000000 : ℝ) (99251968211/100000000000 : ℝ) (992519682107/1000000000000 : ℝ) (99251968211/100000000000 : ℝ) (992519682107/1000000000000 : ℝ) (99251968211/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (493/4096 : ℝ)) 6 (992519682107/1000000000000 : ℝ) (99251968211/100000000000 : ℝ) (992519682107/1000000000000 : ℝ) (99251968211/100000000000 : ℝ) (992519682107/1000000000000 : ℝ) (99251968211/100000000000 : ℝ) (992519682107/1000000000000 : ℝ) (99251968211/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (493/4096 : ℝ)) 7 (992519682107/1000000000000 : ℝ) (99251968211/100000000000 : ℝ) (992519682107/1000000000000 : ℝ) (99251968211/100000000000 : ℝ) (992519682107/1000000000000 : ℝ) (99251968211/100000000000 : ℝ) (992519682107/1000000000000 : ℝ) (99251968211/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (493/4096 : ℝ))) (172168884551/1000000000000 : ℝ) (86084442279/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (493/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (172168884551/1000000000000 : ℝ) (86084442279/500000000000 : ℝ) (23443377691/40000000000 : ℝ) (586084442279/1000000000000 : ℝ) (414932385517/1000000000000 : ℝ) (207466192763/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (493/4096 : ℝ))) 1 (23443377691/40000000000 : ℝ) (586084442279/1000000000000 : ℝ) (414932385517/1000000000000 : ℝ) (207466192763/500000000000 : ℝ) (62563551737/125000000000 : ℝ) (500508413903/1000000000000 : ℝ) (493138333277/1000000000000 : ℝ) (98627666657/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (493/4096 : ℝ))) 2 (62563551737/125000000000 : ℝ) (500508413903/1000000000000 : ℝ) (493138333277/1000000000000 : ℝ) (98627666657/200000000000 : ℝ) (248411686793/500000000000 : ℝ) (248411686797/500000000000 : ℝ) (9936194141/20000000000 : ℝ) (496809707059/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (493/4096 : ℝ))) 3 (248411686793/500000000000 : ℝ) (248411686797/500000000000 : ℝ) (9936194141/20000000000 : ℝ) (496809707059/1000000000000 : ℝ) (248408270159/500000000000 : ℝ) (496816540327/1000000000000 : ℝ) (496816540271/1000000000000 : ℝ) (12420413507/25000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (493/4096 : ℝ))) 4 (248408270159/500000000000 : ℝ) (496816540327/1000000000000 : ℝ) (496816540271/1000000000000 : ℝ) (12420413507/25000000000 : ℝ) (248408270147/500000000000 : ℝ) (31051033769/62500000000 : ℝ) (248408270147/500000000000 : ℝ) (31051033769/62500000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (493/4096 : ℝ))) 5 (248408270147/500000000000 : ℝ) (31051033769/62500000000 : ℝ) (248408270147/500000000000 : ℝ) (31051033769/62500000000 : ℝ) (248408270147/500000000000 : ℝ) (31051033769/62500000000 : ℝ) (248408270147/500000000000 : ℝ) (31051033769/62500000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (493/4096 : ℝ))) 6 (248408270147/500000000000 : ℝ) (31051033769/62500000000 : ℝ) (248408270147/500000000000 : ℝ) (31051033769/62500000000 : ℝ) (248408270147/500000000000 : ℝ) (31051033769/62500000000 : ℝ) (248408270147/500000000000 : ℝ) (31051033769/62500000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (493/4096 : ℝ))) 7 (248408270147/500000000000 : ℝ) (31051033769/62500000000 : ℝ) (248408270147/500000000000 : ℝ) (31051033769/62500000000 : ℝ) (248408270147/500000000000 : ℝ) (31051033769/62500000000 : ℝ) (248408270147/500000000000 : ℝ) (31051033769/62500000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (493/4096 : ℝ)) hmem 8 (992519682107/1000000000000 : ℝ) (99251968211/100000000000 : ℝ) (992519682107/1000000000000 : ℝ) (99251968211/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (493/4096 : ℝ))) hcmem 8 (248408270147/500000000000 : ℝ) (31051033769/62500000000 : ℝ) (248408270147/500000000000 : ℝ) (31051033769/62500000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (493/4096 : ℝ)) (992519682107/1000000000000 : ℝ) (99251968211/100000000000 : ℝ) (248408270147/500000000000 : ℝ) (31051033769/62500000000 : ℝ) (786279215063/1000000000000 : ℝ) (393139607541/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0066_exp_lower
  have heNumeric : (2054955932851/1000000000000 : ℝ)/4 ≤ Real.exp (-1332079914539/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054955932851/1000000000000 : ℝ)/4 ≤ Real.exp ((985/8192 : ℝ)-(393139607541/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (985/8192 : ℝ) (493/4096 : ℝ) (393139607541/500000000000 : ℝ) (2054955932851/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0067; no trusted numerical premise.
theorem cover8_leaf0067_exp_radius : (499059608895531079/500000000000000000 : ℝ) ≤ Real.exp ((-987/65536 : ℝ)/8) ∧ Real.exp ((-987/65536 : ℝ)/8) ≤ (998119217791062159/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-987/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0067_exp_lower : (920115923874616731/1000000000000000000 : ℝ) ≤ Real.exp ((-666044901323/1000000000000 : ℝ)/8) ∧ Real.exp ((-666044901323/1000000000000 : ℝ)/8) ≤ (230028980968654183/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-666044901323/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0067_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256868221633/125000000000 : ℝ) ≤ 4*Real.exp (493/4096 : ℝ)*Real.exp (-mu (radius 8 (987/8192 : ℝ))) ∧ (20549/10000 : ℝ) < (256868221633/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (987/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0067_exp_radius
  have hrNumeric : (246263104051/250000000000 : ℝ) ≤ Real.exp (-987/65536 : ℝ) ∧ Real.exp (-987/65536 : ℝ) ≤ (197010483241/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246263104051/250000000000 : ℝ) ≤ (radius 8 (987/8192 : ℝ)) ∧ (radius 8 (987/8192 : ℝ)) ≤ (197010483241/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (987/8192 : ℝ)) (246263104051/250000000000 : ℝ) (197010483241/200000000000 : ℝ) (172254861553/1000000000000 : ℝ) (172254861559/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (987/8192 : ℝ)) (246263104051/250000000000 : ℝ) (197010483241/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (987/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246263104051/250000000000 : ℝ) (197010483241/200000000000 : ℝ) (496263104051/500000000000 : ℝ) (992526208103/1000000000000 : ℝ) (496249034307/500000000000 : ℝ) (124062258577/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (987/8192 : ℝ)) 1 (496263104051/500000000000 : ℝ) (992526208103/1000000000000 : ℝ) (496249034307/500000000000 : ℝ) (124062258577/125000000000 : ℝ) (496256069179/500000000000 : ℝ) (24812803459/25000000000 : ℝ) (496256069129/500000000000 : ℝ) (49625606913/50000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (987/8192 : ℝ)) 2 (496256069179/500000000000 : ℝ) (24812803459/25000000000 : ℝ) (496256069129/500000000000 : ℝ) (49625606913/50000000000 : ℝ) (248128034577/250000000000 : ℝ) (99251213831/100000000000 : ℝ) (992512138307/1000000000000 : ℝ) (99251213831/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (987/8192 : ℝ)) 3 (248128034577/250000000000 : ℝ) (99251213831/100000000000 : ℝ) (992512138307/1000000000000 : ℝ) (99251213831/100000000000 : ℝ) (992512138307/1000000000000 : ℝ) (99251213831/100000000000 : ℝ) (992512138307/1000000000000 : ℝ) (99251213831/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (987/8192 : ℝ)) 4 (992512138307/1000000000000 : ℝ) (99251213831/100000000000 : ℝ) (992512138307/1000000000000 : ℝ) (99251213831/100000000000 : ℝ) (992512138307/1000000000000 : ℝ) (99251213831/100000000000 : ℝ) (992512138307/1000000000000 : ℝ) (99251213831/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (987/8192 : ℝ)) 5 (992512138307/1000000000000 : ℝ) (99251213831/100000000000 : ℝ) (992512138307/1000000000000 : ℝ) (99251213831/100000000000 : ℝ) (992512138307/1000000000000 : ℝ) (99251213831/100000000000 : ℝ) (992512138307/1000000000000 : ℝ) (99251213831/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (987/8192 : ℝ)) 6 (992512138307/1000000000000 : ℝ) (99251213831/100000000000 : ℝ) (992512138307/1000000000000 : ℝ) (99251213831/100000000000 : ℝ) (992512138307/1000000000000 : ℝ) (99251213831/100000000000 : ℝ) (992512138307/1000000000000 : ℝ) (99251213831/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (987/8192 : ℝ)) 7 (992512138307/1000000000000 : ℝ) (99251213831/100000000000 : ℝ) (992512138307/1000000000000 : ℝ) (99251213831/100000000000 : ℝ) (992512138307/1000000000000 : ℝ) (99251213831/100000000000 : ℝ) (992512138307/1000000000000 : ℝ) (99251213831/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (987/8192 : ℝ))) (172254861553/1000000000000 : ℝ) (172254861559/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (987/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (172254861553/1000000000000 : ℝ) (172254861559/1000000000000 : ℝ) (73265928847/125000000000 : ℝ) (29306371539/50000000000 : ℝ) (83007195243/200000000000 : ℝ) (415035976223/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (987/8192 : ℝ))) 1 (73265928847/125000000000 : ℝ) (29306371539/50000000000 : ℝ) (83007195243/200000000000 : ℝ) (415035976223/1000000000000 : ℝ) (100116340699/200000000000 : ℝ) (250290851751/500000000000 : ℝ) (493217974549/1000000000000 : ℝ) (123304493639/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (987/8192 : ℝ))) 2 (100116340699/200000000000 : ℝ) (250290851751/500000000000 : ℝ) (493217974549/1000000000000 : ℝ) (123304493639/250000000000 : ℝ) (248449919511/500000000000 : ℝ) (496899839029/1000000000000 : ℝ) (124221549533/250000000000 : ℝ) (24844309907/50000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (987/8192 : ℝ))) 3 (248449919511/500000000000 : ℝ) (496899839029/1000000000000 : ℝ) (124221549533/250000000000 : ℝ) (24844309907/50000000000 : ℝ) (496893018577/1000000000000 : ℝ) (99378603717/200000000000 : ℝ) (49689301853/100000000000 : ℝ) (248446509269/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (987/8192 : ℝ))) 4 (496893018577/1000000000000 : ℝ) (99378603717/200000000000 : ℝ) (49689301853/100000000000 : ℝ) (248446509269/500000000000 : ℝ) (496893018553/1000000000000 : ℝ) (248446509281/500000000000 : ℝ) (496893018553/1000000000000 : ℝ) (248446509281/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (987/8192 : ℝ))) 5 (496893018553/1000000000000 : ℝ) (248446509281/500000000000 : ℝ) (496893018553/1000000000000 : ℝ) (248446509281/500000000000 : ℝ) (496893018553/1000000000000 : ℝ) (248446509281/500000000000 : ℝ) (496893018553/1000000000000 : ℝ) (248446509281/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (987/8192 : ℝ))) 6 (496893018553/1000000000000 : ℝ) (248446509281/500000000000 : ℝ) (496893018553/1000000000000 : ℝ) (248446509281/500000000000 : ℝ) (496893018553/1000000000000 : ℝ) (248446509281/500000000000 : ℝ) (496893018553/1000000000000 : ℝ) (248446509281/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (987/8192 : ℝ))) 7 (496893018553/1000000000000 : ℝ) (248446509281/500000000000 : ℝ) (496893018553/1000000000000 : ℝ) (248446509281/500000000000 : ℝ) (496893018553/1000000000000 : ℝ) (248446509281/500000000000 : ℝ) (496893018553/1000000000000 : ℝ) (248446509281/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (987/8192 : ℝ)) hmem 8 (992512138307/1000000000000 : ℝ) (99251213831/100000000000 : ℝ) (992512138307/1000000000000 : ℝ) (99251213831/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (987/8192 : ℝ))) hcmem 8 (496893018553/1000000000000 : ℝ) (248446509281/500000000000 : ℝ) (496893018553/1000000000000 : ℝ) (248446509281/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (987/8192 : ℝ)) (992512138307/1000000000000 : ℝ) (99251213831/100000000000 : ℝ) (496893018553/1000000000000 : ℝ) (248446509281/500000000000 : ℝ) (786406229431/1000000000000 : ℝ) (98300778681/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0067_exp_lower
  have heNumeric : (256868221633/125000000000 : ℝ)/4 ≤ Real.exp (-666044901323/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256868221633/125000000000 : ℝ)/4 ≤ Real.exp ((493/4096 : ℝ)-(98300778681/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (493/4096 : ℝ) (987/8192 : ℝ) (98300778681/125000000000 : ℝ) (256868221633/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0068; no trusted numerical premise.
theorem cover8_leaf0068_exp_radius : (998117314031552287/1000000000000000000 : ℝ) ≤ Real.exp ((-247/16384 : ℝ)/8) ∧ Real.exp ((-247/16384 : ℝ)/8) ≤ (31191166063486009/31250000000000000 : ℝ) := by
  have h := exp_small_bounds ((-247/16384 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0068_exp_lower : (28753605166187879/31250000000000000 : ℝ) ≤ Real.exp ((-1332099515453/2000000000000 : ℝ)/8) ∧ Real.exp ((-1332099515453/2000000000000 : ℝ)/8) ≤ (920115365318012129/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1332099515453/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0068_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027467896721/500000000000 : ℝ) ≤ 4*Real.exp (987/8192 : ℝ)*Real.exp (-mu (radius 8 (247/2048 : ℝ))) ∧ (20549/10000 : ℝ) < (1027467896721/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (247/2048 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0068_exp_radius
  have hrNumeric : (246259346403/250000000000 : ℝ) ≤ Real.exp (-247/16384 : ℝ) ∧ Real.exp (-247/16384 : ℝ) ≤ (985037385613/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246259346403/250000000000 : ℝ) ≤ (radius 8 (247/2048 : ℝ)) ∧ (radius 8 (247/2048 : ℝ)) ≤ (985037385613/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (247/2048 : ℝ)) (246259346403/250000000000 : ℝ) (985037385613/1000000000000 : ℝ) (172340793037/1000000000000 : ℝ) (172340793043/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (247/2048 : ℝ)) (246259346403/250000000000 : ℝ) (985037385613/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (247/2048 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246259346403/250000000000 : ℝ) (985037385613/1000000000000 : ℝ) (496259346403/500000000000 : ℝ) (992518692807/1000000000000 : ℝ) (248122624121/250000000000 : ℝ) (198498099297/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (247/2048 : ℝ)) 1 (496259346403/500000000000 : ℝ) (992518692807/1000000000000 : ℝ) (248122624121/250000000000 : ℝ) (198498099297/200000000000 : ℝ) (198500918929/200000000000 : ℝ) (496252297323/500000000000 : ℝ) (62031537159/62500000000 : ℝ) (496252297273/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (247/2048 : ℝ)) 2 (198500918929/200000000000 : ℝ) (496252297323/500000000000 : ℝ) (62031537159/62500000000 : ℝ) (496252297273/500000000000 : ℝ) (496252297297/500000000000 : ℝ) (248126148649/250000000000 : ℝ) (496252297297/500000000000 : ℝ) (248126148649/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (247/2048 : ℝ)) 3 (496252297297/500000000000 : ℝ) (248126148649/250000000000 : ℝ) (496252297297/500000000000 : ℝ) (248126148649/250000000000 : ℝ) (496252297297/500000000000 : ℝ) (248126148649/250000000000 : ℝ) (496252297297/500000000000 : ℝ) (248126148649/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (247/2048 : ℝ)) 4 (496252297297/500000000000 : ℝ) (248126148649/250000000000 : ℝ) (496252297297/500000000000 : ℝ) (248126148649/250000000000 : ℝ) (496252297297/500000000000 : ℝ) (248126148649/250000000000 : ℝ) (496252297297/500000000000 : ℝ) (248126148649/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (247/2048 : ℝ)) 5 (496252297297/500000000000 : ℝ) (248126148649/250000000000 : ℝ) (496252297297/500000000000 : ℝ) (248126148649/250000000000 : ℝ) (496252297297/500000000000 : ℝ) (248126148649/250000000000 : ℝ) (496252297297/500000000000 : ℝ) (248126148649/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (247/2048 : ℝ)) 6 (496252297297/500000000000 : ℝ) (248126148649/250000000000 : ℝ) (496252297297/500000000000 : ℝ) (248126148649/250000000000 : ℝ) (496252297297/500000000000 : ℝ) (248126148649/250000000000 : ℝ) (496252297297/500000000000 : ℝ) (248126148649/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (247/2048 : ℝ)) 7 (496252297297/500000000000 : ℝ) (248126148649/250000000000 : ℝ) (496252297297/500000000000 : ℝ) (248126148649/250000000000 : ℝ) (496252297297/500000000000 : ℝ) (248126148649/250000000000 : ℝ) (496252297297/500000000000 : ℝ) (248126148649/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (247/2048 : ℝ))) (172340793037/1000000000000 : ℝ) (172340793043/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (247/2048 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (172340793037/1000000000000 : ℝ) (172340793043/1000000000000 : ℝ) (293085198259/500000000000 : ℝ) (293085198261/500000000000 : ℝ) (415139486241/1000000000000 : ℝ) (415139486249/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (247/2048 : ℝ))) 1 (293085198259/500000000000 : ℝ) (293085198261/500000000000 : ℝ) (415139486241/1000000000000 : ℝ) (415139486249/1000000000000 : ℝ) (500654941379/1000000000000 : ℝ) (250327470693/500000000000 : ℝ) (123324388621/250000000000 : ℝ) (493297554491/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (247/2048 : ℝ))) 2 (500654941379/1000000000000 : ℝ) (250327470693/500000000000 : ℝ) (123324388621/250000000000 : ℝ) (493297554491/1000000000000 : ℝ) (496976247931/1000000000000 : ℝ) (496976247939/1000000000000 : ℝ) (248481316311/500000000000 : ℝ) (49696263263/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (247/2048 : ℝ))) 3 (496976247931/1000000000000 : ℝ) (496976247939/1000000000000 : ℝ) (248481316311/500000000000 : ℝ) (49696263263/100000000000 : ℝ) (124242360069/250000000000 : ℝ) (99393888057/200000000000 : ℝ) (496969440229/1000000000000 : ℝ) (248484720119/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (247/2048 : ℝ))) 4 (124242360069/250000000000 : ℝ) (99393888057/200000000000 : ℝ) (496969440229/1000000000000 : ℝ) (248484720119/500000000000 : ℝ) (124242360063/250000000000 : ℝ) (248484720131/500000000000 : ℝ) (124242360063/250000000000 : ℝ) (248484720131/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (247/2048 : ℝ))) 5 (124242360063/250000000000 : ℝ) (248484720131/500000000000 : ℝ) (124242360063/250000000000 : ℝ) (248484720131/500000000000 : ℝ) (124242360063/250000000000 : ℝ) (248484720131/500000000000 : ℝ) (124242360063/250000000000 : ℝ) (248484720131/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (247/2048 : ℝ))) 6 (124242360063/250000000000 : ℝ) (248484720131/500000000000 : ℝ) (124242360063/250000000000 : ℝ) (248484720131/500000000000 : ℝ) (124242360063/250000000000 : ℝ) (248484720131/500000000000 : ℝ) (124242360063/250000000000 : ℝ) (248484720131/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (247/2048 : ℝ))) 7 (124242360063/250000000000 : ℝ) (248484720131/500000000000 : ℝ) (124242360063/250000000000 : ℝ) (248484720131/500000000000 : ℝ) (124242360063/250000000000 : ℝ) (248484720131/500000000000 : ℝ) (124242360063/250000000000 : ℝ) (248484720131/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (247/2048 : ℝ)) hmem 8 (496252297297/500000000000 : ℝ) (248126148649/250000000000 : ℝ) (496252297297/500000000000 : ℝ) (248126148649/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (247/2048 : ℝ))) hcmem 8 (124242360063/250000000000 : ℝ) (248484720131/500000000000 : ℝ) (124242360063/250000000000 : ℝ) (248484720131/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (247/2048 : ℝ)) (496252297297/500000000000 : ℝ) (248126148649/250000000000 : ℝ) (124242360063/250000000000 : ℝ) (248484720131/500000000000 : ℝ) (393266578073/500000000000 : ℝ) (196633289041/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0068_exp_lower
  have heNumeric : (1027467896721/500000000000 : ℝ)/4 ≤ Real.exp (-1332099515453/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027467896721/500000000000 : ℝ)/4 ≤ Real.exp ((987/8192 : ℝ)-(196633289041/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (987/8192 : ℝ) (247/2048 : ℝ) (196633289041/250000000000 : ℝ) (1027467896721/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0069; no trusted numerical premise.
theorem cover8_leaf0069_exp_radius : (499057705137836773/500000000000000000 : ℝ) ≤ Real.exp ((-989/65536 : ℝ)/8) ∧ Real.exp ((-989/65536 : ℝ)/8) ≤ (998115410275673547/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-989/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0069_exp_lower : (18402296336477843/20000000000000000 : ℝ) ≤ Real.exp ((-166513631661/250000000000 : ℝ)/8) ∧ Real.exp ((-166513631661/250000000000 : ℝ)/8) ≤ (920114816823892151/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-166513631661/250000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0069_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054925993647/1000000000000 : ℝ) ≤ 4*Real.exp (247/2048 : ℝ)*Real.exp (-mu (radius 8 (989/8192 : ℝ))) ∧ (20549/10000 : ℝ) < (2054925993647/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (989/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0069_exp_radius
  have hrNumeric : (985022355249/1000000000000 : ℝ) ≤ Real.exp (-989/65536 : ℝ) ∧ Real.exp (-989/65536 : ℝ) ≤ (3940089421/4000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (985022355249/1000000000000 : ℝ) ≤ (radius 8 (989/8192 : ℝ)) ∧ (radius 8 (989/8192 : ℝ)) ≤ (3940089421/4000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (989/8192 : ℝ)) (985022355249/1000000000000 : ℝ) (3940089421/4000000000 : ℝ) (172426679077/1000000000000 : ℝ) (43106669771/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (989/8192 : ℝ)) (985022355249/1000000000000 : ℝ) (3940089421/4000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (989/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (985022355249/1000000000000 : ℝ) (3940089421/4000000000 : ℝ) (124063897203/125000000000 : ℝ) (7940089421/8000000000 : ℝ) (992482924411/1000000000000 : ℝ) (992482924413/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (989/8192 : ℝ)) 1 (124063897203/125000000000 : ℝ) (7940089421/8000000000 : ℝ) (992482924411/1000000000000 : ℝ) (992482924413/1000000000000 : ℝ) (992497051017/1000000000000 : ℝ) (992497051019/1000000000000 : ℝ) (248124262729/250000000000 : ℝ) (992497050919/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (989/8192 : ℝ)) 2 (992497051017/1000000000000 : ℝ) (992497051019/1000000000000 : ℝ) (248124262729/250000000000 : ℝ) (992497050919/1000000000000 : ℝ) (496248525483/500000000000 : ℝ) (992497050969/1000000000000 : ℝ) (496248525483/500000000000 : ℝ) (992497050969/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (989/8192 : ℝ)) 3 (496248525483/500000000000 : ℝ) (992497050969/1000000000000 : ℝ) (496248525483/500000000000 : ℝ) (992497050969/1000000000000 : ℝ) (496248525483/500000000000 : ℝ) (992497050969/1000000000000 : ℝ) (496248525483/500000000000 : ℝ) (992497050969/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (989/8192 : ℝ)) 4 (496248525483/500000000000 : ℝ) (992497050969/1000000000000 : ℝ) (496248525483/500000000000 : ℝ) (992497050969/1000000000000 : ℝ) (496248525483/500000000000 : ℝ) (992497050969/1000000000000 : ℝ) (496248525483/500000000000 : ℝ) (992497050969/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (989/8192 : ℝ)) 5 (496248525483/500000000000 : ℝ) (992497050969/1000000000000 : ℝ) (496248525483/500000000000 : ℝ) (992497050969/1000000000000 : ℝ) (496248525483/500000000000 : ℝ) (992497050969/1000000000000 : ℝ) (496248525483/500000000000 : ℝ) (992497050969/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (989/8192 : ℝ)) 6 (496248525483/500000000000 : ℝ) (992497050969/1000000000000 : ℝ) (496248525483/500000000000 : ℝ) (992497050969/1000000000000 : ℝ) (496248525483/500000000000 : ℝ) (992497050969/1000000000000 : ℝ) (496248525483/500000000000 : ℝ) (992497050969/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (989/8192 : ℝ)) 7 (496248525483/500000000000 : ℝ) (992497050969/1000000000000 : ℝ) (496248525483/500000000000 : ℝ) (992497050969/1000000000000 : ℝ) (496248525483/500000000000 : ℝ) (992497050969/1000000000000 : ℝ) (496248525483/500000000000 : ℝ) (992497050969/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (989/8192 : ℝ))) (172426679077/1000000000000 : ℝ) (43106669771/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (989/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (172426679077/1000000000000 : ℝ) (43106669771/250000000000 : ℝ) (293106669769/500000000000 : ℝ) (293106669771/500000000000 : ℝ) (83048583149/200000000000 : ℝ) (83048583151/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (989/8192 : ℝ))) 1 (293106669769/500000000000 : ℝ) (293106669771/500000000000 : ℝ) (83048583149/200000000000 : ℝ) (83048583151/200000000000 : ℝ) (500728127641/1000000000000 : ℝ) (500728127649/1000000000000 : ℝ) (246688536599/500000000000 : ℝ) (493377073207/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (989/8192 : ℝ))) 2 (500728127641/1000000000000 : ℝ) (500728127649/1000000000000 : ℝ) (246688536599/500000000000 : ℝ) (493377073207/1000000000000 : ℝ) (497052600419/1000000000000 : ℝ) (124263150107/250000000000 : ℝ) (795262417/1600000000 : ℝ) (248519505317/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (989/8192 : ℝ))) 3 (497052600419/1000000000000 : ℝ) (124263150107/250000000000 : ℝ) (795262417/1600000000 : ℝ) (248519505317/500000000000 : ℝ) (248522902761/500000000000 : ℝ) (497045805531/1000000000000 : ℝ) (19881832219/40000000000 : ℝ) (99409161097/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (989/8192 : ℝ))) 4 (248522902761/500000000000 : ℝ) (497045805531/1000000000000 : ℝ) (19881832219/40000000000 : ℝ) (99409161097/200000000000 : ℝ) (248522902749/500000000000 : ℝ) (124261451377/250000000000 : ℝ) (248522902749/500000000000 : ℝ) (124261451377/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (989/8192 : ℝ))) 5 (248522902749/500000000000 : ℝ) (124261451377/250000000000 : ℝ) (248522902749/500000000000 : ℝ) (124261451377/250000000000 : ℝ) (248522902749/500000000000 : ℝ) (124261451377/250000000000 : ℝ) (248522902749/500000000000 : ℝ) (124261451377/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (989/8192 : ℝ))) 6 (248522902749/500000000000 : ℝ) (124261451377/250000000000 : ℝ) (248522902749/500000000000 : ℝ) (124261451377/250000000000 : ℝ) (248522902749/500000000000 : ℝ) (124261451377/250000000000 : ℝ) (248522902749/500000000000 : ℝ) (124261451377/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (989/8192 : ℝ))) 7 (248522902749/500000000000 : ℝ) (124261451377/250000000000 : ℝ) (248522902749/500000000000 : ℝ) (124261451377/250000000000 : ℝ) (248522902749/500000000000 : ℝ) (124261451377/250000000000 : ℝ) (248522902749/500000000000 : ℝ) (124261451377/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (989/8192 : ℝ)) hmem 8 (496248525483/500000000000 : ℝ) (992497050969/1000000000000 : ℝ) (496248525483/500000000000 : ℝ) (992497050969/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (989/8192 : ℝ))) hcmem 8 (248522902749/500000000000 : ℝ) (124261451377/250000000000 : ℝ) (248522902749/500000000000 : ℝ) (124261451377/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (989/8192 : ℝ)) (496248525483/500000000000 : ℝ) (992497050969/1000000000000 : ℝ) (248522902749/500000000000 : ℝ) (124261451377/250000000000 : ℝ) (6293279963/8000000000 : ℝ) (393329997697/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0069_exp_lower
  have heNumeric : (2054925993647/1000000000000 : ℝ)/4 ≤ Real.exp (-166513631661/250000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054925993647/1000000000000 : ℝ)/4 ≤ Real.exp ((247/2048 : ℝ)-(393329997697/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (247/2048 : ℝ) (989/8192 : ℝ) (393329997697/500000000000 : ℝ) (2054925993647/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0070; no trusted numerical premise.
theorem cover8_leaf0070_exp_radius : (124764188315428241/125000000000000000 : ℝ) ≤ Real.exp ((-495/32768 : ℝ)/8) ∧ Real.exp ((-495/32768 : ℝ)/8) ≤ (998113506523425929/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-495/32768 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0070_exp_lower : (920114278374641617/1000000000000000000 : ℝ) ≤ Real.exp ((-1332118416457/2000000000000 : ℝ)/8) ∧ Real.exp ((-1332118416457/2000000000000 : ℝ)/8) ≤ (460057139187320809/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1332118416457/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0070_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054916373359/1000000000000 : ℝ) ≤ 4*Real.exp (989/8192 : ℝ)*Real.exp (-mu (radius 8 (495/4096 : ℝ))) ∧ (20549/10000 : ℝ) < (2054916373359/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (495/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0070_exp_radius
  have hrNumeric : (197001465023/200000000000 : ℝ) ≤ Real.exp (-495/32768 : ℝ) ∧ Real.exp (-495/32768 : ℝ) ≤ (246251831279/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (197001465023/200000000000 : ℝ) ≤ (radius 8 (495/4096 : ℝ)) ∧ (radius 8 (495/4096 : ℝ)) ≤ (246251831279/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (495/4096 : ℝ)) (197001465023/200000000000 : ℝ) (246251831279/250000000000 : ℝ) (86256259871/500000000000 : ℝ) (43128129937/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (495/4096 : ℝ)) (197001465023/200000000000 : ℝ) (246251831279/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (495/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (197001465023/200000000000 : ℝ) (246251831279/250000000000 : ℝ) (992503662557/1000000000000 : ℝ) (496251831279/500000000000 : ℝ) (248118838099/250000000000 : ℝ) (496237676199/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (495/4096 : ℝ)) 1 (992503662557/1000000000000 : ℝ) (496251831279/500000000000 : ℝ) (248118838099/250000000000 : ℝ) (496237676199/500000000000 : ℝ) (248122376869/250000000000 : ℝ) (496244753739/500000000000 : ℝ) (7939916059/8000000000 : ℝ) (496244753689/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (495/4096 : ℝ)) 2 (248122376869/250000000000 : ℝ) (496244753739/500000000000 : ℝ) (7939916059/8000000000 : ℝ) (496244753689/500000000000 : ℝ) (39699580297/40000000000 : ℝ) (248122376857/250000000000 : ℝ) (39699580297/40000000000 : ℝ) (248122376857/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (495/4096 : ℝ)) 3 (39699580297/40000000000 : ℝ) (248122376857/250000000000 : ℝ) (39699580297/40000000000 : ℝ) (248122376857/250000000000 : ℝ) (39699580297/40000000000 : ℝ) (248122376857/250000000000 : ℝ) (39699580297/40000000000 : ℝ) (248122376857/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (495/4096 : ℝ)) 4 (39699580297/40000000000 : ℝ) (248122376857/250000000000 : ℝ) (39699580297/40000000000 : ℝ) (248122376857/250000000000 : ℝ) (39699580297/40000000000 : ℝ) (248122376857/250000000000 : ℝ) (39699580297/40000000000 : ℝ) (248122376857/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (495/4096 : ℝ)) 5 (39699580297/40000000000 : ℝ) (248122376857/250000000000 : ℝ) (39699580297/40000000000 : ℝ) (248122376857/250000000000 : ℝ) (39699580297/40000000000 : ℝ) (248122376857/250000000000 : ℝ) (39699580297/40000000000 : ℝ) (248122376857/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (495/4096 : ℝ)) 6 (39699580297/40000000000 : ℝ) (248122376857/250000000000 : ℝ) (39699580297/40000000000 : ℝ) (248122376857/250000000000 : ℝ) (39699580297/40000000000 : ℝ) (248122376857/250000000000 : ℝ) (39699580297/40000000000 : ℝ) (248122376857/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (495/4096 : ℝ)) 7 (39699580297/40000000000 : ℝ) (248122376857/250000000000 : ℝ) (39699580297/40000000000 : ℝ) (248122376857/250000000000 : ℝ) (39699580297/40000000000 : ℝ) (248122376857/250000000000 : ℝ) (39699580297/40000000000 : ℝ) (248122376857/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (495/4096 : ℝ))) (86256259871/500000000000 : ℝ) (43128129937/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (495/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (86256259871/500000000000 : ℝ) (43128129937/250000000000 : ℝ) (586256259871/1000000000000 : ℝ) (293128129937/500000000000 : ℝ) (41534626487/100000000000 : ℝ) (207673132439/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (495/4096 : ℝ))) 1 (586256259871/1000000000000 : ℝ) (293128129937/500000000000 : ℝ) (41534626487/100000000000 : ℝ) (207673132439/500000000000 : ℝ) (50080126237/100000000000 : ℝ) (62600157797/125000000000 : ℝ) (123364132701/250000000000 : ℝ) (493456530811/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (495/4096 : ℝ))) 2 (50080126237/100000000000 : ℝ) (62600157797/125000000000 : ℝ) (123364132701/250000000000 : ℝ) (493456530811/1000000000000 : ℝ) (497128896587/1000000000000 : ℝ) (248564448297/500000000000 : ℝ) (497115332243/1000000000000 : ℝ) (1988461329/4000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (495/4096 : ℝ))) 3 (497128896587/1000000000000 : ℝ) (248564448297/500000000000 : ℝ) (497115332243/1000000000000 : ℝ) (1988461329/4000000000 : ℝ) (99424422883/200000000000 : ℝ) (248561057211/500000000000 : ℝ) (7767533037/15625000000 : ℝ) (62140264297/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (495/4096 : ℝ))) 4 (99424422883/200000000000 : ℝ) (248561057211/500000000000 : ℝ) (7767533037/15625000000 : ℝ) (62140264297/125000000000 : ℝ) (497122114391/1000000000000 : ℝ) (497122114399/1000000000000 : ℝ) (497122114391/1000000000000 : ℝ) (497122114399/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (495/4096 : ℝ))) 5 (497122114391/1000000000000 : ℝ) (497122114399/1000000000000 : ℝ) (497122114391/1000000000000 : ℝ) (497122114399/1000000000000 : ℝ) (497122114391/1000000000000 : ℝ) (497122114399/1000000000000 : ℝ) (497122114391/1000000000000 : ℝ) (497122114399/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (495/4096 : ℝ))) 6 (497122114391/1000000000000 : ℝ) (497122114399/1000000000000 : ℝ) (497122114391/1000000000000 : ℝ) (497122114399/1000000000000 : ℝ) (497122114391/1000000000000 : ℝ) (497122114399/1000000000000 : ℝ) (497122114391/1000000000000 : ℝ) (497122114399/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (495/4096 : ℝ))) 7 (497122114391/1000000000000 : ℝ) (497122114399/1000000000000 : ℝ) (497122114391/1000000000000 : ℝ) (497122114399/1000000000000 : ℝ) (497122114391/1000000000000 : ℝ) (497122114399/1000000000000 : ℝ) (497122114391/1000000000000 : ℝ) (497122114399/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (495/4096 : ℝ)) hmem 8 (39699580297/40000000000 : ℝ) (248122376857/250000000000 : ℝ) (39699580297/40000000000 : ℝ) (248122376857/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (495/4096 : ℝ))) hcmem 8 (497122114391/1000000000000 : ℝ) (497122114399/1000000000000 : ℝ) (497122114391/1000000000000 : ℝ) (497122114399/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (495/4096 : ℝ)) (39699580297/40000000000 : ℝ) (248122376857/250000000000 : ℝ) (497122114391/1000000000000 : ℝ) (497122114399/1000000000000 : ℝ) (31471469891/40000000000 : ℝ) (786786747291/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0070_exp_lower
  have heNumeric : (2054916373359/1000000000000 : ℝ)/4 ≤ Real.exp (-1332118416457/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054916373359/1000000000000 : ℝ)/4 ≤ Real.exp ((989/8192 : ℝ)-(786786747291/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (989/8192 : ℝ) (495/4096 : ℝ) (786786747291/1000000000000 : ℝ) (2054916373359/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0071; no trusted numerical premise.
theorem cover8_leaf0071_exp_radius : (499055801387404713/500000000000000000 : ℝ) ≤ Real.exp ((-991/65536 : ℝ)/8) ∧ Real.exp ((-991/65536 : ℝ)/8) ≤ (998111602774809427/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-991/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0071_exp_lower : (920113749952760733/1000000000000000000 : ℝ) ≤ Real.exp ((-83257975329/125000000000 : ℝ)/8) ∧ Real.exp ((-83257975329/125000000000 : ℝ)/8) ≤ (460056874976380367/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-83257975329/125000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0071_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027453466133/500000000000 : ℝ) ≤ 4*Real.exp (495/4096 : ℝ)*Real.exp (-mu (radius 8 (991/8192 : ℝ))) ∧ (20549/10000 : ℝ) < (1027453466133/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (991/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0071_exp_radius
  have hrNumeric : (984992295211/1000000000000 : ℝ) ≤ Real.exp (-991/65536 : ℝ) ∧ Real.exp (-991/65536 : ℝ) ≤ (246248073803/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984992295211/1000000000000 : ℝ) ≤ (radius 8 (991/8192 : ℝ)) ∧ (radius 8 (991/8192 : ℝ)) ≤ (246248073803/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (991/8192 : ℝ)) (984992295211/1000000000000 : ℝ) (246248073803/250000000000 : ℝ) (172598315093/1000000000000 : ℝ) (172598315099/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (991/8192 : ℝ)) (984992295211/1000000000000 : ℝ) (246248073803/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (991/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984992295211/1000000000000 : ℝ) (246248073803/250000000000 : ℝ) (198499229521/200000000000 : ℝ) (496248073803/500000000000 : ℝ) (992467780439/1000000000000 : ℝ) (992467780441/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (991/8192 : ℝ)) 1 (198499229521/200000000000 : ℝ) (496248073803/500000000000 : ℝ) (992467780439/1000000000000 : ℝ) (992467780441/1000000000000 : ℝ) (496240982011/500000000000 : ℝ) (124060245503/125000000000 : ℝ) (12406024549/12500000000 : ℝ) (992481963923/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (991/8192 : ℝ)) 2 (496240982011/500000000000 : ℝ) (124060245503/125000000000 : ℝ) (12406024549/12500000000 : ℝ) (992481963923/1000000000000 : ℝ) (992481963971/1000000000000 : ℝ) (496240981987/500000000000 : ℝ) (99248196397/100000000000 : ℝ) (496240981987/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (991/8192 : ℝ)) 3 (992481963971/1000000000000 : ℝ) (496240981987/500000000000 : ℝ) (99248196397/100000000000 : ℝ) (496240981987/500000000000 : ℝ) (99248196397/100000000000 : ℝ) (496240981987/500000000000 : ℝ) (99248196397/100000000000 : ℝ) (496240981987/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (991/8192 : ℝ)) 4 (99248196397/100000000000 : ℝ) (496240981987/500000000000 : ℝ) (99248196397/100000000000 : ℝ) (496240981987/500000000000 : ℝ) (99248196397/100000000000 : ℝ) (496240981987/500000000000 : ℝ) (99248196397/100000000000 : ℝ) (496240981987/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (991/8192 : ℝ)) 5 (99248196397/100000000000 : ℝ) (496240981987/500000000000 : ℝ) (99248196397/100000000000 : ℝ) (496240981987/500000000000 : ℝ) (99248196397/100000000000 : ℝ) (496240981987/500000000000 : ℝ) (99248196397/100000000000 : ℝ) (496240981987/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (991/8192 : ℝ)) 6 (99248196397/100000000000 : ℝ) (496240981987/500000000000 : ℝ) (99248196397/100000000000 : ℝ) (496240981987/500000000000 : ℝ) (99248196397/100000000000 : ℝ) (496240981987/500000000000 : ℝ) (99248196397/100000000000 : ℝ) (496240981987/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (991/8192 : ℝ)) 7 (99248196397/100000000000 : ℝ) (496240981987/500000000000 : ℝ) (99248196397/100000000000 : ℝ) (496240981987/500000000000 : ℝ) (99248196397/100000000000 : ℝ) (496240981987/500000000000 : ℝ) (99248196397/100000000000 : ℝ) (496240981987/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (991/8192 : ℝ))) (172598315093/1000000000000 : ℝ) (172598315099/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (991/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (172598315093/1000000000000 : ℝ) (172598315099/1000000000000 : ℝ) (293149578773/500000000000 : ℝ) (11725983151/20000000000 : ℝ) (415449533749/1000000000000 : ℝ) (207724766879/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (991/8192 : ℝ))) 1 (293149578773/500000000000 : ℝ) (11725983151/20000000000 : ℝ) (415449533749/1000000000000 : ℝ) (207724766879/500000000000 : ℝ) (500874345647/1000000000000 : ℝ) (250437172827/500000000000 : ℝ) (98707185481/200000000000 : ℝ) (493535927413/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (991/8192 : ℝ))) 2 (500874345647/1000000000000 : ℝ) (250437172827/500000000000 : ℝ) (98707185481/200000000000 : ℝ) (493535927413/1000000000000 : ℝ) (248602568263/500000000000 : ℝ) (248602568267/500000000000 : ℝ) (971077339/1953125000 : ℝ) (62148949697/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (991/8192 : ℝ))) 3 (248602568263/500000000000 : ℝ) (248602568267/500000000000 : ℝ) (971077339/1953125000 : ℝ) (62148949697/125000000000 : ℝ) (497198367047/1000000000000 : ℝ) (99439673411/200000000000 : ℝ) (497198367/1000000000 : ℝ) (497198367009/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (991/8192 : ℝ))) 4 (497198367047/1000000000000 : ℝ) (99439673411/200000000000 : ℝ) (497198367/1000000000 : ℝ) (497198367009/1000000000000 : ℝ) (497198367023/1000000000000 : ℝ) (62149795879/125000000000 : ℝ) (497198367023/1000000000000 : ℝ) (62149795879/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (991/8192 : ℝ))) 5 (497198367023/1000000000000 : ℝ) (62149795879/125000000000 : ℝ) (497198367023/1000000000000 : ℝ) (62149795879/125000000000 : ℝ) (497198367023/1000000000000 : ℝ) (62149795879/125000000000 : ℝ) (497198367023/1000000000000 : ℝ) (62149795879/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (991/8192 : ℝ))) 6 (497198367023/1000000000000 : ℝ) (62149795879/125000000000 : ℝ) (497198367023/1000000000000 : ℝ) (62149795879/125000000000 : ℝ) (497198367023/1000000000000 : ℝ) (62149795879/125000000000 : ℝ) (497198367023/1000000000000 : ℝ) (62149795879/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (991/8192 : ℝ))) 7 (497198367023/1000000000000 : ℝ) (62149795879/125000000000 : ℝ) (497198367023/1000000000000 : ℝ) (62149795879/125000000000 : ℝ) (497198367023/1000000000000 : ℝ) (62149795879/125000000000 : ℝ) (497198367023/1000000000000 : ℝ) (62149795879/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (991/8192 : ℝ)) hmem 8 (99248196397/100000000000 : ℝ) (496240981987/500000000000 : ℝ) (99248196397/100000000000 : ℝ) (496240981987/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (991/8192 : ℝ))) hcmem 8 (497198367023/1000000000000 : ℝ) (62149795879/125000000000 : ℝ) (497198367023/1000000000000 : ℝ) (62149795879/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (991/8192 : ℝ)) (99248196397/100000000000 : ℝ) (496240981987/500000000000 : ℝ) (497198367023/1000000000000 : ℝ) (62149795879/125000000000 : ℝ) (196728352997/250000000000 : ℝ) (786913412007/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0071_exp_lower
  have heNumeric : (1027453466133/500000000000 : ℝ)/4 ≤ Real.exp (-83257975329/125000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027453466133/500000000000 : ℝ)/4 ≤ Real.exp ((495/4096 : ℝ)-(786913412007/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (495/4096 : ℝ) (991/8192 : ℝ) (786913412007/1000000000000 : ℝ) (1027453466133/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0072; no trusted numerical premise.
theorem cover8_leaf0072_exp_radius : (998110650901862841/1000000000000000000 : ℝ) ≤ Real.exp ((-1983/131072 : ℝ)/8) ∧ Real.exp ((-1983/131072 : ℝ)/8) ≤ (499055325450931421/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1983/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0072_exp_lower : (920120509431945953/1000000000000000000 : ℝ) ≤ Real.exp ((-1332010064069/2000000000000 : ℝ)/8) ∧ Real.exp ((-1332010064069/2000000000000 : ℝ)/8) ≤ (460060254715972977/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1332010064069/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0072_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2055027703923/1000000000000 : ℝ) ≤ 4*Real.exp (991/8192 : ℝ)*Real.exp (-mu (radius 8 (1983/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (2055027703923/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (1983/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0072_exp_radius
  have hrNumeric : (196996956069/200000000000 : ℝ) ≤ Real.exp (-1983/131072 : ℝ) ∧ Real.exp (-1983/131072 : ℝ) ≤ (492492390173/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196996956069/200000000000 : ℝ) ≤ (radius 8 (1983/16384 : ℝ)) ∧ (radius 8 (1983/16384 : ℝ)) ≤ (492492390173/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (1983/16384 : ℝ)) (196996956069/200000000000 : ℝ) (492492390173/500000000000 : ℝ) (86320597899/500000000000 : ℝ) (34528239161/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (1983/16384 : ℝ)) (196996956069/200000000000 : ℝ) (492492390173/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (1983/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196996956069/200000000000 : ℝ) (492492390173/500000000000 : ℝ) (248123097543/250000000000 : ℝ) (992492390173/1000000000000 : ℝ) (496231997241/500000000000 : ℝ) (248115998621/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (1983/16384 : ℝ)) 1 (248123097543/250000000000 : ℝ) (992492390173/1000000000000 : ℝ) (496231997241/500000000000 : ℝ) (248115998621/250000000000 : ℝ) (992478192327/1000000000000 : ℝ) (992478192329/1000000000000 : ℝ) (39699127689/40000000000 : ℝ) (992478192227/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (1983/16384 : ℝ)) 2 (992478192327/1000000000000 : ℝ) (992478192329/1000000000000 : ℝ) (39699127689/40000000000 : ℝ) (992478192227/1000000000000 : ℝ) (248119548069/250000000000 : ℝ) (496239096139/500000000000 : ℝ) (39699127691/40000000000 : ℝ) (496239096139/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (1983/16384 : ℝ)) 3 (248119548069/250000000000 : ℝ) (496239096139/500000000000 : ℝ) (39699127691/40000000000 : ℝ) (496239096139/500000000000 : ℝ) (39699127691/40000000000 : ℝ) (496239096139/500000000000 : ℝ) (39699127691/40000000000 : ℝ) (496239096139/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (1983/16384 : ℝ)) 4 (39699127691/40000000000 : ℝ) (496239096139/500000000000 : ℝ) (39699127691/40000000000 : ℝ) (496239096139/500000000000 : ℝ) (39699127691/40000000000 : ℝ) (496239096139/500000000000 : ℝ) (39699127691/40000000000 : ℝ) (496239096139/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (1983/16384 : ℝ)) 5 (39699127691/40000000000 : ℝ) (496239096139/500000000000 : ℝ) (39699127691/40000000000 : ℝ) (496239096139/500000000000 : ℝ) (39699127691/40000000000 : ℝ) (496239096139/500000000000 : ℝ) (39699127691/40000000000 : ℝ) (496239096139/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (1983/16384 : ℝ)) 6 (39699127691/40000000000 : ℝ) (496239096139/500000000000 : ℝ) (39699127691/40000000000 : ℝ) (496239096139/500000000000 : ℝ) (39699127691/40000000000 : ℝ) (496239096139/500000000000 : ℝ) (39699127691/40000000000 : ℝ) (496239096139/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (1983/16384 : ℝ)) 7 (39699127691/40000000000 : ℝ) (496239096139/500000000000 : ℝ) (39699127691/40000000000 : ℝ) (496239096139/500000000000 : ℝ) (39699127691/40000000000 : ℝ) (496239096139/500000000000 : ℝ) (39699127691/40000000000 : ℝ) (496239096139/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (1983/16384 : ℝ))) (86320597899/500000000000 : ℝ) (34528239161/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (1983/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (86320597899/500000000000 : ℝ) (34528239161/200000000000 : ℝ) (586320597899/1000000000000 : ℝ) (586320597903/1000000000000 : ℝ) (207750569071/500000000000 : ℝ) (51937642269/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (1983/16384 : ℝ))) 1 (586320597899/1000000000000 : ℝ) (586320597903/1000000000000 : ℝ) (207750569071/500000000000 : ℝ) (51937642269/125000000000 : ℝ) (25045543401/50000000000 : ℝ) (125227717007/250000000000 : ℝ) (30848475179/62500000000 : ℝ) (493575602873/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (1983/16384 : ℝ))) 2 (25045543401/50000000000 : ℝ) (125227717007/250000000000 : ℝ) (30848475179/62500000000 : ℝ) (493575602873/1000000000000 : ℝ) (248621617721/500000000000 : ℝ) (497243235451/1000000000000 : ℝ) (15538428411/31250000000 : ℝ) (248614854581/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (1983/16384 : ℝ))) 3 (248621617721/500000000000 : ℝ) (497243235451/1000000000000 : ℝ) (15538428411/31250000000 : ℝ) (248614854581/500000000000 : ℝ) (497236472297/1000000000000 : ℝ) (497236472307/1000000000000 : ℝ) (497236472251/1000000000000 : ℝ) (497236472261/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (1983/16384 : ℝ))) 4 (497236472297/1000000000000 : ℝ) (497236472307/1000000000000 : ℝ) (497236472251/1000000000000 : ℝ) (497236472261/1000000000000 : ℝ) (248618236137/500000000000 : ℝ) (124309118071/250000000000 : ℝ) (497236472273/1000000000000 : ℝ) (124309118071/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (1983/16384 : ℝ))) 5 (248618236137/500000000000 : ℝ) (124309118071/250000000000 : ℝ) (497236472273/1000000000000 : ℝ) (124309118071/250000000000 : ℝ) (497236472273/1000000000000 : ℝ) (124309118071/250000000000 : ℝ) (497236472273/1000000000000 : ℝ) (124309118071/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (1983/16384 : ℝ))) 6 (497236472273/1000000000000 : ℝ) (124309118071/250000000000 : ℝ) (497236472273/1000000000000 : ℝ) (124309118071/250000000000 : ℝ) (497236472273/1000000000000 : ℝ) (124309118071/250000000000 : ℝ) (497236472273/1000000000000 : ℝ) (124309118071/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (1983/16384 : ℝ))) 7 (497236472273/1000000000000 : ℝ) (124309118071/250000000000 : ℝ) (497236472273/1000000000000 : ℝ) (124309118071/250000000000 : ℝ) (497236472273/1000000000000 : ℝ) (124309118071/250000000000 : ℝ) (497236472273/1000000000000 : ℝ) (124309118071/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (1983/16384 : ℝ)) hmem 8 (39699127691/40000000000 : ℝ) (496239096139/500000000000 : ℝ) (39699127691/40000000000 : ℝ) (496239096139/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (1983/16384 : ℝ))) hcmem 8 (497236472273/1000000000000 : ℝ) (124309118071/250000000000 : ℝ) (497236472273/1000000000000 : ℝ) (124309118071/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (1983/16384 : ℝ)) (39699127691/40000000000 : ℝ) (496239096139/500000000000 : ℝ) (497236472273/1000000000000 : ℝ) (124309118071/250000000000 : ℝ) (786976711701/1000000000000 : ℝ) (393488355861/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0072_exp_lower
  have heNumeric : (2055027703923/1000000000000 : ℝ)/4 ≤ Real.exp (-1332010064069/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2055027703923/1000000000000 : ℝ)/4 ≤ Real.exp ((991/8192 : ℝ)-(393488355861/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (991/8192 : ℝ) (1983/16384 : ℝ) (393488355861/500000000000 : ℝ) (2055027703923/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0073; no trusted numerical premise.
theorem cover8_leaf0073_exp_radius : (31190928094682001/31250000000000000 : ℝ) ≤ Real.exp ((-31/2048 : ℝ)/8) ∧ Real.exp ((-31/2048 : ℝ)/8) ≤ (998109699029824033/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-31/2048 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0073_exp_lower : (920120251473810731/1000000000000000000 : ℝ) ≤ Real.exp ((-2664029099421/4000000000000 : ℝ)/8) ∧ Real.exp ((-2664029099421/4000000000000 : ℝ)/8) ≤ (230030062868452683/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2664029099421/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0073_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (205502309487/100000000000 : ℝ) ≤ 4*Real.exp (1983/16384 : ℝ)*Real.exp (-mu (radius 8 (31/256 : ℝ))) ∧ (20549/10000 : ℝ) < (205502309487/100000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (31/256 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0073_exp_radius
  have hrNumeric : (7695134887/7812500000 : ℝ) ≤ Real.exp (-31/2048 : ℝ) ∧ Real.exp (-31/2048 : ℝ) ≤ (984977265537/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (7695134887/7812500000 : ℝ) ≤ (radius 8 (31/256 : ℝ)) ∧ (radius 8 (31/256 : ℝ)) ≤ (984977265537/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (31/256 : ℝ)) (7695134887/7812500000 : ℝ) (984977265537/1000000000000 : ℝ) (172684065203/1000000000000 : ℝ) (17268406521/100000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (31/256 : ℝ)) (7695134887/7812500000 : ℝ) (984977265537/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (31/256 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (7695134887/7812500000 : ℝ) (984977265537/1000000000000 : ℝ) (15507634887/15625000000 : ℝ) (992488632769/1000000000000 : ℝ) (49623010427/50000000000 : ℝ) (992460208541/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (31/256 : ℝ)) 1 (15507634887/15625000000 : ℝ) (992488632769/1000000000000 : ℝ) (49623010427/50000000000 : ℝ) (992460208541/1000000000000 : ℝ) (496237210327/500000000000 : ℝ) (198494884131/200000000000 : ℝ) (124059302569/125000000000 : ℝ) (496237210277/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (31/256 : ℝ)) 2 (496237210327/500000000000 : ℝ) (198494884131/200000000000 : ℝ) (124059302569/125000000000 : ℝ) (496237210277/500000000000 : ℝ) (992474420603/1000000000000 : ℝ) (198494884121/200000000000 : ℝ) (496237210301/500000000000 : ℝ) (198494884121/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (31/256 : ℝ)) 3 (992474420603/1000000000000 : ℝ) (198494884121/200000000000 : ℝ) (496237210301/500000000000 : ℝ) (198494884121/200000000000 : ℝ) (496237210301/500000000000 : ℝ) (198494884121/200000000000 : ℝ) (496237210301/500000000000 : ℝ) (198494884121/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (31/256 : ℝ)) 4 (496237210301/500000000000 : ℝ) (198494884121/200000000000 : ℝ) (496237210301/500000000000 : ℝ) (198494884121/200000000000 : ℝ) (496237210301/500000000000 : ℝ) (198494884121/200000000000 : ℝ) (496237210301/500000000000 : ℝ) (198494884121/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (31/256 : ℝ)) 5 (496237210301/500000000000 : ℝ) (198494884121/200000000000 : ℝ) (496237210301/500000000000 : ℝ) (198494884121/200000000000 : ℝ) (496237210301/500000000000 : ℝ) (198494884121/200000000000 : ℝ) (496237210301/500000000000 : ℝ) (198494884121/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (31/256 : ℝ)) 6 (496237210301/500000000000 : ℝ) (198494884121/200000000000 : ℝ) (496237210301/500000000000 : ℝ) (198494884121/200000000000 : ℝ) (496237210301/500000000000 : ℝ) (198494884121/200000000000 : ℝ) (496237210301/500000000000 : ℝ) (198494884121/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (31/256 : ℝ)) 7 (496237210301/500000000000 : ℝ) (198494884121/200000000000 : ℝ) (496237210301/500000000000 : ℝ) (198494884121/200000000000 : ℝ) (496237210301/500000000000 : ℝ) (198494884121/200000000000 : ℝ) (496237210301/500000000000 : ℝ) (198494884121/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (31/256 : ℝ))) (172684065203/1000000000000 : ℝ) (17268406521/100000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (31/256 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (172684065203/1000000000000 : ℝ) (17268406521/100000000000 : ℝ) (586342032601/1000000000000 : ℝ) (117268406521/200000000000 : ℝ) (415552722531/1000000000000 : ℝ) (20777636127/50000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (31/256 : ℝ))) 1 (586342032601/1000000000000 : ℝ) (117268406521/200000000000 : ℝ) (415552722531/1000000000000 : ℝ) (20777636127/50000000000 : ℝ) (250473688783/500000000000 : ℝ) (500947377573/1000000000000 : ℝ) (123403815779/250000000000 : ℝ) (123403815781/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (31/256 : ℝ))) 2 (250473688783/500000000000 : ℝ) (500947377573/1000000000000 : ℝ) (123403815779/250000000000 : ℝ) (123403815781/250000000000 : ℝ) (497281320341/1000000000000 : ℝ) (497281320349/1000000000000 : ℝ) (31079237919/62500000000 : ℝ) (62158475839/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (31/256 : ℝ))) 3 (497281320341/1000000000000 : ℝ) (497281320349/1000000000000 : ℝ) (31079237919/62500000000 : ℝ) (62158475839/125000000000 : ℝ) (248637281761/500000000000 : ℝ) (497274563531/1000000000000 : ℝ) (124318640869/250000000000 : ℝ) (99454912697/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (31/256 : ℝ))) 4 (248637281761/500000000000 : ℝ) (497274563531/1000000000000 : ℝ) (124318640869/250000000000 : ℝ) (99454912697/200000000000 : ℝ) (497274563499/1000000000000 : ℝ) (124318640877/250000000000 : ℝ) (248637281749/500000000000 : ℝ) (124318640877/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (31/256 : ℝ))) 5 (497274563499/1000000000000 : ℝ) (124318640877/250000000000 : ℝ) (248637281749/500000000000 : ℝ) (124318640877/250000000000 : ℝ) (248637281749/500000000000 : ℝ) (124318640877/250000000000 : ℝ) (248637281749/500000000000 : ℝ) (124318640877/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (31/256 : ℝ))) 6 (248637281749/500000000000 : ℝ) (124318640877/250000000000 : ℝ) (248637281749/500000000000 : ℝ) (124318640877/250000000000 : ℝ) (248637281749/500000000000 : ℝ) (124318640877/250000000000 : ℝ) (248637281749/500000000000 : ℝ) (124318640877/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (31/256 : ℝ))) 7 (248637281749/500000000000 : ℝ) (124318640877/250000000000 : ℝ) (248637281749/500000000000 : ℝ) (124318640877/250000000000 : ℝ) (248637281749/500000000000 : ℝ) (124318640877/250000000000 : ℝ) (248637281749/500000000000 : ℝ) (124318640877/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (31/256 : ℝ)) hmem 8 (496237210301/500000000000 : ℝ) (198494884121/200000000000 : ℝ) (496237210301/500000000000 : ℝ) (198494884121/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (31/256 : ℝ))) hcmem 8 (248637281749/500000000000 : ℝ) (124318640877/250000000000 : ℝ) (248637281749/500000000000 : ℝ) (124318640877/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (31/256 : ℝ)) (496237210301/500000000000 : ℝ) (198494884121/200000000000 : ℝ) (248637281749/500000000000 : ℝ) (124318640877/250000000000 : ℝ) (9837999871/12500000000 : ℝ) (787039989699/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0073_exp_lower
  have heNumeric : (205502309487/100000000000 : ℝ)/4 ≤ Real.exp (-2664029099421/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (205502309487/100000000000 : ℝ)/4 ≤ Real.exp ((1983/16384 : ℝ)-(787039989699/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (1983/16384 : ℝ) (31/256 : ℝ) (787039989699/1000000000000 : ℝ) (205502309487/100000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0074; no trusted numerical premise.
theorem cover8_leaf0074_exp_radius : (998108747158692999/1000000000000000000 : ℝ) ≤ Real.exp ((-1985/131072 : ℝ)/8) ∧ Real.exp ((-1985/131072 : ℝ)/8) ≤ (998108747158693/1000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1985/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0074_exp_lower : (460059998006936807/500000000000000000 : ℝ) ≤ Real.exp ((-166502373989/250000000000 : ℝ)/8) ∧ Real.exp ((-166502373989/250000000000 : ℝ)/8) ≤ (184023999202774723/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-166502373989/250000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0074_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2055018530461/1000000000000 : ℝ) ≤ 4*Real.exp (31/256 : ℝ)*Real.exp (-mu (radius 8 (1985/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (2055018530461/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (1985/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0074_exp_radius
  have hrNumeric : (196993950157/200000000000 : ℝ) ≤ Real.exp (-1985/131072 : ℝ) ∧ Real.exp (-1985/131072 : ℝ) ≤ (492484875393/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196993950157/200000000000 : ℝ) ≤ (radius 8 (1985/16384 : ℝ)) ∧ (radius 8 (1985/16384 : ℝ)) ≤ (492484875393/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (1985/16384 : ℝ)) (196993950157/200000000000 : ℝ) (492484875393/500000000000 : ℝ) (172726923311/1000000000000 : ℝ) (172726923317/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (1985/16384 : ℝ)) (196993950157/200000000000 : ℝ) (492484875393/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (1985/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196993950157/200000000000 : ℝ) (492484875393/500000000000 : ℝ) (7753788089/7812500000 : ℝ) (992484875393/1000000000000 : ℝ) (248114105653/250000000000 : ℝ) (496228211307/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (1985/16384 : ℝ)) 1 (7753788089/7812500000 : ℝ) (992484875393/1000000000000 : ℝ) (248114105653/250000000000 : ℝ) (496228211307/500000000000 : ℝ) (496235324501/500000000000 : ℝ) (248117662251/250000000000 : ℝ) (9924706489/10000000000 : ℝ) (496235324451/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (1985/16384 : ℝ)) 2 (496235324501/500000000000 : ℝ) (248117662251/250000000000 : ℝ) (9924706489/10000000000 : ℝ) (496235324451/500000000000 : ℝ) (992470648951/1000000000000 : ℝ) (992470648953/1000000000000 : ℝ) (19849412979/20000000000 : ℝ) (992470648953/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (1985/16384 : ℝ)) 3 (992470648951/1000000000000 : ℝ) (992470648953/1000000000000 : ℝ) (19849412979/20000000000 : ℝ) (992470648953/1000000000000 : ℝ) (19849412979/20000000000 : ℝ) (992470648953/1000000000000 : ℝ) (19849412979/20000000000 : ℝ) (992470648953/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (1985/16384 : ℝ)) 4 (19849412979/20000000000 : ℝ) (992470648953/1000000000000 : ℝ) (19849412979/20000000000 : ℝ) (992470648953/1000000000000 : ℝ) (19849412979/20000000000 : ℝ) (992470648953/1000000000000 : ℝ) (19849412979/20000000000 : ℝ) (992470648953/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (1985/16384 : ℝ)) 5 (19849412979/20000000000 : ℝ) (992470648953/1000000000000 : ℝ) (19849412979/20000000000 : ℝ) (992470648953/1000000000000 : ℝ) (19849412979/20000000000 : ℝ) (992470648953/1000000000000 : ℝ) (19849412979/20000000000 : ℝ) (992470648953/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (1985/16384 : ℝ)) 6 (19849412979/20000000000 : ℝ) (992470648953/1000000000000 : ℝ) (19849412979/20000000000 : ℝ) (992470648953/1000000000000 : ℝ) (19849412979/20000000000 : ℝ) (992470648953/1000000000000 : ℝ) (19849412979/20000000000 : ℝ) (992470648953/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (1985/16384 : ℝ)) 7 (19849412979/20000000000 : ℝ) (992470648953/1000000000000 : ℝ) (19849412979/20000000000 : ℝ) (992470648953/1000000000000 : ℝ) (19849412979/20000000000 : ℝ) (992470648953/1000000000000 : ℝ) (19849412979/20000000000 : ℝ) (992470648953/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (1985/16384 : ℝ))) (172726923311/1000000000000 : ℝ) (172726923317/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (1985/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (172726923311/1000000000000 : ℝ) (172726923317/1000000000000 : ℝ) (117272692331/200000000000 : ℝ) (586363461659/1000000000000 : ℝ) (16624171477/40000000000 : ℝ) (415604286933/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (1985/16384 : ℝ))) 1 (117272692331/200000000000 : ℝ) (586363461659/1000000000000 : ℝ) (16624171477/40000000000 : ℝ) (415604286933/1000000000000 : ℝ) (50098387429/100000000000 : ℝ) (62622984287/125000000000 : ℝ) (493654908169/1000000000000 : ℝ) (493654908177/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (1985/16384 : ℝ))) 2 (50098387429/100000000000 : ℝ) (62622984287/125000000000 : ℝ) (493654908169/1000000000000 : ℝ) (493654908177/1000000000000 : ℝ) (497319391229/1000000000000 : ℝ) (497319391237/1000000000000 : ℝ) (497305890229/1000000000000 : ℝ) (497305890237/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (1985/16384 : ℝ))) 3 (497319391229/1000000000000 : ℝ) (497319391237/1000000000000 : ℝ) (497305890229/1000000000000 : ℝ) (497305890237/1000000000000 : ℝ) (497312640729/1000000000000 : ℝ) (497312640737/1000000000000 : ℝ) (497312640683/1000000000000 : ℝ) (124328160173/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (1985/16384 : ℝ))) 4 (497312640729/1000000000000 : ℝ) (497312640737/1000000000000 : ℝ) (497312640683/1000000000000 : ℝ) (124328160173/250000000000 : ℝ) (248656320353/500000000000 : ℝ) (99462528143/200000000000 : ℝ) (99462528141/200000000000 : ℝ) (99462528143/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (1985/16384 : ℝ))) 5 (248656320353/500000000000 : ℝ) (99462528143/200000000000 : ℝ) (99462528141/200000000000 : ℝ) (99462528143/200000000000 : ℝ) (99462528141/200000000000 : ℝ) (99462528143/200000000000 : ℝ) (99462528141/200000000000 : ℝ) (99462528143/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (1985/16384 : ℝ))) 6 (99462528141/200000000000 : ℝ) (99462528143/200000000000 : ℝ) (99462528141/200000000000 : ℝ) (99462528143/200000000000 : ℝ) (99462528141/200000000000 : ℝ) (99462528143/200000000000 : ℝ) (99462528141/200000000000 : ℝ) (99462528143/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (1985/16384 : ℝ))) 7 (99462528141/200000000000 : ℝ) (99462528143/200000000000 : ℝ) (99462528141/200000000000 : ℝ) (99462528143/200000000000 : ℝ) (99462528141/200000000000 : ℝ) (99462528143/200000000000 : ℝ) (99462528141/200000000000 : ℝ) (99462528143/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (1985/16384 : ℝ)) hmem 8 (19849412979/20000000000 : ℝ) (992470648953/1000000000000 : ℝ) (19849412979/20000000000 : ℝ) (992470648953/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (1985/16384 : ℝ))) hcmem 8 (99462528141/200000000000 : ℝ) (99462528143/200000000000 : ℝ) (99462528141/200000000000 : ℝ) (99462528143/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (1985/16384 : ℝ)) (19849412979/20000000000 : ℝ) (992470648953/1000000000000 : ℝ) (99462528141/200000000000 : ℝ) (99462528143/200000000000 : ℝ) (49193952871/62500000000 : ℝ) (196775811489/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0074_exp_lower
  have heNumeric : (2055018530461/1000000000000 : ℝ)/4 ≤ Real.exp (-166502373989/250000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2055018530461/1000000000000 : ℝ)/4 ≤ Real.exp ((31/256 : ℝ)-(196775811489/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (31/256 : ℝ) (1985/16384 : ℝ) (196775811489/250000000000 : ℝ) (2055018530461/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_leaf0050_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0050_certificate
#check SmaleRate.Proofs.cover8_leaf0051_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0051_certificate
#check SmaleRate.Proofs.cover8_leaf0052_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0052_certificate
#check SmaleRate.Proofs.cover8_leaf0053_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0053_certificate
#check SmaleRate.Proofs.cover8_leaf0054_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0054_certificate
#check SmaleRate.Proofs.cover8_leaf0055_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0055_certificate
#check SmaleRate.Proofs.cover8_leaf0056_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0056_certificate
#check SmaleRate.Proofs.cover8_leaf0057_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0057_certificate
#check SmaleRate.Proofs.cover8_leaf0058_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0058_certificate
#check SmaleRate.Proofs.cover8_leaf0059_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0059_certificate
#check SmaleRate.Proofs.cover8_leaf0060_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0060_certificate
#check SmaleRate.Proofs.cover8_leaf0061_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0061_certificate
#check SmaleRate.Proofs.cover8_leaf0062_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0062_certificate
#check SmaleRate.Proofs.cover8_leaf0063_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0063_certificate
#check SmaleRate.Proofs.cover8_leaf0064_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0064_certificate
#check SmaleRate.Proofs.cover8_leaf0065_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0065_certificate
#check SmaleRate.Proofs.cover8_leaf0066_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0066_certificate
#check SmaleRate.Proofs.cover8_leaf0067_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0067_certificate
#check SmaleRate.Proofs.cover8_leaf0068_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0068_certificate
#check SmaleRate.Proofs.cover8_leaf0069_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0069_certificate
#check SmaleRate.Proofs.cover8_leaf0070_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0070_certificate
#check SmaleRate.Proofs.cover8_leaf0071_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0071_certificate
#check SmaleRate.Proofs.cover8_leaf0072_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0072_certificate
#check SmaleRate.Proofs.cover8_leaf0073_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0073_certificate
#check SmaleRate.Proofs.cover8_leaf0074_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0074_certificate
