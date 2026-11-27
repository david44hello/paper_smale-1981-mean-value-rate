/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.AGMCertificates

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

-- Proposed record cover8_leaf1325; no trusted numerical premise.
theorem cover8_leaf1325_exp_radius : (249497472346353947/250000000000000000 : ℝ) ≤ Real.exp ((-16879/1048576 : ℝ)/8) ∧ Real.exp ((-16879/1048576 : ℝ)/8) ≤ (997989889385415789/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16879/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1325_exp_lower : (920113604203269713/1000000000000000000 : ℝ) ≤ Real.exp ((-42628164471187/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628164471187/64000000000000 : ℝ)/8) ≤ (460056802101634857/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628164471187/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1325_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054904328227/1000000000000 : ℝ) ≤ 4*Real.exp (33757/262144 : ℝ)*Real.exp (-mu (radius 8 (16879/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054904328227/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16879/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1325_exp_radius
  have hrNumeric : (492015898323/500000000000 : ℝ) ≤ Real.exp (-16879/1048576 : ℝ) ∧ Real.exp (-16879/1048576 : ℝ) ≤ (984031796647/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492015898323/500000000000 : ℝ) ≤ (radius 8 (16879/131072 : ℝ)) ∧ (radius 8 (16879/131072 : ℝ)) ≤ (984031796647/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16879/131072 : ℝ)) (492015898323/500000000000 : ℝ) (984031796647/1000000000000 : ℝ) (35598552323/200000000000 : ℝ) (88996380811/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16879/131072 : ℝ)) (492015898323/500000000000 : ℝ) (984031796647/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16879/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492015898323/500000000000 : ℝ) (984031796647/1000000000000 : ℝ) (992015898323/1000000000000 : ℝ) (248003974581/250000000000 : ℝ) (991983768337/1000000000000 : ℝ) (991983768339/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16879/131072 : ℝ)) 1 (992015898323/1000000000000 : ℝ) (248003974581/250000000000 : ℝ) (991983768337/1000000000000 : ℝ) (991983768339/1000000000000 : ℝ) (99199983333/100000000000 : ℝ) (247999958333/250000000000 : ℝ) (991999833199/1000000000000 : ℝ) (495999916601/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16879/131072 : ℝ)) 2 (99199983333/100000000000 : ℝ) (247999958333/250000000000 : ℝ) (991999833199/1000000000000 : ℝ) (495999916601/500000000000 : ℝ) (61999989579/62500000000 : ℝ) (991999833267/1000000000000 : ℝ) (61999989579/62500000000 : ℝ) (991999833267/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16879/131072 : ℝ)) 3 (61999989579/62500000000 : ℝ) (991999833267/1000000000000 : ℝ) (61999989579/62500000000 : ℝ) (991999833267/1000000000000 : ℝ) (61999989579/62500000000 : ℝ) (991999833267/1000000000000 : ℝ) (61999989579/62500000000 : ℝ) (991999833267/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16879/131072 : ℝ)) 4 (61999989579/62500000000 : ℝ) (991999833267/1000000000000 : ℝ) (61999989579/62500000000 : ℝ) (991999833267/1000000000000 : ℝ) (61999989579/62500000000 : ℝ) (991999833267/1000000000000 : ℝ) (61999989579/62500000000 : ℝ) (991999833267/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16879/131072 : ℝ)) 5 (61999989579/62500000000 : ℝ) (991999833267/1000000000000 : ℝ) (61999989579/62500000000 : ℝ) (991999833267/1000000000000 : ℝ) (61999989579/62500000000 : ℝ) (991999833267/1000000000000 : ℝ) (61999989579/62500000000 : ℝ) (991999833267/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16879/131072 : ℝ)) 6 (61999989579/62500000000 : ℝ) (991999833267/1000000000000 : ℝ) (61999989579/62500000000 : ℝ) (991999833267/1000000000000 : ℝ) (61999989579/62500000000 : ℝ) (991999833267/1000000000000 : ℝ) (61999989579/62500000000 : ℝ) (991999833267/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16879/131072 : ℝ)) 7 (61999989579/62500000000 : ℝ) (991999833267/1000000000000 : ℝ) (61999989579/62500000000 : ℝ) (991999833267/1000000000000 : ℝ) (61999989579/62500000000 : ℝ) (991999833267/1000000000000 : ℝ) (61999989579/62500000000 : ℝ) (991999833267/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16879/131072 : ℝ))) (35598552323/200000000000 : ℝ) (88996380811/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16879/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35598552323/200000000000 : ℝ) (88996380811/500000000000 : ℝ) (588996380807/1000000000000 : ℝ) (588996380811/1000000000000 : ℝ) (210945941899/500000000000 : ℝ) (421891883807/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16879/131072 : ℝ))) 1 (588996380807/1000000000000 : ℝ) (588996380811/1000000000000 : ℝ) (210945941899/500000000000 : ℝ) (421891883807/1000000000000 : ℝ) (252722066151/500000000000 : ℝ) (505444132309/1000000000000 : ℝ) (498490514101/1000000000000 : ℝ) (498490514109/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16879/131072 : ℝ))) 2 (252722066151/500000000000 : ℝ) (505444132309/1000000000000 : ℝ) (498490514101/1000000000000 : ℝ) (498490514109/1000000000000 : ℝ) (501967323201/1000000000000 : ℝ) (501967323209/1000000000000 : ℝ) (501955282231/1000000000000 : ℝ) (1568610257/3125000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16879/131072 : ℝ))) 3 (501967323201/1000000000000 : ℝ) (501967323209/1000000000000 : ℝ) (501955282231/1000000000000 : ℝ) (1568610257/3125000000 : ℝ) (125490325679/250000000000 : ℝ) (20078452109/40000000000 : ℝ) (501961302679/1000000000000 : ℝ) (501961302689/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16879/131072 : ℝ))) 4 (125490325679/250000000000 : ℝ) (20078452109/40000000000 : ℝ) (501961302679/1000000000000 : ℝ) (501961302689/1000000000000 : ℝ) (501961302697/1000000000000 : ℝ) (501961302707/1000000000000 : ℝ) (501961302697/1000000000000 : ℝ) (501961302707/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16879/131072 : ℝ))) 5 (501961302697/1000000000000 : ℝ) (501961302707/1000000000000 : ℝ) (501961302697/1000000000000 : ℝ) (501961302707/1000000000000 : ℝ) (501961302697/1000000000000 : ℝ) (501961302707/1000000000000 : ℝ) (501961302697/1000000000000 : ℝ) (501961302707/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16879/131072 : ℝ))) 6 (501961302697/1000000000000 : ℝ) (501961302707/1000000000000 : ℝ) (501961302697/1000000000000 : ℝ) (501961302707/1000000000000 : ℝ) (501961302697/1000000000000 : ℝ) (501961302707/1000000000000 : ℝ) (501961302697/1000000000000 : ℝ) (501961302707/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16879/131072 : ℝ))) 7 (501961302697/1000000000000 : ℝ) (501961302707/1000000000000 : ℝ) (501961302697/1000000000000 : ℝ) (501961302707/1000000000000 : ℝ) (501961302697/1000000000000 : ℝ) (501961302707/1000000000000 : ℝ) (501961302697/1000000000000 : ℝ) (501961302707/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16879/131072 : ℝ)) hmem 8 (61999989579/62500000000 : ℝ) (991999833267/1000000000000 : ℝ) (61999989579/62500000000 : ℝ) (991999833267/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16879/131072 : ℝ))) hcmem 8 (501961302697/1000000000000 : ℝ) (501961302707/1000000000000 : ℝ) (501961302697/1000000000000 : ℝ) (501961302707/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16879/131072 : ℝ)) (61999989579/62500000000 : ℝ) (991999833267/1000000000000 : ℝ) (501961302697/1000000000000 : ℝ) (501961302707/1000000000000 : ℝ) (397418902719/500000000000 : ℝ) (397418902729/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1325_exp_lower
  have heNumeric : (2054904328227/1000000000000 : ℝ)/4 ≤ Real.exp (-42628164471187/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054904328227/1000000000000 : ℝ)/4 ≤ Real.exp ((33757/262144 : ℝ)-(397418902729/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33757/262144 : ℝ) (16879/131072 : ℝ) (397418902729/500000000000 : ℝ) (2054904328227/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1326; no trusted numerical premise.
theorem cover8_leaf1326_exp_radius : (199597965980116943/200000000000000000 : ℝ) ≤ Real.exp ((-33759/2097152 : ℝ)/8) ∧ Real.exp ((-33759/2097152 : ℝ)/8) ≤ (249497457475146179/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33759/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1326_exp_lower : (92011360678019343/100000000000000000 : ℝ) ≤ Real.exp ((-170512652149/256000000000 : ℝ)/8) ∧ Real.exp ((-170512652149/256000000000 : ℝ)/8) ≤ (920113606780193431/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-170512652149/256000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1326_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513726093567/250000000000 : ℝ) ≤ 4*Real.exp (16879/131072 : ℝ)*Real.exp (-mu (radius 8 (33759/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (513726093567/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33759/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1326_exp_radius
  have hrNumeric : (984031327423/1000000000000 : ℝ) ≤ Real.exp (-33759/2097152 : ℝ) ∧ Real.exp (-33759/2097152 : ℝ) ≤ (15375489491/15625000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984031327423/1000000000000 : ℝ) ≤ (radius 8 (33759/262144 : ℝ)) ∧ (radius 8 (33759/262144 : ℝ)) ≤ (15375489491/15625000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33759/262144 : ℝ)) (984031327423/1000000000000 : ℝ) (15375489491/15625000000 : ℝ) (44498838923/250000000000 : ℝ) (177995355699/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33759/262144 : ℝ)) (984031327423/1000000000000 : ℝ) (15375489491/15625000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33759/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984031327423/1000000000000 : ℝ) (15375489491/15625000000 : ℝ) (992015663711/1000000000000 : ℝ) (31000489491/31250000000 : ℝ) (99198353183/100000000000 : ℝ) (123997941479/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33759/262144 : ℝ)) 1 (992015663711/1000000000000 : ℝ) (31000489491/31250000000 : ℝ) (99198353183/100000000000 : ℝ) (123997941479/125000000000 : ℝ) (99199959777/100000000000 : ℝ) (247999899443/250000000000 : ℝ) (24799989941/25000000000 : ℝ) (495999798821/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33759/262144 : ℝ)) 2 (99199959777/100000000000 : ℝ) (247999899443/250000000000 : ℝ) (24799989941/25000000000 : ℝ) (495999798821/500000000000 : ℝ) (198399919541/200000000000 : ℝ) (991999597707/1000000000000 : ℝ) (123999949713/125000000000 : ℝ) (991999597707/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33759/262144 : ℝ)) 3 (198399919541/200000000000 : ℝ) (991999597707/1000000000000 : ℝ) (123999949713/125000000000 : ℝ) (991999597707/1000000000000 : ℝ) (123999949713/125000000000 : ℝ) (991999597707/1000000000000 : ℝ) (123999949713/125000000000 : ℝ) (991999597707/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33759/262144 : ℝ)) 4 (123999949713/125000000000 : ℝ) (991999597707/1000000000000 : ℝ) (123999949713/125000000000 : ℝ) (991999597707/1000000000000 : ℝ) (123999949713/125000000000 : ℝ) (991999597707/1000000000000 : ℝ) (123999949713/125000000000 : ℝ) (991999597707/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33759/262144 : ℝ)) 5 (123999949713/125000000000 : ℝ) (991999597707/1000000000000 : ℝ) (123999949713/125000000000 : ℝ) (991999597707/1000000000000 : ℝ) (123999949713/125000000000 : ℝ) (991999597707/1000000000000 : ℝ) (123999949713/125000000000 : ℝ) (991999597707/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33759/262144 : ℝ)) 6 (123999949713/125000000000 : ℝ) (991999597707/1000000000000 : ℝ) (123999949713/125000000000 : ℝ) (991999597707/1000000000000 : ℝ) (123999949713/125000000000 : ℝ) (991999597707/1000000000000 : ℝ) (123999949713/125000000000 : ℝ) (991999597707/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33759/262144 : ℝ)) 7 (123999949713/125000000000 : ℝ) (991999597707/1000000000000 : ℝ) (123999949713/125000000000 : ℝ) (991999597707/1000000000000 : ℝ) (123999949713/125000000000 : ℝ) (991999597707/1000000000000 : ℝ) (123999949713/125000000000 : ℝ) (991999597707/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33759/262144 : ℝ))) (44498838923/250000000000 : ℝ) (177995355699/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33759/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44498838923/250000000000 : ℝ) (177995355699/1000000000000 : ℝ) (294498838923/500000000000 : ℝ) (11779953557/20000000000 : ℝ) (675031933/1600000000 : ℝ) (84378991627/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33759/262144 : ℝ))) 1 (294498838923/500000000000 : ℝ) (11779953557/20000000000 : ℝ) (675031933/1600000000 : ℝ) (84378991627/200000000000 : ℝ) (101089263597/200000000000 : ℝ) (505446317993/1000000000000 : ℝ) (498492879217/1000000000000 : ℝ) (249246439613/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33759/262144 : ℝ))) 2 (101089263597/200000000000 : ℝ) (505446317993/1000000000000 : ℝ) (498492879217/1000000000000 : ℝ) (249246439613/500000000000 : ℝ) (501969598601/1000000000000 : ℝ) (50196959861/100000000000 : ℝ) (501957558307/1000000000000 : ℝ) (125489389579/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33759/262144 : ℝ))) 3 (501969598601/1000000000000 : ℝ) (50196959861/100000000000 : ℝ) (501957558307/1000000000000 : ℝ) (125489389579/250000000000 : ℝ) (250981789227/500000000000 : ℝ) (501963578463/1000000000000 : ℝ) (501963578417/1000000000000 : ℝ) (501963578427/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33759/262144 : ℝ))) 4 (250981789227/500000000000 : ℝ) (501963578463/1000000000000 : ℝ) (501963578417/1000000000000 : ℝ) (501963578427/1000000000000 : ℝ) (100392715687/200000000000 : ℝ) (100392715689/200000000000 : ℝ) (100392715687/200000000000 : ℝ) (100392715689/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33759/262144 : ℝ))) 5 (100392715687/200000000000 : ℝ) (100392715689/200000000000 : ℝ) (100392715687/200000000000 : ℝ) (100392715689/200000000000 : ℝ) (100392715687/200000000000 : ℝ) (100392715689/200000000000 : ℝ) (100392715687/200000000000 : ℝ) (100392715689/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33759/262144 : ℝ))) 6 (100392715687/200000000000 : ℝ) (100392715689/200000000000 : ℝ) (100392715687/200000000000 : ℝ) (100392715689/200000000000 : ℝ) (100392715687/200000000000 : ℝ) (100392715689/200000000000 : ℝ) (100392715687/200000000000 : ℝ) (100392715689/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33759/262144 : ℝ))) 7 (100392715687/200000000000 : ℝ) (100392715689/200000000000 : ℝ) (100392715687/200000000000 : ℝ) (100392715689/200000000000 : ℝ) (100392715687/200000000000 : ℝ) (100392715689/200000000000 : ℝ) (100392715687/200000000000 : ℝ) (100392715689/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33759/262144 : ℝ)) hmem 8 (123999949713/125000000000 : ℝ) (991999597707/1000000000000 : ℝ) (123999949713/125000000000 : ℝ) (991999597707/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33759/262144 : ℝ))) hcmem 8 (100392715687/200000000000 : ℝ) (100392715689/200000000000 : ℝ) (100392715687/200000000000 : ℝ) (100392715689/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33759/262144 : ℝ)) (123999949713/125000000000 : ℝ) (991999597707/1000000000000 : ℝ) (100392715687/200000000000 : ℝ) (100392715689/200000000000 : ℝ) (794841597731/1000000000000 : ℝ) (3179366391/4000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1326_exp_lower
  have heNumeric : (513726093567/250000000000 : ℝ)/4 ≤ Real.exp (-170512652149/256000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513726093567/250000000000 : ℝ)/4 ≤ Real.exp ((16879/131072 : ℝ)-(3179366391/4000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16879/131072 : ℝ) (33759/262144 : ℝ) (3179366391/4000000000 : ℝ) (513726093567/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1327; no trusted numerical premise.
theorem cover8_leaf1327_exp_radius : (997989770415757187/1000000000000000000 : ℝ) ≤ Real.exp ((-1055/65536 : ℝ)/8) ∧ Real.exp ((-1055/65536 : ℝ)/8) ≤ (249497442603939297/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1055/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1327_exp_lower : (920113609366663333/1000000000000000000 : ℝ) ≤ Real.exp ((-42628161598001/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628161598001/64000000000000 : ℝ)/8) ≤ (460056804683331667/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628161598001/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1327_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054904420479/1000000000000 : ℝ) ≤ 4*Real.exp (33759/262144 : ℝ)*Real.exp (-mu (radius 8 (1055/8192 : ℝ))) ∧ (20549/10000 : ℝ) < (2054904420479/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (1055/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1327_exp_radius
  have hrNumeric : (984030858201/1000000000000 : ℝ) ≤ Real.exp (-1055/65536 : ℝ) ∧ Real.exp (-1055/65536 : ℝ) ≤ (492015429101/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984030858201/1000000000000 : ℝ) ≤ (radius 8 (1055/8192 : ℝ)) ∧ (radius 8 (1055/8192 : ℝ)) ≤ (492015429101/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (1055/8192 : ℝ)) (984030858201/1000000000000 : ℝ) (492015429101/500000000000 : ℝ) (44499487431/250000000000 : ℝ) (177997949731/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (1055/8192 : ℝ)) (984030858201/1000000000000 : ℝ) (492015429101/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (1055/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984030858201/1000000000000 : ℝ) (492015429101/500000000000 : ℝ) (9920154291/10000000000 : ℝ) (992015429101/1000000000000 : ℝ) (991983295323/1000000000000 : ℝ) (39679331813/40000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (1055/8192 : ℝ)) 1 (9920154291/10000000000 : ℝ) (992015429101/1000000000000 : ℝ) (991983295323/1000000000000 : ℝ) (39679331813/40000000000 : ℝ) (991999362211/1000000000000 : ℝ) (991999362213/1000000000000 : ℝ) (991999362081/1000000000000 : ℝ) (991999362083/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (1055/8192 : ℝ)) 2 (991999362211/1000000000000 : ℝ) (991999362213/1000000000000 : ℝ) (991999362081/1000000000000 : ℝ) (991999362083/1000000000000 : ℝ) (495999681073/500000000000 : ℝ) (247999840537/250000000000 : ℝ) (198399872429/200000000000 : ℝ) (247999840537/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (1055/8192 : ℝ)) 3 (495999681073/500000000000 : ℝ) (247999840537/250000000000 : ℝ) (198399872429/200000000000 : ℝ) (247999840537/250000000000 : ℝ) (198399872429/200000000000 : ℝ) (247999840537/250000000000 : ℝ) (198399872429/200000000000 : ℝ) (247999840537/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (1055/8192 : ℝ)) 4 (198399872429/200000000000 : ℝ) (247999840537/250000000000 : ℝ) (198399872429/200000000000 : ℝ) (247999840537/250000000000 : ℝ) (198399872429/200000000000 : ℝ) (247999840537/250000000000 : ℝ) (198399872429/200000000000 : ℝ) (247999840537/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (1055/8192 : ℝ)) 5 (198399872429/200000000000 : ℝ) (247999840537/250000000000 : ℝ) (198399872429/200000000000 : ℝ) (247999840537/250000000000 : ℝ) (198399872429/200000000000 : ℝ) (247999840537/250000000000 : ℝ) (198399872429/200000000000 : ℝ) (247999840537/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (1055/8192 : ℝ)) 6 (198399872429/200000000000 : ℝ) (247999840537/250000000000 : ℝ) (198399872429/200000000000 : ℝ) (247999840537/250000000000 : ℝ) (198399872429/200000000000 : ℝ) (247999840537/250000000000 : ℝ) (198399872429/200000000000 : ℝ) (247999840537/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (1055/8192 : ℝ)) 7 (198399872429/200000000000 : ℝ) (247999840537/250000000000 : ℝ) (198399872429/200000000000 : ℝ) (247999840537/250000000000 : ℝ) (198399872429/200000000000 : ℝ) (247999840537/250000000000 : ℝ) (198399872429/200000000000 : ℝ) (247999840537/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (1055/8192 : ℝ))) (44499487431/250000000000 : ℝ) (177997949731/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (1055/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44499487431/250000000000 : ℝ) (177997949731/1000000000000 : ℝ) (294499487431/500000000000 : ℝ) (294499487433/500000000000 : ℝ) (421898032377/1000000000000 : ℝ) (210949016193/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (1055/8192 : ℝ))) 1 (294499487431/500000000000 : ℝ) (294499487433/500000000000 : ℝ) (421898032377/1000000000000 : ℝ) (210949016193/500000000000 : ℝ) (505448503619/1000000000000 : ℝ) (252724251813/500000000000 : ℝ) (124623811069/250000000000 : ℝ) (124623811071/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (1055/8192 : ℝ))) 2 (505448503619/1000000000000 : ℝ) (252724251813/500000000000 : ℝ) (124623811069/250000000000 : ℝ) (124623811071/250000000000 : ℝ) (501971873947/1000000000000 : ℝ) (100394374791/200000000000 : ℝ) (501959834329/1000000000000 : ℝ) (250979917169/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (1055/8192 : ℝ))) 3 (501971873947/1000000000000 : ℝ) (100394374791/200000000000 : ℝ) (501959834329/1000000000000 : ℝ) (250979917169/500000000000 : ℝ) (250982927069/500000000000 : ℝ) (501965854147/1000000000000 : ℝ) (501965854101/1000000000000 : ℝ) (501965854111/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (1055/8192 : ℝ))) 4 (250982927069/500000000000 : ℝ) (501965854147/1000000000000 : ℝ) (501965854101/1000000000000 : ℝ) (501965854111/1000000000000 : ℝ) (501965854119/1000000000000 : ℝ) (501965854129/1000000000000 : ℝ) (501965854119/1000000000000 : ℝ) (501965854129/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (1055/8192 : ℝ))) 5 (501965854119/1000000000000 : ℝ) (501965854129/1000000000000 : ℝ) (501965854119/1000000000000 : ℝ) (501965854129/1000000000000 : ℝ) (501965854119/1000000000000 : ℝ) (501965854129/1000000000000 : ℝ) (501965854119/1000000000000 : ℝ) (501965854129/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (1055/8192 : ℝ))) 6 (501965854119/1000000000000 : ℝ) (501965854129/1000000000000 : ℝ) (501965854119/1000000000000 : ℝ) (501965854129/1000000000000 : ℝ) (501965854119/1000000000000 : ℝ) (501965854129/1000000000000 : ℝ) (501965854119/1000000000000 : ℝ) (501965854129/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (1055/8192 : ℝ))) 7 (501965854119/1000000000000 : ℝ) (501965854129/1000000000000 : ℝ) (501965854119/1000000000000 : ℝ) (501965854129/1000000000000 : ℝ) (501965854119/1000000000000 : ℝ) (501965854129/1000000000000 : ℝ) (501965854119/1000000000000 : ℝ) (501965854129/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (1055/8192 : ℝ)) hmem 8 (198399872429/200000000000 : ℝ) (247999840537/250000000000 : ℝ) (198399872429/200000000000 : ℝ) (247999840537/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (1055/8192 : ℝ))) hcmem 8 (501965854119/1000000000000 : ℝ) (501965854129/1000000000000 : ℝ) (501965854119/1000000000000 : ℝ) (501965854129/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (1055/8192 : ℝ)) (198399872429/200000000000 : ℝ) (247999840537/250000000000 : ℝ) (501965854119/1000000000000 : ℝ) (501965854129/1000000000000 : ℝ) (794845389939/1000000000000 : ℝ) (794845389959/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1327_exp_lower
  have heNumeric : (2054904420479/1000000000000 : ℝ)/4 ≤ Real.exp (-42628161598001/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054904420479/1000000000000 : ℝ)/4 ≤ Real.exp ((33759/262144 : ℝ)-(794845389959/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33759/262144 : ℝ) (1055/8192 : ℝ) (794845389959/1000000000000 : ℝ) (2054904420479/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1328; no trusted numerical premise.
theorem cover8_leaf1328_exp_radius : (199597942186186641/200000000000000000 : ℝ) ≤ Real.exp ((-33761/2097152 : ℝ)/8) ∧ Real.exp ((-33761/2097152 : ℝ)/8) ≤ (498994855465466603/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33761/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1328_exp_lower : (920113611961069223/1000000000000000000 : ℝ) ≤ Real.exp ((-1332130004823/2000000000000 : ℝ)/8) ∧ Real.exp ((-1332130004823/2000000000000 : ℝ)/8) ≤ (115014201495133653/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1332130004823/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1328_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (128431529177/62500000000 : ℝ) ≤ 4*Real.exp (1055/8192 : ℝ)*Real.exp (-mu (radius 8 (33761/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (128431529177/62500000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33761/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1328_exp_radius
  have hrNumeric : (492015194489/500000000000 : ℝ) ≤ Real.exp (-33761/2097152 : ℝ) ∧ Real.exp (-33761/2097152 : ℝ) ≤ (984030388979/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492015194489/500000000000 : ℝ) ≤ (radius 8 (33761/262144 : ℝ)) ∧ (radius 8 (33761/262144 : ℝ)) ≤ (984030388979/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33761/262144 : ℝ)) (492015194489/500000000000 : ℝ) (984030388979/1000000000000 : ℝ) (178000543723/1000000000000 : ℝ) (178000543729/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33761/262144 : ℝ)) (492015194489/500000000000 : ℝ) (984030388979/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33761/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492015194489/500000000000 : ℝ) (984030388979/1000000000000 : ℝ) (992015194489/1000000000000 : ℝ) (99201519449/100000000000 : ℝ) (7749867647/7812500000 : ℝ) (991983058817/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33761/262144 : ℝ)) 1 (992015194489/1000000000000 : ℝ) (99201519449/100000000000 : ℝ) (7749867647/7812500000 : ℝ) (991983058817/1000000000000 : ℝ) (247999781663/250000000000 : ℝ) (495999563327/500000000000 : ℝ) (495999563261/500000000000 : ℝ) (247999781631/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33761/262144 : ℝ)) 2 (247999781663/250000000000 : ℝ) (495999563327/500000000000 : ℝ) (495999563261/500000000000 : ℝ) (247999781631/250000000000 : ℝ) (991999126587/1000000000000 : ℝ) (991999126589/1000000000000 : ℝ) (495999563293/500000000000 : ℝ) (991999126589/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33761/262144 : ℝ)) 3 (991999126587/1000000000000 : ℝ) (991999126589/1000000000000 : ℝ) (495999563293/500000000000 : ℝ) (991999126589/1000000000000 : ℝ) (495999563293/500000000000 : ℝ) (991999126589/1000000000000 : ℝ) (495999563293/500000000000 : ℝ) (991999126589/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33761/262144 : ℝ)) 4 (495999563293/500000000000 : ℝ) (991999126589/1000000000000 : ℝ) (495999563293/500000000000 : ℝ) (991999126589/1000000000000 : ℝ) (495999563293/500000000000 : ℝ) (991999126589/1000000000000 : ℝ) (495999563293/500000000000 : ℝ) (991999126589/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33761/262144 : ℝ)) 5 (495999563293/500000000000 : ℝ) (991999126589/1000000000000 : ℝ) (495999563293/500000000000 : ℝ) (991999126589/1000000000000 : ℝ) (495999563293/500000000000 : ℝ) (991999126589/1000000000000 : ℝ) (495999563293/500000000000 : ℝ) (991999126589/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33761/262144 : ℝ)) 6 (495999563293/500000000000 : ℝ) (991999126589/1000000000000 : ℝ) (495999563293/500000000000 : ℝ) (991999126589/1000000000000 : ℝ) (495999563293/500000000000 : ℝ) (991999126589/1000000000000 : ℝ) (495999563293/500000000000 : ℝ) (991999126589/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33761/262144 : ℝ)) 7 (495999563293/500000000000 : ℝ) (991999126589/1000000000000 : ℝ) (495999563293/500000000000 : ℝ) (991999126589/1000000000000 : ℝ) (495999563293/500000000000 : ℝ) (991999126589/1000000000000 : ℝ) (495999563293/500000000000 : ℝ) (991999126589/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33761/262144 : ℝ))) (178000543723/1000000000000 : ℝ) (178000543729/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33761/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (178000543723/1000000000000 : ℝ) (178000543729/1000000000000 : ℝ) (589000271861/1000000000000 : ℝ) (117800054373/200000000000 : ℝ) (421901106567/1000000000000 : ℝ) (16876044263/40000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33761/262144 : ℝ))) 1 (589000271861/1000000000000 : ℝ) (117800054373/200000000000 : ℝ) (421901106567/1000000000000 : ℝ) (16876044263/40000000000 : ℝ) (252725344607/500000000000 : ℝ) (25272534461/50000000000 : ℝ) (62312201161/125000000000 : ℝ) (99699521859/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33761/262144 : ℝ))) 2 (252725344607/500000000000 : ℝ) (25272534461/50000000000 : ℝ) (62312201161/125000000000 : ℝ) (99699521859/200000000000 : ℝ) (501974149251/1000000000000 : ℝ) (250987074629/500000000000 : ℝ) (501962110309/1000000000000 : ℝ) (125490527579/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33761/262144 : ℝ))) 3 (501974149251/1000000000000 : ℝ) (250987074629/500000000000 : ℝ) (501962110309/1000000000000 : ℝ) (125490527579/250000000000 : ℝ) (25098406489/50000000000 : ℝ) (501968129787/1000000000000 : ℝ) (501968129743/1000000000000 : ℝ) (501968129751/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33761/262144 : ℝ))) 4 (25098406489/50000000000 : ℝ) (501968129787/1000000000000 : ℝ) (501968129743/1000000000000 : ℝ) (501968129751/1000000000000 : ℝ) (501968129761/1000000000000 : ℝ) (501968129769/1000000000000 : ℝ) (501968129761/1000000000000 : ℝ) (501968129769/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33761/262144 : ℝ))) 5 (501968129761/1000000000000 : ℝ) (501968129769/1000000000000 : ℝ) (501968129761/1000000000000 : ℝ) (501968129769/1000000000000 : ℝ) (501968129761/1000000000000 : ℝ) (501968129769/1000000000000 : ℝ) (501968129761/1000000000000 : ℝ) (501968129769/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33761/262144 : ℝ))) 6 (501968129761/1000000000000 : ℝ) (501968129769/1000000000000 : ℝ) (501968129761/1000000000000 : ℝ) (501968129769/1000000000000 : ℝ) (501968129761/1000000000000 : ℝ) (501968129769/1000000000000 : ℝ) (501968129761/1000000000000 : ℝ) (501968129769/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33761/262144 : ℝ))) 7 (501968129761/1000000000000 : ℝ) (501968129769/1000000000000 : ℝ) (501968129761/1000000000000 : ℝ) (501968129769/1000000000000 : ℝ) (501968129761/1000000000000 : ℝ) (501968129769/1000000000000 : ℝ) (501968129761/1000000000000 : ℝ) (501968129769/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33761/262144 : ℝ)) hmem 8 (495999563293/500000000000 : ℝ) (991999126589/1000000000000 : ℝ) (495999563293/500000000000 : ℝ) (991999126589/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33761/262144 : ℝ))) hcmem 8 (501968129761/1000000000000 : ℝ) (501968129769/1000000000000 : ℝ) (501968129761/1000000000000 : ℝ) (501968129769/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33761/262144 : ℝ)) (495999563293/500000000000 : ℝ) (991999126589/1000000000000 : ℝ) (501968129761/1000000000000 : ℝ) (501968129769/1000000000000 : ℝ) (794849182083/1000000000000 : ℝ) (794849182099/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1328_exp_lower
  have heNumeric : (128431529177/62500000000 : ℝ)/4 ≤ Real.exp (-1332130004823/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (128431529177/62500000000 : ℝ)/4 ≤ Real.exp ((1055/8192 : ℝ)-(794849182099/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (1055/8192 : ℝ) (33761/262144 : ℝ) (794849182099/1000000000000 : ℝ) (128431529177/62500000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1329; no trusted numerical premise.
theorem cover8_leaf1329_exp_radius : (1949198537980689/1953125000000000 : ℝ) ≤ Real.exp ((-16881/1048576 : ℝ)/8) ∧ Real.exp ((-16881/1048576 : ℝ)/8) ≤ (997989651446112769/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16881/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1329_exp_lower : (460056807282165607/500000000000000000 : ℝ) ≤ Real.exp ((-42628158705743/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628158705743/64000000000000 : ℝ)/8) ≤ (184022722912866243/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628158705743/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1329_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (32107883021/15625000000 : ℝ) ≤ 4*Real.exp (33761/262144 : ℝ)*Real.exp (-mu (radius 8 (16881/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (32107883021/15625000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16881/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1329_exp_radius
  have hrNumeric : (246007479939/250000000000 : ℝ) ≤ Real.exp (-16881/1048576 : ℝ) ∧ Real.exp (-16881/1048576 : ℝ) ≤ (984029919757/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246007479939/250000000000 : ℝ) ≤ (radius 8 (16881/131072 : ℝ)) ∧ (radius 8 (16881/131072 : ℝ)) ≤ (984029919757/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16881/131072 : ℝ)) (246007479939/250000000000 : ℝ) (984029919757/1000000000000 : ℝ) (178003137677/1000000000000 : ℝ) (44500784421/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16881/131072 : ℝ)) (246007479939/250000000000 : ℝ) (984029919757/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16881/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246007479939/250000000000 : ℝ) (984029919757/1000000000000 : ℝ) (496007479939/500000000000 : ℝ) (992014959879/1000000000000 : ℝ) (247995705577/250000000000 : ℝ) (99198282231/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16881/131072 : ℝ)) 1 (496007479939/500000000000 : ℝ) (992014959879/1000000000000 : ℝ) (247995705577/250000000000 : ℝ) (99198282231/100000000000 : ℝ) (991998891093/1000000000000 : ℝ) (198399778219/200000000000 : ℝ) (495999445481/500000000000 : ℝ) (198399778193/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16881/131072 : ℝ)) 2 (991998891093/1000000000000 : ℝ) (198399778219/200000000000 : ℝ) (495999445481/500000000000 : ℝ) (198399778193/200000000000 : ℝ) (991998891027/1000000000000 : ℝ) (99199889103/100000000000 : ℝ) (991998891027/1000000000000 : ℝ) (99199889103/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16881/131072 : ℝ)) 3 (991998891027/1000000000000 : ℝ) (99199889103/100000000000 : ℝ) (991998891027/1000000000000 : ℝ) (99199889103/100000000000 : ℝ) (991998891027/1000000000000 : ℝ) (99199889103/100000000000 : ℝ) (991998891027/1000000000000 : ℝ) (99199889103/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16881/131072 : ℝ)) 4 (991998891027/1000000000000 : ℝ) (99199889103/100000000000 : ℝ) (991998891027/1000000000000 : ℝ) (99199889103/100000000000 : ℝ) (991998891027/1000000000000 : ℝ) (99199889103/100000000000 : ℝ) (991998891027/1000000000000 : ℝ) (99199889103/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16881/131072 : ℝ)) 5 (991998891027/1000000000000 : ℝ) (99199889103/100000000000 : ℝ) (991998891027/1000000000000 : ℝ) (99199889103/100000000000 : ℝ) (991998891027/1000000000000 : ℝ) (99199889103/100000000000 : ℝ) (991998891027/1000000000000 : ℝ) (99199889103/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16881/131072 : ℝ)) 6 (991998891027/1000000000000 : ℝ) (99199889103/100000000000 : ℝ) (991998891027/1000000000000 : ℝ) (99199889103/100000000000 : ℝ) (991998891027/1000000000000 : ℝ) (99199889103/100000000000 : ℝ) (991998891027/1000000000000 : ℝ) (99199889103/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16881/131072 : ℝ)) 7 (991998891027/1000000000000 : ℝ) (99199889103/100000000000 : ℝ) (991998891027/1000000000000 : ℝ) (99199889103/100000000000 : ℝ) (991998891027/1000000000000 : ℝ) (99199889103/100000000000 : ℝ) (991998891027/1000000000000 : ℝ) (99199889103/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16881/131072 : ℝ))) (178003137677/1000000000000 : ℝ) (44500784421/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16881/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (178003137677/1000000000000 : ℝ) (44500784421/250000000000 : ℝ) (294500784419/500000000000 : ℝ) (294500784421/500000000000 : ℝ) (210952090341/500000000000 : ℝ) (421904180691/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16881/131072 : ℝ))) 1 (294500784419/500000000000 : ℝ) (294500784421/500000000000 : ℝ) (210952090341/500000000000 : ℝ) (421904180691/1000000000000 : ℝ) (12636321869/25000000000 : ℝ) (505452874767/1000000000000 : ℝ) (498499974243/1000000000000 : ℝ) (498499974251/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16881/131072 : ℝ))) 2 (12636321869/25000000000 : ℝ) (505452874767/1000000000000 : ℝ) (498499974243/1000000000000 : ℝ) (498499974251/1000000000000 : ℝ) (501976424501/1000000000000 : ℝ) (501976424509/1000000000000 : ℝ) (100392877247/200000000000 : ℝ) (125491096561/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16881/131072 : ℝ))) 3 (501976424501/1000000000000 : ℝ) (501976424509/1000000000000 : ℝ) (100392877247/200000000000 : ℝ) (125491096561/250000000000 : ℝ) (62746300671/125000000000 : ℝ) (501970405377/1000000000000 : ℝ) (501970405331/1000000000000 : ℝ) (501970405341/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16881/131072 : ℝ))) 4 (62746300671/125000000000 : ℝ) (501970405377/1000000000000 : ℝ) (501970405331/1000000000000 : ℝ) (501970405341/1000000000000 : ℝ) (501970405349/1000000000000 : ℝ) (501970405359/1000000000000 : ℝ) (501970405349/1000000000000 : ℝ) (501970405359/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16881/131072 : ℝ))) 5 (501970405349/1000000000000 : ℝ) (501970405359/1000000000000 : ℝ) (501970405349/1000000000000 : ℝ) (501970405359/1000000000000 : ℝ) (501970405349/1000000000000 : ℝ) (501970405359/1000000000000 : ℝ) (501970405349/1000000000000 : ℝ) (501970405359/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16881/131072 : ℝ))) 6 (501970405349/1000000000000 : ℝ) (501970405359/1000000000000 : ℝ) (501970405349/1000000000000 : ℝ) (501970405359/1000000000000 : ℝ) (501970405349/1000000000000 : ℝ) (501970405359/1000000000000 : ℝ) (501970405349/1000000000000 : ℝ) (501970405359/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16881/131072 : ℝ))) 7 (501970405349/1000000000000 : ℝ) (501970405359/1000000000000 : ℝ) (501970405349/1000000000000 : ℝ) (501970405359/1000000000000 : ℝ) (501970405349/1000000000000 : ℝ) (501970405359/1000000000000 : ℝ) (501970405349/1000000000000 : ℝ) (501970405359/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16881/131072 : ℝ)) hmem 8 (991998891027/1000000000000 : ℝ) (99199889103/100000000000 : ℝ) (991998891027/1000000000000 : ℝ) (99199889103/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16881/131072 : ℝ))) hcmem 8 (501970405349/1000000000000 : ℝ) (501970405359/1000000000000 : ℝ) (501970405349/1000000000000 : ℝ) (501970405359/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16881/131072 : ℝ)) (991998891027/1000000000000 : ℝ) (99199889103/100000000000 : ℝ) (501970405349/1000000000000 : ℝ) (501970405359/1000000000000 : ℝ) (794852974143/1000000000000 : ℝ) (397426487081/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1329_exp_lower
  have heNumeric : (32107883021/15625000000 : ℝ)/4 ≤ Real.exp (-42628158705743/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (32107883021/15625000000 : ℝ)/4 ≤ Real.exp ((33761/262144 : ℝ)-(397426487081/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33761/262144 : ℝ) (16881/131072 : ℝ) (397426487081/500000000000 : ℝ) (32107883021/15625000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1330; no trusted numerical premise.
theorem cover8_leaf1330_exp_radius : (997989591961295877/1000000000000000000 : ℝ) ≤ Real.exp ((-33763/2097152 : ℝ)/8) ∧ Real.exp ((-33763/2097152 : ℝ)/8) ≤ (498994795980647939/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33763/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1330_exp_lower : (460056808588224653/500000000000000000 : ℝ) ≤ Real.exp ((-21314078626111/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314078626111/32000000000000 : ℝ)/8) ≤ (920113617176449307/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314078626111/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1330_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054904560013/1000000000000 : ℝ) ≤ 4*Real.exp (16881/131072 : ℝ)*Real.exp (-mu (radius 8 (33763/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054904560013/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33763/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1330_exp_radius
  have hrNumeric : (492014725267/500000000000 : ℝ) ≤ Real.exp (-33763/2097152 : ℝ) ∧ Real.exp (-33763/2097152 : ℝ) ≤ (196805890107/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492014725267/500000000000 : ℝ) ≤ (radius 8 (33763/262144 : ℝ)) ∧ (radius 8 (33763/262144 : ℝ)) ≤ (196805890107/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33763/262144 : ℝ)) (492014725267/500000000000 : ℝ) (196805890107/200000000000 : ℝ) (22250716449/125000000000 : ℝ) (178005731599/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33763/262144 : ℝ)) (492014725267/500000000000 : ℝ) (196805890107/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33763/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492014725267/500000000000 : ℝ) (196805890107/200000000000 : ℝ) (992014725267/1000000000000 : ℝ) (248003681317/250000000000 : ℝ) (991982585801/1000000000000 : ℝ) (991982585803/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33763/262144 : ℝ)) 1 (992014725267/1000000000000 : ℝ) (248003681317/250000000000 : ℝ) (991982585801/1000000000000 : ℝ) (991982585803/1000000000000 : ℝ) (495999327767/500000000000 : ℝ) (61999915971/62500000000 : ℝ) (991998655403/1000000000000 : ℝ) (495999327703/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33763/262144 : ℝ)) 2 (495999327767/500000000000 : ℝ) (61999915971/62500000000 : ℝ) (991998655403/1000000000000 : ℝ) (495999327703/500000000000 : ℝ) (247999663867/250000000000 : ℝ) (991998655471/1000000000000 : ℝ) (247999663867/250000000000 : ℝ) (991998655471/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33763/262144 : ℝ)) 3 (247999663867/250000000000 : ℝ) (991998655471/1000000000000 : ℝ) (247999663867/250000000000 : ℝ) (991998655471/1000000000000 : ℝ) (247999663867/250000000000 : ℝ) (991998655471/1000000000000 : ℝ) (247999663867/250000000000 : ℝ) (991998655471/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33763/262144 : ℝ)) 4 (247999663867/250000000000 : ℝ) (991998655471/1000000000000 : ℝ) (247999663867/250000000000 : ℝ) (991998655471/1000000000000 : ℝ) (247999663867/250000000000 : ℝ) (991998655471/1000000000000 : ℝ) (247999663867/250000000000 : ℝ) (991998655471/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33763/262144 : ℝ)) 5 (247999663867/250000000000 : ℝ) (991998655471/1000000000000 : ℝ) (247999663867/250000000000 : ℝ) (991998655471/1000000000000 : ℝ) (247999663867/250000000000 : ℝ) (991998655471/1000000000000 : ℝ) (247999663867/250000000000 : ℝ) (991998655471/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33763/262144 : ℝ)) 6 (247999663867/250000000000 : ℝ) (991998655471/1000000000000 : ℝ) (247999663867/250000000000 : ℝ) (991998655471/1000000000000 : ℝ) (247999663867/250000000000 : ℝ) (991998655471/1000000000000 : ℝ) (247999663867/250000000000 : ℝ) (991998655471/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33763/262144 : ℝ)) 7 (247999663867/250000000000 : ℝ) (991998655471/1000000000000 : ℝ) (247999663867/250000000000 : ℝ) (991998655471/1000000000000 : ℝ) (247999663867/250000000000 : ℝ) (991998655471/1000000000000 : ℝ) (247999663867/250000000000 : ℝ) (991998655471/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33763/262144 : ℝ))) (22250716449/125000000000 : ℝ) (178005731599/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33763/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (22250716449/125000000000 : ℝ) (178005731599/1000000000000 : ℝ) (147250716449/250000000000 : ℝ) (2945014329/5000000000 : ℝ) (421907254727/1000000000000 : ℝ) (421907254737/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33763/262144 : ℝ))) 1 (147250716449/250000000000 : ℝ) (2945014329/5000000000 : ℝ) (421907254727/1000000000000 : ℝ) (421907254737/1000000000000 : ℝ) (505455060261/1000000000000 : ℝ) (505455060269/1000000000000 : ℝ) (249251169573/500000000000 : ℝ) (249251169577/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33763/262144 : ℝ))) 2 (505455060261/1000000000000 : ℝ) (505455060269/1000000000000 : ℝ) (249251169573/500000000000 : ℝ) (249251169577/500000000000 : ℝ) (501978699703/1000000000000 : ℝ) (7843417183/15625000000 : ℝ) (501966662113/1000000000000 : ℝ) (250983331061/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33763/262144 : ℝ))) 3 (501978699703/1000000000000 : ℝ) (7843417183/15625000000 : ℝ) (501966662113/1000000000000 : ℝ) (250983331061/500000000000 : ℝ) (125493170227/250000000000 : ℝ) (501972680917/1000000000000 : ℝ) (501972680871/1000000000000 : ℝ) (501972680881/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33763/262144 : ℝ))) 4 (125493170227/250000000000 : ℝ) (501972680917/1000000000000 : ℝ) (501972680871/1000000000000 : ℝ) (501972680881/1000000000000 : ℝ) (501972680889/1000000000000 : ℝ) (501972680899/1000000000000 : ℝ) (501972680889/1000000000000 : ℝ) (501972680899/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33763/262144 : ℝ))) 5 (501972680889/1000000000000 : ℝ) (501972680899/1000000000000 : ℝ) (501972680889/1000000000000 : ℝ) (501972680899/1000000000000 : ℝ) (501972680889/1000000000000 : ℝ) (501972680899/1000000000000 : ℝ) (501972680889/1000000000000 : ℝ) (501972680899/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33763/262144 : ℝ))) 6 (501972680889/1000000000000 : ℝ) (501972680899/1000000000000 : ℝ) (501972680889/1000000000000 : ℝ) (501972680899/1000000000000 : ℝ) (501972680889/1000000000000 : ℝ) (501972680899/1000000000000 : ℝ) (501972680889/1000000000000 : ℝ) (501972680899/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33763/262144 : ℝ))) 7 (501972680889/1000000000000 : ℝ) (501972680899/1000000000000 : ℝ) (501972680889/1000000000000 : ℝ) (501972680899/1000000000000 : ℝ) (501972680889/1000000000000 : ℝ) (501972680899/1000000000000 : ℝ) (501972680889/1000000000000 : ℝ) (501972680899/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33763/262144 : ℝ)) hmem 8 (247999663867/250000000000 : ℝ) (991998655471/1000000000000 : ℝ) (247999663867/250000000000 : ℝ) (991998655471/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33763/262144 : ℝ))) hcmem 8 (501972680889/1000000000000 : ℝ) (501972680899/1000000000000 : ℝ) (501972680889/1000000000000 : ℝ) (501972680899/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33763/262144 : ℝ)) (247999663867/250000000000 : ℝ) (991998655471/1000000000000 : ℝ) (501972680889/1000000000000 : ℝ) (501972680899/1000000000000 : ℝ) (49678547883/62500000000 : ℝ) (198714191537/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1330_exp_lower
  have heNumeric : (2054904560013/1000000000000 : ℝ)/4 ≤ Real.exp (-21314078626111/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054904560013/1000000000000 : ℝ)/4 ≤ Real.exp ((16881/131072 : ℝ)-(198714191537/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16881/131072 : ℝ) (33763/262144 : ℝ) (198714191537/250000000000 : ℝ) (2054904560013/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1331; no trusted numerical premise.
theorem cover8_leaf1331_exp_radius : (997989532476482531/1000000000000000000 : ℝ) ≤ Real.exp ((-8441/524288 : ℝ)/8) ∧ Real.exp ((-8441/524288 : ℝ)/8) ≤ (249497383119120633/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8441/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1331_exp_lower : (57507101237382099/62500000000000000 : ℝ) ≤ Real.exp ((-42628155793389/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628155793389/64000000000000 : ℝ)/8) ≤ (184022723959622717/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628155793389/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1331_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054904606853/1000000000000 : ℝ) ≤ 4*Real.exp (33763/262144 : ℝ)*Real.exp (-mu (radius 8 (8441/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (2054904606853/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8441/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1331_exp_radius
  have hrNumeric : (984028981313/1000000000000 : ℝ) ≤ Real.exp (-8441/524288 : ℝ) ∧ Real.exp (-8441/524288 : ℝ) ≤ (492014490657/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984028981313/1000000000000 : ℝ) ≤ (radius 8 (8441/65536 : ℝ)) ∧ (radius 8 (8441/65536 : ℝ)) ≤ (492014490657/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8441/65536 : ℝ)) (984028981313/1000000000000 : ℝ) (492014490657/500000000000 : ℝ) (89004162731/500000000000 : ℝ) (178008325469/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8441/65536 : ℝ)) (984028981313/1000000000000 : ℝ) (492014490657/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8441/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984028981313/1000000000000 : ℝ) (492014490657/500000000000 : ℝ) (31000452833/31250000000 : ℝ) (992014490657/1000000000000 : ℝ) (198396469859/200000000000 : ℝ) (61998896831/62500000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8441/65536 : ℝ)) 1 (31000452833/31250000000 : ℝ) (992014490657/1000000000000 : ℝ) (198396469859/200000000000 : ℝ) (61998896831/62500000000 : ℝ) (39679936799/40000000000 : ℝ) (991998419977/1000000000000 : ℝ) (198399683969/200000000000 : ℝ) (991998419847/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8441/65536 : ℝ)) 2 (39679936799/40000000000 : ℝ) (991998419977/1000000000000 : ℝ) (198399683969/200000000000 : ℝ) (991998419847/1000000000000 : ℝ) (99199841991/100000000000 : ℝ) (123999802489/125000000000 : ℝ) (991998419909/1000000000000 : ℝ) (123999802489/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8441/65536 : ℝ)) 3 (99199841991/100000000000 : ℝ) (123999802489/125000000000 : ℝ) (991998419909/1000000000000 : ℝ) (123999802489/125000000000 : ℝ) (991998419909/1000000000000 : ℝ) (123999802489/125000000000 : ℝ) (991998419909/1000000000000 : ℝ) (123999802489/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8441/65536 : ℝ)) 4 (991998419909/1000000000000 : ℝ) (123999802489/125000000000 : ℝ) (991998419909/1000000000000 : ℝ) (123999802489/125000000000 : ℝ) (991998419909/1000000000000 : ℝ) (123999802489/125000000000 : ℝ) (991998419909/1000000000000 : ℝ) (123999802489/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8441/65536 : ℝ)) 5 (991998419909/1000000000000 : ℝ) (123999802489/125000000000 : ℝ) (991998419909/1000000000000 : ℝ) (123999802489/125000000000 : ℝ) (991998419909/1000000000000 : ℝ) (123999802489/125000000000 : ℝ) (991998419909/1000000000000 : ℝ) (123999802489/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8441/65536 : ℝ)) 6 (991998419909/1000000000000 : ℝ) (123999802489/125000000000 : ℝ) (991998419909/1000000000000 : ℝ) (123999802489/125000000000 : ℝ) (991998419909/1000000000000 : ℝ) (123999802489/125000000000 : ℝ) (991998419909/1000000000000 : ℝ) (123999802489/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8441/65536 : ℝ)) 7 (991998419909/1000000000000 : ℝ) (123999802489/125000000000 : ℝ) (991998419909/1000000000000 : ℝ) (123999802489/125000000000 : ℝ) (991998419909/1000000000000 : ℝ) (123999802489/125000000000 : ℝ) (991998419909/1000000000000 : ℝ) (123999802489/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8441/65536 : ℝ))) (89004162731/500000000000 : ℝ) (178008325469/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8441/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (89004162731/500000000000 : ℝ) (178008325469/1000000000000 : ℝ) (589004162731/1000000000000 : ℝ) (117800832547/200000000000 : ℝ) (421910328697/1000000000000 : ℝ) (421910328707/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8441/65536 : ℝ))) 1 (589004162731/1000000000000 : ℝ) (117800832547/200000000000 : ℝ) (421910328697/1000000000000 : ℝ) (421910328707/1000000000000 : ℝ) (252728622857/500000000000 : ℝ) (505457245721/1000000000000 : ℝ) (498504703991/1000000000000 : ℝ) (973642/1953125 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8441/65536 : ℝ))) 2 (252728622857/500000000000 : ℝ) (505457245721/1000000000000 : ℝ) (498504703991/1000000000000 : ℝ) (973642/1953125 : ℝ) (125495243713/250000000000 : ℝ) (501980974861/1000000000000 : ℝ) (250984468969/500000000000 : ℝ) (501968937947/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8441/65536 : ℝ))) 3 (125495243713/250000000000 : ℝ) (501980974861/1000000000000 : ℝ) (250984468969/500000000000 : ℝ) (501968937947/1000000000000 : ℝ) (100394991279/200000000000 : ℝ) (125493739101/250000000000 : ℝ) (250987478179/500000000000 : ℝ) (31373434773/62500000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8441/65536 : ℝ))) 4 (100394991279/200000000000 : ℝ) (125493739101/250000000000 : ℝ) (250987478179/500000000000 : ℝ) (31373434773/62500000000 : ℝ) (62746869547/125000000000 : ℝ) (250987478193/500000000000 : ℝ) (62746869547/125000000000 : ℝ) (250987478193/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8441/65536 : ℝ))) 5 (62746869547/125000000000 : ℝ) (250987478193/500000000000 : ℝ) (62746869547/125000000000 : ℝ) (250987478193/500000000000 : ℝ) (62746869547/125000000000 : ℝ) (250987478193/500000000000 : ℝ) (62746869547/125000000000 : ℝ) (250987478193/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8441/65536 : ℝ))) 6 (62746869547/125000000000 : ℝ) (250987478193/500000000000 : ℝ) (62746869547/125000000000 : ℝ) (250987478193/500000000000 : ℝ) (62746869547/125000000000 : ℝ) (250987478193/500000000000 : ℝ) (62746869547/125000000000 : ℝ) (250987478193/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8441/65536 : ℝ))) 7 (62746869547/125000000000 : ℝ) (250987478193/500000000000 : ℝ) (62746869547/125000000000 : ℝ) (250987478193/500000000000 : ℝ) (62746869547/125000000000 : ℝ) (250987478193/500000000000 : ℝ) (62746869547/125000000000 : ℝ) (250987478193/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8441/65536 : ℝ)) hmem 8 (991998419909/1000000000000 : ℝ) (123999802489/125000000000 : ℝ) (991998419909/1000000000000 : ℝ) (123999802489/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8441/65536 : ℝ))) hcmem 8 (62746869547/125000000000 : ℝ) (250987478193/500000000000 : ℝ) (62746869547/125000000000 : ℝ) (250987478193/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8441/65536 : ℝ)) (991998419909/1000000000000 : ℝ) (123999802489/125000000000 : ℝ) (62746869547/125000000000 : ℝ) (250987478193/500000000000 : ℝ) (49678784877/62500000000 : ℝ) (794860558051/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1331_exp_lower
  have heNumeric : (2054904606853/1000000000000 : ℝ)/4 ≤ Real.exp (-42628155793389/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054904606853/1000000000000 : ℝ)/4 ≤ Real.exp ((33763/262144 : ℝ)-(794860558051/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33763/262144 : ℝ) (8441/65536 : ℝ) (794860558051/1000000000000 : ℝ) (2054904606853/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1332; no trusted numerical premise.
theorem cover8_leaf1332_exp_radius : (997989472991672731/1000000000000000000 : ℝ) ≤ Real.exp ((-33765/2097152 : ℝ)/8) ∧ Real.exp ((-33765/2097152 : ℝ)/8) ≤ (249497368247918183/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33765/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1332_exp_lower : (920113622427483821/1000000000000000000 : ℝ) ≤ Real.exp ((-10657038582567/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657038582567/16000000000000 : ℝ)/8) ≤ (460056811213741911/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657038582567/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1332_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054904653831/1000000000000 : ℝ) ≤ 4*Real.exp (8441/65536 : ℝ)*Real.exp (-mu (radius 8 (33765/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054904653831/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33765/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1332_exp_radius
  have hrNumeric : (984028512091/1000000000000 : ℝ) ≤ Real.exp (-33765/2097152 : ℝ) ∧ Real.exp (-33765/2097152 : ℝ) ≤ (246007128023/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984028512091/1000000000000 : ℝ) ≤ (radius 8 (33765/262144 : ℝ)) ∧ (radius 8 (33765/262144 : ℝ)) ≤ (246007128023/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33765/262144 : ℝ)) (984028512091/1000000000000 : ℝ) (246007128023/250000000000 : ℝ) (178010919299/1000000000000 : ℝ) (89005459653/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33765/262144 : ℝ)) (984028512091/1000000000000 : ℝ) (246007128023/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33765/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984028512091/1000000000000 : ℝ) (246007128023/250000000000 : ℝ) (198402851209/200000000000 : ℝ) (496007128023/500000000000 : ℝ) (991982112787/1000000000000 : ℝ) (991982112789/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33765/262144 : ℝ)) 1 (198402851209/200000000000 : ℝ) (496007128023/500000000000 : ℝ) (991982112787/1000000000000 : ℝ) (991982112789/1000000000000 : ℝ) (30999943263/31250000000 : ℝ) (495999092209/500000000000 : ℝ) (198399636857/200000000000 : ℝ) (30999943259/31250000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33765/262144 : ℝ)) 2 (30999943263/31250000000 : ℝ) (495999092209/500000000000 : ℝ) (198399636857/200000000000 : ℝ) (30999943259/31250000000 : ℝ) (19839963687/20000000000 : ℝ) (991998184353/1000000000000 : ℝ) (19839963687/20000000000 : ℝ) (991998184353/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33765/262144 : ℝ)) 3 (19839963687/20000000000 : ℝ) (991998184353/1000000000000 : ℝ) (19839963687/20000000000 : ℝ) (991998184353/1000000000000 : ℝ) (19839963687/20000000000 : ℝ) (991998184353/1000000000000 : ℝ) (19839963687/20000000000 : ℝ) (991998184353/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33765/262144 : ℝ)) 4 (19839963687/20000000000 : ℝ) (991998184353/1000000000000 : ℝ) (19839963687/20000000000 : ℝ) (991998184353/1000000000000 : ℝ) (19839963687/20000000000 : ℝ) (991998184353/1000000000000 : ℝ) (19839963687/20000000000 : ℝ) (991998184353/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33765/262144 : ℝ)) 5 (19839963687/20000000000 : ℝ) (991998184353/1000000000000 : ℝ) (19839963687/20000000000 : ℝ) (991998184353/1000000000000 : ℝ) (19839963687/20000000000 : ℝ) (991998184353/1000000000000 : ℝ) (19839963687/20000000000 : ℝ) (991998184353/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33765/262144 : ℝ)) 6 (19839963687/20000000000 : ℝ) (991998184353/1000000000000 : ℝ) (19839963687/20000000000 : ℝ) (991998184353/1000000000000 : ℝ) (19839963687/20000000000 : ℝ) (991998184353/1000000000000 : ℝ) (19839963687/20000000000 : ℝ) (991998184353/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33765/262144 : ℝ)) 7 (19839963687/20000000000 : ℝ) (991998184353/1000000000000 : ℝ) (19839963687/20000000000 : ℝ) (991998184353/1000000000000 : ℝ) (19839963687/20000000000 : ℝ) (991998184353/1000000000000 : ℝ) (19839963687/20000000000 : ℝ) (991998184353/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33765/262144 : ℝ))) (178010919299/1000000000000 : ℝ) (89005459653/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33765/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (178010919299/1000000000000 : ℝ) (89005459653/500000000000 : ℝ) (589005459649/1000000000000 : ℝ) (589005459653/1000000000000 : ℝ) (210956701303/500000000000 : ℝ) (84382680523/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33765/262144 : ℝ))) 1 (589005459649/1000000000000 : ℝ) (589005459653/1000000000000 : ℝ) (210956701303/500000000000 : ℝ) (84382680523/200000000000 : ℝ) (505459431127/1000000000000 : ℝ) (252729715567/500000000000 : ℝ) (49850706879/100000000000 : ℝ) (249253534399/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33765/262144 : ℝ))) 2 (505459431127/1000000000000 : ℝ) (252729715567/500000000000 : ℝ) (49850706879/100000000000 : ℝ) (249253534399/500000000000 : ℝ) (250991624979/500000000000 : ℝ) (250991624983/500000000000 : ℝ) (501971213719/1000000000000 : ℝ) (15686600429/31250000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33765/262144 : ℝ))) 3 (250991624979/500000000000 : ℝ) (250991624983/500000000000 : ℝ) (501971213719/1000000000000 : ℝ) (15686600429/31250000000 : ℝ) (250988615919/500000000000 : ℝ) (501977231847/1000000000000 : ℝ) (250988615901/500000000000 : ℝ) (501977231811/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33765/262144 : ℝ))) 4 (250988615919/500000000000 : ℝ) (501977231847/1000000000000 : ℝ) (250988615901/500000000000 : ℝ) (501977231811/1000000000000 : ℝ) (25098861591/50000000000 : ℝ) (501977231829/1000000000000 : ℝ) (501977231819/1000000000000 : ℝ) (501977231829/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33765/262144 : ℝ))) 5 (25098861591/50000000000 : ℝ) (501977231829/1000000000000 : ℝ) (501977231819/1000000000000 : ℝ) (501977231829/1000000000000 : ℝ) (501977231819/1000000000000 : ℝ) (501977231829/1000000000000 : ℝ) (501977231819/1000000000000 : ℝ) (501977231829/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33765/262144 : ℝ))) 6 (501977231819/1000000000000 : ℝ) (501977231829/1000000000000 : ℝ) (501977231819/1000000000000 : ℝ) (501977231829/1000000000000 : ℝ) (501977231819/1000000000000 : ℝ) (501977231829/1000000000000 : ℝ) (501977231819/1000000000000 : ℝ) (501977231829/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33765/262144 : ℝ))) 7 (501977231819/1000000000000 : ℝ) (501977231829/1000000000000 : ℝ) (501977231819/1000000000000 : ℝ) (501977231829/1000000000000 : ℝ) (501977231819/1000000000000 : ℝ) (501977231829/1000000000000 : ℝ) (501977231819/1000000000000 : ℝ) (501977231829/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33765/262144 : ℝ)) hmem 8 (19839963687/20000000000 : ℝ) (991998184353/1000000000000 : ℝ) (19839963687/20000000000 : ℝ) (991998184353/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33765/262144 : ℝ))) hcmem 8 (501977231819/1000000000000 : ℝ) (501977231829/1000000000000 : ℝ) (501977231819/1000000000000 : ℝ) (501977231829/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33765/262144 : ℝ)) (19839963687/20000000000 : ℝ) (991998184353/1000000000000 : ℝ) (501977231819/1000000000000 : ℝ) (501977231829/1000000000000 : ℝ) (794864349867/1000000000000 : ℝ) (794864349887/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1332_exp_lower
  have heNumeric : (2054904653831/1000000000000 : ℝ)/4 ≤ Real.exp (-10657038582567/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054904653831/1000000000000 : ℝ)/4 ≤ Real.exp ((8441/65536 : ℝ)-(794864349887/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8441/65536 : ℝ) (33765/262144 : ℝ) (794864349887/1000000000000 : ℝ) (2054904653831/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1333; no trusted numerical premise.
theorem cover8_leaf1333_exp_radius : (249497353376716619/250000000000000000 : ℝ) ≤ Real.exp ((-16883/1048576 : ℝ)/8) ∧ Real.exp ((-16883/1048576 : ℝ)/8) ≤ (997989413506866477/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16883/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1333_exp_lower : (92011362506628523/100000000000000000 : ℝ) ≤ Real.exp ((-42628152861899/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628152861899/64000000000000 : ℝ)/8) ≤ (920113625066285231/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628152861899/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1333_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054904700977/1000000000000 : ℝ) ≤ 4*Real.exp (33765/262144 : ℝ)*Real.exp (-mu (radius 8 (16883/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054904700977/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16883/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1333_exp_radius
  have hrNumeric : (98402804287/100000000000 : ℝ) ≤ Real.exp (-16883/1048576 : ℝ) ∧ Real.exp (-16883/1048576 : ℝ) ≤ (984028042871/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (98402804287/100000000000 : ℝ) ≤ (radius 8 (16883/131072 : ℝ)) ∧ (radius 8 (16883/131072 : ℝ)) ≤ (984028042871/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16883/131072 : ℝ)) (98402804287/100000000000 : ℝ) (984028042871/1000000000000 : ℝ) (44503378273/250000000000 : ℝ) (89006756549/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16883/131072 : ℝ)) (98402804287/100000000000 : ℝ) (984028042871/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16883/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (98402804287/100000000000 : ℝ) (984028042871/1000000000000 : ℝ) (198402804287/200000000000 : ℝ) (248003505359/250000000000 : ℝ) (991981876281/1000000000000 : ℝ) (495990938141/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16883/131072 : ℝ)) 1 (198402804287/200000000000 : ℝ) (248003505359/250000000000 : ℝ) (991981876281/1000000000000 : ℝ) (495990938141/500000000000 : ℝ) (495998974429/500000000000 : ℝ) (991997948859/1000000000000 : ℝ) (991997948727/1000000000000 : ℝ) (991997948729/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16883/131072 : ℝ)) 2 (495998974429/500000000000 : ℝ) (991997948859/1000000000000 : ℝ) (991997948727/1000000000000 : ℝ) (991997948729/1000000000000 : ℝ) (123999743599/125000000000 : ℝ) (495998974397/500000000000 : ℝ) (123999743599/125000000000 : ℝ) (495998974397/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16883/131072 : ℝ)) 3 (123999743599/125000000000 : ℝ) (495998974397/500000000000 : ℝ) (123999743599/125000000000 : ℝ) (495998974397/500000000000 : ℝ) (123999743599/125000000000 : ℝ) (495998974397/500000000000 : ℝ) (123999743599/125000000000 : ℝ) (495998974397/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16883/131072 : ℝ)) 4 (123999743599/125000000000 : ℝ) (495998974397/500000000000 : ℝ) (123999743599/125000000000 : ℝ) (495998974397/500000000000 : ℝ) (123999743599/125000000000 : ℝ) (495998974397/500000000000 : ℝ) (123999743599/125000000000 : ℝ) (495998974397/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16883/131072 : ℝ)) 5 (123999743599/125000000000 : ℝ) (495998974397/500000000000 : ℝ) (123999743599/125000000000 : ℝ) (495998974397/500000000000 : ℝ) (123999743599/125000000000 : ℝ) (495998974397/500000000000 : ℝ) (123999743599/125000000000 : ℝ) (495998974397/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16883/131072 : ℝ)) 6 (123999743599/125000000000 : ℝ) (495998974397/500000000000 : ℝ) (123999743599/125000000000 : ℝ) (495998974397/500000000000 : ℝ) (123999743599/125000000000 : ℝ) (495998974397/500000000000 : ℝ) (123999743599/125000000000 : ℝ) (495998974397/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16883/131072 : ℝ)) 7 (123999743599/125000000000 : ℝ) (495998974397/500000000000 : ℝ) (123999743599/125000000000 : ℝ) (495998974397/500000000000 : ℝ) (123999743599/125000000000 : ℝ) (495998974397/500000000000 : ℝ) (123999743599/125000000000 : ℝ) (495998974397/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16883/131072 : ℝ))) (44503378273/250000000000 : ℝ) (89006756549/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16883/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44503378273/250000000000 : ℝ) (89006756549/500000000000 : ℝ) (294503378273/500000000000 : ℝ) (589006756549/1000000000000 : ℝ) (10547911911/25000000000 : ℝ) (13184889889/31250000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16883/131072 : ℝ))) 1 (294503378273/500000000000 : ℝ) (589006756549/1000000000000 : ℝ) (10547911911/25000000000 : ℝ) (13184889889/31250000000 : ℝ) (505461616493/1000000000000 : ℝ) (505461616499/1000000000000 : ℝ) (124627358383/250000000000 : ℝ) (498509433539/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16883/131072 : ℝ))) 2 (505461616493/1000000000000 : ℝ) (505461616499/1000000000000 : ℝ) (124627358383/250000000000 : ℝ) (498509433539/1000000000000 : ℝ) (125496381253/250000000000 : ℝ) (501985525019/1000000000000 : ℝ) (501973489449/1000000000000 : ℝ) (31373343091/62500000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16883/131072 : ℝ))) 3 (125496381253/250000000000 : ℝ) (501985525019/1000000000000 : ℝ) (501973489449/1000000000000 : ℝ) (31373343091/62500000000 : ℝ) (50197950723/100000000000 : ℝ) (250989753619/500000000000 : ℝ) (250989753597/500000000000 : ℝ) (250989753601/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16883/131072 : ℝ))) 4 (50197950723/100000000000 : ℝ) (250989753619/500000000000 : ℝ) (250989753597/500000000000 : ℝ) (250989753601/500000000000 : ℝ) (125494876803/250000000000 : ℝ) (25098975361/50000000000 : ℝ) (501979507211/1000000000000 : ℝ) (25098975361/50000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16883/131072 : ℝ))) 5 (125494876803/250000000000 : ℝ) (25098975361/50000000000 : ℝ) (501979507211/1000000000000 : ℝ) (25098975361/50000000000 : ℝ) (501979507211/1000000000000 : ℝ) (25098975361/50000000000 : ℝ) (501979507211/1000000000000 : ℝ) (25098975361/50000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16883/131072 : ℝ))) 6 (501979507211/1000000000000 : ℝ) (25098975361/50000000000 : ℝ) (501979507211/1000000000000 : ℝ) (25098975361/50000000000 : ℝ) (501979507211/1000000000000 : ℝ) (25098975361/50000000000 : ℝ) (501979507211/1000000000000 : ℝ) (25098975361/50000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16883/131072 : ℝ))) 7 (501979507211/1000000000000 : ℝ) (25098975361/50000000000 : ℝ) (501979507211/1000000000000 : ℝ) (25098975361/50000000000 : ℝ) (501979507211/1000000000000 : ℝ) (25098975361/50000000000 : ℝ) (501979507211/1000000000000 : ℝ) (25098975361/50000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16883/131072 : ℝ)) hmem 8 (123999743599/125000000000 : ℝ) (495998974397/500000000000 : ℝ) (123999743599/125000000000 : ℝ) (495998974397/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16883/131072 : ℝ))) hcmem 8 (501979507211/1000000000000 : ℝ) (25098975361/50000000000 : ℝ) (501979507211/1000000000000 : ℝ) (25098975361/50000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16883/131072 : ℝ)) (123999743599/125000000000 : ℝ) (495998974397/500000000000 : ℝ) (501979507211/1000000000000 : ℝ) (25098975361/50000000000 : ℝ) (99358517703/125000000000 : ℝ) (794868141641/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1333_exp_lower
  have heNumeric : (2054904700977/1000000000000 : ℝ)/4 ≤ Real.exp (-42628152861899/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054904700977/1000000000000 : ℝ)/4 ≤ Real.exp ((33765/262144 : ℝ)-(794868141641/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33765/262144 : ℝ) (16883/131072 : ℝ) (794868141641/1000000000000 : ℝ) (2054904700977/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1334; no trusted numerical premise.
theorem cover8_leaf1334_exp_radius : (124748669252757971/125000000000000000 : ℝ) ≤ Real.exp ((-33767/2097152 : ℝ)/8) ∧ Real.exp ((-33767/2097152 : ℝ)/8) ≤ (997989354022063769/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33767/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1334_exp_lower : (92011362771336767/100000000000000000 : ℝ) ≤ Real.exp ((-21314075694461/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314075694461/32000000000000 : ℝ)/8) ≤ (920113627713367671/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314075694461/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1334_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054904748271/1000000000000 : ℝ) ≤ 4*Real.exp (16883/131072 : ℝ)*Real.exp (-mu (radius 8 (33767/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054904748271/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33767/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1334_exp_radius
  have hrNumeric : (984027573649/1000000000000 : ℝ) ≤ Real.exp (-33767/2097152 : ℝ) ∧ Real.exp (-33767/2097152 : ℝ) ≤ (19680551473/20000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984027573649/1000000000000 : ℝ) ≤ (radius 8 (33767/262144 : ℝ)) ∧ (radius 8 (33767/262144 : ℝ)) ≤ (19680551473/20000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33767/262144 : ℝ)) (984027573649/1000000000000 : ℝ) (19680551473/20000000000 : ℝ) (35603221369/200000000000 : ℝ) (44504026713/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33767/262144 : ℝ)) (984027573649/1000000000000 : ℝ) (19680551473/20000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33767/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984027573649/1000000000000 : ℝ) (19680551473/20000000000 : ℝ) (124001723353/125000000000 : ℝ) (39680551473/40000000000 : ℝ) (495990819887/500000000000 : ℝ) (39679265591/40000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33767/262144 : ℝ)) 1 (124001723353/125000000000 : ℝ) (39680551473/40000000000 : ℝ) (495990819887/500000000000 : ℝ) (39679265591/40000000000 : ℝ) (991997713299/1000000000000 : ℝ) (9919977133/10000000000 : ℝ) (61999857073/62500000000 : ℝ) (99199771317/100000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33767/262144 : ℝ)) 2 (991997713299/1000000000000 : ℝ) (9919977133/10000000000 : ℝ) (61999857073/62500000000 : ℝ) (99199771317/100000000000 : ℝ) (991997713233/1000000000000 : ℝ) (198399542647/200000000000 : ℝ) (991997713233/1000000000000 : ℝ) (198399542647/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33767/262144 : ℝ)) 3 (991997713233/1000000000000 : ℝ) (198399542647/200000000000 : ℝ) (991997713233/1000000000000 : ℝ) (198399542647/200000000000 : ℝ) (991997713233/1000000000000 : ℝ) (198399542647/200000000000 : ℝ) (991997713233/1000000000000 : ℝ) (198399542647/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33767/262144 : ℝ)) 4 (991997713233/1000000000000 : ℝ) (198399542647/200000000000 : ℝ) (991997713233/1000000000000 : ℝ) (198399542647/200000000000 : ℝ) (991997713233/1000000000000 : ℝ) (198399542647/200000000000 : ℝ) (991997713233/1000000000000 : ℝ) (198399542647/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33767/262144 : ℝ)) 5 (991997713233/1000000000000 : ℝ) (198399542647/200000000000 : ℝ) (991997713233/1000000000000 : ℝ) (198399542647/200000000000 : ℝ) (991997713233/1000000000000 : ℝ) (198399542647/200000000000 : ℝ) (991997713233/1000000000000 : ℝ) (198399542647/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33767/262144 : ℝ)) 6 (991997713233/1000000000000 : ℝ) (198399542647/200000000000 : ℝ) (991997713233/1000000000000 : ℝ) (198399542647/200000000000 : ℝ) (991997713233/1000000000000 : ℝ) (198399542647/200000000000 : ℝ) (991997713233/1000000000000 : ℝ) (198399542647/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33767/262144 : ℝ)) 7 (991997713233/1000000000000 : ℝ) (198399542647/200000000000 : ℝ) (991997713233/1000000000000 : ℝ) (198399542647/200000000000 : ℝ) (991997713233/1000000000000 : ℝ) (198399542647/200000000000 : ℝ) (991997713233/1000000000000 : ℝ) (198399542647/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33767/262144 : ℝ))) (35603221369/200000000000 : ℝ) (44504026713/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33767/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35603221369/200000000000 : ℝ) (44504026713/250000000000 : ℝ) (294504026711/500000000000 : ℝ) (294504026713/500000000000 : ℝ) (105479887551/250000000000 : ℝ) (210959775107/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33767/262144 : ℝ))) 1 (294504026711/500000000000 : ℝ) (294504026713/500000000000 : ℝ) (105479887551/250000000000 : ℝ) (210959775107/500000000000 : ℝ) (505463801813/1000000000000 : ℝ) (25273190091/50000000000 : ℝ) (498511798221/1000000000000 : ℝ) (49851179823/100000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33767/262144 : ℝ))) 2 (505463801813/1000000000000 : ℝ) (25273190091/50000000000 : ℝ) (498511798221/1000000000000 : ℝ) (49851179823/100000000000 : ℝ) (501987800017/1000000000000 : ℝ) (20079512001/40000000000 : ℝ) (501975765129/1000000000000 : ℝ) (250987882569/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33767/262144 : ℝ))) 3 (501987800017/1000000000000 : ℝ) (20079512001/40000000000 : ℝ) (501975765129/1000000000000 : ℝ) (250987882569/500000000000 : ℝ) (501981782573/1000000000000 : ℝ) (250990891291/500000000000 : ℝ) (62747722817/125000000000 : ℝ) (250990891273/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33767/262144 : ℝ))) 4 (501981782573/1000000000000 : ℝ) (250990891291/500000000000 : ℝ) (62747722817/125000000000 : ℝ) (250990891273/500000000000 : ℝ) (250990891277/500000000000 : ℝ) (125495445641/250000000000 : ℝ) (250990891277/500000000000 : ℝ) (125495445641/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33767/262144 : ℝ))) 5 (250990891277/500000000000 : ℝ) (125495445641/250000000000 : ℝ) (250990891277/500000000000 : ℝ) (125495445641/250000000000 : ℝ) (250990891277/500000000000 : ℝ) (125495445641/250000000000 : ℝ) (250990891277/500000000000 : ℝ) (125495445641/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33767/262144 : ℝ))) 6 (250990891277/500000000000 : ℝ) (125495445641/250000000000 : ℝ) (250990891277/500000000000 : ℝ) (125495445641/250000000000 : ℝ) (250990891277/500000000000 : ℝ) (125495445641/250000000000 : ℝ) (250990891277/500000000000 : ℝ) (125495445641/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33767/262144 : ℝ))) 7 (250990891277/500000000000 : ℝ) (125495445641/250000000000 : ℝ) (250990891277/500000000000 : ℝ) (125495445641/250000000000 : ℝ) (250990891277/500000000000 : ℝ) (125495445641/250000000000 : ℝ) (250990891277/500000000000 : ℝ) (125495445641/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33767/262144 : ℝ)) hmem 8 (991997713233/1000000000000 : ℝ) (198399542647/200000000000 : ℝ) (991997713233/1000000000000 : ℝ) (198399542647/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33767/262144 : ℝ))) hcmem 8 (250990891277/500000000000 : ℝ) (125495445641/250000000000 : ℝ) (250990891277/500000000000 : ℝ) (125495445641/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33767/262144 : ℝ)) (991997713233/1000000000000 : ℝ) (198399542647/200000000000 : ℝ) (250990891277/500000000000 : ℝ) (125495445641/250000000000 : ℝ) (158974386661/200000000000 : ℝ) (794871933323/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1334_exp_lower
  have heNumeric : (2054904748271/1000000000000 : ℝ)/4 ≤ Real.exp (-21314075694461/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054904748271/1000000000000 : ℝ)/4 ≤ Real.exp ((16883/131072 : ℝ)-(794871933323/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16883/131072 : ℝ) (33767/262144 : ℝ) (794871933323/1000000000000 : ℝ) (2054904748271/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1335; no trusted numerical premise.
theorem cover8_leaf1335_exp_radius : (249497323634316151/250000000000000000 : ℝ) ≤ Real.exp ((-4221/262144 : ℝ)/8) ∧ Real.exp ((-4221/262144 : ℝ)/8) ≤ (199597858907452921/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4221/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1335_exp_lower : (920113630369191197/1000000000000000000 : ℝ) ≤ Real.exp ((-42628149911081/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628149911081/64000000000000 : ℝ)/8) ≤ (460056815184595599/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628149911081/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1335_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027452397861/500000000000 : ℝ) ≤ 4*Real.exp (33767/262144 : ℝ)*Real.exp (-mu (radius 8 (4221/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (1027452397861/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4221/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1335_exp_radius
  have hrNumeric : (246006776107/250000000000 : ℝ) ≤ Real.exp (-4221/262144 : ℝ) ∧ Real.exp (-4221/262144 : ℝ) ≤ (984027104429/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246006776107/250000000000 : ℝ) ≤ (radius 8 (4221/32768 : ℝ)) ∧ (radius 8 (4221/32768 : ℝ)) ≤ (984027104429/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4221/32768 : ℝ)) (246006776107/250000000000 : ℝ) (984027104429/1000000000000 : ℝ) (2225233757/12500000000 : ℝ) (89009350283/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4221/32768 : ℝ)) (246006776107/250000000000 : ℝ) (984027104429/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4221/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246006776107/250000000000 : ℝ) (984027104429/1000000000000 : ℝ) (496006776107/500000000000 : ℝ) (198402710443/200000000000 : ℝ) (991981403267/1000000000000 : ℝ) (247995350817/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4221/32768 : ℝ)) 1 (496006776107/500000000000 : ℝ) (198402710443/200000000000 : ℝ) (991981403267/1000000000000 : ℝ) (247995350817/250000000000 : ℝ) (49599873887/50000000000 : ℝ) (495998738871/500000000000 : ℝ) (99199747761/100000000000 : ℝ) (247999369403/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4221/32768 : ℝ)) 2 (49599873887/50000000000 : ℝ) (495998738871/500000000000 : ℝ) (99199747761/100000000000 : ℝ) (247999369403/250000000000 : ℝ) (39679899107/40000000000 : ℝ) (991997477677/1000000000000 : ℝ) (495998738837/500000000000 : ℝ) (991997477677/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4221/32768 : ℝ)) 3 (39679899107/40000000000 : ℝ) (991997477677/1000000000000 : ℝ) (495998738837/500000000000 : ℝ) (991997477677/1000000000000 : ℝ) (495998738837/500000000000 : ℝ) (991997477677/1000000000000 : ℝ) (495998738837/500000000000 : ℝ) (991997477677/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4221/32768 : ℝ)) 4 (495998738837/500000000000 : ℝ) (991997477677/1000000000000 : ℝ) (495998738837/500000000000 : ℝ) (991997477677/1000000000000 : ℝ) (495998738837/500000000000 : ℝ) (991997477677/1000000000000 : ℝ) (495998738837/500000000000 : ℝ) (991997477677/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4221/32768 : ℝ)) 5 (495998738837/500000000000 : ℝ) (991997477677/1000000000000 : ℝ) (495998738837/500000000000 : ℝ) (991997477677/1000000000000 : ℝ) (495998738837/500000000000 : ℝ) (991997477677/1000000000000 : ℝ) (495998738837/500000000000 : ℝ) (991997477677/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4221/32768 : ℝ)) 6 (495998738837/500000000000 : ℝ) (991997477677/1000000000000 : ℝ) (495998738837/500000000000 : ℝ) (991997477677/1000000000000 : ℝ) (495998738837/500000000000 : ℝ) (991997477677/1000000000000 : ℝ) (495998738837/500000000000 : ℝ) (991997477677/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4221/32768 : ℝ)) 7 (495998738837/500000000000 : ℝ) (991997477677/1000000000000 : ℝ) (495998738837/500000000000 : ℝ) (991997477677/1000000000000 : ℝ) (495998738837/500000000000 : ℝ) (991997477677/1000000000000 : ℝ) (495998738837/500000000000 : ℝ) (991997477677/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4221/32768 : ℝ))) (2225233757/12500000000 : ℝ) (89009350283/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4221/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (2225233757/12500000000 : ℝ) (89009350283/500000000000 : ℝ) (14725233757/25000000000 : ℝ) (589009350283/1000000000000 : ℝ) (421922623901/1000000000000 : ℝ) (421922623909/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4221/32768 : ℝ))) 1 (14725233757/25000000000 : ℝ) (589009350283/1000000000000 : ℝ) (421922623901/1000000000000 : ℝ) (421922623909/1000000000000 : ℝ) (50546598709/100000000000 : ℝ) (63183248387/125000000000 : ℝ) (24925708143/50000000000 : ℝ) (498514162867/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4221/32768 : ℝ))) 2 (50546598709/100000000000 : ℝ) (63183248387/125000000000 : ℝ) (24925708143/50000000000 : ℝ) (498514162867/1000000000000 : ℝ) (20079602999/40000000000 : ℝ) (250995037491/500000000000 : ℝ) (501978040763/1000000000000 : ℝ) (50197804077/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4221/32768 : ℝ))) 3 (20079602999/40000000000 : ℝ) (250995037491/500000000000 : ℝ) (501978040763/1000000000000 : ℝ) (50197804077/100000000000 : ℝ) (501984057869/1000000000000 : ℝ) (125496014469/250000000000 : ℝ) (62748007229/125000000000 : ℝ) (6274800723/12500000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4221/32768 : ℝ))) 4 (501984057869/1000000000000 : ℝ) (125496014469/250000000000 : ℝ) (62748007229/125000000000 : ℝ) (6274800723/12500000000 : ℝ) (10039681157/20000000000 : ℝ) (250992028929/500000000000 : ℝ) (10039681157/20000000000 : ℝ) (250992028929/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4221/32768 : ℝ))) 5 (10039681157/20000000000 : ℝ) (250992028929/500000000000 : ℝ) (10039681157/20000000000 : ℝ) (250992028929/500000000000 : ℝ) (10039681157/20000000000 : ℝ) (250992028929/500000000000 : ℝ) (10039681157/20000000000 : ℝ) (250992028929/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4221/32768 : ℝ))) 6 (10039681157/20000000000 : ℝ) (250992028929/500000000000 : ℝ) (10039681157/20000000000 : ℝ) (250992028929/500000000000 : ℝ) (10039681157/20000000000 : ℝ) (250992028929/500000000000 : ℝ) (10039681157/20000000000 : ℝ) (250992028929/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4221/32768 : ℝ))) 7 (10039681157/20000000000 : ℝ) (250992028929/500000000000 : ℝ) (10039681157/20000000000 : ℝ) (250992028929/500000000000 : ℝ) (10039681157/20000000000 : ℝ) (250992028929/500000000000 : ℝ) (10039681157/20000000000 : ℝ) (250992028929/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4221/32768 : ℝ)) hmem 8 (495998738837/500000000000 : ℝ) (991997477677/1000000000000 : ℝ) (495998738837/500000000000 : ℝ) (991997477677/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4221/32768 : ℝ))) hcmem 8 (10039681157/20000000000 : ℝ) (250992028929/500000000000 : ℝ) (10039681157/20000000000 : ℝ) (250992028929/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4221/32768 : ℝ)) (495998738837/500000000000 : ℝ) (991997477677/1000000000000 : ℝ) (10039681157/20000000000 : ℝ) (250992028929/500000000000 : ℝ) (794875724913/1000000000000 : ℝ) (794875724929/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1335_exp_lower
  have heNumeric : (1027452397861/500000000000 : ℝ)/4 ≤ Real.exp (-42628149911081/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027452397861/500000000000 : ℝ)/4 ≤ Real.exp ((33767/262144 : ℝ)-(794875724929/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33767/262144 : ℝ) (4221/32768 : ℝ) (794875724929/1000000000000 : ℝ) (1027452397861/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1336; no trusted numerical premise.
theorem cover8_leaf1336_exp_radius : (997989235052468987/1000000000000000000 : ℝ) ≤ Real.exp ((-33769/2097152 : ℝ)/8) ∧ Real.exp ((-33769/2097152 : ℝ)/8) ≤ (249497308763117247/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33769/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1336_exp_lower : (92011363303456091/100000000000000000 : ℝ) ≤ Real.exp ((-5328518553491/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328518553491/8000000000000 : ℝ)/8) ≤ (920113633034560911/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328518553491/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1336_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054904843343/1000000000000 : ℝ) ≤ 4*Real.exp (4221/32768 : ℝ)*Real.exp (-mu (radius 8 (33769/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054904843343/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33769/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1336_exp_radius
  have hrNumeric : (123003329401/125000000000 : ℝ) ≤ Real.exp (-33769/2097152 : ℝ) ∧ Real.exp (-33769/2097152 : ℝ) ≤ (984026635209/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (123003329401/125000000000 : ℝ) ≤ (radius 8 (33769/262144 : ℝ)) ∧ (radius 8 (33769/262144 : ℝ)) ≤ (984026635209/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33769/262144 : ℝ)) (123003329401/125000000000 : ℝ) (984026635209/1000000000000 : ℝ) (178021294229/1000000000000 : ℝ) (44505323559/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33769/262144 : ℝ)) (123003329401/125000000000 : ℝ) (984026635209/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33769/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (123003329401/125000000000 : ℝ) (984026635209/1000000000000 : ℝ) (248003329401/250000000000 : ℝ) (198402663521/200000000000 : ℝ) (24799529169/25000000000 : ℝ) (495990583381/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33769/262144 : ℝ)) 1 (248003329401/250000000000 : ℝ) (198402663521/200000000000 : ℝ) (24799529169/25000000000 : ℝ) (495990583381/500000000000 : ℝ) (495998621091/500000000000 : ℝ) (123999655273/125000000000 : ℝ) (991997242051/1000000000000 : ℝ) (495998621027/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33769/262144 : ℝ)) 2 (495998621091/500000000000 : ℝ) (123999655273/125000000000 : ℝ) (991997242051/1000000000000 : ℝ) (495998621027/500000000000 : ℝ) (247999310529/250000000000 : ℝ) (991997242119/1000000000000 : ℝ) (247999310529/250000000000 : ℝ) (991997242119/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33769/262144 : ℝ)) 3 (247999310529/250000000000 : ℝ) (991997242119/1000000000000 : ℝ) (247999310529/250000000000 : ℝ) (991997242119/1000000000000 : ℝ) (247999310529/250000000000 : ℝ) (991997242119/1000000000000 : ℝ) (247999310529/250000000000 : ℝ) (991997242119/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33769/262144 : ℝ)) 4 (247999310529/250000000000 : ℝ) (991997242119/1000000000000 : ℝ) (247999310529/250000000000 : ℝ) (991997242119/1000000000000 : ℝ) (247999310529/250000000000 : ℝ) (991997242119/1000000000000 : ℝ) (247999310529/250000000000 : ℝ) (991997242119/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33769/262144 : ℝ)) 5 (247999310529/250000000000 : ℝ) (991997242119/1000000000000 : ℝ) (247999310529/250000000000 : ℝ) (991997242119/1000000000000 : ℝ) (247999310529/250000000000 : ℝ) (991997242119/1000000000000 : ℝ) (247999310529/250000000000 : ℝ) (991997242119/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33769/262144 : ℝ)) 6 (247999310529/250000000000 : ℝ) (991997242119/1000000000000 : ℝ) (247999310529/250000000000 : ℝ) (991997242119/1000000000000 : ℝ) (247999310529/250000000000 : ℝ) (991997242119/1000000000000 : ℝ) (247999310529/250000000000 : ℝ) (991997242119/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33769/262144 : ℝ)) 7 (247999310529/250000000000 : ℝ) (991997242119/1000000000000 : ℝ) (247999310529/250000000000 : ℝ) (991997242119/1000000000000 : ℝ) (247999310529/250000000000 : ℝ) (991997242119/1000000000000 : ℝ) (247999310529/250000000000 : ℝ) (991997242119/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33769/262144 : ℝ))) (178021294229/1000000000000 : ℝ) (44505323559/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33769/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (178021294229/1000000000000 : ℝ) (44505323559/250000000000 : ℝ) (294505323557/500000000000 : ℝ) (294505323559/500000000000 : ℝ) (421925697521/1000000000000 : ℝ) (42192569753/100000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33769/262144 : ℝ))) 1 (294505323557/500000000000 : ℝ) (294505323559/500000000000 : ℝ) (421925697521/1000000000000 : ℝ) (42192569753/100000000000 : ℝ) (505468172317/1000000000000 : ℝ) (126367043081/250000000000 : ℝ) (6231456593/12500000000 : ℝ) (62314565931/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33769/262144 : ℝ))) 2 (505468172317/1000000000000 : ℝ) (126367043081/250000000000 : ℝ) (6231456593/12500000000 : ℝ) (62314565931/125000000000 : ℝ) (250996174939/500000000000 : ℝ) (250996174943/500000000000 : ℝ) (250990158171/500000000000 : ℝ) (10039606327/20000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33769/262144 : ℝ))) 3 (250996174939/500000000000 : ℝ) (250996174943/500000000000 : ℝ) (250990158171/500000000000 : ℝ) (10039606327/20000000000 : ℝ) (50198633311/100000000000 : ℝ) (250993166559/500000000000 : ℝ) (501986333073/1000000000000 : ℝ) (250993166541/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33769/262144 : ℝ))) 4 (50198633311/100000000000 : ℝ) (250993166559/500000000000 : ℝ) (501986333073/1000000000000 : ℝ) (250993166541/500000000000 : ℝ) (501986333091/1000000000000 : ℝ) (5019863331/10000000000 : ℝ) (501986333091/1000000000000 : ℝ) (5019863331/10000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33769/262144 : ℝ))) 5 (501986333091/1000000000000 : ℝ) (5019863331/10000000000 : ℝ) (501986333091/1000000000000 : ℝ) (5019863331/10000000000 : ℝ) (501986333091/1000000000000 : ℝ) (5019863331/10000000000 : ℝ) (501986333091/1000000000000 : ℝ) (5019863331/10000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33769/262144 : ℝ))) 6 (501986333091/1000000000000 : ℝ) (5019863331/10000000000 : ℝ) (501986333091/1000000000000 : ℝ) (5019863331/10000000000 : ℝ) (501986333091/1000000000000 : ℝ) (5019863331/10000000000 : ℝ) (501986333091/1000000000000 : ℝ) (5019863331/10000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33769/262144 : ℝ))) 7 (501986333091/1000000000000 : ℝ) (5019863331/10000000000 : ℝ) (501986333091/1000000000000 : ℝ) (5019863331/10000000000 : ℝ) (501986333091/1000000000000 : ℝ) (5019863331/10000000000 : ℝ) (501986333091/1000000000000 : ℝ) (5019863331/10000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33769/262144 : ℝ)) hmem 8 (247999310529/250000000000 : ℝ) (991997242119/1000000000000 : ℝ) (247999310529/250000000000 : ℝ) (991997242119/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33769/262144 : ℝ))) hcmem 8 (501986333091/1000000000000 : ℝ) (5019863331/10000000000 : ℝ) (501986333091/1000000000000 : ℝ) (5019863331/10000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33769/262144 : ℝ)) (247999310529/250000000000 : ℝ) (991997242119/1000000000000 : ℝ) (501986333091/1000000000000 : ℝ) (5019863331/10000000000 : ℝ) (158975903287/200000000000 : ℝ) (198719879113/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1336_exp_lower
  have heNumeric : (2054904843343/1000000000000 : ℝ)/4 ≤ Real.exp (-5328518553491/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054904843343/1000000000000 : ℝ)/4 ≤ Real.exp ((4221/32768 : ℝ)-(198719879113/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4221/32768 : ℝ) (33769/262144 : ℝ) (198719879113/250000000000 : ℝ) (2054904843343/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1337; no trusted numerical premise.
theorem cover8_leaf1337_exp_radius : (498994587783838457/500000000000000000 : ℝ) ≤ Real.exp ((-16885/1048576 : ℝ)/8) ∧ Real.exp ((-16885/1048576 : ℝ)/8) ≤ (199597835113535383/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16885/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1337_exp_lower : (46005681785364577/50000000000000000 : ℝ) ≤ Real.exp ((-42628146940679/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628146940679/64000000000000 : ℝ)/8) ≤ (920113635707291541/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628146940679/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1337_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410980978219/200000000000 : ℝ) ≤ 4*Real.exp (33769/262144 : ℝ)*Real.exp (-mu (radius 8 (16885/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (410980978219/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16885/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1337_exp_radius
  have hrNumeric : (984026165987/1000000000000 : ℝ) ≤ Real.exp (-16885/1048576 : ℝ) ∧ Real.exp (-16885/1048576 : ℝ) ≤ (246006541497/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984026165987/1000000000000 : ℝ) ≤ (radius 8 (16885/131072 : ℝ)) ∧ (radius 8 (16885/131072 : ℝ)) ≤ (246006541497/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16885/131072 : ℝ)) (984026165987/1000000000000 : ℝ) (246006541497/250000000000 : ℝ) (89011943933/500000000000 : ℝ) (173851453/976562500 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16885/131072 : ℝ)) (984026165987/1000000000000 : ℝ) (246006541497/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16885/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984026165987/1000000000000 : ℝ) (246006541497/250000000000 : ℝ) (992013082993/1000000000000 : ℝ) (496006541497/500000000000 : ℝ) (991980930253/1000000000000 : ℝ) (198396186051/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16885/131072 : ℝ)) 1 (992013082993/1000000000000 : ℝ) (496006541497/500000000000 : ℝ) (991980930253/1000000000000 : ℝ) (198396186051/200000000000 : ℝ) (991997006623/1000000000000 : ℝ) (7935976053/8000000000 : ℝ) (247999251623/250000000000 : ℝ) (198399401299/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16885/131072 : ℝ)) 2 (991997006623/1000000000000 : ℝ) (7935976053/8000000000 : ℝ) (247999251623/250000000000 : ℝ) (198399401299/200000000000 : ℝ) (991997006557/1000000000000 : ℝ) (6199981291/6250000000 : ℝ) (991997006557/1000000000000 : ℝ) (6199981291/6250000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16885/131072 : ℝ)) 3 (991997006557/1000000000000 : ℝ) (6199981291/6250000000 : ℝ) (991997006557/1000000000000 : ℝ) (6199981291/6250000000 : ℝ) (991997006557/1000000000000 : ℝ) (6199981291/6250000000 : ℝ) (991997006557/1000000000000 : ℝ) (6199981291/6250000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16885/131072 : ℝ)) 4 (991997006557/1000000000000 : ℝ) (6199981291/6250000000 : ℝ) (991997006557/1000000000000 : ℝ) (6199981291/6250000000 : ℝ) (991997006557/1000000000000 : ℝ) (6199981291/6250000000 : ℝ) (991997006557/1000000000000 : ℝ) (6199981291/6250000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16885/131072 : ℝ)) 5 (991997006557/1000000000000 : ℝ) (6199981291/6250000000 : ℝ) (991997006557/1000000000000 : ℝ) (6199981291/6250000000 : ℝ) (991997006557/1000000000000 : ℝ) (6199981291/6250000000 : ℝ) (991997006557/1000000000000 : ℝ) (6199981291/6250000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16885/131072 : ℝ)) 6 (991997006557/1000000000000 : ℝ) (6199981291/6250000000 : ℝ) (991997006557/1000000000000 : ℝ) (6199981291/6250000000 : ℝ) (991997006557/1000000000000 : ℝ) (6199981291/6250000000 : ℝ) (991997006557/1000000000000 : ℝ) (6199981291/6250000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16885/131072 : ℝ)) 7 (991997006557/1000000000000 : ℝ) (6199981291/6250000000 : ℝ) (991997006557/1000000000000 : ℝ) (6199981291/6250000000 : ℝ) (991997006557/1000000000000 : ℝ) (6199981291/6250000000 : ℝ) (991997006557/1000000000000 : ℝ) (6199981291/6250000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16885/131072 : ℝ))) (89011943933/500000000000 : ℝ) (173851453/976562500 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16885/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (89011943933/500000000000 : ℝ) (173851453/976562500 : ℝ) (589011943933/1000000000000 : ℝ) (1150413953/1953125000 : ℝ) (421928771081/1000000000000 : ℝ) (421928771089/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16885/131072 : ℝ))) 1 (589011943933/1000000000000 : ℝ) (1150413953/1953125000 : ℝ) (421928771081/1000000000000 : ℝ) (421928771089/1000000000000 : ℝ) (505470357507/1000000000000 : ℝ) (505470357513/1000000000000 : ℝ) (249259445987/500000000000 : ℝ) (498518891981/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16885/131072 : ℝ))) 2 (505470357507/1000000000000 : ℝ) (505470357513/1000000000000 : ℝ) (249259445987/500000000000 : ℝ) (498518891981/1000000000000 : ℝ) (25099731237/50000000000 : ℝ) (501994624747/1000000000000 : ℝ) (501982591879/1000000000000 : ℝ) (501982591887/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16885/131072 : ℝ))) 3 (25099731237/50000000000 : ℝ) (501994624747/1000000000000 : ℝ) (501982591879/1000000000000 : ℝ) (501982591887/1000000000000 : ℝ) (501988608309/1000000000000 : ℝ) (501988608317/1000000000000 : ℝ) (501988608273/1000000000000 : ℝ) (501988608281/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16885/131072 : ℝ))) 4 (501988608309/1000000000000 : ℝ) (501988608317/1000000000000 : ℝ) (501988608273/1000000000000 : ℝ) (501988608281/1000000000000 : ℝ) (501988608291/1000000000000 : ℝ) (501988608299/1000000000000 : ℝ) (50198860829/100000000000 : ℝ) (501988608299/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16885/131072 : ℝ))) 5 (501988608291/1000000000000 : ℝ) (501988608299/1000000000000 : ℝ) (50198860829/100000000000 : ℝ) (501988608299/1000000000000 : ℝ) (50198860829/100000000000 : ℝ) (501988608299/1000000000000 : ℝ) (50198860829/100000000000 : ℝ) (501988608299/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16885/131072 : ℝ))) 6 (50198860829/100000000000 : ℝ) (501988608299/1000000000000 : ℝ) (50198860829/100000000000 : ℝ) (501988608299/1000000000000 : ℝ) (50198860829/100000000000 : ℝ) (501988608299/1000000000000 : ℝ) (50198860829/100000000000 : ℝ) (501988608299/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16885/131072 : ℝ))) 7 (50198860829/100000000000 : ℝ) (501988608299/1000000000000 : ℝ) (50198860829/100000000000 : ℝ) (501988608299/1000000000000 : ℝ) (50198860829/100000000000 : ℝ) (501988608299/1000000000000 : ℝ) (50198860829/100000000000 : ℝ) (501988608299/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16885/131072 : ℝ)) hmem 8 (991997006557/1000000000000 : ℝ) (6199981291/6250000000 : ℝ) (991997006557/1000000000000 : ℝ) (6199981291/6250000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16885/131072 : ℝ))) hcmem 8 (50198860829/100000000000 : ℝ) (501988608299/1000000000000 : ℝ) (50198860829/100000000000 : ℝ) (501988608299/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16885/131072 : ℝ)) (991997006557/1000000000000 : ℝ) (6199981291/6250000000 : ℝ) (50198860829/100000000000 : ℝ) (501988608299/1000000000000 : ℝ) (794883307893/1000000000000 : ℝ) (794883307911/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1337_exp_lower
  have heNumeric : (410980978219/200000000000 : ℝ)/4 ≤ Real.exp (-42628146940679/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410980978219/200000000000 : ℝ)/4 ≤ Real.exp ((33769/262144 : ℝ)-(794883307911/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33769/262144 : ℝ) (16885/131072 : ℝ) (794883307911/1000000000000 : ℝ) (410980978219/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1338; no trusted numerical premise.
theorem cover8_leaf1338_exp_radius : (249497279020722097/250000000000000000 : ℝ) ≤ Real.exp ((-33771/2097152 : ℝ)/8) ∧ Real.exp ((-33771/2097152 : ℝ)/8) ≤ (997989116082888389/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33771/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1338_exp_lower : (920113638389683371/1000000000000000000 : ℝ) ≤ Real.exp ((-21314072724027/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314072724027/32000000000000 : ℝ)/8) ≤ (230028409597420843/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314072724027/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1338_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (102745246951/50000000000 : ℝ) ≤ 4*Real.exp (16885/131072 : ℝ)*Real.exp (-mu (radius 8 (33771/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (102745246951/50000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33771/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1338_exp_radius
  have hrNumeric : (984025696767/1000000000000 : ℝ) ≤ Real.exp (-33771/2097152 : ℝ) ∧ Real.exp (-33771/2097152 : ℝ) ≤ (1921925189/1953125000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984025696767/1000000000000 : ℝ) ≤ (radius 8 (33771/262144 : ℝ)) ∧ (radius 8 (33771/262144 : ℝ)) ≤ (1921925189/1953125000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33771/262144 : ℝ)) (984025696767/1000000000000 : ℝ) (1921925189/1953125000 : ℝ) (178026481457/1000000000000 : ℝ) (22253310183/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33771/262144 : ℝ)) (984025696767/1000000000000 : ℝ) (1921925189/1953125000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33771/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984025696767/1000000000000 : ℝ) (1921925189/1953125000 : ℝ) (992012848383/1000000000000 : ℝ) (3875050189/3906250000 : ℝ) (991980693747/1000000000000 : ℝ) (247995173437/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33771/262144 : ℝ)) 1 (992012848383/1000000000000 : ℝ) (3875050189/3906250000 : ℝ) (991980693747/1000000000000 : ℝ) (247995173437/250000000000 : ℝ) (198399354213/200000000000 : ℝ) (495998385533/500000000000 : ℝ) (495998385467/500000000000 : ℝ) (123999596367/125000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33771/262144 : ℝ)) 2 (198399354213/200000000000 : ℝ) (495998385533/500000000000 : ℝ) (495998385467/500000000000 : ℝ) (123999596367/125000000000 : ℝ) (991996770999/1000000000000 : ℝ) (991996771001/1000000000000 : ℝ) (991996770999/1000000000000 : ℝ) (991996771001/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33771/262144 : ℝ)) 3 (991996770999/1000000000000 : ℝ) (991996771001/1000000000000 : ℝ) (991996770999/1000000000000 : ℝ) (991996771001/1000000000000 : ℝ) (991996770999/1000000000000 : ℝ) (991996771001/1000000000000 : ℝ) (991996770999/1000000000000 : ℝ) (991996771001/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33771/262144 : ℝ)) 4 (991996770999/1000000000000 : ℝ) (991996771001/1000000000000 : ℝ) (991996770999/1000000000000 : ℝ) (991996771001/1000000000000 : ℝ) (991996770999/1000000000000 : ℝ) (991996771001/1000000000000 : ℝ) (991996770999/1000000000000 : ℝ) (991996771001/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33771/262144 : ℝ)) 5 (991996770999/1000000000000 : ℝ) (991996771001/1000000000000 : ℝ) (991996770999/1000000000000 : ℝ) (991996771001/1000000000000 : ℝ) (991996770999/1000000000000 : ℝ) (991996771001/1000000000000 : ℝ) (991996770999/1000000000000 : ℝ) (991996771001/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33771/262144 : ℝ)) 6 (991996770999/1000000000000 : ℝ) (991996771001/1000000000000 : ℝ) (991996770999/1000000000000 : ℝ) (991996771001/1000000000000 : ℝ) (991996770999/1000000000000 : ℝ) (991996771001/1000000000000 : ℝ) (991996770999/1000000000000 : ℝ) (991996771001/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33771/262144 : ℝ)) 7 (991996770999/1000000000000 : ℝ) (991996771001/1000000000000 : ℝ) (991996770999/1000000000000 : ℝ) (991996771001/1000000000000 : ℝ) (991996770999/1000000000000 : ℝ) (991996771001/1000000000000 : ℝ) (991996770999/1000000000000 : ℝ) (991996771001/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33771/262144 : ℝ))) (178026481457/1000000000000 : ℝ) (22253310183/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33771/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (178026481457/1000000000000 : ℝ) (22253310183/125000000000 : ℝ) (73626655091/125000000000 : ℝ) (147253310183/250000000000 : ℝ) (421931844563/1000000000000 : ℝ) (421931844573/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33771/262144 : ℝ))) 1 (73626655091/125000000000 : ℝ) (147253310183/250000000000 : ℝ) (421931844563/1000000000000 : ℝ) (421931844573/1000000000000 : ℝ) (101094508529/200000000000 : ℝ) (505472542653/1000000000000 : ℝ) (498521256449/1000000000000 : ℝ) (249260628229/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33771/262144 : ℝ))) 2 (101094508529/200000000000 : ℝ) (505472542653/1000000000000 : ℝ) (498521256449/1000000000000 : ℝ) (249260628229/500000000000 : ℝ) (501996899547/1000000000000 : ℝ) (125499224889/250000000000 : ℝ) (501984867361/1000000000000 : ℝ) (50198486737/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33771/262144 : ℝ))) 3 (501996899547/1000000000000 : ℝ) (125499224889/250000000000 : ℝ) (501984867361/1000000000000 : ℝ) (50198486737/100000000000 : ℝ) (250995441727/500000000000 : ℝ) (501990883463/1000000000000 : ℝ) (501990883417/1000000000000 : ℝ) (501990883427/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33771/262144 : ℝ))) 4 (250995441727/500000000000 : ℝ) (501990883463/1000000000000 : ℝ) (501990883417/1000000000000 : ℝ) (501990883427/1000000000000 : ℝ) (100398176687/200000000000 : ℝ) (100398176689/200000000000 : ℝ) (100398176687/200000000000 : ℝ) (100398176689/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33771/262144 : ℝ))) 5 (100398176687/200000000000 : ℝ) (100398176689/200000000000 : ℝ) (100398176687/200000000000 : ℝ) (100398176689/200000000000 : ℝ) (100398176687/200000000000 : ℝ) (100398176689/200000000000 : ℝ) (100398176687/200000000000 : ℝ) (100398176689/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33771/262144 : ℝ))) 6 (100398176687/200000000000 : ℝ) (100398176689/200000000000 : ℝ) (100398176687/200000000000 : ℝ) (100398176689/200000000000 : ℝ) (100398176687/200000000000 : ℝ) (100398176689/200000000000 : ℝ) (100398176687/200000000000 : ℝ) (100398176689/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33771/262144 : ℝ))) 7 (100398176687/200000000000 : ℝ) (100398176689/200000000000 : ℝ) (100398176687/200000000000 : ℝ) (100398176689/200000000000 : ℝ) (100398176687/200000000000 : ℝ) (100398176689/200000000000 : ℝ) (100398176687/200000000000 : ℝ) (100398176689/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33771/262144 : ℝ)) hmem 8 (991996770999/1000000000000 : ℝ) (991996771001/1000000000000 : ℝ) (991996770999/1000000000000 : ℝ) (991996771001/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33771/262144 : ℝ))) hcmem 8 (100398176687/200000000000 : ℝ) (100398176689/200000000000 : ℝ) (100398176687/200000000000 : ℝ) (100398176689/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33771/262144 : ℝ)) (991996770999/1000000000000 : ℝ) (991996771001/1000000000000 : ℝ) (100398176687/200000000000 : ℝ) (100398176689/200000000000 : ℝ) (198721774817/250000000000 : ℝ) (397443549643/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1338_exp_lower
  have heNumeric : (102745246951/50000000000 : ℝ)/4 ≤ Real.exp (-21314072724027/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (102745246951/50000000000 : ℝ)/4 ≤ Real.exp ((16885/131072 : ℝ)-(397443549643/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16885/131072 : ℝ) (33771/262144 : ℝ) (397443549643/500000000000 : ℝ) (102745246951/50000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1339; no trusted numerical premise.
theorem cover8_leaf1339_exp_radius : (997989056598103407/1000000000000000000 : ℝ) ≤ Real.exp ((-8443/524288 : ℝ)/8) ∧ Real.exp ((-8443/524288 : ℝ)/8) ≤ (62374316037381463/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8443/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1339_exp_lower : (920113641080471247/1000000000000000000 : ℝ) ≤ Real.exp ((-42628143950757/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628143950757/64000000000000 : ℝ)/8) ≤ (57507102567529453/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628143950757/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1339_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410980997419/200000000000 : ℝ) ≤ 4*Real.exp (33771/262144 : ℝ)*Real.exp (-mu (radius 8 (8443/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (410980997419/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8443/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1339_exp_radius
  have hrNumeric : (984025227547/1000000000000 : ℝ) ≤ Real.exp (-8443/524288 : ℝ) ∧ Real.exp (-8443/524288 : ℝ) ≤ (246006306887/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984025227547/1000000000000 : ℝ) ≤ (radius 8 (8443/65536 : ℝ)) ∧ (radius 8 (8443/65536 : ℝ)) ≤ (246006306887/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8443/65536 : ℝ)) (984025227547/1000000000000 : ℝ) (246006306887/250000000000 : ℝ) (17802907501/100000000000 : ℝ) (178029075017/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8443/65536 : ℝ)) (984025227547/1000000000000 : ℝ) (246006306887/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8443/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984025227547/1000000000000 : ℝ) (246006306887/250000000000 : ℝ) (992012613773/1000000000000 : ℝ) (496006306887/500000000000 : ℝ) (24799511431/25000000000 : ℝ) (991980457241/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8443/65536 : ℝ)) 1 (992012613773/1000000000000 : ℝ) (496006306887/500000000000 : ℝ) (24799511431/25000000000 : ℝ) (991980457241/1000000000000 : ℝ) (495998267753/500000000000 : ℝ) (247999133877/250000000000 : ℝ) (61999783461/62500000000 : ℝ) (495998267689/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8443/65536 : ℝ)) 2 (495998267753/500000000000 : ℝ) (247999133877/250000000000 : ℝ) (61999783461/62500000000 : ℝ) (495998267689/500000000000 : ℝ) (991996535441/1000000000000 : ℝ) (991996535443/1000000000000 : ℝ) (12399956693/12500000000 : ℝ) (991996535443/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8443/65536 : ℝ)) 3 (991996535441/1000000000000 : ℝ) (991996535443/1000000000000 : ℝ) (12399956693/12500000000 : ℝ) (991996535443/1000000000000 : ℝ) (12399956693/12500000000 : ℝ) (991996535443/1000000000000 : ℝ) (12399956693/12500000000 : ℝ) (991996535443/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8443/65536 : ℝ)) 4 (12399956693/12500000000 : ℝ) (991996535443/1000000000000 : ℝ) (12399956693/12500000000 : ℝ) (991996535443/1000000000000 : ℝ) (12399956693/12500000000 : ℝ) (991996535443/1000000000000 : ℝ) (12399956693/12500000000 : ℝ) (991996535443/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8443/65536 : ℝ)) 5 (12399956693/12500000000 : ℝ) (991996535443/1000000000000 : ℝ) (12399956693/12500000000 : ℝ) (991996535443/1000000000000 : ℝ) (12399956693/12500000000 : ℝ) (991996535443/1000000000000 : ℝ) (12399956693/12500000000 : ℝ) (991996535443/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8443/65536 : ℝ)) 6 (12399956693/12500000000 : ℝ) (991996535443/1000000000000 : ℝ) (12399956693/12500000000 : ℝ) (991996535443/1000000000000 : ℝ) (12399956693/12500000000 : ℝ) (991996535443/1000000000000 : ℝ) (12399956693/12500000000 : ℝ) (991996535443/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8443/65536 : ℝ)) 7 (12399956693/12500000000 : ℝ) (991996535443/1000000000000 : ℝ) (12399956693/12500000000 : ℝ) (991996535443/1000000000000 : ℝ) (12399956693/12500000000 : ℝ) (991996535443/1000000000000 : ℝ) (12399956693/12500000000 : ℝ) (991996535443/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8443/65536 : ℝ))) (17802907501/100000000000 : ℝ) (178029075017/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8443/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (17802907501/100000000000 : ℝ) (178029075017/1000000000000 : ℝ) (117802907501/200000000000 : ℝ) (589014537509/1000000000000 : ℝ) (421934917979/1000000000000 : ℝ) (105483729497/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8443/65536 : ℝ))) 1 (117802907501/200000000000 : ℝ) (589014537509/1000000000000 : ℝ) (421934917979/1000000000000 : ℝ) (105483729497/250000000000 : ℝ) (252737363871/500000000000 : ℝ) (505474727749/1000000000000 : ℝ) (3988188967/8000000000 : ℝ) (498523620883/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8443/65536 : ℝ))) 2 (252737363871/500000000000 : ℝ) (505474727749/1000000000000 : ℝ) (3988188967/8000000000 : ℝ) (498523620883/1000000000000 : ℝ) (125499793577/250000000000 : ℝ) (125499793579/250000000000 : ℝ) (250993571399/500000000000 : ℝ) (250993571403/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8443/65536 : ℝ))) 3 (125499793577/250000000000 : ℝ) (125499793579/250000000000 : ℝ) (250993571399/500000000000 : ℝ) (250993571403/500000000000 : ℝ) (501993158553/1000000000000 : ℝ) (501993158561/1000000000000 : ℝ) (125498289629/250000000000 : ℝ) (20079726341/40000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8443/65536 : ℝ))) 4 (501993158553/1000000000000 : ℝ) (501993158561/1000000000000 : ℝ) (125498289629/250000000000 : ℝ) (20079726341/40000000000 : ℝ) (250996579267/500000000000 : ℝ) (501993158543/1000000000000 : ℝ) (250996579267/500000000000 : ℝ) (501993158543/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8443/65536 : ℝ))) 5 (250996579267/500000000000 : ℝ) (501993158543/1000000000000 : ℝ) (250996579267/500000000000 : ℝ) (501993158543/1000000000000 : ℝ) (250996579267/500000000000 : ℝ) (501993158543/1000000000000 : ℝ) (250996579267/500000000000 : ℝ) (501993158543/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8443/65536 : ℝ))) 6 (250996579267/500000000000 : ℝ) (501993158543/1000000000000 : ℝ) (250996579267/500000000000 : ℝ) (501993158543/1000000000000 : ℝ) (250996579267/500000000000 : ℝ) (501993158543/1000000000000 : ℝ) (250996579267/500000000000 : ℝ) (501993158543/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8443/65536 : ℝ))) 7 (250996579267/500000000000 : ℝ) (501993158543/1000000000000 : ℝ) (250996579267/500000000000 : ℝ) (501993158543/1000000000000 : ℝ) (250996579267/500000000000 : ℝ) (501993158543/1000000000000 : ℝ) (250996579267/500000000000 : ℝ) (501993158543/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8443/65536 : ℝ)) hmem 8 (12399956693/12500000000 : ℝ) (991996535443/1000000000000 : ℝ) (12399956693/12500000000 : ℝ) (991996535443/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8443/65536 : ℝ))) hcmem 8 (250996579267/500000000000 : ℝ) (501993158543/1000000000000 : ℝ) (250996579267/500000000000 : ℝ) (501993158543/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8443/65536 : ℝ)) (12399956693/12500000000 : ℝ) (991996535443/1000000000000 : ℝ) (250996579267/500000000000 : ℝ) (501993158543/1000000000000 : ℝ) (79489089057/100000000000 : ℝ) (198722722647/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1339_exp_lower
  have heNumeric : (410980997419/200000000000 : ℝ)/4 ≤ Real.exp (-42628143950757/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410980997419/200000000000 : ℝ)/4 ≤ Real.exp ((33771/262144 : ℝ)-(198722722647/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33771/262144 : ℝ) (8443/65536 : ℝ) (198722722647/250000000000 : ℝ) (410980997419/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1340; no trusted numerical premise.
theorem cover8_leaf1340_exp_radius : (997988997113321971/1000000000000000000 : ℝ) ≤ Real.exp ((-33773/2097152 : ℝ)/8) ∧ Real.exp ((-33773/2097152 : ℝ)/8) ≤ (249497249278330493/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33773/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1340_exp_lower : (36804545751204609/40000000000000000 : ℝ) ≤ Real.exp ((-10657035612133/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657035612133/16000000000000 : ℝ)/8) ≤ (460056821890057613/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657035612133/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1340_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (32107891177/15625000000 : ℝ) ≤ 4*Real.exp (8443/65536 : ℝ)*Real.exp (-mu (radius 8 (33773/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (32107891177/15625000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33773/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1340_exp_radius
  have hrNumeric : (984024758327/1000000000000 : ℝ) ≤ Real.exp (-33773/2097152 : ℝ) ∧ Real.exp (-33773/2097152 : ℝ) ≤ (123003094791/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984024758327/1000000000000 : ℝ) ≤ (radius 8 (33773/262144 : ℝ)) ∧ (radius 8 (33773/262144 : ℝ)) ≤ (123003094791/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33773/262144 : ℝ)) (984024758327/1000000000000 : ℝ) (123003094791/125000000000 : ℝ) (44507917131/250000000000 : ℝ) (17803166853/100000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33773/262144 : ℝ)) (984024758327/1000000000000 : ℝ) (123003094791/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33773/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984024758327/1000000000000 : ℝ) (123003094791/125000000000 : ℝ) (992012379163/1000000000000 : ℝ) (248003094791/250000000000 : ℝ) (991980220733/1000000000000 : ℝ) (198396044147/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33773/262144 : ℝ)) 1 (992012379163/1000000000000 : ℝ) (248003094791/250000000000 : ℝ) (991980220733/1000000000000 : ℝ) (198396044147/200000000000 : ℝ) (247999074987/250000000000 : ℝ) (19839925999/20000000000 : ℝ) (991996299817/1000000000000 : ℝ) (49599814991/50000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33773/262144 : ℝ)) 2 (247999074987/250000000000 : ℝ) (19839925999/20000000000 : ℝ) (991996299817/1000000000000 : ℝ) (49599814991/50000000000 : ℝ) (495998149941/500000000000 : ℝ) (198399259977/200000000000 : ℝ) (495998149941/500000000000 : ℝ) (198399259977/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33773/262144 : ℝ)) 3 (495998149941/500000000000 : ℝ) (198399259977/200000000000 : ℝ) (495998149941/500000000000 : ℝ) (198399259977/200000000000 : ℝ) (495998149941/500000000000 : ℝ) (198399259977/200000000000 : ℝ) (495998149941/500000000000 : ℝ) (198399259977/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33773/262144 : ℝ)) 4 (495998149941/500000000000 : ℝ) (198399259977/200000000000 : ℝ) (495998149941/500000000000 : ℝ) (198399259977/200000000000 : ℝ) (495998149941/500000000000 : ℝ) (198399259977/200000000000 : ℝ) (495998149941/500000000000 : ℝ) (198399259977/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33773/262144 : ℝ)) 5 (495998149941/500000000000 : ℝ) (198399259977/200000000000 : ℝ) (495998149941/500000000000 : ℝ) (198399259977/200000000000 : ℝ) (495998149941/500000000000 : ℝ) (198399259977/200000000000 : ℝ) (495998149941/500000000000 : ℝ) (198399259977/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33773/262144 : ℝ)) 6 (495998149941/500000000000 : ℝ) (198399259977/200000000000 : ℝ) (495998149941/500000000000 : ℝ) (198399259977/200000000000 : ℝ) (495998149941/500000000000 : ℝ) (198399259977/200000000000 : ℝ) (495998149941/500000000000 : ℝ) (198399259977/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33773/262144 : ℝ)) 7 (495998149941/500000000000 : ℝ) (198399259977/200000000000 : ℝ) (495998149941/500000000000 : ℝ) (198399259977/200000000000 : ℝ) (495998149941/500000000000 : ℝ) (198399259977/200000000000 : ℝ) (495998149941/500000000000 : ℝ) (198399259977/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33773/262144 : ℝ))) (44507917131/250000000000 : ℝ) (17803166853/100000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33773/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44507917131/250000000000 : ℝ) (17803166853/100000000000 : ℝ) (294507917131/500000000000 : ℝ) (117803166853/200000000000 : ℝ) (16877519653/40000000000 : ℝ) (421937991333/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33773/262144 : ℝ))) 1 (294507917131/500000000000 : ℝ) (117803166853/200000000000 : ℝ) (16877519653/40000000000 : ℝ) (421937991333/1000000000000 : ℝ) (505476912793/1000000000000 : ℝ) (505476912799/1000000000000 : ℝ) (498525985247/1000000000000 : ℝ) (249262992627/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33773/262144 : ℝ))) 2 (505476912793/1000000000000 : ℝ) (505476912799/1000000000000 : ℝ) (498525985247/1000000000000 : ℝ) (249262992627/500000000000 : ℝ) (25100072451/50000000000 : ℝ) (502001449027/1000000000000 : ℝ) (100397883637/200000000000 : ℝ) (31374338637/62500000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33773/262144 : ℝ))) 3 (25100072451/50000000000 : ℝ) (502001449027/1000000000000 : ℝ) (100397883637/200000000000 : ℝ) (31374338637/62500000000 : ℝ) (250997716801/500000000000 : ℝ) (50199543361/100000000000 : ℝ) (250997716783/500000000000 : ℝ) (250997716787/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33773/262144 : ℝ))) 4 (250997716801/500000000000 : ℝ) (50199543361/100000000000 : ℝ) (250997716783/500000000000 : ℝ) (250997716787/500000000000 : ℝ) (31374714599/62500000000 : ℝ) (62749429199/125000000000 : ℝ) (501995433583/1000000000000 : ℝ) (62749429199/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33773/262144 : ℝ))) 5 (31374714599/62500000000 : ℝ) (62749429199/125000000000 : ℝ) (501995433583/1000000000000 : ℝ) (62749429199/125000000000 : ℝ) (501995433583/1000000000000 : ℝ) (62749429199/125000000000 : ℝ) (501995433583/1000000000000 : ℝ) (62749429199/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33773/262144 : ℝ))) 6 (501995433583/1000000000000 : ℝ) (62749429199/125000000000 : ℝ) (501995433583/1000000000000 : ℝ) (62749429199/125000000000 : ℝ) (501995433583/1000000000000 : ℝ) (62749429199/125000000000 : ℝ) (501995433583/1000000000000 : ℝ) (62749429199/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33773/262144 : ℝ))) 7 (501995433583/1000000000000 : ℝ) (62749429199/125000000000 : ℝ) (501995433583/1000000000000 : ℝ) (62749429199/125000000000 : ℝ) (501995433583/1000000000000 : ℝ) (62749429199/125000000000 : ℝ) (501995433583/1000000000000 : ℝ) (62749429199/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33773/262144 : ℝ)) hmem 8 (495998149941/500000000000 : ℝ) (198399259977/200000000000 : ℝ) (495998149941/500000000000 : ℝ) (198399259977/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33773/262144 : ℝ))) hcmem 8 (501995433583/1000000000000 : ℝ) (62749429199/125000000000 : ℝ) (501995433583/1000000000000 : ℝ) (62749429199/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33773/262144 : ℝ)) (495998149941/500000000000 : ℝ) (198399259977/200000000000 : ℝ) (501995433583/1000000000000 : ℝ) (62749429199/125000000000 : ℝ) (198723670449/250000000000 : ℝ) (794894681813/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1340_exp_lower
  have heNumeric : (32107891177/15625000000 : ℝ)/4 ≤ Real.exp (-10657035612133/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (32107891177/15625000000 : ℝ)/4 ≤ Real.exp ((8443/65536 : ℝ)-(794894681813/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8443/65536 : ℝ) (33773/262144 : ℝ) (794894681813/1000000000000 : ℝ) (32107891177/15625000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1341; no trusted numerical premise.
theorem cover8_leaf1341_exp_radius : (997988937628544081/1000000000000000000 : ℝ) ≤ Real.exp ((-16887/1048576 : ℝ)/8) ∧ Real.exp ((-16887/1048576 : ℝ)/8) ≤ (498994468814272041/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16887/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1341_exp_lower : (460056823244480173/500000000000000000 : ℝ) ≤ Real.exp ((-42628140941187/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628140941187/64000000000000 : ℝ)/8) ≤ (920113646488960347/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628140941187/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1341_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027452541863/500000000000 : ℝ) ≤ 4*Real.exp (33773/262144 : ℝ)*Real.exp (-mu (radius 8 (16887/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (1027452541863/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16887/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1341_exp_radius
  have hrNumeric : (246006072277/250000000000 : ℝ) ≤ Real.exp (-16887/1048576 : ℝ) ∧ Real.exp (-16887/1048576 : ℝ) ≤ (984024289109/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246006072277/250000000000 : ℝ) ≤ (radius 8 (16887/131072 : ℝ)) ∧ (radius 8 (16887/131072 : ℝ)) ≤ (984024289109/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16887/131072 : ℝ)) (246006072277/250000000000 : ℝ) (984024289109/1000000000000 : ℝ) (178034261993/1000000000000 : ℝ) (178034261999/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16887/131072 : ℝ)) (246006072277/250000000000 : ℝ) (984024289109/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16887/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246006072277/250000000000 : ℝ) (984024289109/1000000000000 : ℝ) (496006072277/500000000000 : ℝ) (198402428911/200000000000 : ℝ) (991979984227/1000000000000 : ℝ) (991979984229/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16887/131072 : ℝ)) 1 (496006072277/500000000000 : ℝ) (198402428911/200000000000 : ℝ) (991979984227/1000000000000 : ℝ) (991979984229/1000000000000 : ℝ) (99199606439/100000000000 : ℝ) (123999508049/125000000000 : ℝ) (49599803213/50000000000 : ℝ) (495998032131/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16887/131072 : ℝ)) 2 (99199606439/100000000000 : ℝ) (123999508049/125000000000 : ℝ) (49599803213/50000000000 : ℝ) (495998032131/500000000000 : ℝ) (39679842573/40000000000 : ℝ) (991996064327/1000000000000 : ℝ) (247999016081/250000000000 : ℝ) (991996064327/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16887/131072 : ℝ)) 3 (39679842573/40000000000 : ℝ) (991996064327/1000000000000 : ℝ) (247999016081/250000000000 : ℝ) (991996064327/1000000000000 : ℝ) (247999016081/250000000000 : ℝ) (991996064327/1000000000000 : ℝ) (247999016081/250000000000 : ℝ) (991996064327/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16887/131072 : ℝ)) 4 (247999016081/250000000000 : ℝ) (991996064327/1000000000000 : ℝ) (247999016081/250000000000 : ℝ) (991996064327/1000000000000 : ℝ) (247999016081/250000000000 : ℝ) (991996064327/1000000000000 : ℝ) (247999016081/250000000000 : ℝ) (991996064327/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16887/131072 : ℝ)) 5 (247999016081/250000000000 : ℝ) (991996064327/1000000000000 : ℝ) (247999016081/250000000000 : ℝ) (991996064327/1000000000000 : ℝ) (247999016081/250000000000 : ℝ) (991996064327/1000000000000 : ℝ) (247999016081/250000000000 : ℝ) (991996064327/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16887/131072 : ℝ)) 6 (247999016081/250000000000 : ℝ) (991996064327/1000000000000 : ℝ) (247999016081/250000000000 : ℝ) (991996064327/1000000000000 : ℝ) (247999016081/250000000000 : ℝ) (991996064327/1000000000000 : ℝ) (247999016081/250000000000 : ℝ) (991996064327/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16887/131072 : ℝ)) 7 (247999016081/250000000000 : ℝ) (991996064327/1000000000000 : ℝ) (247999016081/250000000000 : ℝ) (991996064327/1000000000000 : ℝ) (247999016081/250000000000 : ℝ) (991996064327/1000000000000 : ℝ) (247999016081/250000000000 : ℝ) (991996064327/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16887/131072 : ℝ))) (178034261993/1000000000000 : ℝ) (178034261999/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16887/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (178034261993/1000000000000 : ℝ) (178034261999/1000000000000 : ℝ) (147254282749/250000000000 : ℝ) (589017131/1000000000 : ℝ) (105485266149/250000000000 : ℝ) (105485266151/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16887/131072 : ℝ))) 1 (147254282749/250000000000 : ℝ) (589017131/1000000000 : ℝ) (105485266149/250000000000 : ℝ) (105485266151/250000000000 : ℝ) (126369774449/250000000000 : ℝ) (252739548901/500000000000 : ℝ) (249264174781/500000000000 : ℝ) (49852834957/100000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16887/131072 : ℝ))) 2 (126369774449/250000000000 : ℝ) (252739548901/500000000000 : ℝ) (249264174781/500000000000 : ℝ) (49852834957/100000000000 : ℝ) (502003723679/1000000000000 : ℝ) (251001861843/500000000000 : ℝ) (501991693519/1000000000000 : ℝ) (501991693527/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16887/131072 : ℝ))) 3 (502003723679/1000000000000 : ℝ) (251001861843/500000000000 : ℝ) (501991693519/1000000000000 : ℝ) (501991693527/1000000000000 : ℝ) (501997708599/1000000000000 : ℝ) (501997708607/1000000000000 : ℝ) (250998854281/500000000000 : ℝ) (501997708571/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16887/131072 : ℝ))) 4 (501997708599/1000000000000 : ℝ) (501997708607/1000000000000 : ℝ) (250998854281/500000000000 : ℝ) (501997708571/1000000000000 : ℝ) (25099885429/50000000000 : ℝ) (501997708589/1000000000000 : ℝ) (25099885429/50000000000 : ℝ) (501997708589/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16887/131072 : ℝ))) 5 (25099885429/50000000000 : ℝ) (501997708589/1000000000000 : ℝ) (25099885429/50000000000 : ℝ) (501997708589/1000000000000 : ℝ) (25099885429/50000000000 : ℝ) (501997708589/1000000000000 : ℝ) (25099885429/50000000000 : ℝ) (501997708589/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16887/131072 : ℝ))) 6 (25099885429/50000000000 : ℝ) (501997708589/1000000000000 : ℝ) (25099885429/50000000000 : ℝ) (501997708589/1000000000000 : ℝ) (25099885429/50000000000 : ℝ) (501997708589/1000000000000 : ℝ) (25099885429/50000000000 : ℝ) (501997708589/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16887/131072 : ℝ))) 7 (25099885429/50000000000 : ℝ) (501997708589/1000000000000 : ℝ) (25099885429/50000000000 : ℝ) (501997708589/1000000000000 : ℝ) (25099885429/50000000000 : ℝ) (501997708589/1000000000000 : ℝ) (25099885429/50000000000 : ℝ) (501997708589/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16887/131072 : ℝ)) hmem 8 (247999016081/250000000000 : ℝ) (991996064327/1000000000000 : ℝ) (247999016081/250000000000 : ℝ) (991996064327/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16887/131072 : ℝ))) hcmem 8 (25099885429/50000000000 : ℝ) (501997708589/1000000000000 : ℝ) (25099885429/50000000000 : ℝ) (501997708589/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16887/131072 : ℝ)) (247999016081/250000000000 : ℝ) (991996064327/1000000000000 : ℝ) (25099885429/50000000000 : ℝ) (501997708589/1000000000000 : ℝ) (39744923647/50000000000 : ℝ) (397449236479/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1341_exp_lower
  have heNumeric : (1027452541863/500000000000 : ℝ)/4 ≤ Real.exp (-42628140941187/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027452541863/500000000000 : ℝ)/4 ≤ Real.exp ((33773/262144 : ℝ)-(397449236479/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33773/262144 : ℝ) (16887/131072 : ℝ) (397449236479/500000000000 : ℝ) (1027452541863/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1342; no trusted numerical premise.
theorem cover8_leaf1342_exp_radius : (997988878143769737/1000000000000000000 : ℝ) ≤ Real.exp ((-33775/2097152 : ℝ)/8) ∧ Real.exp ((-33775/2097152 : ℝ)/8) ≤ (498994439071884869/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33775/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1342_exp_lower : (57507103075394783/62500000000000000 : ℝ) ≤ Real.exp ((-21314069714553/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314069714553/32000000000000 : ℝ)/8) ≤ (920113649206316529/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314069714553/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1342_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513726283069/250000000000 : ℝ) ≤ 4*Real.exp (16887/131072 : ℝ)*Real.exp (-mu (radius 8 (33775/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (513726283069/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33775/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1342_exp_radius
  have hrNumeric : (984023819889/1000000000000 : ℝ) ≤ Real.exp (-33775/2097152 : ℝ) ∧ Real.exp (-33775/2097152 : ℝ) ≤ (98402381989/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984023819889/1000000000000 : ℝ) ≤ (radius 8 (33775/262144 : ℝ)) ∧ (radius 8 (33775/262144 : ℝ)) ≤ (98402381989/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33775/262144 : ℝ)) (984023819889/1000000000000 : ℝ) (98402381989/100000000000 : ℝ) (178036855423/1000000000000 : ℝ) (17803685543/100000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33775/262144 : ℝ)) (984023819889/1000000000000 : ℝ) (98402381989/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33775/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984023819889/1000000000000 : ℝ) (98402381989/100000000000 : ℝ) (124001488743/125000000000 : ℝ) (198402381989/200000000000 : ℝ) (991979747721/1000000000000 : ℝ) (495989873861/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33775/262144 : ℝ)) 1 (124001488743/125000000000 : ℝ) (198402381989/200000000000 : ℝ) (991979747721/1000000000000 : ℝ) (495989873861/500000000000 : ℝ) (30999869651/31250000000 : ℝ) (495997914417/500000000000 : ℝ) (495997914351/500000000000 : ℝ) (30999869647/31250000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33775/262144 : ℝ)) 2 (30999869651/31250000000 : ℝ) (495997914417/500000000000 : ℝ) (495997914351/500000000000 : ℝ) (30999869647/31250000000 : ℝ) (991995828767/1000000000000 : ℝ) (991995828769/1000000000000 : ℝ) (495997914383/500000000000 : ℝ) (991995828769/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33775/262144 : ℝ)) 3 (991995828767/1000000000000 : ℝ) (991995828769/1000000000000 : ℝ) (495997914383/500000000000 : ℝ) (991995828769/1000000000000 : ℝ) (495997914383/500000000000 : ℝ) (991995828769/1000000000000 : ℝ) (495997914383/500000000000 : ℝ) (991995828769/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33775/262144 : ℝ)) 4 (495997914383/500000000000 : ℝ) (991995828769/1000000000000 : ℝ) (495997914383/500000000000 : ℝ) (991995828769/1000000000000 : ℝ) (495997914383/500000000000 : ℝ) (991995828769/1000000000000 : ℝ) (495997914383/500000000000 : ℝ) (991995828769/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33775/262144 : ℝ)) 5 (495997914383/500000000000 : ℝ) (991995828769/1000000000000 : ℝ) (495997914383/500000000000 : ℝ) (991995828769/1000000000000 : ℝ) (495997914383/500000000000 : ℝ) (991995828769/1000000000000 : ℝ) (495997914383/500000000000 : ℝ) (991995828769/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33775/262144 : ℝ)) 6 (495997914383/500000000000 : ℝ) (991995828769/1000000000000 : ℝ) (495997914383/500000000000 : ℝ) (991995828769/1000000000000 : ℝ) (495997914383/500000000000 : ℝ) (991995828769/1000000000000 : ℝ) (495997914383/500000000000 : ℝ) (991995828769/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33775/262144 : ℝ)) 7 (495997914383/500000000000 : ℝ) (991995828769/1000000000000 : ℝ) (495997914383/500000000000 : ℝ) (991995828769/1000000000000 : ℝ) (495997914383/500000000000 : ℝ) (991995828769/1000000000000 : ℝ) (495997914383/500000000000 : ℝ) (991995828769/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33775/262144 : ℝ))) (178036855423/1000000000000 : ℝ) (17803685543/100000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33775/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (178036855423/1000000000000 : ℝ) (17803685543/100000000000 : ℝ) (589018427711/1000000000000 : ℝ) (117803685543/200000000000 : ℝ) (421944137799/1000000000000 : ℝ) (26371508613/62500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33775/262144 : ℝ))) 1 (589018427711/1000000000000 : ℝ) (117803685543/200000000000 : ℝ) (421944137799/1000000000000 : ℝ) (26371508613/62500000000 : ℝ) (101096256551/200000000000 : ℝ) (252740641381/500000000000 : ℝ) (249265356913/500000000000 : ℝ) (249265356917/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33775/262144 : ℝ))) 2 (101096256551/200000000000 : ℝ) (252740641381/500000000000 : ℝ) (249265356913/500000000000 : ℝ) (249265356917/500000000000 : ℝ) (50200599829/100000000000 : ℝ) (251002999149/500000000000 : ℝ) (100398793761/200000000000 : ℝ) (250996984407/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33775/262144 : ℝ))) 3 (50200599829/100000000000 : ℝ) (251002999149/500000000000 : ℝ) (100398793761/200000000000 : ℝ) (250996984407/500000000000 : ℝ) (501999983547/1000000000000 : ℝ) (125499995889/250000000000 : ℝ) (501999983511/1000000000000 : ℝ) (3137499897/6250000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33775/262144 : ℝ))) 4 (501999983547/1000000000000 : ℝ) (125499995889/250000000000 : ℝ) (501999983511/1000000000000 : ℝ) (3137499897/6250000000 : ℝ) (501999983529/1000000000000 : ℝ) (250999991769/500000000000 : ℝ) (62749997941/125000000000 : ℝ) (250999991769/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33775/262144 : ℝ))) 5 (501999983529/1000000000000 : ℝ) (250999991769/500000000000 : ℝ) (62749997941/125000000000 : ℝ) (250999991769/500000000000 : ℝ) (62749997941/125000000000 : ℝ) (250999991769/500000000000 : ℝ) (62749997941/125000000000 : ℝ) (250999991769/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33775/262144 : ℝ))) 6 (62749997941/125000000000 : ℝ) (250999991769/500000000000 : ℝ) (62749997941/125000000000 : ℝ) (250999991769/500000000000 : ℝ) (62749997941/125000000000 : ℝ) (250999991769/500000000000 : ℝ) (62749997941/125000000000 : ℝ) (250999991769/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33775/262144 : ℝ))) 7 (62749997941/125000000000 : ℝ) (250999991769/500000000000 : ℝ) (62749997941/125000000000 : ℝ) (250999991769/500000000000 : ℝ) (62749997941/125000000000 : ℝ) (250999991769/500000000000 : ℝ) (62749997941/125000000000 : ℝ) (250999991769/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33775/262144 : ℝ)) hmem 8 (495997914383/500000000000 : ℝ) (991995828769/1000000000000 : ℝ) (495997914383/500000000000 : ℝ) (991995828769/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33775/262144 : ℝ))) hcmem 8 (62749997941/125000000000 : ℝ) (250999991769/500000000000 : ℝ) (62749997941/125000000000 : ℝ) (250999991769/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33775/262144 : ℝ)) (495997914383/500000000000 : ℝ) (991995828769/1000000000000 : ℝ) (62749997941/125000000000 : ℝ) (250999991769/500000000000 : ℝ) (794902264009/1000000000000 : ℝ) (794902264029/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1342_exp_lower
  have heNumeric : (513726283069/250000000000 : ℝ)/4 ≤ Real.exp (-21314069714553/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513726283069/250000000000 : ℝ)/4 ≤ Real.exp ((16887/131072 : ℝ)-(794902264029/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16887/131072 : ℝ) (33775/262144 : ℝ) (794902264029/1000000000000 : ℝ) (513726283069/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1343; no trusted numerical premise.
theorem cover8_leaf1343_exp_radius : (498994409329499469/500000000000000000 : ℝ) ≤ Real.exp ((-2111/131072 : ℝ)/8) ∧ Real.exp ((-2111/131072 : ℝ)/8) ≤ (997988818658998939/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2111/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1343_exp_lower : (460056825966034377/500000000000000000 : ℝ) ≤ Real.exp ((-42628137912353/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628137912353/64000000000000 : ℝ)/8) ≤ (184022730386413751/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628137912353/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1343_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (82196207239/40000000000 : ℝ) ≤ 4*Real.exp (33775/262144 : ℝ)*Real.exp (-mu (radius 8 (2111/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (82196207239/40000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2111/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1343_exp_radius
  have hrNumeric : (98402335067/100000000000 : ℝ) ≤ Real.exp (-2111/131072 : ℝ) ∧ Real.exp (-2111/131072 : ℝ) ≤ (984023350671/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (98402335067/100000000000 : ℝ) ≤ (radius 8 (2111/16384 : ℝ)) ∧ (radius 8 (2111/16384 : ℝ)) ≤ (984023350671/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2111/16384 : ℝ)) (98402335067/100000000000 : ℝ) (984023350671/1000000000000 : ℝ) (89019724407/500000000000 : ℝ) (178039448821/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2111/16384 : ℝ)) (98402335067/100000000000 : ℝ) (984023350671/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2111/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (98402335067/100000000000 : ℝ) (984023350671/1000000000000 : ℝ) (198402335067/200000000000 : ℝ) (124001459417/125000000000 : ℝ) (495989755607/500000000000 : ℝ) (61998719451/62500000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2111/16384 : ℝ)) 1 (198402335067/200000000000 : ℝ) (124001459417/125000000000 : ℝ) (495989755607/500000000000 : ℝ) (61998719451/62500000000 : ℝ) (495997796637/500000000000 : ℝ) (247998898319/250000000000 : ℝ) (123999449143/125000000000 : ℝ) (495997796573/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2111/16384 : ℝ)) 2 (495997796637/500000000000 : ℝ) (247998898319/250000000000 : ℝ) (123999449143/125000000000 : ℝ) (495997796573/500000000000 : ℝ) (991995593209/1000000000000 : ℝ) (991995593211/1000000000000 : ℝ) (123999449151/125000000000 : ℝ) (991995593211/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2111/16384 : ℝ)) 3 (991995593209/1000000000000 : ℝ) (991995593211/1000000000000 : ℝ) (123999449151/125000000000 : ℝ) (991995593211/1000000000000 : ℝ) (123999449151/125000000000 : ℝ) (991995593211/1000000000000 : ℝ) (123999449151/125000000000 : ℝ) (991995593211/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2111/16384 : ℝ)) 4 (123999449151/125000000000 : ℝ) (991995593211/1000000000000 : ℝ) (123999449151/125000000000 : ℝ) (991995593211/1000000000000 : ℝ) (123999449151/125000000000 : ℝ) (991995593211/1000000000000 : ℝ) (123999449151/125000000000 : ℝ) (991995593211/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2111/16384 : ℝ)) 5 (123999449151/125000000000 : ℝ) (991995593211/1000000000000 : ℝ) (123999449151/125000000000 : ℝ) (991995593211/1000000000000 : ℝ) (123999449151/125000000000 : ℝ) (991995593211/1000000000000 : ℝ) (123999449151/125000000000 : ℝ) (991995593211/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2111/16384 : ℝ)) 6 (123999449151/125000000000 : ℝ) (991995593211/1000000000000 : ℝ) (123999449151/125000000000 : ℝ) (991995593211/1000000000000 : ℝ) (123999449151/125000000000 : ℝ) (991995593211/1000000000000 : ℝ) (123999449151/125000000000 : ℝ) (991995593211/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2111/16384 : ℝ)) 7 (123999449151/125000000000 : ℝ) (991995593211/1000000000000 : ℝ) (123999449151/125000000000 : ℝ) (991995593211/1000000000000 : ℝ) (123999449151/125000000000 : ℝ) (991995593211/1000000000000 : ℝ) (123999449151/125000000000 : ℝ) (991995593211/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2111/16384 : ℝ))) (89019724407/500000000000 : ℝ) (178039448821/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2111/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (89019724407/500000000000 : ℝ) (178039448821/1000000000000 : ℝ) (589019724407/1000000000000 : ℝ) (589019724411/1000000000000 : ℝ) (105486802733/250000000000 : ℝ) (210973605471/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2111/16384 : ℝ))) 1 (589019724407/1000000000000 : ℝ) (589019724411/1000000000000 : ℝ) (105486802733/250000000000 : ℝ) (210973605471/500000000000 : ℝ) (505483467669/1000000000000 : ℝ) (505483467677/1000000000000 : ℝ) (498533078037/1000000000000 : ℝ) (249266539023/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2111/16384 : ℝ))) 2 (505483467669/1000000000000 : ℝ) (505483467677/1000000000000 : ℝ) (498533078037/1000000000000 : ℝ) (249266539023/500000000000 : ℝ) (502008272853/1000000000000 : ℝ) (251004136431/500000000000 : ℝ) (501996244043/1000000000000 : ℝ) (501996244053/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2111/16384 : ℝ))) 3 (502008272853/1000000000000 : ℝ) (251004136431/500000000000 : ℝ) (501996244043/1000000000000 : ℝ) (501996244053/1000000000000 : ℝ) (31375141153/62500000000 : ℝ) (251001129229/500000000000 : ℝ) (502002258411/1000000000000 : ℝ) (251001129211/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2111/16384 : ℝ))) 4 (31375141153/62500000000 : ℝ) (251001129229/500000000000 : ℝ) (502002258411/1000000000000 : ℝ) (251001129211/500000000000 : ℝ) (502002258429/1000000000000 : ℝ) (12550056461/25000000000 : ℝ) (502002258429/1000000000000 : ℝ) (12550056461/25000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2111/16384 : ℝ))) 5 (502002258429/1000000000000 : ℝ) (12550056461/25000000000 : ℝ) (502002258429/1000000000000 : ℝ) (12550056461/25000000000 : ℝ) (502002258429/1000000000000 : ℝ) (12550056461/25000000000 : ℝ) (502002258429/1000000000000 : ℝ) (12550056461/25000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2111/16384 : ℝ))) 6 (502002258429/1000000000000 : ℝ) (12550056461/25000000000 : ℝ) (502002258429/1000000000000 : ℝ) (12550056461/25000000000 : ℝ) (502002258429/1000000000000 : ℝ) (12550056461/25000000000 : ℝ) (502002258429/1000000000000 : ℝ) (12550056461/25000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2111/16384 : ℝ))) 7 (502002258429/1000000000000 : ℝ) (12550056461/25000000000 : ℝ) (502002258429/1000000000000 : ℝ) (12550056461/25000000000 : ℝ) (502002258429/1000000000000 : ℝ) (12550056461/25000000000 : ℝ) (502002258429/1000000000000 : ℝ) (12550056461/25000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2111/16384 : ℝ)) hmem 8 (123999449151/125000000000 : ℝ) (991995593211/1000000000000 : ℝ) (123999449151/125000000000 : ℝ) (991995593211/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2111/16384 : ℝ))) hcmem 8 (502002258429/1000000000000 : ℝ) (12550056461/25000000000 : ℝ) (502002258429/1000000000000 : ℝ) (12550056461/25000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2111/16384 : ℝ)) (123999449151/125000000000 : ℝ) (991995593211/1000000000000 : ℝ) (502002258429/1000000000000 : ℝ) (12550056461/25000000000 : ℝ) (397453027503/500000000000 : ℝ) (794906055027/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1343_exp_lower
  have heNumeric : (82196207239/40000000000 : ℝ)/4 ≤ Real.exp (-42628137912353/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (82196207239/40000000000 : ℝ)/4 ≤ Real.exp ((33775/262144 : ℝ)-(794906055027/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33775/262144 : ℝ) (2111/16384 : ℝ) (794906055027/1000000000000 : ℝ) (82196207239/40000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1344; no trusted numerical premise.
theorem cover8_leaf1344_exp_radius : (199597751834846337/200000000000000000 : ℝ) ≤ Real.exp ((-33777/2097152 : ℝ)/8) ∧ Real.exp ((-33777/2097152 : ℝ)/8) ≤ (498994379587115843/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33777/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1344_exp_lower : (920113654666907111/1000000000000000000 : ℝ) ≤ Real.exp ((-2664258524409/4000000000000 : ℝ)/8) ∧ Real.exp ((-2664258524409/4000000000000 : ℝ)/8) ≤ (115014206833363389/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2664258524409/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1344_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027452614919/500000000000 : ℝ) ≤ 4*Real.exp (2111/16384 : ℝ)*Real.exp (-mu (radius 8 (33777/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (1027452614919/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33777/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1344_exp_radius
  have hrNumeric : (984022881451/1000000000000 : ℝ) ≤ Real.exp (-33777/2097152 : ℝ) ∧ Real.exp (-33777/2097152 : ℝ) ≤ (246005720363/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984022881451/1000000000000 : ℝ) ≤ (radius 8 (33777/262144 : ℝ)) ∧ (radius 8 (33777/262144 : ℝ)) ≤ (246005720363/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33777/262144 : ℝ)) (984022881451/1000000000000 : ℝ) (246005720363/250000000000 : ℝ) (89021021083/500000000000 : ℝ) (178042042173/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33777/262144 : ℝ)) (984022881451/1000000000000 : ℝ) (246005720363/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33777/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984022881451/1000000000000 : ℝ) (246005720363/250000000000 : ℝ) (39680457629/40000000000 : ℝ) (496005720363/500000000000 : ℝ) (247994818677/250000000000 : ℝ) (991979274709/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33777/262144 : ℝ)) 1 (39680457629/40000000000 : ℝ) (496005720363/500000000000 : ℝ) (247994818677/250000000000 : ℝ) (991979274709/1000000000000 : ℝ) (247998839429/250000000000 : ℝ) (495997678859/500000000000 : ℝ) (495997678793/500000000000 : ℝ) (247998839397/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33777/262144 : ℝ)) 2 (247998839429/250000000000 : ℝ) (495997678859/500000000000 : ℝ) (495997678793/500000000000 : ℝ) (247998839397/250000000000 : ℝ) (991995357651/1000000000000 : ℝ) (991995357653/1000000000000 : ℝ) (19839907153/20000000000 : ℝ) (991995357653/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33777/262144 : ℝ)) 3 (991995357651/1000000000000 : ℝ) (991995357653/1000000000000 : ℝ) (19839907153/20000000000 : ℝ) (991995357653/1000000000000 : ℝ) (19839907153/20000000000 : ℝ) (991995357653/1000000000000 : ℝ) (19839907153/20000000000 : ℝ) (991995357653/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33777/262144 : ℝ)) 4 (19839907153/20000000000 : ℝ) (991995357653/1000000000000 : ℝ) (19839907153/20000000000 : ℝ) (991995357653/1000000000000 : ℝ) (19839907153/20000000000 : ℝ) (991995357653/1000000000000 : ℝ) (19839907153/20000000000 : ℝ) (991995357653/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33777/262144 : ℝ)) 5 (19839907153/20000000000 : ℝ) (991995357653/1000000000000 : ℝ) (19839907153/20000000000 : ℝ) (991995357653/1000000000000 : ℝ) (19839907153/20000000000 : ℝ) (991995357653/1000000000000 : ℝ) (19839907153/20000000000 : ℝ) (991995357653/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33777/262144 : ℝ)) 6 (19839907153/20000000000 : ℝ) (991995357653/1000000000000 : ℝ) (19839907153/20000000000 : ℝ) (991995357653/1000000000000 : ℝ) (19839907153/20000000000 : ℝ) (991995357653/1000000000000 : ℝ) (19839907153/20000000000 : ℝ) (991995357653/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33777/262144 : ℝ)) 7 (19839907153/20000000000 : ℝ) (991995357653/1000000000000 : ℝ) (19839907153/20000000000 : ℝ) (991995357653/1000000000000 : ℝ) (19839907153/20000000000 : ℝ) (991995357653/1000000000000 : ℝ) (19839907153/20000000000 : ℝ) (991995357653/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33777/262144 : ℝ))) (89021021083/500000000000 : ℝ) (178042042173/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33777/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (89021021083/500000000000 : ℝ) (178042042173/1000000000000 : ℝ) (589021021083/1000000000000 : ℝ) (589021021087/1000000000000 : ℝ) (210975141999/500000000000 : ℝ) (421950284007/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33777/262144 : ℝ))) 1 (589021021083/1000000000000 : ℝ) (589021021087/1000000000000 : ℝ) (210975141999/500000000000 : ℝ) (421950284007/1000000000000 : ℝ) (25274282627/50000000000 : ℝ) (505485652547/1000000000000 : ℝ) (498535442197/1000000000000 : ℝ) (99707088441/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33777/262144 : ℝ))) 2 (25274282627/50000000000 : ℝ) (505485652547/1000000000000 : ℝ) (498535442197/1000000000000 : ℝ) (99707088441/200000000000 : ℝ) (62751318421/125000000000 : ℝ) (31375659211/62500000000 : ℝ) (250999259617/500000000000 : ℝ) (250999259621/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33777/262144 : ℝ))) 3 (62751318421/125000000000 : ℝ) (31375659211/62500000000 : ℝ) (250999259617/500000000000 : ℝ) (250999259621/500000000000 : ℝ) (502004533301/1000000000000 : ℝ) (502004533309/1000000000000 : ℝ) (31375283329/62500000000 : ℝ) (502004533273/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33777/262144 : ℝ))) 4 (502004533301/1000000000000 : ℝ) (502004533309/1000000000000 : ℝ) (31375283329/62500000000 : ℝ) (502004533273/1000000000000 : ℝ) (251002266641/500000000000 : ℝ) (502004533291/1000000000000 : ℝ) (251002266641/500000000000 : ℝ) (502004533291/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33777/262144 : ℝ))) 5 (251002266641/500000000000 : ℝ) (502004533291/1000000000000 : ℝ) (251002266641/500000000000 : ℝ) (502004533291/1000000000000 : ℝ) (251002266641/500000000000 : ℝ) (502004533291/1000000000000 : ℝ) (251002266641/500000000000 : ℝ) (502004533291/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33777/262144 : ℝ))) 6 (251002266641/500000000000 : ℝ) (502004533291/1000000000000 : ℝ) (251002266641/500000000000 : ℝ) (502004533291/1000000000000 : ℝ) (251002266641/500000000000 : ℝ) (502004533291/1000000000000 : ℝ) (251002266641/500000000000 : ℝ) (502004533291/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33777/262144 : ℝ))) 7 (251002266641/500000000000 : ℝ) (502004533291/1000000000000 : ℝ) (251002266641/500000000000 : ℝ) (502004533291/1000000000000 : ℝ) (251002266641/500000000000 : ℝ) (502004533291/1000000000000 : ℝ) (251002266641/500000000000 : ℝ) (502004533291/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33777/262144 : ℝ)) hmem 8 (19839907153/20000000000 : ℝ) (991995357653/1000000000000 : ℝ) (19839907153/20000000000 : ℝ) (991995357653/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33777/262144 : ℝ))) hcmem 8 (251002266641/500000000000 : ℝ) (502004533291/1000000000000 : ℝ) (251002266641/500000000000 : ℝ) (502004533291/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33777/262144 : ℝ)) (19839907153/20000000000 : ℝ) (991995357653/1000000000000 : ℝ) (251002266641/500000000000 : ℝ) (502004533291/1000000000000 : ℝ) (99363730741/125000000000 : ℝ) (397454922973/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1344_exp_lower
  have heNumeric : (1027452614919/500000000000 : ℝ)/4 ≤ Real.exp (-2664258524409/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027452614919/500000000000 : ℝ)/4 ≤ Real.exp ((2111/16384 : ℝ)-(397454922973/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2111/16384 : ℝ) (33777/262144 : ℝ) (397454922973/500000000000 : ℝ) (1027452614919/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1345; no trusted numerical premise.
theorem cover8_leaf1345_exp_radius : (997988699689467977/1000000000000000000 : ℝ) ≤ Real.exp ((-16889/1048576 : ℝ)/8) ∧ Real.exp ((-16889/1048576 : ℝ)/8) ≤ (498994349844733989/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16889/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1345_exp_lower : (115014207176267689/125000000000000000 : ℝ) ≤ Real.exp ((-42628134864063/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628134864063/64000000000000 : ℝ)/8) ≤ (920113657410141513/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628134864063/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1345_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (41098105577/20000000000 : ℝ) ≤ 4*Real.exp (33777/262144 : ℝ)*Real.exp (-mu (radius 8 (16889/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (41098105577/20000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16889/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1345_exp_radius
  have hrNumeric : (123002801529/125000000000 : ℝ) ≤ Real.exp (-16889/1048576 : ℝ) ∧ Real.exp (-16889/1048576 : ℝ) ≤ (984022412233/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (123002801529/125000000000 : ℝ) ≤ (radius 8 (16889/131072 : ℝ)) ∧ (radius 8 (16889/131072 : ℝ)) ≤ (984022412233/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16889/131072 : ℝ)) (123002801529/125000000000 : ℝ) (984022412233/1000000000000 : ℝ) (178044635479/1000000000000 : ℝ) (89022317743/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16889/131072 : ℝ)) (123002801529/125000000000 : ℝ) (984022412233/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16889/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (123002801529/125000000000 : ℝ) (984022412233/1000000000000 : ℝ) (248002801529/250000000000 : ℝ) (992011206117/1000000000000 : ℝ) (991979038201/1000000000000 : ℝ) (991979038203/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16889/131072 : ℝ)) 1 (248002801529/250000000000 : ℝ) (992011206117/1000000000000 : ℝ) (991979038201/1000000000000 : ℝ) (991979038203/1000000000000 : ℝ) (495997561079/500000000000 : ℝ) (12399939027/12500000000 : ℝ) (247998780507/250000000000 : ℝ) (99199512203/100000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16889/131072 : ℝ)) 2 (495997561079/500000000000 : ℝ) (12399939027/12500000000 : ℝ) (247998780507/250000000000 : ℝ) (99199512203/100000000000 : ℝ) (991995122093/1000000000000 : ℝ) (198399024419/200000000000 : ℝ) (247998780523/250000000000 : ℝ) (198399024419/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16889/131072 : ℝ)) 3 (991995122093/1000000000000 : ℝ) (198399024419/200000000000 : ℝ) (247998780523/250000000000 : ℝ) (198399024419/200000000000 : ℝ) (247998780523/250000000000 : ℝ) (198399024419/200000000000 : ℝ) (247998780523/250000000000 : ℝ) (198399024419/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16889/131072 : ℝ)) 4 (247998780523/250000000000 : ℝ) (198399024419/200000000000 : ℝ) (247998780523/250000000000 : ℝ) (198399024419/200000000000 : ℝ) (247998780523/250000000000 : ℝ) (198399024419/200000000000 : ℝ) (247998780523/250000000000 : ℝ) (198399024419/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16889/131072 : ℝ)) 5 (247998780523/250000000000 : ℝ) (198399024419/200000000000 : ℝ) (247998780523/250000000000 : ℝ) (198399024419/200000000000 : ℝ) (247998780523/250000000000 : ℝ) (198399024419/200000000000 : ℝ) (247998780523/250000000000 : ℝ) (198399024419/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16889/131072 : ℝ)) 6 (247998780523/250000000000 : ℝ) (198399024419/200000000000 : ℝ) (247998780523/250000000000 : ℝ) (198399024419/200000000000 : ℝ) (247998780523/250000000000 : ℝ) (198399024419/200000000000 : ℝ) (247998780523/250000000000 : ℝ) (198399024419/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16889/131072 : ℝ)) 7 (247998780523/250000000000 : ℝ) (198399024419/200000000000 : ℝ) (247998780523/250000000000 : ℝ) (198399024419/200000000000 : ℝ) (247998780523/250000000000 : ℝ) (198399024419/200000000000 : ℝ) (247998780523/250000000000 : ℝ) (198399024419/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16889/131072 : ℝ))) (178044635479/1000000000000 : ℝ) (89022317743/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16889/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (178044635479/1000000000000 : ℝ) (89022317743/500000000000 : ℝ) (589022317739/1000000000000 : ℝ) (589022317743/1000000000000 : ℝ) (210976678497/500000000000 : ℝ) (421953357003/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16889/131072 : ℝ))) 1 (589022317739/1000000000000 : ℝ) (589022317743/1000000000000 : ℝ) (210976678497/500000000000 : ℝ) (421953357003/1000000000000 : ℝ) (252743918683/500000000000 : ℝ) (505487837373/1000000000000 : ℝ) (498537806303/1000000000000 : ℝ) (498537806311/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16889/131072 : ℝ))) 2 (252743918683/500000000000 : ℝ) (505487837373/1000000000000 : ℝ) (498537806303/1000000000000 : ℝ) (498537806311/1000000000000 : ℝ) (251006410917/500000000000 : ℝ) (251006410921/500000000000 : ℝ) (803201271/1600000000 : ℝ) (502000794383/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16889/131072 : ℝ))) 3 (251006410917/500000000000 : ℝ) (251006410921/500000000000 : ℝ) (803201271/1600000000 : ℝ) (502000794383/1000000000000 : ℝ) (62750851013/125000000000 : ℝ) (502006808113/1000000000000 : ℝ) (125501702017/250000000000 : ℝ) (502006808077/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16889/131072 : ℝ))) 4 (62750851013/125000000000 : ℝ) (502006808113/1000000000000 : ℝ) (125501702017/250000000000 : ℝ) (502006808077/1000000000000 : ℝ) (251003404043/500000000000 : ℝ) (100401361619/200000000000 : ℝ) (100401361617/200000000000 : ℝ) (100401361619/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16889/131072 : ℝ))) 5 (251003404043/500000000000 : ℝ) (100401361619/200000000000 : ℝ) (100401361617/200000000000 : ℝ) (100401361619/200000000000 : ℝ) (100401361617/200000000000 : ℝ) (100401361619/200000000000 : ℝ) (100401361617/200000000000 : ℝ) (100401361619/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16889/131072 : ℝ))) 6 (100401361617/200000000000 : ℝ) (100401361619/200000000000 : ℝ) (100401361617/200000000000 : ℝ) (100401361619/200000000000 : ℝ) (100401361617/200000000000 : ℝ) (100401361619/200000000000 : ℝ) (100401361617/200000000000 : ℝ) (100401361619/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16889/131072 : ℝ))) 7 (100401361617/200000000000 : ℝ) (100401361619/200000000000 : ℝ) (100401361617/200000000000 : ℝ) (100401361619/200000000000 : ℝ) (100401361617/200000000000 : ℝ) (100401361619/200000000000 : ℝ) (100401361617/200000000000 : ℝ) (100401361619/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16889/131072 : ℝ)) hmem 8 (247998780523/250000000000 : ℝ) (198399024419/200000000000 : ℝ) (247998780523/250000000000 : ℝ) (198399024419/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16889/131072 : ℝ))) hcmem 8 (100401361617/200000000000 : ℝ) (100401361619/200000000000 : ℝ) (100401361617/200000000000 : ℝ) (100401361619/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16889/131072 : ℝ)) (247998780523/250000000000 : ℝ) (198399024419/200000000000 : ℝ) (100401361617/200000000000 : ℝ) (100401361619/200000000000 : ℝ) (794913636773/1000000000000 : ℝ) (99364204599/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1345_exp_lower
  have heNumeric : (41098105577/20000000000 : ℝ)/4 ≤ Real.exp (-42628134864063/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (41098105577/20000000000 : ℝ)/4 ≤ Real.exp ((33777/262144 : ℝ)-(99364204599/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33777/262144 : ℝ) (16889/131072 : ℝ) (99364204599/125000000000 : ℝ) (41098105577/20000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1346; no trusted numerical premise.
theorem cover8_leaf1346_exp_radius : (199597728040941563/200000000000000000 : ℝ) ≤ Real.exp ((-33779/2097152 : ℝ)/8) ∧ Real.exp ((-33779/2097152 : ℝ)/8) ≤ (124748580025588477/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33779/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1346_exp_lower : (57507103760175443/62500000000000000 : ℝ) ≤ Real.exp ((-21314066666167/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314066666167/32000000000000 : ℝ)/8) ≤ (920113660162807089/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314066666167/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1346_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (205490532803/100000000000 : ℝ) ≤ 4*Real.exp (16889/131072 : ℝ)*Real.exp (-mu (radius 8 (33779/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (205490532803/100000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33779/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1346_exp_radius
  have hrNumeric : (492010971507/500000000000 : ℝ) ≤ Real.exp (-33779/2097152 : ℝ) ∧ Real.exp (-33779/2097152 : ℝ) ≤ (196804388603/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492010971507/500000000000 : ℝ) ≤ (radius 8 (33779/262144 : ℝ)) ∧ (radius 8 (33779/262144 : ℝ)) ≤ (196804388603/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33779/262144 : ℝ)) (492010971507/500000000000 : ℝ) (196804388603/200000000000 : ℝ) (44511807187/250000000000 : ℝ) (89023614377/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33779/262144 : ℝ)) (492010971507/500000000000 : ℝ) (196804388603/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33779/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492010971507/500000000000 : ℝ) (196804388603/200000000000 : ℝ) (992010971507/1000000000000 : ℝ) (248002742877/250000000000 : ℝ) (198395760339/200000000000 : ℝ) (991978801697/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33779/262144 : ℝ)) 1 (992010971507/1000000000000 : ℝ) (248002742877/250000000000 : ℝ) (198395760339/200000000000 : ℝ) (991978801697/1000000000000 : ℝ) (991994886601/1000000000000 : ℝ) (991994886603/1000000000000 : ℝ) (99199488647/100000000000 : ℝ) (991994886473/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33779/262144 : ℝ)) 2 (991994886601/1000000000000 : ℝ) (991994886603/1000000000000 : ℝ) (99199488647/100000000000 : ℝ) (991994886473/1000000000000 : ℝ) (198398977307/200000000000 : ℝ) (495997443269/500000000000 : ℝ) (198398977307/200000000000 : ℝ) (495997443269/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33779/262144 : ℝ)) 3 (198398977307/200000000000 : ℝ) (495997443269/500000000000 : ℝ) (198398977307/200000000000 : ℝ) (495997443269/500000000000 : ℝ) (198398977307/200000000000 : ℝ) (495997443269/500000000000 : ℝ) (198398977307/200000000000 : ℝ) (495997443269/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33779/262144 : ℝ)) 4 (198398977307/200000000000 : ℝ) (495997443269/500000000000 : ℝ) (198398977307/200000000000 : ℝ) (495997443269/500000000000 : ℝ) (198398977307/200000000000 : ℝ) (495997443269/500000000000 : ℝ) (198398977307/200000000000 : ℝ) (495997443269/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33779/262144 : ℝ)) 5 (198398977307/200000000000 : ℝ) (495997443269/500000000000 : ℝ) (198398977307/200000000000 : ℝ) (495997443269/500000000000 : ℝ) (198398977307/200000000000 : ℝ) (495997443269/500000000000 : ℝ) (198398977307/200000000000 : ℝ) (495997443269/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33779/262144 : ℝ)) 6 (198398977307/200000000000 : ℝ) (495997443269/500000000000 : ℝ) (198398977307/200000000000 : ℝ) (495997443269/500000000000 : ℝ) (198398977307/200000000000 : ℝ) (495997443269/500000000000 : ℝ) (198398977307/200000000000 : ℝ) (495997443269/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33779/262144 : ℝ)) 7 (198398977307/200000000000 : ℝ) (495997443269/500000000000 : ℝ) (198398977307/200000000000 : ℝ) (495997443269/500000000000 : ℝ) (198398977307/200000000000 : ℝ) (495997443269/500000000000 : ℝ) (198398977307/200000000000 : ℝ) (495997443269/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33779/262144 : ℝ))) (44511807187/250000000000 : ℝ) (89023614377/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33779/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44511807187/250000000000 : ℝ) (89023614377/500000000000 : ℝ) (294511807187/500000000000 : ℝ) (589023614377/1000000000000 : ℝ) (105489107479/250000000000 : ℝ) (105489107481/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33779/262144 : ℝ))) 1 (294511807187/500000000000 : ℝ) (589023614377/1000000000000 : ℝ) (105489107479/250000000000 : ℝ) (105489107481/250000000000 : ℝ) (101098004429/200000000000 : ℝ) (505490022151/1000000000000 : ℝ) (249270085177/500000000000 : ℝ) (498540170361/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33779/262144 : ℝ))) 2 (101098004429/200000000000 : ℝ) (505490022151/1000000000000 : ℝ) (249270085177/500000000000 : ℝ) (498540170361/1000000000000 : ℝ) (502015096249/1000000000000 : ℝ) (7843985879/15625000000 : ℝ) (100400613893/200000000000 : ℝ) (15687595921/31250000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33779/262144 : ℝ))) 3 (502015096249/1000000000000 : ℝ) (7843985879/15625000000 : ℝ) (100400613893/200000000000 : ℝ) (15687595921/31250000000 : ℝ) (502009082857/1000000000000 : ℝ) (31375567679/62500000000 : ℝ) (25100454141/50000000000 : ℝ) (125502270707/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33779/262144 : ℝ))) 4 (502009082857/1000000000000 : ℝ) (31375567679/62500000000 : ℝ) (25100454141/50000000000 : ℝ) (125502270707/250000000000 : ℝ) (251004541419/500000000000 : ℝ) (251004541423/500000000000 : ℝ) (251004541419/500000000000 : ℝ) (251004541423/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33779/262144 : ℝ))) 5 (251004541419/500000000000 : ℝ) (251004541423/500000000000 : ℝ) (251004541419/500000000000 : ℝ) (251004541423/500000000000 : ℝ) (251004541419/500000000000 : ℝ) (251004541423/500000000000 : ℝ) (251004541419/500000000000 : ℝ) (251004541423/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33779/262144 : ℝ))) 6 (251004541419/500000000000 : ℝ) (251004541423/500000000000 : ℝ) (251004541419/500000000000 : ℝ) (251004541423/500000000000 : ℝ) (251004541419/500000000000 : ℝ) (251004541423/500000000000 : ℝ) (251004541419/500000000000 : ℝ) (251004541423/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33779/262144 : ℝ))) 7 (251004541419/500000000000 : ℝ) (251004541423/500000000000 : ℝ) (251004541419/500000000000 : ℝ) (251004541423/500000000000 : ℝ) (251004541419/500000000000 : ℝ) (251004541423/500000000000 : ℝ) (251004541419/500000000000 : ℝ) (251004541423/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33779/262144 : ℝ)) hmem 8 (198398977307/200000000000 : ℝ) (495997443269/500000000000 : ℝ) (198398977307/200000000000 : ℝ) (495997443269/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33779/262144 : ℝ))) hcmem 8 (251004541419/500000000000 : ℝ) (251004541423/500000000000 : ℝ) (251004541419/500000000000 : ℝ) (251004541423/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33779/262144 : ℝ)) (198398977307/200000000000 : ℝ) (495997443269/500000000000 : ℝ) (251004541419/500000000000 : ℝ) (251004541423/500000000000 : ℝ) (794917427539/1000000000000 : ℝ) (198729356889/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1346_exp_lower
  have heNumeric : (205490532803/100000000000 : ℝ)/4 ≤ Real.exp (-21314066666167/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (205490532803/100000000000 : ℝ)/4 ≤ Real.exp ((16889/131072 : ℝ)-(198729356889/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16889/131072 : ℝ) (33779/262144 : ℝ) (198729356889/250000000000 : ℝ) (205490532803/100000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1347; no trusted numerical premise.
theorem cover8_leaf1347_exp_radius : (997988580719951199/1000000000000000000 : ℝ) ≤ Real.exp ((-8445/524288 : ℝ)/8) ∧ Real.exp ((-8445/524288 : ℝ)/8) ≤ (1247485725899939/1250000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8445/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1347_exp_lower : (23002841573090967/25000000000000000 : ℝ) ≤ Real.exp ((-42628131796061/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628131796061/64000000000000 : ℝ)/8) ≤ (920113662923638681/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628131796061/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1347_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054905377357/1000000000000 : ℝ) ≤ 4*Real.exp (33779/262144 : ℝ)*Real.exp (-mu (radius 8 (8445/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (2054905377357/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8445/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1347_exp_radius
  have hrNumeric : (246005368449/250000000000 : ℝ) ≤ Real.exp (-8445/524288 : ℝ) ∧ Real.exp (-8445/524288 : ℝ) ≤ (984021473797/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246005368449/250000000000 : ℝ) ≤ (radius 8 (8445/65536 : ℝ)) ∧ (radius 8 (8445/65536 : ℝ)) ≤ (984021473797/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8445/65536 : ℝ)) (246005368449/250000000000 : ℝ) (984021473797/1000000000000 : ℝ) (178049821977/1000000000000 : ℝ) (5564056937/31250000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8445/65536 : ℝ)) (246005368449/250000000000 : ℝ) (984021473797/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8445/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246005368449/250000000000 : ℝ) (984021473797/1000000000000 : ℝ) (496005368449/500000000000 : ℝ) (992010736899/1000000000000 : ℝ) (991978565189/1000000000000 : ℝ) (991978565191/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8445/65536 : ℝ)) 1 (496005368449/500000000000 : ℝ) (992010736899/1000000000000 : ℝ) (991978565189/1000000000000 : ℝ) (991978565191/1000000000000 : ℝ) (991994651043/1000000000000 : ℝ) (198398930209/200000000000 : ℝ) (991994650913/1000000000000 : ℝ) (198398930183/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8445/65536 : ℝ)) 2 (991994651043/1000000000000 : ℝ) (198398930209/200000000000 : ℝ) (991994650913/1000000000000 : ℝ) (198398930183/200000000000 : ℝ) (495997325489/500000000000 : ℝ) (49599732549/50000000000 : ℝ) (991994650977/1000000000000 : ℝ) (49599732549/50000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8445/65536 : ℝ)) 3 (495997325489/500000000000 : ℝ) (49599732549/50000000000 : ℝ) (991994650977/1000000000000 : ℝ) (49599732549/50000000000 : ℝ) (991994650977/1000000000000 : ℝ) (49599732549/50000000000 : ℝ) (991994650977/1000000000000 : ℝ) (49599732549/50000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8445/65536 : ℝ)) 4 (991994650977/1000000000000 : ℝ) (49599732549/50000000000 : ℝ) (991994650977/1000000000000 : ℝ) (49599732549/50000000000 : ℝ) (991994650977/1000000000000 : ℝ) (49599732549/50000000000 : ℝ) (991994650977/1000000000000 : ℝ) (49599732549/50000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8445/65536 : ℝ)) 5 (991994650977/1000000000000 : ℝ) (49599732549/50000000000 : ℝ) (991994650977/1000000000000 : ℝ) (49599732549/50000000000 : ℝ) (991994650977/1000000000000 : ℝ) (49599732549/50000000000 : ℝ) (991994650977/1000000000000 : ℝ) (49599732549/50000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8445/65536 : ℝ)) 6 (991994650977/1000000000000 : ℝ) (49599732549/50000000000 : ℝ) (991994650977/1000000000000 : ℝ) (49599732549/50000000000 : ℝ) (991994650977/1000000000000 : ℝ) (49599732549/50000000000 : ℝ) (991994650977/1000000000000 : ℝ) (49599732549/50000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8445/65536 : ℝ)) 7 (991994650977/1000000000000 : ℝ) (49599732549/50000000000 : ℝ) (991994650977/1000000000000 : ℝ) (49599732549/50000000000 : ℝ) (991994650977/1000000000000 : ℝ) (49599732549/50000000000 : ℝ) (991994650977/1000000000000 : ℝ) (49599732549/50000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8445/65536 : ℝ))) (178049821977/1000000000000 : ℝ) (5564056937/31250000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8445/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (178049821977/1000000000000 : ℝ) (5564056937/31250000000 : ℝ) (147256227747/250000000000 : ℝ) (36814056937/62500000000 : ℝ) (26372468923/62500000000 : ℝ) (210979751389/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8445/65536 : ℝ))) 1 (147256227747/250000000000 : ℝ) (36814056937/62500000000 : ℝ) (26372468923/62500000000 : ℝ) (210979751389/500000000000 : ℝ) (252746103439/500000000000 : ℝ) (101098441377/200000000000 : ℝ) (31158908397/62500000000 : ℝ) (12463563359/25000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8445/65536 : ℝ))) 2 (252746103439/500000000000 : ℝ) (101098441377/200000000000 : ℝ) (31158908397/62500000000 : ℝ) (12463563359/25000000000 : ℝ) (100403474123/200000000000 : ℝ) (502017370623/1000000000000 : ℝ) (100401068901/200000000000 : ℝ) (251002672257/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8445/65536 : ℝ))) 3 (100403474123/200000000000 : ℝ) (502017370623/1000000000000 : ℝ) (100401068901/200000000000 : ℝ) (251002672257/500000000000 : ℝ) (12550283939/25000000000 : ℝ) (502011357569/1000000000000 : ℝ) (502011357523/1000000000000 : ℝ) (502011357533/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8445/65536 : ℝ))) 4 (12550283939/25000000000 : ℝ) (502011357569/1000000000000 : ℝ) (502011357523/1000000000000 : ℝ) (502011357533/1000000000000 : ℝ) (502011357541/1000000000000 : ℝ) (502011357551/1000000000000 : ℝ) (502011357541/1000000000000 : ℝ) (502011357551/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8445/65536 : ℝ))) 5 (502011357541/1000000000000 : ℝ) (502011357551/1000000000000 : ℝ) (502011357541/1000000000000 : ℝ) (502011357551/1000000000000 : ℝ) (502011357541/1000000000000 : ℝ) (502011357551/1000000000000 : ℝ) (502011357541/1000000000000 : ℝ) (502011357551/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8445/65536 : ℝ))) 6 (502011357541/1000000000000 : ℝ) (502011357551/1000000000000 : ℝ) (502011357541/1000000000000 : ℝ) (502011357551/1000000000000 : ℝ) (502011357541/1000000000000 : ℝ) (502011357551/1000000000000 : ℝ) (502011357541/1000000000000 : ℝ) (502011357551/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8445/65536 : ℝ))) 7 (502011357541/1000000000000 : ℝ) (502011357551/1000000000000 : ℝ) (502011357541/1000000000000 : ℝ) (502011357551/1000000000000 : ℝ) (502011357541/1000000000000 : ℝ) (502011357551/1000000000000 : ℝ) (502011357541/1000000000000 : ℝ) (502011357551/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8445/65536 : ℝ)) hmem 8 (991994650977/1000000000000 : ℝ) (49599732549/50000000000 : ℝ) (991994650977/1000000000000 : ℝ) (49599732549/50000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8445/65536 : ℝ))) hcmem 8 (502011357541/1000000000000 : ℝ) (502011357551/1000000000000 : ℝ) (502011357541/1000000000000 : ℝ) (502011357551/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8445/65536 : ℝ)) (991994650977/1000000000000 : ℝ) (49599732549/50000000000 : ℝ) (502011357541/1000000000000 : ℝ) (502011357551/1000000000000 : ℝ) (79492121823/100000000000 : ℝ) (794921218249/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1347_exp_lower
  have heNumeric : (2054905377357/1000000000000 : ℝ)/4 ≤ Real.exp (-42628131796061/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054905377357/1000000000000 : ℝ)/4 ≤ Real.exp ((33779/262144 : ℝ)-(794921218249/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33779/262144 : ℝ) (8445/65536 : ℝ) (794921218249/1000000000000 : ℝ) (2054905377357/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1348; no trusted numerical premise.
theorem cover8_leaf1348_exp_radius : (62374282577199883/62500000000000000 : ℝ) ≤ Real.exp ((-33781/2097152 : ℝ)/8) ∧ Real.exp ((-33781/2097152 : ℝ)/8) ≤ (997988521235198129/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33781/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1348_exp_lower : (460056832846663187/500000000000000000 : ℝ) ≤ Real.exp ((-2131406512743/3200000000000 : ℝ)/8) ∧ Real.exp ((-2131406512743/3200000000000 : ℝ)/8) ≤ (7360909325546611/8000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2131406512743/3200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1348_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054905426841/1000000000000 : ℝ) ≤ 4*Real.exp (8445/65536 : ℝ)*Real.exp (-mu (radius 8 (33781/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054905426841/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33781/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1348_exp_radius
  have hrNumeric : (492010502289/500000000000 : ℝ) ≤ Real.exp (-33781/2097152 : ℝ) ∧ Real.exp (-33781/2097152 : ℝ) ≤ (984021004579/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492010502289/500000000000 : ℝ) ≤ (radius 8 (33781/262144 : ℝ)) ∧ (radius 8 (33781/262144 : ℝ)) ≤ (984021004579/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33781/262144 : ℝ)) (492010502289/500000000000 : ℝ) (984021004579/1000000000000 : ℝ) (2782068987/15625000000 : ℝ) (7122096607/40000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33781/262144 : ℝ)) (492010502289/500000000000 : ℝ) (984021004579/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33781/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492010502289/500000000000 : ℝ) (984021004579/1000000000000 : ℝ) (992010502289/1000000000000 : ℝ) (99201050229/100000000000 : ℝ) (991978328683/1000000000000 : ℝ) (198395665737/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33781/262144 : ℝ)) 1 (992010502289/1000000000000 : ℝ) (99201050229/100000000000 : ℝ) (991978328683/1000000000000 : ℝ) (198395665737/200000000000 : ℝ) (495997207743/500000000000 : ℝ) (7749956371/7812500000 : ℝ) (198398883071/200000000000 : ℝ) (495997207679/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33781/262144 : ℝ)) 2 (495997207743/500000000000 : ℝ) (7749956371/7812500000 : ℝ) (198398883071/200000000000 : ℝ) (495997207679/500000000000 : ℝ) (49599720771/50000000000 : ℝ) (991994415423/1000000000000 : ℝ) (49599720771/50000000000 : ℝ) (991994415423/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33781/262144 : ℝ)) 3 (49599720771/50000000000 : ℝ) (991994415423/1000000000000 : ℝ) (49599720771/50000000000 : ℝ) (991994415423/1000000000000 : ℝ) (49599720771/50000000000 : ℝ) (991994415423/1000000000000 : ℝ) (49599720771/50000000000 : ℝ) (991994415423/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33781/262144 : ℝ)) 4 (49599720771/50000000000 : ℝ) (991994415423/1000000000000 : ℝ) (49599720771/50000000000 : ℝ) (991994415423/1000000000000 : ℝ) (49599720771/50000000000 : ℝ) (991994415423/1000000000000 : ℝ) (49599720771/50000000000 : ℝ) (991994415423/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33781/262144 : ℝ)) 5 (49599720771/50000000000 : ℝ) (991994415423/1000000000000 : ℝ) (49599720771/50000000000 : ℝ) (991994415423/1000000000000 : ℝ) (49599720771/50000000000 : ℝ) (991994415423/1000000000000 : ℝ) (49599720771/50000000000 : ℝ) (991994415423/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33781/262144 : ℝ)) 6 (49599720771/50000000000 : ℝ) (991994415423/1000000000000 : ℝ) (49599720771/50000000000 : ℝ) (991994415423/1000000000000 : ℝ) (49599720771/50000000000 : ℝ) (991994415423/1000000000000 : ℝ) (49599720771/50000000000 : ℝ) (991994415423/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33781/262144 : ℝ)) 7 (49599720771/50000000000 : ℝ) (991994415423/1000000000000 : ℝ) (49599720771/50000000000 : ℝ) (991994415423/1000000000000 : ℝ) (49599720771/50000000000 : ℝ) (991994415423/1000000000000 : ℝ) (49599720771/50000000000 : ℝ) (991994415423/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33781/262144 : ℝ))) (2782068987/15625000000 : ℝ) (7122096607/40000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33781/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (2782068987/15625000000 : ℝ) (7122096607/40000000000 : ℝ) (18407068987/31250000000 : ℝ) (147256551897/250000000000 : ℝ) (421962575553/1000000000000 : ℝ) (421962575563/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33781/262144 : ℝ))) 1 (18407068987/31250000000 : ℝ) (147256551897/250000000000 : ℝ) (421962575553/1000000000000 : ℝ) (421962575563/1000000000000 : ℝ) (31593399473/62500000000 : ℝ) (63186798947/125000000000 : ℝ) (498544898299/1000000000000 : ℝ) (124636224577/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33781/262144 : ℝ))) 2 (31593399473/62500000000 : ℝ) (63186798947/125000000000 : ℝ) (498544898299/1000000000000 : ℝ) (124636224577/250000000000 : ℝ) (502019644933/1000000000000 : ℝ) (251009822471/500000000000 : ℝ) (251003809749/500000000000 : ℝ) (125501904877/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33781/262144 : ℝ))) 3 (502019644933/1000000000000 : ℝ) (251009822471/500000000000 : ℝ) (251003809749/500000000000 : ℝ) (125501904877/250000000000 : ℝ) (100402726443/200000000000 : ℝ) (20080545289/40000000000 : ℝ) (502013632179/1000000000000 : ℝ) (502013632189/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33781/262144 : ℝ))) 4 (100402726443/200000000000 : ℝ) (20080545289/40000000000 : ℝ) (502013632179/1000000000000 : ℝ) (502013632189/1000000000000 : ℝ) (502013632197/1000000000000 : ℝ) (502013632207/1000000000000 : ℝ) (125503408049/250000000000 : ℝ) (502013632207/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33781/262144 : ℝ))) 5 (502013632197/1000000000000 : ℝ) (502013632207/1000000000000 : ℝ) (125503408049/250000000000 : ℝ) (502013632207/1000000000000 : ℝ) (125503408049/250000000000 : ℝ) (502013632207/1000000000000 : ℝ) (125503408049/250000000000 : ℝ) (502013632207/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33781/262144 : ℝ))) 6 (125503408049/250000000000 : ℝ) (502013632207/1000000000000 : ℝ) (125503408049/250000000000 : ℝ) (502013632207/1000000000000 : ℝ) (125503408049/250000000000 : ℝ) (502013632207/1000000000000 : ℝ) (125503408049/250000000000 : ℝ) (502013632207/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33781/262144 : ℝ))) 7 (125503408049/250000000000 : ℝ) (502013632207/1000000000000 : ℝ) (125503408049/250000000000 : ℝ) (502013632207/1000000000000 : ℝ) (125503408049/250000000000 : ℝ) (502013632207/1000000000000 : ℝ) (125503408049/250000000000 : ℝ) (502013632207/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33781/262144 : ℝ)) hmem 8 (49599720771/50000000000 : ℝ) (991994415423/1000000000000 : ℝ) (49599720771/50000000000 : ℝ) (991994415423/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33781/262144 : ℝ))) hcmem 8 (125503408049/250000000000 : ℝ) (502013632207/1000000000000 : ℝ) (125503408049/250000000000 : ℝ) (502013632207/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33781/262144 : ℝ)) (49599720771/50000000000 : ℝ) (991994415423/1000000000000 : ℝ) (125503408049/250000000000 : ℝ) (502013632207/1000000000000 : ℝ) (158985001769/200000000000 : ℝ) (158985001773/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1348_exp_lower
  have heNumeric : (2054905426841/1000000000000 : ℝ)/4 ≤ Real.exp (-2131406512743/3200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054905426841/1000000000000 : ℝ)/4 ≤ Real.exp ((8445/65536 : ℝ)-(158985001773/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8445/65536 : ℝ) (33781/262144 : ℝ) (158985001773/200000000000 : ℝ) (2054905426841/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1349; no trusted numerical premise.
theorem cover8_leaf1349_exp_radius : (997988461750448603/1000000000000000000 : ℝ) ≤ Real.exp ((-16891/1048576 : ℝ)/8) ∧ Real.exp ((-16891/1048576 : ℝ)/8) ≤ (249497115437612151/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16891/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1349_exp_lower : (115014208558940641/125000000000000000 : ℝ) ≤ Real.exp ((-42628128708923/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628128708923/64000000000000 : ℝ)/8) ≤ (920113668471525129/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628128708923/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1349_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027452738239/500000000000 : ℝ) ≤ 4*Real.exp (33781/262144 : ℝ)*Real.exp (-mu (radius 8 (16891/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (1027452738239/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16891/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1349_exp_radius
  have hrNumeric : (3075064173/3125000000 : ℝ) ≤ Real.exp (-16891/1048576 : ℝ) ∧ Real.exp (-16891/1048576 : ℝ) ≤ (984020535361/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (3075064173/3125000000 : ℝ) ≤ (radius 8 (16891/131072 : ℝ)) ∧ (radius 8 (16891/131072 : ℝ)) ≤ (984020535361/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16891/131072 : ℝ)) (3075064173/3125000000 : ℝ) (984020535361/1000000000000 : ℝ) (556421901/3125000000 : ℝ) (89027504163/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16891/131072 : ℝ)) (3075064173/3125000000 : ℝ) (984020535361/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16891/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (3075064173/3125000000 : ℝ) (984020535361/1000000000000 : ℝ) (6200064173/6250000000 : ℝ) (992010267681/1000000000000 : ℝ) (991978092177/1000000000000 : ℝ) (495989046089/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16891/131072 : ℝ)) 1 (6200064173/6250000000 : ℝ) (992010267681/1000000000000 : ℝ) (991978092177/1000000000000 : ℝ) (495989046089/500000000000 : ℝ) (123999272491/125000000000 : ℝ) (99199417993/100000000000 : ℝ) (495997089899/500000000000 : ℝ) (4959970899/5000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16891/131072 : ℝ)) 2 (123999272491/125000000000 : ℝ) (99199417993/100000000000 : ℝ) (495997089899/500000000000 : ℝ) (4959970899/5000000000 : ℝ) (991994179863/1000000000000 : ℝ) (198398835973/200000000000 : ℝ) (495997089931/500000000000 : ℝ) (198398835973/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16891/131072 : ℝ)) 3 (991994179863/1000000000000 : ℝ) (198398835973/200000000000 : ℝ) (495997089931/500000000000 : ℝ) (198398835973/200000000000 : ℝ) (495997089931/500000000000 : ℝ) (198398835973/200000000000 : ℝ) (495997089931/500000000000 : ℝ) (198398835973/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16891/131072 : ℝ)) 4 (495997089931/500000000000 : ℝ) (198398835973/200000000000 : ℝ) (495997089931/500000000000 : ℝ) (198398835973/200000000000 : ℝ) (495997089931/500000000000 : ℝ) (198398835973/200000000000 : ℝ) (495997089931/500000000000 : ℝ) (198398835973/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16891/131072 : ℝ)) 5 (495997089931/500000000000 : ℝ) (198398835973/200000000000 : ℝ) (495997089931/500000000000 : ℝ) (198398835973/200000000000 : ℝ) (495997089931/500000000000 : ℝ) (198398835973/200000000000 : ℝ) (495997089931/500000000000 : ℝ) (198398835973/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16891/131072 : ℝ)) 6 (495997089931/500000000000 : ℝ) (198398835973/200000000000 : ℝ) (495997089931/500000000000 : ℝ) (198398835973/200000000000 : ℝ) (495997089931/500000000000 : ℝ) (198398835973/200000000000 : ℝ) (495997089931/500000000000 : ℝ) (198398835973/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16891/131072 : ℝ)) 7 (495997089931/500000000000 : ℝ) (198398835973/200000000000 : ℝ) (495997089931/500000000000 : ℝ) (198398835973/200000000000 : ℝ) (495997089931/500000000000 : ℝ) (198398835973/200000000000 : ℝ) (495997089931/500000000000 : ℝ) (198398835973/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16891/131072 : ℝ))) (556421901/3125000000 : ℝ) (89027504163/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16891/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (556421901/3125000000 : ℝ) (89027504163/500000000000 : ℝ) (3681421901/6250000000 : ℝ) (589027504163/1000000000000 : ℝ) (42196564827/100000000000 : ℝ) (210982824139/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16891/131072 : ℝ))) 1 (3681421901/6250000000 : ℝ) (589027504163/1000000000000 : ℝ) (42196564827/100000000000 : ℝ) (210982824139/500000000000 : ℝ) (101099315243/200000000000 : ℝ) (505496576221/1000000000000 : ℝ) (249273631097/500000000000 : ℝ) (498547262201/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16891/131072 : ℝ))) 2 (101099315243/200000000000 : ℝ) (505496576221/1000000000000 : ℝ) (249273631097/500000000000 : ℝ) (498547262201/1000000000000 : ℝ) (125505479801/250000000000 : ℝ) (502021919211/1000000000000 : ℝ) (125502473611/250000000000 : ℝ) (125502473613/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16891/131072 : ℝ))) 3 (125505479801/250000000000 : ℝ) (502021919211/1000000000000 : ℝ) (125502473611/250000000000 : ℝ) (125502473613/250000000000 : ℝ) (62751988353/125000000000 : ℝ) (31375994177/62500000000 : ℝ) (502015906787/1000000000000 : ℝ) (125503976699/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16891/131072 : ℝ))) 4 (62751988353/125000000000 : ℝ) (31375994177/62500000000 : ℝ) (502015906787/1000000000000 : ℝ) (125503976699/250000000000 : ℝ) (100403181361/200000000000 : ℝ) (251007953407/500000000000 : ℝ) (100403181361/200000000000 : ℝ) (251007953407/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16891/131072 : ℝ))) 5 (100403181361/200000000000 : ℝ) (251007953407/500000000000 : ℝ) (100403181361/200000000000 : ℝ) (251007953407/500000000000 : ℝ) (100403181361/200000000000 : ℝ) (251007953407/500000000000 : ℝ) (100403181361/200000000000 : ℝ) (251007953407/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16891/131072 : ℝ))) 6 (100403181361/200000000000 : ℝ) (251007953407/500000000000 : ℝ) (100403181361/200000000000 : ℝ) (251007953407/500000000000 : ℝ) (100403181361/200000000000 : ℝ) (251007953407/500000000000 : ℝ) (100403181361/200000000000 : ℝ) (251007953407/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16891/131072 : ℝ))) 7 (100403181361/200000000000 : ℝ) (251007953407/500000000000 : ℝ) (100403181361/200000000000 : ℝ) (251007953407/500000000000 : ℝ) (100403181361/200000000000 : ℝ) (251007953407/500000000000 : ℝ) (100403181361/200000000000 : ℝ) (251007953407/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16891/131072 : ℝ)) hmem 8 (495997089931/500000000000 : ℝ) (198398835973/200000000000 : ℝ) (495997089931/500000000000 : ℝ) (198398835973/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16891/131072 : ℝ))) hcmem 8 (100403181361/200000000000 : ℝ) (251007953407/500000000000 : ℝ) (100403181361/200000000000 : ℝ) (251007953407/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16891/131072 : ℝ)) (495997089931/500000000000 : ℝ) (198398835973/200000000000 : ℝ) (100403181361/200000000000 : ℝ) (251007953407/500000000000 : ℝ) (794928799389/1000000000000 : ℝ) (794928799407/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1349_exp_lower
  have heNumeric : (1027452738239/500000000000 : ℝ)/4 ≤ Real.exp (-42628128708923/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027452738239/500000000000 : ℝ)/4 ≤ Real.exp ((33781/262144 : ℝ)-(794928799407/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33781/262144 : ℝ) (16891/131072 : ℝ) (794928799407/1000000000000 : ℝ) (1027452738239/500000000000 : ℝ) hmu.2 heBox
  · norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_leaf1325_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1325_certificate
#check SmaleRate.Proofs.cover8_leaf1326_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1326_certificate
#check SmaleRate.Proofs.cover8_leaf1327_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1327_certificate
#check SmaleRate.Proofs.cover8_leaf1328_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1328_certificate
#check SmaleRate.Proofs.cover8_leaf1329_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1329_certificate
#check SmaleRate.Proofs.cover8_leaf1330_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1330_certificate
#check SmaleRate.Proofs.cover8_leaf1331_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1331_certificate
#check SmaleRate.Proofs.cover8_leaf1332_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1332_certificate
#check SmaleRate.Proofs.cover8_leaf1333_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1333_certificate
#check SmaleRate.Proofs.cover8_leaf1334_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1334_certificate
#check SmaleRate.Proofs.cover8_leaf1335_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1335_certificate
#check SmaleRate.Proofs.cover8_leaf1336_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1336_certificate
#check SmaleRate.Proofs.cover8_leaf1337_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1337_certificate
#check SmaleRate.Proofs.cover8_leaf1338_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1338_certificate
#check SmaleRate.Proofs.cover8_leaf1339_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1339_certificate
#check SmaleRate.Proofs.cover8_leaf1340_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1340_certificate
#check SmaleRate.Proofs.cover8_leaf1341_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1341_certificate
#check SmaleRate.Proofs.cover8_leaf1342_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1342_certificate
#check SmaleRate.Proofs.cover8_leaf1343_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1343_certificate
#check SmaleRate.Proofs.cover8_leaf1344_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1344_certificate
#check SmaleRate.Proofs.cover8_leaf1345_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1345_certificate
#check SmaleRate.Proofs.cover8_leaf1346_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1346_certificate
#check SmaleRate.Proofs.cover8_leaf1347_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1347_certificate
#check SmaleRate.Proofs.cover8_leaf1348_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1348_certificate
#check SmaleRate.Proofs.cover8_leaf1349_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1349_certificate
