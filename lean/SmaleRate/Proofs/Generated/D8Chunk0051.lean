/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.AGMCertificates

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

-- Proposed record cover8_leaf1275; no trusted numerical premise.
theorem cover8_leaf1275_exp_radius : (99799286363149007/100000000000000000 : ℝ) ≤ Real.exp ((-8427/524288 : ℝ)/8) ∧ Real.exp ((-8427/524288 : ℝ)/8) ≤ (997992863631490071/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8427/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1275_exp_lower : (920113486521520013/1000000000000000000 : ℝ) ≤ Real.exp ((-42628229955557/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628229955557/64000000000000 : ℝ)/8) ≤ (460056743260760007/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628229955557/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1275_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (8026961819/3906250000 : ℝ) ≤ 4*Real.exp (33707/262144 : ℝ)*Real.exp (-mu (radius 8 (8427/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (8026961819/3906250000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8427/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1275_exp_radius
  have hrNumeric : (123006907259/125000000000 : ℝ) ≤ Real.exp (-8427/524288 : ℝ) ∧ Real.exp (-8427/524288 : ℝ) ≤ (984055258073/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (123006907259/125000000000 : ℝ) ≤ (radius 8 (8427/65536 : ℝ)) ∧ (radius 8 (8427/65536 : ℝ)) ≤ (984055258073/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8427/65536 : ℝ)) (123006907259/125000000000 : ℝ) (984055258073/1000000000000 : ℝ) (177863006437/1000000000000 : ℝ) (177863006443/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8427/65536 : ℝ)) (123006907259/125000000000 : ℝ) (984055258073/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8427/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (123006907259/125000000000 : ℝ) (984055258073/1000000000000 : ℝ) (248006907259/250000000000 : ℝ) (992027629037/1000000000000 : ℝ) (61999724611/62500000000 : ℝ) (495997796889/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8427/65536 : ℝ)) 1 (248006907259/250000000000 : ℝ) (992027629037/1000000000000 : ℝ) (61999724611/62500000000 : ℝ) (495997796889/500000000000 : ℝ) (496005805703/500000000000 : ℝ) (62000725713/62500000000 : ℝ) (248002902819/250000000000 : ℝ) (992011611279/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8427/65536 : ℝ)) 2 (496005805703/500000000000 : ℝ) (62000725713/62500000000 : ℝ) (248002902819/250000000000 : ℝ) (992011611279/1000000000000 : ℝ) (992011611341/1000000000000 : ℝ) (62000725709/62500000000 : ℝ) (49600580567/50000000000 : ℝ) (62000725709/62500000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8427/65536 : ℝ)) 3 (992011611341/1000000000000 : ℝ) (62000725709/62500000000 : ℝ) (49600580567/50000000000 : ℝ) (62000725709/62500000000 : ℝ) (49600580567/50000000000 : ℝ) (62000725709/62500000000 : ℝ) (49600580567/50000000000 : ℝ) (62000725709/62500000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8427/65536 : ℝ)) 4 (49600580567/50000000000 : ℝ) (62000725709/62500000000 : ℝ) (49600580567/50000000000 : ℝ) (62000725709/62500000000 : ℝ) (49600580567/50000000000 : ℝ) (62000725709/62500000000 : ℝ) (49600580567/50000000000 : ℝ) (62000725709/62500000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8427/65536 : ℝ)) 5 (49600580567/50000000000 : ℝ) (62000725709/62500000000 : ℝ) (49600580567/50000000000 : ℝ) (62000725709/62500000000 : ℝ) (49600580567/50000000000 : ℝ) (62000725709/62500000000 : ℝ) (49600580567/50000000000 : ℝ) (62000725709/62500000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8427/65536 : ℝ)) 6 (49600580567/50000000000 : ℝ) (62000725709/62500000000 : ℝ) (49600580567/50000000000 : ℝ) (62000725709/62500000000 : ℝ) (49600580567/50000000000 : ℝ) (62000725709/62500000000 : ℝ) (49600580567/50000000000 : ℝ) (62000725709/62500000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8427/65536 : ℝ)) 7 (49600580567/50000000000 : ℝ) (62000725709/62500000000 : ℝ) (49600580567/50000000000 : ℝ) (62000725709/62500000000 : ℝ) (49600580567/50000000000 : ℝ) (62000725709/62500000000 : ℝ) (49600580567/50000000000 : ℝ) (62000725709/62500000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8427/65536 : ℝ))) (177863006437/1000000000000 : ℝ) (177863006443/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8427/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177863006437/1000000000000 : ℝ) (177863006443/1000000000000 : ℝ) (294465751609/500000000000 : ℝ) (294465751611/500000000000 : ℝ) (210869039001/500000000000 : ℝ) (42173807801/100000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8427/65536 : ℝ))) 1 (294465751609/500000000000 : ℝ) (294465751611/500000000000 : ℝ) (210869039001/500000000000 : ℝ) (42173807801/100000000000 : ℝ) (50533479061/100000000000 : ℝ) (63166848827/125000000000 : ℝ) (249186095239/500000000000 : ℝ) (99674438097/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8427/65536 : ℝ))) 2 (50533479061/100000000000 : ℝ) (63166848827/125000000000 : ℝ) (249186095239/500000000000 : ℝ) (99674438097/200000000000 : ℝ) (31365843159/62500000000 : ℝ) (501853490551/1000000000000 : ℝ) (501841415709/1000000000000 : ℝ) (125460353929/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8427/65536 : ℝ))) 3 (31365843159/62500000000 : ℝ) (501853490551/1000000000000 : ℝ) (501841415709/1000000000000 : ℝ) (125460353929/250000000000 : ℝ) (250923726563/500000000000 : ℝ) (250923726567/500000000000 : ℝ) (50184745309/100000000000 : ℝ) (250923726549/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8427/65536 : ℝ))) 4 (250923726563/500000000000 : ℝ) (250923726567/500000000000 : ℝ) (50184745309/100000000000 : ℝ) (250923726549/500000000000 : ℝ) (125461863277/250000000000 : ℝ) (125461863279/250000000000 : ℝ) (501847453107/1000000000000 : ℝ) (125461863279/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8427/65536 : ℝ))) 5 (125461863277/250000000000 : ℝ) (125461863279/250000000000 : ℝ) (501847453107/1000000000000 : ℝ) (125461863279/250000000000 : ℝ) (501847453107/1000000000000 : ℝ) (125461863279/250000000000 : ℝ) (501847453107/1000000000000 : ℝ) (125461863279/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8427/65536 : ℝ))) 6 (501847453107/1000000000000 : ℝ) (125461863279/250000000000 : ℝ) (501847453107/1000000000000 : ℝ) (125461863279/250000000000 : ℝ) (501847453107/1000000000000 : ℝ) (125461863279/250000000000 : ℝ) (501847453107/1000000000000 : ℝ) (125461863279/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8427/65536 : ℝ))) 7 (501847453107/1000000000000 : ℝ) (125461863279/250000000000 : ℝ) (501847453107/1000000000000 : ℝ) (125461863279/250000000000 : ℝ) (501847453107/1000000000000 : ℝ) (125461863279/250000000000 : ℝ) (501847453107/1000000000000 : ℝ) (125461863279/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8427/65536 : ℝ)) hmem 8 (49600580567/50000000000 : ℝ) (62000725709/62500000000 : ℝ) (49600580567/50000000000 : ℝ) (62000725709/62500000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8427/65536 : ℝ))) hcmem 8 (501847453107/1000000000000 : ℝ) (125461863279/250000000000 : ℝ) (501847453107/1000000000000 : ℝ) (125461863279/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8427/65536 : ℝ)) (49600580567/50000000000 : ℝ) (62000725709/62500000000 : ℝ) (501847453107/1000000000000 : ℝ) (125461863279/250000000000 : ℝ) (794648093769/1000000000000 : ℝ) (198662023447/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1275_exp_lower
  have heNumeric : (8026961819/3906250000 : ℝ)/4 ≤ Real.exp (-42628229955557/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (8026961819/3906250000 : ℝ)/4 ≤ Real.exp ((33707/262144 : ℝ)-(198662023447/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33707/262144 : ℝ) (8427/65536 : ℝ) (198662023447/250000000000 : ℝ) (8026961819/3906250000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1276; no trusted numerical premise.
theorem cover8_leaf1276_exp_radius : (498996402073240859/500000000000000000 : ℝ) ≤ Real.exp ((-33709/2097152 : ℝ)/8) ∧ Real.exp ((-33709/2097152 : ℝ)/8) ≤ (997992804146481719/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33709/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1276_exp_lower : (920113488660239351/1000000000000000000 : ℝ) ≤ Real.exp ((-2131411438273/3200000000000 : ℝ)/8) ∧ Real.exp ((-2131411438273/3200000000000 : ℝ)/8) ≤ (115014186082529919/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2131411438273/3200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1276_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513725565969/250000000000 : ℝ) ≤ 4*Real.exp (8427/65536 : ℝ)*Real.exp (-mu (radius 8 (33709/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (513725565969/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33709/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1276_exp_radius
  have hrNumeric : (492027394419/500000000000 : ℝ) ≤ Real.exp (-33709/2097152 : ℝ) ∧ Real.exp (-33709/2097152 : ℝ) ≤ (984054788839/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492027394419/500000000000 : ℝ) ≤ (radius 8 (33709/262144 : ℝ)) ∧ (radius 8 (33709/262144 : ℝ)) ≤ (984054788839/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33709/262144 : ℝ)) (492027394419/500000000000 : ℝ) (984054788839/1000000000000 : ℝ) (177865602529/1000000000000 : ℝ) (35573120507/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33709/262144 : ℝ)) (492027394419/500000000000 : ℝ) (984054788839/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33709/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492027394419/500000000000 : ℝ) (984054788839/1000000000000 : ℝ) (992027394419/1000000000000 : ℝ) (49601369721/50000000000 : ℝ) (495997678633/500000000000 : ℝ) (991995357267/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33709/262144 : ℝ)) 1 (992027394419/1000000000000 : ℝ) (49601369721/50000000000 : ℝ) (495997678633/500000000000 : ℝ) (991995357267/1000000000000 : ℝ) (496005687921/500000000000 : ℝ) (248002843961/250000000000 : ℝ) (992011375713/1000000000000 : ℝ) (198402275143/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33709/262144 : ℝ)) 2 (496005687921/500000000000 : ℝ) (248002843961/250000000000 : ℝ) (992011375713/1000000000000 : ℝ) (198402275143/200000000000 : ℝ) (992011375777/1000000000000 : ℝ) (49600568789/50000000000 : ℝ) (992011375777/1000000000000 : ℝ) (49600568789/50000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33709/262144 : ℝ)) 3 (992011375777/1000000000000 : ℝ) (49600568789/50000000000 : ℝ) (992011375777/1000000000000 : ℝ) (49600568789/50000000000 : ℝ) (992011375777/1000000000000 : ℝ) (49600568789/50000000000 : ℝ) (992011375777/1000000000000 : ℝ) (49600568789/50000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33709/262144 : ℝ)) 4 (992011375777/1000000000000 : ℝ) (49600568789/50000000000 : ℝ) (992011375777/1000000000000 : ℝ) (49600568789/50000000000 : ℝ) (992011375777/1000000000000 : ℝ) (49600568789/50000000000 : ℝ) (992011375777/1000000000000 : ℝ) (49600568789/50000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33709/262144 : ℝ)) 5 (992011375777/1000000000000 : ℝ) (49600568789/50000000000 : ℝ) (992011375777/1000000000000 : ℝ) (49600568789/50000000000 : ℝ) (992011375777/1000000000000 : ℝ) (49600568789/50000000000 : ℝ) (992011375777/1000000000000 : ℝ) (49600568789/50000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33709/262144 : ℝ)) 6 (992011375777/1000000000000 : ℝ) (49600568789/50000000000 : ℝ) (992011375777/1000000000000 : ℝ) (49600568789/50000000000 : ℝ) (992011375777/1000000000000 : ℝ) (49600568789/50000000000 : ℝ) (992011375777/1000000000000 : ℝ) (49600568789/50000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33709/262144 : ℝ)) 7 (992011375777/1000000000000 : ℝ) (49600568789/50000000000 : ℝ) (992011375777/1000000000000 : ℝ) (49600568789/50000000000 : ℝ) (992011375777/1000000000000 : ℝ) (49600568789/50000000000 : ℝ) (992011375777/1000000000000 : ℝ) (49600568789/50000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33709/262144 : ℝ))) (177865602529/1000000000000 : ℝ) (35573120507/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33709/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177865602529/1000000000000 : ℝ) (35573120507/200000000000 : ℝ) (36808300079/62500000000 : ℝ) (147233200317/250000000000 : ℝ) (421741155839/1000000000000 : ℝ) (421741155847/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33709/262144 : ℝ))) 1 (36808300079/62500000000 : ℝ) (147233200317/250000000000 : ℝ) (421741155839/1000000000000 : ℝ) (421741155847/1000000000000 : ℝ) (505336978551/1000000000000 : ℝ) (252668489279/500000000000 : ℝ) (99674911651/200000000000 : ℝ) (498374558263/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33709/262144 : ℝ))) 2 (505336978551/1000000000000 : ℝ) (252668489279/500000000000 : ℝ) (99674911651/200000000000 : ℝ) (498374558263/1000000000000 : ℝ) (501855768403/1000000000000 : ℝ) (501855768411/1000000000000 : ℝ) (250921847123/500000000000 : ℝ) (100368738851/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33709/262144 : ℝ))) 3 (501855768403/1000000000000 : ℝ) (501855768411/1000000000000 : ℝ) (250921847123/500000000000 : ℝ) (100368738851/200000000000 : ℝ) (125462432831/250000000000 : ℝ) (501849731333/1000000000000 : ℝ) (62731216411/125000000000 : ℝ) (501849731297/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33709/262144 : ℝ))) 4 (125462432831/250000000000 : ℝ) (501849731333/1000000000000 : ℝ) (62731216411/125000000000 : ℝ) (501849731297/1000000000000 : ℝ) (250924865653/500000000000 : ℝ) (100369946263/200000000000 : ℝ) (100369946261/200000000000 : ℝ) (100369946263/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33709/262144 : ℝ))) 5 (250924865653/500000000000 : ℝ) (100369946263/200000000000 : ℝ) (100369946261/200000000000 : ℝ) (100369946263/200000000000 : ℝ) (100369946261/200000000000 : ℝ) (100369946263/200000000000 : ℝ) (100369946261/200000000000 : ℝ) (100369946263/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33709/262144 : ℝ))) 6 (100369946261/200000000000 : ℝ) (100369946263/200000000000 : ℝ) (100369946261/200000000000 : ℝ) (100369946263/200000000000 : ℝ) (100369946261/200000000000 : ℝ) (100369946263/200000000000 : ℝ) (100369946261/200000000000 : ℝ) (100369946263/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33709/262144 : ℝ))) 7 (100369946261/200000000000 : ℝ) (100369946263/200000000000 : ℝ) (100369946261/200000000000 : ℝ) (100369946263/200000000000 : ℝ) (100369946261/200000000000 : ℝ) (100369946263/200000000000 : ℝ) (100369946261/200000000000 : ℝ) (100369946263/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33709/262144 : ℝ)) hmem 8 (992011375777/1000000000000 : ℝ) (49600568789/50000000000 : ℝ) (992011375777/1000000000000 : ℝ) (49600568789/50000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33709/262144 : ℝ))) hcmem 8 (100369946261/200000000000 : ℝ) (100369946263/200000000000 : ℝ) (100369946261/200000000000 : ℝ) (100369946263/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33709/262144 : ℝ)) (992011375777/1000000000000 : ℝ) (49600568789/50000000000 : ℝ) (100369946261/200000000000 : ℝ) (100369946263/200000000000 : ℝ) (79465188987/100000000000 : ℝ) (79465188989/100000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1276_exp_lower
  have heNumeric : (513725565969/250000000000 : ℝ)/4 ≤ Real.exp (-2131411438273/3200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513725565969/250000000000 : ℝ)/4 ≤ Real.exp ((8427/65536 : ℝ)-(79465188989/100000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8427/65536 : ℝ) (33709/262144 : ℝ) (79465188989/100000000000 : ℝ) (513725565969/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1277; no trusted numerical premise.
theorem cover8_leaf1277_exp_radius : (997992744661476911/1000000000000000000 : ℝ) ≤ Real.exp ((-16855/1048576 : ℝ)/8) ∧ Real.exp ((-16855/1048576 : ℝ)/8) ≤ (62374546541342307/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16855/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1277_exp_lower : (230028372701924943/250000000000000000 : ℝ) ≤ Real.exp ((-42628227570499/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628227570499/64000000000000 : ℝ)/8) ≤ (920113490807699773/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628227570499/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1277_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902302243/1000000000000 : ℝ) ≤ 4*Real.exp (33709/262144 : ℝ)*Real.exp (-mu (radius 8 (16855/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902302243/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16855/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1277_exp_radius
  have hrNumeric : (246013579901/250000000000 : ℝ) ≤ Real.exp (-16855/1048576 : ℝ) ∧ Real.exp (-16855/1048576 : ℝ) ≤ (196810863921/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246013579901/250000000000 : ℝ) ≤ (radius 8 (16855/131072 : ℝ)) ∧ (radius 8 (16855/131072 : ℝ)) ≤ (196810863921/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16855/131072 : ℝ)) (246013579901/250000000000 : ℝ) (196810863921/200000000000 : ℝ) (177868198581/1000000000000 : ℝ) (44467049647/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16855/131072 : ℝ)) (246013579901/250000000000 : ℝ) (196810863921/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16855/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246013579901/250000000000 : ℝ) (196810863921/200000000000 : ℝ) (496013579901/500000000000 : ℝ) (992027159803/1000000000000 : ℝ) (247998780189/250000000000 : ℝ) (991995120757/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16855/131072 : ℝ)) 1 (496013579901/500000000000 : ℝ) (992027159803/1000000000000 : ℝ) (247998780189/250000000000 : ℝ) (991995120757/1000000000000 : ℝ) (992011140279/1000000000000 : ℝ) (24800278507/25000000000 : ℝ) (992011140149/1000000000000 : ℝ) (992011140151/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16855/131072 : ℝ)) 2 (992011140279/1000000000000 : ℝ) (24800278507/25000000000 : ℝ) (992011140149/1000000000000 : ℝ) (992011140151/1000000000000 : ℝ) (496005570107/500000000000 : ℝ) (124001392527/125000000000 : ℝ) (992011140213/1000000000000 : ℝ) (124001392527/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16855/131072 : ℝ)) 3 (496005570107/500000000000 : ℝ) (124001392527/125000000000 : ℝ) (992011140213/1000000000000 : ℝ) (124001392527/125000000000 : ℝ) (992011140213/1000000000000 : ℝ) (124001392527/125000000000 : ℝ) (992011140213/1000000000000 : ℝ) (124001392527/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16855/131072 : ℝ)) 4 (992011140213/1000000000000 : ℝ) (124001392527/125000000000 : ℝ) (992011140213/1000000000000 : ℝ) (124001392527/125000000000 : ℝ) (992011140213/1000000000000 : ℝ) (124001392527/125000000000 : ℝ) (992011140213/1000000000000 : ℝ) (124001392527/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16855/131072 : ℝ)) 5 (992011140213/1000000000000 : ℝ) (124001392527/125000000000 : ℝ) (992011140213/1000000000000 : ℝ) (124001392527/125000000000 : ℝ) (992011140213/1000000000000 : ℝ) (124001392527/125000000000 : ℝ) (992011140213/1000000000000 : ℝ) (124001392527/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16855/131072 : ℝ)) 6 (992011140213/1000000000000 : ℝ) (124001392527/125000000000 : ℝ) (992011140213/1000000000000 : ℝ) (124001392527/125000000000 : ℝ) (992011140213/1000000000000 : ℝ) (124001392527/125000000000 : ℝ) (992011140213/1000000000000 : ℝ) (124001392527/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16855/131072 : ℝ)) 7 (992011140213/1000000000000 : ℝ) (124001392527/125000000000 : ℝ) (992011140213/1000000000000 : ℝ) (124001392527/125000000000 : ℝ) (992011140213/1000000000000 : ℝ) (124001392527/125000000000 : ℝ) (992011140213/1000000000000 : ℝ) (124001392527/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16855/131072 : ℝ))) (177868198581/1000000000000 : ℝ) (44467049647/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16855/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177868198581/1000000000000 : ℝ) (44467049647/250000000000 : ℝ) (58893409929/100000000000 : ℝ) (294467049647/500000000000 : ℝ) (421744233607/1000000000000 : ℝ) (26359014601/62500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16855/131072 : ℝ))) 1 (58893409929/100000000000 : ℝ) (294467049647/500000000000 : ℝ) (421744233607/1000000000000 : ℝ) (26359014601/62500000000 : ℝ) (31583697903/62500000000 : ℝ) (101067833291/200000000000 : ℝ) (24918846299/50000000000 : ℝ) (124594231497/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16855/131072 : ℝ))) 2 (31583697903/62500000000 : ℝ) (101067833291/200000000000 : ℝ) (24918846299/50000000000 : ℝ) (124594231497/250000000000 : ℝ) (250929023107/500000000000 : ℝ) (250929023111/500000000000 : ℝ) (1960335831/3906250000 : ℝ) (62730746593/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16855/131072 : ℝ))) 3 (250929023107/500000000000 : ℝ) (250929023111/500000000000 : ℝ) (1960335831/3906250000 : ℝ) (62730746593/125000000000 : ℝ) (20074080379/40000000000 : ℝ) (501852009483/1000000000000 : ℝ) (250926004719/500000000000 : ℝ) (501852009447/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16855/131072 : ℝ))) 4 (20074080379/40000000000 : ℝ) (501852009483/1000000000000 : ℝ) (250926004719/500000000000 : ℝ) (501852009447/1000000000000 : ℝ) (31365750591/62500000000 : ℝ) (100370401893/200000000000 : ℝ) (31365750591/62500000000 : ℝ) (100370401893/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16855/131072 : ℝ))) 5 (31365750591/62500000000 : ℝ) (100370401893/200000000000 : ℝ) (31365750591/62500000000 : ℝ) (100370401893/200000000000 : ℝ) (31365750591/62500000000 : ℝ) (100370401893/200000000000 : ℝ) (31365750591/62500000000 : ℝ) (100370401893/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16855/131072 : ℝ))) 6 (31365750591/62500000000 : ℝ) (100370401893/200000000000 : ℝ) (31365750591/62500000000 : ℝ) (100370401893/200000000000 : ℝ) (31365750591/62500000000 : ℝ) (100370401893/200000000000 : ℝ) (31365750591/62500000000 : ℝ) (100370401893/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16855/131072 : ℝ))) 7 (31365750591/62500000000 : ℝ) (100370401893/200000000000 : ℝ) (31365750591/62500000000 : ℝ) (100370401893/200000000000 : ℝ) (31365750591/62500000000 : ℝ) (100370401893/200000000000 : ℝ) (31365750591/62500000000 : ℝ) (100370401893/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16855/131072 : ℝ)) hmem 8 (992011140213/1000000000000 : ℝ) (124001392527/125000000000 : ℝ) (992011140213/1000000000000 : ℝ) (124001392527/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16855/131072 : ℝ))) hcmem 8 (31365750591/62500000000 : ℝ) (100370401893/200000000000 : ℝ) (31365750591/62500000000 : ℝ) (100370401893/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16855/131072 : ℝ)) (992011140213/1000000000000 : ℝ) (124001392527/125000000000 : ℝ) (31365750591/62500000000 : ℝ) (100370401893/200000000000 : ℝ) (794655685899/1000000000000 : ℝ) (198663921479/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1277_exp_lower
  have heNumeric : (2054902302243/1000000000000 : ℝ)/4 ≤ Real.exp (-42628227570499/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902302243/1000000000000 : ℝ)/4 ≤ Real.exp ((33709/262144 : ℝ)-(198663921479/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33709/262144 : ℝ) (16855/131072 : ℝ) (198663921479/250000000000 : ℝ) (2054902302243/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1278; no trusted numerical premise.
theorem cover8_leaf1278_exp_radius : (19959853703529513/20000000000000000 : ℝ) ≤ Real.exp ((-33711/2097152 : ℝ)/8) ∧ Real.exp ((-33711/2097152 : ℝ)/8) ≤ (997992685176475651/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33711/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1278_exp_lower : (460056746482065653/500000000000000000 : ℝ) ≤ Real.exp ((-21314113185273/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314113185273/32000000000000 : ℝ)/8) ≤ (920113492964131307/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314113185273/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1278_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902340771/1000000000000 : ℝ) ≤ 4*Real.exp (16855/131072 : ℝ)*Real.exp (-mu (radius 8 (33711/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902340771/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33711/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1278_exp_radius
  have hrNumeric : (984053850371/1000000000000 : ℝ) ≤ Real.exp (-33711/2097152 : ℝ) ∧ Real.exp (-33711/2097152 : ℝ) ≤ (246013462593/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984053850371/1000000000000 : ℝ) ≤ (radius 8 (33711/262144 : ℝ)) ∧ (radius 8 (33711/262144 : ℝ)) ≤ (246013462593/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33711/262144 : ℝ)) (984053850371/1000000000000 : ℝ) (246013462593/250000000000 : ℝ) (177870794589/1000000000000 : ℝ) (44467698649/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33711/262144 : ℝ)) (984053850371/1000000000000 : ℝ) (246013462593/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33711/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984053850371/1000000000000 : ℝ) (246013462593/250000000000 : ℝ) (198405385037/200000000000 : ℝ) (496013462593/500000000000 : ℝ) (495997442123/500000000000 : ℝ) (991994884247/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33711/262144 : ℝ)) 1 (198405385037/200000000000 : ℝ) (496013462593/500000000000 : ℝ) (495997442123/500000000000 : ℝ) (991994884247/1000000000000 : ℝ) (198402180943/200000000000 : ℝ) (992010904717/1000000000000 : ℝ) (496005452293/500000000000 : ℝ) (248002726147/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33711/262144 : ℝ)) 2 (198402180943/200000000000 : ℝ) (992010904717/1000000000000 : ℝ) (496005452293/500000000000 : ℝ) (248002726147/250000000000 : ℝ) (19840218093/20000000000 : ℝ) (992010904653/1000000000000 : ℝ) (19840218093/20000000000 : ℝ) (992010904653/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33711/262144 : ℝ)) 3 (19840218093/20000000000 : ℝ) (992010904653/1000000000000 : ℝ) (19840218093/20000000000 : ℝ) (992010904653/1000000000000 : ℝ) (19840218093/20000000000 : ℝ) (992010904653/1000000000000 : ℝ) (19840218093/20000000000 : ℝ) (992010904653/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33711/262144 : ℝ)) 4 (19840218093/20000000000 : ℝ) (992010904653/1000000000000 : ℝ) (19840218093/20000000000 : ℝ) (992010904653/1000000000000 : ℝ) (19840218093/20000000000 : ℝ) (992010904653/1000000000000 : ℝ) (19840218093/20000000000 : ℝ) (992010904653/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33711/262144 : ℝ)) 5 (19840218093/20000000000 : ℝ) (992010904653/1000000000000 : ℝ) (19840218093/20000000000 : ℝ) (992010904653/1000000000000 : ℝ) (19840218093/20000000000 : ℝ) (992010904653/1000000000000 : ℝ) (19840218093/20000000000 : ℝ) (992010904653/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33711/262144 : ℝ)) 6 (19840218093/20000000000 : ℝ) (992010904653/1000000000000 : ℝ) (19840218093/20000000000 : ℝ) (992010904653/1000000000000 : ℝ) (19840218093/20000000000 : ℝ) (992010904653/1000000000000 : ℝ) (19840218093/20000000000 : ℝ) (992010904653/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33711/262144 : ℝ)) 7 (19840218093/20000000000 : ℝ) (992010904653/1000000000000 : ℝ) (19840218093/20000000000 : ℝ) (992010904653/1000000000000 : ℝ) (19840218093/20000000000 : ℝ) (992010904653/1000000000000 : ℝ) (19840218093/20000000000 : ℝ) (992010904653/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33711/262144 : ℝ))) (177870794589/1000000000000 : ℝ) (44467698649/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33711/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177870794589/1000000000000 : ℝ) (44467698649/250000000000 : ℝ) (294467698647/500000000000 : ℝ) (294467698649/500000000000 : ℝ) (4217473113/10000000000 : ℝ) (421747311309/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33711/262144 : ℝ))) 1 (294467698647/500000000000 : ℝ) (294467698649/500000000000 : ℝ) (4217473113/10000000000 : ℝ) (421747311309/1000000000000 : ℝ) (505341354297/1000000000000 : ℝ) (7895958661/15625000000 : ℝ) (498379293649/1000000000000 : ℝ) (498379293657/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33711/262144 : ℝ))) 2 (505341354297/1000000000000 : ℝ) (7895958661/15625000000 : ℝ) (498379293649/1000000000000 : ℝ) (498379293657/1000000000000 : ℝ) (501860323973/1000000000000 : ℝ) (501860323981/1000000000000 : ℝ) (501848251173/1000000000000 : ℝ) (250924125591/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33711/262144 : ℝ))) 3 (501860323973/1000000000000 : ℝ) (501860323981/1000000000000 : ℝ) (501848251173/1000000000000 : ℝ) (250924125591/500000000000 : ℝ) (501854287573/1000000000000 : ℝ) (250927143791/500000000000 : ℝ) (31365892971/62500000000 : ℝ) (250927143773/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33711/262144 : ℝ))) 4 (501854287573/1000000000000 : ℝ) (250927143791/500000000000 : ℝ) (31365892971/62500000000 : ℝ) (250927143773/500000000000 : ℝ) (250927143777/500000000000 : ℝ) (125463571891/250000000000 : ℝ) (250927143777/500000000000 : ℝ) (125463571891/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33711/262144 : ℝ))) 5 (250927143777/500000000000 : ℝ) (125463571891/250000000000 : ℝ) (250927143777/500000000000 : ℝ) (125463571891/250000000000 : ℝ) (250927143777/500000000000 : ℝ) (125463571891/250000000000 : ℝ) (250927143777/500000000000 : ℝ) (125463571891/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33711/262144 : ℝ))) 6 (250927143777/500000000000 : ℝ) (125463571891/250000000000 : ℝ) (250927143777/500000000000 : ℝ) (125463571891/250000000000 : ℝ) (250927143777/500000000000 : ℝ) (125463571891/250000000000 : ℝ) (250927143777/500000000000 : ℝ) (125463571891/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33711/262144 : ℝ))) 7 (250927143777/500000000000 : ℝ) (125463571891/250000000000 : ℝ) (250927143777/500000000000 : ℝ) (125463571891/250000000000 : ℝ) (250927143777/500000000000 : ℝ) (125463571891/250000000000 : ℝ) (250927143777/500000000000 : ℝ) (125463571891/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33711/262144 : ℝ)) hmem 8 (19840218093/20000000000 : ℝ) (992010904653/1000000000000 : ℝ) (19840218093/20000000000 : ℝ) (992010904653/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33711/262144 : ℝ))) hcmem 8 (250927143777/500000000000 : ℝ) (125463571891/250000000000 : ℝ) (250927143777/500000000000 : ℝ) (125463571891/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33711/262144 : ℝ)) (19840218093/20000000000 : ℝ) (992010904653/1000000000000 : ℝ) (250927143777/500000000000 : ℝ) (125463571891/250000000000 : ℝ) (198664870461/250000000000 : ℝ) (99332435233/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1278_exp_lower
  have heNumeric : (2054902340771/1000000000000 : ℝ)/4 ≤ Real.exp (-21314113185273/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902340771/1000000000000 : ℝ)/4 ≤ Real.exp ((16855/131072 : ℝ)-(99332435233/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16855/131072 : ℝ) (33711/262144 : ℝ) (99332435233/125000000000 : ℝ) (2054902340771/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1279; no trusted numerical premise.
theorem cover8_leaf1279_exp_radius : (199598525138295587/200000000000000000 : ℝ) ≤ Real.exp ((-2107/131072 : ℝ)/8) ∧ Real.exp ((-2107/131072 : ℝ)/8) ≤ (62374539105717371/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2107/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1279_exp_lower : (920113495128728851/1000000000000000000 : ℝ) ≤ Real.exp ((-42628225166049/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628225166049/64000000000000 : ℝ)/8) ≤ (230028373782182213/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628225166049/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1279_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410980475889/200000000000 : ℝ) ≤ 4*Real.exp (33711/262144 : ℝ)*Real.exp (-mu (radius 8 (2107/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (410980475889/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2107/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1279_exp_radius
  have hrNumeric : (984053381137/1000000000000 : ℝ) ≤ Real.exp (-2107/131072 : ℝ) ∧ Real.exp (-2107/131072 : ℝ) ≤ (492026690569/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984053381137/1000000000000 : ℝ) ≤ (radius 8 (2107/16384 : ℝ)) ∧ (radius 8 (2107/16384 : ℝ)) ≤ (492026690569/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2107/16384 : ℝ)) (984053381137/1000000000000 : ℝ) (492026690569/500000000000 : ℝ) (44468347641/250000000000 : ℝ) (17787339057/100000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2107/16384 : ℝ)) (984053381137/1000000000000 : ℝ) (492026690569/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2107/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984053381137/1000000000000 : ℝ) (492026690569/500000000000 : ℝ) (124003336321/125000000000 : ℝ) (992026690569/1000000000000 : ℝ) (123999330967/125000000000 : ℝ) (991994647737/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2107/16384 : ℝ)) 1 (124003336321/125000000000 : ℝ) (992026690569/1000000000000 : ℝ) (123999330967/125000000000 : ℝ) (991994647737/1000000000000 : ℝ) (31000333411/31250000000 : ℝ) (992010669153/1000000000000 : ℝ) (496005334511/500000000000 : ℝ) (31000333407/31250000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2107/16384 : ℝ)) 2 (31000333411/31250000000 : ℝ) (992010669153/1000000000000 : ℝ) (496005334511/500000000000 : ℝ) (31000333407/31250000000 : ℝ) (992010669087/1000000000000 : ℝ) (992010669089/1000000000000 : ℝ) (496005334543/500000000000 : ℝ) (992010669089/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2107/16384 : ℝ)) 3 (992010669087/1000000000000 : ℝ) (992010669089/1000000000000 : ℝ) (496005334543/500000000000 : ℝ) (992010669089/1000000000000 : ℝ) (496005334543/500000000000 : ℝ) (992010669089/1000000000000 : ℝ) (496005334543/500000000000 : ℝ) (992010669089/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2107/16384 : ℝ)) 4 (496005334543/500000000000 : ℝ) (992010669089/1000000000000 : ℝ) (496005334543/500000000000 : ℝ) (992010669089/1000000000000 : ℝ) (496005334543/500000000000 : ℝ) (992010669089/1000000000000 : ℝ) (496005334543/500000000000 : ℝ) (992010669089/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2107/16384 : ℝ)) 5 (496005334543/500000000000 : ℝ) (992010669089/1000000000000 : ℝ) (496005334543/500000000000 : ℝ) (992010669089/1000000000000 : ℝ) (496005334543/500000000000 : ℝ) (992010669089/1000000000000 : ℝ) (496005334543/500000000000 : ℝ) (992010669089/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2107/16384 : ℝ)) 6 (496005334543/500000000000 : ℝ) (992010669089/1000000000000 : ℝ) (496005334543/500000000000 : ℝ) (992010669089/1000000000000 : ℝ) (496005334543/500000000000 : ℝ) (992010669089/1000000000000 : ℝ) (496005334543/500000000000 : ℝ) (992010669089/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2107/16384 : ℝ)) 7 (496005334543/500000000000 : ℝ) (992010669089/1000000000000 : ℝ) (496005334543/500000000000 : ℝ) (992010669089/1000000000000 : ℝ) (496005334543/500000000000 : ℝ) (992010669089/1000000000000 : ℝ) (496005334543/500000000000 : ℝ) (992010669089/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2107/16384 : ℝ))) (44468347641/250000000000 : ℝ) (17787339057/100000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2107/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44468347641/250000000000 : ℝ) (17787339057/100000000000 : ℝ) (294468347641/500000000000 : ℝ) (117787339057/200000000000 : ℝ) (421750388931/1000000000000 : ℝ) (421750388939/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2107/16384 : ℝ))) 1 (294468347641/500000000000 : ℝ) (117787339057/200000000000 : ℝ) (421750388931/1000000000000 : ℝ) (421750388939/1000000000000 : ℝ) (252671771053/500000000000 : ℝ) (15791985691/31250000000 : ℝ) (49838166127/100000000000 : ℝ) (498381661277/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2107/16384 : ℝ))) 2 (252671771053/500000000000 : ℝ) (15791985691/31250000000 : ℝ) (49838166127/100000000000 : ℝ) (498381661277/1000000000000 : ℝ) (62732825211/125000000000 : ℝ) (100372520339/200000000000 : ℝ) (501850529567/1000000000000 : ℝ) (250925264787/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2107/16384 : ℝ))) 3 (62732825211/125000000000 : ℝ) (100372520339/200000000000 : ℝ) (501850529567/1000000000000 : ℝ) (250925264787/500000000000 : ℝ) (501856565627/1000000000000 : ℝ) (100371313127/200000000000 : ℝ) (501856565591/1000000000000 : ℝ) (501856565599/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2107/16384 : ℝ))) 4 (501856565627/1000000000000 : ℝ) (100371313127/200000000000 : ℝ) (501856565591/1000000000000 : ℝ) (501856565599/1000000000000 : ℝ) (501856565609/1000000000000 : ℝ) (501856565617/1000000000000 : ℝ) (62732070701/125000000000 : ℝ) (501856565617/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2107/16384 : ℝ))) 5 (501856565609/1000000000000 : ℝ) (501856565617/1000000000000 : ℝ) (62732070701/125000000000 : ℝ) (501856565617/1000000000000 : ℝ) (62732070701/125000000000 : ℝ) (501856565617/1000000000000 : ℝ) (62732070701/125000000000 : ℝ) (501856565617/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2107/16384 : ℝ))) 6 (62732070701/125000000000 : ℝ) (501856565617/1000000000000 : ℝ) (62732070701/125000000000 : ℝ) (501856565617/1000000000000 : ℝ) (62732070701/125000000000 : ℝ) (501856565617/1000000000000 : ℝ) (62732070701/125000000000 : ℝ) (501856565617/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2107/16384 : ℝ))) 7 (62732070701/125000000000 : ℝ) (501856565617/1000000000000 : ℝ) (62732070701/125000000000 : ℝ) (501856565617/1000000000000 : ℝ) (62732070701/125000000000 : ℝ) (501856565617/1000000000000 : ℝ) (62732070701/125000000000 : ℝ) (501856565617/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2107/16384 : ℝ)) hmem 8 (496005334543/500000000000 : ℝ) (992010669089/1000000000000 : ℝ) (496005334543/500000000000 : ℝ) (992010669089/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2107/16384 : ℝ))) hcmem 8 (62732070701/125000000000 : ℝ) (501856565617/1000000000000 : ℝ) (62732070701/125000000000 : ℝ) (501856565617/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2107/16384 : ℝ)) (496005334543/500000000000 : ℝ) (992010669089/1000000000000 : ℝ) (62732070701/125000000000 : ℝ) (501856565617/1000000000000 : ℝ) (794663277723/1000000000000 : ℝ) (794663277741/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1279_exp_lower
  have heNumeric : (410980475889/200000000000 : ℝ)/4 ≤ Real.exp (-42628225166049/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410980475889/200000000000 : ℝ)/4 ≤ Real.exp ((33711/262144 : ℝ)-(794663277741/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33711/262144 : ℝ) (2107/16384 : ℝ) (794663277741/1000000000000 : ℝ) (410980475889/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1280; no trusted numerical premise.
theorem cover8_leaf1280_exp_radius : (199598513241296753/200000000000000000 : ℝ) ≤ Real.exp ((-33713/2097152 : ℝ)/8) ∧ Real.exp ((-33713/2097152 : ℝ)/8) ≤ (498996283103241883/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33713/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1280_exp_lower : (57507093581407971/62500000000000000 : ℝ) ≤ Real.exp ((-2664263997277/4000000000000 : ℝ)/8) ∧ Real.exp ((-2664263997277/4000000000000 : ℝ)/8) ≤ (920113497302527537/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2664263997277/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1280_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902418283/1000000000000 : ℝ) ≤ 4*Real.exp (2107/16384 : ℝ)*Real.exp (-mu (radius 8 (33713/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902418283/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33713/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1280_exp_radius
  have hrNumeric : (30751653497/31250000000 : ℝ) ≤ Real.exp (-33713/2097152 : ℝ) ∧ Real.exp (-33713/2097152 : ℝ) ≤ (196810582381/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (30751653497/31250000000 : ℝ) ≤ (radius 8 (33713/262144 : ℝ)) ∧ (radius 8 (33713/262144 : ℝ)) ≤ (196810582381/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33713/262144 : ℝ)) (30751653497/31250000000 : ℝ) (196810582381/200000000000 : ℝ) (88937993247/500000000000 : ℝ) (355751973/2000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33713/262144 : ℝ)) (30751653497/31250000000 : ℝ) (196810582381/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33713/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (30751653497/31250000000 : ℝ) (196810582381/200000000000 : ℝ) (62001653497/62500000000 : ℝ) (992026455953/1000000000000 : ℝ) (495997205613/500000000000 : ℝ) (991994411227/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33713/262144 : ℝ)) 1 (62001653497/62500000000 : ℝ) (992026455953/1000000000000 : ℝ) (495997205613/500000000000 : ℝ) (991994411227/1000000000000 : ℝ) (992010433589/1000000000000 : ℝ) (99201043359/100000000000 : ℝ) (992010433459/1000000000000 : ℝ) (992010433461/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33713/262144 : ℝ)) 2 (992010433589/1000000000000 : ℝ) (99201043359/100000000000 : ℝ) (992010433459/1000000000000 : ℝ) (992010433461/1000000000000 : ℝ) (248002608381/250000000000 : ℝ) (496005216763/500000000000 : ℝ) (992010433523/1000000000000 : ℝ) (496005216763/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33713/262144 : ℝ)) 3 (248002608381/250000000000 : ℝ) (496005216763/500000000000 : ℝ) (992010433523/1000000000000 : ℝ) (496005216763/500000000000 : ℝ) (992010433523/1000000000000 : ℝ) (496005216763/500000000000 : ℝ) (992010433523/1000000000000 : ℝ) (496005216763/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33713/262144 : ℝ)) 4 (992010433523/1000000000000 : ℝ) (496005216763/500000000000 : ℝ) (992010433523/1000000000000 : ℝ) (496005216763/500000000000 : ℝ) (992010433523/1000000000000 : ℝ) (496005216763/500000000000 : ℝ) (992010433523/1000000000000 : ℝ) (496005216763/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33713/262144 : ℝ)) 5 (992010433523/1000000000000 : ℝ) (496005216763/500000000000 : ℝ) (992010433523/1000000000000 : ℝ) (496005216763/500000000000 : ℝ) (992010433523/1000000000000 : ℝ) (496005216763/500000000000 : ℝ) (992010433523/1000000000000 : ℝ) (496005216763/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33713/262144 : ℝ)) 6 (992010433523/1000000000000 : ℝ) (496005216763/500000000000 : ℝ) (992010433523/1000000000000 : ℝ) (496005216763/500000000000 : ℝ) (992010433523/1000000000000 : ℝ) (496005216763/500000000000 : ℝ) (992010433523/1000000000000 : ℝ) (496005216763/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33713/262144 : ℝ)) 7 (992010433523/1000000000000 : ℝ) (496005216763/500000000000 : ℝ) (992010433523/1000000000000 : ℝ) (496005216763/500000000000 : ℝ) (992010433523/1000000000000 : ℝ) (496005216763/500000000000 : ℝ) (992010433523/1000000000000 : ℝ) (496005216763/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33713/262144 : ℝ))) (88937993247/500000000000 : ℝ) (355751973/2000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33713/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88937993247/500000000000 : ℝ) (355751973/2000000000 : ℝ) (588937993247/1000000000000 : ℝ) (2355751973/4000000000 : ℝ) (421753466487/1000000000000 : ℝ) (84350693299/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33713/262144 : ℝ))) 1 (588937993247/1000000000000 : ℝ) (2355751973/4000000000 : ℝ) (421753466487/1000000000000 : ℝ) (84350693299/200000000000 : ℝ) (505345729867/1000000000000 : ℝ) (505345729873/1000000000000 : ℝ) (99676805767/200000000000 : ℝ) (249192014421/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33713/262144 : ℝ))) 2 (505345729867/1000000000000 : ℝ) (505345729873/1000000000000 : ℝ) (99676805767/200000000000 : ℝ) (249192014421/500000000000 : ℝ) (501864879351/1000000000000 : ℝ) (250932439679/500000000000 : ℝ) (125463201977/250000000000 : ℝ) (125463201979/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33713/262144 : ℝ))) 3 (501864879351/1000000000000 : ℝ) (250932439679/500000000000 : ℝ) (125463201977/250000000000 : ℝ) (125463201979/250000000000 : ℝ) (501858843629/1000000000000 : ℝ) (501858843637/1000000000000 : ℝ) (501858843593/1000000000000 : ℝ) (501858843601/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33713/262144 : ℝ))) 4 (501858843629/1000000000000 : ℝ) (501858843637/1000000000000 : ℝ) (501858843593/1000000000000 : ℝ) (501858843601/1000000000000 : ℝ) (501858843611/1000000000000 : ℝ) (501858843619/1000000000000 : ℝ) (50185884361/100000000000 : ℝ) (501858843619/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33713/262144 : ℝ))) 5 (501858843611/1000000000000 : ℝ) (501858843619/1000000000000 : ℝ) (50185884361/100000000000 : ℝ) (501858843619/1000000000000 : ℝ) (50185884361/100000000000 : ℝ) (501858843619/1000000000000 : ℝ) (50185884361/100000000000 : ℝ) (501858843619/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33713/262144 : ℝ))) 6 (50185884361/100000000000 : ℝ) (501858843619/1000000000000 : ℝ) (50185884361/100000000000 : ℝ) (501858843619/1000000000000 : ℝ) (50185884361/100000000000 : ℝ) (501858843619/1000000000000 : ℝ) (50185884361/100000000000 : ℝ) (501858843619/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33713/262144 : ℝ))) 7 (50185884361/100000000000 : ℝ) (501858843619/1000000000000 : ℝ) (50185884361/100000000000 : ℝ) (501858843619/1000000000000 : ℝ) (50185884361/100000000000 : ℝ) (501858843619/1000000000000 : ℝ) (50185884361/100000000000 : ℝ) (501858843619/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33713/262144 : ℝ)) hmem 8 (992010433523/1000000000000 : ℝ) (496005216763/500000000000 : ℝ) (992010433523/1000000000000 : ℝ) (496005216763/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33713/262144 : ℝ))) hcmem 8 (50185884361/100000000000 : ℝ) (501858843619/1000000000000 : ℝ) (50185884361/100000000000 : ℝ) (501858843619/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33713/262144 : ℝ)) (992010433523/1000000000000 : ℝ) (496005216763/500000000000 : ℝ) (50185884361/100000000000 : ℝ) (501858843619/1000000000000 : ℝ) (9933338419/12500000000 : ℝ) (397333536769/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1280_exp_lower
  have heNumeric : (2054902418283/1000000000000 : ℝ)/4 ≤ Real.exp (-2664263997277/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902418283/1000000000000 : ℝ)/4 ≤ Real.exp ((2107/16384 : ℝ)-(397333536769/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2107/16384 : ℝ) (33713/262144 : ℝ) (397333536769/500000000000 : ℝ) (2054902418283/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1281; no trusted numerical premise.
theorem cover8_leaf1281_exp_radius : (49899625336074657/50000000000000000 : ℝ) ≤ Real.exp ((-16857/1048576 : ℝ)/8) ∧ Real.exp ((-16857/1048576 : ℝ)/8) ≤ (997992506721493141/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16857/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1281_exp_lower : (184022699897013461/200000000000000000 : ℝ) ≤ Real.exp ((-42628222741951/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628222741951/64000000000000 : ℝ)/8) ≤ (460056749742533653/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628222741951/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1281_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451228639/500000000000 : ℝ) ≤ 4*Real.exp (33713/262144 : ℝ)*Real.exp (-mu (radius 8 (16857/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451228639/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16857/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1281_exp_radius
  have hrNumeric : (984052442671/1000000000000 : ℝ) ≤ Real.exp (-16857/1048576 : ℝ) ∧ Real.exp (-16857/1048576 : ℝ) ≤ (61503277667/62500000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984052442671/1000000000000 : ℝ) ≤ (radius 8 (16857/131072 : ℝ)) ∧ (radius 8 (16857/131072 : ℝ)) ≤ (61503277667/62500000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16857/131072 : ℝ)) (984052442671/1000000000000 : ℝ) (61503277667/62500000000 : ℝ) (11117411399/62500000000 : ℝ) (177878582391/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16857/131072 : ℝ)) (984052442671/1000000000000 : ℝ) (61503277667/62500000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16857/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984052442671/1000000000000 : ℝ) (61503277667/62500000000 : ℝ) (198405244267/200000000000 : ℝ) (124003277667/125000000000 : ℝ) (247998543679/250000000000 : ℝ) (991994174717/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16857/131072 : ℝ)) 1 (198405244267/200000000000 : ℝ) (124003277667/125000000000 : ℝ) (247998543679/250000000000 : ℝ) (991994174717/1000000000000 : ℝ) (39680407921/40000000000 : ℝ) (992010198027/1000000000000 : ℝ) (124001274737/125000000000 : ℝ) (496005098949/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16857/131072 : ℝ)) 2 (39680407921/40000000000 : ℝ) (992010198027/1000000000000 : ℝ) (124001274737/125000000000 : ℝ) (496005098949/500000000000 : ℝ) (24800254949/25000000000 : ℝ) (992010197963/1000000000000 : ℝ) (24800254949/25000000000 : ℝ) (992010197963/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16857/131072 : ℝ)) 3 (24800254949/25000000000 : ℝ) (992010197963/1000000000000 : ℝ) (24800254949/25000000000 : ℝ) (992010197963/1000000000000 : ℝ) (24800254949/25000000000 : ℝ) (992010197963/1000000000000 : ℝ) (24800254949/25000000000 : ℝ) (992010197963/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16857/131072 : ℝ)) 4 (24800254949/25000000000 : ℝ) (992010197963/1000000000000 : ℝ) (24800254949/25000000000 : ℝ) (992010197963/1000000000000 : ℝ) (24800254949/25000000000 : ℝ) (992010197963/1000000000000 : ℝ) (24800254949/25000000000 : ℝ) (992010197963/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16857/131072 : ℝ)) 5 (24800254949/25000000000 : ℝ) (992010197963/1000000000000 : ℝ) (24800254949/25000000000 : ℝ) (992010197963/1000000000000 : ℝ) (24800254949/25000000000 : ℝ) (992010197963/1000000000000 : ℝ) (24800254949/25000000000 : ℝ) (992010197963/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16857/131072 : ℝ)) 6 (24800254949/25000000000 : ℝ) (992010197963/1000000000000 : ℝ) (24800254949/25000000000 : ℝ) (992010197963/1000000000000 : ℝ) (24800254949/25000000000 : ℝ) (992010197963/1000000000000 : ℝ) (24800254949/25000000000 : ℝ) (992010197963/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16857/131072 : ℝ)) 7 (24800254949/25000000000 : ℝ) (992010197963/1000000000000 : ℝ) (24800254949/25000000000 : ℝ) (992010197963/1000000000000 : ℝ) (24800254949/25000000000 : ℝ) (992010197963/1000000000000 : ℝ) (24800254949/25000000000 : ℝ) (992010197963/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16857/131072 : ℝ))) (11117411399/62500000000 : ℝ) (177878582391/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16857/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (11117411399/62500000000 : ℝ) (177878582391/1000000000000 : ℝ) (73617411399/125000000000 : ℝ) (147234822799/250000000000 : ℝ) (105439135993/250000000000 : ℝ) (210878271991/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16857/131072 : ℝ))) 1 (73617411399/125000000000 : ℝ) (147234822799/250000000000 : ℝ) (105439135993/250000000000 : ℝ) (210878271991/500000000000 : ℝ) (252673958791/500000000000 : ℝ) (505347917589/1000000000000 : ℝ) (99677279269/200000000000 : ℝ) (249193198177/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16857/131072 : ℝ))) 2 (252673958791/500000000000 : ℝ) (505347917589/1000000000000 : ℝ) (99677279269/200000000000 : ℝ) (249193198177/500000000000 : ℝ) (501867156963/1000000000000 : ℝ) (125466789243/250000000000 : ℝ) (501855086199/1000000000000 : ℝ) (3920742861/7812500000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16857/131072 : ℝ))) 3 (501867156963/1000000000000 : ℝ) (125466789243/250000000000 : ℝ) (501855086199/1000000000000 : ℝ) (3920742861/7812500000 : ℝ) (501861121581/1000000000000 : ℝ) (50186112159/100000000000 : ℝ) (62732640193/125000000000 : ℝ) (250930560777/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16857/131072 : ℝ))) 4 (501861121581/1000000000000 : ℝ) (50186112159/100000000000 : ℝ) (62732640193/125000000000 : ℝ) (250930560777/500000000000 : ℝ) (250930560781/500000000000 : ℝ) (125465280393/250000000000 : ℝ) (250930560781/500000000000 : ℝ) (125465280393/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16857/131072 : ℝ))) 5 (250930560781/500000000000 : ℝ) (125465280393/250000000000 : ℝ) (250930560781/500000000000 : ℝ) (125465280393/250000000000 : ℝ) (250930560781/500000000000 : ℝ) (125465280393/250000000000 : ℝ) (250930560781/500000000000 : ℝ) (125465280393/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16857/131072 : ℝ))) 6 (250930560781/500000000000 : ℝ) (125465280393/250000000000 : ℝ) (250930560781/500000000000 : ℝ) (125465280393/250000000000 : ℝ) (250930560781/500000000000 : ℝ) (125465280393/250000000000 : ℝ) (250930560781/500000000000 : ℝ) (125465280393/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16857/131072 : ℝ))) 7 (250930560781/500000000000 : ℝ) (125465280393/250000000000 : ℝ) (250930560781/500000000000 : ℝ) (125465280393/250000000000 : ℝ) (250930560781/500000000000 : ℝ) (125465280393/250000000000 : ℝ) (250930560781/500000000000 : ℝ) (125465280393/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16857/131072 : ℝ)) hmem 8 (24800254949/25000000000 : ℝ) (992010197963/1000000000000 : ℝ) (24800254949/25000000000 : ℝ) (992010197963/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16857/131072 : ℝ))) hcmem 8 (250930560781/500000000000 : ℝ) (125465280393/250000000000 : ℝ) (250930560781/500000000000 : ℝ) (125465280393/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16857/131072 : ℝ)) (24800254949/25000000000 : ℝ) (992010197963/1000000000000 : ℝ) (250930560781/500000000000 : ℝ) (125465280393/250000000000 : ℝ) (19866771731/25000000000 : ℝ) (794670869259/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1281_exp_lower
  have heNumeric : (1027451228639/500000000000 : ℝ)/4 ≤ Real.exp (-42628222741951/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451228639/500000000000 : ℝ)/4 ≤ Real.exp ((33713/262144 : ℝ)-(794670869259/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33713/262144 : ℝ) (16857/131072 : ℝ) (794670869259/1000000000000 : ℝ) (1027451228639/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1282; no trusted numerical premise.
theorem cover8_leaf1282_exp_radius : (997992447236506061/1000000000000000000 : ℝ) ≤ Real.exp ((-33715/2097152 : ℝ)/8) ∧ Real.exp ((-33715/2097152 : ℝ)/8) ≤ (498996223618253031/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33715/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1282_exp_lower : (230028375419230807/250000000000000000 : ℝ) ≤ Real.exp ((-21314110761143/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314110761143/32000000000000 : ℝ)/8) ≤ (920113501676923229/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314110761143/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1282_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451248219/500000000000 : ℝ) ≤ 4*Real.exp (16857/131072 : ℝ)*Real.exp (-mu (radius 8 (33715/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451248219/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33715/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1282_exp_radius
  have hrNumeric : (984051973439/1000000000000 : ℝ) ≤ Real.exp (-33715/2097152 : ℝ) ∧ Real.exp (-33715/2097152 : ℝ) ≤ (3075162417/3125000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984051973439/1000000000000 : ℝ) ≤ (radius 8 (33715/262144 : ℝ)) ∧ (radius 8 (33715/262144 : ℝ)) ≤ (3075162417/3125000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33715/262144 : ℝ)) (984051973439/1000000000000 : ℝ) (3075162417/3125000000 : ℝ) (17788117823/100000000000 : ℝ) (177881178237/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33715/262144 : ℝ)) (984051973439/1000000000000 : ℝ) (3075162417/3125000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33715/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984051973439/1000000000000 : ℝ) (3075162417/3125000000 : ℝ) (992025986719/1000000000000 : ℝ) (6200162417/6250000000 : ℝ) (495996969103/500000000000 : ℝ) (30999810569/31250000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33715/262144 : ℝ)) 1 (992025986719/1000000000000 : ℝ) (6200162417/6250000000 : ℝ) (495996969103/500000000000 : ℝ) (30999810569/31250000000 : ℝ) (496004981231/500000000000 : ℝ) (31000311327/31250000000 : ℝ) (992009962333/1000000000000 : ℝ) (198401992467/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33715/262144 : ℝ)) 2 (496004981231/500000000000 : ℝ) (31000311327/31250000000 : ℝ) (992009962333/1000000000000 : ℝ) (198401992467/200000000000 : ℝ) (992009962397/1000000000000 : ℝ) (1240012453/1250000000 : ℝ) (992009962397/1000000000000 : ℝ) (1240012453/1250000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33715/262144 : ℝ)) 3 (992009962397/1000000000000 : ℝ) (1240012453/1250000000 : ℝ) (992009962397/1000000000000 : ℝ) (1240012453/1250000000 : ℝ) (992009962397/1000000000000 : ℝ) (1240012453/1250000000 : ℝ) (992009962397/1000000000000 : ℝ) (1240012453/1250000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33715/262144 : ℝ)) 4 (992009962397/1000000000000 : ℝ) (1240012453/1250000000 : ℝ) (992009962397/1000000000000 : ℝ) (1240012453/1250000000 : ℝ) (992009962397/1000000000000 : ℝ) (1240012453/1250000000 : ℝ) (992009962397/1000000000000 : ℝ) (1240012453/1250000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33715/262144 : ℝ)) 5 (992009962397/1000000000000 : ℝ) (1240012453/1250000000 : ℝ) (992009962397/1000000000000 : ℝ) (1240012453/1250000000 : ℝ) (992009962397/1000000000000 : ℝ) (1240012453/1250000000 : ℝ) (992009962397/1000000000000 : ℝ) (1240012453/1250000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33715/262144 : ℝ)) 6 (992009962397/1000000000000 : ℝ) (1240012453/1250000000 : ℝ) (992009962397/1000000000000 : ℝ) (1240012453/1250000000 : ℝ) (992009962397/1000000000000 : ℝ) (1240012453/1250000000 : ℝ) (992009962397/1000000000000 : ℝ) (1240012453/1250000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33715/262144 : ℝ)) 7 (992009962397/1000000000000 : ℝ) (1240012453/1250000000 : ℝ) (992009962397/1000000000000 : ℝ) (1240012453/1250000000 : ℝ) (992009962397/1000000000000 : ℝ) (1240012453/1250000000 : ℝ) (992009962397/1000000000000 : ℝ) (1240012453/1250000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33715/262144 : ℝ))) (17788117823/100000000000 : ℝ) (177881178237/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33715/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (17788117823/100000000000 : ℝ) (177881178237/1000000000000 : ℝ) (117788117823/200000000000 : ℝ) (588940589119/1000000000000 : ℝ) (52719952673/125000000000 : ℝ) (421759621393/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33715/262144 : ℝ))) 1 (117788117823/200000000000 : ℝ) (588940589119/1000000000000 : ℝ) (52719952673/125000000000 : ℝ) (421759621393/1000000000000 : ℝ) (505350105249/1000000000000 : ℝ) (63168763157/125000000000 : ℝ) (2491943819/5000000000 : ℝ) (15574648869/31250000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33715/262144 : ℝ))) 2 (505350105249/1000000000000 : ℝ) (63168763157/125000000000 : ℝ) (2491943819/5000000000 : ℝ) (15574648869/31250000000 : ℝ) (125467358631/250000000000 : ℝ) (125467358633/250000000000 : ℝ) (250928682219/500000000000 : ℝ) (501857364447/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33715/262144 : ℝ))) 3 (125467358631/250000000000 : ℝ) (125467358633/250000000000 : ℝ) (250928682219/500000000000 : ℝ) (501857364447/1000000000000 : ℝ) (501863399481/1000000000000 : ℝ) (50186339949/100000000000 : ℝ) (125465849861/250000000000 : ℝ) (250931699727/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33715/262144 : ℝ))) 4 (501863399481/1000000000000 : ℝ) (50186339949/100000000000 : ℝ) (125465849861/250000000000 : ℝ) (250931699727/500000000000 : ℝ) (250931699731/500000000000 : ℝ) (31366462467/62500000000 : ℝ) (250931699731/500000000000 : ℝ) (31366462467/62500000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33715/262144 : ℝ))) 5 (250931699731/500000000000 : ℝ) (31366462467/62500000000 : ℝ) (250931699731/500000000000 : ℝ) (31366462467/62500000000 : ℝ) (250931699731/500000000000 : ℝ) (31366462467/62500000000 : ℝ) (250931699731/500000000000 : ℝ) (31366462467/62500000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33715/262144 : ℝ))) 6 (250931699731/500000000000 : ℝ) (31366462467/62500000000 : ℝ) (250931699731/500000000000 : ℝ) (31366462467/62500000000 : ℝ) (250931699731/500000000000 : ℝ) (31366462467/62500000000 : ℝ) (250931699731/500000000000 : ℝ) (31366462467/62500000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33715/262144 : ℝ))) 7 (250931699731/500000000000 : ℝ) (31366462467/62500000000 : ℝ) (250931699731/500000000000 : ℝ) (31366462467/62500000000 : ℝ) (250931699731/500000000000 : ℝ) (31366462467/62500000000 : ℝ) (250931699731/500000000000 : ℝ) (31366462467/62500000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33715/262144 : ℝ)) hmem 8 (992009962397/1000000000000 : ℝ) (1240012453/1250000000 : ℝ) (992009962397/1000000000000 : ℝ) (1240012453/1250000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33715/262144 : ℝ))) hcmem 8 (250931699731/500000000000 : ℝ) (31366462467/62500000000 : ℝ) (250931699731/500000000000 : ℝ) (31366462467/62500000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33715/262144 : ℝ)) (992009962397/1000000000000 : ℝ) (1240012453/1250000000 : ℝ) (250931699731/500000000000 : ℝ) (31366462467/62500000000 : ℝ) (794674664879/1000000000000 : ℝ) (794674664899/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1282_exp_lower
  have heNumeric : (1027451248219/500000000000 : ℝ)/4 ≤ Real.exp (-21314110761143/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451248219/500000000000 : ℝ)/4 ≤ Real.exp ((16857/131072 : ℝ)-(794674664899/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16857/131072 : ℝ) (33715/262144 : ℝ) (794674664899/1000000000000 : ℝ) (1027451248219/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1283; no trusted numerical premise.
theorem cover8_leaf1283_exp_radius : (31187262117235079/31250000000000000 : ℝ) ≤ Real.exp ((-8429/524288 : ℝ)/8) ∧ Real.exp ((-8429/524288 : ℝ)/8) ≤ (997992387751522529/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8429/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1283_exp_lower : (7188386749036837/7812500000000000 : ℝ) ≤ Real.exp ((-8525644059641/12800000000000 : ℝ)/8) ∧ Real.exp ((-8525644059641/12800000000000 : ℝ)/8) ≤ (920113503876715137/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8525644059641/12800000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1283_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902535741/1000000000000 : ℝ) ≤ 4*Real.exp (33715/262144 : ℝ)*Real.exp (-mu (radius 8 (8429/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902535741/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8429/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1283_exp_radius
  have hrNumeric : (492025752103/500000000000 : ℝ) ≤ Real.exp (-8429/524288 : ℝ) ∧ Real.exp (-8429/524288 : ℝ) ≤ (984051504207/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492025752103/500000000000 : ℝ) ≤ (radius 8 (8429/65536 : ℝ)) ∧ (radius 8 (8429/65536 : ℝ)) ≤ (984051504207/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8429/65536 : ℝ)) (492025752103/500000000000 : ℝ) (984051504207/1000000000000 : ℝ) (177883774043/1000000000000 : ℝ) (177883774049/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8429/65536 : ℝ)) (492025752103/500000000000 : ℝ) (984051504207/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8429/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492025752103/500000000000 : ℝ) (984051504207/1000000000000 : ℝ) (992025752103/1000000000000 : ℝ) (124003219013/125000000000 : ℝ) (15499901589/15625000000 : ℝ) (495996850849/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8429/65536 : ℝ)) 1 (992025752103/1000000000000 : ℝ) (124003219013/125000000000 : ℝ) (15499901589/15625000000 : ℝ) (495996850849/500000000000 : ℝ) (992009726899/1000000000000 : ℝ) (992009726901/1000000000000 : ℝ) (99200972677/100000000000 : ℝ) (248002431693/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8429/65536 : ℝ)) 2 (992009726899/1000000000000 : ℝ) (992009726901/1000000000000 : ℝ) (99200972677/100000000000 : ℝ) (248002431693/250000000000 : ℝ) (496004863417/500000000000 : ℝ) (992009726837/1000000000000 : ℝ) (496004863417/500000000000 : ℝ) (992009726837/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8429/65536 : ℝ)) 3 (496004863417/500000000000 : ℝ) (992009726837/1000000000000 : ℝ) (496004863417/500000000000 : ℝ) (992009726837/1000000000000 : ℝ) (496004863417/500000000000 : ℝ) (992009726837/1000000000000 : ℝ) (496004863417/500000000000 : ℝ) (992009726837/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8429/65536 : ℝ)) 4 (496004863417/500000000000 : ℝ) (992009726837/1000000000000 : ℝ) (496004863417/500000000000 : ℝ) (992009726837/1000000000000 : ℝ) (496004863417/500000000000 : ℝ) (992009726837/1000000000000 : ℝ) (496004863417/500000000000 : ℝ) (992009726837/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8429/65536 : ℝ)) 5 (496004863417/500000000000 : ℝ) (992009726837/1000000000000 : ℝ) (496004863417/500000000000 : ℝ) (992009726837/1000000000000 : ℝ) (496004863417/500000000000 : ℝ) (992009726837/1000000000000 : ℝ) (496004863417/500000000000 : ℝ) (992009726837/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8429/65536 : ℝ)) 6 (496004863417/500000000000 : ℝ) (992009726837/1000000000000 : ℝ) (496004863417/500000000000 : ℝ) (992009726837/1000000000000 : ℝ) (496004863417/500000000000 : ℝ) (992009726837/1000000000000 : ℝ) (496004863417/500000000000 : ℝ) (992009726837/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8429/65536 : ℝ)) 7 (496004863417/500000000000 : ℝ) (992009726837/1000000000000 : ℝ) (496004863417/500000000000 : ℝ) (992009726837/1000000000000 : ℝ) (496004863417/500000000000 : ℝ) (992009726837/1000000000000 : ℝ) (496004863417/500000000000 : ℝ) (992009726837/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8429/65536 : ℝ))) (177883774043/1000000000000 : ℝ) (177883774049/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8429/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177883774043/1000000000000 : ℝ) (177883774049/1000000000000 : ℝ) (588941887021/1000000000000 : ℝ) (23557675481/40000000000 : ℝ) (421762698733/1000000000000 : ℝ) (421762698741/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8429/65536 : ℝ))) 1 (588941887021/1000000000000 : ℝ) (23557675481/40000000000 : ℝ) (421762698733/1000000000000 : ℝ) (421762698741/1000000000000 : ℝ) (505352292877/1000000000000 : ℝ) (505352292883/1000000000000 : ℝ) (62298891401/125000000000 : ℝ) (99678226243/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8429/65536 : ℝ))) 2 (505352292877/1000000000000 : ℝ) (505352292883/1000000000000 : ℝ) (62298891401/125000000000 : ℝ) (99678226243/200000000000 : ℝ) (250935856021/500000000000 : ℝ) (501871712049/1000000000000 : ℝ) (250929821317/500000000000 : ℝ) (250929821321/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8429/65536 : ℝ))) 3 (250935856021/500000000000 : ℝ) (501871712049/1000000000000 : ℝ) (250929821317/500000000000 : ℝ) (250929821321/500000000000 : ℝ) (250932838669/500000000000 : ℝ) (250932838673/500000000000 : ℝ) (501865677301/1000000000000 : ℝ) (50186567731/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8429/65536 : ℝ))) 4 (250932838669/500000000000 : ℝ) (250932838673/500000000000 : ℝ) (501865677301/1000000000000 : ℝ) (50186567731/100000000000 : ℝ) (501865677319/1000000000000 : ℝ) (31366604833/62500000000 : ℝ) (501865677319/1000000000000 : ℝ) (31366604833/62500000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8429/65536 : ℝ))) 5 (501865677319/1000000000000 : ℝ) (31366604833/62500000000 : ℝ) (501865677319/1000000000000 : ℝ) (31366604833/62500000000 : ℝ) (501865677319/1000000000000 : ℝ) (31366604833/62500000000 : ℝ) (501865677319/1000000000000 : ℝ) (31366604833/62500000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8429/65536 : ℝ))) 6 (501865677319/1000000000000 : ℝ) (31366604833/62500000000 : ℝ) (501865677319/1000000000000 : ℝ) (31366604833/62500000000 : ℝ) (501865677319/1000000000000 : ℝ) (31366604833/62500000000 : ℝ) (501865677319/1000000000000 : ℝ) (31366604833/62500000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8429/65536 : ℝ))) 7 (501865677319/1000000000000 : ℝ) (31366604833/62500000000 : ℝ) (501865677319/1000000000000 : ℝ) (31366604833/62500000000 : ℝ) (501865677319/1000000000000 : ℝ) (31366604833/62500000000 : ℝ) (501865677319/1000000000000 : ℝ) (31366604833/62500000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8429/65536 : ℝ)) hmem 8 (496004863417/500000000000 : ℝ) (992009726837/1000000000000 : ℝ) (496004863417/500000000000 : ℝ) (992009726837/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8429/65536 : ℝ))) hcmem 8 (501865677319/1000000000000 : ℝ) (31366604833/62500000000 : ℝ) (501865677319/1000000000000 : ℝ) (31366604833/62500000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8429/65536 : ℝ)) (496004863417/500000000000 : ℝ) (992009726837/1000000000000 : ℝ) (501865677319/1000000000000 : ℝ) (31366604833/62500000000 : ℝ) (198669615113/250000000000 : ℝ) (79467846047/100000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1283_exp_lower
  have heNumeric : (2054902535741/1000000000000 : ℝ)/4 ≤ Real.exp (-8525644059641/12800000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902535741/1000000000000 : ℝ)/4 ≤ Real.exp ((33715/262144 : ℝ)-(79467846047/100000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33715/262144 : ℝ) (8429/65536 : ℝ) (79467846047/100000000000 : ℝ) (2054902535741/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1284; no trusted numerical premise.
theorem cover8_leaf1284_exp_radius : (49899616413327127/50000000000000000 : ℝ) ≤ Real.exp ((-33717/2097152 : ℝ)/8) ∧ Real.exp ((-33717/2097152 : ℝ)/8) ≤ (997992328266542541/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33717/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1284_exp_lower : (115014188260713523/125000000000000000 : ℝ) ≤ Real.exp ((-10657054767251/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657054767251/16000000000000 : ℝ)/8) ≤ (184022701217141637/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657054767251/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1284_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256862821901/125000000000 : ℝ) ≤ 4*Real.exp (8429/65536 : ℝ)*Real.exp (-mu (radius 8 (33717/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (256862821901/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33717/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1284_exp_radius
  have hrNumeric : (492025517487/500000000000 : ℝ) ≤ Real.exp (-33717/2097152 : ℝ) ∧ Real.exp (-33717/2097152 : ℝ) ≤ (39362041399/40000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492025517487/500000000000 : ℝ) ≤ (radius 8 (33717/262144 : ℝ)) ∧ (radius 8 (33717/262144 : ℝ)) ≤ (39362041399/40000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33717/262144 : ℝ)) (492025517487/500000000000 : ℝ) (39362041399/40000000000 : ℝ) (177886369811/1000000000000 : ℝ) (177886369817/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33717/262144 : ℝ)) (492025517487/500000000000 : ℝ) (39362041399/40000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33717/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492025517487/500000000000 : ℝ) (39362041399/40000000000 : ℝ) (992025517487/1000000000000 : ℝ) (62001594843/62500000000 : ℝ) (991993465187/1000000000000 : ℝ) (247998366297/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33717/262144 : ℝ)) 1 (992025517487/1000000000000 : ℝ) (62001594843/62500000000 : ℝ) (991993465187/1000000000000 : ℝ) (247998366297/250000000000 : ℝ) (992009491337/1000000000000 : ℝ) (496004745669/500000000000 : ℝ) (992009491207/1000000000000 : ℝ) (992009491209/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33717/262144 : ℝ)) 2 (992009491337/1000000000000 : ℝ) (496004745669/500000000000 : ℝ) (992009491207/1000000000000 : ℝ) (992009491209/1000000000000 : ℝ) (124001186409/125000000000 : ℝ) (496004745637/500000000000 : ℝ) (992009491271/1000000000000 : ℝ) (496004745637/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33717/262144 : ℝ)) 3 (124001186409/125000000000 : ℝ) (496004745637/500000000000 : ℝ) (992009491271/1000000000000 : ℝ) (496004745637/500000000000 : ℝ) (992009491271/1000000000000 : ℝ) (496004745637/500000000000 : ℝ) (992009491271/1000000000000 : ℝ) (496004745637/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33717/262144 : ℝ)) 4 (992009491271/1000000000000 : ℝ) (496004745637/500000000000 : ℝ) (992009491271/1000000000000 : ℝ) (496004745637/500000000000 : ℝ) (992009491271/1000000000000 : ℝ) (496004745637/500000000000 : ℝ) (992009491271/1000000000000 : ℝ) (496004745637/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33717/262144 : ℝ)) 5 (992009491271/1000000000000 : ℝ) (496004745637/500000000000 : ℝ) (992009491271/1000000000000 : ℝ) (496004745637/500000000000 : ℝ) (992009491271/1000000000000 : ℝ) (496004745637/500000000000 : ℝ) (992009491271/1000000000000 : ℝ) (496004745637/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33717/262144 : ℝ)) 6 (992009491271/1000000000000 : ℝ) (496004745637/500000000000 : ℝ) (992009491271/1000000000000 : ℝ) (496004745637/500000000000 : ℝ) (992009491271/1000000000000 : ℝ) (496004745637/500000000000 : ℝ) (992009491271/1000000000000 : ℝ) (496004745637/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33717/262144 : ℝ)) 7 (992009491271/1000000000000 : ℝ) (496004745637/500000000000 : ℝ) (992009491271/1000000000000 : ℝ) (496004745637/500000000000 : ℝ) (992009491271/1000000000000 : ℝ) (496004745637/500000000000 : ℝ) (992009491271/1000000000000 : ℝ) (496004745637/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33717/262144 : ℝ))) (177886369811/1000000000000 : ℝ) (177886369817/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33717/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177886369811/1000000000000 : ℝ) (177886369817/1000000000000 : ℝ) (117788636981/200000000000 : ℝ) (588943184909/1000000000000 : ℝ) (421765776007/1000000000000 : ℝ) (84353155203/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33717/262144 : ℝ))) 1 (117788636981/200000000000 : ℝ) (588943184909/1000000000000 : ℝ) (421765776007/1000000000000 : ℝ) (84353155203/200000000000 : ℝ) (63169310057/125000000000 : ℝ) (252677240231/500000000000 : ℝ) (249196749279/500000000000 : ℝ) (249196749283/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33717/262144 : ℝ))) 2 (63169310057/125000000000 : ℝ) (252677240231/500000000000 : ℝ) (249196749279/500000000000 : ℝ) (249196749283/500000000000 : ℝ) (501873989507/1000000000000 : ℝ) (250936994757/500000000000 : ℝ) (501861920777/1000000000000 : ℝ) (100372384157/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33717/262144 : ℝ))) 3 (501873989507/1000000000000 : ℝ) (250936994757/500000000000 : ℝ) (501861920777/1000000000000 : ℝ) (100372384157/200000000000 : ℝ) (250933977571/500000000000 : ℝ) (10037359103/20000000000 : ℝ) (100373591021/200000000000 : ℝ) (250933977557/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33717/262144 : ℝ))) 4 (250933977571/500000000000 : ℝ) (10037359103/20000000000 : ℝ) (100373591021/200000000000 : ℝ) (250933977557/500000000000 : ℝ) (501867955123/1000000000000 : ℝ) (125466988783/250000000000 : ℝ) (501867955123/1000000000000 : ℝ) (125466988783/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33717/262144 : ℝ))) 5 (501867955123/1000000000000 : ℝ) (125466988783/250000000000 : ℝ) (501867955123/1000000000000 : ℝ) (125466988783/250000000000 : ℝ) (501867955123/1000000000000 : ℝ) (125466988783/250000000000 : ℝ) (501867955123/1000000000000 : ℝ) (125466988783/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33717/262144 : ℝ))) 6 (501867955123/1000000000000 : ℝ) (125466988783/250000000000 : ℝ) (501867955123/1000000000000 : ℝ) (125466988783/250000000000 : ℝ) (501867955123/1000000000000 : ℝ) (125466988783/250000000000 : ℝ) (501867955123/1000000000000 : ℝ) (125466988783/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33717/262144 : ℝ))) 7 (501867955123/1000000000000 : ℝ) (125466988783/250000000000 : ℝ) (501867955123/1000000000000 : ℝ) (125466988783/250000000000 : ℝ) (501867955123/1000000000000 : ℝ) (125466988783/250000000000 : ℝ) (501867955123/1000000000000 : ℝ) (125466988783/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33717/262144 : ℝ)) hmem 8 (992009491271/1000000000000 : ℝ) (496004745637/500000000000 : ℝ) (992009491271/1000000000000 : ℝ) (496004745637/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33717/262144 : ℝ))) hcmem 8 (501867955123/1000000000000 : ℝ) (125466988783/250000000000 : ℝ) (501867955123/1000000000000 : ℝ) (125466988783/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33717/262144 : ℝ)) (992009491271/1000000000000 : ℝ) (496004745637/500000000000 : ℝ) (501867955123/1000000000000 : ℝ) (125466988783/250000000000 : ℝ) (794682255943/1000000000000 : ℝ) (794682255961/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1284_exp_lower
  have heNumeric : (256862821901/125000000000 : ℝ)/4 ≤ Real.exp (-10657054767251/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256862821901/125000000000 : ℝ)/4 ≤ Real.exp ((8429/65536 : ℝ)-(794682255961/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8429/65536 : ℝ) (33717/262144 : ℝ) (794682255961/1000000000000 : ℝ) (256862821901/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1285; no trusted numerical premise.
theorem cover8_leaf1285_exp_radius : (498996134390783049/500000000000000000 : ℝ) ≤ Real.exp ((-16859/1048576 : ℝ)/8) ∧ Real.exp ((-16859/1048576 : ℝ)/8) ≤ (997992268781566099/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16859/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1285_exp_lower : (920113508303212287/1000000000000000000 : ℝ) ≤ Real.exp ((-42628217835067/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628217835067/64000000000000 : ℝ)/8) ≤ (3594193391809423/3906250000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628217835067/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1285_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902614827/1000000000000 : ℝ) ≤ 4*Real.exp (33717/262144 : ℝ)*Real.exp (-mu (radius 8 (16859/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902614827/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16859/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1285_exp_radius
  have hrNumeric : (492025282871/500000000000 : ℝ) ≤ Real.exp (-16859/1048576 : ℝ) ∧ Real.exp (-16859/1048576 : ℝ) ≤ (984050565743/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492025282871/500000000000 : ℝ) ≤ (radius 8 (16859/131072 : ℝ)) ∧ (radius 8 (16859/131072 : ℝ)) ≤ (984050565743/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16859/131072 : ℝ)) (492025282871/500000000000 : ℝ) (984050565743/1000000000000 : ℝ) (177888965539/1000000000000 : ℝ) (88944482773/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16859/131072 : ℝ)) (492025282871/500000000000 : ℝ) (984050565743/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16859/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492025282871/500000000000 : ℝ) (984050565743/1000000000000 : ℝ) (992025282871/1000000000000 : ℝ) (124003160359/125000000000 : ℝ) (991993228677/1000000000000 : ℝ) (495996614339/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16859/131072 : ℝ)) 1 (992025282871/1000000000000 : ℝ) (124003160359/125000000000 : ℝ) (991993228677/1000000000000 : ℝ) (495996614339/500000000000 : ℝ) (496004627887/500000000000 : ℝ) (39680370231/40000000000 : ℝ) (248002313911/250000000000 : ℝ) (496004627823/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16859/131072 : ℝ)) 2 (496004627887/500000000000 : ℝ) (39680370231/40000000000 : ℝ) (248002313911/250000000000 : ℝ) (496004627823/500000000000 : ℝ) (992009255709/1000000000000 : ℝ) (992009255711/1000000000000 : ℝ) (248002313927/250000000000 : ℝ) (992009255711/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16859/131072 : ℝ)) 3 (992009255709/1000000000000 : ℝ) (992009255711/1000000000000 : ℝ) (248002313927/250000000000 : ℝ) (992009255711/1000000000000 : ℝ) (248002313927/250000000000 : ℝ) (992009255711/1000000000000 : ℝ) (248002313927/250000000000 : ℝ) (992009255711/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16859/131072 : ℝ)) 4 (248002313927/250000000000 : ℝ) (992009255711/1000000000000 : ℝ) (248002313927/250000000000 : ℝ) (992009255711/1000000000000 : ℝ) (248002313927/250000000000 : ℝ) (992009255711/1000000000000 : ℝ) (248002313927/250000000000 : ℝ) (992009255711/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16859/131072 : ℝ)) 5 (248002313927/250000000000 : ℝ) (992009255711/1000000000000 : ℝ) (248002313927/250000000000 : ℝ) (992009255711/1000000000000 : ℝ) (248002313927/250000000000 : ℝ) (992009255711/1000000000000 : ℝ) (248002313927/250000000000 : ℝ) (992009255711/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16859/131072 : ℝ)) 6 (248002313927/250000000000 : ℝ) (992009255711/1000000000000 : ℝ) (248002313927/250000000000 : ℝ) (992009255711/1000000000000 : ℝ) (248002313927/250000000000 : ℝ) (992009255711/1000000000000 : ℝ) (248002313927/250000000000 : ℝ) (992009255711/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16859/131072 : ℝ)) 7 (248002313927/250000000000 : ℝ) (992009255711/1000000000000 : ℝ) (248002313927/250000000000 : ℝ) (992009255711/1000000000000 : ℝ) (248002313927/250000000000 : ℝ) (992009255711/1000000000000 : ℝ) (248002313927/250000000000 : ℝ) (992009255711/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16859/131072 : ℝ))) (177888965539/1000000000000 : ℝ) (88944482773/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16859/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177888965539/1000000000000 : ℝ) (88944482773/500000000000 : ℝ) (588944482769/1000000000000 : ℝ) (588944482773/1000000000000 : ℝ) (421768853211/1000000000000 : ℝ) (21088442661/50000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16859/131072 : ℝ))) 1 (588944482769/1000000000000 : ℝ) (588944482773/1000000000000 : ℝ) (421768853211/1000000000000 : ℝ) (21088442661/50000000000 : ℝ) (50535666799/100000000000 : ℝ) (505356667997/1000000000000 : ℝ) (1946858851/3906250000 : ℝ) (62299483233/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16859/131072 : ℝ))) 2 (50535666799/100000000000 : ℝ) (505356667997/1000000000000 : ℝ) (1946858851/3906250000 : ℝ) (62299483233/125000000000 : ℝ) (501876266923/1000000000000 : ℝ) (501876266931/1000000000000 : ℝ) (501864198871/1000000000000 : ℝ) (3136651243/6250000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16859/131072 : ℝ))) 3 (501876266923/1000000000000 : ℝ) (501876266931/1000000000000 : ℝ) (501864198871/1000000000000 : ℝ) (3136651243/6250000000 : ℝ) (501870232897/1000000000000 : ℝ) (250935116453/500000000000 : ℝ) (25093511643/50000000000 : ℝ) (50187023287/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16859/131072 : ℝ))) 4 (501870232897/1000000000000 : ℝ) (250935116453/500000000000 : ℝ) (25093511643/50000000000 : ℝ) (50187023287/100000000000 : ℝ) (250935116439/500000000000 : ℝ) (62733779111/125000000000 : ℝ) (250935116439/500000000000 : ℝ) (62733779111/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16859/131072 : ℝ))) 5 (250935116439/500000000000 : ℝ) (62733779111/125000000000 : ℝ) (250935116439/500000000000 : ℝ) (62733779111/125000000000 : ℝ) (250935116439/500000000000 : ℝ) (62733779111/125000000000 : ℝ) (250935116439/500000000000 : ℝ) (62733779111/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16859/131072 : ℝ))) 6 (250935116439/500000000000 : ℝ) (62733779111/125000000000 : ℝ) (250935116439/500000000000 : ℝ) (62733779111/125000000000 : ℝ) (250935116439/500000000000 : ℝ) (62733779111/125000000000 : ℝ) (250935116439/500000000000 : ℝ) (62733779111/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16859/131072 : ℝ))) 7 (250935116439/500000000000 : ℝ) (62733779111/125000000000 : ℝ) (250935116439/500000000000 : ℝ) (62733779111/125000000000 : ℝ) (250935116439/500000000000 : ℝ) (62733779111/125000000000 : ℝ) (250935116439/500000000000 : ℝ) (62733779111/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16859/131072 : ℝ)) hmem 8 (248002313927/250000000000 : ℝ) (992009255711/1000000000000 : ℝ) (248002313927/250000000000 : ℝ) (992009255711/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16859/131072 : ℝ))) hcmem 8 (250935116439/500000000000 : ℝ) (62733779111/125000000000 : ℝ) (250935116439/500000000000 : ℝ) (62733779111/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16859/131072 : ℝ)) (248002313927/250000000000 : ℝ) (992009255711/1000000000000 : ℝ) (250935116439/500000000000 : ℝ) (62733779111/125000000000 : ℝ) (397343025679/500000000000 : ℝ) (397343025689/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1285_exp_lower
  have heNumeric : (2054902614827/1000000000000 : ℝ)/4 ≤ Real.exp (-42628217835067/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902614827/1000000000000 : ℝ)/4 ≤ Real.exp ((33717/262144 : ℝ)-(397343025689/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33717/262144 : ℝ) (16859/131072 : ℝ) (397343025689/500000000000 : ℝ) (2054902614827/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1286; no trusted numerical premise.
theorem cover8_leaf1286_exp_radius : (498996104648296601/500000000000000000 : ℝ) ≤ Real.exp ((-33719/2097152 : ℝ)/8) ∧ Real.exp ((-33719/2097152 : ℝ)/8) ≤ (997992209296593203/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33719/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1286_exp_lower : (920113510529457473/1000000000000000000 : ℝ) ≤ Real.exp ((-21314108298133/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314108298133/32000000000000 : ℝ)/8) ≤ (460056755264728737/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314108298133/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1286_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451327301/500000000000 : ℝ) ≤ 4*Real.exp (16859/131072 : ℝ)*Real.exp (-mu (radius 8 (33719/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451327301/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33719/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1286_exp_radius
  have hrNumeric : (98405009651/100000000000 : ℝ) ≤ Real.exp (-33719/2097152 : ℝ) ∧ Real.exp (-33719/2097152 : ℝ) ≤ (984050096511/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (98405009651/100000000000 : ℝ) ≤ (radius 8 (33719/262144 : ℝ)) ∧ (radius 8 (33719/262144 : ℝ)) ≤ (984050096511/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33719/262144 : ℝ)) (98405009651/100000000000 : ℝ) (984050096511/1000000000000 : ℝ) (177891561229/1000000000000 : ℝ) (44472890309/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33719/262144 : ℝ)) (98405009651/100000000000 : ℝ) (984050096511/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33719/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (98405009651/100000000000 : ℝ) (984050096511/1000000000000 : ℝ) (198405009651/200000000000 : ℝ) (15500391379/15625000000 : ℝ) (991992992167/1000000000000 : ℝ) (991992992169/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33719/262144 : ℝ)) 1 (198405009651/200000000000 : ℝ) (15500391379/15625000000 : ℝ) (991992992167/1000000000000 : ℝ) (991992992169/1000000000000 : ℝ) (992009020211/1000000000000 : ℝ) (992009020213/1000000000000 : ℝ) (992009020081/1000000000000 : ℝ) (248002255021/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33719/262144 : ℝ)) 2 (992009020211/1000000000000 : ℝ) (992009020213/1000000000000 : ℝ) (992009020081/1000000000000 : ℝ) (248002255021/250000000000 : ℝ) (496004510073/500000000000 : ℝ) (992009020149/1000000000000 : ℝ) (198401804029/200000000000 : ℝ) (992009020149/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33719/262144 : ℝ)) 3 (496004510073/500000000000 : ℝ) (992009020149/1000000000000 : ℝ) (198401804029/200000000000 : ℝ) (992009020149/1000000000000 : ℝ) (198401804029/200000000000 : ℝ) (992009020149/1000000000000 : ℝ) (198401804029/200000000000 : ℝ) (992009020149/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33719/262144 : ℝ)) 4 (198401804029/200000000000 : ℝ) (992009020149/1000000000000 : ℝ) (198401804029/200000000000 : ℝ) (992009020149/1000000000000 : ℝ) (198401804029/200000000000 : ℝ) (992009020149/1000000000000 : ℝ) (198401804029/200000000000 : ℝ) (992009020149/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33719/262144 : ℝ)) 5 (198401804029/200000000000 : ℝ) (992009020149/1000000000000 : ℝ) (198401804029/200000000000 : ℝ) (992009020149/1000000000000 : ℝ) (198401804029/200000000000 : ℝ) (992009020149/1000000000000 : ℝ) (198401804029/200000000000 : ℝ) (992009020149/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33719/262144 : ℝ)) 6 (198401804029/200000000000 : ℝ) (992009020149/1000000000000 : ℝ) (198401804029/200000000000 : ℝ) (992009020149/1000000000000 : ℝ) (198401804029/200000000000 : ℝ) (992009020149/1000000000000 : ℝ) (198401804029/200000000000 : ℝ) (992009020149/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33719/262144 : ℝ)) 7 (198401804029/200000000000 : ℝ) (992009020149/1000000000000 : ℝ) (198401804029/200000000000 : ℝ) (992009020149/1000000000000 : ℝ) (198401804029/200000000000 : ℝ) (992009020149/1000000000000 : ℝ) (198401804029/200000000000 : ℝ) (992009020149/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33719/262144 : ℝ))) (177891561229/1000000000000 : ℝ) (44472890309/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33719/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177891561229/1000000000000 : ℝ) (44472890309/250000000000 : ℝ) (294472890307/500000000000 : ℝ) (294472890309/500000000000 : ℝ) (421771930347/1000000000000 : ℝ) (105442982589/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33719/262144 : ℝ))) 1 (294472890307/500000000000 : ℝ) (294472890309/500000000000 : ℝ) (421771930347/1000000000000 : ℝ) (105442982589/250000000000 : ℝ) (12633971387/25000000000 : ℝ) (505358855487/1000000000000 : ℝ) (249199116551/500000000000 : ℝ) (49839823311/100000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33719/262144 : ℝ))) 2 (12633971387/25000000000 : ℝ) (505358855487/1000000000000 : ℝ) (249199116551/500000000000 : ℝ) (49839823311/100000000000 : ℝ) (501878544291/1000000000000 : ℝ) (501878544299/1000000000000 : ℝ) (501866476917/1000000000000 : ℝ) (250933238463/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33719/262144 : ℝ))) 3 (501878544291/1000000000000 : ℝ) (501878544299/1000000000000 : ℝ) (501866476917/1000000000000 : ℝ) (250933238463/500000000000 : ℝ) (125468127651/250000000000 : ℝ) (501872510613/1000000000000 : ℝ) (501872510567/1000000000000 : ℝ) (501872510577/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33719/262144 : ℝ))) 4 (125468127651/250000000000 : ℝ) (501872510613/1000000000000 : ℝ) (501872510567/1000000000000 : ℝ) (501872510577/1000000000000 : ℝ) (100374502117/200000000000 : ℝ) (100374502119/200000000000 : ℝ) (100374502117/200000000000 : ℝ) (100374502119/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33719/262144 : ℝ))) 5 (100374502117/200000000000 : ℝ) (100374502119/200000000000 : ℝ) (100374502117/200000000000 : ℝ) (100374502119/200000000000 : ℝ) (100374502117/200000000000 : ℝ) (100374502119/200000000000 : ℝ) (100374502117/200000000000 : ℝ) (100374502119/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33719/262144 : ℝ))) 6 (100374502117/200000000000 : ℝ) (100374502119/200000000000 : ℝ) (100374502117/200000000000 : ℝ) (100374502119/200000000000 : ℝ) (100374502117/200000000000 : ℝ) (100374502119/200000000000 : ℝ) (100374502117/200000000000 : ℝ) (100374502119/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33719/262144 : ℝ))) 7 (100374502117/200000000000 : ℝ) (100374502119/200000000000 : ℝ) (100374502117/200000000000 : ℝ) (100374502119/200000000000 : ℝ) (100374502117/200000000000 : ℝ) (100374502119/200000000000 : ℝ) (100374502117/200000000000 : ℝ) (100374502119/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33719/262144 : ℝ)) hmem 8 (198401804029/200000000000 : ℝ) (992009020149/1000000000000 : ℝ) (198401804029/200000000000 : ℝ) (992009020149/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33719/262144 : ℝ))) hcmem 8 (100374502117/200000000000 : ℝ) (100374502119/200000000000 : ℝ) (100374502117/200000000000 : ℝ) (100374502119/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33719/262144 : ℝ)) (198401804029/200000000000 : ℝ) (992009020149/1000000000000 : ℝ) (100374502117/200000000000 : ℝ) (100374502119/200000000000 : ℝ) (794689846699/1000000000000 : ℝ) (794689846719/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1286_exp_lower
  have heNumeric : (1027451327301/500000000000 : ℝ)/4 ≤ Real.exp (-21314108298133/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451327301/500000000000 : ℝ)/4 ≤ Real.exp ((16859/131072 : ℝ)-(794689846719/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16859/131072 : ℝ) (33719/262144 : ℝ) (794689846719/1000000000000 : ℝ) (1027451327301/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1287; no trusted numerical premise.
theorem cover8_leaf1287_exp_radius : (997992149811623851/1000000000000000000 : ℝ) ≤ Real.exp ((-4215/262144 : ℝ)/8) ∧ Real.exp ((-4215/262144 : ℝ)/8) ≤ (249498037452905963/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4215/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1287_exp_lower : (920113512765248843/1000000000000000000 : ℝ) ≤ Real.exp ((-42628215352153/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628215352153/64000000000000 : ℝ)/8) ≤ (230028378191312211/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628215352153/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1287_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513725673637/250000000000 : ℝ) ≤ 4*Real.exp (33719/262144 : ℝ)*Real.exp (-mu (radius 8 (4215/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (513725673637/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4215/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1287_exp_radius
  have hrNumeric : (984049627279/1000000000000 : ℝ) ≤ Real.exp (-4215/262144 : ℝ) ∧ Real.exp (-4215/262144 : ℝ) ≤ (12300620341/12500000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984049627279/1000000000000 : ℝ) ≤ (radius 8 (4215/32768 : ℝ)) ∧ (radius 8 (4215/32768 : ℝ)) ≤ (12300620341/12500000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4215/32768 : ℝ)) (984049627279/1000000000000 : ℝ) (12300620341/12500000000 : ℝ) (88947078437/500000000000 : ℝ) (177894156881/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4215/32768 : ℝ)) (984049627279/1000000000000 : ℝ) (12300620341/12500000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4215/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984049627279/1000000000000 : ℝ) (12300620341/12500000000 : ℝ) (992024813639/1000000000000 : ℝ) (24800620341/25000000000 : ℝ) (495996377829/500000000000 : ℝ) (49599637783/50000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4215/32768 : ℝ)) 1 (992024813639/1000000000000 : ℝ) (24800620341/25000000000 : ℝ) (495996377829/500000000000 : ℝ) (49599637783/50000000000 : ℝ) (124001098081/125000000000 : ℝ) (19840175693/20000000000 : ℝ) (992008784519/1000000000000 : ℝ) (992008784521/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4215/32768 : ℝ)) 2 (124001098081/125000000000 : ℝ) (19840175693/20000000000 : ℝ) (992008784519/1000000000000 : ℝ) (992008784521/1000000000000 : ℝ) (992008784583/1000000000000 : ℝ) (496004392293/500000000000 : ℝ) (992008784583/1000000000000 : ℝ) (496004392293/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4215/32768 : ℝ)) 3 (992008784583/1000000000000 : ℝ) (496004392293/500000000000 : ℝ) (992008784583/1000000000000 : ℝ) (496004392293/500000000000 : ℝ) (992008784583/1000000000000 : ℝ) (496004392293/500000000000 : ℝ) (992008784583/1000000000000 : ℝ) (496004392293/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4215/32768 : ℝ)) 4 (992008784583/1000000000000 : ℝ) (496004392293/500000000000 : ℝ) (992008784583/1000000000000 : ℝ) (496004392293/500000000000 : ℝ) (992008784583/1000000000000 : ℝ) (496004392293/500000000000 : ℝ) (992008784583/1000000000000 : ℝ) (496004392293/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4215/32768 : ℝ)) 5 (992008784583/1000000000000 : ℝ) (496004392293/500000000000 : ℝ) (992008784583/1000000000000 : ℝ) (496004392293/500000000000 : ℝ) (992008784583/1000000000000 : ℝ) (496004392293/500000000000 : ℝ) (992008784583/1000000000000 : ℝ) (496004392293/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4215/32768 : ℝ)) 6 (992008784583/1000000000000 : ℝ) (496004392293/500000000000 : ℝ) (992008784583/1000000000000 : ℝ) (496004392293/500000000000 : ℝ) (992008784583/1000000000000 : ℝ) (496004392293/500000000000 : ℝ) (992008784583/1000000000000 : ℝ) (496004392293/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4215/32768 : ℝ)) 7 (992008784583/1000000000000 : ℝ) (496004392293/500000000000 : ℝ) (992008784583/1000000000000 : ℝ) (496004392293/500000000000 : ℝ) (992008784583/1000000000000 : ℝ) (496004392293/500000000000 : ℝ) (992008784583/1000000000000 : ℝ) (496004392293/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4215/32768 : ℝ))) (88947078437/500000000000 : ℝ) (177894156881/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4215/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88947078437/500000000000 : ℝ) (177894156881/1000000000000 : ℝ) (588947078437/1000000000000 : ℝ) (588947078441/1000000000000 : ℝ) (421775007407/1000000000000 : ℝ) (421775007417/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4215/32768 : ℝ))) 1 (588947078437/1000000000000 : ℝ) (588947078441/1000000000000 : ℝ) (421775007407/1000000000000 : ℝ) (421775007417/1000000000000 : ℝ) (252680521461/500000000000 : ℝ) (505361042929/1000000000000 : ℝ) (49840060029/100000000000 : ℝ) (498400600299/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4215/32768 : ℝ))) 2 (252680521461/500000000000 : ℝ) (505361042929/1000000000000 : ℝ) (49840060029/100000000000 : ℝ) (498400600299/1000000000000 : ℝ) (250940410803/500000000000 : ℝ) (250940410807/500000000000 : ℝ) (50186875491/100000000000 : ℝ) (501868754919/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4215/32768 : ℝ))) 3 (250940410803/500000000000 : ℝ) (250940410807/500000000000 : ℝ) (50186875491/100000000000 : ℝ) (501868754919/1000000000000 : ℝ) (250937394129/500000000000 : ℝ) (501874788267/1000000000000 : ℝ) (501874788221/1000000000000 : ℝ) (501874788231/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4215/32768 : ℝ))) 4 (250937394129/500000000000 : ℝ) (501874788267/1000000000000 : ℝ) (501874788221/1000000000000 : ℝ) (501874788231/1000000000000 : ℝ) (501874788239/1000000000000 : ℝ) (501874788249/1000000000000 : ℝ) (501874788239/1000000000000 : ℝ) (501874788249/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4215/32768 : ℝ))) 5 (501874788239/1000000000000 : ℝ) (501874788249/1000000000000 : ℝ) (501874788239/1000000000000 : ℝ) (501874788249/1000000000000 : ℝ) (501874788239/1000000000000 : ℝ) (501874788249/1000000000000 : ℝ) (501874788239/1000000000000 : ℝ) (501874788249/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4215/32768 : ℝ))) 6 (501874788239/1000000000000 : ℝ) (501874788249/1000000000000 : ℝ) (501874788239/1000000000000 : ℝ) (501874788249/1000000000000 : ℝ) (501874788239/1000000000000 : ℝ) (501874788249/1000000000000 : ℝ) (501874788239/1000000000000 : ℝ) (501874788249/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4215/32768 : ℝ))) 7 (501874788239/1000000000000 : ℝ) (501874788249/1000000000000 : ℝ) (501874788239/1000000000000 : ℝ) (501874788249/1000000000000 : ℝ) (501874788239/1000000000000 : ℝ) (501874788249/1000000000000 : ℝ) (501874788239/1000000000000 : ℝ) (501874788249/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4215/32768 : ℝ)) hmem 8 (992008784583/1000000000000 : ℝ) (496004392293/500000000000 : ℝ) (992008784583/1000000000000 : ℝ) (496004392293/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4215/32768 : ℝ))) hcmem 8 (501874788239/1000000000000 : ℝ) (501874788249/1000000000000 : ℝ) (501874788239/1000000000000 : ℝ) (501874788249/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4215/32768 : ℝ)) (992008784583/1000000000000 : ℝ) (496004392293/500000000000 : ℝ) (501874788239/1000000000000 : ℝ) (501874788249/1000000000000 : ℝ) (794693641957/1000000000000 : ℝ) (794693641977/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1287_exp_lower
  have heNumeric : (513725673637/250000000000 : ℝ)/4 ≤ Real.exp (-42628215352153/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513725673637/250000000000 : ℝ)/4 ≤ Real.exp ((33719/262144 : ℝ)-(794693641977/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33719/262144 : ℝ) (4215/32768 : ℝ) (794693641977/1000000000000 : ℝ) (513725673637/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1288; no trusted numerical premise.
theorem cover8_leaf1288_exp_radius : (199598418065331609/200000000000000000 : ℝ) ≤ Real.exp ((-33721/2097152 : ℝ)/8) ∧ Real.exp ((-33721/2097152 : ℝ)/8) ≤ (498996045163329023/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33721/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1288_exp_lower : (460056757504833141/500000000000000000 : ℝ) ≤ Real.exp ((-1065705352581/1600000000000 : ℝ)/8) ∧ Real.exp ((-1065705352581/1600000000000 : ℝ)/8) ≤ (920113515009666283/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1065705352581/1600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1288_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256862841831/125000000000 : ℝ) ≤ 4*Real.exp (4215/32768 : ℝ)*Real.exp (-mu (radius 8 (33721/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (256862841831/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33721/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1288_exp_radius
  have hrNumeric : (30751536189/31250000000 : ℝ) ≤ Real.exp (-33721/2097152 : ℝ) ∧ Real.exp (-33721/2097152 : ℝ) ≤ (984049158049/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (30751536189/31250000000 : ℝ) ≤ (radius 8 (33721/262144 : ℝ)) ∧ (radius 8 (33721/262144 : ℝ)) ≤ (984049158049/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33721/262144 : ℝ)) (30751536189/31250000000 : ℝ) (984049158049/1000000000000 : ℝ) (1111854703/6250000000 : ℝ) (88948376243/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33721/262144 : ℝ)) (30751536189/31250000000 : ℝ) (984049158049/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33721/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (30751536189/31250000000 : ℝ) (984049158049/1000000000000 : ℝ) (62001536189/62500000000 : ℝ) (39680983161/40000000000 : ℝ) (991992519149/1000000000000 : ℝ) (19839850383/20000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33721/262144 : ℝ)) 1 (62001536189/62500000000 : ℝ) (39680983161/40000000000 : ℝ) (991992519149/1000000000000 : ℝ) (19839850383/20000000000 : ℝ) (496004274543/500000000000 : ℝ) (31000267159/31250000000 : ℝ) (248002137239/250000000000 : ℝ) (496004274479/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33721/262144 : ℝ)) 2 (496004274543/500000000000 : ℝ) (31000267159/31250000000 : ℝ) (248002137239/250000000000 : ℝ) (496004274479/500000000000 : ℝ) (992008549021/1000000000000 : ℝ) (992008549023/1000000000000 : ℝ) (49600427451/50000000000 : ℝ) (992008549023/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33721/262144 : ℝ)) 3 (992008549021/1000000000000 : ℝ) (992008549023/1000000000000 : ℝ) (49600427451/50000000000 : ℝ) (992008549023/1000000000000 : ℝ) (49600427451/50000000000 : ℝ) (992008549023/1000000000000 : ℝ) (49600427451/50000000000 : ℝ) (992008549023/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33721/262144 : ℝ)) 4 (49600427451/50000000000 : ℝ) (992008549023/1000000000000 : ℝ) (49600427451/50000000000 : ℝ) (992008549023/1000000000000 : ℝ) (49600427451/50000000000 : ℝ) (992008549023/1000000000000 : ℝ) (49600427451/50000000000 : ℝ) (992008549023/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33721/262144 : ℝ)) 5 (49600427451/50000000000 : ℝ) (992008549023/1000000000000 : ℝ) (49600427451/50000000000 : ℝ) (992008549023/1000000000000 : ℝ) (49600427451/50000000000 : ℝ) (992008549023/1000000000000 : ℝ) (49600427451/50000000000 : ℝ) (992008549023/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33721/262144 : ℝ)) 6 (49600427451/50000000000 : ℝ) (992008549023/1000000000000 : ℝ) (49600427451/50000000000 : ℝ) (992008549023/1000000000000 : ℝ) (49600427451/50000000000 : ℝ) (992008549023/1000000000000 : ℝ) (49600427451/50000000000 : ℝ) (992008549023/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33721/262144 : ℝ)) 7 (49600427451/50000000000 : ℝ) (992008549023/1000000000000 : ℝ) (49600427451/50000000000 : ℝ) (992008549023/1000000000000 : ℝ) (49600427451/50000000000 : ℝ) (992008549023/1000000000000 : ℝ) (49600427451/50000000000 : ℝ) (992008549023/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33721/262144 : ℝ))) (1111854703/6250000000 : ℝ) (88948376243/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33721/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (1111854703/6250000000 : ℝ) (88948376243/500000000000 : ℝ) (7361854703/12500000000 : ℝ) (588948376243/1000000000000 : ℝ) (421778084399/1000000000000 : ℝ) (421778084407/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33721/262144 : ℝ))) 1 (7361854703/12500000000 : ℝ) (588948376243/1000000000000 : ℝ) (421778084399/1000000000000 : ℝ) (421778084407/1000000000000 : ℝ) (505363230319/1000000000000 : ℝ) (20214529213/40000000000 : ℝ) (498402967427/1000000000000 : ℝ) (249201483717/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33721/262144 : ℝ))) 2 (505363230319/1000000000000 : ℝ) (20214529213/40000000000 : ℝ) (498402967427/1000000000000 : ℝ) (249201483717/500000000000 : ℝ) (501883098873/1000000000000 : ℝ) (392096171/781250000 : ℝ) (100374206571/200000000000 : ℝ) (501871032863/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33721/262144 : ℝ))) 3 (501883098873/1000000000000 : ℝ) (392096171/781250000 : ℝ) (100374206571/200000000000 : ℝ) (501871032863/1000000000000 : ℝ) (62734633233/125000000000 : ℝ) (31367316617/62500000000 : ℝ) (501877065827/1000000000000 : ℝ) (125469266459/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33721/262144 : ℝ))) 4 (62734633233/125000000000 : ℝ) (31367316617/62500000000 : ℝ) (501877065827/1000000000000 : ℝ) (125469266459/250000000000 : ℝ) (100375413169/200000000000 : ℝ) (250938532927/500000000000 : ℝ) (100375413169/200000000000 : ℝ) (250938532927/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33721/262144 : ℝ))) 5 (100375413169/200000000000 : ℝ) (250938532927/500000000000 : ℝ) (100375413169/200000000000 : ℝ) (250938532927/500000000000 : ℝ) (100375413169/200000000000 : ℝ) (250938532927/500000000000 : ℝ) (100375413169/200000000000 : ℝ) (250938532927/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33721/262144 : ℝ))) 6 (100375413169/200000000000 : ℝ) (250938532927/500000000000 : ℝ) (100375413169/200000000000 : ℝ) (250938532927/500000000000 : ℝ) (100375413169/200000000000 : ℝ) (250938532927/500000000000 : ℝ) (100375413169/200000000000 : ℝ) (250938532927/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33721/262144 : ℝ))) 7 (100375413169/200000000000 : ℝ) (250938532927/500000000000 : ℝ) (100375413169/200000000000 : ℝ) (250938532927/500000000000 : ℝ) (100375413169/200000000000 : ℝ) (250938532927/500000000000 : ℝ) (100375413169/200000000000 : ℝ) (250938532927/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33721/262144 : ℝ)) hmem 8 (49600427451/50000000000 : ℝ) (992008549023/1000000000000 : ℝ) (49600427451/50000000000 : ℝ) (992008549023/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33721/262144 : ℝ))) hcmem 8 (100375413169/200000000000 : ℝ) (250938532927/500000000000 : ℝ) (100375413169/200000000000 : ℝ) (250938532927/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33721/262144 : ℝ)) (49600427451/50000000000 : ℝ) (992008549023/1000000000000 : ℝ) (100375413169/200000000000 : ℝ) (250938532927/500000000000 : ℝ) (397348718571/500000000000 : ℝ) (19867435929/25000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1288_exp_lower
  have heNumeric : (256862841831/125000000000 : ℝ)/4 ≤ Real.exp (-1065705352581/1600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256862841831/125000000000 : ℝ)/4 ≤ Real.exp ((4215/32768 : ℝ)-(19867435929/25000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4215/32768 : ℝ) (33721/262144 : ℝ) (19867435929/25000000000 : ℝ) (256862841831/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1289; no trusted numerical premise.
theorem cover8_leaf1289_exp_radius : (498996015420847893/500000000000000000 : ℝ) ≤ Real.exp ((-16861/1048576 : ℝ)/8) ∧ Real.exp ((-16861/1048576 : ℝ)/8) ≤ (997992030841695787/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16861/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1289_exp_lower : (18402270345231193/20000000000000000 : ℝ) ≤ Real.exp ((-42628212850167/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628212850167/64000000000000 : ℝ)/8) ≤ (920113517261559651/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628212850167/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1289_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451387441/500000000000 : ℝ) ≤ 4*Real.exp (33721/262144 : ℝ)*Real.exp (-mu (radius 8 (16861/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451387441/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16861/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1289_exp_radius
  have hrNumeric : (61503043051/62500000000 : ℝ) ≤ Real.exp (-16861/1048576 : ℝ) ∧ Real.exp (-16861/1048576 : ℝ) ≤ (984048688817/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (61503043051/62500000000 : ℝ) ≤ (radius 8 (16861/131072 : ℝ)) ∧ (radius 8 (16861/131072 : ℝ)) ≤ (984048688817/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16861/131072 : ℝ)) (61503043051/62500000000 : ℝ) (984048688817/1000000000000 : ℝ) (44474837013/250000000000 : ℝ) (177899348059/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16861/131072 : ℝ)) (61503043051/62500000000 : ℝ) (984048688817/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16861/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (61503043051/62500000000 : ℝ) (984048688817/1000000000000 : ℝ) (124003043051/125000000000 : ℝ) (992024344409/1000000000000 : ℝ) (991992282639/1000000000000 : ℝ) (12399903533/12500000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16861/131072 : ℝ)) 1 (124003043051/125000000000 : ℝ) (992024344409/1000000000000 : ℝ) (991992282639/1000000000000 : ℝ) (12399903533/12500000000 : ℝ) (992008313523/1000000000000 : ℝ) (39680332541/40000000000 : ℝ) (992008313393/1000000000000 : ℝ) (198401662679/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16861/131072 : ℝ)) 2 (992008313523/1000000000000 : ℝ) (39680332541/40000000000 : ℝ) (992008313393/1000000000000 : ℝ) (198401662679/200000000000 : ℝ) (496004156729/500000000000 : ℝ) (49600415673/50000000000 : ℝ) (992008313457/1000000000000 : ℝ) (49600415673/50000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16861/131072 : ℝ)) 3 (496004156729/500000000000 : ℝ) (49600415673/50000000000 : ℝ) (992008313457/1000000000000 : ℝ) (49600415673/50000000000 : ℝ) (992008313457/1000000000000 : ℝ) (49600415673/50000000000 : ℝ) (992008313457/1000000000000 : ℝ) (49600415673/50000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16861/131072 : ℝ)) 4 (992008313457/1000000000000 : ℝ) (49600415673/50000000000 : ℝ) (992008313457/1000000000000 : ℝ) (49600415673/50000000000 : ℝ) (992008313457/1000000000000 : ℝ) (49600415673/50000000000 : ℝ) (992008313457/1000000000000 : ℝ) (49600415673/50000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16861/131072 : ℝ)) 5 (992008313457/1000000000000 : ℝ) (49600415673/50000000000 : ℝ) (992008313457/1000000000000 : ℝ) (49600415673/50000000000 : ℝ) (992008313457/1000000000000 : ℝ) (49600415673/50000000000 : ℝ) (992008313457/1000000000000 : ℝ) (49600415673/50000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16861/131072 : ℝ)) 6 (992008313457/1000000000000 : ℝ) (49600415673/50000000000 : ℝ) (992008313457/1000000000000 : ℝ) (49600415673/50000000000 : ℝ) (992008313457/1000000000000 : ℝ) (49600415673/50000000000 : ℝ) (992008313457/1000000000000 : ℝ) (49600415673/50000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16861/131072 : ℝ)) 7 (992008313457/1000000000000 : ℝ) (49600415673/50000000000 : ℝ) (992008313457/1000000000000 : ℝ) (49600415673/50000000000 : ℝ) (992008313457/1000000000000 : ℝ) (49600415673/50000000000 : ℝ) (992008313457/1000000000000 : ℝ) (49600415673/50000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16861/131072 : ℝ))) (44474837013/250000000000 : ℝ) (177899348059/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16861/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44474837013/250000000000 : ℝ) (177899348059/1000000000000 : ℝ) (294474837013/500000000000 : ℝ) (58894967403/100000000000 : ℝ) (26361322583/62500000000 : ℝ) (210890580669/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16861/131072 : ℝ))) 1 (294474837013/500000000000 : ℝ) (58894967403/100000000000 : ℝ) (26361322583/62500000000 : ℝ) (210890580669/500000000000 : ℝ) (505365417677/1000000000000 : ℝ) (126341354421/250000000000 : ℝ) (124601333629/250000000000 : ℝ) (19936213381/40000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16861/131072 : ℝ))) 2 (505365417677/1000000000000 : ℝ) (126341354421/250000000000 : ℝ) (124601333629/250000000000 : ℝ) (19936213381/40000000000 : ℝ) (15683918003/31250000000 : ℝ) (100377075221/200000000000 : ℝ) (125468327689/250000000000 : ℝ) (100374662153/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16861/131072 : ℝ))) 3 (15683918003/31250000000 : ℝ) (100377075221/200000000000 : ℝ) (125468327689/250000000000 : ℝ) (100374662153/200000000000 : ℝ) (250939671713/500000000000 : ℝ) (100375868687/200000000000 : ℝ) (501879343389/1000000000000 : ℝ) (501879343399/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16861/131072 : ℝ))) 4 (250939671713/500000000000 : ℝ) (100375868687/200000000000 : ℝ) (501879343389/1000000000000 : ℝ) (501879343399/1000000000000 : ℝ) (501879343407/1000000000000 : ℝ) (501879343417/1000000000000 : ℝ) (501879343407/1000000000000 : ℝ) (501879343417/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16861/131072 : ℝ))) 5 (501879343407/1000000000000 : ℝ) (501879343417/1000000000000 : ℝ) (501879343407/1000000000000 : ℝ) (501879343417/1000000000000 : ℝ) (501879343407/1000000000000 : ℝ) (501879343417/1000000000000 : ℝ) (501879343407/1000000000000 : ℝ) (501879343417/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16861/131072 : ℝ))) 6 (501879343407/1000000000000 : ℝ) (501879343417/1000000000000 : ℝ) (501879343407/1000000000000 : ℝ) (501879343417/1000000000000 : ℝ) (501879343407/1000000000000 : ℝ) (501879343417/1000000000000 : ℝ) (501879343407/1000000000000 : ℝ) (501879343417/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16861/131072 : ℝ))) 7 (501879343407/1000000000000 : ℝ) (501879343417/1000000000000 : ℝ) (501879343407/1000000000000 : ℝ) (501879343417/1000000000000 : ℝ) (501879343407/1000000000000 : ℝ) (501879343417/1000000000000 : ℝ) (501879343407/1000000000000 : ℝ) (501879343417/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16861/131072 : ℝ)) hmem 8 (992008313457/1000000000000 : ℝ) (49600415673/50000000000 : ℝ) (992008313457/1000000000000 : ℝ) (49600415673/50000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16861/131072 : ℝ))) hcmem 8 (501879343407/1000000000000 : ℝ) (501879343417/1000000000000 : ℝ) (501879343407/1000000000000 : ℝ) (501879343417/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16861/131072 : ℝ)) (992008313457/1000000000000 : ℝ) (49600415673/50000000000 : ℝ) (501879343407/1000000000000 : ℝ) (501879343417/1000000000000 : ℝ) (794701232259/1000000000000 : ℝ) (397350616139/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1289_exp_lower
  have heNumeric : (1027451387441/500000000000 : ℝ)/4 ≤ Real.exp (-42628212850167/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451387441/500000000000 : ℝ)/4 ≤ Real.exp ((33721/262144 : ℝ)-(397350616139/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33721/262144 : ℝ) (16861/131072 : ℝ) (397350616139/500000000000 : ℝ) (1027451387441/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1290; no trusted numerical premise.
theorem cover8_leaf1290_exp_radius : (997991971356737071/1000000000000000000 : ℝ) ≤ Real.exp ((-33723/2097152 : ℝ)/8) ∧ Real.exp ((-33723/2097152 : ℝ)/8) ≤ (62374498209796067/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33723/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1290_exp_lower : (115014189940504291/125000000000000000 : ℝ) ≤ Real.exp ((-21314105795603/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314105795603/32000000000000 : ℝ)/8) ≤ (920113519524034329/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314105795603/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1290_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256862851913/125000000000 : ℝ) ≤ 4*Real.exp (16861/131072 : ℝ)*Real.exp (-mu (radius 8 (33723/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (256862851913/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33723/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1290_exp_radius
  have hrNumeric : (492024109793/500000000000 : ℝ) ≤ Real.exp (-33723/2097152 : ℝ) ∧ Real.exp (-33723/2097152 : ℝ) ≤ (984048219587/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492024109793/500000000000 : ℝ) ≤ (radius 8 (33723/262144 : ℝ)) ∧ (radius 8 (33723/262144 : ℝ)) ≤ (984048219587/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33723/262144 : ℝ)) (492024109793/500000000000 : ℝ) (984048219587/1000000000000 : ℝ) (88950971787/500000000000 : ℝ) (177901943581/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33723/262144 : ℝ)) (492024109793/500000000000 : ℝ) (984048219587/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33723/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492024109793/500000000000 : ℝ) (984048219587/1000000000000 : ℝ) (992024109793/1000000000000 : ℝ) (496012054897/500000000000 : ℝ) (99199204613/100000000000 : ℝ) (991992046131/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33723/262144 : ℝ)) 1 (992024109793/1000000000000 : ℝ) (496012054897/500000000000 : ℝ) (99199204613/100000000000 : ℝ) (991992046131/1000000000000 : ℝ) (992008077961/1000000000000 : ℝ) (992008077963/1000000000000 : ℝ) (992008077831/1000000000000 : ℝ) (992008077833/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33723/262144 : ℝ)) 2 (992008077961/1000000000000 : ℝ) (992008077963/1000000000000 : ℝ) (992008077831/1000000000000 : ℝ) (992008077833/1000000000000 : ℝ) (124001009737/125000000000 : ℝ) (496004038949/500000000000 : ℝ) (198401615579/200000000000 : ℝ) (496004038949/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33723/262144 : ℝ)) 3 (124001009737/125000000000 : ℝ) (496004038949/500000000000 : ℝ) (198401615579/200000000000 : ℝ) (496004038949/500000000000 : ℝ) (198401615579/200000000000 : ℝ) (496004038949/500000000000 : ℝ) (198401615579/200000000000 : ℝ) (496004038949/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33723/262144 : ℝ)) 4 (198401615579/200000000000 : ℝ) (496004038949/500000000000 : ℝ) (198401615579/200000000000 : ℝ) (496004038949/500000000000 : ℝ) (198401615579/200000000000 : ℝ) (496004038949/500000000000 : ℝ) (198401615579/200000000000 : ℝ) (496004038949/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33723/262144 : ℝ)) 5 (198401615579/200000000000 : ℝ) (496004038949/500000000000 : ℝ) (198401615579/200000000000 : ℝ) (496004038949/500000000000 : ℝ) (198401615579/200000000000 : ℝ) (496004038949/500000000000 : ℝ) (198401615579/200000000000 : ℝ) (496004038949/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33723/262144 : ℝ)) 6 (198401615579/200000000000 : ℝ) (496004038949/500000000000 : ℝ) (198401615579/200000000000 : ℝ) (496004038949/500000000000 : ℝ) (198401615579/200000000000 : ℝ) (496004038949/500000000000 : ℝ) (198401615579/200000000000 : ℝ) (496004038949/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33723/262144 : ℝ)) 7 (198401615579/200000000000 : ℝ) (496004038949/500000000000 : ℝ) (198401615579/200000000000 : ℝ) (496004038949/500000000000 : ℝ) (198401615579/200000000000 : ℝ) (496004038949/500000000000 : ℝ) (198401615579/200000000000 : ℝ) (496004038949/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33723/262144 : ℝ))) (88950971787/500000000000 : ℝ) (177901943581/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33723/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88950971787/500000000000 : ℝ) (177901943581/1000000000000 : ℝ) (588950971787/1000000000000 : ℝ) (588950971791/1000000000000 : ℝ) (13180757443/31250000000 : ℝ) (84356847637/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33723/262144 : ℝ))) 1 (588950971787/1000000000000 : ℝ) (588950971791/1000000000000 : ℝ) (13180757443/31250000000 : ℝ) (84356847637/200000000000 : ℝ) (505367604981/1000000000000 : ℝ) (126341901247/250000000000 : ℝ) (498407701543/1000000000000 : ℝ) (498407701551/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33723/262144 : ℝ))) 2 (505367604981/1000000000000 : ℝ) (126341901247/250000000000 : ℝ) (498407701543/1000000000000 : ℝ) (498407701551/1000000000000 : ℝ) (250943826631/500000000000 : ℝ) (50188765327/100000000000 : ℝ) (2509377943/5000000000 : ℝ) (980225759/1953125000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33723/262144 : ℝ))) 3 (250943826631/500000000000 : ℝ) (50188765327/100000000000 : ℝ) (2509377943/5000000000 : ℝ) (980225759/1953125000 : ℝ) (501881620931/1000000000000 : ℝ) (501881620939/1000000000000 : ℝ) (250940810447/500000000000 : ℝ) (501881620903/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33723/262144 : ℝ))) 4 (501881620931/1000000000000 : ℝ) (501881620939/1000000000000 : ℝ) (250940810447/500000000000 : ℝ) (501881620903/1000000000000 : ℝ) (31367601307/62500000000 : ℝ) (501881620921/1000000000000 : ℝ) (31367601307/62500000000 : ℝ) (501881620921/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33723/262144 : ℝ))) 5 (31367601307/62500000000 : ℝ) (501881620921/1000000000000 : ℝ) (31367601307/62500000000 : ℝ) (501881620921/1000000000000 : ℝ) (31367601307/62500000000 : ℝ) (501881620921/1000000000000 : ℝ) (31367601307/62500000000 : ℝ) (501881620921/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33723/262144 : ℝ))) 6 (31367601307/62500000000 : ℝ) (501881620921/1000000000000 : ℝ) (31367601307/62500000000 : ℝ) (501881620921/1000000000000 : ℝ) (31367601307/62500000000 : ℝ) (501881620921/1000000000000 : ℝ) (31367601307/62500000000 : ℝ) (501881620921/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33723/262144 : ℝ))) 7 (31367601307/62500000000 : ℝ) (501881620921/1000000000000 : ℝ) (31367601307/62500000000 : ℝ) (501881620921/1000000000000 : ℝ) (31367601307/62500000000 : ℝ) (501881620921/1000000000000 : ℝ) (31367601307/62500000000 : ℝ) (501881620921/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33723/262144 : ℝ)) hmem 8 (198401615579/200000000000 : ℝ) (496004038949/500000000000 : ℝ) (198401615579/200000000000 : ℝ) (496004038949/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33723/262144 : ℝ))) hcmem 8 (31367601307/62500000000 : ℝ) (501881620921/1000000000000 : ℝ) (31367601307/62500000000 : ℝ) (501881620921/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33723/262144 : ℝ)) (198401615579/200000000000 : ℝ) (496004038949/500000000000 : ℝ) (31367601307/62500000000 : ℝ) (501881620921/1000000000000 : ℝ) (397352513643/500000000000 : ℝ) (99338128413/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1290_exp_lower
  have heNumeric : (256862851913/125000000000 : ℝ)/4 ≤ Real.exp (-21314105795603/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256862851913/125000000000 : ℝ)/4 ≤ Real.exp ((16861/131072 : ℝ)-(99338128413/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16861/131072 : ℝ) (33723/262144 : ℝ) (99338128413/125000000000 : ℝ) (256862851913/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1291; no trusted numerical premise.
theorem cover8_leaf1291_exp_radius : (997991911871781903/1000000000000000000 : ℝ) ≤ Real.exp ((-8431/524288 : ℝ)/8) ∧ Real.exp ((-8431/524288 : ℝ)/8) ≤ (62374494491986369/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8431/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1291_exp_lower : (5750709511211687/6250000000000000 : ℝ) ≤ Real.exp ((-42628210328149/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628210328149/64000000000000 : ℝ)/8) ≤ (920113521793869921/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628210328149/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1291_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451427929/500000000000 : ℝ) ≤ 4*Real.exp (33723/262144 : ℝ)*Real.exp (-mu (radius 8 (8431/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451427929/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8431/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1291_exp_radius
  have hrNumeric : (196809550071/200000000000 : ℝ) ≤ Real.exp (-8431/524288 : ℝ) ∧ Real.exp (-8431/524288 : ℝ) ≤ (246011937589/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196809550071/200000000000 : ℝ) ≤ (radius 8 (8431/65536 : ℝ)) ∧ (radius 8 (8431/65536 : ℝ)) ≤ (246011937589/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8431/65536 : ℝ)) (196809550071/200000000000 : ℝ) (246011937589/250000000000 : ℝ) (177904539063/1000000000000 : ℝ) (177904539069/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8431/65536 : ℝ)) (196809550071/200000000000 : ℝ) (246011937589/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8431/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196809550071/200000000000 : ℝ) (246011937589/250000000000 : ℝ) (992023875177/1000000000000 : ℝ) (496011937589/500000000000 : ℝ) (49599590481/50000000000 : ℝ) (495995904811/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8431/65536 : ℝ)) 1 (992023875177/1000000000000 : ℝ) (496011937589/500000000000 : ℝ) (49599590481/50000000000 : ℝ) (495995904811/500000000000 : ℝ) (496003921199/500000000000 : ℝ) (1240009803/1250000000 : ℝ) (248001960567/250000000000 : ℝ) (992007842271/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8431/65536 : ℝ)) 2 (496003921199/500000000000 : ℝ) (1240009803/1250000000 : ℝ) (248001960567/250000000000 : ℝ) (992007842271/1000000000000 : ℝ) (992007842333/1000000000000 : ℝ) (31000245073/31250000000 : ℝ) (248001960583/250000000000 : ℝ) (31000245073/31250000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8431/65536 : ℝ)) 3 (992007842333/1000000000000 : ℝ) (31000245073/31250000000 : ℝ) (248001960583/250000000000 : ℝ) (31000245073/31250000000 : ℝ) (248001960583/250000000000 : ℝ) (31000245073/31250000000 : ℝ) (248001960583/250000000000 : ℝ) (31000245073/31250000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8431/65536 : ℝ)) 4 (248001960583/250000000000 : ℝ) (31000245073/31250000000 : ℝ) (248001960583/250000000000 : ℝ) (31000245073/31250000000 : ℝ) (248001960583/250000000000 : ℝ) (31000245073/31250000000 : ℝ) (248001960583/250000000000 : ℝ) (31000245073/31250000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8431/65536 : ℝ)) 5 (248001960583/250000000000 : ℝ) (31000245073/31250000000 : ℝ) (248001960583/250000000000 : ℝ) (31000245073/31250000000 : ℝ) (248001960583/250000000000 : ℝ) (31000245073/31250000000 : ℝ) (248001960583/250000000000 : ℝ) (31000245073/31250000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8431/65536 : ℝ)) 6 (248001960583/250000000000 : ℝ) (31000245073/31250000000 : ℝ) (248001960583/250000000000 : ℝ) (31000245073/31250000000 : ℝ) (248001960583/250000000000 : ℝ) (31000245073/31250000000 : ℝ) (248001960583/250000000000 : ℝ) (31000245073/31250000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8431/65536 : ℝ)) 7 (248001960583/250000000000 : ℝ) (31000245073/31250000000 : ℝ) (248001960583/250000000000 : ℝ) (31000245073/31250000000 : ℝ) (248001960583/250000000000 : ℝ) (31000245073/31250000000 : ℝ) (248001960583/250000000000 : ℝ) (31000245073/31250000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8431/65536 : ℝ))) (177904539063/1000000000000 : ℝ) (177904539069/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8431/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177904539063/1000000000000 : ℝ) (177904539069/1000000000000 : ℝ) (588952269531/1000000000000 : ℝ) (117790453907/200000000000 : ℝ) (210893657481/500000000000 : ℝ) (42178731497/100000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8431/65536 : ℝ))) 1 (588952269531/1000000000000 : ℝ) (117790453907/200000000000 : ℝ) (210893657481/500000000000 : ℝ) (42178731497/100000000000 : ℝ) (252684896123/500000000000 : ℝ) (505369792253/1000000000000 : ℝ) (124602517131/250000000000 : ℝ) (498410068531/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8431/65536 : ℝ))) 2 (252684896123/500000000000 : ℝ) (505369792253/1000000000000 : ℝ) (124602517131/250000000000 : ℝ) (498410068531/1000000000000 : ℝ) (100377986077/200000000000 : ℝ) (62736241299/125000000000 : ℝ) (501877866401/1000000000000 : ℝ) (501877866409/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8431/65536 : ℝ))) 3 (100377986077/200000000000 : ℝ) (62736241299/125000000000 : ℝ) (501877866401/1000000000000 : ℝ) (501877866409/1000000000000 : ℝ) (501883898393/1000000000000 : ℝ) (501883898401/1000000000000 : ℝ) (125470974589/250000000000 : ℝ) (100376779673/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8431/65536 : ℝ))) 4 (501883898393/1000000000000 : ℝ) (501883898401/1000000000000 : ℝ) (125470974589/250000000000 : ℝ) (100376779673/200000000000 : ℝ) (250941949187/500000000000 : ℝ) (501883898383/1000000000000 : ℝ) (250941949187/500000000000 : ℝ) (501883898383/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8431/65536 : ℝ))) 5 (250941949187/500000000000 : ℝ) (501883898383/1000000000000 : ℝ) (250941949187/500000000000 : ℝ) (501883898383/1000000000000 : ℝ) (250941949187/500000000000 : ℝ) (501883898383/1000000000000 : ℝ) (250941949187/500000000000 : ℝ) (501883898383/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8431/65536 : ℝ))) 6 (250941949187/500000000000 : ℝ) (501883898383/1000000000000 : ℝ) (250941949187/500000000000 : ℝ) (501883898383/1000000000000 : ℝ) (250941949187/500000000000 : ℝ) (501883898383/1000000000000 : ℝ) (250941949187/500000000000 : ℝ) (501883898383/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8431/65536 : ℝ))) 7 (250941949187/500000000000 : ℝ) (501883898383/1000000000000 : ℝ) (250941949187/500000000000 : ℝ) (501883898383/1000000000000 : ℝ) (250941949187/500000000000 : ℝ) (501883898383/1000000000000 : ℝ) (250941949187/500000000000 : ℝ) (501883898383/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8431/65536 : ℝ)) hmem 8 (248001960583/250000000000 : ℝ) (31000245073/31250000000 : ℝ) (248001960583/250000000000 : ℝ) (31000245073/31250000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8431/65536 : ℝ))) hcmem 8 (250941949187/500000000000 : ℝ) (501883898383/1000000000000 : ℝ) (250941949187/500000000000 : ℝ) (501883898383/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8431/65536 : ℝ)) (248001960583/250000000000 : ℝ) (31000245073/31250000000 : ℝ) (250941949187/500000000000 : ℝ) (501883898383/1000000000000 : ℝ) (794708822247/1000000000000 : ℝ) (397354411133/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1291_exp_lower
  have heNumeric : (1027451427929/500000000000 : ℝ)/4 ≤ Real.exp (-42628210328149/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451427929/500000000000 : ℝ)/4 ≤ Real.exp ((33723/262144 : ℝ)-(397354411133/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33723/262144 : ℝ) (8431/65536 : ℝ) (397354411133/500000000000 : ℝ) (1027451427929/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1292; no trusted numerical premise.
theorem cover8_leaf1292_exp_radius : (24949796309670757/25000000000000000 : ℝ) ≤ Real.exp ((-33725/2097152 : ℝ)/8) ∧ Real.exp ((-33725/2097152 : ℝ)/8) ≤ (997991852386830281/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33725/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1292_exp_lower : (920113524073481723/1000000000000000000 : ℝ) ≤ Real.exp ((-10657052264913/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657052264913/16000000000000 : ℝ)/8) ≤ (230028381018370431/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657052264913/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1292_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902896587/1000000000000 : ℝ) ≤ 4*Real.exp (8431/65536 : ℝ)*Real.exp (-mu (radius 8 (33725/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902896587/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33725/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1292_exp_radius
  have hrNumeric : (7872378249/8000000000 : ℝ) ≤ Real.exp (-33725/2097152 : ℝ) ∧ Real.exp (-33725/2097152 : ℝ) ≤ (492023640563/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (7872378249/8000000000 : ℝ) ≤ (radius 8 (33725/262144 : ℝ)) ∧ (radius 8 (33725/262144 : ℝ)) ≤ (492023640563/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33725/262144 : ℝ)) (7872378249/8000000000 : ℝ) (492023640563/500000000000 : ℝ) (177907134507/1000000000000 : ℝ) (177907134513/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33725/262144 : ℝ)) (7872378249/8000000000 : ℝ) (492023640563/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33725/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (7872378249/8000000000 : ℝ) (492023640563/500000000000 : ℝ) (496011820281/500000000000 : ℝ) (992023640563/1000000000000 : ℝ) (991991573111/1000000000000 : ℝ) (991991573113/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33725/262144 : ℝ)) 1 (496011820281/500000000000 : ℝ) (992023640563/1000000000000 : ℝ) (991991573111/1000000000000 : ℝ) (991991573113/1000000000000 : ℝ) (248001901709/250000000000 : ℝ) (496003803419/500000000000 : ℝ) (496003803353/500000000000 : ℝ) (992007606709/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33725/262144 : ℝ)) 2 (248001901709/250000000000 : ℝ) (496003803419/500000000000 : ℝ) (496003803353/500000000000 : ℝ) (992007606709/1000000000000 : ℝ) (992007606771/1000000000000 : ℝ) (496003803387/500000000000 : ℝ) (99200760677/100000000000 : ℝ) (496003803387/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33725/262144 : ℝ)) 3 (992007606771/1000000000000 : ℝ) (496003803387/500000000000 : ℝ) (99200760677/100000000000 : ℝ) (496003803387/500000000000 : ℝ) (99200760677/100000000000 : ℝ) (496003803387/500000000000 : ℝ) (99200760677/100000000000 : ℝ) (496003803387/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33725/262144 : ℝ)) 4 (99200760677/100000000000 : ℝ) (496003803387/500000000000 : ℝ) (99200760677/100000000000 : ℝ) (496003803387/500000000000 : ℝ) (99200760677/100000000000 : ℝ) (496003803387/500000000000 : ℝ) (99200760677/100000000000 : ℝ) (496003803387/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33725/262144 : ℝ)) 5 (99200760677/100000000000 : ℝ) (496003803387/500000000000 : ℝ) (99200760677/100000000000 : ℝ) (496003803387/500000000000 : ℝ) (99200760677/100000000000 : ℝ) (496003803387/500000000000 : ℝ) (99200760677/100000000000 : ℝ) (496003803387/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33725/262144 : ℝ)) 6 (99200760677/100000000000 : ℝ) (496003803387/500000000000 : ℝ) (99200760677/100000000000 : ℝ) (496003803387/500000000000 : ℝ) (99200760677/100000000000 : ℝ) (496003803387/500000000000 : ℝ) (99200760677/100000000000 : ℝ) (496003803387/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33725/262144 : ℝ)) 7 (99200760677/100000000000 : ℝ) (496003803387/500000000000 : ℝ) (99200760677/100000000000 : ℝ) (496003803387/500000000000 : ℝ) (99200760677/100000000000 : ℝ) (496003803387/500000000000 : ℝ) (99200760677/100000000000 : ℝ) (496003803387/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33725/262144 : ℝ))) (177907134507/1000000000000 : ℝ) (177907134513/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33725/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177907134507/1000000000000 : ℝ) (177907134513/1000000000000 : ℝ) (588953567253/1000000000000 : ℝ) (588953567257/1000000000000 : ℝ) (52723798959/125000000000 : ℝ) (659047487/1562500000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33725/262144 : ℝ))) 1 (588953567253/1000000000000 : ℝ) (588953567257/1000000000000 : ℝ) (52723798959/125000000000 : ℝ) (659047487/1562500000 : ℝ) (252685989731/500000000000 : ℝ) (505371979469/1000000000000 : ℝ) (498412435447/1000000000000 : ℝ) (249206217727/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33725/262144 : ℝ))) 2 (252685989731/500000000000 : ℝ) (505371979469/1000000000000 : ℝ) (498412435447/1000000000000 : ℝ) (249206217727/500000000000 : ℝ) (250946103727/500000000000 : ℝ) (250946103731/500000000000 : ℝ) (125470036037/250000000000 : ℝ) (125470036039/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33725/262144 : ℝ))) 3 (250946103727/500000000000 : ℝ) (250946103731/500000000000 : ℝ) (125470036037/250000000000 : ℝ) (125470036039/250000000000 : ℝ) (501886175801/1000000000000 : ℝ) (501886175809/1000000000000 : ℝ) (125471543941/250000000000 : ℝ) (501886175773/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33725/262144 : ℝ))) 4 (501886175801/1000000000000 : ℝ) (501886175809/1000000000000 : ℝ) (125471543941/250000000000 : ℝ) (501886175773/1000000000000 : ℝ) (250943087891/500000000000 : ℝ) (501886175791/1000000000000 : ℝ) (250943087891/500000000000 : ℝ) (501886175791/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33725/262144 : ℝ))) 5 (250943087891/500000000000 : ℝ) (501886175791/1000000000000 : ℝ) (250943087891/500000000000 : ℝ) (501886175791/1000000000000 : ℝ) (250943087891/500000000000 : ℝ) (501886175791/1000000000000 : ℝ) (250943087891/500000000000 : ℝ) (501886175791/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33725/262144 : ℝ))) 6 (250943087891/500000000000 : ℝ) (501886175791/1000000000000 : ℝ) (250943087891/500000000000 : ℝ) (501886175791/1000000000000 : ℝ) (250943087891/500000000000 : ℝ) (501886175791/1000000000000 : ℝ) (250943087891/500000000000 : ℝ) (501886175791/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33725/262144 : ℝ))) 7 (250943087891/500000000000 : ℝ) (501886175791/1000000000000 : ℝ) (250943087891/500000000000 : ℝ) (501886175791/1000000000000 : ℝ) (250943087891/500000000000 : ℝ) (501886175791/1000000000000 : ℝ) (250943087891/500000000000 : ℝ) (501886175791/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33725/262144 : ℝ)) hmem 8 (99200760677/100000000000 : ℝ) (496003803387/500000000000 : ℝ) (99200760677/100000000000 : ℝ) (496003803387/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33725/262144 : ℝ))) hcmem 8 (250943087891/500000000000 : ℝ) (501886175791/1000000000000 : ℝ) (250943087891/500000000000 : ℝ) (501886175791/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33725/262144 : ℝ)) (99200760677/100000000000 : ℝ) (496003803387/500000000000 : ℝ) (250943087891/500000000000 : ℝ) (501886175791/1000000000000 : ℝ) (6357700937/8000000000 : ℝ) (794712617143/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1292_exp_lower
  have heNumeric : (2054902896587/1000000000000 : ℝ)/4 ≤ Real.exp (-10657052264913/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902896587/1000000000000 : ℝ)/4 ≤ Real.exp ((8431/65536 : ℝ)-(794712617143/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8431/65536 : ℝ) (33725/262144 : ℝ) (794712617143/1000000000000 : ℝ) (2054902896587/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1293; no trusted numerical premise.
theorem cover8_leaf1293_exp_radius : (498995896450941101/500000000000000000 : ℝ) ≤ Real.exp ((-16863/1048576 : ℝ)/8) ∧ Real.exp ((-16863/1048576 : ℝ)/8) ≤ (997991792901882203/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16863/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1293_exp_lower : (230028381590199871/250000000000000000 : ℝ) ≤ Real.exp ((-42628207786867/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628207786867/64000000000000 : ℝ)/8) ≤ (184022705272159897/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628207786867/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1293_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902937453/1000000000000 : ℝ) ≤ 4*Real.exp (33725/262144 : ℝ)*Real.exp (-mu (radius 8 (16863/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902937453/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16863/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1293_exp_radius
  have hrNumeric : (492023405947/500000000000 : ℝ) ≤ Real.exp (-16863/1048576 : ℝ) ∧ Real.exp (-16863/1048576 : ℝ) ≤ (196809362379/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492023405947/500000000000 : ℝ) ≤ (radius 8 (16863/131072 : ℝ)) ∧ (radius 8 (16863/131072 : ℝ)) ≤ (196809362379/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16863/131072 : ℝ)) (492023405947/500000000000 : ℝ) (196809362379/200000000000 : ℝ) (177909729917/1000000000000 : ℝ) (177909729923/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16863/131072 : ℝ)) (492023405947/500000000000 : ℝ) (196809362379/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16863/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492023405947/500000000000 : ℝ) (196809362379/200000000000 : ℝ) (992023405947/1000000000000 : ℝ) (248005851487/250000000000 : ℝ) (495995668301/500000000000 : ℝ) (991991336603/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16863/131072 : ℝ)) 1 (992023405947/1000000000000 : ℝ) (248005851487/250000000000 : ℝ) (495995668301/500000000000 : ℝ) (991991336603/1000000000000 : ℝ) (496003685637/500000000000 : ℝ) (248001842819/250000000000 : ℝ) (124000921393/125000000000 : ℝ) (496003685573/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16863/131072 : ℝ)) 2 (496003685637/500000000000 : ℝ) (248001842819/250000000000 : ℝ) (124000921393/125000000000 : ℝ) (496003685573/500000000000 : ℝ) (992007371209/1000000000000 : ℝ) (992007371211/1000000000000 : ℝ) (124000921401/125000000000 : ℝ) (992007371211/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16863/131072 : ℝ)) 3 (992007371209/1000000000000 : ℝ) (992007371211/1000000000000 : ℝ) (124000921401/125000000000 : ℝ) (992007371211/1000000000000 : ℝ) (124000921401/125000000000 : ℝ) (992007371211/1000000000000 : ℝ) (124000921401/125000000000 : ℝ) (992007371211/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16863/131072 : ℝ)) 4 (124000921401/125000000000 : ℝ) (992007371211/1000000000000 : ℝ) (124000921401/125000000000 : ℝ) (992007371211/1000000000000 : ℝ) (124000921401/125000000000 : ℝ) (992007371211/1000000000000 : ℝ) (124000921401/125000000000 : ℝ) (992007371211/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16863/131072 : ℝ)) 5 (124000921401/125000000000 : ℝ) (992007371211/1000000000000 : ℝ) (124000921401/125000000000 : ℝ) (992007371211/1000000000000 : ℝ) (124000921401/125000000000 : ℝ) (992007371211/1000000000000 : ℝ) (124000921401/125000000000 : ℝ) (992007371211/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16863/131072 : ℝ)) 6 (124000921401/125000000000 : ℝ) (992007371211/1000000000000 : ℝ) (124000921401/125000000000 : ℝ) (992007371211/1000000000000 : ℝ) (124000921401/125000000000 : ℝ) (992007371211/1000000000000 : ℝ) (124000921401/125000000000 : ℝ) (992007371211/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16863/131072 : ℝ)) 7 (124000921401/125000000000 : ℝ) (992007371211/1000000000000 : ℝ) (124000921401/125000000000 : ℝ) (992007371211/1000000000000 : ℝ) (124000921401/125000000000 : ℝ) (992007371211/1000000000000 : ℝ) (124000921401/125000000000 : ℝ) (992007371211/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16863/131072 : ℝ))) (177909729917/1000000000000 : ℝ) (177909729923/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16863/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177909729917/1000000000000 : ℝ) (177909729923/1000000000000 : ℝ) (294477432479/500000000000 : ℝ) (294477432481/500000000000 : ℝ) (421793468319/1000000000000 : ℝ) (421793468327/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16863/131072 : ℝ))) 1 (294477432479/500000000000 : ℝ) (294477432481/500000000000 : ℝ) (421793468319/1000000000000 : ℝ) (421793468327/1000000000000 : ℝ) (252687083319/500000000000 : ℝ) (101074833329/200000000000 : ℝ) (249207401161/500000000000 : ℝ) (498414802329/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16863/131072 : ℝ))) 2 (252687083319/500000000000 : ℝ) (101074833329/200000000000 : ℝ) (249207401161/500000000000 : ℝ) (498414802329/1000000000000 : ℝ) (196052533/390625000 : ℝ) (501894484487/1000000000000 : ℝ) (501882421851/1000000000000 : ℝ) (501882421859/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16863/131072 : ℝ))) 3 (196052533/390625000 : ℝ) (501894484487/1000000000000 : ℝ) (501882421851/1000000000000 : ℝ) (501882421859/1000000000000 : ℝ) (100377690633/200000000000 : ℝ) (501888453173/1000000000000 : ℝ) (501888453129/1000000000000 : ℝ) (501888453137/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16863/131072 : ℝ))) 4 (100377690633/200000000000 : ℝ) (501888453173/1000000000000 : ℝ) (501888453129/1000000000000 : ℝ) (501888453137/1000000000000 : ℝ) (501888453147/1000000000000 : ℝ) (100377690631/200000000000 : ℝ) (250944226573/500000000000 : ℝ) (100377690631/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16863/131072 : ℝ))) 5 (501888453147/1000000000000 : ℝ) (100377690631/200000000000 : ℝ) (250944226573/500000000000 : ℝ) (100377690631/200000000000 : ℝ) (250944226573/500000000000 : ℝ) (100377690631/200000000000 : ℝ) (250944226573/500000000000 : ℝ) (100377690631/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16863/131072 : ℝ))) 6 (250944226573/500000000000 : ℝ) (100377690631/200000000000 : ℝ) (250944226573/500000000000 : ℝ) (100377690631/200000000000 : ℝ) (250944226573/500000000000 : ℝ) (100377690631/200000000000 : ℝ) (250944226573/500000000000 : ℝ) (100377690631/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16863/131072 : ℝ))) 7 (250944226573/500000000000 : ℝ) (100377690631/200000000000 : ℝ) (250944226573/500000000000 : ℝ) (100377690631/200000000000 : ℝ) (250944226573/500000000000 : ℝ) (100377690631/200000000000 : ℝ) (250944226573/500000000000 : ℝ) (100377690631/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16863/131072 : ℝ)) hmem 8 (124000921401/125000000000 : ℝ) (992007371211/1000000000000 : ℝ) (124000921401/125000000000 : ℝ) (992007371211/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16863/131072 : ℝ))) hcmem 8 (250944226573/500000000000 : ℝ) (100377690631/200000000000 : ℝ) (250944226573/500000000000 : ℝ) (100377690631/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16863/131072 : ℝ)) (124000921401/125000000000 : ℝ) (992007371211/1000000000000 : ℝ) (250944226573/500000000000 : ℝ) (100377690631/200000000000 : ℝ) (158943282387/200000000000 : ℝ) (794716411953/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1293_exp_lower
  have heNumeric : (2054902937453/1000000000000 : ℝ)/4 ≤ Real.exp (-42628207786867/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902937453/1000000000000 : ℝ)/4 ≤ Real.exp ((33725/262144 : ℝ)-(794716411953/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33725/262144 : ℝ) (16863/131072 : ℝ) (794716411953/1000000000000 : ℝ) (2054902937453/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1294; no trusted numerical premise.
theorem cover8_leaf1294_exp_radius : (99799173341693767/100000000000000000 : ℝ) ≤ Real.exp ((-33727/2097152 : ℝ)/8) ∧ Real.exp ((-33727/2097152 : ℝ)/8) ≤ (997991733416937671/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33727/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1294_exp_lower : (184022705731463677/200000000000000000 : ℝ) ≤ Real.exp ((-21314103254481/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314103254481/32000000000000 : ℝ)/8) ≤ (460056764328659193/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314103254481/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1294_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513725744621/250000000000 : ℝ) ≤ 4*Real.exp (16863/131072 : ℝ)*Real.exp (-mu (radius 8 (33727/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (513725744621/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33727/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1294_exp_radius
  have hrNumeric : (123005792833/125000000000 : ℝ) ≤ Real.exp (-33727/2097152 : ℝ) ∧ Real.exp (-33727/2097152 : ℝ) ≤ (196809268533/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (123005792833/125000000000 : ℝ) ≤ (radius 8 (33727/262144 : ℝ)) ∧ (radius 8 (33727/262144 : ℝ)) ≤ (196809268533/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33727/262144 : ℝ)) (123005792833/125000000000 : ℝ) (196809268533/200000000000 : ℝ) (177912325283/1000000000000 : ℝ) (177912325289/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33727/262144 : ℝ)) (123005792833/125000000000 : ℝ) (196809268533/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33727/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (123005792833/125000000000 : ℝ) (196809268533/200000000000 : ℝ) (248005792833/250000000000 : ℝ) (992023171333/1000000000000 : ℝ) (991991100093/1000000000000 : ℝ) (495995550047/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33727/262144 : ℝ)) 1 (248005792833/250000000000 : ℝ) (992023171333/1000000000000 : ℝ) (991991100093/1000000000000 : ℝ) (495995550047/500000000000 : ℝ) (31000222991/31250000000 : ℝ) (496003567857/500000000000 : ℝ) (496003567791/500000000000 : ℝ) (31000222987/31250000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33727/262144 : ℝ)) 2 (31000222991/31250000000 : ℝ) (496003567857/500000000000 : ℝ) (496003567791/500000000000 : ℝ) (31000222987/31250000000 : ℝ) (992007135647/1000000000000 : ℝ) (992007135649/1000000000000 : ℝ) (496003567823/500000000000 : ℝ) (992007135649/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33727/262144 : ℝ)) 3 (992007135647/1000000000000 : ℝ) (992007135649/1000000000000 : ℝ) (496003567823/500000000000 : ℝ) (992007135649/1000000000000 : ℝ) (496003567823/500000000000 : ℝ) (992007135649/1000000000000 : ℝ) (496003567823/500000000000 : ℝ) (992007135649/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33727/262144 : ℝ)) 4 (496003567823/500000000000 : ℝ) (992007135649/1000000000000 : ℝ) (496003567823/500000000000 : ℝ) (992007135649/1000000000000 : ℝ) (496003567823/500000000000 : ℝ) (992007135649/1000000000000 : ℝ) (496003567823/500000000000 : ℝ) (992007135649/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33727/262144 : ℝ)) 5 (496003567823/500000000000 : ℝ) (992007135649/1000000000000 : ℝ) (496003567823/500000000000 : ℝ) (992007135649/1000000000000 : ℝ) (496003567823/500000000000 : ℝ) (992007135649/1000000000000 : ℝ) (496003567823/500000000000 : ℝ) (992007135649/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33727/262144 : ℝ)) 6 (496003567823/500000000000 : ℝ) (992007135649/1000000000000 : ℝ) (496003567823/500000000000 : ℝ) (992007135649/1000000000000 : ℝ) (496003567823/500000000000 : ℝ) (992007135649/1000000000000 : ℝ) (496003567823/500000000000 : ℝ) (992007135649/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33727/262144 : ℝ)) 7 (496003567823/500000000000 : ℝ) (992007135649/1000000000000 : ℝ) (496003567823/500000000000 : ℝ) (992007135649/1000000000000 : ℝ) (496003567823/500000000000 : ℝ) (992007135649/1000000000000 : ℝ) (496003567823/500000000000 : ℝ) (992007135649/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33727/262144 : ℝ))) (177912325283/1000000000000 : ℝ) (177912325289/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33727/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177912325283/1000000000000 : ℝ) (177912325289/1000000000000 : ℝ) (588956162641/1000000000000 : ℝ) (117791232529/200000000000 : ℝ) (105449136223/250000000000 : ℝ) (4217965449/10000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33727/262144 : ℝ))) 1 (588956162641/1000000000000 : ℝ) (117791232529/200000000000 : ℝ) (105449136223/250000000000 : ℝ) (4217965449/10000000000 : ℝ) (252688176883/500000000000 : ℝ) (505376353773/1000000000000 : ℝ) (498417169141/1000000000000 : ℝ) (124604292287/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33727/262144 : ℝ))) 2 (252688176883/500000000000 : ℝ) (505376353773/1000000000000 : ℝ) (498417169141/1000000000000 : ℝ) (124604292287/250000000000 : ℝ) (501896761453/1000000000000 : ℝ) (501896761461/1000000000000 : ℝ) (250942349751/500000000000 : ℝ) (50188469951/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33727/262144 : ℝ))) 3 (501896761453/1000000000000 : ℝ) (501896761461/1000000000000 : ℝ) (250942349751/500000000000 : ℝ) (50188469951/100000000000 : ℝ) (501890730477/1000000000000 : ℝ) (250945365243/500000000000 : ℝ) (501890730441/1000000000000 : ℝ) (10037814609/20000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33727/262144 : ℝ))) 4 (501890730477/1000000000000 : ℝ) (250945365243/500000000000 : ℝ) (501890730441/1000000000000 : ℝ) (10037814609/20000000000 : ℝ) (501890730459/1000000000000 : ℝ) (125472682617/250000000000 : ℝ) (250945365229/500000000000 : ℝ) (125472682617/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33727/262144 : ℝ))) 5 (501890730459/1000000000000 : ℝ) (125472682617/250000000000 : ℝ) (250945365229/500000000000 : ℝ) (125472682617/250000000000 : ℝ) (250945365229/500000000000 : ℝ) (125472682617/250000000000 : ℝ) (250945365229/500000000000 : ℝ) (125472682617/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33727/262144 : ℝ))) 6 (250945365229/500000000000 : ℝ) (125472682617/250000000000 : ℝ) (250945365229/500000000000 : ℝ) (125472682617/250000000000 : ℝ) (250945365229/500000000000 : ℝ) (125472682617/250000000000 : ℝ) (250945365229/500000000000 : ℝ) (125472682617/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33727/262144 : ℝ))) 7 (250945365229/500000000000 : ℝ) (125472682617/250000000000 : ℝ) (250945365229/500000000000 : ℝ) (125472682617/250000000000 : ℝ) (250945365229/500000000000 : ℝ) (125472682617/250000000000 : ℝ) (250945365229/500000000000 : ℝ) (125472682617/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33727/262144 : ℝ)) hmem 8 (496003567823/500000000000 : ℝ) (992007135649/1000000000000 : ℝ) (496003567823/500000000000 : ℝ) (992007135649/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33727/262144 : ℝ))) hcmem 8 (250945365229/500000000000 : ℝ) (125472682617/250000000000 : ℝ) (250945365229/500000000000 : ℝ) (125472682617/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33727/262144 : ℝ)) (496003567823/500000000000 : ℝ) (992007135649/1000000000000 : ℝ) (250945365229/500000000000 : ℝ) (125472682617/250000000000 : ℝ) (99340025833/125000000000 : ℝ) (794720206683/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1294_exp_lower
  have heNumeric : (513725744621/250000000000 : ℝ)/4 ≤ Real.exp (-21314103254481/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513725744621/250000000000 : ℝ)/4 ≤ Real.exp ((16863/131072 : ℝ)-(794720206683/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16863/131072 : ℝ) (33727/262144 : ℝ) (794720206683/1000000000000 : ℝ) (513725744621/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1295; no trusted numerical premise.
theorem cover8_leaf1295_exp_radius : (249497918482999171/250000000000000000 : ℝ) ≤ Real.exp ((-527/32768 : ℝ)/8) ∧ Real.exp ((-527/32768 : ℝ)/8) ≤ (199598334786399337/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-527/32768 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1295_exp_lower : (230028382740874621/250000000000000000 : ℝ) ≤ Real.exp ((-42628205225681/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628205225681/64000000000000 : ℝ)/8) ≤ (184022706192699697/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628205225681/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1295_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054903019687/1000000000000 : ℝ) ≤ 4*Real.exp (33727/262144 : ℝ)*Real.exp (-mu (radius 8 (527/4096 : ℝ))) ∧ (20549/10000 : ℝ) < (2054903019687/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (527/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1295_exp_radius
  have hrNumeric : (196809174687/200000000000 : ℝ) ≤ Real.exp (-527/32768 : ℝ) ∧ Real.exp (-527/32768 : ℝ) ≤ (246011468359/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196809174687/200000000000 : ℝ) ≤ (radius 8 (527/4096 : ℝ)) ∧ (radius 8 (527/4096 : ℝ)) ≤ (246011468359/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (527/4096 : ℝ)) (196809174687/200000000000 : ℝ) (246011468359/250000000000 : ℝ) (44478730151/250000000000 : ℝ) (17791492061/100000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (527/4096 : ℝ)) (196809174687/200000000000 : ℝ) (246011468359/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (527/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196809174687/200000000000 : ℝ) (246011468359/250000000000 : ℝ) (992022936717/1000000000000 : ℝ) (496011468359/500000000000 : ℝ) (30999714487/31250000000 : ℝ) (198398172717/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (527/4096 : ℝ)) 1 (992022936717/1000000000000 : ℝ) (496011468359/500000000000 : ℝ) (30999714487/31250000000 : ℝ) (198398172717/200000000000 : ℝ) (19840138003/20000000000 : ℝ) (124000862519/125000000000 : ℝ) (49600345001/50000000000 : ℝ) (496003450011/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (527/4096 : ℝ)) 2 (19840138003/20000000000 : ℝ) (124000862519/125000000000 : ℝ) (49600345001/50000000000 : ℝ) (496003450011/500000000000 : ℝ) (198401380017/200000000000 : ℝ) (992006900087/1000000000000 : ℝ) (248001725021/250000000000 : ℝ) (992006900087/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (527/4096 : ℝ)) 3 (198401380017/200000000000 : ℝ) (992006900087/1000000000000 : ℝ) (248001725021/250000000000 : ℝ) (992006900087/1000000000000 : ℝ) (248001725021/250000000000 : ℝ) (992006900087/1000000000000 : ℝ) (248001725021/250000000000 : ℝ) (992006900087/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (527/4096 : ℝ)) 4 (248001725021/250000000000 : ℝ) (992006900087/1000000000000 : ℝ) (248001725021/250000000000 : ℝ) (992006900087/1000000000000 : ℝ) (248001725021/250000000000 : ℝ) (992006900087/1000000000000 : ℝ) (248001725021/250000000000 : ℝ) (992006900087/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (527/4096 : ℝ)) 5 (248001725021/250000000000 : ℝ) (992006900087/1000000000000 : ℝ) (248001725021/250000000000 : ℝ) (992006900087/1000000000000 : ℝ) (248001725021/250000000000 : ℝ) (992006900087/1000000000000 : ℝ) (248001725021/250000000000 : ℝ) (992006900087/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (527/4096 : ℝ)) 6 (248001725021/250000000000 : ℝ) (992006900087/1000000000000 : ℝ) (248001725021/250000000000 : ℝ) (992006900087/1000000000000 : ℝ) (248001725021/250000000000 : ℝ) (992006900087/1000000000000 : ℝ) (248001725021/250000000000 : ℝ) (992006900087/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (527/4096 : ℝ)) 7 (248001725021/250000000000 : ℝ) (992006900087/1000000000000 : ℝ) (248001725021/250000000000 : ℝ) (992006900087/1000000000000 : ℝ) (248001725021/250000000000 : ℝ) (992006900087/1000000000000 : ℝ) (248001725021/250000000000 : ℝ) (992006900087/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (527/4096 : ℝ))) (44478730151/250000000000 : ℝ) (17791492061/100000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (527/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44478730151/250000000000 : ℝ) (17791492061/100000000000 : ℝ) (294478730151/500000000000 : ℝ) (117791492061/200000000000 : ℝ) (421799621389/1000000000000 : ℝ) (421799621397/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (527/4096 : ℝ))) 1 (294478730151/500000000000 : ℝ) (117791492061/200000000000 : ℝ) (421799621389/1000000000000 : ℝ) (421799621397/1000000000000 : ℝ) (101075708169/200000000000 : ℝ) (505378540851/1000000000000 : ℝ) (249209767951/500000000000 : ℝ) (498419535909/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (527/4096 : ℝ))) 2 (101075708169/200000000000 : ℝ) (505378540851/1000000000000 : ℝ) (249209767951/500000000000 : ℝ) (498419535909/1000000000000 : ℝ) (501899038373/1000000000000 : ℝ) (25094951919/50000000000 : ℝ) (5018869771/10000000000 : ℝ) (501886977107/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (527/4096 : ℝ))) 3 (501899038373/1000000000000 : ℝ) (25094951919/50000000000 : ℝ) (5018869771/10000000000 : ℝ) (501886977107/1000000000000 : ℝ) (62736625967/125000000000 : ℝ) (3921039123/7812500000 : ℝ) (5018930077/10000000000 : ℝ) (125473251927/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (527/4096 : ℝ))) 4 (62736625967/125000000000 : ℝ) (3921039123/7812500000 : ℝ) (5018930077/10000000000 : ℝ) (125473251927/250000000000 : ℝ) (250946503859/500000000000 : ℝ) (250946503863/500000000000 : ℝ) (501893007717/1000000000000 : ℝ) (250946503863/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (527/4096 : ℝ))) 5 (250946503859/500000000000 : ℝ) (250946503863/500000000000 : ℝ) (501893007717/1000000000000 : ℝ) (250946503863/500000000000 : ℝ) (501893007717/1000000000000 : ℝ) (250946503863/500000000000 : ℝ) (501893007717/1000000000000 : ℝ) (250946503863/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (527/4096 : ℝ))) 6 (501893007717/1000000000000 : ℝ) (250946503863/500000000000 : ℝ) (501893007717/1000000000000 : ℝ) (250946503863/500000000000 : ℝ) (501893007717/1000000000000 : ℝ) (250946503863/500000000000 : ℝ) (501893007717/1000000000000 : ℝ) (250946503863/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (527/4096 : ℝ))) 7 (501893007717/1000000000000 : ℝ) (250946503863/500000000000 : ℝ) (501893007717/1000000000000 : ℝ) (250946503863/500000000000 : ℝ) (501893007717/1000000000000 : ℝ) (250946503863/500000000000 : ℝ) (501893007717/1000000000000 : ℝ) (250946503863/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (527/4096 : ℝ)) hmem 8 (248001725021/250000000000 : ℝ) (992006900087/1000000000000 : ℝ) (248001725021/250000000000 : ℝ) (992006900087/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (527/4096 : ℝ))) hcmem 8 (501893007717/1000000000000 : ℝ) (250946503863/500000000000 : ℝ) (501893007717/1000000000000 : ℝ) (250946503863/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (527/4096 : ℝ)) (248001725021/250000000000 : ℝ) (992006900087/1000000000000 : ℝ) (501893007717/1000000000000 : ℝ) (250946503863/500000000000 : ℝ) (794724001311/1000000000000 : ℝ) (794724001329/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1295_exp_lower
  have heNumeric : (2054903019687/1000000000000 : ℝ)/4 ≤ Real.exp (-42628205225681/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054903019687/1000000000000 : ℝ)/4 ≤ Real.exp ((33727/262144 : ℝ)-(794724001329/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33727/262144 : ℝ) (527/4096 : ℝ) (794724001329/1000000000000 : ℝ) (2054903019687/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1296; no trusted numerical premise.
theorem cover8_leaf1296_exp_radius : (997991614447059243/1000000000000000000 : ℝ) ≤ Real.exp ((-33729/2097152 : ℝ)/8) ∧ Real.exp ((-33729/2097152 : ℝ)/8) ≤ (249497903611764811/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33729/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1296_exp_lower : (36804541331090781/40000000000000000 : ℝ) ≤ Real.exp ((-333032843267/500000000000 : ℝ)/8) ∧ Real.exp ((-333032843267/500000000000 : ℝ)/8) ≤ (460056766638634763/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-333032843267/500000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1296_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451530513/500000000000 : ℝ) ≤ 4*Real.exp (527/4096 : ℝ)*Real.exp (-mu (radius 8 (33729/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451530513/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33729/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1296_exp_radius
  have hrNumeric : (196809080841/200000000000 : ℝ) ≤ Real.exp (-33729/2097152 : ℝ) ∧ Real.exp (-33729/2097152 : ℝ) ≤ (492022702103/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196809080841/200000000000 : ℝ) ≤ (radius 8 (33729/262144 : ℝ)) ∧ (radius 8 (33729/262144 : ℝ)) ≤ (492022702103/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33729/262144 : ℝ)) (196809080841/200000000000 : ℝ) (492022702103/500000000000 : ℝ) (177917515891/1000000000000 : ℝ) (88958757949/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33729/262144 : ℝ)) (196809080841/200000000000 : ℝ) (492022702103/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33729/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196809080841/200000000000 : ℝ) (492022702103/500000000000 : ℝ) (496011351051/500000000000 : ℝ) (992022702103/1000000000000 : ℝ) (39679625083/40000000000 : ℝ) (247997656769/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33729/262144 : ℝ)) 1 (496011351051/500000000000 : ℝ) (992022702103/1000000000000 : ℝ) (39679625083/40000000000 : ℝ) (247997656769/250000000000 : ℝ) (248001666147/250000000000 : ℝ) (99200666459/100000000000 : ℝ) (496003332229/500000000000 : ℝ) (49600333223/50000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33729/262144 : ℝ)) 2 (248001666147/250000000000 : ℝ) (99200666459/100000000000 : ℝ) (496003332229/500000000000 : ℝ) (49600333223/50000000000 : ℝ) (992006664523/1000000000000 : ℝ) (39680266581/40000000000 : ℝ) (496003332261/500000000000 : ℝ) (39680266581/40000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33729/262144 : ℝ)) 3 (992006664523/1000000000000 : ℝ) (39680266581/40000000000 : ℝ) (496003332261/500000000000 : ℝ) (39680266581/40000000000 : ℝ) (496003332261/500000000000 : ℝ) (39680266581/40000000000 : ℝ) (496003332261/500000000000 : ℝ) (39680266581/40000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33729/262144 : ℝ)) 4 (496003332261/500000000000 : ℝ) (39680266581/40000000000 : ℝ) (496003332261/500000000000 : ℝ) (39680266581/40000000000 : ℝ) (496003332261/500000000000 : ℝ) (39680266581/40000000000 : ℝ) (496003332261/500000000000 : ℝ) (39680266581/40000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33729/262144 : ℝ)) 5 (496003332261/500000000000 : ℝ) (39680266581/40000000000 : ℝ) (496003332261/500000000000 : ℝ) (39680266581/40000000000 : ℝ) (496003332261/500000000000 : ℝ) (39680266581/40000000000 : ℝ) (496003332261/500000000000 : ℝ) (39680266581/40000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33729/262144 : ℝ)) 6 (496003332261/500000000000 : ℝ) (39680266581/40000000000 : ℝ) (496003332261/500000000000 : ℝ) (39680266581/40000000000 : ℝ) (496003332261/500000000000 : ℝ) (39680266581/40000000000 : ℝ) (496003332261/500000000000 : ℝ) (39680266581/40000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33729/262144 : ℝ)) 7 (496003332261/500000000000 : ℝ) (39680266581/40000000000 : ℝ) (496003332261/500000000000 : ℝ) (39680266581/40000000000 : ℝ) (496003332261/500000000000 : ℝ) (39680266581/40000000000 : ℝ) (496003332261/500000000000 : ℝ) (39680266581/40000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33729/262144 : ℝ))) (177917515891/1000000000000 : ℝ) (88958757949/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33729/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177917515891/1000000000000 : ℝ) (88958757949/500000000000 : ℝ) (117791751589/200000000000 : ℝ) (588958757949/1000000000000 : ℝ) (421802697823/1000000000000 : ℝ) (52725337229/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33729/262144 : ℝ))) 1 (117791751589/200000000000 : ℝ) (588958757949/1000000000000 : ℝ) (421802697823/1000000000000 : ℝ) (52725337229/125000000000 : ℝ) (126345181971/250000000000 : ℝ) (505380727891/1000000000000 : ℝ) (62302737827/125000000000 : ℝ) (15575684457/31250000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33729/262144 : ℝ))) 2 (126345181971/250000000000 : ℝ) (505380727891/1000000000000 : ℝ) (62302737827/125000000000 : ℝ) (15575684457/31250000000 : ℝ) (2007605261/4000000000 : ℝ) (250950657629/500000000000 : ℝ) (250944627327/500000000000 : ℝ) (250944627331/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33729/262144 : ℝ))) 3 (2007605261/4000000000 : ℝ) (250950657629/500000000000 : ℝ) (250944627327/500000000000 : ℝ) (250944627331/500000000000 : ℝ) (62736910619/125000000000 : ℝ) (3136845531/6250000000 : ℝ) (100379056983/200000000000 : ℝ) (125473821231/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33729/262144 : ℝ))) 4 (62736910619/125000000000 : ℝ) (3136845531/6250000000 : ℝ) (100379056983/200000000000 : ℝ) (125473821231/250000000000 : ℝ) (501895284933/1000000000000 : ℝ) (250947642471/500000000000 : ℝ) (501895284933/1000000000000 : ℝ) (250947642471/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33729/262144 : ℝ))) 5 (501895284933/1000000000000 : ℝ) (250947642471/500000000000 : ℝ) (501895284933/1000000000000 : ℝ) (250947642471/500000000000 : ℝ) (501895284933/1000000000000 : ℝ) (250947642471/500000000000 : ℝ) (501895284933/1000000000000 : ℝ) (250947642471/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33729/262144 : ℝ))) 6 (501895284933/1000000000000 : ℝ) (250947642471/500000000000 : ℝ) (501895284933/1000000000000 : ℝ) (250947642471/500000000000 : ℝ) (501895284933/1000000000000 : ℝ) (250947642471/500000000000 : ℝ) (501895284933/1000000000000 : ℝ) (250947642471/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33729/262144 : ℝ))) 7 (501895284933/1000000000000 : ℝ) (250947642471/500000000000 : ℝ) (501895284933/1000000000000 : ℝ) (250947642471/500000000000 : ℝ) (501895284933/1000000000000 : ℝ) (250947642471/500000000000 : ℝ) (501895284933/1000000000000 : ℝ) (250947642471/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33729/262144 : ℝ)) hmem 8 (496003332261/500000000000 : ℝ) (39680266581/40000000000 : ℝ) (496003332261/500000000000 : ℝ) (39680266581/40000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33729/262144 : ℝ))) hcmem 8 (501895284933/1000000000000 : ℝ) (250947642471/500000000000 : ℝ) (501895284933/1000000000000 : ℝ) (250947642471/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33729/262144 : ℝ)) (496003332261/500000000000 : ℝ) (39680266581/40000000000 : ℝ) (501895284933/1000000000000 : ℝ) (250947642471/500000000000 : ℝ) (198681948973/250000000000 : ℝ) (794727795909/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1296_exp_lower
  have heNumeric : (1027451530513/500000000000 : ℝ)/4 ≤ Real.exp (-333032843267/500000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451530513/500000000000 : ℝ)/4 ≤ Real.exp ((527/4096 : ℝ)-(794727795909/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (527/4096 : ℝ) (33729/262144 : ℝ) (794727795909/1000000000000 : ℝ) (1027451530513/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1297; no trusted numerical premise.
theorem cover8_leaf1297_exp_radius : (249497888740531337/250000000000000000 : ℝ) ≤ Real.exp ((-16865/1048576 : ℝ)/8) ∧ Real.exp ((-16865/1048576 : ℝ)/8) ≤ (997991554962125349/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16865/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1297_exp_lower : (115014191950058967/125000000000000000 : ℝ) ≤ Real.exp ((-42628202645423/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628202645423/64000000000000 : ℝ)/8) ≤ (920113535600471737/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628202645423/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1297_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451551267/500000000000 : ℝ) ≤ 4*Real.exp (33729/262144 : ℝ)*Real.exp (-mu (radius 8 (16865/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451551267/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16865/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1297_exp_radius
  have hrNumeric : (15375702109/15625000000 : ℝ) ≤ Real.exp (-16865/1048576 : ℝ) ∧ Real.exp (-16865/1048576 : ℝ) ≤ (984044934977/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (15375702109/15625000000 : ℝ) ≤ (radius 8 (16865/131072 : ℝ)) ∧ (radius 8 (16865/131072 : ℝ)) ≤ (984044934977/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16865/131072 : ℝ)) (15375702109/15625000000 : ℝ) (984044934977/1000000000000 : ℝ) (88960055567/500000000000 : ℝ) (177920111141/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16865/131072 : ℝ)) (15375702109/15625000000 : ℝ) (984044934977/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16865/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (15375702109/15625000000 : ℝ) (984044934977/1000000000000 : ℝ) (31000702109/31250000000 : ℝ) (992022467489/1000000000000 : ℝ) (495995195283/500000000000 : ℝ) (991990390567/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16865/131072 : ℝ)) 1 (31000702109/31250000000 : ℝ) (992022467489/1000000000000 : ℝ) (495995195283/500000000000 : ℝ) (991990390567/1000000000000 : ℝ) (992006429027/1000000000000 : ℝ) (248001607257/250000000000 : ℝ) (992006428897/1000000000000 : ℝ) (992006428899/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16865/131072 : ℝ)) 2 (992006429027/1000000000000 : ℝ) (248001607257/250000000000 : ℝ) (992006428897/1000000000000 : ℝ) (992006428899/1000000000000 : ℝ) (496003214481/500000000000 : ℝ) (248001607241/250000000000 : ℝ) (992006428961/1000000000000 : ℝ) (248001607241/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16865/131072 : ℝ)) 3 (496003214481/500000000000 : ℝ) (248001607241/250000000000 : ℝ) (992006428961/1000000000000 : ℝ) (248001607241/250000000000 : ℝ) (992006428961/1000000000000 : ℝ) (248001607241/250000000000 : ℝ) (992006428961/1000000000000 : ℝ) (248001607241/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16865/131072 : ℝ)) 4 (992006428961/1000000000000 : ℝ) (248001607241/250000000000 : ℝ) (992006428961/1000000000000 : ℝ) (248001607241/250000000000 : ℝ) (992006428961/1000000000000 : ℝ) (248001607241/250000000000 : ℝ) (992006428961/1000000000000 : ℝ) (248001607241/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16865/131072 : ℝ)) 5 (992006428961/1000000000000 : ℝ) (248001607241/250000000000 : ℝ) (992006428961/1000000000000 : ℝ) (248001607241/250000000000 : ℝ) (992006428961/1000000000000 : ℝ) (248001607241/250000000000 : ℝ) (992006428961/1000000000000 : ℝ) (248001607241/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16865/131072 : ℝ)) 6 (992006428961/1000000000000 : ℝ) (248001607241/250000000000 : ℝ) (992006428961/1000000000000 : ℝ) (248001607241/250000000000 : ℝ) (992006428961/1000000000000 : ℝ) (248001607241/250000000000 : ℝ) (992006428961/1000000000000 : ℝ) (248001607241/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16865/131072 : ℝ)) 7 (992006428961/1000000000000 : ℝ) (248001607241/250000000000 : ℝ) (992006428961/1000000000000 : ℝ) (248001607241/250000000000 : ℝ) (992006428961/1000000000000 : ℝ) (248001607241/250000000000 : ℝ) (992006428961/1000000000000 : ℝ) (248001607241/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16865/131072 : ℝ))) (88960055567/500000000000 : ℝ) (177920111141/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16865/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88960055567/500000000000 : ℝ) (177920111141/1000000000000 : ℝ) (588960055567/1000000000000 : ℝ) (588960055571/1000000000000 : ℝ) (210902887091/500000000000 : ℝ) (26362860887/62500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16865/131072 : ℝ))) 1 (588960055567/1000000000000 : ℝ) (588960055571/1000000000000 : ℝ) (210902887091/500000000000 : ℝ) (26362860887/62500000000 : ℝ) (252691457437/500000000000 : ℝ) (252691457441/500000000000 : ℝ) (498424269273/1000000000000 : ℝ) (498424269281/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16865/131072 : ℝ))) 2 (252691457437/500000000000 : ℝ) (252691457441/500000000000 : ℝ) (498424269273/1000000000000 : ℝ) (498424269281/1000000000000 : ℝ) (501903592073/1000000000000 : ℝ) (250951796041/500000000000 : ℝ) (100378306431/200000000000 : ℝ) (125472883041/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16865/131072 : ℝ))) 3 (501903592073/1000000000000 : ℝ) (250951796041/500000000000 : ℝ) (100378306431/200000000000 : ℝ) (125472883041/250000000000 : ℝ) (250948781057/500000000000 : ℝ) (501897562123/1000000000000 : ℝ) (501897562077/1000000000000 : ℝ) (501897562087/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16865/131072 : ℝ))) 4 (250948781057/500000000000 : ℝ) (501897562123/1000000000000 : ℝ) (501897562077/1000000000000 : ℝ) (501897562087/1000000000000 : ℝ) (100379512419/200000000000 : ℝ) (100379512421/200000000000 : ℝ) (100379512419/200000000000 : ℝ) (100379512421/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16865/131072 : ℝ))) 5 (100379512419/200000000000 : ℝ) (100379512421/200000000000 : ℝ) (100379512419/200000000000 : ℝ) (100379512421/200000000000 : ℝ) (100379512419/200000000000 : ℝ) (100379512421/200000000000 : ℝ) (100379512419/200000000000 : ℝ) (100379512421/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16865/131072 : ℝ))) 6 (100379512419/200000000000 : ℝ) (100379512421/200000000000 : ℝ) (100379512419/200000000000 : ℝ) (100379512421/200000000000 : ℝ) (100379512419/200000000000 : ℝ) (100379512421/200000000000 : ℝ) (100379512419/200000000000 : ℝ) (100379512421/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16865/131072 : ℝ))) 7 (100379512419/200000000000 : ℝ) (100379512421/200000000000 : ℝ) (100379512419/200000000000 : ℝ) (100379512421/200000000000 : ℝ) (100379512419/200000000000 : ℝ) (100379512421/200000000000 : ℝ) (100379512419/200000000000 : ℝ) (100379512421/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16865/131072 : ℝ)) hmem 8 (992006428961/1000000000000 : ℝ) (248001607241/250000000000 : ℝ) (992006428961/1000000000000 : ℝ) (248001607241/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16865/131072 : ℝ))) hcmem 8 (100379512419/200000000000 : ℝ) (100379512421/200000000000 : ℝ) (100379512419/200000000000 : ℝ) (100379512421/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16865/131072 : ℝ)) (992006428961/1000000000000 : ℝ) (248001607241/250000000000 : ℝ) (100379512419/200000000000 : ℝ) (100379512421/200000000000 : ℝ) (198682897597/250000000000 : ℝ) (794731590407/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1297_exp_lower
  have heNumeric : (1027451551267/500000000000 : ℝ)/4 ≤ Real.exp (-42628202645423/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451551267/500000000000 : ℝ)/4 ≤ Real.exp ((33729/262144 : ℝ)-(794731590407/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33729/262144 : ℝ) (16865/131072 : ℝ) (794731590407/1000000000000 : ℝ) (1027451551267/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1298; no trusted numerical premise.
theorem cover8_leaf1298_exp_radius : (997991495477194999/1000000000000000000 : ℝ) ≤ Real.exp ((-33731/2097152 : ℝ)/8) ∧ Real.exp ((-33731/2097152 : ℝ)/8) ≤ (199598299095439/200000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33731/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1298_exp_lower : (184022707586506009/200000000000000000 : ℝ) ≤ Real.exp ((-21314100673871/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314100673871/32000000000000 : ℝ)/8) ≤ (460056768966265023/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314100673871/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1298_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (10274515721/5000000000 : ℝ) ≤ 4*Real.exp (16865/131072 : ℝ)*Real.exp (-mu (radius 8 (33731/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (10274515721/5000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33731/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1298_exp_radius
  have hrNumeric : (984044465747/1000000000000 : ℝ) ≤ Real.exp (-33731/2097152 : ℝ) ∧ Real.exp (-33731/2097152 : ℝ) ≤ (246011116437/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984044465747/1000000000000 : ℝ) ≤ (radius 8 (33731/262144 : ℝ)) ∧ (radius 8 (33731/262144 : ℝ)) ≤ (246011116437/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33731/262144 : ℝ)) (984044465747/1000000000000 : ℝ) (246011116437/250000000000 : ℝ) (88961353169/500000000000 : ℝ) (22240338293/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33731/262144 : ℝ)) (984044465747/1000000000000 : ℝ) (246011116437/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33731/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984044465747/1000000000000 : ℝ) (246011116437/250000000000 : ℝ) (992022232873/1000000000000 : ℝ) (496011116437/500000000000 : ℝ) (991990154057/1000000000000 : ℝ) (495995077029/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33731/262144 : ℝ)) 1 (992022232873/1000000000000 : ℝ) (496011116437/500000000000 : ℝ) (991990154057/1000000000000 : ℝ) (495995077029/500000000000 : ℝ) (198401238693/200000000000 : ℝ) (496003096733/500000000000 : ℝ) (198401238667/200000000000 : ℝ) (992006193337/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33731/262144 : ℝ)) 2 (198401238693/200000000000 : ℝ) (496003096733/500000000000 : ℝ) (198401238667/200000000000 : ℝ) (992006193337/1000000000000 : ℝ) (4960030967/5000000000 : ℝ) (496003096701/500000000000 : ℝ) (992006193399/1000000000000 : ℝ) (496003096701/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33731/262144 : ℝ)) 3 (4960030967/5000000000 : ℝ) (496003096701/500000000000 : ℝ) (992006193399/1000000000000 : ℝ) (496003096701/500000000000 : ℝ) (992006193399/1000000000000 : ℝ) (496003096701/500000000000 : ℝ) (992006193399/1000000000000 : ℝ) (496003096701/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33731/262144 : ℝ)) 4 (992006193399/1000000000000 : ℝ) (496003096701/500000000000 : ℝ) (992006193399/1000000000000 : ℝ) (496003096701/500000000000 : ℝ) (992006193399/1000000000000 : ℝ) (496003096701/500000000000 : ℝ) (992006193399/1000000000000 : ℝ) (496003096701/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33731/262144 : ℝ)) 5 (992006193399/1000000000000 : ℝ) (496003096701/500000000000 : ℝ) (992006193399/1000000000000 : ℝ) (496003096701/500000000000 : ℝ) (992006193399/1000000000000 : ℝ) (496003096701/500000000000 : ℝ) (992006193399/1000000000000 : ℝ) (496003096701/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33731/262144 : ℝ)) 6 (992006193399/1000000000000 : ℝ) (496003096701/500000000000 : ℝ) (992006193399/1000000000000 : ℝ) (496003096701/500000000000 : ℝ) (992006193399/1000000000000 : ℝ) (496003096701/500000000000 : ℝ) (992006193399/1000000000000 : ℝ) (496003096701/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33731/262144 : ℝ)) 7 (992006193399/1000000000000 : ℝ) (496003096701/500000000000 : ℝ) (992006193399/1000000000000 : ℝ) (496003096701/500000000000 : ℝ) (992006193399/1000000000000 : ℝ) (496003096701/500000000000 : ℝ) (992006193399/1000000000000 : ℝ) (496003096701/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33731/262144 : ℝ))) (88961353169/500000000000 : ℝ) (22240338293/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33731/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88961353169/500000000000 : ℝ) (22240338293/125000000000 : ℝ) (588961353169/1000000000000 : ℝ) (147240338293/250000000000 : ℝ) (421808850473/1000000000000 : ℝ) (421808850481/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33731/262144 : ℝ))) 1 (588961353169/1000000000000 : ℝ) (147240338293/250000000000 : ℝ) (421808850473/1000000000000 : ℝ) (421808850481/1000000000000 : ℝ) (505385101821/1000000000000 : ℝ) (505385101827/1000000000000 : ℝ) (249213317939/500000000000 : ℝ) (99685327177/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33731/262144 : ℝ))) 2 (505385101821/1000000000000 : ℝ) (505385101827/1000000000000 : ℝ) (249213317939/500000000000 : ℝ) (99685327177/200000000000 : ℝ) (501905868849/1000000000000 : ℝ) (62738233607/125000000000 : ℝ) (62736726201/125000000000 : ℝ) (31368363101/62500000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33731/262144 : ℝ))) 3 (501905868849/1000000000000 : ℝ) (62738233607/125000000000 : ℝ) (62736726201/125000000000 : ℝ) (31368363101/62500000000 : ℝ) (125474959807/250000000000 : ℝ) (125474959809/250000000000 : ℝ) (62737479899/125000000000 : ℝ) (627374799/1250000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33731/262144 : ℝ))) 4 (125474959807/250000000000 : ℝ) (125474959809/250000000000 : ℝ) (62737479899/125000000000 : ℝ) (627374799/1250000000 : ℝ) (50189983921/100000000000 : ℝ) (250949919609/500000000000 : ℝ) (501899839209/1000000000000 : ℝ) (250949919609/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33731/262144 : ℝ))) 5 (50189983921/100000000000 : ℝ) (250949919609/500000000000 : ℝ) (501899839209/1000000000000 : ℝ) (250949919609/500000000000 : ℝ) (501899839209/1000000000000 : ℝ) (250949919609/500000000000 : ℝ) (501899839209/1000000000000 : ℝ) (250949919609/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33731/262144 : ℝ))) 6 (501899839209/1000000000000 : ℝ) (250949919609/500000000000 : ℝ) (501899839209/1000000000000 : ℝ) (250949919609/500000000000 : ℝ) (501899839209/1000000000000 : ℝ) (250949919609/500000000000 : ℝ) (501899839209/1000000000000 : ℝ) (250949919609/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33731/262144 : ℝ))) 7 (501899839209/1000000000000 : ℝ) (250949919609/500000000000 : ℝ) (501899839209/1000000000000 : ℝ) (250949919609/500000000000 : ℝ) (501899839209/1000000000000 : ℝ) (250949919609/500000000000 : ℝ) (501899839209/1000000000000 : ℝ) (250949919609/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33731/262144 : ℝ)) hmem 8 (992006193399/1000000000000 : ℝ) (496003096701/500000000000 : ℝ) (992006193399/1000000000000 : ℝ) (496003096701/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33731/262144 : ℝ))) hcmem 8 (501899839209/1000000000000 : ℝ) (250949919609/500000000000 : ℝ) (501899839209/1000000000000 : ℝ) (250949919609/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33731/262144 : ℝ)) (992006193399/1000000000000 : ℝ) (496003096701/500000000000 : ℝ) (501899839209/1000000000000 : ℝ) (250949919609/500000000000 : ℝ) (794735384811/1000000000000 : ℝ) (198683846207/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1298_exp_lower
  have heNumeric : (10274515721/5000000000 : ℝ)/4 ≤ Real.exp (-21314100673871/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (10274515721/5000000000 : ℝ)/4 ≤ Real.exp ((16865/131072 : ℝ)-(198683846207/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16865/131072 : ℝ) (33731/262144 : ℝ) (198683846207/250000000000 : ℝ) (10274515721/5000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1299; no trusted numerical premise.
theorem cover8_leaf1299_exp_radius : (199598287198453639/200000000000000000 : ℝ) ≤ Real.exp ((-8433/524288 : ℝ)/8) ∧ Real.exp ((-8433/524288 : ℝ)/8) ≤ (249497858998067049/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8433/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1299_exp_lower : (46005677013626217/50000000000000000 : ℝ) ≤ Real.exp ((-8525640009129/12800000000000 : ℝ)/8) ∧ Real.exp ((-8525640009129/12800000000000 : ℝ)/8) ≤ (920113540272524341/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8525640009129/12800000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1299_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054903186007/1000000000000 : ℝ) ≤ 4*Real.exp (33731/262144 : ℝ)*Real.exp (-mu (radius 8 (8433/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (2054903186007/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8433/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1299_exp_radius
  have hrNumeric : (492021998259/500000000000 : ℝ) ≤ Real.exp (-8433/524288 : ℝ) ∧ Real.exp (-8433/524288 : ℝ) ≤ (984043996519/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492021998259/500000000000 : ℝ) ≤ (radius 8 (8433/65536 : ℝ)) ∧ (radius 8 (8433/65536 : ℝ)) ≤ (984043996519/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8433/65536 : ℝ)) (492021998259/500000000000 : ℝ) (984043996519/1000000000000 : ℝ) (88962650751/500000000000 : ℝ) (177925301509/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8433/65536 : ℝ)) (492021998259/500000000000 : ℝ) (984043996519/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8433/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492021998259/500000000000 : ℝ) (984043996519/1000000000000 : ℝ) (992021998259/1000000000000 : ℝ) (49601099913/50000000000 : ℝ) (247997479387/250000000000 : ℝ) (19839798351/20000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8433/65536 : ℝ)) 1 (992021998259/1000000000000 : ℝ) (49601099913/50000000000 : ℝ) (247997479387/250000000000 : ℝ) (19839798351/20000000000 : ℝ) (992005957903/1000000000000 : ℝ) (198401191581/200000000000 : ℝ) (992005957773/1000000000000 : ℝ) (62000372361/62500000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8433/65536 : ℝ)) 2 (992005957903/1000000000000 : ℝ) (198401191581/200000000000 : ℝ) (992005957773/1000000000000 : ℝ) (62000372361/62500000000 : ℝ) (496002978919/500000000000 : ℝ) (992005957841/1000000000000 : ℝ) (992005957837/1000000000000 : ℝ) (992005957841/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8433/65536 : ℝ)) 3 (496002978919/500000000000 : ℝ) (992005957841/1000000000000 : ℝ) (992005957837/1000000000000 : ℝ) (992005957841/1000000000000 : ℝ) (992005957837/1000000000000 : ℝ) (992005957841/1000000000000 : ℝ) (992005957837/1000000000000 : ℝ) (992005957841/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8433/65536 : ℝ)) 4 (992005957837/1000000000000 : ℝ) (992005957841/1000000000000 : ℝ) (992005957837/1000000000000 : ℝ) (992005957841/1000000000000 : ℝ) (992005957837/1000000000000 : ℝ) (992005957841/1000000000000 : ℝ) (992005957837/1000000000000 : ℝ) (992005957841/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8433/65536 : ℝ)) 5 (992005957837/1000000000000 : ℝ) (992005957841/1000000000000 : ℝ) (992005957837/1000000000000 : ℝ) (992005957841/1000000000000 : ℝ) (992005957837/1000000000000 : ℝ) (992005957841/1000000000000 : ℝ) (992005957837/1000000000000 : ℝ) (992005957841/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8433/65536 : ℝ)) 6 (992005957837/1000000000000 : ℝ) (992005957841/1000000000000 : ℝ) (992005957837/1000000000000 : ℝ) (992005957841/1000000000000 : ℝ) (992005957837/1000000000000 : ℝ) (992005957841/1000000000000 : ℝ) (992005957837/1000000000000 : ℝ) (992005957841/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8433/65536 : ℝ)) 7 (992005957837/1000000000000 : ℝ) (992005957841/1000000000000 : ℝ) (992005957837/1000000000000 : ℝ) (992005957841/1000000000000 : ℝ) (992005957837/1000000000000 : ℝ) (992005957841/1000000000000 : ℝ) (992005957837/1000000000000 : ℝ) (992005957841/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8433/65536 : ℝ))) (88962650751/500000000000 : ℝ) (177925301509/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8433/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88962650751/500000000000 : ℝ) (177925301509/1000000000000 : ℝ) (588962650751/1000000000000 : ℝ) (117792530151/200000000000 : ℝ) (210905963347/500000000000 : ℝ) (26363245419/62500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8433/65536 : ℝ))) 1 (588962650751/1000000000000 : ℝ) (117792530151/200000000000 : ℝ) (210905963347/500000000000 : ℝ) (26363245419/62500000000 : ℝ) (252693644361/500000000000 : ℝ) (50538728873/100000000000 : ℝ) (49842900243/100000000000 : ℝ) (498429002439/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8433/65536 : ℝ))) 2 (252693644361/500000000000 : ℝ) (50538728873/100000000000 : ℝ) (49842900243/100000000000 : ℝ) (498429002439/1000000000000 : ℝ) (62738518197/125000000000 : ℝ) (100381629117/200000000000 : ℝ) (125474021753/250000000000 : ℝ) (250948043511/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8433/65536 : ℝ))) 3 (62738518197/125000000000 : ℝ) (100381629117/200000000000 : ℝ) (125474021753/250000000000 : ℝ) (250948043511/500000000000 : ℝ) (250951058147/500000000000 : ℝ) (31368882269/62500000000 : ℝ) (501902116257/1000000000000 : ℝ) (125475529067/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8433/65536 : ℝ))) 4 (250951058147/500000000000 : ℝ) (31368882269/62500000000 : ℝ) (501902116257/1000000000000 : ℝ) (125475529067/250000000000 : ℝ) (20076084651/40000000000 : ℝ) (250951058143/500000000000 : ℝ) (20076084651/40000000000 : ℝ) (250951058143/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8433/65536 : ℝ))) 5 (20076084651/40000000000 : ℝ) (250951058143/500000000000 : ℝ) (20076084651/40000000000 : ℝ) (250951058143/500000000000 : ℝ) (20076084651/40000000000 : ℝ) (250951058143/500000000000 : ℝ) (20076084651/40000000000 : ℝ) (250951058143/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8433/65536 : ℝ))) 6 (20076084651/40000000000 : ℝ) (250951058143/500000000000 : ℝ) (20076084651/40000000000 : ℝ) (250951058143/500000000000 : ℝ) (20076084651/40000000000 : ℝ) (250951058143/500000000000 : ℝ) (20076084651/40000000000 : ℝ) (250951058143/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8433/65536 : ℝ))) 7 (20076084651/40000000000 : ℝ) (250951058143/500000000000 : ℝ) (20076084651/40000000000 : ℝ) (250951058143/500000000000 : ℝ) (20076084651/40000000000 : ℝ) (250951058143/500000000000 : ℝ) (20076084651/40000000000 : ℝ) (250951058143/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8433/65536 : ℝ)) hmem 8 (992005957837/1000000000000 : ℝ) (992005957841/1000000000000 : ℝ) (992005957837/1000000000000 : ℝ) (992005957841/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8433/65536 : ℝ))) hcmem 8 (20076084651/40000000000 : ℝ) (250951058143/500000000000 : ℝ) (20076084651/40000000000 : ℝ) (250951058143/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8433/65536 : ℝ)) (992005957837/1000000000000 : ℝ) (992005957841/1000000000000 : ℝ) (20076084651/40000000000 : ℝ) (250951058143/500000000000 : ℝ) (397369589579/500000000000 : ℝ) (39736958959/50000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1299_exp_lower
  have heNumeric : (2054903186007/1000000000000 : ℝ)/4 ≤ Real.exp (-8525640009129/12800000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054903186007/1000000000000 : ℝ)/4 ≤ Real.exp ((33731/262144 : ℝ)-(39736958959/50000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33731/262144 : ℝ) (8433/65536 : ℝ) (39736958959/50000000000 : ℝ) (2054903186007/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_leaf1275_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1275_certificate
#check SmaleRate.Proofs.cover8_leaf1276_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1276_certificate
#check SmaleRate.Proofs.cover8_leaf1277_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1277_certificate
#check SmaleRate.Proofs.cover8_leaf1278_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1278_certificate
#check SmaleRate.Proofs.cover8_leaf1279_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1279_certificate
#check SmaleRate.Proofs.cover8_leaf1280_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1280_certificate
#check SmaleRate.Proofs.cover8_leaf1281_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1281_certificate
#check SmaleRate.Proofs.cover8_leaf1282_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1282_certificate
#check SmaleRate.Proofs.cover8_leaf1283_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1283_certificate
#check SmaleRate.Proofs.cover8_leaf1284_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1284_certificate
#check SmaleRate.Proofs.cover8_leaf1285_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1285_certificate
#check SmaleRate.Proofs.cover8_leaf1286_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1286_certificate
#check SmaleRate.Proofs.cover8_leaf1287_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1287_certificate
#check SmaleRate.Proofs.cover8_leaf1288_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1288_certificate
#check SmaleRate.Proofs.cover8_leaf1289_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1289_certificate
#check SmaleRate.Proofs.cover8_leaf1290_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1290_certificate
#check SmaleRate.Proofs.cover8_leaf1291_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1291_certificate
#check SmaleRate.Proofs.cover8_leaf1292_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1292_certificate
#check SmaleRate.Proofs.cover8_leaf1293_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1293_certificate
#check SmaleRate.Proofs.cover8_leaf1294_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1294_certificate
#check SmaleRate.Proofs.cover8_leaf1295_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1295_certificate
#check SmaleRate.Proofs.cover8_leaf1296_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1296_certificate
#check SmaleRate.Proofs.cover8_leaf1297_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1297_certificate
#check SmaleRate.Proofs.cover8_leaf1298_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1298_certificate
#check SmaleRate.Proofs.cover8_leaf1299_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1299_certificate
