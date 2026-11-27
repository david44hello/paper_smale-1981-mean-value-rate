/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.AGMCertificates

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

-- Proposed record cover7_leaf0175; no trusted numerical premise.
theorem cover7_leaf0175_exp_radius : (498804977808046817/500000000000000000 : ℝ) ≤ Real.exp ((-4391/229376 : ℝ)/8) ∧ Real.exp ((-4391/229376 : ℝ)/8) ≤ (199521991123218727/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4391/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0175_exp_lower : (229522166708372457/250000000000000000 : ℝ) ≤ Real.exp ((-2734761793961/4000000000000 : ℝ)/8) ∧ Real.exp ((-2734761793961/4000000000000 : ℝ)/8) ≤ (918088666833489829/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2734761793961/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0175_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019003176493/1000000000000 : ℝ) ≤ 4*Real.exp (2195/16384 : ℝ)*Real.exp (-mu (radius 7 (4391/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (2019003176493/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4391/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0175_exp_radius
  have hrNumeric : (490519413699/500000000000 : ℝ) ≤ Real.exp (-4391/229376 : ℝ) ∧ Real.exp (-4391/229376 : ℝ) ≤ (981038827399/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490519413699/500000000000 : ℝ) ≤ (radius 7 (4391/32768 : ℝ)) ∧ (radius 7 (4391/32768 : ℝ)) ≤ (981038827399/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4391/32768 : ℝ)) (490519413699/500000000000 : ℝ) (981038827399/1000000000000 : ℝ) (775245191/4000000000 : ℝ) (48452824439/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4391/32768 : ℝ)) (490519413699/500000000000 : ℝ) (981038827399/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4391/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490519413699/500000000000 : ℝ) (981038827399/1000000000000 : ℝ) (990519413699/1000000000000 : ℝ) (9905194137/10000000000 : ℝ) (495237020879/500000000000 : ℝ) (6190462761/6250000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4391/32768 : ℝ)) 1 (990519413699/1000000000000 : ℝ) (9905194137/10000000000 : ℝ) (495237020879/500000000000 : ℝ) (6190462761/6250000000 : ℝ) (61906045483/62500000000 : ℝ) (99049672773/100000000000 : ℝ) (247624181867/250000000000 : ℝ) (990496727471/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4391/32768 : ℝ)) 2 (61906045483/62500000000 : ℝ) (99049672773/100000000000 : ℝ) (247624181867/250000000000 : ℝ) (990496727471/1000000000000 : ℝ) (495248363799/500000000000 : ℝ) (990496727601/1000000000000 : ℝ) (990496727597/1000000000000 : ℝ) (990496727601/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4391/32768 : ℝ)) 3 (495248363799/500000000000 : ℝ) (990496727601/1000000000000 : ℝ) (990496727597/1000000000000 : ℝ) (990496727601/1000000000000 : ℝ) (990496727597/1000000000000 : ℝ) (990496727601/1000000000000 : ℝ) (990496727597/1000000000000 : ℝ) (990496727601/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4391/32768 : ℝ)) 4 (990496727597/1000000000000 : ℝ) (990496727601/1000000000000 : ℝ) (990496727597/1000000000000 : ℝ) (990496727601/1000000000000 : ℝ) (990496727597/1000000000000 : ℝ) (990496727601/1000000000000 : ℝ) (990496727597/1000000000000 : ℝ) (990496727601/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4391/32768 : ℝ)) 5 (990496727597/1000000000000 : ℝ) (990496727601/1000000000000 : ℝ) (990496727597/1000000000000 : ℝ) (990496727601/1000000000000 : ℝ) (990496727597/1000000000000 : ℝ) (990496727601/1000000000000 : ℝ) (990496727597/1000000000000 : ℝ) (990496727601/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4391/32768 : ℝ)) 6 (990496727597/1000000000000 : ℝ) (990496727601/1000000000000 : ℝ) (990496727597/1000000000000 : ℝ) (990496727601/1000000000000 : ℝ) (990496727597/1000000000000 : ℝ) (990496727601/1000000000000 : ℝ) (990496727597/1000000000000 : ℝ) (990496727601/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4391/32768 : ℝ)) 7 (990496727597/1000000000000 : ℝ) (990496727601/1000000000000 : ℝ) (990496727597/1000000000000 : ℝ) (990496727601/1000000000000 : ℝ) (990496727597/1000000000000 : ℝ) (990496727601/1000000000000 : ℝ) (990496727597/1000000000000 : ℝ) (990496727601/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4391/32768 : ℝ))) (775245191/4000000000 : ℝ) (48452824439/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4391/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (775245191/4000000000 : ℝ) (48452824439/250000000000 : ℝ) (4775245191/8000000000 : ℝ) (298452824439/500000000000 : ℝ) (550300057/1250000000 : ℝ) (440240045607/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4391/32768 : ℝ))) 1 (4775245191/8000000000 : ℝ) (298452824439/500000000000 : ℝ) (550300057/1250000000 : ℝ) (440240045607/1000000000000 : ℝ) (518572847237/1000000000000 : ℝ) (518572847243/1000000000000 : ℝ) (512622443987/1000000000000 : ℝ) (512622443993/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4391/32768 : ℝ))) 2 (518572847237/1000000000000 : ℝ) (518572847243/1000000000000 : ℝ) (512622443987/1000000000000 : ℝ) (512622443993/1000000000000 : ℝ) (128899411403/250000000000 : ℝ) (257798822809/500000000000 : ℝ) (515589061497/1000000000000 : ℝ) (4028039543/7812500000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4391/32768 : ℝ))) 3 (128899411403/250000000000 : ℝ) (257798822809/500000000000 : ℝ) (515589061497/1000000000000 : ℝ) (4028039543/7812500000 : ℝ) (257796676777/500000000000 : ℝ) (515593353561/1000000000000 : ℝ) (8056146149/15625000000 : ℝ) (64449169193/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4391/32768 : ℝ))) 4 (257796676777/500000000000 : ℝ) (515593353561/1000000000000 : ℝ) (8056146149/15625000000 : ℝ) (64449169193/125000000000 : ℝ) (103118670709/200000000000 : ℝ) (515593353553/1000000000000 : ℝ) (64449169193/125000000000 : ℝ) (515593353553/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4391/32768 : ℝ))) 5 (103118670709/200000000000 : ℝ) (515593353553/1000000000000 : ℝ) (64449169193/125000000000 : ℝ) (515593353553/1000000000000 : ℝ) (64449169193/125000000000 : ℝ) (515593353553/1000000000000 : ℝ) (64449169193/125000000000 : ℝ) (515593353553/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4391/32768 : ℝ))) 6 (64449169193/125000000000 : ℝ) (515593353553/1000000000000 : ℝ) (64449169193/125000000000 : ℝ) (515593353553/1000000000000 : ℝ) (64449169193/125000000000 : ℝ) (515593353553/1000000000000 : ℝ) (64449169193/125000000000 : ℝ) (515593353553/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4391/32768 : ℝ))) 7 (64449169193/125000000000 : ℝ) (515593353553/1000000000000 : ℝ) (64449169193/125000000000 : ℝ) (515593353553/1000000000000 : ℝ) (64449169193/125000000000 : ℝ) (515593353553/1000000000000 : ℝ) (64449169193/125000000000 : ℝ) (515593353553/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4391/32768 : ℝ)) hmem 8 (990496727597/1000000000000 : ℝ) (990496727601/1000000000000 : ℝ) (990496727597/1000000000000 : ℝ) (990496727601/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4391/32768 : ℝ))) hcmem 8 (64449169193/125000000000 : ℝ) (515593353553/1000000000000 : ℝ) (64449169193/125000000000 : ℝ) (515593353553/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4391/32768 : ℝ)) (990496727597/1000000000000 : ℝ) (990496727601/1000000000000 : ℝ) (64449169193/125000000000 : ℝ) (515593353553/1000000000000 : ℝ) (817662616441/1000000000000 : ℝ) (817662616459/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0175_exp_lower
  have heNumeric : (2019003176493/1000000000000 : ℝ)/4 ≤ Real.exp (-2734761793961/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019003176493/1000000000000 : ℝ)/4 ≤ Real.exp ((2195/16384 : ℝ)-(817662616459/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2195/16384 : ℝ) (4391/32768 : ℝ) (817662616459/1000000000000 : ℝ) (2019003176493/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0176; no trusted numerical premise.
theorem cover7_leaf0176_exp_radius : (997609411961960361/1000000000000000000 : ℝ) ≤ Real.exp ((-549/28672 : ℝ)/8) ∧ Real.exp ((-549/28672 : ℝ)/8) ≤ (498804705980980181/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-549/28672 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0176_exp_lower : (114761078564978591/125000000000000000 : ℝ) ≤ Real.exp ((-5469526258769/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469526258769/8000000000000 : ℝ)/8) ≤ (918088628519828729/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469526258769/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0176_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019002502437/1000000000000 : ℝ) ≤ 4*Real.exp (4391/32768 : ℝ)*Real.exp (-mu (radius 7 (549/4096 : ℝ))) ∧ (2019/1000 : ℝ) < (2019002502437/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (549/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0176_exp_radius
  have hrNumeric : (490517275209/500000000000 : ℝ) ≤ Real.exp (-549/28672 : ℝ) ∧ Real.exp (-549/28672 : ℝ) ≤ (981034550419/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490517275209/500000000000 : ℝ) ≤ (radius 7 (549/4096 : ℝ)) ∧ (radius 7 (549/4096 : ℝ)) ≤ (981034550419/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (549/4096 : ℝ)) (490517275209/500000000000 : ℝ) (981034550419/1000000000000 : ℝ) (193832945817/1000000000000 : ℝ) (193832945823/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (549/4096 : ℝ)) (490517275209/500000000000 : ℝ) (981034550419/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (549/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490517275209/500000000000 : ℝ) (981034550419/1000000000000 : ℝ) (990517275209/1000000000000 : ℝ) (99051727521/100000000000 : ℝ) (990471882699/1000000000000 : ℝ) (9904718827/10000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (549/4096 : ℝ)) 1 (990517275209/1000000000000 : ℝ) (99051727521/100000000000 : ℝ) (990471882699/1000000000000 : ℝ) (9904718827/10000000000 : ℝ) (495247289477/500000000000 : ℝ) (198098915791/200000000000 : ℝ) (990494578693/1000000000000 : ℝ) (198098915739/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (549/4096 : ℝ)) 2 (495247289477/500000000000 : ℝ) (198098915791/200000000000 : ℝ) (990494578693/1000000000000 : ℝ) (198098915739/200000000000 : ℝ) (990494578823/1000000000000 : ℝ) (39619783153/40000000000 : ℝ) (990494578823/1000000000000 : ℝ) (39619783153/40000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (549/4096 : ℝ)) 3 (990494578823/1000000000000 : ℝ) (39619783153/40000000000 : ℝ) (990494578823/1000000000000 : ℝ) (39619783153/40000000000 : ℝ) (990494578823/1000000000000 : ℝ) (39619783153/40000000000 : ℝ) (990494578823/1000000000000 : ℝ) (39619783153/40000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (549/4096 : ℝ)) 4 (990494578823/1000000000000 : ℝ) (39619783153/40000000000 : ℝ) (990494578823/1000000000000 : ℝ) (39619783153/40000000000 : ℝ) (990494578823/1000000000000 : ℝ) (39619783153/40000000000 : ℝ) (990494578823/1000000000000 : ℝ) (39619783153/40000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (549/4096 : ℝ)) 5 (990494578823/1000000000000 : ℝ) (39619783153/40000000000 : ℝ) (990494578823/1000000000000 : ℝ) (39619783153/40000000000 : ℝ) (990494578823/1000000000000 : ℝ) (39619783153/40000000000 : ℝ) (990494578823/1000000000000 : ℝ) (39619783153/40000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (549/4096 : ℝ)) 6 (990494578823/1000000000000 : ℝ) (39619783153/40000000000 : ℝ) (990494578823/1000000000000 : ℝ) (39619783153/40000000000 : ℝ) (990494578823/1000000000000 : ℝ) (39619783153/40000000000 : ℝ) (990494578823/1000000000000 : ℝ) (39619783153/40000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (549/4096 : ℝ)) 7 (990494578823/1000000000000 : ℝ) (39619783153/40000000000 : ℝ) (990494578823/1000000000000 : ℝ) (39619783153/40000000000 : ℝ) (990494578823/1000000000000 : ℝ) (39619783153/40000000000 : ℝ) (990494578823/1000000000000 : ℝ) (39619783153/40000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (549/4096 : ℝ))) (193832945817/1000000000000 : ℝ) (193832945823/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (549/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (193832945817/1000000000000 : ℝ) (193832945823/1000000000000 : ℝ) (149229118227/250000000000 : ℝ) (37307279557/62500000000 : ℝ) (55033078947/125000000000 : ℝ) (13758269737/31250000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (549/4096 : ℝ))) 1 (149229118227/250000000000 : ℝ) (37307279557/62500000000 : ℝ) (55033078947/125000000000 : ℝ) (13758269737/31250000000 : ℝ) (259295276121/500000000000 : ℝ) (64823819031/125000000000 : ℝ) (512641405883/1000000000000 : ℝ) (512641405891/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (549/4096 : ℝ))) 2 (259295276121/500000000000 : ℝ) (64823819031/125000000000 : ℝ) (512641405883/1000000000000 : ℝ) (512641405891/1000000000000 : ℝ) (257807989531/500000000000 : ℝ) (51561597907/100000000000 : ℝ) (515607398879/1000000000000 : ℝ) (515607398887/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (549/4096 : ℝ))) 3 (257807989531/500000000000 : ℝ) (51561597907/100000000000 : ℝ) (515607398879/1000000000000 : ℝ) (515607398887/1000000000000 : ℝ) (51561168897/100000000000 : ℝ) (515611688979/1000000000000 : ℝ) (64451461119/125000000000 : ℝ) (515611688961/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (549/4096 : ℝ))) 4 (51561168897/100000000000 : ℝ) (515611688979/1000000000000 : ℝ) (64451461119/125000000000 : ℝ) (515611688961/1000000000000 : ℝ) (515611688961/1000000000000 : ℝ) (51561168897/100000000000 : ℝ) (25176352/48828125 : ℝ) (51561168897/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (549/4096 : ℝ))) 5 (515611688961/1000000000000 : ℝ) (51561168897/100000000000 : ℝ) (25176352/48828125 : ℝ) (51561168897/100000000000 : ℝ) (25176352/48828125 : ℝ) (51561168897/100000000000 : ℝ) (25176352/48828125 : ℝ) (51561168897/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (549/4096 : ℝ))) 6 (25176352/48828125 : ℝ) (51561168897/100000000000 : ℝ) (25176352/48828125 : ℝ) (51561168897/100000000000 : ℝ) (25176352/48828125 : ℝ) (51561168897/100000000000 : ℝ) (25176352/48828125 : ℝ) (51561168897/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (549/4096 : ℝ))) 7 (25176352/48828125 : ℝ) (51561168897/100000000000 : ℝ) (25176352/48828125 : ℝ) (51561168897/100000000000 : ℝ) (25176352/48828125 : ℝ) (51561168897/100000000000 : ℝ) (25176352/48828125 : ℝ) (51561168897/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (549/4096 : ℝ)) hmem 8 (990494578823/1000000000000 : ℝ) (39619783153/40000000000 : ℝ) (990494578823/1000000000000 : ℝ) (39619783153/40000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (549/4096 : ℝ))) hcmem 8 (25176352/48828125 : ℝ) (51561168897/100000000000 : ℝ) (25176352/48828125 : ℝ) (51561168897/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (549/4096 : ℝ)) (990494578823/1000000000000 : ℝ) (39619783153/40000000000 : ℝ) (25176352/48828125 : ℝ) (51561168897/100000000000 : ℝ) (6541547743/8000000000 : ℝ) (817693467893/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0176_exp_lower
  have heNumeric : (2019002502437/1000000000000 : ℝ)/4 ≤ Real.exp (-5469526258769/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019002502437/1000000000000 : ℝ)/4 ≤ Real.exp ((4391/32768 : ℝ)-(817693467893/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4391/32768 : ℝ) (549/4096 : ℝ) (817693467893/1000000000000 : ℝ) (2019002502437/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0177; no trusted numerical premise.
theorem cover7_leaf0177_exp_radius : (249402217077030839/250000000000000000 : ℝ) ≤ Real.exp ((-4393/229376 : ℝ)/8) ∧ Real.exp ((-4393/229376 : ℝ)/8) ≤ (997608868308123357/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4393/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0177_exp_lower : (183617718148925637/200000000000000000 : ℝ) ≤ Real.exp ((-68369111151/100000000000 : ℝ)/8) ∧ Real.exp ((-68369111151/100000000000 : ℝ)/8) ≤ (459044295372314093/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-68369111151/100000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0177_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009500918927/500000000000 : ℝ) ≤ 4*Real.exp (549/4096 : ℝ)*Real.exp (-mu (radius 7 (4393/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (1009500918927/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4393/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0177_exp_radius
  have hrNumeric : (61314392091/62500000000 : ℝ) ≤ Real.exp (-4393/229376 : ℝ) ∧ Real.exp (-4393/229376 : ℝ) ≤ (981030273457/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (61314392091/62500000000 : ℝ) ≤ (radius 7 (4393/32768 : ℝ)) ∧ (radius 7 (4393/32768 : ℝ)) ≤ (981030273457/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4393/32768 : ℝ)) (61314392091/62500000000 : ℝ) (981030273457/1000000000000 : ℝ) (193854591281/1000000000000 : ℝ) (193854591287/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4393/32768 : ℝ)) (61314392091/62500000000 : ℝ) (981030273457/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4393/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (61314392091/62500000000 : ℝ) (981030273457/1000000000000 : ℝ) (123814392091/125000000000 : ℝ) (990515136729/1000000000000 : ℝ) (247617430911/250000000000 : ℝ) (198093944729/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4393/32768 : ℝ)) 1 (123814392091/125000000000 : ℝ) (990515136729/1000000000000 : ℝ) (247617430911/250000000000 : ℝ) (198093944729/200000000000 : ℝ) (495246215093/500000000000 : ℝ) (990492430187/1000000000000 : ℝ) (39619697197/40000000000 : ℝ) (990492429927/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4393/32768 : ℝ)) 2 (495246215093/500000000000 : ℝ) (990492430187/1000000000000 : ℝ) (39619697197/40000000000 : ℝ) (990492429927/1000000000000 : ℝ) (198098486011/200000000000 : ℝ) (990492430057/1000000000000 : ℝ) (198098486011/200000000000 : ℝ) (990492430057/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4393/32768 : ℝ)) 3 (198098486011/200000000000 : ℝ) (990492430057/1000000000000 : ℝ) (198098486011/200000000000 : ℝ) (990492430057/1000000000000 : ℝ) (198098486011/200000000000 : ℝ) (990492430057/1000000000000 : ℝ) (198098486011/200000000000 : ℝ) (990492430057/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4393/32768 : ℝ)) 4 (198098486011/200000000000 : ℝ) (990492430057/1000000000000 : ℝ) (198098486011/200000000000 : ℝ) (990492430057/1000000000000 : ℝ) (198098486011/200000000000 : ℝ) (990492430057/1000000000000 : ℝ) (198098486011/200000000000 : ℝ) (990492430057/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4393/32768 : ℝ)) 5 (198098486011/200000000000 : ℝ) (990492430057/1000000000000 : ℝ) (198098486011/200000000000 : ℝ) (990492430057/1000000000000 : ℝ) (198098486011/200000000000 : ℝ) (990492430057/1000000000000 : ℝ) (198098486011/200000000000 : ℝ) (990492430057/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4393/32768 : ℝ)) 6 (198098486011/200000000000 : ℝ) (990492430057/1000000000000 : ℝ) (198098486011/200000000000 : ℝ) (990492430057/1000000000000 : ℝ) (198098486011/200000000000 : ℝ) (990492430057/1000000000000 : ℝ) (198098486011/200000000000 : ℝ) (990492430057/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4393/32768 : ℝ)) 7 (198098486011/200000000000 : ℝ) (990492430057/1000000000000 : ℝ) (198098486011/200000000000 : ℝ) (990492430057/1000000000000 : ℝ) (198098486011/200000000000 : ℝ) (990492430057/1000000000000 : ℝ) (198098486011/200000000000 : ℝ) (990492430057/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4393/32768 : ℝ))) (193854591281/1000000000000 : ℝ) (193854591287/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4393/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (193854591281/1000000000000 : ℝ) (193854591287/1000000000000 : ℝ) (14923182391/25000000000 : ℝ) (149231823911/250000000000 : ℝ) (440289213223/1000000000000 : ℝ) (440289213231/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4393/32768 : ℝ))) 1 (14923182391/25000000000 : ℝ) (149231823911/250000000000 : ℝ) (440289213223/1000000000000 : ℝ) (440289213231/1000000000000 : ℝ) (518608254431/1000000000000 : ℝ) (259304127219/500000000000 : ℝ) (256330182259/500000000000 : ℝ) (256330182263/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4393/32768 : ℝ))) 2 (518608254431/1000000000000 : ℝ) (259304127219/500000000000 : ℝ) (256330182259/500000000000 : ℝ) (256330182263/500000000000 : ℝ) (257817154737/500000000000 : ℝ) (257817154741/500000000000 : ℝ) (515625733219/1000000000000 : ℝ) (128906433307/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4393/32768 : ℝ))) 3 (257817154737/500000000000 : ℝ) (257817154741/500000000000 : ℝ) (515625733219/1000000000000 : ℝ) (128906433307/250000000000 : ℝ) (257815010673/500000000000 : ℝ) (103126004271/200000000000 : ℝ) (32226876333/62500000000 : ℝ) (257815010669/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4393/32768 : ℝ))) 4 (257815010673/500000000000 : ℝ) (103126004271/200000000000 : ℝ) (32226876333/62500000000 : ℝ) (257815010669/500000000000 : ℝ) (515630021337/1000000000000 : ℝ) (515630021347/1000000000000 : ℝ) (64453752667/125000000000 : ℝ) (515630021347/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4393/32768 : ℝ))) 5 (515630021337/1000000000000 : ℝ) (515630021347/1000000000000 : ℝ) (64453752667/125000000000 : ℝ) (515630021347/1000000000000 : ℝ) (64453752667/125000000000 : ℝ) (515630021347/1000000000000 : ℝ) (64453752667/125000000000 : ℝ) (515630021347/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4393/32768 : ℝ))) 6 (64453752667/125000000000 : ℝ) (515630021347/1000000000000 : ℝ) (64453752667/125000000000 : ℝ) (515630021347/1000000000000 : ℝ) (64453752667/125000000000 : ℝ) (515630021347/1000000000000 : ℝ) (64453752667/125000000000 : ℝ) (515630021347/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4393/32768 : ℝ))) 7 (64453752667/125000000000 : ℝ) (515630021347/1000000000000 : ℝ) (64453752667/125000000000 : ℝ) (515630021347/1000000000000 : ℝ) (64453752667/125000000000 : ℝ) (515630021347/1000000000000 : ℝ) (64453752667/125000000000 : ℝ) (515630021347/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4393/32768 : ℝ)) hmem 8 (198098486011/200000000000 : ℝ) (990492430057/1000000000000 : ℝ) (198098486011/200000000000 : ℝ) (990492430057/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4393/32768 : ℝ))) hcmem 8 (64453752667/125000000000 : ℝ) (515630021347/1000000000000 : ℝ) (64453752667/125000000000 : ℝ) (515630021347/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4393/32768 : ℝ)) (198098486011/200000000000 : ℝ) (990492430057/1000000000000 : ℝ) (64453752667/125000000000 : ℝ) (515630021347/1000000000000 : ℝ) (163544862923/200000000000 : ℝ) (163544862927/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0177_exp_lower
  have heNumeric : (1009500918927/500000000000 : ℝ)/4 ≤ Real.exp (-68369111151/100000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009500918927/500000000000 : ℝ)/4 ≤ Real.exp ((549/4096 : ℝ)-(163544862927/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (549/4096 : ℝ) (4393/32768 : ℝ) (163544862927/200000000000 : ℝ) (1009500918927/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0178; no trusted numerical premise.
theorem cover7_leaf0178_exp_radius : (997608324654582619/1000000000000000000 : ℝ) ≤ Real.exp ((-2197/114688 : ℝ)/8) ∧ Real.exp ((-2197/114688 : ℝ)/8) ≤ (49880416232729131/50000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2197/114688 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0178_exp_lower : (918088553508691461/1000000000000000000 : ℝ) ≤ Real.exp ((-5469531487799/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469531487799/8000000000000 : ℝ)/8) ≤ (459044276754345731/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469531487799/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0178_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019001182759/1000000000000 : ℝ) ≤ 4*Real.exp (4393/32768 : ℝ)*Real.exp (-mu (radius 7 (2197/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (2019001182759/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2197/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0178_exp_radius
  have hrNumeric : (981025996513/1000000000000 : ℝ) ≤ Real.exp (-2197/114688 : ℝ) ∧ Real.exp (-2197/114688 : ℝ) ≤ (490512998257/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (981025996513/1000000000000 : ℝ) ≤ (radius 7 (2197/16384 : ℝ)) ∧ (radius 7 (2197/16384 : ℝ)) ≤ (490512998257/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2197/16384 : ℝ)) (981025996513/1000000000000 : ℝ) (490512998257/500000000000 : ℝ) (96938117069/500000000000 : ℝ) (6058632317/31250000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2197/16384 : ℝ)) (981025996513/1000000000000 : ℝ) (490512998257/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2197/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (981025996513/1000000000000 : ℝ) (490512998257/500000000000 : ℝ) (61907062391/62500000000 : ℝ) (990512998257/1000000000000 : ℝ) (495233782297/500000000000 : ℝ) (198093512919/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2197/16384 : ℝ)) 1 (61907062391/62500000000 : ℝ) (990512998257/1000000000000 : ℝ) (495233782297/500000000000 : ℝ) (198093512919/200000000000 : ℝ) (39619611257/40000000000 : ℝ) (495245140713/500000000000 : ℝ) (247622570291/250000000000 : ℝ) (495245140583/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2197/16384 : ℝ)) 2 (39619611257/40000000000 : ℝ) (495245140713/500000000000 : ℝ) (247622570291/250000000000 : ℝ) (495245140583/500000000000 : ℝ) (495245140647/500000000000 : ℝ) (61905642581/62500000000 : ℝ) (495245140647/500000000000 : ℝ) (61905642581/62500000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2197/16384 : ℝ)) 3 (495245140647/500000000000 : ℝ) (61905642581/62500000000 : ℝ) (495245140647/500000000000 : ℝ) (61905642581/62500000000 : ℝ) (495245140647/500000000000 : ℝ) (61905642581/62500000000 : ℝ) (495245140647/500000000000 : ℝ) (61905642581/62500000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2197/16384 : ℝ)) 4 (495245140647/500000000000 : ℝ) (61905642581/62500000000 : ℝ) (495245140647/500000000000 : ℝ) (61905642581/62500000000 : ℝ) (495245140647/500000000000 : ℝ) (61905642581/62500000000 : ℝ) (495245140647/500000000000 : ℝ) (61905642581/62500000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2197/16384 : ℝ)) 5 (495245140647/500000000000 : ℝ) (61905642581/62500000000 : ℝ) (495245140647/500000000000 : ℝ) (61905642581/62500000000 : ℝ) (495245140647/500000000000 : ℝ) (61905642581/62500000000 : ℝ) (495245140647/500000000000 : ℝ) (61905642581/62500000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2197/16384 : ℝ)) 6 (495245140647/500000000000 : ℝ) (61905642581/62500000000 : ℝ) (495245140647/500000000000 : ℝ) (61905642581/62500000000 : ℝ) (495245140647/500000000000 : ℝ) (61905642581/62500000000 : ℝ) (495245140647/500000000000 : ℝ) (61905642581/62500000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2197/16384 : ℝ)) 7 (495245140647/500000000000 : ℝ) (61905642581/62500000000 : ℝ) (495245140647/500000000000 : ℝ) (61905642581/62500000000 : ℝ) (495245140647/500000000000 : ℝ) (61905642581/62500000000 : ℝ) (495245140647/500000000000 : ℝ) (61905642581/62500000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2197/16384 : ℝ))) (96938117069/500000000000 : ℝ) (6058632317/31250000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2197/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (96938117069/500000000000 : ℝ) (6058632317/31250000000 : ℝ) (596938117069/1000000000000 : ℝ) (37308632317/62500000000 : ℝ) (220156895269/500000000000 : ℝ) (88062758109/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2197/16384 : ℝ))) 1 (596938117069/1000000000000 : ℝ) (37308632317/62500000000 : ℝ) (220156895269/500000000000 : ℝ) (88062758109/200000000000 : ℝ) (518625953803/1000000000000 : ℝ) (518625953809/1000000000000 : ℝ) (51267931989/100000000000 : ℝ) (64084914987/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2197/16384 : ℝ))) 2 (518625953803/1000000000000 : ℝ) (518625953809/1000000000000 : ℝ) (51267931989/100000000000 : ℝ) (64084914987/125000000000 : ℝ) (257826318423/500000000000 : ℝ) (515652636853/1000000000000 : ℝ) (257822032259/500000000000 : ℝ) (20625762581/40000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2197/16384 : ℝ))) 3 (257826318423/500000000000 : ℝ) (515652636853/1000000000000 : ℝ) (257822032259/500000000000 : ℝ) (20625762581/40000000000 : ℝ) (257824175341/500000000000 : ℝ) (515648350689/1000000000000 : ℝ) (64456043833/125000000000 : ℝ) (32228021917/62500000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2197/16384 : ℝ))) 4 (257824175341/500000000000 : ℝ) (515648350689/1000000000000 : ℝ) (64456043833/125000000000 : ℝ) (32228021917/62500000000 : ℝ) (515648350673/1000000000000 : ℝ) (515648350681/1000000000000 : ℝ) (32228021917/62500000000 : ℝ) (515648350681/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2197/16384 : ℝ))) 5 (515648350673/1000000000000 : ℝ) (515648350681/1000000000000 : ℝ) (32228021917/62500000000 : ℝ) (515648350681/1000000000000 : ℝ) (32228021917/62500000000 : ℝ) (515648350681/1000000000000 : ℝ) (32228021917/62500000000 : ℝ) (515648350681/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2197/16384 : ℝ))) 6 (32228021917/62500000000 : ℝ) (515648350681/1000000000000 : ℝ) (32228021917/62500000000 : ℝ) (515648350681/1000000000000 : ℝ) (32228021917/62500000000 : ℝ) (515648350681/1000000000000 : ℝ) (32228021917/62500000000 : ℝ) (515648350681/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2197/16384 : ℝ))) 7 (32228021917/62500000000 : ℝ) (515648350681/1000000000000 : ℝ) (32228021917/62500000000 : ℝ) (515648350681/1000000000000 : ℝ) (32228021917/62500000000 : ℝ) (515648350681/1000000000000 : ℝ) (32228021917/62500000000 : ℝ) (515648350681/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2197/16384 : ℝ)) hmem 8 (495245140647/500000000000 : ℝ) (61905642581/62500000000 : ℝ) (495245140647/500000000000 : ℝ) (61905642581/62500000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2197/16384 : ℝ))) hcmem 8 (32228021917/62500000000 : ℝ) (515648350681/1000000000000 : ℝ) (32228021917/62500000000 : ℝ) (515648350681/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2197/16384 : ℝ)) (495245140647/500000000000 : ℝ) (61905642581/62500000000 : ℝ) (32228021917/62500000000 : ℝ) (515648350681/1000000000000 : ℝ) (408877578331/500000000000 : ℝ) (408877578339/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0178_exp_lower
  have heNumeric : (2019001182759/1000000000000 : ℝ)/4 ≤ Real.exp (-5469531487799/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019001182759/1000000000000 : ℝ)/4 ≤ Real.exp ((4393/32768 : ℝ)-(408877578339/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4393/32768 : ℝ) (2197/16384 : ℝ) (408877578339/500000000000 : ℝ) (2019001182759/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0179; no trusted numerical premise.
theorem cover7_leaf0179_exp_radius : (997607781001338149/1000000000000000000 : ℝ) ≤ Real.exp ((-4395/229376 : ℝ)/8) ∧ Real.exp ((-4395/229376 : ℝ)/8) ≤ (19952155620026763/20000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4395/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0179_exp_lower : (183617703362082367/200000000000000000 : ℝ) ≤ Real.exp ((-2734767023019/4000000000000 : ℝ)/8) ∧ Real.exp ((-2734767023019/4000000000000 : ℝ)/8) ≤ (229522129202602959/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2734767023019/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0179_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019000537123/1000000000000 : ℝ) ≤ 4*Real.exp (2197/16384 : ℝ)*Real.exp (-mu (radius 7 (4395/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (2019000537123/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4395/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0179_exp_radius
  have hrNumeric : (245255429897/250000000000 : ℝ) ≤ Real.exp (-4395/229376 : ℝ) ∧ Real.exp (-4395/229376 : ℝ) ≤ (981021719589/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (245255429897/250000000000 : ℝ) ≤ (radius 7 (4395/32768 : ℝ)) ∧ (radius 7 (4395/32768 : ℝ)) ≤ (981021719589/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4395/32768 : ℝ)) (245255429897/250000000000 : ℝ) (981021719589/1000000000000 : ℝ) (96948937197/500000000000 : ℝ) (242372343/1250000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4395/32768 : ℝ)) (245255429897/250000000000 : ℝ) (981021719589/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4395/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (245255429897/250000000000 : ℝ) (981021719589/1000000000000 : ℝ) (495255429897/500000000000 : ℝ) (198102171959/200000000000 : ℝ) (247616351387/250000000000 : ℝ) (990465405549/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4395/32768 : ℝ)) 1 (495255429897/500000000000 : ℝ) (198102171959/200000000000 : ℝ) (247616351387/250000000000 : ℝ) (990465405549/1000000000000 : ℝ) (990488132671/1000000000000 : ℝ) (15476377073/15625000000 : ℝ) (99048813241/100000000000 : ℝ) (247622033103/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4395/32768 : ℝ)) 2 (990488132671/1000000000000 : ℝ) (15476377073/15625000000 : ℝ) (99048813241/100000000000 : ℝ) (247622033103/250000000000 : ℝ) (49524406627/50000000000 : ℝ) (495244066271/500000000000 : ℝ) (49524406627/50000000000 : ℝ) (495244066271/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4395/32768 : ℝ)) 3 (49524406627/50000000000 : ℝ) (495244066271/500000000000 : ℝ) (49524406627/50000000000 : ℝ) (495244066271/500000000000 : ℝ) (49524406627/50000000000 : ℝ) (495244066271/500000000000 : ℝ) (49524406627/50000000000 : ℝ) (495244066271/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4395/32768 : ℝ)) 4 (49524406627/50000000000 : ℝ) (495244066271/500000000000 : ℝ) (49524406627/50000000000 : ℝ) (495244066271/500000000000 : ℝ) (49524406627/50000000000 : ℝ) (495244066271/500000000000 : ℝ) (49524406627/50000000000 : ℝ) (495244066271/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4395/32768 : ℝ)) 5 (49524406627/50000000000 : ℝ) (495244066271/500000000000 : ℝ) (49524406627/50000000000 : ℝ) (495244066271/500000000000 : ℝ) (49524406627/50000000000 : ℝ) (495244066271/500000000000 : ℝ) (49524406627/50000000000 : ℝ) (495244066271/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4395/32768 : ℝ)) 6 (49524406627/50000000000 : ℝ) (495244066271/500000000000 : ℝ) (49524406627/50000000000 : ℝ) (495244066271/500000000000 : ℝ) (49524406627/50000000000 : ℝ) (495244066271/500000000000 : ℝ) (49524406627/50000000000 : ℝ) (495244066271/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4395/32768 : ℝ)) 7 (49524406627/50000000000 : ℝ) (495244066271/500000000000 : ℝ) (49524406627/50000000000 : ℝ) (495244066271/500000000000 : ℝ) (49524406627/50000000000 : ℝ) (495244066271/500000000000 : ℝ) (49524406627/50000000000 : ℝ) (495244066271/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4395/32768 : ℝ))) (96948937197/500000000000 : ℝ) (242372343/1250000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4395/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (96948937197/500000000000 : ℝ) (242372343/1250000000 : ℝ) (596948937197/1000000000000 : ℝ) (1492372343/2500000000 : ℝ) (440338363527/1000000000000 : ℝ) (88067672707/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4395/32768 : ℝ))) 1 (596948937197/1000000000000 : ℝ) (1492372343/2500000000 : ℝ) (440338363527/1000000000000 : ℝ) (88067672707/200000000000 : ℝ) (259321825181/500000000000 : ℝ) (8103807037/15625000000 : ℝ) (256349136001/500000000000 : ℝ) (512698272009/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4395/32768 : ℝ))) 2 (259321825181/500000000000 : ℝ) (8103807037/15625000000 : ℝ) (256349136001/500000000000 : ℝ) (512698272009/1000000000000 : ℝ) (257835480591/500000000000 : ℝ) (515670961189/1000000000000 : ℝ) (515662392777/1000000000000 : ℝ) (103132478557/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4395/32768 : ℝ))) 3 (257835480591/500000000000 : ℝ) (515670961189/1000000000000 : ℝ) (515662392777/1000000000000 : ℝ) (103132478557/200000000000 : ℝ) (515666676979/1000000000000 : ℝ) (515666676987/1000000000000 : ℝ) (515666676961/1000000000000 : ℝ) (51566667697/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4395/32768 : ℝ))) 4 (515666676979/1000000000000 : ℝ) (515666676987/1000000000000 : ℝ) (515666676961/1000000000000 : ℝ) (51566667697/100000000000 : ℝ) (51566667697/100000000000 : ℝ) (515666676979/1000000000000 : ℝ) (515666676969/1000000000000 : ℝ) (515666676979/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4395/32768 : ℝ))) 5 (51566667697/100000000000 : ℝ) (515666676979/1000000000000 : ℝ) (515666676969/1000000000000 : ℝ) (515666676979/1000000000000 : ℝ) (515666676969/1000000000000 : ℝ) (515666676979/1000000000000 : ℝ) (515666676969/1000000000000 : ℝ) (515666676979/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4395/32768 : ℝ))) 6 (515666676969/1000000000000 : ℝ) (515666676979/1000000000000 : ℝ) (515666676969/1000000000000 : ℝ) (515666676979/1000000000000 : ℝ) (515666676969/1000000000000 : ℝ) (515666676979/1000000000000 : ℝ) (515666676969/1000000000000 : ℝ) (515666676979/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4395/32768 : ℝ))) 7 (515666676969/1000000000000 : ℝ) (515666676979/1000000000000 : ℝ) (515666676969/1000000000000 : ℝ) (515666676979/1000000000000 : ℝ) (515666676969/1000000000000 : ℝ) (515666676979/1000000000000 : ℝ) (515666676969/1000000000000 : ℝ) (515666676979/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4395/32768 : ℝ)) hmem 8 (49524406627/50000000000 : ℝ) (495244066271/500000000000 : ℝ) (49524406627/50000000000 : ℝ) (495244066271/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4395/32768 : ℝ))) hcmem 8 (515666676969/1000000000000 : ℝ) (515666676979/1000000000000 : ℝ) (515666676969/1000000000000 : ℝ) (515666676979/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4395/32768 : ℝ)) (49524406627/50000000000 : ℝ) (495244066271/500000000000 : ℝ) (515666676969/1000000000000 : ℝ) (515666676979/1000000000000 : ℝ) (817785994017/1000000000000 : ℝ) (204446498509/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0179_exp_lower
  have heNumeric : (2019000537123/1000000000000 : ℝ)/4 ≤ Real.exp (-2734767023019/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019000537123/1000000000000 : ℝ)/4 ≤ Real.exp ((2197/16384 : ℝ)-(204446498509/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2197/16384 : ℝ) (4395/32768 : ℝ) (204446498509/250000000000 : ℝ) (2019000537123/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0180; no trusted numerical premise.
theorem cover7_leaf0180_exp_radius : (199521501834965403/200000000000000000 : ℝ) ≤ Real.exp ((-8791/458752 : ℝ)/8) ∧ Real.exp ((-8791/458752 : ℝ)/8) ≤ (124700938646853377/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8791/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0180_exp_lower : (183618049956021809/200000000000000000 : ℝ) ≤ Real.exp ((-5469413240741/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469413240741/8000000000000 : ℝ)/8) ≤ (459045124890054523/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469413240741/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0180_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009515512799/500000000000 : ℝ) ≤ 4*Real.exp (4395/32768 : ℝ)*Real.exp (-mu (radius 7 (8791/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (1009515512799/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8791/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0180_exp_radius
  have hrNumeric : (981019581133/1000000000000 : ℝ) ≤ Real.exp (-8791/458752 : ℝ) ∧ Real.exp (-8791/458752 : ℝ) ≤ (490509790567/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (981019581133/1000000000000 : ℝ) ≤ (radius 7 (8791/65536 : ℝ)) ∧ (radius 7 (8791/65536 : ℝ)) ≤ (490509790567/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8791/65536 : ℝ)) (981019581133/1000000000000 : ℝ) (490509790567/500000000000 : ℝ) (193908693543/1000000000000 : ℝ) (193908693549/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8791/65536 : ℝ)) (981019581133/1000000000000 : ℝ) (490509790567/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8791/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (981019581133/1000000000000 : ℝ) (490509790567/500000000000 : ℝ) (495254895283/500000000000 : ℝ) (990509790567/1000000000000 : ℝ) (990464326027/1000000000000 : ℝ) (247616081507/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8791/65536 : ℝ)) 1 (495254895283/500000000000 : ℝ) (990509790567/1000000000000 : ℝ) (990464326027/1000000000000 : ℝ) (247616081507/250000000000 : ℝ) (123810882287/125000000000 : ℝ) (495243529149/500000000000 : ℝ) (198097411607/200000000000 : ℝ) (990487058037/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8791/65536 : ℝ)) 2 (123810882287/125000000000 : ℝ) (495243529149/500000000000 : ℝ) (198097411607/200000000000 : ℝ) (990487058037/1000000000000 : ℝ) (198097411633/200000000000 : ℝ) (123810882271/125000000000 : ℝ) (198097411633/200000000000 : ℝ) (123810882271/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8791/65536 : ℝ)) 3 (198097411633/200000000000 : ℝ) (123810882271/125000000000 : ℝ) (198097411633/200000000000 : ℝ) (123810882271/125000000000 : ℝ) (198097411633/200000000000 : ℝ) (123810882271/125000000000 : ℝ) (198097411633/200000000000 : ℝ) (123810882271/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8791/65536 : ℝ)) 4 (198097411633/200000000000 : ℝ) (123810882271/125000000000 : ℝ) (198097411633/200000000000 : ℝ) (123810882271/125000000000 : ℝ) (198097411633/200000000000 : ℝ) (123810882271/125000000000 : ℝ) (198097411633/200000000000 : ℝ) (123810882271/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8791/65536 : ℝ)) 5 (198097411633/200000000000 : ℝ) (123810882271/125000000000 : ℝ) (198097411633/200000000000 : ℝ) (123810882271/125000000000 : ℝ) (198097411633/200000000000 : ℝ) (123810882271/125000000000 : ℝ) (198097411633/200000000000 : ℝ) (123810882271/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8791/65536 : ℝ)) 6 (198097411633/200000000000 : ℝ) (123810882271/125000000000 : ℝ) (198097411633/200000000000 : ℝ) (123810882271/125000000000 : ℝ) (198097411633/200000000000 : ℝ) (123810882271/125000000000 : ℝ) (198097411633/200000000000 : ℝ) (123810882271/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8791/65536 : ℝ)) 7 (198097411633/200000000000 : ℝ) (123810882271/125000000000 : ℝ) (198097411633/200000000000 : ℝ) (123810882271/125000000000 : ℝ) (198097411633/200000000000 : ℝ) (123810882271/125000000000 : ℝ) (198097411633/200000000000 : ℝ) (123810882271/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8791/65536 : ℝ))) (193908693543/1000000000000 : ℝ) (193908693549/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8791/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (193908693543/1000000000000 : ℝ) (193908693549/1000000000000 : ℝ) (596954346771/1000000000000 : ℝ) (23878173871/40000000000 : ℝ) (110087662099/250000000000 : ℝ) (110087662101/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8791/65536 : ℝ))) 1 (596954346771/1000000000000 : ℝ) (23878173871/40000000000 : ℝ) (110087662099/250000000000 : ℝ) (110087662101/250000000000 : ℝ) (518652497583/1000000000000 : ℝ) (51865249759/100000000000 : ℝ) (512707746833/1000000000000 : ℝ) (512707746841/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8791/65536 : ℝ))) 2 (518652497583/1000000000000 : ℝ) (51865249759/100000000000 : ℝ) (512707746833/1000000000000 : ℝ) (512707746841/1000000000000 : ℝ) (16115003819/31250000000 : ℝ) (64460015277/125000000000 : ℝ) (128917888941/250000000000 : ℝ) (515671555773/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8791/65536 : ℝ))) 3 (16115003819/31250000000 : ℝ) (64460015277/125000000000 : ℝ) (128917888941/250000000000 : ℝ) (515671555773/1000000000000 : ℝ) (257837919493/500000000000 : ℝ) (103135167799/200000000000 : ℝ) (64459479871/125000000000 : ℝ) (515675838977/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8791/65536 : ℝ))) 4 (257837919493/500000000000 : ℝ) (103135167799/200000000000 : ℝ) (64459479871/125000000000 : ℝ) (515675838977/1000000000000 : ℝ) (515675838977/1000000000000 : ℝ) (257837919493/500000000000 : ℝ) (1007179373/1953125000 : ℝ) (257837919493/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8791/65536 : ℝ))) 5 (515675838977/1000000000000 : ℝ) (257837919493/500000000000 : ℝ) (1007179373/1953125000 : ℝ) (257837919493/500000000000 : ℝ) (1007179373/1953125000 : ℝ) (257837919493/500000000000 : ℝ) (1007179373/1953125000 : ℝ) (257837919493/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8791/65536 : ℝ))) 6 (1007179373/1953125000 : ℝ) (257837919493/500000000000 : ℝ) (1007179373/1953125000 : ℝ) (257837919493/500000000000 : ℝ) (1007179373/1953125000 : ℝ) (257837919493/500000000000 : ℝ) (1007179373/1953125000 : ℝ) (257837919493/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8791/65536 : ℝ))) 7 (1007179373/1953125000 : ℝ) (257837919493/500000000000 : ℝ) (1007179373/1953125000 : ℝ) (257837919493/500000000000 : ℝ) (1007179373/1953125000 : ℝ) (257837919493/500000000000 : ℝ) (1007179373/1953125000 : ℝ) (257837919493/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8791/65536 : ℝ)) hmem 8 (198097411633/200000000000 : ℝ) (123810882271/125000000000 : ℝ) (198097411633/200000000000 : ℝ) (123810882271/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8791/65536 : ℝ))) hcmem 8 (1007179373/1953125000 : ℝ) (257837919493/500000000000 : ℝ) (1007179373/1953125000 : ℝ) (257837919493/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8791/65536 : ℝ)) (198097411633/200000000000 : ℝ) (123810882271/125000000000 : ℝ) (1007179373/1953125000 : ℝ) (257837919493/500000000000 : ℝ) (204450352733/250000000000 : ℝ) (102225176369/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0180_exp_lower
  have heNumeric : (1009515512799/500000000000 : ℝ)/4 ≤ Real.exp (-5469413240741/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009515512799/500000000000 : ℝ)/4 ≤ Real.exp ((4395/32768 : ℝ)-(102225176369/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4395/32768 : ℝ) (8791/65536 : ℝ) (102225176369/125000000000 : ℝ) (1009515512799/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0181; no trusted numerical premise.
theorem cover7_leaf0181_exp_radius : (997607237348389947/1000000000000000000 : ℝ) ≤ Real.exp ((-157/8192 : ℝ)/8) ∧ Real.exp ((-157/8192 : ℝ)/8) ≤ (249401809337097487/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-157/8192 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0181_exp_lower : (459045115883764989/500000000000000000 : ℝ) ≤ Real.exp ((-10938828992793/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938828992793/16000000000000 : ℝ)/8) ≤ (918090231767529979/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938828992793/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0181_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019030708697/1000000000000 : ℝ) ≤ 4*Real.exp (8791/65536 : ℝ)*Real.exp (-mu (radius 7 (1099/8192 : ℝ))) ∧ (2019/1000 : ℝ) < (2019030708697/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (1099/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0181_exp_radius
  have hrNumeric : (490508721341/500000000000 : ℝ) ≤ Real.exp (-157/8192 : ℝ) ∧ Real.exp (-157/8192 : ℝ) ≤ (981017442683/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490508721341/500000000000 : ℝ) ≤ (radius 7 (1099/8192 : ℝ)) ∧ (radius 7 (1099/8192 : ℝ)) ≤ (981017442683/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (1099/8192 : ℝ)) (490508721341/500000000000 : ℝ) (981017442683/1000000000000 : ℝ) (48479878011/250000000000 : ℝ) (3878390241/20000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (1099/8192 : ℝ)) (490508721341/500000000000 : ℝ) (981017442683/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (1099/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490508721341/500000000000 : ℝ) (981017442683/1000000000000 : ℝ) (990508721341/1000000000000 : ℝ) (495254360671/500000000000 : ℝ) (990463246507/1000000000000 : ℝ) (247615811627/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (1099/8192 : ℝ)) 1 (990508721341/1000000000000 : ℝ) (495254360671/500000000000 : ℝ) (990463246507/1000000000000 : ℝ) (247615811627/250000000000 : ℝ) (247621495981/250000000000 : ℝ) (39619439357/40000000000 : ℝ) (990485983663/1000000000000 : ℝ) (198097196733/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (1099/8192 : ℝ)) 2 (247621495981/250000000000 : ℝ) (39619439357/40000000000 : ℝ) (990485983663/1000000000000 : ℝ) (198097196733/200000000000 : ℝ) (990485983793/1000000000000 : ℝ) (198097196759/200000000000 : ℝ) (990485983793/1000000000000 : ℝ) (198097196759/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (1099/8192 : ℝ)) 3 (990485983793/1000000000000 : ℝ) (198097196759/200000000000 : ℝ) (990485983793/1000000000000 : ℝ) (198097196759/200000000000 : ℝ) (990485983793/1000000000000 : ℝ) (198097196759/200000000000 : ℝ) (990485983793/1000000000000 : ℝ) (198097196759/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (1099/8192 : ℝ)) 4 (990485983793/1000000000000 : ℝ) (198097196759/200000000000 : ℝ) (990485983793/1000000000000 : ℝ) (198097196759/200000000000 : ℝ) (990485983793/1000000000000 : ℝ) (198097196759/200000000000 : ℝ) (990485983793/1000000000000 : ℝ) (198097196759/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (1099/8192 : ℝ)) 5 (990485983793/1000000000000 : ℝ) (198097196759/200000000000 : ℝ) (990485983793/1000000000000 : ℝ) (198097196759/200000000000 : ℝ) (990485983793/1000000000000 : ℝ) (198097196759/200000000000 : ℝ) (990485983793/1000000000000 : ℝ) (198097196759/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (1099/8192 : ℝ)) 6 (990485983793/1000000000000 : ℝ) (198097196759/200000000000 : ℝ) (990485983793/1000000000000 : ℝ) (198097196759/200000000000 : ℝ) (990485983793/1000000000000 : ℝ) (198097196759/200000000000 : ℝ) (990485983793/1000000000000 : ℝ) (198097196759/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (1099/8192 : ℝ)) 7 (990485983793/1000000000000 : ℝ) (198097196759/200000000000 : ℝ) (990485983793/1000000000000 : ℝ) (198097196759/200000000000 : ℝ) (990485983793/1000000000000 : ℝ) (198097196759/200000000000 : ℝ) (990485983793/1000000000000 : ℝ) (198097196759/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (1099/8192 : ℝ))) (48479878011/250000000000 : ℝ) (3878390241/20000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (1099/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (48479878011/250000000000 : ℝ) (3878390241/20000000000 : ℝ) (298479878011/500000000000 : ℝ) (23878390241/40000000000 : ℝ) (220181466093/500000000000 : ℝ) (220181466097/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (1099/8192 : ℝ))) 1 (298479878011/500000000000 : ℝ) (23878390241/40000000000 : ℝ) (220181466093/500000000000 : ℝ) (220181466097/500000000000 : ℝ) (64832668013/125000000000 : ℝ) (51866134411/100000000000 : ℝ) (128179305213/250000000000 : ℝ) (512717220859/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (1099/8192 : ℝ))) 2 (64832668013/125000000000 : ℝ) (51866134411/100000000000 : ℝ) (128179305213/250000000000 : ℝ) (512717220859/1000000000000 : ℝ) (257844641239/500000000000 : ℝ) (103137856497/200000000000 : ℝ) (103136143599/200000000000 : ℝ) (515680718003/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (1099/8192 : ℝ))) 3 (257844641239/500000000000 : ℝ) (103137856497/200000000000 : ℝ) (103136143599/200000000000 : ℝ) (515680718003/1000000000000 : ℝ) (128921250059/250000000000 : ℝ) (128921250061/250000000000 : ℝ) (257842500109/500000000000 : ℝ) (515685000227/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (1099/8192 : ℝ))) 4 (128921250059/250000000000 : ℝ) (128921250061/250000000000 : ℝ) (257842500109/500000000000 : ℝ) (515685000227/1000000000000 : ℝ) (515685000227/1000000000000 : ℝ) (128921250059/250000000000 : ℝ) (257842500113/500000000000 : ℝ) (128921250059/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (1099/8192 : ℝ))) 5 (515685000227/1000000000000 : ℝ) (128921250059/250000000000 : ℝ) (257842500113/500000000000 : ℝ) (128921250059/250000000000 : ℝ) (257842500113/500000000000 : ℝ) (128921250059/250000000000 : ℝ) (257842500113/500000000000 : ℝ) (128921250059/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (1099/8192 : ℝ))) 6 (257842500113/500000000000 : ℝ) (128921250059/250000000000 : ℝ) (257842500113/500000000000 : ℝ) (128921250059/250000000000 : ℝ) (257842500113/500000000000 : ℝ) (128921250059/250000000000 : ℝ) (257842500113/500000000000 : ℝ) (128921250059/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (1099/8192 : ℝ))) 7 (257842500113/500000000000 : ℝ) (128921250059/250000000000 : ℝ) (257842500113/500000000000 : ℝ) (128921250059/250000000000 : ℝ) (257842500113/500000000000 : ℝ) (128921250059/250000000000 : ℝ) (257842500113/500000000000 : ℝ) (128921250059/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (1099/8192 : ℝ)) hmem 8 (990485983793/1000000000000 : ℝ) (198097196759/200000000000 : ℝ) (990485983793/1000000000000 : ℝ) (198097196759/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (1099/8192 : ℝ))) hcmem 8 (257842500113/500000000000 : ℝ) (128921250059/250000000000 : ℝ) (257842500113/500000000000 : ℝ) (128921250059/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (1099/8192 : ℝ)) (990485983793/1000000000000 : ℝ) (198097196759/200000000000 : ℝ) (257842500113/500000000000 : ℝ) (128921250059/250000000000 : ℝ) (817816826679/1000000000000 : ℝ) (408908413349/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0181_exp_lower
  have heNumeric : (2019030708697/1000000000000 : ℝ)/4 ≤ Real.exp (-10938828992793/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019030708697/1000000000000 : ℝ)/4 ≤ Real.exp ((8791/65536 : ℝ)-(408908413349/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8791/65536 : ℝ) (1099/8192 : ℝ) (408908413349/500000000000 : ℝ) (2019030708697/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0182; no trusted numerical premise.
theorem cover7_leaf0182_exp_radius : (498803482761013473/500000000000000000 : ℝ) ≤ Real.exp ((-8793/458752 : ℝ)/8) ∧ Real.exp ((-8793/458752 : ℝ)/8) ≤ (997606965522026947/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8793/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0182_exp_lower : (918090213889336719/1000000000000000000 : ℝ) ≤ Real.exp ((-1367353935671/2000000000000 : ℝ)/8) ∧ Real.exp ((-1367353935671/2000000000000 : ℝ)/8) ≤ (11476127673616709/12500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1367353935671/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0182_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019030394161/1000000000000 : ℝ) ≤ 4*Real.exp (1099/8192 : ℝ)*Real.exp (-mu (radius 7 (8793/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (2019030394161/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8793/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0182_exp_radius
  have hrNumeric : (245253826059/250000000000 : ℝ) ≤ Real.exp (-8793/458752 : ℝ) ∧ Real.exp (-8793/458752 : ℝ) ≤ (981015304237/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (245253826059/250000000000 : ℝ) ≤ (radius 7 (8793/65536 : ℝ)) ∧ (radius 7 (8793/65536 : ℝ)) ≤ (981015304237/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8793/65536 : ℝ)) (245253826059/250000000000 : ℝ) (981015304237/1000000000000 : ℝ) (193930329893/1000000000000 : ℝ) (1939303299/10000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8793/65536 : ℝ)) (245253826059/250000000000 : ℝ) (981015304237/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8793/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (245253826059/250000000000 : ℝ) (981015304237/1000000000000 : ℝ) (495253826059/500000000000 : ℝ) (990507652119/1000000000000 : ℝ) (247615541747/250000000000 : ℝ) (99046216699/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8793/65536 : ℝ)) 1 (495253826059/500000000000 : ℝ) (990507652119/1000000000000 : ℝ) (247615541747/250000000000 : ℝ) (99046216699/100000000000 : ℝ) (990484909553/1000000000000 : ℝ) (198096981911/200000000000 : ℝ) (990484909291/1000000000000 : ℝ) (495242454647/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8793/65536 : ℝ)) 2 (990484909553/1000000000000 : ℝ) (198096981911/200000000000 : ℝ) (990484909291/1000000000000 : ℝ) (495242454647/500000000000 : ℝ) (495242454711/500000000000 : ℝ) (39619396377/40000000000 : ℝ) (990484909421/1000000000000 : ℝ) (39619396377/40000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8793/65536 : ℝ)) 3 (495242454711/500000000000 : ℝ) (39619396377/40000000000 : ℝ) (990484909421/1000000000000 : ℝ) (39619396377/40000000000 : ℝ) (990484909421/1000000000000 : ℝ) (39619396377/40000000000 : ℝ) (990484909421/1000000000000 : ℝ) (39619396377/40000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8793/65536 : ℝ)) 4 (990484909421/1000000000000 : ℝ) (39619396377/40000000000 : ℝ) (990484909421/1000000000000 : ℝ) (39619396377/40000000000 : ℝ) (990484909421/1000000000000 : ℝ) (39619396377/40000000000 : ℝ) (990484909421/1000000000000 : ℝ) (39619396377/40000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8793/65536 : ℝ)) 5 (990484909421/1000000000000 : ℝ) (39619396377/40000000000 : ℝ) (990484909421/1000000000000 : ℝ) (39619396377/40000000000 : ℝ) (990484909421/1000000000000 : ℝ) (39619396377/40000000000 : ℝ) (990484909421/1000000000000 : ℝ) (39619396377/40000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8793/65536 : ℝ)) 6 (990484909421/1000000000000 : ℝ) (39619396377/40000000000 : ℝ) (990484909421/1000000000000 : ℝ) (39619396377/40000000000 : ℝ) (990484909421/1000000000000 : ℝ) (39619396377/40000000000 : ℝ) (990484909421/1000000000000 : ℝ) (39619396377/40000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8793/65536 : ℝ)) 7 (990484909421/1000000000000 : ℝ) (39619396377/40000000000 : ℝ) (990484909421/1000000000000 : ℝ) (39619396377/40000000000 : ℝ) (990484909421/1000000000000 : ℝ) (39619396377/40000000000 : ℝ) (990484909421/1000000000000 : ℝ) (39619396377/40000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8793/65536 : ℝ))) (193930329893/1000000000000 : ℝ) (1939303299/10000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8793/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (193930329893/1000000000000 : ℝ) (1939303299/10000000000 : ℝ) (298482582473/500000000000 : ℝ) (11939303299/20000000000 : ℝ) (220187607447/500000000000 : ℝ) (440375214903/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8793/65536 : ℝ))) 1 (298482582473/500000000000 : ℝ) (11939303299/20000000000 : ℝ) (220187607447/500000000000 : ℝ) (440375214903/1000000000000 : ℝ) (3241688687/6250000000 : ℝ) (518670189927/1000000000000 : ℝ) (102545338811/200000000000 : ℝ) (512726694063/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8793/65536 : ℝ))) 2 (3241688687/6250000000 : ℝ) (518670189927/1000000000000 : ℝ) (102545338811/200000000000 : ℝ) (512726694063/1000000000000 : ℝ) (515698441987/1000000000000 : ℝ) (103139688399/200000000000 : ℝ) (64461234933/125000000000 : ℝ) (515689879473/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8793/65536 : ℝ))) 3 (515698441987/1000000000000 : ℝ) (103139688399/200000000000 : ℝ) (64461234933/125000000000 : ℝ) (515689879473/1000000000000 : ℝ) (20627766429/40000000000 : ℝ) (257847080367/500000000000 : ℝ) (515694160707/1000000000000 : ℝ) (515694160717/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8793/65536 : ℝ))) 4 (20627766429/40000000000 : ℝ) (257847080367/500000000000 : ℝ) (515694160707/1000000000000 : ℝ) (515694160717/1000000000000 : ℝ) (128923540179/250000000000 : ℝ) (257847080363/500000000000 : ℝ) (103138832143/200000000000 : ℝ) (257847080363/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8793/65536 : ℝ))) 5 (128923540179/250000000000 : ℝ) (257847080363/500000000000 : ℝ) (103138832143/200000000000 : ℝ) (257847080363/500000000000 : ℝ) (103138832143/200000000000 : ℝ) (257847080363/500000000000 : ℝ) (103138832143/200000000000 : ℝ) (257847080363/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8793/65536 : ℝ))) 6 (103138832143/200000000000 : ℝ) (257847080363/500000000000 : ℝ) (103138832143/200000000000 : ℝ) (257847080363/500000000000 : ℝ) (103138832143/200000000000 : ℝ) (257847080363/500000000000 : ℝ) (103138832143/200000000000 : ℝ) (257847080363/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8793/65536 : ℝ))) 7 (103138832143/200000000000 : ℝ) (257847080363/500000000000 : ℝ) (103138832143/200000000000 : ℝ) (257847080363/500000000000 : ℝ) (103138832143/200000000000 : ℝ) (257847080363/500000000000 : ℝ) (103138832143/200000000000 : ℝ) (257847080363/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8793/65536 : ℝ)) hmem 8 (990484909421/1000000000000 : ℝ) (39619396377/40000000000 : ℝ) (990484909421/1000000000000 : ℝ) (39619396377/40000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8793/65536 : ℝ))) hcmem 8 (103138832143/200000000000 : ℝ) (257847080363/500000000000 : ℝ) (103138832143/200000000000 : ℝ) (257847080363/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8793/65536 : ℝ)) (990484909421/1000000000000 : ℝ) (39619396377/40000000000 : ℝ) (103138832143/200000000000 : ℝ) (257847080363/500000000000 : ℝ) (817832241251/1000000000000 : ℝ) (817832241273/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0182_exp_lower
  have heNumeric : (2019030394161/1000000000000 : ℝ)/4 ≤ Real.exp (-1367353935671/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019030394161/1000000000000 : ℝ)/4 ≤ Real.exp ((1099/8192 : ℝ)-(817832241273/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (1099/8192 : ℝ) (8793/65536 : ℝ) (817832241273/1000000000000 : ℝ) (2019030394161/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0183; no trusted numerical premise.
theorem cover7_leaf0183_exp_radius : (249401673423934503/250000000000000000 : ℝ) ≤ Real.exp ((-4397/229376 : ℝ)/8) ∧ Real.exp ((-4397/229376 : ℝ)/8) ≤ (997606693695738013/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4397/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0183_exp_lower : (14345159314790033/15625000000000000 : ℝ) ≤ Real.exp ((-10938833959063/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938833959063/16000000000000 : ℝ)/8) ≤ (918090196146562113/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938833959063/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0183_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019030082007/1000000000000 : ℝ) ≤ 4*Real.exp (8793/65536 : ℝ)*Real.exp (-mu (radius 7 (4397/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (2019030082007/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4397/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0183_exp_radius
  have hrNumeric : (196202633159/200000000000 : ℝ) ≤ Real.exp (-4397/229376 : ℝ) ∧ Real.exp (-4397/229376 : ℝ) ≤ (245253291449/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196202633159/200000000000 : ℝ) ≤ (radius 7 (4397/32768 : ℝ)) ∧ (radius 7 (4397/32768 : ℝ)) ≤ (245253291449/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4397/32768 : ℝ)) (196202633159/200000000000 : ℝ) (245253291449/250000000000 : ℝ) (19394114709/100000000000 : ℝ) (24242643387/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4397/32768 : ℝ)) (196202633159/200000000000 : ℝ) (245253291449/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4397/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196202633159/200000000000 : ℝ) (245253291449/250000000000 : ℝ) (990506582897/1000000000000 : ℝ) (495253291449/500000000000 : ℝ) (990461087471/1000000000000 : ℝ) (61903817967/62500000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4397/32768 : ℝ)) 1 (990506582897/1000000000000 : ℝ) (495253291449/500000000000 : ℝ) (990461087471/1000000000000 : ℝ) (61903817967/62500000000 : ℝ) (61905239699/62500000000 : ℝ) (198096767037/200000000000 : ℝ) (495241917461/500000000000 : ℝ) (247620958731/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4397/32768 : ℝ)) 2 (61905239699/62500000000 : ℝ) (198096767037/200000000000 : ℝ) (495241917461/500000000000 : ℝ) (247620958731/250000000000 : ℝ) (990483835053/1000000000000 : ℝ) (198096767011/200000000000 : ℝ) (247620958763/250000000000 : ℝ) (198096767011/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4397/32768 : ℝ)) 3 (990483835053/1000000000000 : ℝ) (198096767011/200000000000 : ℝ) (247620958763/250000000000 : ℝ) (198096767011/200000000000 : ℝ) (247620958763/250000000000 : ℝ) (198096767011/200000000000 : ℝ) (247620958763/250000000000 : ℝ) (198096767011/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4397/32768 : ℝ)) 4 (247620958763/250000000000 : ℝ) (198096767011/200000000000 : ℝ) (247620958763/250000000000 : ℝ) (198096767011/200000000000 : ℝ) (247620958763/250000000000 : ℝ) (198096767011/200000000000 : ℝ) (247620958763/250000000000 : ℝ) (198096767011/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4397/32768 : ℝ)) 5 (247620958763/250000000000 : ℝ) (198096767011/200000000000 : ℝ) (247620958763/250000000000 : ℝ) (198096767011/200000000000 : ℝ) (247620958763/250000000000 : ℝ) (198096767011/200000000000 : ℝ) (247620958763/250000000000 : ℝ) (198096767011/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4397/32768 : ℝ)) 6 (247620958763/250000000000 : ℝ) (198096767011/200000000000 : ℝ) (247620958763/250000000000 : ℝ) (198096767011/200000000000 : ℝ) (247620958763/250000000000 : ℝ) (198096767011/200000000000 : ℝ) (247620958763/250000000000 : ℝ) (198096767011/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4397/32768 : ℝ)) 7 (247620958763/250000000000 : ℝ) (198096767011/200000000000 : ℝ) (247620958763/250000000000 : ℝ) (198096767011/200000000000 : ℝ) (247620958763/250000000000 : ℝ) (198096767011/200000000000 : ℝ) (247620958763/250000000000 : ℝ) (198096767011/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4397/32768 : ℝ))) (19394114709/100000000000 : ℝ) (24242643387/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4397/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (19394114709/100000000000 : ℝ) (24242643387/125000000000 : ℝ) (119394114709/200000000000 : ℝ) (149242643387/250000000000 : ℝ) (220193748259/500000000000 : ℝ) (220193748263/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4397/32768 : ℝ))) 1 (119394114709/200000000000 : ℝ) (149242643387/250000000000 : ℝ) (220193748259/500000000000 : ℝ) (220193748263/500000000000 : ℝ) (518679035031/1000000000000 : ℝ) (518679035037/1000000000000 : ℝ) (256368083221/500000000000 : ℝ) (512736166449/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4397/32768 : ℝ))) 2 (518679035031/1000000000000 : ℝ) (518679035037/1000000000000 : ℝ) (256368083221/500000000000 : ℝ) (512736166449/1000000000000 : ℝ) (16115862523/31250000000 : ℝ) (515707600743/1000000000000 : ℝ) (515699040173/1000000000000 : ℝ) (25784952009/50000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4397/32768 : ℝ))) 3 (16115862523/31250000000 : ℝ) (515707600743/1000000000000 : ℝ) (515699040173/1000000000000 : ℝ) (25784952009/50000000000 : ℝ) (257851660227/500000000000 : ℝ) (257851660231/500000000000 : ℝ) (128925830109/250000000000 : ℝ) (128925830111/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4397/32768 : ℝ))) 4 (257851660227/500000000000 : ℝ) (257851660231/500000000000 : ℝ) (128925830109/250000000000 : ℝ) (128925830111/250000000000 : ℝ) (103140664089/200000000000 : ℝ) (515703320453/1000000000000 : ℝ) (128925830111/250000000000 : ℝ) (515703320453/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4397/32768 : ℝ))) 5 (103140664089/200000000000 : ℝ) (515703320453/1000000000000 : ℝ) (128925830111/250000000000 : ℝ) (515703320453/1000000000000 : ℝ) (128925830111/250000000000 : ℝ) (515703320453/1000000000000 : ℝ) (128925830111/250000000000 : ℝ) (515703320453/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4397/32768 : ℝ))) 6 (128925830111/250000000000 : ℝ) (515703320453/1000000000000 : ℝ) (128925830111/250000000000 : ℝ) (515703320453/1000000000000 : ℝ) (128925830111/250000000000 : ℝ) (515703320453/1000000000000 : ℝ) (128925830111/250000000000 : ℝ) (515703320453/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4397/32768 : ℝ))) 7 (128925830111/250000000000 : ℝ) (515703320453/1000000000000 : ℝ) (128925830111/250000000000 : ℝ) (515703320453/1000000000000 : ℝ) (128925830111/250000000000 : ℝ) (515703320453/1000000000000 : ℝ) (128925830111/250000000000 : ℝ) (515703320453/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4397/32768 : ℝ)) hmem 8 (247620958763/250000000000 : ℝ) (198096767011/200000000000 : ℝ) (247620958763/250000000000 : ℝ) (198096767011/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4397/32768 : ℝ))) hcmem 8 (128925830111/250000000000 : ℝ) (515703320453/1000000000000 : ℝ) (128925830111/250000000000 : ℝ) (515703320453/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4397/32768 : ℝ)) (247620958763/250000000000 : ℝ) (198096767011/200000000000 : ℝ) (128925830111/250000000000 : ℝ) (515703320453/1000000000000 : ℝ) (16356953093/20000000000 : ℝ) (204461913667/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0183_exp_lower
  have heNumeric : (2019030082007/1000000000000 : ℝ)/4 ≤ Real.exp (-10938833959063/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019030082007/1000000000000 : ℝ)/4 ≤ Real.exp ((8793/65536 : ℝ)-(204461913667/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8793/65536 : ℝ) (4397/32768 : ℝ) (204461913667/250000000000 : ℝ) (2019030082007/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0184; no trusted numerical premise.
theorem cover7_leaf0184_exp_radius : (199521284373904629/200000000000000000 : ℝ) ≤ Real.exp ((-8795/458752 : ℝ)/8) ∧ Real.exp ((-8795/458752 : ℝ)/8) ≤ (498803210934761573/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8795/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0184_exp_lower : (459045089268570223/500000000000000000 : ℝ) ≤ Real.exp ((-5469418207083/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469418207083/8000000000000 : ℝ)/8) ≤ (918090178537140447/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469418207083/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0184_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019029772199/1000000000000 : ℝ) ≤ 4*Real.exp (4397/32768 : ℝ)*Real.exp (-mu (radius 7 (8795/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (2019029772199/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8795/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0184_exp_radius
  have hrNumeric : (490505513679/500000000000 : ℝ) ≤ Real.exp (-8795/458752 : ℝ) ∧ Real.exp (-8795/458752 : ℝ) ≤ (981011027359/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490505513679/500000000000 : ℝ) ≤ (radius 7 (8795/65536 : ℝ)) ∧ (radius 7 (8795/65536 : ℝ)) ≤ (981011027359/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8795/65536 : ℝ)) (490505513679/500000000000 : ℝ) (981011027359/1000000000000 : ℝ) (4848799091/25000000000 : ℝ) (96975981823/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8795/65536 : ℝ)) (490505513679/500000000000 : ℝ) (981011027359/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8795/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490505513679/500000000000 : ℝ) (981011027359/1000000000000 : ℝ) (990505513679/1000000000000 : ℝ) (12381318921/12500000000 : ℝ) (495230003977/500000000000 : ℝ) (247615001989/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8795/65536 : ℝ)) 1 (990505513679/1000000000000 : ℝ) (12381318921/12500000000 : ℝ) (495230003977/500000000000 : ℝ) (247615001989/250000000000 : ℝ) (61905172551/62500000000 : ℝ) (495241380409/500000000000 : ℝ) (198096552111/200000000000 : ℝ) (990482760557/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8795/65536 : ℝ)) 2 (61905172551/62500000000 : ℝ) (495241380409/500000000000 : ℝ) (198096552111/200000000000 : ℝ) (990482760557/1000000000000 : ℝ) (198096552137/200000000000 : ℝ) (61905172543/62500000000 : ℝ) (198096552137/200000000000 : ℝ) (61905172543/62500000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8795/65536 : ℝ)) 3 (198096552137/200000000000 : ℝ) (61905172543/62500000000 : ℝ) (198096552137/200000000000 : ℝ) (61905172543/62500000000 : ℝ) (198096552137/200000000000 : ℝ) (61905172543/62500000000 : ℝ) (198096552137/200000000000 : ℝ) (61905172543/62500000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8795/65536 : ℝ)) 4 (198096552137/200000000000 : ℝ) (61905172543/62500000000 : ℝ) (198096552137/200000000000 : ℝ) (61905172543/62500000000 : ℝ) (198096552137/200000000000 : ℝ) (61905172543/62500000000 : ℝ) (198096552137/200000000000 : ℝ) (61905172543/62500000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8795/65536 : ℝ)) 5 (198096552137/200000000000 : ℝ) (61905172543/62500000000 : ℝ) (198096552137/200000000000 : ℝ) (61905172543/62500000000 : ℝ) (198096552137/200000000000 : ℝ) (61905172543/62500000000 : ℝ) (198096552137/200000000000 : ℝ) (61905172543/62500000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8795/65536 : ℝ)) 6 (198096552137/200000000000 : ℝ) (61905172543/62500000000 : ℝ) (198096552137/200000000000 : ℝ) (61905172543/62500000000 : ℝ) (198096552137/200000000000 : ℝ) (61905172543/62500000000 : ℝ) (198096552137/200000000000 : ℝ) (61905172543/62500000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8795/65536 : ℝ)) 7 (198096552137/200000000000 : ℝ) (61905172543/62500000000 : ℝ) (198096552137/200000000000 : ℝ) (61905172543/62500000000 : ℝ) (198096552137/200000000000 : ℝ) (61905172543/62500000000 : ℝ) (198096552137/200000000000 : ℝ) (61905172543/62500000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8795/65536 : ℝ))) (4848799091/25000000000 : ℝ) (96975981823/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8795/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (4848799091/25000000000 : ℝ) (96975981823/500000000000 : ℝ) (29848799091/50000000000 : ℝ) (596975981823/1000000000000 : ℝ) (220199888533/500000000000 : ℝ) (220199888537/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8795/65536 : ℝ))) 1 (29848799091/50000000000 : ℝ) (596975981823/1000000000000 : ℝ) (220199888533/500000000000 : ℝ) (220199888537/500000000000 : ℝ) (518687879443/1000000000000 : ℝ) (518687879449/1000000000000 : ℝ) (256372819009/500000000000 : ℝ) (20509825521/40000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8795/65536 : ℝ))) 2 (518687879443/1000000000000 : ℝ) (518687879449/1000000000000 : ℝ) (256372819009/500000000000 : ℝ) (20509825521/40000000000 : ℝ) (51571675873/100000000000 : ℝ) (515716758737/1000000000000 : ℝ) (257854100063/500000000000 : ℝ) (515708200133/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8795/65536 : ℝ))) 3 (51571675873/100000000000 : ℝ) (515716758737/1000000000000 : ℝ) (257854100063/500000000000 : ℝ) (515708200133/1000000000000 : ℝ) (128928119857/250000000000 : ℝ) (103142495887/200000000000 : ℝ) (51571247941/100000000000 : ℝ) (257856239709/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8795/65536 : ℝ))) 4 (128928119857/250000000000 : ℝ) (103142495887/200000000000 : ℝ) (51571247941/100000000000 : ℝ) (257856239709/500000000000 : ℝ) (515712479419/1000000000000 : ℝ) (515712479427/1000000000000 : ℝ) (257856239709/500000000000 : ℝ) (515712479427/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8795/65536 : ℝ))) 5 (515712479419/1000000000000 : ℝ) (515712479427/1000000000000 : ℝ) (257856239709/500000000000 : ℝ) (515712479427/1000000000000 : ℝ) (257856239709/500000000000 : ℝ) (515712479427/1000000000000 : ℝ) (257856239709/500000000000 : ℝ) (515712479427/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8795/65536 : ℝ))) 6 (257856239709/500000000000 : ℝ) (515712479427/1000000000000 : ℝ) (257856239709/500000000000 : ℝ) (515712479427/1000000000000 : ℝ) (257856239709/500000000000 : ℝ) (515712479427/1000000000000 : ℝ) (257856239709/500000000000 : ℝ) (515712479427/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8795/65536 : ℝ))) 7 (257856239709/500000000000 : ℝ) (515712479427/1000000000000 : ℝ) (257856239709/500000000000 : ℝ) (515712479427/1000000000000 : ℝ) (257856239709/500000000000 : ℝ) (515712479427/1000000000000 : ℝ) (257856239709/500000000000 : ℝ) (515712479427/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8795/65536 : ℝ)) hmem 8 (198096552137/200000000000 : ℝ) (61905172543/62500000000 : ℝ) (198096552137/200000000000 : ℝ) (61905172543/62500000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8795/65536 : ℝ))) hcmem 8 (257856239709/500000000000 : ℝ) (515712479427/1000000000000 : ℝ) (257856239709/500000000000 : ℝ) (515712479427/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8795/65536 : ℝ)) (198096552137/200000000000 : ℝ) (61905172543/62500000000 : ℝ) (257856239709/500000000000 : ℝ) (515712479427/1000000000000 : ℝ) (204465766721/250000000000 : ℝ) (817863066901/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0184_exp_lower
  have heNumeric : (2019029772199/1000000000000 : ℝ)/4 ≤ Real.exp (-5469418207083/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019029772199/1000000000000 : ℝ)/4 ≤ Real.exp ((4397/32768 : ℝ)-(817863066901/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4397/32768 : ℝ) (8795/65536 : ℝ) (817863066901/1000000000000 : ℝ) (2019029772199/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0185; no trusted numerical premise.
theorem cover7_leaf0185_exp_radius : (124700768755422793/125000000000000000 : ℝ) ≤ Real.exp ((-2199/114688 : ℝ)/8) ∧ Real.exp ((-2199/114688 : ℝ)/8) ≤ (199521230008676469/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2199/114688 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0185_exp_lower : (91809016106256361/100000000000000000 : ℝ) ≤ Real.exp ((-10938838850469/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938838850469/16000000000000 : ℝ)/8) ≤ (918090161062563611/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938838850469/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0185_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019029464763/1000000000000 : ℝ) ≤ 4*Real.exp (8795/65536 : ℝ)*Real.exp (-mu (radius 7 (2199/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (2019029464763/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2199/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0185_exp_radius
  have hrNumeric : (490504444463/500000000000 : ℝ) ≤ Real.exp (-2199/114688 : ℝ) ∧ Real.exp (-2199/114688 : ℝ) ≤ (981008888927/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490504444463/500000000000 : ℝ) ≤ (radius 7 (2199/16384 : ℝ)) ∧ (radius 7 (2199/16384 : ℝ)) ≤ (981008888927/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2199/16384 : ℝ)) (490504444463/500000000000 : ℝ) (981008888927/1000000000000 : ℝ) (96981389769/500000000000 : ℝ) (24245347443/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2199/16384 : ℝ)) (490504444463/500000000000 : ℝ) (981008888927/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2199/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490504444463/500000000000 : ℝ) (981008888927/1000000000000 : ℝ) (990504444463/1000000000000 : ℝ) (61906527779/62500000000 : ℝ) (990458928439/1000000000000 : ℝ) (990458928441/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2199/16384 : ℝ)) 1 (990504444463/1000000000000 : ℝ) (61906527779/62500000000 : ℝ) (990458928439/1000000000000 : ℝ) (990458928441/1000000000000 : ℝ) (990481686451/1000000000000 : ℝ) (990481686453/1000000000000 : ℝ) (990481686189/1000000000000 : ℝ) (61905105387/62500000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2199/16384 : ℝ)) 2 (990481686451/1000000000000 : ℝ) (990481686453/1000000000000 : ℝ) (990481686189/1000000000000 : ℝ) (61905105387/62500000000 : ℝ) (12381021079/12500000000 : ℝ) (990481686323/1000000000000 : ℝ) (990481686319/1000000000000 : ℝ) (990481686323/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2199/16384 : ℝ)) 3 (12381021079/12500000000 : ℝ) (990481686323/1000000000000 : ℝ) (990481686319/1000000000000 : ℝ) (990481686323/1000000000000 : ℝ) (990481686319/1000000000000 : ℝ) (990481686323/1000000000000 : ℝ) (990481686319/1000000000000 : ℝ) (990481686323/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2199/16384 : ℝ)) 4 (990481686319/1000000000000 : ℝ) (990481686323/1000000000000 : ℝ) (990481686319/1000000000000 : ℝ) (990481686323/1000000000000 : ℝ) (990481686319/1000000000000 : ℝ) (990481686323/1000000000000 : ℝ) (990481686319/1000000000000 : ℝ) (990481686323/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2199/16384 : ℝ)) 5 (990481686319/1000000000000 : ℝ) (990481686323/1000000000000 : ℝ) (990481686319/1000000000000 : ℝ) (990481686323/1000000000000 : ℝ) (990481686319/1000000000000 : ℝ) (990481686323/1000000000000 : ℝ) (990481686319/1000000000000 : ℝ) (990481686323/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2199/16384 : ℝ)) 6 (990481686319/1000000000000 : ℝ) (990481686323/1000000000000 : ℝ) (990481686319/1000000000000 : ℝ) (990481686323/1000000000000 : ℝ) (990481686319/1000000000000 : ℝ) (990481686323/1000000000000 : ℝ) (990481686319/1000000000000 : ℝ) (990481686323/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2199/16384 : ℝ)) 7 (990481686319/1000000000000 : ℝ) (990481686323/1000000000000 : ℝ) (990481686319/1000000000000 : ℝ) (990481686323/1000000000000 : ℝ) (990481686319/1000000000000 : ℝ) (990481686323/1000000000000 : ℝ) (990481686319/1000000000000 : ℝ) (990481686323/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2199/16384 : ℝ))) (96981389769/500000000000 : ℝ) (24245347443/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2199/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (96981389769/500000000000 : ℝ) (24245347443/125000000000 : ℝ) (596981389769/1000000000000 : ℝ) (149245347443/250000000000 : ℝ) (440412056531/1000000000000 : ℝ) (220206028269/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2199/16384 : ℝ))) 1 (596981389769/1000000000000 : ℝ) (149245347443/250000000000 : ℝ) (440412056531/1000000000000 : ℝ) (220206028269/500000000000 : ℝ) (10373934463/20000000000 : ℝ) (103739344631/200000000000 : ℝ) (256377554389/500000000000 : ℝ) (102551021757/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2199/16384 : ℝ))) 2 (10373934463/20000000000 : ℝ) (103739344631/200000000000 : ℝ) (256377554389/500000000000 : ℝ) (102551021757/200000000000 : ℝ) (128931478991/250000000000 : ℝ) (51572591597/100000000000 : ℝ) (515717359317/1000000000000 : ℝ) (128929339831/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2199/16384 : ℝ))) 3 (128931478991/250000000000 : ℝ) (51572591597/100000000000 : ℝ) (515717359317/1000000000000 : ℝ) (128929339831/250000000000 : ℝ) (12893040941/25000000000 : ℝ) (515721637647/1000000000000 : ℝ) (257860818811/500000000000 : ℝ) (51572163763/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2199/16384 : ℝ))) 4 (12893040941/25000000000 : ℝ) (515721637647/1000000000000 : ℝ) (257860818811/500000000000 : ℝ) (51572163763/100000000000 : ℝ) (515721637631/1000000000000 : ℝ) (515721637639/1000000000000 : ℝ) (51572163763/100000000000 : ℝ) (515721637639/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2199/16384 : ℝ))) 5 (515721637631/1000000000000 : ℝ) (515721637639/1000000000000 : ℝ) (51572163763/100000000000 : ℝ) (515721637639/1000000000000 : ℝ) (51572163763/100000000000 : ℝ) (515721637639/1000000000000 : ℝ) (51572163763/100000000000 : ℝ) (515721637639/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2199/16384 : ℝ))) 6 (51572163763/100000000000 : ℝ) (515721637639/1000000000000 : ℝ) (51572163763/100000000000 : ℝ) (515721637639/1000000000000 : ℝ) (51572163763/100000000000 : ℝ) (515721637639/1000000000000 : ℝ) (51572163763/100000000000 : ℝ) (515721637639/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2199/16384 : ℝ))) 7 (51572163763/100000000000 : ℝ) (515721637639/1000000000000 : ℝ) (51572163763/100000000000 : ℝ) (515721637639/1000000000000 : ℝ) (51572163763/100000000000 : ℝ) (515721637639/1000000000000 : ℝ) (51572163763/100000000000 : ℝ) (515721637639/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2199/16384 : ℝ)) hmem 8 (990481686319/1000000000000 : ℝ) (990481686323/1000000000000 : ℝ) (990481686319/1000000000000 : ℝ) (990481686323/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2199/16384 : ℝ))) hcmem 8 (51572163763/100000000000 : ℝ) (515721637639/1000000000000 : ℝ) (51572163763/100000000000 : ℝ) (515721637639/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2199/16384 : ℝ)) (990481686319/1000000000000 : ℝ) (990481686323/1000000000000 : ℝ) (51572163763/100000000000 : ℝ) (515721637639/1000000000000 : ℝ) (40893923897/50000000000 : ℝ) (817878477959/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0185_exp_lower
  have heNumeric : (2019029464763/1000000000000 : ℝ)/4 ≤ Real.exp (-10938838850469/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019029464763/1000000000000 : ℝ)/4 ≤ Real.exp ((8795/65536 : ℝ)-(817878477959/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8795/65536 : ℝ) (2199/16384 : ℝ) (817878477959/1000000000000 : ℝ) (2019029464763/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0186; no trusted numerical premise.
theorem cover7_leaf0186_exp_radius : (99760587821731561/100000000000000000 : ℝ) ≤ Real.exp ((-8797/458752 : ℝ)/8) ∧ Real.exp ((-8797/458752 : ℝ)/8) ≤ (997605878217315611/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8797/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0186_exp_lower : (36723605748904083/40000000000000000 : ℝ) ≤ Real.exp ((-2734710317001/4000000000000 : ℝ)/8) ∧ Real.exp ((-2734710317001/4000000000000 : ℝ)/8) ≤ (229522535930650519/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2734710317001/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0186_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (126189322481/62500000000 : ℝ) ≤ 4*Real.exp (2199/16384 : ℝ)*Real.exp (-mu (radius 7 (8797/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (126189322481/62500000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8797/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0186_exp_radius
  have hrNumeric : (981006750499/1000000000000 : ℝ) ≤ Real.exp (-8797/458752 : ℝ) ∧ Real.exp (-8797/458752 : ℝ) ≤ (1962013501/2000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (981006750499/1000000000000 : ℝ) ≤ (radius 7 (8797/65536 : ℝ)) ∧ (radius 7 (8797/65536 : ℝ)) ≤ (1962013501/2000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8797/65536 : ℝ)) (981006750499/1000000000000 : ℝ) (1962013501/2000000000 : ℝ) (6061674837/31250000000 : ℝ) (19397359479/100000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8797/65536 : ℝ)) (981006750499/1000000000000 : ℝ) (1962013501/2000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8797/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (981006750499/1000000000000 : ℝ) (1962013501/2000000000 : ℝ) (990503375249/1000000000000 : ℝ) (3962013501/4000000000 : ℝ) (39618313957/40000000000 : ℝ) (990457848927/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8797/65536 : ℝ)) 1 (990503375249/1000000000000 : ℝ) (3962013501/4000000000 : ℝ) (39618313957/40000000000 : ℝ) (990457848927/1000000000000 : ℝ) (990480612087/1000000000000 : ℝ) (990480612089/1000000000000 : ℝ) (39619224473/40000000000 : ℝ) (990480611827/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8797/65536 : ℝ)) 2 (990480612087/1000000000000 : ℝ) (990480612089/1000000000000 : ℝ) (39619224473/40000000000 : ℝ) (990480611827/1000000000000 : ℝ) (247620152989/250000000000 : ℝ) (495240305979/500000000000 : ℝ) (198096122391/200000000000 : ℝ) (495240305979/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8797/65536 : ℝ)) 3 (247620152989/250000000000 : ℝ) (495240305979/500000000000 : ℝ) (198096122391/200000000000 : ℝ) (495240305979/500000000000 : ℝ) (198096122391/200000000000 : ℝ) (495240305979/500000000000 : ℝ) (198096122391/200000000000 : ℝ) (495240305979/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8797/65536 : ℝ)) 4 (198096122391/200000000000 : ℝ) (495240305979/500000000000 : ℝ) (198096122391/200000000000 : ℝ) (495240305979/500000000000 : ℝ) (198096122391/200000000000 : ℝ) (495240305979/500000000000 : ℝ) (198096122391/200000000000 : ℝ) (495240305979/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8797/65536 : ℝ)) 5 (198096122391/200000000000 : ℝ) (495240305979/500000000000 : ℝ) (198096122391/200000000000 : ℝ) (495240305979/500000000000 : ℝ) (198096122391/200000000000 : ℝ) (495240305979/500000000000 : ℝ) (198096122391/200000000000 : ℝ) (495240305979/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8797/65536 : ℝ)) 6 (198096122391/200000000000 : ℝ) (495240305979/500000000000 : ℝ) (198096122391/200000000000 : ℝ) (495240305979/500000000000 : ℝ) (198096122391/200000000000 : ℝ) (495240305979/500000000000 : ℝ) (198096122391/200000000000 : ℝ) (495240305979/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8797/65536 : ℝ)) 7 (198096122391/200000000000 : ℝ) (495240305979/500000000000 : ℝ) (198096122391/200000000000 : ℝ) (495240305979/500000000000 : ℝ) (198096122391/200000000000 : ℝ) (495240305979/500000000000 : ℝ) (198096122391/200000000000 : ℝ) (495240305979/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8797/65536 : ℝ))) (6061674837/31250000000 : ℝ) (19397359479/100000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8797/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (6061674837/31250000000 : ℝ) (19397359479/100000000000 : ℝ) (37311674837/62500000000 : ℝ) (119397359479/200000000000 : ℝ) (440424334913/1000000000000 : ℝ) (440424334921/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8797/65536 : ℝ))) 1 (37311674837/62500000000 : ℝ) (119397359479/200000000000 : ℝ) (440424334913/1000000000000 : ℝ) (440424334921/1000000000000 : ℝ) (64838195769/125000000000 : ℝ) (259352783079/500000000000 : ℝ) (512764578723/1000000000000 : ℝ) (51276457873/100000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8797/65536 : ℝ))) 2 (64838195769/125000000000 : ℝ) (259352783079/500000000000 : ℝ) (512764578723/1000000000000 : ℝ) (51276457873/100000000000 : ℝ) (515735072437/1000000000000 : ℝ) (128933768111/250000000000 : ℝ) (128931629437/250000000000 : ℝ) (128931629439/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8797/65536 : ℝ))) 3 (515735072437/1000000000000 : ℝ) (128933768111/250000000000 : ℝ) (128931629437/250000000000 : ℝ) (128931629439/250000000000 : ℝ) (128932698773/250000000000 : ℝ) (5157307951/10000000000 : ℝ) (257865397537/500000000000 : ℝ) (515730795083/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8797/65536 : ℝ))) 4 (128932698773/250000000000 : ℝ) (5157307951/10000000000 : ℝ) (257865397537/500000000000 : ℝ) (515730795083/1000000000000 : ℝ) (515730795083/1000000000000 : ℝ) (128932698773/250000000000 : ℝ) (257865397541/500000000000 : ℝ) (128932698773/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8797/65536 : ℝ))) 5 (515730795083/1000000000000 : ℝ) (128932698773/250000000000 : ℝ) (257865397541/500000000000 : ℝ) (128932698773/250000000000 : ℝ) (257865397541/500000000000 : ℝ) (128932698773/250000000000 : ℝ) (257865397541/500000000000 : ℝ) (128932698773/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8797/65536 : ℝ))) 6 (257865397541/500000000000 : ℝ) (128932698773/250000000000 : ℝ) (257865397541/500000000000 : ℝ) (128932698773/250000000000 : ℝ) (257865397541/500000000000 : ℝ) (128932698773/250000000000 : ℝ) (257865397541/500000000000 : ℝ) (128932698773/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8797/65536 : ℝ))) 7 (257865397541/500000000000 : ℝ) (128932698773/250000000000 : ℝ) (257865397541/500000000000 : ℝ) (128932698773/250000000000 : ℝ) (257865397541/500000000000 : ℝ) (128932698773/250000000000 : ℝ) (257865397541/500000000000 : ℝ) (128932698773/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8797/65536 : ℝ)) hmem 8 (198096122391/200000000000 : ℝ) (495240305979/500000000000 : ℝ) (198096122391/200000000000 : ℝ) (495240305979/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8797/65536 : ℝ))) hcmem 8 (257865397541/500000000000 : ℝ) (128932698773/250000000000 : ℝ) (257865397541/500000000000 : ℝ) (128932698773/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8797/65536 : ℝ)) (198096122391/200000000000 : ℝ) (495240305979/500000000000 : ℝ) (257865397541/500000000000 : ℝ) (128932698773/250000000000 : ℝ) (32715755513/40000000000 : ℝ) (204473471961/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0186_exp_lower
  have heNumeric : (126189322481/62500000000 : ℝ)/4 ≤ Real.exp (-2734710317001/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (126189322481/62500000000 : ℝ)/4 ≤ Real.exp ((2199/16384 : ℝ)-(204473471961/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2199/16384 : ℝ) (8797/65536 : ℝ) (204473471961/250000000000 : ℝ) (126189322481/62500000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0187; no trusted numerical premise.
theorem cover7_leaf0187_exp_radius : (997605606391322943/1000000000000000000 : ℝ) ≤ Real.exp ((-4399/229376 : ℝ)/8) ∧ Real.exp ((-4399/229376 : ℝ)/8) ≤ (15587587599864421/15625000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4399/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0187_exp_lower : (36723605060667281/40000000000000000 : ℝ) ≤ Real.exp ((-10938843666851/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938843666851/16000000000000 : ℝ)/8) ≤ (459045063258341013/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938843666851/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0187_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019028856987/1000000000000 : ℝ) ≤ 4*Real.exp (8797/65536 : ℝ)*Real.exp (-mu (radius 7 (4399/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (2019028856987/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4399/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0187_exp_radius
  have hrNumeric : (245251153019/250000000000 : ℝ) ≤ Real.exp (-4399/229376 : ℝ) ∧ Real.exp (-4399/229376 : ℝ) ≤ (981004612077/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (245251153019/250000000000 : ℝ) ≤ (radius 7 (4399/32768 : ℝ)) ∧ (radius 7 (4399/32768 : ℝ)) ≤ (981004612077/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4399/32768 : ℝ)) (245251153019/250000000000 : ℝ) (981004612077/1000000000000 : ℝ) (96992204691/500000000000 : ℝ) (193984409389/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4399/32768 : ℝ)) (245251153019/250000000000 : ℝ) (981004612077/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4399/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (245251153019/250000000000 : ℝ) (981004612077/1000000000000 : ℝ) (495251153019/500000000000 : ℝ) (990502306039/1000000000000 : ℝ) (247614192353/250000000000 : ℝ) (495228384707/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4399/32768 : ℝ)) 1 (495251153019/500000000000 : ℝ) (990502306039/1000000000000 : ℝ) (247614192353/250000000000 : ℝ) (495228384707/500000000000 : ℝ) (39619181509/40000000000 : ℝ) (990479537727/1000000000000 : ℝ) (990479537463/1000000000000 : ℝ) (198095907493/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4399/32768 : ℝ)) 2 (39619181509/40000000000 : ℝ) (990479537727/1000000000000 : ℝ) (990479537463/1000000000000 : ℝ) (198095907493/200000000000 : ℝ) (495239768797/500000000000 : ℝ) (247619884399/250000000000 : ℝ) (990479537593/1000000000000 : ℝ) (247619884399/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4399/32768 : ℝ)) 3 (495239768797/500000000000 : ℝ) (247619884399/250000000000 : ℝ) (990479537593/1000000000000 : ℝ) (247619884399/250000000000 : ℝ) (990479537593/1000000000000 : ℝ) (247619884399/250000000000 : ℝ) (990479537593/1000000000000 : ℝ) (247619884399/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4399/32768 : ℝ)) 4 (990479537593/1000000000000 : ℝ) (247619884399/250000000000 : ℝ) (990479537593/1000000000000 : ℝ) (247619884399/250000000000 : ℝ) (990479537593/1000000000000 : ℝ) (247619884399/250000000000 : ℝ) (990479537593/1000000000000 : ℝ) (247619884399/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4399/32768 : ℝ)) 5 (990479537593/1000000000000 : ℝ) (247619884399/250000000000 : ℝ) (990479537593/1000000000000 : ℝ) (247619884399/250000000000 : ℝ) (990479537593/1000000000000 : ℝ) (247619884399/250000000000 : ℝ) (990479537593/1000000000000 : ℝ) (247619884399/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4399/32768 : ℝ)) 6 (990479537593/1000000000000 : ℝ) (247619884399/250000000000 : ℝ) (990479537593/1000000000000 : ℝ) (247619884399/250000000000 : ℝ) (990479537593/1000000000000 : ℝ) (247619884399/250000000000 : ℝ) (990479537593/1000000000000 : ℝ) (247619884399/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4399/32768 : ℝ)) 7 (990479537593/1000000000000 : ℝ) (247619884399/250000000000 : ℝ) (990479537593/1000000000000 : ℝ) (247619884399/250000000000 : ℝ) (990479537593/1000000000000 : ℝ) (247619884399/250000000000 : ℝ) (990479537593/1000000000000 : ℝ) (247619884399/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4399/32768 : ℝ))) (96992204691/500000000000 : ℝ) (193984409389/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4399/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (96992204691/500000000000 : ℝ) (193984409389/1000000000000 : ℝ) (596992204691/1000000000000 : ℝ) (119398440939/200000000000 : ℝ) (440436612217/1000000000000 : ℝ) (220218306113/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4399/32768 : ℝ))) 1 (596992204691/1000000000000 : ℝ) (119398440939/200000000000 : ℝ) (440436612217/1000000000000 : ℝ) (220218306113/500000000000 : ℝ) (259357204227/500000000000 : ℝ) (518714408461/1000000000000 : ℝ) (102554809571/200000000000 : ℝ) (512774047863/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4399/32768 : ℝ))) 2 (259357204227/500000000000 : ℝ) (518714408461/1000000000000 : ℝ) (102554809571/200000000000 : ℝ) (512774047863/1000000000000 : ℝ) (257872114077/500000000000 : ℝ) (257872114081/500000000000 : ℝ) (257867837711/500000000000 : ℝ) (515735675431/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4399/32768 : ℝ))) 3 (257872114077/500000000000 : ℝ) (257872114081/500000000000 : ℝ) (257867837711/500000000000 : ℝ) (515735675431/1000000000000 : ℝ) (128934987947/250000000000 : ℝ) (515739951797/1000000000000 : ℝ) (51573995177/100000000000 : ℝ) (515739951779/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4399/32768 : ℝ))) 4 (128934987947/250000000000 : ℝ) (515739951797/1000000000000 : ℝ) (51573995177/100000000000 : ℝ) (515739951779/1000000000000 : ℝ) (515739951779/1000000000000 : ℝ) (128934987947/250000000000 : ℝ) (257869975889/500000000000 : ℝ) (128934987947/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4399/32768 : ℝ))) 5 (515739951779/1000000000000 : ℝ) (128934987947/250000000000 : ℝ) (257869975889/500000000000 : ℝ) (128934987947/250000000000 : ℝ) (257869975889/500000000000 : ℝ) (128934987947/250000000000 : ℝ) (257869975889/500000000000 : ℝ) (128934987947/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4399/32768 : ℝ))) 6 (257869975889/500000000000 : ℝ) (128934987947/250000000000 : ℝ) (257869975889/500000000000 : ℝ) (128934987947/250000000000 : ℝ) (257869975889/500000000000 : ℝ) (128934987947/250000000000 : ℝ) (257869975889/500000000000 : ℝ) (128934987947/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4399/32768 : ℝ))) 7 (257869975889/500000000000 : ℝ) (128934987947/250000000000 : ℝ) (257869975889/500000000000 : ℝ) (128934987947/250000000000 : ℝ) (257869975889/500000000000 : ℝ) (128934987947/250000000000 : ℝ) (257869975889/500000000000 : ℝ) (128934987947/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4399/32768 : ℝ)) hmem 8 (990479537593/1000000000000 : ℝ) (247619884399/250000000000 : ℝ) (990479537593/1000000000000 : ℝ) (247619884399/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4399/32768 : ℝ))) hcmem 8 (257869975889/500000000000 : ℝ) (128934987947/250000000000 : ℝ) (257869975889/500000000000 : ℝ) (128934987947/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4399/32768 : ℝ)) (990479537593/1000000000000 : ℝ) (247619884399/250000000000 : ℝ) (257869975889/500000000000 : ℝ) (128934987947/250000000000 : ℝ) (817909296541/1000000000000 : ℝ) (817909296561/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0187_exp_lower
  have heNumeric : (2019028856987/1000000000000 : ℝ)/4 ≤ Real.exp (-10938843666851/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019028856987/1000000000000 : ℝ)/4 ≤ Real.exp ((8797/65536 : ℝ)-(817909296561/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8797/65536 : ℝ) (4399/32768 : ℝ) (817909296561/1000000000000 : ℝ) (2019028856987/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0188; no trusted numerical premise.
theorem cover7_leaf0188_exp_radius : (498802667282702171/500000000000000000 : ℝ) ≤ Real.exp ((-1257/65536 : ℝ)/8) ∧ Real.exp ((-1257/65536 : ℝ)/8) ≤ (997605334565404343/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1257/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0188_exp_lower : (918090109445492021/1000000000000000000 : ℝ) ≤ Real.exp ((-5469423023457/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469423023457/8000000000000 : ℝ)/8) ≤ (459045054722746011/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469423023457/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0188_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019028556649/1000000000000 : ℝ) ≤ 4*Real.exp (4399/32768 : ℝ)*Real.exp (-mu (radius 7 (8799/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (2019028556649/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8799/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0188_exp_radius
  have hrNumeric : (490501236829/500000000000 : ℝ) ≤ Real.exp (-1257/65536 : ℝ) ∧ Real.exp (-1257/65536 : ℝ) ≤ (981002473659/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490501236829/500000000000 : ℝ) ≤ (radius 7 (8799/65536 : ℝ)) ∧ (radius 7 (8799/65536 : ℝ)) ≤ (981002473659/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8799/65536 : ℝ)) (490501236829/500000000000 : ℝ) (981002473659/1000000000000 : ℝ) (19399522333/100000000000 : ℝ) (24249402917/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8799/65536 : ℝ)) (490501236829/500000000000 : ℝ) (981002473659/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8799/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490501236829/500000000000 : ℝ) (981002473659/1000000000000 : ℝ) (990501236829/1000000000000 : ℝ) (99050123683/100000000000 : ℝ) (990455689901/1000000000000 : ℝ) (495227844951/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8799/65536 : ℝ)) 1 (990501236829/1000000000000 : ℝ) (99050123683/100000000000 : ℝ) (990455689901/1000000000000 : ℝ) (495227844951/500000000000 : ℝ) (198095692673/200000000000 : ℝ) (495239231683/500000000000 : ℝ) (990478463103/1000000000000 : ℝ) (198095692621/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8799/65536 : ℝ)) 2 (198095692673/200000000000 : ℝ) (495239231683/500000000000 : ℝ) (990478463103/1000000000000 : ℝ) (198095692621/200000000000 : ℝ) (495239231617/500000000000 : ℝ) (247619615809/250000000000 : ℝ) (990478463233/1000000000000 : ℝ) (247619615809/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8799/65536 : ℝ)) 3 (495239231617/500000000000 : ℝ) (247619615809/250000000000 : ℝ) (990478463233/1000000000000 : ℝ) (247619615809/250000000000 : ℝ) (990478463233/1000000000000 : ℝ) (247619615809/250000000000 : ℝ) (990478463233/1000000000000 : ℝ) (247619615809/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8799/65536 : ℝ)) 4 (990478463233/1000000000000 : ℝ) (247619615809/250000000000 : ℝ) (990478463233/1000000000000 : ℝ) (247619615809/250000000000 : ℝ) (990478463233/1000000000000 : ℝ) (247619615809/250000000000 : ℝ) (990478463233/1000000000000 : ℝ) (247619615809/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8799/65536 : ℝ)) 5 (990478463233/1000000000000 : ℝ) (247619615809/250000000000 : ℝ) (990478463233/1000000000000 : ℝ) (247619615809/250000000000 : ℝ) (990478463233/1000000000000 : ℝ) (247619615809/250000000000 : ℝ) (990478463233/1000000000000 : ℝ) (247619615809/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8799/65536 : ℝ)) 6 (990478463233/1000000000000 : ℝ) (247619615809/250000000000 : ℝ) (990478463233/1000000000000 : ℝ) (247619615809/250000000000 : ℝ) (990478463233/1000000000000 : ℝ) (247619615809/250000000000 : ℝ) (990478463233/1000000000000 : ℝ) (247619615809/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8799/65536 : ℝ)) 7 (990478463233/1000000000000 : ℝ) (247619615809/250000000000 : ℝ) (990478463233/1000000000000 : ℝ) (247619615809/250000000000 : ℝ) (990478463233/1000000000000 : ℝ) (247619615809/250000000000 : ℝ) (990478463233/1000000000000 : ℝ) (247619615809/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8799/65536 : ℝ))) (19399522333/100000000000 : ℝ) (24249402917/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8799/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (19399522333/100000000000 : ℝ) (24249402917/125000000000 : ℝ) (119399522333/200000000000 : ℝ) (149249402917/250000000000 : ℝ) (220224444221/500000000000 : ℝ) (8808977769/20000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8799/65536 : ℝ))) 1 (119399522333/200000000000 : ℝ) (149249402917/250000000000 : ℝ) (220224444221/500000000000 : ℝ) (8808977769/20000000000 : ℝ) (518723250053/1000000000000 : ℝ) (518723250059/1000000000000 : ℝ) (256391758087/500000000000 : ℝ) (512783516181/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8799/65536 : ℝ))) 2 (518723250053/1000000000000 : ℝ) (518723250059/1000000000000 : ℝ) (256391758087/500000000000 : ℝ) (512783516181/1000000000000 : ℝ) (515753383113/1000000000000 : ℝ) (6446917289/12500000000 : ℝ) (257872416169/500000000000 : ℝ) (103148966469/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8799/65536 : ℝ))) 3 (515753383113/1000000000000 : ℝ) (6446917289/12500000000 : ℝ) (257872416169/500000000000 : ℝ) (103148966469/200000000000 : ℝ) (20629964309/40000000000 : ℝ) (515749107733/1000000000000 : ℝ) (515749107707/1000000000000 : ℝ) (103149821543/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8799/65536 : ℝ))) 4 (20629964309/40000000000 : ℝ) (515749107733/1000000000000 : ℝ) (515749107707/1000000000000 : ℝ) (103149821543/200000000000 : ℝ) (128937276929/250000000000 : ℝ) (128937276931/250000000000 : ℝ) (103149821543/200000000000 : ℝ) (128937276931/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8799/65536 : ℝ))) 5 (128937276929/250000000000 : ℝ) (128937276931/250000000000 : ℝ) (103149821543/200000000000 : ℝ) (128937276931/250000000000 : ℝ) (103149821543/200000000000 : ℝ) (128937276931/250000000000 : ℝ) (103149821543/200000000000 : ℝ) (128937276931/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8799/65536 : ℝ))) 6 (103149821543/200000000000 : ℝ) (128937276931/250000000000 : ℝ) (103149821543/200000000000 : ℝ) (128937276931/250000000000 : ℝ) (103149821543/200000000000 : ℝ) (128937276931/250000000000 : ℝ) (103149821543/200000000000 : ℝ) (128937276931/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8799/65536 : ℝ))) 7 (103149821543/200000000000 : ℝ) (128937276931/250000000000 : ℝ) (103149821543/200000000000 : ℝ) (128937276931/250000000000 : ℝ) (103149821543/200000000000 : ℝ) (128937276931/250000000000 : ℝ) (103149821543/200000000000 : ℝ) (128937276931/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8799/65536 : ℝ)) hmem 8 (990478463233/1000000000000 : ℝ) (247619615809/250000000000 : ℝ) (990478463233/1000000000000 : ℝ) (247619615809/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8799/65536 : ℝ))) hcmem 8 (103149821543/200000000000 : ℝ) (128937276931/250000000000 : ℝ) (103149821543/200000000000 : ℝ) (128937276931/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8799/65536 : ℝ)) (990478463233/1000000000000 : ℝ) (247619615809/250000000000 : ℝ) (103149821543/200000000000 : ℝ) (128937276931/250000000000 : ℝ) (408962352043/500000000000 : ℝ) (102240588013/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0188_exp_lower
  have heNumeric : (2019028556649/1000000000000 : ℝ)/4 ≤ Real.exp (-5469423023457/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019028556649/1000000000000 : ℝ)/4 ≤ Real.exp ((4399/32768 : ℝ)-(102240588013/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4399/32768 : ℝ) (8799/65536 : ℝ) (102240588013/125000000000 : ℝ) (2019028556649/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0189; no trusted numerical premise.
theorem cover7_leaf0189_exp_radius : (997605062739559809/1000000000000000000 : ℝ) ≤ Real.exp ((-275/14336 : ℝ)/8) ∧ Real.exp ((-275/14336 : ℝ)/8) ≤ (99760506273955981/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-275/14336 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0189_exp_lower : (183618018501783459/200000000000000000 : ℝ) ≤ Real.exp ((-10938848408209/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938848408209/16000000000000 : ℝ)/8) ≤ (57380630781807331/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938848408209/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0189_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019028258679/1000000000000 : ℝ) ≤ 4*Real.exp (8799/65536 : ℝ)*Real.exp (-mu (radius 7 (275/2048 : ℝ))) ∧ (2019/1000 : ℝ) < (2019028258679/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (275/2048 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0189_exp_radius
  have hrNumeric : (196200067049/200000000000 : ℝ) ≤ Real.exp (-275/14336 : ℝ) ∧ Real.exp (-275/14336 : ℝ) ≤ (490500167623/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196200067049/200000000000 : ℝ) ≤ (radius 7 (275/2048 : ℝ)) ∧ (radius 7 (275/2048 : ℝ)) ≤ (490500167623/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (275/2048 : ℝ)) (196200067049/200000000000 : ℝ) (490500167623/500000000000 : ℝ) (1552048293/8000000000 : ℝ) (194006036631/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (275/2048 : ℝ)) (196200067049/200000000000 : ℝ) (490500167623/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (275/2048 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196200067049/200000000000 : ℝ) (490500167623/500000000000 : ℝ) (495250083811/500000000000 : ℝ) (990500167623/1000000000000 : ℝ) (990454610391/1000000000000 : ℝ) (123806826299/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (275/2048 : ℝ)) 1 (495250083811/500000000000 : ℝ) (990500167623/1000000000000 : ℝ) (990454610391/1000000000000 : ℝ) (123806826299/125000000000 : ℝ) (495238694503/500000000000 : ℝ) (61904836813/62500000000 : ℝ) (123809673593/125000000000 : ℝ) (495238694373/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (275/2048 : ℝ)) 2 (495238694503/500000000000 : ℝ) (61904836813/62500000000 : ℝ) (123809673593/125000000000 : ℝ) (495238694373/500000000000 : ℝ) (7923819111/8000000000 : ℝ) (990477388877/1000000000000 : ℝ) (495238694437/500000000000 : ℝ) (990477388877/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (275/2048 : ℝ)) 3 (7923819111/8000000000 : ℝ) (990477388877/1000000000000 : ℝ) (495238694437/500000000000 : ℝ) (990477388877/1000000000000 : ℝ) (495238694437/500000000000 : ℝ) (990477388877/1000000000000 : ℝ) (495238694437/500000000000 : ℝ) (990477388877/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (275/2048 : ℝ)) 4 (495238694437/500000000000 : ℝ) (990477388877/1000000000000 : ℝ) (495238694437/500000000000 : ℝ) (990477388877/1000000000000 : ℝ) (495238694437/500000000000 : ℝ) (990477388877/1000000000000 : ℝ) (495238694437/500000000000 : ℝ) (990477388877/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (275/2048 : ℝ)) 5 (495238694437/500000000000 : ℝ) (990477388877/1000000000000 : ℝ) (495238694437/500000000000 : ℝ) (990477388877/1000000000000 : ℝ) (495238694437/500000000000 : ℝ) (990477388877/1000000000000 : ℝ) (495238694437/500000000000 : ℝ) (990477388877/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (275/2048 : ℝ)) 6 (495238694437/500000000000 : ℝ) (990477388877/1000000000000 : ℝ) (495238694437/500000000000 : ℝ) (990477388877/1000000000000 : ℝ) (495238694437/500000000000 : ℝ) (990477388877/1000000000000 : ℝ) (495238694437/500000000000 : ℝ) (990477388877/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (275/2048 : ℝ)) 7 (495238694437/500000000000 : ℝ) (990477388877/1000000000000 : ℝ) (495238694437/500000000000 : ℝ) (990477388877/1000000000000 : ℝ) (495238694437/500000000000 : ℝ) (990477388877/1000000000000 : ℝ) (495238694437/500000000000 : ℝ) (990477388877/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (275/2048 : ℝ))) (1552048293/8000000000 : ℝ) (194006036631/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (275/2048 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (1552048293/8000000000 : ℝ) (194006036631/1000000000000 : ℝ) (74625377289/125000000000 : ℝ) (149250754579/250000000000 : ℝ) (440461163583/1000000000000 : ℝ) (44046116359/100000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (275/2048 : ℝ))) 1 (74625377289/125000000000 : ℝ) (149250754579/250000000000 : ℝ) (440461163583/1000000000000 : ℝ) (44046116359/100000000000 : ℝ) (518732090947/1000000000000 : ℝ) (518732090953/1000000000000 : ℝ) (128198245919/250000000000 : ℝ) (512792983683/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (275/2048 : ℝ))) 2 (518732090947/1000000000000 : ℝ) (518732090953/1000000000000 : ℝ) (128198245919/250000000000 : ℝ) (512792983683/1000000000000 : ℝ) (515762537311/1000000000000 : ℝ) (257881268659/500000000000 : ℝ) (515753988491/1000000000000 : ℝ) (515753988499/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (275/2048 : ℝ))) 3 (515762537311/1000000000000 : ℝ) (257881268659/500000000000 : ℝ) (515753988491/1000000000000 : ℝ) (515753988499/1000000000000 : ℝ) (515758262901/1000000000000 : ℝ) (515758262909/1000000000000 : ℝ) (515758262883/1000000000000 : ℝ) (515758262891/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (275/2048 : ℝ))) 4 (515758262901/1000000000000 : ℝ) (515758262909/1000000000000 : ℝ) (515758262883/1000000000000 : ℝ) (515758262891/1000000000000 : ℝ) (128939565723/250000000000 : ℝ) (5157582629/10000000000 : ℝ) (515758262891/1000000000000 : ℝ) (5157582629/10000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (275/2048 : ℝ))) 5 (128939565723/250000000000 : ℝ) (5157582629/10000000000 : ℝ) (515758262891/1000000000000 : ℝ) (5157582629/10000000000 : ℝ) (515758262891/1000000000000 : ℝ) (5157582629/10000000000 : ℝ) (515758262891/1000000000000 : ℝ) (5157582629/10000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (275/2048 : ℝ))) 6 (515758262891/1000000000000 : ℝ) (5157582629/10000000000 : ℝ) (515758262891/1000000000000 : ℝ) (5157582629/10000000000 : ℝ) (515758262891/1000000000000 : ℝ) (5157582629/10000000000 : ℝ) (515758262891/1000000000000 : ℝ) (5157582629/10000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (275/2048 : ℝ))) 7 (515758262891/1000000000000 : ℝ) (5157582629/10000000000 : ℝ) (515758262891/1000000000000 : ℝ) (5157582629/10000000000 : ℝ) (515758262891/1000000000000 : ℝ) (5157582629/10000000000 : ℝ) (515758262891/1000000000000 : ℝ) (5157582629/10000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (275/2048 : ℝ)) hmem 8 (495238694437/500000000000 : ℝ) (990477388877/1000000000000 : ℝ) (495238694437/500000000000 : ℝ) (990477388877/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (275/2048 : ℝ))) hcmem 8 (515758262891/1000000000000 : ℝ) (5157582629/10000000000 : ℝ) (515758262891/1000000000000 : ℝ) (5157582629/10000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (275/2048 : ℝ)) (495238694437/500000000000 : ℝ) (990477388877/1000000000000 : ℝ) (515758262891/1000000000000 : ℝ) (5157582629/10000000000 : ℝ) (817940110457/1000000000000 : ℝ) (408970055237/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0189_exp_lower
  have heNumeric : (2019028258679/1000000000000 : ℝ)/4 ≤ Real.exp (-10938848408209/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019028258679/1000000000000 : ℝ)/4 ≤ Real.exp ((8799/65536 : ℝ)-(408970055237/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8799/65536 : ℝ) (275/2048 : ℝ) (408970055237/500000000000 : ℝ) (2019028258679/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0190; no trusted numerical premise.
theorem cover7_leaf0190_exp_radius : (498802395456894671/500000000000000000 : ℝ) ≤ Real.exp ((-8801/458752 : ℝ)/8) ∧ Real.exp ((-8801/458752 : ℝ)/8) ≤ (997604790913789343/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8801/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0190_exp_lower : (459045037852905113/500000000000000000 : ℝ) ≤ Real.exp ((-683678171931/1000000000000 : ℝ)/8) ∧ Real.exp ((-683678171931/1000000000000 : ℝ)/8) ≤ (918090075705810227/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-683678171931/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0190_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019027963057/1000000000000 : ℝ) ≤ 4*Real.exp (275/2048 : ℝ)*Real.exp (-mu (radius 7 (8801/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (2019027963057/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8801/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0190_exp_radius
  have hrNumeric : (245249549209/250000000000 : ℝ) ≤ Real.exp (-8801/458752 : ℝ) ∧ Real.exp (-8801/458752 : ℝ) ≤ (980998196837/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (245249549209/250000000000 : ℝ) ≤ (radius 7 (8801/65536 : ℝ)) ∧ (radius 7 (8801/65536 : ℝ)) ≤ (980998196837/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8801/65536 : ℝ)) (245249549209/250000000000 : ℝ) (980998196837/1000000000000 : ℝ) (97008424637/500000000000 : ℝ) (303151327/1562500000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8801/65536 : ℝ)) (245249549209/250000000000 : ℝ) (980998196837/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8801/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (245249549209/250000000000 : ℝ) (980998196837/1000000000000 : ℝ) (495249549209/500000000000 : ℝ) (990499098419/1000000000000 : ℝ) (990453530881/1000000000000 : ℝ) (990453530883/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8801/65536 : ℝ)) 1 (495249549209/500000000000 : ℝ) (990499098419/1000000000000 : ℝ) (990453530881/1000000000000 : ℝ) (990453530883/1000000000000 : ℝ) (990476314649/1000000000000 : ℝ) (990476314651/1000000000000 : ℝ) (990476314387/1000000000000 : ℝ) (990476314389/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8801/65536 : ℝ)) 2 (990476314649/1000000000000 : ℝ) (990476314651/1000000000000 : ℝ) (990476314387/1000000000000 : ℝ) (990476314389/1000000000000 : ℝ) (495238157259/500000000000 : ℝ) (24761907863/25000000000 : ℝ) (990476314517/1000000000000 : ℝ) (24761907863/25000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8801/65536 : ℝ)) 3 (495238157259/500000000000 : ℝ) (24761907863/25000000000 : ℝ) (990476314517/1000000000000 : ℝ) (24761907863/25000000000 : ℝ) (990476314517/1000000000000 : ℝ) (24761907863/25000000000 : ℝ) (990476314517/1000000000000 : ℝ) (24761907863/25000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8801/65536 : ℝ)) 4 (990476314517/1000000000000 : ℝ) (24761907863/25000000000 : ℝ) (990476314517/1000000000000 : ℝ) (24761907863/25000000000 : ℝ) (990476314517/1000000000000 : ℝ) (24761907863/25000000000 : ℝ) (990476314517/1000000000000 : ℝ) (24761907863/25000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8801/65536 : ℝ)) 5 (990476314517/1000000000000 : ℝ) (24761907863/25000000000 : ℝ) (990476314517/1000000000000 : ℝ) (24761907863/25000000000 : ℝ) (990476314517/1000000000000 : ℝ) (24761907863/25000000000 : ℝ) (990476314517/1000000000000 : ℝ) (24761907863/25000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8801/65536 : ℝ)) 6 (990476314517/1000000000000 : ℝ) (24761907863/25000000000 : ℝ) (990476314517/1000000000000 : ℝ) (24761907863/25000000000 : ℝ) (990476314517/1000000000000 : ℝ) (24761907863/25000000000 : ℝ) (990476314517/1000000000000 : ℝ) (24761907863/25000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8801/65536 : ℝ)) 7 (990476314517/1000000000000 : ℝ) (24761907863/25000000000 : ℝ) (990476314517/1000000000000 : ℝ) (24761907863/25000000000 : ℝ) (990476314517/1000000000000 : ℝ) (24761907863/25000000000 : ℝ) (990476314517/1000000000000 : ℝ) (24761907863/25000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8801/65536 : ℝ))) (97008424637/500000000000 : ℝ) (303151327/1562500000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8801/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (97008424637/500000000000 : ℝ) (303151327/1562500000 : ℝ) (597008424637/1000000000000 : ℝ) (1865651327/3125000000 : ℝ) (27529589853/62500000000 : ℝ) (55059179707/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8801/65536 : ℝ))) 1 (597008424637/1000000000000 : ℝ) (1865651327/3125000000 : ℝ) (27529589853/62500000000 : ℝ) (55059179707/125000000000 : ℝ) (259370465571/500000000000 : ℝ) (129685232787/250000000000 : ℝ) (512802450369/1000000000000 : ℝ) (64100306297/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8801/65536 : ℝ))) 2 (259370465571/500000000000 : ℝ) (129685232787/250000000000 : ℝ) (512802450369/1000000000000 : ℝ) (64100306297/125000000000 : ℝ) (103154338151/200000000000 : ℝ) (257885845381/500000000000 : ℝ) (51576314389/100000000000 : ℝ) (257881571949/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8801/65536 : ℝ))) 3 (103154338151/200000000000 : ℝ) (257885845381/500000000000 : ℝ) (51576314389/100000000000 : ℝ) (257881571949/500000000000 : ℝ) (257883708661/500000000000 : ℝ) (51576741733/100000000000 : ℝ) (64470927163/125000000000 : ℝ) (515767417313/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8801/65536 : ℝ))) 4 (257883708661/500000000000 : ℝ) (51576741733/100000000000 : ℝ) (64470927163/125000000000 : ℝ) (515767417313/1000000000000 : ℝ) (515767417313/1000000000000 : ℝ) (257883708661/500000000000 : ℝ) (16117731791/31250000000 : ℝ) (257883708661/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8801/65536 : ℝ))) 5 (515767417313/1000000000000 : ℝ) (257883708661/500000000000 : ℝ) (16117731791/31250000000 : ℝ) (257883708661/500000000000 : ℝ) (16117731791/31250000000 : ℝ) (257883708661/500000000000 : ℝ) (16117731791/31250000000 : ℝ) (257883708661/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8801/65536 : ℝ))) 6 (16117731791/31250000000 : ℝ) (257883708661/500000000000 : ℝ) (16117731791/31250000000 : ℝ) (257883708661/500000000000 : ℝ) (16117731791/31250000000 : ℝ) (257883708661/500000000000 : ℝ) (16117731791/31250000000 : ℝ) (257883708661/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8801/65536 : ℝ))) 7 (16117731791/31250000000 : ℝ) (257883708661/500000000000 : ℝ) (16117731791/31250000000 : ℝ) (257883708661/500000000000 : ℝ) (16117731791/31250000000 : ℝ) (257883708661/500000000000 : ℝ) (16117731791/31250000000 : ℝ) (257883708661/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8801/65536 : ℝ)) hmem 8 (990476314517/1000000000000 : ℝ) (24761907863/25000000000 : ℝ) (990476314517/1000000000000 : ℝ) (24761907863/25000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8801/65536 : ℝ))) hcmem 8 (16117731791/31250000000 : ℝ) (257883708661/500000000000 : ℝ) (16117731791/31250000000 : ℝ) (257883708661/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8801/65536 : ℝ)) (990476314517/1000000000000 : ℝ) (24761907863/25000000000 : ℝ) (16117731791/31250000000 : ℝ) (257883708661/500000000000 : ℝ) (817955515661/1000000000000 : ℝ) (817955515681/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0190_exp_lower
  have heNumeric : (2019027963057/1000000000000 : ℝ)/4 ≤ Real.exp (-683678171931/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019027963057/1000000000000 : ℝ)/4 ≤ Real.exp ((275/2048 : ℝ)-(817955515681/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (275/2048 : ℝ) (8801/65536 : ℝ) (817955515681/1000000000000 : ℝ) (2019027963057/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0191; no trusted numerical premise.
theorem cover7_leaf0191_exp_radius : (997604519088092941/1000000000000000000 : ℝ) ≤ Real.exp ((-4401/229376 : ℝ)/8) ∧ Real.exp ((-4401/229376 : ℝ)/8) ≤ (498802259544046471/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4401/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0191_exp_lower : (45904502951871659/50000000000000000 : ℝ) ≤ Real.exp ((-10938853074799/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938853074799/16000000000000 : ℝ)/8) ≤ (918090059037433181/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938853074799/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0191_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (403805533961/200000000000 : ℝ) ≤ 4*Real.exp (8801/65536 : ℝ)*Real.exp (-mu (radius 7 (4401/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (403805533961/200000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4401/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0191_exp_radius
  have hrNumeric : (15328063413/15625000000 : ℝ) ≤ Real.exp (-4401/229376 : ℝ) ∧ Real.exp (-4401/229376 : ℝ) ≤ (980996058433/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (15328063413/15625000000 : ℝ) ≤ (radius 7 (4401/32768 : ℝ)) ∧ (radius 7 (4401/32768 : ℝ)) ≤ (980996058433/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4401/32768 : ℝ)) (15328063413/15625000000 : ℝ) (980996058433/1000000000000 : ℝ) (24253457659/125000000000 : ℝ) (97013830639/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4401/32768 : ℝ)) (15328063413/15625000000 : ℝ) (980996058433/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4401/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (15328063413/15625000000 : ℝ) (980996058433/1000000000000 : ℝ) (30953063413/31250000000 : ℝ) (990498029217/1000000000000 : ℝ) (990452451373/1000000000000 : ℝ) (7923619611/8000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4401/32768 : ℝ)) 1 (30953063413/31250000000 : ℝ) (990498029217/1000000000000 : ℝ) (990452451373/1000000000000 : ℝ) (7923619611/8000000000 : ℝ) (495237620147/500000000000 : ℝ) (123809405037/125000000000 : ℝ) (30952351251/31250000000 : ℝ) (495237620017/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4401/32768 : ℝ)) 2 (495237620147/500000000000 : ℝ) (123809405037/125000000000 : ℝ) (30952351251/31250000000 : ℝ) (495237620017/500000000000 : ℝ) (990475240163/1000000000000 : ℝ) (198095048033/200000000000 : ℝ) (495237620081/500000000000 : ℝ) (198095048033/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4401/32768 : ℝ)) 3 (990475240163/1000000000000 : ℝ) (198095048033/200000000000 : ℝ) (495237620081/500000000000 : ℝ) (198095048033/200000000000 : ℝ) (495237620081/500000000000 : ℝ) (198095048033/200000000000 : ℝ) (495237620081/500000000000 : ℝ) (198095048033/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4401/32768 : ℝ)) 4 (495237620081/500000000000 : ℝ) (198095048033/200000000000 : ℝ) (495237620081/500000000000 : ℝ) (198095048033/200000000000 : ℝ) (495237620081/500000000000 : ℝ) (198095048033/200000000000 : ℝ) (495237620081/500000000000 : ℝ) (198095048033/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4401/32768 : ℝ)) 5 (495237620081/500000000000 : ℝ) (198095048033/200000000000 : ℝ) (495237620081/500000000000 : ℝ) (198095048033/200000000000 : ℝ) (495237620081/500000000000 : ℝ) (198095048033/200000000000 : ℝ) (495237620081/500000000000 : ℝ) (198095048033/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4401/32768 : ℝ)) 6 (495237620081/500000000000 : ℝ) (198095048033/200000000000 : ℝ) (495237620081/500000000000 : ℝ) (198095048033/200000000000 : ℝ) (495237620081/500000000000 : ℝ) (198095048033/200000000000 : ℝ) (495237620081/500000000000 : ℝ) (198095048033/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4401/32768 : ℝ)) 7 (495237620081/500000000000 : ℝ) (198095048033/200000000000 : ℝ) (495237620081/500000000000 : ℝ) (198095048033/200000000000 : ℝ) (495237620081/500000000000 : ℝ) (198095048033/200000000000 : ℝ) (495237620081/500000000000 : ℝ) (198095048033/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4401/32768 : ℝ))) (24253457659/125000000000 : ℝ) (97013830639/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4401/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (24253457659/125000000000 : ℝ) (97013830639/500000000000 : ℝ) (149253457659/250000000000 : ℝ) (597013830639/1000000000000 : ℝ) (440485710633/1000000000000 : ℝ) (5506071383/12500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4401/32768 : ℝ))) 1 (149253457659/250000000000 : ℝ) (597013830639/1000000000000 : ℝ) (440485710633/1000000000000 : ℝ) (5506071383/12500000000 : ℝ) (259374885317/500000000000 : ℝ) (6484372133/12500000000 : ℝ) (512811916247/1000000000000 : ℝ) (512811916253/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4401/32768 : ℝ))) 2 (259374885317/500000000000 : ℝ) (6484372133/12500000000 : ℝ) (512811916247/1000000000000 : ℝ) (512811916253/1000000000000 : ℝ) (6447260543/12500000000 : ℝ) (515780843447/1000000000000 : ℝ) (51577229853/100000000000 : ℝ) (515772298537/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4401/32768 : ℝ))) 3 (6447260543/12500000000 : ℝ) (515780843447/1000000000000 : ℝ) (51577229853/100000000000 : ℝ) (515772298537/1000000000000 : ℝ) (103155314197/200000000000 : ℝ) (32236035687/62500000000 : ℝ) (515776570967/1000000000000 : ℝ) (20631062839/40000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4401/32768 : ℝ))) 4 (103155314197/200000000000 : ℝ) (32236035687/62500000000 : ℝ) (515776570967/1000000000000 : ℝ) (20631062839/40000000000 : ℝ) (16118017843/31250000000 : ℝ) (64472071373/125000000000 : ℝ) (20631062839/40000000000 : ℝ) (64472071373/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4401/32768 : ℝ))) 5 (16118017843/31250000000 : ℝ) (64472071373/125000000000 : ℝ) (20631062839/40000000000 : ℝ) (64472071373/125000000000 : ℝ) (20631062839/40000000000 : ℝ) (64472071373/125000000000 : ℝ) (20631062839/40000000000 : ℝ) (64472071373/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4401/32768 : ℝ))) 6 (20631062839/40000000000 : ℝ) (64472071373/125000000000 : ℝ) (20631062839/40000000000 : ℝ) (64472071373/125000000000 : ℝ) (20631062839/40000000000 : ℝ) (64472071373/125000000000 : ℝ) (20631062839/40000000000 : ℝ) (64472071373/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4401/32768 : ℝ))) 7 (20631062839/40000000000 : ℝ) (64472071373/125000000000 : ℝ) (20631062839/40000000000 : ℝ) (64472071373/125000000000 : ℝ) (20631062839/40000000000 : ℝ) (64472071373/125000000000 : ℝ) (20631062839/40000000000 : ℝ) (64472071373/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4401/32768 : ℝ)) hmem 8 (495237620081/500000000000 : ℝ) (198095048033/200000000000 : ℝ) (495237620081/500000000000 : ℝ) (198095048033/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4401/32768 : ℝ))) hcmem 8 (20631062839/40000000000 : ℝ) (64472071373/125000000000 : ℝ) (20631062839/40000000000 : ℝ) (64472071373/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4401/32768 : ℝ)) (495237620081/500000000000 : ℝ) (198095048033/200000000000 : ℝ) (20631062839/40000000000 : ℝ) (64472071373/125000000000 : ℝ) (51123182481/62500000000 : ℝ) (408985459857/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0191_exp_lower
  have heNumeric : (403805533961/200000000000 : ℝ)/4 ≤ Real.exp (-10938853074799/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (403805533961/200000000000 : ℝ)/4 ≤ Real.exp ((8801/65536 : ℝ)-(408985459857/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8801/65536 : ℝ) (4401/32768 : ℝ) (408985459857/500000000000 : ℝ) (403805533961/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0192; no trusted numerical premise.
theorem cover7_leaf0192_exp_radius : (997604247262470607/1000000000000000000 : ℝ) ≤ Real.exp ((-8803/458752 : ℝ)/8) ∧ Real.exp ((-8803/458752 : ℝ)/8) ≤ (62350265453904413/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8803/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0192_exp_lower : (229522510625889157/250000000000000000 : ℝ) ≤ Real.exp ((-218777107599/320000000000 : ℝ)/8) ∧ Real.exp ((-218777107599/320000000000 : ℝ)/8) ≤ (918090042503556629/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-218777107599/320000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0192_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (50475684473/25000000000 : ℝ) ≤ 4*Real.exp (4401/32768 : ℝ)*Real.exp (-mu (radius 7 (8803/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (50475684473/25000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8803/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0192_exp_radius
  have hrNumeric : (980993920033/1000000000000 : ℝ) ≤ Real.exp (-8803/458752 : ℝ) ∧ Real.exp (-8803/458752 : ℝ) ≤ (490496960017/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980993920033/1000000000000 : ℝ) ≤ (radius 7 (8803/65536 : ℝ)) ∧ (radius 7 (8803/65536 : ℝ)) ≤ (490496960017/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8803/65536 : ℝ)) (980993920033/1000000000000 : ℝ) (490496960017/500000000000 : ℝ) (194038472619/1000000000000 : ℝ) (1552307781/8000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8803/65536 : ℝ)) (980993920033/1000000000000 : ℝ) (490496960017/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8803/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980993920033/1000000000000 : ℝ) (490496960017/500000000000 : ℝ) (61906060001/62500000000 : ℝ) (990496960017/1000000000000 : ℝ) (495225685933/500000000000 : ℝ) (247612842967/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8803/65536 : ℝ)) 1 (61906060001/62500000000 : ℝ) (990496960017/1000000000000 : ℝ) (495225685933/500000000000 : ℝ) (247612842967/250000000000 : ℝ) (990474165941/1000000000000 : ℝ) (990474165943/1000000000000 : ℝ) (495237082839/500000000000 : ℝ) (990474165681/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8803/65536 : ℝ)) 2 (990474165941/1000000000000 : ℝ) (990474165943/1000000000000 : ℝ) (495237082839/500000000000 : ℝ) (990474165681/1000000000000 : ℝ) (990474165809/1000000000000 : ℝ) (247618541453/250000000000 : ℝ) (990474165809/1000000000000 : ℝ) (247618541453/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8803/65536 : ℝ)) 3 (990474165809/1000000000000 : ℝ) (247618541453/250000000000 : ℝ) (990474165809/1000000000000 : ℝ) (247618541453/250000000000 : ℝ) (990474165809/1000000000000 : ℝ) (247618541453/250000000000 : ℝ) (990474165809/1000000000000 : ℝ) (247618541453/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8803/65536 : ℝ)) 4 (990474165809/1000000000000 : ℝ) (247618541453/250000000000 : ℝ) (990474165809/1000000000000 : ℝ) (247618541453/250000000000 : ℝ) (990474165809/1000000000000 : ℝ) (247618541453/250000000000 : ℝ) (990474165809/1000000000000 : ℝ) (247618541453/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8803/65536 : ℝ)) 5 (990474165809/1000000000000 : ℝ) (247618541453/250000000000 : ℝ) (990474165809/1000000000000 : ℝ) (247618541453/250000000000 : ℝ) (990474165809/1000000000000 : ℝ) (247618541453/250000000000 : ℝ) (990474165809/1000000000000 : ℝ) (247618541453/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8803/65536 : ℝ)) 6 (990474165809/1000000000000 : ℝ) (247618541453/250000000000 : ℝ) (990474165809/1000000000000 : ℝ) (247618541453/250000000000 : ℝ) (990474165809/1000000000000 : ℝ) (247618541453/250000000000 : ℝ) (990474165809/1000000000000 : ℝ) (247618541453/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8803/65536 : ℝ)) 7 (990474165809/1000000000000 : ℝ) (247618541453/250000000000 : ℝ) (990474165809/1000000000000 : ℝ) (247618541453/250000000000 : ℝ) (990474165809/1000000000000 : ℝ) (247618541453/250000000000 : ℝ) (990474165809/1000000000000 : ℝ) (247618541453/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8803/65536 : ℝ))) (194038472619/1000000000000 : ℝ) (1552307781/8000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8803/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (194038472619/1000000000000 : ℝ) (1552307781/8000000000 : ℝ) (597019236309/1000000000000 : ℝ) (597019236313/1000000000000 : ℝ) (55062247817/125000000000 : ℝ) (27531123909/62500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8803/65536 : ℝ))) 1 (597019236309/1000000000000 : ℝ) (597019236313/1000000000000 : ℝ) (55062247817/125000000000 : ℝ) (27531123909/62500000000 : ℝ) (259379304711/500000000000 : ℝ) (518758609429/1000000000000 : ℝ) (51282138131/100000000000 : ℝ) (512821381317/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8803/65536 : ℝ))) 2 (259379304711/500000000000 : ℝ) (518758609429/1000000000000 : ℝ) (51282138131/100000000000 : ℝ) (512821381317/1000000000000 : ℝ) (257894997683/500000000000 : ℝ) (515789995373/1000000000000 : ℝ) (51578145241/100000000000 : ℝ) (257890726209/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8803/65536 : ℝ))) 3 (257894997683/500000000000 : ℝ) (515789995373/1000000000000 : ℝ) (51578145241/100000000000 : ℝ) (257890726209/500000000000 : ℝ) (32236607743/62500000000 : ℝ) (64473215487/125000000000 : ℝ) (51578572387/100000000000 : ℝ) (257892861939/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8803/65536 : ℝ))) 4 (32236607743/62500000000 : ℝ) (64473215487/125000000000 : ℝ) (51578572387/100000000000 : ℝ) (257892861939/500000000000 : ℝ) (515785723879/1000000000000 : ℝ) (515785723887/1000000000000 : ℝ) (257892861939/500000000000 : ℝ) (515785723887/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8803/65536 : ℝ))) 5 (515785723879/1000000000000 : ℝ) (515785723887/1000000000000 : ℝ) (257892861939/500000000000 : ℝ) (515785723887/1000000000000 : ℝ) (257892861939/500000000000 : ℝ) (515785723887/1000000000000 : ℝ) (257892861939/500000000000 : ℝ) (515785723887/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8803/65536 : ℝ))) 6 (257892861939/500000000000 : ℝ) (515785723887/1000000000000 : ℝ) (257892861939/500000000000 : ℝ) (515785723887/1000000000000 : ℝ) (257892861939/500000000000 : ℝ) (515785723887/1000000000000 : ℝ) (257892861939/500000000000 : ℝ) (515785723887/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8803/65536 : ℝ))) 7 (257892861939/500000000000 : ℝ) (515785723887/1000000000000 : ℝ) (257892861939/500000000000 : ℝ) (515785723887/1000000000000 : ℝ) (257892861939/500000000000 : ℝ) (515785723887/1000000000000 : ℝ) (257892861939/500000000000 : ℝ) (515785723887/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8803/65536 : ℝ)) hmem 8 (990474165809/1000000000000 : ℝ) (247618541453/250000000000 : ℝ) (990474165809/1000000000000 : ℝ) (247618541453/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8803/65536 : ℝ))) hcmem 8 (257892861939/500000000000 : ℝ) (515785723887/1000000000000 : ℝ) (257892861939/500000000000 : ℝ) (515785723887/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8803/65536 : ℝ)) (990474165809/1000000000000 : ℝ) (247618541453/250000000000 : ℝ) (257892861939/500000000000 : ℝ) (515785723887/1000000000000 : ℝ) (817986322557/1000000000000 : ℝ) (32719452903/40000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0192_exp_lower
  have heNumeric : (50475684473/25000000000 : ℝ)/4 ≤ Real.exp (-218777107599/320000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (50475684473/25000000000 : ℝ)/4 ≤ Real.exp ((4401/32768 : ℝ)-(32719452903/40000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4401/32768 : ℝ) (8803/65536 : ℝ) (32719452903/40000000000 : ℝ) (50475684473/25000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0193; no trusted numerical premise.
theorem cover7_leaf0193_exp_radius : (49880198771846117/50000000000000000 : ℝ) ≤ Real.exp ((-2201/114688 : ℝ)/8) ∧ Real.exp ((-2201/114688 : ℝ)/8) ≤ (997603975436922341/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2201/114688 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0193_exp_lower : (229522506525872999/250000000000000000 : ℝ) ≤ Real.exp ((-2187771533289/3200000000000 : ℝ)/8) ∧ Real.exp ((-2187771533289/3200000000000 : ℝ)/8) ≤ (918090026103491997/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2187771533289/3200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0193_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019027090389/1000000000000 : ℝ) ≤ 4*Real.exp (8803/65536 : ℝ)*Real.exp (-mu (radius 7 (2201/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (2019027090389/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2201/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0193_exp_radius
  have hrNumeric : (490495890819/500000000000 : ℝ) ≤ Real.exp (-2201/114688 : ℝ) ∧ Real.exp (-2201/114688 : ℝ) ≤ (980991781639/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490495890819/500000000000 : ℝ) ≤ (radius 7 (2201/16384 : ℝ)) ∧ (radius 7 (2201/16384 : ℝ)) ≤ (980991781639/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2201/16384 : ℝ)) (490495890819/500000000000 : ℝ) (980991781639/1000000000000 : ℝ) (194049283319/1000000000000 : ℝ) (7761971333/40000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2201/16384 : ℝ)) (490495890819/500000000000 : ℝ) (980991781639/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2201/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490495890819/500000000000 : ℝ) (980991781639/1000000000000 : ℝ) (990495890819/1000000000000 : ℝ) (49524794541/50000000000 : ℝ) (990450292361/1000000000000 : ℝ) (495225146181/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2201/16384 : ℝ)) 1 (990495890819/1000000000000 : ℝ) (49524794541/50000000000 : ℝ) (990450292361/1000000000000 : ℝ) (495225146181/500000000000 : ℝ) (99047309159/100000000000 : ℝ) (990473091591/1000000000000 : ℝ) (990473091327/1000000000000 : ℝ) (990473091329/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2201/16384 : ℝ)) 2 (99047309159/100000000000 : ℝ) (990473091591/1000000000000 : ℝ) (990473091327/1000000000000 : ℝ) (990473091329/1000000000000 : ℝ) (495236545729/500000000000 : ℝ) (49523654573/50000000000 : ℝ) (495236545729/500000000000 : ℝ) (49523654573/50000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2201/16384 : ℝ)) 3 (495236545729/500000000000 : ℝ) (49523654573/50000000000 : ℝ) (495236545729/500000000000 : ℝ) (49523654573/50000000000 : ℝ) (495236545729/500000000000 : ℝ) (49523654573/50000000000 : ℝ) (495236545729/500000000000 : ℝ) (49523654573/50000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2201/16384 : ℝ)) 4 (495236545729/500000000000 : ℝ) (49523654573/50000000000 : ℝ) (495236545729/500000000000 : ℝ) (49523654573/50000000000 : ℝ) (495236545729/500000000000 : ℝ) (49523654573/50000000000 : ℝ) (495236545729/500000000000 : ℝ) (49523654573/50000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2201/16384 : ℝ)) 5 (495236545729/500000000000 : ℝ) (49523654573/50000000000 : ℝ) (495236545729/500000000000 : ℝ) (49523654573/50000000000 : ℝ) (495236545729/500000000000 : ℝ) (49523654573/50000000000 : ℝ) (495236545729/500000000000 : ℝ) (49523654573/50000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2201/16384 : ℝ)) 6 (495236545729/500000000000 : ℝ) (49523654573/50000000000 : ℝ) (495236545729/500000000000 : ℝ) (49523654573/50000000000 : ℝ) (495236545729/500000000000 : ℝ) (49523654573/50000000000 : ℝ) (495236545729/500000000000 : ℝ) (49523654573/50000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2201/16384 : ℝ)) 7 (495236545729/500000000000 : ℝ) (49523654573/50000000000 : ℝ) (495236545729/500000000000 : ℝ) (49523654573/50000000000 : ℝ) (495236545729/500000000000 : ℝ) (49523654573/50000000000 : ℝ) (495236545729/500000000000 : ℝ) (49523654573/50000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2201/16384 : ℝ))) (194049283319/1000000000000 : ℝ) (7761971333/40000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2201/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (194049283319/1000000000000 : ℝ) (7761971333/40000000000 : ℝ) (597024641659/1000000000000 : ℝ) (597024641663/1000000000000 : ℝ) (110127563341/250000000000 : ℝ) (110127563343/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2201/16384 : ℝ))) 1 (597024641659/1000000000000 : ℝ) (597024641663/1000000000000 : ℝ) (110127563341/250000000000 : ℝ) (110127563343/250000000000 : ℝ) (518767447511/1000000000000 : ℝ) (259383723759/500000000000 : ℝ) (512830845563/1000000000000 : ℝ) (512830845571/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2201/16384 : ℝ))) 2 (518767447511/1000000000000 : ℝ) (259383723759/500000000000 : ℝ) (512830845563/1000000000000 : ℝ) (512830845571/1000000000000 : ℝ) (515799146537/1000000000000 : ℝ) (103159829309/200000000000 : ℝ) (257895302767/500000000000 : ℝ) (257895302771/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2201/16384 : ℝ))) 3 (515799146537/1000000000000 : ℝ) (103159829309/200000000000 : ℝ) (257895302767/500000000000 : ℝ) (257895302771/500000000000 : ℝ) (103158975207/200000000000 : ℝ) (128948719011/250000000000 : ℝ) (515794876017/1000000000000 : ℝ) (257897438013/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2201/16384 : ℝ))) 4 (103158975207/200000000000 : ℝ) (128948719011/250000000000 : ℝ) (515794876017/1000000000000 : ℝ) (257897438013/500000000000 : ℝ) (257897438013/500000000000 : ℝ) (103158975207/200000000000 : ℝ) (20631795041/40000000000 : ℝ) (103158975207/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2201/16384 : ℝ))) 5 (257897438013/500000000000 : ℝ) (103158975207/200000000000 : ℝ) (20631795041/40000000000 : ℝ) (103158975207/200000000000 : ℝ) (20631795041/40000000000 : ℝ) (103158975207/200000000000 : ℝ) (20631795041/40000000000 : ℝ) (103158975207/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2201/16384 : ℝ))) 6 (20631795041/40000000000 : ℝ) (103158975207/200000000000 : ℝ) (20631795041/40000000000 : ℝ) (103158975207/200000000000 : ℝ) (20631795041/40000000000 : ℝ) (103158975207/200000000000 : ℝ) (20631795041/40000000000 : ℝ) (103158975207/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2201/16384 : ℝ))) 7 (20631795041/40000000000 : ℝ) (103158975207/200000000000 : ℝ) (20631795041/40000000000 : ℝ) (103158975207/200000000000 : ℝ) (20631795041/40000000000 : ℝ) (103158975207/200000000000 : ℝ) (20631795041/40000000000 : ℝ) (103158975207/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2201/16384 : ℝ)) hmem 8 (495236545729/500000000000 : ℝ) (49523654573/50000000000 : ℝ) (495236545729/500000000000 : ℝ) (49523654573/50000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2201/16384 : ℝ))) hcmem 8 (20631795041/40000000000 : ℝ) (103158975207/200000000000 : ℝ) (20631795041/40000000000 : ℝ) (103158975207/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2201/16384 : ℝ)) (495236545729/500000000000 : ℝ) (49523654573/50000000000 : ℝ) (20631795041/40000000000 : ℝ) (103158975207/200000000000 : ℝ) (204500431063/250000000000 : ℝ) (81800172427/100000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0193_exp_lower
  have heNumeric : (2019027090389/1000000000000 : ℝ)/4 ≤ Real.exp (-2187771533289/3200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019027090389/1000000000000 : ℝ)/4 ≤ Real.exp ((8803/65536 : ℝ)-(81800172427/100000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8803/65536 : ℝ) (2201/16384 : ℝ) (81800172427/100000000000 : ℝ) (2019027090389/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0194; no trusted numerical premise.
theorem cover7_leaf0194_exp_radius : (997603703611448139/1000000000000000000 : ℝ) ≤ Real.exp ((-8805/458752 : ℝ)/8) ∧ Real.exp ((-8805/458752 : ℝ)/8) ≤ (49880185180572407/50000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8805/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0194_exp_lower : (459045004918963921/500000000000000000 : ℝ) ≤ Real.exp ((-2734714983547/4000000000000 : ℝ)/8) ∧ Real.exp ((-2734714983547/4000000000000 : ℝ)/8) ≤ (918090009837927843/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2734714983547/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0194_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (3943411727/1953125000 : ℝ) ≤ 4*Real.exp (2201/16384 : ℝ)*Real.exp (-mu (radius 7 (8805/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (3943411727/1953125000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8805/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0194_exp_radius
  have hrNumeric : (61311852703/62500000000 : ℝ) ≤ Real.exp (-8805/458752 : ℝ) ∧ Real.exp (-8805/458752 : ℝ) ≤ (980989643249/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (61311852703/62500000000 : ℝ) ≤ (radius 7 (8805/65536 : ℝ)) ∧ (radius 7 (8805/65536 : ℝ)) ≤ (980989643249/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8805/65536 : ℝ)) (61311852703/62500000000 : ℝ) (980989643249/1000000000000 : ℝ) (24257511671/125000000000 : ℝ) (97030046687/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8805/65536 : ℝ)) (61311852703/62500000000 : ℝ) (980989643249/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8805/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (61311852703/62500000000 : ℝ) (980989643249/1000000000000 : ℝ) (123811852703/125000000000 : ℝ) (7923958573/8000000000 : ℝ) (123806151607/125000000000 : ℝ) (990449212857/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8805/65536 : ℝ)) 1 (123811852703/125000000000 : ℝ) (7923958573/8000000000 : ℝ) (123806151607/125000000000 : ℝ) (990449212857/1000000000000 : ℝ) (24761800431/25000000000 : ℝ) (990472017241/1000000000000 : ℝ) (990472016977/1000000000000 : ℝ) (990472016979/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8805/65536 : ℝ)) 2 (24761800431/25000000000 : ℝ) (990472017241/1000000000000 : ℝ) (990472016977/1000000000000 : ℝ) (990472016979/1000000000000 : ℝ) (247618004277/250000000000 : ℝ) (99047201711/100000000000 : ℝ) (247618004277/250000000000 : ℝ) (99047201711/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8805/65536 : ℝ)) 3 (247618004277/250000000000 : ℝ) (99047201711/100000000000 : ℝ) (247618004277/250000000000 : ℝ) (99047201711/100000000000 : ℝ) (247618004277/250000000000 : ℝ) (99047201711/100000000000 : ℝ) (247618004277/250000000000 : ℝ) (99047201711/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8805/65536 : ℝ)) 4 (247618004277/250000000000 : ℝ) (99047201711/100000000000 : ℝ) (247618004277/250000000000 : ℝ) (99047201711/100000000000 : ℝ) (247618004277/250000000000 : ℝ) (99047201711/100000000000 : ℝ) (247618004277/250000000000 : ℝ) (99047201711/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8805/65536 : ℝ)) 5 (247618004277/250000000000 : ℝ) (99047201711/100000000000 : ℝ) (247618004277/250000000000 : ℝ) (99047201711/100000000000 : ℝ) (247618004277/250000000000 : ℝ) (99047201711/100000000000 : ℝ) (247618004277/250000000000 : ℝ) (99047201711/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8805/65536 : ℝ)) 6 (247618004277/250000000000 : ℝ) (99047201711/100000000000 : ℝ) (247618004277/250000000000 : ℝ) (99047201711/100000000000 : ℝ) (247618004277/250000000000 : ℝ) (99047201711/100000000000 : ℝ) (247618004277/250000000000 : ℝ) (99047201711/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8805/65536 : ℝ)) 7 (247618004277/250000000000 : ℝ) (99047201711/100000000000 : ℝ) (247618004277/250000000000 : ℝ) (99047201711/100000000000 : ℝ) (247618004277/250000000000 : ℝ) (99047201711/100000000000 : ℝ) (247618004277/250000000000 : ℝ) (99047201711/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8805/65536 : ℝ))) (24257511671/125000000000 : ℝ) (97030046687/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8805/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (24257511671/125000000000 : ℝ) (97030046687/500000000000 : ℝ) (149257511671/250000000000 : ℝ) (597030046687/1000000000000 : ℝ) (44052252311/100000000000 : ℝ) (220261261559/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8805/65536 : ℝ))) 1 (149257511671/250000000000 : ℝ) (597030046687/1000000000000 : ℝ) (44052252311/100000000000 : ℝ) (220261261559/500000000000 : ℝ) (518776284897/1000000000000 : ℝ) (518776284903/1000000000000 : ℝ) (256420154501/500000000000 : ℝ) (512840309009/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8805/65536 : ℝ))) 2 (518776284897/1000000000000 : ℝ) (518776284903/1000000000000 : ℝ) (256420154501/500000000000 : ℝ) (512840309009/1000000000000 : ℝ) (515808296949/1000000000000 : ℝ) (128952074239/250000000000 : ℝ) (515799757899/1000000000000 : ℝ) (515799757907/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8805/65536 : ℝ))) 3 (515808296949/1000000000000 : ℝ) (128952074239/250000000000 : ℝ) (515799757899/1000000000000 : ℝ) (515799757907/1000000000000 : ℝ) (16118875857/31250000000 : ℝ) (64475503429/125000000000 : ℝ) (257902013703/500000000000 : ℝ) (257902013707/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8805/65536 : ℝ))) 4 (16118875857/31250000000 : ℝ) (64475503429/125000000000 : ℝ) (257902013703/500000000000 : ℝ) (257902013707/500000000000 : ℝ) (103160805483/200000000000 : ℝ) (515804027423/1000000000000 : ℝ) (257902013707/500000000000 : ℝ) (515804027423/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8805/65536 : ℝ))) 5 (103160805483/200000000000 : ℝ) (515804027423/1000000000000 : ℝ) (257902013707/500000000000 : ℝ) (515804027423/1000000000000 : ℝ) (257902013707/500000000000 : ℝ) (515804027423/1000000000000 : ℝ) (257902013707/500000000000 : ℝ) (515804027423/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8805/65536 : ℝ))) 6 (257902013707/500000000000 : ℝ) (515804027423/1000000000000 : ℝ) (257902013707/500000000000 : ℝ) (515804027423/1000000000000 : ℝ) (257902013707/500000000000 : ℝ) (515804027423/1000000000000 : ℝ) (257902013707/500000000000 : ℝ) (515804027423/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8805/65536 : ℝ))) 7 (257902013707/500000000000 : ℝ) (515804027423/1000000000000 : ℝ) (257902013707/500000000000 : ℝ) (515804027423/1000000000000 : ℝ) (257902013707/500000000000 : ℝ) (515804027423/1000000000000 : ℝ) (257902013707/500000000000 : ℝ) (515804027423/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8805/65536 : ℝ)) hmem 8 (247618004277/250000000000 : ℝ) (99047201711/100000000000 : ℝ) (247618004277/250000000000 : ℝ) (99047201711/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8805/65536 : ℝ))) hcmem 8 (257902013707/500000000000 : ℝ) (515804027423/1000000000000 : ℝ) (257902013707/500000000000 : ℝ) (515804027423/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8805/65536 : ℝ)) (247618004277/250000000000 : ℝ) (99047201711/100000000000 : ℝ) (257902013707/500000000000 : ℝ) (515804027423/1000000000000 : ℝ) (102252140597/125000000000 : ℝ) (818017124793/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0194_exp_lower
  have heNumeric : (3943411727/1953125000 : ℝ)/4 ≤ Real.exp (-2734714983547/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (3943411727/1953125000 : ℝ)/4 ≤ Real.exp ((2201/16384 : ℝ)-(818017124793/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2201/16384 : ℝ) (8805/65536 : ℝ) (818017124793/1000000000000 : ℝ) (3943411727/1953125000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0195; no trusted numerical premise.
theorem cover7_leaf0195_exp_radius : (199520686357209601/200000000000000000 : ℝ) ≤ Real.exp ((-629/32768 : ℝ)/8) ∧ Real.exp ((-629/32768 : ℝ)/8) ≤ (498801715893024003/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-629/32768 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0195_exp_lower : (918089993705946071/1000000000000000000 : ℝ) ≤ Real.exp ((-10938862183307/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938862183307/16000000000000 : ℝ)/8) ≤ (114761249213243259/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938862183307/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0195_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (201902652041/100000000000 : ℝ) ≤ 4*Real.exp (8805/65536 : ℝ)*Real.exp (-mu (radius 7 (4403/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (201902652041/100000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4403/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0195_exp_radius
  have hrNumeric : (490493752431/500000000000 : ℝ) ≤ Real.exp (-629/32768 : ℝ) ∧ Real.exp (-629/32768 : ℝ) ≤ (980987504863/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490493752431/500000000000 : ℝ) ≤ (radius 7 (4403/32768 : ℝ)) ∧ (radius 7 (4403/32768 : ℝ)) ≤ (980987504863/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4403/32768 : ℝ)) (490493752431/500000000000 : ℝ) (980987504863/1000000000000 : ℝ) (194070902771/1000000000000 : ℝ) (194070902777/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4403/32768 : ℝ)) (490493752431/500000000000 : ℝ) (980987504863/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4403/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490493752431/500000000000 : ℝ) (980987504863/1000000000000 : ℝ) (990493752431/1000000000000 : ℝ) (61905859527/62500000000 : ℝ) (123806016669/125000000000 : ℝ) (495224066677/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4403/32768 : ℝ)) 1 (990493752431/1000000000000 : ℝ) (61905859527/62500000000 : ℝ) (123806016669/125000000000 : ℝ) (495224066677/500000000000 : ℝ) (990470942891/1000000000000 : ℝ) (990470942893/1000000000000 : ℝ) (247617735657/250000000000 : ℝ) (990470942631/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4403/32768 : ℝ)) 2 (990470942891/1000000000000 : ℝ) (990470942893/1000000000000 : ℝ) (247617735657/250000000000 : ℝ) (990470942631/1000000000000 : ℝ) (990470942759/1000000000000 : ℝ) (495235471381/500000000000 : ℝ) (990470942759/1000000000000 : ℝ) (495235471381/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4403/32768 : ℝ)) 3 (990470942759/1000000000000 : ℝ) (495235471381/500000000000 : ℝ) (990470942759/1000000000000 : ℝ) (495235471381/500000000000 : ℝ) (990470942759/1000000000000 : ℝ) (495235471381/500000000000 : ℝ) (990470942759/1000000000000 : ℝ) (495235471381/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4403/32768 : ℝ)) 4 (990470942759/1000000000000 : ℝ) (495235471381/500000000000 : ℝ) (990470942759/1000000000000 : ℝ) (495235471381/500000000000 : ℝ) (990470942759/1000000000000 : ℝ) (495235471381/500000000000 : ℝ) (990470942759/1000000000000 : ℝ) (495235471381/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4403/32768 : ℝ)) 5 (990470942759/1000000000000 : ℝ) (495235471381/500000000000 : ℝ) (990470942759/1000000000000 : ℝ) (495235471381/500000000000 : ℝ) (990470942759/1000000000000 : ℝ) (495235471381/500000000000 : ℝ) (990470942759/1000000000000 : ℝ) (495235471381/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4403/32768 : ℝ)) 6 (990470942759/1000000000000 : ℝ) (495235471381/500000000000 : ℝ) (990470942759/1000000000000 : ℝ) (495235471381/500000000000 : ℝ) (990470942759/1000000000000 : ℝ) (495235471381/500000000000 : ℝ) (990470942759/1000000000000 : ℝ) (495235471381/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4403/32768 : ℝ)) 7 (990470942759/1000000000000 : ℝ) (495235471381/500000000000 : ℝ) (990470942759/1000000000000 : ℝ) (495235471381/500000000000 : ℝ) (990470942759/1000000000000 : ℝ) (495235471381/500000000000 : ℝ) (990470942759/1000000000000 : ℝ) (495235471381/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4403/32768 : ℝ))) (194070902771/1000000000000 : ℝ) (194070902777/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4403/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (194070902771/1000000000000 : ℝ) (194070902777/1000000000000 : ℝ) (119407090277/200000000000 : ℝ) (597035451389/1000000000000 : ℝ) (220267395891/500000000000 : ℝ) (44053479179/100000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4403/32768 : ℝ))) 1 (119407090277/200000000000 : ℝ) (597035451389/1000000000000 : ℝ) (220267395891/500000000000 : ℝ) (44053479179/100000000000 : ℝ) (518785121583/1000000000000 : ℝ) (51878512159/100000000000 : ℝ) (512849771631/1000000000000 : ℝ) (256424885819/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4403/32768 : ℝ))) 2 (518785121583/1000000000000 : ℝ) (51878512159/100000000000 : ℝ) (512849771631/1000000000000 : ℝ) (256424885819/500000000000 : ℝ) (515817446607/1000000000000 : ℝ) (257908723307/500000000000 : ℝ) (515808909509/1000000000000 : ℝ) (515808909517/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4403/32768 : ℝ))) 3 (515817446607/1000000000000 : ℝ) (257908723307/500000000000 : ℝ) (515808909509/1000000000000 : ℝ) (515808909517/1000000000000 : ℝ) (257906589029/500000000000 : ℝ) (257906589033/500000000000 : ℝ) (12895329451/25000000000 : ℝ) (8059580907/15625000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4403/32768 : ℝ))) 4 (257906589029/500000000000 : ℝ) (257906589033/500000000000 : ℝ) (12895329451/25000000000 : ℝ) (8059580907/15625000000 : ℝ) (515813178049/1000000000000 : ℝ) (515813178057/1000000000000 : ℝ) (8059580907/15625000000 : ℝ) (515813178057/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4403/32768 : ℝ))) 5 (515813178049/1000000000000 : ℝ) (515813178057/1000000000000 : ℝ) (8059580907/15625000000 : ℝ) (515813178057/1000000000000 : ℝ) (8059580907/15625000000 : ℝ) (515813178057/1000000000000 : ℝ) (8059580907/15625000000 : ℝ) (515813178057/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4403/32768 : ℝ))) 6 (8059580907/15625000000 : ℝ) (515813178057/1000000000000 : ℝ) (8059580907/15625000000 : ℝ) (515813178057/1000000000000 : ℝ) (8059580907/15625000000 : ℝ) (515813178057/1000000000000 : ℝ) (8059580907/15625000000 : ℝ) (515813178057/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4403/32768 : ℝ))) 7 (8059580907/15625000000 : ℝ) (515813178057/1000000000000 : ℝ) (8059580907/15625000000 : ℝ) (515813178057/1000000000000 : ℝ) (8059580907/15625000000 : ℝ) (515813178057/1000000000000 : ℝ) (8059580907/15625000000 : ℝ) (515813178057/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4403/32768 : ℝ)) hmem 8 (990470942759/1000000000000 : ℝ) (495235471381/500000000000 : ℝ) (990470942759/1000000000000 : ℝ) (495235471381/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4403/32768 : ℝ))) hcmem 8 (8059580907/15625000000 : ℝ) (515813178057/1000000000000 : ℝ) (8059580907/15625000000 : ℝ) (515813178057/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4403/32768 : ℝ)) (990470942759/1000000000000 : ℝ) (495235471381/500000000000 : ℝ) (8059580907/15625000000 : ℝ) (515813178057/1000000000000 : ℝ) (163606504827/200000000000 : ℝ) (102254065519/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0195_exp_lower
  have heNumeric : (201902652041/100000000000 : ℝ)/4 ≤ Real.exp (-10938862183307/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (201902652041/100000000000 : ℝ)/4 ≤ Real.exp ((8805/65536 : ℝ)-(102254065519/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8805/65536 : ℝ) (4403/32768 : ℝ) (102254065519/125000000000 : ℝ) (201902652041/100000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0196; no trusted numerical premise.
theorem cover7_leaf0196_exp_radius : (997603159960721937/1000000000000000000 : ℝ) ≤ Real.exp ((-8807/458752 : ℝ)/8) ∧ Real.exp ((-8807/458752 : ℝ)/8) ≤ (498801579980360969/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8807/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0196_exp_lower : (229522494427259643/250000000000000000 : ℝ) ≤ Real.exp ((-5469432206797/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469432206797/8000000000000 : ℝ)/8) ≤ (918089977709038573/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469432206797/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0196_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (504756559743/250000000000 : ℝ) ≤ 4*Real.exp (4403/32768 : ℝ)*Real.exp (-mu (radius 7 (8807/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (504756559743/250000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8807/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0196_exp_radius
  have hrNumeric : (490492683241/500000000000 : ℝ) ≤ Real.exp (-8807/458752 : ℝ) ∧ Real.exp (-8807/458752 : ℝ) ≤ (980985366483/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490492683241/500000000000 : ℝ) ≤ (radius 7 (8807/65536 : ℝ)) ∧ (radius 7 (8807/65536 : ℝ)) ≤ (980985366483/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8807/65536 : ℝ)) (490492683241/500000000000 : ℝ) (980985366483/1000000000000 : ℝ) (194081711519/1000000000000 : ℝ) (7763268461/40000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8807/65536 : ℝ)) (490492683241/500000000000 : ℝ) (980985366483/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8807/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490492683241/500000000000 : ℝ) (980985366483/1000000000000 : ℝ) (990492683241/1000000000000 : ℝ) (495246341621/500000000000 : ℝ) (19808941077/20000000000 : ℝ) (247611763463/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8807/65536 : ℝ)) 1 (990492683241/1000000000000 : ℝ) (495246341621/500000000000 : ℝ) (19808941077/20000000000 : ℝ) (247611763463/250000000000 : ℝ) (198093973709/200000000000 : ℝ) (990469868547/1000000000000 : ℝ) (495234934141/500000000000 : ℝ) (198093973657/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8807/65536 : ℝ)) 2 (198093973709/200000000000 : ℝ) (990469868547/1000000000000 : ℝ) (495234934141/500000000000 : ℝ) (198093973657/200000000000 : ℝ) (990469868413/1000000000000 : ℝ) (7738045847/7812500000 : ℝ) (990469868413/1000000000000 : ℝ) (7738045847/7812500000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8807/65536 : ℝ)) 3 (990469868413/1000000000000 : ℝ) (7738045847/7812500000 : ℝ) (990469868413/1000000000000 : ℝ) (7738045847/7812500000 : ℝ) (990469868413/1000000000000 : ℝ) (7738045847/7812500000 : ℝ) (990469868413/1000000000000 : ℝ) (7738045847/7812500000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8807/65536 : ℝ)) 4 (990469868413/1000000000000 : ℝ) (7738045847/7812500000 : ℝ) (990469868413/1000000000000 : ℝ) (7738045847/7812500000 : ℝ) (990469868413/1000000000000 : ℝ) (7738045847/7812500000 : ℝ) (990469868413/1000000000000 : ℝ) (7738045847/7812500000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8807/65536 : ℝ)) 5 (990469868413/1000000000000 : ℝ) (7738045847/7812500000 : ℝ) (990469868413/1000000000000 : ℝ) (7738045847/7812500000 : ℝ) (990469868413/1000000000000 : ℝ) (7738045847/7812500000 : ℝ) (990469868413/1000000000000 : ℝ) (7738045847/7812500000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8807/65536 : ℝ)) 6 (990469868413/1000000000000 : ℝ) (7738045847/7812500000 : ℝ) (990469868413/1000000000000 : ℝ) (7738045847/7812500000 : ℝ) (990469868413/1000000000000 : ℝ) (7738045847/7812500000 : ℝ) (990469868413/1000000000000 : ℝ) (7738045847/7812500000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8807/65536 : ℝ)) 7 (990469868413/1000000000000 : ℝ) (7738045847/7812500000 : ℝ) (990469868413/1000000000000 : ℝ) (7738045847/7812500000 : ℝ) (990469868413/1000000000000 : ℝ) (7738045847/7812500000 : ℝ) (990469868413/1000000000000 : ℝ) (7738045847/7812500000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8807/65536 : ℝ))) (194081711519/1000000000000 : ℝ) (7763268461/40000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8807/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (194081711519/1000000000000 : ℝ) (7763268461/40000000000 : ℝ) (597040855759/1000000000000 : ℝ) (597040855763/1000000000000 : ℝ) (440547059369/1000000000000 : ℝ) (440547059377/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8807/65536 : ℝ))) 1 (597040855759/1000000000000 : ℝ) (597040855763/1000000000000 : ℝ) (440547059369/1000000000000 : ℝ) (440547059377/1000000000000 : ℝ) (129698489391/250000000000 : ℝ) (51879395757/100000000000 : ℝ) (512859233443/1000000000000 : ℝ) (10257184669/20000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8807/65536 : ℝ))) 2 (129698489391/250000000000 : ℝ) (51879395757/100000000000 : ℝ) (512859233443/1000000000000 : ℝ) (10257184669/20000000000 : ℝ) (515826595503/1000000000000 : ℝ) (51582659551/100000000000 : ℝ) (515818060357/1000000000000 : ℝ) (103163612073/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8807/65536 : ℝ))) 3 (515826595503/1000000000000 : ℝ) (51582659551/100000000000 : ℝ) (515818060357/1000000000000 : ℝ) (103163612073/200000000000 : ℝ) (51582232793/100000000000 : ℝ) (257911163969/500000000000 : ℝ) (64477790989/125000000000 : ℝ) (6447779099/12500000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8807/65536 : ℝ))) 4 (51582232793/100000000000 : ℝ) (257911163969/500000000000 : ℝ) (64477790989/125000000000 : ℝ) (6447779099/12500000000 : ℝ) (515822327921/1000000000000 : ℝ) (515822327929/1000000000000 : ℝ) (6447779099/12500000000 : ℝ) (515822327929/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8807/65536 : ℝ))) 5 (515822327921/1000000000000 : ℝ) (515822327929/1000000000000 : ℝ) (6447779099/12500000000 : ℝ) (515822327929/1000000000000 : ℝ) (6447779099/12500000000 : ℝ) (515822327929/1000000000000 : ℝ) (6447779099/12500000000 : ℝ) (515822327929/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8807/65536 : ℝ))) 6 (6447779099/12500000000 : ℝ) (515822327929/1000000000000 : ℝ) (6447779099/12500000000 : ℝ) (515822327929/1000000000000 : ℝ) (6447779099/12500000000 : ℝ) (515822327929/1000000000000 : ℝ) (6447779099/12500000000 : ℝ) (515822327929/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8807/65536 : ℝ))) 7 (6447779099/12500000000 : ℝ) (515822327929/1000000000000 : ℝ) (6447779099/12500000000 : ℝ) (515822327929/1000000000000 : ℝ) (6447779099/12500000000 : ℝ) (515822327929/1000000000000 : ℝ) (6447779099/12500000000 : ℝ) (515822327929/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8807/65536 : ℝ)) hmem 8 (990469868413/1000000000000 : ℝ) (7738045847/7812500000 : ℝ) (990469868413/1000000000000 : ℝ) (7738045847/7812500000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8807/65536 : ℝ))) hcmem 8 (6447779099/12500000000 : ℝ) (515822327929/1000000000000 : ℝ) (6447779099/12500000000 : ℝ) (515822327929/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8807/65536 : ℝ)) (990469868413/1000000000000 : ℝ) (7738045847/7812500000 : ℝ) (6447779099/12500000000 : ℝ) (515822327929/1000000000000 : ℝ) (818047922317/1000000000000 : ℝ) (409023961167/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0196_exp_lower
  have heNumeric : (504756559743/250000000000 : ℝ)/4 ≤ Real.exp (-5469432206797/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (504756559743/250000000000 : ℝ)/4 ≤ Real.exp ((4403/32768 : ℝ)-(409023961167/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4403/32768 : ℝ) (8807/65536 : ℝ) (409023961167/500000000000 : ℝ) (504756559743/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0197; no trusted numerical premise.
theorem cover7_leaf0197_exp_radius : (62350180508466871/62500000000000000 : ℝ) ≤ Real.exp ((-1101/57344 : ℝ)/8) ∧ Real.exp ((-1101/57344 : ℝ)/8) ≤ (997602888135469937/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1101/57344 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0197_exp_lower : (229522490461514431/250000000000000000 : ℝ) ≤ Real.exp ((-10938866625209/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938866625209/16000000000000 : ℝ)/8) ≤ (36723598473842309/40000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938866625209/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0197_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (201902595989/100000000000 : ℝ) ≤ 4*Real.exp (8807/65536 : ℝ)*Real.exp (-mu (radius 7 (1101/8192 : ℝ))) ∧ (2019/1000 : ℝ) < (201902595989/100000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (1101/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0197_exp_radius
  have hrNumeric : (490491614053/500000000000 : ℝ) ≤ Real.exp (-1101/57344 : ℝ) ∧ Real.exp (-1101/57344 : ℝ) ≤ (980983228107/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490491614053/500000000000 : ℝ) ≤ (radius 7 (1101/8192 : ℝ)) ∧ (radius 7 (1101/8192 : ℝ)) ≤ (980983228107/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (1101/8192 : ℝ)) (490491614053/500000000000 : ℝ) (980983228107/1000000000000 : ℝ) (9704625981/50000000000 : ℝ) (97046259813/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (1101/8192 : ℝ)) (490491614053/500000000000 : ℝ) (980983228107/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (1101/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490491614053/500000000000 : ℝ) (980983228107/1000000000000 : ℝ) (990491614053/1000000000000 : ℝ) (495245807027/500000000000 : ℝ) (990445974349/1000000000000 : ℝ) (990445974351/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (1101/8192 : ℝ)) 1 (990491614053/1000000000000 : ℝ) (495245807027/500000000000 : ℝ) (990445974349/1000000000000 : ℝ) (990445974351/1000000000000 : ℝ) (990468794201/1000000000000 : ℝ) (990468794203/1000000000000 : ℝ) (495234396969/500000000000 : ℝ) (49523439697/50000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (1101/8192 : ℝ)) 2 (990468794201/1000000000000 : ℝ) (990468794203/1000000000000 : ℝ) (495234396969/500000000000 : ℝ) (49523439697/50000000000 : ℝ) (990468794069/1000000000000 : ℝ) (123808599259/125000000000 : ℝ) (990468794069/1000000000000 : ℝ) (123808599259/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (1101/8192 : ℝ)) 3 (990468794069/1000000000000 : ℝ) (123808599259/125000000000 : ℝ) (990468794069/1000000000000 : ℝ) (123808599259/125000000000 : ℝ) (990468794069/1000000000000 : ℝ) (123808599259/125000000000 : ℝ) (990468794069/1000000000000 : ℝ) (123808599259/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (1101/8192 : ℝ)) 4 (990468794069/1000000000000 : ℝ) (123808599259/125000000000 : ℝ) (990468794069/1000000000000 : ℝ) (123808599259/125000000000 : ℝ) (990468794069/1000000000000 : ℝ) (123808599259/125000000000 : ℝ) (990468794069/1000000000000 : ℝ) (123808599259/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (1101/8192 : ℝ)) 5 (990468794069/1000000000000 : ℝ) (123808599259/125000000000 : ℝ) (990468794069/1000000000000 : ℝ) (123808599259/125000000000 : ℝ) (990468794069/1000000000000 : ℝ) (123808599259/125000000000 : ℝ) (990468794069/1000000000000 : ℝ) (123808599259/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (1101/8192 : ℝ)) 6 (990468794069/1000000000000 : ℝ) (123808599259/125000000000 : ℝ) (990468794069/1000000000000 : ℝ) (123808599259/125000000000 : ℝ) (990468794069/1000000000000 : ℝ) (123808599259/125000000000 : ℝ) (990468794069/1000000000000 : ℝ) (123808599259/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (1101/8192 : ℝ)) 7 (990468794069/1000000000000 : ℝ) (123808599259/125000000000 : ℝ) (990468794069/1000000000000 : ℝ) (123808599259/125000000000 : ℝ) (990468794069/1000000000000 : ℝ) (123808599259/125000000000 : ℝ) (990468794069/1000000000000 : ℝ) (123808599259/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (1101/8192 : ℝ))) (9704625981/50000000000 : ℝ) (97046259813/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (1101/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (9704625981/50000000000 : ℝ) (97046259813/500000000000 : ℝ) (59704625981/100000000000 : ℝ) (597046259813/1000000000000 : ℝ) (11013983147/25000000000 : ℝ) (440559325887/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (1101/8192 : ℝ))) 1 (59704625981/100000000000 : ℝ) (597046259813/1000000000000 : ℝ) (11013983147/25000000000 : ℝ) (440559325887/1000000000000 : ℝ) (103760558569/200000000000 : ℝ) (10376055857/20000000000 : ℝ) (128217173611/250000000000 : ℝ) (10257373889/20000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (1101/8192 : ℝ))) 2 (103760558569/200000000000 : ℝ) (10376055857/20000000000 : ℝ) (128217173611/250000000000 : ℝ) (10257373889/20000000000 : ℝ) (128958935911/250000000000 : ℝ) (10316714873/20000000000 : ℝ) (515827210449/1000000000000 : ℝ) (64478401307/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (1101/8192 : ℝ))) 3 (128958935911/250000000000 : ℝ) (10316714873/20000000000 : ℝ) (515827210449/1000000000000 : ℝ) (64478401307/125000000000 : ℝ) (257915738523/500000000000 : ℝ) (515831477053/1000000000000 : ℝ) (128957869257/250000000000 : ℝ) (128957869259/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (1101/8192 : ℝ))) 4 (257915738523/500000000000 : ℝ) (515831477053/1000000000000 : ℝ) (128957869257/250000000000 : ℝ) (128957869259/250000000000 : ℝ) (515831477037/1000000000000 : ℝ) (103166295409/200000000000 : ℝ) (128957869259/250000000000 : ℝ) (103166295409/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (1101/8192 : ℝ))) 5 (515831477037/1000000000000 : ℝ) (103166295409/200000000000 : ℝ) (128957869259/250000000000 : ℝ) (103166295409/200000000000 : ℝ) (128957869259/250000000000 : ℝ) (103166295409/200000000000 : ℝ) (128957869259/250000000000 : ℝ) (103166295409/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (1101/8192 : ℝ))) 6 (128957869259/250000000000 : ℝ) (103166295409/200000000000 : ℝ) (128957869259/250000000000 : ℝ) (103166295409/200000000000 : ℝ) (128957869259/250000000000 : ℝ) (103166295409/200000000000 : ℝ) (128957869259/250000000000 : ℝ) (103166295409/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (1101/8192 : ℝ))) 7 (128957869259/250000000000 : ℝ) (103166295409/200000000000 : ℝ) (128957869259/250000000000 : ℝ) (103166295409/200000000000 : ℝ) (128957869259/250000000000 : ℝ) (103166295409/200000000000 : ℝ) (128957869259/250000000000 : ℝ) (103166295409/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (1101/8192 : ℝ)) hmem 8 (990468794069/1000000000000 : ℝ) (123808599259/125000000000 : ℝ) (990468794069/1000000000000 : ℝ) (123808599259/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (1101/8192 : ℝ))) hcmem 8 (128957869259/250000000000 : ℝ) (103166295409/200000000000 : ℝ) (128957869259/250000000000 : ℝ) (103166295409/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (1101/8192 : ℝ)) (990468794069/1000000000000 : ℝ) (123808599259/125000000000 : ℝ) (128957869259/250000000000 : ℝ) (103166295409/200000000000 : ℝ) (204515829833/250000000000 : ℝ) (818063319349/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0197_exp_lower
  have heNumeric : (201902595989/100000000000 : ℝ)/4 ≤ Real.exp (-10938866625209/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (201902595989/100000000000 : ℝ)/4 ≤ Real.exp ((8807/65536 : ℝ)-(818063319349/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8807/65536 : ℝ) (1101/8192 : ℝ) (818063319349/1000000000000 : ℝ) (201902595989/100000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0198; no trusted numerical premise.
theorem cover7_leaf0198_exp_radius : (498801308155146001/500000000000000000 : ℝ) ≤ Real.exp ((-8809/458752 : ℝ)/8) ∧ Real.exp ((-8809/458752 : ℝ)/8) ≤ (997602616310292003/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8809/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0198_exp_lower : (183617989223285943/200000000000000000 : ℝ) ≤ Real.exp ((-1367358602279/2000000000000 : ℝ)/8) ∧ Real.exp ((-1367358602279/2000000000000 : ℝ)/8) ≤ (229522486529107429/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1367358602279/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0198_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (403805136631/200000000000 : ℝ) ≤ 4*Real.exp (1101/8192 : ℝ)*Real.exp (-mu (radius 7 (8809/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (403805136631/200000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8809/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0198_exp_radius
  have hrNumeric : (490490544867/500000000000 : ℝ) ≤ Real.exp (-8809/458752 : ℝ) ∧ Real.exp (-8809/458752 : ℝ) ≤ (196196217947/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490490544867/500000000000 : ℝ) ≤ (radius 7 (8809/65536 : ℝ)) ∧ (radius 7 (8809/65536 : ℝ)) ≤ (196196217947/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8809/65536 : ℝ)) (490490544867/500000000000 : ℝ) (196196217947/200000000000 : ℝ) (48525831769/250000000000 : ℝ) (97051663541/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8809/65536 : ℝ)) (490490544867/500000000000 : ℝ) (196196217947/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8809/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490490544867/500000000000 : ℝ) (196196217947/200000000000 : ℝ) (990490544867/1000000000000 : ℝ) (247622636217/250000000000 : ℝ) (990444894849/1000000000000 : ℝ) (990444894851/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8809/65536 : ℝ)) 1 (990490544867/1000000000000 : ℝ) (247622636217/250000000000 : ℝ) (990444894849/1000000000000 : ℝ) (990444894851/1000000000000 : ℝ) (495233859929/500000000000 : ℝ) (49523385993/50000000000 : ℝ) (198093543919/200000000000 : ℝ) (990467719597/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8809/65536 : ℝ)) 2 (495233859929/500000000000 : ℝ) (49523385993/50000000000 : ℝ) (198093543919/200000000000 : ℝ) (990467719597/1000000000000 : ℝ) (495233859863/500000000000 : ℝ) (990467719729/1000000000000 : ℝ) (495233859863/500000000000 : ℝ) (990467719729/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8809/65536 : ℝ)) 3 (495233859863/500000000000 : ℝ) (990467719729/1000000000000 : ℝ) (495233859863/500000000000 : ℝ) (990467719729/1000000000000 : ℝ) (495233859863/500000000000 : ℝ) (990467719729/1000000000000 : ℝ) (495233859863/500000000000 : ℝ) (990467719729/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8809/65536 : ℝ)) 4 (495233859863/500000000000 : ℝ) (990467719729/1000000000000 : ℝ) (495233859863/500000000000 : ℝ) (990467719729/1000000000000 : ℝ) (495233859863/500000000000 : ℝ) (990467719729/1000000000000 : ℝ) (495233859863/500000000000 : ℝ) (990467719729/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8809/65536 : ℝ)) 5 (495233859863/500000000000 : ℝ) (990467719729/1000000000000 : ℝ) (495233859863/500000000000 : ℝ) (990467719729/1000000000000 : ℝ) (495233859863/500000000000 : ℝ) (990467719729/1000000000000 : ℝ) (495233859863/500000000000 : ℝ) (990467719729/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8809/65536 : ℝ)) 6 (495233859863/500000000000 : ℝ) (990467719729/1000000000000 : ℝ) (495233859863/500000000000 : ℝ) (990467719729/1000000000000 : ℝ) (495233859863/500000000000 : ℝ) (990467719729/1000000000000 : ℝ) (495233859863/500000000000 : ℝ) (990467719729/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8809/65536 : ℝ)) 7 (495233859863/500000000000 : ℝ) (990467719729/1000000000000 : ℝ) (495233859863/500000000000 : ℝ) (990467719729/1000000000000 : ℝ) (495233859863/500000000000 : ℝ) (990467719729/1000000000000 : ℝ) (495233859863/500000000000 : ℝ) (990467719729/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8809/65536 : ℝ))) (48525831769/250000000000 : ℝ) (97051663541/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8809/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (48525831769/250000000000 : ℝ) (97051663541/500000000000 : ℝ) (298525831769/500000000000 : ℝ) (597051663541/1000000000000 : ℝ) (440571591317/1000000000000 : ℝ) (17622863653/40000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8809/65536 : ℝ))) 1 (298525831769/500000000000 : ℝ) (597051663541/1000000000000 : ℝ) (440571591317/1000000000000 : ℝ) (17622863653/40000000000 : ℝ) (518811627427/1000000000000 : ℝ) (518811627433/1000000000000 : ℝ) (128219538659/250000000000 : ℝ) (512878154643/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8809/65536 : ℝ))) 2 (518811627427/1000000000000 : ℝ) (518811627433/1000000000000 : ℝ) (128219538659/250000000000 : ℝ) (512878154643/1000000000000 : ℝ) (515844891031/1000000000000 : ℝ) (257922445519/500000000000 : ℝ) (515836359787/1000000000000 : ℝ) (257918179897/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8809/65536 : ℝ))) 3 (515844891031/1000000000000 : ℝ) (257922445519/500000000000 : ℝ) (515836359787/1000000000000 : ℝ) (257918179897/500000000000 : ℝ) (515840625409/1000000000000 : ℝ) (64480078177/125000000000 : ℝ) (515840625391/1000000000000 : ℝ) (515840625399/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8809/65536 : ℝ))) 4 (515840625409/1000000000000 : ℝ) (64480078177/125000000000 : ℝ) (515840625391/1000000000000 : ℝ) (515840625399/1000000000000 : ℝ) (2579203127/5000000000 : ℝ) (2015002443/3906250000 : ℝ) (515840625399/1000000000000 : ℝ) (2015002443/3906250000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8809/65536 : ℝ))) 5 (2579203127/5000000000 : ℝ) (2015002443/3906250000 : ℝ) (515840625399/1000000000000 : ℝ) (2015002443/3906250000 : ℝ) (515840625399/1000000000000 : ℝ) (2015002443/3906250000 : ℝ) (515840625399/1000000000000 : ℝ) (2015002443/3906250000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8809/65536 : ℝ))) 6 (515840625399/1000000000000 : ℝ) (2015002443/3906250000 : ℝ) (515840625399/1000000000000 : ℝ) (2015002443/3906250000 : ℝ) (515840625399/1000000000000 : ℝ) (2015002443/3906250000 : ℝ) (515840625399/1000000000000 : ℝ) (2015002443/3906250000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8809/65536 : ℝ))) 7 (515840625399/1000000000000 : ℝ) (2015002443/3906250000 : ℝ) (515840625399/1000000000000 : ℝ) (2015002443/3906250000 : ℝ) (515840625399/1000000000000 : ℝ) (2015002443/3906250000 : ℝ) (515840625399/1000000000000 : ℝ) (2015002443/3906250000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8809/65536 : ℝ)) hmem 8 (495233859863/500000000000 : ℝ) (990467719729/1000000000000 : ℝ) (495233859863/500000000000 : ℝ) (990467719729/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8809/65536 : ℝ))) hcmem 8 (515840625399/1000000000000 : ℝ) (2015002443/3906250000 : ℝ) (515840625399/1000000000000 : ℝ) (2015002443/3906250000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8809/65536 : ℝ)) (495233859863/500000000000 : ℝ) (990467719729/1000000000000 : ℝ) (515840625399/1000000000000 : ℝ) (2015002443/3906250000 : ℝ) (163615743037/200000000000 : ℝ) (409039357601/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0198_exp_lower
  have heNumeric : (403805136631/200000000000 : ℝ)/4 ≤ Real.exp (-1367358602279/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (403805136631/200000000000 : ℝ)/4 ≤ Real.exp ((1101/8192 : ℝ)-(409039357601/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (1101/8192 : ℝ) (8809/65536 : ℝ) (409039357601/500000000000 : ℝ) (403805136631/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0199; no trusted numerical premise.
theorem cover7_leaf0199_exp_radius : (498801172242594067/500000000000000000 : ℝ) ≤ Real.exp ((-4405/229376 : ℝ)/8) ∧ Real.exp ((-4405/229376 : ℝ)/8) ≤ (199520468897037627/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4405/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0199_exp_lower : (183617986104352239/200000000000000000 : ℝ) ≤ Real.exp ((-10938870992439/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938870992439/16000000000000 : ℝ)/8) ≤ (229522482630440299/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938870992439/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0199_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019025408793/1000000000000 : ℝ) ≤ 4*Real.exp (8809/65536 : ℝ)*Real.exp (-mu (radius 7 (4405/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (2019025408793/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4405/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0199_exp_radius
  have hrNumeric : (122622368921/125000000000 : ℝ) ≤ Real.exp (-4405/229376 : ℝ) ∧ Real.exp (-4405/229376 : ℝ) ≤ (980978951369/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (122622368921/125000000000 : ℝ) ≤ (radius 7 (4405/32768 : ℝ)) ∧ (radius 7 (4405/32768 : ℝ)) ≤ (980978951369/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4405/32768 : ℝ)) (122622368921/125000000000 : ℝ) (980978951369/1000000000000 : ℝ) (194114133877/1000000000000 : ℝ) (194114133883/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4405/32768 : ℝ)) (122622368921/125000000000 : ℝ) (980978951369/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4405/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (122622368921/125000000000 : ℝ) (980978951369/1000000000000 : ℝ) (247622368921/250000000000 : ℝ) (198097895137/200000000000 : ℝ) (990443815351/1000000000000 : ℝ) (123805476919/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4405/32768 : ℝ)) 1 (247622368921/250000000000 : ℝ) (198097895137/200000000000 : ℝ) (990443815351/1000000000000 : ℝ) (123805476919/125000000000 : ℝ) (990466645517/1000000000000 : ℝ) (990466645519/1000000000000 : ℝ) (495233322627/500000000000 : ℝ) (123808330657/125000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4405/32768 : ℝ)) 2 (990466645517/1000000000000 : ℝ) (990466645519/1000000000000 : ℝ) (495233322627/500000000000 : ℝ) (123808330657/125000000000 : ℝ) (198093329077/200000000000 : ℝ) (247616661347/250000000000 : ℝ) (198093329077/200000000000 : ℝ) (247616661347/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4405/32768 : ℝ)) 3 (198093329077/200000000000 : ℝ) (247616661347/250000000000 : ℝ) (198093329077/200000000000 : ℝ) (247616661347/250000000000 : ℝ) (198093329077/200000000000 : ℝ) (247616661347/250000000000 : ℝ) (198093329077/200000000000 : ℝ) (247616661347/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4405/32768 : ℝ)) 4 (198093329077/200000000000 : ℝ) (247616661347/250000000000 : ℝ) (198093329077/200000000000 : ℝ) (247616661347/250000000000 : ℝ) (198093329077/200000000000 : ℝ) (247616661347/250000000000 : ℝ) (198093329077/200000000000 : ℝ) (247616661347/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4405/32768 : ℝ)) 5 (198093329077/200000000000 : ℝ) (247616661347/250000000000 : ℝ) (198093329077/200000000000 : ℝ) (247616661347/250000000000 : ℝ) (198093329077/200000000000 : ℝ) (247616661347/250000000000 : ℝ) (198093329077/200000000000 : ℝ) (247616661347/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4405/32768 : ℝ)) 6 (198093329077/200000000000 : ℝ) (247616661347/250000000000 : ℝ) (198093329077/200000000000 : ℝ) (247616661347/250000000000 : ℝ) (198093329077/200000000000 : ℝ) (247616661347/250000000000 : ℝ) (198093329077/200000000000 : ℝ) (247616661347/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4405/32768 : ℝ)) 7 (198093329077/200000000000 : ℝ) (247616661347/250000000000 : ℝ) (198093329077/200000000000 : ℝ) (247616661347/250000000000 : ℝ) (198093329077/200000000000 : ℝ) (247616661347/250000000000 : ℝ) (198093329077/200000000000 : ℝ) (247616661347/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4405/32768 : ℝ))) (194114133877/1000000000000 : ℝ) (194114133883/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4405/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (194114133877/1000000000000 : ℝ) (194114133883/1000000000000 : ℝ) (298528533469/500000000000 : ℝ) (298528533471/500000000000 : ℝ) (440583855669/1000000000000 : ℝ) (440583855677/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4405/32768 : ℝ))) 1 (298528533469/500000000000 : ℝ) (298528533471/500000000000 : ℝ) (440583855669/1000000000000 : ℝ) (440583855677/1000000000000 : ℝ) (518820461303/1000000000000 : ℝ) (51882046131/100000000000 : ℝ) (512887614011/1000000000000 : ℝ) (256443807009/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4405/32768 : ℝ))) 2 (518820461303/1000000000000 : ℝ) (51882046131/100000000000 : ℝ) (512887614011/1000000000000 : ℝ) (256443807009/500000000000 : ℝ) (515854037657/1000000000000 : ℝ) (16120438677/31250000000 : ℝ) (257922754181/500000000000 : ℝ) (51584550837/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4405/32768 : ℝ))) 3 (515854037657/1000000000000 : ℝ) (16120438677/31250000000 : ℝ) (257922754181/500000000000 : ℝ) (51584550837/100000000000 : ℝ) (515849773009/1000000000000 : ℝ) (515849773017/1000000000000 : ℝ) (515849772991/1000000000000 : ℝ) (515849773/1000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4405/32768 : ℝ))) 4 (515849773009/1000000000000 : ℝ) (515849773017/1000000000000 : ℝ) (515849772991/1000000000000 : ℝ) (515849773/1000000000 : ℝ) (515849773/1000000000 : ℝ) (515849773009/1000000000000 : ℝ) (515849772999/1000000000000 : ℝ) (515849773009/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4405/32768 : ℝ))) 5 (515849773/1000000000 : ℝ) (515849773009/1000000000000 : ℝ) (515849772999/1000000000000 : ℝ) (515849773009/1000000000000 : ℝ) (515849772999/1000000000000 : ℝ) (515849773009/1000000000000 : ℝ) (515849772999/1000000000000 : ℝ) (515849773009/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4405/32768 : ℝ))) 6 (515849772999/1000000000000 : ℝ) (515849773009/1000000000000 : ℝ) (515849772999/1000000000000 : ℝ) (515849773009/1000000000000 : ℝ) (515849772999/1000000000000 : ℝ) (515849773009/1000000000000 : ℝ) (515849772999/1000000000000 : ℝ) (515849773009/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4405/32768 : ℝ))) 7 (515849772999/1000000000000 : ℝ) (515849773009/1000000000000 : ℝ) (515849772999/1000000000000 : ℝ) (515849773009/1000000000000 : ℝ) (515849772999/1000000000000 : ℝ) (515849773009/1000000000000 : ℝ) (515849772999/1000000000000 : ℝ) (515849773009/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4405/32768 : ℝ)) hmem 8 (198093329077/200000000000 : ℝ) (247616661347/250000000000 : ℝ) (198093329077/200000000000 : ℝ) (247616661347/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4405/32768 : ℝ))) hcmem 8 (515849772999/1000000000000 : ℝ) (515849773009/1000000000000 : ℝ) (515849772999/1000000000000 : ℝ) (515849773009/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4405/32768 : ℝ)) (198093329077/200000000000 : ℝ) (247616661347/250000000000 : ℝ) (515849772999/1000000000000 : ℝ) (515849773009/1000000000000 : ℝ) (40904705493/50000000000 : ℝ) (818094109879/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0199_exp_lower
  have heNumeric : (2019025408793/1000000000000 : ℝ)/4 ≤ Real.exp (-10938870992439/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019025408793/1000000000000 : ℝ)/4 ≤ Real.exp ((8809/65536 : ℝ)-(818094109879/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8809/65536 : ℝ) (4405/32768 : ℝ) (818094109879/1000000000000 : ℝ) (2019025408793/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover7_leaf0175_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0175_certificate
#check SmaleRate.Proofs.cover7_leaf0176_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0176_certificate
#check SmaleRate.Proofs.cover7_leaf0177_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0177_certificate
#check SmaleRate.Proofs.cover7_leaf0178_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0178_certificate
#check SmaleRate.Proofs.cover7_leaf0179_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0179_certificate
#check SmaleRate.Proofs.cover7_leaf0180_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0180_certificate
#check SmaleRate.Proofs.cover7_leaf0181_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0181_certificate
#check SmaleRate.Proofs.cover7_leaf0182_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0182_certificate
#check SmaleRate.Proofs.cover7_leaf0183_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0183_certificate
#check SmaleRate.Proofs.cover7_leaf0184_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0184_certificate
#check SmaleRate.Proofs.cover7_leaf0185_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0185_certificate
#check SmaleRate.Proofs.cover7_leaf0186_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0186_certificate
#check SmaleRate.Proofs.cover7_leaf0187_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0187_certificate
#check SmaleRate.Proofs.cover7_leaf0188_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0188_certificate
#check SmaleRate.Proofs.cover7_leaf0189_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0189_certificate
#check SmaleRate.Proofs.cover7_leaf0190_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0190_certificate
#check SmaleRate.Proofs.cover7_leaf0191_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0191_certificate
#check SmaleRate.Proofs.cover7_leaf0192_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0192_certificate
#check SmaleRate.Proofs.cover7_leaf0193_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0193_certificate
#check SmaleRate.Proofs.cover7_leaf0194_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0194_certificate
#check SmaleRate.Proofs.cover7_leaf0195_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0195_certificate
#check SmaleRate.Proofs.cover7_leaf0196_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0196_certificate
#check SmaleRate.Proofs.cover7_leaf0197_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0197_certificate
#check SmaleRate.Proofs.cover7_leaf0198_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0198_certificate
#check SmaleRate.Proofs.cover7_leaf0199_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0199_certificate
