/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.AGMCertificates

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

-- Proposed record cover8_leaf0500; no trusted numerical premise.
theorem cover8_leaf0500_exp_radius : (199603652810809507/200000000000000000 : ℝ) ≤ Real.exp ((-33281/2097152 : ℝ)/8) ∧ Real.exp ((-33281/2097152 : ℝ)/8) ≤ (62376141503377971/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33281/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0500_exp_lower : (14376771589462687/15625000000000000 : ℝ) ≤ Real.exp ((-166516751053/250000000000 : ℝ)/8) ∧ Real.exp ((-166516751053/250000000000 : ℝ)/8) ≤ (920113381725611969/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-166516751053/250000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0500_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (128431272083/62500000000 : ℝ) ≤ 4*Real.exp (65/512 : ℝ)*Real.exp (-mu (radius 8 (33281/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (128431272083/62500000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33281/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0500_exp_radius
  have hrNumeric : (492127820719/500000000000 : ℝ) ≤ Real.exp (-33281/2097152 : ℝ) ∧ Real.exp (-33281/2097152 : ℝ) ≤ (984255641439/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492127820719/500000000000 : ℝ) ≤ (radius 8 (33281/262144 : ℝ)) ∧ (radius 8 (33281/262144 : ℝ)) ≤ (984255641439/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33281/262144 : ℝ)) (492127820719/500000000000 : ℝ) (984255641439/1000000000000 : ℝ) (17675076321/100000000000 : ℝ) (176750763217/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33281/262144 : ℝ)) (492127820719/500000000000 : ℝ) (984255641439/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33281/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492127820719/500000000000 : ℝ) (984255641439/1000000000000 : ℝ) (992127820719/1000000000000 : ℝ) (12401597759/12500000000 : ℝ) (248024147191/250000000000 : ℝ) (198419317753/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33281/262144 : ℝ)) 1 (992127820719/1000000000000 : ℝ) (12401597759/12500000000 : ℝ) (248024147191/250000000000 : ℝ) (198419317753/200000000000 : ℝ) (992112204741/1000000000000 : ℝ) (992112204743/1000000000000 : ℝ) (496056102309/500000000000 : ℝ) (49605610231/50000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33281/262144 : ℝ)) 2 (992112204741/1000000000000 : ℝ) (992112204743/1000000000000 : ℝ) (496056102309/500000000000 : ℝ) (49605610231/50000000000 : ℝ) (992112204679/1000000000000 : ℝ) (496056102341/500000000000 : ℝ) (992112204679/1000000000000 : ℝ) (496056102341/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33281/262144 : ℝ)) 3 (992112204679/1000000000000 : ℝ) (496056102341/500000000000 : ℝ) (992112204679/1000000000000 : ℝ) (496056102341/500000000000 : ℝ) (992112204679/1000000000000 : ℝ) (496056102341/500000000000 : ℝ) (992112204679/1000000000000 : ℝ) (496056102341/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33281/262144 : ℝ)) 4 (992112204679/1000000000000 : ℝ) (496056102341/500000000000 : ℝ) (992112204679/1000000000000 : ℝ) (496056102341/500000000000 : ℝ) (992112204679/1000000000000 : ℝ) (496056102341/500000000000 : ℝ) (992112204679/1000000000000 : ℝ) (496056102341/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33281/262144 : ℝ)) 5 (992112204679/1000000000000 : ℝ) (496056102341/500000000000 : ℝ) (992112204679/1000000000000 : ℝ) (496056102341/500000000000 : ℝ) (992112204679/1000000000000 : ℝ) (496056102341/500000000000 : ℝ) (992112204679/1000000000000 : ℝ) (496056102341/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33281/262144 : ℝ)) 6 (992112204679/1000000000000 : ℝ) (496056102341/500000000000 : ℝ) (992112204679/1000000000000 : ℝ) (496056102341/500000000000 : ℝ) (992112204679/1000000000000 : ℝ) (496056102341/500000000000 : ℝ) (992112204679/1000000000000 : ℝ) (496056102341/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33281/262144 : ℝ)) 7 (992112204679/1000000000000 : ℝ) (496056102341/500000000000 : ℝ) (992112204679/1000000000000 : ℝ) (496056102341/500000000000 : ℝ) (992112204679/1000000000000 : ℝ) (496056102341/500000000000 : ℝ) (992112204679/1000000000000 : ℝ) (496056102341/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33281/262144 : ℝ))) (17675076321/100000000000 : ℝ) (176750763217/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33281/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (17675076321/100000000000 : ℝ) (176750763217/1000000000000 : ℝ) (117675076321/200000000000 : ℝ) (588375381609/1000000000000 : ℝ) (420417367873/1000000000000 : ℝ) (420417367883/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33281/262144 : ℝ))) 1 (117675076321/200000000000 : ℝ) (588375381609/1000000000000 : ℝ) (420417367873/1000000000000 : ℝ) (420417367883/1000000000000 : ℝ) (504396374739/1000000000000 : ℝ) (252198187373/500000000000 : ℝ) (497356239787/1000000000000 : ℝ) (124339059949/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33281/262144 : ℝ))) 2 (504396374739/1000000000000 : ℝ) (252198187373/500000000000 : ℝ) (497356239787/1000000000000 : ℝ) (124339059949/250000000000 : ℝ) (500876307263/1000000000000 : ℝ) (500876307271/1000000000000 : ℝ) (500863937913/1000000000000 : ℝ) (250431968961/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33281/262144 : ℝ))) 3 (500876307263/1000000000000 : ℝ) (500876307271/1000000000000 : ℝ) (500863937913/1000000000000 : ℝ) (250431968961/500000000000 : ℝ) (125217530647/250000000000 : ℝ) (500870122597/1000000000000 : ℝ) (500870122549/1000000000000 : ℝ) (500870122559/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33281/262144 : ℝ))) 4 (125217530647/250000000000 : ℝ) (500870122597/1000000000000 : ℝ) (500870122549/1000000000000 : ℝ) (500870122559/1000000000000 : ℝ) (62608765321/125000000000 : ℝ) (250435061289/500000000000 : ℝ) (62608765321/125000000000 : ℝ) (250435061289/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33281/262144 : ℝ))) 5 (62608765321/125000000000 : ℝ) (250435061289/500000000000 : ℝ) (62608765321/125000000000 : ℝ) (250435061289/500000000000 : ℝ) (62608765321/125000000000 : ℝ) (250435061289/500000000000 : ℝ) (62608765321/125000000000 : ℝ) (250435061289/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33281/262144 : ℝ))) 6 (62608765321/125000000000 : ℝ) (250435061289/500000000000 : ℝ) (62608765321/125000000000 : ℝ) (250435061289/500000000000 : ℝ) (62608765321/125000000000 : ℝ) (250435061289/500000000000 : ℝ) (62608765321/125000000000 : ℝ) (250435061289/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33281/262144 : ℝ))) 7 (62608765321/125000000000 : ℝ) (250435061289/500000000000 : ℝ) (62608765321/125000000000 : ℝ) (250435061289/500000000000 : ℝ) (62608765321/125000000000 : ℝ) (250435061289/500000000000 : ℝ) (62608765321/125000000000 : ℝ) (250435061289/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33281/262144 : ℝ)) hmem 8 (992112204679/1000000000000 : ℝ) (496056102341/500000000000 : ℝ) (992112204679/1000000000000 : ℝ) (496056102341/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33281/262144 : ℝ))) hcmem 8 (62608765321/125000000000 : ℝ) (250435061289/500000000000 : ℝ) (62608765321/125000000000 : ℝ) (250435061289/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33281/262144 : ℝ)) (992112204679/1000000000000 : ℝ) (496056102341/500000000000 : ℝ) (62608765321/125000000000 : ℝ) (250435061289/500000000000 : ℝ) (793020129193/1000000000000 : ℝ) (198255032303/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0500_exp_lower
  have heNumeric : (128431272083/62500000000 : ℝ)/4 ≤ Real.exp (-166516751053/250000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (128431272083/62500000000 : ℝ)/4 ≤ Real.exp ((65/512 : ℝ)-(198255032303/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (65/512 : ℝ) (33281/262144 : ℝ) (198255032303/250000000000 : ℝ) (128431272083/62500000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0501; no trusted numerical premise.
theorem cover8_leaf0501_exp_radius : (2495045511418813/2500000000000000 : ℝ) ≤ Real.exp ((-16641/1048576 : ℝ)/8) ∧ Real.exp ((-16641/1048576 : ℝ)/8) ≤ (998018204567525201/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16641/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0501_exp_lower : (920113380072198773/1000000000000000000 : ℝ) ≤ Real.exp ((-8525657837923/12800000000000 : ℝ)/8) ∧ Real.exp ((-8525657837923/12800000000000 : ℝ)/8) ≤ (460056690036099387/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8525657837923/12800000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0501_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054900323787/1000000000000 : ℝ) ≤ 4*Real.exp (33281/262144 : ℝ)*Real.exp (-mu (radius 8 (16641/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054900323787/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16641/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0501_exp_radius
  have hrNumeric : (246063793027/250000000000 : ℝ) ≤ Real.exp (-16641/1048576 : ℝ) ∧ Real.exp (-16641/1048576 : ℝ) ≤ (984255172109/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246063793027/250000000000 : ℝ) ≤ (radius 8 (16641/131072 : ℝ)) ∧ (radius 8 (16641/131072 : ℝ)) ≤ (984255172109/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16641/131072 : ℝ)) (246063793027/250000000000 : ℝ) (984255172109/1000000000000 : ℝ) (35350675341/200000000000 : ℝ) (176753376711/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16641/131072 : ℝ)) (246063793027/250000000000 : ℝ) (984255172109/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16641/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246063793027/250000000000 : ℝ) (984255172109/1000000000000 : ℝ) (496063793027/500000000000 : ℝ) (198425517211/200000000000 : ℝ) (992096352229/1000000000000 : ℝ) (992096352231/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16641/131072 : ℝ)) 1 (496063793027/500000000000 : ℝ) (198425517211/200000000000 : ℝ) (992096352229/1000000000000 : ℝ) (992096352231/1000000000000 : ℝ) (992111969141/1000000000000 : ℝ) (992111969143/1000000000000 : ℝ) (496055984509/500000000000 : ℝ) (992111969021/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16641/131072 : ℝ)) 2 (992111969141/1000000000000 : ℝ) (992111969143/1000000000000 : ℝ) (496055984509/500000000000 : ℝ) (992111969021/1000000000000 : ℝ) (992111969079/1000000000000 : ℝ) (496055984541/500000000000 : ℝ) (992111969079/1000000000000 : ℝ) (496055984541/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16641/131072 : ℝ)) 3 (992111969079/1000000000000 : ℝ) (496055984541/500000000000 : ℝ) (992111969079/1000000000000 : ℝ) (496055984541/500000000000 : ℝ) (992111969079/1000000000000 : ℝ) (496055984541/500000000000 : ℝ) (992111969079/1000000000000 : ℝ) (496055984541/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16641/131072 : ℝ)) 4 (992111969079/1000000000000 : ℝ) (496055984541/500000000000 : ℝ) (992111969079/1000000000000 : ℝ) (496055984541/500000000000 : ℝ) (992111969079/1000000000000 : ℝ) (496055984541/500000000000 : ℝ) (992111969079/1000000000000 : ℝ) (496055984541/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16641/131072 : ℝ)) 5 (992111969079/1000000000000 : ℝ) (496055984541/500000000000 : ℝ) (992111969079/1000000000000 : ℝ) (496055984541/500000000000 : ℝ) (992111969079/1000000000000 : ℝ) (496055984541/500000000000 : ℝ) (992111969079/1000000000000 : ℝ) (496055984541/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16641/131072 : ℝ)) 6 (992111969079/1000000000000 : ℝ) (496055984541/500000000000 : ℝ) (992111969079/1000000000000 : ℝ) (496055984541/500000000000 : ℝ) (992111969079/1000000000000 : ℝ) (496055984541/500000000000 : ℝ) (992111969079/1000000000000 : ℝ) (496055984541/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16641/131072 : ℝ)) 7 (992111969079/1000000000000 : ℝ) (496055984541/500000000000 : ℝ) (992111969079/1000000000000 : ℝ) (496055984541/500000000000 : ℝ) (992111969079/1000000000000 : ℝ) (496055984541/500000000000 : ℝ) (992111969079/1000000000000 : ℝ) (496055984541/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16641/131072 : ℝ))) (35350675341/200000000000 : ℝ) (176753376711/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16641/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35350675341/200000000000 : ℝ) (176753376711/1000000000000 : ℝ) (18386771511/31250000000 : ℝ) (147094172089/250000000000 : ℝ) (420420476077/1000000000000 : ℝ) (84084095217/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16641/131072 : ℝ))) 1 (18386771511/31250000000 : ℝ) (147094172089/250000000000 : ℝ) (420420476077/1000000000000 : ℝ) (84084095217/200000000000 : ℝ) (252199291107/500000000000 : ℝ) (504398582221/1000000000000 : ℝ) (497358630597/1000000000000 : ℝ) (124339657651/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16641/131072 : ℝ))) 2 (252199291107/500000000000 : ℝ) (504398582221/1000000000000 : ℝ) (497358630597/1000000000000 : ℝ) (124339657651/250000000000 : ℝ) (100175721281/200000000000 : ℝ) (500878606413/1000000000000 : ℝ) (500866237757/1000000000000 : ℝ) (100173247553/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16641/131072 : ℝ))) 3 (100175721281/200000000000 : ℝ) (500878606413/1000000000000 : ℝ) (500866237757/1000000000000 : ℝ) (100173247553/200000000000 : ℝ) (500872422081/1000000000000 : ℝ) (500872422089/1000000000000 : ℝ) (250436211021/500000000000 : ℝ) (500872422051/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16641/131072 : ℝ))) 4 (500872422081/1000000000000 : ℝ) (500872422089/1000000000000 : ℝ) (250436211021/500000000000 : ℝ) (500872422051/1000000000000 : ℝ) (500872422061/1000000000000 : ℝ) (50087242207/100000000000 : ℝ) (500872422061/1000000000000 : ℝ) (50087242207/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16641/131072 : ℝ))) 5 (500872422061/1000000000000 : ℝ) (50087242207/100000000000 : ℝ) (500872422061/1000000000000 : ℝ) (50087242207/100000000000 : ℝ) (500872422061/1000000000000 : ℝ) (50087242207/100000000000 : ℝ) (500872422061/1000000000000 : ℝ) (50087242207/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16641/131072 : ℝ))) 6 (500872422061/1000000000000 : ℝ) (50087242207/100000000000 : ℝ) (500872422061/1000000000000 : ℝ) (50087242207/100000000000 : ℝ) (500872422061/1000000000000 : ℝ) (50087242207/100000000000 : ℝ) (500872422061/1000000000000 : ℝ) (50087242207/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16641/131072 : ℝ))) 7 (500872422061/1000000000000 : ℝ) (50087242207/100000000000 : ℝ) (500872422061/1000000000000 : ℝ) (50087242207/100000000000 : ℝ) (500872422061/1000000000000 : ℝ) (50087242207/100000000000 : ℝ) (500872422061/1000000000000 : ℝ) (50087242207/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16641/131072 : ℝ)) hmem 8 (992111969079/1000000000000 : ℝ) (496055984541/500000000000 : ℝ) (992111969079/1000000000000 : ℝ) (496055984541/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16641/131072 : ℝ))) hcmem 8 (500872422061/1000000000000 : ℝ) (50087242207/100000000000 : ℝ) (500872422061/1000000000000 : ℝ) (50087242207/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16641/131072 : ℝ)) (992111969079/1000000000000 : ℝ) (496055984541/500000000000 : ℝ) (500872422061/1000000000000 : ℝ) (50087242207/100000000000 : ℝ) (793023958267/1000000000000 : ℝ) (158604791657/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0501_exp_lower
  have heNumeric : (2054900323787/1000000000000 : ℝ)/4 ≤ Real.exp (-8525657837923/12800000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054900323787/1000000000000 : ℝ)/4 ≤ Real.exp ((33281/262144 : ℝ)-(158604791657/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33281/262144 : ℝ) (16641/131072 : ℝ) (158604791657/200000000000 : ℝ) (2054900323787/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0502; no trusted numerical premise.
theorem cover8_leaf0502_exp_radius : (99801814508100641/100000000000000000 : ℝ) ≤ Real.exp ((-33283/2097152 : ℝ)/8) ∧ Real.exp ((-33283/2097152 : ℝ)/8) ≤ (998018145081006411/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33283/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0502_exp_lower : (460056689214165879/500000000000000000 : ℝ) ≤ Real.exp ((-852565802087/1280000000000 : ℝ)/8) ∧ Real.exp ((-852565802087/1280000000000 : ℝ)/8) ≤ (920113378428331759/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-852565802087/1280000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0502_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054900294417/1000000000000 : ℝ) ≤ 4*Real.exp (16641/131072 : ℝ)*Real.exp (-mu (radius 8 (33283/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054900294417/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33283/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0502_exp_radius
  have hrNumeric : (984254702779/1000000000000 : ℝ) ≤ Real.exp (-33283/2097152 : ℝ) ∧ Real.exp (-33283/2097152 : ℝ) ≤ (49212735139/50000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984254702779/1000000000000 : ℝ) ≤ (radius 8 (33283/262144 : ℝ)) ∧ (radius 8 (33283/262144 : ℝ)) ≤ (49212735139/50000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33283/262144 : ℝ)) (984254702779/1000000000000 : ℝ) (49212735139/50000000000 : ℝ) (88377995077/500000000000 : ℝ) (2209449877/12500000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33283/262144 : ℝ)) (984254702779/1000000000000 : ℝ) (49212735139/50000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33283/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984254702779/1000000000000 : ℝ) (49212735139/50000000000 : ℝ) (992127351389/1000000000000 : ℝ) (99212735139/100000000000 : ℝ) (198419223139/200000000000 : ℝ) (992096115697/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33283/262144 : ℝ)) 1 (992127351389/1000000000000 : ℝ) (99212735139/100000000000 : ℝ) (198419223139/200000000000 : ℝ) (992096115697/1000000000000 : ℝ) (496055866771/500000000000 : ℝ) (124013966693/125000000000 : ℝ) (992111733419/1000000000000 : ℝ) (992111733421/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33283/262144 : ℝ)) 2 (496055866771/500000000000 : ℝ) (124013966693/125000000000 : ℝ) (992111733419/1000000000000 : ℝ) (992111733421/1000000000000 : ℝ) (24802793337/25000000000 : ℝ) (992111733483/1000000000000 : ℝ) (24802793337/25000000000 : ℝ) (992111733483/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33283/262144 : ℝ)) 3 (24802793337/25000000000 : ℝ) (992111733483/1000000000000 : ℝ) (24802793337/25000000000 : ℝ) (992111733483/1000000000000 : ℝ) (24802793337/25000000000 : ℝ) (992111733483/1000000000000 : ℝ) (24802793337/25000000000 : ℝ) (992111733483/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33283/262144 : ℝ)) 4 (24802793337/25000000000 : ℝ) (992111733483/1000000000000 : ℝ) (24802793337/25000000000 : ℝ) (992111733483/1000000000000 : ℝ) (24802793337/25000000000 : ℝ) (992111733483/1000000000000 : ℝ) (24802793337/25000000000 : ℝ) (992111733483/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33283/262144 : ℝ)) 5 (24802793337/25000000000 : ℝ) (992111733483/1000000000000 : ℝ) (24802793337/25000000000 : ℝ) (992111733483/1000000000000 : ℝ) (24802793337/25000000000 : ℝ) (992111733483/1000000000000 : ℝ) (24802793337/25000000000 : ℝ) (992111733483/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33283/262144 : ℝ)) 6 (24802793337/25000000000 : ℝ) (992111733483/1000000000000 : ℝ) (24802793337/25000000000 : ℝ) (992111733483/1000000000000 : ℝ) (24802793337/25000000000 : ℝ) (992111733483/1000000000000 : ℝ) (24802793337/25000000000 : ℝ) (992111733483/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33283/262144 : ℝ)) 7 (24802793337/25000000000 : ℝ) (992111733483/1000000000000 : ℝ) (24802793337/25000000000 : ℝ) (992111733483/1000000000000 : ℝ) (24802793337/25000000000 : ℝ) (992111733483/1000000000000 : ℝ) (24802793337/25000000000 : ℝ) (992111733483/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33283/262144 : ℝ))) (88377995077/500000000000 : ℝ) (2209449877/12500000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33283/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88377995077/500000000000 : ℝ) (2209449877/12500000000 : ℝ) (588377995077/1000000000000 : ℝ) (14709449877/25000000000 : ℝ) (210211792101/500000000000 : ℝ) (420423584211/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33283/262144 : ℝ))) 1 (588377995077/1000000000000 : ℝ) (14709449877/25000000000 : ℝ) (210211792101/500000000000 : ℝ) (420423584211/1000000000000 : ℝ) (504400789639/1000000000000 : ℝ) (252200394823/500000000000 : ℝ) (497361021347/1000000000000 : ℝ) (99472204271/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33283/262144 : ℝ))) 2 (504400789639/1000000000000 : ℝ) (252200394823/500000000000 : ℝ) (497361021347/1000000000000 : ℝ) (99472204271/200000000000 : ℝ) (500880905493/1000000000000 : ℝ) (500880905501/1000000000000 : ℝ) (100173707509/200000000000 : ℝ) (250434268777/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33283/262144 : ℝ))) 3 (500880905493/1000000000000 : ℝ) (500880905501/1000000000000 : ℝ) (100173707509/200000000000 : ℝ) (250434268777/500000000000 : ℝ) (500874721519/1000000000000 : ℝ) (62609340191/125000000000 : ℝ) (12521868037/25000000000 : ℝ) (50087472149/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33283/262144 : ℝ))) 4 (500874721519/1000000000000 : ℝ) (62609340191/125000000000 : ℝ) (12521868037/25000000000 : ℝ) (50087472149/100000000000 : ℝ) (500874721499/1000000000000 : ℝ) (500874721509/1000000000000 : ℝ) (500874721499/1000000000000 : ℝ) (500874721509/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33283/262144 : ℝ))) 5 (500874721499/1000000000000 : ℝ) (500874721509/1000000000000 : ℝ) (500874721499/1000000000000 : ℝ) (500874721509/1000000000000 : ℝ) (500874721499/1000000000000 : ℝ) (500874721509/1000000000000 : ℝ) (500874721499/1000000000000 : ℝ) (500874721509/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33283/262144 : ℝ))) 6 (500874721499/1000000000000 : ℝ) (500874721509/1000000000000 : ℝ) (500874721499/1000000000000 : ℝ) (500874721509/1000000000000 : ℝ) (500874721499/1000000000000 : ℝ) (500874721509/1000000000000 : ℝ) (500874721499/1000000000000 : ℝ) (500874721509/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33283/262144 : ℝ))) 7 (500874721499/1000000000000 : ℝ) (500874721509/1000000000000 : ℝ) (500874721499/1000000000000 : ℝ) (500874721509/1000000000000 : ℝ) (500874721499/1000000000000 : ℝ) (500874721509/1000000000000 : ℝ) (500874721499/1000000000000 : ℝ) (500874721509/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33283/262144 : ℝ)) hmem 8 (24802793337/25000000000 : ℝ) (992111733483/1000000000000 : ℝ) (24802793337/25000000000 : ℝ) (992111733483/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33283/262144 : ℝ))) hcmem 8 (500874721499/1000000000000 : ℝ) (500874721509/1000000000000 : ℝ) (500874721499/1000000000000 : ℝ) (500874721509/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33283/262144 : ℝ)) (24802793337/25000000000 : ℝ) (992111733483/1000000000000 : ℝ) (500874721499/1000000000000 : ℝ) (500874721509/1000000000000 : ℝ) (99128473407/125000000000 : ℝ) (31721111491/40000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0502_exp_lower
  have heNumeric : (2054900294417/1000000000000 : ℝ)/4 ≤ Real.exp (-852565802087/1280000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054900294417/1000000000000 : ℝ)/4 ≤ Real.exp ((16641/131072 : ℝ)-(31721111491/40000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16641/131072 : ℝ) (33283/262144 : ℝ) (31721111491/40000000000 : ℝ) (2054900294417/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0503; no trusted numerical premise.
theorem cover8_leaf0503_exp_radius : (499009042797245583/500000000000000000 : ℝ) ≤ Real.exp ((-8321/524288 : ℝ)/8) ∧ Real.exp ((-8321/524288 : ℝ)/8) ≤ (998018085594491167/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8321/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0503_exp_lower : (184022675358710173/200000000000000000 : ℝ) ≤ Real.exp ((-42628291014029/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628291014029/64000000000000 : ℝ)/8) ≤ (460056688396775433/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628291014029/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0503_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054900265209/1000000000000 : ℝ) ≤ 4*Real.exp (33283/262144 : ℝ)*Real.exp (-mu (radius 8 (8321/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (2054900265209/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8321/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0503_exp_radius
  have hrNumeric : (19685084669/20000000000 : ℝ) ≤ Real.exp (-8321/524288 : ℝ) ∧ Real.exp (-8321/524288 : ℝ) ≤ (984254233451/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (19685084669/20000000000 : ℝ) ≤ (radius 8 (8321/65536 : ℝ)) ∧ (radius 8 (8321/65536 : ℝ)) ≤ (984254233451/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8321/65536 : ℝ)) (19685084669/20000000000 : ℝ) (984254233451/1000000000000 : ℝ) (176758603563/1000000000000 : ℝ) (17675860357/100000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8321/65536 : ℝ)) (19685084669/20000000000 : ℝ) (984254233451/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8321/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (19685084669/20000000000 : ℝ) (984254233451/1000000000000 : ℝ) (39685084669/40000000000 : ℝ) (496063558363/500000000000 : ℝ) (992095879161/1000000000000 : ℝ) (992095879163/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8321/65536 : ℝ)) 1 (39685084669/40000000000 : ℝ) (496063558363/500000000000 : ℝ) (992095879161/1000000000000 : ℝ) (992095879163/1000000000000 : ℝ) (992111497943/1000000000000 : ℝ) (198422299589/200000000000 : ℝ) (49605574891/50000000000 : ℝ) (496055748911/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8321/65536 : ℝ)) 2 (992111497943/1000000000000 : ℝ) (198422299589/200000000000 : ℝ) (49605574891/50000000000 : ℝ) (496055748911/500000000000 : ℝ) (992111497881/1000000000000 : ℝ) (248027874471/250000000000 : ℝ) (992111497881/1000000000000 : ℝ) (248027874471/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8321/65536 : ℝ)) 3 (992111497881/1000000000000 : ℝ) (248027874471/250000000000 : ℝ) (992111497881/1000000000000 : ℝ) (248027874471/250000000000 : ℝ) (992111497881/1000000000000 : ℝ) (248027874471/250000000000 : ℝ) (992111497881/1000000000000 : ℝ) (248027874471/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8321/65536 : ℝ)) 4 (992111497881/1000000000000 : ℝ) (248027874471/250000000000 : ℝ) (992111497881/1000000000000 : ℝ) (248027874471/250000000000 : ℝ) (992111497881/1000000000000 : ℝ) (248027874471/250000000000 : ℝ) (992111497881/1000000000000 : ℝ) (248027874471/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8321/65536 : ℝ)) 5 (992111497881/1000000000000 : ℝ) (248027874471/250000000000 : ℝ) (992111497881/1000000000000 : ℝ) (248027874471/250000000000 : ℝ) (992111497881/1000000000000 : ℝ) (248027874471/250000000000 : ℝ) (992111497881/1000000000000 : ℝ) (248027874471/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8321/65536 : ℝ)) 6 (992111497881/1000000000000 : ℝ) (248027874471/250000000000 : ℝ) (992111497881/1000000000000 : ℝ) (248027874471/250000000000 : ℝ) (992111497881/1000000000000 : ℝ) (248027874471/250000000000 : ℝ) (992111497881/1000000000000 : ℝ) (248027874471/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8321/65536 : ℝ)) 7 (992111497881/1000000000000 : ℝ) (248027874471/250000000000 : ℝ) (992111497881/1000000000000 : ℝ) (248027874471/250000000000 : ℝ) (992111497881/1000000000000 : ℝ) (248027874471/250000000000 : ℝ) (992111497881/1000000000000 : ℝ) (248027874471/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8321/65536 : ℝ))) (176758603563/1000000000000 : ℝ) (17675860357/100000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8321/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176758603563/1000000000000 : ℝ) (17675860357/100000000000 : ℝ) (588379301781/1000000000000 : ℝ) (117675860357/200000000000 : ℝ) (420426692257/1000000000000 : ℝ) (420426692267/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8321/65536 : ℝ))) 1 (588379301781/1000000000000 : ℝ) (117675860357/200000000000 : ℝ) (420426692257/1000000000000 : ℝ) (420426692267/1000000000000 : ℝ) (504402997019/1000000000000 : ℝ) (252201498513/500000000000 : ℝ) (124340853011/250000000000 : ℝ) (124340853013/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8321/65536 : ℝ))) 2 (504402997019/1000000000000 : ℝ) (252201498513/500000000000 : ℝ) (124340853011/250000000000 : ℝ) (124340853013/250000000000 : ℝ) (500883204531/1000000000000 : ℝ) (500883204539/1000000000000 : ℝ) (100174167457/200000000000 : ℝ) (500870837293/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8321/65536 : ℝ))) 3 (500883204531/1000000000000 : ℝ) (500883204539/1000000000000 : ℝ) (100174167457/200000000000 : ℝ) (500870837293/1000000000000 : ℝ) (125219255227/250000000000 : ℝ) (125219255229/250000000000 : ℝ) (500877020869/1000000000000 : ℝ) (250438510439/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8321/65536 : ℝ))) 4 (125219255227/250000000000 : ℝ) (125219255229/250000000000 : ℝ) (500877020869/1000000000000 : ℝ) (250438510439/500000000000 : ℝ) (62609627611/125000000000 : ℝ) (500877020897/1000000000000 : ℝ) (62609627611/125000000000 : ℝ) (500877020897/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8321/65536 : ℝ))) 5 (62609627611/125000000000 : ℝ) (500877020897/1000000000000 : ℝ) (62609627611/125000000000 : ℝ) (500877020897/1000000000000 : ℝ) (62609627611/125000000000 : ℝ) (500877020897/1000000000000 : ℝ) (62609627611/125000000000 : ℝ) (500877020897/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8321/65536 : ℝ))) 6 (62609627611/125000000000 : ℝ) (500877020897/1000000000000 : ℝ) (62609627611/125000000000 : ℝ) (500877020897/1000000000000 : ℝ) (62609627611/125000000000 : ℝ) (500877020897/1000000000000 : ℝ) (62609627611/125000000000 : ℝ) (500877020897/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8321/65536 : ℝ))) 7 (62609627611/125000000000 : ℝ) (500877020897/1000000000000 : ℝ) (62609627611/125000000000 : ℝ) (500877020897/1000000000000 : ℝ) (62609627611/125000000000 : ℝ) (500877020897/1000000000000 : ℝ) (62609627611/125000000000 : ℝ) (500877020897/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8321/65536 : ℝ)) hmem 8 (992111497881/1000000000000 : ℝ) (248027874471/250000000000 : ℝ) (992111497881/1000000000000 : ℝ) (248027874471/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8321/65536 : ℝ))) hcmem 8 (62609627611/125000000000 : ℝ) (500877020897/1000000000000 : ℝ) (62609627611/125000000000 : ℝ) (500877020897/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8321/65536 : ℝ)) (992111497881/1000000000000 : ℝ) (248027874471/250000000000 : ℝ) (62609627611/125000000000 : ℝ) (500877020897/1000000000000 : ℝ) (793031616169/1000000000000 : ℝ) (396515808093/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0503_exp_lower
  have heNumeric : (2054900265209/1000000000000 : ℝ)/4 ≤ Real.exp (-42628291014029/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054900265209/1000000000000 : ℝ)/4 ≤ Real.exp ((33283/262144 : ℝ)-(396515808093/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33283/262144 : ℝ) (8321/65536 : ℝ) (396515808093/500000000000 : ℝ) (2054900265209/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0504; no trusted numerical premise.
theorem cover8_leaf0504_exp_radius : (998018026107979467/1000000000000000000 : ℝ) ≤ Real.exp ((-33285/2097152 : ℝ)/8) ∧ Real.exp ((-33285/2097152 : ℝ)/8) ≤ (249504506526994867/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33285/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0504_exp_lower : (920113375167166009/1000000000000000000 : ℝ) ≤ Real.exp ((-10657072979759/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657072979759/16000000000000 : ℝ)/8) ≤ (92011337516716601/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657072979759/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0504_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054900236151/1000000000000 : ℝ) ≤ 4*Real.exp (8321/65536 : ℝ)*Real.exp (-mu (radius 8 (33285/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054900236151/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33285/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0504_exp_radius
  have hrNumeric : (984253764121/1000000000000 : ℝ) ≤ Real.exp (-33285/2097152 : ℝ) ∧ Real.exp (-33285/2097152 : ℝ) ≤ (492126882061/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984253764121/1000000000000 : ℝ) ≤ (radius 8 (33285/262144 : ℝ)) ∧ (radius 8 (33285/262144 : ℝ)) ≤ (492126882061/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33285/262144 : ℝ)) (984253764121/1000000000000 : ℝ) (492126882061/500000000000 : ℝ) (176761216933/1000000000000 : ℝ) (176761216939/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33285/262144 : ℝ)) (984253764121/1000000000000 : ℝ) (492126882061/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33285/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984253764121/1000000000000 : ℝ) (492126882061/500000000000 : ℝ) (49606344103/50000000000 : ℝ) (992126882061/1000000000000 : ℝ) (992095642627/1000000000000 : ℝ) (992095642629/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33285/262144 : ℝ)) 1 (49606344103/50000000000 : ℝ) (992126882061/1000000000000 : ℝ) (992095642627/1000000000000 : ℝ) (992095642629/1000000000000 : ℝ) (992111262343/1000000000000 : ℝ) (198422252469/200000000000 : ℝ) (49605563111/50000000000 : ℝ) (992111262223/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33285/262144 : ℝ)) 2 (992111262343/1000000000000 : ℝ) (198422252469/200000000000 : ℝ) (49605563111/50000000000 : ℝ) (992111262223/1000000000000 : ℝ) (992111262281/1000000000000 : ℝ) (248027815571/250000000000 : ℝ) (992111262281/1000000000000 : ℝ) (248027815571/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33285/262144 : ℝ)) 3 (992111262281/1000000000000 : ℝ) (248027815571/250000000000 : ℝ) (992111262281/1000000000000 : ℝ) (248027815571/250000000000 : ℝ) (992111262281/1000000000000 : ℝ) (248027815571/250000000000 : ℝ) (992111262281/1000000000000 : ℝ) (248027815571/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33285/262144 : ℝ)) 4 (992111262281/1000000000000 : ℝ) (248027815571/250000000000 : ℝ) (992111262281/1000000000000 : ℝ) (248027815571/250000000000 : ℝ) (992111262281/1000000000000 : ℝ) (248027815571/250000000000 : ℝ) (992111262281/1000000000000 : ℝ) (248027815571/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33285/262144 : ℝ)) 5 (992111262281/1000000000000 : ℝ) (248027815571/250000000000 : ℝ) (992111262281/1000000000000 : ℝ) (248027815571/250000000000 : ℝ) (992111262281/1000000000000 : ℝ) (248027815571/250000000000 : ℝ) (992111262281/1000000000000 : ℝ) (248027815571/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33285/262144 : ℝ)) 6 (992111262281/1000000000000 : ℝ) (248027815571/250000000000 : ℝ) (992111262281/1000000000000 : ℝ) (248027815571/250000000000 : ℝ) (992111262281/1000000000000 : ℝ) (248027815571/250000000000 : ℝ) (992111262281/1000000000000 : ℝ) (248027815571/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33285/262144 : ℝ)) 7 (992111262281/1000000000000 : ℝ) (248027815571/250000000000 : ℝ) (992111262281/1000000000000 : ℝ) (248027815571/250000000000 : ℝ) (992111262281/1000000000000 : ℝ) (248027815571/250000000000 : ℝ) (992111262281/1000000000000 : ℝ) (248027815571/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33285/262144 : ℝ))) (176761216933/1000000000000 : ℝ) (176761216939/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33285/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176761216933/1000000000000 : ℝ) (176761216939/1000000000000 : ℝ) (294190304233/500000000000 : ℝ) (58838060847/100000000000 : ℝ) (420429800243/1000000000000 : ℝ) (420429800251/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33285/262144 : ℝ))) 1 (294190304233/500000000000 : ℝ) (58838060847/100000000000 : ℝ) (420429800243/1000000000000 : ℝ) (420429800251/1000000000000 : ℝ) (252202602177/500000000000 : ℝ) (504405204361/1000000000000 : ℝ) (7771340667/15625000000 : ℝ) (62170725337/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33285/262144 : ℝ))) 2 (252202602177/500000000000 : ℝ) (504405204361/1000000000000 : ℝ) (7771340667/15625000000 : ℝ) (62170725337/125000000000 : ℝ) (500885503521/1000000000000 : ℝ) (500885503529/1000000000000 : ℝ) (20034925479/40000000000 : ℝ) (500873136983/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33285/262144 : ℝ))) 3 (500885503521/1000000000000 : ℝ) (500885503529/1000000000000 : ℝ) (20034925479/40000000000 : ℝ) (500873136983/1000000000000 : ℝ) (62609915031/125000000000 : ℝ) (7826239379/15625000000 : ℝ) (500879320209/1000000000000 : ℝ) (250439660109/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33285/262144 : ℝ))) 4 (62609915031/125000000000 : ℝ) (7826239379/15625000000 : ℝ) (500879320209/1000000000000 : ℝ) (250439660109/500000000000 : ℝ) (125219830057/250000000000 : ℝ) (500879320237/1000000000000 : ℝ) (125219830057/250000000000 : ℝ) (500879320237/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33285/262144 : ℝ))) 5 (125219830057/250000000000 : ℝ) (500879320237/1000000000000 : ℝ) (125219830057/250000000000 : ℝ) (500879320237/1000000000000 : ℝ) (125219830057/250000000000 : ℝ) (500879320237/1000000000000 : ℝ) (125219830057/250000000000 : ℝ) (500879320237/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33285/262144 : ℝ))) 6 (125219830057/250000000000 : ℝ) (500879320237/1000000000000 : ℝ) (125219830057/250000000000 : ℝ) (500879320237/1000000000000 : ℝ) (125219830057/250000000000 : ℝ) (500879320237/1000000000000 : ℝ) (125219830057/250000000000 : ℝ) (500879320237/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33285/262144 : ℝ))) 7 (125219830057/250000000000 : ℝ) (500879320237/1000000000000 : ℝ) (125219830057/250000000000 : ℝ) (500879320237/1000000000000 : ℝ) (125219830057/250000000000 : ℝ) (500879320237/1000000000000 : ℝ) (125219830057/250000000000 : ℝ) (500879320237/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33285/262144 : ℝ)) hmem 8 (992111262281/1000000000000 : ℝ) (248027815571/250000000000 : ℝ) (992111262281/1000000000000 : ℝ) (248027815571/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33285/262144 : ℝ))) hcmem 8 (125219830057/250000000000 : ℝ) (500879320237/1000000000000 : ℝ) (125219830057/250000000000 : ℝ) (500879320237/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33285/262144 : ℝ)) (992111262281/1000000000000 : ℝ) (248027815571/250000000000 : ℝ) (125219830057/250000000000 : ℝ) (500879320237/1000000000000 : ℝ) (396517722503/500000000000 : ℝ) (24782357657/31250000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0504_exp_lower
  have heNumeric : (2054900236151/1000000000000 : ℝ)/4 ≤ Real.exp (-10657072979759/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054900236151/1000000000000 : ℝ)/4 ≤ Real.exp ((8321/65536 : ℝ)-(24782357657/31250000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8321/65536 : ℝ) (33285/262144 : ℝ) (24782357657/31250000000 : ℝ) (2054900236151/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0505; no trusted numerical premise.
theorem cover8_leaf0505_exp_radius : (199603593324294263/200000000000000000 : ℝ) ≤ Real.exp ((-16643/1048576 : ℝ)/8) ∧ Real.exp ((-16643/1048576 : ℝ)/8) ≤ (249504491655367829/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16643/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0505_exp_lower : (7188385730856541/7812500000000000 : ℝ) ≤ Real.exp ((-8525658563823/12800000000000 : ℝ)/8) ∧ Real.exp ((-8525658563823/12800000000000 : ℝ)/8) ≤ (920113373549637249/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8525658563823/12800000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0505_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513725051813/250000000000 : ℝ) ≤ 4*Real.exp (33285/262144 : ℝ)*Real.exp (-mu (radius 8 (16643/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (513725051813/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16643/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0505_exp_radius
  have hrNumeric : (123031661849/125000000000 : ℝ) ≤ Real.exp (-16643/1048576 : ℝ) ∧ Real.exp (-16643/1048576 : ℝ) ≤ (984253294793/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (123031661849/125000000000 : ℝ) ≤ (radius 8 (16643/131072 : ℝ)) ∧ (radius 8 (16643/131072 : ℝ)) ≤ (984253294793/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16643/131072 : ℝ)) (123031661849/125000000000 : ℝ) (984253294793/1000000000000 : ℝ) (88381915131/500000000000 : ℝ) (176763830269/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16643/131072 : ℝ)) (123031661849/125000000000 : ℝ) (984253294793/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16643/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (123031661849/125000000000 : ℝ) (984253294793/1000000000000 : ℝ) (248031661849/250000000000 : ℝ) (992126647397/1000000000000 : ℝ) (992095406093/1000000000000 : ℝ) (198419081219/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16643/131072 : ℝ)) 1 (248031661849/250000000000 : ℝ) (992126647397/1000000000000 : ℝ) (992095406093/1000000000000 : ℝ) (198419081219/200000000000 : ℝ) (124013878343/125000000000 : ℝ) (496055513373/500000000000 : ℝ) (992111026621/1000000000000 : ℝ) (15501734791/15625000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16643/131072 : ℝ)) 2 (124013878343/125000000000 : ℝ) (496055513373/500000000000 : ℝ) (992111026621/1000000000000 : ℝ) (15501734791/15625000000 : ℝ) (496055513341/500000000000 : ℝ) (198422205337/200000000000 : ℝ) (496055513341/500000000000 : ℝ) (198422205337/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16643/131072 : ℝ)) 3 (496055513341/500000000000 : ℝ) (198422205337/200000000000 : ℝ) (496055513341/500000000000 : ℝ) (198422205337/200000000000 : ℝ) (496055513341/500000000000 : ℝ) (198422205337/200000000000 : ℝ) (496055513341/500000000000 : ℝ) (198422205337/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16643/131072 : ℝ)) 4 (496055513341/500000000000 : ℝ) (198422205337/200000000000 : ℝ) (496055513341/500000000000 : ℝ) (198422205337/200000000000 : ℝ) (496055513341/500000000000 : ℝ) (198422205337/200000000000 : ℝ) (496055513341/500000000000 : ℝ) (198422205337/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16643/131072 : ℝ)) 5 (496055513341/500000000000 : ℝ) (198422205337/200000000000 : ℝ) (496055513341/500000000000 : ℝ) (198422205337/200000000000 : ℝ) (496055513341/500000000000 : ℝ) (198422205337/200000000000 : ℝ) (496055513341/500000000000 : ℝ) (198422205337/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16643/131072 : ℝ)) 6 (496055513341/500000000000 : ℝ) (198422205337/200000000000 : ℝ) (496055513341/500000000000 : ℝ) (198422205337/200000000000 : ℝ) (496055513341/500000000000 : ℝ) (198422205337/200000000000 : ℝ) (496055513341/500000000000 : ℝ) (198422205337/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16643/131072 : ℝ)) 7 (496055513341/500000000000 : ℝ) (198422205337/200000000000 : ℝ) (496055513341/500000000000 : ℝ) (198422205337/200000000000 : ℝ) (496055513341/500000000000 : ℝ) (198422205337/200000000000 : ℝ) (496055513341/500000000000 : ℝ) (198422205337/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16643/131072 : ℝ))) (88381915131/500000000000 : ℝ) (176763830269/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16643/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88381915131/500000000000 : ℝ) (176763830269/1000000000000 : ℝ) (588381915131/1000000000000 : ℝ) (117676383027/200000000000 : ℝ) (420432908157/1000000000000 : ℝ) (420432908167/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16643/131072 : ℝ))) 1 (588381915131/1000000000000 : ℝ) (117676383027/200000000000 : ℝ) (420432908157/1000000000000 : ℝ) (420432908167/1000000000000 : ℝ) (126101852911/250000000000 : ℝ) (504407411651/1000000000000 : ℝ) (248684096639/500000000000 : ℝ) (497368193287/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16643/131072 : ℝ))) 2 (126101852911/250000000000 : ℝ) (504407411651/1000000000000 : ℝ) (248684096639/500000000000 : ℝ) (497368193287/1000000000000 : ℝ) (500887802461/1000000000000 : ℝ) (500887802469/1000000000000 : ℝ) (62609429577/125000000000 : ℝ) (4007003493/8000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16643/131072 : ℝ))) 3 (500887802461/1000000000000 : ℝ) (500887802469/1000000000000 : ℝ) (62609429577/125000000000 : ℝ) (4007003493/8000000000 : ℝ) (250440809769/500000000000 : ℝ) (500881619547/1000000000000 : ℝ) (1001763239/2000000000 : ℝ) (500881619509/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16643/131072 : ℝ))) 4 (250440809769/500000000000 : ℝ) (500881619547/1000000000000 : ℝ) (1001763239/2000000000 : ℝ) (500881619509/1000000000000 : ℝ) (500881619519/1000000000000 : ℝ) (62610202441/125000000000 : ℝ) (250440809759/500000000000 : ℝ) (62610202441/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16643/131072 : ℝ))) 5 (500881619519/1000000000000 : ℝ) (62610202441/125000000000 : ℝ) (250440809759/500000000000 : ℝ) (62610202441/125000000000 : ℝ) (250440809759/500000000000 : ℝ) (62610202441/125000000000 : ℝ) (250440809759/500000000000 : ℝ) (62610202441/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16643/131072 : ℝ))) 6 (250440809759/500000000000 : ℝ) (62610202441/125000000000 : ℝ) (250440809759/500000000000 : ℝ) (62610202441/125000000000 : ℝ) (250440809759/500000000000 : ℝ) (62610202441/125000000000 : ℝ) (250440809759/500000000000 : ℝ) (62610202441/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16643/131072 : ℝ))) 7 (250440809759/500000000000 : ℝ) (62610202441/125000000000 : ℝ) (250440809759/500000000000 : ℝ) (62610202441/125000000000 : ℝ) (250440809759/500000000000 : ℝ) (62610202441/125000000000 : ℝ) (250440809759/500000000000 : ℝ) (62610202441/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16643/131072 : ℝ)) hmem 8 (496055513341/500000000000 : ℝ) (198422205337/200000000000 : ℝ) (496055513341/500000000000 : ℝ) (198422205337/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16643/131072 : ℝ))) hcmem 8 (250440809759/500000000000 : ℝ) (62610202441/125000000000 : ℝ) (250440809759/500000000000 : ℝ) (62610202441/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16643/131072 : ℝ)) (496055513341/500000000000 : ℝ) (198422205337/200000000000 : ℝ) (250440809759/500000000000 : ℝ) (62610202441/125000000000 : ℝ) (396519636883/500000000000 : ℝ) (158607854757/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0505_exp_lower
  have heNumeric : (513725051813/250000000000 : ℝ)/4 ≤ Real.exp (-8525658563823/12800000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513725051813/250000000000 : ℝ)/4 ≤ Real.exp ((33285/262144 : ℝ)-(158607854757/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33285/262144 : ℝ) (16643/131072 : ℝ) (158607854757/200000000000 : ℝ) (513725051813/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0506; no trusted numerical premise.
theorem cover8_leaf0506_exp_radius : (249504476783741677/250000000000000000 : ℝ) ≤ Real.exp ((-33287/2097152 : ℝ)/8) ∧ Real.exp ((-33287/2097152 : ℝ)/8) ≤ (998017907134966709/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33287/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0506_exp_lower : (460056685970942347/500000000000000000 : ℝ) ≤ Real.exp ((-21314146856877/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314146856877/32000000000000 : ℝ)/8) ≤ (184022674388376939/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314146856877/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0506_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054900178527/1000000000000 : ℝ) ≤ 4*Real.exp (16643/131072 : ℝ)*Real.exp (-mu (radius 8 (33287/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054900178527/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33287/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0506_exp_radius
  have hrNumeric : (123031603183/125000000000 : ℝ) ≤ Real.exp (-33287/2097152 : ℝ) ∧ Real.exp (-33287/2097152 : ℝ) ≤ (196850565093/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (123031603183/125000000000 : ℝ) ≤ (radius 8 (33287/262144 : ℝ)) ∧ (radius 8 (33287/262144 : ℝ)) ≤ (196850565093/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33287/262144 : ℝ)) (123031603183/125000000000 : ℝ) (196850565093/200000000000 : ℝ) (88383221773/500000000000 : ℝ) (176766443553/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33287/262144 : ℝ)) (123031603183/125000000000 : ℝ) (196850565093/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33287/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (123031603183/125000000000 : ℝ) (196850565093/200000000000 : ℝ) (248031603183/250000000000 : ℝ) (992126412733/1000000000000 : ℝ) (992095169559/1000000000000 : ℝ) (992095169561/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33287/262144 : ℝ)) 1 (248031603183/250000000000 : ℝ) (992126412733/1000000000000 : ℝ) (992095169559/1000000000000 : ℝ) (992095169561/1000000000000 : ℝ) (198422158229/200000000000 : ℝ) (992110791147/1000000000000 : ℝ) (496055395511/500000000000 : ℝ) (39684431641/40000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33287/262144 : ℝ)) 2 (198422158229/200000000000 : ℝ) (992110791147/1000000000000 : ℝ) (496055395511/500000000000 : ℝ) (39684431641/40000000000 : ℝ) (992110791083/1000000000000 : ℝ) (496055395543/500000000000 : ℝ) (992110791083/1000000000000 : ℝ) (496055395543/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33287/262144 : ℝ)) 3 (992110791083/1000000000000 : ℝ) (496055395543/500000000000 : ℝ) (992110791083/1000000000000 : ℝ) (496055395543/500000000000 : ℝ) (992110791083/1000000000000 : ℝ) (496055395543/500000000000 : ℝ) (992110791083/1000000000000 : ℝ) (496055395543/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33287/262144 : ℝ)) 4 (992110791083/1000000000000 : ℝ) (496055395543/500000000000 : ℝ) (992110791083/1000000000000 : ℝ) (496055395543/500000000000 : ℝ) (992110791083/1000000000000 : ℝ) (496055395543/500000000000 : ℝ) (992110791083/1000000000000 : ℝ) (496055395543/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33287/262144 : ℝ)) 5 (992110791083/1000000000000 : ℝ) (496055395543/500000000000 : ℝ) (992110791083/1000000000000 : ℝ) (496055395543/500000000000 : ℝ) (992110791083/1000000000000 : ℝ) (496055395543/500000000000 : ℝ) (992110791083/1000000000000 : ℝ) (496055395543/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33287/262144 : ℝ)) 6 (992110791083/1000000000000 : ℝ) (496055395543/500000000000 : ℝ) (992110791083/1000000000000 : ℝ) (496055395543/500000000000 : ℝ) (992110791083/1000000000000 : ℝ) (496055395543/500000000000 : ℝ) (992110791083/1000000000000 : ℝ) (496055395543/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33287/262144 : ℝ)) 7 (992110791083/1000000000000 : ℝ) (496055395543/500000000000 : ℝ) (992110791083/1000000000000 : ℝ) (496055395543/500000000000 : ℝ) (992110791083/1000000000000 : ℝ) (496055395543/500000000000 : ℝ) (992110791083/1000000000000 : ℝ) (496055395543/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33287/262144 : ℝ))) (88383221773/500000000000 : ℝ) (176766443553/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33287/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88383221773/500000000000 : ℝ) (176766443553/1000000000000 : ℝ) (588383221773/1000000000000 : ℝ) (588383221777/1000000000000 : ℝ) (84087203199/200000000000 : ℝ) (105109004001/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33287/262144 : ℝ))) 1 (588383221773/1000000000000 : ℝ) (588383221777/1000000000000 : ℝ) (84087203199/200000000000 : ℝ) (105109004001/250000000000 : ℝ) (126102404721/250000000000 : ℝ) (504409618891/1000000000000 : ℝ) (497370583811/1000000000000 : ℝ) (497370583819/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33287/262144 : ℝ))) 2 (126102404721/250000000000 : ℝ) (504409618891/1000000000000 : ℝ) (497370583811/1000000000000 : ℝ) (497370583819/1000000000000 : ℝ) (500890101347/1000000000000 : ℝ) (100178020271/200000000000 : ℝ) (500877736203/1000000000000 : ℝ) (500877736211/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33287/262144 : ℝ))) 3 (500890101347/1000000000000 : ℝ) (100178020271/200000000000 : ℝ) (500877736203/1000000000000 : ℝ) (500877736211/1000000000000 : ℝ) (20035356751/40000000000 : ℝ) (500883918783/1000000000000 : ℝ) (31305244921/62500000000 : ℝ) (100176783749/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33287/262144 : ℝ))) 4 (20035356751/40000000000 : ℝ) (500883918783/1000000000000 : ℝ) (31305244921/62500000000 : ℝ) (100176783749/200000000000 : ℝ) (100176783751/200000000000 : ℝ) (125220979691/250000000000 : ℝ) (100176783751/200000000000 : ℝ) (125220979691/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33287/262144 : ℝ))) 5 (100176783751/200000000000 : ℝ) (125220979691/250000000000 : ℝ) (100176783751/200000000000 : ℝ) (125220979691/250000000000 : ℝ) (100176783751/200000000000 : ℝ) (125220979691/250000000000 : ℝ) (100176783751/200000000000 : ℝ) (125220979691/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33287/262144 : ℝ))) 6 (100176783751/200000000000 : ℝ) (125220979691/250000000000 : ℝ) (100176783751/200000000000 : ℝ) (125220979691/250000000000 : ℝ) (100176783751/200000000000 : ℝ) (125220979691/250000000000 : ℝ) (100176783751/200000000000 : ℝ) (125220979691/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33287/262144 : ℝ))) 7 (100176783751/200000000000 : ℝ) (125220979691/250000000000 : ℝ) (100176783751/200000000000 : ℝ) (125220979691/250000000000 : ℝ) (100176783751/200000000000 : ℝ) (125220979691/250000000000 : ℝ) (100176783751/200000000000 : ℝ) (125220979691/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33287/262144 : ℝ)) hmem 8 (992110791083/1000000000000 : ℝ) (496055395543/500000000000 : ℝ) (992110791083/1000000000000 : ℝ) (496055395543/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33287/262144 : ℝ))) hcmem 8 (100176783751/200000000000 : ℝ) (125220979691/250000000000 : ℝ) (100176783751/200000000000 : ℝ) (125220979691/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33287/262144 : ℝ)) (992110791083/1000000000000 : ℝ) (496055395543/500000000000 : ℝ) (100176783751/200000000000 : ℝ) (125220979691/250000000000 : ℝ) (793043102443/1000000000000 : ℝ) (793043102461/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0506_exp_lower
  have heNumeric : (2054900178527/1000000000000 : ℝ)/4 ≤ Real.exp (-21314146856877/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054900178527/1000000000000 : ℝ)/4 ≤ Real.exp ((16643/131072 : ℝ)-(793043102461/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16643/131072 : ℝ) (33287/262144 : ℝ) (793043102461/1000000000000 : ℝ) (2054900178527/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0507; no trusted numerical premise.
theorem cover8_leaf0507_exp_radius : (499008923824232823/500000000000000000 : ℝ) ≤ Real.exp ((-4161/262144 : ℝ)/8) ∧ Real.exp ((-4161/262144 : ℝ)/8) ≤ (998017847648465647/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4161/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0507_exp_lower : (230028342585459523/250000000000000000 : ℝ) ≤ Real.exp ((-8525658920821/12800000000000 : ℝ)/8) ∧ Real.exp ((-8525658920821/12800000000000 : ℝ)/8) ≤ (920113370341838093/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8525658920821/12800000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0507_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (102745007497/50000000000 : ℝ) ≤ 4*Real.exp (33287/262144 : ℝ)*Real.exp (-mu (radius 8 (4161/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (102745007497/50000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4161/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0507_exp_radius
  have hrNumeric : (196850471227/200000000000 : ℝ) ≤ Real.exp (-4161/262144 : ℝ) ∧ Real.exp (-4161/262144 : ℝ) ≤ (123031544517/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196850471227/200000000000 : ℝ) ≤ (radius 8 (4161/32768 : ℝ)) ∧ (radius 8 (4161/32768 : ℝ)) ≤ (123031544517/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4161/32768 : ℝ)) (196850471227/200000000000 : ℝ) (123031544517/125000000000 : ℝ) (44192264199/250000000000 : ℝ) (176769056803/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4161/32768 : ℝ)) (196850471227/200000000000 : ℝ) (123031544517/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4161/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196850471227/200000000000 : ℝ) (123031544517/125000000000 : ℝ) (992126178067/1000000000000 : ℝ) (248031544517/250000000000 : ℝ) (39683797321/40000000000 : ℝ) (992094933027/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4161/32768 : ℝ)) 1 (992126178067/1000000000000 : ℝ) (248031544517/250000000000 : ℝ) (39683797321/40000000000 : ℝ) (992094933027/1000000000000 : ℝ) (496055277773/500000000000 : ℝ) (248027638887/250000000000 : ℝ) (496055277711/500000000000 : ℝ) (39684422217/40000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4161/32768 : ℝ)) 2 (496055277773/500000000000 : ℝ) (248027638887/250000000000 : ℝ) (496055277711/500000000000 : ℝ) (39684422217/40000000000 : ℝ) (248027638871/250000000000 : ℝ) (992110555487/1000000000000 : ℝ) (992110555483/1000000000000 : ℝ) (992110555487/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4161/32768 : ℝ)) 3 (248027638871/250000000000 : ℝ) (992110555487/1000000000000 : ℝ) (992110555483/1000000000000 : ℝ) (992110555487/1000000000000 : ℝ) (992110555483/1000000000000 : ℝ) (992110555487/1000000000000 : ℝ) (992110555483/1000000000000 : ℝ) (992110555487/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4161/32768 : ℝ)) 4 (992110555483/1000000000000 : ℝ) (992110555487/1000000000000 : ℝ) (992110555483/1000000000000 : ℝ) (992110555487/1000000000000 : ℝ) (992110555483/1000000000000 : ℝ) (992110555487/1000000000000 : ℝ) (992110555483/1000000000000 : ℝ) (992110555487/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4161/32768 : ℝ)) 5 (992110555483/1000000000000 : ℝ) (992110555487/1000000000000 : ℝ) (992110555483/1000000000000 : ℝ) (992110555487/1000000000000 : ℝ) (992110555483/1000000000000 : ℝ) (992110555487/1000000000000 : ℝ) (992110555483/1000000000000 : ℝ) (992110555487/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4161/32768 : ℝ)) 6 (992110555483/1000000000000 : ℝ) (992110555487/1000000000000 : ℝ) (992110555483/1000000000000 : ℝ) (992110555487/1000000000000 : ℝ) (992110555483/1000000000000 : ℝ) (992110555487/1000000000000 : ℝ) (992110555483/1000000000000 : ℝ) (992110555487/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4161/32768 : ℝ)) 7 (992110555483/1000000000000 : ℝ) (992110555487/1000000000000 : ℝ) (992110555483/1000000000000 : ℝ) (992110555487/1000000000000 : ℝ) (992110555483/1000000000000 : ℝ) (992110555487/1000000000000 : ℝ) (992110555483/1000000000000 : ℝ) (992110555487/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4161/32768 : ℝ))) (44192264199/250000000000 : ℝ) (176769056803/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4161/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44192264199/250000000000 : ℝ) (176769056803/1000000000000 : ℝ) (294192264199/500000000000 : ℝ) (294192264201/500000000000 : ℝ) (420439123769/1000000000000 : ℝ) (210219561889/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4161/32768 : ℝ))) 1 (294192264199/500000000000 : ℝ) (294192264201/500000000000 : ℝ) (420439123769/1000000000000 : ℝ) (210219561889/500000000000 : ℝ) (504411826083/1000000000000 : ℝ) (50441182609/100000000000 : ℝ) (248686487147/500000000000 : ℝ) (248686487151/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4161/32768 : ℝ))) 2 (504411826083/1000000000000 : ℝ) (50441182609/100000000000 : ℝ) (248686487147/500000000000 : ℝ) (248686487151/500000000000 : ℝ) (125223100047/250000000000 : ℝ) (125223100049/250000000000 : ℝ) (100176007149/200000000000 : ℝ) (500880035753/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4161/32768 : ℝ))) 3 (125223100047/250000000000 : ℝ) (125223100049/250000000000 : ℝ) (100176007149/200000000000 : ℝ) (500880035753/1000000000000 : ℝ) (250443108983/500000000000 : ℝ) (20035448719/40000000000 : ℝ) (62610777241/125000000000 : ℝ) (500886217937/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4161/32768 : ℝ))) 4 (250443108983/500000000000 : ℝ) (20035448719/40000000000 : ℝ) (62610777241/125000000000 : ℝ) (500886217937/1000000000000 : ℝ) (500886217947/1000000000000 : ℝ) (125221554489/250000000000 : ℝ) (250443108973/500000000000 : ℝ) (125221554489/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4161/32768 : ℝ))) 5 (500886217947/1000000000000 : ℝ) (125221554489/250000000000 : ℝ) (250443108973/500000000000 : ℝ) (125221554489/250000000000 : ℝ) (250443108973/500000000000 : ℝ) (125221554489/250000000000 : ℝ) (250443108973/500000000000 : ℝ) (125221554489/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4161/32768 : ℝ))) 6 (250443108973/500000000000 : ℝ) (125221554489/250000000000 : ℝ) (250443108973/500000000000 : ℝ) (125221554489/250000000000 : ℝ) (250443108973/500000000000 : ℝ) (125221554489/250000000000 : ℝ) (250443108973/500000000000 : ℝ) (125221554489/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4161/32768 : ℝ))) 7 (250443108973/500000000000 : ℝ) (125221554489/250000000000 : ℝ) (250443108973/500000000000 : ℝ) (125221554489/250000000000 : ℝ) (250443108973/500000000000 : ℝ) (125221554489/250000000000 : ℝ) (250443108973/500000000000 : ℝ) (125221554489/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4161/32768 : ℝ)) hmem 8 (992110555483/1000000000000 : ℝ) (992110555487/1000000000000 : ℝ) (992110555483/1000000000000 : ℝ) (992110555487/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4161/32768 : ℝ))) hcmem 8 (250443108973/500000000000 : ℝ) (125221554489/250000000000 : ℝ) (250443108973/500000000000 : ℝ) (125221554489/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4161/32768 : ℝ)) (992110555483/1000000000000 : ℝ) (992110555487/1000000000000 : ℝ) (250443108973/500000000000 : ℝ) (125221554489/250000000000 : ℝ) (15860938621/20000000000 : ℝ) (79304693107/100000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0507_exp_lower
  have heNumeric : (102745007497/50000000000 : ℝ)/4 ≤ Real.exp (-8525658920821/12800000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (102745007497/50000000000 : ℝ)/4 ≤ Real.exp ((33287/262144 : ℝ)-(79304693107/100000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33287/262144 : ℝ) (4161/32768 : ℝ) (79304693107/100000000000 : ℝ) (102745007497/50000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0508; no trusted numerical premise.
theorem cover8_leaf0508_exp_radius : (99801778816196813/100000000000000000 : ℝ) ≤ Real.exp ((-33289/2097152 : ℝ)/8) ∧ Real.exp ((-33289/2097152 : ℝ)/8) ≤ (998017788161968131/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33289/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0508_exp_lower : (920113368751567697/1000000000000000000 : ℝ) ≤ Real.exp ((-5328536936127/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328536936127/8000000000000 : ℝ)/8) ≤ (460056684375783849/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328536936127/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0508_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054900121527/1000000000000 : ℝ) ≤ 4*Real.exp (4161/32768 : ℝ)*Real.exp (-mu (radius 8 (33289/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054900121527/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33289/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0508_exp_radius
  have hrNumeric : (984251886807/1000000000000 : ℝ) ≤ Real.exp (-33289/2097152 : ℝ) ∧ Real.exp (-33289/2097152 : ℝ) ≤ (123031485851/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984251886807/1000000000000 : ℝ) ≤ (radius 8 (33289/262144 : ℝ)) ∧ (radius 8 (33289/262144 : ℝ)) ≤ (123031485851/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33289/262144 : ℝ)) (984251886807/1000000000000 : ℝ) (123031485851/125000000000 : ℝ) (17677167/100000000 : ℝ) (176771670007/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33289/262144 : ℝ)) (984251886807/1000000000000 : ℝ) (123031485851/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33289/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984251886807/1000000000000 : ℝ) (123031485851/125000000000 : ℝ) (992125943403/1000000000000 : ℝ) (248031485851/250000000000 : ℝ) (992094696491/1000000000000 : ℝ) (992094696493/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33289/262144 : ℝ)) 1 (992125943403/1000000000000 : ℝ) (248031485851/250000000000 : ℝ) (992094696491/1000000000000 : ℝ) (992094696493/1000000000000 : ℝ) (992110319947/1000000000000 : ℝ) (992110319949/1000000000000 : ℝ) (992110319823/1000000000000 : ℝ) (496055159913/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33289/262144 : ℝ)) 2 (992110319947/1000000000000 : ℝ) (992110319949/1000000000000 : ℝ) (992110319823/1000000000000 : ℝ) (496055159913/500000000000 : ℝ) (198422063977/200000000000 : ℝ) (62006894993/62500000000 : ℝ) (248027579971/250000000000 : ℝ) (62006894993/62500000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33289/262144 : ℝ)) 3 (198422063977/200000000000 : ℝ) (62006894993/62500000000 : ℝ) (248027579971/250000000000 : ℝ) (62006894993/62500000000 : ℝ) (248027579971/250000000000 : ℝ) (62006894993/62500000000 : ℝ) (248027579971/250000000000 : ℝ) (62006894993/62500000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33289/262144 : ℝ)) 4 (248027579971/250000000000 : ℝ) (62006894993/62500000000 : ℝ) (248027579971/250000000000 : ℝ) (62006894993/62500000000 : ℝ) (248027579971/250000000000 : ℝ) (62006894993/62500000000 : ℝ) (248027579971/250000000000 : ℝ) (62006894993/62500000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33289/262144 : ℝ)) 5 (248027579971/250000000000 : ℝ) (62006894993/62500000000 : ℝ) (248027579971/250000000000 : ℝ) (62006894993/62500000000 : ℝ) (248027579971/250000000000 : ℝ) (62006894993/62500000000 : ℝ) (248027579971/250000000000 : ℝ) (62006894993/62500000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33289/262144 : ℝ)) 6 (248027579971/250000000000 : ℝ) (62006894993/62500000000 : ℝ) (248027579971/250000000000 : ℝ) (62006894993/62500000000 : ℝ) (248027579971/250000000000 : ℝ) (62006894993/62500000000 : ℝ) (248027579971/250000000000 : ℝ) (62006894993/62500000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33289/262144 : ℝ)) 7 (248027579971/250000000000 : ℝ) (62006894993/62500000000 : ℝ) (248027579971/250000000000 : ℝ) (62006894993/62500000000 : ℝ) (248027579971/250000000000 : ℝ) (62006894993/62500000000 : ℝ) (248027579971/250000000000 : ℝ) (62006894993/62500000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33289/262144 : ℝ))) (17677167/100000000 : ℝ) (176771670007/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33289/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (17677167/100000000 : ℝ) (176771670007/1000000000000 : ℝ) (117677167/200000000 : ℝ) (147096458751/250000000000 : ℝ) (84088446293/200000000000 : ℝ) (16817689259/40000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33289/262144 : ℝ))) 1 (117677167/200000000 : ℝ) (147096458751/250000000000 : ℝ) (84088446293/200000000000 : ℝ) (16817689259/40000000000 : ℝ) (31525877077/62500000000 : ℝ) (12610350831/25000000000 : ℝ) (497375364719/1000000000000 : ℝ) (62171920591/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33289/262144 : ℝ))) 2 (31525877077/62500000000 : ℝ) (12610350831/25000000000 : ℝ) (497375364719/1000000000000 : ℝ) (62171920591/125000000000 : ℝ) (20035787959/40000000000 : ℝ) (62611837373/125000000000 : ℝ) (978285811/1953125000 : ℝ) (250441167621/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33289/262144 : ℝ))) 3 (20035787959/40000000000 : ℝ) (62611837373/125000000000 : ℝ) (978285811/1953125000 : ℝ) (250441167621/500000000000 : ℝ) (500888517103/1000000000000 : ℝ) (500888517113/1000000000000 : ℝ) (100177703413/200000000000 : ℝ) (20035540683/40000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33289/262144 : ℝ))) 4 (500888517103/1000000000000 : ℝ) (500888517113/1000000000000 : ℝ) (100177703413/200000000000 : ℝ) (20035540683/40000000000 : ℝ) (125222129271/250000000000 : ℝ) (250444258547/500000000000 : ℝ) (500888517083/1000000000000 : ℝ) (250444258547/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33289/262144 : ℝ))) 5 (125222129271/250000000000 : ℝ) (250444258547/500000000000 : ℝ) (500888517083/1000000000000 : ℝ) (250444258547/500000000000 : ℝ) (500888517083/1000000000000 : ℝ) (250444258547/500000000000 : ℝ) (500888517083/1000000000000 : ℝ) (250444258547/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33289/262144 : ℝ))) 6 (500888517083/1000000000000 : ℝ) (250444258547/500000000000 : ℝ) (500888517083/1000000000000 : ℝ) (250444258547/500000000000 : ℝ) (500888517083/1000000000000 : ℝ) (250444258547/500000000000 : ℝ) (500888517083/1000000000000 : ℝ) (250444258547/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33289/262144 : ℝ))) 7 (500888517083/1000000000000 : ℝ) (250444258547/500000000000 : ℝ) (500888517083/1000000000000 : ℝ) (250444258547/500000000000 : ℝ) (500888517083/1000000000000 : ℝ) (250444258547/500000000000 : ℝ) (500888517083/1000000000000 : ℝ) (250444258547/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33289/262144 : ℝ)) hmem 8 (248027579971/250000000000 : ℝ) (62006894993/62500000000 : ℝ) (248027579971/250000000000 : ℝ) (62006894993/62500000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33289/262144 : ℝ))) hcmem 8 (500888517083/1000000000000 : ℝ) (250444258547/500000000000 : ℝ) (500888517083/1000000000000 : ℝ) (250444258547/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33289/262144 : ℝ)) (248027579971/250000000000 : ℝ) (62006894993/62500000000 : ℝ) (500888517083/1000000000000 : ℝ) (250444258547/500000000000 : ℝ) (793050759573/1000000000000 : ℝ) (396525379797/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0508_exp_lower
  have heNumeric : (2054900121527/1000000000000 : ℝ)/4 ≤ Real.exp (-5328536936127/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054900121527/1000000000000 : ℝ)/4 ≤ Real.exp ((4161/32768 : ℝ)-(396525379797/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4161/32768 : ℝ) (33289/262144 : ℝ) (396525379797/500000000000 : ℝ) (2054900121527/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0509; no trusted numerical premise.
theorem cover8_leaf0509_exp_radius : (12475221608443427/12500000000000000 : ℝ) ≤ Real.exp ((-16645/1048576 : ℝ)/8) ∧ Real.exp ((-16645/1048576 : ℝ)/8) ≤ (998017728675474161/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16645/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0509_exp_lower : (92011336717107351/100000000000000000 : ℝ) ≤ Real.exp ((-42628296368487/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628296368487/64000000000000 : ℝ)/8) ≤ (920113367171073511/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628296368487/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0509_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054900093289/1000000000000 : ℝ) ≤ 4*Real.exp (33289/262144 : ℝ)*Real.exp (-mu (radius 8 (16645/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054900093289/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16645/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0509_exp_radius
  have hrNumeric : (24606285437/25000000000 : ℝ) ≤ Real.exp (-16645/1048576 : ℝ) ∧ Real.exp (-16645/1048576 : ℝ) ≤ (984251417481/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (24606285437/25000000000 : ℝ) ≤ (radius 8 (16645/131072 : ℝ)) ∧ (radius 8 (16645/131072 : ℝ)) ≤ (984251417481/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16645/131072 : ℝ)) (24606285437/25000000000 : ℝ) (984251417481/1000000000000 : ℝ) (176774283159/1000000000000 : ℝ) (88387141583/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16645/131072 : ℝ)) (24606285437/25000000000 : ℝ) (984251417481/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16645/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (24606285437/25000000000 : ℝ) (984251417481/1000000000000 : ℝ) (49606285437/50000000000 : ℝ) (992125708741/1000000000000 : ℝ) (496047229979/500000000000 : ℝ) (992094459959/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16645/131072 : ℝ)) 1 (49606285437/50000000000 : ℝ) (992125708741/1000000000000 : ℝ) (496047229979/500000000000 : ℝ) (992094459959/1000000000000 : ℝ) (992110084349/1000000000000 : ℝ) (19842201687/20000000000 : ℝ) (39684403369/40000000000 : ℝ) (992110084227/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16645/131072 : ℝ)) 2 (992110084349/1000000000000 : ℝ) (19842201687/20000000000 : ℝ) (39684403369/40000000000 : ℝ) (992110084227/1000000000000 : ℝ) (992110084287/1000000000000 : ℝ) (992110084289/1000000000000 : ℝ) (496055042143/500000000000 : ℝ) (992110084289/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16645/131072 : ℝ)) 3 (992110084287/1000000000000 : ℝ) (992110084289/1000000000000 : ℝ) (496055042143/500000000000 : ℝ) (992110084289/1000000000000 : ℝ) (496055042143/500000000000 : ℝ) (992110084289/1000000000000 : ℝ) (496055042143/500000000000 : ℝ) (992110084289/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16645/131072 : ℝ)) 4 (496055042143/500000000000 : ℝ) (992110084289/1000000000000 : ℝ) (496055042143/500000000000 : ℝ) (992110084289/1000000000000 : ℝ) (496055042143/500000000000 : ℝ) (992110084289/1000000000000 : ℝ) (496055042143/500000000000 : ℝ) (992110084289/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16645/131072 : ℝ)) 5 (496055042143/500000000000 : ℝ) (992110084289/1000000000000 : ℝ) (496055042143/500000000000 : ℝ) (992110084289/1000000000000 : ℝ) (496055042143/500000000000 : ℝ) (992110084289/1000000000000 : ℝ) (496055042143/500000000000 : ℝ) (992110084289/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16645/131072 : ℝ)) 6 (496055042143/500000000000 : ℝ) (992110084289/1000000000000 : ℝ) (496055042143/500000000000 : ℝ) (992110084289/1000000000000 : ℝ) (496055042143/500000000000 : ℝ) (992110084289/1000000000000 : ℝ) (496055042143/500000000000 : ℝ) (992110084289/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16645/131072 : ℝ)) 7 (496055042143/500000000000 : ℝ) (992110084289/1000000000000 : ℝ) (496055042143/500000000000 : ℝ) (992110084289/1000000000000 : ℝ) (496055042143/500000000000 : ℝ) (992110084289/1000000000000 : ℝ) (496055042143/500000000000 : ℝ) (992110084289/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16645/131072 : ℝ))) (176774283159/1000000000000 : ℝ) (88387141583/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16645/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176774283159/1000000000000 : ℝ) (88387141583/500000000000 : ℝ) (588387141579/1000000000000 : ℝ) (588387141583/1000000000000 : ℝ) (84089067817/200000000000 : ℝ) (84089067819/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16645/131072 : ℝ))) 1 (588387141579/1000000000000 : ℝ) (588387141583/1000000000000 : ℝ) (84089067817/200000000000 : ℝ) (84089067819/200000000000 : ℝ) (126104060083/250000000000 : ℝ) (504416240339/1000000000000 : ℝ) (248688877543/500000000000 : ℝ) (248688877547/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16645/131072 : ℝ))) 2 (126104060083/250000000000 : ℝ) (504416240339/1000000000000 : ℝ) (248688877543/500000000000 : ℝ) (248688877547/500000000000 : ℝ) (500896997709/1000000000000 : ℝ) (500896997717/1000000000000 : ℝ) (250442317333/500000000000 : ℝ) (20035385387/40000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16645/131072 : ℝ))) 3 (500896997709/1000000000000 : ℝ) (500896997717/1000000000000 : ℝ) (250442317333/500000000000 : ℝ) (20035385387/40000000000 : ℝ) (500890816187/1000000000000 : ℝ) (125222704049/250000000000 : ℝ) (500890816149/1000000000000 : ℝ) (250445408079/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16645/131072 : ℝ))) 4 (500890816187/1000000000000 : ℝ) (125222704049/250000000000 : ℝ) (500890816149/1000000000000 : ℝ) (250445408079/500000000000 : ℝ) (62611352021/125000000000 : ℝ) (500890816177/1000000000000 : ℝ) (500890816167/1000000000000 : ℝ) (500890816177/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16645/131072 : ℝ))) 5 (62611352021/125000000000 : ℝ) (500890816177/1000000000000 : ℝ) (500890816167/1000000000000 : ℝ) (500890816177/1000000000000 : ℝ) (500890816167/1000000000000 : ℝ) (500890816177/1000000000000 : ℝ) (500890816167/1000000000000 : ℝ) (500890816177/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16645/131072 : ℝ))) 6 (500890816167/1000000000000 : ℝ) (500890816177/1000000000000 : ℝ) (500890816167/1000000000000 : ℝ) (500890816177/1000000000000 : ℝ) (500890816167/1000000000000 : ℝ) (500890816177/1000000000000 : ℝ) (500890816167/1000000000000 : ℝ) (500890816177/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16645/131072 : ℝ))) 7 (500890816167/1000000000000 : ℝ) (500890816177/1000000000000 : ℝ) (500890816167/1000000000000 : ℝ) (500890816177/1000000000000 : ℝ) (500890816167/1000000000000 : ℝ) (500890816177/1000000000000 : ℝ) (500890816167/1000000000000 : ℝ) (500890816177/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16645/131072 : ℝ)) hmem 8 (496055042143/500000000000 : ℝ) (992110084289/1000000000000 : ℝ) (496055042143/500000000000 : ℝ) (992110084289/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16645/131072 : ℝ))) hcmem 8 (500890816167/1000000000000 : ℝ) (500890816177/1000000000000 : ℝ) (500890816167/1000000000000 : ℝ) (500890816177/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16645/131072 : ℝ)) (496055042143/500000000000 : ℝ) (992110084289/1000000000000 : ℝ) (500890816167/1000000000000 : ℝ) (500890816177/1000000000000 : ℝ) (396527294007/500000000000 : ℝ) (793054588033/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0509_exp_lower
  have heNumeric : (2054900093289/1000000000000 : ℝ)/4 ≤ Real.exp (-42628296368487/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054900093289/1000000000000 : ℝ)/4 ≤ Real.exp ((33289/262144 : ℝ)-(793054588033/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33289/262144 : ℝ) (16645/131072 : ℝ) (793054588033/1000000000000 : ℝ) (2054900093289/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0510; no trusted numerical premise.
theorem cover8_leaf0510_exp_radius : (124752208648622967/125000000000000000 : ℝ) ≤ Real.exp ((-33291/2097152 : ℝ)/8) ∧ Real.exp ((-33291/2097152 : ℝ)/8) ≤ (998017669188983737/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33291/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0510_exp_lower : (920113365598400289/1000000000000000000 : ℝ) ≤ Real.exp ((-21314148621803/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314148621803/32000000000000 : ℝ)/8) ≤ (92011336559840029/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314148621803/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0510_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054900065191/1000000000000 : ℝ) ≤ 4*Real.exp (16645/131072 : ℝ)*Real.exp (-mu (radius 8 (33291/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054900065191/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33291/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0510_exp_radius
  have hrNumeric : (123031368519/125000000000 : ℝ) ≤ Real.exp (-33291/2097152 : ℝ) ∧ Real.exp (-33291/2097152 : ℝ) ≤ (984250948153/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (123031368519/125000000000 : ℝ) ≤ (radius 8 (33291/262144 : ℝ)) ∧ (radius 8 (33291/262144 : ℝ)) ≤ (984250948153/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33291/262144 : ℝ)) (123031368519/125000000000 : ℝ) (984250948153/1000000000000 : ℝ) (44194224071/250000000000 : ℝ) (17677689629/100000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33291/262144 : ℝ)) (123031368519/125000000000 : ℝ) (984250948153/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33291/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (123031368519/125000000000 : ℝ) (984250948153/1000000000000 : ℝ) (248031368519/250000000000 : ℝ) (992125474077/1000000000000 : ℝ) (15501472241/15625000000 : ℝ) (39683768937/40000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33291/262144 : ℝ)) 1 (248031368519/250000000000 : ℝ) (992125474077/1000000000000 : ℝ) (15501472241/15625000000 : ℝ) (39683768937/40000000000 : ℝ) (793687879/800000000 : ℝ) (992109848751/1000000000000 : ℝ) (496054924313/500000000000 : ℝ) (248027462157/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33291/262144 : ℝ)) 2 (793687879/800000000 : ℝ) (992109848751/1000000000000 : ℝ) (496054924313/500000000000 : ℝ) (248027462157/250000000000 : ℝ) (62006865543/62500000000 : ℝ) (99210984869/100000000000 : ℝ) (992109848687/1000000000000 : ℝ) (99210984869/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33291/262144 : ℝ)) 3 (62006865543/62500000000 : ℝ) (99210984869/100000000000 : ℝ) (992109848687/1000000000000 : ℝ) (99210984869/100000000000 : ℝ) (992109848687/1000000000000 : ℝ) (99210984869/100000000000 : ℝ) (992109848687/1000000000000 : ℝ) (99210984869/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33291/262144 : ℝ)) 4 (992109848687/1000000000000 : ℝ) (99210984869/100000000000 : ℝ) (992109848687/1000000000000 : ℝ) (99210984869/100000000000 : ℝ) (992109848687/1000000000000 : ℝ) (99210984869/100000000000 : ℝ) (992109848687/1000000000000 : ℝ) (99210984869/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33291/262144 : ℝ)) 5 (992109848687/1000000000000 : ℝ) (99210984869/100000000000 : ℝ) (992109848687/1000000000000 : ℝ) (99210984869/100000000000 : ℝ) (992109848687/1000000000000 : ℝ) (99210984869/100000000000 : ℝ) (992109848687/1000000000000 : ℝ) (99210984869/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33291/262144 : ℝ)) 6 (992109848687/1000000000000 : ℝ) (99210984869/100000000000 : ℝ) (992109848687/1000000000000 : ℝ) (99210984869/100000000000 : ℝ) (992109848687/1000000000000 : ℝ) (99210984869/100000000000 : ℝ) (992109848687/1000000000000 : ℝ) (99210984869/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33291/262144 : ℝ)) 7 (992109848687/1000000000000 : ℝ) (99210984869/100000000000 : ℝ) (992109848687/1000000000000 : ℝ) (99210984869/100000000000 : ℝ) (992109848687/1000000000000 : ℝ) (99210984869/100000000000 : ℝ) (992109848687/1000000000000 : ℝ) (99210984869/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33291/262144 : ℝ))) (44194224071/250000000000 : ℝ) (17677689629/100000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33291/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44194224071/250000000000 : ℝ) (17677689629/100000000000 : ℝ) (294194224071/500000000000 : ℝ) (117677689629/200000000000 : ℝ) (210224223321/500000000000 : ℝ) (8408968933/20000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33291/262144 : ℝ))) 1 (294194224071/500000000000 : ℝ) (117677689629/200000000000 : ℝ) (210224223321/500000000000 : ℝ) (8408968933/20000000000 : ℝ) (15763076481/31250000000 : ℝ) (252209223699/500000000000 : ℝ) (99476029081/200000000000 : ℝ) (124345036353/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33291/262144 : ℝ))) 2 (15763076481/31250000000 : ℝ) (252209223699/500000000000 : ℝ) (99476029081/200000000000 : ℝ) (124345036353/250000000000 : ℝ) (250449648199/500000000000 : ℝ) (100179859281/200000000000 : ℝ) (62610866757/125000000000 : ℝ) (31305433379/62500000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33291/262144 : ℝ))) 3 (250449648199/500000000000 : ℝ) (100179859281/200000000000 : ℝ) (62610866757/125000000000 : ℝ) (31305433379/62500000000 : ℝ) (500893115227/1000000000000 : ℝ) (100178623047/200000000000 : ℝ) (125223278797/250000000000 : ℝ) (500893115197/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33291/262144 : ℝ))) 4 (500893115227/1000000000000 : ℝ) (100178623047/200000000000 : ℝ) (125223278797/250000000000 : ℝ) (500893115197/1000000000000 : ℝ) (500893115207/1000000000000 : ℝ) (31305819701/62500000000 : ℝ) (500893115207/1000000000000 : ℝ) (31305819701/62500000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33291/262144 : ℝ))) 5 (500893115207/1000000000000 : ℝ) (31305819701/62500000000 : ℝ) (500893115207/1000000000000 : ℝ) (31305819701/62500000000 : ℝ) (500893115207/1000000000000 : ℝ) (31305819701/62500000000 : ℝ) (500893115207/1000000000000 : ℝ) (31305819701/62500000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33291/262144 : ℝ))) 6 (500893115207/1000000000000 : ℝ) (31305819701/62500000000 : ℝ) (500893115207/1000000000000 : ℝ) (31305819701/62500000000 : ℝ) (500893115207/1000000000000 : ℝ) (31305819701/62500000000 : ℝ) (500893115207/1000000000000 : ℝ) (31305819701/62500000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33291/262144 : ℝ))) 7 (500893115207/1000000000000 : ℝ) (31305819701/62500000000 : ℝ) (500893115207/1000000000000 : ℝ) (31305819701/62500000000 : ℝ) (500893115207/1000000000000 : ℝ) (31305819701/62500000000 : ℝ) (500893115207/1000000000000 : ℝ) (31305819701/62500000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33291/262144 : ℝ)) hmem 8 (992109848687/1000000000000 : ℝ) (99210984869/100000000000 : ℝ) (992109848687/1000000000000 : ℝ) (99210984869/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33291/262144 : ℝ))) hcmem 8 (500893115207/1000000000000 : ℝ) (31305819701/62500000000 : ℝ) (500893115207/1000000000000 : ℝ) (31305819701/62500000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33291/262144 : ℝ)) (992109848687/1000000000000 : ℝ) (99210984869/100000000000 : ℝ) (500893115207/1000000000000 : ℝ) (31305819701/62500000000 : ℝ) (396529208193/500000000000 : ℝ) (198264604101/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0510_exp_lower
  have heNumeric : (2054900065191/1000000000000 : ℝ)/4 ≤ Real.exp (-21314148621803/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054900065191/1000000000000 : ℝ)/4 ≤ Real.exp ((16645/131072 : ℝ)-(198264604101/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16645/131072 : ℝ) (33291/262144 : ℝ) (198264604101/250000000000 : ℝ) (2054900065191/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0511; no trusted numerical premise.
theorem cover8_leaf0511_exp_radius : (998017609702496857/1000000000000000000 : ℝ) ≤ Real.exp ((-8323/524288 : ℝ)/8) ∧ Real.exp ((-8323/524288 : ℝ)/8) ≤ (499008804851248429/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8323/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0511_exp_lower : (920113364035273247/1000000000000000000 : ℝ) ≤ Real.exp ((-42628298113413/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628298113413/64000000000000 : ℝ)/8) ≤ (28753542626102289/31250000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628298113413/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0511_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054900037263/1000000000000 : ℝ) ≤ 4*Real.exp (33291/262144 : ℝ)*Real.exp (-mu (radius 8 (8323/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (2054900037263/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8323/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0511_exp_radius
  have hrNumeric : (39370019153/40000000000 : ℝ) ≤ Real.exp (-8323/524288 : ℝ) ∧ Real.exp (-8323/524288 : ℝ) ≤ (492125239413/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (39370019153/40000000000 : ℝ) ≤ (radius 8 (8323/65536 : ℝ)) ∧ (radius 8 (8323/65536 : ℝ)) ≤ (492125239413/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8323/65536 : ℝ)) (39370019153/40000000000 : ℝ) (492125239413/500000000000 : ℝ) (176779509363/1000000000000 : ℝ) (17677950937/100000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8323/65536 : ℝ)) (39370019153/40000000000 : ℝ) (492125239413/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8323/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (39370019153/40000000000 : ℝ) (492125239413/500000000000 : ℝ) (248031309853/250000000000 : ℝ) (992125239413/1000000000000 : ℝ) (99209398689/100000000000 : ℝ) (248023496723/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8323/65536 : ℝ)) 1 (248031309853/250000000000 : ℝ) (992125239413/1000000000000 : ℝ) (99209398689/100000000000 : ℝ) (248023496723/250000000000 : ℝ) (992109613151/1000000000000 : ℝ) (992109613153/1000000000000 : ℝ) (992109613027/1000000000000 : ℝ) (99210961303/100000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8323/65536 : ℝ)) 2 (992109613151/1000000000000 : ℝ) (992109613153/1000000000000 : ℝ) (992109613027/1000000000000 : ℝ) (99210961303/100000000000 : ℝ) (992109613089/1000000000000 : ℝ) (248027403273/250000000000 : ℝ) (31003425409/31250000000 : ℝ) (248027403273/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8323/65536 : ℝ)) 3 (992109613089/1000000000000 : ℝ) (248027403273/250000000000 : ℝ) (31003425409/31250000000 : ℝ) (248027403273/250000000000 : ℝ) (31003425409/31250000000 : ℝ) (248027403273/250000000000 : ℝ) (31003425409/31250000000 : ℝ) (248027403273/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8323/65536 : ℝ)) 4 (31003425409/31250000000 : ℝ) (248027403273/250000000000 : ℝ) (31003425409/31250000000 : ℝ) (248027403273/250000000000 : ℝ) (31003425409/31250000000 : ℝ) (248027403273/250000000000 : ℝ) (31003425409/31250000000 : ℝ) (248027403273/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8323/65536 : ℝ)) 5 (31003425409/31250000000 : ℝ) (248027403273/250000000000 : ℝ) (31003425409/31250000000 : ℝ) (248027403273/250000000000 : ℝ) (31003425409/31250000000 : ℝ) (248027403273/250000000000 : ℝ) (31003425409/31250000000 : ℝ) (248027403273/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8323/65536 : ℝ)) 6 (31003425409/31250000000 : ℝ) (248027403273/250000000000 : ℝ) (31003425409/31250000000 : ℝ) (248027403273/250000000000 : ℝ) (31003425409/31250000000 : ℝ) (248027403273/250000000000 : ℝ) (31003425409/31250000000 : ℝ) (248027403273/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8323/65536 : ℝ)) 7 (31003425409/31250000000 : ℝ) (248027403273/250000000000 : ℝ) (31003425409/31250000000 : ℝ) (248027403273/250000000000 : ℝ) (31003425409/31250000000 : ℝ) (248027403273/250000000000 : ℝ) (31003425409/31250000000 : ℝ) (248027403273/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8323/65536 : ℝ))) (176779509363/1000000000000 : ℝ) (17677950937/100000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8323/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176779509363/1000000000000 : ℝ) (17677950937/100000000000 : ℝ) (588389754681/1000000000000 : ℝ) (117677950937/200000000000 : ℝ) (420451554121/1000000000000 : ℝ) (42045155413/100000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8323/65536 : ℝ))) 1 (588389754681/1000000000000 : ℝ) (117677950937/200000000000 : ℝ) (420451554121/1000000000000 : ℝ) (42045155413/100000000000 : ℝ) (504420654401/1000000000000 : ℝ) (63052581801/125000000000 : ℝ) (31086408479/62500000000 : ℝ) (62172816959/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8323/65536 : ℝ))) 2 (504420654401/1000000000000 : ℝ) (63052581801/125000000000 : ℝ) (31086408479/62500000000 : ℝ) (62172816959/125000000000 : ℝ) (62612699379/125000000000 : ℝ) (3130634969/6250000000 : ℝ) (500889233391/1000000000000 : ℝ) (500889233399/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8323/65536 : ℝ))) 3 (62612699379/125000000000 : ℝ) (3130634969/6250000000 : ℝ) (500889233391/1000000000000 : ℝ) (500889233399/1000000000000 : ℝ) (500895414211/1000000000000 : ℝ) (25044770711/50000000000 : ℝ) (500895414173/1000000000000 : ℝ) (250447707091/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8323/65536 : ℝ))) 4 (500895414211/1000000000000 : ℝ) (25044770711/50000000000 : ℝ) (500895414173/1000000000000 : ℝ) (250447707091/500000000000 : ℝ) (31305963387/62500000000 : ℝ) (500895414201/1000000000000 : ℝ) (500895414191/1000000000000 : ℝ) (500895414201/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8323/65536 : ℝ))) 5 (31305963387/62500000000 : ℝ) (500895414201/1000000000000 : ℝ) (500895414191/1000000000000 : ℝ) (500895414201/1000000000000 : ℝ) (500895414191/1000000000000 : ℝ) (500895414201/1000000000000 : ℝ) (500895414191/1000000000000 : ℝ) (500895414201/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8323/65536 : ℝ))) 6 (500895414191/1000000000000 : ℝ) (500895414201/1000000000000 : ℝ) (500895414191/1000000000000 : ℝ) (500895414201/1000000000000 : ℝ) (500895414191/1000000000000 : ℝ) (500895414201/1000000000000 : ℝ) (500895414191/1000000000000 : ℝ) (500895414201/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8323/65536 : ℝ))) 7 (500895414191/1000000000000 : ℝ) (500895414201/1000000000000 : ℝ) (500895414191/1000000000000 : ℝ) (500895414201/1000000000000 : ℝ) (500895414191/1000000000000 : ℝ) (500895414201/1000000000000 : ℝ) (500895414191/1000000000000 : ℝ) (500895414201/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8323/65536 : ℝ)) hmem 8 (31003425409/31250000000 : ℝ) (248027403273/250000000000 : ℝ) (31003425409/31250000000 : ℝ) (248027403273/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8323/65536 : ℝ))) hcmem 8 (500895414191/1000000000000 : ℝ) (500895414201/1000000000000 : ℝ) (500895414191/1000000000000 : ℝ) (500895414201/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8323/65536 : ℝ)) (31003425409/31250000000 : ℝ) (248027403273/250000000000 : ℝ) (500895414191/1000000000000 : ℝ) (500895414201/1000000000000 : ℝ) (12391597573/15625000000 : ℝ) (198265561173/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0511_exp_lower
  have heNumeric : (2054900037263/1000000000000 : ℝ)/4 ≤ Real.exp (-42628298113413/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054900037263/1000000000000 : ℝ)/4 ≤ Real.exp ((33291/262144 : ℝ)-(198265561173/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33291/262144 : ℝ) (8323/65536 : ℝ) (198265561173/250000000000 : ℝ) (2054900037263/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0512; no trusted numerical premise.
theorem cover8_leaf0512_exp_radius : (998017579959254747/1000000000000000000 : ℝ) ≤ Real.exp ((-66585/4194304 : ℝ)/8) ∧ Real.exp ((-66585/4194304 : ℝ)/8) ≤ (249504394989813687/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66585/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0512_exp_lower : (920113582628731913/1000000000000000000 : ℝ) ≤ Real.exp ((-10657044119101/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657044119101/16000000000000 : ℝ)/8) ≤ (460056791314365957/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657044119101/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0512_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410980788553/200000000000 : ℝ) ≤ 4*Real.exp (8323/65536 : ℝ)*Real.exp (-mu (radius 8 (66585/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (410980788553/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66585/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0512_exp_radius
  have hrNumeric : (984250244161/1000000000000 : ℝ) ≤ Real.exp (-66585/4194304 : ℝ) ∧ Real.exp (-66585/4194304 : ℝ) ≤ (492125122081/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984250244161/1000000000000 : ℝ) ≤ (radius 8 (66585/524288 : ℝ)) ∧ (radius 8 (66585/524288 : ℝ)) ≤ (492125122081/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66585/524288 : ℝ)) (984250244161/1000000000000 : ℝ) (492125122081/500000000000 : ℝ) (17678081589/100000000000 : ℝ) (176780815897/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66585/524288 : ℝ)) (984250244161/1000000000000 : ℝ) (492125122081/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66585/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984250244161/1000000000000 : ℝ) (492125122081/500000000000 : ℝ) (6200782013/6250000000 : ℝ) (992125122081/1000000000000 : ℝ) (992093868623/1000000000000 : ℝ) (7936750949/8000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66585/524288 : ℝ)) 1 (6200782013/6250000000 : ℝ) (992125122081/1000000000000 : ℝ) (992093868623/1000000000000 : ℝ) (7936750949/8000000000 : ℝ) (992109495351/1000000000000 : ℝ) (992109495353/1000000000000 : ℝ) (248027373807/250000000000 : ℝ) (99210949523/100000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66585/524288 : ℝ)) 2 (992109495351/1000000000000 : ℝ) (992109495353/1000000000000 : ℝ) (248027373807/250000000000 : ℝ) (99210949523/100000000000 : ℝ) (992109495289/1000000000000 : ℝ) (248027373823/250000000000 : ℝ) (992109495289/1000000000000 : ℝ) (248027373823/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66585/524288 : ℝ)) 3 (992109495289/1000000000000 : ℝ) (248027373823/250000000000 : ℝ) (992109495289/1000000000000 : ℝ) (248027373823/250000000000 : ℝ) (992109495289/1000000000000 : ℝ) (248027373823/250000000000 : ℝ) (992109495289/1000000000000 : ℝ) (248027373823/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66585/524288 : ℝ)) 4 (992109495289/1000000000000 : ℝ) (248027373823/250000000000 : ℝ) (992109495289/1000000000000 : ℝ) (248027373823/250000000000 : ℝ) (992109495289/1000000000000 : ℝ) (248027373823/250000000000 : ℝ) (992109495289/1000000000000 : ℝ) (248027373823/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66585/524288 : ℝ)) 5 (992109495289/1000000000000 : ℝ) (248027373823/250000000000 : ℝ) (992109495289/1000000000000 : ℝ) (248027373823/250000000000 : ℝ) (992109495289/1000000000000 : ℝ) (248027373823/250000000000 : ℝ) (992109495289/1000000000000 : ℝ) (248027373823/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66585/524288 : ℝ)) 6 (992109495289/1000000000000 : ℝ) (248027373823/250000000000 : ℝ) (992109495289/1000000000000 : ℝ) (248027373823/250000000000 : ℝ) (992109495289/1000000000000 : ℝ) (248027373823/250000000000 : ℝ) (992109495289/1000000000000 : ℝ) (248027373823/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66585/524288 : ℝ)) 7 (992109495289/1000000000000 : ℝ) (248027373823/250000000000 : ℝ) (992109495289/1000000000000 : ℝ) (248027373823/250000000000 : ℝ) (992109495289/1000000000000 : ℝ) (248027373823/250000000000 : ℝ) (992109495289/1000000000000 : ℝ) (248027373823/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66585/524288 : ℝ))) (17678081589/100000000000 : ℝ) (176780815897/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66585/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (17678081589/100000000000 : ℝ) (176780815897/1000000000000 : ℝ) (117678081589/200000000000 : ℝ) (588390407949/1000000000000 : ℝ) (420453107837/1000000000000 : ℝ) (210226553923/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66585/524288 : ℝ))) 1 (117678081589/200000000000 : ℝ) (588390407949/1000000000000 : ℝ) (420453107837/1000000000000 : ℝ) (210226553923/500000000000 : ℝ) (504421757891/1000000000000 : ℝ) (252210878949/500000000000 : ℝ) (497383730777/1000000000000 : ℝ) (99476746157/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66585/524288 : ℝ))) 2 (504421757891/1000000000000 : ℝ) (252210878949/500000000000 : ℝ) (497383730777/1000000000000 : ℝ) (99476746157/200000000000 : ℝ) (250451372167/500000000000 : ℝ) (250451372171/500000000000 : ℝ) (250445191521/500000000000 : ℝ) (500890383051/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66585/524288 : ℝ))) 3 (250451372167/500000000000 : ℝ) (250451372171/500000000000 : ℝ) (250445191521/500000000000 : ℝ) (500890383051/1000000000000 : ℝ) (62612070461/125000000000 : ℝ) (500896563697/1000000000000 : ℝ) (500896563649/1000000000000 : ℝ) (500896563659/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66585/524288 : ℝ))) 4 (62612070461/125000000000 : ℝ) (500896563697/1000000000000 : ℝ) (500896563649/1000000000000 : ℝ) (500896563659/1000000000000 : ℝ) (125224140917/250000000000 : ℝ) (250448281839/500000000000 : ℝ) (125224140917/250000000000 : ℝ) (250448281839/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66585/524288 : ℝ))) 5 (125224140917/250000000000 : ℝ) (250448281839/500000000000 : ℝ) (125224140917/250000000000 : ℝ) (250448281839/500000000000 : ℝ) (125224140917/250000000000 : ℝ) (250448281839/500000000000 : ℝ) (125224140917/250000000000 : ℝ) (250448281839/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66585/524288 : ℝ))) 6 (125224140917/250000000000 : ℝ) (250448281839/500000000000 : ℝ) (125224140917/250000000000 : ℝ) (250448281839/500000000000 : ℝ) (125224140917/250000000000 : ℝ) (250448281839/500000000000 : ℝ) (125224140917/250000000000 : ℝ) (250448281839/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66585/524288 : ℝ))) 7 (125224140917/250000000000 : ℝ) (250448281839/500000000000 : ℝ) (125224140917/250000000000 : ℝ) (250448281839/500000000000 : ℝ) (125224140917/250000000000 : ℝ) (250448281839/500000000000 : ℝ) (125224140917/250000000000 : ℝ) (250448281839/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66585/524288 : ℝ)) hmem 8 (992109495289/1000000000000 : ℝ) (248027373823/250000000000 : ℝ) (992109495289/1000000000000 : ℝ) (248027373823/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66585/524288 : ℝ))) hcmem 8 (125224140917/250000000000 : ℝ) (250448281839/500000000000 : ℝ) (125224140917/250000000000 : ℝ) (250448281839/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66585/524288 : ℝ)) (992109495289/1000000000000 : ℝ) (248027373823/250000000000 : ℝ) (125224140917/250000000000 : ℝ) (250448281839/500000000000 : ℝ) (99133019849/125000000000 : ℝ) (793064158811/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0512_exp_lower
  have heNumeric : (410980788553/200000000000 : ℝ)/4 ≤ Real.exp (-10657044119101/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410980788553/200000000000 : ℝ)/4 ≤ Real.exp ((8323/65536 : ℝ)-(793064158811/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8323/65536 : ℝ) (66585/524288 : ℝ) (793064158811/1000000000000 : ℝ) (410980788553/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0513; no trusted numerical premise.
theorem cover8_leaf0513_exp_radius : (249504387554003381/250000000000000000 : ℝ) ≤ Real.exp ((-33293/2097152 : ℝ)/8) ∧ Real.exp ((-33293/2097152 : ℝ)/8) ≤ (39920702008640541/40000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33293/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0513_exp_lower : (184022716370629789/200000000000000000 : ℝ) ≤ Real.exp ((-85256353815959/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256353815959/128000000000000 : ℝ)/8) ≤ (460056790926574473/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256353815959/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0513_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513725982227/250000000000 : ℝ) ≤ 4*Real.exp (66585/524288 : ℝ)*Real.exp (-mu (radius 8 (33293/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (513725982227/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33293/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0513_exp_radius
  have hrNumeric : (492125004749/500000000000 : ℝ) ≤ Real.exp (-33293/2097152 : ℝ) ∧ Real.exp (-33293/2097152 : ℝ) ≤ (984250009499/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492125004749/500000000000 : ℝ) ≤ (radius 8 (33293/262144 : ℝ)) ∧ (radius 8 (33293/262144 : ℝ)) ≤ (984250009499/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33293/262144 : ℝ)) (492125004749/500000000000 : ℝ) (984250009499/1000000000000 : ℝ) (88391061201/500000000000 : ℝ) (176782122409/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33293/262144 : ℝ)) (492125004749/500000000000 : ℝ) (984250009499/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33293/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492125004749/500000000000 : ℝ) (984250009499/1000000000000 : ℝ) (992125004749/1000000000000 : ℝ) (3968500019/4000000000 : ℝ) (992093750357/1000000000000 : ℝ) (496046875179/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33293/262144 : ℝ)) 1 (992125004749/1000000000000 : ℝ) (3968500019/4000000000 : ℝ) (992093750357/1000000000000 : ℝ) (496046875179/500000000000 : ℝ) (992109377553/1000000000000 : ℝ) (496054688777/500000000000 : ℝ) (992109377429/1000000000000 : ℝ) (992109377431/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33293/262144 : ℝ)) 2 (992109377553/1000000000000 : ℝ) (496054688777/500000000000 : ℝ) (992109377429/1000000000000 : ℝ) (992109377431/1000000000000 : ℝ) (992109377491/1000000000000 : ℝ) (992109377493/1000000000000 : ℝ) (99210937749/100000000000 : ℝ) (992109377493/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33293/262144 : ℝ)) 3 (992109377491/1000000000000 : ℝ) (992109377493/1000000000000 : ℝ) (99210937749/100000000000 : ℝ) (992109377493/1000000000000 : ℝ) (99210937749/100000000000 : ℝ) (992109377493/1000000000000 : ℝ) (99210937749/100000000000 : ℝ) (992109377493/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33293/262144 : ℝ)) 4 (99210937749/100000000000 : ℝ) (992109377493/1000000000000 : ℝ) (99210937749/100000000000 : ℝ) (992109377493/1000000000000 : ℝ) (99210937749/100000000000 : ℝ) (992109377493/1000000000000 : ℝ) (99210937749/100000000000 : ℝ) (992109377493/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33293/262144 : ℝ)) 5 (99210937749/100000000000 : ℝ) (992109377493/1000000000000 : ℝ) (99210937749/100000000000 : ℝ) (992109377493/1000000000000 : ℝ) (99210937749/100000000000 : ℝ) (992109377493/1000000000000 : ℝ) (99210937749/100000000000 : ℝ) (992109377493/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33293/262144 : ℝ)) 6 (99210937749/100000000000 : ℝ) (992109377493/1000000000000 : ℝ) (99210937749/100000000000 : ℝ) (992109377493/1000000000000 : ℝ) (99210937749/100000000000 : ℝ) (992109377493/1000000000000 : ℝ) (99210937749/100000000000 : ℝ) (992109377493/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33293/262144 : ℝ)) 7 (99210937749/100000000000 : ℝ) (992109377493/1000000000000 : ℝ) (99210937749/100000000000 : ℝ) (992109377493/1000000000000 : ℝ) (99210937749/100000000000 : ℝ) (992109377493/1000000000000 : ℝ) (99210937749/100000000000 : ℝ) (992109377493/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33293/262144 : ℝ))) (88391061201/500000000000 : ℝ) (176782122409/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33293/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88391061201/500000000000 : ℝ) (176782122409/1000000000000 : ℝ) (588391061201/1000000000000 : ℝ) (117678212241/200000000000 : ℝ) (420454661529/1000000000000 : ℝ) (210227330769/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33293/262144 : ℝ))) 1 (588391061201/1000000000000 : ℝ) (117678212241/200000000000 : ℝ) (420454661529/1000000000000 : ℝ) (210227330769/500000000000 : ℝ) (100884572273/200000000000 : ℝ) (126105715343/250000000000 : ℝ) (497384925871/1000000000000 : ℝ) (497384925879/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33293/262144 : ℝ))) 2 (100884572273/200000000000 : ℝ) (126105715343/250000000000 : ℝ) (497384925871/1000000000000 : ℝ) (497384925879/1000000000000 : ℝ) (250451946809/500000000000 : ℝ) (250451946813/500000000000 : ℝ) (500891532677/1000000000000 : ℝ) (100178306537/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33293/262144 : ℝ))) 3 (250451946809/500000000000 : ℝ) (250451946813/500000000000 : ℝ) (500891532677/1000000000000 : ℝ) (100178306537/200000000000 : ℝ) (500897713147/1000000000000 : ℝ) (125224428289/250000000000 : ℝ) (500897713109/1000000000000 : ℝ) (250448856559/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33293/262144 : ℝ))) 4 (500897713147/1000000000000 : ℝ) (125224428289/250000000000 : ℝ) (500897713109/1000000000000 : ℝ) (250448856559/500000000000 : ℝ) (62612214141/125000000000 : ℝ) (500897713137/1000000000000 : ℝ) (500897713127/1000000000000 : ℝ) (500897713137/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33293/262144 : ℝ))) 5 (62612214141/125000000000 : ℝ) (500897713137/1000000000000 : ℝ) (500897713127/1000000000000 : ℝ) (500897713137/1000000000000 : ℝ) (500897713127/1000000000000 : ℝ) (500897713137/1000000000000 : ℝ) (500897713127/1000000000000 : ℝ) (500897713137/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33293/262144 : ℝ))) 6 (500897713127/1000000000000 : ℝ) (500897713137/1000000000000 : ℝ) (500897713127/1000000000000 : ℝ) (500897713137/1000000000000 : ℝ) (500897713127/1000000000000 : ℝ) (500897713137/1000000000000 : ℝ) (500897713127/1000000000000 : ℝ) (500897713137/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33293/262144 : ℝ))) 7 (500897713127/1000000000000 : ℝ) (500897713137/1000000000000 : ℝ) (500897713127/1000000000000 : ℝ) (500897713137/1000000000000 : ℝ) (500897713127/1000000000000 : ℝ) (500897713137/1000000000000 : ℝ) (500897713127/1000000000000 : ℝ) (500897713137/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33293/262144 : ℝ)) hmem 8 (99210937749/100000000000 : ℝ) (992109377493/1000000000000 : ℝ) (99210937749/100000000000 : ℝ) (992109377493/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33293/262144 : ℝ))) hcmem 8 (500897713127/1000000000000 : ℝ) (500897713137/1000000000000 : ℝ) (500897713127/1000000000000 : ℝ) (500897713137/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33293/262144 : ℝ)) (99210937749/100000000000 : ℝ) (992109377493/1000000000000 : ℝ) (500897713127/1000000000000 : ℝ) (500897713137/1000000000000 : ℝ) (198266518221/250000000000 : ℝ) (793066072903/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0513_exp_lower
  have heNumeric : (513725982227/250000000000 : ℝ)/4 ≤ Real.exp (-85256353815959/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513725982227/250000000000 : ℝ)/4 ≤ Real.exp ((66585/524288 : ℝ)-(793066072903/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66585/524288 : ℝ) (33293/262144 : ℝ) (793066072903/1000000000000 : ℝ) (513725982227/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0514; no trusted numerical premise.
theorem cover8_leaf0514_exp_radius : (998017520472773187/1000000000000000000 : ℝ) ≤ Real.exp ((-66587/4194304 : ℝ)/8) ∧ Real.exp ((-66587/4194304 : ℝ)/8) ≤ (249504380118193297/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66587/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0514_exp_lower : (920113581079061163/1000000000000000000 : ℝ) ≤ Real.exp ((-42628177338723/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628177338723/64000000000000 : ℝ)/8) ≤ (230028395269765291/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628177338723/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0514_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451957539/500000000000 : ℝ) ≤ 4*Real.exp (33293/262144 : ℝ)*Real.exp (-mu (radius 8 (66587/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451957539/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66587/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0514_exp_radius
  have hrNumeric : (492124887417/500000000000 : ℝ) ≤ Real.exp (-66587/4194304 : ℝ) ∧ Real.exp (-66587/4194304 : ℝ) ≤ (196849954967/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492124887417/500000000000 : ℝ) ≤ (radius 8 (66587/524288 : ℝ)) ∧ (radius 8 (66587/524288 : ℝ)) ≤ (196849954967/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66587/524288 : ℝ)) (492124887417/500000000000 : ℝ) (196849954967/200000000000 : ℝ) (17678342891/100000000000 : ℝ) (44195857229/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66587/524288 : ℝ)) (492124887417/500000000000 : ℝ) (196849954967/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66587/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492124887417/500000000000 : ℝ) (196849954967/200000000000 : ℝ) (992124887417/1000000000000 : ℝ) (496062443709/500000000000 : ℝ) (99209363209/100000000000 : ℝ) (992093632091/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66587/524288 : ℝ)) 1 (992124887417/1000000000000 : ℝ) (496062443709/500000000000 : ℝ) (99209363209/100000000000 : ℝ) (992093632091/1000000000000 : ℝ) (992109259753/1000000000000 : ℝ) (198421851951/200000000000 : ℝ) (99210925963/100000000000 : ℝ) (62006828727/62500000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66587/524288 : ℝ)) 2 (992109259753/1000000000000 : ℝ) (198421851951/200000000000 : ℝ) (99210925963/100000000000 : ℝ) (62006828727/62500000000 : ℝ) (992109259691/1000000000000 : ℝ) (496054629847/500000000000 : ℝ) (992109259691/1000000000000 : ℝ) (496054629847/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66587/524288 : ℝ)) 3 (992109259691/1000000000000 : ℝ) (496054629847/500000000000 : ℝ) (992109259691/1000000000000 : ℝ) (496054629847/500000000000 : ℝ) (992109259691/1000000000000 : ℝ) (496054629847/500000000000 : ℝ) (992109259691/1000000000000 : ℝ) (496054629847/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66587/524288 : ℝ)) 4 (992109259691/1000000000000 : ℝ) (496054629847/500000000000 : ℝ) (992109259691/1000000000000 : ℝ) (496054629847/500000000000 : ℝ) (992109259691/1000000000000 : ℝ) (496054629847/500000000000 : ℝ) (992109259691/1000000000000 : ℝ) (496054629847/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66587/524288 : ℝ)) 5 (992109259691/1000000000000 : ℝ) (496054629847/500000000000 : ℝ) (992109259691/1000000000000 : ℝ) (496054629847/500000000000 : ℝ) (992109259691/1000000000000 : ℝ) (496054629847/500000000000 : ℝ) (992109259691/1000000000000 : ℝ) (496054629847/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66587/524288 : ℝ)) 6 (992109259691/1000000000000 : ℝ) (496054629847/500000000000 : ℝ) (992109259691/1000000000000 : ℝ) (496054629847/500000000000 : ℝ) (992109259691/1000000000000 : ℝ) (496054629847/500000000000 : ℝ) (992109259691/1000000000000 : ℝ) (496054629847/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66587/524288 : ℝ)) 7 (992109259691/1000000000000 : ℝ) (496054629847/500000000000 : ℝ) (992109259691/1000000000000 : ℝ) (496054629847/500000000000 : ℝ) (992109259691/1000000000000 : ℝ) (496054629847/500000000000 : ℝ) (992109259691/1000000000000 : ℝ) (496054629847/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66587/524288 : ℝ))) (17678342891/100000000000 : ℝ) (44195857229/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66587/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (17678342891/100000000000 : ℝ) (44195857229/250000000000 : ℝ) (117678342891/200000000000 : ℝ) (294195857229/500000000000 : ℝ) (420456215211/1000000000000 : ℝ) (420456215219/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66587/524288 : ℝ))) 1 (117678342891/200000000000 : ℝ) (294195857229/500000000000 : ℝ) (420456215211/1000000000000 : ℝ) (420456215219/1000000000000 : ℝ) (504423964833/1000000000000 : ℝ) (504423964839/1000000000000 : ℝ) (497386120957/1000000000000 : ℝ) (124346530241/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66587/524288 : ℝ))) 2 (504423964833/1000000000000 : ℝ) (504423964839/1000000000000 : ℝ) (497386120957/1000000000000 : ℝ) (124346530241/250000000000 : ℝ) (100181008579/200000000000 : ℝ) (250452521451/500000000000 : ℝ) (7826448161/15625000000 : ℝ) (500892682311/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66587/524288 : ℝ))) 3 (100181008579/200000000000 : ℝ) (250452521451/500000000000 : ℝ) (7826448161/15625000000 : ℝ) (500892682311/1000000000000 : ℝ) (500898862599/1000000000000 : ℝ) (500898862607/1000000000000 : ℝ) (500898862561/1000000000000 : ℝ) (500898862569/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66587/524288 : ℝ))) 4 (500898862599/1000000000000 : ℝ) (500898862607/1000000000000 : ℝ) (500898862561/1000000000000 : ℝ) (500898862569/1000000000000 : ℝ) (25044943129/50000000000 : ℝ) (125224715647/250000000000 : ℝ) (500898862579/1000000000000 : ℝ) (125224715647/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66587/524288 : ℝ))) 5 (25044943129/50000000000 : ℝ) (125224715647/250000000000 : ℝ) (500898862579/1000000000000 : ℝ) (125224715647/250000000000 : ℝ) (500898862579/1000000000000 : ℝ) (125224715647/250000000000 : ℝ) (500898862579/1000000000000 : ℝ) (125224715647/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66587/524288 : ℝ))) 6 (500898862579/1000000000000 : ℝ) (125224715647/250000000000 : ℝ) (500898862579/1000000000000 : ℝ) (125224715647/250000000000 : ℝ) (500898862579/1000000000000 : ℝ) (125224715647/250000000000 : ℝ) (500898862579/1000000000000 : ℝ) (125224715647/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66587/524288 : ℝ))) 7 (500898862579/1000000000000 : ℝ) (125224715647/250000000000 : ℝ) (500898862579/1000000000000 : ℝ) (125224715647/250000000000 : ℝ) (500898862579/1000000000000 : ℝ) (125224715647/250000000000 : ℝ) (500898862579/1000000000000 : ℝ) (125224715647/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66587/524288 : ℝ)) hmem 8 (992109259691/1000000000000 : ℝ) (496054629847/500000000000 : ℝ) (992109259691/1000000000000 : ℝ) (496054629847/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66587/524288 : ℝ))) hcmem 8 (500898862579/1000000000000 : ℝ) (125224715647/250000000000 : ℝ) (500898862579/1000000000000 : ℝ) (125224715647/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66587/524288 : ℝ)) (992109259691/1000000000000 : ℝ) (496054629847/500000000000 : ℝ) (500898862579/1000000000000 : ℝ) (125224715647/250000000000 : ℝ) (198266996741/250000000000 : ℝ) (396533993491/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0514_exp_lower
  have heNumeric : (1027451957539/500000000000 : ℝ)/4 ≤ Real.exp (-42628177338723/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451957539/500000000000 : ℝ)/4 ≤ Real.exp ((33293/262144 : ℝ)-(396533993491/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33293/262144 : ℝ) (66587/524288 : ℝ) (396533993491/500000000000 : ℝ) (1027451957539/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0515; no trusted numerical premise.
theorem cover8_leaf0515_exp_radius : (998017490729533737/1000000000000000000 : ℝ) ≤ Real.exp ((-16647/1048576 : ℝ)/8) ∧ Real.exp ((-16647/1048576 : ℝ)/8) ≤ (499008745364766869/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16647/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0515_exp_lower : (920113580307848737/1000000000000000000 : ℝ) ≤ Real.exp ((-85256355535733/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256355535733/128000000000000 : ℝ)/8) ≤ (460056790153924369/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256355535733/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0515_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054903901299/1000000000000 : ℝ) ≤ 4*Real.exp (66587/524288 : ℝ)*Real.exp (-mu (radius 8 (16647/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054903901299/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16647/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0515_exp_radius
  have hrNumeric : (984249540171/1000000000000 : ℝ) ≤ Real.exp (-16647/1048576 : ℝ) ∧ Real.exp (-16647/1048576 : ℝ) ≤ (246062385043/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984249540171/1000000000000 : ℝ) ≤ (radius 8 (16647/131072 : ℝ)) ∧ (radius 8 (16647/131072 : ℝ)) ≤ (246062385043/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16647/131072 : ℝ)) (984249540171/1000000000000 : ℝ) (246062385043/250000000000 : ℝ) (88392367701/500000000000 : ℝ) (11049045963/62500000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16647/131072 : ℝ)) (984249540171/1000000000000 : ℝ) (246062385043/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16647/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984249540171/1000000000000 : ℝ) (246062385043/250000000000 : ℝ) (198424954017/200000000000 : ℝ) (496062385043/500000000000 : ℝ) (992093513823/1000000000000 : ℝ) (39683740553/40000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16647/131072 : ℝ)) 1 (198424954017/200000000000 : ℝ) (496062385043/500000000000 : ℝ) (992093513823/1000000000000 : ℝ) (39683740553/40000000000 : ℝ) (496054570977/500000000000 : ℝ) (248027285489/250000000000 : ℝ) (99210914183/100000000000 : ℝ) (992109141833/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16647/131072 : ℝ)) 2 (496054570977/500000000000 : ℝ) (248027285489/250000000000 : ℝ) (99210914183/100000000000 : ℝ) (992109141833/1000000000000 : ℝ) (248027285473/250000000000 : ℝ) (198421828379/200000000000 : ℝ) (992109141891/1000000000000 : ℝ) (198421828379/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16647/131072 : ℝ)) 3 (248027285473/250000000000 : ℝ) (198421828379/200000000000 : ℝ) (992109141891/1000000000000 : ℝ) (198421828379/200000000000 : ℝ) (992109141891/1000000000000 : ℝ) (198421828379/200000000000 : ℝ) (992109141891/1000000000000 : ℝ) (198421828379/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16647/131072 : ℝ)) 4 (992109141891/1000000000000 : ℝ) (198421828379/200000000000 : ℝ) (992109141891/1000000000000 : ℝ) (198421828379/200000000000 : ℝ) (992109141891/1000000000000 : ℝ) (198421828379/200000000000 : ℝ) (992109141891/1000000000000 : ℝ) (198421828379/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16647/131072 : ℝ)) 5 (992109141891/1000000000000 : ℝ) (198421828379/200000000000 : ℝ) (992109141891/1000000000000 : ℝ) (198421828379/200000000000 : ℝ) (992109141891/1000000000000 : ℝ) (198421828379/200000000000 : ℝ) (992109141891/1000000000000 : ℝ) (198421828379/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16647/131072 : ℝ)) 6 (992109141891/1000000000000 : ℝ) (198421828379/200000000000 : ℝ) (992109141891/1000000000000 : ℝ) (198421828379/200000000000 : ℝ) (992109141891/1000000000000 : ℝ) (198421828379/200000000000 : ℝ) (992109141891/1000000000000 : ℝ) (198421828379/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16647/131072 : ℝ)) 7 (992109141891/1000000000000 : ℝ) (198421828379/200000000000 : ℝ) (992109141891/1000000000000 : ℝ) (198421828379/200000000000 : ℝ) (992109141891/1000000000000 : ℝ) (198421828379/200000000000 : ℝ) (992109141891/1000000000000 : ℝ) (198421828379/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16647/131072 : ℝ))) (88392367701/500000000000 : ℝ) (11049045963/62500000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16647/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88392367701/500000000000 : ℝ) (11049045963/62500000000 : ℝ) (588392367701/1000000000000 : ℝ) (73549045963/125000000000 : ℝ) (105114442217/250000000000 : ℝ) (105114442219/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16647/131072 : ℝ))) 1 (588392367701/1000000000000 : ℝ) (73549045963/125000000000 : ℝ) (105114442217/250000000000 : ℝ) (105114442219/250000000000 : ℝ) (126106267071/250000000000 : ℝ) (50442506829/100000000000 : ℝ) (62173414503/125000000000 : ℝ) (497387316031/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16647/131072 : ℝ))) 2 (126106267071/250000000000 : ℝ) (50442506829/100000000000 : ℝ) (62173414503/125000000000 : ℝ) (497387316031/1000000000000 : ℝ) (250453096077/500000000000 : ℝ) (500906192161/1000000000000 : ℝ) (500893831913/1000000000000 : ℝ) (500893831921/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16647/131072 : ℝ))) 3 (250453096077/500000000000 : ℝ) (500906192161/1000000000000 : ℝ) (500893831913/1000000000000 : ℝ) (500893831921/1000000000000 : ℝ) (500900012033/1000000000000 : ℝ) (500900012041/1000000000000 : ℝ) (100180002399/200000000000 : ℝ) (500900012003/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16647/131072 : ℝ))) 4 (500900012033/1000000000000 : ℝ) (500900012041/1000000000000 : ℝ) (100180002399/200000000000 : ℝ) (500900012003/1000000000000 : ℝ) (250450006007/500000000000 : ℝ) (250450006011/500000000000 : ℝ) (500900012013/1000000000000 : ℝ) (250450006011/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16647/131072 : ℝ))) 5 (250450006007/500000000000 : ℝ) (250450006011/500000000000 : ℝ) (500900012013/1000000000000 : ℝ) (250450006011/500000000000 : ℝ) (500900012013/1000000000000 : ℝ) (250450006011/500000000000 : ℝ) (500900012013/1000000000000 : ℝ) (250450006011/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16647/131072 : ℝ))) 6 (500900012013/1000000000000 : ℝ) (250450006011/500000000000 : ℝ) (500900012013/1000000000000 : ℝ) (250450006011/500000000000 : ℝ) (500900012013/1000000000000 : ℝ) (250450006011/500000000000 : ℝ) (500900012013/1000000000000 : ℝ) (250450006011/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16647/131072 : ℝ))) 7 (500900012013/1000000000000 : ℝ) (250450006011/500000000000 : ℝ) (500900012013/1000000000000 : ℝ) (250450006011/500000000000 : ℝ) (500900012013/1000000000000 : ℝ) (250450006011/500000000000 : ℝ) (500900012013/1000000000000 : ℝ) (250450006011/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16647/131072 : ℝ)) hmem 8 (992109141891/1000000000000 : ℝ) (198421828379/200000000000 : ℝ) (992109141891/1000000000000 : ℝ) (198421828379/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16647/131072 : ℝ))) hcmem 8 (500900012013/1000000000000 : ℝ) (250450006011/500000000000 : ℝ) (500900012013/1000000000000 : ℝ) (250450006011/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16647/131072 : ℝ)) (992109141891/1000000000000 : ℝ) (198421828379/200000000000 : ℝ) (500900012013/1000000000000 : ℝ) (250450006011/500000000000 : ℝ) (793069901017/1000000000000 : ℝ) (198267475259/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0515_exp_lower
  have heNumeric : (2054903901299/1000000000000 : ℝ)/4 ≤ Real.exp (-85256355535733/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054903901299/1000000000000 : ℝ)/4 ≤ Real.exp ((66587/524288 : ℝ)-(198267475259/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66587/524288 : ℝ) (16647/131072 : ℝ) (198267475259/250000000000 : ℝ) (2054903901299/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0516; no trusted numerical premise.
theorem cover8_leaf0516_exp_radius : (998017460986295173/1000000000000000000 : ℝ) ≤ Real.exp ((-66589/4194304 : ℝ)/8) ∧ Real.exp ((-66589/4194304 : ℝ)/8) ≤ (499008730493147587/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66589/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0516_exp_lower : (46005678976941079/50000000000000000 : ℝ) ≤ Real.exp ((-21314089097897/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314089097897/32000000000000 : ℝ)/8) ≤ (920113579538821581/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314089097897/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0516_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054903887559/1000000000000 : ℝ) ≤ 4*Real.exp (16647/131072 : ℝ)*Real.exp (-mu (radius 8 (66589/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054903887559/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66589/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0516_exp_radius
  have hrNumeric : (246062326377/250000000000 : ℝ) ≤ Real.exp (-66589/4194304 : ℝ) ∧ Real.exp (-66589/4194304 : ℝ) ≤ (984249305509/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246062326377/250000000000 : ℝ) ≤ (radius 8 (66589/524288 : ℝ)) ∧ (radius 8 (66589/524288 : ℝ)) ≤ (984249305509/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66589/524288 : ℝ)) (246062326377/250000000000 : ℝ) (984249305509/1000000000000 : ℝ) (44196510471/250000000000 : ℝ) (17678604189/100000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66589/524288 : ℝ)) (246062326377/250000000000 : ℝ) (984249305509/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66589/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246062326377/250000000000 : ℝ) (984249305509/1000000000000 : ℝ) (496062326377/500000000000 : ℝ) (198424930551/200000000000 : ℝ) (992093395557/1000000000000 : ℝ) (496046697779/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66589/524288 : ℝ)) 1 (496062326377/500000000000 : ℝ) (198424930551/200000000000 : ℝ) (992093395557/1000000000000 : ℝ) (496046697779/500000000000 : ℝ) (198421804831/200000000000 : ℝ) (992109024157/1000000000000 : ℝ) (31003407001/31250000000 : ℝ) (496054512017/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66589/524288 : ℝ)) 2 (198421804831/200000000000 : ℝ) (992109024157/1000000000000 : ℝ) (31003407001/31250000000 : ℝ) (496054512017/500000000000 : ℝ) (992109024093/1000000000000 : ℝ) (31003407003/31250000000 : ℝ) (992109024093/1000000000000 : ℝ) (31003407003/31250000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66589/524288 : ℝ)) 3 (992109024093/1000000000000 : ℝ) (31003407003/31250000000 : ℝ) (992109024093/1000000000000 : ℝ) (31003407003/31250000000 : ℝ) (992109024093/1000000000000 : ℝ) (31003407003/31250000000 : ℝ) (992109024093/1000000000000 : ℝ) (31003407003/31250000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66589/524288 : ℝ)) 4 (992109024093/1000000000000 : ℝ) (31003407003/31250000000 : ℝ) (992109024093/1000000000000 : ℝ) (31003407003/31250000000 : ℝ) (992109024093/1000000000000 : ℝ) (31003407003/31250000000 : ℝ) (992109024093/1000000000000 : ℝ) (31003407003/31250000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66589/524288 : ℝ)) 5 (992109024093/1000000000000 : ℝ) (31003407003/31250000000 : ℝ) (992109024093/1000000000000 : ℝ) (31003407003/31250000000 : ℝ) (992109024093/1000000000000 : ℝ) (31003407003/31250000000 : ℝ) (992109024093/1000000000000 : ℝ) (31003407003/31250000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66589/524288 : ℝ)) 6 (992109024093/1000000000000 : ℝ) (31003407003/31250000000 : ℝ) (992109024093/1000000000000 : ℝ) (31003407003/31250000000 : ℝ) (992109024093/1000000000000 : ℝ) (31003407003/31250000000 : ℝ) (992109024093/1000000000000 : ℝ) (31003407003/31250000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66589/524288 : ℝ)) 7 (992109024093/1000000000000 : ℝ) (31003407003/31250000000 : ℝ) (992109024093/1000000000000 : ℝ) (31003407003/31250000000 : ℝ) (992109024093/1000000000000 : ℝ) (31003407003/31250000000 : ℝ) (992109024093/1000000000000 : ℝ) (31003407003/31250000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66589/524288 : ℝ))) (44196510471/250000000000 : ℝ) (17678604189/100000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66589/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44196510471/250000000000 : ℝ) (17678604189/100000000000 : ℝ) (294196510471/500000000000 : ℝ) (117678604189/200000000000 : ℝ) (105114830627/250000000000 : ℝ) (105114830629/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66589/524288 : ℝ))) 1 (294196510471/500000000000 : ℝ) (117678604189/200000000000 : ℝ) (105114830627/250000000000 : ℝ) (105114830629/250000000000 : ℝ) (20177046869/40000000000 : ℝ) (504426171731/1000000000000 : ℝ) (497388511079/1000000000000 : ℝ) (248694255543/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66589/524288 : ℝ))) 2 (20177046869/40000000000 : ℝ) (504426171731/1000000000000 : ℝ) (497388511079/1000000000000 : ℝ) (248694255543/500000000000 : ℝ) (250453670701/500000000000 : ℝ) (500907341409/1000000000000 : ℝ) (500894981511/1000000000000 : ℝ) (500894981519/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66589/524288 : ℝ))) 3 (250453670701/500000000000 : ℝ) (500907341409/1000000000000 : ℝ) (500894981511/1000000000000 : ℝ) (500894981519/1000000000000 : ℝ) (31306322591/62500000000 : ℝ) (62612645183/125000000000 : ℝ) (250450580709/500000000000 : ℝ) (250450580713/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66589/524288 : ℝ))) 4 (31306322591/62500000000 : ℝ) (62612645183/125000000000 : ℝ) (250450580709/500000000000 : ℝ) (250450580713/500000000000 : ℝ) (500901161437/1000000000000 : ℝ) (100180232289/200000000000 : ℝ) (125225290359/250000000000 : ℝ) (100180232289/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66589/524288 : ℝ))) 5 (500901161437/1000000000000 : ℝ) (100180232289/200000000000 : ℝ) (125225290359/250000000000 : ℝ) (100180232289/200000000000 : ℝ) (125225290359/250000000000 : ℝ) (100180232289/200000000000 : ℝ) (125225290359/250000000000 : ℝ) (100180232289/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66589/524288 : ℝ))) 6 (125225290359/250000000000 : ℝ) (100180232289/200000000000 : ℝ) (125225290359/250000000000 : ℝ) (100180232289/200000000000 : ℝ) (125225290359/250000000000 : ℝ) (100180232289/200000000000 : ℝ) (125225290359/250000000000 : ℝ) (100180232289/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66589/524288 : ℝ))) 7 (125225290359/250000000000 : ℝ) (100180232289/200000000000 : ℝ) (125225290359/250000000000 : ℝ) (100180232289/200000000000 : ℝ) (125225290359/250000000000 : ℝ) (100180232289/200000000000 : ℝ) (125225290359/250000000000 : ℝ) (100180232289/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66589/524288 : ℝ)) hmem 8 (992109024093/1000000000000 : ℝ) (31003407003/31250000000 : ℝ) (992109024093/1000000000000 : ℝ) (31003407003/31250000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66589/524288 : ℝ))) hcmem 8 (125225290359/250000000000 : ℝ) (100180232289/200000000000 : ℝ) (125225290359/250000000000 : ℝ) (100180232289/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66589/524288 : ℝ)) (992109024093/1000000000000 : ℝ) (31003407003/31250000000 : ℝ) (125225290359/250000000000 : ℝ) (100180232289/200000000000 : ℝ) (793071815053/1000000000000 : ℝ) (793071815071/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0516_exp_lower
  have heNumeric : (2054903887559/1000000000000 : ℝ)/4 ≤ Real.exp (-21314089097897/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054903887559/1000000000000 : ℝ)/4 ≤ Real.exp ((16647/131072 : ℝ)-(793071815071/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16647/131072 : ℝ) (66589/524288 : ℝ) (793071815071/1000000000000 : ℝ) (2054903887559/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0517; no trusted numerical premise.
theorem cover8_leaf0517_exp_radius : (199603486248611499/200000000000000000 : ℝ) ≤ Real.exp ((-33295/2097152 : ℝ)/8) ∧ Real.exp ((-33295/2097152 : ℝ)/8) ≤ (124752178905382187/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33295/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0517_exp_lower : (920113578771059581/1000000000000000000 : ℝ) ≤ Real.exp ((-17051271449207/25600000000000 : ℝ)/8) ∧ Real.exp ((-17051271449207/25600000000000 : ℝ)/8) ≤ (460056789385529791/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-17051271449207/25600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0517_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451936921/500000000000 : ℝ) ≤ 4*Real.exp (66589/524288 : ℝ)*Real.exp (-mu (radius 8 (33295/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451936921/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33295/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0517_exp_radius
  have hrNumeric : (246062267711/250000000000 : ℝ) ≤ Real.exp (-33295/2097152 : ℝ) ∧ Real.exp (-33295/2097152 : ℝ) ≤ (196849814169/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246062267711/250000000000 : ℝ) ≤ (radius 8 (33295/262144 : ℝ)) ∧ (radius 8 (33295/262144 : ℝ)) ≤ (196849814169/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33295/262144 : ℝ)) (246062267711/250000000000 : ℝ) (196849814169/200000000000 : ℝ) (176787348361/1000000000000 : ℝ) (11049209273/62500000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33295/262144 : ℝ)) (246062267711/250000000000 : ℝ) (196849814169/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33295/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246062267711/250000000000 : ℝ) (196849814169/200000000000 : ℝ) (496062267711/500000000000 : ℝ) (992124535423/1000000000000 : ℝ) (992093277289/1000000000000 : ℝ) (992093277291/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33295/262144 : ℝ)) 1 (496062267711/500000000000 : ℝ) (992124535423/1000000000000 : ℝ) (992093277289/1000000000000 : ℝ) (992093277291/1000000000000 : ℝ) (198421781271/200000000000 : ℝ) (992108906357/1000000000000 : ℝ) (124013613279/125000000000 : ℝ) (496054453117/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33295/262144 : ℝ)) 2 (198421781271/200000000000 : ℝ) (992108906357/1000000000000 : ℝ) (124013613279/125000000000 : ℝ) (496054453117/500000000000 : ℝ) (992108906293/1000000000000 : ℝ) (124013613287/125000000000 : ℝ) (992108906293/1000000000000 : ℝ) (124013613287/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33295/262144 : ℝ)) 3 (992108906293/1000000000000 : ℝ) (124013613287/125000000000 : ℝ) (992108906293/1000000000000 : ℝ) (124013613287/125000000000 : ℝ) (992108906293/1000000000000 : ℝ) (124013613287/125000000000 : ℝ) (992108906293/1000000000000 : ℝ) (124013613287/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33295/262144 : ℝ)) 4 (992108906293/1000000000000 : ℝ) (124013613287/125000000000 : ℝ) (992108906293/1000000000000 : ℝ) (124013613287/125000000000 : ℝ) (992108906293/1000000000000 : ℝ) (124013613287/125000000000 : ℝ) (992108906293/1000000000000 : ℝ) (124013613287/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33295/262144 : ℝ)) 5 (992108906293/1000000000000 : ℝ) (124013613287/125000000000 : ℝ) (992108906293/1000000000000 : ℝ) (124013613287/125000000000 : ℝ) (992108906293/1000000000000 : ℝ) (124013613287/125000000000 : ℝ) (992108906293/1000000000000 : ℝ) (124013613287/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33295/262144 : ℝ)) 6 (992108906293/1000000000000 : ℝ) (124013613287/125000000000 : ℝ) (992108906293/1000000000000 : ℝ) (124013613287/125000000000 : ℝ) (992108906293/1000000000000 : ℝ) (124013613287/125000000000 : ℝ) (992108906293/1000000000000 : ℝ) (124013613287/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33295/262144 : ℝ)) 7 (992108906293/1000000000000 : ℝ) (124013613287/125000000000 : ℝ) (992108906293/1000000000000 : ℝ) (124013613287/125000000000 : ℝ) (992108906293/1000000000000 : ℝ) (124013613287/125000000000 : ℝ) (992108906293/1000000000000 : ℝ) (124013613287/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33295/262144 : ℝ))) (176787348361/1000000000000 : ℝ) (11049209273/62500000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33295/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176787348361/1000000000000 : ℝ) (11049209273/62500000000 : ℝ) (29419683709/50000000000 : ℝ) (73549209273/125000000000 : ℝ) (84092175227/200000000000 : ℝ) (84092175229/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33295/262144 : ℝ))) 1 (29419683709/50000000000 : ℝ) (73549209273/125000000000 : ℝ) (84092175227/200000000000 : ℝ) (84092175229/200000000000 : ℝ) (504427275157/1000000000000 : ℝ) (100885455033/200000000000 : ℝ) (497389706123/1000000000000 : ℝ) (124347426533/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33295/262144 : ℝ))) 2 (504427275157/1000000000000 : ℝ) (100885455033/200000000000 : ℝ) (497389706123/1000000000000 : ℝ) (124347426533/250000000000 : ℝ) (6261356133/12500000000 : ℝ) (500908490649/1000000000000 : ℝ) (500896131099/1000000000000 : ℝ) (500896131109/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33295/262144 : ℝ))) 3 (6261356133/12500000000 : ℝ) (500908490649/1000000000000 : ℝ) (500896131099/1000000000000 : ℝ) (500896131109/1000000000000 : ℝ) (500902310869/1000000000000 : ℝ) (500902310879/1000000000000 : ℝ) (500902310831/1000000000000 : ℝ) (500902310841/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33295/262144 : ℝ))) 4 (500902310869/1000000000000 : ℝ) (500902310879/1000000000000 : ℝ) (500902310831/1000000000000 : ℝ) (500902310841/1000000000000 : ℝ) (10018046217/20000000000 : ℝ) (25045115543/50000000000 : ℝ) (500902310849/1000000000000 : ℝ) (25045115543/50000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33295/262144 : ℝ))) 5 (10018046217/20000000000 : ℝ) (25045115543/50000000000 : ℝ) (500902310849/1000000000000 : ℝ) (25045115543/50000000000 : ℝ) (500902310849/1000000000000 : ℝ) (25045115543/50000000000 : ℝ) (500902310849/1000000000000 : ℝ) (25045115543/50000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33295/262144 : ℝ))) 6 (500902310849/1000000000000 : ℝ) (25045115543/50000000000 : ℝ) (500902310849/1000000000000 : ℝ) (25045115543/50000000000 : ℝ) (500902310849/1000000000000 : ℝ) (25045115543/50000000000 : ℝ) (500902310849/1000000000000 : ℝ) (25045115543/50000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33295/262144 : ℝ))) 7 (500902310849/1000000000000 : ℝ) (25045115543/50000000000 : ℝ) (500902310849/1000000000000 : ℝ) (25045115543/50000000000 : ℝ) (500902310849/1000000000000 : ℝ) (25045115543/50000000000 : ℝ) (500902310849/1000000000000 : ℝ) (25045115543/50000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33295/262144 : ℝ)) hmem 8 (992108906293/1000000000000 : ℝ) (124013613287/125000000000 : ℝ) (992108906293/1000000000000 : ℝ) (124013613287/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33295/262144 : ℝ))) hcmem 8 (500902310849/1000000000000 : ℝ) (25045115543/50000000000 : ℝ) (500902310849/1000000000000 : ℝ) (25045115543/50000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33295/262144 : ℝ)) (992108906293/1000000000000 : ℝ) (124013613287/125000000000 : ℝ) (500902310849/1000000000000 : ℝ) (25045115543/50000000000 : ℝ) (396536864537/500000000000 : ℝ) (158614745819/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0517_exp_lower
  have heNumeric : (1027451936921/500000000000 : ℝ)/4 ≤ Real.exp (-17051271449207/25600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451936921/500000000000 : ℝ)/4 ≤ Real.exp ((66589/524288 : ℝ)-(158614745819/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66589/524288 : ℝ) (33295/262144 : ℝ) (158614745819/200000000000 : ℝ) (1027451936921/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0518; no trusted numerical premise.
theorem cover8_leaf0518_exp_radius : (31188043796869397/31250000000000000 : ℝ) ≤ Real.exp ((-66591/4194304 : ℝ)/8) ∧ Real.exp ((-66591/4194304 : ℝ)/8) ≤ (199603480299964141/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66591/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0518_exp_lower : (46005678900325899/50000000000000000 : ℝ) ≤ Real.exp ((-42628179048449/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628179048449/64000000000000 : ℝ)/8) ≤ (920113578006517981/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628179048449/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0518_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451930091/500000000000 : ℝ) ≤ 4*Real.exp (33295/262144 : ℝ)*Real.exp (-mu (radius 8 (66591/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451930091/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66591/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0518_exp_radius
  have hrNumeric : (984248836181/1000000000000 : ℝ) ≤ Real.exp (-66591/4194304 : ℝ) ∧ Real.exp (-66591/4194304 : ℝ) ≤ (492124418091/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984248836181/1000000000000 : ℝ) ≤ (radius 8 (66591/524288 : ℝ)) ∧ (radius 8 (66591/524288 : ℝ)) ≤ (492124418091/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66591/524288 : ℝ)) (984248836181/1000000000000 : ℝ) (492124418091/500000000000 : ℝ) (176788654823/1000000000000 : ℝ) (17678865483/100000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66591/524288 : ℝ)) (984248836181/1000000000000 : ℝ) (492124418091/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66591/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984248836181/1000000000000 : ℝ) (492124418091/500000000000 : ℝ) (99212441809/100000000000 : ℝ) (992124418091/1000000000000 : ℝ) (992093159023/1000000000000 : ℝ) (62005822439/62500000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66591/524288 : ℝ)) 1 (99212441809/100000000000 : ℝ) (992124418091/1000000000000 : ℝ) (992093159023/1000000000000 : ℝ) (62005822439/62500000000 : ℝ) (248027197139/250000000000 : ℝ) (496054394279/500000000000 : ℝ) (992108788433/1000000000000 : ℝ) (198421757687/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66591/524288 : ℝ)) 2 (248027197139/250000000000 : ℝ) (496054394279/500000000000 : ℝ) (992108788433/1000000000000 : ℝ) (198421757687/200000000000 : ℝ) (496054394247/500000000000 : ℝ) (992108788497/1000000000000 : ℝ) (496054394247/500000000000 : ℝ) (992108788497/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66591/524288 : ℝ)) 3 (496054394247/500000000000 : ℝ) (992108788497/1000000000000 : ℝ) (496054394247/500000000000 : ℝ) (992108788497/1000000000000 : ℝ) (496054394247/500000000000 : ℝ) (992108788497/1000000000000 : ℝ) (496054394247/500000000000 : ℝ) (992108788497/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66591/524288 : ℝ)) 4 (496054394247/500000000000 : ℝ) (992108788497/1000000000000 : ℝ) (496054394247/500000000000 : ℝ) (992108788497/1000000000000 : ℝ) (496054394247/500000000000 : ℝ) (992108788497/1000000000000 : ℝ) (496054394247/500000000000 : ℝ) (992108788497/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66591/524288 : ℝ)) 5 (496054394247/500000000000 : ℝ) (992108788497/1000000000000 : ℝ) (496054394247/500000000000 : ℝ) (992108788497/1000000000000 : ℝ) (496054394247/500000000000 : ℝ) (992108788497/1000000000000 : ℝ) (496054394247/500000000000 : ℝ) (992108788497/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66591/524288 : ℝ)) 6 (496054394247/500000000000 : ℝ) (992108788497/1000000000000 : ℝ) (496054394247/500000000000 : ℝ) (992108788497/1000000000000 : ℝ) (496054394247/500000000000 : ℝ) (992108788497/1000000000000 : ℝ) (496054394247/500000000000 : ℝ) (992108788497/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66591/524288 : ℝ)) 7 (496054394247/500000000000 : ℝ) (992108788497/1000000000000 : ℝ) (496054394247/500000000000 : ℝ) (992108788497/1000000000000 : ℝ) (496054394247/500000000000 : ℝ) (992108788497/1000000000000 : ℝ) (496054394247/500000000000 : ℝ) (992108788497/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66591/524288 : ℝ))) (176788654823/1000000000000 : ℝ) (17678865483/100000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66591/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176788654823/1000000000000 : ℝ) (17678865483/100000000000 : ℝ) (588394327411/1000000000000 : ℝ) (117678865483/200000000000 : ℝ) (21023121487/50000000000 : ℝ) (420462429749/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66591/524288 : ℝ))) 1 (588394327411/1000000000000 : ℝ) (117678865483/200000000000 : ℝ) (21023121487/50000000000 : ℝ) (420462429749/1000000000000 : ℝ) (20177135143/40000000000 : ℝ) (252214189291/500000000000 : ℝ) (497390901151/1000000000000 : ℝ) (497390901159/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66591/524288 : ℝ))) 2 (20177135143/40000000000 : ℝ) (252214189291/500000000000 : ℝ) (497390901151/1000000000000 : ℝ) (497390901159/1000000000000 : ℝ) (500909639863/1000000000000 : ℝ) (500909639871/1000000000000 : ℝ) (15653040021/31250000000 : ℝ) (500897280681/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66591/524288 : ℝ))) 3 (500909639863/1000000000000 : ℝ) (500909639871/1000000000000 : ℝ) (15653040021/31250000000 : ℝ) (500897280681/1000000000000 : ℝ) (500903460267/1000000000000 : ℝ) (125225865069/250000000000 : ℝ) (500903460229/1000000000000 : ℝ) (250451730119/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66591/524288 : ℝ))) 4 (500903460267/1000000000000 : ℝ) (125225865069/250000000000 : ℝ) (500903460229/1000000000000 : ℝ) (250451730119/500000000000 : ℝ) (62612932531/125000000000 : ℝ) (500903460257/1000000000000 : ℝ) (500903460247/1000000000000 : ℝ) (500903460257/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66591/524288 : ℝ))) 5 (62612932531/125000000000 : ℝ) (500903460257/1000000000000 : ℝ) (500903460247/1000000000000 : ℝ) (500903460257/1000000000000 : ℝ) (500903460247/1000000000000 : ℝ) (500903460257/1000000000000 : ℝ) (500903460247/1000000000000 : ℝ) (500903460257/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66591/524288 : ℝ))) 6 (500903460247/1000000000000 : ℝ) (500903460257/1000000000000 : ℝ) (500903460247/1000000000000 : ℝ) (500903460257/1000000000000 : ℝ) (500903460247/1000000000000 : ℝ) (500903460257/1000000000000 : ℝ) (500903460247/1000000000000 : ℝ) (500903460257/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66591/524288 : ℝ))) 7 (500903460247/1000000000000 : ℝ) (500903460257/1000000000000 : ℝ) (500903460247/1000000000000 : ℝ) (500903460257/1000000000000 : ℝ) (500903460247/1000000000000 : ℝ) (500903460257/1000000000000 : ℝ) (500903460247/1000000000000 : ℝ) (500903460257/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66591/524288 : ℝ)) hmem 8 (496054394247/500000000000 : ℝ) (992108788497/1000000000000 : ℝ) (496054394247/500000000000 : ℝ) (992108788497/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66591/524288 : ℝ))) hcmem 8 (500903460247/1000000000000 : ℝ) (500903460257/1000000000000 : ℝ) (500903460247/1000000000000 : ℝ) (500903460257/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66591/524288 : ℝ)) (496054394247/500000000000 : ℝ) (992108788497/1000000000000 : ℝ) (500903460247/1000000000000 : ℝ) (500903460257/1000000000000 : ℝ) (12391806923/15625000000 : ℝ) (793075643091/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0518_exp_lower
  have heNumeric : (1027451930091/500000000000 : ℝ)/4 ≤ Real.exp (-42628179048449/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451930091/500000000000 : ℝ)/4 ≤ Real.exp ((33295/262144 : ℝ)-(793075643091/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33295/262144 : ℝ) (66591/524288 : ℝ) (793075643091/1000000000000 : ℝ) (1027451930091/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0519; no trusted numerical premise.
theorem cover8_leaf0519_exp_radius : (998017371756584799/1000000000000000000 : ℝ) ≤ Real.exp ((-2081/131072 : ℝ)/8) ∧ Real.exp ((-2081/131072 : ℝ)/8) ≤ (1247521714695731/1250000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2081/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0519_exp_lower : (920113577243931621/1000000000000000000 : ℝ) ≤ Real.exp ((-17051271789117/25600000000000 : ℝ)/8) ∧ Real.exp ((-17051271789117/25600000000000 : ℝ)/8) ≤ (460056788621965811/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-17051271789117/25600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0519_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451923279/500000000000 : ℝ) ≤ 4*Real.exp (66591/524288 : ℝ)*Real.exp (-mu (radius 8 (2081/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451923279/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2081/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0519_exp_radius
  have hrNumeric : (492124300759/500000000000 : ℝ) ≤ Real.exp (-2081/131072 : ℝ) ∧ Real.exp (-2081/131072 : ℝ) ≤ (984248601519/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492124300759/500000000000 : ℝ) ≤ (radius 8 (2081/16384 : ℝ)) ∧ (radius 8 (2081/16384 : ℝ)) ≤ (984248601519/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2081/16384 : ℝ)) (492124300759/500000000000 : ℝ) (984248601519/1000000000000 : ℝ) (7071598451/40000000000 : ℝ) (88394980641/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2081/16384 : ℝ)) (492124300759/500000000000 : ℝ) (984248601519/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2081/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492124300759/500000000000 : ℝ) (984248601519/1000000000000 : ℝ) (992124300759/1000000000000 : ℝ) (24803107519/25000000000 : ℝ) (248023260189/250000000000 : ℝ) (496046520379/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2081/16384 : ℝ)) 1 (992124300759/1000000000000 : ℝ) (24803107519/25000000000 : ℝ) (248023260189/250000000000 : ℝ) (496046520379/500000000000 : ℝ) (992108670757/1000000000000 : ℝ) (992108670759/1000000000000 : ℝ) (496054335317/500000000000 : ℝ) (248027167659/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2081/16384 : ℝ)) 2 (992108670757/1000000000000 : ℝ) (992108670759/1000000000000 : ℝ) (496054335317/500000000000 : ℝ) (248027167659/250000000000 : ℝ) (198421734139/200000000000 : ℝ) (496054335349/500000000000 : ℝ) (198421734139/200000000000 : ℝ) (496054335349/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2081/16384 : ℝ)) 3 (198421734139/200000000000 : ℝ) (496054335349/500000000000 : ℝ) (198421734139/200000000000 : ℝ) (496054335349/500000000000 : ℝ) (198421734139/200000000000 : ℝ) (496054335349/500000000000 : ℝ) (198421734139/200000000000 : ℝ) (496054335349/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2081/16384 : ℝ)) 4 (198421734139/200000000000 : ℝ) (496054335349/500000000000 : ℝ) (198421734139/200000000000 : ℝ) (496054335349/500000000000 : ℝ) (198421734139/200000000000 : ℝ) (496054335349/500000000000 : ℝ) (198421734139/200000000000 : ℝ) (496054335349/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2081/16384 : ℝ)) 5 (198421734139/200000000000 : ℝ) (496054335349/500000000000 : ℝ) (198421734139/200000000000 : ℝ) (496054335349/500000000000 : ℝ) (198421734139/200000000000 : ℝ) (496054335349/500000000000 : ℝ) (198421734139/200000000000 : ℝ) (496054335349/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2081/16384 : ℝ)) 6 (198421734139/200000000000 : ℝ) (496054335349/500000000000 : ℝ) (198421734139/200000000000 : ℝ) (496054335349/500000000000 : ℝ) (198421734139/200000000000 : ℝ) (496054335349/500000000000 : ℝ) (198421734139/200000000000 : ℝ) (496054335349/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2081/16384 : ℝ)) 7 (198421734139/200000000000 : ℝ) (496054335349/500000000000 : ℝ) (198421734139/200000000000 : ℝ) (496054335349/500000000000 : ℝ) (198421734139/200000000000 : ℝ) (496054335349/500000000000 : ℝ) (198421734139/200000000000 : ℝ) (496054335349/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2081/16384 : ℝ))) (7071598451/40000000000 : ℝ) (88394980641/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2081/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (7071598451/40000000000 : ℝ) (88394980641/500000000000 : ℝ) (588394980637/1000000000000 : ℝ) (588394980641/1000000000000 : ℝ) (210231991663/500000000000 : ℝ) (52557997917/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2081/16384 : ℝ))) 1 (588394980637/1000000000000 : ℝ) (588394980641/1000000000000 : ℝ) (210231991663/500000000000 : ℝ) (52557997917/125000000000 : ℝ) (504429481981/1000000000000 : ℝ) (504429481989/1000000000000 : ℝ) (99478419233/200000000000 : ℝ) (497392096173/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2081/16384 : ℝ))) 2 (504429481981/1000000000000 : ℝ) (504429481989/1000000000000 : ℝ) (99478419233/200000000000 : ℝ) (497392096173/1000000000000 : ℝ) (500910789073/1000000000000 : ℝ) (500910789081/1000000000000 : ℝ) (500898430233/1000000000000 : ℝ) (250449215121/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2081/16384 : ℝ))) 3 (500910789073/1000000000000 : ℝ) (500910789081/1000000000000 : ℝ) (500898430233/1000000000000 : ℝ) (250449215121/500000000000 : ℝ) (500904609653/1000000000000 : ℝ) (250452304831/500000000000 : ℝ) (250452304807/500000000000 : ℝ) (62613076203/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2081/16384 : ℝ))) 4 (500904609653/1000000000000 : ℝ) (250452304831/500000000000 : ℝ) (250452304807/500000000000 : ℝ) (62613076203/125000000000 : ℝ) (500904609633/1000000000000 : ℝ) (500904609643/1000000000000 : ℝ) (500904609633/1000000000000 : ℝ) (500904609643/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2081/16384 : ℝ))) 5 (500904609633/1000000000000 : ℝ) (500904609643/1000000000000 : ℝ) (500904609633/1000000000000 : ℝ) (500904609643/1000000000000 : ℝ) (500904609633/1000000000000 : ℝ) (500904609643/1000000000000 : ℝ) (500904609633/1000000000000 : ℝ) (500904609643/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2081/16384 : ℝ))) 6 (500904609633/1000000000000 : ℝ) (500904609643/1000000000000 : ℝ) (500904609633/1000000000000 : ℝ) (500904609643/1000000000000 : ℝ) (500904609633/1000000000000 : ℝ) (500904609643/1000000000000 : ℝ) (500904609633/1000000000000 : ℝ) (500904609643/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2081/16384 : ℝ))) 7 (500904609633/1000000000000 : ℝ) (500904609643/1000000000000 : ℝ) (500904609633/1000000000000 : ℝ) (500904609643/1000000000000 : ℝ) (500904609633/1000000000000 : ℝ) (500904609643/1000000000000 : ℝ) (500904609633/1000000000000 : ℝ) (500904609643/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2081/16384 : ℝ)) hmem 8 (198421734139/200000000000 : ℝ) (496054335349/500000000000 : ℝ) (198421734139/200000000000 : ℝ) (496054335349/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2081/16384 : ℝ))) hcmem 8 (500904609633/1000000000000 : ℝ) (500904609643/1000000000000 : ℝ) (500904609633/1000000000000 : ℝ) (500904609643/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2081/16384 : ℝ)) (198421734139/200000000000 : ℝ) (496054335349/500000000000 : ℝ) (500904609633/1000000000000 : ℝ) (500904609643/1000000000000 : ℝ) (15861551141/20000000000 : ℝ) (79307755707/100000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0519_exp_lower
  have heNumeric : (1027451923279/500000000000 : ℝ)/4 ≤ Real.exp (-17051271789117/25600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451923279/500000000000 : ℝ)/4 ≤ Real.exp ((66591/524288 : ℝ)-(79307755707/100000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66591/524288 : ℝ) (2081/16384 : ℝ) (79307755707/100000000000 : ℝ) (1027451923279/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0520; no trusted numerical premise.
theorem cover8_leaf0520_exp_radius : (998017342013349781/1000000000000000000 : ℝ) ≤ Real.exp ((-66593/4194304 : ℝ)/8) ∧ Real.exp ((-66593/4194304 : ℝ)/8) ≤ (499008671006674891/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66593/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0520_exp_lower : (11501419706047007/12500000000000000 : ℝ) ≤ Real.exp ((-2664261243487/4000000000000 : ℝ)/8) ∧ Real.exp ((-2664261243487/4000000000000 : ℝ)/8) ≤ (920113576483760561/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2664261243487/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0520_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (128431489561/62500000000 : ℝ) ≤ 4*Real.exp (2081/16384 : ℝ)*Real.exp (-mu (radius 8 (66593/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (128431489561/62500000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66593/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0520_exp_radius
  have hrNumeric : (196849673371/200000000000 : ℝ) ≤ Real.exp (-66593/4194304 : ℝ) ∧ Real.exp (-66593/4194304 : ℝ) ≤ (123031045857/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196849673371/200000000000 : ℝ) ≤ (radius 8 (66593/524288 : ℝ)) ∧ (radius 8 (66593/524288 : ℝ)) ≤ (123031045857/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66593/524288 : ℝ)) (196849673371/200000000000 : ℝ) (123031045857/125000000000 : ℝ) (176791267717/1000000000000 : ℝ) (44197816931/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66593/524288 : ℝ)) (196849673371/200000000000 : ℝ) (123031045857/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66593/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196849673371/200000000000 : ℝ) (123031045857/125000000000 : ℝ) (992124183427/1000000000000 : ℝ) (248031045857/250000000000 : ℝ) (99209292249/100000000000 : ℝ) (992092922491/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66593/524288 : ℝ)) 1 (992124183427/1000000000000 : ℝ) (248031045857/250000000000 : ℝ) (99209292249/100000000000 : ℝ) (992092922491/1000000000000 : ℝ) (496054276479/500000000000 : ℝ) (775084807/781250000 : ℝ) (198421710567/200000000000 : ℝ) (992108552837/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66593/524288 : ℝ)) 2 (496054276479/500000000000 : ℝ) (775084807/781250000 : ℝ) (198421710567/200000000000 : ℝ) (992108552837/1000000000000 : ℝ) (15501696139/15625000000 : ℝ) (992108552899/1000000000000 : ℝ) (15501696139/15625000000 : ℝ) (992108552899/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66593/524288 : ℝ)) 3 (15501696139/15625000000 : ℝ) (992108552899/1000000000000 : ℝ) (15501696139/15625000000 : ℝ) (992108552899/1000000000000 : ℝ) (15501696139/15625000000 : ℝ) (992108552899/1000000000000 : ℝ) (15501696139/15625000000 : ℝ) (992108552899/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66593/524288 : ℝ)) 4 (15501696139/15625000000 : ℝ) (992108552899/1000000000000 : ℝ) (15501696139/15625000000 : ℝ) (992108552899/1000000000000 : ℝ) (15501696139/15625000000 : ℝ) (992108552899/1000000000000 : ℝ) (15501696139/15625000000 : ℝ) (992108552899/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66593/524288 : ℝ)) 5 (15501696139/15625000000 : ℝ) (992108552899/1000000000000 : ℝ) (15501696139/15625000000 : ℝ) (992108552899/1000000000000 : ℝ) (15501696139/15625000000 : ℝ) (992108552899/1000000000000 : ℝ) (15501696139/15625000000 : ℝ) (992108552899/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66593/524288 : ℝ)) 6 (15501696139/15625000000 : ℝ) (992108552899/1000000000000 : ℝ) (15501696139/15625000000 : ℝ) (992108552899/1000000000000 : ℝ) (15501696139/15625000000 : ℝ) (992108552899/1000000000000 : ℝ) (15501696139/15625000000 : ℝ) (992108552899/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66593/524288 : ℝ)) 7 (15501696139/15625000000 : ℝ) (992108552899/1000000000000 : ℝ) (15501696139/15625000000 : ℝ) (992108552899/1000000000000 : ℝ) (15501696139/15625000000 : ℝ) (992108552899/1000000000000 : ℝ) (15501696139/15625000000 : ℝ) (992108552899/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66593/524288 : ℝ))) (176791267717/1000000000000 : ℝ) (44197816931/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66593/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176791267717/1000000000000 : ℝ) (44197816931/250000000000 : ℝ) (294197816929/500000000000 : ℝ) (294197816931/500000000000 : ℝ) (84093107379/200000000000 : ℝ) (84093107381/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66593/524288 : ℝ))) 1 (294197816929/500000000000 : ℝ) (294197816931/500000000000 : ℝ) (84093107379/200000000000 : ℝ) (84093107381/200000000000 : ℝ) (15763455793/31250000000 : ℝ) (63053823173/125000000000 : ℝ) (99478658233/200000000000 : ℝ) (248696645587/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66593/524288 : ℝ))) 2 (15763455793/31250000000 : ℝ) (63053823173/125000000000 : ℝ) (99478658233/200000000000 : ℝ) (248696645587/500000000000 : ℝ) (50091193827/100000000000 : ℝ) (500911938279/1000000000000 : ℝ) (25044978989/50000000000 : ℝ) (50089957979/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66593/524288 : ℝ))) 3 (50091193827/100000000000 : ℝ) (500911938279/1000000000000 : ℝ) (25044978989/50000000000 : ℝ) (50089957979/100000000000 : ℝ) (20036230361/40000000000 : ℝ) (100181151807/200000000000 : ℝ) (250452879493/500000000000 : ℝ) (500905758997/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66593/524288 : ℝ))) 4 (20036230361/40000000000 : ℝ) (100181151807/200000000000 : ℝ) (250452879493/500000000000 : ℝ) (500905758997/1000000000000 : ℝ) (100181151801/200000000000 : ℝ) (62613219877/125000000000 : ℝ) (100181151801/200000000000 : ℝ) (62613219877/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66593/524288 : ℝ))) 5 (100181151801/200000000000 : ℝ) (62613219877/125000000000 : ℝ) (100181151801/200000000000 : ℝ) (62613219877/125000000000 : ℝ) (100181151801/200000000000 : ℝ) (62613219877/125000000000 : ℝ) (100181151801/200000000000 : ℝ) (62613219877/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66593/524288 : ℝ))) 6 (100181151801/200000000000 : ℝ) (62613219877/125000000000 : ℝ) (100181151801/200000000000 : ℝ) (62613219877/125000000000 : ℝ) (100181151801/200000000000 : ℝ) (62613219877/125000000000 : ℝ) (100181151801/200000000000 : ℝ) (62613219877/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66593/524288 : ℝ))) 7 (100181151801/200000000000 : ℝ) (62613219877/125000000000 : ℝ) (100181151801/200000000000 : ℝ) (62613219877/125000000000 : ℝ) (100181151801/200000000000 : ℝ) (62613219877/125000000000 : ℝ) (100181151801/200000000000 : ℝ) (62613219877/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66593/524288 : ℝ)) hmem 8 (15501696139/15625000000 : ℝ) (992108552899/1000000000000 : ℝ) (15501696139/15625000000 : ℝ) (992108552899/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66593/524288 : ℝ))) hcmem 8 (100181151801/200000000000 : ℝ) (62613219877/125000000000 : ℝ) (100181151801/200000000000 : ℝ) (62613219877/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66593/524288 : ℝ)) (15501696139/15625000000 : ℝ) (992108552899/1000000000000 : ℝ) (100181151801/200000000000 : ℝ) (62613219877/125000000000 : ℝ) (793079471007/1000000000000 : ℝ) (198269867757/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0520_exp_lower
  have heNumeric : (128431489561/62500000000 : ℝ)/4 ≤ Real.exp (-2664261243487/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (128431489561/62500000000 : ℝ)/4 ≤ Real.exp ((2081/16384 : ℝ)-(198269867757/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2081/16384 : ℝ) (66593/524288 : ℝ) (198269867757/250000000000 : ℝ) (128431489561/62500000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0521; no trusted numerical premise.
theorem cover8_leaf0521_exp_radius : (998017312270115649/1000000000000000000 : ℝ) ≤ Real.exp ((-33297/2097152 : ℝ)/8) ∧ Real.exp ((-33297/2097152 : ℝ)/8) ≤ (19960346245402313/20000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33297/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0521_exp_lower : (92011357572577477/100000000000000000 : ℝ) ≤ Real.exp ((-85256360635151/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256360635151/128000000000000 : ℝ)/8) ≤ (920113575725774771/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256360635151/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0521_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451909717/500000000000 : ℝ) ≤ 4*Real.exp (66593/524288 : ℝ)*Real.exp (-mu (radius 8 (33297/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451909717/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33297/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0521_exp_radius
  have hrNumeric : (30757754131/31250000000 : ℝ) ≤ Real.exp (-33297/2097152 : ℝ) ∧ Real.exp (-33297/2097152 : ℝ) ≤ (984248132193/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (30757754131/31250000000 : ℝ) ≤ (radius 8 (33297/262144 : ℝ)) ∧ (radius 8 (33297/262144 : ℝ)) ≤ (984248132193/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33297/262144 : ℝ)) (30757754131/31250000000 : ℝ) (984248132193/1000000000000 : ℝ) (3535851483/20000000000 : ℝ) (44198143539/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33297/262144 : ℝ)) (30757754131/31250000000 : ℝ) (984248132193/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33297/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (30757754131/31250000000 : ℝ) (984248132193/1000000000000 : ℝ) (62007754131/62500000000 : ℝ) (992124066097/1000000000000 : ℝ) (992092804223/1000000000000 : ℝ) (7750725033/7812500000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33297/262144 : ℝ)) 1 (62007754131/62500000000 : ℝ) (992124066097/1000000000000 : ℝ) (992092804223/1000000000000 : ℝ) (7750725033/7812500000 : ℝ) (992108435159/1000000000000 : ℝ) (992108435161/1000000000000 : ℝ) (248027108759/250000000000 : ℝ) (496054217519/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33297/262144 : ℝ)) 2 (992108435159/1000000000000 : ℝ) (992108435161/1000000000000 : ℝ) (248027108759/250000000000 : ℝ) (496054217519/500000000000 : ℝ) (992108435097/1000000000000 : ℝ) (9921084351/10000000000 : ℝ) (992108435097/1000000000000 : ℝ) (9921084351/10000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33297/262144 : ℝ)) 3 (992108435097/1000000000000 : ℝ) (9921084351/10000000000 : ℝ) (992108435097/1000000000000 : ℝ) (9921084351/10000000000 : ℝ) (992108435097/1000000000000 : ℝ) (9921084351/10000000000 : ℝ) (992108435097/1000000000000 : ℝ) (9921084351/10000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33297/262144 : ℝ)) 4 (992108435097/1000000000000 : ℝ) (9921084351/10000000000 : ℝ) (992108435097/1000000000000 : ℝ) (9921084351/10000000000 : ℝ) (992108435097/1000000000000 : ℝ) (9921084351/10000000000 : ℝ) (992108435097/1000000000000 : ℝ) (9921084351/10000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33297/262144 : ℝ)) 5 (992108435097/1000000000000 : ℝ) (9921084351/10000000000 : ℝ) (992108435097/1000000000000 : ℝ) (9921084351/10000000000 : ℝ) (992108435097/1000000000000 : ℝ) (9921084351/10000000000 : ℝ) (992108435097/1000000000000 : ℝ) (9921084351/10000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33297/262144 : ℝ)) 6 (992108435097/1000000000000 : ℝ) (9921084351/10000000000 : ℝ) (992108435097/1000000000000 : ℝ) (9921084351/10000000000 : ℝ) (992108435097/1000000000000 : ℝ) (9921084351/10000000000 : ℝ) (992108435097/1000000000000 : ℝ) (9921084351/10000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33297/262144 : ℝ)) 7 (992108435097/1000000000000 : ℝ) (9921084351/10000000000 : ℝ) (992108435097/1000000000000 : ℝ) (9921084351/10000000000 : ℝ) (992108435097/1000000000000 : ℝ) (9921084351/10000000000 : ℝ) (992108435097/1000000000000 : ℝ) (9921084351/10000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33297/262144 : ℝ))) (3535851483/20000000000 : ℝ) (44198143539/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33297/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (3535851483/20000000000 : ℝ) (44198143539/250000000000 : ℝ) (23535851483/40000000000 : ℝ) (294198143539/500000000000 : ℝ) (26279193153/62500000000 : ℝ) (52558386307/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33297/262144 : ℝ))) 1 (23535851483/40000000000 : ℝ) (294198143539/500000000000 : ℝ) (26279193153/62500000000 : ℝ) (52558386307/125000000000 : ℝ) (504431688761/1000000000000 : ℝ) (504431688767/1000000000000 : ℝ) (248697243077/500000000000 : ℝ) (497394486161/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33297/262144 : ℝ))) 2 (504431688761/1000000000000 : ℝ) (504431688767/1000000000000 : ℝ) (248697243077/500000000000 : ℝ) (497394486161/1000000000000 : ℝ) (500913087457/1000000000000 : ℝ) (62614135933/125000000000 : ℝ) (500900729317/1000000000000 : ℝ) (20036029173/40000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33297/262144 : ℝ))) 3 (500913087457/1000000000000 : ℝ) (62614135933/125000000000 : ℝ) (500900729317/1000000000000 : ℝ) (20036029173/40000000000 : ℝ) (500906908387/1000000000000 : ℝ) (100181381679/200000000000 : ℝ) (125226727087/250000000000 : ℝ) (500906908357/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33297/262144 : ℝ))) 4 (500906908387/1000000000000 : ℝ) (100181381679/200000000000 : ℝ) (125226727087/250000000000 : ℝ) (500906908357/1000000000000 : ℝ) (500906908367/1000000000000 : ℝ) (62613363547/125000000000 : ℝ) (500906908367/1000000000000 : ℝ) (62613363547/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33297/262144 : ℝ))) 5 (500906908367/1000000000000 : ℝ) (62613363547/125000000000 : ℝ) (500906908367/1000000000000 : ℝ) (62613363547/125000000000 : ℝ) (500906908367/1000000000000 : ℝ) (62613363547/125000000000 : ℝ) (500906908367/1000000000000 : ℝ) (62613363547/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33297/262144 : ℝ))) 6 (500906908367/1000000000000 : ℝ) (62613363547/125000000000 : ℝ) (500906908367/1000000000000 : ℝ) (62613363547/125000000000 : ℝ) (500906908367/1000000000000 : ℝ) (62613363547/125000000000 : ℝ) (500906908367/1000000000000 : ℝ) (62613363547/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33297/262144 : ℝ))) 7 (500906908367/1000000000000 : ℝ) (62613363547/125000000000 : ℝ) (500906908367/1000000000000 : ℝ) (62613363547/125000000000 : ℝ) (500906908367/1000000000000 : ℝ) (62613363547/125000000000 : ℝ) (500906908367/1000000000000 : ℝ) (62613363547/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33297/262144 : ℝ)) hmem 8 (992108435097/1000000000000 : ℝ) (9921084351/10000000000 : ℝ) (992108435097/1000000000000 : ℝ) (9921084351/10000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33297/262144 : ℝ))) hcmem 8 (500906908367/1000000000000 : ℝ) (62613363547/125000000000 : ℝ) (500906908367/1000000000000 : ℝ) (62613363547/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33297/262144 : ℝ)) (992108435097/1000000000000 : ℝ) (9921084351/10000000000 : ℝ) (500906908367/1000000000000 : ℝ) (62613363547/125000000000 : ℝ) (793081384949/1000000000000 : ℝ) (793081384967/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0521_exp_lower
  have heNumeric : (1027451909717/500000000000 : ℝ)/4 ≤ Real.exp (-85256360635151/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451909717/500000000000 : ℝ)/4 ≤ Real.exp ((66593/524288 : ℝ)-(793081384967/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66593/524288 : ℝ) (33297/262144 : ℝ) (793081384967/1000000000000 : ℝ) (1027451909717/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0522; no trusted numerical premise.
theorem cover8_leaf0522_exp_radius : (998017282526882403/1000000000000000000 : ℝ) ≤ Real.exp ((-66595/4194304 : ℝ)/8) ∧ Real.exp ((-66595/4194304 : ℝ)/8) ≤ (249504320631720601/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66595/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0522_exp_lower : (3680454299879897/4000000000000000 : ℝ) ≤ Real.exp ((-42628180738143/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628180738143/64000000000000 : ℝ)/8) ≤ (920113574969974251/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628180738143/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0522_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (205490380593/100000000000 : ℝ) ≤ 4*Real.exp (33297/262144 : ℝ)*Real.exp (-mu (radius 8 (66595/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (205490380593/100000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66595/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0522_exp_radius
  have hrNumeric : (984247897529/1000000000000 : ℝ) ≤ Real.exp (-66595/4194304 : ℝ) ∧ Real.exp (-66595/4194304 : ℝ) ≤ (98424789753/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984247897529/1000000000000 : ℝ) ≤ (radius 8 (66595/524288 : ℝ)) ∧ (radius 8 (66595/524288 : ℝ)) ≤ (98424789753/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66595/524288 : ℝ)) (984247897529/1000000000000 : ℝ) (98424789753/100000000000 : ℝ) (44198470143/250000000000 : ℝ) (88396940289/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66595/524288 : ℝ)) (984247897529/1000000000000 : ℝ) (98424789753/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66595/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984247897529/1000000000000 : ℝ) (98424789753/100000000000 : ℝ) (248030987191/250000000000 : ℝ) (198424789753/200000000000 : ℝ) (248023171489/250000000000 : ℝ) (496046342979/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66595/524288 : ℝ)) 1 (248030987191/250000000000 : ℝ) (198424789753/200000000000 : ℝ) (248023171489/250000000000 : ℝ) (496046342979/500000000000 : ℝ) (12401353967/12500000000 : ℝ) (496054158681/500000000000 : ℝ) (248027079309/250000000000 : ℝ) (992108317239/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66595/524288 : ℝ)) 2 (12401353967/12500000000 : ℝ) (496054158681/500000000000 : ℝ) (248027079309/250000000000 : ℝ) (992108317239/1000000000000 : ℝ) (496054158649/500000000000 : ℝ) (992108317301/1000000000000 : ℝ) (992108317297/1000000000000 : ℝ) (992108317301/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66595/524288 : ℝ)) 3 (496054158649/500000000000 : ℝ) (992108317301/1000000000000 : ℝ) (992108317297/1000000000000 : ℝ) (992108317301/1000000000000 : ℝ) (992108317297/1000000000000 : ℝ) (992108317301/1000000000000 : ℝ) (992108317297/1000000000000 : ℝ) (992108317301/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66595/524288 : ℝ)) 4 (992108317297/1000000000000 : ℝ) (992108317301/1000000000000 : ℝ) (992108317297/1000000000000 : ℝ) (992108317301/1000000000000 : ℝ) (992108317297/1000000000000 : ℝ) (992108317301/1000000000000 : ℝ) (992108317297/1000000000000 : ℝ) (992108317301/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66595/524288 : ℝ)) 5 (992108317297/1000000000000 : ℝ) (992108317301/1000000000000 : ℝ) (992108317297/1000000000000 : ℝ) (992108317301/1000000000000 : ℝ) (992108317297/1000000000000 : ℝ) (992108317301/1000000000000 : ℝ) (992108317297/1000000000000 : ℝ) (992108317301/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66595/524288 : ℝ)) 6 (992108317297/1000000000000 : ℝ) (992108317301/1000000000000 : ℝ) (992108317297/1000000000000 : ℝ) (992108317301/1000000000000 : ℝ) (992108317297/1000000000000 : ℝ) (992108317301/1000000000000 : ℝ) (992108317297/1000000000000 : ℝ) (992108317301/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66595/524288 : ℝ)) 7 (992108317297/1000000000000 : ℝ) (992108317301/1000000000000 : ℝ) (992108317297/1000000000000 : ℝ) (992108317301/1000000000000 : ℝ) (992108317297/1000000000000 : ℝ) (992108317301/1000000000000 : ℝ) (992108317297/1000000000000 : ℝ) (992108317301/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66595/524288 : ℝ))) (44198470143/250000000000 : ℝ) (88396940289/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66595/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44198470143/250000000000 : ℝ) (88396940289/500000000000 : ℝ) (294198470143/500000000000 : ℝ) (588396940289/1000000000000 : ℝ) (420468643981/1000000000000 : ℝ) (42046864399/100000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66595/524288 : ℝ))) 1 (294198470143/500000000000 : ℝ) (588396940289/1000000000000 : ℝ) (420468643981/1000000000000 : ℝ) (42046864399/100000000000 : ℝ) (504432792133/1000000000000 : ℝ) (25221639607/50000000000 : ℝ) (497395681127/1000000000000 : ℝ) (99479136227/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66595/524288 : ℝ))) 2 (504432792133/1000000000000 : ℝ) (25221639607/50000000000 : ℝ) (497395681127/1000000000000 : ℝ) (99479136227/200000000000 : ℝ) (50091423663/100000000000 : ℝ) (250457118319/500000000000 : ℝ) (12522546971/25000000000 : ℝ) (7826591857/15625000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66595/524288 : ℝ))) 3 (50091423663/100000000000 : ℝ) (250457118319/500000000000 : ℝ) (12522546971/25000000000 : ℝ) (7826591857/15625000000 : ℝ) (100181611547/200000000000 : ℝ) (500908057743/1000000000000 : ℝ) (15653376803/31250000000 : ℝ) (100181611541/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66595/524288 : ℝ))) 4 (100181611547/200000000000 : ℝ) (500908057743/1000000000000 : ℝ) (15653376803/31250000000 : ℝ) (100181611541/200000000000 : ℝ) (100181611543/200000000000 : ℝ) (125227014431/250000000000 : ℝ) (100181611543/200000000000 : ℝ) (125227014431/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66595/524288 : ℝ))) 5 (100181611543/200000000000 : ℝ) (125227014431/250000000000 : ℝ) (100181611543/200000000000 : ℝ) (125227014431/250000000000 : ℝ) (100181611543/200000000000 : ℝ) (125227014431/250000000000 : ℝ) (100181611543/200000000000 : ℝ) (125227014431/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66595/524288 : ℝ))) 6 (100181611543/200000000000 : ℝ) (125227014431/250000000000 : ℝ) (100181611543/200000000000 : ℝ) (125227014431/250000000000 : ℝ) (100181611543/200000000000 : ℝ) (125227014431/250000000000 : ℝ) (100181611543/200000000000 : ℝ) (125227014431/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66595/524288 : ℝ))) 7 (100181611543/200000000000 : ℝ) (125227014431/250000000000 : ℝ) (100181611543/200000000000 : ℝ) (125227014431/250000000000 : ℝ) (100181611543/200000000000 : ℝ) (125227014431/250000000000 : ℝ) (100181611543/200000000000 : ℝ) (125227014431/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66595/524288 : ℝ)) hmem 8 (992108317297/1000000000000 : ℝ) (992108317301/1000000000000 : ℝ) (992108317297/1000000000000 : ℝ) (992108317301/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66595/524288 : ℝ))) hcmem 8 (100181611543/200000000000 : ℝ) (125227014431/250000000000 : ℝ) (100181611543/200000000000 : ℝ) (125227014431/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66595/524288 : ℝ)) (992108317297/1000000000000 : ℝ) (992108317301/1000000000000 : ℝ) (100181611543/200000000000 : ℝ) (125227014431/250000000000 : ℝ) (793083298869/1000000000000 : ℝ) (793083298887/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0522_exp_lower
  have heNumeric : (205490380593/100000000000 : ℝ)/4 ≤ Real.exp (-42628180738143/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (205490380593/100000000000 : ℝ)/4 ≤ Real.exp ((33297/262144 : ℝ)-(793083298887/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33297/262144 : ℝ) (66595/524288 : ℝ) (793083298887/1000000000000 : ℝ) (205490380593/100000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0523; no trusted numerical premise.
theorem cover8_leaf0523_exp_radius : (249504313195912511/250000000000000000 : ℝ) ≤ Real.exp ((-16649/1048576 : ℝ)/8) ∧ Real.exp ((-16649/1048576 : ℝ)/8) ≤ (199603450556730009/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16649/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0523_exp_lower : (920113574216359001/1000000000000000000 : ℝ) ≤ Real.exp ((-85256362314989/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256362314989/128000000000000 : ℝ)/8) ≤ (460056787108179501/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256362314989/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0523_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451896233/500000000000 : ℝ) ≤ 4*Real.exp (66595/524288 : ℝ)*Real.exp (-mu (radius 8 (16649/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451896233/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16649/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0523_exp_radius
  have hrNumeric : (492123831433/500000000000 : ℝ) ≤ Real.exp (-16649/1048576 : ℝ) ∧ Real.exp (-16649/1048576 : ℝ) ≤ (984247662867/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492123831433/500000000000 : ℝ) ≤ (radius 8 (16649/131072 : ℝ)) ∧ (radius 8 (16649/131072 : ℝ)) ≤ (984247662867/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16649/131072 : ℝ)) (492123831433/500000000000 : ℝ) (984247662867/1000000000000 : ℝ) (22099398373/125000000000 : ℝ) (17679518699/100000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16649/131072 : ℝ)) (492123831433/500000000000 : ℝ) (984247662867/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16649/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492123831433/500000000000 : ℝ) (984247662867/1000000000000 : ℝ) (992123831433/1000000000000 : ℝ) (496061915717/500000000000 : ℝ) (99209256769/100000000000 : ℝ) (992092567691/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16649/131072 : ℝ)) 1 (992123831433/1000000000000 : ℝ) (496061915717/500000000000 : ℝ) (99209256769/100000000000 : ℝ) (992092567691/1000000000000 : ℝ) (992108199561/1000000000000 : ℝ) (992108199563/1000000000000 : ℝ) (496054099719/500000000000 : ℝ) (12401352493/12500000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16649/131072 : ℝ)) 2 (992108199561/1000000000000 : ℝ) (992108199563/1000000000000 : ℝ) (496054099719/500000000000 : ℝ) (12401352493/12500000000 : ℝ) (992108199499/1000000000000 : ℝ) (496054099751/500000000000 : ℝ) (992108199499/1000000000000 : ℝ) (496054099751/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16649/131072 : ℝ)) 3 (992108199499/1000000000000 : ℝ) (496054099751/500000000000 : ℝ) (992108199499/1000000000000 : ℝ) (496054099751/500000000000 : ℝ) (992108199499/1000000000000 : ℝ) (496054099751/500000000000 : ℝ) (992108199499/1000000000000 : ℝ) (496054099751/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16649/131072 : ℝ)) 4 (992108199499/1000000000000 : ℝ) (496054099751/500000000000 : ℝ) (992108199499/1000000000000 : ℝ) (496054099751/500000000000 : ℝ) (992108199499/1000000000000 : ℝ) (496054099751/500000000000 : ℝ) (992108199499/1000000000000 : ℝ) (496054099751/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16649/131072 : ℝ)) 5 (992108199499/1000000000000 : ℝ) (496054099751/500000000000 : ℝ) (992108199499/1000000000000 : ℝ) (496054099751/500000000000 : ℝ) (992108199499/1000000000000 : ℝ) (496054099751/500000000000 : ℝ) (992108199499/1000000000000 : ℝ) (496054099751/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16649/131072 : ℝ)) 6 (992108199499/1000000000000 : ℝ) (496054099751/500000000000 : ℝ) (992108199499/1000000000000 : ℝ) (496054099751/500000000000 : ℝ) (992108199499/1000000000000 : ℝ) (496054099751/500000000000 : ℝ) (992108199499/1000000000000 : ℝ) (496054099751/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16649/131072 : ℝ)) 7 (992108199499/1000000000000 : ℝ) (496054099751/500000000000 : ℝ) (992108199499/1000000000000 : ℝ) (496054099751/500000000000 : ℝ) (992108199499/1000000000000 : ℝ) (496054099751/500000000000 : ℝ) (992108199499/1000000000000 : ℝ) (496054099751/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16649/131072 : ℝ))) (22099398373/125000000000 : ℝ) (17679518699/100000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16649/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (22099398373/125000000000 : ℝ) (17679518699/100000000000 : ℝ) (147099398373/250000000000 : ℝ) (117679518699/200000000000 : ℝ) (420470197497/1000000000000 : ℝ) (210235098753/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16649/131072 : ℝ))) 1 (147099398373/250000000000 : ℝ) (117679518699/200000000000 : ℝ) (420470197497/1000000000000 : ℝ) (210235098753/500000000000 : ℝ) (252216947747/500000000000 : ℝ) (504433895501/1000000000000 : ℝ) (62174609511/125000000000 : ℝ) (99479375219/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16649/131072 : ℝ))) 2 (252216947747/500000000000 : ℝ) (504433895501/1000000000000 : ℝ) (62174609511/125000000000 : ℝ) (99479375219/200000000000 : ℝ) (500915385791/1000000000000 : ℝ) (250457692899/500000000000 : ℝ) (500903028351/1000000000000 : ℝ) (500903028359/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16649/131072 : ℝ))) 3 (500915385791/1000000000000 : ℝ) (250457692899/500000000000 : ℝ) (500903028351/1000000000000 : ℝ) (500903028359/1000000000000 : ℝ) (500909207071/1000000000000 : ℝ) (500909207079/1000000000000 : ℝ) (62613650879/125000000000 : ℝ) (500909207041/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16649/131072 : ℝ))) 4 (500909207071/1000000000000 : ℝ) (500909207079/1000000000000 : ℝ) (62613650879/125000000000 : ℝ) (500909207041/1000000000000 : ℝ) (500909207051/1000000000000 : ℝ) (25045460353/50000000000 : ℝ) (500909207051/1000000000000 : ℝ) (25045460353/50000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16649/131072 : ℝ))) 5 (500909207051/1000000000000 : ℝ) (25045460353/50000000000 : ℝ) (500909207051/1000000000000 : ℝ) (25045460353/50000000000 : ℝ) (500909207051/1000000000000 : ℝ) (25045460353/50000000000 : ℝ) (500909207051/1000000000000 : ℝ) (25045460353/50000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16649/131072 : ℝ))) 6 (500909207051/1000000000000 : ℝ) (25045460353/50000000000 : ℝ) (500909207051/1000000000000 : ℝ) (25045460353/50000000000 : ℝ) (500909207051/1000000000000 : ℝ) (25045460353/50000000000 : ℝ) (500909207051/1000000000000 : ℝ) (25045460353/50000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16649/131072 : ℝ))) 7 (500909207051/1000000000000 : ℝ) (25045460353/50000000000 : ℝ) (500909207051/1000000000000 : ℝ) (25045460353/50000000000 : ℝ) (500909207051/1000000000000 : ℝ) (25045460353/50000000000 : ℝ) (500909207051/1000000000000 : ℝ) (25045460353/50000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16649/131072 : ℝ)) hmem 8 (992108199499/1000000000000 : ℝ) (496054099751/500000000000 : ℝ) (992108199499/1000000000000 : ℝ) (496054099751/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16649/131072 : ℝ))) hcmem 8 (500909207051/1000000000000 : ℝ) (25045460353/50000000000 : ℝ) (500909207051/1000000000000 : ℝ) (25045460353/50000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16649/131072 : ℝ)) (992108199499/1000000000000 : ℝ) (496054099751/500000000000 : ℝ) (500909207051/1000000000000 : ℝ) (25045460353/50000000000 : ℝ) (79308521277/100000000000 : ℝ) (198271303197/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0523_exp_lower
  have heNumeric : (1027451896233/500000000000 : ℝ)/4 ≤ Real.exp (-85256362314989/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451896233/500000000000 : ℝ)/4 ≤ Real.exp ((66595/524288 : ℝ)-(198271303197/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66595/524288 : ℝ) (16649/131072 : ℝ) (198271303197/250000000000 : ℝ) (1027451896233/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0524; no trusted numerical premise.
theorem cover8_leaf0524_exp_radius : (998017223040418571/1000000000000000000 : ℝ) ≤ Real.exp ((-66597/4194304 : ℝ)/8) ∧ Real.exp ((-66597/4194304 : ℝ)/8) ≤ (249504305760104643/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66597/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0524_exp_lower : (115014196683101751/125000000000000000 : ℝ) ≤ Real.exp ((-21314090787847/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314090787847/32000000000000 : ℝ)/8) ≤ (920113573464814009/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314090787847/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0524_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451889519/500000000000 : ℝ) ≤ 4*Real.exp (16649/131072 : ℝ)*Real.exp (-mu (radius 8 (66597/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451889519/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66597/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0524_exp_radius
  have hrNumeric : (984247428203/1000000000000 : ℝ) ≤ Real.exp (-66597/4194304 : ℝ) ∧ Real.exp (-66597/4194304 : ℝ) ≤ (246061857051/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984247428203/1000000000000 : ℝ) ≤ (radius 8 (66597/524288 : ℝ)) ∧ (radius 8 (66597/524288 : ℝ)) ≤ (246061857051/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66597/524288 : ℝ)) (984247428203/1000000000000 : ℝ) (246061857051/250000000000 : ℝ) (88398246693/500000000000 : ℝ) (176796493393/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66597/524288 : ℝ)) (984247428203/1000000000000 : ℝ) (246061857051/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66597/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984247428203/1000000000000 : ℝ) (246061857051/250000000000 : ℝ) (992123714101/1000000000000 : ℝ) (496061857051/500000000000 : ℝ) (992092449423/1000000000000 : ℝ) (62005778089/62500000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66597/524288 : ℝ)) 1 (992123714101/1000000000000 : ℝ) (496061857051/500000000000 : ℝ) (992092449423/1000000000000 : ℝ) (62005778089/62500000000 : ℝ) (496054040881/500000000000 : ℝ) (992108081763/1000000000000 : ℝ) (496054040819/500000000000 : ℝ) (24802702041/25000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66597/524288 : ℝ)) 2 (496054040881/500000000000 : ℝ) (992108081763/1000000000000 : ℝ) (496054040819/500000000000 : ℝ) (24802702041/25000000000 : ℝ) (9921080817/10000000000 : ℝ) (496054040851/500000000000 : ℝ) (992108081699/1000000000000 : ℝ) (496054040851/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66597/524288 : ℝ)) 3 (9921080817/10000000000 : ℝ) (496054040851/500000000000 : ℝ) (992108081699/1000000000000 : ℝ) (496054040851/500000000000 : ℝ) (992108081699/1000000000000 : ℝ) (496054040851/500000000000 : ℝ) (992108081699/1000000000000 : ℝ) (496054040851/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66597/524288 : ℝ)) 4 (992108081699/1000000000000 : ℝ) (496054040851/500000000000 : ℝ) (992108081699/1000000000000 : ℝ) (496054040851/500000000000 : ℝ) (992108081699/1000000000000 : ℝ) (496054040851/500000000000 : ℝ) (992108081699/1000000000000 : ℝ) (496054040851/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66597/524288 : ℝ)) 5 (992108081699/1000000000000 : ℝ) (496054040851/500000000000 : ℝ) (992108081699/1000000000000 : ℝ) (496054040851/500000000000 : ℝ) (992108081699/1000000000000 : ℝ) (496054040851/500000000000 : ℝ) (992108081699/1000000000000 : ℝ) (496054040851/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66597/524288 : ℝ)) 6 (992108081699/1000000000000 : ℝ) (496054040851/500000000000 : ℝ) (992108081699/1000000000000 : ℝ) (496054040851/500000000000 : ℝ) (992108081699/1000000000000 : ℝ) (496054040851/500000000000 : ℝ) (992108081699/1000000000000 : ℝ) (496054040851/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66597/524288 : ℝ)) 7 (992108081699/1000000000000 : ℝ) (496054040851/500000000000 : ℝ) (992108081699/1000000000000 : ℝ) (496054040851/500000000000 : ℝ) (992108081699/1000000000000 : ℝ) (496054040851/500000000000 : ℝ) (992108081699/1000000000000 : ℝ) (496054040851/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66597/524288 : ℝ))) (88398246693/500000000000 : ℝ) (176796493393/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66597/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88398246693/500000000000 : ℝ) (176796493393/1000000000000 : ℝ) (588398246693/1000000000000 : ℝ) (588398246697/1000000000000 : ℝ) (105117937749/250000000000 : ℝ) (84094350201/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66597/524288 : ℝ))) 1 (588398246693/1000000000000 : ℝ) (588398246697/1000000000000 : ℝ) (105117937749/250000000000 : ℝ) (84094350201/200000000000 : ℝ) (126108749711/250000000000 : ℝ) (504434998851/1000000000000 : ℝ) (99479614207/200000000000 : ℝ) (497398071043/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66597/524288 : ℝ))) 2 (126108749711/250000000000 : ℝ) (504434998851/1000000000000 : ℝ) (99479614207/200000000000 : ℝ) (497398071043/1000000000000 : ℝ) (500916534939/1000000000000 : ℝ) (500916534947/1000000000000 : ℝ) (500904177849/1000000000000 : ℝ) (250452088929/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66597/524288 : ℝ))) 3 (500916534939/1000000000000 : ℝ) (500916534947/1000000000000 : ℝ) (500904177849/1000000000000 : ℝ) (250452088929/500000000000 : ℝ) (250455178197/500000000000 : ℝ) (500910356403/1000000000000 : ℝ) (100182071271/200000000000 : ℝ) (100182071273/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66597/524288 : ℝ))) 4 (250455178197/500000000000 : ℝ) (500910356403/1000000000000 : ℝ) (100182071271/200000000000 : ℝ) (100182071273/200000000000 : ℝ) (250455178187/500000000000 : ℝ) (15653448637/31250000000 : ℝ) (250455178187/500000000000 : ℝ) (15653448637/31250000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66597/524288 : ℝ))) 5 (250455178187/500000000000 : ℝ) (15653448637/31250000000 : ℝ) (250455178187/500000000000 : ℝ) (15653448637/31250000000 : ℝ) (250455178187/500000000000 : ℝ) (15653448637/31250000000 : ℝ) (250455178187/500000000000 : ℝ) (15653448637/31250000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66597/524288 : ℝ))) 6 (250455178187/500000000000 : ℝ) (15653448637/31250000000 : ℝ) (250455178187/500000000000 : ℝ) (15653448637/31250000000 : ℝ) (250455178187/500000000000 : ℝ) (15653448637/31250000000 : ℝ) (250455178187/500000000000 : ℝ) (15653448637/31250000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66597/524288 : ℝ))) 7 (250455178187/500000000000 : ℝ) (15653448637/31250000000 : ℝ) (250455178187/500000000000 : ℝ) (15653448637/31250000000 : ℝ) (250455178187/500000000000 : ℝ) (15653448637/31250000000 : ℝ) (250455178187/500000000000 : ℝ) (15653448637/31250000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66597/524288 : ℝ)) hmem 8 (992108081699/1000000000000 : ℝ) (496054040851/500000000000 : ℝ) (992108081699/1000000000000 : ℝ) (496054040851/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66597/524288 : ℝ))) hcmem 8 (250455178187/500000000000 : ℝ) (15653448637/31250000000 : ℝ) (250455178187/500000000000 : ℝ) (15653448637/31250000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66597/524288 : ℝ)) (992108081699/1000000000000 : ℝ) (496054040851/500000000000 : ℝ) (250455178187/500000000000 : ℝ) (15653448637/31250000000 : ℝ) (198271781663/250000000000 : ℝ) (793087126671/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0524_exp_lower
  have heNumeric : (1027451889519/500000000000 : ℝ)/4 ≤ Real.exp (-21314090787847/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451889519/500000000000 : ℝ)/4 ≤ Real.exp ((16649/131072 : ℝ)-(793087126671/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16649/131072 : ℝ) (66597/524288 : ℝ) (793087126671/1000000000000 : ℝ) (1027451889519/500000000000 : ℝ) hmu.2 heBox
  · norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_leaf0500_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0500_certificate
#check SmaleRate.Proofs.cover8_leaf0501_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0501_certificate
#check SmaleRate.Proofs.cover8_leaf0502_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0502_certificate
#check SmaleRate.Proofs.cover8_leaf0503_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0503_certificate
#check SmaleRate.Proofs.cover8_leaf0504_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0504_certificate
#check SmaleRate.Proofs.cover8_leaf0505_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0505_certificate
#check SmaleRate.Proofs.cover8_leaf0506_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0506_certificate
#check SmaleRate.Proofs.cover8_leaf0507_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0507_certificate
#check SmaleRate.Proofs.cover8_leaf0508_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0508_certificate
#check SmaleRate.Proofs.cover8_leaf0509_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0509_certificate
#check SmaleRate.Proofs.cover8_leaf0510_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0510_certificate
#check SmaleRate.Proofs.cover8_leaf0511_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0511_certificate
#check SmaleRate.Proofs.cover8_leaf0512_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0512_certificate
#check SmaleRate.Proofs.cover8_leaf0513_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0513_certificate
#check SmaleRate.Proofs.cover8_leaf0514_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0514_certificate
#check SmaleRate.Proofs.cover8_leaf0515_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0515_certificate
#check SmaleRate.Proofs.cover8_leaf0516_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0516_certificate
#check SmaleRate.Proofs.cover8_leaf0517_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0517_certificate
#check SmaleRate.Proofs.cover8_leaf0518_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0518_certificate
#check SmaleRate.Proofs.cover8_leaf0519_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0519_certificate
#check SmaleRate.Proofs.cover8_leaf0520_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0520_certificate
#check SmaleRate.Proofs.cover8_leaf0521_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0521_certificate
#check SmaleRate.Proofs.cover8_leaf0522_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0522_certificate
#check SmaleRate.Proofs.cover8_leaf0523_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0523_certificate
#check SmaleRate.Proofs.cover8_leaf0524_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0524_certificate
