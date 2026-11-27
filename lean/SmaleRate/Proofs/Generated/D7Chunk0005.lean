/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.AGMCertificates

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

-- Proposed record cover7_leaf0125; no trusted numerical premise.
theorem cover7_leaf0125_exp_radius : (997637138700502437/1000000000000000000 : ℝ) ≤ Real.exp ((-4341/229376 : ℝ)/8) ∧ Real.exp ((-4341/229376 : ℝ)/8) ≤ (498818569350251219/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4341/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0125_exp_lower : (918091274513668957/1000000000000000000 : ℝ) ≤ Real.exp ((-1367335451671/2000000000000 : ℝ)/8) ∧ Real.exp ((-1367335451671/2000000000000 : ℝ)/8) ≤ (459045637256834479/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1367335451671/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0125_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009524527063/500000000000 : ℝ) ≤ 4*Real.exp (1085/8192 : ℝ)*Real.exp (-mu (radius 7 (4341/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (1009524527063/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4341/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0125_exp_radius
  have hrNumeric : (981252700201/1000000000000 : ℝ) ≤ Real.exp (-4341/229376 : ℝ) ∧ Real.exp (-4341/229376 : ℝ) ≤ (490626350101/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (981252700201/1000000000000 : ℝ) ≤ (radius 7 (4341/32768 : ℝ)) ∧ (radius 7 (4341/32768 : ℝ)) ≤ (490626350101/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4341/32768 : ℝ)) (981252700201/1000000000000 : ℝ) (490626350101/500000000000 : ℝ) (48181387969/250000000000 : ℝ) (192725551883/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4341/32768 : ℝ)) (981252700201/1000000000000 : ℝ) (490626350101/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4341/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (981252700201/1000000000000 : ℝ) (490626350101/500000000000 : ℝ) (9906263501/10000000000 : ℝ) (990626350101/1000000000000 : ℝ) (198116400149/200000000000 : ℝ) (990582000747/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4341/32768 : ℝ)) 1 (9906263501/10000000000 : ℝ) (990626350101/1000000000000 : ℝ) (198116400149/200000000000 : ℝ) (990582000747/1000000000000 : ℝ) (495302087711/500000000000 : ℝ) (15478190241/15625000000 : ℝ) (495302087587/500000000000 : ℝ) (123825521897/125000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4341/32768 : ℝ)) 2 (495302087711/500000000000 : ℝ) (15478190241/15625000000 : ℝ) (495302087587/500000000000 : ℝ) (123825521897/125000000000 : ℝ) (495302087649/500000000000 : ℝ) (9906041753/10000000000 : ℝ) (990604175297/1000000000000 : ℝ) (9906041753/10000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4341/32768 : ℝ)) 3 (495302087649/500000000000 : ℝ) (9906041753/10000000000 : ℝ) (990604175297/1000000000000 : ℝ) (9906041753/10000000000 : ℝ) (990604175297/1000000000000 : ℝ) (9906041753/10000000000 : ℝ) (990604175297/1000000000000 : ℝ) (9906041753/10000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4341/32768 : ℝ)) 4 (990604175297/1000000000000 : ℝ) (9906041753/10000000000 : ℝ) (990604175297/1000000000000 : ℝ) (9906041753/10000000000 : ℝ) (990604175297/1000000000000 : ℝ) (9906041753/10000000000 : ℝ) (990604175297/1000000000000 : ℝ) (9906041753/10000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4341/32768 : ℝ)) 5 (990604175297/1000000000000 : ℝ) (9906041753/10000000000 : ℝ) (990604175297/1000000000000 : ℝ) (9906041753/10000000000 : ℝ) (990604175297/1000000000000 : ℝ) (9906041753/10000000000 : ℝ) (990604175297/1000000000000 : ℝ) (9906041753/10000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4341/32768 : ℝ)) 6 (990604175297/1000000000000 : ℝ) (9906041753/10000000000 : ℝ) (990604175297/1000000000000 : ℝ) (9906041753/10000000000 : ℝ) (990604175297/1000000000000 : ℝ) (9906041753/10000000000 : ℝ) (990604175297/1000000000000 : ℝ) (9906041753/10000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4341/32768 : ℝ)) 7 (990604175297/1000000000000 : ℝ) (9906041753/10000000000 : ℝ) (990604175297/1000000000000 : ℝ) (9906041753/10000000000 : ℝ) (990604175297/1000000000000 : ℝ) (9906041753/10000000000 : ℝ) (990604175297/1000000000000 : ℝ) (9906041753/10000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4341/32768 : ℝ))) (48181387969/250000000000 : ℝ) (192725551883/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4341/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (48181387969/250000000000 : ℝ) (192725551883/1000000000000 : ℝ) (298181387969/500000000000 : ℝ) (298181387971/500000000000 : ℝ) (219502592169/500000000000 : ℝ) (439005184347/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4341/32768 : ℝ))) 1 (298181387969/500000000000 : ℝ) (298181387971/500000000000 : ℝ) (219502592169/500000000000 : ℝ) (439005184347/1000000000000 : ℝ) (258841990069/500000000000 : ℝ) (103536796029/200000000000 : ℝ) (511670157799/1000000000000 : ℝ) (511670157807/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4341/32768 : ℝ))) 2 (258841990069/500000000000 : ℝ) (103536796029/200000000000 : ℝ) (511670157799/1000000000000 : ℝ) (511670157807/1000000000000 : ℝ) (64334633621/125000000000 : ℝ) (32167316811/62500000000 : ℝ) (16083383913/31250000000 : ℝ) (64333535653/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4341/32768 : ℝ))) 3 (64334633621/125000000000 : ℝ) (32167316811/62500000000 : ℝ) (16083383913/31250000000 : ℝ) (64333535653/125000000000 : ℝ) (128668169273/250000000000 : ℝ) (5146726771/10000000000 : ℝ) (514672677073/1000000000000 : ℝ) (257336338541/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4341/32768 : ℝ))) 4 (128668169273/250000000000 : ℝ) (5146726771/10000000000 : ℝ) (514672677073/1000000000000 : ℝ) (257336338541/500000000000 : ℝ) (257336338541/500000000000 : ℝ) (514672677091/1000000000000 : ℝ) (257336338541/500000000000 : ℝ) (514672677091/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4341/32768 : ℝ))) 5 (257336338541/500000000000 : ℝ) (514672677091/1000000000000 : ℝ) (257336338541/500000000000 : ℝ) (514672677091/1000000000000 : ℝ) (257336338541/500000000000 : ℝ) (514672677091/1000000000000 : ℝ) (257336338541/500000000000 : ℝ) (514672677091/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4341/32768 : ℝ))) 6 (257336338541/500000000000 : ℝ) (514672677091/1000000000000 : ℝ) (257336338541/500000000000 : ℝ) (514672677091/1000000000000 : ℝ) (257336338541/500000000000 : ℝ) (514672677091/1000000000000 : ℝ) (257336338541/500000000000 : ℝ) (514672677091/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4341/32768 : ℝ))) 7 (257336338541/500000000000 : ℝ) (514672677091/1000000000000 : ℝ) (257336338541/500000000000 : ℝ) (514672677091/1000000000000 : ℝ) (257336338541/500000000000 : ℝ) (514672677091/1000000000000 : ℝ) (257336338541/500000000000 : ℝ) (514672677091/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4341/32768 : ℝ)) hmem 8 (990604175297/1000000000000 : ℝ) (9906041753/10000000000 : ℝ) (990604175297/1000000000000 : ℝ) (9906041753/10000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4341/32768 : ℝ))) hcmem 8 (257336338541/500000000000 : ℝ) (514672677091/1000000000000 : ℝ) (257336338541/500000000000 : ℝ) (514672677091/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4341/32768 : ℝ)) (990604175297/1000000000000 : ℝ) (9906041753/10000000000 : ℝ) (257336338541/500000000000 : ℝ) (514672677091/1000000000000 : ℝ) (816114014881/1000000000000 : ℝ) (408057007449/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0125_exp_lower
  have heNumeric : (1009524527063/500000000000 : ℝ)/4 ≤ Real.exp (-1367335451671/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009524527063/500000000000 : ℝ)/4 ≤ Real.exp ((1085/8192 : ℝ)-(408057007449/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (1085/8192 : ℝ) (4341/32768 : ℝ) (408057007449/500000000000 : ℝ) (1009524527063/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0126; no trusted numerical premise.
theorem cover7_leaf0126_exp_radius : (997636595031555563/1000000000000000000 : ℝ) ≤ Real.exp ((-2171/114688 : ℝ)/8) ∧ Real.exp ((-2171/114688 : ℝ)/8) ≤ (249409148757888891/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2171/114688 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0126_exp_lower : (91809120897401859/100000000000000000 : ℝ) ≤ Real.exp ((-5469346375443/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469346375443/8000000000000 : ℝ)/8) ≤ (918091208974018591/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469346375443/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0126_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009523950529/500000000000 : ℝ) ≤ 4*Real.exp (4341/32768 : ℝ)*Real.exp (-mu (radius 7 (2171/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (1009523950529/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2171/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0126_exp_radius
  have hrNumeric : (61328026393/62500000000 : ℝ) ≤ Real.exp (-2171/114688 : ℝ) ∧ Real.exp (-2171/114688 : ℝ) ≤ (981248422289/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (61328026393/62500000000 : ℝ) ≤ (radius 7 (2171/16384 : ℝ)) ∧ (radius 7 (2171/16384 : ℝ)) ≤ (981248422289/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2171/16384 : ℝ)) (61328026393/62500000000 : ℝ) (981248422289/1000000000000 : ℝ) (192747331383/1000000000000 : ℝ) (192747331389/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2171/16384 : ℝ)) (61328026393/62500000000 : ℝ) (981248422289/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2171/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (61328026393/62500000000 : ℝ) (981248422289/1000000000000 : ℝ) (123828026393/125000000000 : ℝ) (198124842229/200000000000 : ℝ) (19811596829/20000000000 : ℝ) (990579841451/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2171/16384 : ℝ)) 1 (123828026393/125000000000 : ℝ) (198124842229/200000000000 : ℝ) (19811596829/20000000000 : ℝ) (990579841451/1000000000000 : ℝ) (990602026297/1000000000000 : ℝ) (495301013149/500000000000 : ℝ) (15478156657/15625000000 : ℝ) (19812040521/20000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2171/16384 : ℝ)) 2 (990602026297/1000000000000 : ℝ) (495301013149/500000000000 : ℝ) (15478156657/15625000000 : ℝ) (19812040521/20000000000 : ℝ) (247650506543/250000000000 : ℝ) (495301013087/500000000000 : ℝ) (247650506543/250000000000 : ℝ) (495301013087/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2171/16384 : ℝ)) 3 (247650506543/250000000000 : ℝ) (495301013087/500000000000 : ℝ) (247650506543/250000000000 : ℝ) (495301013087/500000000000 : ℝ) (247650506543/250000000000 : ℝ) (495301013087/500000000000 : ℝ) (247650506543/250000000000 : ℝ) (495301013087/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2171/16384 : ℝ)) 4 (247650506543/250000000000 : ℝ) (495301013087/500000000000 : ℝ) (247650506543/250000000000 : ℝ) (495301013087/500000000000 : ℝ) (247650506543/250000000000 : ℝ) (495301013087/500000000000 : ℝ) (247650506543/250000000000 : ℝ) (495301013087/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2171/16384 : ℝ)) 5 (247650506543/250000000000 : ℝ) (495301013087/500000000000 : ℝ) (247650506543/250000000000 : ℝ) (495301013087/500000000000 : ℝ) (247650506543/250000000000 : ℝ) (495301013087/500000000000 : ℝ) (247650506543/250000000000 : ℝ) (495301013087/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2171/16384 : ℝ)) 6 (247650506543/250000000000 : ℝ) (495301013087/500000000000 : ℝ) (247650506543/250000000000 : ℝ) (495301013087/500000000000 : ℝ) (247650506543/250000000000 : ℝ) (495301013087/500000000000 : ℝ) (247650506543/250000000000 : ℝ) (495301013087/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2171/16384 : ℝ)) 7 (247650506543/250000000000 : ℝ) (495301013087/500000000000 : ℝ) (247650506543/250000000000 : ℝ) (495301013087/500000000000 : ℝ) (247650506543/250000000000 : ℝ) (495301013087/500000000000 : ℝ) (247650506543/250000000000 : ℝ) (495301013087/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2171/16384 : ℝ))) (192747331383/1000000000000 : ℝ) (192747331389/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2171/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (192747331383/1000000000000 : ℝ) (192747331389/1000000000000 : ℝ) (596373665691/1000000000000 : ℝ) (119274733139/200000000000 : ℝ) (439029989161/1000000000000 : ℝ) (439029989169/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2171/16384 : ℝ))) 1 (596373665691/1000000000000 : ℝ) (119274733139/200000000000 : ℝ) (439029989161/1000000000000 : ℝ) (439029989169/1000000000000 : ℝ) (258850913713/500000000000 : ℝ) (64712728429/125000000000 : ℝ) (511689284609/1000000000000 : ℝ) (63961160577/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2171/16384 : ℝ))) 2 (258850913713/500000000000 : ℝ) (64712728429/125000000000 : ℝ) (511689284609/1000000000000 : ℝ) (63961160577/125000000000 : ℝ) (514695556017/1000000000000 : ℝ) (64336944503/125000000000 : ℝ) (514686776317/1000000000000 : ℝ) (20587471053/40000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2171/16384 : ℝ))) 3 (514695556017/1000000000000 : ℝ) (64336944503/125000000000 : ℝ) (514686776317/1000000000000 : ℝ) (20587471053/40000000000 : ℝ) (514691166167/1000000000000 : ℝ) (20587646647/40000000000 : ℝ) (128672791537/250000000000 : ℝ) (128672791539/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2171/16384 : ℝ))) 4 (514691166167/1000000000000 : ℝ) (20587646647/40000000000 : ℝ) (128672791537/250000000000 : ℝ) (128672791539/250000000000 : ℝ) (514691166157/1000000000000 : ℝ) (257345583083/500000000000 : ℝ) (514691166157/1000000000000 : ℝ) (257345583083/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2171/16384 : ℝ))) 5 (514691166157/1000000000000 : ℝ) (257345583083/500000000000 : ℝ) (514691166157/1000000000000 : ℝ) (257345583083/500000000000 : ℝ) (514691166157/1000000000000 : ℝ) (257345583083/500000000000 : ℝ) (514691166157/1000000000000 : ℝ) (257345583083/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2171/16384 : ℝ))) 6 (514691166157/1000000000000 : ℝ) (257345583083/500000000000 : ℝ) (514691166157/1000000000000 : ℝ) (257345583083/500000000000 : ℝ) (514691166157/1000000000000 : ℝ) (257345583083/500000000000 : ℝ) (514691166157/1000000000000 : ℝ) (257345583083/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2171/16384 : ℝ))) 7 (514691166157/1000000000000 : ℝ) (257345583083/500000000000 : ℝ) (514691166157/1000000000000 : ℝ) (257345583083/500000000000 : ℝ) (514691166157/1000000000000 : ℝ) (257345583083/500000000000 : ℝ) (514691166157/1000000000000 : ℝ) (257345583083/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2171/16384 : ℝ)) hmem 8 (247650506543/250000000000 : ℝ) (495301013087/500000000000 : ℝ) (247650506543/250000000000 : ℝ) (495301013087/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2171/16384 : ℝ))) hcmem 8 (514691166157/1000000000000 : ℝ) (257345583083/500000000000 : ℝ) (514691166157/1000000000000 : ℝ) (257345583083/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2171/16384 : ℝ)) (247650506543/250000000000 : ℝ) (495301013087/500000000000 : ℝ) (514691166157/1000000000000 : ℝ) (257345583083/500000000000 : ℝ) (408072551777/500000000000 : ℝ) (816145103571/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0126_exp_lower
  have heNumeric : (1009523950529/500000000000 : ℝ)/4 ≤ Real.exp (-5469346375443/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009523950529/500000000000 : ℝ)/4 ≤ Real.exp ((4341/32768 : ℝ)-(816145103571/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4341/32768 : ℝ) (2171/16384 : ℝ) (816145103571/1000000000000 : ℝ) (1009523950529/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0127; no trusted numerical premise.
theorem cover7_leaf0127_exp_radius : (199527210272580993/200000000000000000 : ℝ) ≤ Real.exp ((-4343/229376 : ℝ)/8) ∧ Real.exp ((-4343/229376 : ℝ)/8) ≤ (498818025681452483/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4343/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0127_exp_lower : (114761392998038687/125000000000000000 : ℝ) ≤ Real.exp ((-2734675452933/4000000000000 : ℝ)/8) ∧ Real.exp ((-2734675452933/4000000000000 : ℝ)/8) ≤ (918091143984309497/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2734675452933/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0127_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (403809351533/200000000000 : ℝ) ≤ 4*Real.exp (2171/16384 : ℝ)*Real.exp (-mu (radius 7 (4343/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (403809351533/200000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4343/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0127_exp_radius
  have hrNumeric : (490622072197/500000000000 : ℝ) ≤ Real.exp (-4343/229376 : ℝ) ∧ Real.exp (-4343/229376 : ℝ) ≤ (196248828879/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490622072197/500000000000 : ℝ) ≤ (radius 7 (4343/32768 : ℝ)) ∧ (radius 7 (4343/32768 : ℝ)) ≤ (196248828879/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4343/32768 : ℝ)) (490622072197/500000000000 : ℝ) (196248828879/200000000000 : ℝ) (192769108237/1000000000000 : ℝ) (192769108243/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4343/32768 : ℝ)) (490622072197/500000000000 : ℝ) (196248828879/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4343/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490622072197/500000000000 : ℝ) (196248828879/200000000000 : ℝ) (990622072197/1000000000000 : ℝ) (495311036099/500000000000 : ℝ) (12382221027/12500000000 : ℝ) (990577682161/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4343/32768 : ℝ)) 1 (990622072197/1000000000000 : ℝ) (495311036099/500000000000 : ℝ) (12382221027/12500000000 : ℝ) (990577682161/1000000000000 : ℝ) (495299938589/500000000000 : ℝ) (49529993859/50000000000 : ℝ) (990599876929/1000000000000 : ℝ) (990599876931/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4343/32768 : ℝ)) 2 (495299938589/500000000000 : ℝ) (49529993859/50000000000 : ℝ) (990599876929/1000000000000 : ℝ) (990599876931/1000000000000 : ℝ) (990599877053/1000000000000 : ℝ) (15478123079/15625000000 : ℝ) (990599877053/1000000000000 : ℝ) (15478123079/15625000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4343/32768 : ℝ)) 3 (990599877053/1000000000000 : ℝ) (15478123079/15625000000 : ℝ) (990599877053/1000000000000 : ℝ) (15478123079/15625000000 : ℝ) (990599877053/1000000000000 : ℝ) (15478123079/15625000000 : ℝ) (990599877053/1000000000000 : ℝ) (15478123079/15625000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4343/32768 : ℝ)) 4 (990599877053/1000000000000 : ℝ) (15478123079/15625000000 : ℝ) (990599877053/1000000000000 : ℝ) (15478123079/15625000000 : ℝ) (990599877053/1000000000000 : ℝ) (15478123079/15625000000 : ℝ) (990599877053/1000000000000 : ℝ) (15478123079/15625000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4343/32768 : ℝ)) 5 (990599877053/1000000000000 : ℝ) (15478123079/15625000000 : ℝ) (990599877053/1000000000000 : ℝ) (15478123079/15625000000 : ℝ) (990599877053/1000000000000 : ℝ) (15478123079/15625000000 : ℝ) (990599877053/1000000000000 : ℝ) (15478123079/15625000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4343/32768 : ℝ)) 6 (990599877053/1000000000000 : ℝ) (15478123079/15625000000 : ℝ) (990599877053/1000000000000 : ℝ) (15478123079/15625000000 : ℝ) (990599877053/1000000000000 : ℝ) (15478123079/15625000000 : ℝ) (990599877053/1000000000000 : ℝ) (15478123079/15625000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4343/32768 : ℝ)) 7 (990599877053/1000000000000 : ℝ) (15478123079/15625000000 : ℝ) (990599877053/1000000000000 : ℝ) (15478123079/15625000000 : ℝ) (990599877053/1000000000000 : ℝ) (15478123079/15625000000 : ℝ) (990599877053/1000000000000 : ℝ) (15478123079/15625000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4343/32768 : ℝ))) (192769108237/1000000000000 : ℝ) (192769108243/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4343/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (192769108237/1000000000000 : ℝ) (192769108243/1000000000000 : ℝ) (298192277059/500000000000 : ℝ) (298192277061/500000000000 : ℝ) (439054789561/1000000000000 : ℝ) (439054789569/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4343/32768 : ℝ))) 1 (298192277059/500000000000 : ℝ) (298192277061/500000000000 : ℝ) (439054789561/1000000000000 : ℝ) (439054789569/1000000000000 : ℝ) (517719671839/1000000000000 : ℝ) (258859835923/500000000000 : ℝ) (102341681617/200000000000 : ℝ) (511708408093/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4343/32768 : ℝ))) 2 (517719671839/1000000000000 : ℝ) (258859835923/500000000000 : ℝ) (102341681617/200000000000 : ℝ) (511708408093/1000000000000 : ℝ) (257357019981/500000000000 : ℝ) (51471403997/100000000000 : ℝ) (64338158039/125000000000 : ℝ) (514705264321/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4343/32768 : ℝ))) 3 (257357019981/500000000000 : ℝ) (51471403997/100000000000 : ℝ) (64338158039/125000000000 : ℝ) (514705264321/1000000000000 : ℝ) (514709652137/1000000000000 : ℝ) (257354826073/500000000000 : ℝ) (257354826059/500000000000 : ℝ) (514709652127/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4343/32768 : ℝ))) 4 (514709652137/1000000000000 : ℝ) (257354826073/500000000000 : ℝ) (257354826059/500000000000 : ℝ) (514709652127/1000000000000 : ℝ) (514709652127/1000000000000 : ℝ) (514709652137/1000000000000 : ℝ) (514709652127/1000000000000 : ℝ) (514709652137/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4343/32768 : ℝ))) 5 (514709652127/1000000000000 : ℝ) (514709652137/1000000000000 : ℝ) (514709652127/1000000000000 : ℝ) (514709652137/1000000000000 : ℝ) (514709652127/1000000000000 : ℝ) (514709652137/1000000000000 : ℝ) (514709652127/1000000000000 : ℝ) (514709652137/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4343/32768 : ℝ))) 6 (514709652127/1000000000000 : ℝ) (514709652137/1000000000000 : ℝ) (514709652127/1000000000000 : ℝ) (514709652137/1000000000000 : ℝ) (514709652127/1000000000000 : ℝ) (514709652137/1000000000000 : ℝ) (514709652127/1000000000000 : ℝ) (514709652137/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4343/32768 : ℝ))) 7 (514709652127/1000000000000 : ℝ) (514709652137/1000000000000 : ℝ) (514709652127/1000000000000 : ℝ) (514709652137/1000000000000 : ℝ) (514709652127/1000000000000 : ℝ) (514709652137/1000000000000 : ℝ) (514709652127/1000000000000 : ℝ) (514709652137/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4343/32768 : ℝ)) hmem 8 (990599877053/1000000000000 : ℝ) (15478123079/15625000000 : ℝ) (990599877053/1000000000000 : ℝ) (15478123079/15625000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4343/32768 : ℝ))) hcmem 8 (514709652127/1000000000000 : ℝ) (514709652137/1000000000000 : ℝ) (514709652127/1000000000000 : ℝ) (514709652137/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4343/32768 : ℝ)) (990599877053/1000000000000 : ℝ) (15478123079/15625000000 : ℝ) (514709652127/1000000000000 : ℝ) (514709652137/1000000000000 : ℝ) (102022023429/125000000000 : ℝ) (204044046863/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0127_exp_lower
  have heNumeric : (403809351533/200000000000 : ℝ)/4 ≤ Real.exp (-2734675452933/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (403809351533/200000000000 : ℝ)/4 ≤ Real.exp ((2171/16384 : ℝ)-(204044046863/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2171/16384 : ℝ) (4343/32768 : ℝ) (204044046863/250000000000 : ℝ) (403809351533/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0128; no trusted numerical premise.
theorem cover7_leaf0128_exp_radius : (498817753847275321/500000000000000000 : ℝ) ≤ Real.exp ((-543/28672 : ℝ)/8) ∧ Real.exp ((-543/28672 : ℝ)/8) ≤ (997635507694550643/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-543/28672 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0128_exp_lower : (918091079544426797/1000000000000000000 : ℝ) ≤ Real.exp ((-5469355397961/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469355397961/8000000000000 : ℝ)/8) ≤ (459045539772213399/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469355397961/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0128_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019045623947/1000000000000 : ℝ) ≤ 4*Real.exp (4343/32768 : ℝ)*Real.exp (-mu (radius 7 (543/4096 : ℝ))) ∧ (2019/1000 : ℝ) < (2019045623947/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (543/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0128_exp_radius
  have hrNumeric : (490619933259/500000000000 : ℝ) ≤ Real.exp (-543/28672 : ℝ) ∧ Real.exp (-543/28672 : ℝ) ≤ (981239866519/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490619933259/500000000000 : ℝ) ≤ (radius 7 (543/4096 : ℝ)) ∧ (radius 7 (543/4096 : ℝ)) ≤ (981239866519/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (543/4096 : ℝ)) (490619933259/500000000000 : ℝ) (981239866519/1000000000000 : ℝ) (48197720611/250000000000 : ℝ) (3855817649/20000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (543/4096 : ℝ)) (490619933259/500000000000 : ℝ) (981239866519/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (543/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490619933259/500000000000 : ℝ) (981239866519/1000000000000 : ℝ) (990619933259/1000000000000 : ℝ) (49530996663/50000000000 : ℝ) (495287761437/500000000000 : ℝ) (7924604183/8000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (543/4096 : ℝ)) 1 (990619933259/1000000000000 : ℝ) (49530996663/50000000000 : ℝ) (495287761437/500000000000 : ℝ) (7924604183/8000000000 : ℝ) (495298864033/500000000000 : ℝ) (247649432017/250000000000 : ℝ) (990597727817/1000000000000 : ℝ) (990597727819/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (543/4096 : ℝ)) 2 (495298864033/500000000000 : ℝ) (247649432017/250000000000 : ℝ) (990597727817/1000000000000 : ℝ) (990597727819/1000000000000 : ℝ) (990597727941/1000000000000 : ℝ) (123824715993/125000000000 : ℝ) (990597727941/1000000000000 : ℝ) (123824715993/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (543/4096 : ℝ)) 3 (990597727941/1000000000000 : ℝ) (123824715993/125000000000 : ℝ) (990597727941/1000000000000 : ℝ) (123824715993/125000000000 : ℝ) (990597727941/1000000000000 : ℝ) (123824715993/125000000000 : ℝ) (990597727941/1000000000000 : ℝ) (123824715993/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (543/4096 : ℝ)) 4 (990597727941/1000000000000 : ℝ) (123824715993/125000000000 : ℝ) (990597727941/1000000000000 : ℝ) (123824715993/125000000000 : ℝ) (990597727941/1000000000000 : ℝ) (123824715993/125000000000 : ℝ) (990597727941/1000000000000 : ℝ) (123824715993/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (543/4096 : ℝ)) 5 (990597727941/1000000000000 : ℝ) (123824715993/125000000000 : ℝ) (990597727941/1000000000000 : ℝ) (123824715993/125000000000 : ℝ) (990597727941/1000000000000 : ℝ) (123824715993/125000000000 : ℝ) (990597727941/1000000000000 : ℝ) (123824715993/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (543/4096 : ℝ)) 6 (990597727941/1000000000000 : ℝ) (123824715993/125000000000 : ℝ) (990597727941/1000000000000 : ℝ) (123824715993/125000000000 : ℝ) (990597727941/1000000000000 : ℝ) (123824715993/125000000000 : ℝ) (990597727941/1000000000000 : ℝ) (123824715993/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (543/4096 : ℝ)) 7 (990597727941/1000000000000 : ℝ) (123824715993/125000000000 : ℝ) (990597727941/1000000000000 : ℝ) (123824715993/125000000000 : ℝ) (990597727941/1000000000000 : ℝ) (123824715993/125000000000 : ℝ) (990597727941/1000000000000 : ℝ) (123824715993/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (543/4096 : ℝ))) (48197720611/250000000000 : ℝ) (3855817649/20000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (543/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (48197720611/250000000000 : ℝ) (3855817649/20000000000 : ℝ) (298197720611/500000000000 : ℝ) (23855817649/40000000000 : ℝ) (219539792773/500000000000 : ℝ) (219539792777/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (543/4096 : ℝ))) 1 (298197720611/500000000000 : ℝ) (23855817649/40000000000 : ℝ) (219539792773/500000000000 : ℝ) (219539792777/500000000000 : ℝ) (64717189173/125000000000 : ℝ) (51773751339/100000000000 : ℝ) (255863764117/500000000000 : ℝ) (511727528241/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (543/4096 : ℝ))) 2 (64717189173/125000000000 : ℝ) (51773751339/100000000000 : ℝ) (255863764117/500000000000 : ℝ) (511727528241/1000000000000 : ℝ) (514732520809/1000000000000 : ℝ) (32170782551/62500000000 : ℝ) (514723749207/1000000000000 : ℝ) (257361874607/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (543/4096 : ℝ))) 3 (514732520809/1000000000000 : ℝ) (32170782551/62500000000 : ℝ) (514723749207/1000000000000 : ℝ) (257361874607/500000000000 : ℝ) (16085254219/31250000000 : ℝ) (102945627003/200000000000 : ℝ) (514728134989/1000000000000 : ℝ) (514728134997/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (543/4096 : ℝ))) 4 (16085254219/31250000000 : ℝ) (102945627003/200000000000 : ℝ) (514728134989/1000000000000 : ℝ) (514728134997/1000000000000 : ℝ) (257364067499/500000000000 : ℝ) (257364067503/500000000000 : ℝ) (257364067499/500000000000 : ℝ) (257364067503/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (543/4096 : ℝ))) 5 (257364067499/500000000000 : ℝ) (257364067503/500000000000 : ℝ) (257364067499/500000000000 : ℝ) (257364067503/500000000000 : ℝ) (257364067499/500000000000 : ℝ) (257364067503/500000000000 : ℝ) (257364067499/500000000000 : ℝ) (257364067503/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (543/4096 : ℝ))) 6 (257364067499/500000000000 : ℝ) (257364067503/500000000000 : ℝ) (257364067499/500000000000 : ℝ) (257364067503/500000000000 : ℝ) (257364067499/500000000000 : ℝ) (257364067503/500000000000 : ℝ) (257364067499/500000000000 : ℝ) (257364067503/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (543/4096 : ℝ))) 7 (257364067499/500000000000 : ℝ) (257364067503/500000000000 : ℝ) (257364067499/500000000000 : ℝ) (257364067503/500000000000 : ℝ) (257364067499/500000000000 : ℝ) (257364067503/500000000000 : ℝ) (257364067499/500000000000 : ℝ) (257364067503/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (543/4096 : ℝ)) hmem 8 (990597727941/1000000000000 : ℝ) (123824715993/125000000000 : ℝ) (990597727941/1000000000000 : ℝ) (123824715993/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (543/4096 : ℝ))) hcmem 8 (257364067499/500000000000 : ℝ) (257364067503/500000000000 : ℝ) (257364067499/500000000000 : ℝ) (257364067503/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (543/4096 : ℝ)) (990597727941/1000000000000 : ℝ) (123824715993/125000000000 : ℝ) (257364067499/500000000000 : ℝ) (257364067503/500000000000 : ℝ) (408103633263/500000000000 : ℝ) (408103633271/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0128_exp_lower
  have heNumeric : (2019045623947/1000000000000 : ℝ)/4 ≤ Real.exp (-5469355397961/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019045623947/1000000000000 : ℝ)/4 ≤ Real.exp ((4343/32768 : ℝ)-(408103633271/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4343/32768 : ℝ) (543/4096 : ℝ) (408103633271/500000000000 : ℝ) (2019045623947/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0129; no trusted numerical premise.
theorem cover7_leaf0129_exp_radius : (199526992805298519/200000000000000000 : ℝ) ≤ Real.exp ((-4345/229376 : ℝ)/8) ∧ Real.exp ((-4345/229376 : ℝ)/8) ≤ (249408741006623149/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4345/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0129_exp_lower : (91809101565368181/100000000000000000 : ℝ) ≤ Real.exp ((-21364686921/31250000000 : ℝ)/8) ∧ Real.exp ((-21364686921/31250000000 : ℝ)/8) ≤ (918091015653681811/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21364686921/31250000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0129_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (201904449989/100000000000 : ℝ) ≤ 4*Real.exp (543/4096 : ℝ)*Real.exp (-mu (radius 7 (4345/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (201904449989/100000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4345/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0129_exp_radius
  have hrNumeric : (981235588661/1000000000000 : ℝ) ≤ Real.exp (-4345/229376 : ℝ) ∧ Real.exp (-4345/229376 : ℝ) ≤ (490617794331/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (981235588661/1000000000000 : ℝ) ≤ (radius 7 (4345/32768 : ℝ)) ∧ (radius 7 (4345/32768 : ℝ)) ≤ (490617794331/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4345/32768 : ℝ)) (981235588661/1000000000000 : ℝ) (490617794331/500000000000 : ℝ) (192812654001/1000000000000 : ℝ) (192812654007/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4345/32768 : ℝ)) (981235588661/1000000000000 : ℝ) (490617794331/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4345/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (981235588661/1000000000000 : ℝ) (490617794331/500000000000 : ℝ) (99061779433/100000000000 : ℝ) (990617794331/1000000000000 : ℝ) (990573363593/1000000000000 : ℝ) (198114672719/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4345/32768 : ℝ)) 1 (99061779433/100000000000 : ℝ) (990617794331/1000000000000 : ℝ) (990573363593/1000000000000 : ℝ) (198114672719/200000000000 : ℝ) (990595578961/1000000000000 : ℝ) (990595578963/1000000000000 : ℝ) (123824447339/125000000000 : ℝ) (495297789357/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4345/32768 : ℝ)) 2 (990595578961/1000000000000 : ℝ) (990595578963/1000000000000 : ℝ) (123824447339/125000000000 : ℝ) (495297789357/500000000000 : ℝ) (247648894709/250000000000 : ℝ) (990595578839/1000000000000 : ℝ) (247648894709/250000000000 : ℝ) (990595578839/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4345/32768 : ℝ)) 3 (247648894709/250000000000 : ℝ) (990595578839/1000000000000 : ℝ) (247648894709/250000000000 : ℝ) (990595578839/1000000000000 : ℝ) (247648894709/250000000000 : ℝ) (990595578839/1000000000000 : ℝ) (247648894709/250000000000 : ℝ) (990595578839/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4345/32768 : ℝ)) 4 (247648894709/250000000000 : ℝ) (990595578839/1000000000000 : ℝ) (247648894709/250000000000 : ℝ) (990595578839/1000000000000 : ℝ) (247648894709/250000000000 : ℝ) (990595578839/1000000000000 : ℝ) (247648894709/250000000000 : ℝ) (990595578839/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4345/32768 : ℝ)) 5 (247648894709/250000000000 : ℝ) (990595578839/1000000000000 : ℝ) (247648894709/250000000000 : ℝ) (990595578839/1000000000000 : ℝ) (247648894709/250000000000 : ℝ) (990595578839/1000000000000 : ℝ) (247648894709/250000000000 : ℝ) (990595578839/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4345/32768 : ℝ)) 6 (247648894709/250000000000 : ℝ) (990595578839/1000000000000 : ℝ) (247648894709/250000000000 : ℝ) (990595578839/1000000000000 : ℝ) (247648894709/250000000000 : ℝ) (990595578839/1000000000000 : ℝ) (247648894709/250000000000 : ℝ) (990595578839/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4345/32768 : ℝ)) 7 (247648894709/250000000000 : ℝ) (990595578839/1000000000000 : ℝ) (247648894709/250000000000 : ℝ) (990595578839/1000000000000 : ℝ) (247648894709/250000000000 : ℝ) (990595578839/1000000000000 : ℝ) (247648894709/250000000000 : ℝ) (990595578839/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4345/32768 : ℝ))) (192812654001/1000000000000 : ℝ) (192812654007/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4345/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (192812654001/1000000000000 : ℝ) (192812654007/1000000000000 : ℝ) (596406327/1000000000 : ℝ) (149101581751/250000000000 : ℝ) (219552188557/500000000000 : ℝ) (219552188561/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4345/32768 : ℝ))) 1 (596406327/1000000000 : ℝ) (149101581751/250000000000 : ℝ) (219552188557/500000000000 : ℝ) (219552188561/500000000000 : ℝ) (517755352057/1000000000000 : ℝ) (517755352063/1000000000000 : ℝ) (255873322527/500000000000 : ℝ) (511746645061/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4345/32768 : ℝ))) 2 (517755352057/1000000000000 : ℝ) (517755352063/1000000000000 : ℝ) (255873322527/500000000000 : ℝ) (511746645061/1000000000000 : ℝ) (102950199711/200000000000 : ℝ) (257375499281/500000000000 : ℝ) (514742230999/1000000000000 : ℝ) (257371115503/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4345/32768 : ℝ))) 3 (102950199711/200000000000 : ℝ) (257375499281/500000000000 : ℝ) (514742230999/1000000000000 : ℝ) (257371115503/500000000000 : ℝ) (514746614777/1000000000000 : ℝ) (502682241/976562500 : ℝ) (257373307379/500000000000 : ℝ) (257373307383/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4345/32768 : ℝ))) 4 (514746614777/1000000000000 : ℝ) (502682241/976562500 : ℝ) (257373307379/500000000000 : ℝ) (257373307383/500000000000 : ℝ) (514746614767/1000000000000 : ℝ) (20589864591/40000000000 : ℝ) (514746614767/1000000000000 : ℝ) (20589864591/40000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4345/32768 : ℝ))) 5 (514746614767/1000000000000 : ℝ) (20589864591/40000000000 : ℝ) (514746614767/1000000000000 : ℝ) (20589864591/40000000000 : ℝ) (514746614767/1000000000000 : ℝ) (20589864591/40000000000 : ℝ) (514746614767/1000000000000 : ℝ) (20589864591/40000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4345/32768 : ℝ))) 6 (514746614767/1000000000000 : ℝ) (20589864591/40000000000 : ℝ) (514746614767/1000000000000 : ℝ) (20589864591/40000000000 : ℝ) (514746614767/1000000000000 : ℝ) (20589864591/40000000000 : ℝ) (514746614767/1000000000000 : ℝ) (20589864591/40000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4345/32768 : ℝ))) 7 (514746614767/1000000000000 : ℝ) (20589864591/40000000000 : ℝ) (514746614767/1000000000000 : ℝ) (20589864591/40000000000 : ℝ) (514746614767/1000000000000 : ℝ) (20589864591/40000000000 : ℝ) (514746614767/1000000000000 : ℝ) (20589864591/40000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4345/32768 : ℝ)) hmem 8 (247648894709/250000000000 : ℝ) (990595578839/1000000000000 : ℝ) (247648894709/250000000000 : ℝ) (990595578839/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4345/32768 : ℝ))) hcmem 8 (514746614767/1000000000000 : ℝ) (20589864591/40000000000 : ℝ) (514746614767/1000000000000 : ℝ) (20589864591/40000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4345/32768 : ℝ)) (247648894709/250000000000 : ℝ) (990595578839/1000000000000 : ℝ) (514746614767/1000000000000 : ℝ) (20589864591/40000000000 : ℝ) (816238340831/1000000000000 : ℝ) (816238340847/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0129_exp_lower
  have heNumeric : (201904449989/100000000000 : ℝ)/4 ≤ Real.exp (-21364686921/31250000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (201904449989/100000000000 : ℝ)/4 ≤ Real.exp ((543/4096 : ℝ)-(816238340847/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (543/4096 : ℝ) (4345/32768 : ℝ) (816238340847/1000000000000 : ℝ) (201904449989/100000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0130; no trusted numerical premise.
theorem cover7_leaf0130_exp_radius : (124704302544841353/125000000000000000 : ℝ) ≤ Real.exp ((-2173/114688 : ℝ)/8) ∧ Real.exp ((-2173/114688 : ℝ)/8) ≤ (39905376814349233/40000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2173/114688 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0130_exp_lower : (57380684519526169/62500000000000000 : ℝ) ≤ Real.exp ((-5469364267287/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469364267287/8000000000000 : ℝ)/8) ≤ (183618190462483741/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469364267287/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0130_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019043385501/1000000000000 : ℝ) ≤ 4*Real.exp (4345/32768 : ℝ)*Real.exp (-mu (radius 7 (2173/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (2019043385501/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2173/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0130_exp_radius
  have hrNumeric : (981231310823/1000000000000 : ℝ) ≤ Real.exp (-2173/114688 : ℝ) ∧ Real.exp (-2173/114688 : ℝ) ≤ (122653913853/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (981231310823/1000000000000 : ℝ) ≤ (radius 7 (2173/16384 : ℝ)) ∧ (radius 7 (2173/16384 : ℝ)) ≤ (122653913853/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2173/16384 : ℝ)) (981231310823/1000000000000 : ℝ) (122653913853/125000000000 : ℝ) (48208605727/250000000000 : ℝ) (38566884583/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2173/16384 : ℝ)) (981231310823/1000000000000 : ℝ) (122653913853/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2173/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (981231310823/1000000000000 : ℝ) (122653913853/125000000000 : ℝ) (990615655411/1000000000000 : ℝ) (247653913853/250000000000 : ℝ) (990571204317/1000000000000 : ℝ) (495285602159/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2173/16384 : ℝ)) 1 (990615655411/1000000000000 : ℝ) (247653913853/250000000000 : ℝ) (990571204317/1000000000000 : ℝ) (495285602159/500000000000 : ℝ) (123824178733/125000000000 : ℝ) (198118685973/200000000000 : ℝ) (495296714807/500000000000 : ℝ) (61912089351/62500000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2173/16384 : ℝ)) 2 (123824178733/125000000000 : ℝ) (198118685973/200000000000 : ℝ) (495296714807/500000000000 : ℝ) (61912089351/62500000000 : ℝ) (990593429739/1000000000000 : ℝ) (990593429741/1000000000000 : ℝ) (495296714869/500000000000 : ℝ) (990593429741/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2173/16384 : ℝ)) 3 (990593429739/1000000000000 : ℝ) (990593429741/1000000000000 : ℝ) (495296714869/500000000000 : ℝ) (990593429741/1000000000000 : ℝ) (495296714869/500000000000 : ℝ) (990593429741/1000000000000 : ℝ) (495296714869/500000000000 : ℝ) (990593429741/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2173/16384 : ℝ)) 4 (495296714869/500000000000 : ℝ) (990593429741/1000000000000 : ℝ) (495296714869/500000000000 : ℝ) (990593429741/1000000000000 : ℝ) (495296714869/500000000000 : ℝ) (990593429741/1000000000000 : ℝ) (495296714869/500000000000 : ℝ) (990593429741/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2173/16384 : ℝ)) 5 (495296714869/500000000000 : ℝ) (990593429741/1000000000000 : ℝ) (495296714869/500000000000 : ℝ) (990593429741/1000000000000 : ℝ) (495296714869/500000000000 : ℝ) (990593429741/1000000000000 : ℝ) (495296714869/500000000000 : ℝ) (990593429741/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2173/16384 : ℝ)) 6 (495296714869/500000000000 : ℝ) (990593429741/1000000000000 : ℝ) (495296714869/500000000000 : ℝ) (990593429741/1000000000000 : ℝ) (495296714869/500000000000 : ℝ) (990593429741/1000000000000 : ℝ) (495296714869/500000000000 : ℝ) (990593429741/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2173/16384 : ℝ)) 7 (495296714869/500000000000 : ℝ) (990593429741/1000000000000 : ℝ) (495296714869/500000000000 : ℝ) (990593429741/1000000000000 : ℝ) (495296714869/500000000000 : ℝ) (990593429741/1000000000000 : ℝ) (495296714869/500000000000 : ℝ) (990593429741/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2173/16384 : ℝ))) (48208605727/250000000000 : ℝ) (38566884583/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2173/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (48208605727/250000000000 : ℝ) (38566884583/200000000000 : ℝ) (298208605727/500000000000 : ℝ) (298208605729/500000000000 : ℝ) (54891145533/125000000000 : ℝ) (439129164273/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2173/16384 : ℝ))) 1 (298208605727/500000000000 : ℝ) (298208605729/500000000000 : ℝ) (54891145533/125000000000 : ℝ) (439129164273/1000000000000 : ℝ) (517773187859/1000000000000 : ℝ) (258886593933/500000000000 : ℝ) (31985359909/62500000000 : ℝ) (63970719819/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2173/16384 : ℝ))) 2 (517773187859/1000000000000 : ℝ) (258886593933/500000000000 : ℝ) (31985359909/62500000000 : ℝ) (63970719819/125000000000 : ℝ) (514769473201/1000000000000 : ℝ) (514769473209/1000000000000 : ℝ) (514760709687/1000000000000 : ℝ) (8043136089/15625000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2173/16384 : ℝ))) 3 (514769473201/1000000000000 : ℝ) (514769473209/1000000000000 : ℝ) (514760709687/1000000000000 : ℝ) (8043136089/15625000000 : ℝ) (128691272861/250000000000 : ℝ) (514765091453/1000000000000 : ℝ) (20590603657/40000000000 : ℝ) (257382545717/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2173/16384 : ℝ))) 4 (128691272861/250000000000 : ℝ) (514765091453/1000000000000 : ℝ) (20590603657/40000000000 : ℝ) (257382545717/500000000000 : ℝ) (257382545717/500000000000 : ℝ) (128691272861/250000000000 : ℝ) (257382545717/500000000000 : ℝ) (128691272861/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2173/16384 : ℝ))) 5 (257382545717/500000000000 : ℝ) (128691272861/250000000000 : ℝ) (257382545717/500000000000 : ℝ) (128691272861/250000000000 : ℝ) (257382545717/500000000000 : ℝ) (128691272861/250000000000 : ℝ) (257382545717/500000000000 : ℝ) (128691272861/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2173/16384 : ℝ))) 6 (257382545717/500000000000 : ℝ) (128691272861/250000000000 : ℝ) (257382545717/500000000000 : ℝ) (128691272861/250000000000 : ℝ) (257382545717/500000000000 : ℝ) (128691272861/250000000000 : ℝ) (257382545717/500000000000 : ℝ) (128691272861/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2173/16384 : ℝ))) 7 (257382545717/500000000000 : ℝ) (128691272861/250000000000 : ℝ) (257382545717/500000000000 : ℝ) (128691272861/250000000000 : ℝ) (257382545717/500000000000 : ℝ) (128691272861/250000000000 : ℝ) (257382545717/500000000000 : ℝ) (128691272861/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2173/16384 : ℝ)) hmem 8 (495296714869/500000000000 : ℝ) (990593429741/1000000000000 : ℝ) (495296714869/500000000000 : ℝ) (990593429741/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2173/16384 : ℝ))) hcmem 8 (257382545717/500000000000 : ℝ) (128691272861/250000000000 : ℝ) (257382545717/500000000000 : ℝ) (128691272861/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2173/16384 : ℝ)) (495296714869/500000000000 : ℝ) (990593429741/1000000000000 : ℝ) (257382545717/500000000000 : ℝ) (128691272861/250000000000 : ℝ) (163253882069/200000000000 : ℝ) (204067352591/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0130_exp_lower
  have heNumeric : (2019043385501/1000000000000 : ℝ)/4 ≤ Real.exp (-5469364267287/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019043385501/1000000000000 : ℝ)/4 ≤ Real.exp ((4345/32768 : ℝ)-(204067352591/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4345/32768 : ℝ) (2173/16384 : ℝ) (204067352591/250000000000 : ℝ) (2019043385501/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0131; no trusted numerical premise.
theorem cover7_leaf0131_exp_radius : (62352117293204083/62500000000000000 : ℝ) ≤ Real.exp ((-621/32768 : ℝ)/8) ∧ Real.exp ((-621/32768 : ℝ)/8) ≤ (997633876691265329/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-621/32768 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0131_exp_lower : (229522722379958509/250000000000000000 : ℝ) ≤ Real.exp ((-109387372891/160000000000 : ℝ)/8) ∧ Real.exp ((-109387372891/160000000000 : ℝ)/8) ≤ (918090889519834037/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-109387372891/160000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0131_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009521140383/500000000000 : ℝ) ≤ 4*Real.exp (2173/16384 : ℝ)*Real.exp (-mu (radius 7 (4347/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (1009521140383/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4347/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0131_exp_radius
  have hrNumeric : (981227033003/1000000000000 : ℝ) ≤ Real.exp (-621/32768 : ℝ) ∧ Real.exp (-621/32768 : ℝ) ≤ (245306758251/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (981227033003/1000000000000 : ℝ) ≤ (radius 7 (4347/32768 : ℝ)) ∧ (radius 7 (4347/32768 : ℝ)) ≤ (245306758251/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4347/32768 : ℝ)) (981227033003/1000000000000 : ℝ) (245306758251/250000000000 : ℝ) (48214047293/250000000000 : ℝ) (96428094589/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4347/32768 : ℝ)) (981227033003/1000000000000 : ℝ) (245306758251/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4347/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (981227033003/1000000000000 : ℝ) (245306758251/250000000000 : ℝ) (990613516501/1000000000000 : ℝ) (495306758251/500000000000 : ℝ) (198113809009/200000000000 : ℝ) (990569045047/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4347/32768 : ℝ)) 1 (990613516501/1000000000000 : ℝ) (495306758251/500000000000 : ℝ) (198113809009/200000000000 : ℝ) (990569045047/1000000000000 : ℝ) (990591280773/1000000000000 : ℝ) (39623651231/40000000000 : ℝ) (990591280523/1000000000000 : ℝ) (39623651221/40000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4347/32768 : ℝ)) 2 (990591280773/1000000000000 : ℝ) (39623651231/40000000000 : ℝ) (990591280523/1000000000000 : ℝ) (39623651221/40000000000 : ℝ) (123823910081/125000000000 : ℝ) (19811825613/20000000000 : ℝ) (990591280647/1000000000000 : ℝ) (19811825613/20000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4347/32768 : ℝ)) 3 (123823910081/125000000000 : ℝ) (19811825613/20000000000 : ℝ) (990591280647/1000000000000 : ℝ) (19811825613/20000000000 : ℝ) (990591280647/1000000000000 : ℝ) (19811825613/20000000000 : ℝ) (990591280647/1000000000000 : ℝ) (19811825613/20000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4347/32768 : ℝ)) 4 (990591280647/1000000000000 : ℝ) (19811825613/20000000000 : ℝ) (990591280647/1000000000000 : ℝ) (19811825613/20000000000 : ℝ) (990591280647/1000000000000 : ℝ) (19811825613/20000000000 : ℝ) (990591280647/1000000000000 : ℝ) (19811825613/20000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4347/32768 : ℝ)) 5 (990591280647/1000000000000 : ℝ) (19811825613/20000000000 : ℝ) (990591280647/1000000000000 : ℝ) (19811825613/20000000000 : ℝ) (990591280647/1000000000000 : ℝ) (19811825613/20000000000 : ℝ) (990591280647/1000000000000 : ℝ) (19811825613/20000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4347/32768 : ℝ)) 6 (990591280647/1000000000000 : ℝ) (19811825613/20000000000 : ℝ) (990591280647/1000000000000 : ℝ) (19811825613/20000000000 : ℝ) (990591280647/1000000000000 : ℝ) (19811825613/20000000000 : ℝ) (990591280647/1000000000000 : ℝ) (19811825613/20000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4347/32768 : ℝ)) 7 (990591280647/1000000000000 : ℝ) (19811825613/20000000000 : ℝ) (990591280647/1000000000000 : ℝ) (19811825613/20000000000 : ℝ) (990591280647/1000000000000 : ℝ) (19811825613/20000000000 : ℝ) (990591280647/1000000000000 : ℝ) (19811825613/20000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4347/32768 : ℝ))) (48214047293/250000000000 : ℝ) (96428094589/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4347/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (48214047293/250000000000 : ℝ) (96428094589/500000000000 : ℝ) (298214047293/500000000000 : ℝ) (596428094589/1000000000000 : ℝ) (439153947007/1000000000000 : ℝ) (87830789403/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4347/32768 : ℝ))) 1 (298214047293/500000000000 : ℝ) (596428094589/1000000000000 : ℝ) (439153947007/1000000000000 : ℝ) (87830789403/200000000000 : ℝ) (129447755199/250000000000 : ℝ) (258895510401/500000000000 : ℝ) (63973108589/125000000000 : ℝ) (511784868719/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4347/32768 : ℝ))) 2 (129447755199/250000000000 : ℝ) (258895510401/500000000000 : ℝ) (63973108589/125000000000 : ℝ) (511784868719/1000000000000 : ℝ) (257393972377/500000000000 : ℝ) (514787944761/1000000000000 : ℝ) (804342477/1562500000 : ℝ) (64347398161/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4347/32768 : ℝ))) 3 (257393972377/500000000000 : ℝ) (514787944761/1000000000000 : ℝ) (804342477/1562500000 : ℝ) (64347398161/125000000000 : ℝ) (514783565017/1000000000000 : ℝ) (20591342601/40000000000 : ℝ) (257391782499/500000000000 : ℝ) (257391782503/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4347/32768 : ℝ))) 4 (514783565017/1000000000000 : ℝ) (20591342601/40000000000 : ℝ) (257391782499/500000000000 : ℝ) (257391782503/500000000000 : ℝ) (514783565007/1000000000000 : ℝ) (64347945627/125000000000 : ℝ) (514783565007/1000000000000 : ℝ) (64347945627/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4347/32768 : ℝ))) 5 (514783565007/1000000000000 : ℝ) (64347945627/125000000000 : ℝ) (514783565007/1000000000000 : ℝ) (64347945627/125000000000 : ℝ) (514783565007/1000000000000 : ℝ) (64347945627/125000000000 : ℝ) (514783565007/1000000000000 : ℝ) (64347945627/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4347/32768 : ℝ))) 6 (514783565007/1000000000000 : ℝ) (64347945627/125000000000 : ℝ) (514783565007/1000000000000 : ℝ) (64347945627/125000000000 : ℝ) (514783565007/1000000000000 : ℝ) (64347945627/125000000000 : ℝ) (514783565007/1000000000000 : ℝ) (64347945627/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4347/32768 : ℝ))) 7 (514783565007/1000000000000 : ℝ) (64347945627/125000000000 : ℝ) (514783565007/1000000000000 : ℝ) (64347945627/125000000000 : ℝ) (514783565007/1000000000000 : ℝ) (64347945627/125000000000 : ℝ) (514783565007/1000000000000 : ℝ) (64347945627/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4347/32768 : ℝ)) hmem 8 (990591280647/1000000000000 : ℝ) (19811825613/20000000000 : ℝ) (990591280647/1000000000000 : ℝ) (19811825613/20000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4347/32768 : ℝ))) hcmem 8 (514783565007/1000000000000 : ℝ) (64347945627/125000000000 : ℝ) (514783565007/1000000000000 : ℝ) (64347945627/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4347/32768 : ℝ)) (990591280647/1000000000000 : ℝ) (19811825613/20000000000 : ℝ) (514783565007/1000000000000 : ℝ) (64347945627/125000000000 : ℝ) (408150237541/500000000000 : ℝ) (8163004751/10000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0131_exp_lower
  have heNumeric : (1009521140383/500000000000 : ℝ)/4 ≤ Real.exp (-109387372891/160000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009521140383/500000000000 : ℝ)/4 ≤ Real.exp ((2173/16384 : ℝ)-(8163004751/10000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2173/16384 : ℝ) (4347/32768 : ℝ) (8163004751/10000000000 : ℝ) (1009521140383/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0132; no trusted numerical premise.
theorem cover7_leaf0132_exp_radius : (997633333024096107/1000000000000000000 : ℝ) ≤ Real.exp ((-1087/57344 : ℝ)/8) ∧ Real.exp ((-1087/57344 : ℝ)/8) ≤ (249408333256024027/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1087/57344 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0132_exp_lower : (918090827276386739/1000000000000000000 : ℝ) ≤ Real.exp ((-5469372983533/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469372983533/8000000000000 : ℝ)/8) ≤ (45904541363819337/50000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469372983533/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0132_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019041185693/1000000000000 : ℝ) ≤ 4*Real.exp (4347/32768 : ℝ)*Real.exp (-mu (radius 7 (1087/8192 : ℝ))) ∧ (2019/1000 : ℝ) < (2019041185693/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (1087/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0132_exp_radius
  have hrNumeric : (490611377601/500000000000 : ℝ) ≤ Real.exp (-1087/57344 : ℝ) ∧ Real.exp (-1087/57344 : ℝ) ≤ (981222755203/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490611377601/500000000000 : ℝ) ≤ (radius 7 (1087/8192 : ℝ)) ∧ (radius 7 (1087/8192 : ℝ)) ≤ (981222755203/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (1087/8192 : ℝ)) (490611377601/500000000000 : ℝ) (981222755203/1000000000000 : ℝ) (48219488197/250000000000 : ℝ) (96438976397/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (1087/8192 : ℝ)) (490611377601/500000000000 : ℝ) (981222755203/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (1087/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490611377601/500000000000 : ℝ) (981222755203/1000000000000 : ℝ) (990611377601/1000000000000 : ℝ) (495305688801/500000000000 : ℝ) (990566885779/1000000000000 : ℝ) (49528344289/50000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (1087/8192 : ℝ)) 1 (990611377601/1000000000000 : ℝ) (495305688801/500000000000 : ℝ) (990566885779/1000000000000 : ℝ) (49528344289/50000000000 : ℝ) (99058913169/100000000000 : ℝ) (990589131691/1000000000000 : ℝ) (12382364143/12500000000 : ℝ) (495294565721/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (1087/8192 : ℝ)) 2 (99058913169/100000000000 : ℝ) (990589131691/1000000000000 : ℝ) (12382364143/12500000000 : ℝ) (495294565721/500000000000 : ℝ) (198117826313/200000000000 : ℝ) (990589131567/1000000000000 : ℝ) (247647282891/250000000000 : ℝ) (990589131567/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (1087/8192 : ℝ)) 3 (198117826313/200000000000 : ℝ) (990589131567/1000000000000 : ℝ) (247647282891/250000000000 : ℝ) (990589131567/1000000000000 : ℝ) (247647282891/250000000000 : ℝ) (990589131567/1000000000000 : ℝ) (247647282891/250000000000 : ℝ) (990589131567/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (1087/8192 : ℝ)) 4 (247647282891/250000000000 : ℝ) (990589131567/1000000000000 : ℝ) (247647282891/250000000000 : ℝ) (990589131567/1000000000000 : ℝ) (247647282891/250000000000 : ℝ) (990589131567/1000000000000 : ℝ) (247647282891/250000000000 : ℝ) (990589131567/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (1087/8192 : ℝ)) 5 (247647282891/250000000000 : ℝ) (990589131567/1000000000000 : ℝ) (247647282891/250000000000 : ℝ) (990589131567/1000000000000 : ℝ) (247647282891/250000000000 : ℝ) (990589131567/1000000000000 : ℝ) (247647282891/250000000000 : ℝ) (990589131567/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (1087/8192 : ℝ)) 6 (247647282891/250000000000 : ℝ) (990589131567/1000000000000 : ℝ) (247647282891/250000000000 : ℝ) (990589131567/1000000000000 : ℝ) (247647282891/250000000000 : ℝ) (990589131567/1000000000000 : ℝ) (247647282891/250000000000 : ℝ) (990589131567/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (1087/8192 : ℝ)) 7 (247647282891/250000000000 : ℝ) (990589131567/1000000000000 : ℝ) (247647282891/250000000000 : ℝ) (990589131567/1000000000000 : ℝ) (247647282891/250000000000 : ℝ) (990589131567/1000000000000 : ℝ) (247647282891/250000000000 : ℝ) (990589131567/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (1087/8192 : ℝ))) (48219488197/250000000000 : ℝ) (96438976397/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (1087/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (48219488197/250000000000 : ℝ) (96438976397/500000000000 : ℝ) (298219488197/500000000000 : ℝ) (596438976397/1000000000000 : ℝ) (54897340667/125000000000 : ℝ) (13724335167/31250000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (1087/8192 : ℝ))) 1 (298219488197/500000000000 : ℝ) (596438976397/1000000000000 : ℝ) (54897340667/125000000000 : ℝ) (13724335167/31250000000 : ℝ) (103561770173/200000000000 : ℝ) (517808850871/1000000000000 : ℝ) (255901987777/500000000000 : ℝ) (511803975561/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (1087/8192 : ℝ))) 2 (103561770173/200000000000 : ℝ) (517808850871/1000000000000 : ℝ) (255901987777/500000000000 : ℝ) (511803975561/1000000000000 : ℝ) (514806413209/1000000000000 : ℝ) (16087700413/31250000000 : ℝ) (257398828887/500000000000 : ℝ) (514797657781/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (1087/8192 : ℝ))) 3 (514806413209/1000000000000 : ℝ) (16087700413/31250000000 : ℝ) (257398828887/500000000000 : ℝ) (514797657781/1000000000000 : ℝ) (514802035491/1000000000000 : ℝ) (514802035499/1000000000000 : ℝ) (32175127217/62500000000 : ℝ) (12870050887/25000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (1087/8192 : ℝ))) 4 (514802035491/1000000000000 : ℝ) (514802035499/1000000000000 : ℝ) (32175127217/62500000000 : ℝ) (12870050887/25000000000 : ℝ) (514802035481/1000000000000 : ℝ) (51480203549/100000000000 : ℝ) (514802035481/1000000000000 : ℝ) (51480203549/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (1087/8192 : ℝ))) 5 (514802035481/1000000000000 : ℝ) (51480203549/100000000000 : ℝ) (514802035481/1000000000000 : ℝ) (51480203549/100000000000 : ℝ) (514802035481/1000000000000 : ℝ) (51480203549/100000000000 : ℝ) (514802035481/1000000000000 : ℝ) (51480203549/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (1087/8192 : ℝ))) 6 (514802035481/1000000000000 : ℝ) (51480203549/100000000000 : ℝ) (514802035481/1000000000000 : ℝ) (51480203549/100000000000 : ℝ) (514802035481/1000000000000 : ℝ) (51480203549/100000000000 : ℝ) (514802035481/1000000000000 : ℝ) (51480203549/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (1087/8192 : ℝ))) 7 (514802035481/1000000000000 : ℝ) (51480203549/100000000000 : ℝ) (514802035481/1000000000000 : ℝ) (51480203549/100000000000 : ℝ) (514802035481/1000000000000 : ℝ) (51480203549/100000000000 : ℝ) (514802035481/1000000000000 : ℝ) (51480203549/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (1087/8192 : ℝ)) hmem 8 (247647282891/250000000000 : ℝ) (990589131567/1000000000000 : ℝ) (247647282891/250000000000 : ℝ) (990589131567/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (1087/8192 : ℝ))) hcmem 8 (514802035481/1000000000000 : ℝ) (51480203549/100000000000 : ℝ) (514802035481/1000000000000 : ℝ) (51480203549/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (1087/8192 : ℝ)) (247647282891/250000000000 : ℝ) (990589131567/1000000000000 : ℝ) (514802035481/1000000000000 : ℝ) (51480203549/100000000000 : ℝ) (408165767517/500000000000 : ℝ) (816331535051/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0132_exp_lower
  have heNumeric : (2019041185693/1000000000000 : ℝ)/4 ≤ Real.exp (-5469372983533/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019041185693/1000000000000 : ℝ)/4 ≤ Real.exp ((4347/32768 : ℝ)-(816331535051/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4347/32768 : ℝ) (1087/8192 : ℝ) (816331535051/1000000000000 : ℝ) (2019041185693/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0133; no trusted numerical premise.
theorem cover7_leaf0133_exp_radius : (997632789357223161/1000000000000000000 : ℝ) ≤ Real.exp ((-4349/229376 : ℝ)/8) ∧ Real.exp ((-4349/229376 : ℝ)/8) ≤ (498816394678611581/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4349/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0133_exp_lower : (183618153116323531/200000000000000000 : ℝ) ≤ Real.exp ((-1367344321067/2000000000000 : ℝ)/8) ∧ Real.exp ((-1367344321067/2000000000000 : ℝ)/8) ≤ (114761345697702207/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1367344321067/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0133_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019040100273/1000000000000 : ℝ) ≤ 4*Real.exp (1087/8192 : ℝ)*Real.exp (-mu (radius 7 (4349/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (2019040100273/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4349/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0133_exp_radius
  have hrNumeric : (49060923871/50000000000 : ℝ) ≤ Real.exp (-4349/229376 : ℝ) ∧ Real.exp (-4349/229376 : ℝ) ≤ (981218477421/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (49060923871/50000000000 : ℝ) ≤ (radius 7 (4349/32768 : ℝ)) ∧ (radius 7 (4349/32768 : ℝ)) ≤ (981218477421/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4349/32768 : ℝ)) (49060923871/50000000000 : ℝ) (981218477421/1000000000000 : ℝ) (192899713757/1000000000000 : ℝ) (192899713763/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4349/32768 : ℝ)) (49060923871/50000000000 : ℝ) (981218477421/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4349/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (49060923871/50000000000 : ℝ) (981218477421/1000000000000 : ℝ) (99060923871/100000000000 : ℝ) (990609238711/1000000000000 : ℝ) (990564726517/1000000000000 : ℝ) (495282363259/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4349/32768 : ℝ)) 1 (99060923871/100000000000 : ℝ) (990609238711/1000000000000 : ℝ) (990564726517/1000000000000 : ℝ) (495282363259/500000000000 : ℝ) (990586982613/1000000000000 : ℝ) (198117396523/200000000000 : ℝ) (990586982363/1000000000000 : ℝ) (198117396473/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4349/32768 : ℝ)) 2 (990586982613/1000000000000 : ℝ) (198117396523/200000000000 : ℝ) (990586982363/1000000000000 : ℝ) (198117396473/200000000000 : ℝ) (123823372811/125000000000 : ℝ) (99058698249/100000000000 : ℝ) (990586982487/1000000000000 : ℝ) (99058698249/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4349/32768 : ℝ)) 3 (123823372811/125000000000 : ℝ) (99058698249/100000000000 : ℝ) (990586982487/1000000000000 : ℝ) (99058698249/100000000000 : ℝ) (990586982487/1000000000000 : ℝ) (99058698249/100000000000 : ℝ) (990586982487/1000000000000 : ℝ) (99058698249/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4349/32768 : ℝ)) 4 (990586982487/1000000000000 : ℝ) (99058698249/100000000000 : ℝ) (990586982487/1000000000000 : ℝ) (99058698249/100000000000 : ℝ) (990586982487/1000000000000 : ℝ) (99058698249/100000000000 : ℝ) (990586982487/1000000000000 : ℝ) (99058698249/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4349/32768 : ℝ)) 5 (990586982487/1000000000000 : ℝ) (99058698249/100000000000 : ℝ) (990586982487/1000000000000 : ℝ) (99058698249/100000000000 : ℝ) (990586982487/1000000000000 : ℝ) (99058698249/100000000000 : ℝ) (990586982487/1000000000000 : ℝ) (99058698249/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4349/32768 : ℝ)) 6 (990586982487/1000000000000 : ℝ) (99058698249/100000000000 : ℝ) (990586982487/1000000000000 : ℝ) (99058698249/100000000000 : ℝ) (990586982487/1000000000000 : ℝ) (99058698249/100000000000 : ℝ) (990586982487/1000000000000 : ℝ) (99058698249/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4349/32768 : ℝ)) 7 (990586982487/1000000000000 : ℝ) (99058698249/100000000000 : ℝ) (990586982487/1000000000000 : ℝ) (99058698249/100000000000 : ℝ) (990586982487/1000000000000 : ℝ) (99058698249/100000000000 : ℝ) (990586982487/1000000000000 : ℝ) (99058698249/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4349/32768 : ℝ))) (192899713757/1000000000000 : ℝ) (192899713763/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4349/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (192899713757/1000000000000 : ℝ) (192899713763/1000000000000 : ℝ) (298224928439/500000000000 : ℝ) (298224928441/500000000000 : ℝ) (219601749627/500000000000 : ℝ) (439203499261/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4349/32768 : ℝ))) 1 (298224928439/500000000000 : ℝ) (298224928441/500000000000 : ℝ) (219601749627/500000000000 : ℝ) (439203499261/1000000000000 : ℝ) (258913339033/500000000000 : ℝ) (64728334759/125000000000 : ℝ) (511823079071/1000000000000 : ℝ) (255911539539/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4349/32768 : ℝ))) 2 (258913339033/500000000000 : ℝ) (64728334759/125000000000 : ℝ) (511823079071/1000000000000 : ℝ) (255911539539/500000000000 : ℝ) (64353109821/125000000000 : ℝ) (20592995143/40000000000 : ℝ) (8044001987/15625000000 : ℝ) (64352015897/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4349/32768 : ℝ))) 3 (64353109821/125000000000 : ℝ) (20592995143/40000000000 : ℝ) (8044001987/15625000000 : ℝ) (64352015897/125000000000 : ℝ) (128705125717/250000000000 : ℝ) (128705125719/250000000000 : ℝ) (514820502849/1000000000000 : ℝ) (514820502857/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4349/32768 : ℝ))) 4 (128705125717/250000000000 : ℝ) (128705125719/250000000000 : ℝ) (514820502849/1000000000000 : ℝ) (514820502857/1000000000000 : ℝ) (257410251429/500000000000 : ℝ) (514820502867/1000000000000 : ℝ) (257410251429/500000000000 : ℝ) (514820502867/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4349/32768 : ℝ))) 5 (257410251429/500000000000 : ℝ) (514820502867/1000000000000 : ℝ) (257410251429/500000000000 : ℝ) (514820502867/1000000000000 : ℝ) (257410251429/500000000000 : ℝ) (514820502867/1000000000000 : ℝ) (257410251429/500000000000 : ℝ) (514820502867/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4349/32768 : ℝ))) 6 (257410251429/500000000000 : ℝ) (514820502867/1000000000000 : ℝ) (257410251429/500000000000 : ℝ) (514820502867/1000000000000 : ℝ) (257410251429/500000000000 : ℝ) (514820502867/1000000000000 : ℝ) (257410251429/500000000000 : ℝ) (514820502867/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4349/32768 : ℝ))) 7 (257410251429/500000000000 : ℝ) (514820502867/1000000000000 : ℝ) (257410251429/500000000000 : ℝ) (514820502867/1000000000000 : ℝ) (257410251429/500000000000 : ℝ) (514820502867/1000000000000 : ℝ) (257410251429/500000000000 : ℝ) (514820502867/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4349/32768 : ℝ)) hmem 8 (990586982487/1000000000000 : ℝ) (99058698249/100000000000 : ℝ) (990586982487/1000000000000 : ℝ) (99058698249/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4349/32768 : ℝ))) hcmem 8 (257410251429/500000000000 : ℝ) (514820502867/1000000000000 : ℝ) (257410251429/500000000000 : ℝ) (514820502867/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4349/32768 : ℝ)) (990586982487/1000000000000 : ℝ) (99058698249/100000000000 : ℝ) (257410251429/500000000000 : ℝ) (514820502867/1000000000000 : ℝ) (204090647551/250000000000 : ℝ) (816362590221/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0133_exp_lower
  have heNumeric : (2019040100273/1000000000000 : ℝ)/4 ≤ Real.exp (-1367344321067/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019040100273/1000000000000 : ℝ)/4 ≤ Real.exp ((1087/8192 : ℝ)-(816362590221/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (1087/8192 : ℝ) (4349/32768 : ℝ) (816362590221/1000000000000 : ℝ) (2019040100273/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0134; no trusted numerical premise.
theorem cover7_leaf0134_exp_radius : (99763224569064649/100000000000000000 : ℝ) ≤ Real.exp ((-2175/114688 : ℝ)/8) ∧ Real.exp ((-2175/114688 : ℝ)/8) ≤ (997632245690646491/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2175/114688 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0134_exp_lower : (57380669027170209/62500000000000000 : ℝ) ≤ Real.exp ((-5469381546811/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469381546811/8000000000000 : ℝ)/8) ≤ (183618140886944669/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469381546811/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0134_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019039024493/1000000000000 : ℝ) ≤ 4*Real.exp (4349/32768 : ℝ)*Real.exp (-mu (radius 7 (2175/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (2019039024493/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2175/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0134_exp_radius
  have hrNumeric : (122651774957/125000000000 : ℝ) ≤ Real.exp (-2175/114688 : ℝ) ∧ Real.exp (-2175/114688 : ℝ) ≤ (981214199657/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (122651774957/125000000000 : ℝ) ≤ (radius 7 (2175/16384 : ℝ)) ∧ (radius 7 (2175/16384 : ℝ)) ≤ (981214199657/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2175/16384 : ℝ)) (122651774957/125000000000 : ℝ) (981214199657/1000000000000 : ℝ) (38584294417/200000000000 : ℝ) (192921472091/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2175/16384 : ℝ)) (122651774957/125000000000 : ℝ) (981214199657/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2175/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (122651774957/125000000000 : ℝ) (981214199657/1000000000000 : ℝ) (247651774957/250000000000 : ℝ) (990607099829/1000000000000 : ℝ) (990562567259/1000000000000 : ℝ) (990562567261/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2175/16384 : ℝ)) 1 (247651774957/250000000000 : ℝ) (990607099829/1000000000000 : ℝ) (990562567259/1000000000000 : ℝ) (990562567261/1000000000000 : ℝ) (990584833543/1000000000000 : ℝ) (198116966709/200000000000 : ℝ) (990584833293/1000000000000 : ℝ) (198116966659/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2175/16384 : ℝ)) 2 (990584833543/1000000000000 : ℝ) (198116966709/200000000000 : ℝ) (990584833293/1000000000000 : ℝ) (198116966659/200000000000 : ℝ) (495292416709/500000000000 : ℝ) (49529241671/50000000000 : ℝ) (990584833417/1000000000000 : ℝ) (49529241671/50000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2175/16384 : ℝ)) 3 (495292416709/500000000000 : ℝ) (49529241671/50000000000 : ℝ) (990584833417/1000000000000 : ℝ) (49529241671/50000000000 : ℝ) (990584833417/1000000000000 : ℝ) (49529241671/50000000000 : ℝ) (990584833417/1000000000000 : ℝ) (49529241671/50000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2175/16384 : ℝ)) 4 (990584833417/1000000000000 : ℝ) (49529241671/50000000000 : ℝ) (990584833417/1000000000000 : ℝ) (49529241671/50000000000 : ℝ) (990584833417/1000000000000 : ℝ) (49529241671/50000000000 : ℝ) (990584833417/1000000000000 : ℝ) (49529241671/50000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2175/16384 : ℝ)) 5 (990584833417/1000000000000 : ℝ) (49529241671/50000000000 : ℝ) (990584833417/1000000000000 : ℝ) (49529241671/50000000000 : ℝ) (990584833417/1000000000000 : ℝ) (49529241671/50000000000 : ℝ) (990584833417/1000000000000 : ℝ) (49529241671/50000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2175/16384 : ℝ)) 6 (990584833417/1000000000000 : ℝ) (49529241671/50000000000 : ℝ) (990584833417/1000000000000 : ℝ) (49529241671/50000000000 : ℝ) (990584833417/1000000000000 : ℝ) (49529241671/50000000000 : ℝ) (990584833417/1000000000000 : ℝ) (49529241671/50000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2175/16384 : ℝ)) 7 (990584833417/1000000000000 : ℝ) (49529241671/50000000000 : ℝ) (990584833417/1000000000000 : ℝ) (49529241671/50000000000 : ℝ) (990584833417/1000000000000 : ℝ) (49529241671/50000000000 : ℝ) (990584833417/1000000000000 : ℝ) (49529241671/50000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2175/16384 : ℝ))) (38584294417/200000000000 : ℝ) (192921472091/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2175/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (38584294417/200000000000 : ℝ) (192921472091/1000000000000 : ℝ) (298230368021/500000000000 : ℝ) (298230368023/500000000000 : ℝ) (13725883399/31250000000 : ℝ) (17569130751/40000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2175/16384 : ℝ))) 1 (298230368021/500000000000 : ℝ) (298230368023/500000000000 : ℝ) (13725883399/31250000000 : ℝ) (17569130751/40000000000 : ℝ) (103568900481/200000000000 : ℝ) (517844502411/1000000000000 : ℝ) (511842179269/1000000000000 : ℝ) (127960544819/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2175/16384 : ℝ))) 2 (103568900481/200000000000 : ℝ) (517844502411/1000000000000 : ℝ) (511842179269/1000000000000 : ℝ) (127960544819/250000000000 : ℝ) (514843340837/1000000000000 : ℝ) (128710835211/250000000000 : ℝ) (51483459347/100000000000 : ℝ) (514834593477/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2175/16384 : ℝ))) 3 (514843340837/1000000000000 : ℝ) (128710835211/250000000000 : ℝ) (51483459347/100000000000 : ℝ) (514834593477/1000000000000 : ℝ) (514838967153/1000000000000 : ℝ) (514838967161/1000000000000 : ℝ) (257419483567/500000000000 : ℝ) (257419483571/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2175/16384 : ℝ))) 4 (514838967153/1000000000000 : ℝ) (514838967161/1000000000000 : ℝ) (257419483567/500000000000 : ℝ) (257419483571/500000000000 : ℝ) (514838967143/1000000000000 : ℝ) (32177435447/62500000000 : ℝ) (514838967143/1000000000000 : ℝ) (32177435447/62500000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2175/16384 : ℝ))) 5 (514838967143/1000000000000 : ℝ) (32177435447/62500000000 : ℝ) (514838967143/1000000000000 : ℝ) (32177435447/62500000000 : ℝ) (514838967143/1000000000000 : ℝ) (32177435447/62500000000 : ℝ) (514838967143/1000000000000 : ℝ) (32177435447/62500000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2175/16384 : ℝ))) 6 (514838967143/1000000000000 : ℝ) (32177435447/62500000000 : ℝ) (514838967143/1000000000000 : ℝ) (32177435447/62500000000 : ℝ) (514838967143/1000000000000 : ℝ) (32177435447/62500000000 : ℝ) (514838967143/1000000000000 : ℝ) (32177435447/62500000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2175/16384 : ℝ))) 7 (514838967143/1000000000000 : ℝ) (32177435447/62500000000 : ℝ) (514838967143/1000000000000 : ℝ) (32177435447/62500000000 : ℝ) (514838967143/1000000000000 : ℝ) (32177435447/62500000000 : ℝ) (514838967143/1000000000000 : ℝ) (32177435447/62500000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2175/16384 : ℝ)) hmem 8 (990584833417/1000000000000 : ℝ) (49529241671/50000000000 : ℝ) (990584833417/1000000000000 : ℝ) (49529241671/50000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2175/16384 : ℝ))) hcmem 8 (514838967143/1000000000000 : ℝ) (32177435447/62500000000 : ℝ) (514838967143/1000000000000 : ℝ) (32177435447/62500000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2175/16384 : ℝ)) (990584833417/1000000000000 : ℝ) (49529241671/50000000000 : ℝ) (514838967143/1000000000000 : ℝ) (32177435447/62500000000 : ℝ) (4081968203/5000000000 : ℝ) (816393640617/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0134_exp_lower
  have heNumeric : (2019039024493/1000000000000 : ℝ)/4 ≤ Real.exp (-5469381546811/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019039024493/1000000000000 : ℝ)/4 ≤ Real.exp ((4349/32768 : ℝ)-(816393640617/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4349/32768 : ℝ) (2175/16384 : ℝ) (816393640617/1000000000000 : ℝ) (2019039024493/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0135; no trusted numerical premise.
theorem cover7_leaf0135_exp_radius : (498815851012183047/500000000000000000 : ℝ) ≤ Real.exp ((-4351/229376 : ℝ)/8) ∧ Real.exp ((-4351/229376 : ℝ)/8) ≤ (199526340404873219/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4351/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0135_exp_lower : (918090643836507027/1000000000000000000 : ℝ) ≤ Real.exp ((-2734692885553/4000000000000 : ℝ)/8) ∧ Real.exp ((-2734692885553/4000000000000 : ℝ)/8) ≤ (229522660959126757/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2734692885553/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0135_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009518979183/500000000000 : ℝ) ≤ 4*Real.exp (2175/16384 : ℝ)*Real.exp (-mu (radius 7 (4351/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (1009518979183/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4351/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0135_exp_radius
  have hrNumeric : (981209921911/1000000000000 : ℝ) ≤ Real.exp (-4351/229376 : ℝ) ∧ Real.exp (-4351/229376 : ℝ) ≤ (122651240239/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (981209921911/1000000000000 : ℝ) ≤ (radius 7 (4351/32768 : ℝ)) ∧ (radius 7 (4351/32768 : ℝ)) ≤ (122651240239/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4351/32768 : ℝ)) (981209921911/1000000000000 : ℝ) (122651240239/125000000000 : ℝ) (192943227767/1000000000000 : ℝ) (192943227773/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4351/32768 : ℝ)) (981209921911/1000000000000 : ℝ) (122651240239/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4351/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (981209921911/1000000000000 : ℝ) (122651240239/125000000000 : ℝ) (198120992191/200000000000 : ℝ) (247651240239/250000000000 : ℝ) (990560408007/1000000000000 : ℝ) (123820051001/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4351/32768 : ℝ)) 1 (198120992191/200000000000 : ℝ) (247651240239/250000000000 : ℝ) (990560408007/1000000000000 : ℝ) (123820051001/125000000000 : ℝ) (990582684481/1000000000000 : ℝ) (495291342241/500000000000 : ℝ) (99058268423/100000000000 : ℝ) (123822835529/125000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4351/32768 : ℝ)) 2 (990582684481/1000000000000 : ℝ) (495291342241/500000000000 : ℝ) (99058268423/100000000000 : ℝ) (123822835529/125000000000 : ℝ) (198116536871/200000000000 : ℝ) (990582684357/1000000000000 : ℝ) (198116536871/200000000000 : ℝ) (990582684357/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4351/32768 : ℝ)) 3 (198116536871/200000000000 : ℝ) (990582684357/1000000000000 : ℝ) (198116536871/200000000000 : ℝ) (990582684357/1000000000000 : ℝ) (198116536871/200000000000 : ℝ) (990582684357/1000000000000 : ℝ) (198116536871/200000000000 : ℝ) (990582684357/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4351/32768 : ℝ)) 4 (198116536871/200000000000 : ℝ) (990582684357/1000000000000 : ℝ) (198116536871/200000000000 : ℝ) (990582684357/1000000000000 : ℝ) (198116536871/200000000000 : ℝ) (990582684357/1000000000000 : ℝ) (198116536871/200000000000 : ℝ) (990582684357/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4351/32768 : ℝ)) 5 (198116536871/200000000000 : ℝ) (990582684357/1000000000000 : ℝ) (198116536871/200000000000 : ℝ) (990582684357/1000000000000 : ℝ) (198116536871/200000000000 : ℝ) (990582684357/1000000000000 : ℝ) (198116536871/200000000000 : ℝ) (990582684357/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4351/32768 : ℝ)) 6 (198116536871/200000000000 : ℝ) (990582684357/1000000000000 : ℝ) (198116536871/200000000000 : ℝ) (990582684357/1000000000000 : ℝ) (198116536871/200000000000 : ℝ) (990582684357/1000000000000 : ℝ) (198116536871/200000000000 : ℝ) (990582684357/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4351/32768 : ℝ)) 7 (198116536871/200000000000 : ℝ) (990582684357/1000000000000 : ℝ) (198116536871/200000000000 : ℝ) (990582684357/1000000000000 : ℝ) (198116536871/200000000000 : ℝ) (990582684357/1000000000000 : ℝ) (198116536871/200000000000 : ℝ) (990582684357/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4351/32768 : ℝ))) (192943227767/1000000000000 : ℝ) (192943227773/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4351/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (192943227767/1000000000000 : ℝ) (192943227773/1000000000000 : ℝ) (596471613883/1000000000000 : ℝ) (596471613887/1000000000000 : ℝ) (439253033873/1000000000000 : ℝ) (439253033881/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4351/32768 : ℝ))) 1 (596471613883/1000000000000 : ℝ) (596471613887/1000000000000 : ℝ) (439253033873/1000000000000 : ℝ) (439253033881/1000000000000 : ℝ) (258931161939/500000000000 : ℝ) (129465580971/250000000000 : ℝ) (102372255229/200000000000 : ℝ) (63982659519/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4351/32768 : ℝ))) 2 (258931161939/500000000000 : ℝ) (129465580971/250000000000 : ℝ) (102372255229/200000000000 : ℝ) (63982659519/125000000000 : ℝ) (514861800011/1000000000000 : ℝ) (257430900009/500000000000 : ℝ) (20594122267/40000000000 : ℝ) (257426528341/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4351/32768 : ℝ))) 3 (514861800011/1000000000000 : ℝ) (257430900009/500000000000 : ℝ) (20594122267/40000000000 : ℝ) (257426528341/500000000000 : ℝ) (514857428343/1000000000000 : ℝ) (10297148567/20000000000 : ℝ) (128714357081/250000000000 : ℝ) (128714357083/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4351/32768 : ℝ))) 4 (514857428343/1000000000000 : ℝ) (10297148567/20000000000 : ℝ) (128714357081/250000000000 : ℝ) (128714357083/250000000000 : ℝ) (514857428333/1000000000000 : ℝ) (514857428341/1000000000000 : ℝ) (514857428333/1000000000000 : ℝ) (514857428341/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4351/32768 : ℝ))) 5 (514857428333/1000000000000 : ℝ) (514857428341/1000000000000 : ℝ) (514857428333/1000000000000 : ℝ) (514857428341/1000000000000 : ℝ) (514857428333/1000000000000 : ℝ) (514857428341/1000000000000 : ℝ) (514857428333/1000000000000 : ℝ) (514857428341/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4351/32768 : ℝ))) 6 (514857428333/1000000000000 : ℝ) (514857428341/1000000000000 : ℝ) (514857428333/1000000000000 : ℝ) (514857428341/1000000000000 : ℝ) (514857428333/1000000000000 : ℝ) (514857428341/1000000000000 : ℝ) (514857428333/1000000000000 : ℝ) (514857428341/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4351/32768 : ℝ))) 7 (514857428333/1000000000000 : ℝ) (514857428341/1000000000000 : ℝ) (514857428333/1000000000000 : ℝ) (514857428341/1000000000000 : ℝ) (514857428333/1000000000000 : ℝ) (514857428341/1000000000000 : ℝ) (514857428333/1000000000000 : ℝ) (514857428341/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4351/32768 : ℝ)) hmem 8 (198116536871/200000000000 : ℝ) (990582684357/1000000000000 : ℝ) (198116536871/200000000000 : ℝ) (990582684357/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4351/32768 : ℝ))) hcmem 8 (514857428333/1000000000000 : ℝ) (514857428341/1000000000000 : ℝ) (514857428333/1000000000000 : ℝ) (514857428341/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4351/32768 : ℝ)) (198116536871/200000000000 : ℝ) (990582684357/1000000000000 : ℝ) (514857428333/1000000000000 : ℝ) (514857428341/1000000000000 : ℝ) (816424686217/1000000000000 : ℝ) (102053085779/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0135_exp_lower
  have heNumeric : (1009518979183/500000000000 : ℝ)/4 ≤ Real.exp (-2734692885553/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009518979183/500000000000 : ℝ)/4 ≤ Real.exp ((2175/16384 : ℝ)-(102053085779/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2175/16384 : ℝ) (4351/32768 : ℝ) (102053085779/125000000000 : ℝ) (1009518979183/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0136; no trusted numerical premise.
theorem cover7_leaf0136_exp_radius : (249407789589595493/250000000000000000 : ℝ) ≤ Real.exp ((-17/896 : ℝ)/8) ∧ Real.exp ((-17/896 : ℝ)/8) ≤ (997631158358381973/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-17/896 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0136_exp_lower : (918090583785132413/1000000000000000000 : ℝ) ≤ Real.exp ((-5469389957281/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469389957281/8000000000000 : ℝ)/8) ≤ (459045291892566207/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469389957281/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0136_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (100951845093/50000000000 : ℝ) ≤ 4*Real.exp (4351/32768 : ℝ)*Real.exp (-mu (radius 7 (17/128 : ℝ))) ∧ (2019/1000 : ℝ) < (100951845093/50000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (17/128 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0136_exp_radius
  have hrNumeric : (122650705523/125000000000 : ℝ) ≤ Real.exp (-17/896 : ℝ) ∧ Real.exp (-17/896 : ℝ) ≤ (196241128837/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (122650705523/125000000000 : ℝ) ≤ (radius 7 (17/128 : ℝ)) ∧ (radius 7 (17/128 : ℝ)) ≤ (196241128837/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (17/128 : ℝ)) (122650705523/125000000000 : ℝ) (196241128837/200000000000 : ℝ) (192964980811/1000000000000 : ℝ) (192964980817/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (17/128 : ℝ)) (122650705523/125000000000 : ℝ) (196241128837/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (17/128 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (122650705523/125000000000 : ℝ) (196241128837/200000000000 : ℝ) (247650705523/250000000000 : ℝ) (990602822093/1000000000000 : ℝ) (495279124379/500000000000 : ℝ) (24763956219/25000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (17/128 : ℝ)) 1 (247650705523/250000000000 : ℝ) (990602822093/1000000000000 : ℝ) (495279124379/500000000000 : ℝ) (24763956219/25000000000 : ℝ) (39623221417/40000000000 : ℝ) (990580535427/1000000000000 : ℝ) (495290267587/500000000000 : ℝ) (123822566897/125000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (17/128 : ℝ)) 2 (39623221417/40000000000 : ℝ) (990580535427/1000000000000 : ℝ) (495290267587/500000000000 : ℝ) (123822566897/125000000000 : ℝ) (990580535299/1000000000000 : ℝ) (495290267651/500000000000 : ℝ) (990580535299/1000000000000 : ℝ) (495290267651/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (17/128 : ℝ)) 3 (990580535299/1000000000000 : ℝ) (495290267651/500000000000 : ℝ) (990580535299/1000000000000 : ℝ) (495290267651/500000000000 : ℝ) (990580535299/1000000000000 : ℝ) (495290267651/500000000000 : ℝ) (990580535299/1000000000000 : ℝ) (495290267651/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (17/128 : ℝ)) 4 (990580535299/1000000000000 : ℝ) (495290267651/500000000000 : ℝ) (990580535299/1000000000000 : ℝ) (495290267651/500000000000 : ℝ) (990580535299/1000000000000 : ℝ) (495290267651/500000000000 : ℝ) (990580535299/1000000000000 : ℝ) (495290267651/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (17/128 : ℝ)) 5 (990580535299/1000000000000 : ℝ) (495290267651/500000000000 : ℝ) (990580535299/1000000000000 : ℝ) (495290267651/500000000000 : ℝ) (990580535299/1000000000000 : ℝ) (495290267651/500000000000 : ℝ) (990580535299/1000000000000 : ℝ) (495290267651/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (17/128 : ℝ)) 6 (990580535299/1000000000000 : ℝ) (495290267651/500000000000 : ℝ) (990580535299/1000000000000 : ℝ) (495290267651/500000000000 : ℝ) (990580535299/1000000000000 : ℝ) (495290267651/500000000000 : ℝ) (990580535299/1000000000000 : ℝ) (495290267651/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (17/128 : ℝ)) 7 (990580535299/1000000000000 : ℝ) (495290267651/500000000000 : ℝ) (990580535299/1000000000000 : ℝ) (495290267651/500000000000 : ℝ) (990580535299/1000000000000 : ℝ) (495290267651/500000000000 : ℝ) (990580535299/1000000000000 : ℝ) (495290267651/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (17/128 : ℝ))) (192964980811/1000000000000 : ℝ) (192964980817/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (17/128 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (192964980811/1000000000000 : ℝ) (192964980817/1000000000000 : ℝ) (119296498081/200000000000 : ℝ) (596482490409/1000000000000 : ℝ) (439277794579/1000000000000 : ℝ) (439277794587/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (17/128 : ℝ))) 1 (119296498081/200000000000 : ℝ) (596482490409/1000000000000 : ℝ) (439277794579/1000000000000 : ℝ) (439277794587/1000000000000 : ℝ) (129470035623/250000000000 : ℝ) (258940071249/500000000000 : ℝ) (102376073941/200000000000 : ℝ) (511880369713/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (17/128 : ℝ))) 2 (129470035623/250000000000 : ℝ) (258940071249/500000000000 : ℝ) (102376073941/200000000000 : ℝ) (511880369713/1000000000000 : ℝ) (257440128049/500000000000 : ℝ) (257440128053/500000000000 : ℝ) (51487151679/100000000000 : ℝ) (257435758399/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (17/128 : ℝ))) 3 (257440128049/500000000000 : ℝ) (257440128053/500000000000 : ℝ) (51487151679/100000000000 : ℝ) (257435758399/500000000000 : ℝ) (128718971611/250000000000 : ℝ) (128718971613/250000000000 : ℝ) (20595035457/40000000000 : ℝ) (257437943217/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (17/128 : ℝ))) 4 (128718971611/250000000000 : ℝ) (128718971613/250000000000 : ℝ) (20595035457/40000000000 : ℝ) (257437943217/500000000000 : ℝ) (257437943217/500000000000 : ℝ) (514875886443/1000000000000 : ℝ) (257437943217/500000000000 : ℝ) (514875886443/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (17/128 : ℝ))) 5 (257437943217/500000000000 : ℝ) (514875886443/1000000000000 : ℝ) (257437943217/500000000000 : ℝ) (514875886443/1000000000000 : ℝ) (257437943217/500000000000 : ℝ) (514875886443/1000000000000 : ℝ) (257437943217/500000000000 : ℝ) (514875886443/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (17/128 : ℝ))) 6 (257437943217/500000000000 : ℝ) (514875886443/1000000000000 : ℝ) (257437943217/500000000000 : ℝ) (514875886443/1000000000000 : ℝ) (257437943217/500000000000 : ℝ) (514875886443/1000000000000 : ℝ) (257437943217/500000000000 : ℝ) (514875886443/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (17/128 : ℝ))) 7 (257437943217/500000000000 : ℝ) (514875886443/1000000000000 : ℝ) (257437943217/500000000000 : ℝ) (514875886443/1000000000000 : ℝ) (257437943217/500000000000 : ℝ) (514875886443/1000000000000 : ℝ) (257437943217/500000000000 : ℝ) (514875886443/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (17/128 : ℝ)) hmem 8 (990580535299/1000000000000 : ℝ) (495290267651/500000000000 : ℝ) (990580535299/1000000000000 : ℝ) (495290267651/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (17/128 : ℝ))) hcmem 8 (257437943217/500000000000 : ℝ) (514875886443/1000000000000 : ℝ) (257437943217/500000000000 : ℝ) (514875886443/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (17/128 : ℝ)) (990580535299/1000000000000 : ℝ) (495290267651/500000000000 : ℝ) (257437943217/500000000000 : ℝ) (514875886443/1000000000000 : ℝ) (102056965883/125000000000 : ℝ) (408227863541/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0136_exp_lower
  have heNumeric : (100951845093/50000000000 : ℝ)/4 ≤ Real.exp (-5469389957281/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (100951845093/50000000000 : ℝ)/4 ≤ Real.exp ((4351/32768 : ℝ)-(408227863541/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4351/32768 : ℝ) (17/128 : ℝ) (408227863541/500000000000 : ℝ) (100951845093/50000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0137; no trusted numerical premise.
theorem cover7_leaf0137_exp_radius : (7981044917541553/8000000000000000 : ℝ) ≤ Real.exp ((-4353/229376 : ℝ)/8) ∧ Real.exp ((-4353/229376 : ℝ)/8) ≤ (498815307346347063/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4353/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0137_exp_lower : (459045262141447311/500000000000000000 : ℝ) ≤ Real.exp ((-683674263147/1000000000000 : ℝ)/8) ∧ Real.exp ((-683674263147/1000000000000 : ℝ)/8) ≤ (918090524282894623/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-683674263147/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0137_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (252379481877/125000000000 : ℝ) ≤ 4*Real.exp (17/128 : ℝ)*Real.exp (-mu (radius 7 (4353/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (252379481877/125000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4353/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0137_exp_radius
  have hrNumeric : (981201366477/1000000000000 : ℝ) ≤ Real.exp (-4353/229376 : ℝ) ∧ Real.exp (-4353/229376 : ℝ) ≤ (490600683239/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (981201366477/1000000000000 : ℝ) ≤ (radius 7 (4353/32768 : ℝ)) ∧ (radius 7 (4353/32768 : ℝ)) ≤ (490600683239/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4353/32768 : ℝ)) (981201366477/1000000000000 : ℝ) (490600683239/500000000000 : ℝ) (96493365603/500000000000 : ℝ) (48246682803/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4353/32768 : ℝ)) (981201366477/1000000000000 : ℝ) (490600683239/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4353/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (981201366477/1000000000000 : ℝ) (490600683239/500000000000 : ℝ) (495300341619/500000000000 : ℝ) (990600683239/1000000000000 : ℝ) (198111217903/200000000000 : ℝ) (990556089517/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4353/32768 : ℝ)) 1 (495300341619/500000000000 : ℝ) (990600683239/1000000000000 : ℝ) (198111217903/200000000000 : ℝ) (990556089517/1000000000000 : ℝ) (123822298297/125000000000 : ℝ) (495289193189/500000000000 : ℝ) (7924627089/8000000000 : ℝ) (61911149133/62500000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4353/32768 : ℝ)) 2 (123822298297/125000000000 : ℝ) (495289193189/500000000000 : ℝ) (7924627089/8000000000 : ℝ) (61911149133/62500000000 : ℝ) (792462709/800000000 : ℝ) (990578386253/1000000000000 : ℝ) (792462709/800000000 : ℝ) (990578386253/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4353/32768 : ℝ)) 3 (792462709/800000000 : ℝ) (990578386253/1000000000000 : ℝ) (792462709/800000000 : ℝ) (990578386253/1000000000000 : ℝ) (792462709/800000000 : ℝ) (990578386253/1000000000000 : ℝ) (792462709/800000000 : ℝ) (990578386253/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4353/32768 : ℝ)) 4 (792462709/800000000 : ℝ) (990578386253/1000000000000 : ℝ) (792462709/800000000 : ℝ) (990578386253/1000000000000 : ℝ) (792462709/800000000 : ℝ) (990578386253/1000000000000 : ℝ) (792462709/800000000 : ℝ) (990578386253/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4353/32768 : ℝ)) 5 (792462709/800000000 : ℝ) (990578386253/1000000000000 : ℝ) (792462709/800000000 : ℝ) (990578386253/1000000000000 : ℝ) (792462709/800000000 : ℝ) (990578386253/1000000000000 : ℝ) (792462709/800000000 : ℝ) (990578386253/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4353/32768 : ℝ)) 6 (792462709/800000000 : ℝ) (990578386253/1000000000000 : ℝ) (792462709/800000000 : ℝ) (990578386253/1000000000000 : ℝ) (792462709/800000000 : ℝ) (990578386253/1000000000000 : ℝ) (792462709/800000000 : ℝ) (990578386253/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4353/32768 : ℝ)) 7 (792462709/800000000 : ℝ) (990578386253/1000000000000 : ℝ) (792462709/800000000 : ℝ) (990578386253/1000000000000 : ℝ) (792462709/800000000 : ℝ) (990578386253/1000000000000 : ℝ) (792462709/800000000 : ℝ) (990578386253/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4353/32768 : ℝ))) (96493365603/500000000000 : ℝ) (48246682803/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4353/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (96493365603/500000000000 : ℝ) (48246682803/250000000000 : ℝ) (596493365603/1000000000000 : ℝ) (298246682803/500000000000 : ℝ) (3514420407/8000000000 : ℝ) (439302550883/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4353/32768 : ℝ))) 1 (596493365603/1000000000000 : ℝ) (298246682803/500000000000 : ℝ) (3514420407/8000000000 : ℝ) (439302550883/1000000000000 : ℝ) (517897958239/1000000000000 : ℝ) (103579591649/200000000000 : ℝ) (255949729971/500000000000 : ℝ) (511899459949/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4353/32768 : ℝ))) 2 (517897958239/1000000000000 : ℝ) (103579591649/200000000000 : ℝ) (255949729971/500000000000 : ℝ) (511899459949/1000000000000 : ℝ) (51489870909/100000000000 : ℝ) (514898709097/1000000000000 : ℝ) (514889973807/1000000000000 : ℝ) (102977994763/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4353/32768 : ℝ))) 3 (51489870909/100000000000 : ℝ) (514898709097/1000000000000 : ℝ) (514889973807/1000000000000 : ℝ) (102977994763/200000000000 : ℝ) (64361792681/125000000000 : ℝ) (32180896341/62500000000 : ℝ) (514894341429/1000000000000 : ℝ) (257447170719/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4353/32768 : ℝ))) 4 (64361792681/125000000000 : ℝ) (32180896341/62500000000 : ℝ) (514894341429/1000000000000 : ℝ) (257447170719/500000000000 : ℝ) (257447170719/500000000000 : ℝ) (514894341447/1000000000000 : ℝ) (257447170719/500000000000 : ℝ) (514894341447/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4353/32768 : ℝ))) 5 (257447170719/500000000000 : ℝ) (514894341447/1000000000000 : ℝ) (257447170719/500000000000 : ℝ) (514894341447/1000000000000 : ℝ) (257447170719/500000000000 : ℝ) (514894341447/1000000000000 : ℝ) (257447170719/500000000000 : ℝ) (514894341447/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4353/32768 : ℝ))) 6 (257447170719/500000000000 : ℝ) (514894341447/1000000000000 : ℝ) (257447170719/500000000000 : ℝ) (514894341447/1000000000000 : ℝ) (257447170719/500000000000 : ℝ) (514894341447/1000000000000 : ℝ) (257447170719/500000000000 : ℝ) (514894341447/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4353/32768 : ℝ))) 7 (257447170719/500000000000 : ℝ) (514894341447/1000000000000 : ℝ) (257447170719/500000000000 : ℝ) (514894341447/1000000000000 : ℝ) (257447170719/500000000000 : ℝ) (514894341447/1000000000000 : ℝ) (257447170719/500000000000 : ℝ) (514894341447/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4353/32768 : ℝ)) hmem 8 (792462709/800000000 : ℝ) (990578386253/1000000000000 : ℝ) (792462709/800000000 : ℝ) (990578386253/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4353/32768 : ℝ))) hcmem 8 (257447170719/500000000000 : ℝ) (514894341447/1000000000000 : ℝ) (257447170719/500000000000 : ℝ) (514894341447/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4353/32768 : ℝ)) (792462709/800000000 : ℝ) (990578386253/1000000000000 : ℝ) (257447170719/500000000000 : ℝ) (514894341447/1000000000000 : ℝ) (81648676313/100000000000 : ℝ) (816486763147/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0137_exp_lower
  have heNumeric : (252379481877/125000000000 : ℝ)/4 ≤ Real.exp (-683674263147/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (252379481877/125000000000 : ℝ)/4 ≤ Real.exp ((17/128 : ℝ)-(816486763147/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (17/128 : ℝ) (4353/32768 : ℝ) (816486763147/1000000000000 : ℝ) (252379481877/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0138; no trusted numerical premise.
theorem cover7_leaf0138_exp_radius : (997630071027302551/1000000000000000000 : ℝ) ≤ Real.exp ((-311/16384 : ℝ)/8) ∧ Real.exp ((-311/16384 : ℝ)/8) ≤ (124703758878412819/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-311/16384 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0138_exp_lower : (918090465326465469/1000000000000000000 : ℝ) ≤ Real.exp ((-5469398215023/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469398215023/8000000000000 : ℝ)/8) ≤ (91809046532646547/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469398215023/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0138_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (126189676111/62500000000 : ℝ) ≤ 4*Real.exp (4353/32768 : ℝ)*Real.exp (-mu (radius 7 (2177/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (126189676111/62500000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2177/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0138_exp_radius
  have hrNumeric : (981197088787/1000000000000 : ℝ) ≤ Real.exp (-311/16384 : ℝ) ∧ Real.exp (-311/16384 : ℝ) ≤ (245299272197/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (981197088787/1000000000000 : ℝ) ≤ (radius 7 (2177/16384 : ℝ)) ∧ (radius 7 (2177/16384 : ℝ)) ≤ (245299272197/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2177/16384 : ℝ)) (981197088787/1000000000000 : ℝ) (245299272197/250000000000 : ℝ) (193008478969/1000000000000 : ℝ) (7720339159/40000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2177/16384 : ℝ)) (981197088787/1000000000000 : ℝ) (245299272197/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2177/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (981197088787/1000000000000 : ℝ) (245299272197/250000000000 : ℝ) (990598544393/1000000000000 : ℝ) (495299272197/500000000000 : ℝ) (247638482569/250000000000 : ℝ) (495276965139/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2177/16384 : ℝ)) 1 (990598544393/1000000000000 : ℝ) (495299272197/500000000000 : ℝ) (247638482569/250000000000 : ℝ) (495276965139/500000000000 : ℝ) (495288118667/500000000000 : ℝ) (123822029667/125000000000 : ℝ) (990576237083/1000000000000 : ℝ) (198115247417/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2177/16384 : ℝ)) 2 (495288118667/500000000000 : ℝ) (123822029667/125000000000 : ℝ) (990576237083/1000000000000 : ℝ) (198115247417/200000000000 : ℝ) (123822029651/125000000000 : ℝ) (990576237211/1000000000000 : ℝ) (123822029651/125000000000 : ℝ) (990576237211/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2177/16384 : ℝ)) 3 (123822029651/125000000000 : ℝ) (990576237211/1000000000000 : ℝ) (123822029651/125000000000 : ℝ) (990576237211/1000000000000 : ℝ) (123822029651/125000000000 : ℝ) (990576237211/1000000000000 : ℝ) (123822029651/125000000000 : ℝ) (990576237211/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2177/16384 : ℝ)) 4 (123822029651/125000000000 : ℝ) (990576237211/1000000000000 : ℝ) (123822029651/125000000000 : ℝ) (990576237211/1000000000000 : ℝ) (123822029651/125000000000 : ℝ) (990576237211/1000000000000 : ℝ) (123822029651/125000000000 : ℝ) (990576237211/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2177/16384 : ℝ)) 5 (123822029651/125000000000 : ℝ) (990576237211/1000000000000 : ℝ) (123822029651/125000000000 : ℝ) (990576237211/1000000000000 : ℝ) (123822029651/125000000000 : ℝ) (990576237211/1000000000000 : ℝ) (123822029651/125000000000 : ℝ) (990576237211/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2177/16384 : ℝ)) 6 (123822029651/125000000000 : ℝ) (990576237211/1000000000000 : ℝ) (123822029651/125000000000 : ℝ) (990576237211/1000000000000 : ℝ) (123822029651/125000000000 : ℝ) (990576237211/1000000000000 : ℝ) (123822029651/125000000000 : ℝ) (990576237211/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2177/16384 : ℝ)) 7 (123822029651/125000000000 : ℝ) (990576237211/1000000000000 : ℝ) (123822029651/125000000000 : ℝ) (990576237211/1000000000000 : ℝ) (123822029651/125000000000 : ℝ) (990576237211/1000000000000 : ℝ) (123822029651/125000000000 : ℝ) (990576237211/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2177/16384 : ℝ))) (193008478969/1000000000000 : ℝ) (7720339159/40000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2177/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (193008478969/1000000000000 : ℝ) (7720339159/40000000000 : ℝ) (149126059871/250000000000 : ℝ) (4660189371/7812500000 : ℝ) (439327302781/1000000000000 : ℝ) (439327302789/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2177/16384 : ℝ))) 1 (149126059871/250000000000 : ℝ) (4660189371/7812500000 : ℝ) (439327302781/1000000000000 : ℝ) (439327302789/1000000000000 : ℝ) (129478942783/250000000000 : ℝ) (517915771139/1000000000000 : ℝ) (51191854687/100000000000 : ℝ) (511918546877/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2177/16384 : ℝ))) 2 (129478942783/250000000000 : ℝ) (517915771139/1000000000000 : ℝ) (51191854687/100000000000 : ℝ) (511918546877/1000000000000 : ℝ) (514917159001/1000000000000 : ℝ) (16091161219/31250000000 : ℝ) (514908427741/1000000000000 : ℝ) (514908427749/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2177/16384 : ℝ))) 3 (514917159001/1000000000000 : ℝ) (16091161219/31250000000 : ℝ) (514908427741/1000000000000 : ℝ) (514908427749/1000000000000 : ℝ) (514912793371/1000000000000 : ℝ) (514912793379/1000000000000 : ℝ) (64364099169/125000000000 : ℝ) (6436409917/12500000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2177/16384 : ℝ))) 4 (514912793371/1000000000000 : ℝ) (514912793379/1000000000000 : ℝ) (64364099169/125000000000 : ℝ) (6436409917/12500000000 : ℝ) (514912793361/1000000000000 : ℝ) (51491279337/100000000000 : ℝ) (514912793361/1000000000000 : ℝ) (51491279337/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2177/16384 : ℝ))) 5 (514912793361/1000000000000 : ℝ) (51491279337/100000000000 : ℝ) (514912793361/1000000000000 : ℝ) (51491279337/100000000000 : ℝ) (514912793361/1000000000000 : ℝ) (51491279337/100000000000 : ℝ) (514912793361/1000000000000 : ℝ) (51491279337/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2177/16384 : ℝ))) 6 (514912793361/1000000000000 : ℝ) (51491279337/100000000000 : ℝ) (514912793361/1000000000000 : ℝ) (51491279337/100000000000 : ℝ) (514912793361/1000000000000 : ℝ) (51491279337/100000000000 : ℝ) (514912793361/1000000000000 : ℝ) (51491279337/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2177/16384 : ℝ))) 7 (514912793361/1000000000000 : ℝ) (51491279337/100000000000 : ℝ) (514912793361/1000000000000 : ℝ) (51491279337/100000000000 : ℝ) (514912793361/1000000000000 : ℝ) (51491279337/100000000000 : ℝ) (514912793361/1000000000000 : ℝ) (51491279337/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2177/16384 : ℝ)) hmem 8 (123822029651/125000000000 : ℝ) (990576237211/1000000000000 : ℝ) (123822029651/125000000000 : ℝ) (990576237211/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2177/16384 : ℝ))) hcmem 8 (514912793361/1000000000000 : ℝ) (51491279337/100000000000 : ℝ) (514912793361/1000000000000 : ℝ) (51491279337/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2177/16384 : ℝ)) (123822029651/125000000000 : ℝ) (990576237211/1000000000000 : ℝ) (514912793361/1000000000000 : ℝ) (51491279337/100000000000 : ℝ) (408258897219/500000000000 : ℝ) (102064724307/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0138_exp_lower
  have heNumeric : (126189676111/62500000000 : ℝ)/4 ≤ Real.exp (-5469398215023/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (126189676111/62500000000 : ℝ)/4 ≤ Real.exp ((4353/32768 : ℝ)-(102064724307/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4353/32768 : ℝ) (2177/16384 : ℝ) (102064724307/125000000000 : ℝ) (126189676111/62500000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0139; no trusted numerical premise.
theorem cover7_leaf0139_exp_radius : (249407381840551813/250000000000000000 : ℝ) ≤ Real.exp ((-4355/229376 : ℝ)/8) ∧ Real.exp ((-4355/229376 : ℝ)/8) ≤ (997629527362207253/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4355/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0139_exp_lower : (11476130086482489/12500000000000000 : ℝ) ≤ Real.exp ((-546940228663/800000000000 : ℝ)/8) ∧ Real.exp ((-546940228663/800000000000 : ℝ)/8) ≤ (918090406918599121/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-546940228663/800000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0139_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009516895093/500000000000 : ℝ) ≤ 4*Real.exp (2177/16384 : ℝ)*Real.exp (-mu (radius 7 (4355/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (1009516895093/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4355/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0139_exp_radius
  have hrNumeric : (981192811117/1000000000000 : ℝ) ≤ Real.exp (-4355/229376 : ℝ) ∧ Real.exp (-4355/229376 : ℝ) ≤ (490596405559/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (981192811117/1000000000000 : ℝ) ≤ (radius 7 (4355/32768 : ℝ)) ∧ (radius 7 (4355/32768 : ℝ)) ≤ (490596405559/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4355/32768 : ℝ)) (981192811117/1000000000000 : ℝ) (490596405559/500000000000 : ℝ) (38606044817/200000000000 : ℝ) (193030224091/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4355/32768 : ℝ)) (981192811117/1000000000000 : ℝ) (490596405559/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4355/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (981192811117/1000000000000 : ℝ) (490596405559/500000000000 : ℝ) (495298202779/500000000000 : ℝ) (990596405559/1000000000000 : ℝ) (990551771043/1000000000000 : ℝ) (247637942761/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4355/32768 : ℝ)) 1 (495298202779/500000000000 : ℝ) (990596405559/1000000000000 : ℝ) (990551771043/1000000000000 : ℝ) (247637942761/250000000000 : ℝ) (9905740883/10000000000 : ℝ) (495287044151/500000000000 : ℝ) (990574088049/1000000000000 : ℝ) (990574088051/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4355/32768 : ℝ)) 2 (9905740883/10000000000 : ℝ) (495287044151/500000000000 : ℝ) (990574088049/1000000000000 : ℝ) (990574088051/1000000000000 : ℝ) (495287044087/500000000000 : ℝ) (990574088177/1000000000000 : ℝ) (495287044087/500000000000 : ℝ) (990574088177/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4355/32768 : ℝ)) 3 (495287044087/500000000000 : ℝ) (990574088177/1000000000000 : ℝ) (495287044087/500000000000 : ℝ) (990574088177/1000000000000 : ℝ) (495287044087/500000000000 : ℝ) (990574088177/1000000000000 : ℝ) (495287044087/500000000000 : ℝ) (990574088177/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4355/32768 : ℝ)) 4 (495287044087/500000000000 : ℝ) (990574088177/1000000000000 : ℝ) (495287044087/500000000000 : ℝ) (990574088177/1000000000000 : ℝ) (495287044087/500000000000 : ℝ) (990574088177/1000000000000 : ℝ) (495287044087/500000000000 : ℝ) (990574088177/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4355/32768 : ℝ)) 5 (495287044087/500000000000 : ℝ) (990574088177/1000000000000 : ℝ) (495287044087/500000000000 : ℝ) (990574088177/1000000000000 : ℝ) (495287044087/500000000000 : ℝ) (990574088177/1000000000000 : ℝ) (495287044087/500000000000 : ℝ) (990574088177/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4355/32768 : ℝ)) 6 (495287044087/500000000000 : ℝ) (990574088177/1000000000000 : ℝ) (495287044087/500000000000 : ℝ) (990574088177/1000000000000 : ℝ) (495287044087/500000000000 : ℝ) (990574088177/1000000000000 : ℝ) (495287044087/500000000000 : ℝ) (990574088177/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4355/32768 : ℝ)) 7 (495287044087/500000000000 : ℝ) (990574088177/1000000000000 : ℝ) (495287044087/500000000000 : ℝ) (990574088177/1000000000000 : ℝ) (495287044087/500000000000 : ℝ) (990574088177/1000000000000 : ℝ) (495287044087/500000000000 : ℝ) (990574088177/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4355/32768 : ℝ))) (38606044817/200000000000 : ℝ) (193030224091/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4355/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (38606044817/200000000000 : ℝ) (193030224091/1000000000000 : ℝ) (298257556021/500000000000 : ℝ) (298257556023/500000000000 : ℝ) (439352050279/1000000000000 : ℝ) (439352050287/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4355/32768 : ℝ))) 1 (298257556021/500000000000 : ℝ) (298257556023/500000000000 : ℝ) (439352050279/1000000000000 : ℝ) (439352050287/1000000000000 : ℝ) (12948339529/25000000000 : ℝ) (517933581167/1000000000000 : ℝ) (127984407619/250000000000 : ℝ) (127984407621/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4355/32768 : ℝ))) 2 (12948339529/25000000000 : ℝ) (517933581167/1000000000000 : ℝ) (127984407619/250000000000 : ℝ) (127984407621/250000000000 : ℝ) (257467802909/500000000000 : ℝ) (257467802913/500000000000 : ℝ) (257463439289/500000000000 : ℝ) (514926878587/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4355/32768 : ℝ))) 3 (257467802909/500000000000 : ℝ) (257467802913/500000000000 : ℝ) (257463439289/500000000000 : ℝ) (514926878587/1000000000000 : ℝ) (257465621099/500000000000 : ℝ) (514931242207/1000000000000 : ℝ) (514931242179/1000000000000 : ℝ) (514931242189/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4355/32768 : ℝ))) 4 (257465621099/500000000000 : ℝ) (514931242207/1000000000000 : ℝ) (514931242179/1000000000000 : ℝ) (514931242189/1000000000000 : ℝ) (128732810547/250000000000 : ℝ) (257465621099/500000000000 : ℝ) (128732810547/250000000000 : ℝ) (257465621099/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4355/32768 : ℝ))) 5 (128732810547/250000000000 : ℝ) (257465621099/500000000000 : ℝ) (128732810547/250000000000 : ℝ) (257465621099/500000000000 : ℝ) (128732810547/250000000000 : ℝ) (257465621099/500000000000 : ℝ) (128732810547/250000000000 : ℝ) (257465621099/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4355/32768 : ℝ))) 6 (128732810547/250000000000 : ℝ) (257465621099/500000000000 : ℝ) (128732810547/250000000000 : ℝ) (257465621099/500000000000 : ℝ) (128732810547/250000000000 : ℝ) (257465621099/500000000000 : ℝ) (128732810547/250000000000 : ℝ) (257465621099/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4355/32768 : ℝ))) 7 (128732810547/250000000000 : ℝ) (257465621099/500000000000 : ℝ) (128732810547/250000000000 : ℝ) (257465621099/500000000000 : ℝ) (128732810547/250000000000 : ℝ) (257465621099/500000000000 : ℝ) (128732810547/250000000000 : ℝ) (257465621099/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4355/32768 : ℝ)) hmem 8 (495287044087/500000000000 : ℝ) (990574088177/1000000000000 : ℝ) (495287044087/500000000000 : ℝ) (990574088177/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4355/32768 : ℝ))) hcmem 8 (128732810547/250000000000 : ℝ) (257465621099/500000000000 : ℝ) (128732810547/250000000000 : ℝ) (257465621099/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4355/32768 : ℝ)) (495287044087/500000000000 : ℝ) (990574088177/1000000000000 : ℝ) (128732810547/250000000000 : ℝ) (257465621099/500000000000 : ℝ) (408274410483/500000000000 : ℝ) (163309764197/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0139_exp_lower
  have heNumeric : (1009516895093/500000000000 : ℝ)/4 ≤ Real.exp (-546940228663/800000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009516895093/500000000000 : ℝ)/4 ≤ Real.exp ((2177/16384 : ℝ)-(163309764197/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2177/16384 : ℝ) (4355/32768 : ℝ) (163309764197/200000000000 : ℝ) (1009516895093/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0140; no trusted numerical premise.
theorem cover7_leaf0140_exp_radius : (997628983697408227/1000000000000000000 : ℝ) ≤ Real.exp ((-1089/57344 : ℝ)/8) ∧ Real.exp ((-1089/57344 : ℝ)/8) ≤ (249407245924352057/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1089/57344 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0140_exp_lower : (918090349057459289/1000000000000000000 : ℝ) ≤ Real.exp ((-43755250561/64000000000 : ℝ)/8) ∧ Real.exp ((-43755250561/64000000000 : ℝ)/8) ≤ (91809034905745929/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-43755250561/64000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0140_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (252379096527/125000000000 : ℝ) ≤ 4*Real.exp (4355/32768 : ℝ)*Real.exp (-mu (radius 7 (1089/8192 : ℝ))) ∧ (2019/1000 : ℝ) < (252379096527/125000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (1089/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0140_exp_radius
  have hrNumeric : (196237706693/200000000000 : ℝ) ≤ Real.exp (-1089/57344 : ℝ) ∧ Real.exp (-1089/57344 : ℝ) ≤ (490594266733/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196237706693/200000000000 : ℝ) ≤ (radius 7 (1089/8192 : ℝ)) ∧ (radius 7 (1089/8192 : ℝ)) ≤ (490594266733/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (1089/8192 : ℝ)) (196237706693/200000000000 : ℝ) (490594266733/500000000000 : ℝ) (38610393313/200000000000 : ℝ) (193051966571/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (1089/8192 : ℝ)) (196237706693/200000000000 : ℝ) (490594266733/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (1089/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196237706693/200000000000 : ℝ) (490594266733/500000000000 : ℝ) (247648566683/250000000000 : ℝ) (990594266733/1000000000000 : ℝ) (495274805907/500000000000 : ℝ) (198109922363/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (1089/8192 : ℝ)) 1 (247648566683/250000000000 : ℝ) (990594266733/1000000000000 : ℝ) (495274805907/500000000000 : ℝ) (198109922363/200000000000 : ℝ) (990571939273/1000000000000 : ℝ) (495285969637/500000000000 : ℝ) (990571939021/1000000000000 : ℝ) (990571939023/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (1089/8192 : ℝ)) 2 (990571939273/1000000000000 : ℝ) (495285969637/500000000000 : ℝ) (990571939021/1000000000000 : ℝ) (990571939023/1000000000000 : ℝ) (990571939147/1000000000000 : ℝ) (990571939149/1000000000000 : ℝ) (495285969573/500000000000 : ℝ) (990571939149/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (1089/8192 : ℝ)) 3 (990571939147/1000000000000 : ℝ) (990571939149/1000000000000 : ℝ) (495285969573/500000000000 : ℝ) (990571939149/1000000000000 : ℝ) (495285969573/500000000000 : ℝ) (990571939149/1000000000000 : ℝ) (495285969573/500000000000 : ℝ) (990571939149/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (1089/8192 : ℝ)) 4 (495285969573/500000000000 : ℝ) (990571939149/1000000000000 : ℝ) (495285969573/500000000000 : ℝ) (990571939149/1000000000000 : ℝ) (495285969573/500000000000 : ℝ) (990571939149/1000000000000 : ℝ) (495285969573/500000000000 : ℝ) (990571939149/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (1089/8192 : ℝ)) 5 (495285969573/500000000000 : ℝ) (990571939149/1000000000000 : ℝ) (495285969573/500000000000 : ℝ) (990571939149/1000000000000 : ℝ) (495285969573/500000000000 : ℝ) (990571939149/1000000000000 : ℝ) (495285969573/500000000000 : ℝ) (990571939149/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (1089/8192 : ℝ)) 6 (495285969573/500000000000 : ℝ) (990571939149/1000000000000 : ℝ) (495285969573/500000000000 : ℝ) (990571939149/1000000000000 : ℝ) (495285969573/500000000000 : ℝ) (990571939149/1000000000000 : ℝ) (495285969573/500000000000 : ℝ) (990571939149/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (1089/8192 : ℝ)) 7 (495285969573/500000000000 : ℝ) (990571939149/1000000000000 : ℝ) (495285969573/500000000000 : ℝ) (990571939149/1000000000000 : ℝ) (495285969573/500000000000 : ℝ) (990571939149/1000000000000 : ℝ) (495285969573/500000000000 : ℝ) (990571939149/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (1089/8192 : ℝ))) (38610393313/200000000000 : ℝ) (193051966571/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (1089/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (38610393313/200000000000 : ℝ) (193051966571/1000000000000 : ℝ) (298262991641/500000000000 : ℝ) (298262991643/500000000000 : ℝ) (54922099173/125000000000 : ℝ) (27461049587/62500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (1089/8192 : ℝ))) 1 (298262991641/500000000000 : ℝ) (298262991643/500000000000 : ℝ) (54922099173/125000000000 : ℝ) (27461049587/62500000000 : ℝ) (517951388333/1000000000000 : ℝ) (517951388339/1000000000000 : ℝ) (127989177693/250000000000 : ℝ) (511956710779/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (1089/8192 : ℝ))) 2 (517951388333/1000000000000 : ℝ) (517951388339/1000000000000 : ℝ) (127989177693/250000000000 : ℝ) (511956710779/1000000000000 : ℝ) (32184628097/62500000000 : ℝ) (514954049559/1000000000000 : ℝ) (514945326331/1000000000000 : ℝ) (514945326339/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (1089/8192 : ℝ))) 3 (32184628097/62500000000 : ℝ) (514954049559/1000000000000 : ℝ) (514945326331/1000000000000 : ℝ) (514945326339/1000000000000 : ℝ) (514949687941/1000000000000 : ℝ) (514949687949/1000000000000 : ℝ) (514949687923/1000000000000 : ℝ) (514949687931/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (1089/8192 : ℝ))) 4 (514949687941/1000000000000 : ℝ) (514949687949/1000000000000 : ℝ) (514949687923/1000000000000 : ℝ) (514949687931/1000000000000 : ℝ) (128737421983/250000000000 : ℝ) (25747484397/50000000000 : ℝ) (514949687931/1000000000000 : ℝ) (25747484397/50000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (1089/8192 : ℝ))) 5 (128737421983/250000000000 : ℝ) (25747484397/50000000000 : ℝ) (514949687931/1000000000000 : ℝ) (25747484397/50000000000 : ℝ) (514949687931/1000000000000 : ℝ) (25747484397/50000000000 : ℝ) (514949687931/1000000000000 : ℝ) (25747484397/50000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (1089/8192 : ℝ))) 6 (514949687931/1000000000000 : ℝ) (25747484397/50000000000 : ℝ) (514949687931/1000000000000 : ℝ) (25747484397/50000000000 : ℝ) (514949687931/1000000000000 : ℝ) (25747484397/50000000000 : ℝ) (514949687931/1000000000000 : ℝ) (25747484397/50000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (1089/8192 : ℝ))) 7 (514949687931/1000000000000 : ℝ) (25747484397/50000000000 : ℝ) (514949687931/1000000000000 : ℝ) (25747484397/50000000000 : ℝ) (514949687931/1000000000000 : ℝ) (25747484397/50000000000 : ℝ) (514949687931/1000000000000 : ℝ) (25747484397/50000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (1089/8192 : ℝ)) hmem 8 (495285969573/500000000000 : ℝ) (990571939149/1000000000000 : ℝ) (495285969573/500000000000 : ℝ) (990571939149/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (1089/8192 : ℝ))) hcmem 8 (514949687931/1000000000000 : ℝ) (25747484397/50000000000 : ℝ) (514949687931/1000000000000 : ℝ) (25747484397/50000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (1089/8192 : ℝ)) (495285969573/500000000000 : ℝ) (990571939149/1000000000000 : ℝ) (514949687931/1000000000000 : ℝ) (25747484397/50000000000 : ℝ) (816579842733/1000000000000 : ℝ) (3266319371/4000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0140_exp_lower
  have heNumeric : (252379096527/125000000000 : ℝ)/4 ≤ Real.exp (-43755250561/64000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (252379096527/125000000000 : ℝ)/4 ≤ Real.exp ((4355/32768 : ℝ)-(3266319371/4000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4355/32768 : ℝ) (1089/8192 : ℝ) (3266319371/4000000000 : ℝ) (252379096527/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0141; no trusted numerical premise.
theorem cover7_leaf0141_exp_radius : (39905137601316219/40000000000000000 : ℝ) ≤ Real.exp ((-4357/229376 : ℝ)/8) ∧ Real.exp ((-4357/229376 : ℝ)/8) ≤ (249407110008226369/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4357/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0141_exp_lower : (114761286467866389/125000000000000000 : ℝ) ≤ Real.exp ((-1367352578879/2000000000000 : ℝ)/8) ∧ Real.exp ((-1367352578879/2000000000000 : ℝ)/8) ≤ (918090291742931113/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1367352578879/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0141_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019031763863/1000000000000 : ℝ) ≤ 4*Real.exp (1089/8192 : ℝ)*Real.exp (-mu (radius 7 (4357/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (2019031763863/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4357/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0141_exp_radius
  have hrNumeric : (122648031979/125000000000 : ℝ) ≤ Real.exp (-4357/229376 : ℝ) ∧ Real.exp (-4357/229376 : ℝ) ≤ (981184255833/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (122648031979/125000000000 : ℝ) ≤ (radius 7 (4357/32768 : ℝ)) ∧ (radius 7 (4357/32768 : ℝ)) ≤ (981184255833/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4357/32768 : ℝ)) (122648031979/125000000000 : ℝ) (981184255833/1000000000000 : ℝ) (96536853203/500000000000 : ℝ) (48268426603/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4357/32768 : ℝ)) (122648031979/125000000000 : ℝ) (981184255833/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4357/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (122648031979/125000000000 : ℝ) (981184255833/1000000000000 : ℝ) (247648031979/250000000000 : ℝ) (990592127917/1000000000000 : ℝ) (990547452589/1000000000000 : ℝ) (990547452591/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4357/32768 : ℝ)) 1 (247648031979/250000000000 : ℝ) (990592127917/1000000000000 : ℝ) (990547452589/1000000000000 : ℝ) (990547452591/1000000000000 : ℝ) (247642447563/250000000000 : ℝ) (495284895127/500000000000 : ℝ) (99056979/100000000 : ℝ) (990569790003/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4357/32768 : ℝ)) 2 (247642447563/250000000000 : ℝ) (495284895127/500000000000 : ℝ) (99056979/100000000 : ℝ) (990569790003/1000000000000 : ℝ) (495284895063/500000000000 : ℝ) (990569790129/1000000000000 : ℝ) (7924558321/8000000000 : ℝ) (990569790129/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4357/32768 : ℝ)) 3 (495284895063/500000000000 : ℝ) (990569790129/1000000000000 : ℝ) (7924558321/8000000000 : ℝ) (990569790129/1000000000000 : ℝ) (7924558321/8000000000 : ℝ) (990569790129/1000000000000 : ℝ) (7924558321/8000000000 : ℝ) (990569790129/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4357/32768 : ℝ)) 4 (7924558321/8000000000 : ℝ) (990569790129/1000000000000 : ℝ) (7924558321/8000000000 : ℝ) (990569790129/1000000000000 : ℝ) (7924558321/8000000000 : ℝ) (990569790129/1000000000000 : ℝ) (7924558321/8000000000 : ℝ) (990569790129/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4357/32768 : ℝ)) 5 (7924558321/8000000000 : ℝ) (990569790129/1000000000000 : ℝ) (7924558321/8000000000 : ℝ) (990569790129/1000000000000 : ℝ) (7924558321/8000000000 : ℝ) (990569790129/1000000000000 : ℝ) (7924558321/8000000000 : ℝ) (990569790129/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4357/32768 : ℝ)) 6 (7924558321/8000000000 : ℝ) (990569790129/1000000000000 : ℝ) (7924558321/8000000000 : ℝ) (990569790129/1000000000000 : ℝ) (7924558321/8000000000 : ℝ) (990569790129/1000000000000 : ℝ) (7924558321/8000000000 : ℝ) (990569790129/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4357/32768 : ℝ)) 7 (7924558321/8000000000 : ℝ) (990569790129/1000000000000 : ℝ) (7924558321/8000000000 : ℝ) (990569790129/1000000000000 : ℝ) (7924558321/8000000000 : ℝ) (990569790129/1000000000000 : ℝ) (7924558321/8000000000 : ℝ) (990569790129/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4357/32768 : ℝ))) (96536853203/500000000000 : ℝ) (48268426603/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4357/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (96536853203/500000000000 : ℝ) (48268426603/250000000000 : ℝ) (596536853203/1000000000000 : ℝ) (298268426603/500000000000 : ℝ) (439401532093/1000000000000 : ℝ) (439401532101/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4357/32768 : ℝ))) 1 (596536853203/1000000000000 : ℝ) (298268426603/500000000000 : ℝ) (439401532093/1000000000000 : ℝ) (439401532101/1000000000000 : ℝ) (64746149081/125000000000 : ℝ) (258984596327/500000000000 : ℝ) (255987893877/500000000000 : ℝ) (511975787761/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4357/32768 : ℝ))) 2 (64746149081/125000000000 : ℝ) (258984596327/500000000000 : ℝ) (255987893877/500000000000 : ℝ) (511975787761/1000000000000 : ℝ) (514972490201/1000000000000 : ℝ) (16092890319/31250000000 : ℝ) (102992754199/200000000000 : ℝ) (514963771003/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4357/32768 : ℝ))) 3 (514972490201/1000000000000 : ℝ) (16092890319/31250000000 : ℝ) (102992754199/200000000000 : ℝ) (514963771003/1000000000000 : ℝ) (257484065299/500000000000 : ℝ) (257484065303/500000000000 : ℝ) (514968130579/1000000000000 : ℝ) (128742032647/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4357/32768 : ℝ))) 4 (257484065299/500000000000 : ℝ) (257484065303/500000000000 : ℝ) (514968130579/1000000000000 : ℝ) (128742032647/250000000000 : ℝ) (128742032647/250000000000 : ℝ) (514968130597/1000000000000 : ℝ) (128742032647/250000000000 : ℝ) (514968130597/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4357/32768 : ℝ))) 5 (128742032647/250000000000 : ℝ) (514968130597/1000000000000 : ℝ) (128742032647/250000000000 : ℝ) (514968130597/1000000000000 : ℝ) (128742032647/250000000000 : ℝ) (514968130597/1000000000000 : ℝ) (128742032647/250000000000 : ℝ) (514968130597/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4357/32768 : ℝ))) 6 (128742032647/250000000000 : ℝ) (514968130597/1000000000000 : ℝ) (128742032647/250000000000 : ℝ) (514968130597/1000000000000 : ℝ) (128742032647/250000000000 : ℝ) (514968130597/1000000000000 : ℝ) (128742032647/250000000000 : ℝ) (514968130597/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4357/32768 : ℝ))) 7 (128742032647/250000000000 : ℝ) (514968130597/1000000000000 : ℝ) (128742032647/250000000000 : ℝ) (514968130597/1000000000000 : ℝ) (128742032647/250000000000 : ℝ) (514968130597/1000000000000 : ℝ) (128742032647/250000000000 : ℝ) (514968130597/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4357/32768 : ℝ)) hmem 8 (7924558321/8000000000 : ℝ) (990569790129/1000000000000 : ℝ) (7924558321/8000000000 : ℝ) (990569790129/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4357/32768 : ℝ))) hcmem 8 (128742032647/250000000000 : ℝ) (514968130597/1000000000000 : ℝ) (128742032647/250000000000 : ℝ) (514968130597/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4357/32768 : ℝ)) (7924558321/8000000000 : ℝ) (990569790129/1000000000000 : ℝ) (128742032647/250000000000 : ℝ) (514968130597/1000000000000 : ℝ) (408305429867/500000000000 : ℝ) (102076357469/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0141_exp_lower
  have heNumeric : (2019031763863/1000000000000 : ℝ)/4 ≤ Real.exp (-1367352578879/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019031763863/1000000000000 : ℝ)/4 ≤ Real.exp ((1089/8192 : ℝ)-(102076357469/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (1089/8192 : ℝ) (4357/32768 : ℝ) (102076357469/125000000000 : ℝ) (2019031763863/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0142; no trusted numerical premise.
theorem cover7_leaf0142_exp_radius : (997627896368698997/1000000000000000000 : ℝ) ≤ Real.exp ((-2179/114688 : ℝ)/8) ∧ Real.exp ((-2179/114688 : ℝ)/8) ≤ (498813948184349499/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2179/114688 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0142_exp_lower : (918090234974670203/1000000000000000000 : ℝ) ≤ Real.exp ((-5469414272827/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469414272827/8000000000000 : ℝ)/8) ≤ (229522558743667551/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469414272827/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0142_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009515382561/500000000000 : ℝ) ≤ 4*Real.exp (4357/32768 : ℝ)*Real.exp (-mu (radius 7 (2179/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (1009515382561/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2179/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0142_exp_radius
  have hrNumeric : (981179978217/1000000000000 : ℝ) ≤ Real.exp (-2179/114688 : ℝ) ∧ Real.exp (-2179/114688 : ℝ) ≤ (490589989109/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (981179978217/1000000000000 : ℝ) ≤ (radius 7 (2179/16384 : ℝ)) ∧ (radius 7 (2179/16384 : ℝ)) ≤ (490589989109/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2179/16384 : ℝ)) (981179978217/1000000000000 : ℝ) (490589989109/500000000000 : ℝ) (193095443613/1000000000000 : ℝ) (193095443619/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2179/16384 : ℝ)) (981179978217/1000000000000 : ℝ) (490589989109/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2179/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (981179978217/1000000000000 : ℝ) (490589989109/500000000000 : ℝ) (247647497277/250000000000 : ℝ) (990589989109/1000000000000 : ℝ) (990545293369/1000000000000 : ℝ) (990545293371/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2179/16384 : ℝ)) 1 (247647497277/250000000000 : ℝ) (990589989109/1000000000000 : ℝ) (990545293369/1000000000000 : ℝ) (990545293371/1000000000000 : ℝ) (495283820619/500000000000 : ℝ) (24764191031/25000000000 : ℝ) (495283820493/500000000000 : ℝ) (247641910247/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2179/16384 : ℝ)) 2 (495283820619/500000000000 : ℝ) (24764191031/25000000000 : ℝ) (495283820493/500000000000 : ℝ) (247641910247/250000000000 : ℝ) (123820955139/125000000000 : ℝ) (495283820557/500000000000 : ℝ) (990567641111/1000000000000 : ℝ) (495283820557/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2179/16384 : ℝ)) 3 (123820955139/125000000000 : ℝ) (495283820557/500000000000 : ℝ) (990567641111/1000000000000 : ℝ) (495283820557/500000000000 : ℝ) (990567641111/1000000000000 : ℝ) (495283820557/500000000000 : ℝ) (990567641111/1000000000000 : ℝ) (495283820557/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2179/16384 : ℝ)) 4 (990567641111/1000000000000 : ℝ) (495283820557/500000000000 : ℝ) (990567641111/1000000000000 : ℝ) (495283820557/500000000000 : ℝ) (990567641111/1000000000000 : ℝ) (495283820557/500000000000 : ℝ) (990567641111/1000000000000 : ℝ) (495283820557/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2179/16384 : ℝ)) 5 (990567641111/1000000000000 : ℝ) (495283820557/500000000000 : ℝ) (990567641111/1000000000000 : ℝ) (495283820557/500000000000 : ℝ) (990567641111/1000000000000 : ℝ) (495283820557/500000000000 : ℝ) (990567641111/1000000000000 : ℝ) (495283820557/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2179/16384 : ℝ)) 6 (990567641111/1000000000000 : ℝ) (495283820557/500000000000 : ℝ) (990567641111/1000000000000 : ℝ) (495283820557/500000000000 : ℝ) (990567641111/1000000000000 : ℝ) (495283820557/500000000000 : ℝ) (990567641111/1000000000000 : ℝ) (495283820557/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2179/16384 : ℝ)) 7 (990567641111/1000000000000 : ℝ) (495283820557/500000000000 : ℝ) (990567641111/1000000000000 : ℝ) (495283820557/500000000000 : ℝ) (990567641111/1000000000000 : ℝ) (495283820557/500000000000 : ℝ) (990567641111/1000000000000 : ℝ) (495283820557/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2179/16384 : ℝ))) (193095443613/1000000000000 : ℝ) (193095443619/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2179/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (193095443613/1000000000000 : ℝ) (193095443619/1000000000000 : ℝ) (298273860903/500000000000 : ℝ) (59654772181/100000000000 : ℝ) (109856566603/250000000000 : ℝ) (21971313321/50000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2179/16384 : ℝ))) 1 (298273860903/500000000000 : ℝ) (59654772181/100000000000 : ℝ) (109856566603/250000000000 : ℝ) (21971313321/50000000000 : ℝ) (517986994109/1000000000000 : ℝ) (103597398823/200000000000 : ℝ) (511994861429/1000000000000 : ℝ) (127998715359/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2179/16384 : ℝ))) 2 (517986994109/1000000000000 : ℝ) (103597398823/200000000000 : ℝ) (511994861429/1000000000000 : ℝ) (127998715359/250000000000 : ℝ) (514990927769/1000000000000 : ℝ) (16093466493/31250000000 : ℝ) (514982212577/1000000000000 : ℝ) (64372776573/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2179/16384 : ℝ))) 3 (514990927769/1000000000000 : ℝ) (16093466493/31250000000 : ℝ) (514982212577/1000000000000 : ℝ) (64372776573/125000000000 : ℝ) (514986570173/1000000000000 : ℝ) (25749328509/50000000000 : ℝ) (257493285077/500000000000 : ℝ) (257493285081/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2179/16384 : ℝ))) 4 (514986570173/1000000000000 : ℝ) (25749328509/50000000000 : ℝ) (257493285077/500000000000 : ℝ) (257493285081/500000000000 : ℝ) (514986570163/1000000000000 : ℝ) (514986570171/1000000000000 : ℝ) (514986570163/1000000000000 : ℝ) (514986570171/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2179/16384 : ℝ))) 5 (514986570163/1000000000000 : ℝ) (514986570171/1000000000000 : ℝ) (514986570163/1000000000000 : ℝ) (514986570171/1000000000000 : ℝ) (514986570163/1000000000000 : ℝ) (514986570171/1000000000000 : ℝ) (514986570163/1000000000000 : ℝ) (514986570171/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2179/16384 : ℝ))) 6 (514986570163/1000000000000 : ℝ) (514986570171/1000000000000 : ℝ) (514986570163/1000000000000 : ℝ) (514986570171/1000000000000 : ℝ) (514986570163/1000000000000 : ℝ) (514986570171/1000000000000 : ℝ) (514986570163/1000000000000 : ℝ) (514986570171/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2179/16384 : ℝ))) 7 (514986570163/1000000000000 : ℝ) (514986570171/1000000000000 : ℝ) (514986570163/1000000000000 : ℝ) (514986570171/1000000000000 : ℝ) (514986570163/1000000000000 : ℝ) (514986570171/1000000000000 : ℝ) (514986570163/1000000000000 : ℝ) (514986570171/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2179/16384 : ℝ)) hmem 8 (990567641111/1000000000000 : ℝ) (495283820557/500000000000 : ℝ) (990567641111/1000000000000 : ℝ) (495283820557/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2179/16384 : ℝ))) hcmem 8 (514986570163/1000000000000 : ℝ) (514986570171/1000000000000 : ℝ) (514986570163/1000000000000 : ℝ) (514986570171/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2179/16384 : ℝ)) (990567641111/1000000000000 : ℝ) (495283820557/500000000000 : ℝ) (514986570163/1000000000000 : ℝ) (514986570171/1000000000000 : ℝ) (408320935989/500000000000 : ℝ) (408320935997/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0142_exp_lower
  have heNumeric : (1009515382561/500000000000 : ℝ)/4 ≤ Real.exp (-5469414272827/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009515382561/500000000000 : ℝ)/4 ≤ Real.exp ((4357/32768 : ℝ)-(408320935997/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4357/32768 : ℝ) (2179/16384 : ℝ) (408320935997/500000000000 : ℝ) (1009515382561/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0143; no trusted numerical premise.
theorem cover7_leaf0143_exp_radius : (997627352704788793/1000000000000000000 : ℝ) ≤ Real.exp ((-4359/229376 : ℝ)/8) ∧ Real.exp ((-4359/229376 : ℝ)/8) ≤ (498813676352394397/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4359/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0143_exp_lower : (459045089376567753/500000000000000000 : ℝ) ≤ Real.exp ((-2734709096013/4000000000000 : ℝ)/8) ∧ Real.exp ((-2734709096013/4000000000000 : ℝ)/8) ≤ (918090178753135507/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2734709096013/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0143_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019029775999/1000000000000 : ℝ) ≤ 4*Real.exp (2179/16384 : ℝ)*Real.exp (-mu (radius 7 (4359/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (2019029775999/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4359/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0143_exp_radius
  have hrNumeric : (981175700621/1000000000000 : ℝ) ≤ Real.exp (-4359/229376 : ℝ) ∧ Real.exp (-4359/229376 : ℝ) ≤ (490587850311/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (981175700621/1000000000000 : ℝ) ≤ (radius 7 (4359/32768 : ℝ)) ∧ (radius 7 (4359/32768 : ℝ)) ≤ (490587850311/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4359/32768 : ℝ)) (981175700621/1000000000000 : ℝ) (490587850311/500000000000 : ℝ) (193117178181/1000000000000 : ℝ) (193117178187/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4359/32768 : ℝ)) (981175700621/1000000000000 : ℝ) (490587850311/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4359/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (981175700621/1000000000000 : ℝ) (490587850311/500000000000 : ℝ) (99058785031/100000000000 : ℝ) (990587850311/1000000000000 : ℝ) (495271567077/500000000000 : ℝ) (247635783539/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4359/32768 : ℝ)) 1 (99058785031/100000000000 : ℝ) (990587850311/1000000000000 : ℝ) (495271567077/500000000000 : ℝ) (247635783539/250000000000 : ℝ) (123820686529/125000000000 : ℝ) (495282746117/500000000000 : ℝ) (990565491979/1000000000000 : ℝ) (495282745991/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4359/32768 : ℝ)) 2 (123820686529/125000000000 : ℝ) (495282746117/500000000000 : ℝ) (990565491979/1000000000000 : ℝ) (495282745991/500000000000 : ℝ) (198113098421/200000000000 : ℝ) (247641373027/250000000000 : ℝ) (198113098421/200000000000 : ℝ) (247641373027/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4359/32768 : ℝ)) 3 (198113098421/200000000000 : ℝ) (247641373027/250000000000 : ℝ) (198113098421/200000000000 : ℝ) (247641373027/250000000000 : ℝ) (198113098421/200000000000 : ℝ) (247641373027/250000000000 : ℝ) (198113098421/200000000000 : ℝ) (247641373027/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4359/32768 : ℝ)) 4 (198113098421/200000000000 : ℝ) (247641373027/250000000000 : ℝ) (198113098421/200000000000 : ℝ) (247641373027/250000000000 : ℝ) (198113098421/200000000000 : ℝ) (247641373027/250000000000 : ℝ) (198113098421/200000000000 : ℝ) (247641373027/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4359/32768 : ℝ)) 5 (198113098421/200000000000 : ℝ) (247641373027/250000000000 : ℝ) (198113098421/200000000000 : ℝ) (247641373027/250000000000 : ℝ) (198113098421/200000000000 : ℝ) (247641373027/250000000000 : ℝ) (198113098421/200000000000 : ℝ) (247641373027/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4359/32768 : ℝ)) 6 (198113098421/200000000000 : ℝ) (247641373027/250000000000 : ℝ) (198113098421/200000000000 : ℝ) (247641373027/250000000000 : ℝ) (198113098421/200000000000 : ℝ) (247641373027/250000000000 : ℝ) (198113098421/200000000000 : ℝ) (247641373027/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4359/32768 : ℝ)) 7 (198113098421/200000000000 : ℝ) (247641373027/250000000000 : ℝ) (198113098421/200000000000 : ℝ) (247641373027/250000000000 : ℝ) (198113098421/200000000000 : ℝ) (247641373027/250000000000 : ℝ) (198113098421/200000000000 : ℝ) (247641373027/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4359/32768 : ℝ))) (193117178181/1000000000000 : ℝ) (193117178187/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4359/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (193117178181/1000000000000 : ℝ) (193117178187/1000000000000 : ℝ) (59655858909/100000000000 : ℝ) (298279294547/500000000000 : ℝ) (27465687271/62500000000 : ℝ) (54931374543/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4359/32768 : ℝ))) 1 (59655858909/100000000000 : ℝ) (298279294547/500000000000 : ℝ) (27465687271/62500000000 : ℝ) (54931374543/125000000000 : ℝ) (518004792713/1000000000000 : ℝ) (518004792719/1000000000000 : ℝ) (512013931791/1000000000000 : ℝ) (256006965899/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4359/32768 : ℝ))) 2 (518004792713/1000000000000 : ℝ) (518004792719/1000000000000 : ℝ) (512013931791/1000000000000 : ℝ) (256006965899/500000000000 : ℝ) (128752340563/250000000000 : ℝ) (515009362259/1000000000000 : ℝ) (515000651071/1000000000000 : ℝ) (257500325539/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4359/32768 : ℝ))) 3 (128752340563/250000000000 : ℝ) (515009362259/1000000000000 : ℝ) (515000651071/1000000000000 : ℝ) (257500325539/500000000000 : ℝ) (515005006661/1000000000000 : ℝ) (515005006669/1000000000000 : ℝ) (515005006643/1000000000000 : ℝ) (515005006651/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4359/32768 : ℝ))) 4 (515005006661/1000000000000 : ℝ) (515005006669/1000000000000 : ℝ) (515005006643/1000000000000 : ℝ) (515005006651/1000000000000 : ℝ) (128751251663/250000000000 : ℝ) (25750250333/50000000000 : ℝ) (515005006651/1000000000000 : ℝ) (25750250333/50000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4359/32768 : ℝ))) 5 (128751251663/250000000000 : ℝ) (25750250333/50000000000 : ℝ) (515005006651/1000000000000 : ℝ) (25750250333/50000000000 : ℝ) (515005006651/1000000000000 : ℝ) (25750250333/50000000000 : ℝ) (515005006651/1000000000000 : ℝ) (25750250333/50000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4359/32768 : ℝ))) 6 (515005006651/1000000000000 : ℝ) (25750250333/50000000000 : ℝ) (515005006651/1000000000000 : ℝ) (25750250333/50000000000 : ℝ) (515005006651/1000000000000 : ℝ) (25750250333/50000000000 : ℝ) (515005006651/1000000000000 : ℝ) (25750250333/50000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4359/32768 : ℝ))) 7 (515005006651/1000000000000 : ℝ) (25750250333/50000000000 : ℝ) (515005006651/1000000000000 : ℝ) (25750250333/50000000000 : ℝ) (515005006651/1000000000000 : ℝ) (25750250333/50000000000 : ℝ) (515005006651/1000000000000 : ℝ) (25750250333/50000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4359/32768 : ℝ)) hmem 8 (198113098421/200000000000 : ℝ) (247641373027/250000000000 : ℝ) (198113098421/200000000000 : ℝ) (247641373027/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4359/32768 : ℝ))) hcmem 8 (515005006651/1000000000000 : ℝ) (25750250333/50000000000 : ℝ) (515005006651/1000000000000 : ℝ) (25750250333/50000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4359/32768 : ℝ)) (198113098421/200000000000 : ℝ) (247641373027/250000000000 : ℝ) (515005006651/1000000000000 : ℝ) (25750250333/50000000000 : ℝ) (408336439727/500000000000 : ℝ) (51042054967/62500000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0143_exp_lower
  have heNumeric : (2019029775999/1000000000000 : ℝ)/4 ≤ Real.exp (-2734709096013/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019029775999/1000000000000 : ℝ)/4 ≤ Real.exp ((2179/16384 : ℝ)-(51042054967/62500000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2179/16384 : ℝ) (4359/32768 : ℝ) (51042054967/62500000000 : ℝ) (2019029775999/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0144; no trusted numerical premise.
theorem cover7_leaf0144_exp_radius : (997626809041174861/1000000000000000000 : ℝ) ≤ Real.exp ((-545/28672 : ℝ)/8) ∧ Real.exp ((-545/28672 : ℝ)/8) ≤ (498813404520587431/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-545/28672 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0144_exp_lower : (229522530769524349/250000000000000000 : ℝ) ≤ Real.exp ((-5469422073129/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469422073129/8000000000000 : ℝ)/8) ≤ (918090123078097397/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469422073129/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0144_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019028796491/1000000000000 : ℝ) ≤ 4*Real.exp (4359/32768 : ℝ)*Real.exp (-mu (radius 7 (545/4096 : ℝ))) ∧ (2019/1000 : ℝ) < (2019028796491/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (545/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0144_exp_radius
  have hrNumeric : (245292855761/250000000000 : ℝ) ≤ Real.exp (-545/28672 : ℝ) ∧ Real.exp (-545/28672 : ℝ) ≤ (196234284609/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (245292855761/250000000000 : ℝ) ≤ (radius 7 (545/4096 : ℝ)) ∧ (radius 7 (545/4096 : ℝ)) ≤ (196234284609/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (545/4096 : ℝ)) (245292855761/250000000000 : ℝ) (196234284609/200000000000 : ℝ) (193138910113/1000000000000 : ℝ) (193138910119/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (545/4096 : ℝ)) (245292855761/250000000000 : ℝ) (196234284609/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (545/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (245292855761/250000000000 : ℝ) (196234284609/200000000000 : ℝ) (495292855761/500000000000 : ℝ) (990585711523/1000000000000 : ℝ) (30954405467/31250000000 : ℝ) (495270487473/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (545/4096 : ℝ)) 1 (495292855761/500000000000 : ℝ) (990585711523/1000000000000 : ℝ) (30954405467/31250000000 : ℝ) (495270487473/500000000000 : ℝ) (990563343233/1000000000000 : ℝ) (198112668647/200000000000 : ℝ) (49528167149/50000000000 : ℝ) (495281671491/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (545/4096 : ℝ)) 2 (990563343233/1000000000000 : ℝ) (198112668647/200000000000 : ℝ) (49528167149/50000000000 : ℝ) (495281671491/500000000000 : ℝ) (495281671553/500000000000 : ℝ) (990563343109/1000000000000 : ℝ) (495281671553/500000000000 : ℝ) (990563343109/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (545/4096 : ℝ)) 3 (495281671553/500000000000 : ℝ) (990563343109/1000000000000 : ℝ) (495281671553/500000000000 : ℝ) (990563343109/1000000000000 : ℝ) (495281671553/500000000000 : ℝ) (990563343109/1000000000000 : ℝ) (495281671553/500000000000 : ℝ) (990563343109/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (545/4096 : ℝ)) 4 (495281671553/500000000000 : ℝ) (990563343109/1000000000000 : ℝ) (495281671553/500000000000 : ℝ) (990563343109/1000000000000 : ℝ) (495281671553/500000000000 : ℝ) (990563343109/1000000000000 : ℝ) (495281671553/500000000000 : ℝ) (990563343109/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (545/4096 : ℝ)) 5 (495281671553/500000000000 : ℝ) (990563343109/1000000000000 : ℝ) (495281671553/500000000000 : ℝ) (990563343109/1000000000000 : ℝ) (495281671553/500000000000 : ℝ) (990563343109/1000000000000 : ℝ) (495281671553/500000000000 : ℝ) (990563343109/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (545/4096 : ℝ)) 6 (495281671553/500000000000 : ℝ) (990563343109/1000000000000 : ℝ) (495281671553/500000000000 : ℝ) (990563343109/1000000000000 : ℝ) (495281671553/500000000000 : ℝ) (990563343109/1000000000000 : ℝ) (495281671553/500000000000 : ℝ) (990563343109/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (545/4096 : ℝ)) 7 (495281671553/500000000000 : ℝ) (990563343109/1000000000000 : ℝ) (495281671553/500000000000 : ℝ) (990563343109/1000000000000 : ℝ) (495281671553/500000000000 : ℝ) (990563343109/1000000000000 : ℝ) (495281671553/500000000000 : ℝ) (990563343109/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (545/4096 : ℝ))) (193138910113/1000000000000 : ℝ) (193138910119/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (545/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (193138910113/1000000000000 : ℝ) (193138910119/1000000000000 : ℝ) (37285590941/62500000000 : ℝ) (29828472753/50000000000 : ℝ) (439475721869/1000000000000 : ℝ) (439475721877/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (545/4096 : ℝ))) 1 (37285590941/62500000000 : ℝ) (29828472753/50000000000 : ℝ) (439475721869/1000000000000 : ℝ) (439475721877/1000000000000 : ℝ) (259011294231/500000000000 : ℝ) (518022588469/1000000000000 : ℝ) (128008249711/250000000000 : ℝ) (512032998851/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (545/4096 : ℝ))) 2 (259011294231/500000000000 : ℝ) (518022588469/1000000000000 : ℝ) (128008249711/250000000000 : ℝ) (512032998851/1000000000000 : ℝ) (515027793653/1000000000000 : ℝ) (25751389683/50000000000 : ℝ) (6437738581/12500000000 : ℝ) (64377385811/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (545/4096 : ℝ))) 3 (515027793653/1000000000000 : ℝ) (25751389683/50000000000 : ℝ) (6437738581/12500000000 : ℝ) (64377385811/125000000000 : ℝ) (257511720033/500000000000 : ℝ) (257511720037/500000000000 : ℝ) (32188965003/62500000000 : ℝ) (64377930007/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (545/4096 : ℝ))) 4 (257511720033/500000000000 : ℝ) (257511720037/500000000000 : ℝ) (32188965003/62500000000 : ℝ) (64377930007/125000000000 : ℝ) (515023440057/1000000000000 : ℝ) (103004688013/200000000000 : ℝ) (64377930007/125000000000 : ℝ) (103004688013/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (545/4096 : ℝ))) 5 (515023440057/1000000000000 : ℝ) (103004688013/200000000000 : ℝ) (64377930007/125000000000 : ℝ) (103004688013/200000000000 : ℝ) (64377930007/125000000000 : ℝ) (103004688013/200000000000 : ℝ) (64377930007/125000000000 : ℝ) (103004688013/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (545/4096 : ℝ))) 6 (64377930007/125000000000 : ℝ) (103004688013/200000000000 : ℝ) (64377930007/125000000000 : ℝ) (103004688013/200000000000 : ℝ) (64377930007/125000000000 : ℝ) (103004688013/200000000000 : ℝ) (64377930007/125000000000 : ℝ) (103004688013/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (545/4096 : ℝ))) 7 (64377930007/125000000000 : ℝ) (103004688013/200000000000 : ℝ) (64377930007/125000000000 : ℝ) (103004688013/200000000000 : ℝ) (64377930007/125000000000 : ℝ) (103004688013/200000000000 : ℝ) (64377930007/125000000000 : ℝ) (103004688013/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (545/4096 : ℝ)) hmem 8 (495281671553/500000000000 : ℝ) (990563343109/1000000000000 : ℝ) (495281671553/500000000000 : ℝ) (990563343109/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (545/4096 : ℝ))) hcmem 8 (64377930007/125000000000 : ℝ) (103004688013/200000000000 : ℝ) (64377930007/125000000000 : ℝ) (103004688013/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (545/4096 : ℝ)) (495281671553/500000000000 : ℝ) (990563343109/1000000000000 : ℝ) (64377930007/125000000000 : ℝ) (103004688013/200000000000 : ℝ) (81670388217/100000000000 : ℝ) (204175970547/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0144_exp_lower
  have heNumeric : (2019028796491/1000000000000 : ℝ)/4 ≤ Real.exp (-5469422073129/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019028796491/1000000000000 : ℝ)/4 ≤ Real.exp ((4359/32768 : ℝ)-(204175970547/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4359/32768 : ℝ) (545/4096 : ℝ) (204175970547/250000000000 : ℝ) (2019028796491/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0145; no trusted numerical premise.
theorem cover7_leaf0145_exp_radius : (997626265377857203/1000000000000000000 : ℝ) ≤ Real.exp ((-623/32768 : ℝ)/8) ∧ Real.exp ((-623/32768 : ℝ)/8) ≤ (249406566344464301/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-623/32768 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0145_exp_lower : (918090067948178641/1000000000000000000 : ℝ) ≤ Real.exp ((-683678239529/1000000000000 : ℝ)/8) ∧ Real.exp ((-683678239529/1000000000000 : ℝ)/8) ≤ (459045033974089321/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-683678239529/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0145_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (80761113063/40000000000 : ℝ) ≤ 4*Real.exp (545/4096 : ℝ)*Real.exp (-mu (radius 7 (4361/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (80761113063/40000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4361/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0145_exp_radius
  have hrNumeric : (196233429097/200000000000 : ℝ) ≤ Real.exp (-623/32768 : ℝ) ∧ Real.exp (-623/32768 : ℝ) ≤ (490583572743/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196233429097/200000000000 : ℝ) ≤ (radius 7 (4361/32768 : ℝ)) ∧ (radius 7 (4361/32768 : ℝ)) ≤ (490583572743/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4361/32768 : ℝ)) (196233429097/200000000000 : ℝ) (490583572743/500000000000 : ℝ) (96580319707/500000000000 : ℝ) (9658031971/50000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4361/32768 : ℝ)) (196233429097/200000000000 : ℝ) (490583572743/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4361/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196233429097/200000000000 : ℝ) (490583572743/500000000000 : ℝ) (495291786371/500000000000 : ℝ) (990583572743/1000000000000 : ℝ) (495269407869/500000000000 : ℝ) (49526940787/50000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4361/32768 : ℝ)) 1 (495291786371/500000000000 : ℝ) (990583572743/1000000000000 : ℝ) (495269407869/500000000000 : ℝ) (49526940787/50000000000 : ℝ) (773875933/781250000 : ℝ) (495280597121/500000000000 : ℝ) (990561193987/1000000000000 : ℝ) (990561193989/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4361/32768 : ℝ)) 2 (773875933/781250000 : ℝ) (495280597121/500000000000 : ℝ) (990561193987/1000000000000 : ℝ) (990561193989/1000000000000 : ℝ) (990561194113/1000000000000 : ℝ) (247640298529/250000000000 : ℝ) (990561194113/1000000000000 : ℝ) (247640298529/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4361/32768 : ℝ)) 3 (990561194113/1000000000000 : ℝ) (247640298529/250000000000 : ℝ) (990561194113/1000000000000 : ℝ) (247640298529/250000000000 : ℝ) (990561194113/1000000000000 : ℝ) (247640298529/250000000000 : ℝ) (990561194113/1000000000000 : ℝ) (247640298529/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4361/32768 : ℝ)) 4 (990561194113/1000000000000 : ℝ) (247640298529/250000000000 : ℝ) (990561194113/1000000000000 : ℝ) (247640298529/250000000000 : ℝ) (990561194113/1000000000000 : ℝ) (247640298529/250000000000 : ℝ) (990561194113/1000000000000 : ℝ) (247640298529/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4361/32768 : ℝ)) 5 (990561194113/1000000000000 : ℝ) (247640298529/250000000000 : ℝ) (990561194113/1000000000000 : ℝ) (247640298529/250000000000 : ℝ) (990561194113/1000000000000 : ℝ) (247640298529/250000000000 : ℝ) (990561194113/1000000000000 : ℝ) (247640298529/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4361/32768 : ℝ)) 6 (990561194113/1000000000000 : ℝ) (247640298529/250000000000 : ℝ) (990561194113/1000000000000 : ℝ) (247640298529/250000000000 : ℝ) (990561194113/1000000000000 : ℝ) (247640298529/250000000000 : ℝ) (990561194113/1000000000000 : ℝ) (247640298529/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4361/32768 : ℝ)) 7 (990561194113/1000000000000 : ℝ) (247640298529/250000000000 : ℝ) (990561194113/1000000000000 : ℝ) (247640298529/250000000000 : ℝ) (990561194113/1000000000000 : ℝ) (247640298529/250000000000 : ℝ) (990561194113/1000000000000 : ℝ) (247640298529/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4361/32768 : ℝ))) (96580319707/500000000000 : ℝ) (9658031971/50000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4361/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (96580319707/500000000000 : ℝ) (9658031971/50000000000 : ℝ) (596580319707/1000000000000 : ℝ) (59658031971/100000000000 : ℝ) (439500443019/1000000000000 : ℝ) (219750221513/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4361/32768 : ℝ))) 1 (596580319707/1000000000000 : ℝ) (59658031971/100000000000 : ℝ) (439500443019/1000000000000 : ℝ) (219750221513/500000000000 : ℝ) (518040381363/1000000000000 : ℝ) (64755047671/125000000000 : ℝ) (256026031297/500000000000 : ℝ) (512052062601/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4361/32768 : ℝ))) 2 (518040381363/1000000000000 : ℝ) (64755047671/125000000000 : ℝ) (256026031297/500000000000 : ℝ) (512052062601/1000000000000 : ℝ) (257523110989/500000000000 : ℝ) (103009244397/200000000000 : ℝ) (515037518811/1000000000000 : ℝ) (257518759409/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4361/32768 : ℝ))) 3 (257523110989/500000000000 : ℝ) (103009244397/200000000000 : ℝ) (515037518811/1000000000000 : ℝ) (257518759409/500000000000 : ℝ) (257520935197/500000000000 : ℝ) (257520935201/500000000000 : ℝ) (64380233797/125000000000 : ℝ) (32190116899/62500000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4361/32768 : ℝ))) 4 (257520935197/500000000000 : ℝ) (257520935201/500000000000 : ℝ) (64380233797/125000000000 : ℝ) (32190116899/62500000000 : ℝ) (103008374077/200000000000 : ℝ) (515041870393/1000000000000 : ℝ) (32190116899/62500000000 : ℝ) (515041870393/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4361/32768 : ℝ))) 5 (103008374077/200000000000 : ℝ) (515041870393/1000000000000 : ℝ) (32190116899/62500000000 : ℝ) (515041870393/1000000000000 : ℝ) (32190116899/62500000000 : ℝ) (515041870393/1000000000000 : ℝ) (32190116899/62500000000 : ℝ) (515041870393/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4361/32768 : ℝ))) 6 (32190116899/62500000000 : ℝ) (515041870393/1000000000000 : ℝ) (32190116899/62500000000 : ℝ) (515041870393/1000000000000 : ℝ) (32190116899/62500000000 : ℝ) (515041870393/1000000000000 : ℝ) (32190116899/62500000000 : ℝ) (515041870393/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4361/32768 : ℝ))) 7 (32190116899/62500000000 : ℝ) (515041870393/1000000000000 : ℝ) (32190116899/62500000000 : ℝ) (515041870393/1000000000000 : ℝ) (32190116899/62500000000 : ℝ) (515041870393/1000000000000 : ℝ) (32190116899/62500000000 : ℝ) (515041870393/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4361/32768 : ℝ)) hmem 8 (990561194113/1000000000000 : ℝ) (247640298529/250000000000 : ℝ) (990561194113/1000000000000 : ℝ) (247640298529/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4361/32768 : ℝ))) hcmem 8 (32190116899/62500000000 : ℝ) (515041870393/1000000000000 : ℝ) (32190116899/62500000000 : ℝ) (515041870393/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4361/32768 : ℝ)) (990561194113/1000000000000 : ℝ) (247640298529/250000000000 : ℝ) (32190116899/62500000000 : ℝ) (515041870393/1000000000000 : ℝ) (816734880137/1000000000000 : ℝ) (408367440077/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0145_exp_lower
  have heNumeric : (80761113063/40000000000 : ℝ)/4 ≤ Real.exp (-683678239529/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (80761113063/40000000000 : ℝ)/4 ≤ Real.exp ((545/4096 : ℝ)-(408367440077/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (545/4096 : ℝ) (4361/32768 : ℝ) (408367440077/500000000000 : ℝ) (80761113063/40000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0146; no trusted numerical premise.
theorem cover7_leaf0146_exp_radius : (498812860857417909/500000000000000000 : ℝ) ≤ Real.exp ((-2181/114688 : ℝ)/8) ∧ Real.exp ((-2181/114688 : ℝ)/8) ≤ (997625721714835819/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2181/114688 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0146_exp_lower : (11476125167063757/12500000000000000 : ℝ) ≤ Real.exp ((-1093885944243/1600000000000 : ℝ)/8) ∧ Real.exp ((-1093885944243/1600000000000 : ℝ)/8) ≤ (918090013365100561/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1093885944243/1600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0146_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019026866279/1000000000000 : ℝ) ≤ 4*Real.exp (4361/32768 : ℝ)*Real.exp (-mu (radius 7 (2181/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (2019026866279/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2181/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0146_exp_radius
  have hrNumeric : (490581433973/500000000000 : ℝ) ≤ Real.exp (-2181/114688 : ℝ) ∧ Real.exp (-2181/114688 : ℝ) ≤ (981162867947/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490581433973/500000000000 : ℝ) ≤ (radius 7 (2181/16384 : ℝ)) ∧ (radius 7 (2181/16384 : ℝ)) ≤ (981162867947/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2181/16384 : ℝ)) (490581433973/500000000000 : ℝ) (981162867947/1000000000000 : ℝ) (96591183037/500000000000 : ℝ) (301847447/1562500000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2181/16384 : ℝ)) (490581433973/500000000000 : ℝ) (981162867947/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2181/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490581433973/500000000000 : ℝ) (981162867947/1000000000000 : ℝ) (990581433973/1000000000000 : ℝ) (495290716987/500000000000 : ℝ) (495268328269/500000000000 : ℝ) (990536656539/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2181/16384 : ℝ)) 1 (990581433973/1000000000000 : ℝ) (495290716987/500000000000 : ℝ) (495268328269/500000000000 : ℝ) (990536656539/1000000000000 : ℝ) (198111809051/200000000000 : ℝ) (990559045257/1000000000000 : ℝ) (495279522501/500000000000 : ℝ) (247639761251/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2181/16384 : ℝ)) 2 (198111809051/200000000000 : ℝ) (990559045257/1000000000000 : ℝ) (495279522501/500000000000 : ℝ) (247639761251/250000000000 : ℝ) (123819880641/125000000000 : ℝ) (990559045131/1000000000000 : ℝ) (123819880641/125000000000 : ℝ) (990559045131/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2181/16384 : ℝ)) 3 (123819880641/125000000000 : ℝ) (990559045131/1000000000000 : ℝ) (123819880641/125000000000 : ℝ) (990559045131/1000000000000 : ℝ) (123819880641/125000000000 : ℝ) (990559045131/1000000000000 : ℝ) (123819880641/125000000000 : ℝ) (990559045131/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2181/16384 : ℝ)) 4 (123819880641/125000000000 : ℝ) (990559045131/1000000000000 : ℝ) (123819880641/125000000000 : ℝ) (990559045131/1000000000000 : ℝ) (123819880641/125000000000 : ℝ) (990559045131/1000000000000 : ℝ) (123819880641/125000000000 : ℝ) (990559045131/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2181/16384 : ℝ)) 5 (123819880641/125000000000 : ℝ) (990559045131/1000000000000 : ℝ) (123819880641/125000000000 : ℝ) (990559045131/1000000000000 : ℝ) (123819880641/125000000000 : ℝ) (990559045131/1000000000000 : ℝ) (123819880641/125000000000 : ℝ) (990559045131/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2181/16384 : ℝ)) 6 (123819880641/125000000000 : ℝ) (990559045131/1000000000000 : ℝ) (123819880641/125000000000 : ℝ) (990559045131/1000000000000 : ℝ) (123819880641/125000000000 : ℝ) (990559045131/1000000000000 : ℝ) (123819880641/125000000000 : ℝ) (990559045131/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2181/16384 : ℝ)) 7 (123819880641/125000000000 : ℝ) (990559045131/1000000000000 : ℝ) (123819880641/125000000000 : ℝ) (990559045131/1000000000000 : ℝ) (123819880641/125000000000 : ℝ) (990559045131/1000000000000 : ℝ) (123819880641/125000000000 : ℝ) (990559045131/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2181/16384 : ℝ))) (96591183037/500000000000 : ℝ) (301847447/1562500000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2181/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (96591183037/500000000000 : ℝ) (301847447/1562500000 : ℝ) (596591183037/1000000000000 : ℝ) (1864347447/3125000000 : ℝ) (439525159773/1000000000000 : ℝ) (439525159781/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2181/16384 : ℝ))) 1 (596591183037/1000000000000 : ℝ) (1864347447/3125000000 : ℝ) (439525159773/1000000000000 : ℝ) (439525159781/1000000000000 : ℝ) (103611634281/200000000000 : ℝ) (518058171411/1000000000000 : ℝ) (64008890379/125000000000 : ℝ) (512071123039/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2181/16384 : ℝ))) 2 (103611634281/200000000000 : ℝ) (518058171411/1000000000000 : ℝ) (64008890379/125000000000 : ℝ) (512071123039/1000000000000 : ℝ) (257532323609/500000000000 : ℝ) (20602585889/40000000000 : ℝ) (103011189611/200000000000 : ℝ) (257527974031/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2181/16384 : ℝ))) 3 (257532323609/500000000000 : ℝ) (20602585889/40000000000 : ℝ) (103011189611/200000000000 : ℝ) (257527974031/500000000000 : ℝ) (128765074409/250000000000 : ℝ) (128765074411/250000000000 : ℝ) (257530148809/500000000000 : ℝ) (257530148813/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2181/16384 : ℝ))) 4 (128765074409/250000000000 : ℝ) (128765074411/250000000000 : ℝ) (257530148809/500000000000 : ℝ) (257530148813/500000000000 : ℝ) (515060297627/1000000000000 : ℝ) (103012059527/200000000000 : ℝ) (257530148813/500000000000 : ℝ) (103012059527/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2181/16384 : ℝ))) 5 (515060297627/1000000000000 : ℝ) (103012059527/200000000000 : ℝ) (257530148813/500000000000 : ℝ) (103012059527/200000000000 : ℝ) (257530148813/500000000000 : ℝ) (103012059527/200000000000 : ℝ) (257530148813/500000000000 : ℝ) (103012059527/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2181/16384 : ℝ))) 6 (257530148813/500000000000 : ℝ) (103012059527/200000000000 : ℝ) (257530148813/500000000000 : ℝ) (103012059527/200000000000 : ℝ) (257530148813/500000000000 : ℝ) (103012059527/200000000000 : ℝ) (257530148813/500000000000 : ℝ) (103012059527/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2181/16384 : ℝ))) 7 (257530148813/500000000000 : ℝ) (103012059527/200000000000 : ℝ) (257530148813/500000000000 : ℝ) (103012059527/200000000000 : ℝ) (257530148813/500000000000 : ℝ) (103012059527/200000000000 : ℝ) (257530148813/500000000000 : ℝ) (103012059527/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2181/16384 : ℝ)) hmem 8 (123819880641/125000000000 : ℝ) (990559045131/1000000000000 : ℝ) (123819880641/125000000000 : ℝ) (990559045131/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2181/16384 : ℝ))) hcmem 8 (257530148813/500000000000 : ℝ) (103012059527/200000000000 : ℝ) (257530148813/500000000000 : ℝ) (103012059527/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2181/16384 : ℝ)) (123819880641/125000000000 : ℝ) (990559045131/1000000000000 : ℝ) (257530148813/500000000000 : ℝ) (103012059527/200000000000 : ℝ) (816765873337/1000000000000 : ℝ) (163353174671/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0146_exp_lower
  have heNumeric : (2019026866279/1000000000000 : ℝ)/4 ≤ Real.exp (-1093885944243/1600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019026866279/1000000000000 : ℝ)/4 ≤ Real.exp ((4361/32768 : ℝ)-(163353174671/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4361/32768 : ℝ) (2181/16384 : ℝ) (163353174671/200000000000 : ℝ) (2019026866279/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0147; no trusted numerical premise.
theorem cover7_leaf0147_exp_radius : (199525035610422141/200000000000000000 : ℝ) ≤ Real.exp ((-4363/229376 : ℝ)/8) ∧ Real.exp ((-4363/229376 : ℝ)/8) ≤ (498812589026055353/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4363/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0147_exp_lower : (918089959326108787/1000000000000000000 : ℝ) ≤ Real.exp ((-546943348827/800000000000 : ℝ)/8) ∧ Real.exp ((-546943348827/800000000000 : ℝ)/8) ≤ (229522489831527197/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-546943348827/800000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0147_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (504756478889/250000000000 : ℝ) ≤ 4*Real.exp (2181/16384 : ℝ)*Real.exp (-mu (radius 7 (4363/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (504756478889/250000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4363/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0147_exp_radius
  have hrNumeric : (122644823803/125000000000 : ℝ) ≤ Real.exp (-4363/229376 : ℝ) ∧ Real.exp (-4363/229376 : ℝ) ≤ (39246343617/40000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (122644823803/125000000000 : ℝ) ≤ (radius 7 (4363/32768 : ℝ)) ∧ (radius 7 (4363/32768 : ℝ)) ≤ (39246343617/40000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4363/32768 : ℝ)) (122644823803/125000000000 : ℝ) (39246343617/40000000000 : ℝ) (193204090109/1000000000000 : ℝ) (48301022529/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4363/32768 : ℝ)) (122644823803/125000000000 : ℝ) (39246343617/40000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4363/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (122644823803/125000000000 : ℝ) (39246343617/40000000000 : ℝ) (247644823803/250000000000 : ℝ) (990579295213/1000000000000 : ℝ) (990534497341/1000000000000 : ℝ) (990534497343/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4363/32768 : ℝ)) 1 (247644823803/250000000000 : ℝ) (990579295213/1000000000000 : ℝ) (990534497341/1000000000000 : ℝ) (990534497343/1000000000000 : ℝ) (247639224069/250000000000 : ℝ) (495278448139/500000000000 : ℝ) (990556896023/1000000000000 : ℝ) (39622275841/40000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4363/32768 : ℝ)) 2 (247639224069/250000000000 : ℝ) (495278448139/500000000000 : ℝ) (990556896023/1000000000000 : ℝ) (39622275841/40000000000 : ℝ) (990556896149/1000000000000 : ℝ) (123819612019/125000000000 : ℝ) (990556896149/1000000000000 : ℝ) (123819612019/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4363/32768 : ℝ)) 3 (990556896149/1000000000000 : ℝ) (123819612019/125000000000 : ℝ) (990556896149/1000000000000 : ℝ) (123819612019/125000000000 : ℝ) (990556896149/1000000000000 : ℝ) (123819612019/125000000000 : ℝ) (990556896149/1000000000000 : ℝ) (123819612019/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4363/32768 : ℝ)) 4 (990556896149/1000000000000 : ℝ) (123819612019/125000000000 : ℝ) (990556896149/1000000000000 : ℝ) (123819612019/125000000000 : ℝ) (990556896149/1000000000000 : ℝ) (123819612019/125000000000 : ℝ) (990556896149/1000000000000 : ℝ) (123819612019/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4363/32768 : ℝ)) 5 (990556896149/1000000000000 : ℝ) (123819612019/125000000000 : ℝ) (990556896149/1000000000000 : ℝ) (123819612019/125000000000 : ℝ) (990556896149/1000000000000 : ℝ) (123819612019/125000000000 : ℝ) (990556896149/1000000000000 : ℝ) (123819612019/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4363/32768 : ℝ)) 6 (990556896149/1000000000000 : ℝ) (123819612019/125000000000 : ℝ) (990556896149/1000000000000 : ℝ) (123819612019/125000000000 : ℝ) (990556896149/1000000000000 : ℝ) (123819612019/125000000000 : ℝ) (990556896149/1000000000000 : ℝ) (123819612019/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4363/32768 : ℝ)) 7 (990556896149/1000000000000 : ℝ) (123819612019/125000000000 : ℝ) (990556896149/1000000000000 : ℝ) (123819612019/125000000000 : ℝ) (990556896149/1000000000000 : ℝ) (123819612019/125000000000 : ℝ) (990556896149/1000000000000 : ℝ) (123819612019/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4363/32768 : ℝ))) (193204090109/1000000000000 : ℝ) (48301022529/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4363/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (193204090109/1000000000000 : ℝ) (48301022529/250000000000 : ℝ) (298301022527/500000000000 : ℝ) (298301022529/500000000000 : ℝ) (54943734019/125000000000 : ℝ) (439549872161/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4363/32768 : ℝ))) 1 (298301022527/500000000000 : ℝ) (298301022529/500000000000 : ℝ) (54943734019/125000000000 : ℝ) (439549872161/1000000000000 : ℝ) (518075958603/1000000000000 : ℝ) (51807595861/100000000000 : ℝ) (128022545043/250000000000 : ℝ) (25604509009/50000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4363/32768 : ℝ))) 2 (518075958603/1000000000000 : ℝ) (51807595861/100000000000 : ℝ) (128022545043/250000000000 : ℝ) (25604509009/50000000000 : ℝ) (515083069387/1000000000000 : ℝ) (103016613879/200000000000 : ℝ) (20602974969/40000000000 : ℝ) (257537187117/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4363/32768 : ℝ))) 3 (515083069387/1000000000000 : ℝ) (103016613879/200000000000 : ℝ) (20602974969/40000000000 : ℝ) (257537187117/500000000000 : ℝ) (257539360903/500000000000 : ℝ) (103015744363/200000000000 : ℝ) (515078721787/1000000000000 : ℝ) (515078721797/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4363/32768 : ℝ))) 4 (257539360903/500000000000 : ℝ) (103015744363/200000000000 : ℝ) (515078721787/1000000000000 : ℝ) (515078721797/1000000000000 : ℝ) (128769680449/250000000000 : ℝ) (257539360903/500000000000 : ℝ) (128769680449/250000000000 : ℝ) (257539360903/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4363/32768 : ℝ))) 5 (128769680449/250000000000 : ℝ) (257539360903/500000000000 : ℝ) (128769680449/250000000000 : ℝ) (257539360903/500000000000 : ℝ) (128769680449/250000000000 : ℝ) (257539360903/500000000000 : ℝ) (128769680449/250000000000 : ℝ) (257539360903/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4363/32768 : ℝ))) 6 (128769680449/250000000000 : ℝ) (257539360903/500000000000 : ℝ) (128769680449/250000000000 : ℝ) (257539360903/500000000000 : ℝ) (128769680449/250000000000 : ℝ) (257539360903/500000000000 : ℝ) (128769680449/250000000000 : ℝ) (257539360903/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4363/32768 : ℝ))) 7 (128769680449/250000000000 : ℝ) (257539360903/500000000000 : ℝ) (128769680449/250000000000 : ℝ) (257539360903/500000000000 : ℝ) (128769680449/250000000000 : ℝ) (257539360903/500000000000 : ℝ) (128769680449/250000000000 : ℝ) (257539360903/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4363/32768 : ℝ)) hmem 8 (990556896149/1000000000000 : ℝ) (123819612019/125000000000 : ℝ) (990556896149/1000000000000 : ℝ) (123819612019/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4363/32768 : ℝ))) hcmem 8 (128769680449/250000000000 : ℝ) (257539360903/500000000000 : ℝ) (128769680449/250000000000 : ℝ) (257539360903/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4363/32768 : ℝ)) (990556896149/1000000000000 : ℝ) (123819612019/125000000000 : ℝ) (128769680449/250000000000 : ℝ) (257539360903/500000000000 : ℝ) (204199215449/250000000000 : ℝ) (163359372363/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0147_exp_lower
  have heNumeric : (504756478889/250000000000 : ℝ)/4 ≤ Real.exp (-546943348827/800000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (504756478889/250000000000 : ℝ)/4 ≤ Real.exp ((2181/16384 : ℝ)-(163359372363/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2181/16384 : ℝ) (4363/32768 : ℝ) (163359372363/200000000000 : ℝ) (504756478889/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0148; no trusted numerical premise.
theorem cover7_leaf0148_exp_radius : (199524926877936373/200000000000000000 : ℝ) ≤ Real.exp ((-1091/57344 : ℝ)/8) ∧ Real.exp ((-1091/57344 : ℝ)/8) ≤ (498812317194840933/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1091/57344 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0148_exp_lower : (918089905833727971/1000000000000000000 : ℝ) ≤ Real.exp ((-5469437217221/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469437217221/8000000000000 : ℝ)/8) ≤ (229522476458431993/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469437217221/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0148_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (40380499489/20000000000 : ℝ) ≤ 4*Real.exp (4363/32768 : ℝ)*Real.exp (-mu (radius 7 (1091/8192 : ℝ))) ∧ (2019/1000 : ℝ) < (40380499489/20000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (1091/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0148_exp_radius
  have hrNumeric : (490577156461/500000000000 : ℝ) ≤ Real.exp (-1091/57344 : ℝ) ∧ Real.exp (-1091/57344 : ℝ) ≤ (981154312923/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490577156461/500000000000 : ℝ) ≤ (radius 7 (1091/8192 : ℝ)) ∧ (radius 7 (1091/8192 : ℝ)) ≤ (981154312923/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (1091/8192 : ℝ)) (490577156461/500000000000 : ℝ) (981154312923/1000000000000 : ℝ) (193225811507/1000000000000 : ℝ) (193225811513/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (1091/8192 : ℝ)) (490577156461/500000000000 : ℝ) (981154312923/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (1091/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490577156461/500000000000 : ℝ) (981154312923/1000000000000 : ℝ) (990577156461/1000000000000 : ℝ) (495288578231/500000000000 : ℝ) (19810646763/20000000000 : ℝ) (123816542269/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (1091/8192 : ℝ)) 1 (990577156461/1000000000000 : ℝ) (495288578231/500000000000 : ℝ) (19810646763/20000000000 : ℝ) (123816542269/125000000000 : ℝ) (198110949461/200000000000 : ℝ) (990554747307/1000000000000 : ℝ) (247638686763/250000000000 : ℝ) (495277373527/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (1091/8192 : ℝ)) 2 (198110949461/200000000000 : ℝ) (990554747307/1000000000000 : ℝ) (247638686763/250000000000 : ℝ) (495277373527/500000000000 : ℝ) (495277373589/500000000000 : ℝ) (990554747181/1000000000000 : ℝ) (495277373589/500000000000 : ℝ) (990554747181/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (1091/8192 : ℝ)) 3 (495277373589/500000000000 : ℝ) (990554747181/1000000000000 : ℝ) (495277373589/500000000000 : ℝ) (990554747181/1000000000000 : ℝ) (495277373589/500000000000 : ℝ) (990554747181/1000000000000 : ℝ) (495277373589/500000000000 : ℝ) (990554747181/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (1091/8192 : ℝ)) 4 (495277373589/500000000000 : ℝ) (990554747181/1000000000000 : ℝ) (495277373589/500000000000 : ℝ) (990554747181/1000000000000 : ℝ) (495277373589/500000000000 : ℝ) (990554747181/1000000000000 : ℝ) (495277373589/500000000000 : ℝ) (990554747181/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (1091/8192 : ℝ)) 5 (495277373589/500000000000 : ℝ) (990554747181/1000000000000 : ℝ) (495277373589/500000000000 : ℝ) (990554747181/1000000000000 : ℝ) (495277373589/500000000000 : ℝ) (990554747181/1000000000000 : ℝ) (495277373589/500000000000 : ℝ) (990554747181/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (1091/8192 : ℝ)) 6 (495277373589/500000000000 : ℝ) (990554747181/1000000000000 : ℝ) (495277373589/500000000000 : ℝ) (990554747181/1000000000000 : ℝ) (495277373589/500000000000 : ℝ) (990554747181/1000000000000 : ℝ) (495277373589/500000000000 : ℝ) (990554747181/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (1091/8192 : ℝ)) 7 (495277373589/500000000000 : ℝ) (990554747181/1000000000000 : ℝ) (495277373589/500000000000 : ℝ) (990554747181/1000000000000 : ℝ) (495277373589/500000000000 : ℝ) (990554747181/1000000000000 : ℝ) (495277373589/500000000000 : ℝ) (990554747181/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (1091/8192 : ℝ))) (193225811507/1000000000000 : ℝ) (193225811513/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (1091/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (193225811507/1000000000000 : ℝ) (193225811513/1000000000000 : ℝ) (596612905753/1000000000000 : ℝ) (596612905757/1000000000000 : ℝ) (439574580141/1000000000000 : ℝ) (439574580149/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (1091/8192 : ℝ))) 1 (596612905753/1000000000000 : ℝ) (596612905757/1000000000000 : ℝ) (439574580141/1000000000000 : ℝ) (439574580149/1000000000000 : ℝ) (518093742947/1000000000000 : ℝ) (518093742953/1000000000000 : ℝ) (128027308501/250000000000 : ℝ) (128027308503/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (1091/8192 : ℝ))) 2 (518093742947/1000000000000 : ℝ) (518093742953/1000000000000 : ℝ) (128027308501/250000000000 : ℝ) (128027308503/250000000000 : ℝ) (20604059539/40000000000 : ℝ) (515101488483/1000000000000 : ℝ) (4024162479/7812500000 : ℝ) (12877319933/25000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (1091/8192 : ℝ))) 3 (20604059539/40000000000 : ℝ) (515101488483/1000000000000 : ℝ) (4024162479/7812500000 : ℝ) (12877319933/25000000000 : ℝ) (515097142893/1000000000000 : ℝ) (257548571451/500000000000 : ℝ) (4120777143/8000000000 : ℝ) (128774285721/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (1091/8192 : ℝ))) 4 (515097142893/1000000000000 : ℝ) (257548571451/500000000000 : ℝ) (4120777143/8000000000 : ℝ) (128774285721/250000000000 : ℝ) (128774285721/250000000000 : ℝ) (515097142893/1000000000000 : ℝ) (515097142883/1000000000000 : ℝ) (515097142893/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (1091/8192 : ℝ))) 5 (128774285721/250000000000 : ℝ) (515097142893/1000000000000 : ℝ) (515097142883/1000000000000 : ℝ) (515097142893/1000000000000 : ℝ) (515097142883/1000000000000 : ℝ) (515097142893/1000000000000 : ℝ) (515097142883/1000000000000 : ℝ) (515097142893/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (1091/8192 : ℝ))) 6 (515097142883/1000000000000 : ℝ) (515097142893/1000000000000 : ℝ) (515097142883/1000000000000 : ℝ) (515097142893/1000000000000 : ℝ) (515097142883/1000000000000 : ℝ) (515097142893/1000000000000 : ℝ) (515097142883/1000000000000 : ℝ) (515097142893/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (1091/8192 : ℝ))) 7 (515097142883/1000000000000 : ℝ) (515097142893/1000000000000 : ℝ) (515097142883/1000000000000 : ℝ) (515097142893/1000000000000 : ℝ) (515097142883/1000000000000 : ℝ) (515097142893/1000000000000 : ℝ) (515097142883/1000000000000 : ℝ) (515097142893/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (1091/8192 : ℝ)) hmem 8 (495277373589/500000000000 : ℝ) (990554747181/1000000000000 : ℝ) (495277373589/500000000000 : ℝ) (990554747181/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (1091/8192 : ℝ))) hcmem 8 (515097142883/1000000000000 : ℝ) (515097142893/1000000000000 : ℝ) (515097142883/1000000000000 : ℝ) (515097142893/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (1091/8192 : ℝ)) (495277373589/500000000000 : ℝ) (990554747181/1000000000000 : ℝ) (515097142883/1000000000000 : ℝ) (515097142893/1000000000000 : ℝ) (816827845493/1000000000000 : ℝ) (102103480689/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0148_exp_lower
  have heNumeric : (40380499489/20000000000 : ℝ)/4 ≤ Real.exp (-5469437217221/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (40380499489/20000000000 : ℝ)/4 ≤ Real.exp ((4363/32768 : ℝ)-(102103480689/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4363/32768 : ℝ) (1091/8192 : ℝ) (102103480689/125000000000 : ℝ) (40380499489/20000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0149; no trusted numerical premise.
theorem cover7_leaf0149_exp_radius : (498812045363774649/500000000000000000 : ℝ) ≤ Real.exp ((-4365/229376 : ℝ)/8) ∧ Real.exp ((-4365/229376 : ℝ)/8) ≤ (997624090727549299/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4365/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0149_exp_lower : (183617970577155511/200000000000000000 : ℝ) ≤ Real.exp ((-273472045411/400000000000 : ℝ)/8) ∧ Real.exp ((-273472045411/400000000000 : ℝ)/8) ≤ (229522463221444389/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-273472045411/400000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0149_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019024042923/1000000000000 : ℝ) ≤ 4*Real.exp (1091/8192 : ℝ)*Real.exp (-mu (radius 7 (4365/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (2019024042923/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4365/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0149_exp_radius
  have hrNumeric : (490575017719/500000000000 : ℝ) ≤ Real.exp (-4365/229376 : ℝ) ∧ Real.exp (-4365/229376 : ℝ) ≤ (981150035439/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490575017719/500000000000 : ℝ) ≤ (radius 7 (4365/32768 : ℝ)) ∧ (radius 7 (4365/32768 : ℝ)) ≤ (981150035439/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4365/32768 : ℝ)) (490575017719/500000000000 : ℝ) (981150035439/1000000000000 : ℝ) (48311882569/250000000000 : ℝ) (96623765141/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4365/32768 : ℝ)) (490575017719/500000000000 : ℝ) (981150035439/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4365/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490575017719/500000000000 : ℝ) (981150035439/1000000000000 : ℝ) (990575017719/1000000000000 : ℝ) (24764375443/25000000000 : ℝ) (990530178963/1000000000000 : ℝ) (198106035793/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4365/32768 : ℝ)) 1 (990575017719/1000000000000 : ℝ) (24764375443/25000000000 : ℝ) (990530178963/1000000000000 : ℝ) (198106035793/200000000000 : ℝ) (990552598341/1000000000000 : ℝ) (990552598343/1000000000000 : ℝ) (990552598087/1000000000000 : ℝ) (990552598089/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4365/32768 : ℝ)) 2 (990552598341/1000000000000 : ℝ) (990552598343/1000000000000 : ℝ) (990552598087/1000000000000 : ℝ) (990552598089/1000000000000 : ℝ) (495276299107/500000000000 : ℝ) (123819074777/125000000000 : ℝ) (990552598213/1000000000000 : ℝ) (123819074777/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4365/32768 : ℝ)) 3 (495276299107/500000000000 : ℝ) (123819074777/125000000000 : ℝ) (990552598213/1000000000000 : ℝ) (123819074777/125000000000 : ℝ) (990552598213/1000000000000 : ℝ) (123819074777/125000000000 : ℝ) (990552598213/1000000000000 : ℝ) (123819074777/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4365/32768 : ℝ)) 4 (990552598213/1000000000000 : ℝ) (123819074777/125000000000 : ℝ) (990552598213/1000000000000 : ℝ) (123819074777/125000000000 : ℝ) (990552598213/1000000000000 : ℝ) (123819074777/125000000000 : ℝ) (990552598213/1000000000000 : ℝ) (123819074777/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4365/32768 : ℝ)) 5 (990552598213/1000000000000 : ℝ) (123819074777/125000000000 : ℝ) (990552598213/1000000000000 : ℝ) (123819074777/125000000000 : ℝ) (990552598213/1000000000000 : ℝ) (123819074777/125000000000 : ℝ) (990552598213/1000000000000 : ℝ) (123819074777/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4365/32768 : ℝ)) 6 (990552598213/1000000000000 : ℝ) (123819074777/125000000000 : ℝ) (990552598213/1000000000000 : ℝ) (123819074777/125000000000 : ℝ) (990552598213/1000000000000 : ℝ) (123819074777/125000000000 : ℝ) (990552598213/1000000000000 : ℝ) (123819074777/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4365/32768 : ℝ)) 7 (990552598213/1000000000000 : ℝ) (123819074777/125000000000 : ℝ) (990552598213/1000000000000 : ℝ) (123819074777/125000000000 : ℝ) (990552598213/1000000000000 : ℝ) (123819074777/125000000000 : ℝ) (990552598213/1000000000000 : ℝ) (123819074777/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4365/32768 : ℝ))) (48311882569/250000000000 : ℝ) (96623765141/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4365/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (48311882569/250000000000 : ℝ) (96623765141/500000000000 : ℝ) (298311882569/500000000000 : ℝ) (596623765141/1000000000000 : ℝ) (54949910469/125000000000 : ℝ) (5494991047/12500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4365/32768 : ℝ))) 1 (298311882569/500000000000 : ℝ) (596623765141/1000000000000 : ℝ) (54949910469/125000000000 : ℝ) (5494991047/12500000000 : ℝ) (103622304889/200000000000 : ℝ) (518111524451/1000000000000 : ℝ) (256064142269/500000000000 : ℝ) (102425656909/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4365/32768 : ℝ))) 2 (103622304889/200000000000 : ℝ) (518111524451/1000000000000 : ℝ) (256064142269/500000000000 : ℝ) (102425656909/200000000000 : ℝ) (515119904491/1000000000000 : ℝ) (257559952249/500000000000 : ℝ) (128777804331/250000000000 : ℝ) (515111217331/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4365/32768 : ℝ))) 3 (515119904491/1000000000000 : ℝ) (257559952249/500000000000 : ℝ) (128777804331/250000000000 : ℝ) (515111217331/1000000000000 : ℝ) (515115560907/1000000000000 : ℝ) (103023112183/200000000000 : ℝ) (515115560889/1000000000000 : ℝ) (515115560897/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4365/32768 : ℝ))) 4 (515115560907/1000000000000 : ℝ) (103023112183/200000000000 : ℝ) (515115560889/1000000000000 : ℝ) (515115560897/1000000000000 : ℝ) (257557780449/500000000000 : ℝ) (257557780453/500000000000 : ℝ) (515115560897/1000000000000 : ℝ) (257557780453/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4365/32768 : ℝ))) 5 (257557780449/500000000000 : ℝ) (257557780453/500000000000 : ℝ) (515115560897/1000000000000 : ℝ) (257557780453/500000000000 : ℝ) (515115560897/1000000000000 : ℝ) (257557780453/500000000000 : ℝ) (515115560897/1000000000000 : ℝ) (257557780453/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4365/32768 : ℝ))) 6 (515115560897/1000000000000 : ℝ) (257557780453/500000000000 : ℝ) (515115560897/1000000000000 : ℝ) (257557780453/500000000000 : ℝ) (515115560897/1000000000000 : ℝ) (257557780453/500000000000 : ℝ) (515115560897/1000000000000 : ℝ) (257557780453/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4365/32768 : ℝ))) 7 (515115560897/1000000000000 : ℝ) (257557780453/500000000000 : ℝ) (515115560897/1000000000000 : ℝ) (257557780453/500000000000 : ℝ) (515115560897/1000000000000 : ℝ) (257557780453/500000000000 : ℝ) (515115560897/1000000000000 : ℝ) (257557780453/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4365/32768 : ℝ)) hmem 8 (990552598213/1000000000000 : ℝ) (123819074777/125000000000 : ℝ) (990552598213/1000000000000 : ℝ) (123819074777/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4365/32768 : ℝ))) hcmem 8 (515115560897/1000000000000 : ℝ) (257557780453/500000000000 : ℝ) (515115560897/1000000000000 : ℝ) (257557780453/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4365/32768 : ℝ)) (990552598213/1000000000000 : ℝ) (123819074777/125000000000 : ℝ) (515115560897/1000000000000 : ℝ) (257557780453/500000000000 : ℝ) (816858824447/1000000000000 : ℝ) (163371764893/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0149_exp_lower
  have heNumeric : (2019024042923/1000000000000 : ℝ)/4 ≤ Real.exp (-273472045411/400000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019024042923/1000000000000 : ℝ)/4 ≤ Real.exp ((1091/8192 : ℝ)-(163371764893/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (1091/8192 : ℝ) (4365/32768 : ℝ) (163371764893/200000000000 : ℝ) (2019024042923/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover7_leaf0125_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0125_certificate
#check SmaleRate.Proofs.cover7_leaf0126_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0126_certificate
#check SmaleRate.Proofs.cover7_leaf0127_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0127_certificate
#check SmaleRate.Proofs.cover7_leaf0128_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0128_certificate
#check SmaleRate.Proofs.cover7_leaf0129_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0129_certificate
#check SmaleRate.Proofs.cover7_leaf0130_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0130_certificate
#check SmaleRate.Proofs.cover7_leaf0131_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0131_certificate
#check SmaleRate.Proofs.cover7_leaf0132_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0132_certificate
#check SmaleRate.Proofs.cover7_leaf0133_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0133_certificate
#check SmaleRate.Proofs.cover7_leaf0134_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0134_certificate
#check SmaleRate.Proofs.cover7_leaf0135_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0135_certificate
#check SmaleRate.Proofs.cover7_leaf0136_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0136_certificate
#check SmaleRate.Proofs.cover7_leaf0137_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0137_certificate
#check SmaleRate.Proofs.cover7_leaf0138_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0138_certificate
#check SmaleRate.Proofs.cover7_leaf0139_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0139_certificate
#check SmaleRate.Proofs.cover7_leaf0140_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0140_certificate
#check SmaleRate.Proofs.cover7_leaf0141_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0141_certificate
#check SmaleRate.Proofs.cover7_leaf0142_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0142_certificate
#check SmaleRate.Proofs.cover7_leaf0143_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0143_certificate
#check SmaleRate.Proofs.cover7_leaf0144_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0144_certificate
#check SmaleRate.Proofs.cover7_leaf0145_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0145_certificate
#check SmaleRate.Proofs.cover7_leaf0146_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0146_certificate
#check SmaleRate.Proofs.cover7_leaf0147_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0147_certificate
#check SmaleRate.Proofs.cover7_leaf0148_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0148_certificate
#check SmaleRate.Proofs.cover7_leaf0149_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0149_certificate
