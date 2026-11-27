# SmaleRate claim audit
Generated from Lean output.

CITED: 5, NOT-FORMALIZED: 3, OPEN: 34, PROVED: 160, PROVED-FROM-CITED: 60, PROVED-GIVEN SmaleRate.Background.CoefficientUpperFact: 2, PROVED-GIVEN SmaleRate.Background.CoefficientUpperFact, SmaleRate.Background.JordanCurveFact: 26, PROVED-GIVEN SmaleRate.Background.JordanCurveFact: 4.

PROVED-GIVEN rows retain named explicit computer checks or background hypotheses, recorded separately below and in CLAIMS.json. Cited axioms remain listed even on conditional rows. CITED is a direct external restatement; PROVED-FROM-CITED is internally derived. OPEN and VIOLATION fail the final check.

Type inspection follows project definition aliases and structure constructor types. Any check occurrence in a signature is conservatively treated as conditional and must occur in a binder type. Semantic equivalence, source fidelity, non-vacuity and completeness still require the independent foundations review.

| # | Lean name | Paper claim | Status | Cited axioms used |
|---|---|---|---|---|
| 1 | `minimum_attained` | minimum_attained. | PROVED | — |
| 2 | `critical_nonzero` | critical_nonzero. | PROVED | — |
| 3 | `critical_ratio_norm_formula` | critical_ratio_norm_formula. | PROVED | — |
| 4 | `s_nonneg` | s_nonneg. | PROVED | — |
| 5 | `s_le_ratio` | s_le_ratio. | PROVED | — |
| 6 | `scalar_invariance` | scalar_invariance. | PROVED | — |
| 7 | `zero_critical_value` | zero_critical_value. | PROVED | — |
| 8 | `critical_value_normalization` | critical_value_normalization. | PROVED | — |
| 9 | `kd_finite` | kd_finite. | PROVED | — |
| 10 | `smale_bound` | smale_bound. | PROVED | — |
| 11 | `small_degrees` | small_degrees. | PROVED | — |
| 12 | `small_degrees_two_three` | small_degrees_two_three. | PROVED | — |
| 13 | `counterexample_exists` | counterexample_exists. | PROVED | — |
| 14 | `counterexample_explicit_degree` | counterexample_explicit_degree. | OPEN | — |
| 15 | `jatar_ng_lower` | jatar_ng_lower. | PROVED | — |
| 16 | `kd_monotone` | kd_monotone. | PROVED | — |
| 17 | `kd_limit_and_sup` | kd_limit_and_sup. | PROVED | — |
| 18 | `earlier_bounds` | earlier_bounds. | OPEN | — |
| 19 | `crane_bound` | crane_bound. | OPEN | — |
| 20 | `expanded_lower_bound` | expanded_lower_bound. | OPEN | — |
| 21 | `expanded_upper_bound` | expanded_upper_bound. | OPEN | — |
| 22 | `expanded_crossover` | expanded_crossover. | PROVED | — |
| 23 | `elliptic_integrable` | elliptic_integrable. | PROVED-FROM-CITED | SmaleRate.Cited.dlmf_19_9_5 |
| 24 | `elliptic_positive` | elliptic_positive. | PROVED-FROM-CITED | SmaleRate.Cited.dlmf_19_9_5 |
| 25 | `elliptic_increasing` | elliptic_increasing. | PROVED-FROM-CITED | SmaleRate.Cited.dlmf_19_9_5 |
| 26 | `elliptic_continuous` | elliptic_continuous. | PROVED-FROM-CITED | SmaleRate.Cited.dlmf_19_9_5 |
| 27 | `elliptic_endpoints` | elliptic_endpoints. | PROVED-FROM-CITED | SmaleRate.Cited.dlmf_19_8_5, SmaleRate.Cited.dlmf_19_9_5 |
| 28 | `mu_decreasing` | mu_decreasing. | PROVED-FROM-CITED | SmaleRate.Cited.dlmf_19_9_5 |
| 29 | `mu_range` | mu_range. | PROVED-FROM-CITED | SmaleRate.Cited.dlmf_19_9_5 |
| 30 | `mu_continuous` | mu_continuous. | PROVED-FROM-CITED | SmaleRate.Cited.dlmf_19_9_5 |
| 31 | `mu_positive` | mu_positive. | PROVED-FROM-CITED | SmaleRate.Cited.dlmf_19_9_5 |
| 32 | `mu_endpoints` | mu_endpoints. | PROVED-FROM-CITED | SmaleRate.Cited.dlmf_19_9_5 |
| 33 | `mu_complement` | mu_complement. | PROVED-FROM-CITED | SmaleRate.Cited.dlmf_19_9_5 |
| 34 | `dlmf_19_9_5` | dlmf_19_9_5. | CITED | SmaleRate.Cited.dlmf_19_9_5 |
| 35 | `mu_log_upper` | mu_log_upper. | PROVED-FROM-CITED | SmaleRate.Cited.dlmf_19_9_5 |
| 36 | `mu_small_error` | mu_small_error. | PROVED-FROM-CITED | SmaleRate.Cited.dlmf_19_9_5 |
| 37 | `mu_near_one` | mu_near_one. | PROVED-FROM-CITED | SmaleRate.Cited.dlmf_19_9_5 |
| 38 | `thm_1_1` | thm_1_1. | OPEN | — |
| 39 | `cor_1_2` | cor_1_2. | OPEN | — |
| 40 | `ybound_at_zero` | ybound_at_zero. | PROVED-FROM-CITED | SmaleRate.Cited.dlmf_19_9_5 |
| 41 | `ybound_at_one` | ybound_at_one. | PROVED-FROM-CITED | SmaleRate.Cited.dlmf_19_9_5 |
| 42 | `ybound_below_four_near_one` | ybound_below_four_near_one. | PROVED-FROM-CITED | SmaleRate.Cited.dlmf_19_9_5 |
| 43 | `kd_lt_four` | kd_lt_four. | PROVED | — |
| 44 | `ybound_fixed_y_limit` | ybound_fixed_y_limit. | PROVED-FROM-CITED | SmaleRate.Cited.dlmf_19_9_5 |
| 45 | `degree_example_39` | degree_example_39. | OPEN | — |
| 46 | `inverse_branch_exists` | inverse_branch_exists. | PROVED | — |
| 47 | `inverse_branch_properties` | inverse_branch_properties. | PROVED | — |
| 48 | `inverse_jordan_domain` | inverse_jordan_domain. | PROVED | — |
| 49 | `exterior_image_geometry` | exterior_image_geometry. | PROVED | — |
| 50 | `capacity_identity` | capacity_identity. | OPEN | — |
| 51 | `capacity_step_scalar` | capacity_step_scalar. | PROVED | — |
| 52 | `riemann_map_for_exterior` | riemann_map_for_exterior. | OPEN | — |
| 53 | `xi_bound` | xi_bound. | PROVED | — |
| 54 | `betsakos_inequality` | betsakos_inequality. | CITED | SmaleRate.Cited.betsakos_2013 |
| 55 | `betsakos_equality` | betsakos_equality. | OPEN | — |
| 56 | `betsakos_derivative` | betsakos_derivative. | PROVED-FROM-CITED | SmaleRate.Cited.betsakos_2013, SmaleRate.Cited.dlmf_19_9_5 |
| 57 | `diameter_closure` | diameter_closure. | PROVED | — |
| 58 | `diameter_decreasing` | diameter_decreasing. | PROVED | — |
| 59 | `diameter_capacity` | diameter_capacity. | PROVED | — |
| 60 | `final_scalar_deduction` | final_scalar_deduction. | PROVED | — |
| 61 | `polynomial_bound` | polynomial_bound. | OPEN | — |
| 62 | `beta_y_change` | beta_y_change. | PROVED | — |
| 63 | `bound_set_well_defined` | bound_set_well_defined. | PROVED | — |
| 64 | `kd_le_best` | kd_le_best. | OPEN | — |
| 65 | `cor_step1_mu` | cor_step1_mu. | PROVED-FROM-CITED | SmaleRate.Cited.dlmf_19_9_5 |
| 66 | `cor_step1_majorant` | cor_step1_majorant. | OPEN | — |
| 67 | `exp_lower` | exp_lower. | PROVED | — |
| 68 | `general_L_majorant` | general_L_majorant. | PROVED-FROM-CITED | SmaleRate.Cited.dlmf_19_9_5 |
| 69 | `tail_log_correction` | tail_log_correction. | PROVED | — |
| 70 | `tail_log_ratio_decreasing` | tail_log_ratio_decreasing. | PROVED | — |
| 71 | `tail_lambda_upper` | tail_lambda_upper. | PROVED | — |
| 72 | `tail_constants` | tail_constants. | PROVED | — |
| 73 | `cor_step3` | cor_step3. | PROVED | — |
| 74 | `cor_step2` | cor_step2. | PROVED | — |
| 75 | `best_strict_improvement` | best_strict_improvement. | PROVED-FROM-CITED | SmaleRate.Cited.dlmf_19_9_5 |
| 76 | `prop_3_4_lower_error` | prop_3_4_lower_error. | PROVED-FROM-CITED | SmaleRate.Cited.dlmf_19_9_5 |
| 77 | `prop_3_4_upper` | prop_3_4_upper. | PROVED-FROM-CITED | SmaleRate.Cited.dlmf_19_9_5 |
| 78 | `prop_3_4_limit` | prop_3_4_limit. | PROVED-FROM-CITED | SmaleRate.Cited.dlmf_19_9_5 |
| 79 | `prop_denominator_positive` | prop_denominator_positive. | PROVED | — |
| 80 | `prop_delta_bound` | prop_delta_bound. | PROVED-FROM-CITED | SmaleRate.Cited.dlmf_19_9_5 |
| 81 | `prop_case_a` | prop_case_a. | PROVED-FROM-CITED | SmaleRate.Cited.dlmf_19_9_5 |
| 82 | `prop_case_b` | prop_case_b. | PROVED-FROM-CITED | SmaleRate.Cited.dlmf_19_9_5 |
| 83 | `prop_case_c` | prop_case_c. | PROVED-FROM-CITED | SmaleRate.Cited.dlmf_19_9_5 |
| 84 | `prop_uniform_lower` | prop_uniform_lower. | PROVED-FROM-CITED | SmaleRate.Cited.dlmf_19_9_5 |
| 85 | `prop_selected_L` | prop_selected_L. | PROVED-FROM-CITED | SmaleRate.Cited.dlmf_19_9_5 |
| 86 | `weaker_asymptotic_difference` | weaker_asymptotic_difference. | PROVED-FROM-CITED | SmaleRate.Cited.dlmf_19_9_5 |
| 87 | `weaker_k_gap_liminf` | weaker_k_gap_liminf. | OPEN | — |
| 88 | `earlier_crane_comparison` | earlier_crane_comparison. | PROVED | — |
| 89 | `sqrt_log_minimum` | sqrt_log_minimum. | PROVED | — |
| 90 | `earlier_fujikawa_comparison` | earlier_fujikawa_comparison. | PROVED | — |
| 91 | `earlier_three_comparisons` | earlier_three_comparisons. | PROVED | — |
| 92 | `d_plus_one_log_increasing` | d_plus_one_log_increasing. | PROVED | — |
| 93 | `agm_bracketing` | agm_bracketing. | PROVED | — |
| 94 | `agm_convergence` | agm_convergence. | PROVED | — |
| 95 | `agm_elliptic_identity` | agm_elliptic_identity. | PROVED-FROM-CITED | SmaleRate.Cited.dlmf_19_8_5 |
| 96 | `dlmf_19_8_5` | dlmf_19_8_5. | CITED | SmaleRate.Cited.dlmf_19_8_5 |
| 97 | `range_7_enclosure` | range_7_enclosure. | PROVED-FROM-CITED | SmaleRate.Cited.dlmf_19_8_5, SmaleRate.Cited.dlmf_19_9_5 |
| 98 | `range_8_enclosure` | range_8_enclosure. | PROVED-FROM-CITED | SmaleRate.Cited.dlmf_19_8_5, SmaleRate.Cited.dlmf_19_9_5 |
| 99 | `range_selected_values` | range_selected_values. | PROVED-FROM-CITED | SmaleRate.Cited.dlmf_19_8_5 |
| 100 | `range_tail` | range_tail. | PROVED-FROM-CITED | SmaleRate.Cited.dlmf_19_9_5 |
| 101 | `range_interval_lower` | range_interval_lower. | PROVED-FROM-CITED | SmaleRate.Cited.dlmf_19_9_5 |
| 102 | `figure3_height` | figure3_height. | OPEN | — |
| 103 | `table3_M_8` | Table 3 M, degree 8. | PROVED | — |
| 104 | `table3_target_8` | Table 3 target, degree 8. | PROVED | — |
| 105 | `table3_margin_8` | Table 3 margin, degree 8. | PROVED | — |
| 106 | `table3_M_9` | Table 3 M, degree 9. | PROVED | — |
| 107 | `table3_target_9` | Table 3 target, degree 9. | PROVED | — |
| 108 | `table3_margin_9` | Table 3 margin, degree 9. | PROVED | — |
| 109 | `table3_M_10` | Table 3 M, degree 10. | PROVED | — |
| 110 | `table3_target_10` | Table 3 target, degree 10. | PROVED | — |
| 111 | `table3_margin_10` | Table 3 margin, degree 10. | PROVED | — |
| 112 | `table3_M_11` | Table 3 M, degree 11. | PROVED | — |
| 113 | `table3_target_11` | Table 3 target, degree 11. | PROVED | — |
| 114 | `table3_margin_11` | Table 3 margin, degree 11. | PROVED | — |
| 115 | `table3_M_12` | Table 3 M, degree 12. | PROVED | — |
| 116 | `table3_target_12` | Table 3 target, degree 12. | PROVED | — |
| 117 | `table3_margin_12` | Table 3 margin, degree 12. | PROVED | — |
| 118 | `table3_M_13` | Table 3 M, degree 13. | PROVED | — |
| 119 | `table3_target_13` | Table 3 target, degree 13. | PROVED | — |
| 120 | `table3_margin_13` | Table 3 margin, degree 13. | PROVED | — |
| 121 | `table3_M_14` | Table 3 M, degree 14. | PROVED | — |
| 122 | `table3_target_14` | Table 3 target, degree 14. | PROVED | — |
| 123 | `table3_margin_14` | Table 3 margin, degree 14. | PROVED | — |
| 124 | `table3_M_15` | Table 3 M, degree 15. | PROVED | — |
| 125 | `table3_target_15` | Table 3 target, degree 15. | PROVED | — |
| 126 | `table3_margin_15` | Table 3 margin, degree 15. | PROVED | — |
| 127 | `table3_M_16` | Table 3 M, degree 16. | PROVED | — |
| 128 | `table3_target_16` | Table 3 target, degree 16. | PROVED | — |
| 129 | `table3_margin_16` | Table 3 margin, degree 16. | PROVED | — |
| 130 | `table3_M_17` | Table 3 M, degree 17. | PROVED | — |
| 131 | `table3_target_17` | Table 3 target, degree 17. | PROVED | — |
| 132 | `table3_margin_17` | Table 3 margin, degree 17. | PROVED | — |
| 133 | `table3_M_18` | Table 3 M, degree 18. | PROVED | — |
| 134 | `table3_target_18` | Table 3 target, degree 18. | PROVED | — |
| 135 | `table3_margin_18` | Table 3 margin, degree 18. | PROVED | — |
| 136 | `table3_M_19` | Table 3 M, degree 19. | PROVED | — |
| 137 | `table3_target_19` | Table 3 target, degree 19. | PROVED | — |
| 138 | `table3_margin_19` | Table 3 margin, degree 19. | PROVED | — |
| 139 | `table3_M_20` | Table 3 M, degree 20. | PROVED | — |
| 140 | `table3_target_20` | Table 3 target, degree 20. | PROVED | — |
| 141 | `table3_margin_20` | Table 3 margin, degree 20. | PROVED | — |
| 142 | `tail_star` | tail_star. | PROVED | — |
| 143 | `bounds_below_39` | bounds_below_39. | OPEN | — |
| 144 | `small_bound_below_39` | small_bound_below_39. | OPEN | — |
| 145 | `range_7_best_improvement` | range_7_best_improvement. | OPEN | — |
| 146 | `figure3_gap8` | figure3_gap8. | PROVED-FROM-CITED | SmaleRate.Cited.dlmf_19_8_5, SmaleRate.Cited.dlmf_19_9_5 |
| 147 | `general_exp_upper` | general_exp_upper. | PROVED | — |
| 148 | `log_one_sub` | log_one_sub. | PROVED | — |
| 149 | `log_one_sub_half` | log_one_sub_half. | PROVED | — |
| 150 | `diameter_closure_limit` | diameter_closure_limit. | PROVED | — |
| 151 | `betsakos_small_argument` | betsakos_small_argument. | PROVED-FROM-CITED | SmaleRate.Cited.dlmf_19_9_5 |
| 152 | `betsakos_large_argument` | betsakos_large_argument. | PROVED-FROM-CITED | SmaleRate.Cited.dlmf_19_9_5 |
| 153 | `zero_betsakos_interpretation` | zero_betsakos_interpretation. | PROVED-FROM-CITED | SmaleRate.Cited.dlmf_19_9_5 |
| 154 | `capacity_phi_expansion` | capacity_phi_expansion. | PROVED | — |
| 155 | `exterior_conformal_map` | exterior_conformal_map. | PROVED | — |
| 156 | `xi_polynomial_holomorphic_extension` | xi_polynomial_holomorphic_extension. | PROVED | — |
| 157 | `figure2_example` | figure2_example. | PROVED | — |
| 158 | `table2_8` | table2_8. | PROVED-FROM-CITED | SmaleRate.Cited.dlmf_19_8_5 |
| 159 | `figure3_dot_8` | figure3_dot_8. | PROVED-FROM-CITED | SmaleRate.Cited.dlmf_19_8_5 |
| 160 | `table2_100` | table2_100. | PROVED-FROM-CITED | SmaleRate.Cited.dlmf_19_8_5 |
| 161 | `figure3_dot_100` | figure3_dot_100. | PROVED-FROM-CITED | SmaleRate.Cited.dlmf_19_8_5 |
| 162 | `table2_10000` | table2_10000. | PROVED-FROM-CITED | SmaleRate.Cited.dlmf_19_8_5 |
| 163 | `figure3_dot_10000` | figure3_dot_10000. | PROVED-FROM-CITED | SmaleRate.Cited.dlmf_19_8_5 |
| 164 | `table2_1000000` | table2_1000000. | PROVED-FROM-CITED | SmaleRate.Cited.dlmf_19_8_5 |
| 165 | `figure3_dot_1000000` | figure3_dot_1000000. | PROVED-FROM-CITED | SmaleRate.Cited.dlmf_19_8_5 |
| 166 | `crane_numeric_8` | crane_numeric_8. | OPEN | — |
| 167 | `crane_numeric_9` | crane_numeric_9. | OPEN | — |
| 168 | `crane_numeric_10` | crane_numeric_10. | OPEN | — |
| 169 | `crane_numeric_11` | crane_numeric_11. | OPEN | — |
| 170 | `crane_numeric_12` | crane_numeric_12. | OPEN | — |
| 171 | `crane_numeric_16` | crane_numeric_16. | OPEN | — |
| 172 | `crane_numeric_25` | crane_numeric_25. | OPEN | — |
| 173 | `crane_numeric_100` | crane_numeric_100. | OPEN | — |
| 174 | `crane_numeric_10000` | crane_numeric_10000. | OPEN | — |
| 175 | `inverse_analytic_boundary` | inverse_analytic_boundary. | PROVED | — |
| 176 | `conformal_geometry_witness` | conformal_geometry_witness. | PROVED | — |
| 177 | `capacity_conformal_coefficient` | capacity_conformal_coefficient. | OPEN | — |
| 178 | `table3_printed_minimum` | table3_printed_minimum. | PROVED | — |
| 179 | `crane_unique_minimum` | crane_unique_minimum. | PROVED | — |
| 180 | `figure1_six_dots_above` | figure1_six_dots_above. | PROVED | — |
| 181 | `figure1_three_dots_below` | figure1_three_dots_below. | PROVED | — |
| 182 | `figure1_excluded_regions` | figure1_excluded_regions. | OPEN | — |
| 183 | `first_four_order` | first_four_order. | PROVED | — |
| 184 | `crane_gap_order` | crane_gap_order. | PROVED | — |
| 185 | `small_multiple_asymptotic` | small_multiple_asymptotic. | PROVED | — |
| 186 | `quadratic_inverse_example` | quadratic_inverse_example. | PROVED | — |
| 187 | `table2_earlier_8` | table2_earlier_8. | PROVED | — |
| 188 | `table2_earlier_100` | table2_earlier_100. | PROVED | — |
| 189 | `table2_earlier_10000` | table2_earlier_10000. | PROVED | — |
| 190 | `table2_earlier_1000000` | table2_earlier_1000000. | PROVED | — |
| 191 | `table3_M_rounding_8` | table3_M_rounding_8. | PROVED | — |
| 192 | `table3_target_rounding_8` | table3_target_rounding_8. | PROVED | — |
| 193 | `table3_M_rounding_9` | table3_M_rounding_9. | PROVED | — |
| 194 | `table3_target_rounding_9` | table3_target_rounding_9. | PROVED | — |
| 195 | `table3_M_rounding_10` | table3_M_rounding_10. | PROVED | — |
| 196 | `table3_target_rounding_10` | table3_target_rounding_10. | PROVED | — |
| 197 | `table3_M_rounding_11` | table3_M_rounding_11. | PROVED | — |
| 198 | `table3_target_rounding_11` | table3_target_rounding_11. | PROVED | — |
| 199 | `table3_M_rounding_12` | table3_M_rounding_12. | PROVED | — |
| 200 | `table3_target_rounding_12` | table3_target_rounding_12. | PROVED | — |
| 201 | `table3_M_rounding_13` | table3_M_rounding_13. | PROVED | — |
| 202 | `table3_target_rounding_13` | table3_target_rounding_13. | PROVED | — |
| 203 | `table3_M_rounding_14` | table3_M_rounding_14. | PROVED | — |
| 204 | `table3_target_rounding_14` | table3_target_rounding_14. | PROVED | — |
| 205 | `table3_M_rounding_15` | table3_M_rounding_15. | PROVED | — |
| 206 | `table3_target_rounding_15` | table3_target_rounding_15. | PROVED | — |
| 207 | `table3_M_rounding_16` | table3_M_rounding_16. | PROVED | — |
| 208 | `table3_target_rounding_16` | table3_target_rounding_16. | PROVED | — |
| 209 | `table3_M_rounding_17` | table3_M_rounding_17. | PROVED | — |
| 210 | `table3_target_rounding_17` | table3_target_rounding_17. | PROVED | — |
| 211 | `table3_M_rounding_18` | table3_M_rounding_18. | PROVED | — |
| 212 | `table3_target_rounding_18` | table3_target_rounding_18. | PROVED | — |
| 213 | `table3_M_rounding_19` | table3_M_rounding_19. | PROVED | — |
| 214 | `table3_target_rounding_19` | table3_target_rounding_19. | PROVED | — |
| 215 | `table3_M_rounding_20` | table3_M_rounding_20. | PROVED | — |
| 216 | `table3_target_rounding_20` | table3_target_rounding_20. | PROVED | — |
| 217 | `disk_green_instance` | disk_green_instance. | PROVED | — |
| 218 | `finite_green_exists` | finite_green_exists. | OPEN | — |
| 219 | `finite_green_conformal_invariance` | finite_green_conformal_invariance. | PROVED | — |
| 220 | `exterior_green_exists` | exterior_green_exists. | OPEN | — |
| 221 | `inversion_green_identity` | inversion_green_identity. | PROVED | — |
| 222 | `bernstein_walsh` | bernstein_walsh. | OPEN | — |
| 223 | `dubinin_polynomial_specialization` | dubinin_polynomial_specialization. | OPEN | — |
| 224 | `jatar_ng_boundary_critical_exists` | jatar_ng_boundary_critical_exists. | PROVED | — |
| 225 | `jatar_ng_leading_coefficient` | jatar_ng_leading_coefficient. | PROVED-FROM-CITED | SmaleRate.Cited.jatar_ng_2026_sec1_2_leading_lt_one |
| 226 | `jatar_ng_source_v` | jatar_ng_source_v. | CITED | SmaleRate.Cited.jatar_ng_2026_theorem1_v |
| 227 | `jatar_ng_printed_bound` | jatar_ng_printed_bound. | PROVED-FROM-CITED | SmaleRate.Cited.jatar_ng_2026_sec1_2_leading_lt_one, SmaleRate.Cited.jatar_ng_2026_theorem1_v |
| 228 | `jatar_ng_bound_limit` | jatar_ng_bound_limit. | PROVED | — |
| 229 | `finite_box_soundness` | finite_box_soundness. | PROVED-FROM-CITED | SmaleRate.Cited.dlmf_19_9_5 |
| 230 | `range7_finite_certificate` | range7_finite_certificate. | PROVED-FROM-CITED | SmaleRate.Cited.dlmf_19_8_5 |
| 231 | `range8_finite_certificate` | range8_finite_certificate. | PROVED-FROM-CITED | SmaleRate.Cited.dlmf_19_8_5 |
| 232 | `s_pos_of_critical_values_ne_zero` | s_pos_of_critical_values_ne_zero. | PROVED | — |
| 233 | `ybound_gt_rpow` | ybound_gt_rpow. | PROVED-FROM-CITED | SmaleRate.Cited.dlmf_19_9_5 |
| 234 | `koebe_quarter_omission` | koebe_quarter_omission. | PROVED | — |
| 235 | `lambda_chosen_identity` | lambda_chosen_identity. | PROVED | — |
| 236 | `tail_numerical_endpoints` | tail_numerical_endpoints. | PROVED | — |
| 237 | `fujikawa_identity` | fujikawa_identity. | PROVED | — |
| 238 | `earlier_q_log_bound` | earlier_q_log_bound. | PROVED | — |
| 239 | `earlier_bracket_bound` | earlier_bracket_bound. | PROVED | — |
| 240 | `earlier_endpoint_8` | earlier_endpoint_8. | PROVED | — |
| 241 | `earlier_difference_formulas` | earlier_difference_formulas. | PROVED | — |
| 242 | `earlier_q_half` | earlier_q_half. | PROVED | — |
| 243 | `earlier_q_eight` | earlier_q_eight. | PROVED | — |
| 244 | `prop_mu_complement_lower` | prop_mu_complement_lower. | PROVED-FROM-CITED | SmaleRate.Cited.dlmf_19_9_5 |
| 245 | `prop_log_complement_lower` | prop_log_complement_lower. | PROVED | — |
| 246 | `prop_delta_elementary_lower` | prop_delta_elementary_lower. | PROVED | — |
| 247 | `jn_radius_well_defined` | jn_radius_well_defined. | PROVED | — |
| 248 | `jn_normalization_witness` | jn_normalization_witness. | PROVED | — |
| 249 | `riemann_map_for_exterior_given_jordan` | conditional riemann_map_for_exterior; the unconditional row stays open. | PROVED-GIVEN SmaleRate.Background.JordanCurveFact | — |
| 250 | `capacity_conformal_coefficient_given_background` | conditional coefficient upper bound; the unconditional row stays open. | PROVED-GIVEN SmaleRate.Background.CoefficientUpperFact | — |
| 251 | `exterior_image_geometry_given_jordan` | conditional exterior_image_geometry; the original is now independently proved without this premise. | PROVED-GIVEN SmaleRate.Background.JordanCurveFact | — |
| 252 | `polynomial_bound_given_background` | conditional polynomial bound with both named facts explicit. | PROVED-GIVEN SmaleRate.Background.CoefficientUpperFact, SmaleRate.Background.JordanCurveFact | SmaleRate.Cited.betsakos_2013, SmaleRate.Cited.dlmf_19_9_5 |
| 253 | `thm_1_1_given_background` | conditional Theorem1.1; original unconditional row stays open. | PROVED-GIVEN SmaleRate.Background.CoefficientUpperFact, SmaleRate.Background.JordanCurveFact | SmaleRate.Cited.betsakos_2013, SmaleRate.Cited.dlmf_19_9_5 |
| 254 | `cor_1_2_given_background` | conditional Corollary1.2; original unconditional row stays open. | PROVED-GIVEN SmaleRate.Background.CoefficientUpperFact, SmaleRate.Background.JordanCurveFact | SmaleRate.Cited.betsakos_2013, SmaleRate.Cited.dlmf_19_9_5 |
| 255 | `small_bound_below_39_given_background` | conditional small-degree bound; explicit named facts retained. | PROVED-GIVEN SmaleRate.Background.CoefficientUpperFact, SmaleRate.Background.JordanCurveFact | SmaleRate.Cited.betsakos_2013, SmaleRate.Cited.dlmf_19_9_5 |
| 256 | `bounds_below_39_given_background` | conditional intermediate degree bound; original remains open. | PROVED-GIVEN SmaleRate.Background.CoefficientUpperFact, SmaleRate.Background.JordanCurveFact | SmaleRate.Cited.betsakos_2013, SmaleRate.Cited.dlmf_19_9_5 |
| 257 | `degree_example_39_given_background` | conditional 3.9 degree example; original remains open. | PROVED-GIVEN SmaleRate.Background.CoefficientUpperFact, SmaleRate.Background.JordanCurveFact | SmaleRate.Cited.betsakos_2013, SmaleRate.Cited.dlmf_19_9_5 |
| 258 | `kd_lt_four_given_background` | conditional strict all-degree bound; original remains open. | PROVED-GIVEN SmaleRate.Background.CoefficientUpperFact, SmaleRate.Background.JordanCurveFact | SmaleRate.Cited.betsakos_2013, SmaleRate.Cited.dlmf_19_9_5 |
| 259 | `smale_bound_given_background` | conditional weak all-degree bound; original remains open. | PROVED-GIVEN SmaleRate.Background.CoefficientUpperFact, SmaleRate.Background.JordanCurveFact | SmaleRate.Cited.betsakos_2013, SmaleRate.Cited.dlmf_19_9_5 |
| 260 | `kd_finite_given_background` | conditional supremum finiteness; original unconditional row remains open. | PROVED-GIVEN SmaleRate.Background.CoefficientUpperFact, SmaleRate.Background.JordanCurveFact | SmaleRate.Cited.betsakos_2013, SmaleRate.Cited.dlmf_19_9_5 |
| 261 | `kd_le_best_given_background` | conditional optimized bound; original unconditional row remains open. | PROVED-GIVEN SmaleRate.Background.CoefficientUpperFact, SmaleRate.Background.JordanCurveFact | SmaleRate.Cited.betsakos_2013, SmaleRate.Cited.dlmf_19_9_5 |
| 262 | `weaker_k_gap_liminf_given_background` | conditional K-gap consequence; original unconditional row remains open. | PROVED-GIVEN SmaleRate.Background.CoefficientUpperFact, SmaleRate.Background.JordanCurveFact | SmaleRate.Cited.betsakos_2013, SmaleRate.Cited.dlmf_19_9_5 |
| 263 | `crane_bound_given_background` | conditional Crane comparison for Kd; original remains open. | PROVED-GIVEN SmaleRate.Background.CoefficientUpperFact, SmaleRate.Background.JordanCurveFact | SmaleRate.Cited.betsakos_2013, SmaleRate.Cited.dlmf_19_9_5 |
| 264 | `cor_step1_majorant_given_background` | conditional Step1 majorant; original remains open. | PROVED-GIVEN SmaleRate.Background.CoefficientUpperFact, SmaleRate.Background.JordanCurveFact | SmaleRate.Cited.betsakos_2013, SmaleRate.Cited.dlmf_19_9_5 |
| 265 | `figure1_excluded_regions_given_background` | conditional excluded-region bound; original remains open. | PROVED-GIVEN SmaleRate.Background.CoefficientUpperFact, SmaleRate.Background.JordanCurveFact | SmaleRate.Cited.betsakos_2013, SmaleRate.Cited.dlmf_19_9_5 |
| 266 | `crane_numeric_margins` | scalar margins for the nine printed Crane numbers; no Kd hypothesis. | PROVED | — |
| 267 | `crane_numbers_given_background` | conditional nine-number Crane comparison; original unconditional rows remain open. | PROVED-GIVEN SmaleRate.Background.CoefficientUpperFact, SmaleRate.Background.JordanCurveFact | SmaleRate.Cited.betsakos_2013, SmaleRate.Cited.dlmf_19_9_5 |
| 268 | `crane_numeric_8_given_background` | conditional Crane number at degree 8; original unconditional row remains open. | PROVED-GIVEN SmaleRate.Background.CoefficientUpperFact, SmaleRate.Background.JordanCurveFact | SmaleRate.Cited.betsakos_2013, SmaleRate.Cited.dlmf_19_9_5 |
| 269 | `crane_numeric_9_given_background` | conditional Crane number at degree 9; original unconditional row remains open. | PROVED-GIVEN SmaleRate.Background.CoefficientUpperFact, SmaleRate.Background.JordanCurveFact | SmaleRate.Cited.betsakos_2013, SmaleRate.Cited.dlmf_19_9_5 |
| 270 | `crane_numeric_10_given_background` | conditional Crane number at degree 10; original unconditional row remains open. | PROVED-GIVEN SmaleRate.Background.CoefficientUpperFact, SmaleRate.Background.JordanCurveFact | SmaleRate.Cited.betsakos_2013, SmaleRate.Cited.dlmf_19_9_5 |
| 271 | `crane_numeric_11_given_background` | conditional Crane number at degree 11; original unconditional row remains open. | PROVED-GIVEN SmaleRate.Background.CoefficientUpperFact, SmaleRate.Background.JordanCurveFact | SmaleRate.Cited.betsakos_2013, SmaleRate.Cited.dlmf_19_9_5 |
| 272 | `crane_numeric_12_given_background` | conditional Crane number at degree 12; original unconditional row remains open. | PROVED-GIVEN SmaleRate.Background.CoefficientUpperFact, SmaleRate.Background.JordanCurveFact | SmaleRate.Cited.betsakos_2013, SmaleRate.Cited.dlmf_19_9_5 |
| 273 | `crane_numeric_16_given_background` | conditional Crane number at degree 16; original unconditional row remains open. | PROVED-GIVEN SmaleRate.Background.CoefficientUpperFact, SmaleRate.Background.JordanCurveFact | SmaleRate.Cited.betsakos_2013, SmaleRate.Cited.dlmf_19_9_5 |
| 274 | `crane_numeric_25_given_background` | conditional Crane number at degree 25; original unconditional row remains open. | PROVED-GIVEN SmaleRate.Background.CoefficientUpperFact, SmaleRate.Background.JordanCurveFact | SmaleRate.Cited.betsakos_2013, SmaleRate.Cited.dlmf_19_9_5 |
| 275 | `crane_numeric_100_given_background` | conditional Crane number at degree 100; original unconditional row remains open. | PROVED-GIVEN SmaleRate.Background.CoefficientUpperFact, SmaleRate.Background.JordanCurveFact | SmaleRate.Cited.betsakos_2013, SmaleRate.Cited.dlmf_19_9_5 |
| 276 | `crane_numeric_10000_given_background` | conditional Crane number at degree 10000; original unconditional row remains open. | PROVED-GIVEN SmaleRate.Background.CoefficientUpperFact, SmaleRate.Background.JordanCurveFact | SmaleRate.Cited.betsakos_2013, SmaleRate.Cited.dlmf_19_9_5 |
| 277 | `gap_gt_four` | scalar Figure3 height lower bound; no Kd hypothesis. | PROVED-FROM-CITED | SmaleRate.Cited.dlmf_19_9_5 |
| 278 | `figure3_height_given_background` | conditional Figure3 height; original unconditional row remains open. | PROVED-GIVEN SmaleRate.Background.CoefficientUpperFact, SmaleRate.Background.JordanCurveFact | SmaleRate.Cited.betsakos_2013, SmaleRate.Cited.dlmf_19_9_5 |
| 279 | `degree_seven_target_upper` | degree-seven target comparison; independent of the bestBound enclosure. | PROVED | — |
| 280 | `fujikawa_seven_scalar` | degree-seven older-bound minimum and printed decimal enclosure. | PROVED | — |
| 281 | `table2_target_columns` | elementary target entries in Table2, independent of the elliptic beta columns. | PROVED | — |
| 282 | `finite_green_exists_given_jordan` | finite Green existence from the analytic RMT; original unconditional row remains open. | PROVED-GIVEN SmaleRate.Background.JordanCurveFact | — |
| 283 | `lemniscate_frontier_value` | component-frontier polynomial modulus at the defining radius. | PROVED | — |
| 284 | `jatar_ng_boundary_value` | normalized boundary-critical witness has unit polynomial modulus. | PROVED | — |
| 285 | `jatar_ng_leading_coefficient_positive` | positive leading coefficient; the strict upper bound is a separate cited row. | PROVED | — |
| 286 | `jatar_ng_leading_lt_one` | strict leading-coefficient upper restriction, direct external restatement. | CITED | SmaleRate.Cited.jatar_ng_2026_sec1_2_leading_lt_one |
| 287 | `best_seven_upper` | strict upper half of the degree-seven best-bound enclosure; lower cover remains separate. | PROVED-FROM-CITED | SmaleRate.Cited.dlmf_19_8_5 |
| 288 | `best_eight_upper` | strict upper half of the degree-eight best-bound enclosure; lower cover remains separate. | PROVED-FROM-CITED | SmaleRate.Cited.dlmf_19_8_5 |
| 289 | `finite_green_conformal_invariance_given_jordan` | historical conditional Green coverage from disk coordinates; the original is independently proved without this premise. | PROVED-GIVEN SmaleRate.Background.JordanCurveFact | — |
| 290 | `capacity_exterior_upper_given_coefficient` | upper half of the concrete capacity formula; the original equality remains open. | PROVED-GIVEN SmaleRate.Background.CoefficientUpperFact | — |
| 291 | `range_7_best_improvement_given_background` | degree-seven comparison with explicit main-theorem premises; original unconditional row remains open. | PROVED-GIVEN SmaleRate.Background.CoefficientUpperFact, SmaleRate.Background.JordanCurveFact | SmaleRate.Cited.betsakos_2013, SmaleRate.Cited.dlmf_19_8_5, SmaleRate.Cited.dlmf_19_9_5 |

## Computer-check propositions and proof status

These are ordinary propositions, never project axioms. Per-entry descriptions distinguish external checks from kernel-proved compatibility interfaces. The public mathematical certificate row records a discharged check; this audit does not execute or certify external programs.

| Lean Prop | Description and external check evidence |
|---|---|

## Named background hypotheses

Explicit hypotheses, never axioms or computer checks. Their source areas are not formalized; conditional deductions retain their exact names. Cited axioms used in a deduction remain listed separately.

| Lean Prop | Scope and review evidence | Status |
|---|---|---|
| `SmaleRate.Background.JordanCurveFact` | NAMED HYPOTHESIS, NOT AN AXIOM. Jordan–Schoenflies topology. For a bounded domain with a continuous injective circle frontier, the interior is simply connected and the exterior of its closure is connected. Both clauses are needed: the second supports the constructed exterior E_y; the first feeds the separately proved analytic RMT. Every conditional result must bind this proposition explicitly and report PROVED GIVEN it. The paper's E_y construction is not part of this universal background fact. | NOT-FORMALIZED |
| `SmaleRate.Background.CoefficientUpperFact` | NAMED HYPOTHESIS, NOT AN AXIOM. Upper half of the continuum leading-coefficient formula, in transfinite-diameter notation: Ransford5.2.3 / Corollary5.2.2 AND Fekete–Szegő5.5.2. This remains an explicit hypothesis throughout. The application to E_y, its concrete coefficient and the scalar bound remain proofs. | NOT-FORMALIZED |

## NOT-FORMALIZED registry

Every registered omission is counted separately, including background/method entries. An entry is not a proved theorem. Empty registry means no declared omissions, not automatic completeness of the paper inventory.

| # | Kind | Reason and paper location | Status |
|---|---|---|---|
| NgreenGeneral | out of scope | the general potential-theoretic Green theory for arbitrary irregular domains is not formalized here. Concrete classical Jordan-domain instances have OPEN typed rows; they are not the general theorem. | NOT-FORMALIZED |
| NdubininGeneral | out of scope | Dubinin's general spherical meromorphic inequality with a complete multiplicity-counted pole fiber is not formalized. Its polynomial specialization has an OPEN row; no general result is imported. | NOT-FORMALIZED |
| NcapacityPotential | absorbed boundary | potential-theoretic capacity is not defined. Fekete–Szegő is absorbed into the TD coefficient boundary, which must cite Ransford5.2.3 / Cor5.2.2 AND5.5.2. No theorem is proved by the alias. | NOT-FORMALIZED |
