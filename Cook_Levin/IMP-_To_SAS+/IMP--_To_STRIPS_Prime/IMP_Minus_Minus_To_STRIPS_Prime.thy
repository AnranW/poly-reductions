\<^marker>\<open>creator Anran Wang\<close>

section "IMP-- to STRIPS'"

theory IMP_Minus_Minus_To_STRIPS_Prime
  imports "../IMP--_To_SAS++_Prime/IMP_Minus_Minus_To_SAS_Plus_Plus_Prime_Correctness" 
          "../SAS++_Prime_To_STRIPS_Prime/SAS_Plus_Plus_Prime_To_SAS_Plus"
          "../SAS++_Prime_To_STRIPS_Prime/SAS_Plus_Prime_STRIPS_Prime"
begin 
theorem imp_minus_minus_to_sas_plus_plus:
  assumes "(c, is1) \<rightarrow>\<^bsup>t\<^esup> (SKIP, is2)"
   "vs = enumerate_variables c"
   "dom is1 = set vs"
   "I = imp_minus_state_to_sas_plus (c,is1)"
   "G = imp_minus_state_to_sas_plus (SKIP,is2)"
   "t \<le> t'"
  shows "\<exists>plan. (STRIPS_Prime_Semantics.is_serial_solution_for_problem (\<phi> (SAS_Plus_Plus_Prime_To_SAS_Plus(imp_minus_minus_to_sas_plus_prime c))) plan) 
        \<and> length plan \<le> t' + length vs + 2" 
proof - 
  let ?P_sas2 = "imp_minus_minus_to_sas_plus_prime c "
  let ?P_sas1 = "SAS_Plus_Plus_Prime_To_SAS_Plus ?P_sas2"
  from assms obtain plan2 where 1:"is_serial_solution_for_problem_sas_plus_plus_prime I G ?P_sas2 plan2 
    \<and> length plan2 \<le> t'"
    by (meson imp_minus_minus_to_sas_plus_plus_prime)
    from assms have 2:"is_valid_problem_sas_plus_plus ?P_sas2 "
    by (simp add: imp_minus_minus_to_sas_plus_valid_prime)
  with 1 obtain prefix where 3:"length prefix \<le> length ((?P_sas2)\<^sub>\<V>\<^sub>+) + 1" and 
    4: "SAS_Plus_Prime_Semantics.is_serial_solution_for_problem ?P_sas1 
    (prefix @ (map SAS_Plus_Plus_Prime_Operator_To_SAS_Plus_Operator plan2)) "
    using SAS_Plus_Plus_Prime_To_SAS_Plus_ii  by blast
  have "length (PC # (map VN (enumerate_variables c))) = length (enumerate_variables c) + 1" 
    by simp
  then have 5: "length ((?P_sas2)\<^sub>\<V>\<^sub>+) = length (enumerate_variables c) + 1" 
    using enumerate_variables_def imp_minus_minus_to_sas_plus_def
    by (metis imp_minus_minus_to_sas_plus_prime_def sas_plus_problem.select_convs(1))
  with 3 have 6:"length prefix \<le> length (enumerate_variables c) + 2" 
    by simp
  let ?plan1 = "prefix @ (map SAS_Plus_Plus_Prime_Operator_To_SAS_Plus_Operator plan2)"
  from 1 6 have 7:"length ?plan1 \<le> t' + length (enumerate_variables c) + 2"   
    by simp
  from 2 have 8:"is_valid_problem_sas_plus ?P_sas1" 
    using SAS_Plus_Plus_Prime_To_SAS_Plus_def SAS_Plus_Plus_Prime_To_SAS_Plus_valid
    by blast
  let ?plan3 = "[\<phi>\<^sub>O ?P_sas1 op. op \<leftarrow> ?plan1]"
  have 9: "length ?plan3 = length ?plan1" by simp
  with 7 have 10: "length ?plan3 \<le> t' + length (enumerate_variables c) + 2"
    by simp    
  from 8 4 have "STRIPS_Prime_Semantics.is_serial_solution_for_problem (\<phi> ?P_sas1) ?plan3"
    using serial_sas_plus_equivalent_to_serial_strips 
    by blast  
  with 10 assms(2) show ?thesis 
    by auto
qed

end