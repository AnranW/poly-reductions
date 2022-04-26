\<^marker>\<open>creator Florian Keßler\<close>

section "IMP-- to SAS++ Correctness"

theory IMP_Minus_Minus_To_STRIPS_Prime
  imports IMP_Minus_Minus_To_SAS_Plus_Plus_Reduction "../SAS_Plus_Plus"
begin 

text \<open> We show correctness for the IMP-- to SAS++ reduction. \<close>

lemma imp_minus_minus_to_sas_plus_plus:
  assumes "(c, is1) \<rightarrow>\<^bsup>t\<^esup> (SKIP, is2)"
   "dom is1 = set (enumerate_variables c)"
   "I \<subseteq>\<^sub>m is1"
   "G \<subseteq>\<^sub>m is2"
   "t \<le> t'"
  shows "(\<exists>plan.
     is_serial_solution_for_problem_sas_plus_plus (imp_minus_minus_to_sas_plus c I G) plan
     \<and> length plan \<le> t')"
proof -
  let ?\<Psi> = "imp_minus_minus_to_sas_plus c I G"
  let ?I' = "imp_minus_state_to_sas_plus (c, is1)" 
  obtain plan where plan_def: "set plan \<subseteq> set ((?\<Psi>)\<^sub>\<O>\<^sub>+)
     \<and> length plan = t
     \<and> (execute_serial_plan_sas_plus ?I' plan)
        = imp_minus_state_to_sas_plus (SKIP, is2)"
    using imp_minus_minus_to_sas_plus_plus_aux[OF assms(1)] assms c_in_all_subprograms_c by blast
  moreover then have "(?\<Psi>)\<^sub>G\<^sub>+ \<subseteq>\<^sub>m execute_serial_plan_sas_plus ?I' plan"
    and "dom ?I' = set (((?\<Psi>))\<^sub>\<V>\<^sub>+)"
    and "(\<forall> v \<in> set ((?\<Psi>)\<^sub>\<V>\<^sub>+). the (?I' v) \<in> range_of' ?\<Psi> v)"
    and "((?\<Psi>)\<^sub>I\<^sub>+) \<subseteq>\<^sub>m ?I'"
    using assms plan_def c_in_all_subprograms_c
    apply(auto simp: imp_minus_minus_to_sas_plus_def Let_def 
        range_of'_def imp_minus_state_to_sas_plus_def map_comp_def map_le_def)
        apply (auto split: option.splits variable.splits)
    by (metis domIff option.distinct option.inject)+
  ultimately have "is_serial_solution_for_problem_sas_plus_plus ?\<Psi> plan" 
    using assms
    by(auto simp: is_serial_solution_for_problem_sas_plus_plus_def Let_def list_all_def ListMem_iff)
  then show ?thesis using plan_def \<open>t \<le> t'\<close>
    by blast
qed

lemma sas_plus_plus_to_imp_minus_minus:
  assumes "is_serial_solution_for_problem_sas_plus_plus (imp_minus_minus_to_sas_plus c I G) plan"
    "EV ` (ran I) \<subseteq> set domain"
    "EV ` (ran G) \<subseteq> set domain"
  shows "\<exists>is1 is2 t. (I|` set (enumerate_variables c)) \<subseteq>\<^sub>m is1 \<and> dom is1 = set (enumerate_variables c)
    \<and> (G|` set (enumerate_variables c)) \<subseteq>\<^sub>m is2 \<and> t \<le> length plan 
    \<and> (c, is1) \<rightarrow>\<^bsup>t\<^esup> (SKIP, is2)" 
proof -
  let ?\<Psi> = "imp_minus_minus_to_sas_plus c I G"
  obtain I' where I'_def: "((?\<Psi>)\<^sub>I\<^sub>+) \<subseteq>\<^sub>m I' \<and> dom I' = set ((?\<Psi>)\<^sub>\<V>\<^sub>+) 
        \<and> (\<forall>v \<in> set ((?\<Psi>)\<^sub>\<V>\<^sub>+). the (I' v) \<in> range_of' ?\<Psi> v)
        \<and> ((?\<Psi>)\<^sub>G\<^sub>+) \<subseteq>\<^sub>m execute_serial_plan_sas_plus I' plan" 
    using assms by (auto simp: is_serial_solution_for_problem_sas_plus_plus_def Let_def)
  let ?ss2 = "execute_serial_plan_sas_plus I' plan"
  let ?is1 = "snd (sas_plus_state_to_imp_minus I')"
  let ?is2 = "snd (sas_plus_state_to_imp_minus ?ss2)"
  have "\<forall>v\<in>set (enumerate_variables c). (\<exists>y \<in> set domain. I' (VN v) = Some y)" using I'_def 
    apply (auto simp: imp_minus_minus_to_sas_plus_def Let_def range_of'_def)
    by (metis domIff image_insert insertI1 insertI2 mk_disjoint_insert option.collapse)
  then have "sane_sas_plus_state I'" using I'_def assms
    apply (auto simp: sane_sas_plus_state_def imp_minus_minus_to_sas_plus_def Let_def map_le_def 
         range_of'_def)
    by (metis domIff insertI1 option.collapse)
  then obtain t where t_def: "t \<le> length plan \<and> sas_plus_state_to_imp_minus I' 
    \<rightarrow>\<^bsup>t\<^esup> sas_plus_state_to_imp_minus ?ss2"
    apply - apply(rule exE[OF sas_plus_plus_to_imp_minus_minus_aux[where ?ops=plan]])
    using assms I'_def  
    by(auto simp: is_serial_solution_for_problem_sas_plus_plus_def Let_def list_all_def ListMem_iff)
    
  moreover have "fst (sas_plus_state_to_imp_minus I') = c"
    and "fst (sas_plus_state_to_imp_minus ?ss2) = SKIP"
    using assms I'_def apply(auto simp: imp_minus_minus_to_sas_plus_def Let_def 
         sas_plus_state_to_imp_minus_def map_le_def imp_minus_state_to_sas_plus_def
        sane_sas_plus_state_def)
    by (metis (no_types, lifting) domain_element.inject domain_element.simps option.sel 
        option.inject variable.simps)+
  ultimately have "((c, ?is1) \<rightarrow>\<^bsup>t\<^esup> (SKIP, ?is2))" 
    using I'_def by (metis prod.collapse)
  moreover have "(I|` set (enumerate_variables c)) \<subseteq>\<^sub>m ?is1"
    "(G|` set (enumerate_variables c)) \<subseteq>\<^sub>m ?is2"
    using assms(2) I'_def 
    by (auto simp: imp_minus_minus_to_sas_plus_def imp_minus_state_to_sas_plus_map_le_then Let_def 
        range_of'_def)
  moreover have "dom ?is1 = set (enumerate_variables c)"
    using \<open>sane_sas_plus_state I'\<close> I'_def by(auto simp: imp_minus_minus_to_sas_plus_def 
        dom_snd_sas_plus_state_to_imp_minus Let_def)
  ultimately show ?thesis using I'_def t_def by auto
qed
    
    
end