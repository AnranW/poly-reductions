theory VC_To_HC
  imports  Main "Three_Sat_To_Set_Cover" Graph_Theory.Graph_Theory
begin

subsection\<open>Preliminaries\<close>

definition
  "is_vertex_cover_list E V \<equiv> \<forall> e \<in> set E. \<exists> v \<in> set V. v \<in> e"

(*If size of V is smaller than k, then there is a problem concerning the cover nodes in the Graph*)
definition
  "vertex_cover_list \<equiv>
  {(E, k). \<exists>V. ugraph (set E) \<and> (set V) \<subseteq> \<Union> (set E) \<and> k \<le> card (\<Union> (set E)) \<and> size V = k \<and> 
    is_vertex_cover_list E V \<and> distinct E \<and> distinct V}"

datatype ('a, 'b) hc_node = Cover nat | Edge 'a 'b nat

(*pre_digraph.cycle already assumes that every node is only contained once*)
(*Case for empty c is already in cycle*)
definition
  "is_hc (G::('a,('a \<times> 'a)) pre_digraph) (c:: 'a list)  \<equiv> 
    (pre_digraph.cycle G (vwalk_arcs c) \<and> (\<forall>x\<in> verts G. x \<in> set c))\<or> card (verts G) \<le> 1"

definition
  "hc \<equiv> {G. \<exists>c. wf_digraph G \<and> is_hc G c}"

definition
  "vc_hc \<equiv> \<lambda>(E, k).
    if ugraph (set E) \<and>  k \<le> card (\<Union> (set E))
        then  \<lparr>verts = {Cover i|i. i< k} \<union> {Edge v e 0|v e. e\<in> set E \<and> v \<in> e}\<union> {Edge v e 1|v e. e\<in> set E \<and> v \<in> e},
          arcs = {(Edge v e 0, Edge v e 1)|v e. e\<in> set E \<and> v \<in> e} \<union> 
            {(Edge v e 0, Edge u e 0)|u v e. e\<in>set E \<and> v \<in> e \<and> u \<in> e} \<union>
            {(Edge v e 1, Edge u e 1)|u v e. e\<in> set E \<and> v \<in> e \<and> u \<in> e} \<union>
            {(Edge v e1 1, Edge v e2 0)| v e1 e2 i j. i<length E \<and> j<length E \<and>  e1 = E!i\<and> e2 = E!i \<and> v \<in> e1 \<and> v \<in> e2 \<and> 
              \<not> (\<exists>i'< size E. v \<in> E!i' \<and> i < i' \<and> i' < j)} \<union>
            {(Edge v e 1, Cover n)| v e n i. i<length E \<and> e = E!i\<and> v \<in> e \<and> 
              \<not> (\<exists>j < size E. v \<in> E!j \<and> i < j) \<and> n< k}\<union>
            {(Cover n, Edge v e 0)| v e n i. i<length E \<and> e = E!i\<and> v \<in> e \<and> 
              \<not> (\<exists>j < size E. v \<in> E!j \<and> j < i) \<and> n < k},
          tail = fst, head = snd \<rparr>
        else \<lparr>verts = {Cover 0}, arcs = {}, tail = fst, head = snd\<rparr>"


lemma else_not_in_hc: 
  assumes "G = \<lparr>verts = {Cover 0, Cover 1}, arcs = {}, tail = fst, head = snd\<rparr>"
  shows "G \<notin> hc"
proof 
  assume "G \<in> hc"
  then have "\<exists> c. pre_digraph.cycle G (vwalk_arcs c) \<and> (\<forall>x\<in> verts G. x \<in> set c)" 
    using assms hc_def 
    by (simp add: hc_def doubleton_eq_iff is_hc_def)
  then obtain c where c_def: "pre_digraph.cycle G (vwalk_arcs c)" "(\<forall>x\<in> verts G. x \<in> set c)" by blast
  with pre_digraph.cycle_def have not_empty: "vwalk_arcs c \<noteq> []"  by fastforce
  from pre_digraph.cycle_def pre_digraph.awalk_def c_def have subset: "set (vwalk_arcs c) \<subseteq> arcs G" by metis
  have "arcs G = {}" using assms by(auto)
  with subset  have "set (vwalk_arcs c) = {}" by auto
  then show "False" using not_empty by(auto)
qed

lemma else_wf_digraph: 
  assumes "G = \<lparr>verts = {Cover 0, Cover 1}, arcs = {}, tail = fst, head = snd\<rparr>"
  shows "wf_digraph G"
  by(auto simp add: hc_def wf_digraph_def is_hc_def assms)

lemma if_else_in_hc: 
  assumes "G = \<lparr>verts = {Cover 0}, arcs = {}, tail = fst, head = snd\<rparr>"
  shows "G \<in> hc"
  by(auto simp add: hc_def wf_digraph_def is_hc_def assms)

lemma if_else_wf_digraph: 
  assumes "G = \<lparr>verts = {Cover 0}, arcs = {}, tail = fst, head = snd\<rparr>"
  shows "wf_digraph G"
  by(auto simp add: hc_def wf_digraph_def is_hc_def assms)

subsection\<open>(E,k) \<in> vc \<Longrightarrow> vc_hc (E, k) f \<in> hc\<close>

definition get_second where
  "get_second e \<equiv> SOME v. v \<in> e"

fun construct_cycle_add_edge_nodes:: "('a set list) \<Rightarrow> 'a \<Rightarrow> ('a set) \<Rightarrow>  (('a, 'a set) hc_node) list"
  where 
"construct_cycle_add_edge_nodes [] v C = []" |
"construct_cycle_add_edge_nodes (e#es) v C = (if v \<in> e then 
    (let u = (get_second (e-{v})) in (if u\<in> C then [(Edge v e 0), (Edge v e 1)] 
      else [(Edge v e 0), (Edge u e 0), (Edge u e 1), (Edge v e 1)]))  
    else construct_cycle_add_edge_nodes es v C)"

fun construct_cycle_1::"'a set list \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> 'a set \<Rightarrow> (('a, 'a set) hc_node) list"  where
"construct_cycle_1 E (x#Cs) n C =(Cover n) # (construct_cycle_add_edge_nodes E x C) @ 
    (construct_cycle_1 E Cs (n+1) C)"|
"construct_cycle_1 E [] n C = [(Cover 0)]"

fun construct_cycle:: "'a set list \<Rightarrow> 'a list \<Rightarrow> (('a, 'a set) hc_node \<times> ('a, 'a set) hc_node) list" where
"construct_cycle E C = vwalk_arcs (construct_cycle_1 E C 0 (set C))"


context 
  fixes E k assumes in_vc: "(E, k) \<in> vertex_cover_list"
  fixes Cov assumes cover:"is_vertex_cover_list E Cov" "distinct Cov" "size Cov = k"
  fixes G assumes G_def: "G = vc_hc (E,k)"
  fixes Cycle assumes Cycle_def: "Cycle = construct_cycle_1 E Cov 0 (set Cov)"
begin

lemma "size Cov = card (set Cov)"
  using cover by (simp add: distinct_card)

lemma in_vc_k_smaller:
  assumes "(E, k) \<in> vertex_cover_list" "\<not> k \<le> card (\<Union> (set E))"
  shows "False"
  using vertex_cover_list_def assms by(auto simp add: vertex_cover_list_def assms)

lemma G_def_2:
  shows "G =  \<lparr>verts = {Cover i|i. i< k} \<union> {Edge v e 0|v e. e\<in> set E \<and> v \<in> e}\<union> {Edge v e 1|v e. e\<in> set E \<and> v \<in> e},
          arcs = {(Edge v e 0, Edge v e 1)|v e. e\<in> set E \<and> v \<in> e} \<union> 
            {(Edge v e 0, Edge u e 0)|u v e. e\<in>set E \<and> v \<in> e \<and> u \<in> e} \<union>
            {(Edge v e 1, Edge u e 1)|u v e. e\<in> set E \<and> v \<in> e \<and> u \<in> e} \<union>
            {(Edge v e1 1, Edge v e2 0)| v e1 e2 i j. i<length E \<and> j<length E \<and>  e1 = E!i\<and> e2 = E!i \<and> v \<in> e1 \<and> v \<in> e2 \<and> 
              \<not> (\<exists>i'< size E. v \<in> E!i' \<and> i < i' \<and> i' < j)} \<union>
            {(Edge v e 1, Cover n)| v e n i. i<length E \<and> e = E!i\<and> v \<in> e \<and> 
              \<not> (\<exists>j < size E. v \<in> E!j \<and> i < j) \<and> n< k}\<union>
            {(Cover n, Edge v e 0)| v e n i. i<length E \<and> e = E!i\<and> v \<in> e \<and> 
              \<not> (\<exists>j < size E. v \<in> E!j \<and> j < i) \<and> n < k},
          tail = fst, head = snd \<rparr>" 
  using in_vc vertex_cover_list_def G_def apply(auto simp add: vc_hc_def) 
  using in_vc_k_smaller by blast+ 

lemma is_wf_digraph:
  shows "wf_digraph G"
  by(auto simp add: G_def_2 wf_digraph_def) 

lemma  aux4: "set (vwalk_arcs Cycle) \<subseteq> arcs G" sorry

lemma aux1:assumes "card (verts G) > 1" shows"1 < size Cycle" sorry
lemma aux2: assumes "v = (hd Cycle)" shows "v \<in> (verts G)" using is_wf_digraph aux4 wf_digraph_def sledgehammer  sorry

lemma aux3: assumes "1 < size Cycle" shows "vwalk_arcs Cycle \<noteq> []" proof -
    obtain x y cs where "Cycle = x#y#cs" using assms 
      by (metis One_nat_def length_0_conv length_Cons less_numeral_extra(4) not_one_less_zero vwalk_arcs.cases)
    then have "vwalk_arcs Cycle = (x,y)#(vwalk_arcs (y#cs))" by simp
    then have "vwalk_arcs Cycle \<noteq> []" by auto
    then show ?thesis .
  qed

lemma is_cylce: 
  assumes "card (verts G) > 1" "v \<in> (verts G)"  " v =(hd Cycle)" 
  shows "pre_digraph.cycle G (vwalk_arcs Cycle)"
proof -
  have "1 < size Cycle" using assms aux1 by auto
  then have not_empty: "vwalk_arcs Cycle \<noteq> []" 
    using assms aux3 by auto
  have distinct: "distinct (tl (pre_digraph.awalk_verts G v (vwalk_arcs Cycle)))"sorry
  have contained: "set (vwalk_arcs Cycle) \<subseteq> arcs G" sorry
  have awalk: "pre_digraph.awalk G v (vwalk_arcs Cycle) v" sorry
  show ?thesis using not_empty distinct contained awalk pre_digraph.cycle_def pre_digraph.awalk_def by(auto)  
qed

lemma cylce_contains_all_verts:
  assumes "card (verts G) > 1"
  shows "(\<forall>x\<in> verts G. x \<in> set Cycle)" 
  sorry

lemma is_hc_cycle_graph: 
  shows "is_hc G Cycle"
  using cylce_contains_all_verts is_cylce is_hc_def aux1 aux2
  by (metis One_nat_def is_hc_def leI)


lemma vc_impl_hc_context: "vc_hc (E,k) \<in> hc"
  using is_wf_digraph is_hc_cycle_graph G_def hc_def
  by auto

end


subsection\<open>vc_hc (E, k) f \<in> hc  \<Longrightarrow> (E,k) \<in> VC\<close>
context 
  fixes E k  assumes "vc_hc (E, k) \<in> hc"
begin

end

subsection\<open> Main theorem \<close>

lemma vc_impl_hc: "(E,k) \<in> vertex_cover_list \<Longrightarrow> vc_hc (E,k) \<in> hc"
proof -
  assume in_vc: "(E,k)\<in> vertex_cover_list"
  then obtain Cov where "is_vertex_cover_list E Cov" "distinct Cov" "size Cov = k" 
    using vertex_cover_list_def 
    by (smt case_prodD mem_Collect_eq)
  then show ?thesis 
  using vc_impl_hc_context in_vc by blast
qed

lemma hc_impl_vc: "vc_hc (E,k) \<in> hc \<Longrightarrow> (E,k) \<in> vertex_cover_list"
proof -
  show ?thesis sorry
qed



theorem is_reduction_vc_to_hc:
  "is_reduction vc_hc vertex_cover_list hc"
  unfolding is_reduction_def using vc_impl_hc hc_impl_vc by(auto)


subsection\<open>Need to prove equivalence of Vertex-Cover\<close>

lemma aux: 
  assumes "distinct E" "distinct V" 
  shows "is_vertex_cover (set E) (set V)\<longleftrightarrow> is_vertex_cover_list E V"
  apply(auto) 
  sorry

lemma "(set E, k) \<in> vertex_cover \<longleftrightarrow> (E, k) \<in> vertex_cover_list"
  using vertex_cover_def vertex_cover_list_def aux apply(auto)
  sorry



end

