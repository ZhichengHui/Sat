theory Sat_CDCL
  imports Sat_Proof.Sat_Level0
begin

text \<open>The contract of the CDCL search of \<^verbatim>\<open>core/src/lib.rs\<close>, \<^verbatim>\<open>cdcl\<close>. The functions it calls
  (\<^verbatim>\<open>Sat_Search\<close>) only need to terminate without a panic. Its answers rest on the checks of
  \<^verbatim>\<open>Sat_Certify\<close>.\<close>

section \<open>The clause database of the search\<close>

text \<open>The facts about the clause database and the answers that the main loop of \<^verbatim>\<open>cdcl\<close> uses.\<close>

lemma learned_ok_Nil:
  \<open>rvec_elems L = [] \<Longrightarrow> learned_ok f L\<close>
  unfolding learned_ok_def by simp

lemma f_small:
  assumes \<open>sat_repr_ok f\<close> \<open>\<not> 0x100000000000000 \<le> word64_of_nat (length (cls f))\<close>
  shows \<open>length (cls f) < 4611686018427387904\<close>
proof -
  have lf: \<open>length (cls f) < 2 ^ 64\<close>
    using assms(1) unfolding sat_repr_ok_def by simp
  then have \<open>unat (word64_of_nat (length (cls f))) = length (cls f)\<close>
    by (simp add: unat_of_nat_eq)
  then show ?thesis
    using assms(2) by (simp add: word_le_nat_alt not_le)
qed

lemma db_small_of:
  assumes \<open>sat_repr_ok f\<close> \<open>length (cls f) < 4611686018427387904\<close> \<open>learned_ok f L\<close>
  shows \<open>db_small f L\<close>
  using assms unfolding db_small_def db_def sat_repr_ok_def learned_ok_def by fastforce

lemma db_index_add:
  assumes \<open>length (cls f) < 4611686018427387904\<close> \<open>rvec_length L < 4611686018427387904\<close>
  shows \<open>unat (word64_of_nat (length (cls f))) + unat (word64_of_nat (rvec_length L))
    < 18446744073709551616\<close>
  using assms by (simp add: unat_of_nat_eq)

lemma learned_small:
  assumes \<open>learned_ok f L\<close> \<open>\<not> 0x100000000000000 \<le> word64_of_nat (rvec_length L)\<close>
  shows \<open>rvec_length L < 4611686018427387904\<close>
proof -
  have \<open>rvec_length L < 2 ^ 64\<close>
    using assms(1) unfolding learned_ok_def by simp
  then have \<open>unat (word64_of_nat (rvec_length L)) = rvec_length L\<close>
    by (simp add: unat_of_nat_eq)
  then show ?thesis
    using assms(2) by (simp add: word_le_nat_alt not_le)
qed

lemma cdcl_post_None:
  \<open>cdcl_post f None\<close>
  unfolding cdcl_post_def by simp

lemma cdcl_post_Sat:
  \<open>rvec_length m = unat (Formula_num_vars f) \<Longrightarrow> formula_sat (rvec_elems m) f \<Longrightarrow>
    cdcl_post f (Some (Answer_Sat (make_Assignments m)))\<close>
  unfolding cdcl_post_def by simp

lemma cdcl_post_Unsat:
  \<open>learned_ok f L \<Longrightarrow> \<forall>a. \<exists>c \<in> set (db f L). \<not> clause_sat a c \<Longrightarrow>
    cdcl_post f (Some Answer_Unsat)\<close>
  unfolding cdcl_post_def using db_sat by fastforce

lemma half_add:
  assumes \<open>x < (0x4000000000000000 :: 64 word)\<close>
  shows \<open>unat x + unat (x div 2) < 18446744073709551616\<close>
proof -
  have \<open>unat (x div 2) \<le> unat x\<close>
    by (simp add: unat_div)
  then show ?thesis
    using big_c(1)[OF assms] by linarith
qed

lemma f_len64:
  \<open>sat_repr_ok f \<Longrightarrow> length (cls f) < 18446744073709551616\<close>
  unfolding sat_repr_ok_def by simp

text \<open>A certified clause pushed onto the learned clauses.\<close>
lemma learned_push':
  \<open>learned_ok f L \<Longrightarrow> \<not> 0x100000000000000 \<le> word64_of_nat (rvec_length L) \<Longrightarrow>
    rvec_length x \<le> 4611686018427387904 \<Longrightarrow>
    \<forall>a. (\<forall>c \<in> set (db f L). clause_sat a c) \<longrightarrow> (\<exists>l \<in> set (rvec_elems x). lit_sat a l) \<Longrightarrow>
    vok L24 L \<Longrightarrow>
    learned_ok f (the (rvec_append_val L [make_Clause x]))\<close>
  using learned_ok_push[of f L \<open>make_Clause x\<close> \<open>the (rvec_append_val L [make_Clause x])\<close>]
    learned_small[of f L] push_ok(3)[of L24 L \<open>[make_Clause x]\<close>] cap_max_big(4) by simp

text \<open>\<^verbatim>\<open>on_conflict\<close> pushes onto \<^verbatim>\<open>lbd\<close> and \<^verbatim>\<open>dead\<close>, both shorter than \<^verbatim>\<open>BIG\<close>.\<close>
lemma sok_lbd_dead:
  assumes s: \<open>sok s\<close>
    and l: \<open>word64_of_nat (rvec_length (Search_lbd s)) < (0x100000000000000 :: 64 word)\<close>
    and d: \<open>word64_of_nat (rvec_length (Search_dead s)) < (0x100000000000000 :: 64 word)\<close>
  shows \<open>\<exists>y. rvec_append_val (Search_dead s) [False] = Some y\<close>
    \<open>\<exists>y. rvec_append_val (Search_lbd s) [x] = Some y\<close>
    \<open>sok_in (update_Search_dead (\<lambda>_. the (rvec_append_val (Search_dead s) [False]))
       (update_Search_lbd (\<lambda>_. the (rvec_append_val (Search_lbd s) [x])) s))\<close>
proof -
  have v: \<open>vok L1 (Search_dead s)\<close> \<open>vok L8 (Search_lbd s)\<close>
    using s unfolding sok_def by simp_all
  note pd = push_ok[of L1 \<open>Search_dead s\<close> \<open>[False]\<close>, OF v(1) d cap_max_big(1)]
  note pl = push_ok[of L8 \<open>Search_lbd s\<close> \<open>[x]\<close>, OF v(2) l cap_max_big(2)]
  show \<open>\<exists>y. rvec_append_val (Search_dead s) [False] = Some y\<close>
    \<open>\<exists>y. rvec_append_val (Search_lbd s) [x] = Some y\<close>
    \<open>sok_in (update_Search_dead (\<lambda>_. the (rvec_append_val (Search_dead s) [False]))
       (update_Search_lbd (\<lambda>_. the (rvec_append_val (Search_lbd s) [x])) s))\<close>
    using pd pl s by (simp_all add: sok_in_def sok_def)
qed

text \<open>\<^verbatim>\<open>cdcl\<close> pushes onto \<^verbatim>\<open>lim\<close>, shorter than \<^verbatim>\<open>BIG\<close>.\<close>
lemma sok_lim_push:
  assumes s: \<open>sok_in s\<close>
    and l: \<open>word64_of_nat (rvec_length (Search_lim s)) < (0x100000000000000 :: 64 word)\<close>
  shows \<open>\<exists>y. rvec_append_val (Search_lim s) [x] = Some y\<close>
    \<open>sok_in (update_Search_lim (\<lambda>_. the (rvec_append_val (Search_lim s) [x])) s)\<close>
proof -
  have v: \<open>vok L8 (Search_lim s)\<close>
    using s unfolding sok_in_def sok_def by simp
  show \<open>\<exists>y. rvec_append_val (Search_lim s) [x] = Some y\<close>
    \<open>sok_in (update_Search_lim (\<lambda>_. the (rvec_append_val (Search_lim s) [x])) s)\<close>
    using push_ok[of L8 \<open>Search_lim s\<close> \<open>[x]\<close>, OF v l cap_max_big(2)] s
    by (simp_all add: sok_in_def sok_def)
qed

text \<open>\<^verbatim>\<open>on_conflict\<close> pushes a learned clause onto \<open>L\<close>, shorter than \<^verbatim>\<open>BIG\<close>.\<close>
lemma learned_push_ok:
  assumes \<open>vok L24 L\<close> \<open>\<not> 0x100000000000000 \<le> word64_of_nat (rvec_length L)\<close>
  shows \<open>\<exists>y. rvec_append_val L [x] = Some y\<close> \<open>vok L24 (the (rvec_append_val L [x]))\<close>
  using push_ok(1,2)[of L24 L \<open>[x]\<close>] assms cap_max_big(4) by (simp_all add: not_le)

section \<open>Bounds of the main loop\<close>

method cdcl_bound =
  (search_bound | rule cdcl_post_None | (rule learned_ok_Nil, simp) |
    (rule cdcl_post_Sat cdcl_post_Unsat half_add f_small f_len64 learned_push'; assumption) |
    (rule db_small_of db_index_add;
      (assumption | (rule learned_ok_Nil, simp) |
       (rule f_small learned_small learned_push'; assumption))))

context Sat_ctx
begin

section \<open>The search with certified answers\<close>

text \<open>A conflict adds a certified learned clause to the database; \<^verbatim>\<open>cdcl\<close> answers only what the
  checks show.\<close>

definition Search_certify_contract :: \<open>('addr, 'gv, Search) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> Search \<Rightarrow>
    Formula \<Rightarrow> Clause rvec \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> Lit rvec \<Rightarrow>
    ('s, bool, 'abort) function_contract\<close> where
  \<open>Search_certify_contract r g s f L lo nres c learnt \<equiv>
     let pre = can_alloc_reference \<star> r \<mapsto>\<langle>\<top>\<rangle> g\<down>s \<star>
        \<langle>sok_in s \<and> db_small f L \<and> rvec_length learnt \<le> 2^62\<rangle> in
     let post = \<lambda>res. can_alloc_reference \<star> (\<Squnion>g' s'. r \<mapsto>\<langle>\<top>\<rangle> g'\<down>s' \<star>
        \<langle>sok s' \<and> (res \<longrightarrow>
           (\<forall>a. (\<forall>c \<in> set (db f L). clause_sat a c) \<longrightarrow> (\<exists>l \<in> set (rvec_elems learnt). lit_sat a l)))\<rangle>) in
     make_function_contract pre post\<close>

lemma Search_certify_spec:
  shows \<open>\<Gamma>; Search_certify r f L lo nres c learnt \<Turnstile>\<^sub>F Search_certify_contract r g s f L lo nres c learnt\<close>
  apply (crush_boot f: Search_certify_def contract: Search_certify_contract_def)
  apply (crush_base inline: BIG_def mem_replace_def
      specs add: all_false_spec mark_spec
        force_trail_spec[where X=\<open>\<lambda>a. \<forall>l \<in> set (rvec_elems learnt). \<not> lit_sat a l\<close>]
        force_fix_spec[where X=\<open>\<lambda>a. \<forall>l \<in> set (rvec_elems learnt). \<not> lit_sat a l\<close>]
        force_back_spec[where X=\<open>\<lambda>a. \<forall>l \<in> set (rvec_elems learnt). \<not> lit_sat a l\<close>]
        reason_ok_spec
      contracts add: all_false_contract_def mark_contract_def force_trail_contract_def
        force_fix_contract_def force_back_contract_def reason_ok_contract_def
      simp add: true_def false_def rvec_elems_focus_modify)
  apply (all \<open>(sok_tac; fail)?\<close>)
  apply (all \<open>(auto simp add: sok_in_def sok_def; fail)?\<close>)
  apply (all \<open>(use certify_sound in blast; fail)?\<close>)
  apply (all \<open>(rule forced_sound_mark; auto; fail)?\<close>)
  apply (all \<open>(simp add: not_le word_less_nat_alt; fail)?\<close>)
  done

definition on_conflict_contract :: \<open>('addr, 'gv, Search) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> Search \<Rightarrow>
    Formula \<Rightarrow> ('addr, 'gv, Clause rvec) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> Clause rvec \<Rightarrow> 64 word \<Rightarrow>
    ('s, 64 word, 'abort) function_contract\<close> where
  \<open>on_conflict_contract r g s f lref gl L c \<equiv>
     let pre = can_alloc_reference \<star> r \<mapsto>\<langle>\<top>\<rangle> g\<down>s \<star> lref \<mapsto>\<langle>\<top>\<rangle> gl\<down>L \<star>
        \<langle>sok_in s \<and> sat_repr_ok f \<and> length (cls f) < 4611686018427387904 \<and> learned_ok f L \<and>
         vok L24 L\<rangle> in
     let post = \<lambda>res. can_alloc_reference \<star> (\<Squnion>g' s'. r \<mapsto>\<langle>\<top>\<rangle> g'\<down>s' \<star> \<langle>sok s'\<rangle>) \<star>
        (\<Squnion>gl' L'. lref \<mapsto>\<langle>\<top>\<rangle> gl'\<down>L' \<star>
           \<langle>learned_ok f L' \<and> vok L24 L' \<and>
            (res = 1 \<longrightarrow> \<not> (\<exists>a. \<forall>c \<in> set (db f L'). clause_sat a c))\<rangle>) in
     make_function_contract pre post\<close>

lemma on_conflict_spec:
  shows \<open>\<Gamma>; on_conflict r f lref c \<Turnstile>\<^sub>F on_conflict_contract r g s f lref gl L c\<close>
  apply (crush_boot f: on_conflict_def contract: on_conflict_contract_def)
  apply (crush_base inline: ACT_def NONE_def BIG_def Clause_mk_def
      specs add: Search_certify_spec Search_analyze_spec Search_backtrack_spec Search_attach_spec
        Search_enqueue_spec Search_learnt_lbd_spec Search_level0_hint_spec
      contracts add: Search_certify_contract_def Search_analyze_contract_def Search_backtrack_contract_def
        Search_attach_contract_def Search_enqueue_contract_def Search_learnt_lbd_contract_def
        Search_level0_hint_contract_def
      simp add: true_def false_def rvec_elems_focus_modify rvec_elems_focus_modify_fun)
  apply (all \<open>sok_asm?\<close>)
  apply (all \<open>(rule sok_lbd_dead; (assumption | (simp add: not_le; fail)))?\<close>)
  apply (all \<open>(rule learned_push_ok; assumption)?\<close>)
  apply (all \<open>cdcl_bound?\<close>)
  apply (all \<open>(sok_tac; fail)?\<close>)
  done

definition cdcl_contract :: \<open>Formula \<Rightarrow> ('s, Answer option, 'abort) function_contract\<close> where
  \<open>cdcl_contract f \<equiv>
     let pre = can_alloc_reference \<star> \<langle>sat_repr_ok f\<rangle> in
     let post = \<lambda>r. can_alloc_reference \<star> \<langle>cdcl_post f r\<rangle> in
     make_function_contract pre post\<close>

lemma cdcl_spec:
  shows \<open>\<Gamma>; cdcl f \<Turnstile>\<^sub>F cdcl_contract f\<close>
  apply (crush_boot f: cdcl_def contract: cdcl_contract_def)
  apply (crush_base inline: ACT_def NONE_def BIG_def
      specs add: new_search_spec init_spec
      contracts add: new_search_contract_def init_contract_def
      simp add: true_def false_def rvec_elems_focus_modify rvec_elems_focus_modify_fun)
  apply (all \<open>search_bound?\<close>)
  apply (all \<open>sok_asm?\<close>)
  subgoal for _ s_ref l_ref _ _ _ confl_ref sr_ref ra_ref st_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>gs s' gl L gc c gsr sr gra ra gt t. s_ref \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star> l_ref \<mapsto>\<langle>\<top>\<rangle> gl\<down>L \<star>
               confl_ref \<mapsto>\<langle>\<top>\<rangle> gc\<down>c \<star>
               sr_ref \<mapsto>\<langle>\<top>\<rangle> gsr\<down>sr \<star> ra_ref \<mapsto>\<langle>\<top>\<rangle> gra\<down>ra \<star>
               st_ref \<mapsto>\<langle>\<top>\<rangle> gt\<down>t \<star> can_alloc_reference \<star>
               \<langle>sok_in s' \<and> learned_ok f L \<and> vok L24 L\<rangle>\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>gs s' gl L gc c gsr sr gra ra gt t. s_ref \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star> l_ref \<mapsto>\<langle>\<top>\<rangle> gl\<down>L \<star>
               confl_ref \<mapsto>\<langle>\<top>\<rangle> gc\<down>c \<star>
               sr_ref \<mapsto>\<langle>\<top>\<rangle> gsr\<down>sr \<star> ra_ref \<mapsto>\<langle>\<top>\<rangle> gra\<down>ra \<star>
               st_ref \<mapsto>\<langle>\<top>\<rangle> gt\<down>t \<star> can_alloc_reference \<star>
               \<langle>sok_in s' \<and> learned_ok f L \<and> vok L24 L \<and> t < 0xFFFFFFFFFFFFFFFF\<rangle>\<close> and
        \<tau>=\<open>\<lambda>r. can_alloc_reference \<star> \<langle>cdcl_post f r\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base inline: ACT_def NONE_def BIG_def Answer_Sat_mk_def Assignments_mk_def
        specs add: Search_propagate_spec on_conflict_spec Search_backtrack_spec Search_enqueue_spec
          Search_pick_spec model_spec satisfies_spec Search_reduce_spec Search_restart_due_spec
        contracts add: Search_propagate_contract_def on_conflict_contract_def Search_backtrack_contract_def
          Search_enqueue_contract_def Search_pick_contract_def model_contract_def satisfies_contract_def
          Search_reduce_contract_def Search_restart_due_contract_def
        simp add: true_def false_def rvec_elems_focus_modify rvec_elems_focus_modify_fun)
    apply (all \<open>sok_asm?\<close>)
    apply (all \<open>(rule sok_lim_push; (sok_asm | (simp add: not_le; fail)))?\<close>)
    apply (all \<open>(rule vok_new)?\<close>)
    apply (all \<open>cdcl_bound?\<close>)
    done
  apply (all \<open>cdcl_bound?\<close>)
  apply (all \<open>sok_asm?\<close>)
  apply (all \<open>(rule vok_new)?\<close>)
  done

end

end
