theory Sat_Heap
  imports Sat_Proof.Sat_Vectors
begin

text \<open>The contracts of the variable heap of the CDCL search of \<^verbatim>\<open>core/src/lib.rs\<close>, from which
  \<^verbatim>\<open>pick\<close> takes the decisions. The heap is search state like the rest of \<^verbatim>\<open>Search\<close>: its
  functions only need to return without a panic and keep \<open>sok\<close>. Every index is checked before
  use, so no property of the heap is needed.\<close>

context Sat_ctx
begin

section \<open>The heap\<close>

definition Search_before_contract :: \<open>Search \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> ('s, bool, 'abort) function_contract\<close> where
  \<open>Search_before_contract s a b \<equiv> make_function_contract can_alloc_reference (\<lambda>_. can_alloc_reference)\<close>

lemma Search_before_spec:
  shows \<open>\<Gamma>; Search_before s a b \<Turnstile>\<^sub>F Search_before_contract s a b\<close>
  apply (crush_boot f: Search_before_def contract: Search_before_contract_def)
  apply (crush_base simp add: true_def false_def)
  apply (all \<open>search_bound?\<close>)
  done

definition Search_sift_up_contract :: \<open>('addr, 'gv, Search) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> Search \<Rightarrow>
    64 word \<Rightarrow> ('s, unit, 'abort) function_contract\<close> where
  \<open>Search_sift_up_contract r g s i \<equiv>
     let pre = can_alloc_reference \<star> r \<mapsto>\<langle>\<top>\<rangle> g\<down>s \<star> \<langle>sok_in s\<rangle> in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' s'. r \<mapsto>\<langle>\<top>\<rangle> g'\<down>s' \<star> \<langle>sok s'\<rangle>) in
     make_function_contract pre post\<close>

lemma Search_sift_up_spec:
  shows \<open>\<Gamma>; Search_sift_up r i \<Turnstile>\<^sub>F Search_sift_up_contract r g s i\<close>
  apply (crush_boot f: Search_sift_up_def contract: Search_sift_up_contract_def)
  apply (crush_base inline: NONE_def specs add: Search_before_spec contracts add: Search_before_contract_def
      simp add: true_def false_def rvec_elems_focus_modify)
  apply (all \<open>search_bound?\<close>)
  apply (all \<open>(sok_tac; fail)?\<close>)
  subgoal for i_ref go_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>gs s' gi j gg go. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>j \<star>
               go_ref \<mapsto>\<langle>\<top>\<rangle> gg\<down>go \<star> can_alloc_reference \<star> \<langle>sok s'\<rangle>\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>gs s' gi j gg go. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>j \<star>
               go_ref \<mapsto>\<langle>\<top>\<rangle> gg\<down>go \<star> can_alloc_reference \<star>
               \<langle>sok s' \<and> 0 < j \<and> j < word64_of_nat (rvec_length (Search_heap s'))\<rangle>\<close> and
        \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base inline: NONE_def specs add: Search_before_spec contracts add: Search_before_contract_def
        simp add: true_def false_def rvec_elems_focus_modify)
    apply (all \<open>search_bound?\<close>)
    apply (all \<open>(sok_tac; fail)?\<close>)
    done
  done

definition Search_sift_down_contract :: \<open>('addr, 'gv, Search) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> Search \<Rightarrow>
    64 word \<Rightarrow> ('s, unit, 'abort) function_contract\<close> where
  \<open>Search_sift_down_contract r g s i \<equiv>
     let pre = can_alloc_reference \<star> r \<mapsto>\<langle>\<top>\<rangle> g\<down>s \<star> \<langle>sok_in s\<rangle> in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' s'. r \<mapsto>\<langle>\<top>\<rangle> g'\<down>s' \<star> \<langle>sok s'\<rangle>) in
     make_function_contract pre post\<close>

lemma Search_sift_down_spec:
  shows \<open>\<Gamma>; Search_sift_down r i \<Turnstile>\<^sub>F Search_sift_down_contract r g s i\<close>
  apply (crush_boot f: Search_sift_down_def contract: Search_sift_down_contract_def)
  apply (crush_base inline: NONE_def BIG_def specs add: Search_before_spec contracts add: Search_before_contract_def
      simp add: true_def false_def rvec_elems_focus_modify)
  apply (all \<open>search_bound?\<close>)
  apply (all \<open>(sok_tac; fail)?\<close>)
  subgoal for i_ref go_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>gs s' gi j gg go. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>j \<star>
               go_ref \<mapsto>\<langle>\<top>\<rangle> gg\<down>go \<star> can_alloc_reference \<star> \<langle>sok s'\<rangle>\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>gs s' gi j gg go. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>j \<star>
               go_ref \<mapsto>\<langle>\<top>\<rangle> gg\<down>go \<star> can_alloc_reference \<star>
               \<langle>sok s' \<and> j < 0x100000000000000 \<and> j < word64_of_nat (rvec_length (Search_heap s'))\<rangle>\<close> and
        \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base inline: NONE_def BIG_def specs add: Search_before_spec contracts add: Search_before_contract_def
        simp add: true_def false_def rvec_elems_focus_modify)
    apply (all \<open>search_bound?\<close>)
    apply (all \<open>(sok_tac; fail)?\<close>)
    done
  done

definition Search_heapify_contract :: \<open>('addr, 'gv, Search) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> Search \<Rightarrow>
    ('s, unit, 'abort) function_contract\<close> where
  \<open>Search_heapify_contract r g s \<equiv>
     let pre = can_alloc_reference \<star> r \<mapsto>\<langle>\<top>\<rangle> g\<down>s \<star> \<langle>sok_in s\<rangle> in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' s'. r \<mapsto>\<langle>\<top>\<rangle> g'\<down>s' \<star> \<langle>sok s'\<rangle>) in
     make_function_contract pre post\<close>

lemma Search_heapify_spec:
  shows \<open>\<Gamma>; Search_heapify r \<Turnstile>\<^sub>F Search_heapify_contract r g s\<close>
  apply (crush_boot f: Search_heapify_def contract: Search_heapify_contract_def)
  apply (crush_base specs add: Search_sift_down_spec contracts add: Search_sift_down_contract_def
      simp add: true_def false_def rvec_elems_focus_modify)
  apply (all \<open>search_bound?\<close>)
  apply (all \<open>(sok_tac; fail)?\<close>)
  subgoal for i_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>gs s' gi j. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>j \<star> can_alloc_reference \<star> \<langle>sok s'\<rangle>\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>gs s' gi j. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>j \<star> can_alloc_reference \<star>
               \<langle>sok s' \<and> 0 < j\<rangle>\<close> and
        \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base specs add: Search_sift_down_spec contracts add: Search_sift_down_contract_def
        simp add: true_def false_def rvec_elems_focus_modify)
    apply (all \<open>search_bound?\<close>)
    apply (all \<open>sok_asm?\<close>)
    apply (all \<open>(sok_tac; fail)?\<close>)
    done
  done

definition Search_insert_contract :: \<open>('addr, 'gv, Search) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> Search \<Rightarrow>
    64 word \<Rightarrow> ('s, unit, 'abort) function_contract\<close> where
  \<open>Search_insert_contract r g s v \<equiv>
     let pre = can_alloc_reference \<star> r \<mapsto>\<langle>\<top>\<rangle> g\<down>s \<star> \<langle>sok_in s\<rangle> in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' s'. r \<mapsto>\<langle>\<top>\<rangle> g'\<down>s' \<star> \<langle>sok s'\<rangle>) in
     make_function_contract pre post\<close>

lemma Search_insert_spec:
  shows \<open>\<Gamma>; Search_insert r v \<Turnstile>\<^sub>F Search_insert_contract r g s v\<close>
  apply (crush_boot f: Search_insert_def contract: Search_insert_contract_def)
  apply (crush_base inline: NONE_def specs add: Search_sift_up_spec contracts add: Search_sift_up_contract_def
      simp add: true_def false_def rvec_elems_focus_modify)
  apply (all \<open>search_bound?\<close>)
  apply (all \<open>(sok_tac; fail)?\<close>)
  done

definition Search_reinsert_contract :: \<open>('addr, 'gv, Search) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> Search \<Rightarrow>
    64 word \<Rightarrow> ('s, unit, 'abort) function_contract\<close> where
  \<open>Search_reinsert_contract r g s i \<equiv>
     let pre = can_alloc_reference \<star> r \<mapsto>\<langle>\<top>\<rangle> g\<down>s \<star> \<langle>sok_in s\<rangle> in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' s'. r \<mapsto>\<langle>\<top>\<rangle> g'\<down>s' \<star> \<langle>sok s'\<rangle>) in
     make_function_contract pre post\<close>

lemma Search_reinsert_spec:
  shows \<open>\<Gamma>; Search_reinsert r i \<Turnstile>\<^sub>F Search_reinsert_contract r g s i\<close>
  apply (crush_boot f: Search_reinsert_def contract: Search_reinsert_contract_def)
  apply (crush_base specs add: Search_insert_spec contracts add: Search_insert_contract_def
      simp add: true_def false_def rvec_elems_focus_modify)
  apply (all \<open>search_bound?\<close>)
  apply (all \<open>(sok_tac; fail)?\<close>)
  subgoal for j_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>gs s' gj j. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star> j_ref \<mapsto>\<langle>\<top>\<rangle> gj\<down>j \<star> can_alloc_reference \<star> \<langle>sok s'\<rangle>\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>gs s' gj j. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star> j_ref \<mapsto>\<langle>\<top>\<rangle> gj\<down>j \<star> can_alloc_reference \<star>
               \<langle>sok s' \<and> j < word64_of_nat (rvec_length (Search_trail s'))\<rangle>\<close> and
        \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base specs add: Search_insert_spec contracts add: Search_insert_contract_def
        simp add: true_def false_def rvec_elems_focus_modify)
    apply (all \<open>search_bound?\<close>)
    apply (all \<open>sok_asm?\<close>)
    apply (all \<open>(sok_tac; fail)?\<close>)
    done
  done

definition Search_heap_pop_contract :: \<open>('addr, 'gv, Search) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> Search \<Rightarrow>
    ('s, 64 word, 'abort) function_contract\<close> where
  \<open>Search_heap_pop_contract r g s \<equiv>
     let pre = can_alloc_reference \<star> r \<mapsto>\<langle>\<top>\<rangle> g\<down>s \<star> \<langle>sok_in s\<rangle> in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' s'. r \<mapsto>\<langle>\<top>\<rangle> g'\<down>s' \<star> \<langle>sok s'\<rangle>) in
     make_function_contract pre post\<close>

lemma Search_heap_pop_spec:
  shows \<open>\<Gamma>; Search_heap_pop r \<Turnstile>\<^sub>F Search_heap_pop_contract r g s\<close>
  apply (crush_boot f: Search_heap_pop_def contract: Search_heap_pop_contract_def)
  apply (crush_base inline: NONE_def specs add: Search_sift_down_spec contracts add: Search_sift_down_contract_def
      simp add: true_def false_def rvec_elems_focus_modify)
  apply (all \<open>search_bound?\<close>)
  apply (all \<open>(sok_tac; fail)?\<close>)
  done

definition Search_pick_scan_contract :: \<open>Search \<Rightarrow> ('s, 64 word, 'abort) function_contract\<close> where
  \<open>Search_pick_scan_contract s \<equiv> make_function_contract can_alloc_reference (\<lambda>_. can_alloc_reference)\<close>

lemma Search_pick_scan_spec:
  shows \<open>\<Gamma>; Search_pick_scan s \<Turnstile>\<^sub>F Search_pick_scan_contract s\<close>
  apply (crush_boot f: Search_pick_scan_def contract: Search_pick_scan_contract_def)
  apply (crush_base inline: NONE_def simp add: true_def false_def rvec_elems_focus_modify)
  apply (all \<open>search_bound?\<close>)
  apply (all \<open>(sok_tac; fail)?\<close>)
  subgoal for best_ref best_act_ref v_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>gb b ga a gv v. best_ref \<mapsto>\<langle>\<top>\<rangle> gb\<down>b \<star> best_act_ref \<mapsto>\<langle>\<top>\<rangle> ga\<down>a \<star>
               v_ref \<mapsto>\<langle>\<top>\<rangle> gv\<down>v \<star> can_alloc_reference\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>gb b ga a gv v. best_ref \<mapsto>\<langle>\<top>\<rangle> gb\<down>b \<star> best_act_ref \<mapsto>\<langle>\<top>\<rangle> ga\<down>a \<star>
               v_ref \<mapsto>\<langle>\<top>\<rangle> gv\<down>v \<star> can_alloc_reference \<star> \<langle>v < word64_of_nat (rvec_length (Search_set s))\<rangle>\<close> and
        \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base inline: NONE_def simp add: true_def false_def rvec_elems_focus_modify)
    apply (all \<open>search_bound?\<close>)
    apply (all \<open>(sok_tac; fail)?\<close>)
    done
  done

definition Search_pick_heap_contract :: \<open>('addr, 'gv, Search) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> Search \<Rightarrow>
    ('s, 64 word, 'abort) function_contract\<close> where
  \<open>Search_pick_heap_contract r g s \<equiv>
     let pre = can_alloc_reference \<star> r \<mapsto>\<langle>\<top>\<rangle> g\<down>s \<star> \<langle>sok_in s\<rangle> in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' s'. r \<mapsto>\<langle>\<top>\<rangle> g'\<down>s' \<star> \<langle>sok s'\<rangle>) in
     make_function_contract pre post\<close>

lemma Search_pick_heap_spec:
  shows \<open>\<Gamma>; Search_pick_heap r \<Turnstile>\<^sub>F Search_pick_heap_contract r g s\<close>
  apply (crush_boot f: Search_pick_heap_def contract: Search_pick_heap_contract_def)
  apply (crush_base inline: NONE_def specs add: Search_heap_pop_spec contracts add: Search_heap_pop_contract_def
      simp add: true_def false_def rvec_elems_focus_modify)
  apply (all \<open>search_bound?\<close>)
  apply (all \<open>(sok_tac; fail)?\<close>)
  subgoal for best_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>gs s' gb b. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star> best_ref \<mapsto>\<langle>\<top>\<rangle> gb\<down>b \<star> can_alloc_reference \<star> \<langle>sok s'\<rangle>\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>gs s' gb b. r \<mapsto>\<langle>\<top>\<rangle> gs\<down>s' \<star> best_ref \<mapsto>\<langle>\<top>\<rangle> gb\<down>b \<star> can_alloc_reference \<star> \<langle>sok s'\<rangle>\<close> and
        \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base inline: NONE_def specs add: Search_heap_pop_spec contracts add: Search_heap_pop_contract_def
        simp add: true_def false_def rvec_elems_focus_modify)
    apply (all \<open>search_bound?\<close>)
    apply (all \<open>sok_asm?\<close>)
    apply (all \<open>(sok_tac; fail)?\<close>)
    done
  done

definition Search_pick_contract :: \<open>('addr, 'gv, Search) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> Search \<Rightarrow>
    ('s, 64 word, 'abort) function_contract\<close> where
  \<open>Search_pick_contract r g s \<equiv>
     let pre = can_alloc_reference \<star> r \<mapsto>\<langle>\<top>\<rangle> g\<down>s \<star> \<langle>sok_in s\<rangle> in
     let post = \<lambda>_. can_alloc_reference \<star> (\<Squnion>g' s'. r \<mapsto>\<langle>\<top>\<rangle> g'\<down>s' \<star> \<langle>sok s'\<rangle>) in
     make_function_contract pre post\<close>

lemma Search_pick_spec:
  shows \<open>\<Gamma>; Search_pick r \<Turnstile>\<^sub>F Search_pick_contract r g s\<close>
  apply (crush_boot f: Search_pick_def contract: Search_pick_contract_def)
  apply (crush_base specs add: Search_pick_heap_spec Search_pick_scan_spec
      contracts add: Search_pick_heap_contract_def Search_pick_scan_contract_def
      simp add: true_def false_def rvec_elems_focus_modify)
  apply (all \<open>sok_asm?\<close>)
  apply (all \<open>(sok_tac; fail)?\<close>)
  done

definition iota_contract :: \<open>64 word \<Rightarrow> ('s, (64 word) rvec, 'abort) function_contract\<close> where
  \<open>iota_contract n \<equiv>
     make_function_contract (can_alloc_reference \<star> \<langle>n < 0x100000000000000\<rangle>) (\<lambda>_. can_alloc_reference)\<close>

lemma iota_spec:
  shows \<open>\<Gamma>; iota n \<Turnstile>\<^sub>F iota_contract n\<close>
  apply (crush_boot f: iota_def contract: iota_contract_def)
  apply (crush_base simp add: true_def false_def rvec_elems_focus_modify)
  apply (all \<open>search_bound?\<close>)
  subgoal for _ xs_ref i_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>k. \<Squnion>gx xs gi i. xs_ref \<mapsto>\<langle>\<top>\<rangle> gx\<down>xs \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference\<close> and
        INV'=\<open>\<lambda>k. \<Squnion>gx xs gi i. xs_ref \<mapsto>\<langle>\<top>\<rangle> gx\<down>xs \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
               \<langle>i < word64_of_nat (rvec_length xs)\<rangle>\<close> and
        \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base simp add: true_def false_def rvec_elems_focus_modify)
    apply (all \<open>search_bound?\<close>)
    done
  apply (simp add: word_less_nat_alt rvec_cap_max_def isize_max_def)
  done

end

end
