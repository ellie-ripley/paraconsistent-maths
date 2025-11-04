(* Title: subDMQ.thy
   Author: Ellie Ripley, https://negation.rocks *)

theory subDMQ
  imports Pure
begin

subsection \<open>Abstract syntax\<close>

typedecl i
typedecl o

judgment Is_theorem :: "o ⇒ prop"  ("_" 5)

subsection \<open>Object Language\<close>

axiomatization
      entl :: "o ⇒ o ⇒ o"   (infixr "→" 25)
  and impl :: "o ⇒ o ⇒ o"   (infixr "⇛" 10)
  and conj :: "o ⇒ o ⇒ o"   (infixr "⊗" 45)
  and disj :: "o ⇒ o ⇒ o"   (infixr "∨" 40)
  and neg  :: "o ⇒ o"   ("¬ _" [60] 60)
  and all  :: "(i ⇒ o) ⇒ o" ("∀ _" [60] 60)
  and some :: "(i ⇒ o) ⇒ o" ("∃ _" [60] 60)
  and false :: "o"           ("⊥")
  and equals :: "i ⇒ i ⇒ o" (infix "=" 70)

definition bientl :: "o ⇒ o ⇒ o" (infix "↔" 20)
  where "A ↔ B \<equiv> (A → B) ⊗ (B → A)"

definition biimpl :: "o ⇒ o ⇒ o" (infix "⇌" 20)
  where "A ⇌ B \<equiv> (A ⇛ B) ⊗ (B ⇛ A)"

abbreviation noteq :: "i ⇒ i ⇒ o" (infix "≠" 70)
  where "x ≠ y \<equiv> ¬(x = y)"

axiomatization
  (* "Formalizing inconsistent mathematics" section 3.1.1 *)
  where implB:           "(B ⇛ C) ⇛ (A ⇛ B) ⇛ A ⇛ C"
    and implC:           "(A ⇛ B ⇛ C) ⇛ B ⇛ A ⇛ C"
    and implK:           "A ⇛ B ⇛ A"
    and impl_conj_in:    "A ⇛ B ⇛ A ⊗ B"
    and conj_import:     "(A ⇛ B ⇛ C) ⇛ A ⊗ B ⇛ C"
    and impl_mp [dest]:  "A ⇛ B ⟹ A ⟹ B"
  (* paper section 3.1.2 *)
    and entlI:           "A → A"
    and entl_impl:       "(A → B) ⇛ A ⇛ B"
    and entl_cel:        "A ⊗ B → A"
    and entl_conj_comm:  "A ⊗ B → B ⊗ A"
    and entl_conj_ass:   "A ⊗ B ⊗ C → (A ⊗ B) ⊗ C"
    and entl_cs:         "(A → B) ⊗ (B → C) → (A → C)"
    and efq_entl:        "⊥ → A"
  (* paper section 3.1.3 *)
    and entl_contra:     "(A → B) → ¬B → ¬A"
    and nimpl_nentl:     "¬(A ⇛ B) ⇛ ¬(A → B)"
    and dn_bi:           "A ↔ ¬¬A"
    and impl_cex:        "A ⊗ ¬B ⇛ ¬(A ⇛ B)"
  (* paper section 3.1.4 *)
    and entl_disj_inl:   "A → A ∨ B"
    and impl_disj_left:  "(A ⇛ C) ⇛ (B ⇛ C) ⇛ A ∨ B ⇛ C"
    and dm_ndcn_bi:      "¬(A ∨ B) ↔ ¬A ⊗ ¬B"
    and dm_ncdn_bi:      "¬(A ⊗ B) ↔ ¬A ∨ ¬B"
    and lem:             "A ∨ ¬A"
  (* paper section 3.1.5 *)
    and entl_ui:         "∀ P → P t"
    and bisub_open_impl: "∀(λx. P x ↔ Q x) ⇛ (R P) ↔ (R Q)"
    and all_conj_dist:   "∀(λx. P x ⊗ Q x) ⇛ ∀ P ⊗ ∀ Q"
    and all_disj:        "∀(λx. A ∨ P x) → A ∨ ∀ P"
    and all_ante:        "∀(λx. P x ⇛ A) ⇛ ∃ P ⇛ A"
    and all_cons:        "∀(λx. A ⇛ P x) ⇛ A ⇛ ∀ P"
    and dm_nsan_bi:       "¬∃ P ↔ ∀(λx. ¬P x)"
    and dm_nasn_bi:       "¬∀ P ↔ ∃(λx. ¬P x)"
    and ug [intro]:      "(\<And> x. P x) ⟹ ∀ P"
  (* paper section 3.1.6 *)
    and refl:            "x = x"
    and eq_sym_entl:     "x = y → y = x"
    and equals_sub_impl: "x = y ⇛ (P x → P y)"

lemma eq_sym_bientl: "x = y ↔ y = x"
  proof -
    from impl_conj_in and eq_sym_entl have
      "(y = x → x = y) ⇛ (x = y ↔ y = x)"
      unfolding bientl_def ..
    from this and eq_sym_entl show ?thesis ..
  qed

lemma impl_trans_rule [dest]: "A ⇛ B ⟹ B ⇛ C ⟹ A ⇛ C"
  proof -
    assume ab:"A ⇛ B" and bc:"B ⇛ C"
    from implB and bc have "(A ⇛ B) ⇛ A ⇛ C" ..
    from this and ab show "A ⇛ C" ..
  qed

lemma implI: "A ⇛ A"
  proof -
    from implC and implK have "(C ⇛ D ⇛ C) ⇛ A ⇛ A" ..
    from this and implK show "A ⇛ A" ..
  qed

lemma implCI: "A ⇛ (A ⇛ B) ⇛ B"
  proof -
    from implC and implI show ?thesis ..
  qed

lemma impl_ppmp: "(A ⇛ B) ⊗ A ⇛ B"
  proof -
    from conj_import and implI show ?thesis ..
  qed

lemma entl_mp [dest]: "A → B ⟹ A ⟹ B"
  proof -
    assume ab:"A → B" and a:"A"
      from entl_impl and ab have "A ⇛ B" ..
      from this and a show "B" ..
  qed

lemma bisub_impl: "A ↔ B ⇛ (a A) ↔ (a B)"
  proof -
    from implI have "∀(λx. (A ↔ B) ⇛ (A ↔ B))" ..
    from all_cons and this have "(A ↔ B) ⇛ ∀(λx. A ↔ B)" ..
    from this and bisub_open_impl show ?thesis ..
  qed

lemma bisub: "A ↔ B ⟹ (a A) ↔ (a B)"
  proof -
    assume ab:"A ↔ B"
      from bisub_impl and this show ?thesis ..
  qed

lemma bientl_mp_ltr [dest]: "A ↔ B ⟹ A ⟹ B"
  unfolding bientl_def
  proof -
    assume abba:"(A → B) ⊗ (B → A)" and a:"A"
    from entl_cel and abba have "A → B" ..
    from this and a show "B" ..
  qed

lemma bisub_rule: "A ↔ B ⟹ a A ⟹ a B"
  proof -
    assume ab:"A ↔ B" and contxt:"a A"
    from ab have "a A ↔ a B"
      by(rule bisub)
    from this and contxt show "a B" ..
  qed

lemma bisub_open: "(\<And> x :: i. (P x ↔ Q x)) ⟹ (R P) ↔ (R Q)"
  proof -
    assume pq:"\<And> x :: i. (P x ↔ Q x)"
      from this have "∀(λx. P x ↔ Q x)" ..
      from bisub_open_impl and this show ?thesis ..
  qed

lemma bientlI: "A ↔ A"
  proof -
    have aa:"A → A" by(rule entlI)
    from impl_conj_in and this have "(A → A) ⇛ (A ↔ A)"
      unfolding bientl_def ..
    from this and aa show ?thesis ..
  qed

lemma bientl_sym_impl: "(A ↔ B) ⇛ (B ↔ A)"
  unfolding bientl_def
  proof -
    from entl_impl and entl_conj_comm show
      "(A → B) ⊗ (B → A) ⇛ (B → A) ⊗ (A → B)" ..
  qed

lemma bientl_sym_rule: "A ↔ B ⟹ B ↔ A"
  proof -
    assume ab:"A ↔ B"
    from bientl_sym_impl and this show ?thesis ..
  qed

lemma bisub_rule': "A ↔ B ⟹ a B ⟹ a A"
  proof -
    assume ab:"A ↔ B" and contxt:"a B"
    from ab have "B ↔ A" by(rule bientl_sym_rule)
    from this and contxt show "a A" by(rule bisub_rule)
  qed

lemma cel_rule [elim]: "A ⊗ B ⟹ A"
  proof -
    assume "A ⊗ B"
    from entl_cel and this show "A" ..
  qed

lemma conj_intro [intro]: "A ⟹ B ⟹ A ⊗ B"
  proof -
    assume a:"A" and b:"B"
    from impl_conj_in and a have "B ⇛ A ⊗ B" ..
    from this and b show "A ⊗ B" ..
  qed

lemma entl_trans_rule [dest]: "A → B ⟹ B → C ⟹ A → C"
  proof -
    assume ab:"A → B" and bc:"B → C"
    then have "(A → B) ⊗ (B → C)" ..
    from entl_cs and this show "A → C" ..
  qed

 lemma entl_cer: "A ⊗ B → B"
   proof -
     from entl_conj_comm and entl_cel show ?thesis ..
   qed

lemma cer_rule [elim]: "A ⊗ B ⟹ B"
  proof -
    assume "A ⊗ B"
    from entl_cer and this show "B" ..
  qed

lemma bientl_mp_rtl [dest]: "A ↔ B ⟹ B ⟹ A"
  unfolding bientl_def
  proof -
    assume abba:"(A → B) ⊗ (B → A)" and b:"B"
    from entl_cer and abba have "B → A" ..
    from this and b show "A" ..
  qed

lemma biimpl_mp_ltr [dest]: "A ⇌ B ⟹ A ⟹ B"
  unfolding biimpl_def
  proof -
    assume abba:"(A ⇛ B) ⊗ (B ⇛ A)" and a:"A"
    from entl_cel and abba have "A ⇛ B" ..
    from this and a show "B" ..
  qed

lemma biimpl_mp_rtl [dest]: "A ⇌ B ⟹ B ⟹ A"
  unfolding biimpl_def
  proof -
    assume abba:"(A ⇛ B) ⊗ (B ⇛ A)" and b:"B"
    from entl_cer and abba have "B ⇛ A" ..
    from this and b show "A" ..
  qed

lemma bisub_open_rule: "(\<And> x :: i. (P x ↔ Q x)) ⟹ (R P) ⟹ (R Q)"
  proof -
    assume pq:"\<And> x :: i. (P x ↔ Q x)" and rp:"R P"
    from pq have "(R P) ↔ (R Q)"
      by(rule bisub_open)
    from this and rp show ?thesis ..
  qed

lemma bisub_open_rule': "(\<And> x :: i. (P x ↔ Q x)) ⟹ (R Q) ⟹ (R P)"
  proof -
    assume pq:"\<And> x :: i. (P x ↔ Q x)" and rq:"R Q"
    from pq have "(R P) ↔ (R Q)"
      by(rule bisub_open)
    from this and rq show ?thesis ..
  qed

lemma equals_sub: "x = y ⟹ P x → P y"
  proof -
    assume xy:"x = y"
      from equals_sub_impl and this show ?thesis ..
  qed

lemma eqsub_rule: "x = y ⟹ P x ⟹ P y"
proof -
  assume xy:"x = y" and px:"P x"
  from equals_sub_impl and xy have "P x \<rightarrow> P y" ..
  from this and px show ?thesis ..
qed

lemma eqsub_rule': "y = x ⟹ P x ⟹ P y"
proof -
  assume yx:"y = x" and px:"P x"
  from eq_sym_bientl and yx have "x = y" ..
  from this and px show ?thesis by (rule eqsub_rule)
qed

lemma impl_equals_left: "P x ⇛ x = y ⇛ P y"
  proof -
    from equals_sub_impl and entl_impl have
      "x = y ⇛ P x ⇛ P y" ..
    from implC and this show ?thesis ..
  qed

lemma equals_left_rule: "P x ⟹ x = y ⇛ P y"
  proof -
    assume px:"P x"
    from impl_equals_left and px show ?thesis ..
  qed

lemma equals_left_rule': "P x ⟹ y = x ⇛ P y"
  proof -
    assume px:"P x"
    from px have "x = y ⇛ P y" by (rule equals_left_rule)
    then show ?thesis by (rule bisub_rule[OF eq_sym_bientl])
  qed

lemma eqsub_context: "x = y ⇛ t x = t y"
proof -
  from equals_sub_impl and entl_impl have "x = y ⇛ t x = t x ⇛ t x = t y" ..
  from implC and this have "t x = t x ⇛ x = y ⇛ t x = t y" ..
  from this and refl show ?thesis ..
qed

lemma eqsub_rule_dt: "A ⇛ x = y ⟹ P x ⟹ A ⇛ P y"
proof -
  assume axy:"A ⇛ x = y" and px:"P x"
  from axy and equals_sub_impl have "A ⇛ (P x → P y)"..
  from this and entl_impl have "A ⇛ P x ⇛ P y" ..
  from implC and this have "P x ⇛ A ⇛ P y" ..
  from this and px show ?thesis..
qed

lemma eqsub_rule'_dt: "A ⇛ x = y ⟹ P y ⟹ A ⇛ P x"
proof -
  assume axy:"A ⇛ x = y" and py:"P y"
  from eq_sym_bientl and axy have "A ⇛ y = x" by (rule bisub_rule)
  from this and py show ?thesis by (rule eqsub_rule_dt)
qed

lemma eqsub_context_dt: "(A ⇛ x = y) ⇛ A ⇛ t x = t y"
proof -
  from implB and eqsub_context show ?thesis..
qed

lemma implB': "(A ⇛ B) ⇛ (B ⇛ C) ⇛ A ⇛ C"
  proof -
    from implC and implB show "(A ⇛ B) ⇛ (B ⇛ C) ⇛ A ⇛ C" ..
  qed

lemma impl_mp_2 [dest]: "A ⇛ B ⇛ C ⟹ A ⟹ B ⟹ C"
  proof -
    assume abc:"A ⇛ B ⇛ C" and a:"A" and b:"B"
    from abc and a have "B ⇛ C" ..
    from this and b show "C" ..
  qed

lemma entl_mp_under_impl: "A ⇛ (B → C) ⟹ B ⟹ A ⇛ C"
  proof -
    assume abc: "A ⇛ (B → C)" and b:"B"
    from abc and entl_impl have "A ⇛ B ⇛ C" ..
    from implC and this have "B ⇛ A ⇛ C" ..
    from this and b show ?thesis ..
  qed

lemma impl_cel: "A ⊗ B ⇛ A"
  proof -
    from entl_impl and entl_cel show "A ⊗ B ⇛ A" ..
  qed

lemma impl_cer: "A ⊗ B ⇛ B"
  proof -
    from entl_impl and entl_cer show "A ⊗ B ⇛ B" ..
  qed

lemma impl_disj_inl: "A ⇛ A ∨ B"
  proof -
    from entl_impl and entl_disj_inl show ?thesis ..
  qed

lemma disj_left_rule: "A ⇛ C ⟹ B ⇛ C ⟹ A ∨ B ⇛ C"
  proof -
    assume ac:"A ⇛ C" and bc:"B ⇛ C"
    from impl_disj_left and ac have
      "(B ⇛ C) ⇛ A ∨ B ⇛ C" ..
    from this and bc show ?thesis ..
  qed

lemma dne: "¬¬A → A"
  proof -
    from entl_cer and dn_bi show "¬¬A → A"
      unfolding bientl_def
      by(rule entl_mp)
  qed

lemma impl_dne: "¬¬A ⇛ A"
  proof -
    from entl_impl and dne show "¬¬A ⇛ A" ..
  qed

lemma dni: "A → ¬¬A"
  proof -
    from entl_cel and dn_bi show "A → ¬¬A"
      unfolding bientl_def
      by(rule entl_mp)
  qed

lemma impl_dni: "A ⇛ ¬¬A"
  proof -
    from entl_impl and dni show "A ⇛ ¬¬A" ..
  qed

lemma bientl_trans_rule: "A ↔ B ⟹ B ↔ C ⟹ A ↔ C"
  unfolding bientl_def
  proof
    assume abba:"(A → B) ⊗ (B → A)" and bccb:"(B → C) ⊗ (C → B)"
    from impl_cel and abba have ab:"A → B" ..
    from impl_cer and abba have ba:"B → A" ..
    from impl_cel and bccb have bc:"B → C" ..
    from impl_cer and bccb have cb:"C → B" ..
    from ab and bc show "A → C" ..
    from cb and ba show "C → A" ..
  qed

 lemma dm_cnd_bi : "A ⊗ B ↔ ¬(¬A ∨ ¬B)"
   proof -
     from dn_bi and dm_ndcn_bi have "¬(¬A ∨ ¬B) ↔ ¬¬A ⊗ B"
       by(rule bisub_rule')
     from dn_bi and this have "¬(¬A ∨ ¬B) ↔ A ⊗ B"
       by(rule bisub_rule')
     from this show ?thesis
       by(rule bientl_sym_rule)
   qed

lemma dm_cnd: "A ⊗ B → ¬(¬A ∨ ¬B)"
  proof -
    from entl_cel and dm_cnd_bi show "A ⊗ B → ¬(¬A ∨ ¬B)"
      unfolding bientl_def
      by(rule entl_mp)
  qed

lemma entl_ncil: "¬A → ¬(A ⊗ B)"
  proof -
    from entl_contra and entl_cel show ?thesis ..
  qed

lemma entl_ncir: "¬B → ¬(A ⊗ B)"
  proof -
    from entl_contra and entl_cer show ?thesis ..
  qed

 lemma dm_sna_bi: "∃ P ↔ ¬∀(λx. ¬P x)"
   proof -
     from dm_nsan_bi and bientlI have "¬¬∃ P ↔ ¬∀(λx. ¬P x)"
       by(rule bisub_rule)
     from dn_bi and this show ?thesis
       by(rule bisub_rule')
   qed

 lemma dm_ans_bi: "∀ P ↔ ¬∃(λx. ¬P x)"
   proof -
     from dm_nasn_bi and bientlI have "¬¬∀ P ↔ ¬∃(λx. ¬P x)"
       by(rule bisub_rule)
     from dn_bi and this show ?thesis
       by(rule bisub_rule')
   qed

lemma dm_nas: "¬∀(λx. ¬P x) → ∃ P"
  proof -
    from entl_cer and dm_sna_bi show "¬∀(λx. ¬P x) → ∃ P"
      unfolding bientl_def ..
  qed

lemma dm_sna: "∃ P → ¬∀(λz. ¬P(z))"
  proof -
    from entl_cel and dm_sna_bi show "∃ P → ¬∀(λz. ¬P(z))"
      unfolding bientl_def ..
  qed

lemma dm_ans: "∀ P → ¬∃(λx. ¬P x)"
  proof -
    from entl_cel and dm_ans_bi show "∀ P → ¬∃(λx. ¬P x)"
      unfolding bientl_def ..
  qed

lemma dm_nsa: "¬∃(λx. ¬P x) → ∀ P"
  proof -
    from entl_cer and dm_ans_bi show "¬∃(λx. ¬P x) → ∀ P"
      unfolding bientl_def ..
  qed

lemma impl_ui: "∀ P ⇛ P(t)"
  proof -
    from entl_impl and entl_ui show ?thesis ..
  qed

lemma entl_eg: "P(t) → ∃(λx. P x)"
  proof -
    from entl_contra and entl_ui have
      "¬¬P(t) → ¬∀(λx. ¬P x)" ..
    from dni and this have
      "P(t) → ¬∀(λx. ¬P x)" ..
    from this and dm_nas show
      "P(t) → ∃(λx. P x)" ..
  qed

lemma impl_eg: "P(t) ⇛ ∃(λx. P x)"
  proof -
    from entl_impl and entl_eg show ?thesis ..
  qed

lemma eg [intro]: "P(t) ⟹ ∃(λx. P x)"
  proof -
    assume "P(t)"
    from entl_eg and this show "∃(λx. P x)" ..
  qed

lemma impl_some_monotone_rule: "(\<And> x. (P x ⇛ Q x)) ⟹ ∃ P ⇛ ∃ Q"
  proof -
    assume op:"\<And> x. (P x ⇛ Q x)"
    {
    fix y
      from entl_impl and entl_eg have
        "Q y ⇛ ∃ Q" ..
      from op and this have
        "P y ⇛ ∃ Q" ..
    }
    have "\<And> y. (P y ⇛ ∃ Q)" by fact
    from this have
      "∀(λy. P y ⇛ ∃ Q)" ..
    from all_ante and this show "∃ P ⇛ ∃ Q" ..
  qed

lemma impl_all_monotone_rule: "(\<And> x. (P x ⇛ Q x)) ⟹ ∀ P ⇛ ∀ Q"
  proof -
    assume op: "\<And> x. (P x ⇛ Q x)"
    {
      fix y
      have "∀ P ⇛ P y" by(rule impl_ui)
      from this and op have
        "∀ P ⇛ Q y" ..
    }
    have "\<And> y. (∀ P ⇛ Q y)" by fact
    from this have
      "∀(λy. (∀ P ⇛ Q y))" ..
    from all_cons and this show ?thesis ..
  qed

lemma equals_sub_rule: "x = y ⟹ P x ⟹ P y"
  proof -
    assume xy:"x = y" and px:"P x"
    from xy have "P x → P y"
      by(rule equals_sub)
    from this and px show "P y" ..
  qed

lemma conj_bicomm: "A ⊗ B ↔ B ⊗ A"
  unfolding bientl_def
  proof
    show "A ⊗ B → B ⊗ A" by(rule entl_conj_comm)
    show "B ⊗ A → A ⊗ B" by(rule entl_conj_comm)
  qed

 lemma dm_dnc_bi: "A ∨ B ↔ ¬(¬A ⊗ ¬B)"
   proof -
     from dm_ndcn_bi and bientlI have "¬¬(A ∨ B) ↔ ¬(¬A ⊗ ¬B)"
       by(rule bisub_rule)
     from dn_bi and this show ?thesis
       by(rule bisub_rule')
   qed

lemma disj_bicomm: "A ∨ B ↔ B ∨ A"
  proof -
    from conj_bicomm and dm_dnc_bi have step1:"A ∨ B ↔ ¬(¬B ⊗ ¬A)"
      by(rule bisub_rule)
    from dm_dnc_bi and this show "A ∨ B ↔ B ∨ A"
      by(rule bisub_rule')
  qed

 lemma entl_disj_inr: "B → A ∨ B"
   proof -
     from disj_bicomm and entl_disj_inl show ?thesis
       by(rule bisub_rule)
   qed

lemma impl_disj_inr: "B ⇛ A ∨ B"
  proof -
    from entl_impl and entl_disj_inr show ?thesis ..
  qed

lemma cer_under_disjr: "A ∨ (B ⊗ C) ⇛ A ∨ C"
  proof -
    from impl_disj_left and impl_disj_inl have
      step1:"(B ⊗ C ⇛ A ∨ C) ⇛ A ∨ (B ⊗ C) ⇛ A ∨ C" ..
    from impl_cer and impl_disj_inr have
      "B ⊗ C ⇛ A ∨ C" ..
    from step1 and this show ?thesis ..
  qed

lemma impl_na_conj_r: "¬∀ P ⇛ ¬∀(λx. P x ⊗ Q x)"
  proof -
    have "\<And> z. (¬P(z) ⇛ ¬(P(z) ⊗ Q(z)))"
      proof -
        fix z
          from entl_contra and entl_cel have
            "¬P(z) → ¬(P(z) ⊗ Q(z))" ..
          from entl_impl and this show
            "¬P(z) ⇛ ¬(P(z) ⊗ Q(z))" ..
      qed
    from this have
      step1:"∃(λz. ¬P(z)) ⇛ ∃(λz. ¬(P(z) ⊗ Q(z)))"
      by(rule impl_some_monotone_rule)

    from entl_impl and dm_sna have
      "∃(λz. ¬(P(z) ⊗ Q(z))) ⇛ ¬∀(λz. ¬¬(P(z) ⊗ Q(z)))" ..
    from step1 and this have
      step2:"∃(λz. ¬P(z)) ⇛ ¬∀(λz. ¬¬(P(z) ⊗ Q(z)))" ..

    from dm_ans_bi and step2 have
      "∃(λz. ¬P(z)) ⇛ ¬¬∃(λz. ¬¬¬(P(z) ⊗ Q(z)))"
      by(rule bisub_rule)
    from this and impl_dne have
      step3:"∃(λz. ¬P(z)) ⇛ ∃(λz. ¬¬¬(P(z) ⊗ Q(z)))" ..

    have "\<And> z. ¬¬¬(P(z) ⊗ Q(z)) ⇛ ¬(P(z) ⊗ Q(z))"
      proof -
        fix z
          show "¬¬¬(P(z) ⊗ Q(z)) ⇛ ¬(P(z) ⊗ Q(z))"
            by(rule impl_dne)
      qed
    from this have
      "∃(λz. ¬¬¬(P(z) ⊗ Q(z))) ⇛ ∃(λz. ¬(P(z) ⊗ Q(z)))"
      by(rule impl_some_monotone_rule)

    from step3 and this have
      step4:"∃(λz. ¬P(z)) ⇛ ∃(λz. ¬(P(z) ⊗ Q(z)))" ..
    from entl_contra and dm_ans have
      "¬¬∃(λz. ¬(P(z) ⊗ Q(z))) → ¬∀(λx. P x ⊗ Q x)" ..
    from entl_impl and this have
      "¬¬∃(λz. ¬(P(z) ⊗ Q(z))) ⇛ ¬∀(λx. P x ⊗ Q x)" ..
    from impl_dni and this have
      "∃(λz. ¬(P(z) ⊗ Q(z))) ⇛ ¬∀(λx. P x ⊗ Q x)" ..
    from step4 and this have
      step5:"∃(λz. ¬P(z)) ⇛ ¬∀(λx. P x ⊗ Q x)" ..

    from entl_contra and dm_nsa have
      "¬∀ P → ¬¬∃(λz. ¬P(z))" ..
    from entl_impl and this have
      "¬∀ P ⇛ ¬¬∃(λz. ¬P(z))" ..
    from this and impl_dne have
      "¬∀ P ⇛ ∃(λz. ¬P(z))" ..
    from this and step5 show
      "¬∀ P ⇛ ¬∀(λx. P x ⊗ Q x)" ..
  qed

lemma bientl_comm_entl: "(A ↔ B) → (B ↔ A)"
  proof -
    from conj_bicomm show ?thesis
      unfolding bientl_def ..
  qed

lemma bientl_comm_bientl: "(A ↔ B) ↔ (B ↔ A)"
  proof -
    from bientl_comm_entl and bientl_comm_entl show ?thesis
      unfolding bientl_def ..
  qed

lemma entl_conj_ass': "(A ⊗ B) ⊗ C → A ⊗ (B ⊗ C)"
  proof -
    from entl_conj_comm and entl_conj_ass have
      "(A ⊗ B) ⊗ C → (C ⊗ A) ⊗ B" ..
    from this and entl_conj_comm have
      "(A ⊗ B) ⊗ C → B ⊗ (C ⊗ A)" ..
    from this and entl_conj_ass have
      "(A ⊗ B) ⊗ C → (B ⊗ C) ⊗ A" ..
    from this and entl_conj_comm show
      "(A ⊗ B) ⊗ C → A ⊗ (B ⊗ C)" ..
  qed

lemma conj_biass: "A ⊗ (B ⊗ C) ↔ (A ⊗ B) ⊗ C"
  unfolding bientl_def
  proof
    show "A ⊗ (B ⊗ C) → (A ⊗ B) ⊗ C" by(rule entl_conj_ass)
    show "(A ⊗ B) ⊗ C → A ⊗ (B ⊗ C)" by(rule entl_conj_ass')
  qed

lemma conj_biass': "(A ⊗ B) ⊗ C ↔ A ⊗ (B ⊗ C)"
  proof -
    from conj_biass show "(A ⊗ B) ⊗ C ↔ A ⊗ (B ⊗ C)"
      by(rule bientl_sym_rule)
  qed

lemma disj_biass: "A ∨ (B ∨ C) ↔ (A ∨ B) ∨ C"
  proof -
    from conj_biass have
      nca:"¬(¬A ⊗ (¬B ⊗ ¬ C)) ↔ ¬((¬A ⊗ ¬B) ⊗ ¬C)"
      by(rule bisub)

    from dm_dnc_bi have
      "¬(B ∨ C) ↔ ¬¬(¬B ⊗ ¬C)"
      by(rule bisub)
    from dn_bi and this have
      "¬(B ∨ C) ↔ ¬B ⊗ ¬C"
      by(rule bisub_rule')
    from this have
      "¬(¬A ⊗ ¬(B ∨ C)) ↔ ¬(¬A ⊗ (¬B ⊗ ¬C))"
      by(rule bisub)
    from dm_dnc_bi and this have
      "A ∨ (B ∨ C) ↔ ¬(¬A ⊗ (¬B ⊗ ¬C))"
      by(rule bientl_trans_rule)
    from this and nca have
      step1:"A ∨ (B ∨ C) ↔ ¬((¬A ⊗ ¬B) ⊗ ¬ C)"
      by(rule bientl_trans_rule)

    from dm_dnc_bi have
      "¬(A ∨ B) ↔ ¬¬(¬A ⊗ ¬B)"
      by(rule bisub)
    from dn_bi and this have
      "¬(A ∨ B) ↔ ¬A ⊗ ¬ B"
      by(rule bisub_rule')
    from this have
      "¬(¬(A ∨ B) ⊗ ¬C) ↔ ¬((¬A ⊗ ¬B) ⊗ ¬C)"
      by(rule bisub)
    from dm_dnc_bi and this have
      "(A ∨ B) ∨ C ↔ ¬((¬A ⊗ ¬B) ⊗ ¬C)"
      by(rule bientl_trans_rule)
    from this and step1 show
      "A ∨ (B ∨ C) ↔ (A ∨ B) ∨ C"
      by(rule bisub_rule')
  qed

lemma dm_cnnd_bi: "¬A ⊗ ¬B ↔ ¬(A ∨ B)"
  proof -
    from dm_ndcn_bi show ?thesis
      by(rule bientl_sym_rule)
  qed

lemma dm_dnnc_bi: "¬A ∨ ¬B ↔ ¬(A ⊗ B)"
  proof -
    from dm_ncdn_bi show ?thesis
      by(rule bientl_sym_rule)
  qed

 lemma dn_bi': "¬¬A ↔ A"
   proof -
     from dn_bi show ?thesis
       by(rule bientl_sym_rule)
   qed

lemma dm_anns_bi: "∀(λx. ¬P x) ↔ ¬∃ P"
  proof -
    from dn_bi' have "¬∃(λx. ¬¬P x) ↔ ¬∃ P"
      by(rule bisub_open)
    from dm_ans_bi and this show
      "∀(λx. ¬P x) ↔ ¬∃ P"
      by(rule bientl_trans_rule)
  qed

lemma dm_snna_bi: "∃(λx. ¬P x) ↔ ¬∀ P"
  proof -
    from dn_bi' have "¬∀(λx. ¬¬P x) ↔ ¬∀ P"
      by(rule bisub_open)
    from dm_sna_bi and this show ?thesis
      by(rule bientl_trans_rule)
  qed

lemma lnc: "¬(A ⊗ ¬A)"
  proof -
    from dm_dnc_bi and lem have
      "¬(¬A ⊗ ¬¬A)" ..
    from conj_bicomm and this have
      step1:"¬(¬¬A ⊗ ¬A)"
      by(rule bisub_rule)
    from dn_bi' and this show "¬(A ⊗ ¬A)"
      by(rule bisub_rule)
  qed

lemma conj_export: "(A ⊗ B ⇛ C) ⇛ A ⇛ B ⇛ C"
proof -
  from implB' and impl_conj_in have "((B ⇛ A ⊗ B) ⇛ B ⇛ C) ⇛ A ⇛ B ⇛ C" ..
  from implB and this show "(A ⊗ B ⇛ C) ⇛ A ⇛ B ⇛ C" ..
qed

lemma conj_export_rule: "(A ⊗ B ⇛ C) ⟹ A ⇛ B ⇛ C"
proof -
  assume abc:"A ⊗ B ⇛ C"
  from conj_export and abc show ?thesis..
qed

lemma conj_import_rule: "A ⇛ B ⇛ C ⟹ A ⊗ B ⇛ C"
proof -
  assume abc:"A ⇛ B ⇛ C"
  from conj_import and abc show ?thesis..
qed

lemma rearrange_aLbcRde_LaebcRd: "A ⊗ (B ⊗ C) ⊗ D ⊗ E ↔ (A ⊗ E ⊗ B ⊗ C) ⊗ D"
  proof -
    from conj_bicomm and bientlI have
      "A ⊗ (B ⊗ C) ⊗ D ⊗ E ↔ A ⊗ (D ⊗ E) ⊗ B ⊗ C"
      by(rule bisub_rule)
    from conj_biass and this have
      "A ⊗ (B ⊗ C) ⊗ D ⊗ E ↔ (A ⊗ D ⊗ E) ⊗ B ⊗ C"
      by(rule bisub_rule)
    from conj_biass and this have
      "A ⊗ (B ⊗ C) ⊗ D ⊗ E ↔ ((A ⊗ D) ⊗ E) ⊗ B ⊗ C"
      by(rule bisub_rule)
    from conj_bicomm and this have
      "A ⊗ (B ⊗ C) ⊗ D ⊗ E ↔ ((D ⊗ A) ⊗ E) ⊗ B ⊗ C"
      by(rule bisub_rule)
    from conj_biass and this have
      "A ⊗ (B ⊗ C) ⊗ D ⊗ E ↔ (D ⊗ A ⊗ E) ⊗ B ⊗ C"
      by(rule bisub_rule')
    from conj_biass and this have
      "A ⊗ (B ⊗ C) ⊗ D ⊗ E ↔ D ⊗ (A ⊗ E) ⊗ B ⊗ C"
      by(rule bisub_rule')
    from conj_bicomm and this have
      "A ⊗ (B ⊗ C) ⊗ D ⊗ E ↔ ((A ⊗ E) ⊗ B ⊗ C) ⊗ D"
      by(rule bisub_rule)
    from conj_biass and this show ?thesis
      by(rule bisub_rule')
  qed

lemma rearrange_abcd_LLacRdRb: "A ⊗ B ⊗ C ⊗ D ↔ ((A ⊗ C) ⊗ D) ⊗ B"
  proof -
    from conj_bicomm and bientlI have
      "A ⊗ B ⊗ C ⊗ D ↔ A ⊗ (C ⊗ D) ⊗ B"
      by(rule bisub_rule)
    from conj_biass and this have
      "A ⊗ B ⊗ C ⊗ D ↔ (A ⊗ C ⊗ D) ⊗ B"
      by(rule bisub_rule)
    from conj_biass and this show ?thesis
      by(rule bisub_rule)
  qed

lemma impl_link_212: "A ⇛ B ⇛ C ⟹ D ⇛ B ⟹ A ⇛ D ⇛ C"
  proof -
    assume abc:"A ⇛ B ⇛ C" and db:"D ⇛ B"
    from implC and abc have "B ⇛ A ⇛ C" ..
    from db and this have "D ⇛ A ⇛ C" ..
    from implC and this show "A ⇛ D ⇛ C" ..
  qed

lemma impl_link_202 [dest]: "A ⇛ B ⇛ C ⟹ B ⟹ A ⇛ C"
  proof -
    assume abc:"A ⇛ B ⇛ C" and b:"B"
    from implC and abc have "B ⇛ A ⇛ C" ..
    from this and b show "A ⇛ C" ..
  qed

lemma impl_link_121: "A ⇛ B ⟹ C ⇛ D ⇛ A ⟹ C ⇛ D ⇛ B"
  proof -
    assume ab:"A ⇛ B" and cda:"C ⇛ D ⇛ A"
    from conj_import and cda have "C ⊗ D ⇛ A" ..
    from this and ab have "C ⊗ D ⇛ B" ..
    from conj_export and this show ?thesis..
  qed

lemma impl_link_222: "A ⇛ B ⇛ C ⟹ D ⇛ E ⇛ B ⟹ A ⇛ D ⇛ E ⇛ C"
  proof -
    assume abc:"A ⇛ B ⇛ C" and deb:"D ⇛ E ⇛ B"
    from implC and abc have "B ⇛ A ⇛ C" ..
    from deb and this have "D ⇛ E ⇛ A ⇛ C" by(rule impl_link_121[rotated])
    from this and implC have "D ⇛ A ⇛ E ⇛ C" ..
    from implC and this show ?thesis ..
  qed

lemma entl_trans_01: "B → C ⟹ A ⇛ (C → E) ⟹ A ⇛ (B → E)"
  proof -
    assume bc:"B → C" and ace:"A ⇛ (C → E)"
    from impl_conj_in and bc have "(C → E) ⇛ (B → C) ⊗ (C → E)" ..
    from ace and this have step1:"A ⇛ (B → C) ⊗ (C → E)" ..
    from entl_impl and entl_cs have link:"(B → C) ⊗ (C → E) ⇛ (B → E)" ..
    from step1 and link show "A ⇛ (B → E)" ..
  qed

lemma entl_trans_10: "A ⇛ (B → C) ⟹ C → E ⟹ A ⇛ (B → E)"
  proof -
    assume abc:"A ⇛ (B → C)" and ce:"C → E"
    from implC and impl_conj_in have "(C → E) ⇛ (B → C) ⇛ (B → C) ⊗ (C → E)" ..
    from this and ce have "(B → C) ⇛ (B → C) ⊗ (C → E)" ..
    from abc and this have step1:"A ⇛ (B → C) ⊗ (C → E)" ..
    from entl_impl and entl_cs have link:"(B → C) ⊗ (C → E) ⇛ (B → E)" ..
    from step1 and link show "A ⇛ (B → E)" ..
  qed

lemma entl_after_impl_trans: "A ⇛ B ⟹ B → C ⟹ A ⇛ C"
  proof -
    assume ab:"A ⇛ B" and bc:"B → C"
    from entl_impl and bc have "B ⇛ C" ..
    from ab and this show ?thesis ..
  qed

lemma impl_after_entl_trans: "A → B ⟹ B ⇛ C ⟹ A ⇛ C"
  proof -
    assume ab:"A → B" and bc:"B ⇛ C"
    from entl_impl and ab have "A ⇛ B" ..
    from this and bc show ?thesis ..
  qed

lemma impl_pmp: "A ⊗ (A ⇛ B) ⇛ B"
  proof -
    from conj_import and implI have "(A ⇛ B) ⊗ A ⇛ B" ..
    from conj_bicomm and this show "A ⊗ (A ⇛ B) ⇛ B"
      by(rule bisub_rule)
  qed

lemma conj_monotone_left_twisted: "(A ⊗ B) ⊗ (A ⇛ C) ⇛ (B ⊗ C)"
proof -
  from impl_pmp and impl_conj_in have "A ⊗ (A ⇛ C) ⇛ B ⇛ C ⊗ B"
    by(rule impl_trans_rule)
  from conj_import and this have "(A ⊗ (A ⇛ C)) ⊗ B ⇛ C ⊗ B"
    by(rule impl_mp)
  from conj_bicomm and this have "(A ⊗ (A ⇛ C)) ⊗ B ⇛ B ⊗ C"
    by(rule bisub_rule)
  from conj_biass' and this have "A ⊗ ((A ⇛ C) ⊗ B) ⇛ B ⊗ C"
    by(rule bisub_rule)
  from conj_bicomm and this have "A ⊗ (B ⊗ (A ⇛ C)) ⇛ B ⊗ C"
    by(rule bisub_rule)
  from conj_biass and this show "(A ⊗ B) ⊗ (A ⇛ C) ⇛ (B ⊗ C)"
    by(rule bisub_rule)
qed

lemma conj_monotone_left_rule: "A ⇛ C ⟹ A ⊗ B ⇛ C ⊗ B"
  proof -
    assume ac:"A ⇛ C"
    from conj_export and conj_monotone_left_twisted have
      "A ⊗ B ⇛ (A ⇛ C) ⇛ B ⊗ C" ..
    from this and ac have
      "A ⊗ B ⇛ B ⊗ C" ..
    from conj_bicomm and this show ?thesis
      by(rule bisub_rule)
  qed

lemma conj_monotone_right: "(A ⊗ B) ⊗ (B ⇛ C) ⇛ A ⊗ C"
  proof -
    from conj_bicomm and conj_monotone_left_twisted show ?thesis
      by(rule bisub_rule)
  qed

lemma conj_monotone_right_rule: "B ⇛ C ⟹ A ⊗ B ⇛ A ⊗ C"
  proof -
    assume bc:"B ⇛ C"
    from conj_export and conj_monotone_right have
      "A ⊗ B ⇛ (B ⇛ C) ⇛ A ⊗ C" ..
    from this and bc show ?thesis ..
  qed

lemma factor: "(A ⇛ B) ⊗ (C ⇛ D) ⇛ (A ⊗ C ⇛ B ⊗ D)"
proof -
  from conj_export and conj_monotone_left_twisted have
    "(C ⊗ (C ⇛ D)) ⊗ B ⇛ ((C ⊗ (C ⇛ D)) ⇛ D) ⇛ B ⊗ D" ..
  from this and impl_pmp have
    "(C ⊗ (C ⇛ D)) ⊗ B ⇛ B ⊗ D"
    by(rule impl_link_202)
  from conj_monotone_left_twisted and this have
    step1:"(A ⊗ (C ⊗ (C ⇛ D))) ⊗ (A ⇛ B) ⇛ B ⊗ D" ..

  from conj_biass and this have
    "((A ⊗ C) ⊗ (C ⇛ D)) ⊗ (A ⇛ B) ⇛ B ⊗ D"
    by(rule bisub_rule)
  from conj_biass' and this have
    "(A ⊗ C) ⊗ ((C ⇛ D) ⊗ (A ⇛ B)) ⇛ B ⊗ D"
    by(rule bisub_rule)
  from conj_bicomm and this have
    "(A ⊗ C) ⊗ ((A ⇛ B) ⊗ (C ⇛ D)) ⇛ B ⊗ D"
    by(rule bisub_rule)
  from conj_bicomm and this have
    "((A ⇛ B) ⊗ (C ⇛ D)) ⊗ (A ⊗ C) ⇛ B ⊗ D"
    by(rule bisub_rule)

  from conj_export and this show
    "(A ⇛ B) ⊗ (C ⇛ D) ⇛ (A ⊗ C ⇛ B ⊗ D)"
    by(rule impl_mp)
qed

lemma factor_rule: "A ⇛ B ⟹ C ⇛ D ⟹ A ⊗ C ⇛ B ⊗ D"
  proof -
    assume ab:"A ⇛ B" and cd:"C ⇛ D"
    from ab and cd have "(A ⇛ B) ⊗ (C ⇛ D)" ..
    from factor and this show "A ⊗ C ⇛ B ⊗ D" ..
  qed

lemma bientl_trans_impl: "(A ↔ B) ⊗ (B ↔ C) ⇛ (A ↔ C)"
  proof -
    from entl_impl and entl_cs have
      abbcab:"(A → B) ⊗ (B → C) ⇛ (A → C)" ..
    from entl_impl and entl_cs have
      "(C → B) ⊗ (B → A) ⇛ (C → A)" ..
    from abbcab and this have
      "((A → B) ⊗ (B → C)) ⊗ ((C → B) ⊗ (B → A)) ⇛ (A → C) ⊗ (C → A)"
      by(rule factor_rule)
    from this have
      step1:"((A → B) ⊗ (B → C)) ⊗ ((C → B) ⊗ (B → A)) ⇛ (A ↔ C)"
      by(fold bientl_def)

    from conj_biass' and this have
      "(A → B) ⊗ ((B → C) ⊗ ((C → B) ⊗ (B → A))) ⇛ (A ↔ C)"
      by(rule bisub_rule)
    from conj_biass and this have
      "(A → B) ⊗ (((B → C) ⊗ (C → B)) ⊗ (B → A)) ⇛ (A ↔ C)"
      by(rule bisub_rule)
    from this have
      "(A → B) ⊗ ((B ↔ C) ⊗ (B → A)) ⇛ (A ↔ C)"
      by(fold bientl_def)
    from conj_bicomm and this have
      "(A → B) ⊗ ((B → A) ⊗ (B ↔ C)) ⇛ (A ↔ C)"
      by(rule bisub_rule)
    from conj_biass and this have
      "((A → B) ⊗ (B → A)) ⊗ (B ↔ C) ⇛ (A ↔ C)"
      by(rule bisub_rule)

    from this show
      "(A ↔ B) ⊗ (B ↔ C) ⇛ (A ↔ C)"
      by(fold bientl_def)
  qed

lemma entl_antecedent_strengthening: "(A → B) ⇛ (A ⊗ C → B)"
  proof -
    from entl_impl and entl_contra have "(A → B) ⇛ (¬B → ¬A)" ..
    from this and entl_disj_inl have step1:"(A → B) ⇛ (¬B → ¬A ∨ ¬C)"
      by(rule entl_trans_10)
    from entl_impl and entl_contra have "(¬B → ¬A ∨ ¬C) ⇛ (¬(¬A ∨ ¬C) → ¬¬B)" ..
    from step1 and this have "(A → B) ⇛ (¬(¬A ∨ ¬C) → ¬¬B)" ..
    from this and dne have "(A → B) ⇛ (¬(¬A ∨ ¬C) → B)"
      by(rule entl_trans_10)
    from dm_cnd and this show "(A → B) ⇛ (A ⊗ C → B)"
      by(rule entl_trans_01)
  qed

lemma impl_material: "(A ⇛ B) ⇛ (¬A ∨ B)"
proof -
  from entl_impl and entl_disj_inl have "¬A ⇛ ¬A ∨ B" ..
  from impl_disj_left and this have "(A ⇛ ¬A ∨ B) ⇛ ¬A ∨ A ⇛ ¬A ∨ B" ..
  from implC and this have step1:"¬A ∨ A ⇛ (A ⇛ ¬A ∨ B) ⇛ ¬A ∨ B" ..
  from disj_bicomm and lem have "¬A ∨ A"
    by(rule bientl_mp_ltr)
  from step1 and this have step2:"(A ⇛ ¬A ∨ B) ⇛ ¬A ∨ B" ..
  from entl_impl and entl_disj_inr have "B ⇛ ¬A ∨ B" ..
  from implB and this have "(A ⇛ B) ⇛ A ⇛ ¬A ∨ B" ..
  from this and step2 show "(A ⇛ B) ⇛ ¬A ∨ B" ..
qed

lemma pmp_with_side_premises: "(A ⊗ B ⇛ C) ⊗ B ⇛ A ⇛ C"
proof -
  from conj_export and implC have "(A ⊗ B ⇛ C) ⇛ B ⇛ A ⇛ C" ..
  from conj_import and this show "(A ⊗ B ⇛ C) ⊗ B ⇛ A ⇛ C" ..
qed

lemma dist_cd_ltr: "A ⊗ (B ∨ C) ⇛ (A ⊗ B) ∨ (A ⊗ C)"
  proof -
    from impl_conj_in and impl_disj_inl have
      "A ⇛ B ⇛ (A ⊗ B) ∨ (A ⊗ C)"
      by(rule impl_link_121[rotated])
    from implC and this have
      bhorn:"B ⇛ A ⇛ (A ⊗ B) ∨ (A ⊗ C)" ..

    from impl_conj_in and impl_disj_inr have
      "A ⇛ C ⇛ (A ⊗ B) ∨ (A ⊗ C)"
      by(rule impl_link_121[rotated])
    from implC and this have
      "C ⇛ A ⇛ (A ⊗ B) ∨ (A ⊗ C)" ..

    from bhorn and this have
      "B ∨ C ⇛ A ⇛ (A ⊗ B) ∨ (A ⊗ C)"
      by(rule disj_left_rule)
    from implC and this have
      "A ⇛ B ∨ C ⇛ (A ⊗ B) ∨ (A ⊗ C)" ..
    from conj_import and this show ?thesis ..
  qed

lemma dist_cd_rtl: "(A ⊗ B) ∨ (A ⊗ C) ⇛ A ⊗ (B ∨ C)"
  proof -
    from impl_disj_inl have
      abhorn:"A ⊗ B ⇛ A ⊗ (B ∨ C)"
      by(rule conj_monotone_right_rule)
    from impl_disj_inr have
      "A ⊗ C ⇛ A ⊗ (B ∨ C)"
      by(rule conj_monotone_right_rule)
    from abhorn and this show ?thesis
      by(rule disj_left_rule)
  qed

lemma dist_cd_biimpl: "A ⊗ (B ∨ C) ⇌ (A ⊗ B) ∨ (A ⊗ C)"
  proof -
    from dist_cd_ltr and dist_cd_rtl show ?thesis
      unfolding biimpl_def ..
  qed

lemma cases_with_side_premise: "(A ⊗ B ⇛ C) ⊗ (D ⇛ C) ⇛ A ⊗ (B ∨ D) ⇛ C"
proof -
  from entl_impl and entl_cer have "A ⊗ D ⇛ D" ..
  from implB' and this have step1: "(D ⇛ C) ⇛ (A ⊗ D ⇛ C)" ..
  from implC and impl_disj_left have "(A ⊗ D ⇛ C) ⇛ (A ⊗ B ⇛ C) ⇛ (A ⊗ B) ∨ (A ⊗ D) ⇛ C" ..
  from step1 and this have "(D ⇛ C) ⇛ (A ⊗ B ⇛ C) ⇛ (A ⊗ B) ∨ (A ⊗ D) ⇛ C" ..
  from implC and this have "(A ⊗ B ⇛ C) ⇛ (D ⇛ C) ⇛ (A ⊗ B) ∨ (A ⊗ D) ⇛ C" ..
  from conj_import and this have "(A ⊗ B ⇛ C) ⊗ (D ⇛ C) ⇛ (A ⊗ B) ∨ (A ⊗ D) ⇛ C" ..
  from implC and this have step1:"(A ⊗ B) ∨ (A ⊗ D) ⇛ (A ⊗ B ⇛ C) ⊗ (D ⇛ C) ⇛ C" ..

  from dist_cd_ltr and step1 have "A ⊗ (B ∨ D) ⇛ (A ⊗ B ⇛ C) ⊗ (D ⇛ C) ⇛ C" ..
  from implC and this show "(A ⊗ B ⇛ C) ⊗ (D ⇛ C) ⇛ A ⊗ (B ∨ D) ⇛ C" ..
qed

lemma final_prop_exercise: "(A ⇛ B ⇛ C) ⇛ (C ⇛ D) ⇛ (A ⇛ B ⇛ D)"
proof -
  from conj_import and implB' have "(A ⇛ B ⇛ C) ⇛ (C ⇛ D) ⇛ (A ⊗ B ⇛ D)" ..
  from conj_import and this have "(A ⇛ B ⇛ C) ⊗ (C ⇛ D) ⇛ (A ⊗ B ⇛ D)" ..
  from this and conj_export have "(A ⇛ B ⇛ C) ⊗ (C ⇛ D) ⇛ A ⇛ B ⇛ D" ..
  from conj_export and this show "(A ⇛ B ⇛ C) ⇛ (C ⇛ D) ⇛ (A ⇛ B ⇛ D)" ..
qed

lemma all_impl_mp:"∀(λx. P x ⇛ Q x) ⊗ ∀ P ⇛ ∀ Q"
proof -
  {
  fix y
  from entl_impl and entl_ui have step1:"∀(λx. P x ⇛ Q x) ⇛ P y ⇛ Q y" ..
  from entl_impl and entl_ui have "∀ P ⇛ P y" ..
  from step1 and this have "∀(λx. P x ⇛ Q x) ⇛ ∀ P ⇛ Q y"
    by(rule impl_link_212)
  from conj_import and this have "∀(λx. P x ⇛ Q x) ⊗ ∀ P ⇛ Q y" ..
  }
  have "\<And> y. (∀(λx. P x ⇛ Q x) ⊗ ∀ P ⇛ Q y)" by fact
  from this have "∀(λy. ∀(λx. P x ⇛ Q x) ⊗ ∀ P ⇛ Q y)" ..
  from all_cons and this show "∀(λx. P x ⇛ Q x) ⊗ ∀ P ⇛ ∀ Q" ..
qed

lemma all_impl_dist:"∀(λx. P x ⇛ Q x) ⇛ ∀ P ⇛ ∀ Q"
proof -
  from conj_export and all_impl_mp show "∀(λx. P x ⇛ Q x) ⇛ ∀ P ⇛ ∀ Q" ..
qed

lemma all_impl_factor: "∀(λx. P x ⇛  Q x) ⊗ ∀(λy. R(y) ⇛ S(y)) ⇛ ∀(λw. P(w) ⊗ R(w)) ⇛ ∀(λz. Q(z) ⊗ S(z))"
proof -
  {
  fix z
  from entl_impl and entl_ui have step1:"∀(λx. P x ⇛ Q x) ⇛ P(z) ⇛ Q(z)" ..
  from entl_impl and entl_ui have step2:"∀(λy. R(y) ⇛ S(y)) ⇛ R(z) ⇛ S(z)" ..
  from step1 and step2 have
    "(∀(λx. P x ⇛ Q x) ⇛ P(z) ⇛ Q(z)) ⊗ (∀(λy. R(y) ⇛ S(y)) ⇛ R(z) ⇛ S(z))" ..
  from factor and this have
    "∀(λx. P x ⇛ Q x) ⊗ ∀(λy. R(y) ⇛ S(y)) ⇛ (P(z) ⇛ Q(z)) ⊗ (R(z) ⇛ S(z))" ..
  from this and factor have
    step3:"∀(λx. P x ⇛ Q x) ⊗ ∀(λy. R(y) ⇛ S(y)) ⇛ P(z) ⊗ R(z) ⇛ Q(z) ⊗ S(z)" ..
  from entl_impl and entl_ui have "∀(λw. P(w) ⊗ R(w)) ⇛ P(z) ⊗ R(z)" ..
  from step3 and this have
    "(∀(λx. P x ⇛ Q x) ⊗ ∀(λy. R(y) ⇛ S(y))) ⇛ ∀(λw. P(w) ⊗ R(w)) ⇛ Q(z) ⊗ S(z)"
    by(rule impl_link_212)
  from conj_import and this have
    "(∀(λx. P x ⇛ Q x) ⊗ ∀(λy. R(y) ⇛ S(y))) ⊗ ∀(λw. P(w) ⊗ R(w)) ⇛ Q(z) ⊗ S(z)" ..
  }
  have "\<And> z. ((∀(λx. P x ⇛ Q x) ⊗ ∀(λy. R(y) ⇛ S(y))) ⊗ ∀(λw. P(w) ⊗ R(w)) ⇛ Q(z) ⊗ S(z))" by fact
  from this have
    "∀(λz. (∀(λx. P x ⇛ Q x) ⊗ ∀(λy. R(y) ⇛ S(y))) ⊗ ∀(λw. P(w) ⊗ R(w)) ⇛ Q(z) ⊗ S(z))" ..
  from all_cons and this have
    "(∀(λx. P x ⇛ Q x) ⊗ ∀(λy. R(y) ⇛ S(y))) ⊗ ∀(λw. P(w) ⊗ R(w)) ⇛ ∀(λz. Q(z) ⊗ S(z))" ..
  from conj_export and this show
    "∀(λx. P x ⇛  Q x) ⊗ ∀(λy. R(y) ⇛ S(y)) ⇛ ∀(λw. P(w) ⊗ R(w)) ⇛ ∀(λz. Q(z) ⊗ S(z))" ..
qed

lemma all_over_conj: "∀ P ⊗ ∀ Q ⇛ ∀(λx. P x ⊗ Q x)"
proof -
  {
  fix x
  from entl_impl and entl_ui have appx:"∀ P ⇛ P x" ..
  from entl_impl and entl_ui have aqqx:"∀ Q ⇛ Q x" ..
  from appx and aqqx have "(∀ P ⇛ P x) ⊗ (∀ Q ⇛ Q x)" ..
  from factor and this have "∀ P ⊗ ∀ Q ⇛ P x ⊗ Q x" ..
  }
  have "\<And> x. (∀ P ⊗ ∀ Q ⇛ P x ⊗ Q x)" by fact
  from this have "∀(λx. ∀ P ⊗ ∀ Q ⇛ P x ⊗ Q x)" ..
  from all_cons and this show "∀ P ⊗ ∀ Q ⇛ ∀(λx. P x ⊗ Q x)" ..
qed

lemma everything_self_entl: "∀(λx. P x → P x)"
proof -
  fix x
  from entlI show "∀(λx. P x → P x)" ..
qed

lemma all_entl_entl_bientl_ltr: "∀(λx. P x → Q x) ⊗ ∀(λy. Q y → P y) ⇛ ∀(λz. P(z) ↔ Q(z))"
  unfolding bientl_def
  proof -
    {
    fix z
    from entl_impl and entl_ui have pqz:"∀(λx. P x → Q x) ⇛ (P(z) → Q(z))" ..
    from entl_impl and entl_ui have qpz:"∀(λy. Q y → P y) ⇛ (Q(z) → P(z))" ..
    from pqz and qpz have
      "(∀(λx. P x → Q x) ⇛ (P(z) → Q(z))) ⊗ (∀(λy. Q y → P y) ⇛ (Q(z) → P(z)))" ..
    from factor and this have
      "∀(λx. P x → Q x) ⊗ ∀(λy. Q y → P y) ⇛ (P(z) → Q(z)) ⊗ (Q(z) → P(z))" ..
    }
    have "\<And> z. (∀(λx. P x → Q x) ⊗ ∀(λy. Q y → P y) ⇛ (P(z) → Q(z)) ⊗ (Q(z) → P(z)))" by fact
    from this have
      "∀(λz. ∀(λx. P x → Q x) ⊗ ∀(λy. Q y → P y) ⇛ (P(z) → Q(z)) ⊗ (Q(z) → P(z)))" ..
    from all_cons and this show
      "∀(λx. P x → Q x) ⊗ ∀(λy. Q y → P y) ⇛ ∀(λz. (P(z) → Q(z)) ⊗ (Q(z) → P(z)))" ..
  qed

lemma bientl_contra_impl: "(A ↔ B) ⇛ (¬B ↔ ¬A)"
  proof -
    from entl_impl and entl_contra have
      abba: "(A → B) ⇛ (¬B → ¬A)" ..
    from entl_impl and entl_contra have
      baab: "(B → A) ⇛ (¬A → ¬B)" ..
    from abba and baab show ?thesis
      unfolding bientl_def
      by(rule factor_rule)
qed

lemma conj_in_under_disjr: "(A ∨ B) ⊗ (A ∨ C) ⇛ A ∨ (B ⊗ C)"
  proof -
    from impl_disj_inl and implK have
      "A ⇛ A ∨ C ⇛ A ∨ (B ⊗ C)"
      by(rule impl_link_121)
    from impl_disj_left and this have
      step1:"(B ⇛ A ∨ C ⇛ A ∨ (B ⊗ C)) ⇛ A ∨ B ⇛ A ∨ C ⇛ A ∨ (B ⊗ C)" ..

    from impl_disj_inl and implK have
      "A ⇛ B ⇛ A ∨ (B ⊗ C)"
      by(rule impl_link_121)
    from impl_disj_left and this have
      step2:"(C ⇛ B ⇛ A ∨ (B ⊗ C)) ⇛ A ∨ C ⇛ B ⇛ A ∨ (B ⊗ C)" ..

    from conj_bicomm and impl_conj_in have
      "C ⇛ B ⇛ B ⊗ C"
      by(rule bisub_rule)
    from impl_disj_inr and this have
      "C ⇛ B ⇛ A ∨ (B ⊗ C)"
      by(rule impl_link_121)
    from step2 and this have
      "A ∨ C ⇛ B ⇛ A ∨ (B ⊗ C)" ..
    from implC and this have
      "B ⇛ A ∨ C ⇛ A ∨ (B ⊗ C)" ..
    from step1 and this have
      "A ∨ B ⇛ A ∨ C ⇛ A ∨ (B ⊗ C)" ..
    from conj_import and this show ?thesis ..
  qed

lemma double_dist: "(A ∨ B) ⊗ (C ∨ D) ⇛ A ∨ C ∨ (B ⊗ D)"
proof -
  from dist_cd_ltr have
    "(A ∨ B) ⊗ (C ∨ D) ⇛ (C ⊗ (A ∨ B)) ∨ ((A ∨ B) ⊗ D)" by(rule bisub_rule[OF conj_bicomm])
  then have
    step1:"(A ∨ B) ⊗ (C ∨ D) ⇛ (C ⊗ (A ∨ B)) ∨ (D ⊗ (A ∨ B))" by(rule bisub_rule[OF conj_bicomm])

  from impl_cel and impl_disj_inl have
    "C ⊗ (A ∨ B) ⇛ C ∨ (B ⊗ D)" ..
  from this and impl_disj_inr have
    step2:"C ⊗ (A ∨ B) ⇛ A ∨ C ∨ (B ⊗ D)" ..

  from impl_cer and impl_disj_inl have
    horn1:"D ⊗ A ⇛ A ∨ C ∨ (B ⊗ D)" ..
  from impl_disj_inr and impl_disj_inr have
    "D ⊗ B ⇛ A ∨ C ∨ (D ⊗ B)" ..
  then have
    "D ⊗ B ⇛ A ∨ C ∨ (B ⊗ D)" by(rule bisub_rule[OF conj_bicomm])
  from horn1 and this have
    "(D ⊗ A) ∨ (D ⊗ B) ⇛ A ∨ C ∨ (B ⊗ D)" by (rule disj_left_rule)
  from dist_cd_ltr and this have
    step3:"D ⊗ (A ∨ B) ⇛ A ∨ C ∨ (B ⊗ D)" ..

  from step2 and step3 have
    "(C ⊗ (A ∨ B)) ∨ (D ⊗ (A ∨ B)) ⇛ A ∨ C ∨ (B ⊗ D)" by(rule disj_left_rule)
  from step1 and this show ?thesis ..
qed

lemma cer_under_disjl: "(A ⊗ B) ∨ C ⇛ B ∨ C"
  proof -
    from disj_bicomm and cer_under_disjr have
      "(A ⊗ B) ∨ C ⇛ C ∨ B"
      by(rule bisub_rule)
    from disj_bicomm and this show ?thesis
      by(rule bisub_rule)
  qed

lemma add_conjunct_on_left: "(A ⇛ B) ⇛ C ⊗ A ⇛ C ⊗ B"
  proof -
    from conj_bicomm and conj_monotone_right have
      "(A ⇛ B) ⊗ (C ⊗ A) ⇛ C ⊗ B"
      by(rule bisub_rule)
    from conj_export and this show ?thesis ..
  qed

lemma impl_some_monotone: "∀(λx. P x ⇛ Q x) ⇛ ∃ P ⇛ ∃ Q"
  proof -
    {
    fix y
    from impl_eg and impl_ui have
      "∀(λx. P x ⇛ Q x) ⇛ P y ⇛ ∃ Q"
      by(rule impl_link_121)
    }
    have "\<And> y. (∀(λx. P x ⇛ Q x) ⇛ P y ⇛ ∃ Q)" by fact
    from this have
      "∀(λy. ∀(λx. P x ⇛ Q x) ⇛ P y ⇛ ∃ Q)" ..
    from all_cons and this have
      "∀(λx. P x ⇛ Q x) ⇛ ∀(λy. P y ⇛ ∃ Q)" ..
    from this and all_ante show ?thesis ..
  qed

lemma disj_in_under_impl: "A ∨ (B ⇛ C) ⇛ B ⇛ A ∨ C"
  proof -
    from impl_disj_inl and implK have
      "A ⇛ B ⇛ A ∨ C"
      by(rule impl_link_121)
    from impl_disj_left and this have
      step1:"((B ⇛ C) ⇛ B ⇛ A ∨ C) ⇛ A ∨ (B ⇛ C) ⇛ B ⇛ A ∨ C" ..

    from implB and impl_disj_inr have
      "(B ⇛ C) ⇛ B ⇛ A ∨ C" ..
    from step1 and this show ?thesis ..
  qed

lemma conj_in_under_impl: "A ⊗ (B ⇛ C) ⇛ B ⇛ A ⊗ C"
  proof -
     from conj_export and conj_monotone_right have
       "A ⊗ (B ⇛ C) ⇛ ((B ⇛ C) ⇛ C) ⇛ A ⊗ C" ..
     from this and implCI show ?thesis
       by(rule impl_link_212)
  qed

lemma disj_monotone_right: "(A ∨ B) ⊗ (B ⇛ C) ⇛ A ∨ C"
  proof -
    from impl_disj_inl and implK have
      step1:"A ⇛ (B ⇛ C) ⇛ A ∨ C"
      by(rule impl_link_121)
    from impl_disj_inr and implCI have
      step2:"B ⇛ (B ⇛ C) ⇛ A ∨ C"
      by(rule impl_link_121)

    from impl_disj_left and step1 have
      "(B ⇛ (B ⇛ C) ⇛ A ∨ C) ⇛ A ∨ B ⇛ (B ⇛ C) ⇛ A ∨ C" ..
    from this and step2 have
      "A ∨ B ⇛ (B ⇛ C) ⇛ A ∨ C" ..
    from conj_import and this show ?thesis ..
  qed

lemma disj_monotone_left: "(A ∨ B) ⊗ (A ⇛ C) ⇛ C ∨ B"
  apply(rule bisub_rule[OF disj_bicomm[of B A]])
  apply(rule bisub_rule[OF disj_bicomm[of B C]])
  apply(rule disj_monotone_right)
  done

lemma disj_monotone_left_impl_rule: "A ⇛ C ⟹ A ∨ B ⇛ C ∨ B"
proof -
  assume ac:"A ⇛ C"
  from disj_monotone_left have "(A ⇛ C) ⊗ (A ∨ B) ⇛ C ∨ B"
    by(rule bisub_rule[OF conj_bicomm])
  from conj_export and this have "(A ⇛ C) ⇛ A ∨ B ⇛ C ∨ B" ..
  from this and ac show ?thesis ..
qed

lemma disj_monotone_right_impl_rule: "B ⇛ C ⟹ A ∨ B ⇛ A ∨ C"
proof -
  assume bc:"B ⇛ C"
  from disj_monotone_right have "(B ⇛ C) ⊗ (A ∨ B) ⇛ A ∨ C"
    by(rule bisub_rule[OF conj_bicomm])
  from conj_export and this have "(B ⇛ C) ⇛ A ∨ B ⇛ A ∨ C" ..
  from this and bc show ?thesis ..
qed

lemma disj_monotone_left_rule: "A ⇛ C ⟹ A ∨ B ⟹ C ∨ B"
proof -
  assume ac:"A ⇛ C" and ab:"A ∨ B"
  from disj_monotone_left have "(A ⇛ C) ⊗ (A ∨ B) ⇛ C ∨ B"
    by(rule bisub_rule[OF conj_bicomm])
  from conj_export and this have "(A ⇛ C) ⇛ A ∨ B ⇛ C ∨ B" ..
  from this and ac have "A ∨ B ⇛ C ∨ B" ..
  from this and ab show ?thesis ..
qed

lemma disj_monotone_right_rule: "B ⇛ C ⟹ A ∨ B ⟹ A ∨ C"
proof -
  assume bc:"B ⇛ C" and ab:"A ∨ B"
  from disj_monotone_right have "(B ⇛ C) ⊗ (A ∨ B) ⇛ A ∨ C"
    by(rule bisub_rule[OF conj_bicomm])
  from conj_export and this have "(B ⇛ C) ⇛ A ∨ B ⇛ A ∨ C" ..
  from this and bc have "A ∨ B ⇛ A ∨ C" ..
  from this and ab show ?thesis ..
qed

lemma eg_under_disjr: "(A ∨ P(t)) ⇛ A ∨ ∃ P"
  proof -
    from conj_export and disj_monotone_right have
      "(A ∨ P(t)) ⇛ (P(t) ⇛ ∃ P) ⇛ A ∨ ∃ P" ..
    from this and impl_eg show ?thesis ..
  qed

lemma entl_get_conjunct_2_of_3: "A ⊗ B ⊗ C → B"
  proof -
    from entl_cer and entl_cel show ?thesis ..
  qed

lemma impl_get_conjunct_2_of_3: "A ⊗ B ⊗ C ⇛ B"
  proof -
    from entl_impl and entl_get_conjunct_2_of_3 show ?thesis ..
  qed

lemma entl_get_conjunct_3_of_4: "A ⊗ B ⊗ C ⊗ D → C"
  proof -
    from entl_cer and entl_get_conjunct_2_of_3 show ?thesis ..
  qed

lemma entl_get_conjunct_4_of_5: "A ⊗ B ⊗ C ⊗ D ⊗ E → D"
  proof -
    from entl_cer and entl_get_conjunct_3_of_4 show ?thesis .. 
  qed

lemma bocardo: "∃(λz. P(z) ⊗ ¬Q(z)) ⇛ ∀(λz. P(z) ⇛ R(z)) ⇛ ∃(λz. R(z) ⊗ ¬Q(z))"
  proof -
    {
      fix t
      from implCI and impl_ui have
        "P(t) ⇛ ∀(λz. P(z) ⇛ R(z)) ⇛ R(t)"
        by(rule impl_link_212)
      from add_conjunct_on_left and this have
        "¬Q(t) ⊗ P(t) ⇛ ¬Q(t) ⊗ (∀(λz. P(z) ⇛ R(z)) ⇛ R(t))" ..
      from this and conj_in_under_impl have
        "¬Q(t) ⊗ P(t) ⇛ ∀(λz. P(z) ⇛ R(z)) ⇛ ¬Q(t) ⊗ R(t)" ..
      from conj_bicomm and this have
        "P(t) ⊗ ¬Q(t) ⇛ ∀(λz. P(z) ⇛ R(z)) ⇛ ¬Q(t) ⊗ R(t)"
        by(rule bisub_rule)
      from conj_bicomm and this have
        "P(t) ⊗ ¬Q(t) ⇛ ∀(λz. P(z) ⇛ R(z)) ⇛ R(t) ⊗ ¬Q(t)"
        by(rule bisub_rule)
      from impl_eg and this have
        "P(t) ⊗ ¬Q(t) ⇛ ∀(λz. P(z) ⇛ R(z)) ⇛ ∃(λz. R(z) ⊗ ¬Q(z))"
        by(rule impl_link_121)
    }
    have "⋀t. P(t) ⊗ ¬Q(t) ⇛ ∀(λz. P(z) ⇛ R(z)) ⇛ ∃(λz. R(z) ⊗ ¬Q(z))" by fact
    from this have "∀(λz. P(z) ⊗ ¬Q(z) ⇛ ∀(λz. P(z) ⇛ R(z)) ⇛ ∃(λz. R(z) ⊗ ¬Q(z)))" ..
    from all_ante and this show ?thesis ..
  qed

(* Note the difference between this and bocardo:
   where bocardo has ⇛ in its antecedent, baroco has →.
   This is because the proof of baroco uses contraposition .*)
lemma baroco: "∀(λz. P(z) → Q(z)) ⇛ ∃(λz. R(z) ⊗ ¬Q(z)) ⇛ ∃(λz. R(z) ⊗ ¬P(z))"
  proof -
    {
      fix t
      from entl_impl and add_conjunct_on_left have
        "(¬Q(t) → ¬P(t)) ⇛ R(t) ⊗ ¬Q(t) ⇛ R(t) ⊗ ¬P(t)" ..
      from entl_contra and this have
        "(P(t) → Q(t)) ⇛ R(t) ⊗ ¬Q(t) ⇛ R(t) ⊗ ¬P(t)"
        by(rule impl_after_entl_trans)
      from impl_ui and this have
        "∀(λz. P(z) → Q(z)) ⇛ R(t) ⊗ ¬Q(t) ⇛ R(t) ⊗ ¬P(t)" ..
      from impl_eg and this have
        "∀(λz. P(z) → Q(z)) ⇛ R(t) ⊗ ¬Q(t) ⇛ ∃(λz. R(z) ⊗ ¬P(z))"
        by(rule impl_link_121)
    }
    have "⋀t. ∀(λz. P(z) → Q(z)) ⇛ R(t) ⊗ ¬Q(t) ⇛ ∃(λz. R(z) ⊗ ¬P(z))" by fact
    from this have
      "∀(λt. ∀(λz. P(z) → Q(z)) ⇛ R(t) ⊗ ¬Q(t) ⇛ ∃(λz. R(z) ⊗ ¬P(z)))" ..
    from all_cons and this have
      "∀(λz. P(z) → Q(z)) ⇛ ∀(λt. R(t) ⊗ ¬Q(t) ⇛ ∃(λz. R(z) ⊗ ¬P(z)))" ..
    from this and all_ante show ?thesis ..
  qed

lemma no_counterexample_to_contraction: "¬(A ⊗ A) ⇛ ¬A"
  proof -
    from impl_disj_left and implI have
      "(¬A ⇛ ¬A) ⇛ ¬A ∨ ¬A ⇛ ¬A" ..
    from this and implI have
      "¬A ∨ ¬A ⇛ ¬A" ..
    from dm_dnnc_bi and this show ?thesis
      by(rule bisub_rule)
  qed

lemma bientl_biimpl: "(A ↔ B) ⇛ (A ⇌ B)"
  proof -
    from entl_impl and entl_impl show ?thesis
      unfolding bientl_def
      unfolding biimpl_def
      by(rule factor_rule)
qed

lemma biimpl_trans_rule: "A ⇌ B ⟹ B ⇌ C ⟹ A ⇌ C"
  unfolding biimpl_def
  proof
    assume abba:"(A ⇛ B) ⊗ (B ⇛ A)" and bccb:"(B ⇛ C) ⊗ (C ⇛ B)"
    from impl_cel and abba have ab:"A ⇛ B" ..
    from impl_cer and abba have ba:"B ⇛ A" ..
    from impl_cel and bccb have bc:"B ⇛ C" ..
    from impl_cer and bccb have cb:"C ⇛ B" ..
    from ab and bc show "A ⇛ C" ..
    from cb and ba show "C ⇛ A" ..
  qed

lemma some_over_and: "A ⊗ ∃ P ⇛ ∃(λx. A ⊗ P x)"
  proof -
    {
      fix y
      from impl_conj_in and impl_eg have
        "A ⇛ P y ⇛ ∃(λx. A ⊗ P x)"
        by(rule impl_link_121[rotated])
      from implC and this have
        "P y ⇛ A ⇛ ∃(λx. A ⊗ P x)" ..
    }
    have "\<And> y. P y ⇛ A ⇛ ∃(λx. A ⊗ P x)" by fact
    from this have
      "∀(λy. P y ⇛ A ⇛ ∃(λx. A ⊗ P x))" ..
    from all_ante and this have
      "∃ P ⇛ A ⇛ ∃(λx. A ⊗ P x)" ..
    from implC and this have
      "A ⇛ ∃ P ⇛ ∃(λx. A ⊗ P x)" ..
    from conj_import and this show ?thesis ..
  qed

lemma impl_trans: "(A ⇛ B) ⊗ (B ⇛ C) ⇛ A ⇛ C"
proof -
  from conj_import and implB have "(B ⇛ C) ⊗ (A ⇛ B) ⇛ A ⇛ C" ..
  from this show ?thesis by(rule bisub_rule[OF conj_bicomm])
qed

lemma disj_factor: "(A ⇛ B) ⊗ (C ⇛ D) ⇛ A ∨ C ⇛ B ∨ D"
proof -
  from disj_monotone_left have
    "(A ⇛ B) ⊗ (A ∨ C) ⇛ B ∨ C" by (rule bisub_rule[OF conj_bicomm])
  from conj_export and this have
    step1:"(A ⇛ B) ⇛ A ∨ C ⇛ B ∨ C" ..

  from disj_monotone_right have
    "(C ⇛ D) ⊗ (B ∨ C) ⇛ B ∨ D" by (rule bisub_rule[OF conj_bicomm])
  from conj_export and this have
    step2: "(C ⇛ D) ⇛ B ∨ C ⇛ B ∨ D" ..

  from step1 and step2 have
    "(A ⇛ B) ⊗ (C ⇛ D) ⇛ (A ∨ C ⇛ B ∨ C) ⊗ (B ∨ C ⇛ B ∨ D)" by(rule factor_rule)
  from this and impl_trans show ?thesis ..
qed

lemma disj_factor_rule: "A ⇛ B ⟹ C ⇛ D ⟹ A ∨ C ⇛ B ∨ D"
proof -
  assume ab:"A ⇛ B" and cd:"C ⇛ D"
  from ab and cd have "(A ⇛ B) ⊗ (C ⇛ D)" ..
  from disj_factor and this show ?thesis ..
qed

lemma chain_across_conj_left_rule: "A ⇛ B ⟹ B ⊗ C ⇛ D ⟹ A ⊗ C ⇛ D"
proof -
  assume ab:"A ⇛ B" and bcd:"B ⊗ C ⇛ D"
  from ab have "A ⊗ C ⇛ B ⊗ C" by(rule conj_monotone_left_rule)
  from this and bcd show ?thesis..
qed

lemma chain_across_conj_right_rule: "A ⇛ B ⟹ C ⊗ B ⇛ D ⟹ C ⊗ A ⇛ D"
proof -
  assume ab:"A ⇛ B" and cbd:"C ⊗ B ⇛ D"
  from ab have "C ⊗ A ⇛ C ⊗ B" by(rule conj_monotone_right_rule)
  from this and cbd show ?thesis..
qed

lemma reductio: "(A ⇛ ¬A) ⇛ ¬A"
  proof -
    from impl_disj_left and implI have
    "(A ⇛ ¬A) ⇛ A ∨ ¬A ⇛ ¬A" ..
    from this and lem show ?thesis ..
  qed

lemma consequentia_mirabilis: "(¬A ⇛ A) ⇛ A"
  proof -
    from dn_bi' and reductio show "(¬A ⇛ A) ⇛ A"
      by(rule bisub_rule)
  qed

lemma reductio_contraction: "(A ⊗ A ⇛ ¬A) ⇛ A ⇛ ¬A"
  proof -
    from reductio and conj_export show ?thesis
      by(rule impl_link_121)
  qed

lemma reductio_contraction_3: "(A ⊗ A ⊗ A ⇛ ¬A) ⇛ A ⇛ ¬A"
  proof -
    from reductio and conj_export have
      "((A ⊗ A) ⊗ A ⇛ ¬A) ⇛ A ⊗ A ⇛ ¬A"
      by(rule impl_link_121)
    from conj_biass and this have
      "(A ⊗ A ⊗ A ⇛ ¬A) ⇛ A ⊗ A ⇛ ¬A"
      by(rule bisub_rule')
    from this and reductio_contraction show ?thesis ..
  qed

lemma efq_impl: "⊥ ⇛ A"
  proof -
    from entl_impl and efq_entl show ?thesis ..
  qed

lemma falsum_reductio: "(A ⇛ ⊥) ⇛ ¬A"
  proof -
    from implB and efq_impl have "(A ⇛ ⊥) ⇛ A ⇛ ¬A" ..
    from this and reductio show ?thesis ..
  qed

lemma falsum_ds: "A ⊗ ((A ⇛ ⊥) ∨ B) ⇛ B"
  proof -
    from implB and efq_impl have
      "(A ⇛ ⊥) ⇛ A ⇛ B" ..
    from implC and this have
      step1:"A ⇛ (A ⇛ ⊥) ⇛ B" ..

    from impl_disj_left and implI have
      "((A ⇛ ⊥) ⇛ B) ⇛ (A ⇛ ⊥) ∨ B ⇛ B" ..
    from step1 and this have
      "A ⇛ (A ⇛ ⊥) ∨ B ⇛ B" ..
    from conj_import and this show ?thesis ..
  qed

lemma falsum_antilogism: "(A ⊗ B ⇛ ⊥) ⇛ A ⇛ ¬B"
  proof -
    from falsum_reductio and conj_export show ?thesis
      by(rule impl_link_121)
  qed

lemma identity_contracts: "x = y ⇛ x = y ⊗ x = y"
  proof -
    from refl and refl have "x = x ⊗ x = x" ..
    from equals_sub_impl and this show ?thesis by(rule entl_mp_under_impl)
  qed

lemma bisub_impl_oneway: "A ↔ B ⇛ (a A) → (a B)"
  proof -
    from bisub_impl and impl_cel show ?thesis
      unfolding bientl_def ..
  qed

lemma bientailments_contract: "A ↔ B ⇛ (A ↔ B) ⊗ (A ↔ B)"
  proof -
    from entlI and entlI have "A ↔ A"
      unfolding bientl_def ..
    from this and this have "(A ↔ A) ⊗ (A ↔ A)" ..
    from bisub_impl_oneway and this show ?thesis by (rule entl_mp_under_impl)
  qed

lemma nonselfidentity_nonidentity: "x ≠ x ⇛ x ≠ y"
  proof -
    from equals_sub_impl and entl_impl have
      "x = y ⇛ x ≠ x ⇛ x ≠ y" ..
    from implC and this have
      "x ≠ x ⇛ x = y ⇛ x ≠ y" ..
    from this and reductio show ?thesis ..
  qed

lemma eq_sym_impl: "x = y ⇛ y = x"
  proof -
    from equals_sub_impl and entl_impl have
      "x = y ⇛ x = x ⇛ y = x" ..
    from implC and this have
      "x = x ⇛ x = y ⇛ y = x" ..
    from this and refl show ?thesis ..
  qed

lemma eq_trans: "x = y ⊗ y = z ⇛ x = z"
  proof -
    from equals_sub_impl and entl_impl have 
      "y = x ⇛ y = z ⇛ x = z" ..
    from eq_sym_impl and this have
      "x = y ⇛ y = z ⇛ x = z" ..
    from conj_import and this show ?thesis ..
  qed

lemmas o_equivI = equal_intr_rule[
    where phi=‹PROP (Is_theorem p)› and psi=‹PROP (Is_theorem q)› for p q]

lemma bientl_equiv_in_context:
  assumes ab: ‹A ↔ B›
  shows ‹(Is_theorem (p A) ≡ Is_theorem (p B))›
proof -
  have ‹p A ⟹ p B›
    by(rule bisub_rule[OF ab])
  moreover have ‹p B ⟹ p A›
    by(rule bisub_rule'[OF ab])
  ultimately show ‹PROP ?thesis›
    by (rule o_equivI)
qed


lemmas conj_assoc_in_context = bisub_rule[OF conj_biass]
lemmas conj_assoc_in_context2 = bisub_rule'[OF conj_biass]
lemmas conj_comm_in_context = bisub_rule[OF conj_bicomm]

lemma conj_left_comm_in_context:
  ‹p (A ⊗ (B ⊗ C)) ⟹ p (B ⊗ (A ⊗ C))›
  apply (rule bisub_rule[OF conj_biass', of _ B A C])
  apply (rule conj_comm_in_context[of _ A B])
  apply (rule conj_assoc_in_context)
  apply assumption
  done


lemmas disj_assoc_in_context = bisub_rule[OF disj_biass]
lemmas disj_assoc_in_context2 = bisub_rule'[OF disj_biass]
lemmas disj_comm_in_context = bisub_rule[OF disj_bicomm]

lemma disj_left_comm_in_context:
  ‹p (A ∨ (B ∨ C)) ⟹ p (B ∨ (A ∨ C))›
  apply (rule bisub_rule[OF bientl_sym_rule[OF disj_biass], of _ B A C])
  apply (rule disj_comm_in_context[of _ A B])
  apply (rule disj_assoc_in_context)
  apply assumption
  done

lemma strip_dn_in_context:
  ‹p A ⟹ p (¬¬A)›
  apply (rule bisub_rule[OF dn_bi, of _ A])
  apply assumption
  done

lemma strip_dn_in_context2:
  ‹p (¬¬A) ⟹ p A›
  apply (rule bisub_rule'[OF dn_bi, of _ A])
  apply assumption
  done

lemma conj_left_comm:
  ‹(A ⊗ (B ⊗ C)) ↔ (B ⊗ (A ⊗ C))›
  apply (rule bisub_rule[OF conj_biass', of _ B A C])
  apply (rule bisub_rule[OF conj_bicomm, of _ A B])
  apply (rule bisub_rule[OF conj_biass, of _ A B C])
  apply (rule bientlI)
  done

lemmas disj_biass' = bientl_sym_rule[OF disj_biass]

lemma disj_left_comm:
  ‹(A ∨ (B ∨ C)) ↔ (B ∨ (A ∨ C))›
  apply (rule bisub_rule[OF disj_biass', of _ B A C])
  apply (rule bisub_rule[OF disj_bicomm, of _ A B])
  apply (rule bisub_rule[OF disj_biass, of _ A B])
  apply (rule bientlI)
  done

lemmas conj_assoc_in_context3 = bientl_equiv_in_context[OF conj_biass]
lemmas conj_comm_in_context3 = bientl_equiv_in_context[OF conj_bicomm]
lemmas conj_left_comm_in_context3 = bientl_equiv_in_context[OF conj_left_comm]

lemmas disj_assoc_in_context3 = bientl_equiv_in_context[OF disj_biass]
lemmas disj_comm_in_context3 = bientl_equiv_in_context[OF disj_bicomm]
lemmas disj_left_comm_in_context3 = bientl_equiv_in_context[OF disj_left_comm]

lemmas bientl_comm_in_context3 = bientl_equiv_in_context[OF bientl_comm_bientl]
lemmas dnbi_in_context3 = bientl_equiv_in_context[OF bientl_sym_rule[OF bientl_sym_rule[OF dn_bi]]]

end
