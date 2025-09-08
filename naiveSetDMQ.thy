(* Title: naiveSetDMQ.thy
   Author: Ellie Ripley, https://negation.rocks
*)


section \<open>Naive set theory in subDMQ\<close>

theory naiveSetDMQ
  imports subDMQ
begin

subsection \<open>Axioms\<close>

axiomatization
        member ::        "i ⇒ i ⇒ o" (infix "∈" 75)
    and strong_set_of :: "(i ⇒ i ⇒ o) ⇒ i" ("{{_}}" [80] 80)
  where strong_abstraction: "x ∈ {{P}} ↔ P(x)({{P}})"
    and extensionality:     "∀(λz. z ∈ x ↔ z ∈ y) ↔ x = y"

definition set_of :: "(i ⇒ o) ⇒ i" ("{_}" [80] 80)
  where "{P} ≡ {{(λx y. P(x))}}"

definition singleton :: "i ⇒ i" ("{!_}" [80] 80)
  where "{!x} ≡ {(λy. y = x)}"

abbreviation not_member :: "i ⇒ i ⇒ o" (infix "∉" 75)
  where "x ∉ y ≡ ¬(x ∈ y)"

lemma abstraction: "x ∈ {P} ↔ P(x)"
  unfolding set_of_def
  proof -
    show "x ∈ {{(λy . λz. P(y))}} ↔ (λy z. P(y))(x)({{(λy z. P(y))}})"
      by(rule strong_abstraction)
  qed

lemma abstraction': "P(x) ↔ x ∈ {P}"
  proof -
    from abstraction show "P(x) ↔ x ∈ {P}"
      by(rule bientl_sym_rule)
  qed

lemma strong_comprehension: "∃(λx. ∀(λy. y ∈ x ↔ P(y)(x)))"
  proof -
    from strong_abstraction have
      "∀(λy. y ∈ {{P}} ↔ P(y)({{P}}))" ..
    from this show ?thesis ..
  qed

lemma comprehension: "∃(λx. ∀(λy. y ∈ x ↔ P(y)))"
  proof -
    from abstraction have
      "∀(λy. y ∈ {P} ↔ P(y))" ..
    from this show ?thesis ..
  qed

lemma blv_aux_ltr: "∀(λx. x ∈ {P} ↔ x ∈ {Q}) ⇛ ∀(λz. P(z) ↔ Q(z))"
  proof -
    {
    fix z
    from abstraction have
      "(z ∈ {P} ↔ z ∈ {Q}) ↔ (P(z) ↔ z ∈ {Q})"
      by(rule bisub)
    then have
      step2:"(z ∈ {P} ↔ z ∈ {Q}) ↔ (P(z) ↔ Q(z))"
      using abstraction
      by(rule bisub_rule[rotated])
    from entl_impl and entl_ui have
      "∀(λx. x ∈ {P} ↔ x ∈ {Q}) ⇛ (z ∈ {P} ↔ z ∈ {Q})" ..
    from step2 and this have
      "∀(λx. x ∈ {P} ↔ x ∈ {Q}) ⇛ (P(z) ↔ Q(z))"
      by(rule bisub_rule)
    }
    have "⋀ z. (∀(λx. x ∈ {P} ↔ x ∈ {Q}) ⇛ (P(z) ↔ Q(z)))" by fact
    from this have
      "∀(λz. ∀(λx. x ∈ {P} ↔ x ∈ {Q}) ⇛ (P(z) ↔ Q(z)))" ..
    from all_cons and this show
      "∀(λx. x ∈ {P} ↔ x ∈ {Q}) ⇛ ∀(λz. P(z) ↔ Q(z))" ..
  qed

lemma blv_aux_rtl: "∀(λz. P(z) ↔ Q(z)) ⇛ ∀(λx. x ∈ {P} ↔ x ∈ {Q})"
  proof -
   {
   fix x
   from abstraction' have
     "(P(x) ↔ Q(x)) ↔ (x ∈ {P} ↔ Q(x))"
     by(rule bisub)
   from abstraction' and this have
     step2:"(P(x) ↔ Q(x)) ↔ (x ∈ {P} ↔ x ∈ {Q})"
     by(rule bisub_rule)
   have "∀(λz. P(z) ↔ Q(z)) → (P(x) ↔ Q(x))"
     by(rule entl_ui)
   from step2 and this have
     "∀(λz. P(z) ↔ Q(z)) → (x ∈ {P} ↔ x ∈ {Q})"
     by(rule bisub_rule)
   from entl_impl and this have
     "∀(λz. P(z) ↔ Q(z)) ⇛ (x ∈ {P} ↔ x ∈ {Q})" ..
   }
    have "⋀ x. (∀(λz. P(z) ↔ Q(z)) ⇛ (x ∈ {P} ↔ x ∈ {Q}))" by fact
   from this have
     "∀(λx. ∀(λz. P(z) ↔ Q(z)) ⇛ (x ∈ {P} ↔ x ∈ {Q}))" ..
   from all_cons and this show
     "∀(λz. P(z) ↔ Q(z)) ⇛ ∀(λx. x ∈ {P} ↔ x ∈ {Q})" ..
  qed

lemma basic_law_V_ltr: "{P} = {Q} ⇛ ∀(λx. P(x) ↔ Q(x))"
  proof -
    from entl_cer and extensionality
      have "{P} = {Q} → ∀(λz. z ∈ {P} ↔ z ∈ {Q})"
      unfolding bientl_def ..
    from entl_impl and this
      have "{P} = {Q} ⇛ ∀(λz. z ∈ {P} ↔ z ∈ {Q})" ..
    from this and blv_aux_ltr
      show "{P} = {Q} ⇛ ∀(λx. P(x) ↔ Q(x))" ..
  qed

lemma basic_law_V_rtl: "∀(λx. P(x) ↔ Q(x)) ⇛ {P} = {Q}"
  proof -
    from extensionality
      have "∀(λx. x ∈ {P} ↔ x ∈ {Q}) → {P} = {Q}"
      unfolding bientl_def ..
    from entl_impl and this
      have "∀(λx. x ∈ {P} ↔ x ∈ {Q}) ⇛ {P} = {Q}" ..
    from blv_aux_rtl and this show
      "∀(λx. P(x) ↔ Q(x)) ⇛ {P} = {Q}" ..
  qed

lemma refl_without_refl: "x = x"
  proof -
    from bientlI have
      "∀(λy. y ∈ x ↔ y ∈ x)" ..
    from extensionality and this show "x = x" ..
  qed

lemma eq_sym_bientl: "x = y ↔ y = x"
  proof -
    from bientl_comm_bientl have
      "∀(λz. z ∈ x ↔ z ∈ y) ↔ ∀(λz. z ∈ y ↔ z ∈ x)"
      by(rule bisub_open)
    from this and extensionality have
      "∀(λz. z ∈ y ↔ z ∈ x) ↔ x = y"
      by(rule bisub_rule)
    from this and extensionality show ?thesis
      by(rule bisub_rule)
  qed

lemma equals_sub_rule': "x = y ⟹ P(y) ⟹ P(x)"
  proof -
    assume xy:"x = y" and py:"P(y)"
    from eq_sym_bientl and xy have "y = x" by(rule bisub_rule)
    from this and py show "P(x)" by(rule equals_sub_rule)
  qed

definition subset :: "i ⇒ i ⇒ o" (infix "⊆" 75)
  where "x ⊆ y ≡ ∀(λz. z ∈ x → z ∈ y)"

lemma subset_refl: "x ⊆ x"
  unfolding subset_def
  proof -
    from entlI show "∀(λz. z ∈ x → z ∈ x)" ..
  qed

lemma subset_antisym: "x ⊆ y ⊗ y ⊆ x ⇛ x = y"
  proof -
    {
    fix z
    from entl_impl and entl_ui have fac1:"x ⊆ y ⇛ (z ∈ x → z ∈ y)"
      unfolding subset_def ..
    from entl_impl and entl_ui have "y ⊆ x ⇛ (z ∈ y → z ∈ x)"
      unfolding subset_def ..
    from fac1 and this have
      "x ⊆ y ⊗ y ⊆ x ⇛ (z ∈ x → z ∈ y) ⊗ (z ∈ y → z ∈ x)"
      by(rule factor_rule)
    from this have
      "x ⊆ y ⊗ y ⊆ x ⇛ (z ∈ x ↔ z ∈ y)"
      by(fold bientl_def)
    }
    have "⋀ z. (x ⊆ y ⊗ y ⊆ x ⇛ (z ∈ x ↔ z ∈ y))" by fact
    from this have
      "∀(λz. x ⊆ y ⊗ y ⊆ x ⇛ (z ∈ x ↔ z ∈ y))" ..
    from all_cons and this have
      "x ⊆ y ⊗ y ⊆ x ⇛ ∀(λz. z ∈ x ↔ z ∈ y)" ..
    from extensionality and this show "x ⊆ y ⊗ y ⊆ x ⇛ x = y"
      by(rule bisub_rule)
  qed

lemma subset_trans: "x ⊆ y ⊗ y ⊆ z ⇛ x ⊆ z"
  proof -
    {
    fix w
    from entl_impl and entl_ui have fac1:"x ⊆ y ⇛ (w ∈ x → w ∈ y)"
      unfolding subset_def ..
    from entl_impl and entl_ui have "y ⊆ z ⇛ (w ∈ y → w ∈ z)"
      unfolding subset_def ..
    from fac1 and this have
      step1:"x ⊆ y ⊗ y ⊆ z ⇛ (w ∈ x → w ∈ y) ⊗ (w ∈ y → w ∈ z)"
      by(rule factor_rule)
    from entl_impl and entl_cs have
      "(w ∈ x → w ∈ y) ⊗ (w ∈ y → w ∈ z) ⇛ (w ∈ x → w ∈ z)" ..
    from step1 and this have
      "x ⊆ y ⊗ y ⊆ z ⇛ (w ∈ x → w ∈ z)" ..
    }
    have "⋀ w. (x ⊆ y ⊗ y ⊆ z ⇛ (w ∈ x → w ∈ z))" by fact
    from this have
      "∀(λw. x ⊆ y ⊗ y ⊆ z ⇛ (w ∈ x → w ∈ z))" ..
    from all_cons and this have
      "x ⊆ y ⊗ y ⊆ z ⇛ ∀(λw. w ∈ x → w ∈ z)" ..
    from this show "x ⊆ y ⊗ y ⊆ z ⇛ x ⊆ z"
      by(fold subset_def)
  qed

lemma subset_contra_entl: "x ⊆ y → z ∉ y → z ∉ x"
  proof -
    from abstraction and entlI have
      "x ⊆ y → ∀(λz. z ∈ x → z ∈ y)"
      unfolding subset_def
      by(rule bisub_rule)
    from this and entl_ui have
      "x ⊆ y → z ∈ x → z ∈ y" ..
    from this and entl_contra show ?thesis ..
  qed

lemma subset_extensionality_ltr: "∀(λz. (z ⊆ x ⇛ z ⊆ y) ⊗ (z ⊆ y ⇛ z ⊆ x)) ⇛ x = y"
  proof -
    from entl_impl and entl_ui have "∀(λz. z ⊆ x ⇛ z ⊆ y) ⇛ x ⊆ x ⇛ x ⊆ y" ..
    from this and subset_refl have fac1:"∀(λz. z ⊆ x ⇛ z ⊆ y) ⇛ x ⊆ y" ..
    from entl_impl and entl_ui have "∀(λz. z ⊆ y ⇛ z ⊆ x) ⇛ y ⊆ y ⇛ y ⊆ x" ..
    from this and subset_refl have "∀(λz. z ⊆ y ⇛ z ⊆ x) ⇛ y ⊆ x" ..
    from fac1 and this have
      "∀(λz. z ⊆ x ⇛ z ⊆ y) ⊗ ∀(λz. z ⊆ y ⇛ z ⊆ x) ⇛ x ⊆ y ⊗ y ⊆ x"
      by(rule factor_rule)
    from this and subset_antisym have
      "∀(λz. z ⊆ x ⇛ z ⊆ y) ⊗ ∀(λz. z ⊆ y ⇛ z ⊆ x) ⇛ x = y" ..
    from all_conj_dist and this show
      "∀(λz. (z ⊆ x ⇛ z ⊆ y) ⊗ (z ⊆ y ⇛ z ⊆ x)) ⇛ x = y" ..
  qed

lemma sub_ext_rtl_aux: "(v ∈ x → v ∈ y) ⇛ z ⊆ x ⇛ (v ∈ z → v ∈ y)"
  proof -
    from entl_impl and entl_cs have
        "(v ∈ z → v ∈ x) ⊗ (v ∈ x → v ∈ y) ⇛ (v ∈ z → v ∈ y)" ..
    from conj_export and this have
        fac1a:"(v ∈ z → v ∈ x) ⇛ (v ∈ x → v ∈ y) ⇛ (v ∈ z → v ∈ y)" ..
    from entl_impl and entl_ui have
        "∀(λu. u ∈ z → u ∈ x) ⇛ (v ∈ z → v ∈ x)" ..
    from this have
        "z ⊆ x ⇛ (v ∈ z → v ∈ x)"
        by(fold subset_def)
    from this and fac1a have
        "z ⊆ x ⇛ (v ∈ x → v ∈ y) ⇛ (v ∈ z → v ∈ y)" ..
    from implC and this show
        "(v ∈ x → v ∈ y) ⇛ z ⊆ x ⇛ (v ∈ z → v ∈ y)" ..
  qed

lemma subset_extensionality_rtl: "x = y ⇛ ∀(λz. (z ⊆ x ⇛ z ⊆ y) ⊗ (z ⊆ y ⇛ z ⊆ x))"
  proof -
    {
    fix z
      from extensionality have
        "x = y → ∀(λw. w ∈ x ↔ w ∈ y)"
        unfolding bientl_def ..
      from entl_impl and this have
        step1:"x = y ⇛ ∀(λw. w ∈ x ↔ w ∈ y)" ..
      {
      fix v
        from sub_ext_rtl_aux and sub_ext_rtl_aux have
          "(v ∈ x → v ∈ y) ⊗ (v ∈ y → v ∈ x)
                ⇛ (z ⊆ x ⇛ (v ∈ z → v ∈ y)) ⊗ (z ⊆ y ⇛ (v ∈ z → v ∈ x))"
          by(rule factor_rule)
        from this have
          step2:"(v ∈ x ↔ v ∈ y) ⇛ (z ⊆ x ⇛ (v ∈ z → v ∈ y)) ⊗ (z ⊆ y ⇛ (v ∈ z → v ∈ x))"
          by(fold bientl_def)
        from entl_impl and entl_ui have
          "∀(λw. w ∈ x ↔ w ∈ y) ⇛ (v ∈ x ↔ v ∈ y)" ..
        from this and step2 have
          "∀(λw. w ∈ x ↔ w ∈ y) ⇛ (z ⊆ x ⇛ (v ∈ z → v ∈ y)) ⊗ (z ⊆ y ⇛ (v ∈ z → v ∈ x))" ..
        from step1 and this have
          "x = y ⇛ (z ⊆ x ⇛ (v ∈ z → v ∈ y)) ⊗ (z ⊆ y ⇛ (v ∈ z → v ∈ x))" ..
      }
      have "⋀ v. (x = y ⇛ (z ⊆ x ⇛ (v ∈ z → v ∈ y)) ⊗ (z ⊆ y ⇛ (v ∈ z → v ∈ x)))" by fact
      from this have
        "∀(λv. x = y ⇛ (z ⊆ x ⇛ (v ∈ z → v ∈ y)) ⊗ (z ⊆ y ⇛ (v ∈ z → v ∈ x)))" ..
      from all_cons and this have
        "x = y ⇛ ∀(λv. (z ⊆ x ⇛ (v ∈ z → v ∈ y)) ⊗ (z ⊆ y ⇛ (v ∈ z → v ∈ x)))" ..
      from this and all_conj_dist have
        step3:"x = y ⇛ ∀(λv. z ⊆ x ⇛ (v ∈ z → v ∈ y)) ⊗ ∀(λv. z ⊆ y ⇛ (v ∈ z → v ∈ x))" ..

      from all_cons and all_cons have
        "∀(λv. z ⊆ x ⇛ (v ∈ z → v ∈ y)) ⊗ ∀(λv. z ⊆ y ⇛ (v ∈ z → v ∈ x))
                ⇛ (z ⊆ x ⇛ ∀(λv. v ∈ z → v ∈ y)) ⊗ (z ⊆ y ⇛ ∀(λv. v ∈ z → v ∈ x))"
        by(rule factor_rule)
      from this have
        "∀(λv. z ⊆ x ⇛ (v ∈ z → v ∈ y)) ⊗ ∀(λv. z ⊆ y ⇛ (v ∈ z → v ∈ x))
                ⇛ (z ⊆ x ⇛ z ⊆ y) ⊗ (z ⊆ y ⇛ z ⊆ x)"
      by(fold subset_def)
      from step3 and this have
        "x = y ⇛ (z ⊆ x ⇛ z ⊆ y) ⊗ (z ⊆ y ⇛ z ⊆ x)" ..
    }
    have "⋀ z. (x = y ⇛ (z ⊆ x ⇛ z ⊆ y) ⊗ (z ⊆ y ⇛ z ⊆ x))" by fact
    from this have
      "∀(λz. x = y ⇛ (z ⊆ x ⇛ z ⊆ y) ⊗ (z ⊆ y ⇛ z ⊆ x))" ..
    from all_cons and this show
      "x = y ⇛ ∀(λz. (z ⊆ x ⇛ z ⊆ y) ⊗ (z ⊆ y ⇛ z ⊆ x))" ..
  qed

lemma leibniz_law_rtl: "∀(λz. x ∈ z ↔ y ∈ z) ⇛ x = y"
  proof -
    from entl_impl and entl_ui have
      step1:"∀(λz. x ∈ z ↔ y ∈ z) ⇛ (x ∈ {(λu. u = y)} ↔ y ∈ {(λu. u = y)})" ..
    from abstraction have
      "(x ∈ {(λu. u = y)} ↔ y ∈ {(λu. u = y)}) ↔ (x = y ↔ y ∈ {(λu. u = y)})"
      by(rule bisub)
    from abstraction and this have
      "(x ∈ {(λu. u = y)} ↔ y ∈ {(λu. u = y)}) ↔ (x = y ↔ y = y)"
      by(rule bisub_rule)
    from this and step1 have
      "∀(λz. x ∈ z ↔ y ∈ z) ⇛ (x = y ↔ y = y)"
      by(rule bisub_rule)
    from this and impl_cer have
      "∀(λz. x ∈ z ↔ y ∈ z) ⇛ (y = y → x = y)"
      unfolding bientl_def ..
    from this and entl_impl have
      "∀(λz. x ∈ z ↔ y ∈ z) ⇛ y = y ⇛ x = y" ..
    from this and refl_without_refl show
      "∀(λz. x ∈ z ↔ y ∈ z) ⇛ x = y" ..
  qed

lemma leibniz_law_ltr: "x = y ⇛ ∀(λz. x ∈ z ↔ y ∈ z)"
  proof -
    {
    fix z
    from entlI and entlI have "x ∈ z ↔ x ∈ z"
      unfolding bientl_def ..
    }
    have "⋀ z. (x ∈ z ↔ x ∈ z)" by fact
    from this have "∀(λz. x ∈ z ↔ x ∈ z)" ..
    from equals_sub_impl and this show ?thesis
      by(rule entl_mp_under_impl)
  qed

definition epart :: "i ⇒ i ⇒ o" (infix "⊑" 75)
  where "x ⊑ y ≡ ∀(λz. z ∈ x ⇛ z ∈ y)"

definition eequiv :: "i ⇒ i ⇒ o" (infix "≃" 75)
  where "x ≃ y ≡ ∀(λz. (z ∈ x ⇛ z ∈ y) ⊗ (z ∈ y ⇛ z ∈ x))"

lemma epart_refl: "x ⊑ x"
  proof -
    from implI show "x ⊑ x"
      unfolding epart_def ..
  qed

lemma epart_antisym: "x ⊑ y ⊗ y ⊑ x ⇛ x ≃ y"
  proof -
    {
    fix w
      from entl_impl and entl_ui have
        step1:"x ⊑ y ⇛ w ∈ x ⇛ w ∈ y"
        unfolding epart_def ..
      from entl_impl and entl_ui have
        "y ⊑ x ⇛ w ∈ y ⇛ w ∈ x"
        unfolding epart_def ..
      from step1 and this have
        "x ⊑ y ⊗ y ⊑ x ⇛ (w ∈ x ⇛ w ∈ y) ⊗ (w ∈ y ⇛ w ∈ x)"
        by(rule factor_rule)
    }
    have "⋀ w. (x ⊑ y ⊗ y ⊑ x ⇛ (w ∈ x ⇛ w ∈ y) ⊗ (w ∈ y ⇛ w ∈ x))" by fact
    from this have
      "∀(λw. x ⊑ y ⊗ y ⊑ x ⇛ (w ∈ x ⇛ w ∈ y) ⊗ (w ∈ y ⇛ w ∈ x))" ..
    from all_cons and this show
      "x ⊑ y ⊗ y ⊑ x ⇛ x ≃ y"
      unfolding eequiv_def ..
  qed

lemma epart_trans: "x ⊑ y ⊗ y ⊑ z ⇛ x ⊑ z"
  proof -
    {
    fix w
      from entl_impl and entl_ui have
        step1:"x ⊑ y ⇛ w ∈ x ⇛ w ∈ y"
        unfolding epart_def ..
      from entl_impl and entl_ui have
        "y ⊑ z ⇛ w ∈ y ⇛ w ∈ z"
        unfolding epart_def ..
      from step1 and this have
        step2:"x ⊑ y ⊗ y ⊑ z ⇛ (w ∈ x ⇛ w ∈ y) ⊗ (w ∈ y ⇛ w ∈ z)"
        by(rule factor_rule)
      from conj_import and implB' have
        "(w ∈ x ⇛ w ∈ y) ⊗ (w ∈ y ⇛ w ∈ z) ⇛ w ∈ x ⇛ w ∈ z" ..
      from step2 and this have
        "x ⊑ y ⊗ y ⊑ z ⇛ w ∈ x ⇛ w ∈ z" ..
    }
    have "⋀ w. (x ⊑ y ⊗ y ⊑ z ⇛ w ∈ x ⇛ w ∈ z)" by fact
    from this have
      "∀(λw. x ⊑ y ⊗ y ⊑ z ⇛ w ∈ x ⇛ w ∈ z)" ..
    from all_cons and this show
      "x ⊑ y ⊗ y ⊑ z ⇛ x ⊑ z"
      unfolding epart_def ..
  qed

lemma subset_epart: "x ⊆ y ⇛ x ⊑ y"
  proof -
    {
    fix w
    from entl_impl and entl_ui have
      "x ⊆ y ⇛ (w ∈ x → w ∈ y)"
      unfolding subset_def ..
    from this and entl_impl have
      "x ⊆ y ⇛ w ∈ x ⇛ w ∈ y" ..
    }
    have "⋀ w. (x ⊆ y ⇛ w ∈ x ⇛ w ∈ y)" by fact
    from this have
      "∀(λw. x ⊆ y ⇛ w ∈ x ⇛ w ∈ y)" ..
    from all_cons and this show
      "x ⊆ y ⇛ x ⊑ y"
      unfolding epart_def ..
  qed

lemma eequiv_refl: "x ≃ x"
  proof -
    {
    fix z
      from implI and implI have "(z ∈ x ⇛ z ∈ x) ⊗ (z ∈ x ⇛ z ∈ x)" ..
    }
    have "⋀ z. ((z ∈ x ⇛ z ∈ x) ⊗ (z ∈ x ⇛ z ∈ x))" by fact
    from this show "x ≃ x"
      unfolding eequiv_def ..
  qed

lemma eequiv_sym: "x ≃ y ⇛ y ≃ x"
  proof -
    {
    fix z
      from entl_impl and entl_ui have
        "∀(λw. (w ∈ x ⇛ w ∈ y) ⊗ (w ∈ y ⇛ w ∈ x)) ⇛ (z ∈ x ⇛ z ∈ y) ⊗ (z ∈ y ⇛ z ∈ x)" ..
      from this have "x ≃ y ⇛ (z ∈ x ⇛ z ∈ y) ⊗ (z ∈ y ⇛ z ∈ x)"
        by(fold eequiv_def)
      from conj_bicomm and this have
        "x ≃ y ⇛ (z ∈ y ⇛ z ∈ x) ⊗ (z ∈ x ⇛ z ∈ y)"
        by(rule bisub_rule)
    } 
    have "⋀ z. (x ≃ y ⇛ (z ∈ y ⇛ z ∈ x) ⊗ (z ∈ x ⇛ z ∈ y))" by fact
    from this have
      "∀(λz. x ≃ y ⇛ (z ∈ y ⇛ z ∈ x) ⊗ (z ∈ x ⇛ z ∈ y))" ..
    from all_cons and this show
      "x ≃ y ⇛ y ≃ x"
      unfolding eequiv_def ..
  qed

lemma eequiv_eparts: "x ≃ y ⇛ x ⊑ y ⊗ y ⊑ x"
  proof -
    {
    fix z
      from entl_impl and entl_ui have
        "∀(λw. (w ∈ x ⇛ w ∈ y) ⊗ (w ∈ y ⇛ w ∈ x)) ⇛ (z ∈ x ⇛ z ∈ y) ⊗ (z ∈ y ⇛ z ∈ x)" ..
      from this have
        "x ≃ y ⇛ (z ∈ x ⇛ z ∈ y) ⊗ (z ∈ y ⇛ z ∈ x)"
        by(fold eequiv_def)
    }
    have "⋀ z. (x ≃ y ⇛ (z ∈ x ⇛ z ∈ y) ⊗ (z ∈ y ⇛ z ∈ x))" by fact
    from this have
        "∀(λz. x ≃ y ⇛ (z ∈ x ⇛ z ∈ y) ⊗ (z ∈ y ⇛ z ∈ x))" ..
    from all_cons and this have
      "x ≃ y ⇛ ∀(λz. (z ∈ x ⇛ z ∈ y) ⊗ (z ∈ y ⇛ z ∈ x))" ..
    from this and all_conj_dist show
      "x ≃ y ⇛ x ⊑ y ⊗ y ⊑ x"
      unfolding epart_def ..
  qed

lemma eequiv_trans: "x ≃ y ⊗ y ≃ z ⇛ x ≃ z"
  proof -
    from eequiv_eparts and eequiv_eparts have
      step1:"x ≃ y ⊗ y ≃ z ⇛ (x ⊑ y ⊗ y ⊑ x) ⊗ (y ⊑ z ⊗ z ⊑ y)"
      by(rule factor_rule)

    from epart_trans and epart_trans have
      "(x ⊑ y ⊗ y ⊑ z) ⊗ (z ⊑ y ⊗ y ⊑ x) ⇛ x ⊑ z ⊗ z ⊑ x"
      by(rule factor_rule)
    from this and epart_antisym have
      step2:"(x ⊑ y ⊗ y ⊑ z) ⊗ (z ⊑ y ⊗ y ⊑ x) ⇛ x ≃ z" ..

    from conj_bicomm have
      "x ⊑ y ⊗ (y ⊑ x ⊗ (y ⊑ z ⊗ z ⊑ y)) ↔ x ⊑ y ⊗ ((y ⊑ z ⊗ z ⊑ y) ⊗ y ⊑ x)"
      by(rule bisub)
    from conj_biass and this have
      "(x ⊑ y ⊗ y ⊑ x) ⊗ (y ⊑ z ⊗ z ⊑ y) ↔ x ⊑ y ⊗ ((y ⊑ z ⊗ z ⊑ y) ⊗ y ⊑ x)"
      by(rule bisub_rule)
    from conj_biass' and this have
      "(x ⊑ y ⊗ y ⊑ x) ⊗ (y ⊑ z ⊗ z ⊑ y) ↔ x ⊑ y ⊗ (y ⊑ z ⊗ (z ⊑ y ⊗ y ⊑ x))"
      by(rule bisub_rule)
    from this and conj_biass have
      "(x ⊑ y ⊗ y ⊑ x) ⊗ (y ⊑ z ⊗ z ⊑ y) ↔ (x ⊑ y ⊗ y ⊑ z) ⊗ (z ⊑ y ⊗ y ⊑ x)"
      by(rule bientl_trans_rule)

    from this and step1 have
      "x ≃ y ⊗ y ≃ z ⇛ (x ⊑ y ⊗ y ⊑ z) ⊗ (z ⊑ y ⊗ y ⊑ x)"
      by(rule bisub_rule)
    from this and step2 show
      "x ≃ y ⊗ y ≃ z ⇛ x ≃ z" ..
  qed

lemma equals_impl_eequiv: "x = y ⇛ x ≃ y"
  proof -
    from equals_sub_impl and eequiv_refl show ?thesis
      by(rule entl_mp_under_impl)
  qed

definition proper_subset :: "i ⇒ i ⇒ o" (infix "⊂" 75)
  where "x ⊂ y ≡ x ⊆ y ⊗ ∃(λz. z ∈ y ⊗ z ∉ x)"

lemma counterexample_nonsubset: "∃(λz. z ∈ x ⊗ z ∉ y) ⇛ ¬(x ⊆ y)"
  proof -
    {
    fix w
    from entl_contra and entl_ui have
      "¬(w ∈ x → w ∈ y) → ¬(x ⊆ y)"
        unfolding subset_def ..
    from entl_impl and this have
      "¬(w ∈ x → w ∈ y) ⇛ ¬(x ⊆ y)" ..
    from nimpl_nentl and this have
      "¬(w ∈ x ⇛ w ∈ y) ⇛ ¬(x ⊆ y)" ..
    from impl_cex and this have
      "w ∈ x ⊗ w ∉ y ⇛ ¬(x ⊆ y)" ..
    }
    have "⋀ w. (w ∈ x ⊗ w ∉ y ⇛ ¬(x ⊆ y))" by fact
    from this have
      "∀(λz. z ∈ x ⊗ z ∉ y ⇛ ¬(x ⊆ y))" ..
    from all_ante and this show
      "∃(λz. z ∈ x ⊗ z ∉ y) ⇛ ¬(x ⊆ y)" ..
  qed

lemma counterexample_nonidentity: "∃(λz. z ∈ x ⊗ z ∉ y) ⇛ x ≠ y"
  proof -
    {
    fix w
    from entl_contra and entl_ui have
      "¬(w ∈ x → w ∈ y) → ¬∀(λz. z ∈ x → z ∈ y)" ..
    from entl_impl and this have
      "¬(w ∈ x → w ∈ y) ⇛ ¬∀(λz. z ∈ x → z ∈ y)" ..
    from this and impl_na_conj_r have
      "¬(w ∈ x → w ∈ y) ⇛ ¬∀(λz. z ∈ x ↔ z ∈ y)"
      unfolding bientl_def ..
    from extensionality and this have
      "¬(w ∈ x → w ∈ y) ⇛ x ≠ y"
      by(rule bisub_rule)
    from nimpl_nentl and this have
      "¬(w ∈ x ⇛ w ∈ y) ⇛ x ≠ y" ..
    from impl_cex and this have
      "w ∈ x ⊗ w ∉ y ⇛ x ≠ y" ..
    }
    have "⋀ w. (w ∈ x ⊗ w ∉ y ⇛ x ≠ y)" by fact
    from this have
      "∀(λw. w ∈ x ⊗ w ∉ y ⇛ x ≠ y)" ..
    from all_ante and this show
      "∃(λz. z ∈ x ⊗ z ∉ y) ⇛ x ≠ y" ..
  qed

lemma proper_subset_irrefl: "¬(x ⊂ x)"
  proof -
    from lnc have
      "∀(λz. ¬(z ∈ x ⊗ z ∉ x))" ..
    from dni and this have
      step1:"¬¬∀(λz. ¬(z ∈ x ⊗ z ∉ x))" ..

    from entl_contra and dm_sna have
      "¬¬∀(λz. ¬(z ∈ x ⊗ z ∉ x)) → ¬∃(λz. z ∈ x ⊗ z ∉ x)" ..
    from entl_impl and this have
      "¬¬∀(λz. ¬(z ∈ x ⊗ z ∉ x)) ⇛ ¬∃(λz. z ∈ x ⊗ z ∉ x)" ..
    from this and step1 have
      step2:"¬∃(λz. z ∈ x ⊗ z ∉ x)" ..

    from entl_contra and entl_cer have
      "¬∃(λz. z ∈ x ⊗ z ∉ x) → ¬(x ⊆ x ⊗ ∃(λz. z ∈ x ⊗ z ∉ x))" ..
    from this and step2 show
      "¬(x ⊂ x)"
      unfolding proper_subset_def ..
  qed

lemma proper_subset_asymm: "x ⊂ y ⇛ ¬(y ⊂ x)"
  proof -
    have "x ⊂ y ⇛ ∃(λz. z ∈ y ⊗ z ∉ x)"
      unfolding proper_subset_def
        by(rule impl_cer)
    from this and counterexample_nonsubset have
      step1:"x ⊂ y ⇛ ¬(y ⊆ x)" ..

    from entl_contra and entl_cel have
      "¬(y ⊆ x) → ¬(y ⊂ x)"
        unfolding proper_subset_def ..
    from entl_impl and this have
      "¬(y ⊆ x) ⇛ ¬(y ⊂ x)" ..

    from step1 and this show
      "x ⊂ y ⇛ ¬(y ⊂ x)" ..
  qed

lemma proper_subset_kinda_trans_1: "x ⊂ y ⊗ y ⊑ z ⊗ y ⊆ z ⇛ x ⊂ z"
  proof -
    from conj_import and bocardo have
      "∃(λw. w ∈ y ⊗ w ∉ x) ⊗ y ⊑ z ⇛ ∃(λw. w ∈ z ⊗ w ∉ x)"
      unfolding epart_def ..
    from this and subset_trans have
      "(∃(λw. w ∈ y ⊗ w ∉ x) ⊗ y ⊑ z) ⊗ x ⊆ y ⊗ y ⊆ z ⇛ ∃(λw. w ∈ z ⊗ w ∉ x) ⊗ x ⊆ z"
      by(rule factor_rule)
    from conj_bicomm and this have
      "(∃(λw. w ∈ y ⊗ w ∉ x) ⊗ y ⊑ z) ⊗ x ⊆ y ⊗ y ⊆ z ⇛ x ⊂ z"
      unfolding proper_subset_def
      by(rule bisub_rule)
    from conj_biass and this have
      "∃(λw. w ∈ y ⊗ w ∉ x) ⊗ y ⊑ z ⊗ x ⊆ y ⊗ y ⊆ z ⇛ x ⊂ z"
      by(rule bisub_rule')
    from conj_biass and this have
      "∃(λw. w ∈ y ⊗ w ∉ x) ⊗ (y ⊑ z ⊗ x ⊆ y) ⊗ y ⊆ z ⇛ x ⊂ z"
      by(rule bisub_rule)
    from conj_bicomm and this have
      "∃(λw. w ∈ y ⊗ w ∉ x) ⊗ (x ⊆ y ⊗ y ⊑ z) ⊗ y ⊆ z ⇛ x ⊂ z"
      by(rule bisub_rule)
    from conj_biass and this have
      "∃(λw. w ∈ y ⊗ w ∉ x) ⊗ x ⊆ y ⊗ y ⊑ z ⊗ y ⊆ z ⇛ x ⊂ z"
      by(rule bisub_rule')
    from conj_biass and this have
      "(∃(λw. w ∈ y ⊗ w ∉ x) ⊗ x ⊆ y) ⊗ y ⊑ z ⊗ y ⊆ z ⇛ x ⊂ z"
      by(rule bisub_rule)
    from conj_bicomm and this show ?thesis
      unfolding proper_subset_def
      by(rule bisub_rule)
  qed

lemma proper_subset_kinda_trans_2: "x ⊆ y ⊗ x ⊆ y ⊗ y ⊂ z ⇛ x ⊂ z"
  proof -
    from conj_import and baroco have
      "x ⊆ y ⊗ ∃(λw. w ∈ z ⊗ w ∉ y) ⇛ ∃(λw. w ∈ z ⊗ w ∉ x)"
      unfolding subset_def ..
    from this and subset_trans have
      "(x ⊆ y ⊗ ∃(λw. w ∈ z ⊗ w ∉ y)) ⊗ x ⊆ y ⊗ y ⊆ z ⇛ ∃(λw. w ∈ z ⊗ w ∉ x) ⊗ x ⊆ z"
      by(rule factor_rule)
    from conj_bicomm and this have
      "(x ⊆ y ⊗ ∃(λw. w ∈ z ⊗ w ∉ y)) ⊗ x ⊆ y ⊗ y ⊆ z ⇛ x ⊂ z"
      unfolding proper_subset_def
      by(rule bisub_rule)
    from conj_biass and this have
      "x ⊆ y ⊗ ∃(λw. w ∈ z ⊗ w ∉ y) ⊗ x ⊆ y ⊗ y ⊆ z ⇛ x ⊂ z"
      by(rule bisub_rule')
    from conj_biass and this have
      "x ⊆ y ⊗ (∃(λw. w ∈ z ⊗ w ∉ y) ⊗ x ⊆ y) ⊗ y ⊆ z ⇛ x ⊂ z"
      by(rule bisub_rule)
    from conj_bicomm and this have
      "x ⊆ y ⊗ (x ⊆ y ⊗ ∃(λw. w ∈ z ⊗ w ∉ y)) ⊗ y ⊆ z ⇛ x ⊂ z"
      by(rule bisub_rule)
    from conj_biass and this have
      "x ⊆ y ⊗ x ⊆ y ⊗ ∃(λw. w ∈ z ⊗ w ∉ y) ⊗ y ⊆ z ⇛ x ⊂ z"
      by(rule bisub_rule')
    from conj_bicomm and this show ?thesis
      unfolding proper_subset_def
      by(rule bisub_rule)
  qed

abbreviation russ :: "i" ("russ" 80)
  where "russ ≡ {(λx. x ∉ x)}"

lemma russ_bient: "x ∈ russ ↔ x ∉ x"
  proof -
     show "x ∈ russ ↔ x ∉ x"
      by(rule abstraction)
  qed

lemma russ_self_member: "russ ∈ russ"
  proof -
    from entl_cer and russ_bient have
      "russ ∉ russ → russ ∈ russ"
      unfolding bientl_def ..
    from entl_impl and this have
      case2:"russ ∉ russ ⇛ russ ∈ russ" ..

    from impl_disj_left and implI have
      "(russ ∉ russ ⇛ russ ∈ russ) ⇛ (russ ∈ russ ∨ russ ∉ russ) ⇛ russ ∈ russ" ..
    from this and case2 have
      "(russ ∈ russ ∨ russ ∉ russ) ⇛ russ ∈ russ" ..
    from this and lem show
      "russ ∈ russ" ..
  qed

lemma russ_not_self_member: "russ ∉ russ"
  proof -
    from entl_cel and russ_bient have
      "russ ∈ russ → russ ∉ russ"
      unfolding bientl_def ..
    from entl_impl and this have
      "russ ∈ russ ⇛ russ ∉ russ" ..

    from impl_disj_left and this have
      "(russ ∉ russ ⇛ russ ∉ russ) ⇛ (russ ∈ russ ∨ russ ∉ russ) ⇛ russ ∉ russ" ..
    from this and implI have
      "(russ ∈ russ ∨ russ ∉ russ) ⇛ russ ∉ russ" ..
    from this and lem show
      "russ ∉ russ" ..
  qed

lemma russell_contradiction: "russ ∈ russ ⊗ russ ∉ russ"
  proof -
    from russ_self_member and russ_not_self_member show ?thesis ..
  qed

lemma two_things: "∃(λx. ∃(λy. x ≠ y))"
  proof -
    from russ_self_member and russ_not_self_member have
      "russ ∈ russ ⊗ russ ∉ russ" ..
    from this have
      "∃(λx. x ∈ russ ⊗ x ∉ russ)" ..
    from counterexample_nonidentity and this have
      "russ ≠ russ" ..
    from this have
      "∃(λy. russ ≠ y)" ..
    from this show
      "∃(λx. ∃(λy. x ≠ y))" ..
  qed

lemma nonselfidentity_singletons: "x ≠ x ⇛ {!x} ≠ {!x}"
  proof -
    have step1:"x ∈ {!x} ↔ x = x"
      unfolding singleton_def
        by(rule abstraction)

    from this and refl_without_refl have step2:"x ∈ {!x}" ..

    from step1 have "x ∈ {!x} → x = x"
      unfolding bientl_def ..
    from entl_contra and this have
      "x ≠ x → x ∉ {!x}" ..
    from entl_impl and this have
      step3:"x ≠ x ⇛ x ∉ {!x}" ..

    from impl_conj_in and step2 have
      "x ∉ {!x} ⇛ x ∈ {!x} ⊗ x ∉ {!x}" ..
    from step3 and this have
      step4:"x ≠ x ⇛ x ∈ {!x} ⊗ x ∉ {!x}" ..

    from entl_impl and entl_eg have
      "x ∈ {!x} ⊗ x ∉ {!x} ⇛ ∃(λy. y ∈ {!x} ⊗ y ∉ {!x})" ..
    from step4 and this have
      "x ≠ x ⇛ ∃(λy. y ∈ {!x} ⊗ y ∉ {!x})" ..
    from this and counterexample_nonidentity show
      "x ≠ x ⇛ {!x} ≠ {!x}" ..
  qed

definition intersection :: "i ⇒ i ⇒ i" (infix "∩" 77)
  where "x ∩ y ≡ {(λz. z ∈ x ⊗ z ∈ y)}"

definition union :: "i ⇒ i ⇒ i" (infix "∪" 77)
  where "x ∪ y ≡ {(λz. z ∈ x ∨ z ∈ y)}"

lemma intersection_conj: "w ∈ x ∩ y ↔ w ∈ x ⊗ w ∈ y"
  proof -
    show "w ∈ x ∩ y ↔ w ∈ x ⊗ w ∈ y"
      unfolding intersection_def
        by(rule abstraction)
  qed

lemma intersection_ass : "x ∩ (y ∩ z) = (x ∩ y) ∩ z"
  proof -
    {
    fix w
    from intersection_conj have
      "w ∈ x ⊗ w ∈ y ∩ z ↔ w ∈ x ⊗ (w ∈ y ⊗ w ∈ z)"
      by(rule bisub)
    from this and intersection_conj have
      "w ∈ x ∩ (y ∩ z) ↔ w ∈ x ⊗ (w ∈ y ⊗ w ∈ z)"
      by(rule bisub_rule)
    from conj_biass and this have
      step1:"w ∈ x ∩ (y ∩ z) ↔ (w ∈ x ⊗ w ∈ y) ⊗ w ∈ z"
      by(rule bisub_rule)

    from intersection_conj have "w ∈ x ∩ y ⊗ w ∈ z ↔ (w ∈ x ⊗ w ∈ y) ⊗ w ∈ z"
      by(rule bisub)
    from this and intersection_conj have
      "w ∈ (x ∩ y) ∩ z ↔ (w ∈ x ⊗ w ∈ y) ⊗ w ∈ z"
      by(rule bisub_rule)

    from this and step1 have
      "w ∈ x ∩ (y ∩ z) ↔ w ∈ (x ∩ y) ∩ z"
      by(rule bisub_rule')
    }
    have "⋀ w. (w ∈ x ∩ (y ∩ z) ↔ w ∈ (x ∩ y) ∩ z)" by fact
    from this have
      "∀(λw. w ∈ x ∩ (y ∩ z) ↔ w ∈ (x ∩ y) ∩ z)" ..
    from extensionality and this show
      "x ∩ (y ∩ z) = (x ∩ y) ∩ z" ..
  qed

  lemma intersection_comm : "x ∩ y = y ∩ x"
    proof -
      {
      fix w
      from intersection_conj and conj_bicomm have
        step1:"w ∈ x ∩ y ↔ w ∈ y ⊗ w ∈ x"
        by(rule bientl_trans_rule)
      from intersection_conj have
        "w ∈ y ⊗ w ∈ x ↔ w ∈ y ∩ x"
        by(rule bientl_sym_rule)
      from step1 and this have
        "w ∈ x ∩ y ↔ w ∈ y ∩ x"
        by(rule bientl_trans_rule)
      }
      have "⋀ w. (w ∈ x ∩ y ↔ w ∈ y ∩ x)" by fact
      from this have
        "∀(λw. w ∈ x ∩ y ↔ w ∈ y ∩ x)" ..
      from extensionality and this show
        "x ∩ y = y ∩ x" ..
    qed

lemma union_disj: "w ∈ x ∪ y ↔ w ∈ x ∨ w ∈ y"
  proof -
    show "w ∈ x ∪ y ↔ w ∈ x ∨ w ∈ y"
      unfolding union_def
        by(rule abstraction)
  qed

lemma union_ass : "x ∪ (y ∪ z) = (x ∪ y) ∪ z"
  proof -
    {
    fix w
    from union_disj have
      "w ∈ x ∨ w ∈ y ∪ z ↔ w ∈ x ∨ (w ∈ y ∨ w ∈ z)"
      by(rule bisub)
    from union_disj and this have
      "w ∈ x ∪ (y ∪ z) ↔ w ∈ x ∨ (w ∈ y ∨ w ∈ z)"
      by(rule bisub_rule')
    from disj_biass and this have
      step1:"w ∈ x ∪ (y ∪ z) ↔ (w ∈ x ∨ w ∈ y) ∨ w ∈ z"
      by(rule bisub_rule)

    from union_disj have "w ∈ x ∪ y ∨ w ∈ z ↔ (w ∈ x ∨ w ∈ y) ∨ w ∈ z"
      by(rule bisub)
    from union_disj and this have
      "w ∈ (x ∪ y) ∪ z ↔ (w ∈ x ∨ w ∈ y) ∨ w ∈ z"
      by(rule bientl_trans_rule)
    from this and step1 have
      "w ∈ x ∪ (y ∪ z) ↔ w ∈ (x ∪ y) ∪ z"
      by(rule bisub_rule')
    }
    have "⋀ w. (w ∈ x ∪ (y ∪ z) ↔ w ∈ (x ∪ y) ∪ z)" by fact
    from this have
      "∀(λw. w ∈ x ∪ (y ∪ z) ↔ w ∈ (x ∪ y) ∪ z)" ..
    from extensionality and this show
      "x ∪ (y ∪ z) = (x ∪ y) ∪ z" ..
  qed

  lemma union_comm : "x ∪ y = y ∪ x"
    proof -
      {
      fix w
      from union_disj and disj_bicomm have
        step1:"w ∈ x ∪ y ↔ w ∈ y ∨ w ∈ x"
        by(rule bientl_trans_rule)
      from union_disj have
        "w ∈ y ∨ w ∈ x ↔ w ∈ y ∪ x"
        by(rule bientl_sym_rule)
      from step1 and this have
        "w ∈ x ∪ y ↔ w ∈ y ∪ x"
        by(rule bientl_trans_rule)
      }
      have "⋀ w. (w ∈ x ∪ y ↔ w ∈ y ∪ x)" by fact
      from this have
        "∀(λw. w ∈ x ∪ y ↔ w ∈ y ∪ x)" ..
      from extensionality and this show
        "x ∪ y = y ∪ x" ..
    qed

lemma intersection_subset: "x ∩ y ⊆ x"
  proof -
    {
    fix w
    from intersection_conj have
      "w ∈ x ∩ y → w ∈ x ⊗ w ∈ y"
      unfolding bientl_def ..
    from this and entl_cel have
      "w ∈ x ∩ y → w ∈ x" ..
    }
    have "⋀ w. (w ∈ x ∩ y → w ∈ x)" by fact
    from this show "x ∩ y ⊆ x"
      unfolding subset_def ..
  qed

lemma subset_union: "x ⊆ x ∪ y"
  proof -
    {
    fix w
    from union_disj have
      "w ∈ x ∨ w ∈ y → w ∈ x ∪ y"
      unfolding bientl_def ..
    from entl_disj_inl and this have
      "w ∈ x → w ∈ x ∪ y" ..
    }
    have "⋀ w. (w ∈ x → w ∈ x ∪ y)" by fact
    from this show "x ⊆ x ∪ y"
      unfolding subset_def ..
  qed

lemma dist_i_over_u_equiv: "x ∩ (y ∪ z) ≃ (x ∩ y) ∪ (x ∩ z)"
  proof -
    {
    fix w
    from union_disj have
      "w ∈ x ⊗ w ∈ (y ∪ z) ↔ w ∈ x ⊗ (w ∈ y ∨ w ∈ z)"
      by(rule bisub)
    from intersection_conj and this have
      "w ∈ x ∩ (y ∪ z) ↔ w ∈ x ⊗ (w ∈ y ∨ w ∈ z)"
      by(rule bientl_trans_rule)
    from bientl_biimpl and this have
      "w ∈ x ∩ (y ∪ z) ⇌ w ∈ x ⊗ (w ∈ y ∨ w ∈ z)" ..
    from this and dist_cd_biimpl have
      "w ∈ x ∩ (y ∪ z) ⇌ (w ∈ x ⊗ w ∈ y) ∨ (w ∈ x ⊗ w ∈ z)"
      by(rule biimpl_trans_rule)

    from intersection_conj and this have
      "w ∈ x ∩ (y ∪ z) ⇌ (w ∈ x ∩ y) ∨ (w ∈ x ⊗ w ∈ z)"
      by(rule bisub_rule')
    from intersection_conj and this have
      "w ∈ x ∩ (y ∪ z) ⇌ (w ∈ x ∩ y) ∨ (w ∈ x ∩ z)"
      by(rule bisub_rule')
    from union_disj and this have
      "w ∈ x ∩ (y ∪ z) ⇌ w ∈ (x ∩ y) ∪ (x ∩ z)"
      by(rule bisub_rule')
    }
    have "⋀ w. (w ∈ x ∩ (y ∪ z) ⇌ w ∈ (x ∩ y) ∪ (x ∩ z))" by fact
    from this show ?thesis
      unfolding biimpl_def
      unfolding eequiv_def ..
  qed

lemma epart_union_equiv: "x ⊑ y ⇛ x ∪ y ≃ y"
  proof -
    {
    fix w
    from entl_impl and entl_disj_inr have
      step1:"w ∈ y ⇛ w ∈ x ∨ w ∈ y" ..
    from union_disj have
      "w ∈ x ∨ w ∈ y → w ∈ x ∪ y"
      unfolding bientl_def ..
    from entl_impl and this have
      "w ∈ x ∨ w ∈ y ⇛ w ∈ x ∪ y" ..
    from step1 and this have
      "w ∈ y ⇛ w ∈ x ∪ y" ..
    from impl_conj_in and this have
      step2:"(w ∈ x ∪ y ⇛ w ∈ y) ⇛ (w ∈ x ∪ y ⇛ w ∈ y) ⊗ (w ∈ y ⇛ w ∈ x ∪ y)" ..

    from entl_impl and entl_ui have
      "x ⊑ y ⇛ w ∈ x ⇛ w ∈ y"
      unfolding epart_def ..
    from this and impl_disj_left have
      "x ⊑ y ⇛ (w ∈ y ⇛ w ∈ y) ⇛ (w ∈ x ∨ w ∈ y ⇛ w ∈ y)" ..
    from this and implI have
      "x ⊑ y ⇛ (w ∈ x ∨ w ∈ y ⇛ w ∈ y)" ..
    from union_disj and this have
      "x ⊑ y ⇛ (w ∈ x ∪ y ⇛ w ∈ y)"
      by(rule bisub_rule')

    from this and step2 have
      "x ⊑ y ⇛ (w ∈ x ∪ y ⇛ w ∈ y) ⊗ (w ∈ y ⇛ w ∈ x ∪ y)" ..
    }
    have "⋀ w. (x ⊑ y ⇛ (w ∈ x ∪ y ⇛ w ∈ y) ⊗ (w ∈ y ⇛ w ∈ x ∪ y))" by fact
    from this have
      "∀(λw. x ⊑ y ⇛ (w ∈ x ∪ y ⇛ w ∈ y) ⊗ (w ∈ y ⇛ w ∈ x ∪ y))" ..
    from all_cons and this show
      "x ⊑ y ⇛ x ∪ y ≃ y"
      unfolding eequiv_def ..
  qed

lemma union_equiv_epart: "x ∪ y ≃ y ⇛ x ⊑ y"
  proof -
    {
    fix w
    from entl_impl and entl_disj_inl have
      inl:"w ∈ x ⇛ w ∈ x ∨ w ∈ y" ..
    from union_disj and inl have
      "w ∈ x ⇛ w ∈ x ∪ y"
      by(rule bisub_rule')
    from implB' and this have
      "(w ∈ x ∪ y ⇛ w ∈ y) ⇛ w ∈ x ⇛ w ∈ y" ..
    from impl_cel and this have
      step1:"(w ∈ x ∪ y ⇛ w ∈ y) ⊗ (w ∈ y ⇛ w ∈ x ∪ y) ⇛ w ∈ x ⇛ w ∈ y" ..

    from entl_impl and entl_ui have
      "x ∪ y ≃ y ⇛ (w ∈ x ∪ y ⇛ w ∈ y) ⊗ (w ∈ y ⇛ w ∈ x ∪ y)"
      unfolding eequiv_def ..
    from this and step1 have
      "x ∪ y ≃ y ⇛ w ∈ x ⇛ w ∈ y" ..
    }
    have "⋀ w. (x ∪ y ≃ y ⇛ w ∈ x ⇛ w ∈ y)" by fact
    from this have
      "∀(λw. x ∪ y ≃ y ⇛ w ∈ x ⇛ w ∈ y)" ..
    from all_cons and this show
      "x ∪ y ≃ y ⇛ x ⊑ y"
      unfolding epart_def ..
  qed

lemma epart_intersection: "x ⊑ y ⇛ x ∩ x ⊑ x ∩ y"
  proof -
    {
    fix w
    from impl_conj_in and implI have
      "(w ∈ x ⇛ w ∈ y) ⇛ (w ∈ x ⇛ w ∈ x) ⊗ (w ∈ x ⇛ w ∈ y)" ..
    from this and factor have
      step1:"(w ∈ x ⇛ w ∈ y) ⇛ w ∈ x ⊗ w ∈ x ⇛ w ∈ x ⊗ w ∈ y" ..

    from entl_impl and entl_ui have
      "x ⊑ y ⇛ w ∈ x ⇛ w ∈ y"
      unfolding epart_def ..
    from this and step1 have
      "x ⊑ y ⇛ w ∈ x ⊗ w ∈ x ⇛ w ∈ x ⊗ w ∈ y" ..
    from intersection_conj and this have
      "x ⊑ y ⇛ w ∈ x ∩ x ⇛ w ∈ x ⊗ w ∈ y"
      by(rule bisub_rule')
    from intersection_conj and this have
      "x ⊑ y ⇛ w ∈ x ∩ x ⇛ w ∈ x ∩ y"
      by(rule bisub_rule')
    }
    have "⋀ w. (x ⊑ y ⇛ w ∈ x ∩ x ⇛ w ∈ x ∩ y)" by fact
    from this have
      "∀(λw. x ⊑ y ⇛ w ∈ x ∩ x ⇛ w ∈ x ∩ y)" ..
    from all_cons and this show
      "x ⊑ y ⇛ x ∩ x ⊑ x ∩ y"
      unfolding epart_def ..
  qed

lemma intersection_equiv_epart: "x ∩ y ≃ x ⇛ x ⊑ y"
  proof -
    {
    fix w
    from intersection_conj have
      "w ∈ x ∩ y → w ∈ x ⊗ w ∈ y"
      unfolding bientl_def ..
    from entl_impl and this have
      "w ∈ x ∩ y ⇛ w ∈ x ⊗ w ∈ y" ..
    from this and impl_cer have
      "w ∈ x ∩ y ⇛ w ∈ y" ..
    from implB and this have
      "(w ∈ x ⇛ w ∈ x ∩ y) ⇛ w ∈ x ⇛ w ∈ y" ..
    from impl_cer and this have
      step1:"(w ∈ x ∩ y ⇛ w ∈ x) ⊗ (w ∈ x ⇛ w ∈ x ∩ y) ⇛ w ∈ x ⇛ w ∈ y" ..

    from entl_impl and entl_ui have
      "x ∩ y ≃ x ⇛ (w ∈ x ∩ y ⇛ w ∈ x) ⊗ (w ∈ x ⇛ w ∈ x ∩ y)"
      unfolding eequiv_def ..
    from this and step1 have
      "x ∩ y ≃ x ⇛ w ∈ x ⇛ w ∈ y" ..
    }
    have "⋀ w. (x ∩ y ≃ x ⇛ w ∈ x ⇛ w ∈ y)" by fact
    from this have
      "∀(λw. x ∩ y ≃ x ⇛ w ∈ x ⇛ w ∈ y)" ..
    from all_cons and this show
      "x ∩ y ≃ x ⇛ x ⊑ y"
      unfolding epart_def ..
  qed

lemma intersection_emonotonic_left: "x ⊑ y ⇛ x ∩ z ⊑ y ∩ z"
  proof -
   {
   fix w
   from conj_export and factor have
     "(w ∈ x ⇛ w ∈ y) ⇛ (w ∈ z ⇛ w ∈ z) ⇛ (w ∈ x ⊗ w ∈ z ⇛ w ∈ y ⊗ w ∈ z)" ..
   from implC and this have
     "(w ∈ z ⇛ w ∈ z) ⇛ (w ∈ x ⇛ w ∈ y) ⇛ (w ∈ x ⊗ w ∈ z ⇛ w ∈ y ⊗ w ∈ z)" ..
   from this and implI have
     step1:"(w ∈ x ⇛ w ∈ y) ⇛ w ∈ x ⊗ w ∈ z ⇛ w ∈ y ⊗ w ∈ z" ..

   from entl_impl and entl_ui have
     "x ⊑ y ⇛ (w ∈ x ⇛ w ∈ y)"
     unfolding epart_def ..
   from this and step1 have
     "x ⊑ y ⇛ w ∈ x ⊗ w ∈ z ⇛ w ∈ y ⊗ w ∈ z" ..
   from intersection_conj and this have
     "x ⊑ y ⇛ w ∈ x ∩ z ⇛ w ∈ y ⊗ w ∈ z"
     by(rule bisub_rule')
   from intersection_conj and this have
     "x ⊑ y ⇛ w ∈ x ∩ z ⇛ w ∈ y ∩ z"
     by(rule bisub_rule')
   }
   have "⋀ w. (x ⊑ y ⇛ w ∈ x ∩ z ⇛ w ∈ y ∩ z)" by fact
   from this have
     "∀(λw. x ⊑ y ⇛ w ∈ x ∩ z ⇛ w ∈ y ∩ z)" ..
   from all_cons and this show
     "x ⊑ y ⇛ x ∩ z ⊑ y ∩ z"
     unfolding epart_def ..
  qed

lemma intersection_emonotonic_right: "x ⊑ y ⇛ z ∩ x ⊑ z ∩ y"
  proof -
    from intersection_comm and intersection_emonotonic_left have
      "x ⊑ y ⇛ x ∩ z ⊑ z ∩ y"
      by(rule equals_sub_rule)
    from intersection_comm and this show
      "x ⊑ y ⇛ z ∩ x ⊑ z ∩ y"
      by(rule equals_sub_rule)
  qed

lemma union_emonotonic_left: "x ⊑ y ⇛ x ∪ z ⊑ y ∪ z"
  proof -
    {
    fix w
    from entl_impl and entl_disj_inl have yyz:"w ∈ y ⇛ w ∈ y ∨ w ∈ z" ..
    from entl_impl and entl_disj_inr have zyz:"w ∈ z ⇛ w ∈ y ∨ w ∈ z" ..
    from implB' and yyz have
      "(w ∈ x ⇛ w ∈ y) ⇛ w ∈ x ⇛ w ∈ y ∨ w ∈ z" ..
    from this and impl_disj_left have
      "(w ∈ x ⇛ w ∈ y) ⇛ (w ∈ z ⇛ w ∈ y ∨ w ∈ z) ⇛ w ∈ x ∨ w ∈ z ⇛ w ∈ y ∨ w ∈ z" ..
    from this and zyz have
      step1:"(w ∈ x ⇛ w ∈ y) ⇛ w ∈ x ∨ w ∈ z ⇛ w ∈ y ∨ w ∈ z" ..

    from entl_impl and entl_ui have
      "x ⊑ y ⇛ w ∈ x ⇛ w ∈ y"
      unfolding epart_def ..
    from this and step1 have
      "x ⊑ y ⇛ w ∈ x ∨ w ∈ z ⇛ w ∈ y ∨ w ∈ z" ..
    from union_disj and this have
      "x ⊑ y ⇛ w ∈ x ∪ z ⇛ w ∈ y ∨ w ∈ z"
      by(rule bisub_rule')
    from union_disj and this have
      "x ⊑ y ⇛ w ∈ x ∪ z ⇛ w ∈ y ∪ z"
      by(rule bisub_rule')
    }
    have "⋀ w. (x ⊑ y ⇛ w ∈ x ∪ z ⇛ w ∈ y ∪ z)" by fact
    from this have
      "∀(λw. x ⊑ y ⇛ w ∈ x ∪ z ⇛ w ∈ y ∪ z)" ..
    from all_cons and this show
      "x ⊑ y ⇛ x ∪ z ⊑ y ∪ z"
      unfolding epart_def ..
  qed

lemma union_emonotonic_right: "x ⊑ y ⇛ z ∪ x ⊑ z ∪ y"
  proof -
    from union_comm and union_emonotonic_left have
      "x ⊑ y ⇛ z ∪ x ⊑ y ∪ z"
      by(rule equals_sub_rule)
    from union_comm and this show
      "x ⊑ y ⇛ z ∪ x ⊑ z ∪ y"
      by(rule equals_sub_rule)
  qed

lemma union_left: "x ⊑ z ⇛ y ⊑ z ⇛ x ∪ y ⊑ z"
  proof -
    {
    fix w
    from entl_impl and entl_ui have
      xz:"x ⊑ z ⇛ w ∈ x ⇛ w ∈ z"
      unfolding epart_def ..
    from entl_impl and entl_ui have
      yz:"y ⊑ z ⇛ w ∈ y ⇛ w ∈ z"
      unfolding epart_def ..
    from xz and impl_disj_left have
      "x ⊑ z ⇛ (w ∈ y ⇛ w ∈ z) ⇛ (w ∈ x ∨ w ∈ y ⇛ w ∈ z)" ..
    from this and yz have
      "x ⊑ z ⇛ y ⊑ z ⇛ w ∈ x ∨ w ∈ y ⇛ w ∈ z"
      by(rule impl_link_212)
    from union_disj and this have
      "x ⊑ z ⇛ y ⊑ z ⇛ w ∈ x ∪ y ⇛ w ∈ z"
      by(rule bisub_rule')
    }
    have "⋀ w. (x ⊑ z ⇛ y ⊑ z ⇛ w ∈ x ∪ y ⇛ w ∈ z)" by fact
    from this have
      "∀(λw. x ⊑ z ⇛ y ⊑ z ⇛ w ∈ x ∪ y ⇛ w ∈ z)" ..
    from all_cons and this have
      "x ⊑ z ⇛ ∀(λw. y ⊑ z ⇛ w ∈ x ∪ y ⇛ w ∈ z)" ..
    from this and all_cons show
      "x ⊑ z ⇛ y ⊑ z ⇛ x ∪ y ⊑ z"
      unfolding epart_def ..
  qed

lemma out_of_self_intersection: "x ∉ y ∩ y ⇛ x ∉ y"
  proof -
    from intersection_conj and no_counterexample_to_contraction show ?thesis
      by(rule bisub_rule')
  qed

lemma self_intersection_proper_ltr: "y ∩ y ⊂ y ⇛ y ⊂ y"
  proof -
    {
      fix x
      from add_conjunct_on_left and out_of_self_intersection have
        "x ∈ y ⊗ x ∉ y ∩ y ⇛ x ∈ y ⊗ x ∉ y" ..
      from this and impl_eg have
        "x ∈ y ⊗ x ∉ y ∩ y ⇛ ∃(λz. z ∈ y ⊗ z ∉ y)" ..
      from subset_refl and this have
        "y ⊆ y ⊗ (x ∈ y ⊗ x ∉ y ∩ y ⇛ ∃(λz. z ∈ y ⊗ z ∉ y))" ..
      from conj_in_under_impl and this have
        "x ∈ y ⊗ x ∉ y ∩ y ⇛ y ⊂ y"
        unfolding proper_subset_def ..
    }
    have "⋀x. x ∈ y ⊗ x ∉ y ∩ y ⇛ y ⊂ y" by fact
    from this have
      "∀(λx. x ∈ y ⊗ x ∉ y ∩ y ⇛ y ⊂ y)" ..
    from all_ante and this have
      "∃(λx. x ∈ y ⊗ x ∉ y ∩ y) ⇛ y ⊂ y" ..
    from impl_cer and this show ?thesis
      unfolding proper_subset_def ..
  qed

lemma self_intersection_proper_rtl: "y ⊂ y ⇛ y ∩ y ⊂ y"
  proof -
    {
      fix x
      from entl_impl and entl_ncil have
        "x ∉ y ⇛ ¬(x ∈ y ⊗ x ∈ y)" ..
      from intersection_conj and this have
        "x ∉ y ⇛ x ∉ y ∩ y"
        by(rule bisub_rule')
      from add_conjunct_on_left and this have
        "x ∈ y ⊗ x ∉ y ⇛ x ∈ y ⊗ x ∉ y ∩ y" ..
    }
    have "⋀x. x ∈ y ⊗ x ∉ y ⇛ x ∈ y ⊗ x ∉ y ∩ y" by fact
    from this have
      "∃(λx. x ∈ y ⊗ x ∉ y) ⇛ ∃(λx. x ∈ y ⊗ x ∉ y ∩ y)"
      by(rule impl_some_monotone_rule)
    from impl_cer and this have
      "y ⊂ y ⇛ ∃(λx. x ∈ y ⊗ x ∉ y ∩ y)"
      unfolding proper_subset_def ..
    from intersection_subset and this have
      "y ∩ y ⊆ y ⊗ (y ⊂ y ⇛ ∃(λx. x ∈ y ⊗ x ∉ y ∩ y))" ..
    from conj_in_under_impl and this show ?thesis
      unfolding proper_subset_def ..
  qed

lemma in_its_singleton: "x ∈ {!x}"
  proof -
    from abstraction and refl_without_refl show ?thesis
      unfolding singleton_def
      by(rule bientl_mp_rtl)
  qed

lemma in_singleton_equals: "x ∈ {!y} → x = y"
  proof -
    from abstraction show ?thesis
      unfolding singleton_def
      unfolding bientl_def ..
  qed

  lemma singleton_epart_self_intersection: "{!x} ⊑ {!x} ∩ {!x}"
    proof -
      {
      fix y
      from abstraction and identity_contracts have
        "y ∈ {!x} ⇛ y ∈ {!x} ⊗ y ∈ {!x}"
          unfolding singleton_def
          by(rule bisub_rule')
      from intersection_conj and this have
        "y ∈ {!x} ⇛ y ∈ {!x} ∩ {!x}"
           by(rule bisub_rule')
      }
      have "⋀ y. (y ∈ {!x} ⇛ y ∈ {!x} ∩ {!x})" by fact
      from this show ?thesis
        unfolding epart_def ..
    qed

  lemma singleton_preserves_equality: "x = y ⇛ {!x} = {!y}"
    proof -
      from equals_sub_impl and entl_impl have
        "x = y ⇛ {!x} = {!x} ⇛ {!x} = {!y}" ..
      from this and refl_without_refl show ?thesis ..
    qed

lemma singleton_reflects_equality: "{!x} = {!y} ⇛ x = y"
    proof -
      from equals_sub_impl and entl_impl have
        "{!x} = {!y} ⇛ x ∈ {!x} ⇛ x ∈ {!y}" ..
      from this and in_its_singleton have
        step1:"{!x} = {!y} ⇛ x ∈ {!y}" ..

      from entl_impl and in_singleton_equals have
        "x ∈ {!y} ⇛ x = y" ..
      from step1 and this show ?thesis ..
    qed

lemma membership_singleton_epart_ltr: "x ∈ y ⇛ {!x} ⊑ y"
    proof -
      {
      fix z
      from equals_sub_impl and entl_impl have
        "x = z ⇛ x ∈ y ⇛ z ∈ y" ..
      from implC and this have
        "x ∈ y ⇛ x = z ⇛ z ∈ y" ..
      }
      have "⋀ z. (x ∈ y ⇛ x = z ⇛ z ∈ y)" by fact
      from this have
        "∀(λz. x ∈ y ⇛ x = z ⇛ z ∈ y)" ..
      from all_cons and this have
        step1: "x ∈ y ⇛ ∀(λz. x = z ⇛ z ∈ y)" ..

      from eq_sym_bientl have
        link1: "∀(λz. x = z ⇛ z ∈ y) ↔ ∀(λz. z = x ⇛ z ∈ y)"
        by(rule bisub_open)
      from abstraction have
        "∀(λz. z ∈ {!x} ⇛ z ∈ y) ↔ ∀(λz. z = x ⇛ z ∈ y)"
        unfolding singleton_def
        by(rule bisub_open)
      from this and link1 have
        "∀(λz. x = z ⇛ z ∈ y) ↔ ∀(λz. z ∈ {!x} ⇛ z ∈ y)"
        by(rule bisub_rule')

      from this and step1 show ?thesis
        unfolding epart_def
        by(rule bisub_rule)
    qed

lemma membership_singleton_epart_rtl: "{!x} ⊑ y ⇛ x ∈ y"
    proof -
      from entl_impl and entl_ui have
        "{!x} ⊑ y ⇛ x ∈ {!x} ⇛ x ∈ y"
        unfolding epart_def ..
      from abstraction and this have
        "{!x} ⊑ y ⇛ x = x ⇛ x ∈ y"
        unfolding singleton_def
        by(rule bisub_rule)
      from this and refl_without_refl show ?thesis ..
    qed

definition complement :: "i ⇒ i" ("_*" [79] 79)
  where "x* ≡ {(λy. y ∉ x)}"

lemma double_complement: "x** = x"
  proof -
    {
    fix w
    from abstraction have "w ∉ x* ↔ ¬(w ∉ x)"
      unfolding complement_def
      by(rule bisub)
    from abstraction and this have
      "w ∈ x** ↔ ¬(w ∉ x)"
      unfolding complement_def
      by(rule bientl_trans_rule)
    from dn_bi' and this have
      "w ∈ x** ↔ w ∈ x"
      by(rule bisub_rule)
    }
    have "⋀ w. (w ∈ x** ↔ w ∈ x)" by fact
    from this have
      "∀(λw. w ∈ x** ↔ w ∈ x)" ..
    from extensionality and this show
      "x** = x" ..
  qed

lemma membership_union_complement_lem: "w ∈ x ∪ x*"
  proof -
    from abstraction' and lem have
      "w ∈ x ∨ w ∈ x*"
      unfolding complement_def
      by(rule bisub_rule)
    from union_disj and this show
      "w ∈ x ∪ x*"
      by(rule bisub_rule')
  qed

lemma membership_none_intersection_complement: "¬∃(λw. w ∈ x ∩ x*)"
  proof -
    {
    fix w
    from abstraction' have
      "¬(w ∈ x ⊗ w ∉ x) ↔ ¬(w ∈ x ⊗ w ∈ x*)"
      unfolding complement_def
      by(rule bisub)
    from this and lnc have
      lncc:"¬(w ∈ x ⊗ w ∈ x*)" ..

    from intersection_conj and this have
      "¬(w ∈ x ∩ x*)"
      by(rule bisub_rule')
    }
    have "⋀ w. (¬(w ∈ x ∩ x*))" by fact
    from this have
      "∀(λw. ¬(w ∈ x ∩ x*))" ..
    from dm_anns_bi and this show
      "¬∃(λw. w ∈ x ∩ x*)" ..
  qed

lemma membership_dm_ciuc: "(x ∩ y)* = x* ∪ y*"
  proof -
    {
    fix w
    from intersection_conj have
      step1:"w ∉ x ∩ y ↔ ¬(w ∈ x ⊗ w ∈ y)"
      by(rule bisub)
    from dm_dnnc_bi and this have
      "w ∉ x ∩ y ↔ w ∉ x ∨ w ∉ y"
      by(rule bisub_rule')
    from abstraction and this have
      "w ∈ (x ∩ y)* ↔ w ∉ x ∨ w ∉ y"
      unfolding complement_def
      by(rule bientl_trans_rule)
    from abstraction and this have
      "w ∈ (x ∩ y)* ↔ w ∈ x* ∨ w ∉ y"
      unfolding complement_def
      by(rule bisub_rule')
    from abstraction and this have
      "w ∈ (x ∩ y)* ↔ w ∈ x* ∨ w ∈ y*"
      unfolding complement_def
      by(rule bisub_rule')

    from union_disj and this have
      "w ∈ (x ∩ y)* ↔ w ∈ x* ∪ y*"
      by(rule bisub_rule')
    }
    have "⋀ w. (w ∈ (x ∩ y)* ↔ w ∈ x* ∪ y*)" by fact
    from this have
      "∀(λw. w ∈ (x ∩ y)* ↔ w ∈ x* ∪ y*)" ..
    from extensionality and this show
      "(x ∩ y)* = x* ∪ y*" ..
  qed

lemma membership_dm_cuic: "(x ∪ y)* = x* ∩ y*"
  proof -
    {
    fix w
    from union_disj have
      "w ∉ x ∪ y ↔ ¬(w ∈ x ∨ w ∈ y)"
      by(rule bisub)
    from dm_cnnd_bi and this have
      "w ∉ x ∪ y ↔ w ∉ x ⊗ w ∉ y"
      by(rule bisub_rule')
    from abstraction and this have
      "w ∈ (x ∪ y)* ↔ w ∉ x ⊗ w ∉ y"
      unfolding complement_def
      by(rule bientl_trans_rule)

    from abstraction and this have
      "w ∈ (x ∪ y)* ↔ w ∈ x* ⊗ w ∉ y"
      unfolding complement_def
      by(rule bisub_rule')
    from abstraction and this have
      "w ∈ (x ∪ y)* ↔ w ∈ x* ⊗ w ∈ y*"
      unfolding complement_def
      by(rule bisub_rule')
    from intersection_conj and this have
      "w ∈ (x ∪ y)* ↔ w ∈ x* ∩ y*"
      by(rule bisub_rule')
    }
    have "⋀ w. (w ∈ (x ∪ y)* ↔ w ∈ x* ∩ y*)" by fact
    from this have
      "∀(λw. w ∈ (x ∪ y)* ↔ w ∈ x* ∩ y*)" ..
    from extensionality and this show
      "(x ∪ y)* = x* ∩ y*" ..
  qed

lemma subset_contra: "x ⊆ y ⇛ y* ⊆ x*"
  proof -
    {
    fix w
    from entl_ui and entl_contra have
      "x ⊆ y → (w ∉ y → w ∉ x)"
      unfolding subset_def ..
    from entl_impl and this have
      "x ⊆ y ⇛ (w ∉ y → w ∉ x)" ..
    from abstraction and this have
      "x ⊆ y ⇛ (w ∈ y* → w ∉ x)"
      unfolding complement_def
      by(rule bisub_rule')
    from abstraction and this have
      "x ⊆ y ⇛ (w ∈ y* → w ∈ x*)"
      unfolding complement_def
      by(rule bisub_rule')
    }
    have "⋀ w. (x ⊆ y ⇛ (w ∈ y* → w ∈ x*))" by fact
    from this have
      "∀(λw. x ⊆ y ⇛ (w ∈ y* → w ∈ x*))" ..
    from all_cons and this show
      "x ⊆ y ⇛ y* ⊆ x*"
      unfolding subset_def ..
  qed

lemma subset_contra': "y* ⊆ x* ⇛ x ⊆ y"
  proof -
    from double_complement and subset_contra have
      "y* ⊆ x* ⇛ x ⊆ y**"
      by(rule equals_sub_rule)
    from double_complement and this show
      "y* ⊆ x* ⇛ x ⊆ y"
      by(rule equals_sub_rule)
  qed

definition rel_complement :: "i ⇒ i ⇒ i" (infix "-" 77)
  where "x - y ≡ x ∩ y*"

definition self_complement :: "i ⇒ i" ("!?_" [80] 80)
  where "!?x ≡ x ∩ x*"

lemma russ_self_comp: "russ ∈ !?russ"
  proof -
    from abstraction' and russ_not_self_member have
      "russ ∈ russ*"
      unfolding complement_def ..
    from russ_self_member and this have
      step1:"russ ∈ russ ⊗ russ ∈ russ*" ..
    from intersection_conj and this show
      "russ ∈ !?russ"
      unfolding self_complement_def ..
  qed

lemma self_comp_subset: "!?x ⊆ x"
  proof -
    show "!?x ⊆ x"
      unfolding self_complement_def
      by(rule intersection_subset)
  qed

lemma self_comp_subset': "x ⊆ y ⇛ !?x ⊆ y"
  proof -
    from conj_export and subset_trans have
      "!?x ⊆ x ⇛ x ⊆ y ⇛ !?x ⊆ y" ..
    from this and self_comp_subset show
      "x ⊆ y ⇛ !?x ⊆ y" ..
  qed

lemma rel_comp_dne_aux: "x - (x - a) ≃ !?x ∪ (x ∩ a)"
  proof -
    have "x - (x - a) = x ∩ (x ∩ a*)*"
      unfolding rel_complement_def
      by(rule refl_without_refl)
    from membership_dm_ciuc and this have
      "x - (x - a) = x ∩ (x* ∪ a**)"
      by(rule equals_sub_rule)
    from double_complement and this have
      "x - (x - a) = x ∩ (x* ∪ a)"
      by(rule equals_sub_rule)
    from this and dist_i_over_u_equiv show
      "x - (x - a) ≃ !?x ∪ (x ∩ a)"
      unfolding self_complement_def
      by(rule equals_sub_rule')
  qed

lemma rel_comp_dne: "x - (x - a) ⊑ a ∪ !?x"
  proof -
    from union_comm and rel_comp_dne_aux have
      "x - (x - a) ≃ (x ∩ a) ∪ !?x"
      by(rule equals_sub_rule)
    from eequiv_eparts and this have
      "(x - (x - a) ⊑ (x ∩ a) ∪ !?x) ⊗ ((x ∩ a) ∪ !?x ⊑ x - (x - a))" ..
    from this have
      step1: "x - (x - a) ⊑ (x ∩ a) ∪ !?x"..

    from subset_epart and intersection_subset have
      "a ∩ x ⊑ a" ..
    from intersection_comm and this have
      "x ∩ a ⊑ a"
      by(rule equals_sub_rule)
    from union_emonotonic_left and this have
      "(x ∩ a) ∪ !?x ⊑ a ∪ !?x" ..
    from step1 and this have
      "(x - (x - a) ⊑ (x ∩ a) ∪ !?x) ⊗ ((x ∩ a) ∪ !?x ⊑ a ∪ !?x)" ..
    from epart_trans and this show
      "x - (x - a) ⊑ a ∪ !?x" ..
  qed

lemma rel_comp_dni: "a ⊑ x ⇛ a ∩ a ⊑ x - (x - a)"
  proof -
    from subset_epart and subset_union have
      "a ⊑ a ∪ x*" ..
    from union_comm and this have
      "a ⊑ x* ∪ a"
      by(rule equals_sub_rule)
    from intersection_emonotonic_right and this have
      "a ∩ a ⊑ a ∩ (x* ∪ a)" ..
    from impl_conj_in and this have
      "a ∩ (x* ∪ a) ⊑ x ∩ (x* ∪ a) ⇛ (a ∩ a ⊑ a ∩ (x* ∪ a)) ⊗ (a ∩ (x* ∪ a) ⊑ x ∩ (x* ∪ a))" ..
    from this and epart_trans have
      "a ∩ (x* ∪ a) ⊑ x ∩ (x* ∪ a) ⇛ a ∩ a ⊑ x ∩ (x* ∪ a)" ..
    from intersection_emonotonic_left and this have
      step1:"a ⊑ x ⇛ a ∩ a ⊑ x ∩ (x* ∪ a)" ..

    from double_complement and refl_without_refl have
      "x ∩ (x* ∪ a) = x ∩ (x* ∪ a)**"
      by(rule equals_sub_rule')
    from membership_dm_cuic and this have
      "x ∩ (x* ∪ a) = x ∩ (x** ∩ a*)*"
      by(rule equals_sub_rule)
    from double_complement and this have
      "x ∩ (x* ∪ a) = x - (x - a)"
      unfolding rel_complement_def
      by(rule equals_sub_rule)

    from this and step1 show ?thesis
      by(rule equals_sub_rule)
  qed

lemma rel_comp_dni_plus: "a ⊑ x ⇛ (a ∩ a) ∪ !?x ⊑ x - (x - a)"
  proof -
    {
    fix w
    from conj_export and factor have
      "(w ∈ x ⇛ w ∈ x) ⇛ (w ∈ x* ⇛ w ∈ x* ∨ w ∈ a) ⇛ w ∈ x ⊗ w ∈ x* ⇛ w ∈ x ⊗ (w ∈ x* ∨ w ∈ a)" ..
    from this and implI have
      step1:"(w ∈ x* ⇛ w ∈ x* ∨ w ∈ a) ⇛ w ∈ x ⊗ w ∈ x* ⇛ w ∈ x ⊗ (w ∈ x* ∨ w ∈ a)" ..
    from entl_impl and entl_disj_inl have
      "w ∈ x* ⇛ w ∈ x* ∨ w ∈ a" ..
    from step1 and this have
      "w ∈ x ⊗ w ∈ x* ⇛ w ∈ x ⊗ (w ∈ x* ∨ w ∈ a)" ..
    from intersection_conj and this have
      "w ∈ !?x ⇛ w ∈ x ⊗ (w ∈ x* ∨ w ∈ a)"
        unfolding self_complement_def
        by(rule bisub_rule')
    from union_disj and this have
      "w ∈ !?x ⇛ w ∈ x ⊗ w ∈ x* ∪ a"
      by(rule bisub_rule')
    from intersection_conj and this have
      step2:"w ∈ !?x ⇛ w ∈ x ∩ (x* ∪ a)"
      by(rule bisub_rule')


    from double_complement and refl_without_refl have
      "x ∩ (x* ∪ a) = x ∩ (x* ∪ a)**"
      by(rule equals_sub_rule')
    from membership_dm_cuic and this have
      "x ∩ (x* ∪ a) = x ∩ (x** ∩ a*)*"
      by(rule equals_sub_rule)
    from double_complement and this have
      "x ∩ (x* ∪ a) = x - (x - a)"
      unfolding rel_complement_def
      by(rule equals_sub_rule)
        
    from this and step2 have
      "w ∈ !?x ⇛ w ∈ x - (x - a)"
      by(rule equals_sub_rule)
    }
    have "⋀ w. (w ∈ !?x ⇛ w ∈ x - (x - a))" by fact
    from this have
      step3:"!?x ⊑ x - (x - a)"
      unfolding epart_def ..

    from rel_comp_dni and union_left have
      "a ⊑ x ⇛ !?x ⊑ x - (x - a) ⇛ (a ∩ a) ∪ !?x ⊑ x - (x - a)" ..
    from this and step3 show
      "a ⊑ x ⇛ (a ∩ a) ∪ !?x ⊑ x - (x - a)" ..
  qed

lemma eight_three_a: "x - !?x ⊆ x"
  proof -
    {
    fix w
    from intersection_conj and entl_cel have
      "w ∈ x - !?x → w ∈ x"
      unfolding rel_complement_def
      by(rule bisub_rule')
    }
    have "⋀ w. (w ∈ x - !?x → w ∈ x)" by fact
    from this show
      "x - !?x ⊆ x"
      unfolding subset_def ..
  qed

lemma eight_three_b: "x ∩ x ⊑ x - !?x"
  proof -
    from subset_epart and subset_union have
      "x ⊑ x ∪ x*" ..
    from double_complement and this have
      "x ⊑ (x ∪ x*)**"
      by(rule equals_sub_rule')
    from membership_dm_cuic and this have
      "x ⊑ (x* ∩ x**)*"
      by(rule equals_sub_rule)
    from double_complement and this have
      "x ⊑ (x* ∩ x)*"
      by(rule equals_sub_rule)
    from intersection_comm and this have
      "x ⊑ (!?x)*"
      unfolding self_complement_def
      by(rule equals_sub_rule')
    from intersection_emonotonic_right and this show
      "x ∩ x ⊑ x - !?x"
      unfolding rel_complement_def ..
  qed

lemma eight_four_aux: "x ∪ !?x ⊑ x"
  proof -
    {
    fix w
    from intersection_conj and entl_cel have
      "w ∈ !?x → w ∈ x"
      unfolding self_complement_def
      by(rule bisub_rule')
    from entl_impl and this have
      step1:"w ∈ !?x ⇛ w ∈ x" ..
    from impl_disj_left and implI have
      "(w ∈ !?x ⇛ w ∈ x) ⇛ w ∈ x ∨ w ∈ !?x ⇛ w ∈ x" ..
    from this and step1 have
      "w ∈ x ∨ w ∈ !?x ⇛ w ∈ x" ..
    from union_disj and this have
      "w ∈ x ∪ !?x ⇛ w ∈ x"
      by(rule bisub_rule')
    }
    have "⋀ w. (w ∈ x ∪ !?x ⇛ w ∈ x)" by fact
    from this show
      "x ∪ !?x ⊑ x"
      unfolding epart_def ..
  qed

lemma eight_four: "x ≃ x ∪ !?x"
  proof -
    from subset_epart and subset_union have
      "x ⊑ x ∪ !?x" ..
    from this and eight_four_aux have
      "x ⊑ x ∪ !?x ⊗ x ∪ !?x ⊑ x" ..
    from epart_antisym and this show
      "x ≃ x ∪ !?x" ..
  qed

lemma eight_five_ltr: "x ⊑ a ∪ (x - a)"
  proof -
    {
    fix w
    from impl_conj_in and lem have
      "w ∈ x ⇛ (w ∈ a ∨ w ∉ a) ⊗ w ∈ x" ..
    from conj_bicomm and this have
      step0:"w ∈ x ⇛ w ∈ x ⊗ (w ∈ a ∨ w ∉ a)"
      by(rule bisub_rule)
    from dist_cd_biimpl have
      "w ∈ x ⊗ (w ∈ a ∨ w ∉ a) ⇛ (w ∈ x ⊗ w ∈ a) ∨ (w ∈ x ⊗ w ∉ a)"
      unfolding biimpl_def ..
    from step0 and this have
      "w ∈ x ⇛ (w ∈ x ⊗ w ∈ a) ∨ (w ∈ x ⊗ w ∉ a)" ..
    from intersection_conj and this have
      "w ∈ x ⇛ w ∈ x ∩ a ∨ (w ∈ x ⊗ w ∉ a)"
      by(rule bisub_rule')
    from abstraction and this have
      "w ∈ x ⇛ w ∈ x ∩ a ∨ (w ∈ x ⊗ w ∈ a*)"
      unfolding complement_def
      by(rule bisub_rule')
    from intersection_conj and this have
      "w ∈ x ⇛ w ∈ x ∩ a ∨ w ∈ x ∩ a*"
      by(rule bisub_rule')
    from union_disj and this have
      "w ∈ x ⇛ w ∈ (x ∩ a) ∪ (x - a)"
      unfolding rel_complement_def
      by(rule bisub_rule')
    }
    have "⋀ w. (w ∈ x ⇛ w ∈ (x ∩ a) ∪ (x - a))" by fact
    from this have
      step1:"x ⊑ (x ∩ a) ∪ (x - a)"
      unfolding epart_def ..

    from subset_epart and intersection_subset have
      "a ∩ x ⊑ a" ..
    from intersection_comm and this have
      "x ∩ a ⊑ a"
      by(rule equals_sub_rule)
    from union_emonotonic_left and this have
      "(x ∩ a) ∪ (x - a) ⊑ a ∪ (x - a)" ..
    from step1 and this have
      "(x ⊑ (x ∩ a) ∪ (x - a)) ⊗ ((x ∩ a) ∪ (x - a) ⊑ a ∪ (x - a))" ..
    from epart_trans and this show
      "x ⊑ a ∪ (x - a)" ..
  qed

lemma eight_five: "a ⊑ x ⇛ x ≃ a ∪ (x - a)"
  proof -
    {
    fix w
    from implI and impl_ui have
      "a ⊑ x ⇛ (w ∈ a ⇛ w ∈ x)"
      unfolding epart_def ..
    from this and impl_disj_left have
      "a ⊑ x ⇛ (w ∈ x - a ⇛ w ∈ x) ⇛ w ∈ a ∨ w ∈ x - a ⇛ w ∈ x" ..
    from union_disj and this have
      step1:"a ⊑ x ⇛ (w ∈ x - a ⇛ w ∈ x) ⇛ w ∈ a ∪ (x - a) ⇛ w ∈ x"
      by(rule bisub_rule')

    from intersection_conj have
      "w ∈ x - a → w ∈ x ⊗ w ∈ a*"
      unfolding rel_complement_def
      unfolding bientl_def ..
    from this and entl_cel have
      "w ∈ x - a → w ∈ x" ..
    from entl_impl and this have
      "w ∈ x - a ⇛ w ∈ x" ..
    from step1 and this have
      "a ⊑ x ⇛ w ∈ a ∪ (x - a) ⇛ w ∈ x"
      by(rule impl_link_202)
    }
    have "⋀ w. (a ⊑ x ⇛ w ∈ a ∪ (x - a) ⇛ w ∈ x)" by fact
    from this have
      "∀(λw. a ⊑ x ⇛ w ∈ a ∪ (x - a) ⇛ w ∈ x)" ..
    from all_cons and this have
      step2:"a ⊑ x ⇛ a ∪ (x - a) ⊑ x"
      unfolding epart_def ..

    from impl_conj_in and eight_five_ltr have
      "a ∪ (x - a) ⊑ x ⇛ x ⊑ a ∪ (x - a) ⊗ a ∪ (x - a) ⊑ x" ..
    from step2 and this have
      "a ⊑ x ⇛ x ⊑ a ∪ (x - a) ⊗ a ∪ (x - a) ⊑ x" ..
    from this and epart_antisym show
      "a ⊑ x ⇛ x ≃ a ∪ (x - a)" ..
  qed

definition powerset :: "i ⇒ i" ("Pow(_)" [80] 80)
  where "Pow(x) ≡ {(λy. y ⊑ x)}"

definition proper_epart :: "i ⇒ i ⇒ o" (infix "⊏" 75)
  where "x ⊏ y ≡ x ⊑ y ⊗ ∃(λz. z ∈ y ⊗ z ∉ x)"

lemma russ_self_proper_epart: "russ ⊏ russ"
  proof -
    from russ_self_member and russ_not_self_member have
      "russ ∈ russ ⊗ russ ∉ russ" ..
    from this have
      "∃(λz. z ∈ russ ⊗ z ∉ russ)" ..
    from epart_refl and this show
      "russ ⊏ russ"
      unfolding proper_epart_def ..
  qed

lemma russ_not_self_epart: "¬(russ ⊑ russ)"
  proof -
    from russ_self_member and russ_not_self_member have
      "russ ∈ russ ⊗ russ ∉ russ" ..
    from impl_cex and this have
      step1:"¬(russ ∈ russ ⇛ russ ∈ russ)" ..
    from entl_contra and entl_ui have
      "¬(russ ∈ russ ⇛ russ ∈ russ) → ¬∀(λz. z ∈ russ ⇛ z ∈ russ)" ..
    from this and step1 show
      "¬(russ ⊑ russ)"
      unfolding epart_def ..
  qed

lemma power_russ_epart_russ: "Pow(russ) ⊑ russ"
  proof -
    {
    fix x
    from abstraction' have
      "x ∉ x → x ∈ russ"
      unfolding bientl_def ..
    from entl_impl and this have
      "x ∉ x ⇛ x ∈ russ" ..
    from impl_disj_left and this have
      "(x ∈ x ⇛ x ∈ russ) ⇛ x ∈ x ∨ x ∉ x ⇛ x ∈ russ" ..
    from this and lem have
      step1:"(x ∈ x ⇛ x ∈ russ) ⇛ x ∈ russ" ..

    from entl_impl and entl_ui have
      "x ⊑ russ ⇛ x ∈ x ⇛ x ∈ russ"
      unfolding epart_def ..
    from this and step1 have
      "x ⊑ russ ⇛ x ∈ russ" ..
    from abstraction and this have
      "x ∈ Pow(russ) ⇛ x ∈ russ"
      unfolding powerset_def
      by(rule bisub_rule')
    }
    have "⋀ x. (x ∈ Pow(russ) ⇛ x ∈ russ)" by fact
    from this show
      "Pow(russ) ⊑ russ"
      unfolding epart_def ..
  qed

lemma power_russ_proper_epart_russ: "Pow(russ) ⊏ russ"
  proof -
    from abstraction and russ_not_self_epart have
      "russ ∉ Pow(russ)"
      unfolding powerset_def
      by(rule bisub_rule')
    from russ_self_member and this have
      "russ ∈ russ ⊗ russ ∉ Pow(russ)" ..
    from this have
      "∃(λx. x ∈ russ ⊗ x ∉ Pow(russ))" ..
    from power_russ_epart_russ and this show
      "Pow(russ) ⊏ russ"
      unfolding proper_epart_def ..
  qed

lemma powerset_emonotonic: "x ⊑ y ⇛ Pow(x) ⊑ Pow(y)"
  proof -
    {
    fix z
    {
    fix w
    from entl_impl and entl_ui have
      "x ⊑ y ⇛ w ∈ x ⇛ w ∈ y"
      unfolding epart_def ..
    from this and implB have
      step1:"x ⊑ y ⇛ (w ∈ z ⇛ w ∈ x) ⇛ (w ∈ z ⇛ w ∈ y)" ..

    from entl_impl and entl_ui have
      "z ⊑ x ⇛ w ∈ z ⇛ w ∈ x"
      unfolding epart_def ..
    from abstraction and this have
      "z ∈ Pow(x) ⇛ w ∈ z ⇛ w ∈ x"
      unfolding powerset_def
      by(rule bisub_rule')
    from step1 and this have
      "x ⊑ y ⇛ z ∈ Pow(x) ⇛ w ∈ z ⇛ w ∈ y"
      by(rule impl_link_212)
    }
    have "⋀ w. (x ⊑ y ⇛ z ∈ Pow(x) ⇛ w ∈ z ⇛ w ∈ y)" by fact
    from this have
      "∀(λw. x ⊑ y ⇛ z ∈ Pow(x) ⇛ w ∈ z ⇛ w ∈ y)" ..
    from all_cons and this have
      "x ⊑ y ⇛ ∀(λw. z ∈ Pow(x) ⇛ w ∈ z ⇛ w ∈ y)" ..
    from this and all_cons have
      "x ⊑ y ⇛ z ∈ Pow(x) ⇛ z ⊑ y"
      unfolding epart_def ..
    from abstraction and this have
      "x ⊑ y ⇛ z ∈ Pow(x) ⇛ z ∈ Pow(y)"
      unfolding powerset_def
      by(rule bisub_rule')
    }
    have "⋀ z. (x ⊑ y ⇛ z ∈ Pow(x) ⇛ z ∈ Pow(y))" by fact
    from this have
      "∀(λz. x ⊑ y ⇛ z ∈ Pow(x) ⇛ z ∈ Pow(y))" ..
    from all_cons and this show
      "x ⊑ y ⇛ Pow(x) ⊑ Pow(y)"
      unfolding epart_def ..
  qed

  lemma powerset_proper_emonotonic: "x ⊏ y ⇛ Pow(x) ⊏ Pow(y)"
    proof -
      from abstraction and epart_refl have
        step1:"y ∈ Pow(y)"
        unfolding powerset_def
        by(rule bisub_rule')

      {
      fix t
      from entl_contra and entl_ui have
        "¬(t ∈ y ⇛ t ∈ x) → ¬(y ⊑ x)"
        unfolding epart_def ..
      from entl_impl and this have
        "¬(t ∈ y ⇛ t ∈ x) ⇛ ¬(y ⊑ x)" ..
      from abstraction and this have
        "¬(t ∈ y ⇛ t ∈ x) ⇛ y ∉ Pow(x)"
        unfolding powerset_def
        by(rule bisub_rule')
      from impl_cex and this have
        step2:"t ∈ y ⊗ t ∉ x ⇛ y ∉ Pow(x)" ..

      from impl_conj_in and step1 have
        "y ∉ Pow(x) ⇛ y ∈ Pow(y) ⊗ y ∉ Pow(x)" ..
      from step2 and this have
        step3:"t ∈ y ⊗ t ∉ x ⇛ y ∈ Pow(y) ⊗ y ∉ Pow(x)" ..

      from entl_impl and entl_eg have
        "y ∈ Pow(y) ⊗ y ∉ Pow(x) ⇛ ∃(λw. w ∈ Pow(y) ⊗ w ∉ Pow(x))" ..
      from step3 and this have
        "t ∈ y ⊗ t ∉ x ⇛ ∃(λw. w ∈ Pow(y) ⊗ w ∉ Pow(x))" ..
      }
      have "⋀ t. (t ∈ y ⊗ t ∉ x ⇛ ∃(λw. w ∈ Pow(y) ⊗ w ∉ Pow(x)))" by fact
      from this have
        "∀(λt. t ∈ y ⊗ t ∉ x ⇛ ∃(λw. w ∈ Pow(y) ⊗ w ∉ Pow(x)))" ..
      from all_ante and this have
        "∃(λt. t ∈ y ⊗ t ∉ x) ⇛ ∃(λw. w ∈ Pow(y) ⊗ w ∉ Pow(x))" ..

      from powerset_emonotonic and this  have
        "(x ⊑ y ⇛ Pow(x) ⊑ Pow(y)) ⊗ (∃(λt. t ∈ y ⊗ t ∉ x) ⇛ ∃(λw. w ∈ Pow(y) ⊗ w ∉ Pow(x)))" ..
      from factor and this show
        "x ⊏ y ⇛ Pow(x) ⊏ Pow(y)"
        unfolding proper_epart_def ..
    qed

definition Uni :: "i"
  where "Uni ≡ {(λx. ∃(λy. x ∈ y))}"

definition Emp :: "i"
  where "Emp ≡ {(λx. ∀(λy. x ∈ y))}"

definition falsum :: "o" ("FALSE")
  where "FALSE ≡ Emp ∈ Emp"

abbreviation verum :: "o" ("⊤")
  where "⊤ ≡ ¬ FALSE"

lemma uni_is_universal: "z ∈ Uni"
  proof -
    from in_its_singleton have
      "∃(λy. z ∈ y)" ..
    from abstraction and this show
      "z ∈ Uni"
      unfolding Uni_def
      by(rule bisub_rule')
  qed

lemma uni_is_universal_superset: "z ⊆ Uni"
  proof -
    {
    fix x
    from abstraction and entl_eg have
      "x ∈ z → x ∈ Uni"
      unfolding Uni_def
      by(rule bisub_rule')
    }
    have "⋀ x. (x ∈ z → x ∈ Uni)" by fact
    from this show "z ⊆ Uni"
      unfolding subset_def ..
  qed

lemma emp_is_empty: "z ∉ Emp"
  proof -
    from abstraction have
      "z ∈ Emp → ∀(λy. z ∈ y)"
      unfolding bientl_def
      unfolding Emp_def ..
    from this and entl_ui have
      "z ∈ Emp → z ∈ {(λy. y ∉ Emp)}" ..
    from abstraction and this have
      "z ∈ Emp → z ∉ Emp"
      by(rule bisub_rule)
    from entl_impl and this have
      "z ∈ Emp ⇛ z ∉ Emp" ..

    from impl_disj_left and this have
      "(z ∉ Emp ⇛ z ∉ Emp) ⇛ z ∈ Emp ∨ z ∉ Emp ⇛ z ∉ Emp" ..
    from this and implI have
      "z ∈ Emp ∨ z ∉ Emp ⇛ z ∉ Emp" ..
    from this and lem show
      "z ∉ Emp" ..
  qed

lemma emp_is_universal_subset: "Emp ⊆ z"
  proof -
    {
    fix x
    from abstraction have
      "x ∈ Emp → ∀(λy. x ∈ y)"
      unfolding bientl_def
      unfolding Emp_def ..
    from this and entl_ui have
      "x ∈ Emp → x ∈ z" ..
    }
    have "⋀ x. (x ∈ Emp → x ∈ z)" by fact
    from this show
      "Emp ⊆ z"
      unfolding subset_def ..
  qed

lemma emp_uni_complement: "Emp = Uni*"
  proof -
    {
    fix x
    from abstraction have "∃(λy. x ∈ y) → x ∈ Uni"
      unfolding bientl_def
      unfolding Uni_def ..
    from entl_contra and this have
      "x ∉ Uni → ¬ ∃(λy. x ∈ y)" ..
    from dm_anns_bi and this have
      "x ∉ Uni → ∀(λy. x ∉ y)"
      by(rule bisub_rule')
    from this and entl_ui have
      "x ∉ Uni → x ∉ Emp*" ..
    from entl_contra and this have
      "¬¬(x ∈ Emp*) → ¬¬(x ∈ Uni)" ..
    from dn_bi' and this have
      "x ∈ Emp* → ¬¬(x ∈ Uni)"
      by(rule bisub_rule)
    from dn_bi' and this have
      "x ∈ Emp* → x ∈ Uni"
      by(rule bisub_rule)
    }
    have "⋀ x. (x ∈ Emp* → x ∈ Uni)" by fact
    from this have
      "Emp* ⊆ Uni"
      unfolding subset_def ..
    from subset_contra and this have
      "Uni* ⊆ Emp**" ..
    from double_complement and this have
      "Uni* ⊆ Emp"
      by(rule equals_sub_rule)
    from emp_is_universal_subset and this have
      "Emp ⊆ Uni* ⊗ Uni* ⊆ Emp" ..
    from subset_antisym and this show "Emp = Uni*" ..
  qed

lemma uni_emp_complement: "Uni = Emp*"
  proof -
    from emp_uni_complement and refl_without_refl have
      "Emp* = Uni**"
      by(rule equals_sub_rule)
    from double_complement and this have
      "Emp* = Uni"
      by(rule equals_sub_rule)
    from this and refl_without_refl show "Uni = Emp*"
      by(rule equals_sub_rule)
  qed

lemma efq: "FALSE → A"
  proof -
    from abstraction have
      "FALSE → ∀(λy. Emp ∈ y)"
      unfolding bientl_def
      unfolding falsum_def
      unfolding Emp_def ..
    from this and entl_ui have
      "FALSE → Emp ∈ {(λz. A)}" ..
    from abstraction and this show
      "FALSE → A"
      by(rule bisub_rule)
  qed

lemma eqt: "A → ⊤"
  proof -
    from entl_contra and efq have "¬¬A → ⊤" ..
    from dn_bi' and this show "A → ⊤"
      by(rule bisub_rule)
  qed

lemma verum_therum: "⊤"
  proof -
    from eqt and eqt show "⊤" ..
  qed

lemma emp_falsum: "Emp = {(λx. FALSE)}"
  proof -
    {
    fix y
    from abstraction and efq have
      "y ∈ {(λx. FALSE)} → y ∈ Emp"
      by(rule bisub_rule')
    }
    have "⋀ y. (y ∈ {(λx. FALSE)} → y ∈ Emp)" by fact
    from this have
      "{(λx. FALSE)} ⊆ Emp"
      unfolding subset_def ..
    from emp_is_universal_subset and this have
      "Emp ⊆ {(λx. FALSE)} ⊗ {(λx. FALSE)} ⊆ Emp" ..
    from subset_antisym and this show
      "Emp = {(λx. FALSE)}" ..
  qed

lemma emp_explodes: "y ∈ Emp → A"
  proof -
    from emp_falsum and entlI have
      "y ∈ Emp → y ∈ {(λx. FALSE)}"
      by(rule equals_sub_rule)
    from abstraction and this have
      "y ∈ Emp → FALSE"
      by(rule bisub_rule)
    from this and efq show ?thesis ..
  qed

 lemma emp_gives_logical_falsum: "x ∈ Emp ↔ ⊥"
   proof -
     from emp_explodes and efq_entl show ?thesis
       unfolding bientl_def ..
   qed

lemma uni_verum: "Uni = {(λx. ⊤)}"
  proof -
    {
    fix y
    from abstraction and eqt have
      "y ∈ Uni → y ∈ {(λx. ⊤)}"
      by(rule bisub_rule')
    }
    have "⋀ y. (y ∈ Uni → y ∈ {(λx. ⊤)})" by fact
    from this have
      "Uni ⊆ {(λx. ⊤)}"
      unfolding subset_def ..
    from this and uni_is_universal_superset have
      "Uni ⊆ {(λx. ⊤)} ⊗ {(λx. ⊤)} ⊆ Uni" ..
    from subset_antisym and this show
      "Uni = {(λx. ⊤)}" ..
  qed

lemma uni_implodes: "A → y ∈ Uni"
  proof -
    from uni_verum and entlI have
      "y ∈ {(λx. ⊤)} → y ∈ Uni"
      by(rule equals_sub_rule)
    from abstraction and this have
      "⊤ → y ∈ Uni"
      by(rule bisub_rule)
    from eqt and this show ?thesis ..
  qed

lemma uni_intersection_identity: "x ∩ Uni ≃ x"
  proof -
    {
    fix y
    from uni_verum and entlI have
      "y ∈ {(λx.⊤)} → y ∈ Uni"
      by(rule equals_sub_rule)
    from abstraction and this have
      "⊤ → y ∈ Uni"
      by(rule bisub_rule)
    from entl_impl and this have
      "⊤ ⇛ y ∈ Uni" ..
    from implI and this have
      "y ∈ x ⊗ ⊤ ⇛ y ∈ x ⊗ y ∈ Uni"
      by(rule factor_rule)
    from conj_bicomm and this have
      "⊤ ⊗ y ∈ x ⇛ y ∈ x ⊗ y ∈ Uni"
      by(rule bisub_rule)
    from conj_export and this have
      "⊤ ⇛ y ∈ x ⇛ y ∈ x ⊗ y ∈ Uni" ..
    from this and verum_therum have
      "y ∈ x ⇛ y ∈ x ⊗ y ∈ Uni" ..
    from intersection_conj and this have
      "y ∈ x ⇛ y ∈ x ∩ Uni"
      by(rule bisub_rule')
    }
    have "⋀ y. (y ∈ x ⇛ y ∈ x ∩ Uni)" by fact
    from this have
      step1: "x ⊑ x ∩ Uni"
      unfolding epart_def ..

    {
    fix y
    from intersection_conj and impl_cel have
      "y ∈ x ∩ Uni ⇛ y ∈ x"
      by(rule bisub_rule')
    }
    have "⋀ y. (y ∈ x ∩ Uni ⇛ y ∈ x)" by fact
    from this have
      "x ∩ Uni ⊑ x"
      unfolding epart_def ..

    from this and step1 have
      "x ∩ Uni ⊑ x ⊗ x ⊑ x ∩ Uni" ..
    from epart_antisym and this show
      "x ∩ Uni ≃ x" ..
  qed

lemma uni_union_uni: "x ∪ Uni = Uni"
  proof -
    from uni_implodes have
      ltr:"x ∪ Uni ⊆ Uni"
      unfolding subset_def ..

    {
    fix y
    from union_disj and entl_disj_inr have
      "y ∈ Uni → y ∈ x ∪ Uni"
      by(rule bisub_rule')
    }
    have "⋀ y. (y ∈ Uni → y ∈ x ∪ Uni)" by fact
    from this have
      rtl: "Uni ⊆ x ∪ Uni"
      unfolding subset_def ..

    from ltr and rtl have
      "x ∪ Uni ⊆ Uni ⊗ Uni ⊆ x ∪ Uni" ..
    from subset_antisym and this show ?thesis ..
  qed

lemma emp_union_identity: "x ∪ Emp ≃ x"
  proof -
    {
    fix y
    from entl_impl and emp_explodes have
      "y ∈ Emp ⇛ y ∈ x" ..
    from impl_disj_left and implI and this have
      "y ∈ x ∨ y ∈ Emp ⇛ y ∈ x" ..
    from union_disj and this have
      "y ∈ x ∪ Emp ⇛ y ∈ x"
      by(rule bisub_rule')
    }
    have "⋀ y. (y ∈ x ∪ Emp ⇛ y ∈ x)" by fact
    from this have
      ltr: "x ∪ Emp ⊑ x"
      unfolding epart_def ..

    {
    fix y
    from entl_impl and entl_disj_inl have
      "y ∈ x ⇛ y ∈ x ∨ y ∈ Emp" ..
    from union_disj and this have
      "y ∈ x ⇛ y ∈ x ∪ Emp"
      by(rule bisub_rule')
    }
    have "⋀ y. (y ∈ x ⇛ y ∈ x ∪ Emp)" by fact
    from this have
      rtl: "x ⊑ x ∪ Emp"
      unfolding epart_def ..

    from ltr and rtl have
      "x ∪ Emp ⊑ x ⊗ x ⊑ x ∪ Emp" ..
    from epart_antisym and this show ?thesis ..
  qed

lemma emp_intersection_emp: "x ∩ Emp = Emp"
  proof -
    {
    fix y
    from intersection_conj and entl_cer have
      "y ∈ x ∩ Emp → y ∈ Emp"
      by(rule bisub_rule')
    }
    have "⋀ y. (y ∈ x ∩ Emp → y ∈ Emp)" by fact
    from this have
      ltr: "x ∩ Emp ⊆ Emp"
      unfolding subset_def ..

    from emp_explodes have
      "Emp ⊆ x ∩ Emp"
      unfolding subset_def ..
    from ltr and this have
      "x ∩ Emp ⊆ Emp ⊗ Emp ⊆ x ∩ Emp" ..
    from subset_antisym and this show ?thesis ..
  qed

lemma union_lem: "x ∪ x* ≃ Uni"
  proof -
    {
    fix y
    from entl_impl and uni_implodes have
      "y ∈ x ∪ x* ⇛ y ∈ Uni" ..
    }
    have "⋀ y. (y ∈ x ∪ x* ⇛ y ∈ Uni)" by fact
    from this have
      ltr: "x ∪ x* ⊑ Uni"
      unfolding epart_def ..

    {
    fix y
    from implK and membership_union_complement_lem have
      "y ∈ Uni ⇛ y ∈ x ∪ x*" ..
    }
    have "⋀ y. (y ∈ Uni ⇛ y ∈ x ∪ x*)" by fact
    from this have
      rtl: "Uni ⊑ x ∪ x*"
      unfolding epart_def ..

    from ltr and rtl have
      "x ∪ x* ⊑ Uni ⊗ Uni ⊑ x ∪ x*" ..
    from epart_antisym and this show ?thesis ..
  qed

lemma emp_self_complement_is_emp: "!?Emp = Emp"
  proof -
    from uni_emp_complement and refl_without_refl have
      "!?Emp = Emp ∩ Uni"
      unfolding self_complement_def
      by(rule equals_sub_rule')
    from intersection_comm and this have
      "!?Emp = Uni ∩ Emp"
      by(rule equals_sub_rule)
    from emp_intersection_emp and this show ?thesis
      by(rule equals_sub_rule)
  qed

lemma uni_powerset_uni: "Pow(Uni) ≃ Uni"
  proof -
    {
    fix x
    from implK and uni_is_universal have
      "x ∈ Pow(Uni) ⇛ x ∈ Uni" ..
    }
    have "⋀ x. (x ∈ Pow(Uni) ⇛ x ∈ Uni)" by fact
    from this have
      ltr: "Pow(Uni) ⊑ Uni"
      unfolding epart_def ..

    {
    fix x
    from subset_epart and uni_is_universal_superset have
      "x ⊑ Uni" ..
    from abstraction and this have
      "x ∈ Pow(Uni)"
      unfolding powerset_def
      by(rule bientl_mp_rtl)
    from implK and this have
      "x ∈ Uni ⇛ x ∈ Pow(Uni)" ..
    }
    have "⋀ x. (x ∈ Uni ⇛ x ∈ Pow(Uni))" by fact
    from this have
      rtl: "Uni ⊑ Pow(Uni)"
      unfolding epart_def ..

    from ltr and rtl have
      "Pow(Uni) ⊑ Uni ⊗ Uni ⊑ Pow(Uni)" ..
    from epart_antisym and this show ?thesis ..
  qed

definition Rout :: "i"
  where "Rout ≡ {{(λx y. x ∉ y)}}"

definition Rout_of :: "i ⇒ i"
  where "Rout_of(x) ≡ x ∩ Rout"

lemma rout_own_complement: "Rout = Rout*"
  proof -
    {
    fix x
    from strong_abstraction have
      step1: "x ∈ Rout → x ∉ Rout"
      unfolding bientl_def
      unfolding Rout_def ..
    from abstraction have
      "x ∉ Rout → x ∈ Rout*"
      unfolding bientl_def
      unfolding complement_def ..
    from step1 and this have
      "x ∈ Rout → x ∈ Rout*" ..
    }
    have "⋀ x. (x ∈ Rout → x ∈ Rout*)" by fact
    from this have
      ltr: "Rout ⊆ Rout*"
      unfolding subset_def ..

    {
    fix x
    from strong_abstraction have
      step2: "x ∉ Rout → x ∈ Rout"
      unfolding bientl_def
      unfolding Rout_def ..
    from abstraction have
      "x ∈ Rout* → x ∉ Rout"
      unfolding bientl_def
      unfolding complement_def ..
    from this and step2 have
      "x ∈ Rout* → x ∈ Rout" ..
    }
    have "⋀ x. (x ∈ Rout* → x ∈ Rout)" by fact
    from this have
      rtl: "Rout* ⊆ Rout"
      unfolding subset_def ..

    from ltr and rtl have
      "Rout ⊆ Rout* ⊗ Rout* ⊆ Rout" ..
    from subset_antisym and this show ?thesis ..
  qed

lemma rout_is_universal: "x ∈ Rout"
  proof -
    from strong_abstraction have
      "x ∉ Rout → x ∈ Rout"
      unfolding bientl_def
      unfolding Rout_def ..
    from entl_impl and this have
      step1: "x ∉ Rout ⇛ x ∈ Rout" ..

    from impl_disj_left and implI have
      "(x ∉ Rout ⇛ x ∈ Rout) ⇛ (x ∈ Rout ∨ x ∉ Rout) ⇛ x ∈ Rout" ..
    from this and step1 have
      "x ∈ Rout ∨ x ∉ Rout ⇛ x ∈ Rout" ..
    from this and lem show ?thesis ..
  qed

lemma rout_is_empty: "x ∉ Rout"
  proof -
    from strong_abstraction have
      "x ∈ Rout → x ∉ Rout"
      unfolding bientl_def
      unfolding Rout_def ..
    from entl_impl and this have
      step1: "x ∈ Rout ⇛ x ∉ Rout" ..

    from impl_disj_left and step1 have
      "(x ∉ Rout ⇛ x ∉ Rout) ⇛ (x ∈ Rout ∨ x ∉ Rout) ⇛ x ∉ Rout" ..
    from this and implI have
      "x ∈ Rout ∨ x ∉ Rout ⇛ x ∉ Rout" ..
    from this and lem show ?thesis ..
  qed

lemma rout_of_is_empty: "y ∉ Rout_of(x)"
  proof -
    from intersection_conj have
      "y ∈ Rout_of(x) → y ∈ x ⊗ y ∈ Rout"
      unfolding Rout_of_def
      unfolding bientl_def ..
    from entl_contra and this have
      "¬(y ∈ x ⊗ y ∈ Rout) → y ∉ Rout_of(x)" ..
    from entl_ncir and this have
      "y ∉ Rout → y ∉ Rout_of(x)" ..
    from this and rout_is_empty show ?thesis ..
  qed

lemma rout_of_is_eequiv: "x ≃ Rout_of(x)"
  proof -
    {
    fix y
    from implC and impl_conj_in have
      "y ∈ Rout ⇛ y ∈ x ⇛ y ∈ x ⊗ y ∈ Rout" ..
    from this and rout_is_universal have
      step1: "y ∈ x ⇛ y ∈ x ⊗ y ∈ Rout" ..
    from intersection_conj have
      "y ∈ x ⊗ y ∈ Rout → y ∈ Rout_of(x)"
      unfolding Rout_of_def
      unfolding bientl_def ..
    from entl_impl and this have
      "y ∈ x ⊗ y ∈ Rout ⇛ y ∈ Rout_of(x)" ..
    from step1 and this have
      "y ∈ x ⇛ y ∈ Rout_of(x)" ..
    }
    have "⋀ y. (y ∈ x ⇛ y ∈ Rout_of(x))" by fact
    from this have
      ltr: "x ⊑ Rout_of(x)"
      unfolding epart_def ..

    from subset_epart and intersection_subset have
      rtl: "Rout_of(x) ⊑ x"
      unfolding Rout_of_def ..

    from ltr and rtl have
      "x ⊑ Rout_of(x) ⊗ Rout_of(x) ⊑ x" ..
    from epart_antisym and this show ?thesis ..
  qed

  lemma rout_of_nonempty_is_proper_subset: "y ∈ x ⇛ Rout_of(x) ⊂ x"
    proof -
      from implC and impl_conj_in have
        "y ∉ Rout_of(x) ⇛ y ∈ x ⇛ y ∈ x ⊗ y ∉ Rout_of(x)" ..
      from this and rout_of_is_empty have
        "y ∈ x ⇛ y ∈ x ⊗ y ∉ Rout_of(x)" ..
      from this and impl_eg have
        step1: "y ∈ x ⇛ ∃(λz. z ∈ x ⊗ z ∉ Rout_of(x))" ..

      from impl_conj_in and intersection_subset have
        "∃(λz. z ∈ x ⊗ z ∉ Rout_of(x)) ⇛ Rout_of(x) ⊆ x ⊗ ∃(λz. z ∈ x ⊗ z ∉ Rout_of(x))"
        unfolding Rout_of_def ..
      from step1 and this show ?thesis
        unfolding proper_subset_def ..
    qed

lemma rout_of_preserves_membership: "y ∈ x ⇛ y ∈ Rout_of(x)"
  proof -
    from impl_conj_in and rout_is_universal have 
      "y ∈ x ⇛ y ∈ x ⊗ y ∈ Rout" ..
    from intersection_conj and this show ?thesis
      unfolding Rout_of_def
      by(rule bisub_rule')
  qed

lemma rout_of_nonempty_is_nonselfidentical: "y ∈ x ⇛ Rout_of(x) ≠ Rout_of(x)"
  proof -
    from rout_of_preserves_membership and impl_conj_in have 
      "y ∈ x ⇛ y ∉ Rout_of(x) ⇛ y ∈ Rout_of(x) ⊗ y ∉ Rout_of(x)" ..
    from this and rout_of_is_empty have
      "y ∈ x ⇛ y ∈ Rout_of(x) ⊗ y ∉ Rout_of(x)" ..
    from this and impl_eg have
      "y ∈ x ⇛ ∃(λz. z ∈ Rout_of(x) ⊗ z ∉ Rout_of(x))" ..
    from this and counterexample_nonidentity show ?thesis ..
  qed

lemma zermelo_pair: "∀(λx. ∀(λy. ∃(λz. z = {(λw. w = x ∨ w = y)})))"
  proof -
    {
    fix x
    {
    fix y
    from refl_without_refl have
      "∃(λz. z = {(λw. w = x ∨ w = y)})" ..
    }
    have "⋀ y. (∃(λz. z = {(λw. w = x ∨ w = y)}))" by fact
    from this have
      "∀(λy. ∃(λz. z = {(λw. w = x ∨ w = y)}))" ..
    }
    have "⋀ x. (∀(λy. ∃(λz. z = {(λw. w = x ∨ w = y)})))" by fact
    from this show ?thesis ..
  qed

lemma zermelo_separation: "∀(λz. ∃(λy. y = {(λx. P(x) ⊗ x ∈ z)}))"
  proof -
    {
    fix z
    from refl_without_refl have
      "∃(λy. y = {(λx. P(x) ⊗ x ∈ z)})" ..
    }
    have "⋀ z. ∃(λy. y = {(λx. P(x) ⊗ x ∈ z)})" by fact
    from this show ?thesis ..
  qed

lemma zermelo_union: "∀(λx. ∃(λy. y = {(λz. ∃(λu. u ∈ x ⊗ z ∈ u))}))"
  proof -
    {
    fix x
    from refl_without_refl have
      "∃(λy. y = {(λz. ∃(λu. u ∈ x ⊗ z ∈ u))})" ..
    }
    have "⋀ x. ∃(λy. y = {(λz. ∃(λu. u ∈ x ⊗ z ∈ u))})" by fact
    from this show ?thesis ..
  qed

lemma zermelo_powerset: "∀(λx. ∃(λy. y = {(λz. z ⊆ x)}))"
  proof -
    {
    fix x
    from refl_without_refl have
      "∃(λy. y = {(λz. z ⊆ x)})" ..
    }
    have "⋀ x. ∃(λy. y = {(λz. z ⊆ x)})" by fact
    from this show ?thesis ..
  qed

lemma zermelo_infinity_1: "∃(λx. (∃(λy. y ∈ x) ⊗ ∀(λz. z ∈ x ⇛ {!z} ∈ x)))"
  proof -
    from uni_is_universal have
      step1: "∃(λy. y ∈ Uni)" ..

    {
    fix z
    from implK and uni_is_universal have
      "z ∈ Uni ⇛ {!z} ∈ Uni" ..
    }
    have "⋀ z. (z ∈ Uni ⇛ {!z} ∈ Uni)" by fact
    from this have
      "∀(λz. z ∈ Uni ⇛ {!z} ∈ Uni)" ..
    from step1 and this have
      "∃(λy. y ∈ Uni) ⊗ ∀(λz. z ∈ Uni ⇛ {!z} ∈ Uni)" ..
    from this show ?thesis ..
  qed

lemma zermelo_infinity_2: "∃(λx. ∃(λy. y ⊂ x ⊗ x = y))"
  proof -
    from russ_self_member and russ_not_self_member have
      "russ ∈ russ ⊗ russ ∉ russ" ..
    from this have
      "∃(λz. z ∈ russ ⊗ z ∉ russ)" ..
    from subset_refl and this have
      "russ ⊂ russ"
      unfolding proper_subset_def ..
    from this and refl_without_refl have
      "russ ⊂ russ ⊗ russ = russ" ..
    from this have
      "∃(λy. y ⊂ russ ⊗ russ = y)" ..
    from this show ?thesis ..
  qed

definition upair :: "i ⇒ i ⇒ i" ("{!! _, _}" [80] 80)
  where "{!! x, y} ≡ {(λw. w = x ∨ w = y)}"

definition opair :: "i ⇒ i ⇒ i" ("<_, _>" [80] 80)
  where "<x, y> ≡ {!! {!x}, ({!! x, y})}"

lemma upair_contains_member1: "x ∈ {!! x, y}"
  proof -
    from entl_disj_inl and refl_without_refl have
      "x = x ∨ x = y" ..
    from abstraction' and this show ?thesis
      unfolding upair_def ..
  qed

lemma upair_contains_member2: "y ∈ {!! x, y}"
  proof -
    from entl_disj_inr and refl_without_refl have
      "y = x ∨ y = y" ..
    from abstraction' and this show ?thesis
      unfolding upair_def ..
  qed

lemma upair_is_unordered: "{!! x, y} = {!! y, x}"
  proof -
    {
    fix w
    from disj_bicomm and abstraction have
      "w ∈ {!! x, y} ↔ w = y ∨ w = x"
      unfolding upair_def
      by(rule bisub_rule)
    from this and abstraction' have
      "w ∈ {!! x, y} ↔ w ∈ {!! y, x}"
      unfolding upair_def
      by(rule bientl_trans_rule)
    }
    have "⋀ w. (w ∈ {!! x, y} ↔ w ∈ {!! y, x})" by fact
    from this have
      "∀(λw. w ∈ {!! x, y} ↔ w ∈ {!! y, x})" ..
    from extensionality and this show ?thesis ..
  qed

lemma upair_equals_split_aux: "{!! x, y} = {!! u, v} ⇛ (y = u ⊗ v = x) ∨ y = v"
  proof -
    from equals_sub_impl and upair_contains_member2 have
      "{!! u, v} = {!! x, y} ⇛ v ∈ {!! x, y}"
      by(rule entl_mp_under_impl)
    from eq_sym_bientl and this have
      "{!! x, y} = {!! u, v} ⇛ v ∈ {!! x, y}"
      by(rule bisub_rule)
    from abstraction and this have
      cases:"{!! x, y} = {!! u, v} ⇛ v = x ∨ v = y"
      unfolding upair_def
      by(rule bisub_rule)

    from equals_sub_impl and upair_contains_member2 have
      "{!! x, y} = {!! u, v} ⇛ y ∈ {!! u, v}"
      by(rule entl_mp_under_impl)
    from abstraction and this have
      "{!! x, y} = {!! u, v} ⇛ y = u ∨ y = v"
      unfolding upair_def
      by(rule bisub_rule)

    from cases and this have
      "{!! x, y} = {!! u, v} ⊗ {!! x, y} = {!! u, v} ⇛ (v = x ∨ v = y) ⊗ (y = u ∨ y = v)"
      by(rule factor_rule)
    from identity_contracts and this have
      step1:"{!! x, y} = {!! u, v} ⇛ (v = x ∨ v = y) ⊗ (y = u ∨ y = v)" ..

    from dist_cd_biimpl have
      "(v = x ∨ v = y) ⊗ (y = u ∨ y = v) ⇛ ((v = x ∨ v = y) ⊗ y = u) ∨ ((v = x ∨ v = y) ⊗ y = v)"
      unfolding biimpl_def ..
    from step1 and this have
      "{!! x, y} = {!! u, v} ⇛ ((v = x ∨ v = y) ⊗ y = u) ∨ ((v = x ∨ v = y) ⊗ y = v)" ..
    from this and cer_under_disjr have
      "{!! x, y} = {!! u, v} ⇛ ((v = x ∨ v = y) ⊗ y = u) ∨ y = v" ..
    from disj_bicomm and this have
      step2:"{!! x, y} = {!! u, v} ⇛ y = v ∨ ((v = x ∨ v = y) ⊗ y = u)"
      by(rule bisub_rule)

    from dist_cd_biimpl have
      "y = u ⊗ (v = x ∨ v = y) ⇛ (y = u ⊗ v = x) ∨ (y = u ⊗ v = y)"
      unfolding biimpl_def ..
    from conj_bicomm and this have
      "(v = x ∨ v = y) ⊗ y = u ⇛ (y = u ⊗ v = x) ∨ (y = u ⊗ v = y)"
      by(rule bisub_rule)
    from this and cer_under_disjr have
      "(v = x ∨ v = y) ⊗ y = u ⇛ (y = u ⊗ v = x) ∨ v = y" ..
    from eq_sym_bientl and this have
      step3:"(v = x ∨ v = y) ⊗ y = u ⇛ (y = u ⊗ v = x) ∨ y = v"
      by(rule bisub_rule)

    from impl_disj_left and impl_disj_inr have
      "((v = x ∨ v = y) ⊗ y = u ⇛ (y = u ⊗ v = x) ∨ y = v) ⇛ y = v ∨ ((v = x ∨ v = y) ⊗ y = u) ⇛ (y = u ⊗ v = x) ∨ y = v" ..
    from this and step3 have
      "y = v ∨ ((v = x ∨ v = y) ⊗ y = u) ⇛ (y = u ⊗ v = x) ∨ y = v" ..
    from step2 and this show
      "{!! x, y} = {!! u, v} ⇛ (y = u ⊗ v = x) ∨ y = v" ..
  qed

lemma upair_equals_split: "{!! x, y} = {!! u, v} ⇛ (x = u ⊗ y = v) ∨ (x = v ⊗ y = u)"
  proof -
    from upair_equals_split_aux and upair_equals_split_aux have
      "{!! x, y} = {!! u, v} ⊗ {!! y, x} = {!! v, u} ⇛ ((y = u ⊗ v = x) ∨ y = v) ⊗ ((x = v ⊗ u = y) ∨ x = u)"
      by(rule factor_rule)
    from upair_is_unordered and this have
      "{!! x, y} = {!! u, v} ⊗ {!! x, y} = {!! v, u} ⇛ ((y = u ⊗ v = x) ∨ y = v) ⊗ ((x = v ⊗ u = y) ∨ x = u)"
      by(rule equals_sub_rule)
    from upair_is_unordered and this have
      "{!! x, y} = {!! u, v} ⊗ {!! x, y} = {!! u, v} ⇛ ((y = u ⊗ v = x) ∨ y = v) ⊗ ((x = v ⊗ u = y) ∨ x = u)"
      by(rule equals_sub_rule)
    from identity_contracts and this have
      "{!! x, y} = {!! u, v} ⇛ ((y = u ⊗ v = x) ∨ y = v) ⊗ ((x = v ⊗ u = y) ∨ x = u)" ..
    from eq_sym_bientl and this have
      "{!! x, y} = {!! u, v} ⇛ ((y = u ⊗ x = v) ∨ y = v) ⊗ ((x = v ⊗ u = y) ∨ x = u)"
      by(rule bisub_rule)
    from eq_sym_bientl and this have
      "{!! x, y} = {!! u, v} ⇛ ((y = u ⊗ x = v) ∨ y = v) ⊗ ((x = v ⊗ y = u) ∨ x = u)"
      by(rule bisub_rule)
    from conj_bicomm and this have
      "{!! x, y} = {!! u, v} ⇛ ((x = v ⊗ y = u) ∨ y = v) ⊗ ((x = v ⊗ y = u) ∨ x = u)"
      by(rule bisub_rule)
    from conj_bicomm and this have
      "{!! x, y} = {!! u, v} ⇛ ((x = v ⊗ y = u) ∨ x = u) ⊗ ((x = v ⊗ y = u) ∨ y = v)"
      by(rule bisub_rule)
    from this and conj_in_under_disjr have
      "{!! x, y} = {!! u, v} ⇛ (x = v ⊗ y = u) ∨ (x = u ⊗ y = v)" ..
    from disj_bicomm and this show ?thesis
      by(rule bisub_rule)
  qed

lemma upair_equals_combine_aux: "(x = u ⊗ y = v) ⇛ {!! x, y} = {!! u, v}"
  proof -
    from equals_sub_impl and equals_sub_impl have
      "x = u ⊗ y = v ⇛ ({!! x, y} = {!! x, y} → {!! x, y} = {!! u, y}) ⊗ ({!! x, y} = {!! u, y} → {!! x, y} = {!! u, v})"
      by(rule factor_rule)
    from this and entl_cs have
      "x = u ⊗ y = v ⇛ ({!! x, y} = {!! x, y} → {!! x, y} = {!! u, v})"
      by(rule entl_after_impl_trans)
    from this and entl_impl have
      "x = u ⊗ y = v ⇛ {!! x, y} = {!! x, y} ⇛ {!! x, y} = {!! u, v}" ..
    from this and refl show ?thesis ..
  qed

lemma upair_equals_combine: "(x = u ⊗ y = v) ∨ (x = v ⊗ y = u) ⇛ {!! x, y} = {!! u, v}"
  proof -
    from impl_disj_left and upair_equals_combine_aux have
      step1:"(x = v ⊗ y = u ⇛ {!! x, y} = {!! u, v}) ⇛ (x = u ⊗ y = v) ∨ (x = v ⊗ y = u) ⇛ {!! x, y} = {!! u, v}" ..
    from upair_is_unordered and upair_equals_combine_aux have
      "x = v ⊗ y = u ⇛ {!! x, y} = {!! u, v}"
      by(rule equals_sub_rule)
    from step1 and this show ?thesis ..
  qed

lemma upair_singleton_lemma1: "{!x} = {!u} ⊗ {!! x, y} = {!! u, v} ⇛ y = v"
  proof -
    from upair_equals_split and cer_under_disjl have
      step1:"{!! x, y} = {!! u, v} ⇛ y = v ∨ (x = v ⊗ y = u)" ..
    from impl_disj_left and implI have
      step2:"(x = v ⊗ y = u ⇛ y = v) ⇛ y = v ∨ (x = v ⊗ y = u) ⇛ y = v" ..

    from singleton_reflects_equality and equals_sub_impl have
      "{!x} = {!u} ⇛ (x = v ⊗ y = u → u = v ⊗ y = u)" ..
    from this and entl_impl have
      "{!x} = {!u} ⇛ x = v ⊗ y = u ⇛ u = v ⊗ y = u" ..
    from conj_bicomm and this have
      "{!x} = {!u} ⇛ x = v ⊗ y = u ⇛ y = u ⊗ u = v"
      by(rule bisub_rule)
    from eq_trans and this have
      "{!x} = {!u} ⇛ x = v ⊗ y = u ⇛ y = v"
      by(rule impl_link_121)

    from this and step2 have
      "{!x} = {!u} ⇛ y = v ∨ (x = v ⊗ y = u) ⇛ y = v" ..
    from this and step1 have
      "{!x} = {!u} ⇛ {!! x, y} = {!! u, v} ⇛ y = v"
      by(rule impl_link_212)
    from conj_import and this show ?thesis ..
  qed

lemma upair_singleton_lemma2: "{!x} = {!! u, v} ⇛ x = u ⊗ x = v"
  proof -
    from extensionality and impl_ui have
      "{!x} = {!! u, v} ⇛ (u ∈ {!x} ↔ u ∈ {!! u, v})"
      by(rule bisub_rule)
    from this and impl_cer have
      "{!x} = {!! u, v} ⇛ (u ∈ {!! u, v} → u ∈ {!x})"
      unfolding bientl_def ..
    from this and upair_contains_member1 have
      "{!x} = {!! u, v} ⇛ u ∈ {!x}"
      by(rule entl_mp_under_impl)
    from this and in_singleton_equals have
      "{!x} = {!! u, v} ⇛ u = x"
      by(rule entl_after_impl_trans)
    from eq_sym_bientl and this have
      step1:"{!x} = {!! u, v} ⇛ x = u"
      by(rule bisub_rule)

    from extensionality and impl_ui have
      "{!x} = {!! u, v} ⇛ (v ∈ {!x} ↔ v ∈ {!! u, v})"
      by(rule bisub_rule)
    from this and impl_cer have
      "{!x} = {!! u, v} ⇛ (v ∈ {!! u, v} → v ∈ {!x})"
      unfolding bientl_def ..
    from this and upair_contains_member2 have
      "{!x} = {!! u, v} ⇛ v ∈ {!x}"
      by(rule entl_mp_under_impl)
    from this and in_singleton_equals have
      "{!x} = {!! u, v} ⇛ v = x"
      by(rule entl_after_impl_trans)
    from eq_sym_bientl and this have
      "{!x} = {!! u, v} ⇛ x = v"
      by(rule bisub_rule)

    from step1 and this have
      "{!x} = {!! u, v} ⊗ {!x} = {!! u, v} ⇛ x = u ⊗ x = v"
      by(rule factor_rule)
    from identity_contracts and this show ?thesis ..
  qed

lemma opair_equals_split: "<x, y> = <u, v> ⇛ x = u ⊗ y = v"
  proof -
    have step1:"<x, y> = <u, v> ⇛ ({!x} = {!u} ⊗ {!! x, y} = {!! u, v}) ∨ ({!x} = {!! u, v} ⊗ {!! x, y} = {!u})"
      unfolding opair_def
      by(rule upair_equals_split)

    from singleton_reflects_equality and upair_singleton_lemma1 have
      "{!x} = {!u} ⊗ ({!x} = {!u} ⊗ {!! x, y} = {!! u, v}) ⇛ x = u ⊗ y = v"
      by(rule factor_rule)
    from conj_biass and this have
      "({!x} = {!u} ⊗ {!x} = {!u}) ⊗ {!! x, y} = {!! u, v} ⇛ x = u ⊗ y = v"
      by(rule bisub_rule)
    from conj_export and this have
      "{!x} = {!u} ⊗ {!x} = {!u} ⇛ {!! x, y} = {!! u, v} ⇛ x = u ⊗ y = v" ..
    from identity_contracts and this have
      "{!x} = {!u} ⇛ {!! x, y} = {!! u, v} ⇛ x = u ⊗ y = v" ..
    from conj_import and this have
      horn1:"{!x} = {!u} ⊗ {!! x, y} = {!! u, v} ⇛ x = u ⊗ y = v" ..

    from upair_singleton_lemma2 and upair_singleton_lemma2 have
      "{!x} = {!! u, v} ⊗ {!u} = {!! x, y} ⇛ (x = u ⊗ x = v) ⊗ (u = x ⊗ u = y)"
      by(rule factor_rule)
    from conj_biass and this have
      step2:"{!x} = {!! u, v} ⊗ {!u} = {!! x, y} ⇛ x = u ⊗ (x = v ⊗ (u = x ⊗ u = y))"
      by(rule bisub_rule')

    from impl_conj_in and eq_trans have
      "x = v ⊗ (u = x ⊗ u = y) ⇛ (x = v ⊗ (u = x ⊗ u = y)) ⊗ (x = u ⊗ u = y ⇛ x = y)" ..
    from eq_sym_bientl and this have
      "x = v ⊗ (u = x ⊗ u = y) ⇛ (x = v ⊗ (x = u ⊗ u = y)) ⊗ (x = u ⊗ u = y ⇛ x = y)"
      by(rule bisub_rule)
    from this and conj_monotone_right have
      "x = v ⊗ (u = x ⊗ u = y) ⇛ x = v ⊗ x = y" ..
    from eq_sym_bientl and this have
      "x = v ⊗ (u = x ⊗ u = y) ⇛ v = x ⊗ x = y"
      by(rule bisub_rule)
    from this and eq_trans have
      "x = v ⊗ (u = x ⊗ u = y) ⇛ v = y" ..
    from impl_conj_in and this have
      "x = u ⇛ x = v ⊗ (u = x ⊗ u = y) ⇛ x = u ⊗ v = y"
      by(rule impl_link_212)
    from conj_import and this have
      "x = u ⊗ (x = v ⊗ (u = x ⊗ u = y)) ⇛ x = u ⊗ v = y" ..
    from step2 and this have
      "{!x} = {!! u, v} ⊗ {!u} = {!! x, y} ⇛ x = u ⊗ v = y" ..
    from eq_sym_bientl and this have
      "{!x} = {!! u, v} ⊗ {!u} = {!! x, y} ⇛ x = u ⊗ y = v"
      by(rule bisub_rule)
    from eq_sym_bientl and this have
      horn2:"{!x} = {!! u, v} ⊗ {!! x, y} = {!u} ⇛ x = u ⊗ y = v"
      by(rule bisub_rule)

    from horn1 and horn2 have
      "({!x} = {!u} ⊗ {!! x, y} = {!! u, v}) ∨ ({!x} = {!! u, v} ⊗ {!! x, y} = {!u}) ⇛ x = u ⊗ y = v"
      by(rule disj_left_rule)
    from step1 and this show ?thesis ..
  qed

lemma opair_equals_combine: "x = u ⊗ y = v ⇛ <x, y> = <u, v>"
  proof -
    from equals_sub_impl and refl_without_refl have
      link1: "x = u ⇛ <x, y> = <u, y>"
      by(rule entl_mp_under_impl)
    from equals_sub_impl and refl_without_refl have
      "y = v ⇛ <u, y> = <u, v>"
      by(rule entl_mp_under_impl)
    from link1 and this have
      "(x = u ⇛ <x, y> = <u, y>) ⊗ (y = v ⇛ <u, y> = <u, v>)" ..
    from factor and this have
      "x = u ⊗ y = v ⇛ <x, y> = <u, y> ⊗ <u, y> = <u, v>" ..
    from this and eq_trans show ?thesis ..
  qed

 lemma ordered_pairs: "<x, y> = <u, v> ⇌ x = u ⊗ y = v"
   proof -
     from opair_equals_split and opair_equals_combine show ?thesis
       unfolding biimpl_def ..
   qed

definition cprod :: "i ⇒ i ⇒ i" ("_ × _" [80] 80)
  where "x × y ≡ {(λw. ∃(λu. ∃(λv. w = <u, v> ⊗ (u ∈ x ⊗ v ∈ y))))}"

definition im :: "i ⇒ i ⇒ i" ("_ im _" [80] 80)
  where "x im y ≡ {(λz. ∃(λw. <w, z> ∈ x ⊗ w ∈ y))}"

definition fix1 :: "i ⇒ i"
  where "fix1 z ≡ {(λx. <x, z> ∈ z)}"

definition fix2 ::  "(i ⇒ o) ⇒ i"
  where "fix2 P ≡ {(λu. ∃(λx. ∃(λy. u = <x, y> ⊗ P(fix1 y))))}"

lemma im_monotone_right: "a ⊑ b ⇛ (x im a) ⊑ (x im b)"
  proof -
    {
    fix z
    {
    fix w
    from implI and impl_ui have
      "a ⊑ b ⇛ w ∈ a ⇛ w ∈ b"
      unfolding epart_def ..
    from this and add_conjunct_on_left have
      "a ⊑ b ⇛ <w, z> ∈ x ⊗ w ∈ a ⇛ <w, z> ∈ x ⊗ w ∈ b" ..
    }
    have "⋀ w. (a ⊑ b ⇛ <w, z> ∈ x ⊗ w ∈ a ⇛ <w, z> ∈ x ⊗ w ∈ b)" by fact
    from this have
      "∀(λw. a ⊑ b ⇛ <w, z> ∈ x ⊗ w ∈ a ⇛ <w, z> ∈ x ⊗ w ∈ b)" ..
    from all_cons and this have
      "a ⊑ b ⇛ ∀(λw. <w, z> ∈ x ⊗ w ∈ a ⇛ <w, z> ∈ x ⊗ w ∈ b)" ..
    from this and impl_some_monotone have
      "a ⊑ b ⇛ ∃(λw. <w, z> ∈ x ⊗ w ∈ a) ⇛ ∃(λw. <w, z> ∈ x ⊗ w ∈ b)" ..
    from abstraction and this have
      "a ⊑ b ⇛ z ∈ (x im a) ⇛ ∃(λw. <w, z> ∈ x ⊗ w ∈ b)"
      unfolding im_def
      by(rule bisub_rule')
    from abstraction and this have
      "a ⊑ b ⇛ z ∈ (x im a) ⇛ z ∈ (x im b)"
      unfolding im_def
      by(rule bisub_rule')
    }
    have "⋀ z. (a ⊑ b ⇛ z ∈ (x im a) ⇛ z ∈ (x im b))" by fact
    from this have
      "∀(λz. a ⊑ b ⇛ z ∈ (x im a) ⇛ z ∈ (x im b))" ..
    from all_cons and this show ?thesis
      unfolding epart_def ..
  qed

lemma im_preserves_empty: "∀(λx. x ∉ a) ⇛ v ∉ (f im a)"
  proof -
    {
    fix y
    from entl_impl and entl_ncir have
      "y ∉ a ⇛ ¬(<y, v> ∈ f ⊗ y ∈ a)" ..
    from impl_ui and this have
      "∀(λx. x ∉ a) ⇛ ¬(<y, v> ∈ f ⊗ y ∈ a)" ..
    }
    have "⋀ y. (∀(λx. x ∉ a) ⇛ ¬(<y, v> ∈ f ⊗ y ∈ a))" by fact
    from this have
      "∀(λu. ∀(λx. x ∉ a) ⇛ ¬(<u, v> ∈ f ⊗ u ∈ a))" ..
    from all_cons and this have
      "∀(λx. x ∉ a) ⇛ ∀(λu. ¬(<u, v> ∈ f ⊗ u ∈ a))" ..
    from dm_anns_bi and this have
      "∀(λx. x ∉ a) ⇛ ¬ ∃(λu. <u, v> ∈ f ⊗ u ∈ a)"
      by(rule bisub_rule)
    from abstraction and this show ?thesis
      unfolding im_def
      by(rule bisub_rule')
  qed

lemma fixed_point_ltr: "x ∈ fix1 (fix2 P) ⇛ P(fix1 (fix2 P))"
  proof -
    from abstraction have
      "x ∈ fix1 (fix2 P) → <x, fix2 P> ∈ fix2 P"
      unfolding bientl_def and fix1_def ..
    from abstraction and this have
      "x ∈ fix1 (fix2 P) → ∃(λw. ∃(λv. <x, fix2 P> = <w, v> ⊗ P(fix1 v)))"
      unfolding fix2_def
      by(rule bisub_rule)
    from entl_impl and this have
      step1:"x ∈ fix1 (fix2 P) ⇛ ∃(λw. ∃(λv. <x, fix2 P> = <w, v> ⊗ P(fix1 v)))" ..

    {
    fix w
    {
    fix v
    from eq_sym_bientl and equals_sub_impl have
      "(fix2 P) = v ⇛ (P(fix1 v) → P(fix1 (fix2 P)))"
      by(rule bisub_rule)
    from this and entl_impl have
      "(fix2 P) = v ⇛ P(fix1 v) ⇛ P(fix1 (fix2 P))" ..
    from impl_cer and this have
      "x = w ⊗ (fix2 P) = v ⇛ P(fix1 v) ⇛ P(fix1 (fix2 P))" ..
    from opair_equals_split and this have
      "<x, fix2 P> = <w, v> ⇛ P(fix1 v) ⇛ P(fix1 (fix2 P))" ..
    from conj_import and this have
      "<x, fix2 P> = <w, v> ⊗ P(fix1 v) ⇛ P(fix1 (fix2 P))" ..
    }
    have "⋀ v. (<x, fix2 P> = <w, v> ⊗ P(fix1 v) ⇛ P(fix1 (fix2 P)))" by fact
    from this have
      "∀(λv. <x, fix2 P> = <w, v> ⊗ P(fix1 v) ⇛ P(fix1 (fix2 P)))" ..
    from all_ante and this have
      "∃(λv. <x, fix2 P> = <w, v> ⊗ P(fix1 v)) ⇛ P(fix1 (fix2 P))" ..
    }
    have "⋀ w. (∃(λv. <x, fix2 P> = <w, v> ⊗ P(fix1 v)) ⇛ P(fix1 (fix2 P)))" by fact
    from this have
      "∀(λw. ∃(λv. <x, fix2 P> = <w, v> ⊗ P(fix1 v)) ⇛ P(fix1 (fix2 P)))" ..
    from all_ante and this have
      "∃(λw. ∃(λv. <x, fix2 P> = <w, v> ⊗ P(fix1 v))) ⇛ P(fix1 (fix2 P))" ..
    from step1 and this show ?thesis ..
  qed

lemma fixed_point_rtl: "P(fix1 (fix2 P)) ⇛ x ∈ fix1 (fix2 P)"
  proof -
    from impl_conj_in and refl have
      "P(fix1 (fix2 P)) ⇛ <x, fix2 P> = <x, fix2 P> ⊗ P(fix1 (fix2 P))" ..
    from this and impl_eg have
      "P(fix1 (fix2 P)) ⇛ ∃(λv. <x, fix2 P> = <x, v> ⊗ P(fix1 v))" ..
    from this and impl_eg have
      "P(fix1 (fix2 P)) ⇛ ∃(λu. ∃(λv. <x, fix2 P> = <u, v> ⊗ P(fix1 v)))" ..
    from abstraction and this have
      "P(fix1 (fix2 P)) ⇛ <x, fix2 P> ∈ (fix2 P)"
      unfolding fix2_def
      by(rule bisub_rule')
    from abstraction and this show ?thesis
      unfolding fix1_def
      by(rule bisub_rule')
  qed

lemma fixed_point: "∃(λt. ∀(λx. (x ∈ t ⇛ P(t)) ⊗ (P(t) ⇛ x ∈ t)))"
  proof -
    {
    fix x
    from fixed_point_ltr and fixed_point_rtl have
      "(x ∈ fix1 (fix2 P) ⇛ P(fix1 (fix2 P))) ⊗ (P(fix1 (fix2 P)) ⇛ x ∈ fix1 (fix2 P))"
      by(rule conj_intro)
    }
    have "⋀ x. ((x ∈ fix1 (fix2 P) ⇛ P(fix1 (fix2 P))) ⊗ (P(fix1 (fix2 P)) ⇛ x ∈ fix1 (fix2 P)))" by fact
    from this have
      "∀(λx. (x ∈ fix1 (fix2 P) ⇛ P(fix1 (fix2 P))) ⊗ (P(fix1 (fix2 P)) ⇛ x ∈ fix1 (fix2 P)))" ..
    from this show ?thesis ..
  qed

lemma cantor: "∃(λy. y ⊆ x ⊗ ∀(λz. z ∈ x ⇛ ∀(λw. w ∈ (f im z) ⇛ y ≠ w)))"
  proof -
    {fix z
      {fix w
        from implK and rout_of_nonempty_is_nonselfidentical have 
          "w ∈ (f im z) ⇛ z ∈ x ⇛ Rout_of(x) ≠ Rout_of(x)" ..
        from nonselfidentity_nonidentity and this have
          "w ∈ (f im z) ⇛ z ∈ x ⇛ Rout_of(x) ≠ w" 
          by(rule impl_link_121)
        from implC and this have
          "z ∈ x ⇛ w ∈ (f im z) ⇛ Rout_of(x) ≠ w" ..
      }
      have "⋀ w. (z ∈ x ⇛ w ∈ (f im z) ⇛ Rout_of(x) ≠ w)" by fact
      from this have "∀(λw. z ∈ x ⇛ w ∈ (f im z) ⇛ Rout_of(x) ≠ w)" ..
      from all_cons and this have
        "z ∈ x ⇛ ∀(λw. w ∈ (f im z) ⇛ Rout_of(x) ≠ w)" ..
    }
    have "⋀ z. (z ∈ x ⇛ ∀(λw. w ∈ (f im z) ⇛ Rout_of(x) ≠ w))" by fact
    from this have
      "∀(λz. z ∈ x ⇛ ∀(λw. w ∈ (f im z) ⇛ Rout_of(x) ≠ w))" ..
      
    from intersection_subset and this have
      "Rout_of(x) ⊆ x ⊗ ∀(λz. z ∈ x ⇛ ∀(λw. w ∈ (f im z) ⇛ Rout_of(x) ≠ w))"
      unfolding Rout_of_def ..
    from impl_eg and this show ?thesis ..
  qed

definition WF :: "i"
  where "WF ≡ {(λx. ∀(λy. y ⊑ x ⊗ ∃(λz. z ∈ y) ⇛ ∃(λz. z ∈ y ⊗ ¬∃(λw. w ∈ z ∩ y))))}"

abbreviation wf :: "i ⇒ o"
  where "wf x ≡ x ∈ WF"

lemma eparts_of_wf_sets_are_wf: "x ⊑ y ⇛ wf y ⇛ wf x"
  proof -
    from abstraction and implI have
      step1:"wf y ⇛ ∀(λu. u ⊑ y ⊗ ∃(λv. v ∈ u) ⇛ ∃(λv. v ∈ u ⊗ ¬∃(λw. w ∈ v ∩ u)))"
      unfolding WF_def
      by(rule bisub_rule)
    {
    fix t
    from step1 and impl_ui have
      "wf y ⇛ t ⊑ y ⊗ ∃(λv. v ∈ t) ⇛ ∃(λv. v ∈ t ⊗ ¬∃(λw. w ∈ v ∩ t))" ..
    from implC and this have
      "t ⊑ y ⊗ ∃(λv. v ∈ t) ⇛ wf y ⇛ ∃(λv. v ∈ t ⊗ ¬∃(λw. w ∈ v ∩ t))" ..
    from conj_export and this have
      "t ⊑ y ⇛ ∃(λv. v ∈ t) ⇛ wf y ⇛ ∃(λv. v ∈ t ⊗ ¬∃(λw. w ∈ v ∩ t))" ..
    from epart_trans and this have
      "t ⊑ x ⊗ x ⊑ y ⇛ ∃(λv. v ∈ t) ⇛ wf y ⇛ ∃(λv. v ∈ t ⊗ ¬∃(λw. w ∈ v ∩ t))" ..
    from conj_bicomm and this have
      "x ⊑ y ⊗ t ⊑ x ⇛ ∃(λv. v ∈ t) ⇛ wf y ⇛ ∃(λv. v ∈ t ⊗ ¬∃(λw. w ∈ v ∩ t))"
      by(rule bisub_rule[where A="t ⊑ x ⊗ x ⊑ y"])
    from conj_export and this have
      "x ⊑ y ⇛ t ⊑ x ⇛ ∃(λv. v ∈ t) ⇛ wf y ⇛ ∃(λv. v ∈ t ⊗ ¬∃(λw. w ∈ v ∩ t))" ..
    from this and conj_import have
      "x ⊑ y ⇛ t ⊑ x ⊗ ∃(λv. v ∈ t) ⇛ wf y ⇛ ∃(λv. v ∈ t ⊗ ¬∃(λw. w ∈ v ∩ t))" ..
    from this and implC have
      "x ⊑ y ⇛ wf y ⇛ t ⊑ x ⊗ ∃(λv. v ∈ t) ⇛ ∃(λv. v ∈ t ⊗ ¬∃(λw. w ∈ v ∩ t))" ..
    }
    have "⋀ t. (x ⊑ y ⇛ wf y ⇛ t ⊑ x ⊗ ∃(λv. v ∈ t) ⇛ ∃(λv. v ∈ t ⊗ ¬∃(λw. w ∈ v ∩ t)))" by fact
    from this have
      "∀(λt. x ⊑ y ⇛ wf y ⇛ t ⊑ x ⊗ ∃(λv. v ∈ t) ⇛ ∃(λv. v ∈ t ⊗ ¬∃(λw. w ∈ v ∩ t)))" ..
    from all_cons and this have
      "x ⊑ y ⇛ ∀(λt. wf y ⇛ t ⊑ x ⊗ ∃(λv. v ∈ t) ⇛ ∃(λv. v ∈ t ⊗ ¬∃(λw. w ∈ v ∩ t)))" ..
    from this and all_cons have
      "x ⊑ y ⇛ wf y ⇛ ∀(λt. t ⊑ x ⊗ ∃(λv. v ∈ t) ⇛ ∃(λv. v ∈ t ⊗ ¬∃(λw. w ∈ v ∩ t)))" ..
    from abstraction[where P="λx. ∀(λt. t ⊑ x ⊗ ∃(λv. v ∈ t) ⇛ ∃(λv. v ∈ t ⊗ ¬∃(λw. w ∈ v ∩ t)))"]
      and this show
      "x ⊑ y ⇛ wf y ⇛ wf x"
      unfolding WF_def
      by(rule bisub_rule')
  qed

lemma seventeen_i_aux: "wf x ⊗ x ∈ x ⇛ x ∉ x ∨ x ≠ x"
  proof -
    from abstraction and implI[where A = "wf x"] have
      "wf x ⇛ ∀(λt. t ⊑ x ⊗ ∃(λv. v ∈ t) ⇛ ∃(λz. z ∈ t ⊗ ¬∃(λw. w ∈ z ∩ t)))"
      unfolding WF_def
      by(rule bisub_rule)
    from this and impl_ui have
      "wf x ⇛ {!x} ⊑ x ⊗ ∃(λv. v ∈ {!x}) ⇛ ∃(λz. z ∈ {!x} ⊗ ¬∃(λw. w ∈ z ∩ {!x}))" ..
    from this and conj_export have
      "wf x ⇛ {!x} ⊑ x ⇛ ∃(λv. v ∈ {!x}) ⇛ ∃(λz. z ∈ {!x} ⊗ ¬∃(λw. w ∈ z ∩ {!x}))" ..
    from this and membership_singleton_epart_ltr have
      "wf x ⇛ x ∈ x ⇛ ∃(λv. v ∈ {!x}) ⇛ ∃(λz. z ∈ {!x} ⊗ ¬∃(λw. w ∈ z ∩ {!x}))"
      by(rule impl_link_212)
    from conj_import and this have
      step1:"wf x ⊗ x ∈ x ⇛ ∃(λv. v ∈ {!x}) ⇛ ∃(λz. z ∈ {!x} ⊗ ¬∃(λw. w ∈ z ∩ {!x}))" ..

    from entl_eg and in_its_singleton have
      "∃(λv. v ∈ {!x})" ..
    from step1 and this have
      step2:"wf x ⊗ x ∈ x ⇛ ∃(λz. z ∈ {!x} ⊗ ¬∃(λw. w ∈ z ∩ {!x}))" ..

    from dm_dnnc_bi and impl_ui have
      "∀(λw. ¬(w ∈ x ⊗ w ∈ {!x})) ⇛ x ∉ x ∨ x ∉ {!x}"
      by(rule bisub_open_rule)
    from dm_anns_bi and this have
      "¬∃(λw. (w ∈ x ⊗ w ∈ {!x})) ⇛ x ∉ x ∨ x ∉ {!x}"
      by(rule bisub_rule)
    from abstraction and this have
      "¬∃(λw. (w ∈ x ⊗ w ∈ {!x})) ⇛ x ∉ x ∨ x ≠ x"
      unfolding singleton_def
      by(rule bisub_rule)
    from intersection_conj and this have
      step3:"¬∃(λw. w ∈ x ∩ {!x}) ⇛ x ∉ x ∨ x ≠ x"
      by(rule bisub_open_rule')
    {
    fix z
    from equals_sub_impl and entl_impl have
      "z = x ⇛ ¬∃(λw. w ∈ z ∩ {!x}) ⇛ ¬∃(λw. w ∈ x ∩ {!x})" ..
    from abstraction and this have
      "z ∈ {!x} ⇛ ¬∃(λw. w ∈ z ∩ {!x}) ⇛ ¬∃(λw. w ∈ x ∩ {!x})"
      unfolding singleton_def
      by(rule bisub_rule')
    from conj_import and this have
      "z ∈ {!x} ⊗ ¬∃(λw. w ∈ z ∩ {!x}) ⇛ ¬∃(λw. w ∈ x ∩ {!x})" ..
    }
    have "⋀ z. (z ∈ {!x} ⊗ ¬∃(λw. w ∈ z ∩ {!x}) ⇛ ¬∃(λw. w ∈ x ∩ {!x}))" by fact
    from this have
      "∀(λz. z ∈ {!x} ⊗ ¬∃(λw. w ∈ z ∩ {!x}) ⇛ ¬∃(λw. w ∈ x ∩ {!x}))" ..
    from all_ante and this have
      "∃(λz. z ∈ {!x} ⊗ ¬∃(λw. w ∈ z ∩ {!x})) ⇛ ¬∃(λw. w ∈ x ∩ {!x})" ..
    from step2 and this have
      "wf x ⊗ x ∈ x ⇛ ¬∃(λw. w ∈ x ∩ {!x})" ..
    from this and step3 show ?thesis ..
  qed

lemma seventeen_i: "wf x ⇛ x ∉ x ∨ x ≠ x"
  proof -
    from impl_disj_left and impl_disj_inl have
      "(x ∈ x ⇛ x ∉ x ∨ x ≠ x) ⇛ x ∉ x ∨ x ∈ x ⇛ x ∉ x ∨ x ≠ x" ..
    from disj_bicomm and this have
      "(x ∈ x ⇛ x ∉ x ∨ x ≠ x) ⇛ x ∈ x ∨ x ∉ x ⇛ x ∉ x ∨ x ≠ x"
      by(rule bisub_rule)
    from this and lem have
      step1:"(x ∈ x ⇛ x ∉ x ∨ x ≠ x) ⇛ x ∉ x ∨ x ≠ x" ..

    from conj_export and seventeen_i_aux have
      "wf x ⇛ x ∈ x ⇛ x ∉ x ∨ x ≠ x" ..
    from this and step1 show ?thesis ..
  qed

  lemma seventeen_ii: "x ∈ x ⊗ x ∈ x ⇛ ¬ (wf x)"
    proof -
      from membership_singleton_epart_ltr and impl_conj_in have
        step1: "x ∈ x ⇛ ∃(λz. z ∈ {!x}) ⇛ {!x} ⊑ x ⊗ ∃(λz. z ∈ {!x})" ..
      from entl_eg and in_its_singleton have "∃(λz. z ∈ {!x})" ..
      from step1 and this have
        step2: "x ∈ x ⇛ {!x} ⊑ x ⊗ ∃(λz. z ∈ {!x})" ..

      {
        fix z
        from impl_conj_in and in_its_singleton have
            "x ∈ x ⇛ x ∈ x ⊗ x ∈ {!x}" ..
        from intersection_conj and this have
            "x ∈ x ⇛ x ∈ x ∩ {!x}"
            by(rule bisub_rule')
        from this have
            "x = z ⇛ x ∈ x ⇛ x ∈ z ∩ {!x}"
            by(rule equals_left_rule)
        from eq_sym_bientl and this have
            "z = x ⇛ x ∈ x ⇛ x ∈ z ∩ {!x}"
            by(rule bisub_rule)
        from in_singleton_equals and this have
            "z ∈ {!x} ⇛ x ∈ x ⇛ x ∈ z ∩ {!x}"
            by(rule impl_after_entl_trans)
        from lem and this have
            "(z ∈ {!x} ∨ z ∉ {!x}) ⊗ (z ∈ {!x} ⇛ x ∈ x ⇛ x ∈ z ∩ {!x})" ..
        from disj_bicomm and this have
            "(z ∉ {!x} ∨ z ∈ {!x}) ⊗ (z ∈ {!x} ⇛ x ∈ x ⇛ x ∈ z ∩ {!x})"
            by(rule bisub_rule)
        from disj_monotone_right and this have
            "z ∉ {!x} ∨ (x ∈ x ⇛ x ∈ z ∩ {!x})" ..
        from disj_in_under_impl and this have
            "x ∈ x ⇛ z ∉ {!x} ∨ x ∈ z ∩ {!x}" ..
        from this and eg_under_disjr have
            "x ∈ x ⇛ z ∉ {!x} ∨ ∃(λu. u ∈ z ∩ {!x})" ..
      }
      have "⋀ z. x ∈ x ⇛ z ∉ {!x} ∨ ∃(λu. u ∈ z ∩ {!x})" by fact
      from this have
        "∀(λz. x ∈ x ⇛ z ∉ {!x} ∨ ∃(λu. u ∈ z ∩ {!x}))" ..
      from all_cons and this have
        "x ∈ x ⇛ ∀(λz. z ∉ {!x} ∨ ∃(λu. u ∈ z ∩ {!x}))" ..
      from dm_ans_bi and this have
        "x ∈ x ⇛ ¬∃(λz. ¬(z ∉ {!x} ∨ ∃(λu. u ∈ z ∩ {!x})))"
        by(rule bisub_rule)
      from dm_cnnd_bi and this have
        "x ∈ x ⇛ ¬∃(λz. ¬¬(z ∈ {!x}) ⊗ ¬∃(λu. u ∈ z ∩ {!x}))"
        by(rule bisub_open_rule')
      from dn_bi' and this have
        "x ∈ x ⇛ ¬∃(λz. z ∈ {!x} ⊗ ¬∃(λu. u ∈ z ∩ {!x}))"
        by(rule bisub_open_rule)

      from step2 and this have
        "x ∈ x ⊗ x ∈ x ⇛ ({!x} ⊑ x ⊗ ∃(λz. z ∈ {!x})) ⊗ ¬∃(λz. z ∈ {!x} ⊗ ¬∃(λu. u ∈ z ∩ {!x}))"
        by(rule factor_rule)
      from this and impl_cex have
        "x ∈ x ⊗ x ∈ x ⇛ ¬({!x} ⊑ x ⊗ ∃(λz. z ∈ {!x}) ⇛ ∃(λz. z ∈ {!x} ⊗ ¬∃(λu. u ∈ z ∩ {!x})))" ..
      from this and impl_eg have
        "x ∈ x ⊗ x ∈ x ⇛ ∃(λy. ¬(y ⊑ x ⊗ ∃(λz. z ∈ y) ⇛ ∃(λz. z ∈ y ⊗ ¬∃(λu. u ∈ z ∩ y))))" ..
      from dm_snna_bi and this have
        "x ∈ x ⊗ x ∈ x ⇛ ¬∀(λy. (y ⊑ x ⊗ ∃(λz. z ∈ y) ⇛ ∃(λz. z ∈ y ⊗ ¬∃(λu. u ∈ z ∩ y))))"
        by(rule bisub_rule)
      from abstraction and this show ?thesis
        unfolding WF_def
        by(rule bisub_rule')
    qed

lemma mirimanoff_negative_half: "WF ∉ WF"
  proof -
    from reductio_contraction and seventeen_ii have
      "WF ∈ WF ⇛ WF ∉ WF" ..
    from reductio and this show ?thesis ..
  qed

abbreviation strict :: "i ⇒ o"
  where "strict x ≡ ∀(λy. y ∈ x ⇛ y ∉ y) ⊗ ∀(λy. ∀(λz. y ∈ x ⊗ z ∈ x ⇛ y ∈ z ⇛ z ∉ y))"

abbreviation transitive :: "i ⇒ o"
  where "transitive x ≡ ∀(λy. y ∈ x → y ⊆ x) ⊗ ∀(λy. ∀(λz. y ∈ x ⊗ z ∈ x ⇛ (y ∈ z → y ⊆ z)))"

definition On :: "i"
  where "On ≡ {{(λx o. x ⊆ o ⊗ strict x ⊗ transitive x ⊗ wf x ⊗ ∀(λy. y ∈ o ⇛ x ≠ y ⇛ x ⊆ y ∨ y ⊆ x))}}"

lemma ordinals_are_strict: "x ∈ On → strict x"
  proof -
    from strong_abstraction have
      "x ∈ On → x ⊆ On ⊗ strict x ⊗ transitive x ⊗ wf x ⊗ ∀(λy. y ∈ On ⇛ x ≠ y ⇛ x ⊆ y ∨ y ⊆ x)"
      unfolding On_def
      unfolding bientl_def ..
    from this and entl_get_conjunct_2_of_3 show ?thesis ..
  qed

lemma ordinals_are_transitive: "x ∈ On → transitive x"
  proof -
    from strong_abstraction have
      "x ∈ On → x ⊆ On ⊗ strict x ⊗ transitive x ⊗ wf x ⊗ ∀(λy. y ∈ On ⇛ x ≠ y ⇛ x ⊆ y ∨ y ⊆ x)"
      unfolding On_def
      unfolding bientl_def ..
    from this and entl_get_conjunct_3_of_4 show ?thesis ..
  qed

lemma ordinals_are_strict_and_transitive: "x ∈ On → strict x ⊗ transitive x"
  proof -
    from strong_abstraction have
      "x ∈ On → x ⊆ On ⊗ strict x ⊗ transitive x ⊗ wf x ⊗ ∀(λy. y ∈ On ⇛ x ≠ y ⇛ x ⊆ y ∨ y ⊆ x)"
      unfolding On_def
      unfolding bientl_def ..
    from this and entl_cer have
      "x ∈ On → strict x ⊗ transitive x ⊗ wf x ⊗ ∀(λy. y ∈ On ⇛ x ≠ y ⇛ x ⊆ y ∨ y ⊆ x)" ..
    from conj_biass and this have
      "x ∈ On → (strict x ⊗ transitive x) ⊗ wf x ⊗ ∀(λy. y ∈ On ⇛ x ≠ y ⇛ x ⊆ y ∨ y ⊆ x)"
      by(rule bisub_rule)
    from this and entl_cel show ?thesis ..
  qed

lemma ordinals_are_transitive_and_wf: "x ∈ On → transitive x ⊗ wf x"
  proof -
    from strong_abstraction have
      "x ∈ On → x ⊆ On ⊗ strict x ⊗ transitive x ⊗ wf x ⊗ ∀(λy. y ∈ On ⇛ x ≠ y ⇛ x ⊆ y ∨ y ⊆ x)"
      unfolding On_def
      unfolding bientl_def ..
    from this and entl_cer have
      "x ∈ On → strict x ⊗ transitive x ⊗ wf x ⊗ ∀(λy. y ∈ On ⇛ x ≠ y ⇛ x ⊆ y ∨ y ⊆ x)" ..
    from this and entl_cer have
      "x ∈ On → transitive x ⊗ wf x ⊗ ∀(λy. y ∈ On ⇛ x ≠ y ⇛ x ⊆ y ∨ y ⊆ x)" ..
    from conj_biass and this have
      "x ∈ On → (transitive x ⊗ wf x) ⊗ ∀(λy. y ∈ On ⇛ x ≠ y ⇛ x ⊆ y ∨ y ⊆ x)"
      by(rule bisub_rule)
    from this and entl_cel show ?thesis ..
  qed

lemma ordinals_are_wf: "x ∈ On → wf x"
  proof -
    from strong_abstraction have
      "x ∈ On → x ⊆ On ⊗ strict x ⊗ transitive x ⊗ wf x ⊗ ∀(λy. y ∈ On ⇛ x ≠ y ⇛ x ⊆ y ∨ y ⊆ x)"
      unfolding On_def
      unfolding bientl_def ..
    then show ?thesis
      using entl_get_conjunct_4_of_5 ..
  qed

lemma strict_not_self_member: "strict x ⇛ x ∉ x"
  proof -
    from conj_biass and reductio_contraction_3 have
      "((x ∈ x ⊗ x ∈ x) ⊗ x ∈ x ⇛ x ∉ x) ⇛ x ∈ x ⇛ x ∉ x"
      by(rule bisub_rule)
    from this and reductio have
      "((x ∈ x ⊗ x ∈ x) ⊗ x ∈ x ⇛ x ∉ x) ⇛ x ∉ x" ..
    from conj_import and this have
      "(x ∈ x ⊗ x ∈ x ⇛ x ∈ x ⇛ x ∉ x) ⇛ x ∉ x" ..
    from impl_ui and this have
      "∀(λz. x ∈ x ⊗ z ∈ x ⇛ x ∈ z ⇛ z ∉ x) ⇛ x ∉ x" ..
    from impl_ui and this have
      "∀(λy. ∀(λz. y ∈ x ⊗ z ∈ x ⇛ y ∈ z ⇛ z ∉ y)) ⇛ x ∉ x" ..
    from impl_cer and this show ?thesis ..
  qed

lemma On_is_strict_i: "x ∈ On ⇛ x ∉ x"
  proof -
    from ordinals_are_strict and strict_not_self_member show ?thesis
      by(rule impl_after_entl_trans)
  qed

lemma On_is_strict_ii: "y ∈ On ⊗ z ∈ On ⇛ y ∈ z ⇛ z ∉ y"
  proof -
    from impl_cel and impl_ui have
      "transitive y ⇛ z ∈ y → z ⊆ y" ..
    from this and entl_impl have
      zsuby:"transitive y ⇛ z ∈ y ⇛ z ⊆ y" ..
    from impl_cel and impl_ui have
      "transitive z ⇛ y ∈ z → y ⊆ z" ..
    from this and entl_impl have
      ysubz:"transitive z ⇛ y ∈ z ⇛ y ⊆ z" ..
    from zsuby and ysubz have
      "transitive y ⊗ transitive z ⇛ (z ∈ y ⇛ z ⊆ y) ⊗ (y ∈ z ⇛ y ⊆ z)"
      by(rule factor_rule)
    from this and factor have
      "transitive y ⊗ transitive z ⇛ z ∈ y ⊗ y ∈ z ⇛ z ⊆ y ⊗ y ⊆ z" ..
    from subset_antisym and this have
      "transitive y ⊗ transitive z ⇛ z ∈ y ⊗ y ∈ z ⇛ z = y"
      by(rule impl_link_121)
    from conj_import and this have
      step1:"(transitive y ⊗ transitive z) ⊗ z ∈ y ⊗ y ∈ z ⇛ z = y" ..

    from strict_not_self_member and impl_equals_left have
      "strict y ⇛ y = z ⇛ z ∉ y" ..
    from eq_sym_bientl and this have
      "strict y ⇛ z = y ⇛ z ∉ y"
      by(rule bisub_rule)
    from this and step1 have
      "strict y ⊗ (transitive y ⊗ transitive z) ⊗ z ∈ y ⊗ y ∈ z ⇛ (z = y ⇛ z ∉ y) ⊗ z = y"
      by(rule factor_rule)
    from this and impl_ppmp have
      "strict y ⊗ (transitive y ⊗ transitive z) ⊗ z ∈ y ⊗ y ∈ z ⇛ z ∉ y" ..

    from rearrange_aLbcRde_LaebcRd and this have
      "(strict y ⊗ y ∈ z ⊗ transitive y ⊗ transitive z) ⊗ z ∈ y ⇛ z ∉ y"
      by(rule bisub_rule)

    from conj_export and this have
      "strict y ⊗ y ∈ z ⊗ transitive y ⊗ transitive z ⇛ z ∈ y ⇛ z ∉ y" ..
    from this and reductio have
      "strict y ⊗ y ∈ z ⊗ transitive y ⊗ transitive z ⇛ z ∉ y" ..

    from rearrange_abcd_LLacRdRb and this have
      "((strict y ⊗ transitive y) ⊗ transitive z) ⊗ y ∈ z ⇛ z ∉ y"
      by(rule bisub_rule)
    from conj_export and this have
      "(strict y ⊗ transitive y) ⊗ transitive z ⇛ y ∈ z ⇛ z ∉ y" ..
    from conj_export and this have
      "strict y ⊗ transitive y ⇛ transitive z ⇛ y ∈ z ⇛ z ∉ y" ..
      
    from ordinals_are_strict_and_transitive and this have
      almost:"y ∈ On ⇛ transitive z ⇛ y ∈ z ⇛ z ∉ y"
      by(rule impl_after_entl_trans)
    from entl_impl and ordinals_are_transitive have
      "z ∈ On ⇛ transitive z" ..
    from almost and this have
      "y ∈ On ⇛ z ∈ On ⇛ y ∈ z ⇛ z ∉ y"
      by(rule impl_link_212)
    from conj_import and this show ?thesis ..
  qed

lemma On_is_strict: "strict On"
  proof -
    {
      fix y
      have "y ∈ On ⇛ y ∉ y"
        by(rule On_is_strict_i)
    }
    have "⋀y. y ∈ On ⇛ y ∉ y" by fact
    from this have
      part1:"∀(λy. y ∈ On ⇛ y ∉ y)" ..

    {
      fix y
        {
          fix z
          have "y ∈ On ⊗ z ∈ On ⇛ y ∈ z ⇛ z ∉ y"
            by(rule On_is_strict_ii)
        }
        have "⋀z. y ∈ On ⊗ z ∈ On ⇛ y ∈ z ⇛ z ∉ y" by fact
        from this have
          "∀(λz. y ∈ On ⊗ z ∈ On ⇛ y ∈ z ⇛ z ∉ y)" ..
    }
    have "⋀y. ∀(λz. y ∈ On ⊗ z ∈ On ⇛ y ∈ z ⇛ z ∉ y)" by fact
    from this have
      "∀(λy. ∀(λz. y ∈ On ⊗ z ∈ On ⇛ y ∈ z ⇛ z ∉ y))" ..

    from part1 and this show ?thesis ..
  qed

lemma On_not_in_On: "On ∉ On"
  proof -
    from strict_not_self_member and On_is_strict show ?thesis ..
  qed

lemma ordinals_are_subsets_of_On: "x ∈ On → x ⊆ On"
  proof -
    from strong_abstraction have
      "x ∈ On → x ⊆ On ⊗ strict x ⊗ transitive x ⊗ wf x ⊗ ∀(λy. y ∈ On ⇛ x ≠ y ⇛ x ⊆ y ∨ y ⊆ x)"
      unfolding On_def
      unfolding bientl_def ..
    from this and entl_cel show ?thesis ..
  qed

lemma On_is_transitive: "transitive On"
  proof -
    {
      fix y
      have "y ∈ On → y ⊆ On" by(rule ordinals_are_subsets_of_On)
    }
    have "⋀y. y ∈ On → y ⊆ On" by fact
    from this have
      part1:"∀(λy. y ∈ On → y ⊆ On)" ..

    {
      fix y
      {
        fix z
        from ordinals_are_transitive and entl_cel have
          "z ∈ On → ∀(λy. y ∈ z → y ⊆ z)" ..
        from this and entl_ui have
          "z ∈ On → y ∈ z → y ⊆ z" ..
        from entl_impl and this have
          "z ∈ On ⇛ (y ∈ z → y ⊆ z)" ..
        from impl_cer and this have
          "y ∈ On ⊗ z ∈ On ⇛ (y ∈ z → y ⊆ z)" ..
      }
      have "⋀z. (y ∈ On ⊗ z ∈ On ⇛ (y ∈ z → y ⊆ z))" by fact
      from this have
        "∀(λz. (y ∈ On ⊗ z ∈ On ⇛ (y ∈ z → y ⊆ z)))" ..
    }
    have "⋀y. ∀(λz. (y ∈ On ⊗ z ∈ On ⇛ (y ∈ z → y ⊆ z)))" by fact
    from this have
      "∀(λy. ∀(λz. (y ∈ On ⊗ z ∈ On ⇛ (y ∈ z → y ⊆ z))))" ..
    from part1 and this show ?thesis ..
  qed

lemma On_is_linear: "∀(λy. y ∈ On ⇛ On ≠ y ⇛ On ⊆ y ∨ y ⊆ On)"
  proof -
    {
      fix y
      from entl_impl and ordinals_are_subsets_of_On have
        "y ∈ On ⇛ y ⊆ On" ..
      from this and impl_disj_inr have
        "y ∈ On ⇛ On ⊆ y ∨ y ⊆ On" ..
      from this and implK have
        "y ∈ On ⇛ On ≠ y ⇛ On ⊆ y ∨ y ⊆ On" ..
    }
    have "⋀y. y ∈ On ⇛ On ≠ y ⇛ On ⊆ y ∨ y ⊆ On" by fact
    from this show ?thesis ..
  qed

lemma members_of_eparts_of_On_are_wf: "y ⊑ On ⊗ x ∈ y ⇛ wf x"
  proof -
    from conj_import and impl_ui have
      "y ⊑ On ⊗ x ∈ y ⇛ x ∈ On"
      unfolding epart_def ..
    from this and ordinals_are_wf show ?thesis
      by(rule entl_after_impl_trans)
  qed

lemma On_is_wf_aux: "transitive b ⇛ d ∈ b ⇛ ¬(v ∈ d ∩ (b ∩ y)) ⇛ ¬(v ∈ d ⊗ v ∈ y)"
  proof -
    have d_horn:"v ∉ d ⇛ v ∉ d ∨ v ∉ y" by(rule impl_disj_inl)
    have y_horn:"v ∉ y ⇛ v ∉ d ∨ v ∉ y" by(rule impl_disj_inr)

    from entl_impl and subset_contra_entl have
      "d ⊆ b ⇛ v ∉ b → v ∉ d" ..
    from this and entl_impl have
      "d ⊆ b ⇛ v ∉ b ⇛ v ∉ d" ..
    from this and d_horn have
      "d ⊆ b ⇛ v ∉ b ⇛ v ∉ d ∨ v ∉ y"
      by(rule impl_link_121[rotated])
    from implC and this have
      step1:"v ∉ b ⇛ d ⊆ b ⇛ v ∉ d ∨ v ∉ y" ..

    from implK and y_horn have
      "d ⊆ b ⇛ v ∉ y ⇛ v ∉ d ∨ v ∉ y" ..
    from implC and this have
      "v ∉ y ⇛ d ⊆ b ⇛ v ∉ d ∨ v ∉ y" ..
    from step1 and this have
      "v ∉ b ∨ v ∉ y ⇛ d ⊆ b ⇛ v ∉ d ∨ v ∉ y"
      by(rule disj_left_rule)
    from dm_dnnc_bi and this have
      "¬(v ∈ b ⊗ v ∈ y) ⇛ d ⊆ b ⇛ v ∉ d ∨ v ∉ y"
      by(rule bisub_rule)
    from intersection_conj and this have
      step2:"v ∉ b ∩ y ⇛ d ⊆ b ⇛ v ∉ d ∨ v ∉ y"
      by(rule bisub_rule')

    from implK and d_horn have
      "d ⊆ b ⇛ v ∉ d ⇛ v ∉ d ∨ v ∉ y" ..
    from implC and this have
      "v ∉ d ⇛ d ⊆ b ⇛ v ∉ d ∨ v ∉ y" ..
    from this and step2 have
      "v ∉ d ∨ v ∉ b ∩ y ⇛ d ⊆ b ⇛ v ∉ d ∨ v ∉ y"
      by(rule disj_left_rule)
    from dm_dnnc_bi and this have
      "¬(v ∈ d ⊗ v ∈ b ∩ y) ⇛ d ⊆ b ⇛ v ∉ d ∨ v ∉ y"
      by(rule bisub_rule)
    from intersection_conj and this have
      "v ∉ d ∩ (b ∩ y) ⇛ d ⊆ b ⇛ v ∉ d ∨ v ∉ y"
      by(rule bisub_rule')
    from implC and this have
      "d ⊆ b ⇛ v ∉ d ∩ (b ∩ y) ⇛ v ∉ d ∨ v ∉ y" ..
    from dm_dnnc_bi and this have
      step2:"d ⊆ b ⇛ v ∉ d ∩ (b ∩ y) ⇛ ¬(v ∈ d ⊗ v ∈ y)"
      by(rule bisub_rule)

    from impl_cel and impl_ui have
      "transitive b ⇛ (d ∈ b → d ⊆ b)" ..
    from this and entl_impl have
      "transitive b ⇛ d ∈ b ⇛ d ⊆ b" ..
    from this and step2 show ?thesis
      by(rule impl_link_121[rotated])
  qed

lemma On_is_wf: "wf On"
  proof -
     {
       fix y
       {
         fix b
         from conj_bicomm and impl_conj_in have
           "¬∃(λu. u ∈ b ∩ y) ⇛ b ∈ y ⇛ b ∈ y ⊗ ¬∃(λu. u ∈ b ∩ y)"
           by(rule bisub_rule)
         from this and impl_cer have
           "¬∃(λu. u ∈ b ∩ y) ⇛ y ⊑ On ⊗ b ∈ y ⇛ b ∈ y ⊗ ¬∃(λu. u ∈ b ∩ y)"
           by(rule impl_link_212)
         from this and impl_eg have
           b_is_least:"¬∃(λd. d ∈ b ∩ y) ⇛ y ⊑ On ⊗ b ∈ y ⇛ ∃(λg. g ∈ y ⊗ ¬∃(λu. u ∈ g ∩ y))"
           by(rule impl_link_121[rotated])

         from subset_epart and intersection_subset have
           "b ∩ y ⊑ b" ..
         from eparts_of_wf_sets_are_wf and this have
           "wf b ⇛ wf (b ∩ y)" ..
         from abstraction and this have
           "wf b ⇛ ∀(λc. c ⊑ b ∩ y ⊗ ∃(λd. d ∈ c) ⇛ ∃(λd. d ∈ c ⊗ ¬∃(λv. v ∈ d ∩ c)))"
           unfolding WF_def
           by(rule bisub_rule)
         from this and impl_ui have
           "wf b ⇛ b ∩ y ⊑ b ∩ y ⊗ ∃(λd. d ∈ b ∩ y) ⇛ ∃(λd. d ∈ b ∩ y ⊗ ¬∃(λv. v ∈ d ∩ (b ∩ y)))" ..
         from this and conj_export have
           "wf b ⇛ b ∩ y ⊑ b ∩ y ⇛ ∃(λd. d ∈ b ∩ y) ⇛ ∃(λd. d ∈ b ∩ y ⊗ ¬∃(λv. v ∈ d ∩ (b ∩ y)))" ..
         from this and epart_refl have
           "wf b ⇛ ∃(λd. d ∈ b ∩ y) ⇛ ∃(λd. d ∈ b ∩ y ⊗ ¬∃(λv. v ∈ d ∩ (b ∩ y)))" ..
         from dm_sna_bi and this have
           "wf b ⇛ ∃(λd. d ∈ b ∩ y) ⇛ ∃(λd. d ∈ b ∩ y ⊗ ¬¬∀(λv. v ∉ d ∩ (b ∩ y)))"
           by(rule bisub_open_rule)
         from dn_bi' and this have
           step1:"wf b ⇛ ∃(λd. d ∈ b ∩ y) ⇛ ∃(λd. d ∈ b ∩ y ⊗ ∀(λv. ¬(v ∈ d ∩ (b ∩ y))))"
           by(rule bisub_open_rule)
         {
           fix d
           {
             fix v
             from intersection_conj and implI have
               "d ∈ b ∩ y ⊗ v ∉ d ∩ (b ∩ y) ⇛ (d ∈ b ⊗ d ∈ y) ⊗ v ∉ d ∩ (b ∩ y)"
               by(rule bisub_rule)
             from conj_bicomm and this have
               "d ∈ b ∩ y ⊗ v ∉ d ∩ (b ∩ y) ⇛ (d ∈ y ⊗ d ∈ b) ⊗ v ∉ d ∩ (b ∩ y)"
               by(rule bisub_rule)
             from conj_biass and this have
               step3:"d ∈ b ∩ y ⊗ v ∉ d ∩ (b ∩ y) ⇛ d ∈ y ⊗ (d ∈ b ⊗ v ∉ d ∩ (b ∩ y))"
               by(rule bisub_rule')

             from On_is_wf_aux and conj_import have
               "transitive b ⇛ d ∈ b ⊗ v ∉ d ∩ (b ∩ y) ⇛ ¬(v ∈ d ⊗ v ∈ y)" ..
             from this and add_conjunct_on_left have
               "transitive b ⇛ d ∈ y ⊗ (d ∈ b ⊗ v ∉ d ∩ (b ∩ y)) ⇛ d ∈ y ⊗ ¬(v ∈ d ⊗ v ∈ y)" ..
             from step3 and this have
               "transitive b ⇛ d ∈ b ∩ y ⊗ v ∉ d ∩ (b ∩ y) ⇛ d ∈ y ⊗ ¬(v ∈ d ⊗ v ∈ y)"
               by(rule impl_link_212[rotated])
             from intersection_conj and this have
               "transitive b ⇛ d ∈ b ∩ y ⊗ v ∉ d ∩ (b ∩ y) ⇛ d ∈ y ⊗ ¬(v ∈ d ∩ y)"
               by(rule bisub_rule')
            }
            have "\<And> v. transitive b ⇛ d ∈ b ∩ y ⊗ v ∉ d ∩ (b ∩ y) ⇛ d ∈ y ⊗ ¬(v ∈ d ∩ y)" by fact
            from this have
              "∀(λv. transitive b ⇛ d ∈ b ∩ y ⊗ v ∉ d ∩ (b ∩ y) ⇛ d ∈ y ⊗ ¬(v ∈ d ∩ y))" ..
            from all_cons and this have
              "transitive b ⇛ ∀(λv. d ∈ b ∩ y ⊗ v ∉ d ∩ (b ∩ y) ⇛ d ∈ y ⊗ ¬(v ∈ d ∩ y))" ..
            from this and all_impl_dist have
              step4:"transitive b ⇛ ∀(λv. d ∈ b ∩ y ⊗ v ∉ d ∩ (b ∩ y)) ⇛ ∀(λv. d ∈ y ⊗ ¬(v ∈ d ∩ y))" ..

           {
             fix w
             have "d ∈ b ∩ y ⇛ d ∈ b ∩ y" by(rule implI)
           }
           have "\<And> w. d ∈ b ∩ y ⇛ d ∈ b ∩ y" by fact
           from this have
             "∀(λw. d ∈ b ∩ y ⇛ d ∈ b ∩ y)" ..
           from all_cons and this have
             "d ∈ b ∩ y ⇛ ∀(λw. d ∈ b ∩ y)" ..
           from this have
             "d ∈ b ∩ y ⊗ ∀(λv. v ∉ d ∩ (b ∩ y)) ⇛ ∀(λw. d ∈ b ∩ y) ⊗ ∀(λv. v ∉ d ∩ (b ∩ y))"
             by(rule conj_monotone_left_rule)
           from this and all_over_conj have
             "d ∈ b ∩ y ⊗ ∀(λv. v ∉ d ∩ (b ∩ y)) ⇛ ∀(λv. d ∈ b ∩ y ⊗ v ∉ d ∩ (b ∩ y))" ..

           from step4 and this have
             "transitive b ⇛ d ∈ b ∩ y ⊗ ∀(λv. v ∉ d ∩ (b ∩ y)) ⇛ ∀(λv. d ∈ y ⊗ ¬(v ∈ d ∩ y))"
             by(rule impl_link_212)
           from this and all_conj_dist have
             step2:"transitive b ⇛ d ∈ b ∩ y ⊗ ∀(λv. v ∉ d ∩ (b ∩ y)) ⇛ ∀(λv. d ∈ y) ⊗ ∀(λv. ¬(v ∈ d ∩ y))"
             by(rule impl_link_121[rotated])

           from impl_ui have
             "∀(λw. d ∈ y) ⊗ ∀(λv. ¬(v ∈ d ∩ y)) ⇛ d ∈ y ⊗ ∀(λv. ¬(v ∈ d ∩ y))"
             by(rule conj_monotone_left_rule)
           from step2 and this have
             "transitive b ⇛ d ∈ b ∩ y ⊗ ∀(λv. v ∉ d ∩ (b ∩ y)) ⇛ d ∈ y ⊗ ∀(λv. ¬(v ∈ d ∩ y))"
             by(rule impl_link_121[rotated])
           from this and impl_eg have
             "transitive b ⇛ d ∈ b ∩ y ⊗ ∀(λv. v ∉ d ∩ (b ∩ y)) ⇛ ∃(λd. d ∈ y ⊗ ∀(λv. ¬(v ∈ d ∩ y)))"
             by(rule impl_link_121[rotated])
         }
         have "\<And> d. transitive b ⇛ d ∈ b ∩ y ⊗ ∀(λv. v ∉ d ∩ (b ∩ y)) ⇛ ∃(λd. d ∈ y ⊗ ∀(λv. ¬(v ∈ d ∩ y)))" by fact
         from this have
           "∀(λd. transitive b ⇛ d ∈ b ∩ y ⊗ ∀(λv. v ∉ d ∩ (b ∩ y)) ⇛ ∃(λd. d ∈ y ⊗ ∀(λv. ¬(v ∈ d ∩ y))))" ..
         from all_cons and this have
           "transitive b ⇛ ∀(λd. d ∈ b ∩ y ⊗ ∀(λv. v ∉ d ∩ (b ∩ y)) ⇛ ∃(λd. d ∈ y ⊗ ∀(λv. ¬(v ∈ d ∩ y))))" ..
         from this and all_ante have
           "transitive b ⇛ ∃(λd. d ∈ b ∩ y ⊗ ∀(λv. v ∉ d ∩ (b ∩ y))) ⇛ ∃(λd. d ∈ y ⊗ ∀(λv. ¬(v ∈ d ∩ y)))" ..

         from step1 and this have
           "transitive b ⇛ wf b ⇛ ∃(λd. d ∈ b ∩ y) ⇛ ∃(λd. d ∈ y ⊗ ∀(λv. v ∉ d ∩ y))"
           by(rule impl_link_222[rotated])
         from conj_import and this have
           "transitive b ⊗ wf b ⇛ ∃(λd. d ∈ b ∩ y) ⇛ ∃(λd. d ∈ y ⊗ ∀(λv. v ∉ d ∩ y))" ..
         from ordinals_are_transitive_and_wf and this have
           step5:"b ∈ On ⇛ ∃(λd. d ∈ b ∩ y) ⇛ ∃(λd. d ∈ y ⊗ ∀(λv. v ∉ d ∩ y))"
           by(rule impl_after_entl_trans)

         from implI and impl_ui have
           "y ⊑ On ⇛ b ∈ y ⇛ b ∈ On"
           unfolding epart_def ..
         from conj_import and this have
           "y ⊑ On ⊗ b ∈ y ⇛ b ∈ On" ..
         from this and step5 have
           "y ⊑ On ⊗ b ∈ y ⇛ ∃(λd. d ∈ b ∩ y) ⇛ ∃(λd. d ∈ y ⊗ ∀(λv. v ∉ d ∩ y))" ..
         from implC and this have
           "∃(λd. d ∈ b ∩ y) ⇛ y ⊑ On ⊗ b ∈ y ⇛ ∃(λd. d ∈ y ⊗ ∀(λv. v ∉ d ∩ y))" ..
         from dm_anns_bi and this have
           b_isnt_least:"∃(λd. d ∈ b ∩ y) ⇛ y ⊑ On ⊗ b ∈ y ⇛ ∃(λd. d ∈ y ⊗ ¬∃(λv. v ∈ d ∩ y))"
           by(rule bisub_open_rule)

         from b_isnt_least and b_is_least have
           "∃(λd. d ∈ b ∩ y) ∨ ¬∃(λd. d ∈ b ∩ y) ⇛ y ⊑ On ⊗ b ∈ y ⇛ ∃(λd. d ∈ y ⊗ ¬∃(λv. v ∈ d ∩ y))"
           by(rule disj_left_rule)
         from this and lem have
           "y ⊑ On ⊗ b ∈ y ⇛ ∃(λd. d ∈ y ⊗ ¬∃(λv. v ∈ d ∩ y))" ..
       }
       have "\<And> b. y ⊑ On ⊗ b ∈ y ⇛ ∃(λd. d ∈ y ⊗ ¬∃(λv. v ∈ d ∩ y))" by fact
       from this have
         "∀(λb. y ⊑ On ⊗ b ∈ y ⇛ ∃(λd. d ∈ y ⊗ ¬∃(λv. v ∈ d ∩ y)))" ..
       from all_ante and this have
         "∃(λb. y ⊑ On ⊗ b ∈ y) ⇛ ∃(λd. d ∈ y ⊗ ¬∃(λv. v ∈ d ∩ y))" ..
       from some_over_and and this have
         "y ⊑ On ⊗ ∃(λb. b ∈ y) ⇛ ∃(λd. d ∈ y ⊗ ¬∃(λv. v ∈ d ∩ y))" ..
     }
     have "\<And> y. y ⊑ On ⊗ ∃(λb. b ∈ y) ⇛ ∃(λd. d ∈ y ⊗ ¬∃(λv. v ∈ d ∩ y))" by fact
     from this have
         "∀(λy. y ⊑ On ⊗ ∃(λb. b ∈ y) ⇛ ∃(λd. d ∈ y ⊗ ¬∃(λv. v ∈ d ∩ y)))" ..
     from abstraction and this show ?thesis
       unfolding WF_def
       by(rule bisub_rule')
  qed

lemma On_in_On: "On ∈ On"
  proof -
    from On_is_wf and On_is_linear have
      "wf On ⊗ ∀(λy. y ∈ On ⇛ On ≠ y ⇛ On ⊆ y ∨ y ⊆ On)" ..
    from On_is_transitive and this have
      "transitive On ⊗ wf On ⊗ ∀(λy. y ∈ On ⇛ On ≠ y ⇛ On ⊆ y ∨ y ⊆ On)" ..
    from On_is_strict and this have
      "strict On ⊗ transitive On ⊗ wf On ⊗ ∀(λy. y ∈ On ⇛ On ≠ y ⇛ On ⊆ y ∨ y ⊆ On)" ..
    from subset_refl and this have
      "On ⊆ On ⊗ strict On ⊗ transitive On ⊗ wf On ⊗ ∀(λy. y ∈ On ⇛ On ≠ y ⇛ On ⊆ y ∨ y ⊆ On)" ..
    from strong_abstraction[where P="(λx o. x ⊆ o ⊗ strict x ⊗ transitive x ⊗ wf x ⊗ ∀(λy. y ∈ o ⇛ x ≠ y ⇛ x ⊆ y ∨ y ⊆ x))"]
      and this show ?thesis
      unfolding On_def
      by(rule bisub_rule')
  qed

lemma burali_forti_contradiction: "On ∈ On ⊗ On ∉ On"
  proof -
    from On_in_On and On_not_in_On show ?thesis ..
  qed

lemma On_not_self_identical: "On ≠ On"
  proof -
    from impl_eg and burali_forti_contradiction have
      "∃(λx. x ∈ On ⊗ x ∉ On)" ..
    from counterexample_nonidentity and this show ?thesis ..
  qed

end
