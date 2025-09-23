(* Title: subDMQ-posneg.thy
   Author: Ellie Ripley, https://negation.rocks
*)


section \<open>Positive and negative formula contexts in subDMQ\<close>

theory "subDMQ-posneg"
  imports subDMQ
begin

  abbreviation entl_positive_context :: "(o ⇒ o) ⇒ prop" ("epos _" 5)
    where "epos C \<equiv> (\<And> A B . (A → B ⟹ C A → C B))"

  abbreviation impl_impl_positive_context :: "(o ⇒ o) ⇒ prop" ("iipos _" 5)
    where "iipos C \<equiv> (\<And> A B . (A ⇛ B ⟹ C A ⇛ C B))"

  abbreviation entl_impl_positive_context :: "(o ⇒ o) ⇒ prop" ("eipos _" 5)
    where "eipos C \<equiv> (\<And> A B . (A → B ⟹ C A ⇛ C B))"

  abbreviation positive_context :: "(o ⇒ o) ⇒ prop" ("pos _" 5)
    where "pos C \<equiv> (\<And> A B . (A → B ⟹ C A ⟹ C B))"

  abbreviation entl_negative_context :: "(o ⇒ o) ⇒ prop" ("eneg _" 5)
    where "eneg C \<equiv> (\<And> A B . (A → B ⟹ C B → C A))"

  abbreviation impl_impl_negative_context :: "(o ⇒ o) ⇒ prop" ("iineg _" 5)
    where "iineg C \<equiv> (\<And> A B . (A ⇛ B ⟹ C B ⇛ C A))"

  abbreviation entl_impl_negative_context :: "(o ⇒ o) ⇒ prop" ("eineg _" 5)
    where "eineg C \<equiv> (\<And> A B . (A → B ⟹ C B ⇛ C A))"

  abbreviation negative_context :: "(o ⇒ o) ⇒ prop" ("neg _" 5)
    where "neg C \<equiv> (\<And> A B . (A → B ⟹ C B ⟹ C A))"

lemma epos_eipos: "epos C ⟹ eipos C"
proof -
 assume ec:"epos C"
 { fix A B
   { assume ab:"A → B"
     from ab have "C A → C B" by(rule ec)
     from entl_impl and this have "C A ⇛ C B" ..
   } have "A → B ⟹ C A ⇛ C B" by fact
 } show "eipos C" by fact
qed

lemma eneg_eineg: "eneg C ⟹ eineg C"
proof -
 assume ec:"eneg C"
 { fix A B
   { assume ab:"A → B"
     from ab have "C B → C A" by(rule ec)
     from entl_impl and this have "C B ⇛ C A" ..
   } have "A → B ⟹ C B ⇛ C A" by fact
 } show "eineg C" by fact
qed

lemma iipos_eipos: "iipos C ⟹ eipos C"
proof -
 assume ec:"iipos C"
 { fix A B
   { assume ab:"A → B"
     from entl_impl and ab have "A ⇛ B" ..
     then have "C A ⇛ C B" by(rule ec)
   } have "A → B ⟹ C A ⇛ C B" by fact
 } show "eipos C" by fact
qed

lemma iineg_eineg: "iineg C ⟹ eineg C"
proof -
 assume ec:"iineg C"
 { fix A B
   { assume ab:"A → B"
     from entl_impl and ab have "A ⇛ B" ..
     then have "C B ⇛ C A" by(rule ec)
   } have "A → B ⟹ C B ⇛ C A" by fact
 } show "eineg C" by fact
qed

lemma eipos_pos: "eipos C ⟹ pos C"
proof -
  assume ic:"eipos C"
  { fix A B
    { assume ab:"A → B"
      from ab have "C A ⇛ C B" by(rule ic)
      from this have "C A ⟹ C B" ..
    } have "A → B ⟹ C A ⟹ C B" by fact
  } show "pos C" by fact
qed

lemma eineg_neg: "eineg C ⟹ neg C"
proof -
  assume ic:"eineg C"
  { fix A B
    { assume ab:"A → B"
      from ab have "C B ⇛ C A" by(rule ic)
      from this have "C B ⟹ C A" ..
    } have "A → B ⟹ C B ⟹ C A" by fact
  } show "neg C" by fact
qed

lemma epos_pos: "epos C ⟹ pos C"
proof -
  assume ec:"epos C"
  from ec have "eipos C" by (rule epos_eipos)
  then show "pos C" by (rule eipos_pos)
qed

lemma eneg_neg: "eneg C ⟹ neg C"
proof -
  assume ec:"eneg C"
  from ec have "eineg C" by (rule eneg_eineg)
  then show "neg C" by (rule eineg_neg)
qed

lemma negation_eneg: "eneg (λ p. ¬ p)"
proof -
  { fix A B
    { assume ab:"A → B"
      from entl_contra and ab have "¬ B → ¬ A" ..
    } have "A → B ⟹ ¬ B → ¬ A" by fact
  } show "eneg (λ p. ¬ p)" by fact
qed

lemma conjunction_left_iipos: "iipos (λ p. p ⊗ C)"
  apply(rule conj_monotone_left_rule)
  apply assumption
  done

lemma conjunction_right_iipos: "iipos (λ p. C ⊗ p)"
  apply(rule conj_monotone_right_rule)
  apply assumption
  done

lemma disjunction_left_iipos: "iipos (λ p. p ∨ C)"
  apply(rule disj_monotone_left_impl_rule)
  apply assumption
  done

lemma disjunction_right_iipos: "iipos (λ p. C ∨ p)"
  apply(rule disj_monotone_right_impl_rule)
  apply assumption
  done

lemma implication_left_iineg: "iineg (λ p. p ⇛ C)"
proof -
  { fix A B
    { assume ab:"A ⇛ B"
      from implB' and ab have "(B ⇛ C) ⇛ A ⇛ C" ..
    } have "A ⇛ B ⟹ (B ⇛ C) ⇛ A ⇛ C" by fact
  } show "iineg (λ p. p ⇛ C)" by fact
qed

lemma implication_right_iipos: "iipos (λ p. C ⇛ p)"
proof -
  { fix A B
    { assume ab:"A ⇛ B"
      from implB and ab have "(C ⇛ A) ⇛ C ⇛ B" ..
    } have "A ⇛ B ⟹ (C ⇛ A) ⇛ C ⇛ B" by fact
  } show "iipos (λ p. C ⇛ p)" by fact
qed

lemma entailment_left_eineg: "eineg (λ p . p → C)"
proof -
  { fix A B
    { assume ab:"A → B"
      from entl_impl and entl_cs have "(A → B) ⊗ (B → C) ⇛ (A → C)" ..
      from conj_export and this have "A → B ⇛ (B → C) ⇛ A → C" ..
      from this and ab have "(B → C) ⇛ (A → C)" ..
    } have "A → B ⟹ (B → C) ⇛ (A → C)" by fact
  } show "eineg (λ p. p → C)" by fact
qed

lemma entailment_right_eipos: "eipos (λ p . C → p)"
proof -
  { fix A B
    { assume ab:"A → B"
      from entl_impl and entl_cs have "(C → A) ⊗ (A → B) ⇛ (C → B)" ..
      then have "(A → B) ⊗ (C → A) ⇛ (C → B)" by(rule bisub_rule[OF conj_bicomm])
      from conj_export and this have "A → B ⇛ (C → A) ⇛ C → B" ..
      from this and ab have "(C → A) ⇛ (C → B)" ..
    } have "A → B ⟹ (C → A) ⇛ (C → B)" by fact
  } show "eipos (λ p. C → p)" by fact
qed

lemma epos_epos_epos: "epos C ⟹ epos D ⟹ epos (λ p. D ( C p ))"
proof -

qed
