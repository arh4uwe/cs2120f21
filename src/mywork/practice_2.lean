/-
Prove the following simple logical conjectures.
Give a formal and an English proof of each one.
Your English language proofs should be complete
in the sense that they identify all the axioms
and/or theorems that you use.
-/

example : true := true.intro

example : false := _    -- trick question? why?

example : ∀ (P : Prop), P ∨ P ↔ P := 
begin
  assume P, 
  apply iff.intro _ _,
  -- forward
    assume porp,
    apply or.elim porp,
    -- left disjunct is true
      assume p,
      exact p,
    -- right disjunct is true
      assume p,
      exact p,
  -- backwards
    assume p,
    exact or.intro_left P p,
end

example : ∀ (P : Prop), P ∧ P ↔ P := 
begin
  assume P,
  apply iff.intro,
  assume p_p,
  apply and.elim_left p_p,
  assume p,
  apply and.intro,
  exact p,
  exact p,
end

example : ∀ (P Q : Prop), P ∨ Q ↔ Q ∨ P := 
begin
  assume P Q,
  apply iff.intro,
  assume porq,
  apply or.elim porq,
  assume p,
  apply or.intro_right,
  exact p,
  assume q,
  apply or.intro_left,
  exact q,
  assume qorp,
  apply or.elim qorp,
  assume q,
  apply or.intro_right,
  exact q,
  assume p,
  apply or.intro_left,
  exact p,
end

example : ∀ (P Q : Prop), P ∧ Q ↔ Q ∧ P := 
begin
  assume P Q,
  apply iff.intro,
  -- forwards
    assume pandq,
    apply and.intro,
    apply and.elim_right pandq,
    apply and.elim_left pandq,
  -- backwards
    assume qandp,
    apply and.intro,
    apply and.elim_right qandp,
    apply and.elim_left qandp,
end

example : ∀ (P Q R : Prop), P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := 
begin
  assume P Q R,
  apply iff.intro,
  -- forwards
    assume p_and_qorr,
    have p : P := and.elim_left p_and_qorr,
    have qorr : Q ∨ R := and.elim_right p_and_qorr,
    apply or.elim qorr,
    -- if Q is true
      assume q,
      apply or.intro_left,
      apply and.intro,
      exact p,
      exact q,
    -- if R is true
      assume r,
      apply or.intro_right,
      apply and.intro,
      exact p,
      exact r,
  -- backwards
    assume pandq_or_pandr,
    apply or.elim pandq_or_pandr,
    -- if P ∧ Q is true
      assume pandq,
      have p := and.elim_left pandq,
      have q := and.elim_right pandq,
      apply and.intro,
      exact p,
      apply or.intro_left,
      exact q,
    -- if P ∧ R is true
      assume pandr,
      have p := and.elim_left pandr,
      have r := and.elim_right pandr,
      apply and.intro,
      exact p,
      apply or.intro_right,
      exact r,
end

example : ∀ (P Q R : Prop), P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) := 
begin
  assume P Q R,
  apply iff.intro,
  -- forwards
    assume p_or_qandr,
    apply or.elim p_or_qandr,
    -- if P is true
      assume p,
      apply and.intro,
      apply or.intro_left,
      exact p,
      apply or.intro_left,
      exact p,
    -- if Q ∧ R is true
      assume qandr,
      have q : Q := and.elim_left qandr,
      have r : R := and.elim_right qandr,
      apply and.intro,
      apply or.intro_right,
      exact q,
      apply or.intro_right,
      exact r,
  -- backwards
    assume porq_and_porr,
    have porq : P ∨ Q := and.elim_left porq_and_porr,
    have porr : P ∨ R := and.elim_right porq_and_porr,
    apply or.elim porq,
    -- if P is true
      assume p,
      apply or.intro_left,
      exact p,
    -- if Q is true
      assume q,
      apply or.elim porr,
      -- if P is true
        assume p,
        apply or.intro_left,
        exact p,
      -- if R is true
        assume r,
        apply or.intro_right,
        apply and.intro,
        exact q,
        exact r,
end

example : ∀ (P Q : Prop), P ∧ (P ∨ Q) ↔ P := 
begin
  assume P Q,
  apply iff.intro,
  -- forwards
    assume p_and_porq,
    exact and.elim_left p_and_porq,
  -- backwards,
    assume p,
    apply and.intro,
    exact p,
    apply or.intro_left,
    exact p,
end

example : ∀ (P Q : Prop), P ∨ (P ∧ Q) ↔ P := 
begin
  assume P Q,
  apply iff.intro,
  -- forwards
    assume p_or_pandq,
    apply or.elim p_or_pandq,
    -- if P is true
      assume p,
      exact p,
    -- if P ∧ Q is true
      assume pandq,
      exact and.elim_left pandq,
  -- backwards
    assume p,
    apply or.intro_left,
    exact p,
end

example : ∀ (P : Prop), P ∨ true ↔ true := 
begin
  assume P,
  apply iff.intro,
  -- forwards
    assume pandtrue,
    apply true.intro,
  -- backwards
    assume tr,
    apply or.intro_right,
    apply true.intro,
end

example : ∀ (P : Prop), P ∨ false ↔ P := 
begin
  assume P,
  apply iff.intro,
  -- forwards
    assume pandfalse,
    apply or.elim pandfalse,
    -- if P is true
      assume p,
      exact p,
    -- if false is true
      assume fa,
      apply false.elim fa,
  -- backwards
    assume p,
    apply or.intro_left,
    exact p,
end

example : ∀ (P : Prop), P ∧ true ↔ P := 
begin
  assume p,
  apply iff.intro,
  -- forwards
    assume pandtrue,
    exact and.elim_left pandtrue,
  -- backwards
    assume p,
    apply and.intro,
    exact p,
    apply true.intro,
end

example : ∀ (P : Prop), P ∧ false ↔ false := 
begin
  assume P,
  apply iff.intro,
  -- forwards
    assume pandfalse,
    exact and.elim_right pandfalse,
  -- backwards
    assume fa,
    apply false.elim,
    exact fa,
end


