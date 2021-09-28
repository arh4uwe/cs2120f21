-- 1
example : 0 ≠ 1 :=
begin
  -- ¬ (0 = 1)
  -- (0 = 1) → false
  assume h,
  cases h,
end


-- 2
example : 0 ≠ 0 → 2 = 3 :=
begin
  assume h,
  have f : false := h (eq.refl 0),
  exact false.elim (f),
end

-- 3
example : ∀ (P : Prop), P → ¬¬P :=
begin
  assume P,
  assume (p : P),
  -- ¬¬P
  -- ¬P → false
  -- (P → false) → false
  assume h,
  have f := h p,
  exact f,
end 

-- We might need classical (vs constructive) reasoning 
#check classical.em
open classical
#check em

/-
axiom em : ∀ (p : Prop), p ∨ ¬p

This is the famous and historically controversial
"law" (now axiom) of the excluded middle. It's is
a key to proving many intuitive theorems in logic
and mathematics. But it also leads to giving up on
having evidence *why* something is either true or
not true, in that you no longer need a proof of 
either P or of ¬P to have a proof of P ∨ ¬P.
-/

-- 4
theorem neg_elim : ∀ (P : Prop), ¬¬P → P :=
begin
  assume P,
  assume h,
  have pornp := classical.em P,
  cases pornp with p pn,
  assumption,
  contradiction,
end

-- 5
theorem demorgan_1 : ∀ (P Q : Prop), ¬ (P ∧ Q) ↔ ¬ P ∨ ¬ Q :=
begin
  assume P Q,
  apply iff.intro,
  assume h,
  have pornp := classical.em P,
  cases pornp with p np,
  have qornq := classical.em Q,
  cases qornq with q nq,
  have pandq : P ∧ Q := and.intro p q,
  apply false.elim,
  exact h pandq,
  apply or.intro_right,
  exact nq,
  apply or.intro_left,
  exact np,
  assume h₁ h₂,
  have p := and.elim_left h₂,
  have q := and.elim_right h₂,
  cases h₁ with np nq,
  exact np p,
  exact nq q,
end


-- 6
theorem demorgan_2 : ∀ (P Q : Prop), ¬ (P ∨ Q) → ¬P ∧ ¬Q :=
begin
  assume P Q h,
  apply and.intro,
  assume p,
  have porq : P ∨ Q := or.intro_left _ p,
  exact h porq,
  assume q,
  have porq : P ∨ Q := or.intro_right _ q,
  exact h porq,
end


-- 7
theorem disappearing_opposite : 
  ∀ (P Q : Prop), P ∨ ¬P ∧ Q ↔ P ∨ Q := 
begin
  assume P Q,
  apply iff.intro,
  -- forward
    assume h,
    cases h,
    -- P
      apply or.intro_left,
      exact h,
    -- ¬P ∧ Q
      have q := and.elim_right h,
      apply or.intro_right,
      exact q,
  -- backward
    assume porq,
    cases porq with p q,
    -- P
      apply or.intro_left,
      exact p,
    -- Q
      have pornp := classical.em P,
      cases pornp with p np,
      -- P
        apply or.intro_left,
        exact p,
      -- ¬P
        apply or.intro_right,
        apply and.intro,
        exact np,
        exact q,
end


-- 8
theorem distrib_and_or : 
  ∀ (P Q R: Prop), (P ∨ Q) ∧ (P ∨ R) ↔
                    P ∨ (Q ∧ R) :=
begin
  assume P Q R,
  apply iff.intro,
  -- forward
    assume h,
    have porq := and.elim_left h,
    have porr := and.elim_right h,
    cases porq with p q,
    -- P
      apply or.intro_left,
      exact p,
    -- Q
      cases porr with p r,
      -- P
        apply or.intro_left,
        exact p,
      -- R
        apply or.intro_right,
        apply and.intro,
        apply q,
        apply r,
  -- backward
    assume h,
    cases h with p qandr,
    -- P
      apply and.intro,
      apply or.intro_left,
      exact p,
      apply or.intro_left,
      exact p,
    -- Q ∧ R
      have q := and.elim_left qandr,
      have r := and.elim_right qandr,
      apply and.intro,
      apply or.intro_right,
      exact q,
      apply or.intro_right,
      exact r,
end

-- remember or is right associative
-- you need this to know what the lefts and rights are
-- 9
theorem distrib_and_or_foil : 
  ∀ (P Q R S : Prop),
  (P ∨ Q) ∧ (R ∨ S) ↔
  (P ∧ R) ∨ (P ∧ S) ∨ (Q ∧ R) ∨ (Q ∧ S) :=
begin
  assume P Q R S,
  apply iff.intro,
  -- forward
    assume h,
    have porq := and.elim_left h,
    have rors := and.elim_right h,
    cases porq with p q,
    -- P
      cases rors with r s,
      -- R
        apply or.intro_left,
        apply and.intro p r,
      -- S
        apply or.intro_right,
        apply or.intro_left,
        apply and.intro p s,
    -- Q
      cases rors with r s,
      -- R
        apply or.intro_right,
        apply or.intro_right,
        apply or.intro_left,
        exact and.intro q r,
      -- S
        repeat {apply or.intro_right},
        exact and.intro q s,
  -- backward
    assume h,
    cases h with pandr h,
    -- P ∧ R
      apply and.intro,
      apply or.intro_left,
      exact and.elim_left pandr,
      apply or.intro_left,
      exact and.elim_right pandr,
    cases h with pands h,
    -- P ∧ S
      apply and.intro,
      apply or.intro_left,
      exact and.elim_left pands,
      apply or.intro_right,
      exact and.elim_right pands,
    cases h with qandr qands,
    -- Q ∧ R
      apply and.intro,
      apply or.intro_right,
      exact and.elim_left qandr,
      apply or.intro_left,
      exact and.elim_right qandr,
    -- Q ∧ S
      apply and.intro,
      apply or.intro_right,
      exact and.elim_left qands,
      apply or.intro_right,
      exact and.elim_right qands,
end


/- 10
Formally state and prove the proposition that
not every natural number is equal to zero.
-/
lemma not_all_nats_are_zero : ¬ (∀ n : ℕ, n = 0) :=
begin
  assume h,
  have f : 1 = 0 := h 1,
  contradiction,
end 

-- 11. equivalence of P→Q and (¬P∨Q)
example : ∀ (P Q : Prop), (P → Q) ↔ (¬P ∨ Q) :=
begin
  assume P Q,
  apply iff.intro,
  -- forward
    assume h,
    have pornp := classical.em P,
    cases pornp with p np,
    -- P
      have q : Q := h p,
      apply or.intro_right,
      exact q,
    -- ¬P
      apply or.intro_left,
      exact np,
  -- backward
    assume h,
    assume p,
    cases h with np q,
    -- ¬P
      contradiction,
    -- Q
      exact q,
end

-- 12
example : ∀ (P Q : Prop), (P → Q) → (¬ Q → ¬ P) :=
begin
  assume P Q h nq p,
  have q := h p,
  contradiction,
end

-- 13
example : ∀ (P Q : Prop), ( ¬P → ¬Q) → (Q → P) :=
begin
  assume P Q h q,
  have pornp : P ∨ ¬P := classical.em P,
  cases pornp with p np,
  -- P
    exact p,
  -- ¬P
    have nq : ¬Q := h np,
    contradiction,
end

