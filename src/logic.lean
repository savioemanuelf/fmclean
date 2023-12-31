
section propositional

variables P Q R : Prop


------------------------------------------------
-- Proposições de dupla negaço:
------------------------------------------------

theorem doubleneg_intro :
  P → ¬¬P  :=
begin
  intro hp,    
  intro hnp,
  apply hnp hp,
end

theorem doubleneg_elim :
  ¬¬P → P  :=
begin
  intro hnnp,
  by_cases p: P,
  exact p,

  contradiction,
end

theorem doubleneg_law :
  ¬¬P ↔ P  :=
begin
  split,
  exact doubleneg_elim P,
  
  exact doubleneg_intro P,
end

------------------------------------------------
-- Comutatividade dos ∨,∧:
------------------------------------------------

theorem disj_comm :
  (P ∨ Q) → (Q ∨ P)  :=
begin
  intro hpq,
  cases hpq,
  right,
  exact hpq,

  left,
  exact hpq,
end

theorem conj_comm :
  (P ∧ Q) → (Q ∧ P)  :=
begin
  intro hpq,
  split,
  cases hpq,
  exact hpq_right,

  cases hpq,
  exact hpq_left,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos →,∨:
------------------------------------------------

theorem impl_as_disj_converse :
  (¬P ∨ Q) → (P → Q)  :=
begin
  intro hnpq,
  intro hp,
  cases hnpq,
  contradiction,

  exact hnpq,
end

theorem disj_as_impl :
  (P ∨ Q) → (¬P → Q)  :=
begin
  intro hpq,
  intro hnp,
  cases hpq,
  contradiction,
  
  exact hpq,
end


------------------------------------------------
-- Proposições de contraposição:
------------------------------------------------

theorem impl_as_contrapositive :
  (P → Q) → (¬Q → ¬P)  :=
begin
  intro hpq,
  intro hnq,
  intro hp,
  apply hnq (hpq(hp)),
end

theorem impl_as_contrapositive_converse :
  (¬Q → ¬P) → (P → Q)  :=
begin
  intro hnqnp,
  by_cases q: Q,
  intro hp,
  exact q,

  intro hp,
  have np : ¬P := hnqnp q,
  contradiction,
end

theorem contrapositive_law :
  (P → Q) ↔ (¬Q → ¬P)  :=
begin
  split,
  apply impl_as_contrapositive,
  
  apply impl_as_contrapositive_converse,
end


------------------------------------------------
-- A irrefutabilidade do LEM:
------------------------------------------------

theorem lem_irrefutable :
  ¬¬(P∨¬P)  :=
begin
  intro hpnp,
  apply hpnp,
  right,
  intro hp,
  apply hpnp,
  left,
  exact hp,
end


------------------------------------------------
-- A lei de Peirce
------------------------------------------------

theorem peirce_law_weak :
  ((P → Q) → P) → ¬¬P  :=
begin
  intro hpq,
  intro np,
  apply np,
  apply hpq,
  intro hp,
  contradiction,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∨,∧:
------------------------------------------------

theorem disj_as_negconj :
  P∨Q → ¬(¬P∧¬Q)  :=
begin
  intro hpq,
  intro hnpnq,
  cases hpq with p q,
  apply hnpnq.left p,

  apply hnpnq.right q,
end

theorem conj_as_negdisj :
  P∧Q → ¬(¬P∨¬Q)  :=
begin
  intro hpq,
  intro hnpnq,
  cases hnpnq with np nq,
  exact np hpq.left,

  exact nq hpq.right,
end


------------------------------------------------
-- As leis de De Morgan para ∨,∧:
------------------------------------------------

theorem demorgan_disj :
  ¬(P∨Q) → (¬P ∧ ¬Q)  :=
begin
  intro hnpq,
  split,
  intro p,
  apply hnpq,
  left,
  exact p,

  intro q,
  apply hnpq,
  right,
  exact q,
end

theorem demorgan_disj_converse :
  (¬P ∧ ¬Q) → ¬(P∨Q)  :=
begin
  intro hnpnq,
  intro hpq,
  cases hpq with p q,
  exact hnpnq.left p,

  exact hnpnq.right q,
end

theorem demorgan_conj :
  ¬(P∧Q) → (¬Q ∨ ¬P)  :=
begin
  intro hnpq,
  by_cases q : Q,
  right,
  intro p,
  apply hnpq,
  split,

  exact p,

  exact q,
  
  left,
  exact q,
end

theorem demorgan_conj_converse :
  (¬Q ∨ ¬P) → ¬(P∧Q)  :=
begin
  intro hnqnp,
  intro hpq,
  cases hnqnp with nq np,
  exact nq hpq.right,

  exact np hpq.left,
end

theorem demorgan_conj_law :
  ¬(P∧Q) ↔ (¬Q ∨ ¬P)  :=
begin
  split,
  exact demorgan_conj P Q,
  
  exact demorgan_conj_converse P Q,
end

theorem demorgan_disj_law :
  ¬(P∨Q) ↔ (¬P ∧ ¬Q)  :=
begin
  split, 
  exact demorgan_disj P Q,

  exact demorgan_disj_converse P Q,
end

------------------------------------------------
-- Proposições de distributividade dos ∨,∧:
------------------------------------------------

theorem distr_conj_disj :
  P∧(Q∨R) → (P∧Q)∨(P∧R)  :=
begin
  intro hpqr,
  cases hpqr with p qr,
  cases qr with q r,
  left,
  split,
  exact p,

  exact q,

  right,
  split,
  exact p,

  exact r,
end

theorem distr_conj_disj_converse :
  (P∧Q)∨(P∧R) → P∧(Q∨R)  :=
begin
  intro hpqpr,
  cases hpqpr with pq pr,
  split,
  exact pq.left,

  left,
  exact pq.right,

  split,
  exact pr.left,

  right,
  exact pr.right,
end

theorem distr_disj_conj :
  P∨(Q∧R) → (P∨Q)∧(P∨R)  :=
begin
    intro hpqr,
  cases hpqr with p qr,
  split,
  left,
  exact p,

  left,
  exact p,

  split,
  right,
  exact qr.left,

  right,
  exact qr.right,
end

theorem distr_disj_conj_converse :
  (P∨Q)∧(P∨R) → P∨(Q∧R)  :=
begin
    intro hpqpr,
  cases hpqpr with pq pr,
  cases pq with p q,
  left,
  exact p,
  
  cases pr with p r,
  left,
  exact p,

  right,
  split,
  exact q,

  exact r,
end


------------------------------------------------
-- Currificação
------------------------------------------------

theorem curry_prop :
  ((P∧Q)→R) → (P→(Q→R))  :=
begin
  intro hpqr,
  intros p q,
  apply hpqr,
  split,
  exact p,

  exact q,
end

theorem uncurry_prop :
  (P→(Q→R)) → ((P∧Q)→R)  :=
begin
  intro hpqr,
  intro pq,
  cases pq with p q,
  apply hpqr,
  exact p,

  exact q,
end


------------------------------------------------
-- Reflexividade da →:
------------------------------------------------

theorem impl_refl :
  P → P  :=
begin
  intro p,
  exact p,
end

------------------------------------------------
-- Weakening and contraction:
------------------------------------------------

theorem weaken_disj_right :
  P → (P∨Q)  :=
begin
  intro p,
  left,
  exact p,
end

theorem weaken_disj_left :
  Q → (P∨Q)  :=
begin
  intro q,
  right,
  exact q,
end

theorem weaken_conj_right :
  (P∧Q) → P  :=
begin
  intro pq,
  exact pq.left,
end

theorem weaken_conj_left :
  (P∧Q) → Q  :=
begin
  intro pq,
  exact pq.right,
end

theorem conj_idempot :
  (P∧P) ↔ P :=
begin
  split,
  intro pp,
  exact pp.left,

  intro p,
  split,
  exact p,

  exact p,
end

theorem disj_idempot :
  (P∨P) ↔ P  :=
begin
  split,
  intro pp,
  cases pp with p p,
  exact p,

  exact p,

  intro p,
  left,
  exact p,
end

end propositional


----------------------------------------------------------------


section predicate

variable U : Type
variables P Q : U -> Prop


------------------------------------------------
-- As leis de De Morgan para ∃,∀:
------------------------------------------------

theorem demorgan_exists :
  ¬(∃x, P x) → (∀x, ¬P x)  :=
begin
  intro h,
  intro u,
  intro pu,
  apply h,
  existsi u,
  exact pu,
end

theorem demorgan_exists_converse :
  (∀x, ¬P x) → ¬(∃x, P x)  :=
begin
  intro h,
  intro h',
  cases h' with x px,
  apply h x,
  exact px,
end

theorem demorgan_forall :
  ¬(∀x, P x) → (∃x, ¬P x)  :=
begin
  intro h,
  by_contradiction h',
  apply h,
  intro x,
  by_contradiction npx,
  apply h',
  existsi x,
  exact npx,
end

theorem demorgan_forall_converse :
  (∃x, ¬P x) → ¬(∀x, P x)  :=
begin
  intro h,
  intro h',
  cases h with x npx,
  have px : P x := h'(x),
  exact npx px,
end

theorem demorgan_forall_law :
  ¬(∀x, P x) ↔ (∃x, ¬P x)  :=
begin
  split,
  exact demorgan_forall U P,

  exact demorgan_forall_converse U P,
end

theorem demorgan_exists_law :
  ¬(∃x, P x) ↔ (∀x, ¬P x)  :=
begin
  split,
  exact demorgan_exists U P,

  exact demorgan_exists_converse U P,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∃,∀:
------------------------------------------------

theorem exists_as_neg_forall :
  (∃x, P x) → ¬(∀x, ¬P x)  :=
begin
  intro h,
  intro h',
  cases h with x px,
  have npx : ¬P x := h' x,
  exact npx px,
end

theorem forall_as_neg_exists :
  (∀x, P x) → ¬(∃x, ¬P x)  :=
begin
  intro h,
  intro h',
  cases h' with x npx,
  have px : P x := h x,
  exact npx px,
end

theorem forall_as_neg_exists_converse :
  ¬(∃x, ¬P x) → (∀x, P x)  :=
begin
  intro h,
  intro x,
  by_contra hnpx,
  apply h,
  existsi x,
  exact hnpx,
end

theorem exists_as_neg_forall_converse :
  ¬(∀x, ¬P x) → (∃x, P x)  :=
begin
  intro h,
  by_contra h',
  apply h,
  intro x,
  intro px,
  apply h',
  existsi x,
  exact px,
end

theorem forall_as_neg_exists_law :
  (∀x, P x) ↔ ¬(∃x, ¬P x)  :=
begin
  split,
  exact forall_as_neg_exists U P,

  exact forall_as_neg_exists_converse U P,
end

theorem exists_as_neg_forall_law :
  (∃x, P x) ↔ ¬(∀x, ¬P x)  :=
begin
  split,
  exact exists_as_neg_forall U P,

  exact exists_as_neg_forall_converse U P,
end


------------------------------------------------
--  Proposições de distributividade de quantificadores:
------------------------------------------------

theorem exists_conj_as_conj_exists :
  (∃x, P x ∧ Q x) → (∃x, P x) ∧ (∃x, Q x)  :=
begin
  intro h,
  cases h with x pxqx,
  split,
  existsi x,
  exact pxqx.left,

  existsi x,
  exact pxqx.right,
end

theorem exists_disj_as_disj_exists :
  (∃x, P x ∨ Q x) → (∃x, P x) ∨ (∃x, Q x)  :=
begin
  intro h,
  cases h with x pxqx,
  cases pxqx with px qx,
  left,
  existsi x,
  exact px,

  right,
  existsi x,
  exact qx,
end

theorem exists_disj_as_disj_exists_converse :
  (∃x, P x) ∨ (∃x, Q x) → (∃x, P x ∨ Q x)  :=
begin
  intro h,
  cases h with hpx,
  cases hpx with x px,
  existsi x,
  left,
  exact px,

  cases h with x qx,
  existsi x,
  right,
  exact qx,
end

theorem forall_conj_as_conj_forall :
  (∀x, P x ∧ Q x) → (∀x, P x) ∧ (∀x, Q x)  :=
begin
  intro h,
  split,
  intro x,
  have pxqx : P x ∧ Q x := h x,
  exact pxqx.left,

  intro x,
  have pxqx : P x ∧ Q x := h x,
  exact pxqx.right,
end

theorem forall_conj_as_conj_forall_converse :
  (∀x, P x) ∧ (∀x, Q x) → (∀x, P x ∧ Q x)  :=
begin
  intro h,
  intro x,
  cases h with hpx hqx,
  split,
  exact hpx x,

  exact hqx x,
end


theorem forall_disj_as_disj_forall_converse :
  (∀x, P x) ∨ (∀x, Q x) → (∀x, P x ∨ Q x)  :=
begin
  intro h,
  cases h with hpx hqx,
  intro x,
  left,
  exact hpx x,

  intro x,
  right,
  exact hqx x,
end


/- NOT THEOREMS --------------------------------

theorem forall_disj_as_disj_forall :
  (∀x, P x ∨ Q x) → (∀x, P x) ∨ (∀x, Q x)  :=
begin
end

theorem exists_conj_as_conj_exists_converse :
  (∃x, P x) ∧ (∃x, Q x) → (∃x, P x ∧ Q x)  :=
begin
end

---------------------------------------------- -/

end predicate
