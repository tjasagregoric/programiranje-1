-- Izomorfizmi

theorem eq1 {A B : Prop} : (A ∧ B) ↔ (B ∧ A) :=
  by
    --apply Iff.intro
    constructor
    intro ab
    constructor
    exact ab.right --dostop do para kar in v resnici je
    exact ab.left
    --sedaj pa se druga smer
    intro ba
    sorry

theorem eq2 {A B : Prop} : (A ∨ B) ↔ (B ∨ A) :=
  sorry

theorem eq3 {A B C : Prop} : (A ∧ (B ∧ C)) ↔ (B ∧ (A ∧ C)) :=
  sorry

theorem eq4 {A B C : Prop} : (A ∨ (B ∨ C)) ↔ (B ∨ (A ∨ C)) :=
 sorry

theorem eq5 {A B C : Prop} : A ∧ (B ∨ C) ↔ (A ∧ B) ∨ (A ∧ C) :=
  sorry

theorem eq6 {A B C : Prop} : (B ∨ C) → A ↔ (B → A) ∧ (C → A) :=
  by
    constructor
    intro h
    constructor
    intro b
    apply h
    left --izbrali smo si levo stran ker imamo b
    exact b
    intro c -- moramo nacarati c ali b iz c
    have xx : B ∨ C := Or.inr c --neka lukna ali c in lean nezna rect samo 'a
    have yy := h (Or.inr c)
    exact yy
    intro h BvC
    cases BvC --moramo eksplicitno oznaciti
    case inr c =>
      exact h.right c
    case inl b =>
      have l := h.left
      apply h.left
      exact b
      --exact h.left b



theorem eq7 {A B C : Prop} : C → (A ∧ B) ↔ (C → A) ∧ (C → B) :=
  sorry
