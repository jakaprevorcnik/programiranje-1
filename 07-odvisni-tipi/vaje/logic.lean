-- Izomorfizmi

theorem eq1 {A B : Prop} : (A ∧ B) ↔ (B ∧ A) :=
  by
    constructor
    intro h1
    constructor
    exact h1.right
    exact h1.left
    intro h2
    constructor
    exact h2.right
    exact h2.left

theorem eq2 {A B : Prop} : (A ∨ B) ↔ (B ∨ A) :=
   by
    constructor
    . intro h1
      cases h1 with  --locimo glede na levo ali desno izjavo v inkluziji
      | inl h1a => 
        apply Or.inr -- iz a naredibmo b ali a
        assumption
      | inr h1b => 
        apply Or.inl
        assumption
    . intro h2
      cases h2 with
      | inl h2a => 
        apply Or.inr
        assumption
      | inr h2b => 
        apply Or.inl
        assumption


theorem eq3 {A B C : Prop} : (A ∧ (B ∧ C)) ↔ (B ∧ (A ∧ C)) :=
  by
  constructor
  . intro h1
    constructor
    exact h1.right.left
    constructor
    exact h1.left
    exact h1.right.right
  . intro h2
    constructor
    exact h2.right.left
    constructor
    exact h2.left
    exact h2.right.right

theorem eq4 {A B C : Prop} : (A ∨ (B ∨ C)) ↔ (B ∨ (A ∨ C)) :=
  sorry

theorem eq5 {A B C : Prop} : A ∧ (B ∨ C) ↔ (A ∧ B) ∨ (A ∧ C) :=
  sorry

theorem eq6 {A B C : Prop} : (B ∨ C) → A ↔ (B → A) ∧ (C → A) :=
  sorry

theorem eq7 {A B C : Prop} : C → (A ∧ B) ↔ (C → A) ∧ (C → B) :=
  by
  constructor
  . intro h1
    constructor
    . intro hc
      exact (h1 hc).left
    . intro hc
      exact (h1 hc).right
  . intro h2
    . intro hc
      exact
   
    
    
      

    
