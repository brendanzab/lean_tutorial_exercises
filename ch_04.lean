open classical

variables (A : Type) (p q : A → Prop)
variable a : A
variable r : Prop


-- Universal quantifiers


example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
  iff.intro
    (assume H : ∀ x, p x ∧ q x,
     show (∀ x, p x) ∧ (∀ x, q x), from
       and.intro
         (take x, show p x, from and.left (H x))
         (take x, show q x, from and.right (H x)))
    (assume H : (∀ x, p x) ∧ (∀ x, q x),
     have Hp : ∀ x, p x, from and.left H,
     have Hq : ∀ x, q x, from and.right H,
     show (∀ x, p x ∧ q x), from
       (take x, and.intro (Hp x) (Hq x)))

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
  assume H : ∀ x, p x → q x,
  assume Hp : ∀ x, p x,
  show ∀ x, q x, from
    (take x, (H x) (Hp x))

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
  assume H : (∀ x, p x) ∨ (∀ x, q x),
  or.elim H
    (assume Hp : ∀ x, p x,
     take x, or.inl (Hp x))
    (assume Hq : ∀ x, q x,
     take x, or.inr (Hq x))


-- Moving universal quantifiers


example : A → ((∀ x : A, r) ↔ r) :=
  assume x : A,
  iff.intro
    (assume Hr : ∀ x, r, Hr x)
    (assume Hr : r, take x, Hr)

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
  iff.intro
    (assume H : ∀ x, p x ∨ r,
     have Hp : ∀ x, p x, from
       (take x,
        or.elim (H x)
          (assume Hp : p x, Hp)
          (assume Hr : r, sorry)),
     show (∀ x, p x) ∨ r, from or.inl Hp)
    (assume H : (∀ x, p x) ∨ r,
     take x,
     or.elim H
       (assume Hp : ∀ x, p x, or.inl (Hp x))
       (assume Hr : r, or.inr Hr))

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
  iff.intro
    (assume H : ∀ x, r → p x,
     show r → ∀ x, p x, from
       assume Hr : r,
       take x : A,
       show p x, from (H x) Hr)
    (assume H : r → ∀ x, p x,
     show ∀ x, r → p x, from
       take x : A,
       assume Hr : r,
       show p x, from (H Hr) x)


-- The Barber Paradox

-- "in a certain town there is a (male) barber that shaves all and only
--  the men who do not shave themselves"

variables (men : Type) (barber : men) (shaves : men → men → Prop)

open classical
example (H : ∀ x : men, shaves barber x ↔ ¬shaves x x) : false :=
  sorry


--

example : (∃ x : A, r) → r := sorry
example : r → (∃ x : A, r) := sorry
example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := sorry
example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := sorry

--

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := sorry
example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := sorry
example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := sorry
example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := sorry

--

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := sorry
example : (∃ x, p x → r) ↔ (∀ x, p x) → r := sorry
example : (∃ x, r → p x) ↔ (r → ∃ x, p x) := sorry
