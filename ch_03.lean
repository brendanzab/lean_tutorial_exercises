variables p q r s : Prop


-- commutativity of ∧ and ∨


example : p ∧ q ↔ q ∧ p :=
  iff.intro and.swap and.swap

example : p ∨ q ↔ q ∨ p :=
  iff.intro or.swap or.swap


-- associativity of ∧ and ∨


example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  iff.intro
    (assume H : (p ∧ q) ∧ r,
     have Hpq : p ∧ q, from and.left H,
     have Hp : p, from and.left Hpq,
     have Hq : q, from and.right Hpq,
     have Hr : r, from and.right H,
     show p ∧ (q ∧ r), from and.intro Hp (and.intro Hq Hr))
    (assume H : p ∧ (q ∧ r),
     have Hp : p, from and.left H,
     have Hqr : q ∧ r, from and.right H,
     have Hq : q, from and.left Hqr,
     have Hr : r, from and.right Hqr,
     show (p ∧ q) ∧ r, from and.intro (and.intro Hp Hq) Hr)

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  iff.intro
    (assume H : (p ∨ q) ∨ r,
     or.elim H
       (assume Hpq : p ∨ q,
        or.elim Hpq
          (assume Hp : p,
           show p ∨ (q ∨ r), from or.inl Hp)
          (assume Hq : q,
           have Hqr : q ∨ r, from or.inl Hq,
           show p ∨ (q ∨ r), from or.inr Hqr))
       (assume Hr : r,
        have Hqr : q ∨ r, from or.inr Hr,
        show p ∨ (q ∨ r), from or.inr Hqr))
    (assume H : p ∨ (q ∨ r),
     or.elim H
       (assume Hp : p,
        have Hpq : p ∨ q, from or.inl Hp,
        show (p ∨ q) ∨ r, from or.inl Hpq)
       (assume Hqr : q ∨ r,
        or.elim Hqr
          (assume Hq : q,
           have Hpq : p ∨ q, from or.inr Hq,
           show (p ∨ q) ∨ r, from or.inl Hpq)
          (assume Hr : r,
           show (p ∨ q) ∨ r, from or.inr Hr)))


-- distributivity


example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  iff.intro
    (assume H : p ∧ (q ∨ r),
     have Hp : p, from and.left H,
     have Hqr : q ∨ r, from and.right H,
     or.elim Hqr
       (assume Hq : q,
        have Hpq : p ∧ q, from and.intro Hp Hq,
        show (p ∧ q) ∨ (p ∧ r), from or.inl Hpq)
       (assume Hr : r,
        have Hpr : p ∧ r, from and.intro Hp Hr,
        show (p ∧ q) ∨ (p ∧ r), from or.inr Hpr))
    (assume H : (p ∧ q) ∨ (p ∧ r),
     or.elim H
       (assume Hpq : p ∧ q,
        have Hp : p, from and.left Hpq,
        have Hq : q, from and.right Hpq,
        show p ∧ (q ∨ r), from and.intro Hp (or.inl Hq))
       (assume Hpr : p ∧ r,
        have Hp : p, from and.left Hpr,
        have Hr : r, from and.right Hpr,
        show p ∧ (q ∨ r), from and.intro Hp (or.inr Hr)))

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  iff.intro
    (assume H : p ∨ (q ∧ r),
     or.elim H
       (assume Hp : p,
        have Hpq : p ∨ q, from or.inl Hp,
        have Hpr : p ∨ r, from or.inl Hp,
        show (p ∨ q) ∧ (p ∨ r), from and.intro Hpq Hpr)
       (assume Hqr : q ∧ r,
        have Hq : q, from and.left Hqr,
        have Hr : r, from and.right Hqr,
        have Hpq : p ∨ q, from or.inr Hq,
        have Hpr : p ∨ r, from or.inr Hr,
        show (p ∨ q) ∧ (p ∨ r), from and.intro Hpq Hpr))
    (assume H : (p ∨ q) ∧ (p ∨ r),
     have Hpq : p ∨ q, from and.left H,
     have Hpr : p ∨ r, from and.right H,
     or.elim Hpq
       (assume Hp : p,
        show p ∨ (q ∧ r), from or.inl Hp)
       (assume Hq : q,
        or.elim Hpr
          (assume Hp : p,
           show p ∨ (q ∧ r), from or.inl Hp)
          (assume Hr : r,
           have Hqr : q ∧ r, from and.intro Hq Hr,
           show p ∨ (q ∧ r), from or.inr Hqr)))


-- other properties


example : (p → (q → r)) ↔ (p ∧ q → r) :=
  iff.intro
    (assume H : p → q → r,
     assume Hpq : p ∧ q,
     have Hp : p, from and.left Hpq,
     have Hq : q, from and.right Hpq,
     show r, from H Hp Hq)
    (assume H : p ∧ q → r,
     assume Hp : p,
     assume Hq : q,
     show r, from H (and.intro Hp Hq))

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
  iff.intro
    (assume H : (p ∨ q) → r,
     have Hpr : p → r, from (assume Hp, H (or.inl Hp)),
     have Hqr : q → r, from (assume Hq, H (or.inr Hq)),
     show (p → r) ∧ (q → r), from and.intro Hpr Hqr)
    (assume H : (p → r) ∧ (q → r),
     show (p ∨ q) → r, from
       (assume Hpq : p ∨ q,
        or.elim Hpq
          (and.left H)
          (and.right H)))

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  iff.intro
    (assume H : ¬(p ∨ q),
     have Hnp : ¬p, from (assume Hp, H (or.inl Hp)),
     have Hnq : ¬q, from (assume Hq, H (or.inr Hq)),
     show ¬p ∧ ¬q, from and.intro Hnp Hnq)
    (assume H : ¬p ∧ ¬q,
     have Hnp : ¬p, from and.left H,
     have Hnq : ¬q, from and.right H,
     show ¬(p ∨ q), from
       assume Hpq : p ∨ q,
       show false, from
         or.elim Hpq Hnp Hnq)

example : ¬p ∨ ¬q → ¬(p ∧ q) :=
  assume H : ¬p ∨ ¬q,
  or.elim H
    (assume Hnp : ¬p,
     show ¬(p ∧ q), from
       assume Hpq : p ∧ q,
       show false, from Hnp (and.left Hpq))
    (assume Hnq : ¬q,
     show ¬(p ∧ q), from
       assume Hpq : p ∧ q,
       show false, from Hnq (and.right Hpq))

example : ¬(p ∧ ¬p) :=
  not.intro
    (assume H : p ∧ ¬p,
     have Hp : p, from and.left H,
     have Hnp : ¬p, from and.right H,
     show false, from Hnp Hp)

example : p ∧ ¬q → ¬(p → q) :=
  (assume H : p ∧ ¬q,
   have Hp : p, from and.left H,
   have Hnq : ¬q, from and.right H,
   show ¬(p → q), from
     (assume Hpq : p → q,
      show false, from Hnq (Hpq Hp)))

example : ¬p → (p → q) :=
  assume Hnp : ¬p,
  assume Hp : p,
  have Hf : false, from Hnp Hp,
  show q, from false.elim Hf

example : (¬p ∨ q) → (p → q) :=
  (assume Hnpq : ¬p ∨ q,
   assume Hp : p,
   or.elim Hnpq
     (assume Hnp : ¬p,
      show q, from false.elim (Hnp Hp))
     (assume Hq : q, Hq)) 

example : p ∨ false ↔ p :=
  iff.intro
    (assume H : p ∨ false,
     or.elim H
       (assume Hp : p, Hp)
       (assume Hf : false, false.elim Hf))
    (assume Hp : p, or.inl Hp)

example : p ∧ false ↔ false :=
  iff.intro
    (assume H : p ∧ false,
     show false, from and.right H)
    (assume H : false,
     show p ∧ false, from false.elim H)

example : ¬(p ↔ ¬p) :=
  iff.elim
    (assume Hpnp : p → ¬p,
     assume Hnpp : ¬p → p,
     have Hp : p, from
       Hnpp (assume Hp : p,
             have Hnp : ¬p, from Hpnp Hp,
             show false, from Hnp Hp),
     show false, from (Hpnp Hp) Hp)

example : (p → q) → (¬q → ¬p) :=
  assume Hpq : p → q,
  show ¬q → ¬p, from
    (assume Hnq : ¬q,
     show ¬p, from
       (assume Hp : p,
        show false, from Hnq (Hpq Hp)))

-- these require classical reasoning


open classical


example : (p → r ∨ s) → ((p → r) ∨ (p → s)) :=
  assume H : p → r ∨ s,
  sorry

example : ¬(p ∧ q) → ¬p ∨ ¬q :=
  assume Hnpq : ¬(p ∧ q),
  sorry

example : ¬(p → q) → p ∧ ¬q :=
  assume H : ¬(p → q),
  sorry

example : (p → q) → (¬p ∨ q) :=
  assume Hpq : p → q,
  show ¬p ∨ q, from
    by_cases
      (assume Hp : p, or.inr (Hpq Hp))
      (assume Hnp : ¬p, or.inl Hnp)

example : (¬q → ¬p) → (p → q) :=
  assume Hnqnp : ¬q → ¬p,
  assume Hp : p,
  by_contradiction
    (assume Hnq : ¬q,
     show false, from (Hnqnp Hnq) Hp)

example : p ∨ ¬p :=
  by_cases
    (assume H : p, or.inl H)
    (assume H : ¬p, or.inr H)

example : (((p → q) → p) → p) :=
  --assume H : (p → q) → p,
  sorry
