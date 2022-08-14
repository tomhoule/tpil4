-- Exercises from Theorem Proving in Lean 4

-- ===============================
--   3. Propositions and Proofs
-- ===============================

namespace chap3noclassic

  -- No tactics, working with the tools introduced so far for now.

  variable (p q r : Prop)

  -- commutativity of ∧ and ∨
  example : p ∧ q ↔ q ∧ p := Iff.intro
    (λ (And.intro hp hq) => And.intro hq hp)
    (λ (And.intro hq hp) => And.intro hp hq)


  example : p ∨ q ↔ q ∨ p :=
    let swap := λ {pr1 pr2 : Prop} (h : pr1 ∨ pr2) => Or.elim h Or.inr Or.inl;
    Iff.intro swap swap

  -- associativity of ∧ and ∨
  example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := Iff.intro
    (λ (And.intro (And.intro hp hq) hr) => ⟨hp, ⟨hq, hr⟩⟩)
    (λ (And.intro hp (And.intro hq hr)) => ⟨⟨hp, hq⟩, hr⟩)

  example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := Iff.intro
    (λ h => Or.elim h
      (λ h₁ => Or.elim h₁ Or.inl (λ hq => Or.inr (Or.inl hq)))
      (λ hr => Or.inr (Or.inr hr)))
    (λ h => Or.elim h (λ hp => Or.inl (Or.inl hp)) (λ hqr => Or.elim hqr (λ hq => Or.inl (Or.inr hq)) Or.inr))

  -- distributivity
  example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := Iff.intro
    (λ (And.intro hp hqr) => Or.elim hqr (λ hq => Or.inl ⟨hp, hq⟩) (λ hr => Or.inr ⟨hp, hr⟩))
    (λ h => Or.elim h
      (λ (And.intro hp hq) => ⟨hp, Or.inl hq⟩)
      (λ (And.intro hp hr) => ⟨hp, Or.inr hr⟩))

  example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := Iff.intro
    (λ h => Or.elim h
      (λ hp => And.intro (Or.inl hp) (Or.inl hp))
      (λ hqr => And.intro (Or.inr hqr.left) (Or.inr hqr.right)))
    (λ (And.intro hpq hpr) => Or.elim hpq Or.inl (λ hq => Or.elim hpr Or.inl (λ hr => Or.inr ⟨hq, hr⟩)))

  -- other properties
  example : (p → (q → r)) ↔ (p ∧ q → r) := Iff.intro
    (λ hptoqtor => λ (And.intro hp hq) => hptoqtor hp hq)
    (λ h hp hq => h ⟨hp, hq⟩)

  example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := Iff.intro
    (λ h => And.intro (λ hp => h (Or.inl hp)) (λ hq => h (Or.inr hq)))
    (λ (And.intro h1 h2) hpq => Or.elim hpq h1 h2)

  example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := Iff.intro
    (λ h => And.intro (λ hp => h (Or.inl hp)) (λ hq => h (Or.inr hq)))
    (λ (And.intro hnp hnq) hpq => Or.elim hpq (λ hp => hnp hp) (λ hq => hnq hq))

  example : ¬p ∨ ¬q → ¬(p ∧ q) := 
    λ hnpq (And.intro hp hq) =>
    Or.elim hnpq (λ hnp => hnp hp) (λ hnq => hnq hq)

  example : ¬(p ∧ ¬p) := λ (And.intro hp hnp) => hnp hp

  example : p ∧ ¬q → ¬(p → q) := λ (And.intro hp hnq) hptoq => hnq (hptoq hp)

  theorem t2 : ¬p → (p → q) := λ hnp hp => False.elim (hnp hp)

  example : (¬p ∨ q) → (p → q) := λ h hp => Or.elim h (λ hnp => False.elim $ hnp hp) id

  example : p ∨ False ↔ p := Iff.intro (λ h => Or.elim h id False.elim) Or.inl

  example : p ∧ False ↔ False := Iff.intro (λ (And.intro _ contra) => False.elim contra) False.elim

  example : (p → q) → (¬q → ¬p) := λ hpq hnq hp => hnq (hpq hp)

  theorem noNegIff : ¬(p ↔ ¬p) := λ h => 
    let l := Iff.mp h;
    let r := Iff.mpr h;
    let hnp: ¬p := λ hp => (l hp) hp;
    hnp $ r hnp

end chap3noclassic

namespace chap3classic

  open Classical

  variable (p q r : Prop)

  example : (p → q ∨ r) → ((p → q) ∨ (p → r)) := λ h => @byCases p _
    (λ hp => Or.elim (h hp) (λ hq => Or.inl (λ _ => hq)) (λ hr => Or.inr (λ _ => hr)))
    (λ hnp => Or.inl $ λ hp => False.elim $ hnp hp)

  example : ¬(p ∧ q) → ¬p ∨ ¬q := λ hn => @byCases p _
    (λ hp => @byCases q _ (λ hq => False.elim $ hn ⟨hp, hq⟩) Or.inr)
    Or.inl

  theorem t1 : ¬(p → q) → p ∧ ¬q := λ h => @byCases p _
    (λ hp => ⟨hp, λ hq => h $ λ _ => hq⟩ )
    (λ hnp => False.elim $ h $ chap3noclassic.t2 _ _ hnp)

  example : (p → q) → (¬p ∨ q) := λ hpq => @byCases p _ (λ hp => Or.inr $ hpq hp) Or.inl

  example : (¬q → ¬p) → (p → q) := λ h hp => byContradiction (λ hnq => ((h hnq) hp))

  example : p ∨ ¬p := em p

  example : (((p → q) → p) → p) := λ h => @byCases (p → q) _
    (λ hpq => h hpq)
    (λ hnpq => (t1 p q hnpq).left)

end chap3classic


-- ===============================
--   4. Quantifiers and Equality
-- ===============================

namespace chap4pt1

variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := Iff.intro
  (λ h => ⟨ λ hx => (h hx).left, λ hx => (h hx).right ⟩)
  (λ ⟨hpx, hqx⟩ hx => ⟨hpx hx, hqx hx⟩)

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := λ h1 h2 a => h1 a $ h2 a

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := λ h hx => match h with
| (Or.inl hpx) => Or.inl $ hpx hx
| (Or.inr hqx) => Or.inr $ hqx hx

end chap4pt1

namespace chap4pt2

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : α → ((∀ _x : α, r) ↔ r) := λ a => Iff.intro 
  (λ ator => ator a)
  (λ dis _ => dis)

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := Iff.intro
  (λ h => @Classical.byCases r _
    Or.inr
    (λ hnr =>
      suffices ∀ (x : α), p x from Or.inl this
      λ hx => Or.elim (h hx) id (λ hr => False.elim $ hnr hr)))
  (λ h hx => Or.elim h (λ hl => Or.inl $ hl hx) Or.inr)

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := Iff.intro
  (λ h hr hx => h hx hr)
  (λ h hx hr => h hr hx)

end chap4pt2

namespace chap4pt3

variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False := chap3noclassic.noNegIff (shaves barber barber) (h barber)

end chap4pt3

namespace chap4pt4

def even (n : Nat) : Prop := ∃ (m : Nat), n = 2 * m

def prime (n : Nat) : Prop := n > 1 ∧ ¬∃ m k, m < n ∧ k < n ∧ n = m * k

def infinitely_many_primes : Prop := ∀ (n : Nat), ∃ m, m > n ∧ prime m

def Fermat_prime (n : Nat) : Prop := ∃ m, n = 2^2^m + 1

def infinitely_many_Fermat_primes : Prop := ∀ (n : Nat), ∃ m, m > n ∧ Fermat_prime m

def odd (n : Nat) : Prop := ¬even n

def goldbach_conjecture : Prop := ∀ (n : Nat), n > 2 → even n → ∃ a b, prime a ∧ prime b ∧ a + b = n

def Goldbach's_weak_conjecture : Prop := ∀ n, n > 5 → odd n → ∃ a b c, prime a ∧ prime b ∧ prime c ∧ a + b + c = n

def Fermat's_last_theorem : Prop := ¬∃ (a b c n : Nat), n > 2 ∧ a^n + b^n = c^n

end chap4pt4

namespace chap4pt5

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ _x : α, r) → r := λ ⟨_, hr⟩ => hr

example (a : α) : r → (∃ _x : α, r) := λ hr => ⟨a, hr⟩ 

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := Iff.intro
  (λ ⟨hx, ⟨hpx, hr⟩⟩ => ⟨⟨hx, hpx⟩, hr⟩ )
  (λ ⟨⟨hx, hpx⟩, hr⟩ => ⟨hx, ⟨hpx, hr⟩⟩)

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := Iff.intro
  (λ ⟨hx, h⟩ => Or.elim h (λ hpx => Or.inl ⟨hx, hpx⟩) (λ hqx => Or.inr ⟨hx, hqx⟩))
  (λ h => Or.elim h (λ ⟨hx, hpx⟩ => ⟨hx, Or.inl hpx⟩) (λ ⟨hx, hqx⟩ => ⟨hx, Or.inr hqx⟩))

---

open Classical

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := Iff.intro
  (λ h ⟨hx, hnpx⟩ => hnpx $ h hx)
  (λ h hx => byContradiction $ λ hnpx => h ⟨hx, hnpx⟩)

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := Iff.intro
  (λ ⟨hx, hpx⟩ hcontra => hcontra hx hpx)
  (λ h => byContradiction $ λ hne => 
    suffices ∀ x, ¬ p x from h this
    λ a hpa => hne ⟨a, hpa⟩)

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := Iff.intro
  (λ h hx hpx => h ⟨hx, hpx⟩ )
  (λ h ⟨hx, hpx⟩  => (h hx) hpx)

theorem t2 : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := Iff.intro
  (λ h => byContradiction $ λ hne => h $ λ x => byContradiction $ λ hnpx => hne ⟨x, hnpx⟩)
  (λ ⟨hx, hnpx⟩ h => hnpx (h hx))

---

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := Iff.intro
  (λ h ⟨hx, hpx⟩  => h hx hpx)
  (λ h hx hpx => h ⟨hx, hpx⟩)

example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := Iff.intro
  (λ ⟨hx, hpxtor⟩ h => hpxtor $ h hx)
  (λ h => @byCases (∀ x, p x) _
    (λ h1 => ⟨a, λ _ => h h1⟩)
    (λ hnotallx => byContradiction $ λ hne =>
      let ⟨hx, hnpx⟩ : ∃ x, ¬ p x := (t2 _ _).mp hnotallx
      hne ⟨hx, λ hpx => False.elim $ hnpx hpx⟩))

example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := Iff.intro
  (λ ⟨hx, hrpx⟩ hr => ⟨hx, hrpx hr⟩ )
  (λ h => @byCases r _
    (λ hr => let ⟨x, px⟩ := h hr; ⟨x, λ _ => px⟩)
    (λ hnr => ⟨a, λ hr => False.elim $ hnr hr⟩))

end chap4pt5

namespace chap5pt2

example (p q r : Prop) (hp : p) : (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) := by
  repeat (first | assumption | (apply Or.inl ; assumption) | apply Or.inr | constructor)

end chap5pt2

namespace chap7pt2

open List

variable {α : Type}

def length : List α → Nat := λ xs =>
match xs with
| nil => 0 
| cons _ xs => Nat.succ $ length xs

theorem length_nil : length (@nil α) = 0 := rfl

theorem length_cons {x : α} {xs : List α} : length (x :: xs) = Nat.succ (length xs) := rfl

theorem length_append (s t : List α) : length (s ++ t) = length s + length t := by
  induction s with
  | nil => simp only [nil_append, length_nil, Nat.zero_add]
  | cons x xs ih => rw [length_cons, Nat.succ_add, cons_append, length_cons, ih]

theorem length_reverse {xs : List α} : length (reverse xs) = length xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => rw [reverse_cons, length_append, length_cons, length_nil, length_cons, ih]

theorem double_reverse {xs : List α} : reverse (reverse xs) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => rw [reverse_cons, reverse_append, ih]; rfl

end chap7pt2

namespace chap7pt3

inductive Expr : Type where
| const : Nat → Expr
| var : Nat → Expr
| plus : Expr → Expr → Expr
| times : Expr → Expr → Expr

open Expr

def eval : Expr → (Nat → Nat) → Nat := λ expr env =>
  match expr with
  | const n => n
  | var n => env n
  | plus s t => (eval s env) + (eval t env)
  | times s t => (eval s env) * (eval t env)

end chap7pt3
