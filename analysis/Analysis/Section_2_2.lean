import Mathlib.Tactic
import Analysis.Section_2_1

/-!
# Analysis I, Section 2.2

This file is a translation of Section 2.2 of Analysis I to Lean 4.
All numbering refers to the original text.

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Definition of addition and order for the "Chapter 2" natural numbers, `Chapter2.Nat`
- Establishment of basic properties of addition and order

Note: at the end of this chapter, the `Chapter2.Nat` class will be deprecated in favor of the
standard Mathlib class `_root_.Nat`, or `ℕ`.  However, we will develop the properties of
`Chapter2.Nat` "by hand" for pedagogical purposes.
-/

namespace Chapter2

/-- Definition 2.2.1. (Addition of natural numbers).
    Compare with Mathlib's `Nat.add` -/
abbrev Nat.add (n m : Nat) : Nat := Nat.recurse (fun _ sum ↦ sum++) m n

/-- This instance allows for the `+` notation to be used for natural number addition. -/
instance Nat.instAdd : Add Nat where
  add := add

/-- Compare with Mathlib's `Nat.zero_add`-/
@[simp]
theorem Nat.zero_add (m: Nat) : 0 + m = m := recurse_zero (fun _ sum ↦ sum++) _

/-- Compare with Mathlib's `Nat.succ_add` -/
theorem Nat.succ_add (n m: Nat) : n++ + m = (n+m)++ := by rfl

/-- Compare with Mathlib's `Nat.one_add` -/
theorem Nat.one_add (m:Nat) : 1 + m = m++ := by
  rw [show 1 = 0++ from rfl, succ_add, zero_add]

theorem Nat.two_add (m:Nat) : 2 + m = (m++)++ := by
  rw [show 2 = 1++ from rfl, succ_add, one_add]

example : (2:Nat) + 3 = 5 := by
  rw [Nat.two_add, show 3++=4 from rfl, show 4++=5 from rfl]

-- sum of two natural numbers is again a natural number
#check (fun (n m:Nat) ↦ n + m)

/-- Lemma 2.2.2 (n + 0 = n). Compare with Mathlib's `Nat.add_zero` -/
@[simp]
lemma Nat.add_zero (n:Nat) : n + 0 = n := by
  -- this proof is written to follow the structure of the original text.
  revert n; apply induction
  . exact zero_add 0
  intro n ih
  calc
    (n++) + 0 = (n + 0)++ := by rfl
    _ = n++ := by rw [ih]

/-- Lemma 2.2.3 (n+(m++) = (n+m)++). Compare with Mathlib's `Nat.add_succ` -/
lemma Nat.add_succ (n m:Nat) : n + (m++) = (n + m)++ := by
  -- this proof is written to follow the structure of the original text.
  revert n; apply induction
  . rw [zero_add, zero_add]
  intro n ih
  rw [succ_add, ih]
  rw [succ_add]


/-- n++ = n + 1 (Why?). Compare with Mathlib's `Nat.succ_eq_add_one` -/
theorem Nat.succ_eq_add_one (n:Nat) : n++ = n + 1 := by
  revert n; apply induction
  · rfl
  intro n ih
  rw [succ_add, ih]

/-- Proposition 2.2.4 (Addition is commutative). Compare with Mathlib's `Nat.add_comm` -/
theorem Nat.add_comm (n m:Nat) : n + m = m + n := by
  -- this proof is written to follow the structure of the original text.
  revert n; apply induction
  . rw [zero_add, add_zero]
  intro n ih
  rw [succ_add]
  rw [add_succ, ih]

/-- Proposition 2.2.5 (Addition is associative) / Exercise 2.2.1
    Compare with Mathlib's `Nat.add_assoc` -/
theorem Nat.add_assoc (a b c:Nat) : (a + b) + c = a + (b + c) := by
  revert c; apply induction
  · rw [add_zero, add_zero]
  intro n ih
  rw [add_succ, add_succ, add_succ, ih]

/-- Proposition 2.2.6 (Cancellation law)
    Compare with Mathlib's `Nat.add_left_cancel` -/
theorem Nat.add_left_cancel (a b c:Nat) (habc: a + b = a + c) : b = c := by
  -- this proof is written to follow the structure of the original text.
  revert a; apply induction
  . intro hbc
    rwa [zero_add, zero_add] at hbc
  intro a ih
  intro hbc
  rw [succ_add, succ_add] at hbc
  replace hbc := succ_cancel hbc
  exact ih hbc


/-- (Not from textbook) Nat can be given the structure of a commutative additive monoid. -/
instance Nat.addCommMonoid : AddCommMonoid Nat where
  add_assoc := add_assoc
  add_comm := add_comm
  zero_add := zero_add
  add_zero := add_zero
  nsmul := nsmulRec

/-- Definition 2.2.7 (Positive natural numbers).-/
def Nat.isPos (n:Nat) : Prop := n ≠ 0

theorem Nat.isPos_iff (n:Nat) : n.isPos ↔ n ≠ 0 := by rfl

/-- Proposition 2.2.8 (positive plus natural number is positive).
    Compare with Mathlib's `Nat.add_pos_left` -/
theorem Nat.add_pos_left {a:Nat} (b:Nat) (ha: a.isPos) : (a + b).isPos := by
  -- this proof is written to follow the structure of the original text.
  revert b; apply induction
  . rwa [add_zero]
  intro b hab
  rw [add_succ]
  have : (a+b)++ ≠ 0 := succ_ne _
  exact this

/-- Compare with Mathlib's `Nat.add_pos_right` -/
theorem Nat.add_pos_right {a:Nat} (b:Nat) (ha: a.isPos) : (b + a).isPos := by
  rw [add_comm]
  exact add_pos_left _ ha

/-- Corollary 2.2.9 (if sum vanishes, then summands vanish).
    Compare with Mathlib's `Nat.add_eq_zero` -/
theorem Nat.add_eq_zero (a b:Nat) (hab: a + b = 0) : a = 0 ∧ b = 0 := by
  -- this proof is written to follow the structure of the original text.
  by_contra h
  simp only [not_and_or, ←ne_eq] at h
  rcases h with ha | hb
  . rw [←isPos_iff] at ha
    have : (a + b).isPos := add_pos_left _ ha
    contradiction
  rw [←isPos_iff] at hb
  have : (a + b).isPos := add_pos_right _ hb
  contradiction

/-
The following API for ∃! may be useful for the next problem.  Also, the `obtain` tactic is useful
for extracting witnesses from existential statements; for instance, `obtain ⟨ x, hx ⟩ := h`
extracts a witness `x` and a proof `hx : P x` of the property from a hypothesis `h : ∃ x, P x`.
-/

#check existsUnique_of_exists_of_unique
#check ExistsUnique.exists
#check ExistsUnique.unique

/-- Lemma 2.2.10 (unique predecessor) / Exercise 2.2.2 -/
lemma Nat.uniq_succ_eq (a:Nat) (ha: a.isPos) : ∃! b, b++ = a := by
  revert a; apply induction
  · tauto
  intro a _ _
  apply existsUnique_of_exists_of_unique
  · use a
  intro _ _ hx hy
  rw [←hy] at hx
  exact succ_cancel hx

/-- Definition 2.2.11 (Ordering of the natural numbers)
    This defines the `≤` operation on the natural numbers. -/
instance Nat.instLE : LE Nat where
  le n m := ∃ a:Nat, m = n + a

/-- Definition 2.2.11 (Ordering of the natural numbers)
    This defines the `<` notation on the natural numbers. -/
instance Nat.instLT : LT Nat where
  lt n m := n ≤ m ∧ n ≠ m

lemma Nat.le_iff (n m:Nat) : n ≤ m ↔ ∃ a:Nat, m = n + a := by rfl

lemma Nat.lt_iff (n m:Nat) : n < m ↔ (∃ a:Nat, m = n + a) ∧ n ≠ m := by rfl

/-- Compare with Mathlib's `ge_iff_le` -/
lemma Nat.ge_iff_le (n m:Nat) : n ≥ m ↔ m ≤ n := by rfl

/-- Compare with Mathlib's `gt_iff_lt` -/
lemma Nat.gt_iff_lt (n m:Nat) : n > m ↔ m < n := by rfl

/-- Compare with Mathlib's `Nat.le_of_lt` -/
lemma Nat.le_of_lt {n m:Nat} (hnm: n < m) : n ≤ m := hnm.1

/-- Compare with Mathlib's `Nat.le_iff_lt_or_eq` -/
lemma Nat.le_iff_lt_or_eq (n m:Nat) : n ≤ m ↔ n < m ∨ n = m := by
  rw [Nat.le_iff, Nat.lt_iff]
  by_cases h : n = m
  . simp [h]
    use 0
    rw [add_zero]
  simp [h]

example : (8:Nat) > 5 := by
  rw [Nat.gt_iff_lt, Nat.lt_iff]
  constructor
  . have : (8:Nat) = 5 + 3 := by rfl
    rw [this]
    use 3
  decide

/-- Compare with Mathlib's `Nat.lt_succ_self`-/
theorem Nat.succ_gt_self (n:Nat) : n++ > n := by
  rw [Nat.gt_iff_lt, Nat.lt_iff]
  constructor
  · use 1
    apply succ_eq_add_one
  revert n; apply induction
  · decide
  intro n hn
  apply succ_ne_succ
  apply hn

/-- Proposition 2.2.12 (Basic properties of order for natural numbers) / Exercise 2.2.3

(a) (Order is reflexive). Compare with Mathlib's `Nat.le_refl`-/
theorem Nat.ge_refl (a:Nat) : a ≥ a := by
  rw [Nat.ge_iff_le, Nat.le_iff]
  use 0
  rw [Nat.add_zero]

/-- (b) (Order is transitive).  The `obtain` tactic will be useful here.
    Compare with Mathlib's `Nat.le_trans` -/
theorem Nat.ge_trans {a b c:Nat} (hab: a ≥ b) (hbc: b ≥ c) : a ≥ c := by
  obtain ⟨d, rfl⟩ := hab
  obtain ⟨e, rfl⟩ := hbc
  use d + e
  rw [add_assoc, add_comm e]

/-- (c) (Order is anti-symmetric). Compare with Mathlib's `Nat.le_antisymm`  -/
theorem Nat.ge_antisymm {a b:Nat} (hab: a ≥ b) (hba: b ≥ a) : a = b := by
  obtain ⟨d, rfl⟩ := hab
  obtain ⟨e, he⟩ := hba
  symm at he
  have : b + (d + e) = b + 0 := by
    nth_rw 1 [add_zero]
    rw [←add_assoc]
    exact he
  have hde: (d + e) = 0 := by exact add_left_cancel _ _ _ this
  have hd: d = 0 ∧ e = 0 := by exact add_eq_zero _ _ hde
  rw [hd.left, add_zero]

/-- (d) (Addition preserves order).  Compare with Mathlib's `Nat.add_le_add_right`  -/
theorem Nat.add_ge_add_right (a b c:Nat) : a ≥ b ↔ a + c ≥ b + c := by
  constructor
  · rintro ⟨d, rfl⟩
    use d
    rw [add_assoc, add_assoc, add_comm d]
  rintro ⟨e, he⟩
  use e
  rw [add_comm, add_comm b, add_assoc] at he
  apply add_left_cancel _ _ _ he

/-- (d) (Addition preserves order).  Compare with Mathlib's `Nat.add_le_add_left`  -/
theorem Nat.add_ge_add_left (a b c:Nat) : a ≥ b ↔ c + a ≥ c + b := by
  simp only [add_comm]
  exact add_ge_add_right _ _ _

/-- (d) (Addition preserves order).  Compare with Mathlib's `Nat.add_le_add_right`  -/
theorem Nat.add_le_add_right (a b c:Nat) : a ≤ b ↔ a + c ≤ b + c := add_ge_add_right _ _ _

/-- (d) (Addition preserves order).  Compare with Mathlib's `Nat.add_le_add_left`  -/
theorem Nat.add_le_add_left (a b c:Nat) : a ≤ b ↔ c + a ≤ c + b := add_ge_add_left _ _ _

/-- (e) a < b iff a++ ≤ b.  Compare with Mathlib's `Nat.succ_le_iff` -/
theorem Nat.lt_iff_succ_le (a b:Nat) : a < b ↔ a++ ≤ b := by
  constructor
  · rintro ⟨⟨c, hc⟩, ha⟩
    have cpos : c.isPos := by
      rw [isPos_iff]
      contrapose! ha
      rw [hc, ha, add_zero]
    obtain ⟨d, ⟨hd⟩⟩ := uniq_succ_eq c cpos
    use d
    rw [succ_eq_add_one, add_assoc, add_comm 1]
    rw [←succ_eq_add_one, hc, hd]
  rintro ⟨c, hc⟩
  rw [succ_eq_add_one, add_assoc, add_comm 1] at hc
  constructor
  · use c + 1
  rw [hc, ←succ_eq_add_one]
  intro h
  nth_rewrite 1 [←add_zero a] at h
  apply add_left_cancel at h
  tauto

/-- (f) a < b if and only if b = a + d for positive d. -/
theorem Nat.lt_iff_add_pos (a b:Nat) : a < b ↔ ∃ d:Nat, d.isPos ∧ b = a + d := by
  constructor
  · rintro ⟨⟨d, hd⟩, hab⟩
    have : d.isPos := by
      rw [isPos_iff]
      contrapose! hab
      rw [hab, add_zero] at hd
      rw [hd]
    use d
  rintro ⟨c, hc, hb⟩
  constructor
  · use c
  have : a ≠ b := by
    rw [isPos_iff] at hc
    contrapose! hc
    rw [hc] at hb
    nth_rewrite 1 [←add_zero b] at hb
    apply add_left_cancel at hb
    symm
    exact hb
  exact this

/-- If a < b then a ̸= b,-/
theorem Nat.ne_of_lt (a b:Nat) : a < b → a ≠ b := by
  intro h; exact h.2

/-- if a > b then a ̸= b. -/
theorem Nat.ne_of_gt (a b:Nat) : a > b → a ≠ b := by
  intro h; exact h.2.symm

/-- If a > b and a < b then contradiction -/
theorem Nat.not_lt_of_gt (a b:Nat) : a < b ∧ a > b → False := by
  intro h
  have := (ge_antisymm (Nat.le_of_lt h.1) (Nat.le_of_lt h.2)).symm
  have := ne_of_lt _ _ h.1
  contradiction


/-- Proposition 2.2.13 (Trichotomy of order for natural numbers) / Exercise 2.2.4
    Compare with Mathlib's `trichotomous` -/
theorem Nat.trichotomous (a b:Nat) : a < b ∨ a = b ∨ a > b := by
  -- this proof is written to follow the structure of the original text.
  revert a; apply induction
  . have why : 0 ≤ b := by tauto
    replace why := (Nat.le_iff_lt_or_eq _ _).mp why
    tauto
  intro a ih
  rcases ih with case1 | case2 | case3
  . rw [lt_iff_succ_le] at case1
    rw [Nat.le_iff_lt_or_eq] at case1
    tauto
  . have why : a++ > b := by
      rw [case2]
      apply succ_gt_self
    tauto
  have why : a++ > b := by
    have ⟨⟨c, hc⟩, anb⟩ := case3
    constructor
    · use c++;
      rw [add_succ, hc]
    contrapose! anb
    apply ge_antisymm
    · rw [succ_eq_add_one] at anb
      use 1
    exact le_of_lt case3
  tauto

/--
  (Not from textbook) Establish the decidability of this order computably.  The portion of the
  proof involving decidability has been provided; the remaining sorries involve claims about the
  natural numbers.  One could also have established this result by the `classical` tactic
  followed by `exact Classical.decRel _`, but this would make this definition (as well as some
  instances below) noncomputable.

  Compare with Mathlib's `Nat.decLe`
-/
def Nat.decLe : (a b : Nat) → Decidable (a ≤ b)
  | 0, b => by
    apply isTrue
    tauto
  | a++, b => by
    cases decLe a b with
    | isTrue h =>
      cases decEq a b with
      | isTrue h =>
        apply isFalse
        rw [h]
        rw [le_iff_lt_or_eq, not_or]
        have := succ_gt_self b
        constructor
        · intro h
          apply not_lt_of_gt _ _ ⟨this, h⟩
        apply ne_of_gt
        exact this
      | isFalse h =>
        apply isTrue
        rw [←lt_iff_succ_le]
        constructor
        · assumption
        exact h
    | isFalse h =>
      apply isFalse
      contrapose! h
      apply ge_trans h
      apply le_of_lt
      apply succ_gt_self

instance Nat.decidableRel : DecidableRel (· ≤ · : Nat → Nat → Prop) := Nat.decLe


/-- (Not from textbook) Nat has the structure of a linear ordering. -/
instance Nat.linearOrder : LinearOrder Nat where
  le_refl := ge_refl
  le_trans a b c hab hbc := ge_trans hbc hab
  lt_iff_le_not_le := by
    intro a b
    constructor
    · intro hab
      constructor
      · apply le_of_lt hab
      intro hba
      apply not_lt_of_gt
      have : b ≠ a := by exact ne_of_gt _ _ hab
      tauto
    rintro ⟨hab, hba⟩
    rw [le_iff_lt_or_eq, not_or] at hba
    have : b ≠ a := hba.right
    tauto
  le_antisymm a b hab hba := ge_antisymm hba hab
  le_total := by
    intro a b
    rcases trichotomous a b with case1 | case2 | case3
    · left
      exact le_of_lt case1
    · left
      rw [le_iff_lt_or_eq]
      right
      exact case2
    right
    exact le_of_lt case3

  toDecidableLE := decidableRel

/-- (Not from textbook) Nat has the structure of an ordered monoid. -/
instance Nat.isOrderedAddMonoid : IsOrderedAddMonoid Nat where
  add_le_add_left := by
    intro a b hab c
    exact (add_le_add_left a b c).mp hab

lemma le_of_lt_succ : ∀ m n, m < n++ → m ≤ n := by
  rintro m n ⟨⟨a, ha⟩, ha'⟩
  by_cases haz : a = 0
  · rw [haz, add_zero] at ha
    symm at ha
    contradiction
  change a.isPos at haz
  have ⟨b, hb⟩ := Nat.uniq_succ_eq a haz
  use b
  apply Nat.succ_cancel
  rw [ha, ←Nat.add_succ, hb.1]

/-- Proposition 2.2.14 (Strong principle of induction) / Exercise 2.2.5
    Compare with Mathlib's `Nat.strong_induction_on`
-/
theorem Nat.strong_induction {m₀:Nat} {P: Nat → Prop}
  (hind: ∀ m, m ≥ m₀ → (∀ m', m₀ ≤ m' ∧ m' < m → P m') → P m) :
    ∀ m, m ≥ m₀ → P m := by
  let Q n := ∀ m', m₀ ≤ m' ∧ m' < n → P m'
  change ∀ m ≥ m₀, Q m → P m at hind
  have hQ : ∀ n, Q n := by
    apply induction
    · intro m ⟨hm₀, h1, h2⟩
      have h3 : m ≥ 0 := by tauto
      have := ge_antisymm h3 h1
      contradiction
    rintro n ih m ⟨hm₀, hm⟩
    by_cases hmn : m = n
    · rw [hmn]
      rw [hmn] at hm₀
      exact hind n hm₀ ih
    have h : ∀ m', m₀ ≤ m' ∧ m' < m → P m' := by
      rintro m' ⟨hm₀, hm'⟩
      apply ih m'
      use hm₀
      apply gt_of_ge_of_gt _ hm'
      apply le_of_lt_succ _ _ hm
    exact hind m hm₀ h
  intro m hm₀
  exact hind m hm₀ (hQ m)

/-- Exercise 2.2.6 (backwards induction)
    Compare with Mathlib's `Nat.decreasingInduction` -/
theorem Nat.backwards_induction {n:Nat} {P: Nat → Prop}
  (hind: ∀ m, P (m++) → P m) (hn: P n) :
    ∀ m, m ≤ n → P m := by
  revert n; apply induction
  · intro h0 m hm
    by_cases hmz : m = 0
    · rwa [hmz]
    have hm' : m ≥ 0 := by tauto
    have := ge_antisymm hm' hm
    contradiction
  intro n ih hns m hm
  by_cases hms : m = n++;
    · rwa [hms]
  apply ih (hind n hns)
  apply le_of_lt_succ
  use hm

/-- Exercise 2.2.7 (induction from a starting point)
    Compare with Mathlib's `Nat.le_induction` -/
theorem Nat.induction_from {n:Nat} {P: Nat → Prop} (hind: ∀ m, P m → P (m++)) :
    P n → ∀ m, m ≥ n → P m := by
  intro hbase
  have h : ∀ a, P (n + a) := by
    apply induction
    · rwa [add_zero]
    intro a hna
    rw [add_succ]
    apply hind _ hna
  rintro _ ⟨_, rfl⟩
  apply h



end Chapter2
