import Mathlib.Tactic
import Mathlib.Algebra.Group.MinimalAxioms

/-!
# Analysis I, Section 4.1: The integers

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Definition of the "Section 4.1" integers, `Section_4_1.Int`, as formal differences `a —— b` of
  natural numbers `a b:ℕ`, up to equivalence.  (This is a quotient of a scaffolding type
  `Section_4_1.PreInt`, which consists of formal differences without any equivalence imposed.)

- ring operations and order these integers, as well as an embedding of ℕ.

- Equivalence with the Mathlib integers `_root_.Int` (or `ℤ`), which we will use going forward.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Section_4_1

structure PreInt where
  minuend : ℕ
  subtrahend : ℕ

/-- Definition 4.1.1 -/
instance PreInt.instSetoid : Setoid PreInt where
  r a b := a.minuend + b.subtrahend = b.minuend + a.subtrahend
  iseqv := {
    refl := by intro; rfl
    symm := by intro; omega
    trans := by
      -- This proof is written to follow the structure of the original text.
      intro ⟨ a,b ⟩ ⟨ c,d ⟩ ⟨ e,f ⟩ h1 h2; simp_all
      have h3 := congrArg₂ (· + ·) h1 h2; simp at h3
      have : (a + f) + (c + d) = (e + b) + (c + d) := calc
        (a + f) + (c + d) = a + d + (c + f) := by abel
        _ = c + b + (e + d) := h3
        _ = (e + b) + (c + d) := by abel
      exact Nat.add_right_cancel this
    }

@[simp]
theorem PreInt.eq (a b c d:ℕ) : (⟨ a,b ⟩: PreInt) ≈ ⟨ c,d ⟩ ↔ a + d = c + b := by rfl

abbrev Int := Quotient PreInt.instSetoid

abbrev Int.formalDiff (a b:ℕ)  : Int := Quotient.mk PreInt.instSetoid ⟨ a,b ⟩

infix:100 " —— " => Int.formalDiff

/-- Definition 4.1.1 (Integers) -/
theorem Int.eq (a b c d:ℕ): a —— b = c —— d ↔ a + d = c + b :=
  ⟨ Quotient.exact, by intro h; exact Quotient.sound h ⟩

/-- Decidability of equality -/
instance Int.decidableEq : DecidableEq Int := by
  intro a b
  have : ∀ (n:PreInt) (m: PreInt),
      Decidable (Quotient.mk PreInt.instSetoid n = Quotient.mk PreInt.instSetoid m) := by
    intro ⟨ a,b ⟩ ⟨ c,d ⟩
    rw [eq]
    exact decEq _ _
  exact Quotient.recOnSubsingleton₂ a b this

/-- Definition 4.1.1 (Integers) -/
theorem Int.eq_diff (n:Int) : ∃ a b, n = a —— b := by apply n.ind _; intro ⟨ a, b ⟩; use a, b

/-- Lemma 4.1.3 (Addition well-defined) -/
instance Int.instAdd : Add Int where
  add := Quotient.lift₂ (fun ⟨ a, b ⟩ ⟨ c, d ⟩ ↦ (a+c) —— (b+d) ) (by
    intro ⟨ a, b ⟩ ⟨ c, d ⟩ ⟨ a', b' ⟩ ⟨ c', d' ⟩ h1 h2
    simp [Setoid.r] at *
    calc
      _ = (a+b') + (c+d') := by abel
      _ = (a'+b) + (c'+d) := by rw [h1,h2]
      _ = _ := by abel)

/-- Definition 4.1.2 (Definition of addition) -/
theorem Int.add_eq (a b c d:ℕ) : a —— b + c —— d = (a+c)——(b+d) := Quotient.lift₂_mk _ _ _ _

/-- Lemma 4.1.3 (Multiplication well-defined) -/
theorem Int.mul_congr_left (a b a' b' c d : ℕ) (h: a —— b = a' —— b') :
    (a*c+b*d) —— (a*d+b*c) = (a'*c+b'*d) —— (a'*d+b'*c) := by
  simp only [eq] at *
  calc
    _ = c*(a+b') + d*(a'+b) := by ring
    _ = c*(a'+b) + d*(a+b') := by rw [h]
    _ = _ := by ring

/-- Lemma 4.1.3 (Multiplication well-defined) -/
theorem Int.mul_congr_right (a b c d c' d' : ℕ) (h: c —— d = c' —— d') :
    (a*c+b*d) —— (a*d+b*c) = (a*c'+b*d') —— (a*d'+b*c') := by
  simp only [eq] at *
  calc
    _ = a*(c+d') + b*(c'+d) := by ring
    _ = a*(c'+d) + b*(c+d') := by rw [h]
    _ = _ := by ring

/-- Lemma 4.1.3 (Multiplication well-defined) -/
theorem Int.mul_congr {a b c d a' b' c' d' : ℕ} (h1: a —— b = a' —— b') (h2: c —— d = c' —— d') :
  (a*c+b*d) —— (a*d+b*c) = (a'*c'+b'*d') —— (a'*d'+b'*c') := by
  rw [mul_congr_left a b a' b' c d h1, mul_congr_right a' b' c d c' d' h2]

instance Int.instMul : Mul Int where
  mul := Quotient.lift₂ (fun ⟨ a, b ⟩ ⟨ c, d ⟩ ↦ (a * c + b * d) —— (a * d + b * c)) (by
    intro ⟨ a, b ⟩ ⟨ c, d ⟩ ⟨ a', b' ⟩ ⟨ c', d' ⟩ h1 h2; simp at h1 h2
    convert mul_congr _ _ <;> simpa
    )

/-- Definition 4.1.2 (Multiplication of integers) -/
theorem Int.mul_eq (a b c d:ℕ) : a —— b * c —— d = (a*c+b*d) —— (a*d+b*c) := Quotient.lift₂_mk _ _ _ _

instance Int.instOfNat {n:ℕ} : OfNat Int n where
  ofNat := n —— 0

instance Int.instNatCast : NatCast Int where
  natCast n := n —— 0

theorem Int.ofNat_eq (n:ℕ) : ofNat(n) = n —— 0 := rfl

theorem Int.natCast_eq (n:ℕ) : (n:Int) = n —— 0 := rfl

@[simp]
theorem Int.natCast_ofNat (n:ℕ) : ((ofNat(n):ℕ): Int) = ofNat(n) := by rfl

@[simp]
theorem Int.ofNat_inj (n m:ℕ) : (ofNat(n) : Int) = (ofNat(m) : Int) ↔ ofNat(n) = ofNat(m) := by
  simp only [ofNat_eq, eq, add_zero]; rfl

@[simp]
theorem Int.natCast_inj (n m:ℕ) : (n : Int) = (m : Int) ↔ n = m := by
  simp only [natCast_eq, eq, add_zero]

example : 3 = 3 —— 0 := rfl

example : 3 = 4 —— 1 := by rw [Int.ofNat_eq, Int.eq]

/-- (Not from textbook) 0 is the only natural whose cast is 0 -/
lemma Int.cast_eq_0_iff_eq_0 (n : ℕ) : (n : Int) = 0 ↔ n = 0 := by
  rw [←natCast_inj]
  rfl

/-- Definition 4.1.4 (Negation of integers) / Exercise 4.1.2 -/
instance Int.instNeg : Neg Int where
  neg := Quotient.lift (fun ⟨ a, b ⟩ ↦ b —— a) (by
    intro ⟨a, b⟩ ⟨c, d⟩ h
    simp [Quotient.eq, Setoid.r] at *
    omega
  )

theorem Int.neg_eq (a b:ℕ) : -(a —— b) = b —— a := rfl

example : -(3 —— 5) = 5 —— 3 := rfl

abbrev Int.IsPos (x:Int) : Prop := ∃ (n:ℕ), n > 0 ∧ x = n
abbrev Int.IsNeg (x:Int) : Prop := ∃ (n:ℕ), n > 0 ∧ x = -n

/-- Lemma 4.1.5 (trichotomy of integers )-/
theorem Int.trichotomous (x:Int) : x = 0 ∨ x.IsPos ∨ x.IsNeg := by
  -- This proof is slightly modified from that in the original text.
  obtain ⟨ a, b, rfl ⟩ := eq_diff x
  obtain h_lt | rfl | h_gt := _root_.trichotomous (r := LT.lt) a b
  . obtain ⟨ c, rfl ⟩ := Nat.exists_eq_add_of_lt h_lt
    right; right; refine ⟨ c+1, by linarith, ?_ ⟩
    simp_rw [natCast_eq, neg_eq, eq]; abel
  . left; simp_rw [ofNat_eq, eq, add_zero, zero_add]
  obtain ⟨ c, rfl ⟩ := Nat.exists_eq_add_of_lt h_gt
  right; left; refine ⟨ c+1, by linarith, ?_ ⟩
  simp_rw [natCast_eq, eq]; abel

/-- Lemma 4.1.5 (trichotomy of integers)-/
theorem Int.not_pos_zero (x:Int) : x = 0 ∧ x.IsPos → False := by
  rintro ⟨ rfl, ⟨ n, _, _ ⟩ ⟩; simp_all [←natCast_ofNat]

/-- Lemma 4.1.5 (trichotomy of integers)-/
theorem Int.not_neg_zero (x:Int) : x = 0 ∧ x.IsNeg → False := by
  rintro ⟨ rfl, ⟨ n, _, hn ⟩ ⟩; simp_rw [←natCast_ofNat, natCast_eq, neg_eq, eq] at hn
  linarith

/-- Lemma 4.1.5 (trichotomy of integers)-/
theorem Int.not_pos_neg (x:Int) : x.IsPos ∧ x.IsNeg → False := by
  rintro ⟨ ⟨ n, _, rfl ⟩, ⟨ m, _, hm ⟩ ⟩; simp_rw [natCast_eq, neg_eq, eq] at hm
  linarith

/-- Proposition 4.1.6 (laws of algebra) / Exercise 4.1.4 -/
instance Int.instAddGroup : AddGroup Int :=
  AddGroup.ofLeftAxioms (by
    intro x y z
    obtain ⟨a, b, rfl⟩ := eq_diff x
    obtain ⟨c, d, rfl⟩ := eq_diff y
    obtain ⟨e, ⟨f, rfl⟩⟩ := eq_diff z
    simp only [add_eq, eq]
    ring
  ) (by
    intro x
    obtain ⟨a, b, rfl⟩ := eq_diff x
    simp [ofNat_eq, add_eq]
  ) (by
    intro x
    obtain ⟨a, b, rfl⟩ := eq_diff x
    simp only [neg_eq, ofNat_eq, add_eq, eq]
    ring
  )

/-- Proposition 4.1.6 (laws of algebra) / Exercise 4.1.4 -/
instance Int.instAddCommGroup : AddCommGroup Int where
  add_comm := by
    intro x y
    obtain ⟨a, b, rfl⟩ := eq_diff x
    obtain ⟨c, d, rfl⟩ := eq_diff y
    simp only [add_eq, eq]
    ring

/-- Proposition 4.1.6 (laws of algebra) / Exercise 4.1.4 -/
instance Int.instCommMonoid : CommMonoid Int where
  mul_comm := by
    intro x y
    obtain ⟨a, b, rfl⟩ := eq_diff x
    obtain ⟨c, d, rfl⟩ := eq_diff y
    simp only [mul_eq, eq]
    ring
  mul_assoc := by
    -- This proof is written to follow the structure of the original text.
    intro x y z
    obtain ⟨ a, b, rfl ⟩ := eq_diff x
    obtain ⟨ c, d, rfl ⟩ := eq_diff y
    obtain ⟨ e, f, rfl ⟩ := eq_diff z
    simp_rw [mul_eq]; congr 1 <;> ring
  one_mul := by
    intro x
    obtain ⟨a, b, rfl⟩ := eq_diff x
    simp only [ofNat_eq, mul_eq, eq]
    ring
  mul_one := by
    intro x
    obtain ⟨a, b, rfl⟩ := eq_diff x
    simp only [ofNat_eq, mul_eq, eq]
    ring

/-- Proposition 4.1.6 (laws of algebra) / Exercise 4.1.4 -/
instance Int.instCommRing : CommRing Int where
  left_distrib := by
    intro x y z
    obtain ⟨a, b, rfl⟩ := eq_diff x
    obtain ⟨c, d, rfl⟩ := eq_diff y
    obtain ⟨e, f, rfl⟩ := eq_diff z
    simp only [mul_eq, add_eq, eq]
    ring
  right_distrib := by
    intro x y z
    obtain ⟨a, b, rfl⟩ := eq_diff x
    obtain ⟨c, d, rfl⟩ := eq_diff y
    obtain ⟨e, f, rfl⟩ := eq_diff z
    simp only [mul_eq, add_eq, eq]
    ring
  zero_mul := by
    intro x
    obtain ⟨a, b, rfl⟩ := eq_diff x
    simp only [ofNat_eq, mul_eq, eq]
    ring
  mul_zero := by
    intro x
    obtain ⟨a, b, rfl⟩ := eq_diff x
    simp only [ofNat_eq, mul_eq, eq]
    ring

/-- Definition of subtraction -/
theorem Int.sub_eq (a b:Int) : a - b = a + (-b) := by rfl

theorem Int.sub_eq_formal_sub (a b:ℕ) : (a:Int) - (b:Int) = a —— b := by
  obtain ⟨m, n, ha⟩ := eq_diff (a:Int)
  obtain ⟨x, y, hb⟩ := eq_diff (b:Int)
  simp [sub_eq, natCast_eq, neg_eq, add_eq]

/-- Proposition 4.1.8 (No zero divisors) / Exercise 4.1.5 -/
theorem Int.mul_eq_zero {a b:Int} (h: a * b = 0) : a = 0 ∨ b = 0 := by
  obtain ⟨m, n, rfl⟩ := eq_diff a
  obtain ⟨x, y, rfl⟩ := eq_diff b
  simp_all only [mul_eq, ofNat_eq, eq, add_zero, zero_add]
  wlog hmn : m < n
  . rcases eq_or_gt_of_not_lt hmn with (hmn | hmn)
    . omega
    . specialize this n m x y (by omega) hmn; omega
  wlog hxy : x < y
  . rcases eq_or_gt_of_not_lt hxy with (hxy | hxy)
    . omega
    . specialize this m n y x (by omega) hmn hxy; omega
  rw [lt_iff_exists_add] at hmn hxy
  obtain ⟨o, ho⟩ := hmn
  obtain ⟨z, hz⟩ := hxy
  simp only [hz.2, ho.2, right_distrib, left_distrib] at h
  have : o * z = 0 := by omega
  simp_all

/-- Corollary 4.1.9 (Cancellation law) / Exercise 4.1.6 -/
theorem Int.mul_right_cancel₀ (a b c:Int) (h: a*c = b*c) (hc: c ≠ 0) : a = b := by
  obtain ⟨m, n, rfl⟩ := eq_diff a
  obtain ⟨u, v, rfl⟩ := eq_diff b
  obtain ⟨x, y, rfl⟩ := eq_diff c
  simp_all only [ofNat_eq, ne_eq, mul_eq, eq, add_zero, zero_add]
  wlog hxy : x < y
  . rcases eq_or_gt_of_not_lt hxy with (hxy | hxy)
    . omega
    . specialize this m n u v y x (by omega)
      omega
  rw [lt_iff_exists_add] at hxy
  obtain ⟨z, hz⟩ := hxy
  simp only [hz.2, left_distrib] at h
  have h' : m * z + v * z = u * z + n * z := by omega
  have hz' : z ≠ 0 := by omega
  simp only [←right_distrib] at h'
  rwa [Nat.mul_left_inj hz'] at h'

/-- Definition 4.1.10 (Ordering of the integers) -/
instance Int.instLE : LE Int where
  le n m := ∃ a:ℕ, m = n + a

/-- Definition 4.1.10 (Ordering of the integers) -/
instance Int.instLT : LT Int where
  lt n m := n ≤ m ∧ n ≠ m

theorem Int.le_iff (a b:Int) : a ≤ b ↔ ∃ t:ℕ, b = a + t := by rfl

theorem Int.lt_iff (a b:Int): a < b ↔ (∃ t:ℕ, b = a + t) ∧ a ≠ b := by rfl

/-- Lemma 4.1.11(a) (Properties of order) / Exercise 4.1.7 -/
theorem Int.lt_iff_exists_positive_difference (a b:Int) : a < b ↔ ∃ n:ℕ, n ≠ 0 ∧ b = a + n := by
  simp only [lt_iff]
  constructor
  · rintro ⟨⟨n, hn⟩, hab⟩
    aesop
  rintro ⟨n, ⟨hn, rfl⟩⟩
  constructor
  · aesop
  contrapose! hn
  rwa [left_eq_add, cast_eq_0_iff_eq_0] at hn

/-- Lemma 4.1.11(b) (Addition preserves order) / Exercise 4.1.7 -/
theorem Int.add_lt_add_right {a b:Int} (c:Int) (h: a < b) : a+c < b+c := by
  simp_all only [lt_iff]
  grind

/-- Lemma 4.1.11(c) (Positive multiplication preserves order) / Exercise 4.1.7 -/
theorem Int.mul_lt_mul_of_pos_right {a b c:Int} (hab : a < b) (hc: 0 < c) : a*c < b*c := by
  rw [lt_iff_exists_positive_difference] at *
  obtain ⟨n, hn⟩ := hab
  obtain ⟨m, hm⟩ := hc
  rw [hm.2, hn.2, zero_add, right_distrib]
  use n * m, (by simp_all)
  simp_all

/-- Lemma 4.1.11(d) (Negation reverses order) / Exercise 4.1.7 -/
theorem Int.neg_gt_neg {a b:Int} (h: b < a) : -a < -b := by
  rw [lt_iff_exists_positive_difference] at *
  obtain ⟨n, hn⟩ := h
  use n, hn.1
  simp_all

/-- Lemma 4.1.11(d) (Negation reverses order) / Exercise 4.1.7 -/
theorem Int.neg_ge_neg {a b:Int} (h: b ≤ a) : -a ≤ -b := by
  by_cases b = a
  · rw [le_iff]
    use 0
    simp_all
  suffices : -a < -b
  · exact this.1
  apply neg_gt_neg
  use h

/-- Lemma 4.1.11(e) (Order is transitive) / Exercise 4.1.7 -/
theorem Int.lt_trans {a b c:Int} (hab: a < b) (hbc: b < c) : a < c := by
  rw [lt_iff_exists_positive_difference] at *
  obtain ⟨m, hm⟩ := hbc
  obtain ⟨n, hn⟩ := hab
  use m + n
  constructor
  · omega
  simp [hm.2, hn.2, add_assoc, add_comm m]

/-- Lemma 4.1.11(f) (Order trichotomy) / Exercise 4.1.7 -/
theorem Int.trichotomous' (a b:Int) : a > b ∨ a < b ∨ a = b := by
  rcases (a - b).trichotomous with (h | h | h)
  · right; right; grind
  · left
    rw [gt_iff_lt, lt_iff_exists_positive_difference]
    obtain ⟨n, hn⟩ := h
    use n, by omega, by grind
  · right; left
    rw [lt_iff_exists_positive_difference]
    obtain ⟨n, hn⟩ := h
    use n, by omega, by grind

/-- Lemma 4.1.11(f) (Order trichotomy) / Exercise 4.1.7 -/
theorem Int.not_gt_and_lt (a b:Int) : ¬ (a > b ∧ a < b):= by
  intro h
  obtain ⟨⟨n, hn⟩, h1⟩ := h.1
  obtain ⟨⟨m, hm⟩, h2⟩ := h.2
  rw [hm] at hn
  obtain ⟨x, y, rfl⟩ := eq_diff a
  simp only [natCast_eq, add_eq, eq] at hn
  have : m = 0 := by omega
  subst this
  grind

/-- Lemma 4.1.11(f) (Order trichotomy) / Exercise 4.1.7 -/
theorem Int.not_gt_and_eq (a b:Int) : ¬ (a > b ∧ a = b):= by
  intro h
  rw [h.2, gt_iff_lt, lt_iff_exists_positive_difference] at h
  obtain ⟨x, y, rfl⟩ := eq_diff b
  simp only [natCast_eq, add_eq, eq] at h
  omega

/-- Lemma 4.1.11(f) (Order trichotomy) / Exercise 4.1.7 -/
theorem Int.not_lt_and_eq (a b:Int) : ¬ (a < b ∧ a = b):= by
  have := not_gt_and_eq b a
  grind

/-- (Not from textbook) Establish the decidability of this order. -/
instance Int.decidableRel : DecidableRel (· ≤ · : Int → Int → Prop) := by
  intro n m
  have : ∀ (n:PreInt) (m: PreInt),
      Decidable (Quotient.mk PreInt.instSetoid n ≤ Quotient.mk PreInt.instSetoid m) := by
    intro ⟨ a,b ⟩ ⟨ c,d ⟩
    change Decidable (a —— b ≤ c —— d)
    cases (a + d).decLe (b + c) with
      | isTrue h =>
        apply isTrue
        rw [le_iff]
        simp only [natCast_eq, add_eq, eq, add_zero]
        simp [le_iff_exists_add] at h
        grind
      | isFalse h =>
        apply isFalse
        rw [le_iff]
        simp only [natCast_eq, add_eq, eq, add_zero]
        grind
  exact Quotient.recOnSubsingleton₂ n m this

/-- (Not from textbook) 0 is the only additive identity -/
lemma Int.is_additive_identity_iff_eq_0 (b : Int) : (∀ a, a = a + b) ↔ b = 0 := by
  simp_all

/-- (Not from textbook) Int has the structure of a linear ordering. -/
instance Int.instLinearOrder : LinearOrder Int where
  le_refl := by intro a; rw [le_iff]; use 0; simp
  le_trans := by
    rintro a b c ⟨x, rfl⟩ ⟨y, rfl⟩
    use x + y
    simp only [Nat.cast_add]
    ring
  lt_iff_le_not_ge := by
    intro a b
    constructor
    · rintro ⟨haleb, hneq⟩
      constructor
      · grind
      intro hba
      rcases (trichotomous' a b) with (hab | hab | hab)
      · have : a < b := ⟨haleb, hneq⟩
        have := not_gt_and_lt
        grind
      · have : b < a := ⟨hba, hneq.symm⟩
        have := not_gt_and_lt
        grind
      · grind
    intro
    constructor <;> grind
  le_antisymm := by
    intro a b hab hba
    by_cases heq : a = b
    · grind
    have : a < b := ⟨hab, heq⟩
    have : b < a := ⟨hba, by grind⟩
    have := not_gt_and_lt
    grind
  le_total := by
    intro a b
    rcases trichotomous' a b with (hab | hab | hab)
    · right; exact hab.1
    · left; exact hab.1
    · left; use 0; grind
  toDecidableLE := decidableRel

/-- Exercise 4.1.3 -/
theorem Int.neg_one_mul (a:Int) : -1 * a = -a := by
  ring

/-- Exercise 4.1.8 -/
theorem Int.no_induction : ∃ P: Int → Prop, (P 0 ∧ ∀ n, P n → P (n+1)) ∧ ¬ ∀ n, P n := by
  use fun x ↦ x ≥ 0
  simp only [le_refl, true_and]
  constructor
  · intro n hn
    trans n
    · rw [ge_iff_le, le_iff]
      use 1
      simp
    exact hn
  push_neg
  use -1
  rw [lt_iff]
  constructor
  · use 1; norm_num
  · norm_num

/-- A nonnegative number squared is nonnegative. This is a special case of 4.1.9 that's useful for proving the general case. --/
lemma Int.sq_nonneg_of_pos (n:Int) (h: 0 ≤ n) : 0 ≤ n*n := by
  by_cases hz : n = 0
  · subst hz; simp
  apply le_of_lt
  rw [show 0 = 0 * n by simp]
  apply mul_lt_mul_of_pos_right <;> exact ⟨h, by grind⟩

/-- Exercise 4.1.9. The square of any integer is nonnegative. -/
theorem Int.sq_nonneg (n:Int) : 0 ≤ n*n := by
  by_cases hn : 0 ≤ n
  · exact sq_nonneg_of_pos n hn
  have hn' : n ≤ 0 := by have := le_total n 0; grind
  have hsq := sq_nonneg_of_pos _ (neg_ge_neg hn')
  simp_all

/-- Exercise 4.1.9 -/
theorem Int.sq_nonneg' (n:Int) : ∃ (m:Nat), n*n = m := by
  have := sq_nonneg n
  simpa only [le_iff, zero_add]

/--
  Not in textbook: create an equivalence between Int and ℤ.
  This requires some familiarity with the API for Mathlib's version of the integers.
-/
abbrev Int.equivInt : Int ≃ ℤ where
  toFun := Quotient.lift (fun ⟨ a, b ⟩ ↦ a - b) (by
    intro a b hab
    rw [PreInt.eq] at hab
    grind
  )
  invFun n := match n with
    | .ofNat m => m
    | .negSucc m => -(m + 1)
  left_inv n := by
    obtain ⟨a, b, rfl⟩ := eq_diff n
    simp only [Quotient.lift_mk]
    rcases h : (a:ℤ) - b with (m | m)
    · simp_all only [Int.ofNat_eq_coe, natCast_eq, eq]
      omega
    simp_all only [ofNat_eq, natCast_eq, neg_eq, add_eq, eq]
    omega
  right_inv n := by
    rcases n with (m | m)
    · simp only [Int.ofNat_eq_coe, natCast_eq, Quotient.lift_mk]
      omega
    simp only [ofNat_eq, natCast_eq, neg_eq, add_eq, Quotient.lift_mk]
    omega

/-- Not in textbook: equivalence preserves order and ring operations -/
abbrev Int.equivInt_ordered_ring : Int ≃+*o ℤ where
  toEquiv := equivInt
  map_add' := by
    intro x y
    obtain ⟨a, b, rfl⟩ := eq_diff x
    obtain ⟨c, d, rfl⟩ := eq_diff y
    simp_all only [add_eq, Quotient.lift_mk]
    grind
  map_mul' := by
    intro x y
    obtain ⟨a, b, rfl⟩ := eq_diff x
    obtain ⟨c, d, rfl⟩ := eq_diff y
    simp_all only [mul_eq, Quotient.lift_mk]
    grind
  map_le_map_iff' := by
    intro x y
    obtain ⟨a, b, rfl⟩ := eq_diff x
    obtain ⟨c, d, rfl⟩ := eq_diff y
    simp_all only [Quotient.lift_mk, le_iff, natCast_eq, add_eq, eq]
    rw [show (a:ℤ) - b ≤ c - d ↔ a + d ≤ c + b by omega, le_iff_exists_nonneg_add]
    grind

end Section_4_1
