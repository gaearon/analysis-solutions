import Mathlib.Tactic
import Analysis.Section_3_5

/-!
# Analysis I, Section 3.6: Cardinality of sets

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.


Main constructions and results of this section:

- Cardinality of a set
- Finite and infinite sets
- Connections with Mathlib equivalents

After this section, these notions will be deprecated in favor of their Mathlib equivalents.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Chapter3

export SetTheory (Set Object nat)

variable [SetTheory]

/-- Definition 3.6.1 (Equal cardinality) -/
abbrev SetTheory.Set.EqualCard (X Y:Set) : Prop := ∃ f : X → Y, Function.Bijective f

/-- Example 3.6.2 -/
theorem SetTheory.Set.Example_3_6_2 : EqualCard {0,1,2} {3,4,5} := by
  use open Classical in fun x ↦
    ⟨if x.val = 0 then 3 else if x.val = 1 then 4 else 5, by aesop⟩
  constructor
  · intro; aesop
  intro y
  have : y = (3: Object) ∨ y = (4: Object) ∨ y = (5: Object) := by
    have := y.property
    aesop
  rcases this with (_ | _ | _)
  · use ⟨0, by simp⟩; aesop
  · use ⟨1, by simp⟩; aesop
  · use ⟨2, by simp⟩; aesop

/-- Example 3.6.3 -/
theorem SetTheory.Set.Example_3_6_3 : EqualCard nat (nat.specify (fun x ↦ Even (x:ℕ))) := by
  use fun x ↦ ⟨((2:ℕ) * (x:ℕ)), by
    rw [specification_axiom'']
    constructor
    · use x; rw [@Equiv.apply_eq_iff_eq_symm_apply]; congr; ring
    · use ((2:ℕ) * (x:ℕ): nat).property⟩
  constructor
  · intro x y hf
    aesop
  intro ⟨y, hy⟩
  rw [specification_axiom''] at hy
  obtain ⟨_, ⟨x, hx⟩⟩ := hy
  use x
  rw [←Nat.two_mul] at hx
  simp [←hx]

@[refl]
theorem SetTheory.Set.EqualCard.refl (X:Set) : EqualCard X X := by
  use id
  exact Function.bijective_id

@[symm]
theorem SetTheory.Set.EqualCard.symm {X Y:Set} (h: EqualCard X Y) : EqualCard Y X := by
  obtain ⟨f, hf⟩ := h
  use Function.surjInv hf.2
  constructor
  · apply Function.injective_surjInv
  apply Function.RightInverse.surjective
  apply Function.leftInverse_surjInv hf

@[trans]
theorem SetTheory.Set.EqualCard.trans {X Y Z:Set} (h1: EqualCard X Y) (h2: EqualCard Y Z) : EqualCard X Z := by
  obtain ⟨f1, hf1⟩ := h1
  obtain ⟨f2, hf2⟩ := h2
  unfold EqualCard
  use (f2 ∘ f1)
  exact Function.Bijective.comp hf2 hf1

/-- Proposition 3.6.4 / Exercise 3.6.1 -/
instance SetTheory.Set.EqualCard.inst_setoid : Setoid SetTheory.Set := ⟨ EqualCard, {refl, symm, trans} ⟩

/-- Definition 3.6.5 -/
abbrev SetTheory.Set.has_card (X:Set) (n:ℕ) : Prop := X ≈ Fin n

theorem SetTheory.Set.has_card_iff (X:Set) (n:ℕ) :
    X.has_card n ↔ ∃ f: X → Fin n, Function.Bijective f := by
  simp [has_card, HasEquiv.Equiv, Setoid.r, EqualCard]

/-- Remark 3.6.6 -/
theorem SetTheory.Set.Remark_3_6_6 (n:ℕ) :
    (nat.specify (fun x ↦ 1 ≤ (x:ℕ) ∧ (x:ℕ) ≤ n)).has_card n := by
  rw [has_card_iff]
  use fun x ↦ Fin_mk _ (((⟨x.val, by aesop⟩: nat): ℕ) - (1:ℕ)) (by
    have := x.property
    rw [specification_axiom''] at this
    obtain ⟨_, ⟨h1, h2⟩⟩ := this
    use Nat.sub_one_lt_of_le h1 h2)
  constructor
  · intro x y hf
    simp only [Subtype.mk.injEq, Object.natCast_inj] at hf
    have := x.property
    have := y.property
    have := Nat.sub_one_cancel (by aesop) (by aesop) hf
    aesop
  intro ⟨y, hy⟩
  rw [mem_Fin] at hy
  obtain ⟨y', hy', rfl⟩ := hy
  use ⟨y' + (1:ℕ), by
    rw [specification_axiom'']
    use ((y' + (1:ℕ)): nat).property
    aesop⟩
  simp

/-- Example 3.6.7 -/
theorem SetTheory.Set.Example_3_6_7a (a:Object) : ({a}:Set).has_card 1 := by
  rw [has_card_iff]
  use fun _ ↦ Fin_mk _ 0 (by simp)
  constructor
  · intro x1 x2 hf; aesop
  intro y
  use ⟨a, by simp⟩
  have := Fin.toNat_lt y
  simp_all

theorem SetTheory.Set.Example_3_6_7b {a b c d:Object} (hab: a ≠ b) (hac: a ≠ c) (had: a ≠ d)
    (hbc: b ≠ c) (hbd: b ≠ d) (hcd: c ≠ d) : ({a,b,c,d}:Set).has_card 4 := by
  rw [has_card_iff]
  use open Classical in fun x ↦ Fin_mk _ (
    if x.val = a then 0 else if x.val = b then 1 else if x.val = c then 2 else 3
  ) (by aesop)
  constructor
  · intro x1 x2 hf; aesop
  intro y
  have : y = (0:ℕ) ∨ y = (1:ℕ) ∨ y = (2:ℕ) ∨ y = (3:ℕ) := by
    have := Fin.toNat_lt y
    omega
  rcases this with (_ | _ | _ | _)
  · use ⟨a, by aesop⟩; aesop
  · use ⟨b, by aesop⟩; aesop
  · use ⟨c, by aesop⟩; aesop
  · use ⟨d, by aesop⟩; aesop

/-- Lemma 3.6.9 -/
theorem SetTheory.Set.pos_card_nonempty {n:ℕ} (h: n ≥ 1) {X:Set} (hX: X.has_card n) : X ≠ ∅ := by
  -- This proof is written to follow the structure of the original text.
  by_contra! this
  have hnon : Fin n ≠ ∅ := by
    apply nonempty_of_inhabited (x := 0); rw [mem_Fin]; use 0, (by omega); rfl
  rw [has_card_iff] at hX
  choose f hf using hX
  -- obtain a contradiction from the fact that `f` is a bijection from the empty set to a
  -- non-empty set.
  subst this
  let z := Fin_mk n 0 (by aesop)
  choose e he using hf.2 z
  have := e.property
  simp_all

/-- Exercise 3.6.2a -/
theorem SetTheory.Set.has_card_zero {X:Set} : X.has_card 0 ↔ X = ∅ := by
  rw [has_card_iff]
  have : Fin 0 = ∅ := by aesop
  rw [this]
  constructor
  · choose f hf
    by_contra! h
    have := (f (nonempty_choose h)).property
    simp_all
  rintro rfl
  use id
  exact Function.bijective_id

/-- Lemma 3.6.9 -/
theorem SetTheory.Set.card_erase {n:ℕ} (h: n ≥ 1) {X:Set} (hX: X.has_card n) (x:X) :
    (X \ {x.val}).has_card (n-1) := by
  -- This proof has been rewritten from the original text to try to make it friendlier to
  -- formalize in Lean.
  rw [has_card_iff] at hX; choose f hf using hX
  set X' : Set := X \ {x.val}
  set ι : X' → X := fun ⟨y, hy⟩ ↦ ⟨ y, by aesop ⟩
  observe hι : ∀ x:X', (ι x:Object) = x
  choose m₀ hm₀ hm₀f using (mem_Fin _ _).mp (f x).property
  set g : X' → Fin (n-1) := fun x' ↦
    let := Fin.toNat_lt (f (ι x'))
    let : (f (ι x'):ℕ) ≠ m₀ := by
      by_contra!; simp [←this, Subtype.val_inj, hf.1.eq_iff, ι] at hm₀f
      have := x'.property; aesop
    if h' : f (ι x') < m₀ then Fin_mk _ (f (ι x')) (by omega)
    else Fin_mk _ (f (ι x') - 1) (by omega)
  have hg_def (x':X') : if (f (ι x'):ℕ) < m₀ then (g x':ℕ) = f (ι x') else (g x':ℕ) = f (ι x') - 1 := by
    split_ifs with h' <;> simp [g,h']
  have hg : Function.Bijective g := by
    constructor
    · intro x1' x2' hgx
      let x1 : X := ⟨x1', by have := x1'.property; simp_all [X']⟩
      let x2 : X := ⟨x2', by have := x2'.property; simp_all [X']⟩
      suffices : x1 = x2
      · aesop
      apply hf.1
      have hgx1 := hg_def x1'
      have hgx2 := hg_def x2'
      set fx1 := (f (ι x1'):ℕ)
      set fx2 := (f (ι x2'):ℕ)
      let gx := ((g x1'):ℕ)
      rw [show ((g x1'):ℕ) = gx by rfl] at hgx1
      rw [show ((g x2'):ℕ) = gx by rw [←hgx]] at hgx2
      suffices : fx1 = fx2
      · simpa [fx1, fx2]
      have hfx : ∀ (x': X'), (f (ι x'):ℕ) ≠ m₀ := by
        intro x'
        by_contra h
        have hfeq : (f x) = f (ι x') := by simp [Subtype.eq_iff, ←h, hm₀f]
        have heq : (x': Object) = x := by subst h; simp_all [hf.1 hfeq]
        have hneq : (x': Object) ≠ x := by have := x'.property; simp_all [X']
        tauto
      have := hfx x1'
      have := hfx x2'
      by_cases gx < m₀ <;> by_cases fx1 < m₀ <;> grind
    intro y
    by_cases hy : y < m₀
    · choose x2 hx2 using hf.2 (Fin_mk _ y (by omega))
      have hneq : x2 ≠ x := by
        by_contra hx2
        subst hx2
        have : y = m₀ := by simpa [hx2] using hm₀f
        omega
      let x' : X' := ⟨x2, by aesop⟩
      use x'
      specialize hg_def x'
      aesop
    choose x2 hx2 using hf.2 (Fin_mk _ (y + 1) (by have := Fin.toNat_lt y; omega))
    have hneq : x2 ≠ x := by
      by_contra hx2
      subst hx2
      have : m₀ = y + 1 := by simp_rw [hx2, Object.natCast_inj] at hm₀f; tauto
      simp_all
    let x' : X' := ⟨x2, by aesop⟩
    use x'
    specialize hg_def x'
    have : ¬(f x2 < m₀) := by simp_rw [hx2, Fin.toNat_mk]; omega
    rw [if_neg this, hx2] at hg_def
    simp_all
  use g

/-- Proposition 3.6.8 (Uniqueness of cardinality) -/
theorem SetTheory.Set.card_uniq {X:Set} {n m:ℕ} (h1: X.has_card n) (h2: X.has_card m) : n = m := by
  -- This proof is written to follow the structure of the original text.
  revert X m; induction' n with n hn
  . intro _ _ h1 h2; rw [has_card_zero] at h1; contrapose! h1
    apply pos_card_nonempty _ h2; omega
  intro X m h1 h2
  have : X ≠ ∅ := pos_card_nonempty (by omega) h1
  choose x hx using nonempty_def this
  have : m ≠ 0 := by contrapose! this; simpa [has_card_zero, this] using h2
  specialize hn (card_erase ?_ h1 ⟨ _, hx ⟩) (card_erase ?_ h2 ⟨ _, hx ⟩) <;> omega

lemma SetTheory.Set.Example_3_6_8_a: ({0,1,2}:Set).has_card 3 := by
  rw [has_card_iff]
  have : ({0, 1, 2}: Set) = SetTheory.Set.Fin 3 := by
    ext x
    simp only [mem_insert, mem_singleton, mem_Fin]
    constructor
    · aesop
    rintro ⟨x, ⟨_, rfl⟩⟩
    simp only [nat_coe_eq_iff]
    omega
  rw [this]
  use id
  exact Function.bijective_id

lemma SetTheory.Set.Example_3_6_8_b: ({3,4}:Set).has_card 2 := by
  rw [has_card_iff]
  use open Classical in fun x ↦ Fin_mk _ (if x = (3:Object) then 0 else 1) (by aesop)
  constructor
  · intro x1 x2
    aesop
  intro y
  have := Fin.toNat_lt y
  have : y = (0:ℕ) ∨ y = (1:ℕ) := by omega
  aesop

lemma SetTheory.Set.Example_3_6_8_c : ¬({0,1,2}:Set) ≈ ({3,4}:Set) := by
  by_contra h
  have h1 : Fin 3 ≈ Fin 2 := (Example_3_6_8_a.symm.trans h).trans Example_3_6_8_b
  have h2 : Fin 3 ≈ Fin 3 := by rfl
  have := card_uniq h1 h2
  contradiction

abbrev SetTheory.Set.finite (X:Set) : Prop := ∃ n:ℕ, X.has_card n

abbrev SetTheory.Set.infinite (X:Set) : Prop := ¬ finite X

/-- Exercise 3.6.3, phrased using Mathlib natural numbers -/
theorem SetTheory.Set.bounded_on_finite {n:ℕ} (f: Fin n → nat) : ∃ M, ∀ i, (f i:ℕ) ≤ M := by
  induction' n with n ih
  · simp
  let f' := fun (i: Fin n) ↦ f (Fin_embed _ _ (by omega) i)
  choose M' hM' using ih f'
  let M'' := f ⟨n, by rw [mem_Fin]; simp_all⟩
  use Nat.max M' M''
  intro i
  simp only [le_sup_iff]
  by_cases hi : (i:ℕ) = n
  · right
    apply le_of_eq
    congr; simpa
  left
  have : i < n + 1 := by have := i.property; rw [mem_Fin] at this; simpa
  have : i < n := by omega
  exact hM' ⟨i, by rw [mem_Fin]; simpa⟩

/-- Theorem 3.6.12 -/
theorem SetTheory.Set.nat_infinite : infinite nat := by
  -- This proof is written to follow the structure of the original text.
  by_contra this; choose n hn using this
  simp [has_card] at hn; symm at hn; simp [HasEquiv.Equiv, Setoid.r, EqualCard] at hn
  choose f hf using hn; choose M hM using bounded_on_finite f
  replace hf := hf.surjective ↑(M+1); contrapose! hf
  peel hM with hi; contrapose! hi
  apply_fun nat_equiv.symm at hi; simp_all

open Classical in
/-- It is convenient for Lean purposes to give infinite sets the ``junk`` cardinality of zero. -/
noncomputable def SetTheory.Set.card (X:Set) : ℕ := if h:X.finite then h.choose else 0

theorem SetTheory.Set.has_card_card {X:Set} (hX: X.finite) : X.has_card (SetTheory.Set.card X) := by
  simp [card, hX, hX.choose_spec]

theorem SetTheory.Set.has_card_to_card {X:Set} {n: ℕ}: X.has_card n → X.card = n := by
  intro h; simp [card, card_uniq (⟨ n, h ⟩:X.finite).choose_spec h]; aesop

theorem SetTheory.Set.card_to_has_card {X:Set} {n: ℕ} (hn: n ≠ 0): X.card = n → X.has_card n
  := by grind [card, has_card_card]

theorem SetTheory.Set.card_fin_eq (n:ℕ): (Fin n).has_card n := (has_card_iff _ _).mp ⟨ id, Function.bijective_id ⟩

theorem SetTheory.Set.Fin_card (n:ℕ): (Fin n).card = n := has_card_to_card (card_fin_eq n)

theorem SetTheory.Set.Fin_finite (n:ℕ): (Fin n).finite := ⟨n, card_fin_eq n⟩

theorem SetTheory.Set.EquivCard_to_has_card_eq {X Y:Set} {n: ℕ} (h: X ≈ Y): X.has_card n ↔ Y.has_card n := by
  choose f hf using h; let e := Equiv.ofBijective f hf
  constructor <;> (intro h'; rw [has_card_iff] at *; choose g hg using h')
  . use e.symm.trans (.ofBijective _ hg); apply Equiv.bijective
  . use e.trans (.ofBijective _ hg); apply Equiv.bijective

theorem SetTheory.Set.EquivCard_to_card_eq {X Y:Set} (h: X ≈ Y): X.card = Y.card := by
  by_cases hX: X.finite <;> by_cases hY: Y.finite <;> try rw [finite] at hX hY
  . choose nX hXn using hX; choose nY hYn using hY
    simp [has_card_to_card hXn, has_card_to_card hYn, EquivCard_to_has_card_eq h] at *
    solve_by_elim [card_uniq]
  . choose nX hXn using hX; rw [EquivCard_to_has_card_eq h] at hXn; tauto
  . choose nY hYn using hY; rw [←EquivCard_to_has_card_eq h] at hYn; tauto
  simp [card, hX, hY]

/-- Exercise 3.6.2 -/
theorem SetTheory.Set.empty_iff_card_eq_zero {X:Set} : X = ∅ ↔ X.finite ∧ X.card = 0 := by
  constructor
  · intro h
    rw [←has_card_zero] at h
    constructor
    · use 0
    exact has_card_to_card h
  intro ⟨h1, h2⟩
  rw [←has_card_zero]
  have := has_card_card h1
  rwa [h2] at this

lemma SetTheory.Set.empty_of_card_eq_zero {X:Set} (hX : X.finite) : X.card = 0 → X = ∅ := by
  intro h
  rw [empty_iff_card_eq_zero]
  exact ⟨hX, h⟩

lemma SetTheory.Set.finite_of_empty {X:Set} : X = ∅ → X.finite := by
  intro h
  rw [empty_iff_card_eq_zero] at h
  exact h.1

lemma SetTheory.Set.card_eq_zero_of_empty {X:Set} : X = ∅ → X.card = 0 := by
  intro h
  rw [empty_iff_card_eq_zero] at h
  exact h.2

@[simp]
lemma SetTheory.Set.empty_finite : (∅: Set).finite := finite_of_empty rfl

@[simp]
lemma SetTheory.Set.empty_card_eq_zero : (∅: Set).card = 0 := card_eq_zero_of_empty rfl

/-- Proposition 3.6.14 (a) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_insert {X:Set} (hX: X.finite) {x:Object} (hx: x ∉ X) :
    (X ∪ {x}).finite ∧ (X ∪ {x}).card = X.card + 1 := by
  have : (X ∪ {x}).card = X.card + 1 := by
    choose n hXn using hX
    have : X ∪ {x} ≈ Fin (n + 1) := by
      choose f hf using hXn
      use open Classical in fun a ↦
        if ha: a = x then
          Fin_mk _ n (by omega)
        else
          Fin_embed _ _ (by omega) (f ⟨a, by have := a.property; simp_all⟩)
      constructor
      · intro x1 x2 heq
        by_cases hx1 : x1 = x
        · by_cases hx2 : x2 = x
          · aesop
          simp only [hx1, hx2, reduceDIte, Subtype.mk.injEq] at heq
          symm at heq
          rw [Fin.coe_eq_iff] at heq
          generalize_proofs hx2' at heq
          have := Fin.toNat_lt (f ⟨x2, hx2'⟩)
          omega
        by_cases hx2 : x2 = x
        · simp only [hx1, hx2, reduceDIte, Subtype.mk.injEq] at heq
          rw [Fin.coe_eq_iff] at heq
          generalize_proofs hx1' at heq
          have := Fin.toNat_lt (f ⟨x1, hx1'⟩)
          omega
        simp only [hx1, hx2, reduceDIte, Subtype.mk.injEq, SetCoe.ext_iff] at heq
        ext; convert hf.1 heq; simp_all
      intro y
      by_cases hy : y = n
      · use ⟨x, by aesop⟩; simp_all
      let y' : Fin n := ⟨y, by
        have := Fin.toNat_lt y
        rw [mem_Fin]
        use y, by omega
        simp⟩
      choose x' hx' using hf.2 y'
      use ⟨x', by aesop⟩
      grind
    have : (X ∪ {x}).card = (Fin (n + 1)).card := EquivCard_to_card_eq this
    have : (X ∪ {x}).card = n + 1 := by simpa [Fin_card]
    have : X.card = n := has_card_to_card hXn
    grind
  constructor
  · use X.card + 1
    apply card_to_has_card (by simp) this
  exact this

/-- Proposition 3.6.14 (b) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_union {X Y:Set} (hX: X.finite) (hY: Y.finite) :
    (X ∪ Y).finite ∧ (X ∪ Y).card ≤ X.card + Y.card := by
  obtain ⟨n, hXn⟩ := hX
  obtain ⟨m, hXm⟩ := hY
  induction' n with n ih generalizing X
  · rw [has_card_zero] at hXn
    aesop
  have := pos_card_nonempty (by omega) hXn
  let x := nonempty_choose this
  have hX'n := card_erase (by omega) hXn x
  simp only [add_tsub_cancel_right] at hX'n
  obtain ⟨hX'Yf, hX'Yc⟩ := ih hX'n
  set X' := X \ {↑x}
  have hX : X = X' ∪ {↑x} := by
    symm; rw [union_comm]
    apply union_compl
    simp [subset_def, x.property]
  rw [hX, union_assoc, union_comm {↑x}, ←union_assoc, ←hX]
  replace hX'n := has_card_to_card hX'n
  replace hXn := has_card_to_card hXn
  by_cases hxY: ↑x ∈ Y
  · have : X' ∪ Y ∪ {↑x} = X' ∪ Y := by ext; grind [mem_union, mem_sdiff, mem_singleton]
    rw [this]
    use hX'Yf
    omega
  have hx : ↑x ∉ X' ∪ Y := by simpa [X']
  obtain ⟨hf, _⟩ := card_insert hX'Yf hx
  use hf
  omega

/-- Proposition 3.6.14 (b) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_union_disjoint {X Y:Set} (hX: X.finite) (hY: Y.finite)
    (hdisj: Disjoint X Y) : (X ∪ Y).card = X.card + Y.card := by
  obtain ⟨n, hXn⟩ := hX
  obtain ⟨m, hXm⟩ := hY
  induction' n with n ih generalizing X
  · rw [has_card_zero] at hXn
    aesop
  have hxne := pos_card_nonempty (by omega) hXn
  let x := nonempty_choose hxne
  have hX'n := card_erase (by omega) hXn x
  simp only [add_tsub_cancel_right] at hX'n
  set X' := X \ {↑x}
  have : Disjoint X' Y := by
    rw [disjoint_iff] at *; ext
    simp_rw [eq_empty_iff_forall_notMem, mem_inter] at hdisj
    simp_all [X']
  specialize ih this hX'n
  replace hX'n := has_card_to_card hX'n
  replace hXn := has_card_to_card hXn
  have : (X ∪ Y).card = (X' ∪ Y).card + 1 := by
    have hf : (X' ∪ Y).finite := by
      have hX'f : X'.finite := by
        by_cases X = {↑x}
        · have : X' = ∅ := by ext; grind [not_mem_empty, mem_sdiff]
          simp_all
        have := card_to_has_card (by omega) hXn
        have := card_erase (by omega) this x
        tauto
      have hYf : Y.finite := ⟨m, hXm⟩
      have := card_union hX'f hYf
      tauto
    have hx : ↑x ∉ X' ∪ Y := by
      simp only [mem_union, not_or, X']
      constructor
      · simp
      have := x.property
      simp only [disjoint_iff, eq_empty_iff_forall_notMem, mem_inter] at hdisj
      tauto
    have : X ∪ Y = X' ∪ Y ∪ {↑x} := by
      rw [union_assoc, union_comm Y, ←union_assoc]
      have := x.property
      have : X \ {↑x} ∪ {↑x} = X := by ext; grind [mem_union, mem_sdiff, mem_singleton]
      tauto
    have := card_insert hf hx
    simp_all
  grind

/-- Proposition 3.6.14 (c) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_subset {X Y:Set} (hX: X.finite) (hY: Y ⊆ X) :
    Y.finite ∧ Y.card ≤ X.card := by
  have finite_subset : ∀ {A B: Set}, A.finite → B ⊆ A → B.finite := by
    intro A B hA hB
    have ⟨n, hAn⟩ := hA
    induction' n with n ih generalizing A B
    · apply finite_of_empty
      rw [has_card_zero] at hAn
      rw [subset_def] at hB
      aesop
    by_cases hAB : A \ B = ∅
    · have : A = B := by ext a; rw [eq_empty_iff_forall_notMem] at hAB; aesop
      rwa [←this]
    have := pos_card_nonempty (by omega) hAn
    let a := nonempty_choose hAB
    let A' := A \ {↑a}
    have hA'n := card_erase (by omega) hAn ⟨a, by have := a.property; simp_all⟩
    simp only [add_tsub_cancel_right] at hA'n
    have ha : ↑a ∉ B := by have := a.property; simp_all
    have hBA' : B ⊆ A' := by simp only [subset_def]; aesop
    aesop
  let X' := X \ Y
  have hX' : X' ⊆ X := by simp only [subset_def]; aesop
  have hX'f : X'.finite := finite_subset hX hX'
  have hYf : Y.finite := finite_subset hX hY
  use hYf
  have hd : Disjoint X' Y := by
    have := inter_compl hY
    rwa [←disjoint_iff, disjoint_comm] at this
  obtain hc := card_union_disjoint hX'f hYf hd
  have hu : X' ∪ Y = X := by
    ext a
    simp only [X', mem_union, mem_sdiff]
    constructor <;> tauto
  rw [hu] at hc
  omega

/-- Proposition 3.6.14 (c) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_ssubset {X Y:Set} (hX: X.finite) (hY: Y ⊂ X) :
    Y.card < X.card := by
  have hY' : Y ⊆ X := by grind [subset_def, ssubset_def]
  let X' := (X \ Y)
  have hX'X : X' ⊆ X := by simp only [subset_def]; aesop
  have hX'f : X'.finite := (card_subset hX hX'X).1
  have hYf : Y.finite := (card_subset hX hY').1
  have hd : Disjoint X' Y := by simp [disjoint_iff, Set.ext_iff, X']
  have hc := card_union_disjoint hX'f hYf hd
  have hu : X' ∪ Y = X := by
    ext a
    simp only [X', mem_union, mem_sdiff]
    constructor <;> tauto
  rw [hu] at hc
  have : X' ≠ ∅ := by
    simp only [ssubset_def, subset_def, ne_eq, Set.ext_iff] at hY
    simp only [ne_eq, X', eq_empty_iff_forall_notMem, mem_sdiff]
    grind
  have : X'.card > 0 := by
    apply Nat.zero_lt_of_ne_zero
    intro h
    have := empty_of_card_eq_zero hX'f h
    contradiction
  omega

/-- Proposition 3.6.14 (d) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_image {X Y:Set} (hX: X.finite) (f: X → Y) :
    (image f X).finite ∧ (image f X).card ≤ X.card := by
  obtain ⟨n, hXn⟩ := hX
  induction' n with n ih generalizing X
  · rw [has_card_zero] at hXn
    constructor
    · apply finite_of_empty; aesop
    apply le_of_eq
    simp_rw [hXn, empty_card_eq_zero]
    apply card_eq_zero_of_empty
    aesop
  have hxne := pos_card_nonempty (by omega) hXn
  let x := nonempty_choose hxne
  have hX'n := card_erase (by omega) hXn x
  simp only [add_tsub_cancel_right] at hX'n
  set X' := X \ {↑x}
  let f' (x' : X') := f ⟨x', by have := x'.property; aesop⟩
  obtain ⟨hif, hic⟩ := ih f' hX'n
  have hi : image f X = (image f' X') ∪ {↑(f x)} := by
    simp only [f', X']
    ext y
    constructor
    · intro hy; rw [mem_image] at hy; obtain ⟨x2, ⟨_, rfl⟩⟩ := hy
      by_cases x = x2
      · aesop
      · rw [mem_union, mem_image]
        left; use ⟨x2, by grind [mem_sdiff, mem_singleton]⟩; grind
    intro hy; rw [mem_union] at hy; rcases hy
    · rw [mem_image] at *; grind
    · rw [mem_image]; use x, x.property; simp_all
  have hs : finite {↑(f x)} ∧ card {↑(f x)} = 1 := by
    have := card_insert empty_finite (not_mem_empty (f x))
    simp_all
  have hu := card_union hif hs.1
  rw [←hi, hs.2] at hu
  use hu.1
  have := has_card_to_card hX'n
  have := has_card_to_card hXn
  omega

/-- Proposition 3.6.14 (d) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_image_inj {X Y:Set} (hX: X.finite) {f: X → Y}
    (hf: Function.Injective f) : (image f X).card = X.card := by
  obtain ⟨n, hXn⟩ := hX
  induction' n with n ih generalizing X
  · rw [has_card_to_card hXn]
    rw [has_card_zero] at hXn
    apply card_eq_zero_of_empty
    simp_all [eq_empty_iff_forall_notMem]
  have hxne := pos_card_nonempty (by omega) hXn
  let x := nonempty_choose hxne
  have hX'n := card_erase (by omega) hXn x
  simp only [add_tsub_cancel_right] at hX'n
  set X' := X \ {↑x}
  let f' (x' : X') := f ⟨x', by have := x'.property; aesop⟩
  have hf' : Function.Injective f' := by intro x1 x2 heq; have := hf heq; grind
  obtain hc := ih hf' hX'n
  have hi : (image f X) = (image f' X') ∪ {↑(f x)} := by
    simp only [f', X']
    ext y
    constructor
    · intro hy; rw [mem_image] at hy; obtain ⟨x2, ⟨_, rfl⟩⟩ := hy
      by_cases x = x2
      · aesop
      · rw [mem_union, mem_image]
        left; use ⟨x2, by grind [mem_sdiff, mem_singleton]⟩; grind
    intro hy; rw [mem_union] at hy; rcases hy
    · rw [mem_image] at *; grind
    · rw [mem_image]; use x, x.property; simp_all
  have hif : (image f' X').finite := by
    use n
    by_cases hn : n = 0
    · simp_all [has_card_zero, eq_empty_iff_forall_notMem]
    · apply card_to_has_card hn (by simp_all [has_card_to_card hX'n])
  have hfx : ↑(f x) ∉ (image f' X') := by
    intro h; simp only [mem_image, f', X'] at h
    obtain ⟨x2, ⟨hx2, hx2'⟩⟩ := h
    have : f ⟨x2, by aesop⟩ = f x := by grind
    have : x2.val = x := by have := hf this; grind
    have : x2.val ≠ x := by rw [mem_sdiff] at hx2; simp_all
    grind
  have hic := card_insert hif hfx
  rw [hi]
  have := has_card_to_card hX'n
  have := has_card_to_card hXn
  omega

/-- Proposition 3.6.14 (e) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_prod {X Y:Set} (hX: X.finite) (hY: Y.finite) :
    (X ×ˢ Y).finite ∧ (X ×ˢ Y).card = X.card * Y.card := by
  induction' hXc: X.card with n ih generalizing X
  · rw [zero_mul]
    have := has_card_card hX
    rw [hXc] at this
    have : (X ×ˢ Y).has_card 0 := by rw [has_card_zero] at *; aesop
    constructor
    · use 0
    apply has_card_to_card
    exact this
  have hXn := card_to_has_card (by omega) hXc
  have hxne := pos_card_nonempty (by omega) hXn
  let x := nonempty_choose hxne
  have hX'n := card_erase (by omega) hXn x
  simp only [add_tsub_cancel_right] at hX'n
  set X' := X \ {↑x}
  have hX : X = X' ∪ {↑x} := by
    symm; rw [union_comm]
    apply union_compl
    simp [subset_def, x.property]
  by_cases hYz : Y = ∅
  · constructor
    · apply finite_of_empty; simp_all [Set.ext_iff]
    have : Y.card = 0 := by simp_all
    rw [this, mul_zero]
    apply card_eq_zero_of_empty
    simp_all [Set.ext_iff]
  have hYc : Y.card ≠ 0 := by
    rw [←has_card_zero] at hYz
    contrapose! hYz
    rw [has_card_zero]
    exact empty_of_card_eq_zero hY hYz
  have hX'f: X'.finite := ⟨n, hX'n⟩
  have hX'c := has_card_to_card hX'n
  obtain ⟨hpf, hpc⟩ := ih hX'f hX'c
  simp only [hX, union_prod, add_mul, one_mul]
  have hspc : card (({↑x}: Set) ×ˢ Y) = Y.card := by
    apply EquivCard_to_card_eq
    use fun z ↦ snd z
    constructor
    · intro z1 z2 heq; ext
      rw [pair_eq_fst_snd, pair_eq_fst_snd]
      grind [mem_singleton]
    intro y
    use mk_cartesian ⟨x, by simp⟩ y
    simp
  have hspf : (({↑x}: Set) ×ˢ Y).finite := by
    use Y.card
    exact card_to_has_card hYc hspc
  have hdisj : Disjoint (X' ×ˢ Y) (({↑x}: Set) ×ˢ Y) := by
    simp [disjoint_iff, inter_of_prod, Set.ext_iff, X']
  have hc := card_union_disjoint hpf hspf hdisj
  rw [hpc, hspc] at hc
  constructor
  · have := card_to_has_card (by omega) hc
    use n * Y.card + Y.card
  exact hc

noncomputable def SetTheory.Set.pow_fun_equiv {A B : Set} : ↑(A ^ B) ≃ (B → A) where
  toFun F := ((powerset_axiom _).mp F.property).choose
  invFun f := ⟨f, (powerset_axiom _).mpr ⟨f, by simp⟩⟩
  left_inv F := by ext; exact ((powerset_axiom _).mp F.property).choose_spec
  right_inv f := by simp

lemma SetTheory.Set.pow_fun_eq_iff {A B : Set} (x y : ↑(A ^ B)) : x = y ↔ pow_fun_equiv x = pow_fun_equiv y := by
  rw [←pow_fun_equiv.apply_eq_iff_eq]

/-- Proposition 3.6.14 (f) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_pow {X Y:Set} (hY: Y.finite) (hX: X.finite) :
    (Y ^ X).finite ∧ (Y ^ X).card = Y.card ^ X.card := by
  induction' hXc: X.card with n ih generalizing X
  · rw [pow_zero, empty_of_card_eq_zero hX hXc]
    have heq : Y ^ (∅: Set) ≈ Fin 1 := by
      use fun _ ↦ ⟨0, by rw [mem_Fin]; aesop⟩
      constructor
      · intro z1 z2
        rw [pow_fun_eq_iff]
        grind [not_mem_empty]
      intro y
      let f : (∅: Set) → Y := fun e ↦ by have := e.property; simp_all
      use pow_fun_equiv.symm f
      have := y.property
      rw [mem_Fin] at this
      simp_all
    constructor
    · use 1
    rw [EquivCard_to_card_eq heq, Fin_card]
  have hXn := card_to_has_card (by omega) hXc
  have hxne := pos_card_nonempty (by omega) hXn
  let x := nonempty_choose hxne
  have hX'n := card_erase (by omega) hXn x
  simp only [add_tsub_cancel_right] at hX'n
  set X' := X \ {↑x}
  have hX : X = X' ∪ {↑x} := by
    symm; rw [union_comm]
    apply union_compl
    simp [subset_def, x.property]
  have hX'f: X'.finite := ⟨n, hX'n⟩
  have hX'c := has_card_to_card hX'n
  obtain ⟨hpowf, hpowc⟩ := ih hX'f hX'c
  rw [pow_succ, ←hpowc]
  have ⟨hprodf, hprodc⟩ := card_prod hpowf hY
  have heq : Y ^ X ≈ (Y ^ X') ×ˢ Y := by
    use fun z ↦
      let f := pow_fun_equiv z
      let f' : X' → Y := fun x' ↦ f ⟨x', by have := x'.property; simp [X'] at this; grind⟩
      mk_cartesian (pow_fun_equiv.symm f') (f x)
    constructor
    · intro z1 z2 heq
      rw [pow_fun_eq_iff]
      ext x2; congr
      simp only [mk_cartesian, Subtype.mk.injEq, EmbeddingLike.apply_eq_iff_eq,
        OrderedPair.mk.injEq, SetCoe.ext_iff] at heq
      by_cases hx : x = x2
      · grind
      let x2' : X' := ⟨x2, by simp only [mem_sdiff, mem_singleton, X', x2.property]; grind⟩
      have := congrArg (pow_fun_equiv · x2') heq.1
      grind
    intro z'
    let f' := pow_fun_equiv (fst z')
    let f : X → Y := open Classical in fun x2 ↦
      if hx2 : x2 = x then
        (snd z')
      else
        f' ⟨x2, by have := x2.property; simp [X']; grind⟩
    use pow_fun_equiv.symm f
    rw [←mk_cartesian_fst_snd_eq z']
    simp only [mk_cartesian, Subtype.mk.injEq,
      EmbeddingLike.apply_eq_iff_eq, OrderedPair.mk.injEq]
    constructor
    · simp only [f, f']
      congr
      rw [pow_fun_eq_iff]
      ext x'
      have : x'.val ≠ x := by have := x'.property; simp [X'] at this; grind
      grind
    simp [f]
  have heqc := EquivCard_to_card_eq heq
  constructor
  · use ((Y ^ X') ×ˢ Y).card
    rw [EquivCard_to_has_card_eq heq]
    exact has_card_card hprodf
  rw [heqc]
  exact hprodc

/-- Exercise 3.6.5. You might find `SetTheory.Set.prod_commutator` useful. -/
theorem SetTheory.Set.prod_EqualCard_prod (A B:Set) :
    EqualCard (A ×ˢ B) (B ×ˢ A) := by
  use prod_commutator A B
  apply Equiv.bijective

noncomputable abbrev SetTheory.Set.pow_fun_equiv' (A B : Set) : ↑(A ^ B) ≃ (B → A) :=
  pow_fun_equiv (A:=A) (B:=B)

/-- Exercise 3.6.6. You may find `SetTheory.Set.curry_equiv` useful. -/
theorem SetTheory.Set.pow_pow_EqualCard_pow_prod (A B C:Set) :
    EqualCard ((A ^ B) ^ C) (A ^ (B ×ˢ C)) := by
  have e1 := pow_fun_equiv' (A ^ B) C
  have e2 := Equiv.arrowCongr (Equiv.refl C) (pow_fun_equiv' A B)
  have e3 : (C → (B → A)) ≃ (C ×ˢ B → A) := curry_equiv
  have e4 := Equiv.arrowCongr (prod_commutator C B) (Equiv.refl A)
  have e5 := (pow_fun_equiv' A (B ×ˢ C)).symm
  use e1.trans <| e2.trans <| e3.trans <| e4.trans <| e5
  apply Equiv.bijective

theorem SetTheory.Set.pow_pow_eq_pow_mul (a b c:ℕ): (a^b)^c = a^(b*c) := by
  have h1 := card_pow (Fin_finite a) (Fin_finite b)
  have h2 := card_pow h1.1 (Fin_finite c)
  have h3 := card_prod (Fin_finite b) (Fin_finite c)
  have h4 := card_pow (Fin_finite a) h3.1
  rw [←Fin_card a, ←Fin_card b, ←Fin_card c]
  rw [←h1.2, ←h2.2, ←h3.2, ←h4.2]
  have := pow_pow_EqualCard_pow_prod (Fin a) (Fin b) (Fin c)
  rw [EquivCard_to_card_eq this]

theorem SetTheory.Set.pow_prod_pow_EqualCard_pow_union (A B C:Set) (hd: Disjoint B C) :
    EqualCard ((A ^ B) ×ˢ (A ^ C)) (A ^ (B ∪ C)) := by
  use fun z ↦
    let f' (bc : ↑(B ∪ C)) : A := open Classical in
      if h: ↑bc ∈ B then
        let b : B := ⟨bc, by simp_all⟩
        pow_fun_equiv (fst z) b
      else
        let c : C := ⟨bc, by have := bc.property; simp_all⟩
        pow_fun_equiv (snd z) c
    pow_fun_equiv.symm f'
  constructor
  · intro z1 z2 heq
    ext
    simp only [pair_eq_fst_snd, pair_eq_fst_snd, EmbeddingLike.apply_eq_iff_eq, OrderedPair.mk.injEq]
    simp only [EmbeddingLike.apply_eq_iff_eq] at heq
    constructor
    · rw [Subtype.val_inj, pow_fun_eq_iff]
      ext b
      let bc : ↑(B ∪ C) := ⟨b, by have := b.property; simp_all⟩
      have := congrFun heq bc
      grind
    rw [Subtype.val_inj, pow_fun_eq_iff]
    ext c
    let bc : ↑(B ∪ C) := ⟨c, by have := c.property; simp_all⟩
    simp_rw [disjoint_iff, eq_empty_iff_forall_notMem, mem_inter] at hd
    have := congrFun heq bc
    grind
  intro z'
  let f := pow_fun_equiv z'
  let ba (b : B) := f ⟨b, by have := b.property; simp_all⟩
  let ca (c : C) := f ⟨c, by have := c.property; simp_all⟩
  use mk_cartesian (pow_fun_equiv.symm ba) (pow_fun_equiv.symm ca)
  simp [f, ba, ca]

theorem SetTheory.Set.pow_mul_pow_eq_pow_add (a b c:ℕ): (a^b) * a^c = a^(b+c) := by
  let fc (c: Fin c): Nat := ↑(c + b)
  have hfc : Function.Injective fc := by intro x1 x2; aesop
  have ⟨hCf, _⟩ := card_image (Fin_finite c) fc
  set C := image fc (Fin c)
  have hCd : Disjoint (Fin b) C := by rw [disjoint_iff]; aesop
  have h1 := card_image_inj (Fin_finite c) hfc
  have h2 := card_pow (Fin_finite a) (Fin_finite b)
  have h3 := card_pow (Fin_finite a) hCf
  have h4 := card_prod h2.1 h3.1
  have h5 := card_union_disjoint (Fin_finite b) hCf hCd
  have h6 := card_union (Fin_finite b) hCf
  have h7 := card_pow (Fin_finite a) h6.1
  rw [←Fin_card a, ←Fin_card b, ←Fin_card c]
  rw [←h1, ←h2.2, ←h3.2, ←h4.2, ←h5, ←h7.2]
  have := pow_prod_pow_EqualCard_pow_union (Fin a) (Fin b) C hCd
  rw [EquivCard_to_card_eq this]

/-- Exercise 3.6.7 -/
theorem SetTheory.Set.injection_iff_card_le {A B:Set} (hA: A.finite) (hB: B.finite) :
    (∃ f:A → B, Function.Injective f) ↔ A.card ≤ B.card := by
  constructor
  · rintro ⟨f, hf⟩
    rw [←card_image_inj hA hf]
    have hi := image_in_codomain f A
    exact (card_subset hB hi).2
  intro hAB
  have ⟨f, hf⟩ := has_card_card hA
  have ⟨g, hg⟩ := (has_card_card hB).symm
  let e : Fin A.card → Fin B.card := Fin_embed _ _ hAB
  have he : Function.Injective e := by intro a1 a2 heq; aesop
  use fun a ↦ g (e (f a))
  intro a1 a2 heq
  apply hf.1
  apply he
  apply hg.1
  exact heq

/-- Exercise 3.6.8 -/
theorem SetTheory.Set.surjection_from_injection {A B:Set} (hA: A ≠ ∅) (f: A → B)
    (hf: Function.Injective f) : ∃ g:B → A, Function.Surjective g := by
  let g := open Classical in fun b ↦
    if h: ∃! a, f a = b then h.exists.choose else nonempty_choose hA
  use g
  intro a
  use f a
  have hu : ∃! a', f a' = f a := by
    apply existsUnique_of_exists_of_unique
    · use a
    · intros; apply hf; grind
  simp only [g, hu, reduceDIte]
  generalize_proofs h
  exact hf h.choose_spec

/-- Exercise 3.6.9 -/
theorem SetTheory.Set.card_union_add_card_inter {A B:Set} (hA: A.finite) (hB: B.finite) :
    A.card + B.card = (A ∪ B).card + (A ∩ B).card := by
  have : A = (A \ B) ∪ (A ∩ B) := by ext; grind [mem_union, mem_sdiff, mem_inter]
  have : B = (B \ A) ∪ (A ∩ B) := by ext; grind [mem_union, mem_sdiff, mem_inter]
  have hAdf : (A \ B).finite := (card_subset hA (by simp [subset_def]; grind)).1
  have hBdf : (B \ A).finite := (card_subset hB (by simp [subset_def]; grind)).1
  have hif : (A ∩ B).finite := (card_subset hA (by apply inter_subset_left)).1
  have huf : (A \ B ∪ A ∩ B).finite := (card_union hAdf hif).1
  have hAd : Disjoint (A \ B) (A ∩ B) := by
    simp only [disjoint_iff, eq_empty_iff_forall_notMem, mem_inter, mem_sdiff]; grind
  have hBd : Disjoint (B \ A) (A ∩ B) := by
    simp only [disjoint_iff, eq_empty_iff_forall_notMem, mem_inter, mem_sdiff]; grind
  have hud : Disjoint (A \ B ∪ A ∩ B) (B \ A) := by
    simp only [disjoint_iff, eq_empty_iff_forall_notMem, mem_inter, mem_sdiff]; grind
  have := card_union_disjoint hAdf hif hAd
  have := card_union_disjoint hBdf hif hBd
  have := card_union_disjoint huf hBdf hud
  grind [union_eq_partition]

/-- Exercise 3.6.10 -/
theorem SetTheory.Set.pigeonhole_principle {n:ℕ} {A: Fin n → Set}
    (hA: ∀ i, (A i).finite) (hAcard: (iUnion _ A).card > n) : ∃ i, (A i).card ≥ 2 := by
  induction' n with n ih
  · contrapose! hAcard
    apply Nat.le_zero.mpr
    apply card_eq_zero_of_empty
    simp [eq_empty_iff_forall_notMem, mem_iUnion]
  let A' : Fin n → Set := fun i' ↦ A (Fin_embed _ _ (by simp) i')
  have hA' : ∀ i', (A' i').finite := by
    intro i'
    specialize hA (Fin_embed _ _ (by simp) i')
    simpa [A']
  specialize ih hA'
  by_cases h: ((Fin n).iUnion A').card > n
  · specialize ih h
    have ⟨i, hi⟩ := ih
    let i' : Fin (n + 1) := Fin_embed _ _ (by simp) i
    have hi' : i'.val = i := by simp [i']
    use i'
  let n': Fin (n+1) := Fin_mk _ n (by simp)
  use n'
  suffices : ((Fin (n + 1)).iUnion A).card ≤ ((Fin n).iUnion A').card + (A n').card
  · omega
  have hu : (Fin (n + 1)).iUnion A = (Fin n).iUnion A' ∪ A n' := by
    ext x
    simp only [mem_union, mem_iUnion]
    constructor
    · intro ⟨a, ha⟩
      by_cases a = n
      · right; convert ha; simp_all
      left
      use Fin_mk _ a (by have := Fin.toNat_lt a; omega)
      simpa [A', Fin_embed]
    rintro ⟨a, _⟩
    use Fin_embed _ _ (by simp) a
    use n'
  rw [hu]
  refine (card_union ?_ (hA n')).2
  have hs := subset_union_left ((Fin n).iUnion A') (A n')
  refine (card_subset ?_ hs).1
  have : ((Fin (n + 1)).iUnion A).card ≠ 0 := by omega
  have := card_to_has_card this rfl
  aesop

/-- Exercise 3.6.11 -/
theorem SetTheory.Set.two_to_two_iff {X Y:Set} (f: X → Y): Function.Injective f ↔
    ∀ S ⊆ X, S.card = 2 → (image f S).card = 2 := by
  constructor
  · intro hf S hS hSc
    rw [←hSc]
    have hSf : S.finite := by use 2; exact card_to_has_card (by simp) hSc
    let f' : S → Y := fun s ↦ f ⟨s, by aesop⟩
    have hf' : Function.Injective f' := by intro s1 s2 heq; have := hf heq; aesop
    have heq : image f S = image f' S := by simp only [f']; aesop
    rw [heq]
    exact card_image_inj hSf hf'
  intro hS x1 x2 heq
  let S : Set := {(x1: Object), (x2: Object)}
  have hSs : S ⊆ X := by simp only [S, subset_def]; aesop
  by_cases hxeq: x1 = x2
  · tauto
  have hSc : S.card = 2 := by
    apply has_card_to_card
    use open Classical in fun s ↦
      if s.val = x1 then
        Fin_mk _ 0 (by omega)
      else
        Fin_mk _ 1 (by omega)
    constructor
    · intro s1 s2 heq
      simp only [Fin.coe_inj] at heq
      by_cases s1.val = x1 <;> aesop
    intro y
    by_cases (y:ℕ) = 0
    · use ⟨x1, by aesop⟩; aesop
    use ⟨x2, by aesop⟩
    have : ((x2: Object) ≠ x1) := by aesop
    simp only [this, reduceIte, Fin.coe_inj, Fin.toNat_mk]
    have := Fin.toNat_lt y
    omega
  specialize hS S hSs hSc
  have : (image f S).card = 1 := by
    apply has_card_to_card
    use fun s ↦ Fin_mk _ 0 (by omega)
    constructor
    · intro y1 y2 hyeq; aesop
    · intro n
      use ⟨f x1, by aesop⟩
      simp only [Fin.coe_inj, Fin.toNat_mk]
      have := Fin.toNat_lt n
      omega
  rw [this] at hS
  tauto

/-- Exercise 3.6.12 -/
def SetTheory.Set.Permutations (n: ℕ): Set := (Fin n ^ Fin n).specify (fun F ↦
    Function.Bijective (pow_fun_equiv F))

/-- Exercise 3.6.12 (i), first part -/
theorem SetTheory.Set.Permutations_finite (n: ℕ): (Permutations n).finite := by
  have hs : Permutations n ⊆ (Fin n ^ Fin n) := by
    simp only [Permutations]
    apply specify_subset
  have ⟨hpf, hpc⟩ := card_pow (Fin_finite n) (Fin_finite n)
  exact (card_subset hpf hs).1

/- To continue Exercise 3.6.12 (i), we'll first develop some theory about `Permutations` and `Fin`. -/

noncomputable def SetTheory.Set.Permutations_toFun {n: ℕ} (p: Permutations n) : (Fin n) → (Fin n) := by
  have := p.property
  simp only [Permutations, specification_axiom'', powerset_axiom] at this
  exact this.choose.choose

theorem SetTheory.Set.Permutations_bijective {n: ℕ} (p: Permutations n) : Function.Bijective (Permutations_toFun p) := by
  have := p.property
  simp only [Permutations, specification_axiom'', powerset_axiom] at this
  aesop

theorem SetTheory.Set.Permutations_inj {n: ℕ} (p1 p2: Permutations n) : Permutations_toFun p1 = Permutations_toFun p2 ↔ p1 = p2 := by
  constructor
  · intro h
    simp [Permutations_toFun] at h
    generalize_proofs h1 h2 at h
    have := h1.choose_spec
    have := h2.choose_spec
    grind
  intro h
  grind

/-- This connects our concept of a permutation with Mathlib's `Equiv` between `Fin n` and `Fin n`. -/
noncomputable def SetTheory.Set.perm_equiv_equiv {n : ℕ} : Permutations n ≃ (Fin n ≃ Fin n) := {
  toFun := fun p => Equiv.ofBijective (Permutations_toFun p) (Permutations_bijective p)
  invFun := fun e => ⟨e, by simp [Permutations, pow_fun_equiv, e.bijective]⟩
  left_inv := fun p => by rw [←Permutations_inj]; simp [Equiv.ofBijective, Permutations_toFun]
  right_inv := fun e => by ext; simp [Permutations_toFun, Equiv.ofBijective]
}

/- Exercise 3.6.12 involves a lot of moving between `Fin n` and `Fin (n + 1)` so let's add some conveniences. -/

/-- Any `Fin n` can be cast to `Fin (n + 1)`. Compare to Mathlib `Fin.castSucc`. -/
def SetTheory.Set.Fin.castSucc {n} (x : Fin n) : Fin (n + 1) :=
  Fin_embed _ _ (by omega) x

@[simp]
lemma SetTheory.Set.Fin.castSucc_inj {n} {x y : Fin n} : castSucc x = castSucc y ↔ x = y := by
  constructor
  · intro h
    simp [castSucc] at h
    aesop
  aesop

@[simp]
theorem SetTheory.Set.Fin.castSucc_ne {n} (x : Fin n) : castSucc x ≠ n := by
  intro h
  have : (x : ℕ) = n := by
    simp [castSucc] at h
    exact h
  have : (x : ℕ) < n := Fin.toNat_lt x
  omega

/-- Any `Fin (n + 1)` except `n` can be cast to `Fin n`. Compare to Mathlib `Fin.castPred`. -/
noncomputable def SetTheory.Set.Fin.castPred {n} (x : Fin (n + 1)) (h : (x : ℕ) ≠ n) : Fin n :=
  Fin_mk _ (x : ℕ) (by have := Fin.toNat_lt x; omega)

@[simp]
theorem SetTheory.Set.Fin.castSucc_castPred {n} (x : Fin (n + 1)) (h : (x : ℕ) ≠ n) :
    castSucc (castPred x h) = x := by ext; simp [castSucc, castPred, Fin_embed]

@[simp]
theorem SetTheory.Set.Fin.castPred_castSucc {n} (x : Fin n) (h : ((castSucc x : Fin (n + 1)) : ℕ) ≠ n) :
    castPred (castSucc x) h = x := by ext; simp [castSucc, castPred, Fin_embed]

/-- Any natural `n` can be cast to `Fin (n + 1)`. Compare to Mathlib `Fin.last`. -/
def SetTheory.Set.Fin.last (n : ℕ) : Fin (n + 1) := Fin_mk _ n (by omega)

/-- Now is a good time to prove this result, which will be useful for completing Exercise 3.6.12 (i). -/
theorem SetTheory.Set.card_iUnion_card_disjoint {n m: ℕ} {S : Fin n → Set}
    (hSc : ∀ i, (S i).has_card m)
    (hSd : Pairwise fun i j => Disjoint (S i) (S j)) :
    ((Fin n).iUnion S).finite ∧ ((Fin n).iUnion S).card = n * m := by
  induction' n with n ih
  · rw [zero_mul]
    suffices : (Fin 0).iUnion S = ∅
    · constructor
      · apply finite_of_empty this
      · apply card_eq_zero_of_empty this
    ext x
    simp only [not_mem_empty, iff_false]
    intro h
    rw [mem_iUnion] at h
    obtain ⟨a, ha⟩ := h
    have := Fin.toNat_lt a
    omega
  let S' : (Fin n).toSubtype → Set := fun i ↦ S (Fin.castSucc i)
  have hS' : ∀ i, S (Fin.castSucc i) = S' i := by simp [S']
  have hSc' : ∀ (i : (Fin n).toSubtype), (S' i).has_card m := by intro i; apply hSc
  have hSd' : Pairwise fun i j ↦ Disjoint (S' i) (S' j) := by intro i j hij; apply hSd; aesop
  specialize ih hSc' hSd'
  have hSnf : (S (Fin.last n)).finite := by use m; apply hSc
  have hSnc := has_card_to_card (hSc (Fin.last n))
  rw [add_mul, one_mul, ←ih.2, ←hSnc]
  have hU : (Fin (n + 1)).iUnion S = (Fin n).iUnion S' ∪ S (Fin.last n) := by
    ext x
    constructor
    · intro hx
      rw [mem_iUnion] at hx
      rw [mem_union, mem_iUnion]
      obtain ⟨a, ha⟩ := hx
      by_cases ha' : a < n
      · left
        use Fin.castPred a (by omega)
        aesop
      right
      have : a = n := by have := Fin.toNat_lt a; omega
      have : a = Fin.last n := by aesop
      aesop
    intro hx
    rw [mem_iUnion]
    rw [mem_union, mem_iUnion] at hx
    rcases hx with (hx | hx)
    · simp only [S'] at hx
      obtain ⟨a, ha⟩ := hx
      use Fin.castSucc a
    use Fin.last n
  have hUf : ((Fin n).iUnion S').finite := ih.1
  rw [hU]
  set X := (Fin n).iUnion S'
  set Y := S (Fin.last n)
  have hd : Disjoint X Y := by
    rw [disjoint_iff, eq_empty_iff_forall_notMem]
    intro x
    rw [mem_inter]
    simp only [X, Y, mem_iUnion]
    intro ⟨⟨i, hi⟩, hx⟩
    let i' : Fin (n+1) := Fin_embed _ _ (by omega) i
    have : i' ≠ Fin.last n := by
      intro h
      have := Fin.toNat_lt i
      have : i = n := by aesop
      omega
    specialize hSd this
    rw [disjoint_iff, eq_empty_iff_forall_notMem] at hSd
    aesop
  have := card_union hUf hSnf
  use this.1
  exact card_union_disjoint hUf hSnf hd

/- Finally, we'll set up a way to shrink `Fin (n + 1)` into `Fin n` (or expand the latter) by making a hole. -/

/--
  If some `x : Fin (n+1)` is never equal to `i`, we can shrink it into `Fin n` by shifting all `x > i` down by one.
  Compare to Mathlib `Fin.predAbove`.
-/
noncomputable def SetTheory.Set.Fin.predAbove {n} (i : Fin (n + 1)) (x : Fin (n + 1)) (h : x ≠ i) : Fin n :=
  if hlt : (x:ℕ) < i then
    Fin_mk _ (x:ℕ) (by have := Fin.toNat_lt x; have := Fin.toNat_lt i; omega)
  else
    Fin_mk _ ((x:ℕ) - 1) (by
      have := Fin.toNat_lt x
      have : (x : ℕ) ≠ i := by aesop
      omega)

/--
  We can expand `x : Fin n` into `Fin (n + 1)` by shifting all `x ≥ i` up by one.
  The output is never `i`, so it forms an inverse to the shrinking done by `predAbove`.
  Compare to Mathlib `Fin.succAbove`.
-/
noncomputable def SetTheory.Set.Fin.succAbove {n} (i : Fin (n + 1)) (x : Fin n) : Fin (n + 1) :=
  if (x:ℕ) < i then
    Fin_embed _ _ (by omega) x
  else
    Fin_mk _ ((x:ℕ) + 1) (by have := Fin.toNat_lt x; omega)

@[simp]
theorem SetTheory.Set.Fin.succAbove_ne {n} (i : Fin (n + 1)) (x : Fin n) : succAbove i x ≠ i := by
  intro h
  simp only [succAbove, Fin_embed] at h
  by_cases hx : (x:ℕ) < i
  · aesop
  simp only [hx, ↓reduceIte, coe_inj, toNat_mk] at h
  omega

@[simp]
theorem SetTheory.Set.Fin.succAbove_predAbove {n} (i : Fin (n + 1)) (x : Fin (n + 1)) (h : x ≠ i) :
    (succAbove i) (predAbove i x h) = x := by
  simp only [succAbove, predAbove, coe_inj]
  have : x ≠ (i:ℕ) := by aesop
  by_cases hx : (x:ℕ) < i <;> simp only [hx, ↓reduceDIte, toNat_mk, ↓reduceIte, coe_eq_iff']
  by_cases hx' : (x:ℕ) - 1 < i <;> simp only [hx', coe_eq_iff', toNat_mk, ↓reduceIte] <;> omega

@[simp]
theorem SetTheory.Set.Fin.predAbove_succAbove {n} (i : Fin (n + 1)) (x : Fin n) :
    (predAbove i) (succAbove i x) (succAbove_ne i x) = x := by
  simp only [succAbove, predAbove]
  by_cases hx : (x:ℕ) < i <;> simp only [hx, ↓reduceIte]
  · aesop
  have hx' : ¬((x:ℕ) + 1 < i) := by omega
  simp [hx']

/-- Exercise 3.6.12 (i), second part -/
theorem SetTheory.Set.Permutations_ih (n: ℕ):
    (Permutations (n + 1)).card = (n + 1) * (Permutations n).card := by
  let S i := (Permutations (n + 1)).specify (fun p ↦ perm_equiv_equiv p (Fin.last n) = i)

  have hSd : Pairwise fun i j => Disjoint (S i) (S j) := by
    intro i h hij
    rw [disjoint_iff, eq_empty_iff_forall_notMem]
    aesop

  have hSe : ∀ i, S i ≈ Permutations n := by
    intro i
    have si_to_equiv : S i ≃ {f : Fin (n + 1) ≃ Fin (n + 1) // f (Fin.last n) = i} := {
      toFun s := by
        let hs := s.property
        simp only [specification_axiom'', S] at hs
        let p : Permutations (n + 1) := ⟨s, by grind⟩
        let f := perm_equiv_equiv p
        exact ⟨f, by grind⟩
      invFun := fun ⟨f, hf⟩ ↦
        let p := perm_equiv_equiv.symm f
        ⟨p, by simp only [specification_axiom'', S]; grind⟩
      left_inv s := by ext; simp
      right_inv e := by ext; simp
    }
    have equiv_to_equiv : {f : Fin (n + 1) ≃ Fin (n + 1) // f (Fin.last n) = i} ≃ (Fin n ≃ Fin n) := open Classical in {
      toFun := fun ⟨f, hf⟩ => {
        toFun x := Fin.predAbove i (f (Fin.castSucc x)) (by
          intro h
          rw [←hf] at h
          have := f.injective h
          have : x = n := by simpa
          have : x < n := Fin.toNat_lt x
          omega)
        invFun x := Fin.castPred (f.invFun (Fin.succAbove i x)) (by
          suffices : f.invFun (Fin.succAbove i x) ≠ (Fin.last n)
          · simpa
          intro h
          rw [←h, Equiv.invFun_as_coe] at hf
          aesop)
        left_inv := by intro; simp
        right_inv := by intro; simp
      },
      invFun := fun g => ⟨{
        toFun x := if hx : x = n then i else Fin.succAbove i (g (Fin.castPred x hx))
        invFun x := if hx : x = i then Fin.last n else Fin.castSucc (g.invFun (Fin.predAbove i x hx))
        left_inv := by intro; aesop
        right_inv := by intro; aesop
      }, by simp⟩
      left_inv := by intro f; ext x; simp_all [Subtype.coe_inj, ←f.property]
      right_inv := by intro; aesop
    }
    have equiv := si_to_equiv.trans (equiv_to_equiv.trans perm_equiv_equiv.symm)
    use equiv, equiv.injective, equiv.surjective

  have hSc : ∀ i, (S i).has_card (Permutations n).card := by
    intro i
    rw [EquivCard_to_has_card_eq (hSe i)]
    apply has_card_card
    apply Permutations_finite

  have hPu : Permutations (n + 1) = iUnion (Fin (n + 1)) S := by
    ext x
    simp only [mem_iUnion, S, specification_axiom'']
    grind

  have ⟨_, huc⟩ := card_iUnion_card_disjoint hSc hSd
  rw [hPu, huc]

/-- Exercise 3.6.12 (ii) -/
theorem SetTheory.Set.Permutations_card (n: ℕ):
    (Permutations n).card = n.factorial := by
  induction' n with n ih
  · rw [Nat.factorial_zero, Permutations]
    have hs : (Fin 0 ^ Fin 0) = (Fin 0 ^ Fin 0).specify
        fun F ↦ Function.Bijective (pow_fun_equiv F) := by
      ext x
      rw [specification_axiom'']
      constructor
      · intro hx
        let f := pow_fun_equiv ⟨x, hx⟩
        have : Function.Bijective f := by
          constructor
          · intro x1 x2 heq
            have := x1.property
            rw [mem_Fin] at this
            tauto
          intro y
          have := y.property
          rw [mem_Fin] at this
          tauto
        grind
      grind
    rw [←hs]
    have ⟨hpf, hpc⟩ := card_pow (Fin_finite 0) (Fin_finite 0)
    rw [hpc, Fin_card 0, pow_zero]
  rw [Nat.factorial_succ, Permutations_ih, ih]

/-- Connections with Mathlib's `Finite` -/
theorem SetTheory.Set.finite_iff_finite {X:Set} : X.finite ↔ Finite X := by
  rw [finite_iff_exists_equiv_fin, finite]
  constructor
  · rintro ⟨n, hn⟩
    use n
    obtain ⟨f, hf⟩ := hn
    have eq := (Equiv.ofBijective f hf).trans (Fin.Fin_equiv_Fin n)
    exact ⟨eq⟩
  rintro ⟨n, hn⟩
  use n
  have eq := hn.some.trans (Fin.Fin_equiv_Fin n).symm
  exact ⟨eq, eq.bijective⟩

/-- Connections with Mathlib's `Set.Finite` -/
theorem SetTheory.Set.finite_iff_set_finite {X:Set} :
    X.finite ↔ (X :_root_.Set Object).Finite := by
  rw [finite_iff_finite]
  rfl

/-- Connections with Mathlib's `Nat.card` -/
theorem SetTheory.Set.card_eq_nat_card {X:Set} : X.card = Nat.card X := by
  by_cases hf : X.finite
  · by_cases hz : X.card = 0
    · rw [hz]; symm
      have : X = ∅ := empty_of_card_eq_zero hf hz
      rw [this, Nat.card_eq_zero, isEmpty_iff]
      aesop
    symm
    have hc := has_card_card hf
    obtain ⟨f, hf⟩ := hc
    apply Nat.card_eq_of_equiv_fin
    exact (Equiv.ofBijective f hf).trans (Fin.Fin_equiv_Fin X.card)
  simp only [card, hf, ↓reduceDIte]; symm
  rw [Nat.card_eq_zero, ←not_finite_iff_infinite]
  right
  rwa [finite_iff_set_finite] at hf

/-- Connections with Mathlib's `Set.ncard` -/
theorem SetTheory.Set.card_eq_ncard {X:Set} : X.card = (X: _root_.Set Object).ncard := by
  rw [card_eq_nat_card]
  rfl

end Chapter3
