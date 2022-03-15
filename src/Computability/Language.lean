/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson
-/
import Mathbin.Data.List.Join
import Mathbin.Data.Set.Lattice

/-!
# Languages

This file contains the definition and operations on formal languages over an alphabet. Note strings
are implemented as lists over the alphabet.
The operations in this file define a [Kleene algebra](https://en.wikipedia.org/wiki/Kleene_algebra)
over the languages.
-/


universe u v

variable {α : Type u}

-- ././Mathport/Syntax/Translate/Basic.lean:980:9: unsupported derive handler has_mem (list α)
-- ././Mathport/Syntax/Translate/Basic.lean:980:9: unsupported derive handler has_singleton (list α)
-- ././Mathport/Syntax/Translate/Basic.lean:980:9: unsupported derive handler has_insert (list α)
/-- A language is a set of strings over an alphabet. -/
def Language α :=
  Set (List α)deriving [anonymous], [anonymous], [anonymous], CompleteBooleanAlgebra

namespace Language

attribute [local reducible] Language

/-- Zero language has no elements. -/
instance : Zero (Language α) :=
  ⟨(∅ : Set _)⟩

/-- `1 : language α` contains only one element `[]`. -/
instance : One (Language α) :=
  ⟨{[]}⟩

instance : Inhabited (Language α) :=
  ⟨0⟩

/-- The sum of two languages is the union of  -/
instance : Add (Language α) :=
  ⟨Set.Union⟩

instance : Mul (Language α) :=
  ⟨Set.Image2 (· ++ ·)⟩

theorem zero_def : (0 : Language α) = (∅ : Set _) :=
  rfl

theorem one_def : (1 : Language α) = {[]} :=
  rfl

theorem add_def (l m : Language α) : l + m = l ∪ m :=
  rfl

theorem mul_def (l m : Language α) : l * m = Set.Image2 (· ++ ·) l m :=
  rfl

/-- The star of a language `L` is the set of all strings which can be written by concatenating
  strings from `L`. -/
def Star (l : Language α) : Language α :=
  { x | ∃ S : List (List α), x = S.join ∧ ∀, ∀ y ∈ S, ∀, y ∈ l }

theorem star_def (l : Language α) : l.star = { x | ∃ S : List (List α), x = S.join ∧ ∀, ∀ y ∈ S, ∀, y ∈ l } :=
  rfl

@[simp]
theorem mem_one (x : List α) : x ∈ (1 : Language α) ↔ x = [] := by
  rfl

@[simp]
theorem mem_add (l m : Language α) (x : List α) : x ∈ l + m ↔ x ∈ l ∨ x ∈ m := by
  simp [add_def]

theorem mem_mul (l m : Language α) (x : List α) : x ∈ l * m ↔ ∃ a b, a ∈ l ∧ b ∈ m ∧ a ++ b = x := by
  simp [mul_def]

theorem mem_star (l : Language α) (x : List α) : x ∈ l.star ↔ ∃ S : List (List α), x = S.join ∧ ∀, ∀ y ∈ S, ∀, y ∈ l :=
  Iff.rfl

instance : Semiringₓ (Language α) where
  add := (· + ·)
  add_assoc := Set.union_assoc
  zero := 0
  zero_add := Set.empty_union
  add_zero := Set.union_empty
  add_comm := Set.union_comm
  mul := (· * ·)
  mul_assoc := fun l m n => by
    simp only [mul_def, Set.image2_image2_left, Set.image2_image2_right, List.append_assoc]
  zero_mul := by
    simp [zero_def, mul_def]
  mul_zero := by
    simp [zero_def, mul_def]
  one := 1
  one_mul := fun l => by
    simp [mul_def, one_def]
  mul_one := fun l => by
    simp [mul_def, one_def]
  left_distrib := fun l m n => by
    simp only [mul_def, add_def, Set.image2_union_right]
  right_distrib := fun l m n => by
    simp only [mul_def, add_def, Set.image2_union_left]

@[simp]
theorem add_self (l : Language α) : l + l = l :=
  sup_idem

theorem star_def_nonempty (l : Language α) :
    l.star = { x | ∃ S : List (List α), x = S.join ∧ ∀, ∀ y ∈ S, ∀, y ∈ l ∧ y ≠ [] } := by
  ext x
  constructor
  · rintro ⟨S, rfl, h⟩
    refine'
      ⟨S.filter fun l => ¬List.empty l, by
        simp , fun y hy => _⟩
    rw [List.mem_filterₓ, List.empty_iff_eq_nil] at hy
    exact ⟨h y hy.1, hy.2⟩
    
  · rintro ⟨S, hx, h⟩
    exact ⟨S, hx, fun y hy => (h y hy).1⟩
    

theorem le_iff (l m : Language α) : l ≤ m ↔ l + m = m :=
  sup_eq_right.symm

theorem le_mul_congr {l₁ l₂ m₁ m₂ : Language α} : l₁ ≤ m₁ → l₂ ≤ m₂ → l₁ * l₂ ≤ m₁ * m₂ := by
  intro h₁ h₂ x hx
  simp only [mul_def, exists_and_distrib_left, Set.mem_image2, Set.image_prod] at hx⊢
  tauto

theorem le_add_congr {l₁ l₂ m₁ m₂ : Language α} : l₁ ≤ m₁ → l₂ ≤ m₂ → l₁ + l₂ ≤ m₁ + m₂ :=
  sup_le_sup

theorem mem_supr {ι : Sort v} {l : ι → Language α} {x : List α} : (x ∈ ⨆ i, l i) ↔ ∃ i, x ∈ l i :=
  Set.mem_Union

theorem supr_mul {ι : Sort v} (l : ι → Language α) (m : Language α) : (⨆ i, l i) * m = ⨆ i, l i * m :=
  Set.image2_Union_left _ _ _

theorem mul_supr {ι : Sort v} (l : ι → Language α) (m : Language α) : (m * ⨆ i, l i) = ⨆ i, m * l i :=
  Set.image2_Union_right _ _ _

theorem supr_add {ι : Sort v} [Nonempty ι] (l : ι → Language α) (m : Language α) : (⨆ i, l i) + m = ⨆ i, l i + m :=
  supr_sup

theorem add_supr {ι : Sort v} [Nonempty ι] (l : ι → Language α) (m : Language α) : (m + ⨆ i, l i) = ⨆ i, m + l i :=
  sup_supr

theorem mem_pow {l : Language α} {x : List α} {n : ℕ} :
    x ∈ l ^ n ↔ ∃ S : List (List α), x = S.join ∧ S.length = n ∧ ∀, ∀ y ∈ S, ∀, y ∈ l := by
  induction' n with n ihn generalizing x
  · simp only [mem_one, pow_zeroₓ, List.length_eq_zero]
    constructor
    · rintro rfl
      exact ⟨[], rfl, rfl, fun y h => h.elim⟩
      
    · rintro ⟨_, rfl, rfl, _⟩
      rfl
      
    
  · simp only [pow_succₓ, mem_mul, ihn]
    constructor
    · rintro ⟨a, b, ha, ⟨S, rfl, rfl, hS⟩, rfl⟩
      exact ⟨a :: S, rfl, rfl, List.forall_mem_consₓ.2 ⟨ha, hS⟩⟩
      
    · rintro ⟨_ | ⟨a, S⟩, rfl, hn, hS⟩ <;> cases hn
      rw [List.forall_mem_consₓ] at hS
      exact ⟨a, _, hS.1, ⟨S, rfl, rfl, hS.2⟩, rfl⟩
      
    

theorem star_eq_supr_pow (l : Language α) : l.star = ⨆ i : ℕ, l ^ i := by
  ext x
  simp only [mem_star, mem_supr, mem_pow]
  constructor
  · rintro ⟨S, rfl, hS⟩
    exact ⟨_, S, rfl, rfl, hS⟩
    
  · rintro ⟨_, S, rfl, rfl, hS⟩
    exact ⟨S, rfl, hS⟩
    

theorem mul_self_star_comm (l : Language α) : l.star * l = l * l.star := by
  simp only [star_eq_supr_pow, mul_supr, supr_mul, ← pow_succₓ, ← pow_succ'ₓ]

@[simp]
theorem one_add_self_mul_star_eq_star (l : Language α) : 1 + l * l.star = l.star := by
  simp only [star_eq_supr_pow, mul_supr, ← pow_succₓ, ← pow_zeroₓ l]
  exact sup_supr_nat_succ _

@[simp]
theorem one_add_star_mul_self_eq_star (l : Language α) : 1 + l.star * l = l.star := by
  rw [mul_self_star_comm, one_add_self_mul_star_eq_star]

theorem star_mul_le_right_of_mul_le_right (l m : Language α) : l * m ≤ m → l.star * m ≤ m := by
  intro h
  rw [star_eq_supr_pow, supr_mul]
  refine' supr_le _
  intro n
  induction' n with n ih
  · simp
    
  rw [pow_succ'ₓ, mul_assoc (l ^ n) l m]
  exact le_transₓ (le_mul_congr le_rfl h) ih

theorem star_mul_le_left_of_mul_le_left (l m : Language α) : m * l ≤ m → m * l.star ≤ m := by
  intro h
  rw [star_eq_supr_pow, mul_supr]
  refine' supr_le _
  intro n
  induction' n with n ih
  · simp
    
  rw [pow_succₓ, ← mul_assoc m l (l ^ n)]
  exact le_transₓ (le_mul_congr h le_rfl) ih

end Language

