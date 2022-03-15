/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathbin.Data.SetLike.Basic
import Mathbin.Data.Fintype.Basic
import Mathbin.ModelTheory.TermsAndFormulas

/-!
# Definable Sets
This file defines what it means for a set over a first-order structure to be definable.

## Main Definitions
* `first_order.language.definable` is defined so that `L.definable A s` indicates that the
set `s` of a finite cartesian power of `M` is definable with parameters in `A`.
* `first_order.language.definable₁` is defined so that `L.definable₁ A s` indicates that
`(s : set M)` is definable with parameters in `A`.
* `first_order.language.definable₂` is defined so that `L.definable₂ A s` indicates that
`(s : set (M × M))` is definable with parameters in `A`.
* A `first_order.language.definable_set` is defined so that `L.definable_set α A` is the boolean
  algebra of subsets of `α → M` defined by formulas with parameters in `A`.

## Main Results
* `L.definable_set M α` forms a `boolean_algebra`.
* `definable.image_comp_sum` shows that definability is closed under projections.

-/


universe u v w

namespace FirstOrder

namespace Language

variable (L : Language.{u, v}) {M : Type w} [L.Structure M] (A : Set M)

open_locale FirstOrder

open Structure Set

variable {α : Type} [Fintype α] {β : Type} [Fintype β]

/-- A subset of a finite Cartesian product of a structure is definable over a set `A` when
  membership in the set is given by a first-order formula with parameters from `A`. -/
structure Definable (s : Set (α → M)) : Prop where
  exists_formula : ∃ φ : L[[A]].Formula α, s = SetOf φ.realize

variable {L} {A} {B : Set M} {s : Set (α → M)}

@[simp]
theorem definable_empty : L.Definable A (∅ : Set (α → M)) :=
  ⟨⟨⊥, by
      ext
      simp ⟩⟩

@[simp]
theorem definable_univ : L.Definable A (Univ : Set (α → M)) :=
  ⟨⟨⊤, by
      ext
      simp ⟩⟩

@[simp]
theorem Definable.inter {f g : Set (α → M)} (hf : L.Definable A f) (hg : L.Definable A g) : L.Definable A (f ∩ g) :=
  ⟨by
    rcases hf.exists_formula with ⟨φ, rfl⟩
    rcases hg.exists_formula with ⟨θ, rfl⟩
    refine' ⟨φ⊓θ, _⟩
    ext
    simp ⟩

@[simp]
theorem Definable.union {f g : Set (α → M)} (hf : L.Definable A f) (hg : L.Definable A g) : L.Definable A (f ∪ g) :=
  ⟨by
    rcases hf.exists_formula with ⟨φ, hφ⟩
    rcases hg.exists_formula with ⟨θ, hθ⟩
    refine' ⟨φ⊔θ, _⟩
    ext
    rw [hφ, hθ, mem_set_of_eq, formula.realize_sup, mem_union_eq, mem_set_of_eq, mem_set_of_eq]⟩

theorem definable_finset_inf {ι : Type _} {f : ∀ i : ι, Set (α → M)} (hf : ∀ i, L.Definable A (f i)) (s : Finset ι) :
    L.Definable A (s.inf f) := by
  classical
  refine' Finset.induction definable_univ (fun i s is h => _) s
  rw [Finset.inf_insert]
  exact (hf i).inter h

theorem definable_finset_sup {ι : Type _} {f : ∀ i : ι, Set (α → M)} (hf : ∀ i, L.Definable A (f i)) (s : Finset ι) :
    L.Definable A (s.sup f) := by
  classical
  refine' Finset.induction definable_empty (fun i s is h => _) s
  rw [Finset.sup_insert]
  exact (hf i).union h

theorem definable_finset_bInter {ι : Type _} {f : ∀ i : ι, Set (α → M)} (hf : ∀ i, L.Definable A (f i)) (s : Finset ι) :
    L.Definable A (⋂ i ∈ s, f i) := by
  rw [← Finset.inf_set_eq_bInter]
  exact definable_finset_inf hf s

theorem definable_finset_bUnion {ι : Type _} {f : ∀ i : ι, Set (α → M)} (hf : ∀ i, L.Definable A (f i)) (s : Finset ι) :
    L.Definable A (⋃ i ∈ s, f i) := by
  rw [← Finset.sup_set_eq_bUnion]
  exact definable_finset_sup hf s

@[simp]
theorem Definable.compl {s : Set (α → M)} (hf : L.Definable A s) : L.Definable A (sᶜ) :=
  ⟨by
    rcases hf.exists_formula with ⟨φ, hφ⟩
    refine' ⟨φ.not, _⟩
    rw [hφ]
    rfl⟩

@[simp]
theorem Definable.sdiff {s t : Set (α → M)} (hs : L.Definable A s) (ht : L.Definable A t) : L.Definable A (s \ t) :=
  hs.inter ht.Compl

theorem Definable.preimage_comp (f : α → β) {s : Set (α → M)} (h : L.Definable A s) :
    L.Definable A ((fun g : β → M => g ∘ f) ⁻¹' s) := by
  obtain ⟨φ, rfl⟩ := h.exists_formula
  refine' ⟨⟨φ.relabel f, _⟩⟩
  ext
  simp only [Set.preimage_set_of_eq, mem_set_of_eq, formula.realize_relabel]

theorem Definable.image_comp_equiv {s : Set (β → M)} (h : L.Definable A s) (f : α ≃ β) :
    L.Definable A ((fun g : β → M => g ∘ f) '' s) := by
  refine' (congr rfl _).mp (h.preimage_comp f.symm)
  rw [image_eq_preimage_of_inverse]
  · intro i
    ext b
    simp
    
  · intro i
    ext a
    simp
    

variable (L) {M} (A)

/-- A 1-dimensional version of `definable`, for `set M`. -/
def Definable₁ (s : Set M) : Prop :=
  L.Definable A { x : Finₓ 1 → M | x 0 ∈ s }

/-- A 2-dimensional version of `definable`, for `set (M × M)`. -/
def Definable₂ (s : Set (M × M)) : Prop :=
  L.Definable A { x : Finₓ 2 → M | (x 0, x 1) ∈ s }

variable (α)

/-- Definable sets are subsets of finite Cartesian products of a structure such that membership is
  given by a first-order formula. -/
def DefinableSet :=
  Subtype fun s : Set (α → M) => L.Definable A s

namespace DefinableSet

variable {A} {α}

instance : HasTop (L.DefinableSet A α) :=
  ⟨⟨⊤, definable_univ⟩⟩

instance : HasBot (L.DefinableSet A α) :=
  ⟨⟨⊥, definable_empty⟩⟩

instance : Inhabited (L.DefinableSet A α) :=
  ⟨⊥⟩

instance : SetLike (L.DefinableSet A α) (α → M) where
  coe := Subtype.val
  coe_injective' := Subtype.val_injective

@[simp]
theorem mem_top {x : α → M} : x ∈ (⊤ : L.DefinableSet A α) :=
  mem_univ x

@[simp]
theorem coe_top : ((⊤ : L.DefinableSet A α) : Set (α → M)) = ⊤ :=
  rfl

@[simp]
theorem not_mem_bot {x : α → M} : ¬x ∈ (⊥ : L.DefinableSet A α) :=
  not_mem_empty x

@[simp]
theorem coe_bot : ((⊥ : L.DefinableSet A α) : Set (α → M)) = ⊥ :=
  rfl

instance : Lattice (L.DefinableSet A α) :=
  Subtype.lattice (fun _ _ => Definable.union) fun _ _ => Definable.inter

theorem le_iff {s t : L.DefinableSet A α} : s ≤ t ↔ (s : Set (α → M)) ≤ (t : Set (α → M)) :=
  Iff.rfl

@[simp]
theorem coe_sup {s t : L.DefinableSet A α} : ((s⊔t : L.DefinableSet A α) : Set (α → M)) = s ∪ t :=
  rfl

@[simp]
theorem mem_sup {s t : L.DefinableSet A α} {x : α → M} : x ∈ s⊔t ↔ x ∈ s ∨ x ∈ t :=
  Iff.rfl

@[simp]
theorem coe_inf {s t : L.DefinableSet A α} : ((s⊓t : L.DefinableSet A α) : Set (α → M)) = s ∩ t :=
  rfl

@[simp]
theorem mem_inf {s t : L.DefinableSet A α} {x : α → M} : x ∈ s⊓t ↔ x ∈ s ∧ x ∈ t :=
  Iff.rfl

instance : BoundedOrder (L.DefinableSet A α) :=
  { DefinableSet.hasTop L, DefinableSet.hasBot L with bot_le := fun s x hx => False.elim hx,
    le_top := fun s x hx => mem_univ x }

instance : DistribLattice (L.DefinableSet A α) :=
  { DefinableSet.lattice L with
    le_sup_inf := by
      intro s t u x
      simp only [and_imp, mem_inter_eq, SetLike.mem_coe, coe_sup, coe_inf, mem_union_eq, Subtype.val_eq_coe]
      tauto }

/-- The complement of a definable set is also definable. -/
@[reducible]
instance : HasCompl (L.DefinableSet A α) :=
  ⟨fun ⟨s, hs⟩ => ⟨sᶜ, hs.Compl⟩⟩

@[simp]
theorem mem_compl {s : L.DefinableSet A α} {x : α → M} : x ∈ sᶜ ↔ ¬x ∈ s := by
  cases' s with s hs
  rfl

@[simp]
theorem coe_compl {s : L.DefinableSet A α} : ((sᶜ : L.DefinableSet A α) : Set (α → M)) = sᶜ := by
  ext
  simp

instance : BooleanAlgebra (L.DefinableSet A α) :=
  { DefinableSet.hasCompl L, DefinableSet.boundedOrder L, DefinableSet.distribLattice L with sdiff := fun s t => s⊓tᶜ,
    sdiff_eq := fun s t => rfl,
    sup_inf_sdiff := fun ⟨s, hs⟩ ⟨t, ht⟩ => by
      apply le_antisymmₓ <;> simp [le_iff],
    inf_inf_sdiff := fun ⟨s, hs⟩ ⟨t, ht⟩ => by
      rw [eq_bot_iff]
      simp only [coe_compl, le_iff, coe_bot, coe_inf, Subtype.coe_mk, le_eq_subset]
      intro x hx
      simp only [Set.mem_inter_eq, mem_compl_eq] at hx
      tauto,
    inf_compl_le_bot := fun ⟨s, hs⟩ => by
      simp [le_iff],
    top_le_sup_compl := fun ⟨s, hs⟩ => by
      simp [le_iff] }

end DefinableSet

end Language

end FirstOrder

