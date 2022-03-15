/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathbin.Data.Finset.Pairwise
import Mathbin.Data.Set.Finite

/-!
# Finite supremum independence

In this file, we define supremum independence of indexed sets. An indexed family `f : ι → α` is
sup-independent if, for all `a`, `f a` and the supremum of the rest are disjoint.

In distributive lattices, this is equivalent to being pairwise disjoint.

## Implementation notes

We avoid the "obvious" definition `∀ i ∈ s, disjoint (f i) ((s.erase i).sup f)` because `erase`
would require decidable equality on `ι`.

## TODO

`complete_lattice.independent` and `complete_lattice.set_independent` should live in this file.
-/


variable {α β ι ι' : Type _}

namespace Finset

section Lattice

variable [Lattice α] [OrderBot α]

/-- Supremum independence of finite sets. We avoid the "obvious" definition using `s.erase i`
because `erase` would require decidable equality on `ι`. -/
def SupIndep (s : Finset ι) (f : ι → α) : Prop :=
  ∀ ⦃t⦄, t ⊆ s → ∀ ⦃i⦄, i ∈ s → i ∉ t → Disjoint (f i) (t.sup f)

variable {s t : Finset ι} {f : ι → α} {i : ι}

instance [DecidableEq ι] [DecidableEq α] : Decidable (SupIndep s f) := by
  apply @Finset.decidableForallOfDecidableSubsets _ _ _ _
  intro t ht
  apply @Finset.decidableDforallFinset _ _ _ _
  exact fun i hi => @Implies.decidable _ _ _ (decidableOfIff' (_ = ⊥) disjoint_iff)

theorem SupIndep.subset (ht : t.SupIndep f) (h : s ⊆ t) : s.SupIndep f := fun u hu i hi => ht (hu.trans h) (h hi)

theorem sup_indep_empty (f : ι → α) : (∅ : Finset ι).SupIndep f := fun _ _ a ha => ha.elim

theorem sup_indep_singleton (i : ι) (f : ι → α) : ({i} : Finset ι).SupIndep f := fun s hs j hji hj => by
  rw [eq_empty_of_ssubset_singleton ⟨hs, fun h => hj (h hji)⟩, sup_empty]
  exact disjoint_bot_right

theorem SupIndep.pairwise_disjoint (hs : s.SupIndep f) : (s : Set ι).PairwiseDisjoint f := fun a ha b hb hab =>
  sup_singleton.subst <| hs (singleton_subset_iff.2 hb) ha <| not_mem_singleton.2 hab

/-- The RHS looks like the definition of `complete_lattice.independent`. -/
theorem sup_indep_iff_disjoint_erase [DecidableEq ι] :
    s.SupIndep f ↔ ∀, ∀ i ∈ s, ∀, Disjoint (f i) ((s.erase i).sup f) :=
  ⟨fun hs i hi => hs (erase_subset _ _) hi (not_mem_erase _ _), fun hs t ht i hi hit =>
    (hs i hi).mono_right (sup_mono fun j hj => mem_erase.2 ⟨ne_of_mem_of_not_mem hj hit, ht hj⟩)⟩

@[simp]
theorem sup_indep_pair [DecidableEq ι] {i j : ι} (hij : i ≠ j) :
    ({i, j} : Finset ι).SupIndep f ↔ Disjoint (f i) (f j) :=
  ⟨fun h =>
    h.PairwiseDisjoint
      (by
        simp )
      (by
        simp )
      hij,
    fun h => by
    rw [sup_indep_iff_disjoint_erase]
    intro k hk
    rw [Finset.mem_insert, Finset.mem_singleton] at hk
    obtain rfl | rfl := hk
    · convert h using 1
      rw [Finset.erase_insert, Finset.sup_singleton]
      simpa using hij
      
    · convert h.symm using 1
      have : ({i, k} : Finset ι).erase k = {i} := by
        ext
        rw [mem_erase, mem_insert, mem_singleton, mem_singleton, and_or_distrib_left, Ne.def, not_and_selfₓ, or_falseₓ,
          and_iff_right_of_imp]
        rintro rfl
        exact hij
      rw [this, Finset.sup_singleton]
      ⟩

theorem sup_indep_univ_bool (f : Bool → α) : (Finset.univ : Finset Bool).SupIndep f ↔ Disjoint (f false) (f true) :=
  have : tt ≠ ff := by
    simp only [Ne.def, not_false_iff]
  (sup_indep_pair this).trans Disjoint.comm

@[simp]
theorem sup_indep_univ_fin_two (f : Finₓ 2 → α) : (Finset.univ : Finset (Finₓ 2)).SupIndep f ↔ Disjoint (f 0) (f 1) :=
  have : (0 : Finₓ 2) ≠ 1 := by
    simp
  sup_indep_pair this

theorem SupIndep.attach (hs : s.SupIndep f) : s.attach.SupIndep (f ∘ Subtype.val) := by
  intro t ht i _ hi
  classical
  rw [← Finset.sup_image]
  refine' hs (image_subset_iff.2 fun _ => j.2) i.2 fun hi' => hi _
  rw [mem_image] at hi'
  obtain ⟨j, hj, hji⟩ := hi'
  rwa [Subtype.ext hji] at hj

end Lattice

section DistribLattice

variable [DistribLattice α] [OrderBot α] {s : Finset ι} {f : ι → α}

theorem sup_indep_iff_pairwise_disjoint : s.SupIndep f ↔ (s : Set ι).PairwiseDisjoint f :=
  ⟨SupIndep.pairwise_disjoint, fun hs t ht i hi hit =>
    disjoint_sup_right.2 fun j hj => hs hi (ht hj) (ne_of_mem_of_not_mem hj hit).symm⟩

alias sup_indep_iff_pairwise_disjoint ↔ Finset.SupIndep.pairwise_disjoint Set.PairwiseDisjoint.sup_indep

/-- Bind operation for `sup_indep`. -/
theorem SupIndep.sup [DecidableEq ι] {s : Finset ι'} {g : ι' → Finset ι} {f : ι → α}
    (hs : s.SupIndep fun i => (g i).sup f) (hg : ∀, ∀ i' ∈ s, ∀, (g i').SupIndep f) : (s.sup g).SupIndep f := by
  simp_rw [sup_indep_iff_pairwise_disjoint]  at hs hg⊢
  rw [sup_eq_bUnion, coe_bUnion]
  exact hs.bUnion_finset hg

/-- Bind operation for `sup_indep`. -/
theorem SupIndep.bUnion [DecidableEq ι] {s : Finset ι'} {g : ι' → Finset ι} {f : ι → α}
    (hs : s.SupIndep fun i => (g i).sup f) (hg : ∀, ∀ i' ∈ s, ∀, (g i').SupIndep f) : (s.bUnion g).SupIndep f := by
  rw [← sup_eq_bUnion]
  exact hs.sup hg

end DistribLattice

end Finset

theorem CompleteLattice.independent_iff_sup_indep [CompleteLattice α] {s : Finset ι} {f : ι → α} :
    CompleteLattice.Independent (f ∘ (coe : s → ι)) ↔ s.SupIndep f := by
  classical
  rw [Finset.sup_indep_iff_disjoint_erase]
  refine' subtype.forall.trans (forall₂_congrₓ fun a b => _)
  rw [Finset.sup_eq_supr]
  congr 2
  refine' supr_subtype.trans _
  congr 1 with x
  simp [supr_and, @supr_comm _ (x ∈ s)]

alias CompleteLattice.independent_iff_sup_indep ↔ CompleteLattice.Independent.sup_indep Finset.SupIndep.independent

/-- A variant of `complete_lattice.independent_iff_sup_indep` for `fintype`s. -/
theorem CompleteLattice.independent_iff_sup_indep_univ [CompleteLattice α] [Fintype ι] {f : ι → α} :
    CompleteLattice.Independent f ↔ Finset.univ.SupIndep f := by
  classical
  simp [Finset.sup_indep_iff_disjoint_erase, CompleteLattice.Independent, Finset.sup_eq_supr]

alias CompleteLattice.independent_iff_sup_indep_univ ↔
  CompleteLattice.Independent.sup_indep_univ Finset.SupIndep.independent_of_univ

