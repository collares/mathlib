/-
Copyright (c) 2021 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson, Yaël Dillies
-/
import data.fintype.basic
import order.conditionally_complete_lattice

/-!
# Order structures on finite types

This file provides order instances on fintypes.

## Computable instances

On a `fintype`, we can construct
* an `order_bot` from `semilattice_inf`.
* an `order_top` from `semilattice_sup`.
* a `bounded_order` from `lattice`.

Those are marked as `def` to avoid defeqness issues.

## Completion instances

Those instances are noncomputable because the definitions of `Sup` and `Inf` use `set.to_finset` and
set membership is undecidable in general.

On a `fintype`, we can promote:
* a `lattice` to a `complete_lattice`.
* a `distrib_lattice` to a `complete_distrib_lattice`.
* a `linear_order`  to a `complete_linear_order`.
* a `boolean_algebra` to a `complete_boolean_algebra`.

Those are marked as `def` to avoid typeclass loops.

## Concrete instances

We provide a few instances for concrete types:
* `fin.complete_linear_order`
* `bool.complete_linear_order`
* `bool.complete_boolean_algebra`
-/

namespace finset

end finset

variables {ι α : Type*} [fintype ι] [fintype α]

section inhabited
variables (α) [inhabited α]

/-- Constructs the `⊥` of a finite inhabited `semilattice_inf`. -/
@[reducible] -- See note [reducible non-instances]
def fintype.to_order_bot [semilattice_inf α] : order_bot α :=
{ bot := finset.fold (⊓) (arbitrary α) id finset.univ,
  bot_le := λ a, ((finset.fold_op_rel_iff_and (@le_inf_iff α _)).1 le_rfl).2 a (finset.mem_univ _) }

/-- Constructs the `⊤` of a finite inhabited `semilattice_sup` -/
@[reducible] -- See note [reducible non-instances]
def fintype.to_order_top [semilattice_sup α] : order_top α :=
{ top := finset.fold (⊔) (arbitrary α) id finset.univ,
  le_top := λ a,
    ((finset.fold_op_rel_iff_and (λ x y z, show x ≥ y ⊔ z ↔ _, from sup_le_iff)).mp le_rfl).2
      a (finset.mem_univ a) }

/-- Constructs the `⊤` and `⊥` of a finite inhabited `lattice`. -/
@[reducible] -- See note [reducible non-instances]
def fintype.to_bounded_order [lattice α] : bounded_order α :=
{ .. fintype.to_order_bot α,
  .. fintype.to_order_top α }

end inhabited

section bounded_order
variables (α)

open_locale classical

/-- A finite bounded lattice is complete. -/
@[reducible] -- See note [reducible non-instances]
noncomputable def fintype.to_complete_lattice [hl : lattice α] [hb : bounded_order α] :
  complete_lattice α :=
{ Sup := λ s, s.to_finset.sup id,
  Inf := λ s, s.to_finset.inf id,
  le_Sup := λ _ _ ha, finset.le_sup (set.mem_to_finset.mpr ha),
  Sup_le := λ s _ ha, finset.sup_le (λ b hb, ha _ $ set.mem_to_finset.mp hb),
  Inf_le := λ _ _ ha, finset.inf_le (set.mem_to_finset.mpr ha),
  le_Inf := λ s _ ha, finset.le_inf (λ b hb, ha _ $ set.mem_to_finset.mp hb),
  .. hl, .. hb }

/-- A finite bounded distributive lattice is completely distributive. -/
@[reducible] -- See note [reducible non-instances]
noncomputable def fintype.to_complete_distrib_lattice [distrib_lattice α] [bounded_order α] :
  complete_distrib_lattice α :=
{ infi_sup_le_sup_Inf := λ a s, begin
    convert (finset.inf_sup_distrib_left _ _ _).ge,
    convert (finset.inf_eq_infi _ _).symm,
    simp_rw set.mem_to_finset,
    refl,
  end,
  inf_Sup_le_supr_inf := λ a s, begin
    convert (finset.sup_inf_distrib_left _ _ _).le,
    convert (finset.sup_eq_supr _ _).symm,
    simp_rw set.mem_to_finset,
    refl,
  end,
  ..fintype.to_complete_lattice α }

/-- A finite bounded linear order is complete. -/
@[reducible] -- See note [reducible non-instances]
noncomputable def fintype.to_complete_linear_order [h : linear_order α] [bounded_order α] :
  complete_linear_order α :=
{ .. fintype.to_complete_lattice α, .. h }

/-- A finite boolean algebra is complete. -/
@[reducible] -- See note [reducible non-instances]
noncomputable def fintype.to_complete_boolean_algebra [boolean_algebra α] :
  complete_boolean_algebra α :=
{ ..fintype.to_complete_distrib_lattice α, ..‹boolean_algebra α› }

end bounded_order

section nonempty
variables (α) [nonempty α]

/-- A nonempty finite lattice is complete. If the lattice is already a `bounded_order`, then use
`fintype.to_complete_lattice` instead, as this gives definitional equality for `⊥` and `⊤`. -/
@[reducible] -- See note [reducible non-instances]
noncomputable def fintype.to_complete_lattice_of_lattice [lattice α] : complete_lattice α :=
@fintype.to_complete_lattice _ _ _ $ @fintype.to_bounded_order α _ ⟨classical.arbitrary α⟩ _

/-- A nonempty finite linear order is complete. If the linear order is already a `bounded_order`,
then use `fintype.to_complete_linear_order` instead, as this gives definitional equality for `⊥` and
`⊤`. -/
@[reducible] -- See note [reducible non-instances]
noncomputable def fintype.to_complete_linear_order_of_linear_order [h : linear_order α] :
  complete_linear_order α :=
{ .. fintype.to_complete_lattice_of_lattice α,
  .. h }

end nonempty

/-! ### Concrete instances -/

noncomputable instance {n : ℕ} : complete_linear_order (fin (n + 1)) :=
fintype.to_complete_linear_order _

noncomputable instance : complete_linear_order bool := fintype.to_complete_linear_order _
noncomputable instance : complete_boolean_algebra bool := fintype.to_complete_boolean_algebra _
