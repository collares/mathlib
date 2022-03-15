/-
Copyright (c) 2022 Yaël Dillies, Sara Rousta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Sara Rousta
-/
import Mathbin.Data.Set.Lattice
import Mathbin.Data.SetLike.Basic

/-!
# Up-sets and down-sets

This file defines upper and lower sets in an order.

## Main declarations

* `is_upper_set`: Predicate for a set to be an upper set. This means every element greater than a
  member of the set is in the set itself.
* `is_lower_set`: Predicate for a set to be a lower set. This means every element less than a member
  of the set is in the set itself.
* `upper_set`: The type of upper sets.
* `lower_set`: The type of lower sets.

## TODO

Lattice structure on antichains. Order equivalence between upper/lower sets and antichains.
-/


open OrderDual Set

variable {ι : Sort _} {κ : ι → Sort _} {α : Type _}

/-! ### Unbundled upper/lower sets -/


section Unbundled

variable [LE α] {s t : Set α}

/-- An upper set in an order `α` is a set such that any element greater than one of its members is
also a member. Also called up-set, upward-closed set. -/
def IsUpperSet (s : Set α) : Prop :=
  ∀ ⦃a b : α⦄, a ≤ b → a ∈ s → b ∈ s

/-- A lower set in an order `α` is a set such that any element less than one of its members is also
a member. Also called down-set, downward-closed set. -/
def IsLowerSet (s : Set α) : Prop :=
  ∀ ⦃a b : α⦄, b ≤ a → a ∈ s → b ∈ s

theorem is_upper_set_empty : IsUpperSet (∅ : Set α) := fun _ _ _ => id

theorem is_lower_set_empty : IsLowerSet (∅ : Set α) := fun _ _ _ => id

theorem is_upper_set_univ : IsUpperSet (Univ : Set α) := fun _ _ _ => id

theorem is_lower_set_univ : IsLowerSet (Univ : Set α) := fun _ _ _ => id

theorem IsUpperSet.compl (hs : IsUpperSet s) : IsLowerSet (sᶜ) := fun a b h hb ha => hb <| hs h ha

theorem IsLowerSet.compl (hs : IsLowerSet s) : IsUpperSet (sᶜ) := fun a b h hb ha => hb <| hs h ha

theorem IsUpperSet.union (hs : IsUpperSet s) (ht : IsUpperSet t) : IsUpperSet (s ∪ t) := fun a b h =>
  Or.imp (hs h) (ht h)

theorem IsLowerSet.union (hs : IsLowerSet s) (ht : IsLowerSet t) : IsLowerSet (s ∪ t) := fun a b h =>
  Or.imp (hs h) (ht h)

theorem IsUpperSet.inter (hs : IsUpperSet s) (ht : IsUpperSet t) : IsUpperSet (s ∩ t) := fun a b h =>
  And.imp (hs h) (ht h)

theorem IsLowerSet.inter (hs : IsLowerSet s) (ht : IsLowerSet t) : IsLowerSet (s ∩ t) := fun a b h =>
  And.imp (hs h) (ht h)

theorem is_upper_set_Union {f : ι → Set α} (hf : ∀ i, IsUpperSet (f i)) : IsUpperSet (⋃ i, f i) := fun a b h =>
  Exists₂.imp <| forall_range_iff.2 fun i => hf i h

theorem is_lower_set_Union {f : ι → Set α} (hf : ∀ i, IsLowerSet (f i)) : IsLowerSet (⋃ i, f i) := fun a b h =>
  Exists₂.imp <| forall_range_iff.2 fun i => hf i h

-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i j)
theorem is_upper_set_Union₂ {f : ∀ i, κ i → Set α} (hf : ∀ i j, IsUpperSet (f i j)) : IsUpperSet (⋃ (i) (j), f i j) :=
  is_upper_set_Union fun i => is_upper_set_Union <| hf i

-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i j)
theorem is_lower_set_Union₂ {f : ∀ i, κ i → Set α} (hf : ∀ i j, IsLowerSet (f i j)) : IsLowerSet (⋃ (i) (j), f i j) :=
  is_lower_set_Union fun i => is_lower_set_Union <| hf i

theorem is_upper_set_sUnion {S : Set (Set α)} (hf : ∀, ∀ s ∈ S, ∀, IsUpperSet s) : IsUpperSet (⋃₀S) := fun a b h =>
  Exists₂.imp fun s hs => hf s hs h

theorem is_lower_set_sUnion {S : Set (Set α)} (hf : ∀, ∀ s ∈ S, ∀, IsLowerSet s) : IsLowerSet (⋃₀S) := fun a b h =>
  Exists₂.imp fun s hs => hf s hs h

theorem is_upper_set_Inter {f : ι → Set α} (hf : ∀ i, IsUpperSet (f i)) : IsUpperSet (⋂ i, f i) := fun a b h =>
  forall₂_imp <| forall_range_iff.2 fun i => hf i h

theorem is_lower_set_Inter {f : ι → Set α} (hf : ∀ i, IsLowerSet (f i)) : IsLowerSet (⋂ i, f i) := fun a b h =>
  forall₂_imp <| forall_range_iff.2 fun i => hf i h

-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i j)
theorem is_upper_set_Inter₂ {f : ∀ i, κ i → Set α} (hf : ∀ i j, IsUpperSet (f i j)) : IsUpperSet (⋂ (i) (j), f i j) :=
  is_upper_set_Inter fun i => is_upper_set_Inter <| hf i

-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i j)
theorem is_lower_set_Inter₂ {f : ∀ i, κ i → Set α} (hf : ∀ i j, IsLowerSet (f i j)) : IsLowerSet (⋂ (i) (j), f i j) :=
  is_lower_set_Inter fun i => is_lower_set_Inter <| hf i

theorem is_upper_set_sInter {S : Set (Set α)} (hf : ∀, ∀ s ∈ S, ∀, IsUpperSet s) : IsUpperSet (⋂₀ S) := fun a b h =>
  forall₂_imp fun s hs => hf s hs h

theorem is_lower_set_sInter {S : Set (Set α)} (hf : ∀, ∀ s ∈ S, ∀, IsLowerSet s) : IsLowerSet (⋂₀ S) := fun a b h =>
  forall₂_imp fun s hs => hf s hs h

@[simp]
theorem is_lower_set_preimage_of_dual_iff : IsLowerSet (of_dual ⁻¹' s) ↔ IsUpperSet s :=
  Iff.rfl

@[simp]
theorem is_upper_set_preimage_of_dual_iff : IsUpperSet (of_dual ⁻¹' s) ↔ IsLowerSet s :=
  Iff.rfl

@[simp]
theorem is_lower_set_preimage_to_dual_iff {s : Set (OrderDual α)} : IsLowerSet (to_dual ⁻¹' s) ↔ IsUpperSet s :=
  Iff.rfl

@[simp]
theorem is_upper_set_preimage_to_dual_iff {s : Set (OrderDual α)} : IsUpperSet (to_dual ⁻¹' s) ↔ IsLowerSet s :=
  Iff.rfl

alias is_lower_set_preimage_of_dual_iff ↔ _ IsUpperSet.of_dual

alias is_upper_set_preimage_of_dual_iff ↔ _ IsLowerSet.of_dual

alias is_lower_set_preimage_to_dual_iff ↔ _ IsUpperSet.to_dual

alias is_upper_set_preimage_to_dual_iff ↔ _ IsLowerSet.to_dual

end Unbundled

/-! ### Bundled upper/lower sets -/


section Bundled

variable [LE α]

/-- The type of upper sets of an order. -/
structure UpperSet (α : Type _) [LE α] where
  Carrier : Set α
  upper' : IsUpperSet carrier

/-- The type of lower sets of an order. -/
structure LowerSet (α : Type _) [LE α] where
  Carrier : Set α
  lower' : IsLowerSet carrier

namespace UpperSet

instance UpperSet.setLike : SetLike (UpperSet α) α where
  coe := UpperSet.Carrier
  coe_injective' := fun s t h => by
    cases s
    cases t
    congr

@[ext]
theorem ext {s t : UpperSet α} : (s : Set α) = t → s = t :=
  SetLike.ext'

protected theorem upper (s : UpperSet α) : IsUpperSet (s : Set α) :=
  s.upper'

end UpperSet

namespace LowerSet

instance : SetLike (LowerSet α) α where
  coe := LowerSet.Carrier
  coe_injective' := fun s t h => by
    cases s
    cases t
    congr

@[ext]
theorem ext {s t : LowerSet α} : (s : Set α) = t → s = t :=
  SetLike.ext'

protected theorem lower (s : LowerSet α) : IsLowerSet (s : Set α) :=
  s.lower'

end LowerSet

/-! #### Order -/


namespace UpperSet

instance : HasSup (UpperSet α) :=
  ⟨fun s t => ⟨s ∪ t, s.upper.union t.upper⟩⟩

instance : HasInf (UpperSet α) :=
  ⟨fun s t => ⟨s ∩ t, s.upper.inter t.upper⟩⟩

instance : HasTop (UpperSet α) :=
  ⟨⟨Univ, is_upper_set_univ⟩⟩

instance : HasBot (UpperSet α) :=
  ⟨⟨∅, is_upper_set_empty⟩⟩

instance : HasSupₓ (UpperSet α) :=
  ⟨fun S => ⟨sup (coe '' S), is_upper_set_sUnion <| ball_image_iff.2 fun s _ => s.upper⟩⟩

instance : HasInfₓ (UpperSet α) :=
  ⟨fun S => ⟨inf (coe '' S), is_upper_set_sInter <| ball_image_iff.2 fun s _ => s.upper⟩⟩

instance : CompleteDistribLattice (UpperSet α) :=
  SetLike.coe_injective.CompleteDistribLattice _ (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl) rfl rfl

instance : Inhabited (UpperSet α) :=
  ⟨⊥⟩

@[simp]
theorem coe_top : ((⊤ : UpperSet α) : Set α) = univ :=
  rfl

@[simp]
theorem coe_bot : ((⊥ : UpperSet α) : Set α) = ∅ :=
  rfl

@[simp]
theorem coe_sup (s t : UpperSet α) : (↑(s⊔t) : Set α) = s ∪ t :=
  rfl

@[simp]
theorem coe_inf (s t : UpperSet α) : (↑(s⊓t) : Set α) = s ∩ t :=
  rfl

@[simp]
theorem coe_Sup (S : Set (UpperSet α)) : (↑(sup S) : Set α) = sup (coe '' S) :=
  rfl

@[simp]
theorem coe_Inf (S : Set (UpperSet α)) : (↑(inf S) : Set α) = inf (coe '' S) :=
  rfl

@[simp]
theorem coe_supr (f : ι → UpperSet α) : (↑(⨆ i, f i) : Set α) = ⨆ i, f i :=
  congr_argₓ sup (range_comp _ _).symm

@[simp]
theorem coe_infi (f : ι → UpperSet α) : (↑(⨅ i, f i) : Set α) = ⨅ i, f i :=
  congr_argₓ inf (range_comp _ _).symm

-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i j)
-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i j)
@[simp]
theorem coe_supr₂ (f : ∀ i, κ i → UpperSet α) : (↑(⨆ (i) (j), f i j) : Set α) = ⨆ (i) (j), f i j := by
  simp_rw [coe_supr]

-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i j)
-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i j)
@[simp]
theorem coe_infi₂ (f : ∀ i, κ i → UpperSet α) : (↑(⨅ (i) (j), f i j) : Set α) = ⨅ (i) (j), f i j := by
  simp_rw [coe_infi]

end UpperSet

namespace LowerSet

instance : HasSup (LowerSet α) :=
  ⟨fun s t => ⟨s ∪ t, fun a b h => Or.imp (s.lower h) (t.lower h)⟩⟩

instance : HasInf (LowerSet α) :=
  ⟨fun s t => ⟨s ∩ t, fun a b h => And.imp (s.lower h) (t.lower h)⟩⟩

instance : HasTop (LowerSet α) :=
  ⟨⟨Univ, fun a b h => id⟩⟩

instance : HasBot (LowerSet α) :=
  ⟨⟨∅, fun a b h => id⟩⟩

instance : HasSupₓ (LowerSet α) :=
  ⟨fun S => ⟨sup (coe '' S), is_lower_set_sUnion <| ball_image_iff.2 fun s _ => s.lower⟩⟩

instance : HasInfₓ (LowerSet α) :=
  ⟨fun S => ⟨inf (coe '' S), is_lower_set_sInter <| ball_image_iff.2 fun s _ => s.lower⟩⟩

instance : CompleteDistribLattice (LowerSet α) :=
  SetLike.coe_injective.CompleteDistribLattice _ (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl) rfl rfl

instance : Inhabited (LowerSet α) :=
  ⟨⊥⟩

@[simp]
theorem coe_top : ((⊤ : LowerSet α) : Set α) = univ :=
  rfl

@[simp]
theorem coe_bot : ((⊥ : LowerSet α) : Set α) = ∅ :=
  rfl

@[simp]
theorem coe_sup (s t : LowerSet α) : (↑(s⊔t) : Set α) = s ∪ t :=
  rfl

@[simp]
theorem coe_inf (s t : LowerSet α) : (↑(s⊓t) : Set α) = s ∩ t :=
  rfl

@[simp]
theorem coe_Sup (S : Set (LowerSet α)) : (↑(sup S) : Set α) = sup (coe '' S) :=
  rfl

@[simp]
theorem coe_Inf (S : Set (LowerSet α)) : (↑(inf S) : Set α) = inf (coe '' S) :=
  rfl

@[simp]
theorem coe_supr (f : ι → LowerSet α) : (↑(⨆ i, f i) : Set α) = ⨆ i, f i :=
  congr_argₓ sup (range_comp _ _).symm

@[simp]
theorem coe_infi (f : ι → LowerSet α) : (↑(⨅ i, f i) : Set α) = ⨅ i, f i :=
  congr_argₓ inf (range_comp _ _).symm

-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i j)
-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i j)
@[simp]
theorem coe_supr₂ (f : ∀ i, κ i → LowerSet α) : (↑(⨆ (i) (j), f i j) : Set α) = ⨆ (i) (j), f i j := by
  simp_rw [coe_supr]

-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i j)
-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i j)
@[simp]
theorem coe_infi₂ (f : ∀ i, κ i → LowerSet α) : (↑(⨅ (i) (j), f i j) : Set α) = ⨅ (i) (j), f i j := by
  simp_rw [coe_infi]

end LowerSet

/-! #### Complement -/


/-- The complement of a lower set as an upper set. -/
def UpperSet.compl (s : UpperSet α) : LowerSet α :=
  ⟨sᶜ, s.upper.Compl⟩

/-- The complement of a lower set as an upper set. -/
def LowerSet.compl (s : LowerSet α) : UpperSet α :=
  ⟨sᶜ, s.lower.Compl⟩

namespace UpperSet

@[simp]
theorem coe_compl (s : UpperSet α) : (s.Compl : Set α) = sᶜ :=
  rfl

@[simp]
theorem compl_compl (s : UpperSet α) : s.Compl.Compl = s :=
  UpperSet.ext <| compl_compl _

protected theorem compl_sup (s t : UpperSet α) : (s⊔t).Compl = s.Compl⊓t.Compl :=
  LowerSet.ext compl_sup

protected theorem compl_inf (s t : UpperSet α) : (s⊓t).Compl = s.Compl⊔t.Compl :=
  LowerSet.ext compl_inf

protected theorem compl_top : (⊤ : UpperSet α).Compl = ⊥ :=
  LowerSet.ext compl_univ

protected theorem compl_bot : (⊥ : UpperSet α).Compl = ⊤ :=
  LowerSet.ext compl_empty

protected theorem compl_Sup (S : Set (UpperSet α)) : (sup S).Compl = inf (UpperSet.compl '' S) :=
  LowerSet.ext <|
    compl_Sup'.trans <| by
      congr 1
      ext
      simp only [mem_image, exists_exists_and_eq_and, coe_compl]

protected theorem compl_Inf (S : Set (UpperSet α)) : (inf S).Compl = sup (UpperSet.compl '' S) :=
  LowerSet.ext <|
    compl_Inf'.trans <| by
      congr 1
      ext
      simp only [mem_image, exists_exists_and_eq_and, coe_compl]

protected theorem compl_supr (f : ι → UpperSet α) : (⨆ i, f i).Compl = ⨅ i, (f i).Compl :=
  LowerSet.ext <| by
    simp only [coe_compl, coe_supr, supr_eq_Union, compl_Union, LowerSet.coe_infi, infi_eq_Inter]

protected theorem compl_infi (f : ι → UpperSet α) : (⨅ i, f i).Compl = ⨆ i, (f i).Compl :=
  LowerSet.ext <| by
    simp only [coe_compl, coe_infi, infi_eq_Inter, compl_Inter, LowerSet.coe_supr, supr_eq_Union]

-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i j)
-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i j)
@[simp]
theorem compl_supr₂ (f : ∀ i, κ i → UpperSet α) : (⨆ (i) (j), f i j).Compl = ⨅ (i) (j), (f i j).Compl := by
  simp_rw [UpperSet.compl_supr]

-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i j)
-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i j)
@[simp]
theorem compl_infi₂ (f : ∀ i, κ i → UpperSet α) : (⨅ (i) (j), f i j).Compl = ⨆ (i) (j), (f i j).Compl := by
  simp_rw [UpperSet.compl_infi]

end UpperSet

namespace LowerSet

@[simp]
theorem coe_compl (s : LowerSet α) : (s.Compl : Set α) = sᶜ :=
  rfl

@[simp]
theorem compl_compl (s : LowerSet α) : s.Compl.Compl = s :=
  LowerSet.ext <| compl_compl _

protected theorem compl_sup (s t : LowerSet α) : (s⊔t).Compl = s.Compl⊓t.Compl :=
  UpperSet.ext compl_sup

protected theorem compl_inf (s t : LowerSet α) : (s⊓t).Compl = s.Compl⊔t.Compl :=
  UpperSet.ext compl_inf

protected theorem compl_top : (⊤ : LowerSet α).Compl = ⊥ :=
  UpperSet.ext compl_univ

protected theorem compl_bot : (⊥ : LowerSet α).Compl = ⊤ :=
  UpperSet.ext compl_empty

protected theorem compl_Sup (S : Set (LowerSet α)) : (sup S).Compl = inf (LowerSet.compl '' S) :=
  UpperSet.ext <|
    compl_Sup'.trans <| by
      congr 1
      ext
      simp only [mem_image, exists_exists_and_eq_and, coe_compl]

protected theorem compl_Inf (S : Set (LowerSet α)) : (inf S).Compl = sup (LowerSet.compl '' S) :=
  UpperSet.ext <|
    compl_Inf'.trans <| by
      congr 1
      ext
      simp only [mem_image, exists_exists_and_eq_and, coe_compl]

protected theorem compl_supr (f : ι → LowerSet α) : (⨆ i, f i).Compl = ⨅ i, (f i).Compl :=
  UpperSet.ext <| by
    simp only [coe_compl, coe_supr, supr_eq_Union, compl_Union, UpperSet.coe_infi, infi_eq_Inter]

protected theorem compl_infi (f : ι → LowerSet α) : (⨅ i, f i).Compl = ⨆ i, (f i).Compl :=
  UpperSet.ext <| by
    simp only [coe_compl, coe_infi, infi_eq_Inter, compl_Inter, UpperSet.coe_supr, supr_eq_Union]

-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i j)
-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i j)
@[simp]
theorem compl_supr₂ (f : ∀ i, κ i → LowerSet α) : (⨆ (i) (j), f i j).Compl = ⨅ (i) (j), (f i j).Compl := by
  simp_rw [LowerSet.compl_supr]

-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i j)
-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i j)
@[simp]
theorem compl_infi₂ (f : ∀ i, κ i → LowerSet α) : (⨅ (i) (j), f i j).Compl = ⨆ (i) (j), (f i j).Compl := by
  simp_rw [LowerSet.compl_infi]

end LowerSet

end Bundled

