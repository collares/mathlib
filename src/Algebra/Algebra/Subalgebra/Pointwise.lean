/-
Copyright (c) 2021 Eric Weiser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathbin.Algebra.Algebra.Operations
import Mathbin.Algebra.Algebra.Subalgebra.Basic
import Mathbin.RingTheory.Subring.Pointwise

/-!
# Pointwise actions on subalgebras.

If `R'` acts on an `R`-algebra `A` (so that `R'` and `R` actions commute)
then we get an `R'` action on the collection of `R`-subalgebras.
-/


namespace Subalgebra

section Pointwise

variable {R : Type _} {A : Type _} [CommSemiringₓ R] [Semiringₓ A] [Algebra R A] (S : Subalgebra R A)

/-- As submodules, subalgebras are idempotent. -/
@[simp]
theorem mul_self : S.toSubmodule * S.toSubmodule = S.toSubmodule := by
  apply le_antisymmₓ
  · rw [Submodule.mul_le]
    intro y hy z hz
    exact mul_mem S hy hz
    
  · intro x hx1
    rw [← mul_oneₓ x]
    exact Submodule.mul_mem_mul hx1 (one_mem S)
    

variable {R' : Type _} [Semiringₓ R'] [MulSemiringAction R' A] [SmulCommClass R' R A]

/-- The action on a subalgebra corresponding to applying the action to every element.

This is available as an instance in the `pointwise` locale. -/
protected def pointwiseMulAction : MulAction R' (Subalgebra R A) where
  smul := fun a S => S.map (MulSemiringAction.toAlgHom _ _ a)
  one_smul := fun S => (congr_argₓ (fun f => S.map f) (AlgHom.ext <| one_smul R')).trans S.map_id
  mul_smul := fun a₁ a₂ S => (congr_argₓ (fun f => S.map f) (AlgHom.ext <| mul_smul _ _)).trans (S.map_map _ _).symm

localized [Pointwise] attribute [instance] Subalgebra.pointwiseMulAction

open_locale Pointwise

@[simp]
theorem coe_pointwise_smul (m : R') (S : Subalgebra R A) : ↑(m • S) = m • (S : Set A) :=
  rfl

@[simp]
theorem pointwise_smul_to_subsemiring (m : R') (S : Subalgebra R A) : (m • S).toSubsemiring = m • S.toSubsemiring :=
  rfl

@[simp]
theorem pointwise_smul_to_submodule (m : R') (S : Subalgebra R A) : (m • S).toSubmodule = m • S.toSubmodule :=
  rfl

@[simp]
theorem pointwise_smul_to_subring {R' R A : Type _} [Semiringₓ R'] [CommRingₓ R] [Ringₓ A] [MulSemiringAction R' A]
    [Algebra R A] [SmulCommClass R' R A] (m : R') (S : Subalgebra R A) : (m • S).toSubring = m • S.toSubring :=
  rfl

theorem smul_mem_pointwise_smul (m : R') (r : A) (S : Subalgebra R A) : r ∈ S → m • r ∈ m • S :=
  (Set.smul_mem_smul_set : _ → _ ∈ m • (S : Set A))

end Pointwise

end Subalgebra

