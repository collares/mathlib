/-
Copyright (c) 2021 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathbin.Data.MvPolynomial.Cardinal
import Mathbin.Data.MvPolynomial.Equiv

/-!
# Cardinality of Polynomial Ring

The reuslt in this file is that the cardinality of `polynomial R` is at most the maximum
of `#R` and `ω`.
-/


universe u

open_locale Cardinal Polynomial

open Cardinal

namespace Polynomial

theorem cardinal_mk_le_max {R : Type u} [CommSemiringₓ R] : # R[X] ≤ max (# R) ω :=
  calc
    # R[X] = # (MvPolynomial PUnit.{u + 1} R) := Cardinal.eq.2 ⟨(MvPolynomial.punitAlgEquiv.{u, u} R).toEquiv.symm⟩
    _ ≤ _ := MvPolynomial.cardinal_mk_le_max
    _ ≤ _ := by
      have : # PUnit.{u + 1} ≤ ω := le_of_ltₓ (lt_omega_iff_fintype.2 ⟨inferInstance⟩)
      rw [max_assocₓ, max_eq_rightₓ this]
    

end Polynomial

