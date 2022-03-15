/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
import Mathbin.Data.Real.Ennreal

/-!
# Real conjugate exponents

`p.is_conjugate_exponent q` registers the fact that the real numbers `p` and `q` are `> 1` and
satisfy `1/p + 1/q = 1`. This property shows up often in analysis, especially when dealing with
`L^p` spaces.

We make several basic facts available through dot notation in this situation.

We also introduce `p.conjugate_exponent` for `p / (p-1)`. When `p > 1`, it is conjugate to `p`.
-/


noncomputable section

namespace Real

/-- Two real exponents `p, q` are conjugate if they are `> 1` and satisfy the equality
`1/p + 1/q = 1`. This condition shows up in many theorems in analysis, notably related to `L^p`
norms. -/
structure IsConjugateExponent (p q : ℝ) : Prop where
  one_lt : 1 < p
  inv_add_inv_conj : 1 / p + 1 / q = 1

/-- The conjugate exponent of `p` is `q = p/(p-1)`, so that `1/p + 1/q = 1`. -/
def conjugateExponent (p : ℝ) : ℝ :=
  p / (p - 1)

namespace IsConjugateExponent

variable {p q : ℝ} (h : p.IsConjugateExponent q)

include h

/- Register several non-vanishing results following from the fact that `p` has a conjugate exponent
`q`: many computations using these exponents require clearing out denominators, which can be done
with `field_simp` given a proof that these denominators are non-zero, so we record the most usual
ones. -/
theorem pos : 0 < p :=
  lt_transₓ zero_lt_one h.one_lt

theorem nonneg : 0 ≤ p :=
  le_of_ltₓ h.Pos

theorem ne_zero : p ≠ 0 :=
  ne_of_gtₓ h.Pos

theorem sub_one_pos : 0 < p - 1 :=
  sub_pos.2 h.one_lt

theorem sub_one_ne_zero : p - 1 ≠ 0 :=
  ne_of_gtₓ h.sub_one_pos

theorem one_div_pos : 0 < 1 / p :=
  one_div_pos.2 h.Pos

theorem one_div_nonneg : 0 ≤ 1 / p :=
  le_of_ltₓ h.one_div_pos

theorem one_div_ne_zero : 1 / p ≠ 0 :=
  ne_of_gtₓ h.one_div_pos

theorem conj_eq : q = p / (p - 1) := by
  have := h.inv_add_inv_conj
  rw [← eq_sub_iff_add_eq', one_div, inv_eq_iff_inv_eq] at this
  field_simp [← this, h.ne_zero]

theorem conjugate_eq : conjugateExponent p = q :=
  h.conj_eq.symm

theorem sub_one_mul_conj : (p - 1) * q = p :=
  mul_comm q (p - 1) ▸ (eq_div_iff h.sub_one_ne_zero).1 h.conj_eq

theorem mul_eq_add : p * q = p + q := by
  simpa only [sub_mul, sub_eq_iff_eq_add, one_mulₓ] using h.sub_one_mul_conj

@[symm]
protected theorem symm : q.IsConjugateExponent p :=
  { one_lt := by
      rw [h.conj_eq]
      exact (one_lt_div h.sub_one_pos).mpr (sub_one_lt p),
    inv_add_inv_conj := by
      simpa [add_commₓ] using h.inv_add_inv_conj }

theorem div_conj_eq_sub_one : p / q = p - 1 := by
  field_simp [h.symm.ne_zero]
  rw [h.sub_one_mul_conj]

theorem one_lt_nnreal : 1 < Real.toNnreal p := by
  rw [← Real.to_nnreal_one, Real.to_nnreal_lt_to_nnreal_iff h.pos]
  exact h.one_lt

theorem inv_add_inv_conj_nnreal : 1 / Real.toNnreal p + 1 / Real.toNnreal q = 1 := by
  rw [← Real.to_nnreal_one, ← Real.to_nnreal_div' h.nonneg, ← Real.to_nnreal_div' h.symm.nonneg, ←
    Real.to_nnreal_add h.one_div_nonneg h.symm.one_div_nonneg, h.inv_add_inv_conj]

theorem inv_add_inv_conj_ennreal : 1 / Ennreal.ofReal p + 1 / Ennreal.ofReal q = 1 := by
  rw [← Ennreal.of_real_one, ← Ennreal.of_real_div_of_pos h.pos, ← Ennreal.of_real_div_of_pos h.symm.pos, ←
    Ennreal.of_real_add h.one_div_nonneg h.symm.one_div_nonneg, h.inv_add_inv_conj]

end IsConjugateExponent

theorem is_conjugate_exponent_iff {p q : ℝ} (h : 1 < p) : p.IsConjugateExponent q ↔ q = p / (p - 1) :=
  ⟨fun H => H.conj_eq, fun H =>
    ⟨h, by
      field_simp [H, ne_of_gtₓ (lt_transₓ zero_lt_one h)]⟩⟩

theorem is_conjugate_exponent_conjugate_exponent {p : ℝ} (h : 1 < p) : p.IsConjugateExponent (conjugateExponent p) :=
  (is_conjugate_exponent_iff h).2 rfl

end Real

