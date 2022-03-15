/-
Copyright (c) 2021 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best
-/
import Mathbin.Data.List.BigOperators
import Mathbin.Algebra.Group.Commute

/-!
# Products / sums of lists of terms of a monoid

This file provides basic results about `list.prod` (definition in `data.list.defs`) in a monoid.
-/


open Nat

namespace List

universe u v

variable {α : Type u}

@[simp, to_additive]
theorem prod_repeat [Monoidₓ α] (a : α) (n : ℕ) : (repeat a n).Prod = a ^ n := by
  induction' n with n ih
  · rw [pow_zeroₓ]
    rfl
    
  · rw [List.repeat_succ, List.prod_cons, ih, pow_succₓ]
    

@[to_additive sum_eq_card_nsmul]
theorem prod_eq_pow_card [Monoidₓ α] (l : List α) (m : α) (h : ∀, ∀ x ∈ l, ∀, x = m) : l.Prod = m ^ l.length := by
  convert List.prod_repeat m l.length
  exact list.eq_repeat.mpr ⟨rfl, h⟩

@[to_additive sum_le_card_nsmul]
theorem prod_le_pow_card [OrderedCommMonoid α] (l : List α) (n : α) (h : ∀, ∀ x ∈ l, ∀, x ≤ n) :
    l.Prod ≤ n ^ l.length := by
  induction' l with y l IH
  · simp
    
  · rw [List.ball_consₓ] at h
    simpa [pow_succₓ] using mul_le_mul' h.1 (IH h.2)
    

@[to_additive]
theorem prod_commute [Monoidₓ α] (l : List α) (y : α) (h : ∀, ∀ x ∈ l, ∀, Commute y x) : Commute y l.Prod := by
  induction' l with y l IH
  · simp
    
  · rw [List.ball_consₓ] at h
    rw [List.prod_cons]
    exact Commute.mul_right h.1 (IH h.2)
    

end List

