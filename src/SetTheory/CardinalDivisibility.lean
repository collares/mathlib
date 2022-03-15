/-
Copyright (c) 2022 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
import Mathbin.SetTheory.CardinalOrdinal
import Mathbin.Algebra.IsPrimePow

/-!
# Cardinal Divisibility

We show basic results about divisibility in the cardinal numbers. This relation can be characterised
in the following simple way: if `a` and `b` are both less than `ω`, then `a ∣ b` iff they are
divisible as natural numbers. If `b` is greater than `ω`, then `a ∣ b` iff `a ≤ b`. This furthermore
shows that all infinite cardinals are prime; recall that `a * b = max a b` if `ω ≤ a * b`; therefore
`a ∣ b * c = a ∣ max b c` and therefore clearly either `a ∣ b` or `a ∣ c`. Note furthermore that
no infinite cardinal is irreducible (`cardinal.not_irreducible_of_omega_le`), showing that the
cardinal numbers do not form a `comm_cancel_monoid_with_zero`.

## Main results

* `cardinal.prime_of_omega_le`: a `cardinal` is prime if it is infinite.
* `cardinal.is_prime_iff`: a `cardinal` is prime iff it is infinite or a prime natural number.
* `cardinal.is_prime_pow_iff`: a `cardinal` is a prime power iff it is infinite or a natural number
  which is itself a prime power.

-/


namespace Cardinal

open_locale Cardinal

universe u

variable {a b : Cardinal.{u}} {n m : ℕ}

@[simp]
theorem is_unit_iff : IsUnit a ↔ a = 1 := by
  refine'
    ⟨fun h => _, by
      rintro rfl
      exact is_unit_one⟩
  rcases eq_or_ne a 0 with (rfl | ha)
  · exact (not_is_unit_zero h).elim
    
  rw [is_unit_iff_forall_dvd] at h
  cases' h 1 with t ht
  rw [eq_comm, mul_eq_one_iff'] at ht
  · exact ht.1
    
  all_goals
    rwa [one_le_iff_ne_zero]
  · rintro rfl
    rw [mul_zero] at ht
    exact zero_ne_one ht
    

instance : Unique Cardinal.{u}ˣ where
  default := 1
  uniq := fun a => Units.coe_eq_one.mp <| is_unit_iff.mp a.IsUnit

theorem le_of_dvd : ∀ {a b : Cardinal}, b ≠ 0 → a ∣ b → a ≤ b
  | a, _, b0, ⟨b, rfl⟩ => by
    simpa only [mul_oneₓ] using
      mul_le_mul_left'
        (one_le_iff_ne_zero.2 fun h : b = 0 => by
          simpa only [h, mul_zero] using b0)
        a

theorem dvd_of_le_of_omega_le (ha : a ≠ 0) (h : a ≤ b) (hb : ω ≤ b) : a ∣ b :=
  ⟨b, (mul_eq_right hb h ha).symm⟩

@[simp]
theorem prime_of_omega_le (ha : ω ≤ a) : Prime a := by
  refine' ⟨(omega_pos.trans_le ha).ne', _, fun b c hbc => _⟩
  · rw [is_unit_iff]
    exact (one_lt_omega.trans_le ha).ne'
    
  cases' eq_or_ne (b * c) 0 with hz hz
  · rcases mul_eq_zero.mp hz with (rfl | rfl) <;> simp
    
  wlog h : c ≤ b
  left
  have habc := le_of_dvd hz hbc
  rwa [mul_eq_max' <| ha.trans <| habc, max_def, if_pos h] at hbc

theorem not_irreducible_of_omega_le (ha : ω ≤ a) : ¬Irreducible a := by
  rw [irreducible_iff, not_and_distrib]
  refine' Or.inr fun h => _
  simpa [mul_omega_eq ha, is_unit_iff, (one_lt_omega.trans_le ha).ne', one_lt_omega.ne'] using h a ω

@[simp, norm_cast]
theorem nat_coe_dvd_iff : (n : Cardinal) ∣ m ↔ n ∣ m := by
  refine'
    ⟨_, fun ⟨h, ht⟩ =>
      ⟨h, by
        exact_mod_cast ht⟩⟩
  rintro ⟨k, hk⟩
  have : ↑m < ω := nat_lt_omega m
  rw [hk, mul_lt_omega_iff] at this
  rcases this with (h | h | ⟨-, hk'⟩)
  iterate 2 
    simp only [h, mul_zero, zero_mul, Nat.cast_eq_zero] at hk
    simp [hk]
  lift k to ℕ using hk'
  exact
    ⟨k, by
      exact_mod_cast hk⟩

@[simp]
theorem nat_is_prime_iff : Prime (n : Cardinal) ↔ n.Prime := by
  simp only [Prime, Nat.prime_iff]
  refine'
    and_congr
      (by
        simp )
      (and_congr _ ⟨fun h b c hbc => _, fun h b c hbc => _⟩)
  · simp only [is_unit_iff, Nat.is_unit_iff]
    exact_mod_cast Iff.rfl
    
  · exact_mod_cast
      h b c
        (by
          exact_mod_cast hbc)
    
  cases' lt_or_leₓ (b * c) ω with h' h'
  · rcases mul_lt_omega_iff.mp h' with (rfl | rfl | ⟨hb, hc⟩)
    · simp
      
    · simp
      
    lift b to ℕ using hb
    lift c to ℕ using hc
    exact_mod_cast
      h b c
        (by
          exact_mod_cast hbc)
    
  rcases omega_le_mul_iff.mp h' with ⟨hb, hc, hω⟩
  have hn : (n : Cardinal) ≠ 0 := by
    intro h
    rw [h, zero_dvd_iff, mul_eq_zero] at hbc
    cases hbc <;> contradiction
  wlog hω : ω ≤ b := hω using b c
  exact Or.inl (dvd_of_le_of_omega_le hn ((nat_lt_omega n).le.trans hω) hω)

theorem is_prime_iff {a : Cardinal} : Prime a ↔ ω ≤ a ∨ ∃ p : ℕ, a = p ∧ p.Prime := by
  cases' le_or_ltₓ ω a with h h
  · simp [h]
    
  lift a to ℕ using id h
  simp [not_le.mpr h]

theorem is_prime_pow_iff {a : Cardinal} : IsPrimePow a ↔ ω ≤ a ∨ ∃ n : ℕ, a = n ∧ IsPrimePow n := by
  by_cases' h : ω ≤ a
  · simp [h, (prime_of_omega_le h).IsPrimePow]
    
  lift a to ℕ using not_le.mp h
  simp only [h, Nat.cast_inj, exists_eq_left', false_orₓ, is_prime_pow_nat_iff]
  rw [is_prime_pow_def]
  refine'
    ⟨_, fun ⟨p, k, hp, hk, h⟩ =>
      ⟨p, k, nat_is_prime_iff.2 hp, by
        exact_mod_cast And.intro hk h⟩⟩
  rintro ⟨p, k, hp, hk, hpk⟩
  have key : _ ≤ p ^ k :=
    power_le_power_left hp.ne_zero
      (show (1 : Cardinal) ≤ k by
        exact_mod_cast hk)
  rw [power_one, hpk] at key
  lift p to ℕ using key.trans_lt (nat_lt_omega a)
  exact
    ⟨p, k, nat_is_prime_iff.mp hp, hk, by
      exact_mod_cast hpk⟩

end Cardinal

