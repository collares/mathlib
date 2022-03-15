/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson, Markus Himmel
-/
import Mathbin.Data.Nat.Bitwise
import Mathbin.SetTheory.Game.Impartial
import Mathbin.SetTheory.OrdinalArithmetic

/-!
# Nim and the Sprague-Grundy theorem

This file contains the definition for nim for any ordinal `O`. In the game of `nim O₁` both players
may move to `nim O₂` for any `O₂ < O₁`.
We also define a Grundy value for an impartial game `G` and prove the Sprague-Grundy theorem, that
`G` is equivalent to `nim (grundy_value G)`.
Finally, we compute the sum of finite Grundy numbers: if `G` and `H` have Grundy values `n` and `m`,
where `n` and `m` are natural numbers, then `G + H` has the Grundy value `n xor m`.

## Implementation details

The pen-and-paper definition of nim defines the possible moves of `nim O` to be `{O' | O' < O}`.
However, this definition does not work for us because it would make the type of nim
`ordinal.{u} → pgame.{u + 1}`, which would make it impossible for us to state the Sprague-Grundy
theorem, since that requires the type of `nim` to be `ordinal.{u} → pgame.{u}`. For this reason, we
instead use `O.out.α` for the possible moves, which makes proofs significantly more messy and
tedious, but avoids the universe bump.

The lemma `nim_def` is somewhat prone to produce "motive is not type correct" errors. If you run
into this problem, you may find the lemmas `exists_ordinal_move_left_eq` and `exists_move_left_eq`
useful.

-/


universe u

/-- `ordinal.out'` has the sole purpose of making `nim` computable. It performs the same job as
  `quotient.out` but is specific to ordinals. -/
def Ordinal.out' (o : Ordinal) : WellOrder :=
  ⟨o.out.α, (· < ·), o.out.wo⟩

/-- The definition of single-heap nim, which can be viewed as a pile of stones where each player can
  take a positive number of stones from it on their turn. -/
def nim : Ordinal → Pgame
  | O₁ =>
    let f := fun O₂ =>
      have hwf : Ordinal.typein O₁.out'.R O₂ < O₁ := Ordinal.typein_lt_self O₂
      nim (Ordinal.typein O₁.out'.R O₂)
    ⟨O₁.out'.α, O₁.out'.α, f, f⟩

namespace Pgame

-- mathport name: «expr ≈ »
local infixl:0 " ≈ " => Equiv

namespace nim

open Ordinal

theorem nim_def (O : Ordinal) :
    nim O =
      Pgame.mk O.out.α O.out.α (fun O₂ => nim (Ordinal.typein (· < ·) O₂)) fun O₂ => nim (Ordinal.typein (· < ·) O₂) :=
  by
  rw [nim]
  rfl

instance nim_impartial : ∀ O : Ordinal, Impartial (nim O)
  | O => by
    rw [impartial_def, nim_def, neg_def]
    constructor
    constructor <;> rw [Pgame.le_def]
    all_goals
      refine'
        ⟨fun i =>
          let hwf := Ordinal.typein_lt_self i
          _,
          fun j =>
          let hwf := Ordinal.typein_lt_self j
          _⟩
    · exact Or.inl ⟨i, (@impartial.neg_equiv_self _ <| nim_impartial <| typein (· < ·) i).1⟩
      
    · exact Or.inr ⟨j, (@impartial.neg_equiv_self _ <| nim_impartial <| typein (· < ·) j).1⟩
      
    · exact Or.inl ⟨i, (@impartial.neg_equiv_self _ <| nim_impartial <| typein (· < ·) i).2⟩
      
    · exact Or.inr ⟨j, (@impartial.neg_equiv_self _ <| nim_impartial <| typein (· < ·) j).2⟩
      
    · exact nim_impartial (typein (· < ·) i)
      
    · exact nim_impartial (typein (· < ·) j)
      

theorem exists_ordinal_move_left_eq (O : Ordinal) : ∀ i, ∃ O' < O, (nim O).moveLeft i = nim O' := by
  rw [nim_def]
  exact fun i => ⟨_, ⟨Ordinal.typein_lt_self i, rfl⟩⟩

theorem exists_move_left_eq {O : Ordinal} : ∀, ∀ O' < O, ∀, ∃ i, (nim O).moveLeft i = nim O' := by
  rw [nim_def]
  exact fun _ h =>
    ⟨(Ordinal.principalSegOut h).top, by
      simp ⟩

theorem zero_first_loses : (nim (0 : Ordinal)).FirstLoses := by
  rw [impartial.first_loses_symm, nim_def, le_def_lt]
  exact ⟨@isEmptyElim (0 : Ordinal).out.α _ _, @isEmptyElim Pempty _ _⟩

theorem non_zero_first_wins {O : Ordinal} (hO : O ≠ 0) : (nim O).FirstWins := by
  rw [impartial.first_wins_symm, nim_def, lt_def_le]
  rw [← Ordinal.pos_iff_ne_zero] at hO
  exact
    Or.inr
      ⟨(Ordinal.principalSegOut hO).top, by
        simpa using zero_first_loses.1⟩

theorem sum_first_loses_iff_eq (O₁ O₂ : Ordinal) : (nim O₁ + nim O₂).FirstLoses ↔ O₁ = O₂ := by
  constructor
  · contrapose
    intro h
    rw [impartial.not_first_loses]
    wlog h' : O₁ ≤ O₂ using O₁ O₂, O₂ O₁
    · exact Ordinal.le_total O₁ O₂
      
    · have h : O₁ < O₂ := lt_of_le_of_neₓ h' h
      rw [impartial.first_wins_symm', lt_def_le, nim_def O₂]
      refine' Or.inl ⟨(left_moves_add (nim O₁) _).symm (Sum.inr _), _⟩
      · exact (Ordinal.principalSegOut h).top
        
      · simpa using (impartial.add_self (nim O₁)).2
        
      
    · exact first_wins_of_equiv add_comm_equiv (this (Ne.symm h))
      
    
  · rintro rfl
    exact impartial.add_self (nim O₁)
    

theorem sum_first_wins_iff_neq (O₁ O₂ : Ordinal) : (nim O₁ + nim O₂).FirstWins ↔ O₁ ≠ O₂ := by
  rw [iff_not_comm, impartial.not_first_wins, sum_first_loses_iff_eq]

theorem equiv_iff_eq (O₁ O₂ : Ordinal) : (nim O₁ ≈ nim O₂) ↔ O₁ = O₂ :=
  ⟨fun h =>
    (sum_first_loses_iff_eq _ _).1 <| by
      rw [first_loses_of_equiv_iff (add_congr h (equiv_refl _)), sum_first_loses_iff_eq],
    by
    rintro rfl
    rfl⟩

end nim

/-- This definition will be used in the proof of the Sprague-Grundy theorem. It takes a function
  from some type to ordinals and returns a nonempty set of ordinals with empty intersection with
  the image of the function. It is guaranteed that the smallest ordinal not in the image will be
  in the set, i.e. we can use this to find the mex. -/
def Nonmoves {α : Type u} (M : α → Ordinal.{u}) : Set Ordinal.{u} :=
  Set.Range Mᶜ

theorem nonmoves_nonempty {α : Type u} (M : α → Ordinal.{u}) : Set.Nonempty (Nonmoves M) :=
  ⟨_, Ordinal.lsub_nmem_range.{u, u} M⟩

/-- The Grundy value of an impartial game, the ordinal which corresponds to the game of nim that the
 game is equivalent to -/
noncomputable def grundyValue : ∀ G : Pgame.{u} [G.Impartial], Ordinal.{u}
  | G => fun hG => Inf (nonmoves fun i => grundy_value (G.move_left i))

theorem grundy_value_def (G : Pgame) [G.Impartial] :
    grundyValue G = inf (Nonmoves fun i => grundyValue (G.moveLeft i)) := by
  rw [grundy_value]

/-- The Sprague-Grundy theorem which states that every impartial game is equivalent to a game of
 nim, namely the game of nim corresponding to the games Grundy value -/
theorem equiv_nim_grundy_value : ∀ G : Pgame.{u} [G.Impartial], G ≈ nim (grundy_value G)
  | G => by
    intro hG
    rw [impartial.equiv_iff_sum_first_loses, ← impartial.no_good_left_moves_iff_first_loses]
    intro i
    equiv_rw left_moves_add G (nim (grundy_value G))  at i
    cases' i with i₁ i₂
    · rw [add_move_left_inl]
      apply first_wins_of_equiv (add_congr (equiv_nim_grundy_value (G.move_left i₁)).symm (equiv_refl _))
      rw [nim.sum_first_wins_iff_neq]
      intro heq
      rw [eq_comm, grundy_value_def G] at heq
      have h := Inf_mem (nonmoves_nonempty _)
      rw [HEq] at h
      have hcontra :
        ∃ i' : G.left_moves,
          (fun i'' : G.left_moves => grundy_value (G.move_left i'')) i' = grundy_value (G.move_left i₁) :=
        ⟨i₁, rfl⟩
      contradiction
      
    · rw [add_move_left_inr, ← impartial.good_left_move_iff_first_wins]
      revert i₂
      rw [nim.nim_def]
      intro i₂
      have h' :
        ∃ i : G.left_moves, grundy_value (G.move_left i) = Ordinal.typein (Quotientₓ.out (grundy_value G)).R i₂ := by
        revert i₂
        rw [grundy_value_def]
        intro i₂
        have hnotin : _ ∉ _ := fun hin => (le_not_le_of_ltₓ (Ordinal.typein_lt_self i₂)).2 (cInf_le' hin)
        simpa [nonmoves] using hnotin
      cases' h' with i hi
      use (left_moves_add _ _).symm (Sum.inl i)
      rw [add_move_left_inl, move_left_mk]
      apply first_loses_of_equiv (add_congr (equiv_symm (equiv_nim_grundy_value (G.move_left i))) (equiv_refl _))
      simpa only [hi] using impartial.add_self (nim (grundy_value (G.move_left i)))
      

theorem equiv_nim_iff_grundy_value_eq (G : Pgame) [G.Impartial] (O : Ordinal) : (G ≈ nim O) ↔ grundyValue G = O :=
  ⟨by
    intro h
    rw [← nim.equiv_iff_eq]
    exact equiv_trans (equiv_symm (equiv_nim_grundy_value G)) h, by
    rintro rfl
    exact equiv_nim_grundy_value G⟩

theorem Nim.grundy_value (O : Ordinal.{u}) : grundyValue (nim O) = O := by
  rw [← equiv_nim_iff_grundy_value_eq]

theorem equiv_iff_grundy_value_eq (G H : Pgame) [G.Impartial] [H.Impartial] : (G ≈ H) ↔ grundyValue G = grundyValue H :=
  (equiv_congr_left.1 (equiv_nim_grundy_value H) _).trans <| equiv_nim_iff_grundy_value_eq _ _

theorem grundy_value_zero : grundyValue 0 = 0 := by
  rw [(equiv_iff_grundy_value_eq 0 (nim 0)).1 (equiv_symm nim.zero_first_loses), nim.grundy_value]

theorem equiv_zero_iff_grundy_value (G : Pgame) [G.Impartial] : (G ≈ 0) ↔ grundyValue G = 0 := by
  rw [equiv_iff_grundy_value_eq, grundy_value_zero]

theorem grundy_value_nim_add_nim (n m : ℕ) : grundyValue (nim n + nim m) = Nat.lxor n m := by
  induction' n using Nat.strong_induction_onₓ with n hn generalizing m
  induction' m using Nat.strong_induction_onₓ with m hm
  rw [grundy_value_def]
  -- We want to show that `n xor m` is the smallest unreachable Grundy value. We will do this in two
  -- steps:
  -- h₀: `n xor m` is not a reachable grundy number.
  -- h₁: every Grundy number strictly smaller than `n xor m` is reachable.
  have h₀ : (Nat.lxor n m : Ordinal) ∈ nonmoves fun i => grundy_value ((nim n + nim m).moveLeft i) := by
    -- To show that `n xor m` is unreachable, we show that every move produces a Grundy number
    -- different from `n xor m`.
    rw [nonmoves, Set.mem_compl_eq, Set.mem_range, not_exists]
    equiv_rw left_moves_add _ _
    -- The move operates either on the left pile or on the right pile.
    rintro (a | a)
    all_goals
      -- One of the piles is reduced to `k` stones, with `k < n` or `k < m`.
      obtain ⟨ok, ⟨hk, hk'⟩⟩ := nim.exists_ordinal_move_left_eq _ a
      obtain ⟨k, rfl⟩ := Ordinal.lt_omega.1 (lt_transₓ hk (Ordinal.nat_lt_omega _))
      replace hk := Ordinal.nat_cast_lt.1 hk
      -- Thus, the problem is reduced to computing the Grundy value of `nim n + nim k` or
      -- `nim k + nim m`, both of which can be dealt with using an inductive hypothesis.
      simp only [hk', add_move_left_inl, add_move_left_inr, id]
      first |
        rw [hn _ hk]|
        rw [hm _ hk]
      -- But of course xor is injective, so if we change one of the arguments, we will not get the
      -- same value again.
      intro h
      rw [Ordinal.nat_cast_inj] at h
      try
        rw [Nat.lxor_comm n k, Nat.lxor_comm n m] at h
      exact hk.ne (Nat.lxor_left_inj h)
  have h₁ : ∀ u : Ordinal, u < Nat.lxor n m → u ∉ nonmoves fun i => grundy_value ((nim n + nim m).moveLeft i) := by
    -- Take any natural number `u` less than `n xor m`.
    intro ou hu
    obtain ⟨u, rfl⟩ := Ordinal.lt_omega.1 (lt_transₓ hu (Ordinal.nat_lt_omega _))
    replace hu := Ordinal.nat_cast_lt.1 hu
    -- Our goal is to produce a move that gives the Grundy value `u`.
    rw [nonmoves, Set.mem_compl_eq, Set.mem_range, not_not]
    -- By a lemma about xor, either `u xor m < n` or `u xor n < m`.
    have : Nat.lxor u (Nat.lxor n m) ≠ 0 := by
      intro h
      rw [Nat.lxor_eq_zero] at h
      linarith
    rcases Nat.lxor_trichotomy this with (h | h | h)
    · linarith
      
    -- Therefore, we can play the corresponding move, and by the inductive hypothesis the new state
    -- is `(u xor m) xor m = u` or `n xor (u xor n) = u` as required.
    · obtain ⟨i, hi⟩ := nim.exists_move_left_eq _ (Ordinal.nat_cast_lt.2 h)
      refine' ⟨(left_moves_add _ _).symm (Sum.inl i), _⟩
      simp only [hi, add_move_left_inl]
      rw [hn _ h, Nat.lxor_assoc, Nat.lxor_self, Nat.lxor_zero]
      
    · obtain ⟨i, hi⟩ := nim.exists_move_left_eq _ (Ordinal.nat_cast_lt.2 h)
      refine' ⟨(left_moves_add _ _).symm (Sum.inr i), _⟩
      simp only [hi, add_move_left_inr]
      rw [hm _ h, Nat.lxor_comm, Nat.lxor_assoc, Nat.lxor_self, Nat.lxor_zero]
      
  -- We are done!
  apply (cInf_le' h₀).antisymm
  contrapose! h₁
  exact ⟨_, ⟨h₁, Inf_mem (nonmoves_nonempty _)⟩⟩

theorem nim_add_nim_equiv {n m : ℕ} : nim n + nim m ≈ nim (Nat.lxor n m) := by
  rw [equiv_nim_iff_grundy_value_eq, grundy_value_nim_add_nim]

theorem grundy_value_add (G H : Pgame) [G.Impartial] [H.Impartial] {n m : ℕ} (hG : grundyValue G = n)
    (hH : grundyValue H = m) : grundyValue (G + H) = Nat.lxor n m := by
  rw [← nim.grundy_value (Nat.lxor n m), ← equiv_iff_grundy_value_eq]
  refine' equiv_trans _ nim_add_nim_equiv
  convert add_congr (equiv_nim_grundy_value G) (equiv_nim_grundy_value H) <;> simp only [hG, hH]

end Pgame

