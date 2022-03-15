/-
Copyright (c) 2021 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov, Alex J. Best
-/
import Mathbin.MeasureTheory.Group.Arithmetic

/-!
# Pointwise set operations on `measurable_set`s

In this file we prove several versions of the following fact: if `s` is a measurable set, then so is
`a • s`. Note that the pointwise product of two measurable sets need not be measurable, so there is
no `measurable_set.mul` etc.
-/


open_locale Pointwise

open Set

@[to_additive]
theorem MeasurableSet.const_smul {G α : Type _} [Groupₓ G] [MulAction G α] [MeasurableSpace G] [MeasurableSpace α]
    [HasMeasurableSmul G α] {s : Set α} (hs : MeasurableSet s) (a : G) : MeasurableSet (a • s) := by
  rw [← preimage_smul_inv]
  exact measurable_const_smul _ hs

theorem MeasurableSet.const_smul_of_ne_zero {G₀ α : Type _} [GroupWithZeroₓ G₀] [MulAction G₀ α] [MeasurableSpace G₀]
    [MeasurableSpace α] [HasMeasurableSmul G₀ α] {s : Set α} (hs : MeasurableSet s) {a : G₀} (ha : a ≠ 0) :
    MeasurableSet (a • s) := by
  rw [← preimage_smul_inv₀ ha]
  exact measurable_const_smul _ hs

theorem MeasurableSet.const_smul₀ {G₀ α : Type _} [GroupWithZeroₓ G₀] [Zero α] [MulActionWithZero G₀ α]
    [MeasurableSpace G₀] [MeasurableSpace α] [HasMeasurableSmul G₀ α] [MeasurableSingletonClass α] {s : Set α}
    (hs : MeasurableSet s) (a : G₀) : MeasurableSet (a • s) := by
  rcases eq_or_ne a 0 with (rfl | ha)
  exacts[(subsingleton_zero_smul_set s).MeasurableSet, hs.const_smul_of_ne_zero ha]

