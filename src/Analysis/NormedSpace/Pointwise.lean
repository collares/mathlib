/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathbin.Analysis.Normed.Group.Pointwise
import Mathbin.Analysis.Normed.Group.AddTorsor
import Mathbin.Analysis.NormedSpace.Basic
import Mathbin.Topology.MetricSpace.HausdorffDistance

/-!
# Properties of pointwise scalar multiplication of sets in normed spaces.

We explore the relationships between scalar multiplication of sets in vector spaces, and the norm.
Notably, we express arbitrary balls as rescaling of other balls, and we show that the
multiplication of bounded sets remain bounded.
-/


open Metric Set

open_locale Pointwise TopologicalSpace

variable {𝕜 E : Type _} [NormedField 𝕜]

section SemiNormedGroup

variable [SemiNormedGroup E] [NormedSpace 𝕜 E]

theorem smul_ball {c : 𝕜} (hc : c ≠ 0) (x : E) (r : ℝ) : c • Ball x r = Ball (c • x) (∥c∥ * r) := by
  ext y
  rw [mem_smul_set_iff_inv_smul_mem₀ hc]
  conv_lhs => rw [← inv_smul_smul₀ hc x]
  simp [← div_eq_inv_mul, div_lt_iff (norm_pos_iff.2 hc), mul_comm _ r, dist_smul]

theorem smul_unit_ball {c : 𝕜} (hc : c ≠ 0) : c • Ball (0 : E) (1 : ℝ) = Ball (0 : E) ∥c∥ := by
  rw [smul_ball hc, smul_zero, mul_oneₓ]

theorem smul_sphere' {c : 𝕜} (hc : c ≠ 0) (x : E) (r : ℝ) : c • Sphere x r = Sphere (c • x) (∥c∥ * r) := by
  ext y
  rw [mem_smul_set_iff_inv_smul_mem₀ hc]
  conv_lhs => rw [← inv_smul_smul₀ hc x]
  simp only [mem_sphere, dist_smul, norm_inv, ← div_eq_inv_mul, div_eq_iff (norm_pos_iff.2 hc).ne', mul_comm r]

theorem smul_closed_ball' {c : 𝕜} (hc : c ≠ 0) (x : E) (r : ℝ) : c • ClosedBall x r = ClosedBall (c • x) (∥c∥ * r) := by
  simp only [← ball_union_sphere, Set.smul_set_union, smul_ball hc, smul_sphere' hc]

theorem Metric.Bounded.smul {s : Set E} (hs : Bounded s) (c : 𝕜) : Bounded (c • s) := by
  obtain ⟨R, hR⟩ : ∃ R : ℝ, ∀, ∀ x ∈ s, ∀, ∥x∥ ≤ R := hs.exists_norm_le
  refine' bounded_iff_exists_norm_le.2 ⟨∥c∥ * R, _⟩
  intro z hz
  obtain ⟨y, ys, rfl⟩ : ∃ y : E, y ∈ s ∧ c • y = z := mem_smul_set.1 hz
  calc ∥c • y∥ = ∥c∥ * ∥y∥ := norm_smul _ _ _ ≤ ∥c∥ * R := mul_le_mul_of_nonneg_left (hR y ys) (norm_nonneg _)

/-- If `s` is a bounded set, then for small enough `r`, the set `{x} + r • s` is contained in any
fixed neighborhood of `x`. -/
theorem eventually_singleton_add_smul_subset {x : E} {s : Set E} (hs : Bounded s) {u : Set E} (hu : u ∈ 𝓝 x) :
    ∀ᶠ r in 𝓝 (0 : 𝕜), {x} + r • s ⊆ u := by
  obtain ⟨ε, εpos, hε⟩ : ∃ (ε : _)(hε : 0 < ε), closed_ball x ε ⊆ u := nhds_basis_closed_ball.mem_iff.1 hu
  obtain ⟨R, Rpos, hR⟩ : ∃ R : ℝ, 0 < R ∧ s ⊆ closed_ball 0 R := hs.subset_ball_lt 0 0
  have : Metric.ClosedBall (0 : 𝕜) (ε / R) ∈ 𝓝 (0 : 𝕜) := closed_ball_mem_nhds _ (div_pos εpos Rpos)
  filter_upwards [this] with r hr
  simp only [image_add_left, singleton_add]
  intro y hy
  obtain ⟨z, zs, hz⟩ : ∃ z : E, z ∈ s ∧ r • z = -x + y := by
    simpa [mem_smul_set] using hy
  have I : ∥r • z∥ ≤ ε :=
    calc
      ∥r • z∥ = ∥r∥ * ∥z∥ := norm_smul _ _
      _ ≤ ε / R * R :=
        mul_le_mul (mem_closed_ball_zero_iff.1 hr) (mem_closed_ball_zero_iff.1 (hR zs)) (norm_nonneg _)
          (div_pos εpos Rpos).le
      _ = ε := by
        field_simp [Rpos.ne']
      
  have : y = x + r • z := by
    simp only [hz, add_neg_cancel_left]
  apply hε
  simpa only [this, dist_eq_norm, add_sub_cancel', mem_closed_ball] using I

theorem set_smul_mem_nhds_zero {s : Set E} (hs : s ∈ 𝓝 (0 : E)) {c : 𝕜} (hc : c ≠ 0) : c • s ∈ 𝓝 (0 : E) := by
  obtain ⟨ε, εpos, hε⟩ : ∃ (ε : ℝ)(H : 0 < ε), ball 0 ε ⊆ s := Metric.mem_nhds_iff.1 hs
  have : c • ball (0 : E) ε ∈ 𝓝 (0 : E) := by
    rw [smul_ball hc, smul_zero]
    exact
      ball_mem_nhds _
        (mul_pos
          (by
            simpa using hc)
          εpos)
  exact Filter.mem_of_superset this ((set_smul_subset_set_smul_iff₀ hc).2 hε)

theorem set_smul_mem_nhds_zero_iff (s : Set E) {c : 𝕜} (hc : c ≠ 0) : c • s ∈ 𝓝 (0 : E) ↔ s ∈ 𝓝 (0 : E) := by
  refine' ⟨fun h => _, fun h => set_smul_mem_nhds_zero h hc⟩
  convert set_smul_mem_nhds_zero h (inv_ne_zero hc)
  rw [smul_smul, inv_mul_cancel hc, one_smul]

/-- Any ball is the image of a ball centered at the origin under a shift. -/
theorem vadd_ball_zero (x : E) (r : ℝ) : x +ᵥ Ball 0 r = Ball x r := by
  rw [vadd_ball, vadd_eq_add, add_zeroₓ]

/-- Any closed ball is the image of a closed ball centered at the origin under a shift. -/
theorem vadd_closed_ball_zero (x : E) (r : ℝ) : x +ᵥ ClosedBall 0 r = ClosedBall x r := by
  rw [vadd_closed_ball, vadd_eq_add, add_zeroₓ]

variable [NormedSpace ℝ E]

/-- In a real normed space, the image of the unit ball under scalar multiplication by a positive
constant `r` is the ball of radius `r`. -/
theorem smul_unit_ball_of_pos {r : ℝ} (hr : 0 < r) : r • Ball 0 1 = Ball (0 : E) r := by
  rw [smul_unit_ball hr.ne', Real.norm_of_nonneg hr.le]

end SemiNormedGroup

section NormedGroup

variable [NormedGroup E] [NormedSpace 𝕜 E]

theorem smul_closed_ball (c : 𝕜) (x : E) {r : ℝ} (hr : 0 ≤ r) : c • ClosedBall x r = ClosedBall (c • x) (∥c∥ * r) := by
  rcases eq_or_ne c 0 with (rfl | hc)
  · simp [hr, zero_smul_set, Set.singleton_zero, ← nonempty_closed_ball]
    
  · exact smul_closed_ball' hc x r
    

theorem smul_closed_unit_ball (c : 𝕜) : c • ClosedBall (0 : E) (1 : ℝ) = ClosedBall (0 : E) ∥c∥ := by
  rw [smul_closed_ball _ _ zero_le_one, smul_zero, mul_oneₓ]

variable [NormedSpace ℝ E]

/-- In a real normed space, the image of the unit closed ball under multiplication by a nonnegative
number `r` is the closed ball of radius `r` with center at the origin. -/
theorem smul_closed_unit_ball_of_nonneg {r : ℝ} (hr : 0 ≤ r) : r • ClosedBall 0 1 = ClosedBall (0 : E) r := by
  rw [smul_closed_unit_ball, Real.norm_of_nonneg hr]

/-- In a nontrivial real normed space, a sphere is nonempty if and only if its radius is
nonnegative. -/
@[simp]
theorem NormedSpace.sphere_nonempty [Nontrivial E] {x : E} {r : ℝ} : (Sphere x r).Nonempty ↔ 0 ≤ r := by
  obtain ⟨y, hy⟩ := exists_ne x
  refine'
    ⟨fun h => nonempty_closed_ball.1 (h.mono sphere_subset_closed_ball), fun hr => ⟨r • ∥y - x∥⁻¹ • (y - x) + x, _⟩⟩
  have : ∥y - x∥ ≠ 0 := by
    simpa [sub_eq_zero]
  simp [norm_smul, this, Real.norm_of_nonneg hr]

theorem smul_sphere [Nontrivial E] (c : 𝕜) (x : E) {r : ℝ} (hr : 0 ≤ r) : c • Sphere x r = Sphere (c • x) (∥c∥ * r) :=
  by
  rcases eq_or_ne c 0 with (rfl | hc)
  · simp [zero_smul_set, Set.singleton_zero, hr]
    
  · exact smul_sphere' hc x r
    

/-- Any ball `metric.ball x r`, `0 < r` is the image of the unit ball under `λ y, x + r • y`. -/
theorem affinity_unit_ball {r : ℝ} (hr : 0 < r) (x : E) : x +ᵥ r • Ball 0 1 = Ball x r := by
  rw [smul_unit_ball_of_pos hr, vadd_ball_zero]

/-- Any closed ball `metric.closed_ball x r`, `0 ≤ r` is the image of the unit closed ball under
`λ y, x + r • y`. -/
theorem affinity_unit_closed_ball {r : ℝ} (hr : 0 ≤ r) (x : E) : x +ᵥ r • ClosedBall 0 1 = ClosedBall x r := by
  rw [smul_closed_unit_ball, Real.norm_of_nonneg hr, vadd_closed_ball_zero]

end NormedGroup

