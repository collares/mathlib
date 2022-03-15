/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl
-/
import Mathbin.Analysis.Normed.NormedField
import Mathbin.Analysis.Normed.Group.InfiniteSum
import Mathbin.Data.Matrix.Basic
import Mathbin.Topology.Sequences

/-!
# Normed spaces

In this file we define (semi)normed spaces and algebras. We also prove some theorems
about these definitions.
-/


variable {α : Type _} {β : Type _} {γ : Type _} {ι : Type _}

noncomputable section

open Filter Metric

open_locale TopologicalSpace BigOperators Nnreal Ennreal uniformity Pointwise

section SemiNormedGroup

section Prio

-- ././Mathport/Syntax/Translate/Basic.lean:210:40: warning: unsupported option extends_priority
set_option extends_priority 920

/-- A normed space over a normed field is a vector space endowed with a norm which satisfies the
equality `∥c • x∥ = ∥c∥ ∥x∥`. We require only `∥c • x∥ ≤ ∥c∥ ∥x∥` in the definition, then prove
`∥c • x∥ = ∥c∥ ∥x∥` in `norm_smul`.

Note that since this requires `semi_normed_group` and not `normed_group`, this typeclass can be
used for "semi normed spaces" too, just as `module` can be used for "semi modules". -/
-- Here, we set a rather high priority for the instance `[normed_space α β] : module α β`
-- to take precedence over `semiring.to_module` as this leads to instance paths with better
-- unification properties.
class NormedSpace (α : Type _) (β : Type _) [NormedField α] [SemiNormedGroup β] extends Module α β where
  norm_smul_le : ∀ a : α b : β, ∥a • b∥ ≤ ∥a∥ * ∥b∥

end Prio

variable [NormedField α] [SemiNormedGroup β]

-- see Note [lower instance priority]
instance (priority := 100) NormedSpace.has_bounded_smul [NormedSpace α β] : HasBoundedSmul α β where
  dist_smul_pair' := fun x y₁ y₂ => by
    simpa [dist_eq_norm, smul_sub] using NormedSpace.norm_smul_le x (y₁ - y₂)
  dist_pair_smul' := fun x₁ x₂ y => by
    simpa [dist_eq_norm, sub_smul] using NormedSpace.norm_smul_le (x₁ - x₂) y

instance NormedField.toNormedSpace : NormedSpace α α where
  norm_smul_le := fun a b => le_of_eqₓ (norm_mul a b)

theorem norm_smul [NormedSpace α β] (s : α) (x : β) : ∥s • x∥ = ∥s∥ * ∥x∥ := by
  by_cases' h : s = 0
  · simp [h]
    
  · refine' le_antisymmₓ (NormedSpace.norm_smul_le s x) _
    calc ∥s∥ * ∥x∥ = ∥s∥ * ∥s⁻¹ • s • x∥ := by
        rw [inv_smul_smul₀ h]_ ≤ ∥s∥ * (∥s⁻¹∥ * ∥s • x∥) :=
        mul_le_mul_of_nonneg_left (NormedSpace.norm_smul_le _ _) (norm_nonneg _)_ = ∥s • x∥ := by
        rw [norm_inv, ← mul_assoc, mul_inv_cancel (mt norm_eq_zero.1 h), one_mulₓ]
    

@[simp]
theorem abs_norm_eq_norm (z : β) : abs ∥z∥ = ∥z∥ :=
  (abs_eq (norm_nonneg z)).mpr (Or.inl rfl)

theorem dist_smul [NormedSpace α β] (s : α) (x y : β) : dist (s • x) (s • y) = ∥s∥ * dist x y := by
  simp only [dist_eq_norm, (norm_smul _ _).symm, smul_sub]

theorem nnnorm_smul [NormedSpace α β] (s : α) (x : β) : ∥s • x∥₊ = ∥s∥₊ * ∥x∥₊ :=
  Nnreal.eq <| norm_smul s x

theorem nndist_smul [NormedSpace α β] (s : α) (x y : β) : nndist (s • x) (s • y) = ∥s∥₊ * nndist x y :=
  Nnreal.eq <| dist_smul s x y

theorem lipschitz_with_smul [NormedSpace α β] (s : α) : LipschitzWith ∥s∥₊ ((· • ·) s : β → β) :=
  lipschitz_with_iff_dist_le_mul.2 fun x y => by
    rw [dist_smul, coe_nnnorm]

theorem norm_smul_of_nonneg [NormedSpace ℝ β] {t : ℝ} (ht : 0 ≤ t) (x : β) : ∥t • x∥ = t * ∥x∥ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]

variable {E : Type _} [SemiNormedGroup E] [NormedSpace α E]

variable {F : Type _} [SemiNormedGroup F] [NormedSpace α F]

theorem eventually_nhds_norm_smul_sub_lt (c : α) (x : E) {ε : ℝ} (h : 0 < ε) : ∀ᶠ y in 𝓝 x, ∥c • (y - x)∥ < ε :=
  have : Tendsto (fun y => ∥c • (y - x)∥) (𝓝 x) (𝓝 0) :=
    ((continuous_id.sub continuous_const).const_smul _).norm.tendsto' _ _
      (by
        simp )
  this.Eventually (gt_mem_nhds h)

theorem closure_ball [NormedSpace ℝ E] (x : E) {r : ℝ} (hr : 0 < r) : Closure (Ball x r) = ClosedBall x r := by
  refine' Set.Subset.antisymm closure_ball_subset_closed_ball fun y hy => _
  have : ContinuousWithinAt (fun c : ℝ => c • (y - x) + x) (Set.Ico 0 1) 1 :=
    ((continuous_id.smul continuous_const).add continuous_const).ContinuousWithinAt
  convert this.mem_closure _ _
  · rw [one_smul, sub_add_cancel]
    
  · simp [closure_Ico (@zero_ne_one ℝ _ _), zero_le_one]
    
  · rintro c ⟨hc0, hc1⟩
    rw [mem_ball, dist_eq_norm, add_sub_cancel, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc0, mul_comm, ← mul_oneₓ r]
    rw [mem_closed_ball, dist_eq_norm] at hy
    apply mul_lt_mul' <;> assumption
    

theorem frontier_ball [NormedSpace ℝ E] (x : E) {r : ℝ} (hr : 0 < r) : Frontier (Ball x r) = Sphere x r := by
  rw [Frontier, closure_ball x hr, is_open_ball.interior_eq]
  ext x
  exact (@eq_iff_le_not_lt ℝ _ _ _).symm

theorem interior_closed_ball [NormedSpace ℝ E] (x : E) {r : ℝ} (hr : r ≠ 0) : Interior (ClosedBall x r) = Ball x r := by
  cases' hr.lt_or_lt with hr hr
  · rw [closed_ball_eq_empty.2 hr, ball_eq_empty.2 hr.le, interior_empty]
    
  refine' Set.Subset.antisymm _ ball_subset_interior_closed_ball
  intro y hy
  rcases(mem_closed_ball.1 <| interior_subset hy).lt_or_eq with (hr | rfl)
  · exact hr
    
  set f : ℝ → E := fun c : ℝ => c • (y - x) + x
  suffices f ⁻¹' closed_ball x (dist y x) ⊆ Set.Icc (-1) 1 by
    have hfc : Continuous f := (continuous_id.smul continuous_const).add continuous_const
    have hf1 : (1 : ℝ) ∈ f ⁻¹' Interior (closed_ball x <| dist y x) := by
      simpa [f]
    have h1 : (1 : ℝ) ∈ Interior (Set.Icc (-1 : ℝ) 1) :=
      interior_mono this (preimage_interior_subset_interior_preimage hfc hf1)
    contrapose h1
    simp
  intro c hc
  rw [Set.mem_Icc, ← abs_le, ← Real.norm_eq_abs, ← mul_le_mul_right hr]
  simpa [f, dist_eq_norm, norm_smul] using hc

theorem frontier_closed_ball [NormedSpace ℝ E] (x : E) {r : ℝ} (hr : r ≠ 0) : Frontier (ClosedBall x r) = Sphere x r :=
  by
  rw [Frontier, closure_closed_ball, interior_closed_ball x hr, closed_ball_diff_ball]

/-- A (semi) normed real vector space is homeomorphic to the unit ball in the same space.
This homeomorphism sends `x : E` to `(1 + ∥x∥)⁻¹ • x`.

In many cases the actual implementation is not important, so we don't mark the projection lemmas
`homeomorph_unit_ball_apply_coe` and `homeomorph_unit_ball_symm_apply` as `@[simp]`. -/
@[simps (config := { attrs := [] })]
def homeomorphUnitBall {E : Type _} [SemiNormedGroup E] [NormedSpace ℝ E] : E ≃ₜ Ball (0 : E) 1 where
  toFun := fun x =>
    ⟨(1 + ∥x∥)⁻¹ • x, by
      have : ∥x∥ < abs (1 + ∥x∥) := (lt_one_add _).trans_le (le_abs_self _)
      rwa [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_inv, ← div_eq_inv_mul,
        div_lt_one ((norm_nonneg x).trans_lt this)]⟩
  invFun := fun x => (1 - ∥(x : E)∥)⁻¹ • (x : E)
  left_inv := fun x => by
    have : 0 < 1 + ∥x∥ := (norm_nonneg x).trans_lt (lt_one_add _)
    field_simp [this.ne', abs_of_pos this, norm_smul, smul_smul, Real.norm_eq_abs, abs_div]
  right_inv := fun x =>
    Subtype.ext
      (by
        have : 0 < 1 - ∥(x : E)∥ := sub_pos.2 (mem_ball_zero_iff.1 x.2)
        field_simp [norm_smul, smul_smul, Real.norm_eq_abs, abs_div, abs_of_pos this, this.ne'])
  continuous_to_fun :=
    continuous_subtype_mk _ <|
      ((continuous_const.add continuous_norm).inv₀ fun x => ((norm_nonneg x).trans_lt (lt_one_add _)).ne').smul
        continuous_id
  continuous_inv_fun :=
    Continuous.smul
      ((continuous_const.sub continuous_subtype_coe.norm).inv₀ fun x => (sub_pos.2 <| mem_ball_zero_iff.1 x.2).ne')
      continuous_subtype_coe

variable (α)

theorem ne_neg_of_mem_sphere [CharZero α] {r : ℝ} (hr : r ≠ 0) (x : Sphere (0 : E) r) : x ≠ -x := fun h =>
  ne_zero_of_mem_sphere hr x
    ((self_eq_neg α _).mp
      (by
        conv_lhs => rw [h]
        simp ))

theorem ne_neg_of_mem_unit_sphere [CharZero α] (x : Sphere (0 : E) 1) : x ≠ -x :=
  ne_neg_of_mem_sphere α one_ne_zero x

variable {α}

open NormedField

/-- The product of two normed spaces is a normed space, with the sup norm. -/
instance Prod.normedSpace : NormedSpace α (E × F) :=
  { Prod.normedGroup, Prod.module with
    norm_smul_le := fun s x =>
      le_of_eqₓ <| by
        simp [Prod.norm_def, norm_smul, mul_max_of_nonneg] }

/-- The product of finitely many normed spaces is a normed space, with the sup norm. -/
instance Pi.normedSpace {E : ι → Type _} [Fintype ι] [∀ i, SemiNormedGroup (E i)] [∀ i, NormedSpace α (E i)] :
    NormedSpace α (∀ i, E i) where
  norm_smul_le := fun a f =>
    le_of_eqₓ <|
      show
        (↑(Finset.sup Finset.univ fun b : ι => ∥a • f b∥₊) : ℝ) = ∥a∥₊ * ↑(Finset.sup Finset.univ fun b : ι => ∥f b∥₊)
        by
        simp only [(Nnreal.coe_mul _ _).symm, Nnreal.mul_finset_sup, nnnorm_smul]

/-- A subspace of a normed space is also a normed space, with the restriction of the norm. -/
instance Submodule.normedSpace {𝕜 R : Type _} [HasScalar 𝕜 R] [NormedField 𝕜] [Ringₓ R] {E : Type _} [SemiNormedGroup E]
    [NormedSpace 𝕜 E] [Module R E] [IsScalarTower 𝕜 R E] (s : Submodule R E) : NormedSpace 𝕜 s where
  norm_smul_le := fun c x => le_of_eqₓ <| norm_smul c (x : E)

/-- If there is a scalar `c` with `∥c∥>1`, then any element with nonzero norm can be
moved by scalar multiplication to any shell of width `∥c∥`. Also recap information on the norm of
the rescaling element that shows up in applications. -/
theorem rescale_to_shell_semi_normed {c : α} (hc : 1 < ∥c∥) {ε : ℝ} (εpos : 0 < ε) {x : E} (hx : ∥x∥ ≠ 0) :
    ∃ d : α, d ≠ 0 ∧ ∥d • x∥ < ε ∧ ε / ∥c∥ ≤ ∥d • x∥ ∧ ∥d∥⁻¹ ≤ ε⁻¹ * ∥c∥ * ∥x∥ := by
  have xεpos : 0 < ∥x∥ / ε := div_pos ((Ne.symm hx).le_iff_lt.1 (norm_nonneg x)) εpos
  rcases exists_mem_Ico_zpow xεpos hc with ⟨n, hn⟩
  have cpos : 0 < ∥c∥ := lt_transₓ (zero_lt_one : (0 : ℝ) < 1) hc
  have cnpos : 0 < ∥c ^ (n + 1)∥ := by
    rw [norm_zpow]
    exact lt_transₓ xεpos hn.2
  refine' ⟨(c ^ (n + 1))⁻¹, _, _, _, _⟩
  show (c ^ (n + 1))⁻¹ ≠ 0
  · rwa [Ne.def, inv_eq_zero, ← Ne.def, ← norm_pos_iff]
    
  show ∥(c ^ (n + 1))⁻¹ • x∥ < ε
  · rw [norm_smul, norm_inv, ← div_eq_inv_mul, div_lt_iff cnpos, mul_comm, norm_zpow]
    exact (div_lt_iff εpos).1 hn.2
    
  show ε / ∥c∥ ≤ ∥(c ^ (n + 1))⁻¹ • x∥
  · rw [div_le_iff cpos, norm_smul, norm_inv, norm_zpow, zpow_add₀ (ne_of_gtₓ cpos), zpow_one, mul_inv_rev₀, mul_comm, ←
      mul_assoc, ← mul_assoc, mul_inv_cancel (ne_of_gtₓ cpos), one_mulₓ, ← div_eq_inv_mul,
      le_div_iff (zpow_pos_of_pos cpos _), mul_comm]
    exact (le_div_iff εpos).1 hn.1
    
  show ∥(c ^ (n + 1))⁻¹∥⁻¹ ≤ ε⁻¹ * ∥c∥ * ∥x∥
  · have : ε⁻¹ * ∥c∥ * ∥x∥ = ε⁻¹ * ∥x∥ * ∥c∥ := by
      ring
    rw [norm_inv, inv_invₓ, norm_zpow, zpow_add₀ (ne_of_gtₓ cpos), zpow_one, this, ← div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_right hn.1 (norm_nonneg _)
    

end SemiNormedGroup

section NormedGroup

variable [NormedField α]

variable {E : Type _} [NormedGroup E] [NormedSpace α E]

variable {F : Type _} [NormedGroup F] [NormedSpace α F]

open NormedField

/-- While this may appear identical to `normed_space.to_module`, it contains an implicit argument
involving `normed_group.to_semi_normed_group` that typeclass inference has trouble inferring.

Specifically, the following instance cannot be found without this `normed_space.to_module'`:
```lean
example
  (𝕜 ι : Type*) (E : ι → Type*)
  [normed_field 𝕜] [Π i, normed_group (E i)] [Π i, normed_space 𝕜 (E i)] :
  Π i, module 𝕜 (E i) := by apply_instance
```

[This Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Typeclass.20resolution.20under.20binders/near/245151099)
gives some more context. -/
instance (priority := 100) NormedSpace.toModule' : Module α F :=
  NormedSpace.toModule

theorem interior_closed_ball' [NormedSpace ℝ E] [Nontrivial E] (x : E) (r : ℝ) : Interior (ClosedBall x r) = Ball x r :=
  by
  rcases eq_or_ne r 0 with (rfl | hr)
  · rw [closed_ball_zero, ball_zero, interior_singleton]
    
  · exact interior_closed_ball x hr
    

theorem frontier_closed_ball' [NormedSpace ℝ E] [Nontrivial E] (x : E) (r : ℝ) :
    Frontier (ClosedBall x r) = Sphere x r := by
  rw [Frontier, closure_closed_ball, interior_closed_ball' x r, closed_ball_diff_ball]

variable {α}

/-- If there is a scalar `c` with `∥c∥>1`, then any element can be moved by scalar multiplication to
any shell of width `∥c∥`. Also recap information on the norm of the rescaling element that shows
up in applications. -/
theorem rescale_to_shell {c : α} (hc : 1 < ∥c∥) {ε : ℝ} (εpos : 0 < ε) {x : E} (hx : x ≠ 0) :
    ∃ d : α, d ≠ 0 ∧ ∥d • x∥ < ε ∧ ε / ∥c∥ ≤ ∥d • x∥ ∧ ∥d∥⁻¹ ≤ ε⁻¹ * ∥c∥ * ∥x∥ :=
  rescale_to_shell_semi_normed hc εpos (ne_of_ltₓ (norm_pos_iff.2 hx)).symm

section

attribute [local instance] Matrix.normedGroup

/-- Normed space instance (using sup norm of sup norm) for matrices over a normed field.  Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
def Matrix.normedSpace {α : Type _} [NormedField α] {n m : Type _} [Fintype n] [Fintype m] :
    NormedSpace α (Matrix n m α) :=
  Pi.normedSpace

theorem Matrix.norm_entry_le_entrywise_sup_norm {α : Type _} [NormedRing α] {n m : Type _} [Fintype n] [Fintype m]
    (M : Matrix n m α) {i : n} {j : m} : ∥M i j∥ ≤ ∥M∥ :=
  (norm_le_pi_norm (M i) j).trans (norm_le_pi_norm M i)

end

end NormedGroup

section NormedSpaceNondiscrete

variable (𝕜 E : Type _) [NondiscreteNormedField 𝕜] [NormedGroup E] [NormedSpace 𝕜 E] [Nontrivial E]

include 𝕜

/-- If `E` is a nontrivial normed space over a nondiscrete normed field `𝕜`, then `E` is unbounded:
for any `c : ℝ`, there exists a vector `x : E` with norm strictly greater than `c`. -/
theorem NormedSpace.exists_lt_norm (c : ℝ) : ∃ x : E, c < ∥x∥ := by
  rcases exists_ne (0 : E) with ⟨x, hx⟩
  rcases NormedField.exists_lt_norm 𝕜 (c / ∥x∥) with ⟨r, hr⟩
  use r • x
  rwa [norm_smul, ← div_lt_iff]
  rwa [norm_pos_iff]

protected theorem NormedSpace.unbounded_univ : ¬Bounded (Set.Univ : Set E) := fun h =>
  let ⟨R, hR⟩ := bounded_iff_forall_norm_le.1 h
  let ⟨x, hx⟩ := NormedSpace.exists_lt_norm 𝕜 E R
  hx.not_le (hR x trivialₓ)

/-- A normed vector space over a nondiscrete normed field is a noncompact space. This cannot be
an instance because in order to apply it, Lean would have to search for `normed_space 𝕜 E` with
unknown `𝕜`. We register this as an instance in two cases: `𝕜 = E` and `𝕜 = ℝ`. -/
protected theorem NormedSpace.noncompact_space : NoncompactSpace E :=
  ⟨fun h => NormedSpace.unbounded_univ 𝕜 _ h.Bounded⟩

instance (priority := 100) NondiscreteNormedField.noncompact_space : NoncompactSpace 𝕜 :=
  NormedSpace.noncompact_space 𝕜 𝕜

omit 𝕜

instance (priority := 100) RealNormedSpace.noncompact_space [NormedSpace ℝ E] : NoncompactSpace E :=
  NormedSpace.noncompact_space ℝ E

end NormedSpaceNondiscrete

section NormedAlgebra

/-- A normed algebra `𝕜'` over `𝕜` is an algebra endowed with a norm for which the
embedding of `𝕜` in `𝕜'` is an isometry. -/
class NormedAlgebra (𝕜 : Type _) (𝕜' : Type _) [NormedField 𝕜] [SemiNormedRing 𝕜'] extends Algebra 𝕜 𝕜' where
  norm_algebra_map_eq : ∀ x : 𝕜, ∥algebraMap 𝕜 𝕜' x∥ = ∥x∥

@[simp]
theorem norm_algebra_map_eq {𝕜 : Type _} (𝕜' : Type _) [NormedField 𝕜] [SemiNormedRing 𝕜'] [h : NormedAlgebra 𝕜 𝕜']
    (x : 𝕜) : ∥algebraMap 𝕜 𝕜' x∥ = ∥x∥ :=
  NormedAlgebra.norm_algebra_map_eq _

/-- In a normed algebra, the inclusion of the base field in the extended field is an isometry. -/
theorem algebra_map_isometry (𝕜 : Type _) (𝕜' : Type _) [NormedField 𝕜] [SemiNormedRing 𝕜'] [NormedAlgebra 𝕜 𝕜'] :
    Isometry (algebraMap 𝕜 𝕜') := by
  refine' isometry_emetric_iff_metric.2 fun x y => _
  rw [dist_eq_norm, dist_eq_norm, ← RingHom.map_sub, norm_algebra_map_eq]

variable (𝕜 : Type _) (𝕜' : Type _) [NormedField 𝕜]

/-- The inclusion of the base field in a normed algebra as a continuous linear map. -/
@[simps]
def algebraMapClm [SemiNormedRing 𝕜'] [NormedAlgebra 𝕜 𝕜'] : 𝕜 →L[𝕜] 𝕜' where
  toFun := algebraMap 𝕜 𝕜'
  map_add' := (algebraMap 𝕜 𝕜').map_add
  map_smul' := fun r x => by
    rw [Algebra.id.smul_eq_mul, map_mul, RingHom.id_apply, Algebra.smul_def]
  cont := (algebra_map_isometry 𝕜 𝕜').Continuous

theorem algebra_map_clm_coe [SemiNormedRing 𝕜'] [NormedAlgebra 𝕜 𝕜'] :
    (algebraMapClm 𝕜 𝕜' : 𝕜 → 𝕜') = (algebraMap 𝕜 𝕜' : 𝕜 → 𝕜') :=
  rfl

theorem algebra_map_clm_to_linear_map [SemiNormedRing 𝕜'] [NormedAlgebra 𝕜 𝕜'] :
    (algebraMapClm 𝕜 𝕜').toLinearMap = Algebra.linearMap 𝕜 𝕜' :=
  rfl

instance (priority := 100) NormedAlgebra.toNormedSpace [SemiNormedRing 𝕜'] [h : NormedAlgebra 𝕜 𝕜'] :
    NormedSpace 𝕜 𝕜' :=
  { h with
    norm_smul_le := fun s x =>
      calc
        ∥s • x∥ = ∥(algebraMap 𝕜 𝕜') s * x∥ := by
          rw [h.smul_def']
          rfl
        _ ≤ ∥algebraMap 𝕜 𝕜' s∥ * ∥x∥ := SemiNormedRing.norm_mul _ _
        _ = ∥s∥ * ∥x∥ := by
          rw [norm_algebra_map_eq]
         }

/-- While this may appear identical to `normed_algebra.to_normed_space`, it contains an implicit
argument involving `normed_ring.to_semi_normed_ring` that typeclass inference has trouble inferring.

Specifically, the following instance cannot be found without this `normed_space.to_module'`:
```lean
example
  (𝕜 ι : Type*) (E : ι → Type*)
  [normed_field 𝕜] [Π i, normed_ring (E i)] [Π i, normed_algebra 𝕜 (E i)] :
  Π i, module 𝕜 (E i) := by apply_instance
```

See `normed_space.to_module'` for a similar situation. -/
instance (priority := 100) NormedAlgebra.toNormedSpace' [NormedRing 𝕜'] [NormedAlgebra 𝕜 𝕜'] : NormedSpace 𝕜 𝕜' := by
  infer_instance

instance NormedAlgebra.id : NormedAlgebra 𝕜 𝕜 :=
  { Algebra.id 𝕜 with
    norm_algebra_map_eq := by
      simp }

variable (𝕜') [SemiNormedRing 𝕜'] [NormedAlgebra 𝕜 𝕜']

include 𝕜

theorem NormedAlgebra.norm_one : ∥(1 : 𝕜')∥ = 1 := by
  simpa using norm_algebra_map_eq 𝕜' (1 : 𝕜)

theorem NormedAlgebra.norm_one_class : NormOneClass 𝕜' :=
  ⟨NormedAlgebra.norm_one 𝕜 𝕜'⟩

theorem NormedAlgebra.zero_ne_one : (0 : 𝕜') ≠ 1 := by
  refine' (ne_zero_of_norm_ne_zero _).symm
  rw [NormedAlgebra.norm_one 𝕜 𝕜']
  norm_num

theorem NormedAlgebra.nontrivial : Nontrivial 𝕜' :=
  ⟨⟨0, 1, NormedAlgebra.zero_ne_one 𝕜 𝕜'⟩⟩

end NormedAlgebra

section RestrictScalars

variable (𝕜 : Type _) (𝕜' : Type _) [NormedField 𝕜] [NormedField 𝕜'] [NormedAlgebra 𝕜 𝕜'] (E : Type _)
  [SemiNormedGroup E] [NormedSpace 𝕜' E]

/-- Warning: This declaration should be used judiciously.
Please consider using `is_scalar_tower` instead.

`𝕜`-normed space structure induced by a `𝕜'`-normed space structure when `𝕜'` is a
normed algebra over `𝕜`. Not registered as an instance as `𝕜'` can not be inferred.

The type synonym `restrict_scalars 𝕜 𝕜' E` will be endowed with this instance by default.
-/
def NormedSpace.restrictScalars : NormedSpace 𝕜 E :=
  { RestrictScalars.module 𝕜 𝕜' E with
    norm_smul_le := fun c x =>
      le_of_eqₓ <| by
        change ∥algebraMap 𝕜 𝕜' c • x∥ = ∥c∥ * ∥x∥
        simp [norm_smul] }

instance {𝕜 : Type _} {𝕜' : Type _} {E : Type _} [I : SemiNormedGroup E] : SemiNormedGroup (RestrictScalars 𝕜 𝕜' E) :=
  I

instance {𝕜 : Type _} {𝕜' : Type _} {E : Type _} [I : NormedGroup E] : NormedGroup (RestrictScalars 𝕜 𝕜' E) :=
  I

instance Module.RestrictScalars.normedSpaceOrig {𝕜 : Type _} {𝕜' : Type _} {E : Type _} [NormedField 𝕜']
    [SemiNormedGroup E] [I : NormedSpace 𝕜' E] : NormedSpace 𝕜' (RestrictScalars 𝕜 𝕜' E) :=
  I

instance : NormedSpace 𝕜 (RestrictScalars 𝕜 𝕜' E) :=
  (NormedSpace.restrictScalars 𝕜 𝕜' E : NormedSpace 𝕜 E)

end RestrictScalars

