/-
Copyright (c) 2022 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import Mathbin.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Uniform integrability

This file contains the definitions for uniform integrability (both in the measure theory sense
as well as the probability theory sense). This file also contains the Vitali convergence theorem
which estabishes a relation between uniform integrability, convergence in measure and
Lp convergence.

Uniform integrability plays a vital role in the theory of martingales most notably is used to
fomulate the martingale convergence theorem.

## Main definitions

* `measure_theory.unif_integrable`: uniform integrability in the measure theory sense.
  In particular, a sequence of functions `f` is uniformly integrable if for all `ε > 0`, there
  exists some `δ > 0` such that for all sets `s` of smaller measure than `δ`, the Lp-norm of
  `f i` restricted `s` is smaller than `ε` for all `i`.
* `measure_theory.uniform_integrable`: uniform integrability in the probability theory sense.
  In particular, a sequence of measurable functions `f` is uniformly integrable in the
  probability theory sense if it is uniformly integrable in the measure theory sense and
  has uniformly bounded Lp-norm.

# Main results

* `measure_theory.unif_integrable_fintype`: a finite sequence of Lp functions is uniformly
  integrable.
* `measure_theory.tendsto_Lp_of_tendsto_ae`: a sequence of Lp functions which is uniformly
  integrable converges in Lp if they converge almost everywhere.
* `measure_theory.tendsto_in_measure_iff_tendsto_Lp`: Vitali convergence theorem:
  a sequence of Lp functions converges in Lp if and only if it is uniformly integrable
  and converges in measure.

## Tags
uniform integrable, uniformly absolutely continuous integral, Vitali convergence theorem
-/


noncomputable section

open_locale Classical MeasureTheory Nnreal Ennreal TopologicalSpace

namespace MeasureTheory

open Set Filter TopologicalSpace

variable {α β ι : Type _} {m : MeasurableSpace α} {μ : Measure α} [NormedGroup β]

/-- Uniform integrability in the measure theory sense.

A sequence of functions `f` is said to be uniformly integrable if for all `ε > 0`, there exists
some `δ > 0` such that for all sets `s` with measure less than `δ`, the Lp-norm of `f i`
restricted on `s` is less than `ε`.

Uniform integrablility is also known as uniformly absolutely continuous integrals. -/
def UnifIntegrable {m : MeasurableSpace α} (f : ι → α → β) (p : ℝ≥0∞) (μ : Measure α) : Prop :=
  ∀ ⦃ε : ℝ⦄ hε : 0 < ε,
    ∃ (δ : ℝ)(hδ : 0 < δ),
      ∀ i s, MeasurableSet s → μ s ≤ Ennreal.ofReal δ → snorm (s.indicator (f i)) p μ ≤ Ennreal.ofReal ε

/-- In probability theory, a family of measurable functions is uniformly integrable if it is
uniformly integrable in the measure theory sense and is uniformly bounded. -/
def UniformIntegrable {m : MeasurableSpace α} [MeasurableSpace β] (f : ι → α → β) (p : ℝ≥0∞) (μ : Measure α) : Prop :=
  (∀ i, Measurable (f i)) ∧ UnifIntegrable f p μ ∧ ∃ C : ℝ≥0 , ∀ i, snorm (f i) p μ ≤ C

theorem UniformIntegrable.measurable {mβ : MeasurableSpace β} {f : ι → α → β} {p : ℝ≥0∞} (hf : UniformIntegrable f p μ)
    (i : ι) : Measurable (f i) :=
  hf.1 i

theorem UniformIntegrable.unif_integrable {mβ : MeasurableSpace β} {f : ι → α → β} {p : ℝ≥0∞}
    (hf : UniformIntegrable f p μ) : UnifIntegrable f p μ :=
  hf.2.1

theorem UniformIntegrable.mem_ℒp {mβ : MeasurableSpace β} {f : ι → α → β} {p : ℝ≥0∞} (hf : UniformIntegrable f p μ)
    (i : ι) : Memℒp (f i) p μ :=
  ⟨(hf.1 i).AeMeasurable,
    let ⟨_, _, hC⟩ := hf.2
    lt_of_le_of_ltₓ (hC i) Ennreal.coe_lt_top⟩

section UnifIntegrable

/-! ### `unif_integrable`

This section deals with uniform integrability in the measure theory sense. -/


namespace UnifIntegrable

variable {f g : ι → α → β} {p : ℝ≥0∞}

protected theorem add {mβ : MeasurableSpace β} [OpensMeasurableSpace β] (hf : UnifIntegrable f p μ)
    (hg : UnifIntegrable g p μ) (hp : 1 ≤ p) (hf_meas : ∀ i, AeMeasurable (f i) μ)
    (hg_meas : ∀ i, AeMeasurable (g i) μ) : UnifIntegrable (f + g) p μ := by
  intro ε hε
  have hε2 : 0 < ε / 2 := half_pos hε
  obtain ⟨δ₁, hδ₁_pos, hfδ₁⟩ := hf hε2
  obtain ⟨δ₂, hδ₂_pos, hgδ₂⟩ := hg hε2
  refine' ⟨min δ₁ δ₂, lt_minₓ hδ₁_pos hδ₂_pos, fun i s hs hμs => _⟩
  simp_rw [Pi.add_apply, indicator_add']
  refine' (snorm_add_le ((hf_meas i).indicator hs) ((hg_meas i).indicator hs) hp).trans _
  have hε_halves : Ennreal.ofReal ε = Ennreal.ofReal (ε / 2) + Ennreal.ofReal (ε / 2) := by
    rw [← Ennreal.of_real_add hε2.le hε2.le, add_halves]
  rw [hε_halves]
  exact
    add_le_add (hfδ₁ i s hs (hμs.trans (Ennreal.of_real_le_of_real (min_le_leftₓ _ _))))
      (hgδ₂ i s hs (hμs.trans (Ennreal.of_real_le_of_real (min_le_rightₓ _ _))))

protected theorem neg (hf : UnifIntegrable f p μ) : UnifIntegrable (-f) p μ := by
  simp_rw [unif_integrable, Pi.neg_apply, indicator_neg', snorm_neg]
  exact hf

protected theorem sub {mβ : MeasurableSpace β} [OpensMeasurableSpace β] [HasMeasurableNeg β] (hf : UnifIntegrable f p μ)
    (hg : UnifIntegrable g p μ) (hp : 1 ≤ p) (hf_meas : ∀ i, AeMeasurable (f i) μ)
    (hg_meas : ∀ i, AeMeasurable (g i) μ) : UnifIntegrable (f - g) p μ := by
  rw [sub_eq_add_neg]
  exact hf.add hg.neg hp hf_meas fun i => (hg_meas i).neg

protected theorem ae_eq (hf : UnifIntegrable f p μ) (hfg : ∀ n, f n =ᵐ[μ] g n) : UnifIntegrable g p μ := by
  intro ε hε
  obtain ⟨δ, hδ_pos, hfδ⟩ := hf hε
  refine' ⟨δ, hδ_pos, fun n s hs hμs => (le_of_eqₓ <| snorm_congr_ae _).trans (hfδ n s hs hμs)⟩
  filter_upwards [hfg n] with x hx
  simp_rw [indicator_apply, hx]

end UnifIntegrable

theorem unif_integrable_congr_ae {f g : ι → α → β} {p : ℝ≥0∞} (hfg : ∀ n, f n =ᵐ[μ] g n) :
    UnifIntegrable f p μ ↔ UnifIntegrable g p μ :=
  ⟨fun hf => hf.ae_eq hfg, fun hg => hg.ae_eq fun n => (hfg n).symm⟩

theorem tendsto_indicator_ge (f : α → β) (x : α) :
    Tendsto (fun M : ℕ => { x | (M : ℝ) ≤ ∥f x∥₊ }.indicator f x) atTop (𝓝 0) := by
  refine' @tendsto_at_top_of_eventually_const _ _ _ _ _ _ _ (Nat.ceil (∥f x∥₊ : ℝ) + 1) fun n hn => _
  rw [indicator_of_not_mem]
  simp only [not_leₓ, mem_set_of_eq]
  refine' lt_of_le_of_ltₓ (Nat.le_ceil _) _
  refine' lt_of_lt_of_leₓ (lt_add_one _) _
  norm_cast
  rwa [ge_iff_le, coe_nnnorm] at hn

variable (μ) {p : ℝ≥0∞}

section

variable [MeasurableSpace β] [BorelSpace β] [hβ : SecondCountableTopology β] {f : α → β}

include hβ

/-- This lemma is weaker than `measure_theory.mem_ℒp.integral_indicator_norm_ge_nonneg_le`
as the latter provides `0 ≤ M` and does not require the measurability of `f`. -/
theorem Memℒp.integral_indicator_norm_ge_le (hf : Memℒp f 1 μ) (hmeas : Measurable f) {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℝ, (∫⁻ x, ∥{ x | M ≤ ∥f x∥₊ }.indicator f x∥₊ ∂μ) ≤ Ennreal.ofReal ε := by
  have htendsto : ∀ᵐ x ∂μ, tendsto (fun M : ℕ => { x | (M : ℝ) ≤ ∥f x∥₊ }.indicator f x) at_top (𝓝 0) :=
    univ_mem' (id fun x => tendsto_indicator_ge f x)
  have hmeas : ∀ M : ℕ, AeMeasurable ({ x | (M : ℝ) ≤ ∥f x∥₊ }.indicator f) μ := by
    cases hf
    measurability
  have hbound : has_finite_integral (fun x => ∥f x∥) μ := by
    rw [mem_ℒp_one_iff_integrable] at hf
    exact hf.norm.2
  have := tendsto_lintegral_norm_of_dominated_convergence hmeas hbound _ htendsto
  · rw [Ennreal.tendsto_at_top_zero] at this
    obtain ⟨M, hM⟩ := this (Ennreal.ofReal ε) (Ennreal.of_real_pos.2 hε)
    simp only [true_andₓ, ge_iff_le, zero_tsub, zero_le, sub_zero, zero_addₓ, coe_nnnorm, mem_Icc] at hM
    refine' ⟨M, _⟩
    convert hM M le_rfl
    ext1 x
    simp only [coe_nnnorm, Ennreal.of_real_eq_coe_nnreal (norm_nonneg _)]
    rfl
    
  · refine' fun n => univ_mem' (id fun x => _)
    by_cases' hx : (n : ℝ) ≤ ∥f x∥
    · dsimp
      rwa [indicator_of_mem]
      
    · dsimp
      rw [indicator_of_not_mem, norm_zero]
      · exact norm_nonneg _
        
      · assumption
        
      
    

/-- This lemma is superceded by `measure_theory.mem_ℒp.integral_indicator_norm_ge_nonneg_le`
which does not require measurability. -/
theorem Memℒp.integral_indicator_norm_ge_nonneg_le_of_meas (hf : Memℒp f 1 μ) (hmeas : Measurable f) {ε : ℝ}
    (hε : 0 < ε) : ∃ M : ℝ, 0 ≤ M ∧ (∫⁻ x, ∥{ x | M ≤ ∥f x∥₊ }.indicator f x∥₊ ∂μ) ≤ Ennreal.ofReal ε :=
  let ⟨M, hM⟩ := hf.integral_indicator_norm_ge_le μ hmeas hε
  ⟨max M 0, le_max_rightₓ _ _, by
    simpa⟩

theorem Memℒp.integral_indicator_norm_ge_nonneg_le (hf : Memℒp f 1 μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℝ, 0 ≤ M ∧ (∫⁻ x, ∥{ x | M ≤ ∥f x∥₊ }.indicator f x∥₊ ∂μ) ≤ Ennreal.ofReal ε := by
  have hf_mk : mem_ℒp (hf.1.mk f) 1 μ := (mem_ℒp_congr_ae hf.1.ae_eq_mk).mp hf
  obtain ⟨M, hM_pos, hfM⟩ := hf_mk.integral_indicator_norm_ge_nonneg_le_of_meas μ hf.1.measurable_mk hε
  refine' ⟨M, hM_pos, (le_of_eqₓ _).trans hfM⟩
  refine' lintegral_congr_ae _
  filter_upwards [hf.1.ae_eq_mk] with x hx
  simp only [indicator_apply, coe_nnnorm, mem_set_of_eq, Ennreal.coe_eq_coe, hx.symm]

omit hβ

theorem Memℒp.snorm_ess_sup_indicator_norm_ge_eq_zero (hf : Memℒp f ∞ μ) (hmeas : Measurable f) :
    ∃ M : ℝ, snormEssSup ({ x | M ≤ ∥f x∥₊ }.indicator f) μ = 0 := by
  have hbdd : snorm_ess_sup f μ < ∞ := hf.snorm_lt_top
  refine' ⟨(snorm f ∞ μ + 1).toReal, _⟩
  rw [snorm_ess_sup_indicator_eq_snorm_ess_sup_restrict]
  have : μ.restrict { x : α | (snorm f ⊤ μ + 1).toReal ≤ ∥f x∥₊ } = 0 := by
    simp only [coe_nnnorm, snorm_exponent_top, measure.restrict_eq_zero]
    have : { x : α | (snorm_ess_sup f μ + 1).toReal ≤ ∥f x∥ } ⊆ { x : α | snorm_ess_sup f μ < ∥f x∥₊ } := by
      intro x hx
      rw [mem_set_of_eq, ← Ennreal.to_real_lt_to_real hbdd.ne ennreal.coe_lt_top.ne, Ennreal.coe_to_real, coe_nnnorm]
      refine' lt_of_lt_of_leₓ _ hx
      rw [Ennreal.to_real_lt_to_real hbdd.ne]
      · exact Ennreal.lt_add_right hbdd.ne one_ne_zero
        
      · exact (Ennreal.add_lt_top.2 ⟨hbdd, Ennreal.one_lt_top⟩).Ne
        
    rw [← nonpos_iff_eq_zero]
    refine' (measure_mono this).trans _
    have hle := coe_nnnorm_ae_le_snorm_ess_sup f μ
    simp_rw [ae_iff, not_leₓ]  at hle
    exact nonpos_iff_eq_zero.2 hle
  rw [this, snorm_ess_sup_measure_zero]
  exact measurable_set_le measurable_const hmeas.nnnorm.subtype_coe

/- This lemma is slightly weaker than `measure_theory.mem_ℒp.snorm_indicator_norm_ge_pos_le` as the
latter provides `0 < M`. -/
theorem Memℒp.snorm_indicator_norm_ge_le (hf : Memℒp f p μ) (hmeas : Measurable f) {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℝ, snorm ({ x | M ≤ ∥f x∥₊ }.indicator f) p μ ≤ Ennreal.ofReal ε := by
  by_cases' hp_ne_zero : p = 0
  · refine' ⟨1, hp_ne_zero.symm ▸ _⟩
    simp [snorm_exponent_zero]
    
  by_cases' hp_ne_top : p = ∞
  · subst hp_ne_top
    obtain ⟨M, hM⟩ := hf.snorm_ess_sup_indicator_norm_ge_eq_zero μ hmeas
    refine' ⟨M, _⟩
    simp only [snorm_exponent_top, hM, zero_le]
    
  obtain ⟨M, hM', hM⟩ :=
    @mem_ℒp.integral_indicator_norm_ge_nonneg_le _ _ _ μ _ _ _ _ (fun x => ∥f x∥ ^ p.to_real)
      (hf.norm_rpow hp_ne_zero hp_ne_top) _ (Real.rpow_pos_of_pos hε p.to_real)
  refine' ⟨M ^ (1 / p.to_real), _⟩
  rw [snorm_eq_lintegral_rpow_nnnorm hp_ne_zero hp_ne_top, ← Ennreal.rpow_one (Ennreal.ofReal ε)]
  conv_rhs => rw [← mul_one_div_cancel (Ennreal.to_real_pos hp_ne_zero hp_ne_top).Ne.symm]
  rw [Ennreal.rpow_mul, Ennreal.rpow_le_rpow_iff (one_div_pos.2 <| Ennreal.to_real_pos hp_ne_zero hp_ne_top),
    Ennreal.of_real_rpow_of_pos hε]
  convert hM
  ext1 x
  rw [Ennreal.coe_rpow_of_nonneg _ Ennreal.to_real_nonneg, nnnorm_indicator_eq_indicator_nnnorm,
    nnnorm_indicator_eq_indicator_nnnorm]
  have hiff : M ^ (1 / p.to_real) ≤ ∥f x∥₊ ↔ M ≤ ∥∥f x∥ ^ p.to_real∥₊ := by
    rw [coe_nnnorm, coe_nnnorm, Real.norm_rpow_of_nonneg (norm_nonneg _), norm_norm, ←
      Real.rpow_le_rpow_iff hM' (Real.rpow_nonneg_of_nonneg (norm_nonneg _) _)
        (one_div_pos.2 <| Ennreal.to_real_pos hp_ne_zero hp_ne_top),
      ← Real.rpow_mul (norm_nonneg _), mul_one_div_cancel (Ennreal.to_real_pos hp_ne_zero hp_ne_top).Ne.symm,
      Real.rpow_one]
  by_cases' hx : x ∈ { x : α | M ^ (1 / p.to_real) ≤ ∥f x∥₊ }
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem, Real.nnnorm_of_nonneg]
    rfl
    change _ ≤ _
    rwa [← hiff]
    
  · rw [Set.indicator_of_not_mem hx, Set.indicator_of_not_mem]
    · simp [(Ennreal.to_real_pos hp_ne_zero hp_ne_top).Ne.symm]
      
    · change ¬_ ≤ _
      rwa [← hiff]
      
    

/-- This lemma implies that a single function is uniformly integrable (in the probability sense). -/
theorem Memℒp.snorm_indicator_norm_ge_pos_le (hf : Memℒp f p μ) (hmeas : Measurable f) {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℝ, 0 < M ∧ snorm ({ x | M ≤ ∥f x∥₊ }.indicator f) p μ ≤ Ennreal.ofReal ε := by
  obtain ⟨M, hM⟩ := hf.snorm_indicator_norm_ge_le μ hmeas hε
  refine' ⟨max M 1, lt_of_lt_of_leₓ zero_lt_one (le_max_rightₓ _ _), le_transₓ (snorm_mono fun x => _) hM⟩
  rw [norm_indicator_eq_indicator_norm, norm_indicator_eq_indicator_norm]
  refine' indicator_le_indicator_of_subset (fun x hx => _) (fun x => norm_nonneg _) x
  change max _ _ ≤ _ at hx
  -- removing the `change` breaks the proof!
  exact (max_le_iff.1 hx).1

end

-- ././Mathport/Syntax/Translate/Basic.lean:535:40: in filter_upwards: ././Mathport/Syntax/Translate/Basic.lean:223:22: unsupported: parse error
theorem snorm_indicator_le_of_bound {f : α → β} (hp_top : p ≠ ∞) {ε : ℝ} (hε : 0 < ε) {M : ℝ} (hf : ∀ x, ∥f x∥ < M) :
    ∃ (δ : ℝ)(hδ : 0 < δ),
      ∀ s, MeasurableSet s → μ s ≤ Ennreal.ofReal δ → snorm (s.indicator f) p μ ≤ Ennreal.ofReal ε :=
  by
  by_cases' hM : M ≤ 0
  · refine' ⟨1, zero_lt_one, fun s hs hμ => _⟩
    rw [(_ : f = 0)]
    · simp [hε.le]
      
    · ext x
      rw [Pi.zero_apply, ← norm_le_zero_iff]
      exact (lt_of_lt_of_leₓ (hf x) hM).le
      
    
  rw [not_leₓ] at hM
  refine' ⟨(ε / M) ^ p.to_real, Real.rpow_pos_of_pos (div_pos hε hM) _, fun s hs hμ => _⟩
  by_cases' hp : p = 0
  · simp [hp]
    
  rw [snorm_indicator_eq_snorm_restrict hs]
  have haebdd : ∀ᵐ x ∂μ.restrict s, ∥f x∥ ≤ M := by
    "././Mathport/Syntax/Translate/Basic.lean:535:40: in filter_upwards: ././Mathport/Syntax/Translate/Basic.lean:223:22: unsupported: parse error"
    exact fun x => (hf x).le
  refine' le_transₓ (snorm_le_of_ae_bound haebdd) _
  rw [measure.restrict_apply MeasurableSet.univ, univ_inter, ←
    Ennreal.le_div_iff_mul_le (Or.inl _) (Or.inl Ennreal.of_real_ne_top)]
  · rw [← one_div, Ennreal.rpow_one_div_le_iff (Ennreal.to_real_pos hp hp_top)]
    refine' le_transₓ hμ _
    rw [← Ennreal.of_real_rpow_of_pos (div_pos hε hM), Ennreal.rpow_le_rpow_iff (Ennreal.to_real_pos hp hp_top),
      Ennreal.of_real_div_of_pos hM]
    exact le_rfl
    
  · simpa only [Ennreal.of_real_eq_zero, not_leₓ, Ne.def]
    

section

variable [MeasurableSpace β] [BorelSpace β] {f : α → β}

/-- Auxiliary lemma for `measure_theory.mem_ℒp.snorm_indicator_le`. -/
theorem Memℒp.snorm_indicator_le' (hp_one : 1 ≤ p) (hp_top : p ≠ ∞) (hf : Memℒp f p μ) (hmeas : Measurable f) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ (δ : ℝ)(hδ : 0 < δ),
      ∀ s, MeasurableSet s → μ s ≤ Ennreal.ofReal δ → snorm (s.indicator f) p μ ≤ 2 * Ennreal.ofReal ε :=
  by
  obtain ⟨M, hMpos, hM⟩ := hf.snorm_indicator_norm_ge_pos_le μ hmeas hε
  obtain ⟨δ, hδpos, hδ⟩ := @snorm_indicator_le_of_bound _ _ _ μ _ _ ({ x | ∥f x∥ < M }.indicator f) hp_top _ hε M _
  · refine' ⟨δ, hδpos, fun s hs hμs => _⟩
    rw [(_ : f = { x : α | M ≤ ∥f x∥₊ }.indicator f + { x : α | ∥f x∥ < M }.indicator f)]
    · rw [snorm_indicator_eq_snorm_restrict hs]
      refine' le_transₓ (snorm_add_le _ _ hp_one) _
      · exact Measurable.ae_measurable (hmeas.indicator (measurable_set_le measurable_const hmeas.nnnorm.subtype_coe))
        
      · exact Measurable.ae_measurable (hmeas.indicator (measurable_set_lt hmeas.nnnorm.subtype_coe measurable_const))
        
      · rw [two_mul]
        refine' add_le_add (le_transₓ (snorm_mono_measure _ measure.restrict_le_self) hM) _
        rw [← snorm_indicator_eq_snorm_restrict hs]
        exact hδ s hs hμs
        
      
    · ext x
      by_cases' hx : M ≤ ∥f x∥
      · rw [Pi.add_apply, indicator_of_mem, indicator_of_not_mem, add_zeroₓ] <;> simpa
        
      · rw [Pi.add_apply, indicator_of_not_mem, indicator_of_mem, zero_addₓ] <;> simpa using hx
        
      
    
  · intro x
    rw [norm_indicator_eq_indicator_norm, indicator_apply]
    split_ifs
    exacts[h, hMpos]
    

/-- This lemma is superceded by `measure_theory.mem_ℒp.snorm_indicator_le` which does not require
measurability on `f`. -/
theorem Memℒp.snorm_indicator_le_of_meas (hp_one : 1 ≤ p) (hp_top : p ≠ ∞) (hf : Memℒp f p μ) (hmeas : Measurable f)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (δ : ℝ)(hδ : 0 < δ),
      ∀ s, MeasurableSet s → μ s ≤ Ennreal.ofReal δ → snorm (s.indicator f) p μ ≤ Ennreal.ofReal ε :=
  by
  obtain ⟨δ, hδpos, hδ⟩ := hf.snorm_indicator_le' μ hp_one hp_top hmeas (half_pos hε)
  refine' ⟨δ, hδpos, fun s hs hμs => le_transₓ (hδ s hs hμs) _⟩
  rw [Ennreal.of_real_div_of_pos zero_lt_two,
      (by
        norm_num : Ennreal.ofReal 2 = 2),
      Ennreal.mul_div_cancel'] <;>
    norm_num

theorem Memℒp.snorm_indicator_le (hp_one : 1 ≤ p) (hp_top : p ≠ ∞) (hf : Memℒp f p μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (δ : ℝ)(hδ : 0 < δ),
      ∀ s, MeasurableSet s → μ s ≤ Ennreal.ofReal δ → snorm (s.indicator f) p μ ≤ Ennreal.ofReal ε :=
  by
  have hℒp := hf
  obtain ⟨⟨f', hf', heq⟩, hnorm⟩ := hf
  obtain ⟨δ, hδpos, hδ⟩ := (hℒp.ae_eq HEq).snorm_indicator_le_of_meas μ hp_one hp_top hf' hε
  refine' ⟨δ, hδpos, fun s hs hμs => _⟩
  convert hδ s hs hμs using 1
  rw [snorm_indicator_eq_snorm_restrict hs, snorm_indicator_eq_snorm_restrict hs]
  refine' snorm_congr_ae heq.restrict

/-- A constant function is uniformly integrable. -/
theorem unif_integrable_const {g : α → β} (hp : 1 ≤ p) (hp_ne_top : p ≠ ∞) (hg : Memℒp g p μ) :
    UnifIntegrable (fun n : ι => g) p μ := by
  intro ε hε
  obtain ⟨δ, hδ_pos, hgδ⟩ := hg.snorm_indicator_le μ hp hp_ne_top hε
  exact ⟨δ, hδ_pos, fun i => hgδ⟩

/-- A single function is uniformly integrable. -/
theorem unif_integrable_subsingleton [Subsingleton ι] (hp_one : 1 ≤ p) (hp_top : p ≠ ∞) {f : ι → α → β}
    (hf : ∀ i, Memℒp (f i) p μ) : UnifIntegrable f p μ := by
  intro ε hε
  by_cases' hι : Nonempty ι
  · cases' hι with i
    obtain ⟨δ, hδpos, hδ⟩ := (hf i).snorm_indicator_le μ hp_one hp_top hε
    refine' ⟨δ, hδpos, fun j s hs hμs => _⟩
    convert hδ s hs hμs
    
  · exact ⟨1, zero_lt_one, fun i => False.elim <| hι <| Nonempty.intro i⟩
    

/-- This lemma is less general than `measure_theory.unif_integrable_fintype` which applies to
all sequences indexed by a fintype. -/
theorem unif_integrable_fin (hp_one : 1 ≤ p) (hp_top : p ≠ ∞) {n : ℕ} {f : Finₓ n → α → β} (hf : ∀ i, Memℒp (f i) p μ) :
    UnifIntegrable f p μ := by
  revert f
  induction' n with n h
  · exact fun f hf => unif_integrable_subsingleton μ hp_one hp_top hf
    
  intro f hfLp ε hε
  set g : Finₓ n → α → β := fun k => f k with hg
  have hgLp : ∀ i, mem_ℒp (g i) p μ := fun i => hfLp i
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := h hgLp hε
  obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := (hfLp n).snorm_indicator_le μ hp_one hp_top hε
  refine' ⟨min δ₁ δ₂, lt_minₓ hδ₁pos hδ₂pos, fun i s hs hμs => _⟩
  by_cases' hi : i.val < n
  · rw [(_ : f i = g ⟨i.val, hi⟩)]
    · exact hδ₁ _ s hs (le_transₓ hμs <| Ennreal.of_real_le_of_real <| min_le_leftₓ _ _)
      
    · rw [hg]
      simp
      
    
  · rw [(_ : i = n)]
    · exact hδ₂ _ hs (le_transₓ hμs <| Ennreal.of_real_le_of_real <| min_le_rightₓ _ _)
      
    · have hi' := Finₓ.is_lt i
      rw [Nat.lt_succ_iffₓ] at hi'
      rw [not_ltₓ] at hi
      simp [← le_antisymmₓ hi' hi]
      
    

/-- A finite sequence of Lp functions is uniformly integrable. -/
theorem unif_integrable_fintype [Fintype ι] (hp_one : 1 ≤ p) (hp_top : p ≠ ∞) {f : ι → α → β}
    (hf : ∀ i, Memℒp (f i) p μ) : UnifIntegrable f p μ := by
  intro ε hε
  set g : Finₓ (Fintype.card ι) → α → β := f ∘ (Fintype.equivFin ι).symm
  have hg : ∀ i, mem_ℒp (g i) p μ := fun _ => hf _
  obtain ⟨δ, hδpos, hδ⟩ := unif_integrable_fin μ hp_one hp_top hg hε
  exact
    ⟨δ, hδpos, fun i s hs hμs => Equivₓ.symm_apply_apply (Fintype.equivFin ι) i ▸ hδ (Fintype.equivFin ι i) s hs hμs⟩

end

theorem snorm_sub_le_of_dist_bdd {p : ℝ≥0∞} (hp : p ≠ 0) (hp' : p ≠ ∞) {s : Set α} (hs : measurable_set[m] s)
    {f g : α → β} {c : ℝ} (hc : 0 ≤ c) (hf : ∀, ∀ x ∈ s, ∀, dist (f x) (g x) ≤ c) :
    snorm (s.indicator (f - g)) p μ ≤ Ennreal.ofReal c * μ s ^ (1 / p.toReal) := by
  have : ∀ x, ∥s.indicator (f - g) x∥ ≤ ∥s.indicator (fun x => c) x∥ := by
    intro x
    by_cases' hx : x ∈ s
    · rw [indicator_of_mem hx, indicator_of_mem hx, Pi.sub_apply, ← dist_eq_norm, Real.norm_eq_abs, abs_of_nonneg hc]
      exact hf x hx
      
    · simp [indicator_of_not_mem hx]
      
  refine' le_transₓ (snorm_mono this) _
  rw [snorm_indicator_const hs hp hp']
  refine' Ennreal.mul_le_mul (le_of_eqₓ _) le_rfl
  rw [← of_real_norm_eq_coe_nnnorm, Real.norm_eq_abs, abs_of_nonneg hc]

/-- A sequence of uniformly integrable functions which converges μ-a.e. converges in Lp. -/
theorem tendsto_Lp_of_tendsto_ae_of_meas {mβ : MeasurableSpace β} [BorelSpace β] [SecondCountableTopology β]
    [IsFiniteMeasure μ] (hp : 1 ≤ p) (hp' : p ≠ ∞) {f : ℕ → α → β} {g : α → β} (hf : ∀ n, Measurable (f n))
    (hg : Measurable g) (hg' : Memℒp g p μ) (hui : UnifIntegrable f p μ)
    (hfg : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) : Tendsto (fun n => snorm (f n - g) p μ) atTop (𝓝 0) := by
  rw [Ennreal.tendsto_at_top_zero]
  intro ε hε
  by_cases' ε < ∞
  swap
  · rw [not_ltₓ, top_le_iff] at h
    exact
      ⟨0, fun n hn => by
        simp [h]⟩
    
  by_cases' hμ : μ = 0
  · exact
      ⟨0, fun n hn => by
        simp [hμ]⟩
    
  have hε' : 0 < ε.to_real / 3 :=
    div_pos (Ennreal.to_real_pos (gt_iff_lt.1 hε).Ne.symm h.ne)
      (by
        norm_num)
  have hdivp : 0 ≤ 1 / p.to_real := by
    refine' one_div_nonneg.2 _
    rw [← Ennreal.zero_to_real, Ennreal.to_real_le_to_real Ennreal.zero_ne_top hp']
    exact le_transₓ ennreal.zero_lt_one.le hp
  have hpow : 0 < measure_univ_nnreal μ ^ (1 / p.to_real) := Real.rpow_pos_of_pos (measure_univ_nnreal_pos hμ) _
  obtain ⟨δ₁, hδ₁, hsnorm₁⟩ := hui hε'
  obtain ⟨δ₂, hδ₂, hsnorm₂⟩ := hg'.snorm_indicator_le μ hp hp' hε'
  obtain ⟨t, htm, ht₁, ht₂⟩ := tendsto_uniformly_on_of_ae_tendsto' hf hg hfg (lt_minₓ hδ₁ hδ₂)
  rw [Metric.tendsto_uniformly_on_iff] at ht₂
  specialize
    ht₂ (ε.to_real / (3 * measure_univ_nnreal μ ^ (1 / p.to_real)))
      (div_pos (Ennreal.to_real_pos (gt_iff_lt.1 hε).Ne.symm h.ne)
        (mul_pos
          (by
            norm_num)
          hpow))
  obtain ⟨N, hN⟩ := eventually_at_top.1 ht₂
  clear ht₂
  refine' ⟨N, fun n hn => _⟩
  rw [← t.indicator_self_add_compl (f n - g)]
  refine'
    le_transₓ
      (snorm_add_le (((hf n).sub hg).indicator htm).AeMeasurable (((hf n).sub hg).indicator htm.compl).AeMeasurable hp)
      _
  rw [sub_eq_add_neg, indicator_add' t, indicator_neg']
  refine'
    le_transₓ
      (add_le_add_right (snorm_add_le ((hf n).indicator htm).AeMeasurable (hg.indicator htm).neg.AeMeasurable hp) _) _
  have hnf : snorm (t.indicator (f n)) p μ ≤ Ennreal.ofReal (ε.to_real / 3) := by
    refine' hsnorm₁ n t htm (le_transₓ ht₁ _)
    rw [Ennreal.of_real_le_of_real_iff hδ₁.le]
    exact min_le_leftₓ _ _
  have hng : snorm (t.indicator g) p μ ≤ Ennreal.ofReal (ε.to_real / 3) := by
    refine' hsnorm₂ t htm (le_transₓ ht₁ _)
    rw [Ennreal.of_real_le_of_real_iff hδ₂.le]
    exact min_le_rightₓ _ _
  have hlt : snorm (tᶜ.indicator (f n - g)) p μ ≤ Ennreal.ofReal (ε.to_real / 3) := by
    specialize hN n hn
    have :=
      snorm_sub_le_of_dist_bdd μ (lt_of_lt_of_leₓ Ennreal.zero_lt_one hp).Ne.symm hp' htm.compl _ fun x hx =>
        (dist_comm (g x) (f n x) ▸ (hN x hx).le :
          dist (f n x) (g x) ≤ ε.to_real / (3 * measure_univ_nnreal μ ^ (1 / p.to_real)))
    refine' le_transₓ this _
    rw [div_mul_eq_div_mul_one_div, ← Ennreal.of_real_to_real (measure_lt_top μ (tᶜ)).Ne,
      Ennreal.of_real_rpow_of_nonneg Ennreal.to_real_nonneg hdivp, ← Ennreal.of_real_mul, mul_assoc]
    · refine' Ennreal.of_real_le_of_real (mul_le_of_le_one_right hε'.le _)
      rw [mul_comm, mul_one_div, div_le_one]
      · refine'
          Real.rpow_le_rpow Ennreal.to_real_nonneg (Ennreal.to_real_le_of_le_of_real (measure_univ_nnreal_pos hμ).le _)
            hdivp
        rw [Ennreal.of_real_coe_nnreal, coe_measure_univ_nnreal]
        exact measure_mono (subset_univ _)
        
      · exact Real.rpow_pos_of_pos (measure_univ_nnreal_pos hμ) _
        
      
    · refine' mul_nonneg hε'.le (one_div_nonneg.2 hpow.le)
      
    · rw [div_mul_eq_div_mul_one_div]
      exact mul_nonneg hε'.le (one_div_nonneg.2 hpow.le)
      
  have : Ennreal.ofReal (ε.to_real / 3) = ε / 3 := by
    rw
      [Ennreal.of_real_div_of_pos
        (show (0 : ℝ) < 3 by
          norm_num),
      Ennreal.of_real_to_real h.ne]
    simp
  rw [this] at hnf hng hlt
  rw [snorm_neg, ← Ennreal.add_thirds ε, ← sub_eq_add_neg]
  exact add_le_add_three hnf hng hlt

/-- A sequence of uniformly integrable functions which converges μ-a.e. converges in Lp. -/
theorem tendsto_Lp_of_tendsto_ae {mβ : MeasurableSpace β} [BorelSpace β] [SecondCountableTopology β] [IsFiniteMeasure μ]
    (hp : 1 ≤ p) (hp' : p ≠ ∞) {f : ℕ → α → β} {g : α → β} (hf : ∀ n, AeMeasurable (f n) μ) (hg : Memℒp g p μ)
    (hui : UnifIntegrable f p μ) (hfg : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n => snorm (f n - g) p μ) atTop (𝓝 0) := by
  suffices tendsto (fun n : ℕ => snorm ((hf n).mk (f n) - hg.1.mk g) p μ) at_top (𝓝 0) by
    convert this
    exact funext fun n => snorm_congr_ae ((hf n).ae_eq_mk.sub hg.1.ae_eq_mk)
  refine'
    tendsto_Lp_of_tendsto_ae_of_meas μ hp hp' (fun n => (hf n).measurable_mk) hg.1.measurable_mk
      (hg.ae_eq hg.1.ae_eq_mk) (hui.ae_eq fun n => (hf n).ae_eq_mk) _
  have h_ae_forall_eq : ∀ᵐ x ∂μ, ∀ n, f n x = (hf n).mk (f n) x := by
    rw [ae_all_iff]
    exact fun n => (hf n).ae_eq_mk
  filter_upwards [hfg, h_ae_forall_eq, hg.1.ae_eq_mk] with x hx_tendsto hxf_eq hxg_eq
  rw [← hxg_eq]
  convert hx_tendsto
  ext1 n
  exact (hxf_eq n).symm

variable {mβ : MeasurableSpace β} [BorelSpace β]

variable {f : ℕ → α → β} {g : α → β}

include mβ

theorem unif_integrable_of_tendsto_Lp_zero (hp : 1 ≤ p) (hp' : p ≠ ∞) (hf : ∀ n, Memℒp (f n) p μ)
    (hf_tendsto : Tendsto (fun n => snorm (f n) p μ) atTop (𝓝 0)) : UnifIntegrable f p μ := by
  intro ε hε
  rw [Ennreal.tendsto_at_top_zero] at hf_tendsto
  obtain ⟨N, hN⟩ :=
    hf_tendsto (Ennreal.ofReal ε)
      (by
        simpa)
  set F : Finₓ N → α → β := fun n => f n
  have hF : ∀ n, mem_ℒp (F n) p μ := fun n => hf n
  obtain ⟨δ₁, hδpos₁, hδ₁⟩ := unif_integrable_fin μ hp hp' hF hε
  refine' ⟨δ₁, hδpos₁, fun n s hs hμs => _⟩
  by_cases' hn : n < N
  · exact hδ₁ ⟨n, hn⟩ s hs hμs
    
  · exact (snorm_indicator_le _).trans (hN n (not_ltₓ.1 hn))
    

variable [SecondCountableTopology β]

/-- Convergence in Lp implies uniform integrability. -/
theorem unif_integrable_of_tendsto_Lp (hp : 1 ≤ p) (hp' : p ≠ ∞) (hf : ∀ n, Memℒp (f n) p μ) (hg : Memℒp g p μ)
    (hfg : Tendsto (fun n => snorm (f n - g) p μ) atTop (𝓝 0)) : UnifIntegrable f p μ := by
  have : f = (fun n => g) + fun n => f n - g := by
    ext1 n
    simp
  rw [this]
  refine' unif_integrable.add _ _ hp (fun _ => hg.ae_measurable) fun n => (hf n).1.sub hg.ae_measurable
  · exact unif_integrable_const μ hp hp' hg
    
  · exact unif_integrable_of_tendsto_Lp_zero μ hp hp' (fun n => (hf n).sub hg) hfg
    

/-- Forward direction of Vitali's convergence theorem: if `f` is a sequence of uniformly integrable
functions that converge in measure to some function `g` in a finite measure space, then `f`
converge in Lp to `g`. -/
theorem tendsto_Lp_of_tendsto_in_measure [IsFiniteMeasure μ] (hp : 1 ≤ p) (hp' : p ≠ ∞) (hf : ∀ n, AeMeasurable (f n) μ)
    (hg : Memℒp g p μ) (hui : UnifIntegrable f p μ) (hfg : TendstoInMeasure μ f atTop g) :
    Tendsto (fun n => snorm (f n - g) p μ) atTop (𝓝 0) := by
  refine' tendsto_of_subseq_tendsto fun ns hns => _
  obtain ⟨ms, hms, hms'⟩ := tendsto_in_measure.exists_seq_tendsto_ae fun ε hε => (hfg ε hε).comp hns
  exact
    ⟨ms,
      tendsto_Lp_of_tendsto_ae μ hp hp' (fun _ => hf _) hg
        (fun ε hε =>
          let ⟨δ, hδ, hδ'⟩ := hui hε
          ⟨δ, hδ, fun i s hs hμs => hδ' _ s hs hμs⟩)
        hms'⟩

/-- **Vitali's convergence theorem**: A sequence of functions `f` converges to `g` in Lp if and
only if it is uniformly integrable and converges to `g` in measure. -/
theorem tendsto_in_measure_iff_tendsto_Lp [IsFiniteMeasure μ] (hp : 1 ≤ p) (hp' : p ≠ ∞) (hf : ∀ n, Memℒp (f n) p μ)
    (hg : Memℒp g p μ) :
    TendstoInMeasure μ f atTop g ∧ UnifIntegrable f p μ ↔ Tendsto (fun n => snorm (f n - g) p μ) atTop (𝓝 0) :=
  ⟨fun h => tendsto_Lp_of_tendsto_in_measure μ hp hp' (fun n => (hf n).1) hg h.2 h.1, fun h =>
    ⟨tendsto_in_measure_of_tendsto_snorm (lt_of_lt_of_leₓ Ennreal.zero_lt_one hp).Ne.symm (fun n => (hf n).AeMeasurable)
        hg.AeMeasurable h,
      unif_integrable_of_tendsto_Lp μ hp hp' hf hg h⟩⟩

end UnifIntegrable

end MeasureTheory

