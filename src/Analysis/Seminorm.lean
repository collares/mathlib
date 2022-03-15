/-
Copyright (c) 2019 Jean Lo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean Lo, Yaël Dillies, Moritz Doll
-/
import Mathbin.Analysis.LocallyConvex.Basic
import Mathbin.Data.Real.Pointwise
import Mathbin.Data.Real.Sqrt
import Mathbin.Topology.Algebra.FilterBasis
import Mathbin.Topology.Algebra.Module.LocallyConvex

/-!
# Seminorms

This file defines seminorms.

A seminorm is a function to the reals which is positive-semidefinite, absolutely homogeneous, and
subadditive. They are closely related to convex sets and a topological vector space is locally
convex if and only if its topology is induced by a family of seminorms.

## Main declarations

For a module over a normed ring:
* `seminorm`: A function to the reals that is positive-semidefinite, absolutely homogeneous, and
  subadditive.
* `norm_seminorm 𝕜 E`: The norm on `E` as a seminorm.

## References

* [H. H. Schaefer, *Topological Vector Spaces*][schaefer1966]

## TODO

Define and show equivalence of two notions of local convexity for a
topological vector space over ℝ or ℂ: that it has a local base of
balanced convex absorbent sets, and that it carries the initial
topology induced by a family of seminorms.

## Tags

seminorm, locally convex, LCTVS
-/


open NormedField Set

open_locale BigOperators Nnreal Pointwise TopologicalSpace

variable {R R' 𝕜 E F G ι ι' : Type _}

/-- A seminorm on a module over a normed ring is a function to the reals that is positive
semidefinite, positive homogeneous, and subadditive. -/
structure Seminorm (𝕜 : Type _) (E : Type _) [SemiNormedRing 𝕜] [AddMonoidₓ E] [HasScalar 𝕜 E] where
  toFun : E → ℝ
  smul' : ∀ a : 𝕜 x : E, to_fun (a • x) = ∥a∥ * to_fun x
  triangle' : ∀ x y : E, to_fun (x + y) ≤ to_fun x + to_fun y

namespace Seminorm

section SemiNormedRing

variable [SemiNormedRing 𝕜]

section AddMonoidₓ

variable [AddMonoidₓ E]

section HasScalar

variable [HasScalar 𝕜 E]

instance funLike : FunLike (Seminorm 𝕜 E) E fun _ => ℝ where
  coe := Seminorm.toFun
  coe_injective' := fun f g h => by
    cases f <;> cases g <;> congr

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`. -/
instance : CoeFun (Seminorm 𝕜 E) fun _ => E → ℝ :=
  ⟨fun p => p.toFun⟩

@[ext]
theorem ext {p q : Seminorm 𝕜 E} (h : ∀ x, (p : E → ℝ) x = q x) : p = q :=
  FunLike.ext p q h

instance : Zero (Seminorm 𝕜 E) :=
  ⟨{ toFun := 0, smul' := fun _ _ => (mul_zero _).symm, triangle' := fun _ _ => Eq.ge (zero_addₓ _) }⟩

@[simp]
theorem coe_zero : ⇑(0 : Seminorm 𝕜 E) = 0 :=
  rfl

@[simp]
theorem zero_apply (x : E) : (0 : Seminorm 𝕜 E) x = 0 :=
  rfl

instance : Inhabited (Seminorm 𝕜 E) :=
  ⟨0⟩

variable (p : Seminorm 𝕜 E) (c : 𝕜) (x y : E) (r : ℝ)

protected theorem smul : p (c • x) = ∥c∥ * p x :=
  p.smul' _ _

protected theorem triangle : p (x + y) ≤ p x + p y :=
  p.triangle' _ _

/-- Any action on `ℝ` which factors through `ℝ≥0` applies to a seminorm. -/
instance [HasScalar R ℝ] [HasScalar R ℝ≥0 ] [IsScalarTower R ℝ≥0 ℝ] : HasScalar R (Seminorm 𝕜 E) where
  smul := fun r p =>
    { toFun := fun x => r • p x,
      smul' := fun _ _ => by
        simp only [← smul_one_smul ℝ≥0 r (_ : ℝ), Nnreal.smul_def, smul_eq_mul]
        rw [p.smul, mul_left_commₓ],
      triangle' := fun _ _ => by
        simp only [← smul_one_smul ℝ≥0 r (_ : ℝ), Nnreal.smul_def, smul_eq_mul]
        exact (mul_le_mul_of_nonneg_left (p.triangle _ _) (Nnreal.coe_nonneg _)).trans_eq (mul_addₓ _ _ _) }

instance [HasScalar R ℝ] [HasScalar R ℝ≥0 ] [IsScalarTower R ℝ≥0 ℝ] [HasScalar R' ℝ] [HasScalar R' ℝ≥0 ]
    [IsScalarTower R' ℝ≥0 ℝ] [HasScalar R R'] [IsScalarTower R R' ℝ] : IsScalarTower R R' (Seminorm 𝕜 E) where
  smul_assoc := fun r a p => ext fun x => smul_assoc r a (p x)

theorem coe_smul [HasScalar R ℝ] [HasScalar R ℝ≥0 ] [IsScalarTower R ℝ≥0 ℝ] (r : R) (p : Seminorm 𝕜 E) :
    ⇑(r • p) = r • p :=
  rfl

@[simp]
theorem smul_apply [HasScalar R ℝ] [HasScalar R ℝ≥0 ] [IsScalarTower R ℝ≥0 ℝ] (r : R) (p : Seminorm 𝕜 E) (x : E) :
    (r • p) x = r • p x :=
  rfl

instance : Add (Seminorm 𝕜 E) where
  add := fun p q =>
    { toFun := fun x => p x + q x,
      smul' := fun a x => by
        rw [p.smul, q.smul, mul_addₓ],
      triangle' := fun _ _ =>
        LE.le.trans_eq (add_le_add (p.triangle _ _) (q.triangle _ _)) (add_add_add_commₓ _ _ _ _) }

theorem coe_add (p q : Seminorm 𝕜 E) : ⇑(p + q) = p + q :=
  rfl

@[simp]
theorem add_apply (p q : Seminorm 𝕜 E) (x : E) : (p + q) x = p x + q x :=
  rfl

instance : AddMonoidₓ (Seminorm 𝕜 E) :=
  FunLike.coe_injective.AddMonoid _ rfl coe_add fun p n => coe_smul n p

instance : OrderedCancelAddCommMonoid (Seminorm 𝕜 E) :=
  FunLike.coe_injective.OrderedCancelAddCommMonoid _ rfl coe_add fun p n => coe_smul n p

instance [Monoidₓ R] [MulAction R ℝ] [HasScalar R ℝ≥0 ] [IsScalarTower R ℝ≥0 ℝ] : MulAction R (Seminorm 𝕜 E) :=
  FunLike.coe_injective.MulAction _ coe_smul

variable (𝕜 E)

/-- `coe_fn` as an `add_monoid_hom`. Helper definition for showing that `seminorm 𝕜 E` is
a module. -/
@[simps]
def coeFnAddMonoidHom : AddMonoidHom (Seminorm 𝕜 E) (E → ℝ) :=
  ⟨coeFn, coe_zero, coe_add⟩

theorem coe_fn_add_monoid_hom_injective : Function.Injective (coeFnAddMonoidHom 𝕜 E) :=
  show @Function.Injective (Seminorm 𝕜 E) (E → ℝ) coeFn from FunLike.coe_injective

variable {𝕜 E}

instance [Monoidₓ R] [DistribMulAction R ℝ] [HasScalar R ℝ≥0 ] [IsScalarTower R ℝ≥0 ℝ] :
    DistribMulAction R (Seminorm 𝕜 E) :=
  (coe_fn_add_monoid_hom_injective 𝕜 E).DistribMulAction _ coe_smul

instance [Semiringₓ R] [Module R ℝ] [HasScalar R ℝ≥0 ] [IsScalarTower R ℝ≥0 ℝ] : Module R (Seminorm 𝕜 E) :=
  (coe_fn_add_monoid_hom_injective 𝕜 E).Module R _ coe_smul

-- TODO: define `has_Sup` too, from the skeleton at
-- https://github.com/leanprover-community/mathlib/pull/11329#issuecomment-1008915345
noncomputable instance : HasSup (Seminorm 𝕜 E) where
  sup := fun p q =>
    { toFun := p⊔q,
      triangle' := fun x y =>
        sup_le ((p.triangle x y).trans <| add_le_add le_sup_left le_sup_left)
          ((q.triangle x y).trans <| add_le_add le_sup_right le_sup_right),
      smul' := fun x v =>
        (congr_arg2ₓ max (p.smul x v) (q.smul x v)).trans <| (mul_max_of_nonneg _ _ <| norm_nonneg x).symm }

@[simp]
theorem coe_sup (p q : Seminorm 𝕜 E) : ⇑(p⊔q) = p⊔q :=
  rfl

theorem sup_apply (p q : Seminorm 𝕜 E) (x : E) : (p⊔q) x = p x⊔q x :=
  rfl

theorem smul_sup [HasScalar R ℝ] [HasScalar R ℝ≥0 ] [IsScalarTower R ℝ≥0 ℝ] (r : R) (p q : Seminorm 𝕜 E) :
    r • (p⊔q) = r • p⊔r • q :=
  have real.smul_max : ∀ x y : ℝ, r • max x y = max (r • x) (r • y) := fun x y => by
    simpa only [← smul_eq_mul, ← Nnreal.smul_def, smul_one_smul ℝ≥0 r (_ : ℝ)] using
      mul_max_of_nonneg x y (r • 1 : ℝ≥0 ).Prop
  ext fun x => real.smul_max _ _

instance : PartialOrderₓ (Seminorm 𝕜 E) :=
  PartialOrderₓ.lift _ FunLike.coe_injective

theorem le_def (p q : Seminorm 𝕜 E) : p ≤ q ↔ (p : E → ℝ) ≤ q :=
  Iff.rfl

theorem lt_def (p q : Seminorm 𝕜 E) : p < q ↔ (p : E → ℝ) < q :=
  Iff.rfl

noncomputable instance : SemilatticeSup (Seminorm 𝕜 E) :=
  Function.Injective.semilatticeSup _ FunLike.coe_injective coe_sup

end HasScalar

section SmulWithZero

variable [SmulWithZero 𝕜 E] (p : Seminorm 𝕜 E)

@[simp]
protected theorem zero : p 0 = 0 :=
  calc
    p 0 = p ((0 : 𝕜) • 0) := by
      rw [zero_smul]
    _ = 0 := by
      rw [p.smul, norm_zero, zero_mul]
    

end SmulWithZero

end AddMonoidₓ

section Module

variable [AddCommGroupₓ E] [AddCommGroupₓ F] [AddCommGroupₓ G]

variable [Module 𝕜 E] [Module 𝕜 F] [Module 𝕜 G]

variable [HasScalar R ℝ] [HasScalar R ℝ≥0 ] [IsScalarTower R ℝ≥0 ℝ]

/-- Composition of a seminorm with a linear map is a seminorm. -/
def comp (p : Seminorm 𝕜 F) (f : E →ₗ[𝕜] F) : Seminorm 𝕜 E where
  toFun := fun x => p (f x)
  smul' := fun _ _ => (congr_argₓ p (f.map_smul _ _)).trans (p.smul _ _)
  triangle' := fun _ _ => Eq.trans_le (congr_argₓ p (f.map_add _ _)) (p.triangle _ _)

theorem coe_comp (p : Seminorm 𝕜 F) (f : E →ₗ[𝕜] F) : ⇑(p.comp f) = p ∘ f :=
  rfl

@[simp]
theorem comp_apply (p : Seminorm 𝕜 F) (f : E →ₗ[𝕜] F) (x : E) : (p.comp f) x = p (f x) :=
  rfl

@[simp]
theorem comp_id (p : Seminorm 𝕜 E) : p.comp LinearMap.id = p :=
  ext fun _ => rfl

@[simp]
theorem comp_zero (p : Seminorm 𝕜 F) : p.comp (0 : E →ₗ[𝕜] F) = 0 :=
  ext fun _ => Seminorm.zero _

@[simp]
theorem zero_comp (f : E →ₗ[𝕜] F) : (0 : Seminorm 𝕜 F).comp f = 0 :=
  ext fun _ => rfl

theorem comp_comp (p : Seminorm 𝕜 G) (g : F →ₗ[𝕜] G) (f : E →ₗ[𝕜] F) : p.comp (g.comp f) = (p.comp g).comp f :=
  ext fun _ => rfl

theorem add_comp (p q : Seminorm 𝕜 F) (f : E →ₗ[𝕜] F) : (p + q).comp f = p.comp f + q.comp f :=
  ext fun _ => rfl

theorem comp_triangle (p : Seminorm 𝕜 F) (f g : E →ₗ[𝕜] F) : p.comp (f + g) ≤ p.comp f + p.comp g := fun _ =>
  p.triangle _ _

theorem smul_comp (p : Seminorm 𝕜 F) (f : E →ₗ[𝕜] F) (c : R) : (c • p).comp f = c • p.comp f :=
  ext fun _ => rfl

theorem comp_mono {p : Seminorm 𝕜 F} {q : Seminorm 𝕜 F} (f : E →ₗ[𝕜] F) (hp : p ≤ q) : p.comp f ≤ q.comp f := fun _ =>
  hp _

/-- The composition as an `add_monoid_hom`. -/
@[simps]
def pullback (f : E →ₗ[𝕜] F) : AddMonoidHom (Seminorm 𝕜 F) (Seminorm 𝕜 E) :=
  ⟨fun p => p.comp f, zero_comp f, fun p q => add_comp p q f⟩

section NormOneClass

variable [NormOneClass 𝕜] (p : Seminorm 𝕜 E) (x y : E) (r : ℝ)

@[simp]
protected theorem neg : p (-x) = p x :=
  calc
    p (-x) = p ((-1 : 𝕜) • x) := by
      rw [neg_one_smul]
    _ = p x := by
      rw [p.smul, norm_neg, norm_one, one_mulₓ]
    

protected theorem sub_le : p (x - y) ≤ p x + p y :=
  calc
    p (x - y) = p (x + -y) := by
      rw [sub_eq_add_neg]
    _ ≤ p x + p (-y) := p.triangle x (-y)
    _ = p x + p y := by
      rw [p.neg]
    

theorem nonneg : 0 ≤ p x :=
  have h : 0 ≤ 2 * p x :=
    calc
      0 = p (x + -x) := by
        rw [add_neg_selfₓ, p.zero]
      _ ≤ p x + p (-x) := p.triangle _ _
      _ = 2 * p x := by
        rw [p.neg, two_mul]
      
  nonneg_of_mul_nonneg_left h zero_lt_two

theorem sub_rev : p (x - y) = p (y - x) := by
  rw [← neg_sub, p.neg]

/-- The direct path from 0 to y is shorter than the path with x "inserted" in between. -/
theorem le_insert : p y ≤ p x + p (x - y) :=
  calc
    p y = p (x - (x - y)) := by
      rw [sub_sub_cancel]
    _ ≤ p x + p (x - y) := p.sub_le _ _
    

/-- The direct path from 0 to x is shorter than the path with y "inserted" in between. -/
theorem le_insert' : p x ≤ p y + p (x - y) := by
  rw [sub_rev]
  exact le_insert _ _ _

instance : OrderBot (Seminorm 𝕜 E) :=
  ⟨0, nonneg⟩

@[simp]
theorem coe_bot : ⇑(⊥ : Seminorm 𝕜 E) = 0 :=
  rfl

theorem bot_eq_zero : (⊥ : Seminorm 𝕜 E) = 0 :=
  rfl

theorem smul_le_smul {p q : Seminorm 𝕜 E} {a b : ℝ≥0 } (hpq : p ≤ q) (hab : a ≤ b) : a • p ≤ b • q := by
  simp_rw [le_def, Pi.le_def, coe_smul]
  intro x
  simp_rw [Pi.smul_apply, Nnreal.smul_def, smul_eq_mul]
  exact mul_le_mul hab (hpq x) (nonneg p x) (Nnreal.coe_nonneg b)

theorem finset_sup_apply (p : ι → Seminorm 𝕜 E) (s : Finset ι) (x : E) :
    s.sup p x = ↑(s.sup fun i => ⟨p i x, nonneg (p i) x⟩ : ℝ≥0 ) := by
  induction' s using Finset.cons_induction_on with a s ha ih
  · rw [Finset.sup_empty, Finset.sup_empty, coe_bot, _root_.bot_eq_zero, Pi.zero_apply, Nonneg.coe_zero]
    
  · rw [Finset.sup_cons, Finset.sup_cons, coe_sup, sup_eq_max, Pi.sup_apply, sup_eq_max, Nnreal.coe_max, Subtype.coe_mk,
      ih]
    

theorem finset_sup_le_sum (p : ι → Seminorm 𝕜 E) (s : Finset ι) : s.sup p ≤ ∑ i in s, p i := by
  classical
  refine' finset.sup_le_iff.mpr _
  intro i hi
  rw [Finset.sum_eq_sum_diff_singleton_add hi, le_add_iff_nonneg_left]
  exact bot_le

theorem finset_sup_apply_le {p : ι → Seminorm 𝕜 E} {s : Finset ι} {x : E} {a : ℝ} (ha : 0 ≤ a)
    (h : ∀ i, i ∈ s → p i x ≤ a) : s.sup p x ≤ a := by
  lift a to ℝ≥0 using ha
  rw [finset_sup_apply, Nnreal.coe_le_coe]
  exact Finset.sup_le h

theorem finset_sup_apply_lt {p : ι → Seminorm 𝕜 E} {s : Finset ι} {x : E} {a : ℝ} (ha : 0 < a)
    (h : ∀ i, i ∈ s → p i x < a) : s.sup p x < a := by
  lift a to ℝ≥0 using ha.le
  rw [finset_sup_apply, Nnreal.coe_lt_coe, Finset.sup_lt_iff]
  · exact h
    
  · exact nnreal.coe_pos.mpr ha
    

end NormOneClass

end Module

end SemiNormedRing

section SemiNormedCommRing

variable [SemiNormedCommRing 𝕜] [AddCommGroupₓ E] [AddCommGroupₓ F] [Module 𝕜 E] [Module 𝕜 F]

theorem comp_smul (p : Seminorm 𝕜 F) (f : E →ₗ[𝕜] F) (c : 𝕜) : p.comp (c • f) = ∥c∥₊ • p.comp f :=
  ext fun _ => by
    rw [comp_apply, smul_apply, LinearMap.smul_apply, p.smul, Nnreal.smul_def, coe_nnnorm, smul_eq_mul, comp_apply]

theorem comp_smul_apply (p : Seminorm 𝕜 F) (f : E →ₗ[𝕜] F) (c : 𝕜) (x : E) : p.comp (c • f) x = ∥c∥ * p (f x) :=
  p.smul _ _

end SemiNormedCommRing

section NormedField

variable [NormedField 𝕜] [AddCommGroupₓ E] [Module 𝕜 E]

private theorem bdd_below_range_add (x : E) (p q : Seminorm 𝕜 E) : BddBelow (Range fun u : E => p u + q (x - u)) := by
  use 0
  rintro _ ⟨x, rfl⟩
  exact add_nonneg (p.nonneg _) (q.nonneg _)

noncomputable instance : HasInf (Seminorm 𝕜 E) where
  inf := fun p q =>
    { toFun := fun x => ⨅ u : E, p u + q (x - u),
      triangle' := fun x y => by
        refine' le_cinfi_add_cinfi fun u v => _
        apply cinfi_le_of_le (bdd_below_range_add _ _ _) (v + u)
        dsimp only
        convert add_le_add (p.triangle v u) (q.triangle (y - v) (x - u)) using 1
        · rw
            [show x + y - (v + u) = y - v + (x - u) by
              abel]
          
        · abel
          ,
      smul' := fun a x => by
        obtain rfl | ha := eq_or_ne a 0
        · simp_rw [norm_zero, zero_mul, zero_smul, zero_sub, Seminorm.neg]
          refine'
            cinfi_eq_of_forall_ge_of_forall_gt_exists_lt (fun i => add_nonneg (p.nonneg _) (q.nonneg _)) fun x hx =>
              ⟨0, by
                rwa [p.zero, q.zero, add_zeroₓ]⟩
          
        simp_rw [Real.mul_infi_of_nonneg (norm_nonneg a), mul_addₓ, ← p.smul, ← q.smul, smul_sub]
        refine' infi_congr ((· • ·) a⁻¹ : E → E) (fun u => ⟨a • u, inv_smul_smul₀ ha u⟩) fun u => _
        rw [smul_inv_smul₀ ha] }

@[simp]
theorem inf_apply (p q : Seminorm 𝕜 E) (x : E) : (p⊓q) x = ⨅ u : E, p u + q (x - u) :=
  rfl

noncomputable instance : Lattice (Seminorm 𝕜 E) :=
  { Seminorm.semilatticeSup with inf := (·⊓·),
    inf_le_left := fun p q x => by
      apply cinfi_le_of_le (bdd_below_range_add _ _ _) x
      simp only [sub_self, Seminorm.zero, add_zeroₓ],
    inf_le_right := fun p q x => by
      apply cinfi_le_of_le (bdd_below_range_add _ _ _) (0 : E)
      simp only [sub_self, Seminorm.zero, zero_addₓ, sub_zero],
    le_inf := fun a b c hab hac x => le_cinfi fun u => le_transₓ (a.le_insert' _ _) (add_le_add (hab _) (hac _)) }

theorem smul_inf [HasScalar R ℝ] [HasScalar R ℝ≥0 ] [IsScalarTower R ℝ≥0 ℝ] (r : R) (p q : Seminorm 𝕜 E) :
    r • (p⊓q) = r • p⊓r • q := by
  ext
  simp_rw [smul_apply, inf_apply, smul_apply, ← smul_one_smul ℝ≥0 r (_ : ℝ), Nnreal.smul_def, smul_eq_mul,
    Real.mul_infi_of_nonneg (Subtype.prop _), mul_addₓ]

end NormedField

/-! ### Seminorm ball -/


section SemiNormedRing

variable [SemiNormedRing 𝕜]

section AddCommGroupₓ

variable [AddCommGroupₓ E]

section HasScalar

variable [HasScalar 𝕜 E] (p : Seminorm 𝕜 E)

/-- The ball of radius `r` at `x` with respect to seminorm `p` is the set of elements `y` with
`p (y - x) < `r`. -/
def Ball (x : E) (r : ℝ) :=
  { y : E | p (y - x) < r }

variable {x y : E} {r : ℝ}

@[simp]
theorem mem_ball : y ∈ Ball p x r ↔ p (y - x) < r :=
  Iff.rfl

theorem mem_ball_zero : y ∈ Ball p 0 r ↔ p y < r := by
  rw [mem_ball, sub_zero]

theorem ball_zero_eq : Ball p 0 r = { y : E | p y < r } :=
  Set.ext fun x => p.mem_ball_zero

@[simp]
theorem ball_zero' (x : E) (hr : 0 < r) : Ball (0 : Seminorm 𝕜 E) x r = Set.Univ := by
  rw [Set.eq_univ_iff_forall, ball]
  simp [hr]

theorem ball_smul (p : Seminorm 𝕜 E) {c : Nnreal} (hc : 0 < c) (r : ℝ) (x : E) : (c • p).ball x r = p.ball x (r / c) :=
  by
  ext
  rw [mem_ball, mem_ball, smul_apply, Nnreal.smul_def, smul_eq_mul, mul_comm, lt_div_iff (nnreal.coe_pos.mpr hc)]

theorem ball_sup (p : Seminorm 𝕜 E) (q : Seminorm 𝕜 E) (e : E) (r : ℝ) : Ball (p⊔q) e r = Ball p e r ∩ Ball q e r := by
  simp_rw [ball, ← Set.set_of_and, coe_sup, Pi.sup_apply, sup_lt_iff]

theorem ball_finset_sup' (p : ι → Seminorm 𝕜 E) (s : Finset ι) (H : s.Nonempty) (e : E) (r : ℝ) :
    Ball (s.sup' H p) e r = s.inf' H fun i => Ball (p i) e r := by
  induction' H using Finset.Nonempty.cons_induction with a a s ha hs ih
  · classical
    simp
    
  · rw [Finset.sup'_cons hs, Finset.inf'_cons hs, ball_sup, inf_eq_inter, ih]
    

theorem ball_mono {p : Seminorm 𝕜 E} {r₁ r₂ : ℝ} (h : r₁ ≤ r₂) : p.ball x r₁ ⊆ p.ball x r₂ := fun hx : _ < _ =>
  hx.trans_le h

theorem ball_antitone {p q : Seminorm 𝕜 E} (h : q ≤ p) : p.ball x r ⊆ q.ball x r := fun _ => (h _).trans_lt

theorem ball_add_ball_subset (p : Seminorm 𝕜 E) (r₁ r₂ : ℝ) (x₁ x₂ : E) :
    p.ball (x₁ : E) r₁ + p.ball (x₂ : E) r₂ ⊆ p.ball (x₁ + x₂) (r₁ + r₂) := by
  rintro x ⟨y₁, y₂, hy₁, hy₂, rfl⟩
  rw [mem_ball, add_sub_comm]
  exact (p.triangle _ _).trans_lt (add_lt_add hy₁ hy₂)

end HasScalar

section Module

variable [Module 𝕜 E]

variable [AddCommGroupₓ F] [Module 𝕜 F]

theorem ball_comp (p : Seminorm 𝕜 F) (f : E →ₗ[𝕜] F) (x : E) (r : ℝ) : (p.comp f).ball x r = f ⁻¹' p.ball (f x) r := by
  ext
  simp_rw [ball, mem_preimage, comp_apply, Set.mem_set_of_eq, map_sub]

section NormOneClass

variable [NormOneClass 𝕜] (p : Seminorm 𝕜 E)

@[simp]
theorem ball_bot {r : ℝ} (x : E) (hr : 0 < r) : Ball (⊥ : Seminorm 𝕜 E) x r = Set.Univ :=
  ball_zero' x hr

/-- Seminorm-balls at the origin are balanced. -/
theorem balanced_ball_zero (r : ℝ) : Balanced 𝕜 (Ball p 0 r) := by
  rintro a ha x ⟨y, hy, hx⟩
  rw [mem_ball_zero, ← hx, p.smul]
  calc _ ≤ p y := mul_le_of_le_one_left (p.nonneg _) ha _ < r := by
      rwa [mem_ball_zero] at hy

theorem ball_finset_sup_eq_Inter (p : ι → Seminorm 𝕜 E) (s : Finset ι) (x : E) {r : ℝ} (hr : 0 < r) :
    Ball (s.sup p) x r = ⋂ i ∈ s, Ball (p i) x r := by
  lift r to Nnreal using hr.le
  simp_rw [ball, Inter_set_of, finset_sup_apply, Nnreal.coe_lt_coe, Finset.sup_lt_iff (show ⊥ < r from hr), ←
    Nnreal.coe_lt_coe, Subtype.coe_mk]

theorem ball_finset_sup (p : ι → Seminorm 𝕜 E) (s : Finset ι) (x : E) {r : ℝ} (hr : 0 < r) :
    Ball (s.sup p) x r = s.inf fun i => Ball (p i) x r := by
  rw [Finset.inf_eq_infi]
  exact ball_finset_sup_eq_Inter _ _ _ hr

theorem ball_smul_ball (p : Seminorm 𝕜 E) (r₁ r₂ : ℝ) : Metric.Ball (0 : 𝕜) r₁ • p.ball 0 r₂ ⊆ p.ball 0 (r₁ * r₂) := by
  rw [Set.subset_def]
  intro x hx
  rw [Set.mem_smul] at hx
  rcases hx with ⟨a, y, ha, hy, hx⟩
  rw [← hx, mem_ball_zero, Seminorm.smul]
  exact mul_lt_mul'' (mem_ball_zero_iff.mp ha) (p.mem_ball_zero.mp hy) (norm_nonneg a) (p.nonneg y)

end NormOneClass

end Module

end AddCommGroupₓ

end SemiNormedRing

section NormedField

variable [NormedField 𝕜] [AddCommGroupₓ E] [Module 𝕜 E] (p : Seminorm 𝕜 E) {A B : Set E} {a : 𝕜} {r : ℝ} {x : E}

/-- Seminorm-balls at the origin are absorbent. -/
protected theorem absorbent_ball_zero (hr : 0 < r) : Absorbent 𝕜 (Ball p (0 : E) r) := by
  rw [absorbent_iff_nonneg_lt]
  rintro x
  have hxr : 0 ≤ p x / r := div_nonneg (p.nonneg _) hr.le
  refine' ⟨p x / r, hxr, fun a ha => _⟩
  have ha₀ : 0 < ∥a∥ := hxr.trans_lt ha
  refine' ⟨a⁻¹ • x, _, smul_inv_smul₀ (norm_pos_iff.1 ha₀) x⟩
  rwa [mem_ball_zero, p.smul, norm_inv, inv_mul_lt_iff ha₀, ← div_lt_iff hr]

/-- Seminorm-balls containing the origin are absorbent. -/
protected theorem absorbent_ball (hpr : p x < r) : Absorbent 𝕜 (Ball p x r) := by
  refine' (p.absorbent_ball_zero <| sub_pos.2 hpr).Subset fun y hy => _
  rw [p.mem_ball_zero] at hy
  exact p.mem_ball.2 ((p.sub_le _ _).trans_lt <| add_lt_of_lt_sub_right hy)

theorem symmetric_ball_zero (r : ℝ) (hx : x ∈ Ball p 0 r) : -x ∈ Ball p 0 r :=
  balanced_ball_zero p r (-1)
    (by
      rw [norm_neg, norm_one])
    ⟨x, hx, by
      rw [neg_smul, one_smul]⟩

@[simp]
theorem neg_ball (p : Seminorm 𝕜 E) (r : ℝ) (x : E) : -Ball p x r = Ball p (-x) r := by
  ext
  rw [mem_neg, mem_ball, mem_ball, ← neg_add', sub_neg_eq_add, p.neg]

@[simp]
theorem smul_ball_preimage (p : Seminorm 𝕜 E) (y : E) (r : ℝ) (a : 𝕜) (ha : a ≠ 0) :
    (· • ·) a ⁻¹' p.ball y r = p.ball (a⁻¹ • y) (r / ∥a∥) :=
  Set.ext fun _ => by
    rw [mem_preimage, mem_ball, mem_ball, lt_div_iff (norm_pos_iff.mpr ha), mul_comm, ← p.smul, smul_sub,
      smul_inv_smul₀ ha]

end NormedField

section Convex

variable [NormedField 𝕜] [AddCommGroupₓ E] [NormedSpace ℝ 𝕜] [Module 𝕜 E]

section HasScalar

variable [HasScalar ℝ E] [IsScalarTower ℝ 𝕜 E] (p : Seminorm 𝕜 E)

/-- A seminorm is convex. Also see `convex_on_norm`. -/
protected theorem convex_on : ConvexOn ℝ Univ p := by
  refine' ⟨convex_univ, fun x y _ _ a b ha hb hab => _⟩
  calc p (a • x + b • y) ≤ p (a • x) + p (b • y) := p.triangle _ _ _ = ∥a • (1 : 𝕜)∥ * p x + ∥b • (1 : 𝕜)∥ * p y := by
      rw [← p.smul, ← p.smul, smul_one_smul, smul_one_smul]_ = a * p x + b * p y := by
      rw [norm_smul, norm_smul, norm_one, mul_oneₓ, mul_oneₓ, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]

end HasScalar

section Module

variable [Module ℝ E] [IsScalarTower ℝ 𝕜 E] (p : Seminorm 𝕜 E) (x : E) (r : ℝ)

/-- Seminorm-balls are convex. -/
theorem convex_ball : Convex ℝ (Ball p x r) := by
  convert (p.convex_on.translate_left (-x)).convex_lt r
  ext y
  rw [preimage_univ, sep_univ, p.mem_ball, sub_eq_add_neg]
  rfl

end Module

end Convex

end Seminorm

/-! ### The norm as a seminorm -/


section normSeminorm

variable (𝕜 E) [NormedField 𝕜] [SemiNormedGroup E] [NormedSpace 𝕜 E] {r : ℝ}

/-- The norm of a seminormed group as a seminorm. -/
def normSeminorm : Seminorm 𝕜 E :=
  ⟨norm, norm_smul, norm_add_le⟩

@[simp]
theorem coe_norm_seminorm : ⇑(normSeminorm 𝕜 E) = norm :=
  rfl

@[simp]
theorem ball_norm_seminorm : (normSeminorm 𝕜 E).ball = Metric.Ball := by
  ext x r y
  simp only [Seminorm.mem_ball, Metric.mem_ball, coe_norm_seminorm, dist_eq_norm]

variable {𝕜 E} {x : E}

/-- Balls at the origin are absorbent. -/
theorem absorbent_ball_zero (hr : 0 < r) : Absorbent 𝕜 (Metric.Ball (0 : E) r) := by
  rw [← ball_norm_seminorm 𝕜]
  exact (normSeminorm _ _).absorbent_ball_zero hr

/-- Balls containing the origin are absorbent. -/
theorem absorbent_ball (hx : ∥x∥ < r) : Absorbent 𝕜 (Metric.Ball x r) := by
  rw [← ball_norm_seminorm 𝕜]
  exact (normSeminorm _ _).absorbent_ball hx

/-- Balls at the origin are balanced. -/
theorem balanced_ball_zero [NormOneClass 𝕜] : Balanced 𝕜 (Metric.Ball (0 : E) r) := by
  rw [← ball_norm_seminorm 𝕜]
  exact (normSeminorm _ _).balanced_ball_zero r

end normSeminorm

/-! ### Topology induced by a family of seminorms -/


namespace Seminorm

section FilterBasis

variable [NormedField 𝕜] [AddCommGroupₓ E] [Module 𝕜 E]

/-- A filter basis for the neighborhood filter of 0. -/
def SeminormBasisZero (p : ι → Seminorm 𝕜 E) : Set (Set E) :=
  ⋃ (s : Finset ι) (r) (hr : 0 < r), singleton <| Ball (s.sup p) (0 : E) r

theorem seminorm_basis_zero_iff (p : ι → Seminorm 𝕜 E) (U : Set E) :
    U ∈ SeminormBasisZero p ↔ ∃ (i : Finset ι)(r : _)(hr : 0 < r), U = Ball (i.sup p) 0 r := by
  simp only [seminorm_basis_zero, mem_Union, mem_singleton_iff]

theorem seminorm_basis_zero_mem (p : ι → Seminorm 𝕜 E) (i : Finset ι) {r : ℝ} (hr : 0 < r) :
    (i.sup p).ball 0 r ∈ SeminormBasisZero p :=
  (seminorm_basis_zero_iff _ _).mpr ⟨i, _, hr, rfl⟩

theorem seminorm_basis_zero_singleton_mem (p : ι → Seminorm 𝕜 E) (i : ι) {r : ℝ} (hr : 0 < r) :
    (p i).ball 0 r ∈ SeminormBasisZero p :=
  (seminorm_basis_zero_iff _ _).mpr
    ⟨{i}, _, hr, by
      rw [Finset.sup_singleton]⟩

theorem seminorm_basis_zero_nonempty (p : ι → Seminorm 𝕜 E) [Nonempty ι] : (SeminormBasisZero p).Nonempty := by
  let i := Classical.arbitrary ι
  refine' set.nonempty_def.mpr ⟨ball (p i) 0 1, _⟩
  exact seminorm_basis_zero_singleton_mem _ i zero_lt_one

theorem seminorm_basis_zero_intersect (p : ι → Seminorm 𝕜 E) (U V : Set E) (hU : U ∈ SeminormBasisZero p)
    (hV : V ∈ SeminormBasisZero p) : ∃ (z : Set E)(H : z ∈ SeminormBasisZero p), z ⊆ U ∩ V := by
  classical
  rcases(seminorm_basis_zero_iff p U).mp hU with ⟨s, r₁, hr₁, hU⟩
  rcases(seminorm_basis_zero_iff p V).mp hV with ⟨t, r₂, hr₂, hV⟩
  use ((s ∪ t).sup p).ball 0 (min r₁ r₂)
  refine' ⟨seminorm_basis_zero_mem p (s ∪ t) (lt_min_iff.mpr ⟨hr₁, hr₂⟩), _⟩
  rw [hU, hV, ball_finset_sup_eq_Inter _ _ _ (lt_min_iff.mpr ⟨hr₁, hr₂⟩), ball_finset_sup_eq_Inter _ _ _ hr₁,
    ball_finset_sup_eq_Inter _ _ _ hr₂]
  exact
    Set.subset_inter (Set.Inter₂_mono' fun i hi => ⟨i, Finset.subset_union_left _ _ hi, ball_mono <| min_le_leftₓ _ _⟩)
      (Set.Inter₂_mono' fun i hi => ⟨i, Finset.subset_union_right _ _ hi, ball_mono <| min_le_rightₓ _ _⟩)

theorem seminorm_basis_zero_zero (p : ι → Seminorm 𝕜 E) U (hU : U ∈ SeminormBasisZero p) : (0 : E) ∈ U := by
  rcases(seminorm_basis_zero_iff p U).mp hU with ⟨ι', r, hr, hU⟩
  rw [hU, mem_ball_zero, (ι'.sup p).zero]
  exact hr

theorem seminorm_basis_zero_add (p : ι → Seminorm 𝕜 E) U (hU : U ∈ SeminormBasisZero p) :
    ∃ (V : Set E)(H : V ∈ SeminormBasisZero p), V + V ⊆ U := by
  rcases(seminorm_basis_zero_iff p U).mp hU with ⟨s, r, hr, hU⟩
  use (s.sup p).ball 0 (r / 2)
  refine' ⟨seminorm_basis_zero_mem p s (div_pos hr zero_lt_two), _⟩
  refine' Set.Subset.trans (ball_add_ball_subset (s.sup p) (r / 2) (r / 2) 0 0) _
  rw [hU, add_zeroₓ, add_halves']

theorem seminorm_basis_zero_neg (p : ι → Seminorm 𝕜 E) U (hU' : U ∈ SeminormBasisZero p) :
    ∃ (V : Set E)(H : V ∈ SeminormBasisZero p), V ⊆ (fun x : E => -x) ⁻¹' U := by
  rcases(seminorm_basis_zero_iff p U).mp hU' with ⟨s, r, hr, hU⟩
  rw [hU, neg_preimage, neg_ball (s.sup p), neg_zero]
  exact ⟨U, hU', Eq.subset hU⟩

/-- The `add_group_filter_basis` induced by the filter basis `seminorm_basis_zero`. -/
def seminormAddGroupFilterBasis [Nonempty ι] (p : ι → Seminorm 𝕜 E) : AddGroupFilterBasis E :=
  addGroupFilterBasisOfComm (SeminormBasisZero p) (seminorm_basis_zero_nonempty p) (seminorm_basis_zero_intersect p)
    (seminorm_basis_zero_zero p) (seminorm_basis_zero_add p) (seminorm_basis_zero_neg p)

theorem seminorm_basis_zero_smul_right (p : ι → Seminorm 𝕜 E) (v : E) (U : Set E) (hU : U ∈ SeminormBasisZero p) :
    ∀ᶠ x : 𝕜 in 𝓝 0, x • v ∈ U := by
  rcases(seminorm_basis_zero_iff p U).mp hU with ⟨s, r, hr, hU⟩
  rw [hU, Filter.eventually_iff]
  simp_rw [(s.sup p).mem_ball_zero, (s.sup p).smul]
  by_cases' h : 0 < (s.sup p) v
  · simp_rw [(lt_div_iff h).symm]
    rw [← _root_.ball_zero_eq]
    exact Metric.ball_mem_nhds 0 (div_pos hr h)
    
  simp_rw [le_antisymmₓ (not_lt.mp h) ((s.sup p).Nonneg v), mul_zero, hr]
  exact IsOpen.mem_nhds is_open_univ (mem_univ 0)

variable [Nonempty ι]

theorem seminorm_basis_zero_smul (p : ι → Seminorm 𝕜 E) U (hU : U ∈ SeminormBasisZero p) :
    ∃ (V : Set 𝕜)(H : V ∈ 𝓝 (0 : 𝕜))(W : Set E)(H : W ∈ (seminormAddGroupFilterBasis p).Sets), V • W ⊆ U := by
  rcases(seminorm_basis_zero_iff p U).mp hU with ⟨s, r, hr, hU⟩
  refine' ⟨Metric.Ball 0 r.sqrt, Metric.ball_mem_nhds 0 (real.sqrt_pos.mpr hr), _⟩
  refine' ⟨(s.sup p).ball 0 r.sqrt, seminorm_basis_zero_mem p s (real.sqrt_pos.mpr hr), _⟩
  refine' Set.Subset.trans (ball_smul_ball (s.sup p) r.sqrt r.sqrt) _
  rw [hU, Real.mul_self_sqrt (le_of_ltₓ hr)]

theorem seminorm_basis_zero_smul_left (p : ι → Seminorm 𝕜 E) (x : 𝕜) (U : Set E) (hU : U ∈ SeminormBasisZero p) :
    ∃ (V : Set E)(H : V ∈ (seminormAddGroupFilterBasis p).Sets), V ⊆ (fun y : E => x • y) ⁻¹' U := by
  rcases(seminorm_basis_zero_iff p U).mp hU with ⟨s, r, hr, hU⟩
  rw [hU]
  by_cases' h : x ≠ 0
  · rw [(s.sup p).smul_ball_preimage 0 r x h, smul_zero]
    use (s.sup p).ball 0 (r / ∥x∥)
    exact ⟨seminorm_basis_zero_mem p s (div_pos hr (norm_pos_iff.mpr h)), subset.rfl⟩
    
  refine' ⟨(s.sup p).ball 0 r, seminorm_basis_zero_mem p s hr, _⟩
  simp only [not_ne_iff.mp h, subset_def, mem_ball_zero, hr, mem_univ, Seminorm.zero, implies_true_iff,
    preimage_const_of_mem, zero_smul]

/-- The `module_filter_basis` induced by the filter basis `seminorm_basis_zero`. -/
def seminormModuleFilterBasis (p : ι → Seminorm 𝕜 E) : ModuleFilterBasis 𝕜 E where
  toAddGroupFilterBasis := seminormAddGroupFilterBasis p
  smul' := seminorm_basis_zero_smul p
  smul_left' := seminorm_basis_zero_smul_left p
  smul_right' := seminorm_basis_zero_smul_right p

end FilterBasis

section Bounded

variable [NormedField 𝕜] [AddCommGroupₓ E] [Module 𝕜 E] [AddCommGroupₓ F] [Module 𝕜 F]

/-- The proposition that a linear map is bounded between spaces with families of seminorms. -/
def IsBounded (p : ι → Seminorm 𝕜 E) (q : ι' → Seminorm 𝕜 F) (f : E →ₗ[𝕜] F) : Prop :=
  ∀ i, ∃ s : Finset ι, ∃ C : ℝ≥0 , C ≠ 0 ∧ (q i).comp f ≤ C • s.sup p

theorem is_bounded_const (ι' : Type _) [Nonempty ι'] {p : ι → Seminorm 𝕜 E} {q : Seminorm 𝕜 F} (f : E →ₗ[𝕜] F) :
    IsBounded p (fun _ : ι' => q) f ↔ ∃ (s : Finset ι)(C : ℝ≥0 ), C ≠ 0 ∧ q.comp f ≤ C • s.sup p := by
  simp only [is_bounded, forall_const]

theorem const_is_bounded (ι : Type _) [Nonempty ι] {p : Seminorm 𝕜 E} {q : ι' → Seminorm 𝕜 F} (f : E →ₗ[𝕜] F) :
    IsBounded (fun _ : ι => p) q f ↔ ∀ i, ∃ C : ℝ≥0 , C ≠ 0 ∧ (q i).comp f ≤ C • p := by
  dunfold is_bounded
  constructor
  · intro h i
    rcases h i with ⟨s, C, hC, h⟩
    exact ⟨C, hC, le_transₓ h (smul_le_smul (Finset.sup_le fun _ _ => le_rfl) le_rfl)⟩
    
  intro h i
  use {Classical.arbitrary ι}
  simp only [h, Finset.sup_singleton]

theorem is_bounded_sup {p : ι → Seminorm 𝕜 E} {q : ι' → Seminorm 𝕜 F} {f : E →ₗ[𝕜] F} (hf : IsBounded p q f)
    (s' : Finset ι') : ∃ (C : ℝ≥0 )(s : Finset ι), 0 < C ∧ (s'.sup q).comp f ≤ C • s.sup p := by
  classical
  by_cases' hs' : ¬s'.nonempty
  · refine' ⟨1, ∅, zero_lt_one, _⟩
    rw [finset.not_nonempty_iff_eq_empty.mp hs', Finset.sup_empty, bot_eq_zero, zero_comp]
    exact Seminorm.nonneg _
    
  rw [not_not] at hs'
  choose fₛ fC hf using hf
  use s'.card • s'.sup fC, Finset.bUnion s' fₛ
  constructor
  · refine' nsmul_pos _ (ne_of_gtₓ (Finset.Nonempty.card_pos hs'))
    cases' Finset.Nonempty.bex hs' with j hj
    exact lt_of_lt_of_leₓ (zero_lt_iff.mpr (And.elim_left (hf j))) (Finset.le_sup hj)
    
  have hs : ∀ i : ι', i ∈ s' → (q i).comp f ≤ s'.sup fC • (Finset.bUnion s' fₛ).sup p := by
    intro i hi
    refine' le_transₓ (And.elim_right (hf i)) (smul_le_smul _ (Finset.le_sup hi))
    exact Finset.sup_mono (Finset.subset_bUnion_of_mem fₛ hi)
  refine' le_transₓ (comp_mono f (finset_sup_le_sum q s')) _
  simp_rw [← pullback_apply, AddMonoidHom.map_sum, pullback_apply]
  --improve this
  refine' le_transₓ (Finset.sum_le_sum hs) _
  rw [Finset.sum_const, smul_assoc]
  exact le_rfl

end Bounded

section Topology

variable [NormedField 𝕜] [AddCommGroupₓ E] [Module 𝕜 E] [Nonempty ι]

/-- The proposition that the topology of `E` is induced by a family of seminorms `p`. -/
class WithSeminorms (p : ι → Seminorm 𝕜 E) [t : TopologicalSpace E] : Prop where
  topology_eq_with_seminorms : t = (seminormModuleFilterBasis p).topology

theorem with_seminorms_eq (p : ι → Seminorm 𝕜 E) [t : TopologicalSpace E] [WithSeminorms p] :
    t = (seminormModuleFilterBasis p).topology :=
  with_seminorms.topology_eq_with_seminorms

end Topology

section TopologicalAddGroup

variable [NormedField 𝕜] [AddCommGroupₓ E] [Module 𝕜 E]

variable [TopologicalSpace E] [TopologicalAddGroup E]

variable [Nonempty ι]

theorem with_seminorms_of_nhds (p : ι → Seminorm 𝕜 E)
    (h : 𝓝 (0 : E) = (seminormModuleFilterBasis p).toFilterBasis.filter) : WithSeminorms p := by
  refine'
    ⟨TopologicalAddGroup.ext
        (by
          infer_instance)
        (seminorm_add_group_filter_basis _).is_topological_add_group _⟩
  rw [AddGroupFilterBasis.nhds_zero_eq]
  exact h

theorem with_seminorms_of_has_basis (p : ι → Seminorm 𝕜 E)
    (h : (𝓝 (0 : E)).HasBasis (fun s : Set E => s ∈ SeminormBasisZero p) id) : WithSeminorms p :=
  with_seminorms_of_nhds p <| Filter.HasBasis.eq_of_same_basis h (seminormAddGroupFilterBasis p).toFilterBasis.HasBasis

end TopologicalAddGroup

section NormedSpace

/-- The topology of a `normed_space 𝕜 E` is induced by the seminorm `norm_seminorm 𝕜 E`. -/
instance norm_with_seminorms 𝕜 E [NormedField 𝕜] [SemiNormedGroup E] [NormedSpace 𝕜 E] :
    WithSeminorms fun _ : Finₓ 1 => normSeminorm 𝕜 E := by
  let p := fun _ : Finₓ 1 => normSeminorm 𝕜 E
  refine' ⟨TopologicalAddGroup.ext normed_top_group (seminorm_add_group_filter_basis _).is_topological_add_group _⟩
  refine' Filter.HasBasis.eq_of_same_basis Metric.nhds_basis_ball _
  rw [← ball_norm_seminorm 𝕜 E]
  refine'
    Filter.HasBasis.to_has_basis (seminorm_add_group_filter_basis p).nhds_zero_has_basis _ fun r hr =>
      ⟨(normSeminorm 𝕜 E).ball 0 r, seminorm_basis_zero_singleton_mem p 0 hr, rfl.subset⟩
  rintro U (hU : U ∈ seminorm_basis_zero p)
  rcases(seminorm_basis_zero_iff p U).mp hU with ⟨s, r, hr, hU⟩
  use r, hr
  rw [hU, id.def]
  by_cases' h : s.nonempty
  · rw [Finset.sup_const h]
    
  rw [finset.not_nonempty_iff_eq_empty.mp h, Finset.sup_empty, ball_bot _ hr]
  exact Set.subset_univ _

end NormedSpace

section ContinuousBounded

variable [NormedField 𝕜] [AddCommGroupₓ E] [Module 𝕜 E] [AddCommGroupₓ F] [Module 𝕜 F]

variable [Nonempty ι] [Nonempty ι']

theorem continuous_from_bounded (p : ι → Seminorm 𝕜 E) (q : ι' → Seminorm 𝕜 F) [UniformSpace E] [UniformAddGroup E]
    [WithSeminorms p] [UniformSpace F] [UniformAddGroup F] [WithSeminorms q] (f : E →ₗ[𝕜] F) (hf : IsBounded p q f) :
    Continuous f := by
  refine' UniformContinuous.continuous _
  refine' AddMonoidHom.uniform_continuous_of_continuous_at_zero f.to_add_monoid_hom _
  rw [f.to_add_monoid_hom_coe, continuous_at_def, f.map_zero, with_seminorms_eq p]
  intro U hU
  rw [with_seminorms_eq q, AddGroupFilterBasis.nhds_zero_eq, FilterBasis.mem_filter_iff] at hU
  rcases hU with ⟨V, hV : V ∈ seminorm_basis_zero q, hU⟩
  rcases(seminorm_basis_zero_iff q V).mp hV with ⟨s₂, r, hr, hV⟩
  rw [hV] at hU
  rw [(seminorm_add_group_filter_basis p).nhds_zero_eq, FilterBasis.mem_filter_iff]
  rcases is_bounded_sup hf s₂ with ⟨C, s₁, hC, hf⟩
  refine' ⟨(s₁.sup p).ball 0 (r / C), seminorm_basis_zero_mem p _ (div_pos hr (nnreal.coe_pos.mpr hC)), _⟩
  refine' subset.trans _ (preimage_mono hU)
  simp_rw [← LinearMap.map_zero f, ← ball_comp]
  refine' subset.trans _ (ball_antitone hf)
  rw [ball_smul (s₁.sup p) hC]

theorem cont_with_seminorms_normed_space F [SemiNormedGroup F] [NormedSpace 𝕜 F] [UniformSpace E] [UniformAddGroup E]
    (p : ι → Seminorm 𝕜 E) [WithSeminorms p] (f : E →ₗ[𝕜] F)
    (hf : ∃ (s : Finset ι)(C : ℝ≥0 ), C ≠ 0 ∧ (normSeminorm 𝕜 F).comp f ≤ C • s.sup p) : Continuous f := by
  rw [← is_bounded_const (Finₓ 1)] at hf
  exact continuous_from_bounded p (fun _ : Finₓ 1 => normSeminorm 𝕜 F) f hf

theorem cont_normed_space_to_with_seminorms E [SemiNormedGroup E] [NormedSpace 𝕜 E] [UniformSpace F] [UniformAddGroup F]
    (q : ι → Seminorm 𝕜 F) [WithSeminorms q] (f : E →ₗ[𝕜] F)
    (hf : ∀ i : ι, ∃ C : ℝ≥0 , C ≠ 0 ∧ (q i).comp f ≤ C • normSeminorm 𝕜 E) : Continuous f := by
  rw [← const_is_bounded (Finₓ 1)] at hf
  exact continuous_from_bounded (fun _ : Finₓ 1 => normSeminorm 𝕜 E) q f hf

end ContinuousBounded

section LocallyConvexSpace

open LocallyConvexSpace

variable [Nonempty ι] [NormedField 𝕜] [NormedSpace ℝ 𝕜] [AddCommGroupₓ E] [Module 𝕜 E] [Module ℝ E]
  [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E] [TopologicalAddGroup E]

theorem WithSeminorms.to_locally_convex_space (p : ι → Seminorm 𝕜 E) [WithSeminorms p] : LocallyConvexSpace ℝ E := by
  apply of_basis_zero ℝ E id fun s => s ∈ seminorm_basis_zero p
  · rw [with_seminorms_eq p, AddGroupFilterBasis.nhds_eq _, AddGroupFilterBasis.N_zero]
    exact FilterBasis.has_basis _
    
  · intro s hs
    change s ∈ Set.Unionₓ _ at hs
    simp_rw [Set.mem_Union, Set.mem_singleton_iff]  at hs
    rcases hs with ⟨I, r, hr, rfl⟩
    exact convex_ball _ _ _
    

end LocallyConvexSpace

end Seminorm

section NormedSpace

variable (𝕜) [NormedField 𝕜] [NormedSpace ℝ 𝕜] [SemiNormedGroup E]

/-- Not an instance since `𝕜` can't be inferred. See `normed_space.to_locally_convex_space` for a
slightly weaker instance version. -/
theorem NormedSpace.to_locally_convex_space' [NormedSpace 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E] :
    LocallyConvexSpace ℝ E :=
  Seminorm.WithSeminorms.to_locally_convex_space fun _ : Finₓ 1 => normSeminorm 𝕜 E

/-- See `normed_space.to_locally_convex_space'` for a slightly stronger version which is not an
instance. -/
instance NormedSpace.to_locally_convex_space [NormedSpace ℝ E] : LocallyConvexSpace ℝ E :=
  NormedSpace.to_locally_convex_space' ℝ

end NormedSpace

