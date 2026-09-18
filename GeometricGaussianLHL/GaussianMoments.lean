import GeometricGaussianLHL.GaussianAnalysis
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Gaussian moments, tails, and column estimates

This module collects the following proof sections, in dependency order.
- Relative error of Gaussian precision operators (`RelativePrecision`).
- Markov's inequality for a discrete expectation (`DiscreteMarkov`).
- Exact and rounded column constants (`ColumnCondition`).
- The cubic Gaussian: integral and unimodality (`GaussianCubicIntegral`).
- A unimodal sum is at most its integral plus its maximum (`UnimodalSumIntegral`).
- Relative precision under a lattice coordinate change (`PrecisionTransport`).
- Unit translation of a symmetric unimodal integer law (`IntegerUnimodalShift`).
- The numerical bound for the cubic Gaussian sum (`GaussianCubicBound`).
- Scalar Gaussian partitions and convergent moments (`IntegerGaussianMoments`).
- Uniform overlap at width one (`GaussianUnitOverlap`).
- The dual-theta correction in the variance formula (`IntegerVarianceTail`).
- Convergent moments of Gaussian linear forms (`ProductGaussianMoments`).
- Scalar Gaussian exponential moments (`IntegerGaussianMGF`).
- Differentiating the actual scalar theta series (`IntegerThetaDerivative`).
- The exact characteristic coefficient of a modular Gaussian (`IntegerGaussianCharacter`).
- A fourth-moment bound for the scalar discrete Gaussian (`IntegerGaussianFourthMoment`).
- The uniform discrete Gaussian variance lower bound (`IntegerGaussianVariance`).
- The numerical nonuniformity bound at coefficient width one (`IntegerGaussianNonuniform`).
- Uniform scalar discrete Gaussian moments (`IntegerGaussianThirdMoment`).
- Exact second and fourth moments of Gaussian linear forms (`ProductGaussianFourthMoment`).
- Uniform escape for every Gaussian linear form (`UniformGaussianEscape`).
- A short integer displacement (`Displacement`).
- Uniform escape of complex Gaussian linear forms (`ComplexGaussianEscape`).
- Disjoint translates of integer slabs (`IntegerSlabs`).
- Periodic Gaussian bounds away from the integers (`PeriodicGaussianTail`).
- Integer shifts of ellipsoidal Gaussians (`GaussianShift`).
- Gaussian subspace anti-concentration (`GaussianSubspace`).
- Gaussian escape from integer slabs (`SlabProbability`).
- A witness coordinate bounds the whole column expectation (`ColumnExpectation`).
- Exponential moments of the Euclidean norm (`GaussianNormMoment`).
- Polynomial-width parameters for the column bound (`ColumnParameters`).
- Independent discrete columns (`IndependentColumns`).
- Gaussian norm tails as probability-measure bounds (`GaussianNormTail`).
- Gaussian linear moments of independent vector columns (`IndependentLinearMoment`).
- The column-norm exceptional event (`ColumnTails`).
- Elementary ellipsoidal Gaussian estimates (`ElementaryGaussian`).
- Standardized Gaussian moments and tails (`GaussianStandardized`).
- Lower tails for the number of independent escapes (`IndependentEscapeCount`).
- Chernoff tails of actual product Gaussian linear forms (`ProductGaussianTail`).
-/

section RelativePrecision

/-!
## Relative error of Gaussian precision operators

The precision is the inverse-shape Gram operator. It is an actual two-sided
inverse of the covariance. The paper's relative operator-norm error controls
the difference of the two Gaussian quadratic forms.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace GeometricGaussianLHL

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def shapeCovariance (S : E ≃L[ℝ] E) : E →L[ℝ] E :=
  S.toContinuousLinearMap.comp S.toContinuousLinearMap.adjoint

def shapePrecision (S : E ≃L[ℝ] E) : E →L[ℝ] E :=
  S.symm.toContinuousLinearMap.adjoint.comp S.symm.toContinuousLinearMap

theorem adjoint_equiv_cancel (S : E ≃L[ℝ] E) :
    S.toContinuousLinearMap.adjoint.comp S.symm.toContinuousLinearMap.adjoint = ContinuousLinearMap.id ℝ E := by
  rw [← ContinuousLinearMap.adjoint_comp, S.coe_symm_comp_coe, ContinuousLinearMap.adjoint_id]

theorem shapeCovariance_comp_precision (S : E ≃L[ℝ] E) :
    (shapeCovariance S).comp (shapePrecision S) = ContinuousLinearMap.id ℝ E := by
  rw [shapeCovariance, shapePrecision, ContinuousLinearMap.comp_assoc,
    ← ContinuousLinearMap.comp_assoc S.toContinuousLinearMap.adjoint,
    adjoint_equiv_cancel, ContinuousLinearMap.id_comp, S.coe_comp_coe_symm]

theorem shapePrecision_comp_covariance (S : E ≃L[ℝ] E) :
    (shapePrecision S).comp (shapeCovariance S) = ContinuousLinearMap.id ℝ E := by
  rw [shapeCovariance, shapePrecision, ContinuousLinearMap.comp_assoc,
    ← ContinuousLinearMap.comp_assoc S.symm.toContinuousLinearMap,
    S.coe_symm_comp_coe, ContinuousLinearMap.id_comp]
  exact adjoint_equiv_cancel S.symm

def shapeCovarianceUnit (S : E ≃L[ℝ] E) : (E →L[ℝ] E)ˣ where
  val := shapeCovariance S
  inv := shapePrecision S
  val_inv := shapeCovariance_comp_precision S
  inv_val := shapePrecision_comp_covariance S

theorem shapePrecision_eq_covariance_inverse (S : E ≃L[ℝ] E) :
    shapePrecision S = Ring.inverse (shapeCovariance S) :=
  (Ring.inverse_unit (shapeCovarianceUnit S)).symm

theorem shapePrecision_inner (S : E ≃L[ℝ] E) (x : E) :
    inner ℝ x (shapePrecision S x) = ‖S.symm x‖ ^ 2 := by
  rw [shapePrecision, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
    real_inner_self_eq_norm_sq]
  rfl

def relativePrecision (S T : E ≃L[ℝ] E) : E →L[ℝ] E :=
  S.toContinuousLinearMap.adjoint.comp ((shapePrecision T - shapePrecision S).comp S.toContinuousLinearMap)

theorem relativePrecision_inner (S T : E ≃L[ℝ] E) (y : E) :
    inner ℝ y (relativePrecision S T y) = ‖T.symm (S y)‖ ^ 2 - ‖y‖ ^ 2 := by
  rw [relativePrecision, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
    ContinuousLinearMap.comp_apply, sub_apply, inner_sub_right,
    shapePrecision_inner, shapePrecision_inner]
  simp only [ContinuousLinearEquiv.coe_coe, S.symm_apply_apply]

theorem relativePrecision_quadratic_bound (S T : E ≃L[ℝ] E) {θ : ℝ}
    (hθ : ‖relativePrecision S T‖ ≤ θ) (x : E) :
    |‖T.symm x‖ ^ 2 - ‖S.symm x‖ ^ 2| ≤ θ * ‖S.symm x‖ ^ 2 := by
  have he := relativePrecision_inner S T (S.symm x)
  rw [S.apply_symm_apply] at he
  rw [← he]
  calc
    _ ≤ ‖S.symm x‖ * ‖relativePrecision S T (S.symm x)‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖S.symm x‖ * (‖relativePrecision S T‖ * ‖S.symm x‖) :=
      mul_le_mul_of_nonneg_left ((relativePrecision S T).le_opNorm _) (norm_nonneg _)
    _ = ‖relativePrecision S T‖ * ‖S.symm x‖ ^ 2 := by ring
    _ ≤ θ * ‖S.symm x‖ ^ 2 := mul_le_mul_of_nonneg_right hθ (sq_nonneg _)

theorem relativePrecision_lower (S T : E ≃L[ℝ] E) {θ : ℝ}
    (hθ : ‖relativePrecision S T‖ ≤ θ) (x : E) :
    (1 - θ) * ‖S.symm x‖ ^ 2 ≤ ‖T.symm x‖ ^ 2 := by
  have h := (abs_le.mp (relativePrecision_quadratic_bound S T hθ x)).1
  linarith

end GeometricGaussianLHL
end

end RelativePrecision

section DiscreteMarkov

/-!
## Markov's inequality for a discrete expectation

The probability is the actual PMF measure, and the expectation is a
nonnegative sum. The indicator form directly handles an exceptional event
intersected with the column-norm event.
-/

noncomputable section

open scoped ENNReal

namespace GeometricGaussianLHL

theorem pmf_markov_bound {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (p : PMF α) (f : α → ℝ≥0∞) {a C : ℝ} (ha : 0 < a)
    (hexpect : (∑' x, p x * f x) ≤ ENNReal.ofReal C) :
    p.toMeasure {x | ENNReal.ofReal a < f x} ≤ ENNReal.ofReal C / ENNReal.ofReal a := by
  classical
  apply (ENNReal.le_div_iff_mul_le
    (Or.inl (ne_of_gt (ENNReal.ofReal_pos.mpr ha))) (Or.inl ENNReal.ofReal_ne_top)).mpr
  apply le_trans _ hexpect
  rw [PMF.toMeasure_apply_eq_tsum, ← ENNReal.tsum_mul_right]
  apply ENNReal.tsum_le_tsum
  intro x
  by_cases hx : ENNReal.ofReal a < f x
  · rw [Set.indicator_of_mem (show x ∈ {x | ENNReal.ofReal a < f x} from hx)]
    exact mul_le_mul_right hx.le (p x)
  · rw [Set.indicator_of_notMem (show x ∉ {x | ENNReal.ofReal a < f x} from hx), zero_mul]
    exact zero_le

theorem pmf_markov_indicator_square {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (p : PMF α) (f : α → ℝ) (G : Set α) {δ : ℝ} (hδ : 0 < δ)
    (hexpect : (∑' x, p x * G.indicator (fun x => ENNReal.ofReal (f x)) x) ≤ ENNReal.ofReal (δ ^ 2)) :
    p.toMeasure (G ∩ {x | δ < f x}) ≤ ENNReal.ofReal δ := by
  classical
  have heq : G ∩ {x | δ < f x} =
      {x | ENNReal.ofReal δ < G.indicator (fun x => ENNReal.ofReal (f x)) x} := by
    ext x
    by_cases hx : x ∈ G
    · simp only [Set.mem_inter_iff, hx, true_and, Set.mem_setOf_eq, Set.indicator_of_mem hx]
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hδ.le).symm
    · simp [hx, Set.indicator]
  rw [heq]
  have h := pmf_markov_bound p _ hδ hexpect
  have hratio : ENNReal.ofReal (δ ^ 2) / ENNReal.ofReal δ = ENNReal.ofReal δ := by
    rw [← ENNReal.ofReal_div_of_pos hδ]
    congr 1
    field_simp
  rwa [hratio] at h

end GeometricGaussianLHL
end

end DiscreteMarkov

section ColumnCondition

/-!
## Exact and rounded column constants

The decimal constants 7.5 and 49.5 are conservative upper bounds for the
reciprocal logarithms, rather than exact algebraic reformulations.
-/

noncomputable section

namespace GeometricGaussianLHL

theorem log_eight_sevenths_gt : (2 / 15 : ℝ) < Real.log (8 / 7) := by
  have h := Real.lt_log_one_add_of_pos (by norm_num : (0 : ℝ) < 1 / 7)
  norm_num at h ⊢
  exact h

theorem polynomial_column_constant_lt : 1 / Real.log (8 / 7) < (15 / 2 : ℝ) := by
  have hlog : 0 < Real.log (8 / 7 : ℝ) := by linarith [log_eight_sevenths_gt]
  apply (div_lt_iff₀ hlog).mpr
  linarith [log_eight_sevenths_gt]

theorem constant_column_constant_lt : 1 / Real.log (50 / 49) < (99 / 2 : ℝ) := by
  have h := Real.lt_log_one_add_of_pos (by norm_num : (0 : ℝ) < 1 / 49)
  norm_num at h
  have hlog : 0 < Real.log (50 / 49 : ℝ) := by linarith
  apply (div_lt_iff₀ hlog).mpr
  linarith

theorem exact_polynomial_column_condition {m B : ℝ} :
    B ≤ m * Real.log (8 / 7) ↔ B / Real.log (8 / 7) ≤ m := by
  exact (div_le_iff₀ (show 0 < Real.log (8 / 7 : ℝ) by
    linarith [log_eight_sevenths_gt])).symm

theorem rounded_polynomial_column_condition {m B : ℝ} (hB : 0 ≤ B)
    (hm : (15 / 2) * B ≤ m) : B ≤ m * Real.log (8 / 7) := by
  have hlog : 0 < Real.log (8 / 7 : ℝ) := by linarith [log_eight_sevenths_gt]
  have hc : 1 ≤ (15 / 2) * Real.log (8 / 7 : ℝ) := by linarith [log_eight_sevenths_gt]
  have h₁ := mul_le_mul_of_nonneg_right hc hB
  have h₂ := mul_le_mul_of_nonneg_right hm hlog.le
  nlinarith

end GeometricGaussianLHL
end

end ColumnCondition

section GaussianCubicIntegral

/-!
## The cubic Gaussian: integral and unimodality

These are the analytic ingredients of the third absolute moment estimate.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped Topology

namespace GeometricGaussianLHL

def cubicGaussian (a x : ℝ) : ℝ := x ^ 3 * Real.exp (-a * x ^ 2)

theorem hasDerivAt_cubicGaussian (a x : ℝ) :
    HasDerivAt (cubicGaussian a) (x ^ 2 * (3 - 2 * a * x ^ 2) * Real.exp (-a * x ^ 2)) x := by
  have hd := ((hasDerivAt_id x).pow 3).mul ((((hasDerivAt_id x).pow 2).const_mul (-a)).exp)
  simp only [id_eq, Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one] at hd
  have he : 3 * x ^ 2 * Real.exp (-a * x ^ 2) + x ^ 3 * (Real.exp (-a * x ^ 2) * (-a * (2 * x))) =
      x ^ 2 * (3 - 2 * a * x ^ 2) * Real.exp (-a * x ^ 2) := by ring
  rwa [he] at hd

theorem cubicGaussian_monotone {a : ℝ} (ha : 0 < a) :
    MonotoneOn (cubicGaussian a) (Icc 0 (Real.sqrt (3 / (2 * a)))) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    (by unfold cubicGaussian; fun_prop) (fun x _ => (hasDerivAt_cubicGaussian a x).differentiableAt.differentiableWithinAt)
  intro x hx
  rw [(hasDerivAt_cubicGaussian a x).deriv]
  have hx' := interior_subset hx
  have hs := (sq_le_sq₀ hx'.1 (Real.sqrt_nonneg _)).mpr hx'.2
  rw [Real.sq_sqrt (by positivity)] at hs
  have hcoef : 0 ≤ 3 - 2 * a * x ^ 2 := by
    have h := (le_div_iff₀ (mul_pos (by norm_num) ha)).mp hs
    nlinarith
  exact mul_nonneg (mul_nonneg (sq_nonneg x) hcoef) (Real.exp_pos _).le

theorem cubicGaussian_antitone {a : ℝ} (ha : 0 < a) :
    AntitoneOn (cubicGaussian a) (Ici (Real.sqrt (3 / (2 * a)))) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici _)
    (by unfold cubicGaussian; fun_prop) (fun x _ => (hasDerivAt_cubicGaussian a x).differentiableAt.differentiableWithinAt)
  intro x hx
  rw [(hasDerivAt_cubicGaussian a x).deriv]
  have hx' : Real.sqrt (3 / (2 * a)) ≤ x := interior_subset hx
  have hx0 := (Real.sqrt_nonneg (3 / (2 * a))).trans hx'
  have hs := (sq_le_sq₀ (Real.sqrt_nonneg _) hx0).mpr hx'
  rw [Real.sq_sqrt (by positivity)] at hs
  have hcoef : 3 - 2 * a * x ^ 2 ≤ 0 := by
    have h := (div_le_iff₀ (mul_pos (by norm_num) ha)).mp hs
    nlinarith
  exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg x) hcoef) (Real.exp_pos _).le

theorem cubicGaussian_integrable {a : ℝ} (ha : 0 < a) : IntegrableOn (cubicGaussian a) (Ioi 0) := by
  unfold cubicGaussian
  simpa only [Real.rpow_ofNat] using
    integrableOn_rpow_mul_exp_neg_mul_sq ha (by norm_num : (-1 : ℝ) < 3)

theorem integral_cubicGaussian {a : ℝ} (ha : 0 < a) :
    (∫ x in Ioi (0 : ℝ), cubicGaussian a x) = 1 / (2 * a ^ 2) := by
  let F : ℝ → ℝ := fun x => -((a * x ^ 2 + 1) * Real.exp (-a * x ^ 2)) / (2 * a ^ 2)
  have hd (x : ℝ) : HasDerivAt F (cubicGaussian a x) x := by
    have h0 := (((((hasDerivAt_id x).pow 2).const_mul a).add_const 1).mul
      ((((hasDerivAt_id x).pow 2).const_mul (-a)).exp)).neg.div_const (2 * a ^ 2)
    simp only [id_eq, Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one] at h0
    have he : -((a * (2 * x)) * Real.exp (-a * x ^ 2) +
        (a * x ^ 2 + 1) * (Real.exp (-a * x ^ 2) * (-a * (2 * x)))) / (2 * a ^ 2) =
          cubicGaussian a x := by unfold cubicGaussian; field_simp; ring
    rwa [he] at h0
  have hu : Tendsto (fun x : ℝ => a * x ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by decide : 2 ≠ 0)).const_mul_atTop ha
  have h1 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hu
  have h0 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 0).comp hu
  have hlim : Tendsto F atTop (𝓝 0) := by
    have h := (h1.add h0).neg.div_const (2 * a ^ 2)
    have he : F = fun x => -(a * x ^ 2 * Real.exp (-(a * x ^ 2)) + Real.exp (-(a * x ^ 2))) / (2 * a ^ 2) := by
      funext x
      dsimp [F]
      rw [neg_mul a]
      ring
    rw [he]
    simpa only [Function.comp_def, pow_one, pow_zero, one_mul, zero_add, neg_zero, zero_div] using h
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' (fun x _ => hd x) (cubicGaussian_integrable ha) hlim
  simpa only [F, zero_pow (by omega : 2 ≠ 0), mul_zero, zero_add, Real.exp_zero, mul_one,
    zero_sub, neg_div, neg_neg] using h

end GeometricGaussianLHL
end

end GaussianCubicIntegral

section UnimodalSumIntegral

/-!
## A unimodal sum is at most its integral plus its maximum

Split a unimodal function into the difference of two increasing functions.
The left/right integral comparisons then leave only one peak value, even
when the maximum is between consecutive integers.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory

namespace GeometricGaussianLHL

theorem unimodal_sum_range_le_integral {f : ℝ → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hn : ∀ x ∈ Ici (0 : ℝ), 0 ≤ f x) (hi : MonotoneOn f (Icc 0 c))
    (hd : AntitoneOn f (Ici c)) (N : ℕ) :
    (∑ k ∈ Finset.range N, f ((k + 1 : ℕ) : ℝ)) ≤ (∫ x in (0 : ℝ)..N, f x) + f c := by
  let g : ℝ → ℝ := fun x => f (min x c)
  let h : ℝ → ℝ := fun x => f c - f (max x c)
  have hg : MonotoneOn g (Ici 0) := by
    intro x hx y hy hxy
    exact hi ⟨le_min hx hc, min_le_right _ _⟩ ⟨le_min hy hc, min_le_right _ _⟩
      (min_le_min_right c hxy)
  have hh : MonotoneOn h (Ici 0) := by
    intro x _ y _ hxy
    have hxy' : f (max y c) ≤ f (max x c) := hd
      (show max x c ∈ Ici c from le_max_right x c)
      (show max y c ∈ Ici c from le_max_right y c) (max_le_max_right c hxy)
    exact sub_le_sub_left hxy' _
  have he (x : ℝ) : f x = g x - h x := by
    dsimp [g, h]
    rcases le_total x c with hx | hx
    · rw [min_eq_left hx, max_eq_right hx]; ring
    · rw [min_eq_right hx, max_eq_left hx]; ring
  have hgN : MonotoneOn g (Icc (0 : ℝ) (0 + N)) := hg.mono (fun _ hx => hx.1)
  have hhN : MonotoneOn h (Icc (0 : ℝ) (0 + N)) := hh.mono (fun _ hx => hx.1)
  have hgint : IntervalIntegrable g volume 0 N := by
    apply MonotoneOn.intervalIntegrable
    rw [uIcc_of_le (Nat.cast_nonneg N)]
    exact hg.mono (fun _ hx => hx.1)
  have hhint : IntervalIntegrable h volume 0 N := by
    apply MonotoneOn.intervalIntegrable
    rw [uIcc_of_le (Nat.cast_nonneg N)]
    exact hh.mono (fun _ hx => hx.1)
  have hleft := hgN.sum_le_integral
  have hright := hhN.integral_le_sum
  simp only [zero_add] at hleft hright
  have hshift : (∑ k ∈ Finset.range N, g ((k + 1 : ℕ) : ℝ)) =
      (∑ k ∈ Finset.range N, g (k : ℝ)) + g N - g 0 := by
    clear hgN hhN hgint hhint hleft hright
    induction N with
    | zero => simp
    | succ n ih => simp only [Finset.sum_range_succ, ih]; ring
  have hpeak : g N ≤ f c := hi ⟨le_min (Nat.cast_nonneg N) hc, min_le_right _ _⟩
    ⟨hc, le_rfl⟩ (min_le_right _ _)
  have hg0 : 0 ≤ g 0 := hn _ (le_min le_rfl hc)
  have hsum : (∑ k ∈ Finset.range N, f ((k + 1 : ℕ) : ℝ)) =
      (∑ k ∈ Finset.range N, g ((k + 1 : ℕ) : ℝ)) -
        ∑ k ∈ Finset.range N, h ((k + 1 : ℕ) : ℝ) := by
    simp_rw [he]
    exact Finset.sum_sub_distrib _ _
  have hint : (∫ x in (0 : ℝ)..N, f x) = (∫ x in (0 : ℝ)..N, g x) -
      ∫ x in (0 : ℝ)..N, h x := by
    rw [show f = fun x => g x - h x from funext he]
    exact intervalIntegral.integral_sub hgint hhint
  linarith

theorem unimodal_tsum_le_integral {f : ℝ → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hn : ∀ x ∈ Ici (0 : ℝ), 0 ≤ f x) (hi : MonotoneOn f (Icc 0 c))
    (hd : AntitoneOn f (Ici c)) (hf : IntegrableOn f (Ioi 0)) :
    (∑' k : ℕ, f ((k + 1 : ℕ) : ℝ)) ≤ (∫ x in Ioi (0 : ℝ), f x) + f c := by
  apply Real.tsum_le_of_sum_range_le (fun k => hn _ (by
    change (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ)
    positivity))
  intro N
  apply (unimodal_sum_range_le_integral hc hn hi hd N).trans
  apply add_le_add _ le_rfl
  rw [intervalIntegral.integral_of_le (Nat.cast_nonneg N)]
  apply setIntegral_mono_set hf _ Ioc_subset_Ioi_self.eventuallyLE
  exact ae_restrict_of_forall_mem measurableSet_Ioi (fun x hx => hn x (Ioi_subset_Ici_self hx))

end GeometricGaussianLHL
end

end UnimodalSumIntegral

section PrecisionTransport

/-!
## Relative precision under a lattice coordinate change

Changing the lattice coordinates acts on both shapes on the left. Their
relative precision operator is unchanged, so its operator norm continues
to refer to the original Euclidean geometry.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace GeometricGaussianLHL

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem relativePrecision_eq_relative_gram (S T : E ≃L[ℝ] E) :
    relativePrecision S T =
      (T.symm.toContinuousLinearMap.comp S.toContinuousLinearMap).adjoint.comp
        (T.symm.toContinuousLinearMap.comp S.toContinuousLinearMap) - ContinuousLinearMap.id ℝ E := by
  have hc (x : E) : S.toContinuousLinearMap.adjoint (S.symm.toContinuousLinearMap.adjoint x) = x := by
    have h := congrArg (fun f : E →L[ℝ] E => f x) (adjoint_equiv_cancel S)
    exact h
  apply ContinuousLinearMap.ext
  intro x
  simp only [relativePrecision, shapePrecision, ContinuousLinearMap.comp_apply, sub_apply,
    map_sub, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.id_apply]
  change S.toContinuousLinearMap.adjoint (T.symm.toContinuousLinearMap.adjoint (T.symm (S x))) -
      S.toContinuousLinearMap.adjoint (S.symm.toContinuousLinearMap.adjoint (S.symm (S x))) = _
  rw [S.symm_apply_apply, hc]
  rfl

theorem relativePrecision_change_coordinates (B S T : E ≃L[ℝ] E) :
    relativePrecision (S.trans B.symm) (T.trans B.symm) = relativePrecision S T := by
  have h : (T.trans B.symm).symm.toContinuousLinearMap.comp (S.trans B.symm).toContinuousLinearMap =
      T.symm.toContinuousLinearMap.comp S.toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro x
    change T.symm (B (B.symm (S x))) = T.symm (S x)
    rw [B.apply_symm_apply]
  rw [relativePrecision_eq_relative_gram, relativePrecision_eq_relative_gram, h]

end GeometricGaussianLHL
end

end PrecisionTransport

section IntegerUnimodalShift

/-!
## Unit translation of a symmetric unimodal integer law

Telescoping the two integer tails shows that total variation under a unit
translate is exactly the mass at zero. All series converge; the proof uses
the actual pushforward PMF.
-/

noncomputable section

namespace GeometricGaussianLHL

theorem pmf_map_integer_add_apply (p : PMF ℤ) (v z : ℤ) :
    (p.map (fun x => x + v)) (z + v) = p z := by
  rw [PMF.map_apply]
  simp only [add_left_inj, tsum_ite_eq']

theorem tsum_integer_unimodal_difference (f : ℤ → ℝ) (hf : Summable f)
    (hsym : ∀ z, f (-z) = f z)
    (hmono : ∀ n : ℕ, f ((n : ℤ) + 1) ≤ f n) :
    (∑' z : ℤ, |f (z + 1) - f z|) = 2 * f 0 := by
  have hn : Summable (fun n : ℕ => f (n : ℤ)) := hf.comp_injective Nat.cast_injective
  have hnext : Summable (fun n : ℕ => f ((n : ℤ) + 1)) := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one, Nat.cast_succ] using
      hn.comp_injective Nat.succ_injective
  have hd := hn.sub hnext
  have hpos (n : ℕ) : |f ((n : ℤ) + 1) - f n| = f n - f ((n : ℤ) + 1) := by
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (hmono n))]
  have hneg (n : ℕ) : |f (-((n : ℤ) + 1) + 1) - f (-((n : ℤ) + 1))| =
      f n - f ((n : ℤ) + 1) := by
    rw [show -((n : ℤ) + 1) + 1 = -(n : ℤ) by ring, hsym, hsym,
      abs_of_nonneg (sub_nonneg.mpr (hmono n))]
  have hsum : (∑' n : ℕ, (f (n : ℤ) - f ((n : ℤ) + 1))) = f 0 := by
    have hh := hn.tsum_eq_zero_add
    rw [Summable.tsum_sub hn hnext]
    simp only [Nat.cast_zero, Nat.cast_add, Nat.cast_one] at hh
    linarith
  have hp : Summable (fun n : ℕ => |f ((n : ℤ) + 1) - f n|) := by
    simpa only [hpos, Nat.cast_add, Nat.cast_one] using hd
  have hm : Summable (fun n : ℕ => |f (-((n : ℤ) + 1) + 1) - f (-((n : ℤ) + 1))|) := by
    simpa only [hneg, Nat.cast_add, Nat.cast_one] using hd
  rw [tsum_of_nat_of_neg_add_one (f := fun z : ℤ => |f (z + 1) - f z|) hp hm]
  simp only [hpos, hneg, hsum]
  ring

/-- The exact unit-translation distance for any symmetric unimodal PMF.
-/
theorem pmf_unimodal_unit_translation (p : PMF ℤ)
    (hsym : ∀ z, p (-z) = p z)
    (hmono : ∀ n : ℕ, (p ((n : ℤ) + 1)).toReal ≤ (p n).toReal) :
    discreteTotalVariation p (p.map (fun z => z + 1)) = (p 0).toReal := by
  unfold discreteTotalVariation
  rw [← (Equiv.addRight (1 : ℤ)).tsum_eq]
  simp only [Equiv.coe_addRight, pmf_map_integer_add_apply]
  rw [tsum_integer_unimodal_difference (fun z => (p z).toReal) (pmf_summable_toReal p)
    (fun z => by rw [hsym]) hmono]
  ring

end GeometricGaussianLHL
end

end IntegerUnimodalShift

section GaussianCubicBound

/-!
## The numerical bound for the cubic Gaussian sum

The integral-plus-maximum bound has a coefficient strictly below `1/4`.
All numerical inequalities use rational bounds and proved exponential
series estimates.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory

namespace GeometricGaussianLHL

theorem gaussian_cubic_constant_lt :
    1 / Real.pi ^ 2 + 2 * (Real.sqrt (3 / (2 * Real.pi))) ^ 3 * Real.exp (-(3 / 2 : ℝ)) < 1 / 4 := by
  have hp : 1 / Real.pi ^ 2 ≤ (203 / 2000 : ℝ) := by
    apply (div_le_iff₀ (sq_pos_of_pos Real.pi_pos)).mpr
    nlinarith [Real.pi_gt_d2]
  have hc : Real.sqrt (3 / (2 * Real.pi)) ≤ (691 / 1000 : ℝ) := by
    apply Real.sqrt_le_iff.mpr ⟨by norm_num, ?_⟩
    apply (div_le_iff₀ (mul_pos (by norm_num) Real.pi_pos)).mpr
    linarith [Real.pi_gt_d4]
  have he : Real.exp (-(3 / 2 : ℝ)) ≤ 9 / 40 := by
    have ht := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 2) 7
    norm_num [Finset.sum_range_succ] at ht
    have ht' : (40 / 9 : ℝ) ≤ Real.exp (3 / 2) := by linarith
    rw [Real.exp_neg]
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 40 / 9) ht'
    norm_num only [one_div] at h
    exact h
  have hc3 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hc 3
  calc
    _ ≤ 203 / 2000 + 2 * (691 / 1000 : ℝ) ^ 3 * (9 / 40) := by
      apply add_le_add hp
      exact mul_le_mul (mul_le_mul_of_nonneg_left hc3 (by norm_num)) he (Real.exp_pos _).le (by norm_num)
    _ < _ := by norm_num

theorem cubicGaussian_peak_width {s : ℝ} (hs : 0 < s) :
    Real.sqrt (3 / (2 * (Real.pi / s ^ 2))) = s * Real.sqrt (3 / (2 * Real.pi)) := by
  rw [show 3 / (2 * (Real.pi / s ^ 2)) = s ^ 2 * (3 / (2 * Real.pi)) by field_simp,
    Real.sqrt_mul (sq_nonneg s), Real.sqrt_sq hs.le]

theorem cubicGaussian_peak_value {s : ℝ} (hs : 0 < s) :
    cubicGaussian (Real.pi / s ^ 2) (Real.sqrt (3 / (2 * (Real.pi / s ^ 2)))) =
      s ^ 3 * (Real.sqrt (3 / (2 * Real.pi))) ^ 3 * Real.exp (-(3 / 2 : ℝ)) := by
  rw [cubicGaussian_peak_width hs, cubicGaussian]
  have he : -(Real.pi / s ^ 2) * (s * Real.sqrt (3 / (2 * Real.pi))) ^ 2 = -(3 / 2 : ℝ) := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    field_simp
  rw [he, mul_pow]

theorem positive_integer_cubicGaussian_sum_le {s : ℝ} (hs : 0 < s) :
    (∑' n : ℕ, (((n + 1 : ℕ) : ℝ) ^ 3) * Real.exp (-(Real.pi / s ^ 2) * ((n + 1 : ℕ) : ℝ) ^ 2)) ≤
      s ^ 4 / (2 * Real.pi ^ 2) + s ^ 3 * (Real.sqrt (3 / (2 * Real.pi))) ^ 3 * Real.exp (-(3 / 2 : ℝ)) := by
  have ha := div_pos Real.pi_pos (sq_pos_of_pos hs)
  have h := unimodal_tsum_le_integral (Real.sqrt_nonneg (3 / (2 * (Real.pi / s ^ 2))))
    (f := cubicGaussian (Real.pi / s ^ 2))
    (fun x hx => mul_nonneg (pow_nonneg hx 3) (Real.exp_pos _).le)
    (cubicGaussian_monotone ha) (cubicGaussian_antitone ha) (cubicGaussian_integrable ha)
  rw [integral_cubicGaussian ha, cubicGaussian_peak_value hs] at h
  have he : 1 / (2 * (Real.pi / s ^ 2) ^ 2) = s ^ 4 / (2 * Real.pi ^ 2) := by field_simp
  rw [he] at h
  exact h

end GeometricGaussianLHL
end

end GaussianCubicBound

section IntegerGaussianMoments

/-!
## Scalar Gaussian partitions and convergent moments

The partition and moments below are actual real series. Polynomial
Gaussian majorants prove convergence before any differentiation or
probability-moment identity is used.
-/

noncomputable section

namespace GeometricGaussianLHL

def integerTheta (a : ℝ) : ℝ := ∑' z : ℤ, Real.exp (-a * (z : ℝ) ^ 2)

def integerGaussianPartition (s : ℝ) : ℝ := integerTheta (Real.pi / s ^ 2)

def integerGaussianSecondMoment (s : ℝ) (hs : 0 < s) : ℝ :=
  ∑' z : ℤ, (integerGaussian s hs z).toReal * (z : ℝ) ^ 2

def integerGaussianThirdAbsMoment (s : ℝ) (hs : 0 < s) : ℝ :=
  ∑' z : ℤ, (integerGaussian s hs z).toReal * |(z : ℝ)| ^ 3

theorem gaussian_evenMoment_majorant {a : ℝ} (ha : 0 < a) (k : ℕ) (x : ℝ) :
    (x ^ 2) ^ k * Real.exp (-a * x ^ 2) ≤
      ((k.factorial : ℝ) / (a / 2) ^ k) * Real.exp (-(a / 2) * x ^ 2) := by
  have hfactor : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hhalf : a / 2 ≠ 0 := (half_pos ha).ne'
  have hpoly : (x ^ 2) ^ k ≤ ((k.factorial : ℝ) / (a / 2) ^ k) *
      Real.exp ((a / 2) * x ^ 2) := by
    calc
      (x ^ 2) ^ k = (((a / 2) * x ^ 2) ^ k / k.factorial) *
          ((k.factorial : ℝ) / (a / 2) ^ k) := by
        rw [mul_pow]
        field_simp
      _ ≤ Real.exp ((a / 2) * x ^ 2) * ((k.factorial : ℝ) / (a / 2) ^ k) :=
        mul_le_mul_of_nonneg_right
          (Real.pow_div_factorial_le_exp _ (mul_nonneg (half_pos ha).le (sq_nonneg x)) k)
          (by positivity)
      _ = _ := mul_comm _ _
  calc
    _ ≤ (((k.factorial : ℝ) / (a / 2) ^ k) * Real.exp ((a / 2) * x ^ 2)) *
        Real.exp (-a * x ^ 2) := mul_le_mul_of_nonneg_right hpoly (Real.exp_pos _).le
    _ = _ := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring

theorem summable_integer_gaussian_evenMoment {a : ℝ} (ha : 0 < a) (k : ℕ) :
    Summable (fun z : ℤ => ((z : ℝ) ^ 2) ^ k * Real.exp (-a * (z : ℝ) ^ 2)) := by
  apply ((summable_integer_gaussian (half_pos ha)).mul_left
    ((k.factorial : ℝ) / (a / 2) ^ k)).of_norm_bounded
  intro z
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact gaussian_evenMoment_majorant ha k z

theorem integerTheta_ge_one {a : ℝ} (ha : 0 < a) : 1 ≤ integerTheta a := by
  unfold integerTheta
  have h := (summable_integer_gaussian ha).le_tsum 0 (fun _ _ => (Real.exp_pos _).le)
  simpa only [Int.cast_zero, zero_pow (by omega : 2 ≠ 0), mul_zero, Real.exp_zero] using h

theorem integerGaussianPartition_pos {s : ℝ} (hs : 0 < s) : 0 < integerGaussianPartition s :=
  zero_lt_one.trans_le (integerTheta_ge_one (div_pos Real.pi_pos (sq_pos_of_pos hs)))

theorem integerGaussian_toReal (s : ℝ) (hs : 0 < s) (z : ℤ) :
    (integerGaussian s hs z).toReal = Real.exp (-(Real.pi / s ^ 2) * (z : ℝ) ^ 2) /
      integerGaussianPartition s := by
  rw [integerGaussian_apply, ENNReal.toReal_div]
  simp only [integerGaussianWeight]
  rw [
    ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
  simp only [ENNReal.toReal_ofReal (Real.exp_pos _).le,
    integerGaussianPartition, integerTheta]

theorem summable_integerGaussian_evenMoment (s : ℝ) (hs : 0 < s) (k : ℕ) :
    Summable (fun z : ℤ => (integerGaussian s hs z).toReal * ((z : ℝ) ^ 2) ^ k) := by
  simpa only [integerGaussian_toReal, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
    (summable_integer_gaussian_evenMoment (div_pos Real.pi_pos (sq_pos_of_pos hs)) k).div_const
      (integerGaussianPartition s)

theorem integerGaussianSecondMoment_eq (s : ℝ) (hs : 0 < s) :
    integerGaussianSecondMoment s hs =
      (∑' z : ℤ, (z : ℝ) ^ 2 * Real.exp (-(Real.pi / s ^ 2) * (z : ℝ) ^ 2)) /
        integerGaussianPartition s := by
  simp only [integerGaussianSecondMoment, integerGaussian_toReal, div_mul_eq_mul_div,
    mul_comm (Real.exp _) _, tsum_div_const]

theorem integerGaussianSecondMoment_nonneg (s : ℝ) (hs : 0 < s) :
    0 ≤ integerGaussianSecondMoment s hs := tsum_nonneg (fun _ => by positivity)

end GeometricGaussianLHL
end

end IntegerGaussianMoments

section GaussianUnitOverlap

/-!
## Uniform overlap at width one

Exact rational exponential bounds verify the paper's `0.921` unit-shift
constant. The partition lower bound keeps the three terms at `-1`, `0`,
and `1` of the actual Gaussian series.
-/

noncomputable section

namespace GeometricGaussianLHL

theorem exp_pi_lt_233_div_ten : Real.exp Real.pi < (233 / 10 : ℝ) := by
  have h1 := Real.exp_bound' (x := 1) (by norm_num) (by norm_num) (n := 8) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h1
  have h3 : Real.exp 3 ≤ (201 / 10 : ℝ) := by
    have hp := pow_le_pow_left₀ (Real.exp_pos 1).le h1 3
    have he : Real.exp (3 : ℝ) = Real.exp 1 ^ 3 := by
      rw [← Real.exp_nat_mul]
      norm_num
    rw [← he] at hp
    norm_num at hp
    linarith
  have h7 := Real.exp_bound' (x := 1 / 7) (by norm_num) (by norm_num) (n := 3) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h7
  have h7' : Real.exp (1 / 7 : ℝ) ≤ 231 / 200 := by linarith
  have harg : Real.pi < 3 + (1 / 7 : ℝ) := by linarith [Real.pi_lt_d4]
  have h := Real.exp_lt_exp.mpr harg
  rw [Real.exp_add] at h
  have hm := mul_le_mul h3 h7' (Real.exp_pos _).le (by norm_num : (0 : ℝ) ≤ 201 / 10)
  linarith

theorem gaussian_unit_overlap_constant :
    1 / (1 + 2 * Real.exp (-Real.pi)) < (921 / 1000 : ℝ) := by
  have he := exp_pi_lt_233_div_ten
  have hpos := Real.exp_pos Real.pi
  have hinv : (10 / 233 : ℝ) < Real.exp (-Real.pi) := by
    rw [Real.exp_neg, ← one_div]
    apply (lt_div_iff₀ hpos).mpr
    linarith
  apply (div_lt_iff₀ (by positivity : 0 < 1 + 2 * Real.exp (-Real.pi))).mpr
  linarith

theorem integerGaussianPartition_three_terms {s : ℝ} (hs : 1 ≤ s) :
    1 + 2 * Real.exp (-Real.pi) ≤ integerGaussianPartition s := by
  have hsp : 0 < s := by linarith
  have hsum := summable_integer_gaussian (div_pos Real.pi_pos (sq_pos_of_pos hsp))
  have hf := hsum.sum_le_tsum ({-1, 0, 1} : Finset ℤ) (fun _ _ => (Real.exp_pos _).le)
  norm_num at hf
  have ha : Real.pi / s ^ 2 ≤ Real.pi := div_le_self Real.pi_pos.le (by nlinarith)
  have he := Real.exp_le_exp.mpr (neg_le_neg ha)
  change 1 + 2 * Real.exp (-Real.pi) ≤ ∑' z : ℤ, Real.exp (-(Real.pi / s ^ 2) * (z : ℝ) ^ 2)
  simp only [neg_mul]
  linarith

theorem integerGaussian_zero_mass_bound {s : ℝ} (hs : 1 ≤ s) :
    (integerGaussian s (by linarith) 0).toReal ≤ 1 / (1 + 2 * Real.exp (-Real.pi)) := by
  rw [integerGaussian_toReal]
  simp only [Int.cast_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, Real.exp_zero]
  exact one_div_le_one_div_of_le (by positivity) (integerGaussianPartition_three_terms hs)

theorem integerGaussian_zero_mass_lt {s : ℝ} (hs : 1 ≤ s) :
    (integerGaussian s (by linarith) 0).toReal < (921 / 1000 : ℝ) :=
  (integerGaussian_zero_mass_bound hs).trans_lt gaussian_unit_overlap_constant

end GeometricGaussianLHL
end

end GaussianUnitOverlap

section IntegerVarianceTail

/-!
## The dual-theta correction in the variance formula

The positive weighted Gaussian tail is dominated by a geometric series
with ratio `1/1000`. This slightly coarser rational bound suffices for the
paper's variance constant `1/16`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace GeometricGaussianLHL

theorem exp_neg_pi_le_one_twentyTwo : Real.exp (-Real.pi) ≤ 1 / 22 := by
  have ht := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 31 / 10) 10
  norm_num [Finset.sum_range_succ] at ht
  have hp : (31 / 10 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d2]
  have hb : 22 ≤ Real.exp Real.pi := by linarith [Real.exp_le_exp.mpr hp]
  rw [Real.exp_neg]
  simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 22) hb

theorem weightedGaussian_step (n : ℕ) :
    ((n : ℝ) + 2) ^ 2 * Real.exp (-Real.pi * ((n : ℝ) + 2) ^ 2) ≤
      (1 / 1000 : ℝ) * (((n : ℝ) + 1) ^ 2 * Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2)) := by
  have hc : Real.exp (-3 * Real.pi) = Real.exp (-Real.pi) ^ 3 := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hratio : 4 * Real.exp (-3 * Real.pi) ≤ (1 / 1000 : ℝ) := by
    rw [hc]
    have h := pow_le_pow_left₀ (Real.exp_pos (-Real.pi)).le exp_neg_pi_le_one_twentyTwo 3
    norm_num at h
    linarith
  have hs : ((n : ℝ) + 2) ^ 2 ≤ 4 * ((n : ℝ) + 1) ^ 2 := by
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have he : Real.exp (-Real.pi * ((n : ℝ) + 2) ^ 2) ≤
      Real.exp (-3 * Real.pi) * Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg Real.pi_pos.le (Nat.cast_nonneg (α := ℝ) n)]
  calc
    _ ≤ (4 * ((n : ℝ) + 1) ^ 2) *
        (Real.exp (-3 * Real.pi) * Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2)) :=
      mul_le_mul hs he (Real.exp_pos _).le (by positivity)
    _ = (4 * Real.exp (-3 * Real.pi)) *
        (((n : ℝ) + 1) ^ 2 * Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hratio (by positivity)

theorem weightedGaussian_geometric (n : ℕ) :
    ((n : ℝ) + 1) ^ 2 * Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2) ≤
      (1 / 22 : ℝ) * (1 / 1000 : ℝ) ^ n := by
  induction n with
  | zero => simpa using exp_neg_pi_le_one_twentyTwo
  | succ n ih =>
    have h := (weightedGaussian_step n).trans (mul_le_mul_of_nonneg_left ih (by norm_num))
    simpa only [Nat.cast_add, Nat.cast_one, pow_succ, show (n : ℝ) + 1 + 1 = (n : ℝ) + 2 by ring,
      mul_comm, mul_left_comm, mul_assoc] using h

theorem integer_gaussian_second_tail_le :
    (∑' z : ℤ, (z : ℝ) ^ 2 * Real.exp (-Real.pi * (z : ℝ) ^ 2)) ≤ 1000 / 10989 := by
  let f : ℤ → ℝ := fun z => (z : ℝ) ^ 2 * Real.exp (-Real.pi * (z : ℝ) ^ 2)
  have hf : Summable f := by simpa only [f, pow_one] using summable_integer_gaussian_evenMoment Real.pi_pos 1
  have hnat : Summable (fun n : ℕ => f n) := hf.comp_injective Nat.cast_injective
  have hneg : Summable (fun n : ℕ => f (-((n : ℤ) + 1))) :=
    hf.comp_injective (fun _ _ h => by omega)
  have hpos : Summable (fun n : ℕ => f ((n : ℤ) + 1)) :=
    hf.comp_injective (fun _ _ h => by omega)
  have hb : (∑' n : ℕ, f ((n : ℤ) + 1)) ≤ 500 / 10989 := by
    have hg := (hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 1000)
      (by norm_num : (1 / 1000 : ℝ) < 1)).summable.mul_left (1 / 22)
    have h := hpos.tsum_le_tsum (fun n => by
      simpa only [f, Int.cast_add, Int.cast_natCast, Int.cast_one] using weightedGaussian_geometric n) hg
    norm_num only [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 1000)
      (by norm_num : (1 / 1000 : ℝ) < 1)] at h
    exact h
  have he := tsum_of_nat_of_neg_add_one hnat hneg
  rw [hnat.tsum_eq_zero_add] at he
  have hneg_eq : (∑' n : ℕ, f (-((n : ℤ) + 1))) = ∑' n : ℕ, f ((n : ℤ) + 1) := by
    apply tsum_congr
    intro n
    simp only [f, Int.cast_neg, neg_sq]
  rw [hneg_eq] at he
  simp only [Nat.cast_zero, Nat.cast_add, Nat.cast_one] at he
  rw [show f 0 = 0 by simp [f], zero_add] at he
  change (∑' z : ℤ, f z) ≤ _
  linarith

theorem scaled_gaussian_square_le {u x : ℝ} (hu : 1 ≤ u) (hx : 1 ≤ x ^ 2) :
    u * Real.exp (-Real.pi * u * x ^ 2) ≤ Real.exp (-Real.pi * x ^ 2) := by
  have hp : 1 ≤ Real.pi * x ^ 2 := by nlinarith [Real.pi_gt_three]
  have he : u ≤ Real.exp (Real.pi * x ^ 2 * (u - 1)) := by
    have h := Real.add_one_le_exp (Real.pi * x ^ 2 * (u - 1))
    nlinarith [mul_nonneg (sub_nonneg.mpr hp) (sub_nonneg.mpr hu)]
  calc
    _ ≤ Real.exp (Real.pi * x ^ 2 * (u - 1)) * Real.exp (-Real.pi * u * x ^ 2) :=
      mul_le_mul_of_nonneg_right he (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem scaled_integer_gaussian_second_tail_le {s : ℝ} (hs : 1 ≤ s) :
    s ^ 2 * (∑' z : ℤ, (z : ℝ) ^ 2 * Real.exp (-(Real.pi * s ^ 2) * (z : ℝ) ^ 2)) ≤
      1000 / 10989 := by
  have hs0 : 0 < s := by linarith
  have hss : 1 ≤ s ^ 2 := by nlinarith
  have hsum : Summable (fun z : ℤ => (z : ℝ) ^ 2 * Real.exp (-(Real.pi * s ^ 2) * (z : ℝ) ^ 2)) := by
    simpa only [pow_one] using summable_integer_gaussian_evenMoment
      (mul_pos Real.pi_pos (sq_pos_of_pos hs0)) 1
  rw [← tsum_mul_left]
  apply ((hsum.mul_left (s ^ 2)).tsum_le_tsum ?_
    (by simpa only [pow_one] using summable_integer_gaussian_evenMoment Real.pi_pos 1)).trans
    integer_gaussian_second_tail_le
  intro z
  by_cases hz : z = 0
  · simp [hz]
  · have hz1 : (1 : ℝ) ≤ (z : ℝ) ^ 2 := by
      have h : (1 : ℤ) ≤ z ^ 2 := by have hp := sq_pos_of_ne_zero hz; omega
      exact_mod_cast h
    have h := mul_le_mul_of_nonneg_left (scaled_gaussian_square_le hss hz1) (sq_nonneg (z : ℝ))
    simpa only [neg_mul, mul_assoc, mul_comm, mul_left_comm] using h

end GeometricGaussianLHL
end

end IntegerVarianceTail

section ProductGaussianMoments

/-!
## Convergent moments of Gaussian linear forms

The distribution is the actual finite product of normalized integer
Gaussians. Reindexing by `Fin.consEquiv` and an absolutely convergent
binomial expansion justify every moment recurrence.
-/

noncomputable section

namespace GeometricGaussianLHL

def integerLinearForm {n : ℕ} (y : Fin n → ℝ) (z : Coeff n) : ℝ :=
  ∑ i, y i * (z i : ℝ)

def productGaussianMoment {n : ℕ} (y : Fin n → ℝ) (s : ℝ) (hs : 0 < s) (k : ℕ) : ℝ :=
  ∑' z : Coeff n, (productIntegerGaussian n s hs z).toReal * integerLinearForm y z ^ k

theorem summable_integerGaussian_pow (s : ℝ) (hs : 0 < s) (k : ℕ) :
    Summable (fun z : ℤ => (integerGaussian s hs z).toReal * (z : ℝ) ^ k) := by
  apply ((summable_integerGaussian_evenMoment s hs 0).add
    (summable_integerGaussian_evenMoment s hs k)).of_norm_bounded
  intro z
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
  simp only [pow_zero, mul_one]
  have hx : |(z : ℝ) ^ k| ≤ 1 + ((z : ℝ) ^ 2) ^ k := by
    have he : ((z : ℝ) ^ 2) ^ k = ((z : ℝ) ^ k) ^ 2 := by ring
    rw [he]
    nlinarith [sq_abs ((z : ℝ) ^ k), sq_nonneg (|(z : ℝ) ^ k| - 1)]
  simpa only [mul_add, mul_one] using mul_le_mul_of_nonneg_left hx
    (show 0 ≤ (integerGaussian s hs z).toReal from ENNReal.toReal_nonneg)

theorem summable_integerGaussian_scaled_pow (s : ℝ) (hs : 0 < s) (a : ℝ) (k : ℕ) :
    Summable (fun z : ℤ => (integerGaussian s hs z).toReal * (a * (z : ℝ)) ^ k) := by
  exact ((summable_integerGaussian_pow s hs k).mul_left (a ^ k)).congr (fun _ => by ring)

theorem productIntegerGaussian_symmetric (n : ℕ) (s : ℝ) (hs : 0 < s) (z : Coeff n) :
    productIntegerGaussian n s hs (-z) = productIntegerGaussian n s hs z := by
  simp only [productIntegerGaussian, independentProduct_apply, Pi.neg_apply, integerGaussian_symmetric]

theorem integerLinearForm_neg {n : ℕ} (y : Fin n → ℝ) (z : Coeff n) :
    integerLinearForm y (-z) = -integerLinearForm y z := by
  simp only [integerLinearForm, Pi.neg_apply, Int.cast_neg, mul_neg, Finset.sum_neg_distrib]

theorem productGaussianMoment_odd {n : ℕ} (y : Fin n → ℝ) (s : ℝ) (hs : 0 < s) (k : ℕ) :
    productGaussianMoment y s hs (2 * k + 1) = 0 := by
  have he := (Equiv.neg (Coeff n)).tsum_eq (fun z : Coeff n =>
    (productIntegerGaussian n s hs z).toReal * integerLinearForm y z ^ (2 * k + 1))
  simp only [Equiv.neg_apply, productIntegerGaussian_symmetric, integerLinearForm_neg,
    (show Odd (2 * k + 1) from ⟨k, by omega⟩).neg_pow, mul_neg, tsum_neg] at he
  change -productGaussianMoment y s hs (2 * k + 1) = productGaussianMoment y s hs (2 * k + 1) at he
  linarith

theorem integerLinearForm_cons {n : ℕ} (y : Fin (n + 1) → ℝ) (a : ℤ) (z : Coeff n) :
    integerLinearForm y (Fin.cons a z) = y 0 * (a : ℝ) +
      integerLinearForm (fun i => y i.succ) z := by
  simp only [integerLinearForm, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]

theorem productIntegerGaussian_cons_toReal {n : ℕ} (s : ℝ) (hs : 0 < s) (a : ℤ) (z : Coeff n) :
    (productIntegerGaussian (n + 1) s hs (Fin.cons a z)).toReal =
      (integerGaussian s hs a).toReal * (productIntegerGaussian n s hs z).toReal := by
  simp only [productIntegerGaussian, independentProduct_apply, Fin.prod_univ_succ,
    Fin.cons_zero, Fin.cons_succ, ENNReal.toReal_mul]

theorem summable_productGaussian_moment {n : ℕ} (y : Fin n → ℝ) (s : ℝ) (hs : 0 < s) (k : ℕ) :
    Summable (fun z : Coeff n => (productIntegerGaussian n s hs z).toReal * integerLinearForm y z ^ k) := by
  induction n generalizing k with
  | zero => exact summable_of_hasFiniteSupport (Set.toFinite _)
  | succ n ih =>
    let e := Fin.consEquiv (fun _ : Fin (n + 1) => ℤ)
    apply e.summable_iff.mp
    change Summable (fun z : ℤ × Coeff n =>
      (productIntegerGaussian (n + 1) s hs (e z)).toReal * integerLinearForm y (e z) ^ k)
    have hh := summable_pmf_product_add_pow (integerGaussian s hs) (productIntegerGaussian n s hs)
      (fun a : ℤ => y 0 * (a : ℝ)) (integerLinearForm (fun i => y i.succ))
      (summable_integerGaussian_scaled_pow s hs (y 0)) (fun k => ih (fun i => y i.succ) k) k
    simpa only [Function.comp_apply, e, Fin.consEquiv, Equiv.coe_fn_mk,
      productIntegerGaussian_cons_toReal, integerLinearForm_cons] using hh

theorem productGaussianMoment_zero {n : ℕ} (y : Fin n → ℝ) (s : ℝ) (hs : 0 < s) :
    productGaussianMoment y s hs 0 = 1 := by
  simp only [productGaussianMoment, pow_zero, mul_one, pmf_tsum_toReal]

theorem productGaussianMoment_succ {n : ℕ} (y : Fin (n + 1) → ℝ) (s : ℝ) (hs : 0 < s) (k : ℕ) :
    productGaussianMoment y s hs k = ∑ j ∈ Finset.range (k + 1),
      (y 0 ^ j * (∑' a : ℤ, (integerGaussian s hs a).toReal * (a : ℝ) ^ j)) *
        productGaussianMoment (fun i => y i.succ) s hs (k - j) * (k.choose j : ℝ) := by
  let e := Fin.consEquiv (fun _ : Fin (n + 1) => ℤ)
  unfold productGaussianMoment
  rw [← e.tsum_eq]
  simp only [e, Fin.consEquiv, Equiv.coe_fn_mk, productIntegerGaussian_cons_toReal,
    integerLinearForm_cons]
  rw [tsum_pmf_product_add_pow (integerGaussian s hs) (productIntegerGaussian n s hs)
    (fun a : ℤ => y 0 * (a : ℝ)) (integerLinearForm (fun i => y i.succ))
    (summable_integerGaussian_scaled_pow s hs (y 0))
    (fun j => summable_productGaussian_moment _ s hs j)]
  apply Finset.sum_congr rfl
  intro j _
  have he : (∑' a : ℤ, (integerGaussian s hs a).toReal * (y 0 * (a : ℝ)) ^ j) =
      y 0 ^ j * ∑' a : ℤ, (integerGaussian s hs a).toReal * (a : ℝ) ^ j := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro a
    ring
  rw [he]

end GeometricGaussianLHL
end

end ProductGaussianMoments

section IntegerGaussianMGF

/-!
## Scalar Gaussian exponential moments

Completing the square and the proved maximum-at-zero theta bound give the moment-generating-function
assertion of the uniform-moments lemma for every positive width. The actual normalized scalar
distribution is used throughout.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace GeometricGaussianLHL

theorem integerGaussian_mgf_tilt (s : ℝ) (hs : 0 < s) (u : ℝ) (z : ℤ) :
    (integerGaussian s hs z).toReal * Real.exp (u * (z : ℝ)) =
      (Real.exp (s ^ 2 * u ^ 2 / (4 * Real.pi)) / integerGaussianPartition s) *
        Real.exp (-Real.pi * (1 / s) ^ 2 * ((z : ℝ) - s ^ 2 * u / (2 * Real.pi)) ^ 2) := by
  rw [integerGaussian_toReal, div_mul_eq_mul_div, div_mul_eq_mul_div, ← Real.exp_add, ← Real.exp_add]
  congr 2
  field_simp
  ring

theorem summable_integerGaussian_mgf (s : ℝ) (hs : 0 < s) (u : ℝ) :
    Summable (fun z : ℤ => (integerGaussian s hs z).toReal * Real.exp (u * (z : ℝ))) := by
  simp_rw [integerGaussian_mgf_tilt]
  exact (periodicGaussian_summable (one_div_pos.mpr hs) (s ^ 2 * u / (2 * Real.pi))).mul_left _

theorem integerGaussian_mgf_le (s : ℝ) (hs : 0 < s) (u : ℝ) :
    (∑' z : ℤ, (integerGaussian s hs z).toReal * Real.exp (u * (z : ℝ))) ≤
      Real.exp (s ^ 2 * u ^ 2 / (4 * Real.pi)) := by
  simp_rw [integerGaussian_mgf_tilt]
  rw [tsum_mul_left]
  have he : periodicGaussian (1 / s) 0 = integerGaussianPartition s := by
    unfold periodicGaussian integerGaussianPartition integerTheta
    apply tsum_congr
    intro z
    congr 1
    ring
  have ht := periodicGaussian_le_zero (one_div_pos.mpr hs) (s ^ 2 * u / (2 * Real.pi))
  rw [he] at ht
  have hp := integerGaussianPartition_pos hs
  calc
    _ ≤ (Real.exp (s ^ 2 * u ^ 2 / (4 * Real.pi)) / integerGaussianPartition s) *
        integerGaussianPartition s := mul_le_mul_of_nonneg_left ht (by positivity)
    _ = _ := div_mul_cancel₀ _ hp.ne'

theorem summable_integerGaussian_linear (s : ℝ) (hs : 0 < s) :
    Summable (fun z : ℤ => (integerGaussian s hs z).toReal * (z : ℝ)) := by
  apply ((summable_integerGaussian_evenMoment s hs 0).add
    (summable_integerGaussian_evenMoment s hs 1)).of_norm_bounded
  intro z
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
  simp only [pow_zero, pow_one, mul_one]
  have hx : |(z : ℝ)| ≤ 1 + (z : ℝ) ^ 2 := by nlinarith [sq_abs (z : ℝ), sq_nonneg (|(z : ℝ)| - 1)]
  simpa only [mul_add, mul_one] using mul_le_mul_of_nonneg_left hx (ENNReal.toReal_nonneg : 0 ≤ (integerGaussian s hs z).toReal)

theorem integerGaussian_mean_zero (s : ℝ) (hs : 0 < s) :
    (∑' z : ℤ, (integerGaussian s hs z).toReal * (z : ℝ)) = 0 := by
  have he := (Equiv.neg ℤ).tsum_eq (fun z : ℤ => (integerGaussian s hs z).toReal * (z : ℝ))
  simp only [Equiv.neg_apply, integerGaussian_symmetric, Int.cast_neg, mul_neg, tsum_neg] at he
  linarith

end GeometricGaussianLHL
end

end IntegerGaussianMGF

section IntegerThetaDerivative

/-!
## Differentiating the actual scalar theta series

A summable polynomial Gaussian bounds the derivatives on a neighborhood
of each positive parameter. This justifies the termwise derivative used
in the discrete variance calculation.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Set

namespace GeometricGaussianLHL

theorem hasDerivAt_integerTheta {a : ℝ} (ha : 0 < a) :
    HasDerivAt integerTheta (-(∑' z : ℤ, (z : ℝ) ^ 2 * Real.exp (-a * (z : ℝ) ^ 2))) a := by
  unfold integerTheta
  have hu : Summable (fun z : ℤ => (z : ℝ) ^ 2 * Real.exp (-(a / 2) * (z : ℝ) ^ 2)) := by
    simpa only [pow_one] using summable_integer_gaussian_evenMoment (half_pos ha) 1
  have hd (z : ℤ) (y : ℝ) : HasDerivAt (fun x : ℝ => Real.exp (-x * (z : ℝ) ^ 2))
      (-(z : ℝ) ^ 2 * Real.exp (-y * (z : ℝ) ^ 2)) y := by
    convert (((hasDerivAt_id y).neg).mul_const ((z : ℝ) ^ 2)).exp using 1 <;> simp [mul_comm]
  have hb (z : ℤ) (y : ℝ) (hy : y ∈ Ioi (a / 2)) :
      ‖-(z : ℝ) ^ 2 * Real.exp (-y * (z : ℝ) ^ 2)‖ ≤
        (z : ℝ) ^ 2 * Real.exp (-(a / 2) * (z : ℝ) ^ 2) := by
    rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg (sq_nonneg _),
      abs_of_pos (Real.exp_pos _)]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right (neg_le_neg hy.le) (sq_nonneg _)
  have h := hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioi (convex_Ioi (a / 2)).isPreconnected
    (fun z y _ => hd z y) hb (half_lt_self ha) (summable_integer_gaussian ha) (half_lt_self ha)
  simpa only [neg_mul, tsum_neg] using h

theorem integerGaussianPartition_poisson {s : ℝ} (hs : 0 < s) :
    integerGaussianPartition s = s * integerTheta (Real.pi * s ^ 2) := by
  have h := periodicGaussian_zero_eq_fourier_sum (one_div_pos.mpr hs)
  have hleft : periodicGaussian (1 / s) 0 = integerGaussianPartition s := by
    unfold periodicGaussian integerGaussianPartition integerTheta
    apply tsum_congr
    intro z
    congr 1
    ring
  rw [hleft] at h
  simp only [gaussianFourierCoefficient, one_div, inv_pow, div_inv_eq_mul, one_mul,
    tsum_mul_left] at h
  exact h

theorem hasDerivAt_integerGaussianPartition {s : ℝ} (hs : 0 < s) :
    HasDerivAt integerGaussianPartition
      ((2 * Real.pi / s ^ 3) *
        (∑' z : ℤ, (z : ℝ) ^ 2 * Real.exp (-(Real.pi / s ^ 2) * (z : ℝ) ^ 2))) s := by
  have hg : HasDerivAt (fun u : ℝ => Real.pi / u ^ 2) (-(2 * Real.pi / s ^ 3)) s := by
    have h0 := (hasDerivAt_const s Real.pi).div ((hasDerivAt_id s).pow 2) (pow_ne_zero _ hs.ne')
    change HasDerivAt (fun u : ℝ => Real.pi / u ^ 2)
      ((0 * s ^ 2 - Real.pi * (2 * s ^ (2 - 1 : ℕ) * 1)) / (s ^ 2) ^ 2) s at h0
    have he : (0 * s ^ 2 - Real.pi * (2 * s ^ (2 - 1 : ℕ) * 1)) / (s ^ 2) ^ 2 =
        -(2 * Real.pi / s ^ 3) := by field_simp; ring
    rw [he] at h0
    exact h0
  have hd := (hasDerivAt_integerTheta (div_pos Real.pi_pos (sq_pos_of_pos hs))).comp s hg
  unfold integerGaussianPartition
  simpa only [Function.comp_def, neg_mul_neg, mul_comm] using hd

theorem integerGaussian_variance_poisson_identity {s : ℝ} (hs : 0 < s) :
    (2 * Real.pi / s ^ 3) *
      (∑' z : ℤ, (z : ℝ) ^ 2 * Real.exp (-(Real.pi / s ^ 2) * (z : ℝ) ^ 2)) =
        integerTheta (Real.pi * s ^ 2) - 2 * Real.pi * s ^ 2 *
          (∑' z : ℤ, (z : ℝ) ^ 2 * Real.exp (-(Real.pi * s ^ 2) * (z : ℝ) ^ 2)) := by
  have hd := (hasDerivAt_id s).mul
    ((hasDerivAt_integerTheta (mul_pos Real.pi_pos (sq_pos_of_pos hs))).comp s
      (((hasDerivAt_id s).pow 2).const_mul Real.pi))
  have he : integerGaussianPartition =ᶠ[nhds s]
      (fun u => u * integerTheta (Real.pi * u ^ 2)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hs] with u hu
    exact integerGaussianPartition_poisson hu
  have heq := (hasDerivAt_integerGaussianPartition hs).unique (hd.congr_of_eventuallyEq he)
  convert heq using 1
  dsimp
  ring

end GeometricGaussianLHL
end

end IntegerThetaDerivative

section IntegerGaussianCharacter

/-!
## The exact characteristic coefficient of a modular Gaussian

Poisson summation identifies the expectation of the first modular character
with a positive shifted dual Gaussian sum divided by the dual partition.
-/
noncomputable section
namespace GeometricGaussianLHL

theorem zmod_stdAddChar_fourier (q : ℕ) [NeZero q] (z : ℤ) :
    ZMod.stdAddChar (z : ZMod q) = fourier z (((1 / (q : ℝ)) : ℝ) : UnitAddCircle) := by
  rw [ZMod.stdAddChar_coe, fourier_coe_apply]
  push_cast
  congr 1
  ring

theorem integerGaussian_character_poisson {s : ℝ} (hs : 0 < s) (q : ℕ) [NeZero q] :
    pmfComplexExpectation (integerGaussian s hs) (fun z : ℤ => ZMod.stdAddChar (z : ZMod q)) =
      ((periodicGaussian s (-(1 / (q : ℝ))) / integerTheta (Real.pi * s ^ 2) : ℝ) : ℂ) := by
  have ht : 0 < integerTheta (Real.pi * s ^ 2) :=
    zero_lt_one.trans_le (integerTheta_ge_one (mul_pos Real.pi_pos (sq_pos_of_pos hs)))
  have h := periodicGaussian_fourier hs (-(1 / (q : ℝ)))
  simp only [neg_neg] at h
  have he (z : ℤ) : ((integerGaussian s hs z).toReal : ℂ) * ZMod.stdAddChar (z : ZMod q) =
      ((gaussianFourierCoefficient s z : ℂ) * fourier z ((1 / (q : ℝ) : ℝ) : UnitAddCircle)) /
        (integerTheta (Real.pi * s ^ 2) : ℂ) := by
    rw [zmod_stdAddChar_fourier, integerGaussian_toReal, integerGaussianPartition_poisson hs]
    unfold gaussianFourierCoefficient
    push_cast
    field_simp
  unfold pmfComplexExpectation
  simp_rw [he]
  rw [tsum_div_const, ← h, Complex.ofReal_div]

theorem integerGaussian_modular_distance_lower {s : ℝ} (hs : 0 < s)
    (q : ℕ) [NeZero q] [Nontrivial (ZMod q)] :
    Real.exp (-Real.pi * s ^ 2 / (q : ℝ) ^ 2) / (2 * integerTheta (Real.pi * s ^ 2)) ≤
      discreteTotalVariation ((integerGaussian s hs).map (fun z : ℤ => (z : ZMod q)))
        (PMF.uniformOfFintype (ZMod q)) := by
  have ht : 0 < integerTheta (Real.pi * s ^ 2) :=
    zero_lt_one.trans_le (integerTheta_ge_one (mul_pos Real.pi_pos (sq_pos_of_pos hs)))
  have hnorm : ∀ a : ZMod q, ‖ZMod.stdAddChar a‖ ≤ 1 := fun a => (zmod_stdAddChar_norm q a).le
  have htest := pmfComplexExpectation_sub_norm_le
    ((integerGaussian s hs).map (fun z : ℤ => (z : ZMod q)))
    (PMF.uniformOfFintype (ZMod q)) ZMod.stdAddChar hnorm
  rw [uniform_zmod_character_zero, sub_zero, pmfComplexExpectation_map _ _ _ hnorm] at htest
  dsimp only [Function.comp_def] at htest
  rw [integerGaussian_character_poisson hs q,
    Complex.norm_of_nonneg (div_nonneg (periodicGaussian_pos hs _).le ht.le)] at htest
  have hterm := (periodicGaussian_summable hs (-(1 / (q : ℝ)))).le_tsum 0
    (fun _ _ => (Real.exp_pos _).le)
  change Real.exp (-Real.pi * s ^ 2 * ((0 : ℤ) - -(1 / (q : ℝ))) ^ 2) ≤
    periodicGaussian s (-(1 / (q : ℝ))) at hterm
  have he : -Real.pi * s ^ 2 * ((0 : ℤ) - -(1 / (q : ℝ))) ^ 2 =
      -Real.pi * s ^ 2 / (q : ℝ) ^ 2 := by push_cast; ring
  rw [he] at hterm
  have h := (div_le_div_of_nonneg_right hterm ht.le).trans htest
  calc
    _ = (Real.exp (-Real.pi * s ^ 2 / (q : ℝ) ^ 2) / integerTheta (Real.pi * s ^ 2)) / 2 := by ring
    _ ≤ _ := by linarith

end GeometricGaussianLHL
end

end IntegerGaussianCharacter

section IntegerGaussianFourthMoment

/-!
## A fourth-moment bound for the scalar discrete Gaussian

Poisson summation compares the partitions at widths `s` and `sqrt 2 * s`.
This controls a squared exponential moment and then the fourth moment,
which will support an elementary constant-width contraction proof.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace GeometricGaussianLHL

theorem integerTheta_antitone {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : integerTheta b ≤ integerTheta a := by
  apply (summable_integer_gaussian (ha.trans_le hab)).tsum_le_tsum _ (summable_integer_gaussian ha)
  intro z
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg hab) (sq_nonneg _))

theorem integerGaussianPartition_sqrt_two_le {s : ℝ} (hs : 0 < s) :
    integerGaussianPartition (s * Real.sqrt 2) ≤ Real.sqrt 2 * integerGaussianPartition s := by
  rw [integerGaussianPartition_poisson (mul_pos hs (Real.sqrt_pos.mpr (by norm_num))),
    integerGaussianPartition_poisson hs]
  have h := integerTheta_antitone (mul_pos Real.pi_pos (sq_pos_of_pos hs))
    (show Real.pi * s ^ 2 ≤ Real.pi * (s * Real.sqrt 2) ^ 2 by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      nlinarith [mul_pos Real.pi_pos (sq_pos_of_pos hs)])
  exact (mul_le_mul_of_nonneg_left h (by positivity)).trans_eq (by ring)

theorem integerGaussian_exp_sq_tilt (s : ℝ) (hs : 0 < s) (z : ℤ) :
    (integerGaussian s hs z).toReal * Real.exp (Real.pi * (z : ℝ) ^ 2 / (2 * s ^ 2)) =
      Real.exp (-(Real.pi / (s * Real.sqrt 2) ^ 2) * (z : ℝ) ^ 2) / integerGaussianPartition s := by
  rw [integerGaussian_toReal, div_mul_eq_mul_div, ← Real.exp_add,
    mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  congr 2
  ring

theorem summable_integerGaussian_exp_sq (s : ℝ) (hs : 0 < s) :
    Summable (fun z : ℤ => (integerGaussian s hs z).toReal *
      Real.exp (Real.pi * (z : ℝ) ^ 2 / (2 * s ^ 2))) := by
  simp_rw [integerGaussian_exp_sq_tilt]
  exact (summable_integer_gaussian (div_pos Real.pi_pos
    (sq_pos_of_pos (mul_pos hs (Real.sqrt_pos.mpr (by norm_num)))))).div_const _

theorem integerGaussian_exp_sq_le (s : ℝ) (hs : 0 < s) :
    (∑' z : ℤ, (integerGaussian s hs z).toReal *
      Real.exp (Real.pi * (z : ℝ) ^ 2 / (2 * s ^ 2))) ≤ Real.sqrt 2 := by
  simp_rw [integerGaussian_exp_sq_tilt]
  rw [tsum_div_const]
  exact (div_le_iff₀ (integerGaussianPartition_pos hs)).mpr (integerGaussianPartition_sqrt_two_le hs)

theorem gaussian_fourthMoment_majorant {s : ℝ} (hs : 0 < s) (x : ℝ) :
    x ^ 4 ≤ (8 * s ^ 4 / Real.pi ^ 2) * Real.exp (Real.pi * x ^ 2 / (2 * s ^ 2)) := by
  have h := Real.pow_div_factorial_le_exp (Real.pi * x ^ 2 / (2 * s ^ 2)) (by positivity) 2
  norm_num only [Nat.factorial, Nat.cast_ofNat] at h
  have he : x ^ 4 = ((Real.pi * x ^ 2 / (2 * s ^ 2)) ^ 2 / 2) *
      (8 * s ^ 4 / Real.pi ^ 2) := by field_simp; ring
  rw [he]
  exact (mul_le_mul_of_nonneg_right h (by positivity)).trans_eq (mul_comm _ _)

theorem integerGaussian_fourthMoment_le (s : ℝ) (hs : 0 < s) :
    (∑' z : ℤ, (integerGaussian s hs z).toReal * (z : ℝ) ^ 4) ≤ 2 * s ^ 4 := by
  have hsum : Summable (fun z : ℤ => (integerGaussian s hs z).toReal * (z : ℝ) ^ 4) := by
    simpa only [← pow_mul] using summable_integerGaussian_evenMoment s hs 2
  have hmajor : Summable (fun z : ℤ => (integerGaussian s hs z).toReal *
      ((8 * s ^ 4 / Real.pi ^ 2) * Real.exp (Real.pi * (z : ℝ) ^ 2 / (2 * s ^ 2)))) :=
    ((summable_integerGaussian_exp_sq s hs).mul_left (8 * s ^ 4 / Real.pi ^ 2)).congr
      (fun z => by ring)
  have h := hsum.tsum_le_tsum
    (fun z : ℤ => mul_le_mul_of_nonneg_left (gaussian_fourthMoment_majorant hs (z : ℝ))
      (show 0 ≤ (integerGaussian s hs z).toReal from ENNReal.toReal_nonneg))
    hmajor
  have ht : (∑' z : ℤ, (integerGaussian s hs z).toReal *
      ((8 * s ^ 4 / Real.pi ^ 2) * Real.exp (Real.pi * (z : ℝ) ^ 2 / (2 * s ^ 2)))) =
        (8 * s ^ 4 / Real.pi ^ 2) * (∑' z : ℤ, (integerGaussian s hs z).toReal *
          Real.exp (Real.pi * (z : ℝ) ^ 2 / (2 * s ^ 2))) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro z
    ring
  rw [ht] at h
  have hc : 8 * Real.sqrt 2 / Real.pi ^ 2 ≤ 2 := by
    apply (div_le_iff₀ (sq_pos_of_pos Real.pi_pos)).mpr
    have hr : Real.sqrt 2 ≤ 2 := (Real.sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
    nlinarith [Real.pi_gt_three]
  calc
    _ ≤ (8 * s ^ 4 / Real.pi ^ 2) * Real.sqrt 2 := h.trans
      (mul_le_mul_of_nonneg_left (integerGaussian_exp_sq_le s hs) (by positivity))
    _ = (8 * Real.sqrt 2 / Real.pi ^ 2) * s ^ 4 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hc (by positivity)

end GeometricGaussianLHL
end

end IntegerGaussianFourthMoment

section IntegerGaussianVariance

/-!
## The uniform discrete Gaussian variance lower bound

The normalized second moment is evaluated by the differentiated Poisson identity, and the proved
dual-theta tail gives the uniform-moments lemma's constant `1/16` .
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace GeometricGaussianLHL

theorem integerGaussianSecondMoment_poisson (s : ℝ) (hs : 0 < s) :
    integerGaussianSecondMoment s hs / s ^ 2 = 1 / (2 * Real.pi) -
      (s ^ 2 * (∑' z : ℤ, (z : ℝ) ^ 2 * Real.exp (-(Real.pi * s ^ 2) * (z : ℝ) ^ 2))) /
        integerTheta (Real.pi * s ^ 2) := by
  have ht : 0 < integerTheta (Real.pi * s ^ 2) := zero_lt_one.trans_le
    (integerTheta_ge_one (mul_pos Real.pi_pos (sq_pos_of_pos hs)))
  have h := integerGaussian_variance_poisson_identity hs
  rw [integerGaussianSecondMoment_eq, integerGaussianPartition_poisson hs]
  field_simp [hs.ne', ht.ne', Real.pi_ne_zero] at h ⊢
  nlinarith only [h]

theorem integerGaussianSecondMoment_lower {s : ℝ} (hs : 1 ≤ s) :
    s ^ 2 / 16 ≤ integerGaussianSecondMoment s (by linarith) := by
  have hs0 : 0 < s := by linarith
  have ht := integerTheta_ge_one (mul_pos Real.pi_pos (sq_pos_of_pos hs0))
  have hn : 0 ≤ s ^ 2 * (∑' z : ℤ, (z : ℝ) ^ 2 *
      Real.exp (-(Real.pi * s ^ 2) * (z : ℝ) ^ 2)) :=
    mul_nonneg (sq_nonneg s) (tsum_nonneg (fun _ => by positivity))
  have hquot := (div_le_self hn ht).trans (scaled_integer_gaussian_second_tail_le hs)
  have hpi : (5 / 32 : ℝ) ≤ 1 / (2 * Real.pi) := by
    apply (le_div_iff₀ (mul_pos (by norm_num) Real.pi_pos)).mpr
    linarith [Real.pi_lt_d2]
  have hbound : (1 / 16 : ℝ) ≤ integerGaussianSecondMoment s hs0 / s ^ 2 := by
    rw [integerGaussianSecondMoment_poisson]
    linarith
  have h := (le_div_iff₀ (sq_pos_of_pos hs0)).mp hbound
  linarith

end GeometricGaussianLHL
end

end IntegerGaussianVariance

section IntegerGaussianNonuniform

/-!
## The numerical nonuniformity bound at coefficient width one

The strict constant `0.459` in the constant-width asymptotic parameter discussion follows from a
rational bound on the scalar theta series. The modulus is explicitly at least two.
-/
noncomputable section
namespace GeometricGaussianLHL

theorem exp_neg_pi_le_one_twentyThree : Real.exp (-Real.pi) ≤ 1 / 23 := by
  have ht := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 314 / 100) 14
  norm_num [Finset.sum_range_succ] at ht
  have hp : (314 / 100 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d4]
  have hb : 23 ≤ Real.exp Real.pi := by linarith [Real.exp_le_exp.mpr hp]
  rw [Real.exp_neg]
  simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 23) hb

theorem weightedGaussian_geometric_twentyThree (n : ℕ) :
    ((n : ℝ) + 1) ^ 2 * Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2) ≤
      (1 / 23 : ℝ) * (1 / 1000 : ℝ) ^ n := by
  induction n with
  | zero => simpa using exp_neg_pi_le_one_twentyThree
  | succ n ih =>
    have h := (weightedGaussian_step n).trans (mul_le_mul_of_nonneg_left ih (by norm_num))
    simpa only [Nat.cast_add, Nat.cast_one, pow_succ, show (n : ℝ) + 1 + 1 = (n : ℝ) + 2 by ring,
      mul_comm, mul_left_comm, mul_assoc] using h

theorem integerTheta_pi_upper : integerTheta Real.pi ≤ 1 + 2000 / 22977 := by
  let f : ℤ → ℝ := fun z => Real.exp (-Real.pi * (z : ℝ) ^ 2)
  have hf : Summable f := summable_integer_gaussian Real.pi_pos
  have hnat : Summable (fun n : ℕ => f n) := hf.comp_injective Nat.cast_injective
  have hneg : Summable (fun n : ℕ => f (-((n : ℤ) + 1))) := hf.comp_injective (fun _ _ h => by omega)
  have hpos : Summable (fun n : ℕ => f ((n : ℤ) + 1)) := hf.comp_injective (fun _ _ h => by omega)
  have hb : (∑' n : ℕ, f ((n : ℤ) + 1)) ≤ 1000 / 22977 := by
    have hg := (hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 1000)
      (by norm_num : (1 / 1000 : ℝ) < 1)).summable.mul_left (1 / 23)
    have h := hpos.tsum_le_tsum (fun n => by
      have hw := weightedGaussian_geometric_twentyThree n
      have hs : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
      have hmul := mul_le_mul_of_nonneg_right hs (Real.exp_pos (-Real.pi * ((n : ℝ) + 1) ^ 2)).le
      dsimp [f]
      push_cast
      nlinarith) hg
    norm_num only [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 1000)
      (by norm_num : (1 / 1000 : ℝ) < 1)] at h
    exact h
  have he := tsum_of_nat_of_neg_add_one hnat hneg
  rw [hnat.tsum_eq_zero_add] at he
  have hneg_eq : (∑' n : ℕ, f (-((n : ℤ) + 1))) = ∑' n : ℕ, f ((n : ℤ) + 1) := by
    apply tsum_congr
    intro n
    simp only [f, Int.cast_neg, neg_sq]
  rw [hneg_eq] at he
  simp only [Nat.cast_zero, Nat.cast_add, Nat.cast_one] at he
  rw [show f 0 = 1 by simp [f]] at he
  change (∑' z : ℤ, f z) ≤ _
  linarith

theorem integerGaussian_widthOne_nonuniform (q : ℕ) (hq : 2 ≤ q) :
    let : NeZero q := ⟨by omega⟩
    (459 / 1000 : ℝ) * Real.exp (-Real.pi / (q : ℝ) ^ 2) <
      discreteTotalVariation ((integerGaussian 1 (by norm_num)).map (fun z : ℤ => (z : ZMod q)))
        (PMF.uniformOfFintype (ZMod q)) := by
  let : NeZero q := ⟨by omega⟩
  let : Fact (1 < q) := ⟨by omega⟩
  have h := integerGaussian_modular_distance_lower (by norm_num : (0 : ℝ) < 1) q
  norm_num only [one_pow, mul_one] at h
  have ht := integerTheta_ge_one Real.pi_pos
  have hden : (459 / 1000 : ℝ) < 1 / (2 * integerTheta Real.pi) := by
    apply (lt_div_iff₀ (by positivity)).mpr
    nlinarith [integerTheta_pi_upper]
  have hmul := mul_lt_mul_of_pos_right hden (Real.exp_pos (-Real.pi / (q : ℝ) ^ 2))
  have hstrict : (459 / 1000 : ℝ) * Real.exp (-Real.pi / (q : ℝ) ^ 2) <
      Real.exp (-Real.pi / (q : ℝ) ^ 2) / (2 * integerTheta Real.pi) := by
    simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using hmul
  exact hstrict.trans_le h

end GeometricGaussianLHL
end

end IntegerGaussianNonuniform

section IntegerGaussianThirdMoment

/-!
## Uniform scalar discrete Gaussian moments

The third absolute moment is bounded by the integral and maximum of the cubic Gaussian. Together
with the proved variance and MGF estimates this completes the uniform-moments lemma for the actual
normalized integer Gaussian.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace GeometricGaussianLHL

theorem abs_cube_le_one_add_fourth (x : ℝ) : |x| ^ 3 ≤ 1 + x ^ 4 := by
  have h4 : |x| ^ 4 = x ^ 4 := by
    calc
      |x| ^ 4 = (|x| ^ 2) ^ 2 := by ring
      _ = (x ^ 2) ^ 2 := congrArg (fun y : ℝ => y ^ 2) (sq_abs x)
      _ = x ^ 4 := by ring
  by_cases hx : |x| ≤ 1
  · have h := pow_le_pow_left₀ (abs_nonneg x) hx 3
    norm_num at h
    linarith [show 0 ≤ x ^ 4 by positivity]
  · have h := pow_le_pow_right₀ (le_of_lt (lt_of_not_ge hx)) (by norm_num : 3 ≤ 4)
    rw [h4] at h
    linarith

theorem summable_integer_gaussian_abs_third {a : ℝ} (ha : 0 < a) :
    Summable (fun z : ℤ => |(z : ℝ)| ^ 3 * Real.exp (-a * (z : ℝ) ^ 2)) := by
  have h4 : Summable (fun z : ℤ => (z : ℝ) ^ 4 * Real.exp (-a * (z : ℝ) ^ 2)) := by
    simpa only [← pow_mul] using summable_integer_gaussian_evenMoment ha 2
  apply ((summable_integer_gaussian ha).add h4).of_norm_bounded
  intro z
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  simpa only [add_mul, one_mul] using
    mul_le_mul_of_nonneg_right (abs_cube_le_one_add_fourth (z : ℝ)) (Real.exp_pos _).le

theorem integerGaussianThirdAbsMoment_eq (s : ℝ) (hs : 0 < s) :
    integerGaussianThirdAbsMoment s hs =
      (∑' z : ℤ, |(z : ℝ)| ^ 3 * Real.exp (-(Real.pi / s ^ 2) * (z : ℝ) ^ 2)) /
        integerGaussianPartition s := by
  simp only [integerGaussianThirdAbsMoment, integerGaussian_toReal, div_mul_eq_mul_div,
    mul_comm (Real.exp _) _, tsum_div_const]

theorem summable_integerGaussian_abs_third (s : ℝ) (hs : 0 < s) :
    Summable (fun z : ℤ => (integerGaussian s hs z).toReal * |(z : ℝ)| ^ 3) := by
  simpa only [integerGaussian_toReal, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
    (summable_integer_gaussian_abs_third (div_pos Real.pi_pos (sq_pos_of_pos hs))).div_const
      (integerGaussianPartition s)

theorem integer_gaussian_abs_third_le {s : ℝ} (hs : 0 < s) :
    (∑' z : ℤ, |(z : ℝ)| ^ 3 * Real.exp (-(Real.pi / s ^ 2) * (z : ℝ) ^ 2)) ≤
      2 * (s ^ 4 / (2 * Real.pi ^ 2) +
        s ^ 3 * (Real.sqrt (3 / (2 * Real.pi))) ^ 3 * Real.exp (-(3 / 2 : ℝ))) := by
  let f : ℤ → ℝ := fun z => |(z : ℝ)| ^ 3 * Real.exp (-(Real.pi / s ^ 2) * (z : ℝ) ^ 2)
  have hf : Summable f := summable_integer_gaussian_abs_third (div_pos Real.pi_pos (sq_pos_of_pos hs))
  have hnat : Summable (fun n : ℕ => f n) := hf.comp_injective Nat.cast_injective
  have hneg : Summable (fun n : ℕ => f (-((n : ℤ) + 1))) := hf.comp_injective (fun _ _ h => by omega)
  have he := tsum_of_nat_of_neg_add_one hnat hneg
  rw [hnat.tsum_eq_zero_add] at he
  have hneg_eq : (∑' n : ℕ, f (-((n : ℤ) + 1))) = ∑' n : ℕ, f ((n : ℤ) + 1) := by
    apply tsum_congr
    intro n
    simp only [f, Int.cast_neg, abs_neg, neg_sq]
  rw [hneg_eq] at he
  simp only [Nat.cast_zero, Nat.cast_add, Nat.cast_one] at he
  rw [show f 0 = 0 by simp [f], zero_add] at he
  have hb : (∑' n : ℕ, f ((n : ℤ) + 1)) ≤ s ^ 4 / (2 * Real.pi ^ 2) +
      s ^ 3 * (Real.sqrt (3 / (2 * Real.pi))) ^ 3 * Real.exp (-(3 / 2 : ℝ)) := by
    have hfpos (n : ℕ) : f ((n : ℤ) + 1) = (((n + 1 : ℕ) : ℝ) ^ 3) *
        Real.exp (-(Real.pi / s ^ 2) * ((n + 1 : ℕ) : ℝ) ^ 2) := by
      dsimp [f]
      push_cast
      rw [abs_of_nonneg (by positivity)]
    simp_rw [hfpos]
    exact positive_integer_cubicGaussian_sum_le hs
  change (∑' z : ℤ, f z) ≤ _
  linarith

theorem integerGaussianThirdAbsMoment_upper {s : ℝ} (hs : 1 ≤ s) :
    integerGaussianThirdAbsMoment s (by linarith) ≤ s ^ 3 / 4 := by
  have hs0 : 0 < s := by linarith
  have hpart : s ≤ integerGaussianPartition s := by
    rw [integerGaussianPartition_poisson hs0]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (integerTheta_ge_one (mul_pos Real.pi_pos (sq_pos_of_pos hs0))) hs0.le
  have hn : 0 ≤ ∑' z : ℤ, |(z : ℝ)| ^ 3 * Real.exp (-(Real.pi / s ^ 2) * (z : ℝ) ^ 2) :=
    tsum_nonneg (fun _ => by positivity)
  rw [integerGaussianThirdAbsMoment_eq]
  apply (div_le_div_of_nonneg_left hn hs0 hpart).trans
  apply ((div_le_div_of_nonneg_right (integer_gaussian_abs_third_le hs0) hs0.le)).trans
  have he : 2 * (s ^ 4 / (2 * Real.pi ^ 2) + s ^ 3 *
      (Real.sqrt (3 / (2 * Real.pi))) ^ 3 * Real.exp (-(3 / 2 : ℝ))) / s =
        s ^ 3 / Real.pi ^ 2 + 2 * s ^ 2 *
          (Real.sqrt (3 / (2 * Real.pi))) ^ 3 * Real.exp (-(3 / 2 : ℝ)) := by field_simp
  rw [he]
  have hs23 : s ^ 2 ≤ s ^ 3 := by nlinarith [mul_nonneg (sq_nonneg s) (sub_nonneg.mpr hs)]
  have h := mul_le_mul_of_nonneg_right hs23
    (show 0 ≤ 2 * (Real.sqrt (3 / (2 * Real.pi))) ^ 3 * Real.exp (-(3 / 2 : ℝ)) by positivity)
  have hc := mul_le_mul_of_nonneg_left gaussian_cubic_constant_lt.le (pow_nonneg hs0.le 3)
  calc
    _ ≤ s ^ 3 / Real.pi ^ 2 + s ^ 3 *
        (2 * (Real.sqrt (3 / (2 * Real.pi))) ^ 3 * Real.exp (-(3 / 2 : ℝ))) := by
      nlinarith only [h]
    _ = s ^ 3 * (1 / Real.pi ^ 2 + 2 *
        (Real.sqrt (3 / (2 * Real.pi))) ^ 3 * Real.exp (-(3 / 2 : ℝ))) := by ring
    _ ≤ s ^ 3 / 4 := by linarith only [hc]

theorem integerGaussian_uniform_moments {s : ℝ} (hs : 1 ≤ s) :
    s ^ 2 / 16 ≤ integerGaussianSecondMoment s (by linarith) ∧
    integerGaussianThirdAbsMoment s (by linarith) ≤ s ^ 3 / 4 ∧
    ∀ u : ℝ, (∑' z : ℤ, (integerGaussian s (by linarith) z).toReal * Real.exp (u * (z : ℝ))) ≤
      Real.exp (s ^ 2 * u ^ 2 / (4 * Real.pi)) :=
  ⟨integerGaussianSecondMoment_lower hs, integerGaussianThirdAbsMoment_upper hs,
    integerGaussian_mgf_le s (by linarith)⟩

end GeometricGaussianLHL
end

end IntegerGaussianThirdMoment

section ProductGaussianFourthMoment

/-!
## Exact second and fourth moments of Gaussian linear forms

Independence supplies the exact fourth-moment formula. Small coordinates
then bound it by five times the second moment squared, allowing a direct
Paley–Zygmund escape estimate for the actual product Gaussian.
-/

noncomputable section

namespace GeometricGaussianLHL

theorem productGaussianMoment_second_succ {n : ℕ} (y : Fin (n + 1) → ℝ)
    (s : ℝ) (hs : 0 < s) :
    productGaussianMoment y s hs 2 =
      y 0 ^ 2 * integerGaussianSecondMoment s hs +
        productGaussianMoment (fun i => y i.succ) s hs 2 := by
  have hz : productGaussianMoment (fun i : Fin n => y i.succ) s hs 1 = 0 :=
    productGaussianMoment_odd _ s hs 0
  rw [productGaussianMoment_succ]
  norm_num [Finset.sum_range_succ, Nat.choose, productGaussianMoment_zero,
    integerGaussian_mean_zero, hz, integerGaussianSecondMoment]
  ring

theorem productGaussianMoment_second {n : ℕ} (y : Fin n → ℝ) (s : ℝ) (hs : 0 < s) :
    productGaussianMoment y s hs 2 = integerGaussianSecondMoment s hs * ∑ i, y i ^ 2 := by
  induction n with
  | zero => simp [productGaussianMoment, integerLinearForm]
  | succ n ih =>
    rw [productGaussianMoment_second_succ, ih, Fin.sum_univ_succ]
    ring

theorem productGaussianMoment_fourth_succ {n : ℕ} (y : Fin (n + 1) → ℝ)
    (s : ℝ) (hs : 0 < s) :
    productGaussianMoment y s hs 4 =
      y 0 ^ 4 * (∑' a : ℤ, (integerGaussian s hs a).toReal * (a : ℝ) ^ 4) +
      6 * y 0 ^ 2 * integerGaussianSecondMoment s hs *
        productGaussianMoment (fun i => y i.succ) s hs 2 +
      productGaussianMoment (fun i => y i.succ) s hs 4 := by
  have hz : productGaussianMoment (fun i : Fin n => y i.succ) s hs 1 = 0 :=
    productGaussianMoment_odd _ s hs 0
  rw [productGaussianMoment_succ]
  norm_num [Finset.sum_range_succ, Nat.choose, productGaussianMoment_zero,
    integerGaussian_mean_zero, hz, integerGaussianSecondMoment]
  ring

/-- The exact fourth moment, including the fourth cumulant of each scalar
coordinate. The statement also covers the zero-dimensional product.
-/
theorem productGaussianMoment_fourth {n : ℕ} (y : Fin n → ℝ) (s : ℝ) (hs : 0 < s) :
    productGaussianMoment y s hs 4 =
      3 * (integerGaussianSecondMoment s hs * ∑ i, y i ^ 2) ^ 2 +
      ((∑' a : ℤ, (integerGaussian s hs a).toReal * (a : ℝ) ^ 4) -
        3 * integerGaussianSecondMoment s hs ^ 2) * ∑ i, y i ^ 4 := by
  induction n with
  | zero => simp [productGaussianMoment, integerLinearForm]
  | succ n ih =>
    rw [productGaussianMoment_fourth_succ, ih, productGaussianMoment_second,
      Fin.sum_univ_succ, Fin.sum_univ_succ]
    ring

theorem productGaussianMoment_fourth_le {n : ℕ} (y : Fin n → ℝ) (s : ℝ) (hs : 0 < s)
    {A : ℝ} (hA : ∀ i, y i ^ 2 ≤ A) :
    productGaussianMoment y s hs 4 ≤
      3 * (integerGaussianSecondMoment s hs * ∑ i, y i ^ 2) ^ 2 +
        2 * s ^ 4 * A * ∑ i, y i ^ 2 := by
  have hsum : (∑ i, y i ^ 4) ≤ A * ∑ i, y i ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => by nlinarith [mul_le_mul_of_nonneg_right (hA i) (sq_nonneg (y i))])
  have hn : 0 ≤ ∑ i, y i ^ 4 := Finset.sum_nonneg (fun i _ => by positivity)
  have hm := mul_le_mul_of_nonneg_right (integerGaussian_fourthMoment_le s hs) hn
  have ha := mul_le_mul_of_nonneg_left hsum (show 0 ≤ 2 * s ^ 4 by positivity)
  rw [productGaussianMoment_fourth]
  have hv := mul_nonneg (sq_nonneg (integerGaussianSecondMoment s hs)) hn
  nlinarith

/-- Uniformly small coordinates give the moment ratio needed below. -/
theorem productGaussianMoment_fourth_le_five {n : ℕ} (y : Fin n → ℝ) {s : ℝ} (hs : 1 ≤ s)
    (hy : ∀ i, y i ^ 2 ≤ (∑ j, y j ^ 2) / 400) :
    productGaussianMoment y s (by linarith) 4 ≤
      5 * (integerGaussianSecondMoment s (by linarith) * ∑ i, y i ^ 2) ^ 2 := by
  have hsp : 0 < s := by linarith
  let Q : ℝ := ∑ i, y i ^ 2
  let v := integerGaussianSecondMoment s hsp
  have hQ : 0 ≤ Q := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hv : s ^ 2 / 16 ≤ v := integerGaussianSecondMoment_lower hs
  have hv0 : 0 ≤ v := integerGaussianSecondMoment_nonneg s hsp
  have hv2 : s ^ 4 ≤ 256 * v ^ 2 := by
    have hsq := (sq_le_sq₀ (by positivity : 0 ≤ s ^ 2 / 16) hv0).mpr hv
    nlinarith
  have h := productGaussianMoment_fourth_le y s hsp hy
  change productGaussianMoment y s hsp 4 ≤ 3 * (v * Q) ^ 2 + 2 * s ^ 4 * (Q / 400) * Q at h
  have hm := mul_le_mul_of_nonneg_right hv2 (sq_nonneg Q)
  change productGaussianMoment y s hsp 4 ≤ 5 * (v * Q) ^ 2
  nlinarith [sq_nonneg (v * Q)]

/-- At least `1/20` of an actual product Gaussian linear form exceeds
half its second moment in squared magnitude. -/
theorem productGaussian_square_escape {n : ℕ} (y : Fin n → ℝ) {s : ℝ} (hs : 1 ≤ s)
    (hQ : 0 < ∑ i, y i ^ 2) (hy : ∀ i, y i ^ 2 ≤ (∑ j, y j ^ 2) / 400) :
    (1 / 20 : ℝ) ≤ (productIntegerGaussian n s (by linarith)).toMeasure.real
      {z | (integerGaussianSecondMoment s (by linarith) * ∑ i, y i ^ 2) / 2 <
        integerLinearForm y z ^ 2} := by
  have hsp : 0 < s := by linarith
  apply pmf_square_escape_of_fourth_moment (productIntegerGaussian n s hsp) (integerLinearForm y)
  · exact mul_pos ((by positivity : 0 < s ^ 2 / 16).trans_le (integerGaussianSecondMoment_lower hs)) hQ
  · exact summable_productGaussian_moment y s hsp 2
  · exact summable_productGaussian_moment y s hsp 4
  · exact productGaussianMoment_second y s hsp
  · exact productGaussianMoment_fourth_le_five y hs hy

end GeometricGaussianLHL
end

end ProductGaussianFourthMoment

section UniformGaussianEscape

/-!
## Uniform escape for every Gaussian linear form

Without a small-coordinate assumption, the fourth moment is at most
`515` times the second moment squared. This gives a conservative absolute
escape probability, sufficient for the lower spectral estimate.
-/

noncomputable section

open MeasureTheory

namespace GeometricGaussianLHL

theorem productGaussianMoment_fourth_le_uniform {n : ℕ} (y : Fin n → ℝ) {s : ℝ} (hs : 1 ≤ s) :
    productGaussianMoment y s (by linarith) 4 ≤
      515 * (integerGaussianSecondMoment s (by linarith) * ∑ i, y i ^ 2) ^ 2 := by
  have hsp : 0 < s := by linarith
  let Q : ℝ := ∑ i, y i ^ 2
  let v := integerGaussianSecondMoment s hsp
  have hv : s ^ 2 / 16 ≤ v := integerGaussianSecondMoment_lower hs
  have hv0 : 0 ≤ v := integerGaussianSecondMoment_nonneg s hsp
  have hv2 : s ^ 4 ≤ 256 * v ^ 2 := by
    have hsq := (sq_le_sq₀ (by positivity : 0 ≤ s ^ 2 / 16) hv0).mpr hv
    nlinarith
  have hy (i : Fin n) : y i ^ 2 ≤ Q :=
    Finset.single_le_sum (fun j _ => sq_nonneg (y j)) (Finset.mem_univ i)
  have h := productGaussianMoment_fourth_le y s hsp hy
  change productGaussianMoment y s hsp 4 ≤ 3 * (v * Q) ^ 2 + 2 * s ^ 4 * Q * Q at h
  have hm := mul_le_mul_of_nonneg_right hv2 (sq_nonneg Q)
  change productGaussianMoment y s hsp 4 ≤ 515 * (v * Q) ^ 2
  nlinarith

theorem pmf_square_escape_of_uniform_fourth_moment {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (p : PMF α) (f : α → ℝ) {V : ℝ} (hV : 0 < V)
    (hs₂ : Summable (fun x => (p x).toReal * f x ^ 2))
    (hs₄ : Summable (fun x => (p x).toReal * f x ^ 4))
    (hsecond : (∑' x, (p x).toReal * f x ^ 2) = V)
    (hfourth : (∑' x, (p x).toReal * f x ^ 4) ≤ 515 * V ^ 2) :
    (1 / 2060 : ℝ) ≤ p.toMeasure.real {x | V / 2 < f x ^ 2} := by
  have h := pmf_paley_zygmund p (fun x => f x ^ 2) (fun _ => sq_nonneg _)
    hs₂ (by simpa only [← pow_mul] using hs₄) (a := V / 2) (by positivity)
    (by rw [hsecond]; linarith)
  simp only [← pow_mul, hsecond] at h
  have hp := measureReal_nonneg (μ := p.toMeasure) (s := {x | V / 2 < f x ^ 2})
  have hm := mul_le_mul_of_nonneg_right hfourth hp
  have hVs : 0 < V ^ 2 := sq_pos_of_pos hV
  nlinarith

theorem productGaussian_square_escape_uniform {n : ℕ} (y : Fin n → ℝ) {s : ℝ} (hs : 1 ≤ s)
    (hQ : 0 < ∑ i, y i ^ 2) :
    (1 / 2060 : ℝ) ≤ (productIntegerGaussian n s (by linarith)).toMeasure.real
      {z | (integerGaussianSecondMoment s (by linarith) * ∑ i, y i ^ 2) / 2 <
        integerLinearForm y z ^ 2} := by
  have hsp : 0 < s := by linarith
  apply pmf_square_escape_of_uniform_fourth_moment (productIntegerGaussian n s hsp) (integerLinearForm y)
  · exact mul_pos ((by positivity : 0 < s ^ 2 / 16).trans_le (integerGaussianSecondMoment_lower hs)) hQ
  · exact summable_productGaussian_moment y s hsp 2
  · exact summable_productGaussian_moment y s hsp 4
  · exact productGaussianMoment_second y s hsp
  · exact productGaussianMoment_fourth_le_uniform y hs

theorem productGaussian_scaled_square_escape {n : ℕ} (y : Fin n → ℝ) {s : ℝ} (hs : 1 ≤ s)
    (hQ : 0 < ∑ i, y i ^ 2) :
    (1 / 2060 : ℝ) ≤ (productIntegerGaussian n s (by linarith)).toMeasure.real
      {z | s ^ 2 * (∑ i, y i ^ 2) / 32 < integerLinearForm y z ^ 2} := by
  apply (productGaussian_square_escape_uniform y hs hQ).trans
  refine measureReal_mono ?_ (by finiteness)
  intro z hz
  have hv := mul_le_mul_of_nonneg_right (integerGaussianSecondMoment_lower hs) hQ.le
  change (integerGaussianSecondMoment s (by linarith) * ∑ i, y i ^ 2) / 2 < integerLinearForm y z ^ 2 at hz
  change s ^ 2 * (∑ i, y i ^ 2) / 32 < integerLinearForm y z ^ 2
  nlinarith

end GeometricGaussianLHL
end

end UniformGaussianEscape

section Displacement

/-!
## A short integer displacement

The integer-displacement lemma's vector is constructed by signed coordinate rounding. A large
coordinate supplies a unit vector; otherwise a subset of unit increments crosses the required
inner-product threshold with controlled overshoot.
-/

noncomputable section

open scoped BigOperators

namespace GeometricGaussianLHL

theorem integer_displacement_small_coordinates {R : ℕ} (y : Euclidean R)
    (hy : y ≠ 0) {a : ℝ} (ha : 0 < a) (hsmall : ∀ i, |y i| < a) :
    ∃ v : Coeff R, a ≤ inner ℝ y (integerEmbedding R v) ∧
      inner ℝ y (integerEmbedding R v) < 2 * a ∧
      ‖integerEmbedding R v‖ ≤ a / ‖y‖ + Real.sqrt R := by
  classical
  let c : ℝ := a / ‖y‖ ^ 2
  let w : Fin R → ℝ := fun i => |y i|
  let n : Fin R → ℤ := fun i => ⌊c * w i⌋
  let base : ℝ := ∑ i, w i * (n i : ℝ)
  have hnorm : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have hc : 0 < c := div_pos ha (sq_pos_of_pos hnorm)
  have htotal : (∑ i, w i * (c * w i)) = a := by
    calc
      _ = c * ∑ i, (y i) ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        dsimp [w]
        nlinarith [sq_abs (y i)]
      _ = c * ‖y‖ ^ 2 := by rw [EuclideanSpace.real_norm_sq_eq]
      _ = a := div_mul_cancel₀ a (ne_of_gt (sq_pos_of_pos hnorm))
  have hbase : base ≤ a := by
    rw [← htotal]
    exact Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (Int.floor_le (c * w i)) (abs_nonneg (y i))
  have hdeficit : a - base ≤ ∑ i, w i := by
    have hlower : (∑ i, w i * (c * w i - 1)) ≤ base := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg (y i))
      have hf := Int.lt_floor_add_one (c * w i)
      change c * w i - 1 ≤ (⌊c * w i⌋ : ℝ)
      linarith
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib, htotal] at hlower
    linarith
  obtain ⟨t, _, htlo, hthi⟩ := exists_subset_sum_crossing Finset.univ w ha
    (sub_nonneg.mpr hbase) (fun i _ => hsmall i) hdeficit
  let v : Coeff R := fun i => orientedInteger (y i) (n i + if i ∈ t then 1 else 0)
  have hdot : inner ℝ y (integerEmbedding R v) = base + ∑ i ∈ t, w i := by
    calc
      _ = ∑ i, w i * ((n i : ℝ) + if i ∈ t then 1 else 0) := by
        simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, integerEmbedding_apply]
        apply Finset.sum_congr rfl
        intro i _
        change (v i : ℝ) * y i = _
        rw [mul_comm]
        dsimp only [v]
        rw [mul_orientedInteger]
        dsimp only [w]
        simp only [Int.cast_add]
        split_ifs <;> simp
      _ = base + ∑ i ∈ t, w i := by
        simp [mul_add, Finset.sum_add_distrib, base]
  have herr : ‖integerEmbedding R v - c • y‖ ≤ Real.sqrt R := by
    apply integer_rounding_norm_error
    intro i
    simpa only [v, n, w, Bool.ite_eq_true_distrib, decide_eq_true_eq] using
      oriented_floor_error_le_one (y i) c (decide (i ∈ t))
  refine ⟨v, ?_, ?_, ?_⟩
  · rw [hdot]
    linarith
  · rw [hdot]
    linarith
  · have hcnorm : c * ‖y‖ = a / ‖y‖ := by
      dsimp [c]
      field_simp
    calc
      ‖integerEmbedding R v‖ = ‖(integerEmbedding R v - c • y) + c • y‖ := by
        rw [sub_add_cancel]
      _ ≤ ‖integerEmbedding R v - c • y‖ + ‖c • y‖ := norm_add_le _ _
      _ ≤ Real.sqrt R + c * ‖y‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc]
        linarith
      _ = a / ‖y‖ + Real.sqrt R := by rw [hcnorm, add_comm]

theorem exists_signed_integer_basis {R : ℕ} (y : Euclidean R) (i : Fin R) :
    ∃ v : Coeff R, inner ℝ y (integerEmbedding R v) = |y i| ∧
      ‖integerEmbedding R v‖ = 1 := by
  let v : Coeff R := Pi.basisFun ℤ (Fin R) i
  have hv : integerEmbedding R v = EuclideanSpace.basisFun (Fin R) ℝ i :=
    integerEmbedding_basis R i
  have hnorm : ‖integerEmbedding R v‖ = 1 := by
    rw [hv]
    exact (EuclideanSpace.basisFun (Fin R) ℝ).norm_eq_one i
  have hinner : inner ℝ y (integerEmbedding R v) = y i := by
    rw [hv, EuclideanSpace.inner_basisFun_real]
  by_cases hi : y i < 0
  · refine ⟨-v, ?_, ?_⟩
    · rw [map_neg, inner_neg_right, hinner, abs_of_neg hi]
    · simpa only [map_neg, norm_neg] using hnorm
  · exact ⟨v, hinner.trans (abs_of_nonneg (le_of_not_gt hi)).symm, hnorm⟩

/-- The displacement vector and both bounds from the integer-displacement lemma. -/
theorem exists_integer_displacement {R : ℕ} {τ : ℝ} (hτ : 0 < τ) (hτsmall : τ ≤ 1 / 8)
    (y : Euclidean R) (hy : y ≠ 0) (hcube : y ∈ centeredUnitCube R) :
    ∃ v : Coeff R, 2 * τ ≤ inner ℝ y (integerEmbedding R v) ∧
      inner ℝ y (integerEmbedding R v) ≤ 1 - 2 * τ ∧
      ‖integerEmbedding R v‖ ≤ 2 * τ / ‖y‖ + Real.sqrt R := by
  classical
  by_cases hlarge : ∃ i, 2 * τ ≤ |y i|
  · obtain ⟨i, hi⟩ := hlarge
    obtain ⟨v, hv, hnorm⟩ := exists_signed_integer_basis y i
    have hR : (1 : ℝ) ≤ R := by
      have hiR := i.isLt
      exact_mod_cast (show 1 ≤ R by omega)
    have hsqrt : (1 : ℝ) ≤ Real.sqrt R := by
      simpa using Real.sqrt_le_sqrt hR
    have hnonneg : 0 ≤ 2 * τ / ‖y‖ := by positivity
    refine ⟨v, by rwa [hv], ?_, ?_⟩
    · rw [hv]
      have hiupper := hcube i
      change |y i| ≤ 1 / 2 at hiupper
      linarith
    · rw [hnorm]
      linarith
  · push Not at hlarge
    obtain ⟨v, hvlo, hvhi, hvnorm⟩ := integer_displacement_small_coordinates y hy
      (show 0 < 2 * τ by positivity) hlarge
    exact ⟨v, hvlo, by linarith, hvnorm⟩

end GeometricGaussianLHL
end

end Displacement

section ComplexGaussianEscape

/-!
## Uniform escape of complex Gaussian linear forms

One of the real and imaginary coefficient energies is at least half the
complex energy. Applying the real fourth-moment escape bound to that part
avoids a nondegenerate two-dimensional covariance assumption. This also
covers purely real coefficients, including the degree-one field case.
-/

noncomputable section

open MeasureTheory

namespace GeometricGaussianLHL

def integerComplexLinearForm {n : ℕ} (a : Fin n → ℂ) (z : Coeff n) : ℂ :=
  ∑ i, a i * (z i : ℂ)

theorem integerComplexLinearForm_re {n : ℕ} (a : Fin n → ℂ) (z : Coeff n) :
    (integerComplexLinearForm a z).re = integerLinearForm (fun i => (a i).re) z := by
  simp [integerComplexLinearForm, integerLinearForm, Complex.mul_re]

theorem integerComplexLinearForm_im {n : ℕ} (a : Fin n → ℂ) (z : Coeff n) :
    (integerComplexLinearForm a z).im = integerLinearForm (fun i => (a i).im) z := by
  simp [integerComplexLinearForm, integerLinearForm, Complex.mul_im]

theorem complex_norm_sq_parts (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

theorem complex_coefficient_energy_parts {n : ℕ} (a : Fin n → ℂ) :
    (∑ i, ‖a i‖ ^ 2) = (∑ i, (a i).re ^ 2) + ∑ i, (a i).im ^ 2 := by
  simp only [complex_norm_sq_parts, Finset.sum_add_distrib]

theorem productGaussian_complex_square_escape {n : ℕ} (a : Fin n → ℂ) {s : ℝ} (hs : 1 ≤ s)
    (hQ : 0 < ∑ i, ‖a i‖ ^ 2) :
    (1 / 2060 : ℝ) ≤ (productIntegerGaussian n s (by linarith)).toMeasure.real
      {z | s ^ 2 * (∑ i, ‖a i‖ ^ 2) / 64 < ‖integerComplexLinearForm a z‖ ^ 2} := by
  have hparts := complex_coefficient_energy_parts a
  by_cases hre : (∑ i, ‖a i‖ ^ 2) / 2 ≤ ∑ i, (a i).re ^ 2
  · have hqr : 0 < ∑ i, (a i).re ^ 2 := by linarith
    apply (productGaussian_scaled_square_escape (fun i => (a i).re) hs hqr).trans
    refine measureReal_mono ?_ (by finiteness)
    intro z hz
    change s ^ 2 * (∑ i, (a i).re ^ 2) / 32 < integerLinearForm (fun i => (a i).re) z ^ 2 at hz
    change s ^ 2 * (∑ i, ‖a i‖ ^ 2) / 64 < ‖integerComplexLinearForm a z‖ ^ 2
    rw [complex_norm_sq_parts, integerComplexLinearForm_re, integerComplexLinearForm_im]
    have h := mul_le_mul_of_nonneg_left hre (sq_nonneg s)
    nlinarith [sq_nonneg (integerLinearForm (fun i => (a i).im) z)]
  · have him : (∑ i, ‖a i‖ ^ 2) / 2 ≤ ∑ i, (a i).im ^ 2 := by linarith
    have hqi : 0 < ∑ i, (a i).im ^ 2 := by linarith
    apply (productGaussian_scaled_square_escape (fun i => (a i).im) hs hqi).trans
    refine measureReal_mono ?_ (by finiteness)
    intro z hz
    change s ^ 2 * (∑ i, (a i).im ^ 2) / 32 < integerLinearForm (fun i => (a i).im) z ^ 2 at hz
    change s ^ 2 * (∑ i, ‖a i‖ ^ 2) / 64 < ‖integerComplexLinearForm a z‖ ^ 2
    rw [complex_norm_sq_parts, integerComplexLinearForm_re, integerComplexLinearForm_im]
    have h := mul_le_mul_of_nonneg_left him (sq_nonneg s)
    nlinarith [sq_nonneg (integerLinearForm (fun i => (a i).re) z)]

end GeometricGaussianLHL
end

end ComplexGaussianEscape

section IntegerSlabs

/-!
## Disjoint translates of integer slabs

The slab is defined using the actual distance from a real scalar to the embedded integers. The
displacement in the integer-displacement lemma separates a slab from its translate, including the
non-strict endpoint bounds on the displacement.
-/

noncomputable section

namespace GeometricGaussianLHL

def integerDistance (u : ℝ) : ℝ := Metric.infDist u (Set.range (Int.cast : ℤ → ℝ))

theorem integerDistance_lt_iff (u τ : ℝ) :
    integerDistance u < τ ↔ ∃ k : ℤ, |u - (k : ℝ)| < τ := by
  rw [integerDistance, Metric.infDist_lt_iff (Set.range_nonempty _)]
  simp only [Set.mem_range, exists_exists_eq_and, Real.dist_eq]

theorem le_abs_sub_integer_of_interval {a b : ℝ} (hlo : b ≤ a) (hhi : a ≤ 1 - b)
    (k : ℤ) : b ≤ |a - (k : ℝ)| := by
  by_cases hk : k ≤ 0
  · have hk' : (k : ℝ) ≤ 0 := by exact_mod_cast hk
    linarith [le_abs_self (a - (k : ℝ))]
  · have hk' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show 1 ≤ k by omega)
    linarith [neg_le_abs (a - (k : ℝ))]

def integerSlab {R : ℕ} (y : Euclidean R) (τ : ℝ) : Set (Coeff R) :=
  {x | integerDistance (inner ℝ y (integerEmbedding R x)) < τ}

theorem integerSlab_disjoint_translate {R : ℕ} (y : Euclidean R) (τ : ℝ) (v : Coeff R)
    (hlo : 2 * τ ≤ inner ℝ y (integerEmbedding R v))
    (hhi : inner ℝ y (integerEmbedding R v) ≤ 1 - 2 * τ) :
    Disjoint (integerSlab y τ) ((fun x => x + v) '' integerSlab y τ) := by
  apply Set.disjoint_left.mpr
  rintro z hz ⟨x, hx, rfl⟩
  obtain ⟨k, hk⟩ := (integerDistance_lt_iff _ _).mp hz
  obtain ⟨l, hl⟩ := (integerDistance_lt_iff _ _).mp hx
  have hlow := le_abs_sub_integer_of_interval hlo hhi (k - l)
  have htriangle : |inner ℝ y (integerEmbedding R v) - ((k - l : ℤ) : ℝ)| ≤
      |inner ℝ y (integerEmbedding R (x + v)) - (k : ℝ)| +
      |inner ℝ y (integerEmbedding R x) - (l : ℝ)| := by
    have heq : inner ℝ y (integerEmbedding R v) - ((k - l : ℤ) : ℝ) =
        (inner ℝ y (integerEmbedding R (x + v)) - (k : ℝ)) -
          (inner ℝ y (integerEmbedding R x) - (l : ℝ)) := by
      rw [map_add, inner_add_right, Int.cast_sub]
      ring
    rw [heq]
    exact abs_sub _ _
  linarith

/-- The integer-displacement lemma, including the disjointness assertion for the actual integer
slab. -/
theorem integer_displacement_and_disjoint_slabs {R : ℕ} {τ : ℝ}
    (hτ : 0 < τ) (hτsmall : τ ≤ 1 / 8) (y : Euclidean R) (hy : y ≠ 0)
    (hcube : y ∈ centeredUnitCube R) :
    ∃ v : Coeff R, (2 * τ ≤ inner ℝ y (integerEmbedding R v) ∧
      inner ℝ y (integerEmbedding R v) ≤ 1 - 2 * τ) ∧
      ‖integerEmbedding R v‖ ≤ 2 * τ / ‖y‖ + Real.sqrt R ∧
      Disjoint (integerSlab y τ) ((fun x => x + v) '' integerSlab y τ) := by
  obtain ⟨v, hlo, hhi, hnorm⟩ := exists_integer_displacement hτ hτsmall y hy hcube
  exact ⟨v, ⟨hlo, hhi⟩, hnorm, integerSlab_disjoint_translate y τ v hlo hhi⟩

end GeometricGaussianLHL
end

end IntegerSlabs

section PeriodicGaussianTail

/-!
## Periodic Gaussian bounds away from the integers

Uniform geometric bounds on the two integer tails prove the origin and off-integer estimates used in
the one-column expectation lemma. Integer translation reduces an arbitrary real argument to the
centered unit interval.
-/

noncomputable section

namespace GeometricGaussianLHL

theorem gaussian_centered_positive_tail {a u r : ℝ} (ha : 2 ≤ a)
    (_hr : 0 ≤ r) (hrhalf : r ≤ 1 / 2) (hu : |u| ≤ r) (n : ℕ) :
    Real.exp (-a * (((n : ℝ) + 1) - u) ^ 2) ≤
      Real.exp (-a * (1 - r) ^ 2) * (1 / 4 : ℝ) ^ n := by
  have hn : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    exact_mod_cast (show n ≤ n ^ 2 by simpa only [pow_two] using Nat.le_mul_self n)
  have hsq : ((n : ℝ) + 1 - r) ^ 2 ≤ ((n : ℝ) + 1 - u) ^ 2 := by
    have hule := (abs_le.mp hu).2
    nlinarith [mul_nonneg (show 0 ≤ r - u by linarith)
      (show 0 ≤ 2 * (n : ℝ) + 2 - r - u by linarith [show (0 : ℝ) ≤ n by positivity])]
  have hpoly : (1 - r) ^ 2 + 2 * n ≤ ((n : ℝ) + 1 - u) ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ (n : ℝ) by positivity) (show 0 ≤ 1 - 2 * r by linarith)]
  have hratio : Real.exp (-(2 * a)) ≤ 1 / 4 := by
    have he : 4 ≤ Real.exp (2 * a) := by linarith [Real.add_one_le_exp (2 * a)]
    rw [Real.exp_neg]
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4) he
  calc
    _ ≤ Real.exp (-a * (1 - r) ^ 2) * Real.exp (-(2 * a)) ^ n := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left hpoly (show 0 ≤ a by linarith)]
    _ ≤ _ := by gcongr

theorem shifted_integer_gaussian_centered_bound {a u r : ℝ} (ha : 2 ≤ a)
    (hr : 0 ≤ r) (hrhalf : r ≤ 1 / 2) (hu : |u| ≤ r) :
    (∑' k : ℤ, Real.exp (-a * ((k : ℝ) - u) ^ 2)) ≤
      Real.exp (-a * u ^ 2) + (8 / 3) * Real.exp (-a * (1 - r) ^ 2) := by
  let f : ℤ → ℝ := fun k => Real.exp (-a * ((k : ℝ) - u) ^ 2)
  let C : ℝ := Real.exp (-a * (1 - r) ^ 2)
  have hf : Summable f := summable_shifted_integer_gaussian (by linarith) u
  have hnat : Summable (fun n : ℕ => f n) := hf.comp_injective Nat.cast_injective
  have hpos : Summable (fun n : ℕ => f ((n : ℤ) + 1)) :=
    hf.comp_injective (fun _ _ h => by omega)
  have hneg : Summable (fun n : ℕ => f (-((n : ℤ) + 1))) :=
    hf.comp_injective (fun _ _ h => by omega)
  have hgeom := (hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (by norm_num : (1 / 4 : ℝ) < 1)).summable.mul_left C
  have hsum : (∑' n : ℕ, C * (1 / 4 : ℝ) ^ n) = C * (4 / 3) := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
      (by norm_num : (1 / 4 : ℝ) < 1)]
    norm_num
  have hp : (∑' n : ℕ, f ((n : ℤ) + 1)) ≤ C * (4 / 3) := by
    rw [← hsum]
    apply hpos.tsum_le_tsum _ hgeom
    intro n
    simpa only [f, C, Int.cast_add, Int.cast_natCast, Int.cast_one] using
      gaussian_centered_positive_tail ha hr hrhalf hu n
  have hn : (∑' n : ℕ, f (-((n : ℤ) + 1))) ≤ C * (4 / 3) := by
    rw [← hsum]
    apply hneg.tsum_le_tsum _ hgeom
    intro n
    have hb := gaussian_centered_positive_tail ha hr hrhalf (u := -u) (by simpa using hu) n
    simpa only [f, C, Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one,
      show (-((n : ℝ) + 1) - u) ^ 2 = ((n : ℝ) + 1 - -u) ^ 2 by ring] using hb
  have heq := tsum_of_nat_of_neg_add_one hnat hneg
  rw [hnat.tsum_eq_zero_add] at heq
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero] at heq
  change (∑' k, f k) ≤ _
  rw [heq]
  have hf0 : f 0 = Real.exp (-a * u ^ 2) := by simp [f]
  rw [hf0]
  dsimp [C] at hp hn
  linarith

theorem periodicGaussian_origin_bound {t : ℝ} (ht : 1 ≤ t) :
    periodicGaussian t 0 ≤ 1 + 3 * Real.exp (-Real.pi * t ^ 2) := by
  have ha : 2 ≤ Real.pi * t ^ 2 := by
    nlinarith [Real.two_le_pi, mul_le_mul_of_nonneg_left (show 1 ≤ t ^ 2 by nlinarith)
      Real.pi_pos.le]
  have hb := shifted_integer_gaussian_centered_bound (u := 0) (r := 0) ha
    (by norm_num) (by norm_num) (by norm_num)
  have hb' : periodicGaussian t 0 ≤ 1 + (8 / 3) * Real.exp (-Real.pi * t ^ 2) := by
    simpa [periodicGaussian, neg_mul] using hb
  linarith [Real.exp_pos (-Real.pi * t ^ 2)]

theorem periodicGaussian_centered_off_bound {t u : ℝ} (ht : 8 ≤ t)
    (hu : |u| ≤ 1 / 2) (haway : 1 / t ≤ |u|) :
    periodicGaussian t u ≤ Real.exp (-Real.pi) + (8 / 3) * Real.exp (-Real.pi * t ^ 2 / 4) := by
  have htpos : 0 < t := by linarith
  have ha : 2 ≤ Real.pi * t ^ 2 := by
    nlinarith [Real.two_le_pi, mul_le_mul_of_nonneg_left (show 1 ≤ t ^ 2 by nlinarith)
      Real.pi_pos.le]
  have hb := shifted_integer_gaussian_centered_bound ha (r := 1 / 2)
    (by norm_num) le_rfl hu
  have hprod : 1 ≤ t * |u| := by simpa [mul_comm] using (div_le_iff₀ htpos).mp haway
  have hsquare : 1 ≤ t ^ 2 * u ^ 2 := by nlinarith [sq_abs u, sq_nonneg (t * |u| - 1)]
  have hmain : Real.exp (-(Real.pi * t ^ 2) * u ^ 2) ≤ Real.exp (-Real.pi) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hsquare Real.pi_pos.le]
  have htail : -(Real.pi * t ^ 2) * (1 - (1 / 2 : ℝ)) ^ 2 = -Real.pi * t ^ 2 / 4 := by ring
  rw [htail] at hb
  simpa only [periodicGaussian, neg_mul] using hb.trans (add_le_add hmain le_rfl)

theorem exp_neg_pi_le_one_sixteen : Real.exp (-Real.pi) ≤ 1 / 16 := by
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 3) 5
  norm_num [Finset.sum_range_succ] at he
  have hep := Real.exp_le_exp.mpr Real.pi_gt_three.le
  have hlower : 16 ≤ Real.exp Real.pi := by linarith
  rw [Real.exp_neg]
  simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 16) hlower

theorem gaussian_centered_tail_small {t : ℝ} (ht : 8 ≤ t) :
    Real.exp (-Real.pi * t ^ 2 / 4) ≤ 1 / 128 := by
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 16) 3
  norm_num [Finset.sum_range_succ] at he
  have hx : 16 ≤ Real.pi * t ^ 2 / 4 := by
    nlinarith [Real.two_le_pi, mul_le_mul_of_nonneg_left (show 64 ≤ t ^ 2 by nlinarith)
      Real.pi_pos.le]
  have hep := Real.exp_le_exp.mpr hx
  have hlower : 128 ≤ Real.exp (Real.pi * t ^ 2 / 4) := by linarith
  rw [show -Real.pi * t ^ 2 / 4 = -(Real.pi * t ^ 2 / 4) by ring, Real.exp_neg]
  simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 128) hlower

/-- The off-integer estimate in the one-column expectation lemma, with a strict margin. -/
theorem periodicGaussian_off_integer {t u : ℝ} (ht : 8 ≤ t)
    (haway : 1 / t ≤ integerDistance u) : periodicGaussian t u < 1 / 8 := by
  let k : ℤ := round u
  let v : ℝ := u - (k : ℝ)
  have hv : |v| ≤ 1 / 2 := abs_sub_round u
  have hd : integerDistance u ≤ |v| := by
    exact (Metric.infDist_le_dist_of_mem (show (k : ℝ) ∈ Set.range (Int.cast : ℤ → ℝ)
      from ⟨k, rfl⟩)).trans_eq (Real.dist_eq _ _)
  have heq : periodicGaussian t u = periodicGaussian t v := by
    have he := periodicGaussian_add_int t v k
    simpa only [v, sub_add_cancel] using he
  rw [heq]
  have hb := periodicGaussian_centered_off_bound ht hv (haway.trans hd)
  have hmain := exp_neg_pi_le_one_sixteen
  have htail := gaussian_centered_tail_small ht
  linarith

theorem gaussian_origin_exponent_small {x : ℝ} (hx : 64 ≤ x) :
    3 * x * Real.exp (-Real.pi * x) ≤ 1 / 10 := by
  have hx0 : 0 ≤ x := by linarith
  have he := Real.sum_le_exp_of_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hx0) 3
  norm_num [Finset.sum_range_succ] at he
  have harg : 2 * x ≤ Real.pi * x := mul_le_mul_of_nonneg_right Real.two_le_pi hx0
  have hemono := Real.exp_le_exp.mpr harg
  have hlower : 30 * x ≤ Real.exp (Real.pi * x) := by
    nlinarith [mul_nonneg hx0 (show 0 ≤ x - 64 by linarith)]
  rw [show -Real.pi * x = -(Real.pi * x) by ring, Real.exp_neg, ← div_eq_mul_inv]
  apply (div_le_iff₀ (Real.exp_pos _)).mpr
  linarith

/-- The uniform factor inflation bound used in the one-column expectation lemma. -/
theorem periodicGaussian_origin_pow_bound {t : ℝ} (ht : 8 ≤ t) (d : ℕ)
    (hd : (d : ℝ) ≤ t ^ 2) : periodicGaussian t 0 ^ d < 28 / 25 := by
  have htpos : 0 < t := by linarith
  have hbase : periodicGaussian t 0 ≤ Real.exp (3 * Real.exp (-Real.pi * t ^ 2)) := by
    have hb := periodicGaussian_origin_bound (show 1 ≤ t by linarith)
    linarith [Real.add_one_le_exp (3 * Real.exp (-Real.pi * t ^ 2))]
  have hp : periodicGaussian t 0 ^ d ≤ Real.exp (3 * Real.exp (-Real.pi * t ^ 2)) ^ d := by
    gcongr
    exact (periodicGaussian_pos htpos 0).le
  rw [← Real.exp_nat_mul] at hp
  have harg : (d : ℝ) * (3 * Real.exp (-Real.pi * t ^ 2)) ≤ 1 / 10 := by
    have hsmall := gaussian_origin_exponent_small (show 64 ≤ t ^ 2 by nlinarith)
    have hmono := mul_le_mul_of_nonneg_right hd
      (show 0 ≤ 3 * Real.exp (-Real.pi * t ^ 2) by positivity)
    nlinarith
  have he := Real.exp_le_exp.mpr harg
  have hnum := Real.exp_bound_div_one_sub_of_interval (by norm_num : (0 : ℝ) ≤ 1 / 10)
    (by norm_num : (1 / 10 : ℝ) < 1)
  norm_num at hnum
  linarith

end GeometricGaussianLHL
end

end PeriodicGaussianTail

section GaussianShift

/-!
## Integer shifts of ellipsoidal Gaussians

The log density ratio is affine in the sampled integer vector. Absolute integrability and zero mean
give relative entropy exactly `π ‖S⁻¹ v‖²` in both directions. The symmetric entropy inequality then
proves the total-variation estimate in the first part of the elementary Gaussian estimates lemma.
-/

noncomputable section

namespace GeometricGaussianLHL

variable {R : ℕ}

theorem ellipsoidalGaussian_log_mass (S : Euclidean R ≃L[ℝ] Euclidean R)
    (c : Euclidean R) (z : Coeff R) :
    Real.log (ellipsoidalGaussian S c z).toReal =
      -Real.pi * ‖S.symm (integerEmbedding R z - c)‖ ^ 2 - Real.log (ellipsoidPartition S c) := by
  rw [ellipsoidalGaussian_toReal,
    Real.log_div (ellipsoidWeight_pos S c z).ne' (ellipsoidPartition_pos S c).ne']
  simp only [ellipsoidWeight, gaussianWeight, one_pow, mul_one, Real.log_exp]

theorem ellipsoidalGaussian_shift_log_ratio (S : Euclidean R ≃L[ℝ] Euclidean R)
    (v z : Coeff R) :
    Real.log ((ellipsoidalGaussian S 0 z).toReal /
      (ellipsoidalGaussian S (integerEmbedding R v) z).toReal) =
      Real.pi * ‖S.symm (integerEmbedding R v)‖ ^ 2 - 2 * Real.pi *
        inner ℝ (S.symm.toContinuousLinearMap.adjoint (S.symm (integerEmbedding R v)))
          (integerEmbedding R z) := by
  have hP : ellipsoidPartition S (integerEmbedding R v) = ellipsoidPartition S 0 := by
    simpa only [zero_add] using ellipsoidPartition_add_integer S 0 v
  have hin := S.symm.toContinuousLinearMap.adjoint_inner_left
    (integerEmbedding R z) (S.symm (integerEmbedding R v))
  rw [Real.log_div (ellipsoidalGaussian_toReal_pos S 0 z).ne'
    (ellipsoidalGaussian_toReal_pos S _ z).ne',
    ellipsoidalGaussian_log_mass, ellipsoidalGaussian_log_mass, hP]
  simp only [sub_zero, map_sub, norm_sub_sq_real, ContinuousLinearEquiv.coe_coe] at hin ⊢
  rw [hin, real_inner_comm (S.symm (integerEmbedding R v))]
  ring

theorem summable_ellipsoidalGaussian_shift_entropy
    (S : Euclidean R ≃L[ℝ] Euclidean R) (v : Coeff R) :
    Summable (fun z : Coeff R => (ellipsoidalGaussian S 0 z).toReal *
      Real.log ((ellipsoidalGaussian S 0 z).toReal /
        (ellipsoidalGaussian S (integerEmbedding R v) z).toReal)) := by
  let h := S.symm.toContinuousLinearMap.adjoint (S.symm (integerEmbedding R v))
  apply (((pmf_summable_toReal (ellipsoidalGaussian S 0)).mul_right
    (Real.pi * ‖S.symm (integerEmbedding R v)‖ ^ 2)).sub
      ((summable_ellipsoidalGaussian_linear S h).mul_left (2 * Real.pi))).congr
  intro z
  rw [ellipsoidalGaussian_shift_log_ratio]
  dsimp [h]
  ring

theorem ellipsoidalGaussian_shift_entropy (S : Euclidean R ≃L[ℝ] Euclidean R)
    (v : Coeff R) :
    (∑' z : Coeff R, (ellipsoidalGaussian S 0 z).toReal *
      Real.log ((ellipsoidalGaussian S 0 z).toReal /
        (ellipsoidalGaussian S (integerEmbedding R v) z).toReal)) =
      Real.pi * ‖S.symm (integerEmbedding R v)‖ ^ 2 := by
  let h := S.symm.toContinuousLinearMap.adjoint (S.symm (integerEmbedding R v))
  have he : (fun z : Coeff R => (ellipsoidalGaussian S 0 z).toReal *
      Real.log ((ellipsoidalGaussian S 0 z).toReal /
        (ellipsoidalGaussian S (integerEmbedding R v) z).toReal)) =
      fun z => (ellipsoidalGaussian S 0 z).toReal *
        (Real.pi * ‖S.symm (integerEmbedding R v)‖ ^ 2) -
          2 * Real.pi * ((ellipsoidalGaussian S 0 z).toReal * inner ℝ h (integerEmbedding R z)) := by
    funext z
    rw [ellipsoidalGaussian_shift_log_ratio]
    dsimp [h]
    ring
  rw [he, Summable.tsum_sub
    ((pmf_summable_toReal _).mul_right _)
    ((summable_ellipsoidalGaussian_linear S h).mul_left _),
    tsum_mul_right, tsum_mul_left, pmf_tsum_toReal, ellipsoidalGaussian_linear_mean_zero]
  ring

theorem ellipsoidalGaussian_shift_swap (S : Euclidean R ≃L[ℝ] Euclidean R)
    (v z : Coeff R) :
    (ellipsoidalGaussian S (integerEmbedding R v) (z + v)).toReal *
      Real.log ((ellipsoidalGaussian S (integerEmbedding R v) (z + v)).toReal /
        (ellipsoidalGaussian S 0 (z + v)).toReal) =
    (ellipsoidalGaussian S 0 z).toReal * Real.log ((ellipsoidalGaussian S 0 z).toReal /
      (ellipsoidalGaussian S (integerEmbedding R (-v)) z).toReal) := by
  have h₁ : ellipsoidalGaussian S (integerEmbedding R v) (z + v) =
      ellipsoidalGaussian S 0 z := by
    simpa only [zero_add] using ellipsoidalGaussian_add_center S 0 z v
  have h₂ : ellipsoidalGaussian S 0 (z + v) =
      ellipsoidalGaussian S (integerEmbedding R (-v)) z := by
    simpa only [zero_add, add_neg_cancel_right] using
      (ellipsoidalGaussian_add_center S 0 (z + v) (-v)).symm
  rw [h₁, h₂]

theorem summable_ellipsoidalGaussian_reverse_shift_entropy
    (S : Euclidean R ≃L[ℝ] Euclidean R) (v : Coeff R) :
    Summable (fun z : Coeff R => (ellipsoidalGaussian S (integerEmbedding R v) z).toReal *
      Real.log ((ellipsoidalGaussian S (integerEmbedding R v) z).toReal /
        (ellipsoidalGaussian S 0 z).toReal)) := by
  apply (Equiv.addRight v).summable_iff.mp
  change Summable (fun z => (ellipsoidalGaussian S (integerEmbedding R v) (z + v)).toReal *
    Real.log ((ellipsoidalGaussian S (integerEmbedding R v) (z + v)).toReal /
      (ellipsoidalGaussian S 0 (z + v)).toReal))
  simpa only [ellipsoidalGaussian_shift_swap]
    using summable_ellipsoidalGaussian_shift_entropy S (-v)

theorem ellipsoidalGaussian_reverse_shift_entropy (S : Euclidean R ≃L[ℝ] Euclidean R)
    (v : Coeff R) :
    (∑' z : Coeff R, (ellipsoidalGaussian S (integerEmbedding R v) z).toReal *
      Real.log ((ellipsoidalGaussian S (integerEmbedding R v) z).toReal /
        (ellipsoidalGaussian S 0 z).toReal)) =
      Real.pi * ‖S.symm (integerEmbedding R v)‖ ^ 2 := by
  rw [← (Equiv.addRight v).tsum_eq]
  change (∑' z, (ellipsoidalGaussian S (integerEmbedding R v) (z + v)).toReal *
    Real.log ((ellipsoidalGaussian S (integerEmbedding R v) (z + v)).toReal /
      (ellipsoidalGaussian S 0 (z + v)).toReal)) = _
  simp only [ellipsoidalGaussian_shift_swap]
  rw [ellipsoidalGaussian_shift_entropy]
  simp only [map_neg, norm_neg]

theorem ellipsoidalGaussian_shift_variation (S : Euclidean R ≃L[ℝ] Euclidean R)
    (v : Coeff R) :
    discreteTotalVariation (ellipsoidalGaussian S 0)
      (ellipsoidalGaussian S (integerEmbedding R v)) ≤
        Real.sqrt (Real.pi / 2) * ‖S.symm (integerEmbedding R v)‖ := by
  let p := ellipsoidalGaussian S 0
  let q := ellipsoidalGaussian S (integerEmbedding R v)
  have he : (fun z => ((p z).toReal - (q z).toReal) *
      Real.log ((p z).toReal / (q z).toReal)) =
      fun z => (p z).toReal * Real.log ((p z).toReal / (q z).toReal) +
        (q z).toReal * Real.log ((q z).toReal / (p z).toReal) := by
    funext z
    rw [Real.log_div (ellipsoidalGaussian_toReal_pos S 0 z).ne'
      (ellipsoidalGaussian_toReal_pos S _ z).ne',
      Real.log_div (ellipsoidalGaussian_toReal_pos S _ z).ne'
      (ellipsoidalGaussian_toReal_pos S 0 z).ne']
    ring
  have hsum := (summable_ellipsoidalGaussian_shift_entropy S v).add
    (summable_ellipsoidalGaussian_reverse_shift_entropy S v)
  have hJ : Summable (fun z => ((p z).toReal - (q z).toReal) *
      Real.log ((p z).toReal / (q z).toReal)) := by rw [he]; exact hsum
  have hb := discreteTotalVariation_le_sqrt_symmetricEntropy p q
    (ellipsoidalGaussian_toReal_pos S 0) (ellipsoidalGaussian_toReal_pos S _) hJ
  rw [he, Summable.tsum_add (summable_ellipsoidalGaussian_shift_entropy S v)
    (summable_ellipsoidalGaussian_reverse_shift_entropy S v),
    ellipsoidalGaussian_shift_entropy, ellipsoidalGaussian_reverse_shift_entropy] at hb
  have hs : Real.sqrt (Real.pi * ‖S.symm (integerEmbedding R v)‖ ^ 2 +
      Real.pi * ‖S.symm (integerEmbedding R v)‖ ^ 2) / 2 =
      Real.sqrt (Real.pi / 2) * ‖S.symm (integerEmbedding R v)‖ := by
    apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
    rw [div_pow, Real.sq_sqrt (by positivity), mul_pow, Real.sq_sqrt (by positivity)]
    ring
  exact hb.trans_eq hs

/-- Identifies the law with the actual pushforward by integer translation. -/
theorem ellipsoidalGaussian_map_add (S : Euclidean R ≃L[ℝ] Euclidean R)
    (v : Coeff R) :
    (ellipsoidalGaussian S 0).map (fun z => z + v) =
      ellipsoidalGaussian S (integerEmbedding R v) := by
  ext z
  obtain ⟨x, rfl⟩ := (Equiv.addRight v).surjective z
  change ((ellipsoidalGaussian S 0).map (fun z => z + v)) (x + v) = _
  rw [PMF.map_apply]
  simp only [add_left_inj, tsum_ite_eq']
  change ellipsoidalGaussian S 0 x = ellipsoidalGaussian S (integerEmbedding R v) (x + v)
  simpa only [zero_add] using (ellipsoidalGaussian_add_center S 0 x v).symm

/-- The elementary Gaussian estimates lemma, first estimate: the TV distance between `x` and `x + v`
. -/
theorem ellipsoidalGaussian_translate_variation (S : Euclidean R ≃L[ℝ] Euclidean R)
    (v : Coeff R) :
    discreteTotalVariation (ellipsoidalGaussian S 0)
      ((ellipsoidalGaussian S 0).map (fun z => z + v)) ≤
        Real.sqrt (Real.pi / 2) * ‖S.symm (integerEmbedding R v)‖ := by
  rw [ellipsoidalGaussian_map_add]
  exact ellipsoidalGaussian_shift_variation S v

end GeometricGaussianLHL
end

end GaussianShift

section GaussianSubspace

/-!
## Gaussian subspace anti-concentration

A proper real subspace has a transverse signed coordinate vector. Its mass is at most the difference
on a half-space between a distribution and its translate by that vector. The Gaussian translation
bound proves the fourth estimate in the elementary Gaussian estimates lemma, even without the
paper's lower-width restriction.
-/

noncomputable section

open MeasureTheory

namespace GeometricGaussianLHL

variable {R : ℕ}

theorem exists_unit_integer_transverse (V : Submodule ℝ (Euclidean R)) (hV : V ≠ ⊤) :
    ∃ (v : Coeff R) (h : Euclidean R), ‖integerEmbedding R v‖ = 1 ∧
      (∀ x ∈ V, inner ℝ h x = 0) ∧ 0 < inner ℝ h (integerEmbedding R v) := by
  have ho : Vᗮ ≠ ⊥ := fun hz => hV (Submodule.orthogonal_eq_bot_iff.mp hz)
  obtain ⟨h, hh, hn⟩ := Submodule.exists_mem_ne_zero_of_ne_bot ho
  have hi : ∃ i : Fin R, h i ≠ 0 := by
    by_contra! hi
    apply hn
    ext i
    exact hi i
  obtain ⟨i, hi⟩ := hi
  let v : Coeff R := Pi.basisFun ℤ (Fin R) i
  have hv : integerEmbedding R v = EuclideanSpace.basisFun (Fin R) ℝ i :=
    integerEmbedding_basis R i
  have hvnorm : ‖integerEmbedding R v‖ = 1 := by
    rw [hv]
    exact (EuclideanSpace.basisFun (Fin R) ℝ).norm_eq_one i
  have hvinner : inner ℝ h (integerEmbedding R v) = h i := by
    rw [hv, EuclideanSpace.inner_basisFun_real]
  have hvanish : ∀ x ∈ V, inner ℝ h x = 0 := (V.mem_orthogonal' h).mp hh
  rcases lt_or_gt_of_ne hi with hi | hi
  · refine ⟨-v, h, ?_, hvanish, ?_⟩
    · simpa only [map_neg, norm_neg] using hvnorm
    · rw [map_neg, inner_neg_right, hvinner]
      exact neg_pos.mpr hi
  · exact ⟨v, h, hvnorm, hvanish, hvinner.symm ▸ hi⟩

theorem pmf_hyperplane_le_translate_variation (p : PMF (Coeff R))
    (h : Euclidean R) (v : Coeff R) (hv : 0 < inner ℝ h (integerEmbedding R v)) :
    p.toMeasure.real {z : Coeff R | inner ℝ h (integerEmbedding R z) = 0} ≤
      discreteTotalVariation p (p.map (fun z => z + v)) := by
  let ℓ : Coeff R → ℝ := fun z => inner ℝ h (integerEmbedding R z)
  let A : Set (Coeff R) := {z | ℓ z = 0}
  let B : Set (Coeff R) := {z | ℓ z ≤ -ℓ v}
  let H : Set (Coeff R) := {z | ℓ z ≤ 0}
  have hd : Disjoint A B := by
    apply Set.disjoint_left.mpr
    intro z hzA hzB
    change ℓ z = 0 at hzA
    change ℓ z ≤ -ℓ v at hzB
    change 0 < ℓ v at hv
    linarith
  have hs : A ∪ B ⊆ H := by
    intro z hz
    rcases hz with hz | hz
    · exact le_of_eq hz
    · change ℓ z ≤ -ℓ v at hz
      change ℓ z ≤ 0
      change 0 < ℓ v at hv
      linarith
  have hm := measureReal_mono (μ := p.toMeasure) hs
  rw [measureReal_union hd (Set.to_countable B).measurableSet] at hm
  have he : (fun z : Coeff R => z + v) ⁻¹' H = B := by
    ext z
    change inner ℝ h (integerEmbedding R (z + v)) ≤ 0 ↔
      inner ℝ h (integerEmbedding R z) ≤ -inner ℝ h (integerEmbedding R v)
    rw [map_add, inner_add_right]
    constructor <;> intro hz <;> linarith
  have hq := pmf_map_measureReal p (fun z => z + v) H
  rw [he] at hq
  have ht := pmf_event_sub_le_totalVariation p (p.map (fun z => z + v)) H
  rw [hq] at ht
  change p.toMeasure.real A ≤ _
  linarith

theorem ellipsoidalGaussian_subspace_operator_bound
    (S : Euclidean R ≃L[ℝ] Euclidean R) (V : Submodule ℝ (Euclidean R)) (hV : V ≠ ⊤) :
    (ellipsoidalGaussian S 0).toMeasure.real {z : Coeff R | integerEmbedding R z ∈ V} ≤
      Real.sqrt (Real.pi / 2) * ‖S.symm.toContinuousLinearMap‖ := by
  obtain ⟨v, h, hvnorm, hvanish, hpositive⟩ := exists_unit_integer_transverse V hV
  have hsubset : {z : Coeff R | integerEmbedding R z ∈ V} ⊆
      {z : Coeff R | inner ℝ h (integerEmbedding R z) = 0} := fun z hz => hvanish _ hz
  have hn := S.symm.toContinuousLinearMap.le_opNorm (integerEmbedding R v)
  rw [hvnorm, mul_one] at hn
  calc
    _ ≤ (ellipsoidalGaussian S 0).toMeasure.real
        {z : Coeff R | inner ℝ h (integerEmbedding R z) = 0} := measureReal_mono hsubset
    _ ≤ discreteTotalVariation (ellipsoidalGaussian S 0)
        ((ellipsoidalGaussian S 0).map (fun z => z + v)) :=
      pmf_hyperplane_le_translate_variation _ h v hpositive
    _ ≤ Real.sqrt (Real.pi / 2) * ‖S.symm (integerEmbedding R v)‖ :=
      ellipsoidalGaussian_translate_variation S v
    _ ≤ _ := mul_le_mul_of_nonneg_left hn (Real.sqrt_nonneg _)

/-- The elementary Gaussian estimates lemma, fourth estimate. The proof only needs a positive lower
width. -/
theorem ellipsoidalGaussian_subspace_bound
    (S : Euclidean R ≃L[ℝ] Euclidean R) {s₀ : ℝ} (hs₀ : 0 < s₀)
    (hS : ‖S.symm.toContinuousLinearMap‖ ≤ 1 / s₀)
    (V : Submodule ℝ (Euclidean R)) (hV : V ≠ ⊤) :
    (ellipsoidalGaussian S 0).toMeasure {z : Coeff R | integerEmbedding R z ∈ V} ≤
      ENNReal.ofReal (2 / s₀) := by
  apply (ENNReal.le_ofReal_iff_toReal_le (by finiteness) (by positivity)).mpr
  change (ellipsoidalGaussian S 0).toMeasure.real {z : Coeff R | integerEmbedding R z ∈ V} ≤ _
  have hc : Real.sqrt (Real.pi / 2) ≤ 2 := by
    nlinarith [Real.sq_sqrt (show 0 ≤ Real.pi / 2 by positivity), Real.sqrt_nonneg (Real.pi / 2),
      Real.pi_le_four]
  calc
    _ ≤ Real.sqrt (Real.pi / 2) * ‖S.symm.toContinuousLinearMap‖ :=
      ellipsoidalGaussian_subspace_operator_bound S V hV
    _ ≤ Real.sqrt (Real.pi / 2) * (1 / s₀) := mul_le_mul_of_nonneg_left hS (Real.sqrt_nonneg _)
    _ ≤ 2 * (1 / s₀) := mul_le_mul_of_nonneg_right hc (one_div_pos.mpr hs₀).le
    _ = 2 / s₀ := by ring

end GeometricGaussianLHL
end

end GaussianSubspace

section SlabProbability

/-!
## Gaussian escape from integer slabs

The disjoint translate constructed in the integer-displacement lemma and the actual Gaussian
translation estimate imply the quarter-probability saving used in the one-column expectation lemma.
-/

noncomputable section

open MeasureTheory

namespace GeometricGaussianLHL

theorem discreteTotalVariation_symm {α : Type*} (p q : PMF α) :
    discreteTotalVariation p q = discreteTotalVariation q p := by
  simp only [discreteTotalVariation, abs_sub_comm]

theorem pmf_compl_of_disjoint_image {α : Type*} [Countable α]
    [MeasurableSpace α] [MeasurableSingletonClass α] (p : PMF α) (A : Set α)
    (f : α → α) (hf : Function.Injective f) (hd : Disjoint A (f '' A)) :
    (1 - discreteTotalVariation p (p.map f)) / 2 ≤ p.toMeasure.real Aᶜ := by
  have hq : (p.map f).toMeasure.real (f '' A) = p.toMeasure.real A := by
    rw [pmf_map_measureReal, Set.preimage_image_eq _ hf]
  have htv := pmf_event_sub_le_totalVariation (p.map f) p (f '' A)
  rw [hq, discreteTotalVariation_symm (p.map f) p] at htv
  have hunion := measureReal_mono (μ := p.toMeasure) (Set.subset_univ (A ∪ f '' A))
  rw [measureReal_union hd (Set.to_countable _).measurableSet, probReal_univ] at hunion
  rw [measureReal_compl (Set.to_countable A).measurableSet, probReal_univ]
  linarith

theorem ellipsoidalGaussian_escape_slab_of_displacement {R : ℕ}
    (S : Euclidean R ≃L[ℝ] Euclidean R) {s₀ : ℝ} (hs₀ : 0 < s₀)
    (hlower : ‖S.symm.toContinuousLinearMap‖ ≤ 1 / s₀)
    (y : Euclidean R) (τ : ℝ) (v : Coeff R)
    (hlo : 2 * τ ≤ inner ℝ y (integerEmbedding R v))
    (hhi : inner ℝ y (integerEmbedding R v) ≤ 1 - 2 * τ)
    (hnorm : ‖integerEmbedding R v‖ ≤ s₀ / 4) :
    (1 / 4 : ℝ) ≤ (ellipsoidalGaussian S 0).toMeasure.real (integerSlab y τ)ᶜ := by
  have hinv : ‖S.symm (integerEmbedding R v)‖ ≤ 1 / 4 := by
    calc
      _ ≤ ‖S.symm.toContinuousLinearMap‖ * ‖integerEmbedding R v‖ :=
        S.symm.toContinuousLinearMap.le_opNorm _
      _ ≤ (1 / s₀) * (s₀ / 4) :=
        mul_le_mul hlower hnorm (norm_nonneg _) (by positivity)
      _ = 1 / 4 := by field_simp
  have hsqrt : Real.sqrt (Real.pi / 2) ≤ 2 := by
    nlinarith [Real.sq_sqrt (show 0 ≤ Real.pi / 2 by positivity),
      Real.sqrt_nonneg (Real.pi / 2), Real.pi_le_four]
  have htv : discreteTotalVariation (ellipsoidalGaussian S 0)
      ((ellipsoidalGaussian S 0).map (fun z => z + v)) ≤ 1 / 2 := by
    calc
      _ ≤ Real.sqrt (Real.pi / 2) * ‖S.symm (integerEmbedding R v)‖ :=
        ellipsoidalGaussian_translate_variation S v
      _ ≤ 2 * (1 / 4) := mul_le_mul hsqrt hinv (norm_nonneg _) (by norm_num)
      _ = 1 / 2 := by norm_num
  have hescape := pmf_compl_of_disjoint_image (ellipsoidalGaussian S 0) (integerSlab y τ)
    (fun x => x + v) (add_left_injective v) (integerSlab_disjoint_translate y τ v hlo hhi)
  linarith

/-- The quarter-probability saving, with the geometric width budget explicit.
-/
theorem ellipsoidalGaussian_escape_slab {R : ℕ}
    (S : Euclidean R ≃L[ℝ] Euclidean R) {s₀ τ : ℝ} (hs₀ : 0 < s₀)
    (hlower : ‖S.symm.toContinuousLinearMap‖ ≤ 1 / s₀)
    (hτ : 0 < τ) (hτsmall : τ ≤ 1 / 8) (y : Euclidean R) (hy : y ≠ 0)
    (hcube : y ∈ centeredUnitCube R) (hbudget : 2 * τ / ‖y‖ + Real.sqrt R ≤ s₀ / 4) :
    (1 / 4 : ℝ) ≤ (ellipsoidalGaussian S 0).toMeasure.real (integerSlab y τ)ᶜ := by
  obtain ⟨v, hlo, hhi, hnorm⟩ := exists_integer_displacement hτ hτsmall y hy hcube
  exact ellipsoidalGaussian_escape_slab_of_displacement S hs₀ hlower y τ v hlo hhi
    (hnorm.trans hbudget)

end GeometricGaussianLHL
end

end SlabProbability

section ColumnExpectation

/-!
## A witness coordinate bounds the whole column expectation

Only one factor must escape an integer slab. The other factors may depend
arbitrarily on the same sample: no within-column independence is assumed.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace GeometricGaussianLHL

theorem pmf_weighted_summable_of_bounded {α : Type*} (p : PMF α) (f : α → ℝ)
    {C : ℝ} (hf0 : ∀ x, 0 ≤ f x) (hfC : ∀ x, f x ≤ C) :
    Summable (fun x => (p x).toReal * f x) := by
  apply ((pmf_summable_toReal p).mul_right C).of_norm_bounded
  intro x
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ENNReal.toReal_nonneg (hf0 x))]
  exact mul_le_mul_of_nonneg_left (hfC x) ENNReal.toReal_nonneg

theorem pmf_expectation_bound_of_event {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (p : PMF α) (f : α → ℝ) (A : Set α)
    {C a : ℝ} (hf0 : ∀ x, 0 ≤ f x) (hfC : ∀ x, f x ≤ C)
    (hsmall : ∀ x ∈ A, f x ≤ a * C) :
    (∑' x, (p x).toReal * f x) ≤ C * (1 - (1 - a) * p.toMeasure.real A) := by
  classical
  have hp := pmf_summable_toReal p
  have hA := hp.indicator A
  have hs := pmf_weighted_summable_of_bounded p f hf0 hfC
  have hbound : (∑' x, (p x).toReal * f x) ≤
      ∑' x, C * ((p x).toReal - (1 - a) * A.indicator (fun x => (p x).toReal) x) := by
    apply hs.tsum_le_tsum _ ((hp.sub (hA.mul_left (1 - a))).mul_left C)
    intro x
    by_cases hx : x ∈ A
    · rw [Set.indicator_of_mem hx]
      have hh := mul_le_mul_of_nonneg_left (hsmall x hx) (ENNReal.toReal_nonneg (a := p x))
      nlinarith
    · rw [Set.indicator_of_notMem hx]
      have hh := mul_le_mul_of_nonneg_left (hfC x) (ENNReal.toReal_nonneg (a := p x))
      nlinarith
  rw [tsum_mul_left, Summable.tsum_sub hp (hA.mul_left (1 - a)), tsum_mul_left,
    pmf_tsum_toReal, ← pmf_measureReal_eq_tsum] at hbound
  exact hbound

theorem periodicGaussian_zero_ge_one {t : ℝ} (ht : 0 < t) : 1 ≤ periodicGaussian t 0 := by
  have h := (periodicGaussian_summable ht 0).le_tsum (0 : ℤ)
    (fun _ _ => (Real.exp_pos _).le)
  simpa [periodicGaussian] using h

theorem product_bound_with_witness {d : ℕ} (f : Fin d → ℝ) (i : Fin d) {a b : ℝ}
    (hf0 : ∀ k, 0 ≤ f k) (hfb : ∀ k, f k ≤ b) (hfi : f i ≤ a * b) (hab : 0 ≤ a * b) :
    (∏ k, f k) ≤ a * b ^ d := by
  classical
  let s : Finset (Fin d) := Finset.univ.erase i
  have hprod : (∏ k ∈ s, f k) ≤ ∏ _k ∈ s, b :=
    Finset.prod_le_prod (fun k _ => hf0 k) (fun k _ => hfb k)
  calc
    _ = f i * ∏ k ∈ s, f k := (Finset.mul_prod_erase Finset.univ f (Finset.mem_univ i)).symm
    _ ≤ (a * b) * ∏ _k ∈ s, b := mul_le_mul hfi hprod (Finset.prod_nonneg (fun k _ => hf0 k)) hab
    _ = a * (b * ∏ _k ∈ s, b) := by ring
    _ = a * ∏ _k : Fin d, b := by
      rw [show b * ∏ _k ∈ s, b = ∏ _k : Fin d, b from
        Finset.mul_prod_erase Finset.univ (fun _ : Fin d => b) (Finset.mem_univ i)]
    _ = a * b ^ d := by simp

theorem periodicGaussian_column_expectation {R d : ℕ} (p : PMF (Coeff R))
    (g : Fin d → Coeff R → ℝ) (i : Fin d) (y : Euclidean R) {t : ℝ}
    (ht : 8 ≤ t) (hd : (d : ℝ) ≤ t ^ 2)
    (hwitness : ∀ x, g i x = inner ℝ y (integerEmbedding R x))
    (hescape : (1 / 4 : ℝ) ≤ p.toMeasure.real (integerSlab y (1 / t))ᶜ) :
    (∑' x : Coeff R, (p x).toReal * ∏ k : Fin d, periodicGaussian t (g k x)) ≤ 7 / 8 := by
  classical
  let f : Coeff R → ℝ := fun x => ∏ k, periodicGaussian t (g k x)
  let C : ℝ := periodicGaussian t 0 ^ d
  have htpos : 0 < t := by linarith
  have hφ0 : 0 ≤ periodicGaussian t 0 := (periodicGaussian_pos htpos 0).le
  have hC : 0 ≤ C := pow_nonneg hφ0 _
  have hf0 : ∀ x, 0 ≤ f x := fun x => Finset.prod_nonneg fun k _ => (periodicGaussian_pos htpos _).le
  have hfC : ∀ x, f x ≤ C := by
    intro x
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
      Finset.prod_le_prod (s := Finset.univ) (fun k _ => (periodicGaussian_pos htpos (g k x)).le)
        (fun k _ => periodicGaussian_le_zero htpos (g k x))
  have hsmall : ∀ x ∈ (integerSlab y (1 / t))ᶜ, f x ≤ (1 / 8) * C := by
    intro x hx
    have haway : 1 / t ≤ integerDistance (g i x) := by
      rw [hwitness]
      exact le_of_not_gt hx
    have hfactor := (periodicGaussian_off_integer ht haway).le
    have hfi : periodicGaussian t (g i x) ≤ (1 / 8) * periodicGaussian t 0 := by
      linarith [periodicGaussian_zero_ge_one htpos]
    exact product_bound_with_witness (fun k => periodicGaussian t (g k x)) i
      (fun k => (periodicGaussian_pos htpos _).le)
      (fun k => periodicGaussian_le_zero htpos _) hfi (by positivity)
  have he := pmf_expectation_bound_of_event p f (integerSlab y (1 / t))ᶜ hf0 hfC hsmall
  have hprob := mul_le_mul_of_nonneg_left hescape hC
  have hCbound : C < 28 / 25 := periodicGaussian_origin_pow_bound ht d hd
  change (∑' x, (p x).toReal * f x) ≤ _
  nlinarith

theorem ellipsoidalGaussian_one_column_bound {R d : ℕ}
    (S : Euclidean R ≃L[ℝ] Euclidean R) {s₀ t : ℝ} (hs₀ : 0 < s₀)
    (hlower : ‖S.symm.toContinuousLinearMap‖ ≤ 1 / s₀)
    (g : Fin d → Coeff R → ℝ) (i : Fin d) (y : Euclidean R) (hy : y ≠ 0)
    (hcube : y ∈ centeredUnitCube R) (ht : 8 ≤ t) (hd : (d : ℝ) ≤ t ^ 2)
    (hwitness : ∀ x, g i x = inner ℝ y (integerEmbedding R x))
    (hbudget : 2 * (1 / t) / ‖y‖ + Real.sqrt R ≤ s₀ / 4) :
    (∑' x : Coeff R, (ellipsoidalGaussian S 0 x).toReal *
      ∏ k : Fin d, periodicGaussian t (g k x)) ≤ 7 / 8 := by
  have htpos : 0 < t := by linarith
  apply periodicGaussian_column_expectation _ g i y ht hd hwitness
  exact ellipsoidalGaussian_escape_slab S hs₀ hlower (one_div_pos.mpr htpos)
    (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 8) ht) y hy hcube hbudget

end GeometricGaussianLHL
end

end ColumnExpectation

section GaussianNormMoment

/-!
## Exponential moments of the Euclidean norm

Integrating the linear exponential-moment bound against a continuous
Gaussian gives the norm moment with constant `sqrt(2)^R`. Tonelli's theorem
applies to actual nonnegative PMF masses, before asserting summability of
the resulting norm moment.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace GeometricGaussianLHL

variable {R : ℕ}

theorem ellipsoidalGaussian_exp_moment_ennreal_le
    (S : Euclidean R ≃L[ℝ] Euclidean R) (h : Euclidean R) :
    (∑' z : Coeff R, ellipsoidalGaussian S 0 z *
      ENNReal.ofReal (Real.exp (inner ℝ h (integerEmbedding R z)))) ≤
        ENNReal.ofReal (Real.exp (‖S.toContinuousLinearMap.adjoint h‖ ^ 2 / (4 * Real.pi))) := by
  have hh := ENNReal.ofReal_le_ofReal (ellipsoidalGaussian_exp_moment_le S h)
  rw [ENNReal.ofReal_tsum_of_nonneg (fun z => mul_nonneg ENNReal.toReal_nonneg
    (Real.exp_pos _).le) (summable_ellipsoidalGaussian_exp S h)] at hh
  simpa only [ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal (PMF.apply_ne_top _ _)] using hh

theorem ellipsoidalGaussian_exp_moment_opNorm
    (S : Euclidean R ≃L[ℝ] Euclidean R) {b : ℝ} (hb : 0 < b)
    (hS : ‖S.toContinuousLinearMap‖ ≤ b) (h : Euclidean R) :
    (∑' z : Coeff R, ellipsoidalGaussian S 0 z *
      ENNReal.ofReal (Real.exp (inner ℝ h (integerEmbedding R z)))) ≤
        ENNReal.ofReal (Real.exp (b ^ 2 * ‖h‖ ^ 2 / (4 * Real.pi))) := by
  apply (ellipsoidalGaussian_exp_moment_ennreal_le S h).trans
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  have hn : ‖S.toContinuousLinearMap.adjoint h‖ ≤ b * ‖h‖ := by
    calc
      _ ≤ ‖S.toContinuousLinearMap.adjoint‖ * ‖h‖ :=
        S.toContinuousLinearMap.adjoint.le_opNorm h
      _ = ‖S.toContinuousLinearMap‖ * ‖h‖ := by rw [ContinuousLinearMap.adjoint.norm_map]
      _ ≤ b * ‖h‖ := mul_le_mul_of_nonneg_right hS (norm_nonneg _)
  apply div_le_div_of_nonneg_right _ (by positivity)
  simpa only [mul_pow] using (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hb.le (norm_nonneg _))).mpr hn

/-- The auxiliary-Gaussian argument for any countable probability mass function.
-/
theorem norm_exp_moment_of_linear_mgf {α : Type*} [Countable α]
    (p : PMF α) (X : α → Euclidean R) {b : ℝ} (hb : 0 < b)
    (hmgf : ∀ h : Euclidean R, (∑' z, p z * ENNReal.ofReal (Real.exp (inner ℝ h (X z)))) ≤
      ENNReal.ofReal (Real.exp (b ^ 2 * ‖h‖ ^ 2 / (4 * Real.pi)))) :
    (∑' z, p z * ENNReal.ofReal (Real.exp (Real.pi * ‖X z‖ ^ 2 / (2 * b ^ 2)))) ≤
      ENNReal.ofReal (Real.sqrt 2 ^ R) := by
  let k : ℝ := Real.pi * Real.sqrt 2 / b
  calc
    (∑' z, p z * ENNReal.ofReal (Real.exp (Real.pi * ‖X z‖ ^ 2 / (2 * b ^ 2)))) =
        ∑' z, ∫⁻ x : Euclidean R, p z * (ENNReal.ofReal (gaussianWeight 1 x) *
          ENNReal.ofReal (Real.exp (inner ℝ (k • x) (X z)))) := by
      apply tsum_congr
      intro z
      rw [lintegral_const_mul' _ _ (p.apply_ne_top z), lintegral_gaussian_auxiliary hb (X z)]
    _ = ∫⁻ x : Euclidean R, ∑' z, p z * (ENNReal.ofReal (gaussianWeight 1 x) *
        ENNReal.ofReal (Real.exp (inner ℝ (k • x) (X z)))) := by
      symm
      apply lintegral_tsum
      intro z
      apply Measurable.aemeasurable
      unfold gaussianWeight
      fun_prop
    _ = ∫⁻ x : Euclidean R, ENNReal.ofReal (gaussianWeight 1 x) *
        ∑' z, p z * ENNReal.ofReal (Real.exp (inner ℝ (k • x) (X z))) := by
      apply lintegral_congr
      intro x
      rw [← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro z
      ring
    _ ≤ ∫⁻ x : Euclidean R, ENNReal.ofReal (gaussianWeight 1 x) *
        ENNReal.ofReal (Real.exp (b ^ 2 * ‖k • x‖ ^ 2 / (4 * Real.pi))) := by
      apply lintegral_mono
      intro x
      exact mul_le_mul_right (hmgf (k • x)) _
    _ = ∫⁻ x : Euclidean R, ENNReal.ofReal (gaussianWeight (1 / Real.sqrt 2) x) := by
      apply lintegral_congr
      intro x
      rw [← ENNReal.ofReal_mul (gaussianWeight_pos _ _).le, gaussian_auxiliary_majorant hb]
    _ = ENNReal.ofReal (Real.sqrt 2 ^ R) := by
      have hi : Integrable (fun x : Euclidean R => gaussianWeight (1 / Real.sqrt 2) x) := by
        apply Integrable.of_integral_ne_zero
        rw [integral_half_gaussian]
        positivity
      rw [← ofReal_integral_eq_lintegral_ofReal hi
        (Filter.Eventually.of_forall (fun x => (gaussianWeight_pos _ _).le)), integral_half_gaussian]

theorem ellipsoidalGaussian_norm_exp_moment
    (S : Euclidean R ≃L[ℝ] Euclidean R) {b : ℝ} (hb : 0 < b)
    (hS : ‖S.toContinuousLinearMap‖ ≤ b) :
    (∑' z : Coeff R, ellipsoidalGaussian S 0 z *
      ENNReal.ofReal (Real.exp (Real.pi * ‖integerEmbedding R z‖ ^ 2 / (2 * b ^ 2)))) ≤
        ENNReal.ofReal (Real.sqrt 2 ^ R) :=
  norm_exp_moment_of_linear_mgf (ellipsoidalGaussian S 0) (integerEmbedding R) hb
    (ellipsoidalGaussian_exp_moment_opNorm S hb hS)

theorem summable_ellipsoidalGaussian_norm_exp
    (S : Euclidean R ≃L[ℝ] Euclidean R) {b : ℝ} (hb : 0 < b)
    (hS : ‖S.toContinuousLinearMap‖ ≤ b) : Summable (fun z : Coeff R =>
      (ellipsoidalGaussian S 0 z).toReal *
        Real.exp (Real.pi * ‖integerEmbedding R z‖ ^ 2 / (2 * b ^ 2))) := by
  have hh := ellipsoidalGaussian_norm_exp_moment S hb hS
  have hfin := ne_of_lt (hh.trans_lt ENNReal.ofReal_lt_top)
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le]
    using ENNReal.summable_toReal hfin

end GeometricGaussianLHL
end

end GaussianNormMoment

section ColumnParameters

/-!
## Polynomial-width parameters for the column bound

The paper's `t = 64 κ μ √H` and `U = s₁ √H`, with `s₁ = κ s₀`,
provide the displacement budget required by the expectation theorem.
The logarithmic definition of `H` is checked separately below.
-/

noncomputable section

namespace GeometricGaussianLHL

def polynomialThetaWidth (κ μ H : ℝ) : ℝ := 64 * κ * μ * Real.sqrt H

def polynomialColumnThreshold (s₀ κ H : ℝ) : ℝ := κ * s₀ * Real.sqrt H

theorem polynomialWidth_parameters {R : ℕ} (hR : 1 ≤ R)
    {s₀ κ μ H : ℝ} (hκ : 1 ≤ κ) (hμ : 1 ≤ μ) (hH : (R : ℝ) ≤ H)
    (hs₀ : 8 * Real.sqrt R ≤ s₀) :
    0 < s₀ ∧ 0 < polynomialColumnThreshold s₀ κ H ∧
      8 ≤ polynomialThetaWidth κ μ H ∧ (R : ℝ) ≤ polynomialThetaWidth κ μ H ^ 2 := by
  have hRreal : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hsqrtR : (1 : ℝ) ≤ Real.sqrt R := by simpa using Real.sqrt_le_sqrt hRreal
  have hsqrtH : (1 : ℝ) ≤ Real.sqrt H := hsqrtR.trans (Real.sqrt_le_sqrt hH)
  have hspos : 0 < s₀ := by linarith
  have hkm : 1 ≤ κ * μ := by
    nlinarith [mul_nonneg (show 0 ≤ κ - 1 by linarith) (show 0 ≤ μ - 1 by linarith)]
  have ht : 64 * Real.sqrt H ≤ polynomialThetaWidth κ μ H := by
    dsimp [polynomialThetaWidth]
    nlinarith [mul_le_mul_of_nonneg_right hkm (Real.sqrt_nonneg H)]
  have htsq : H ≤ polynomialThetaWidth κ μ H ^ 2 := by
    nlinarith [Real.sq_sqrt (show 0 ≤ H by linarith), Real.sqrt_nonneg H]
  refine ⟨hspos, ?_, by linarith, hH.trans htsq⟩
  dsimp [polynomialColumnThreshold]
  positivity

theorem polynomialWidth_displacement_budget {R : ℕ} (hR : 1 ≤ R)
    {s₀ κ μ H : ℝ} (hκ : 1 ≤ κ) (hμ : 1 ≤ μ) (hH : (R : ℝ) ≤ H)
    (hs₀ : 8 * Real.sqrt R ≤ s₀) (y : Euclidean R)
    (hfar : 1 / (4 * μ * polynomialColumnThreshold s₀ κ H) < ‖y‖) :
    y ≠ 0 ∧ 2 * (1 / polynomialThetaWidth κ μ H) / ‖y‖ + Real.sqrt R ≤ s₀ / 4 := by
  obtain ⟨hspos, hUpos, ht, _⟩ := polynomialWidth_parameters hR hκ hμ hH hs₀
  have hμpos : 0 < μ := by linarith
  have hκpos : 0 < κ := by linarith
  have hHpos : 0 < H := by
    have hRreal : (1 : ℝ) ≤ R := by exact_mod_cast hR
    linarith
  have htpos : 0 < polynomialThetaWidth κ μ H := by linarith
  have hden : 0 < 4 * μ * polynomialColumnThreshold s₀ κ H := by positivity
  have hypos : 0 < ‖y‖ := (one_div_pos.mpr hden).trans hfar
  have hinv : 1 / ‖y‖ ≤ 4 * μ * polynomialColumnThreshold s₀ κ H := by
    apply (div_le_iff₀ hypos).mpr
    have h := (div_lt_iff₀ hden).mp hfar
    linarith
  have hcalc : 2 * (1 / polynomialThetaWidth κ μ H) *
      (4 * μ * polynomialColumnThreshold s₀ κ H) = s₀ / 8 := by
    dsimp [polynomialThetaWidth, polynomialColumnThreshold]
    have hsqrtne : Real.sqrt H ≠ 0 := (Real.sqrt_pos.mpr hHpos).ne'
    field_simp
    ring
  have hshort : 2 * (1 / polynomialThetaWidth κ μ H) / ‖y‖ ≤ s₀ / 8 := by
    have hh := mul_le_mul_of_nonneg_left hinv
      (show 0 ≤ 2 * (1 / polynomialThetaWidth κ μ H) by positivity)
    rw [hcalc] at hh
    simpa only [mul_one_div] using hh
  exact ⟨norm_pos_iff.mp hypos, by linarith⟩

theorem logarithmicColumnHeight_ge_rank {R m : ℕ} (hm : 1 ≤ m) {δ : ℝ}
    (hδ : 0 < δ) (hδone : δ ≤ 1) :
    (R : ℝ) ≤ (R : ℝ) + Real.log (2 * m / δ) := by
  have hmreal : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hr : 1 ≤ 2 * m / δ := (le_div_iff₀ hδ).mpr (by linarith)
  linarith [Real.log_nonneg hr]

/-- The one-column expectation lemma's analytic bound for arbitrary column factors with one identity
witness. The width and far-region hypotheses are the paper's parameters; only the lower
singular-width bound is needed for this conclusion.
-/
theorem polynomialWidth_one_column {R d : ℕ} (hR : 1 ≤ R) (hdR : d ≤ R)
    (S : Euclidean R ≃L[ℝ] Euclidean R) {s₀ κ μ H : ℝ}
    (hκ : 1 ≤ κ) (hμ : 1 ≤ μ) (hH : (R : ℝ) ≤ H) (hs₀ : 8 * Real.sqrt R ≤ s₀)
    (hlower : ‖S.symm.toContinuousLinearMap‖ ≤ 1 / s₀)
    (g : Fin d → Coeff R → ℝ) (i : Fin d) (y : Euclidean R)
    (hcube : y ∈ centeredUnitCube R)
    (hfar : 1 / (4 * μ * polynomialColumnThreshold s₀ κ H) < ‖y‖)
    (hwitness : ∀ x, g i x = inner ℝ y (integerEmbedding R x)) :
    (∑' x : Coeff R, (ellipsoidalGaussian S 0 x).toReal *
      ∏ k : Fin d, periodicGaussian (polynomialThetaWidth κ μ H) (g k x)) ≤ 7 / 8 := by
  obtain ⟨hspos, _, ht, hRt⟩ := polynomialWidth_parameters hR hκ hμ hH hs₀
  obtain ⟨hy, hbudget⟩ := polynomialWidth_displacement_budget hR hκ hμ hH hs₀ y hfar
  have hd : (d : ℝ) ≤ polynomialThetaWidth κ μ H ^ 2 :=
    (show (d : ℝ) ≤ R by exact_mod_cast hdR).trans hRt
  exact ellipsoidalGaussian_one_column_bound S hspos hlower g i y hy hcube ht hd hwitness hbudget

def polynomialColumnHeight (R m : ℕ) (ell : ℝ) : ℝ :=
  (R : ℝ) + Real.log (2 * m / realSecurityError (ell + 4))

theorem polynomialColumnHeight_ge_rank {R m : ℕ} {ell : ℝ} (hm : 1 ≤ m) (hell : 1 ≤ ell) :
    (R : ℝ) ≤ polynomialColumnHeight R m ell := by
  have hδ : realSecurityError (ell + 4) ≤ 1 := by
    exact (real_polynomial_failureBudget_le hell).trans (by norm_num)
  exact logarithmicColumnHeight_ge_rank hm (realSecurityError_pos _) hδ

/-- The one-column estimate with the logarithmic height and the actual linear coordinate factors.
Taking `T k = Iᵣ ⊗ Tₖ` gives the coefficient form of the one-column expectation lemma; the
distinguished multiplication matrix is the identity. -/
theorem polynomialWidth_one_operator_column {R d m : ℕ} {ell : ℝ}
    (hR : 1 ≤ R) (hm : 1 ≤ m) (hell : 1 ≤ ell) (hdR : d ≤ R)
    (S : Euclidean R ≃L[ℝ] Euclidean R) {s₀ κ μ : ℝ}
    (hκ : 1 ≤ κ) (hμ : 1 ≤ μ) (hs₀ : 8 * Real.sqrt R ≤ s₀)
    (hlower : ‖S.symm.toContinuousLinearMap‖ ≤ 1 / s₀)
    (T : Fin d → Euclidean R →ₗ[ℝ] Euclidean R) (i : Fin d) (hidentity : T i = LinearMap.id)
    (y : Euclidean R) (hcube : y ∈ centeredUnitCube R)
    (hfar : 1 / (4 * μ * polynomialColumnThreshold s₀ κ (polynomialColumnHeight R m ell)) < ‖y‖) :
    (∑' x : Coeff R, (ellipsoidalGaussian S 0 x).toReal *
      ∏ k : Fin d, periodicGaussian (polynomialThetaWidth κ μ (polynomialColumnHeight R m ell))
        (inner ℝ y (T k (integerEmbedding R x)))) ≤ 7 / 8 := by
  apply polynomialWidth_one_column hR hdR S hκ hμ (polynomialColumnHeight_ge_rank hm hell)
    hs₀ hlower (fun k x => inner ℝ y (T k (integerEmbedding R x))) i y hcube hfar
  intro x
  simp [hidentity]

end GeometricGaussianLHL
end

end ColumnParameters

section IndependentColumns

/-!
## Independent discrete columns

Exact product expectations and coordinate-event probabilities for the
actual finite product PMF. Nonnegative expectations use Tonelli, so the
factorization never silently assumes convergence of a real-valued sum.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace GeometricGaussianLHL

theorem independentProduct_expectation {α : Type*} {m : ℕ} (p : Fin m → PMF α)
    (f : Fin m → α → ℝ≥0∞) :
    (∑' z : Fin m → α, independentProduct p z * ∏ i, f i (z i)) =
      ∏ i, ∑' x, p i x * f i x := by
  simp only [independentProduct_apply, ← Finset.prod_mul_distrib]
  exact tsum_finite_product m (fun i x => p i x * f i x)

theorem pmf_ennreal_expectation_eq_ofReal {α : Type*} (p : PMF α) (f : α → ℝ)
    (hf0 : ∀ x, 0 ≤ f x) (hs : Summable (fun x => (p x).toReal * f x)) :
    (∑' x, p x * ENNReal.ofReal (f x)) = ENNReal.ofReal (∑' x, (p x).toReal * f x) := by
  rw [ENNReal.ofReal_tsum_of_nonneg (fun x => mul_nonneg ENNReal.toReal_nonneg (hf0 x)) hs]
  simp only [ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal (PMF.apply_ne_top _ _)]

theorem pmf_ennreal_expectation_le_of_bounded {α : Type*} (p : PMF α) (f : α → ℝ)
    {B C : ℝ} (hf0 : ∀ x, 0 ≤ f x) (hfB : ∀ x, f x ≤ B)
    (hbound : (∑' x, (p x).toReal * f x) ≤ C) :
    (∑' x, p x * ENNReal.ofReal (f x)) ≤ ENNReal.ofReal C := by
  rw [pmf_ennreal_expectation_eq_ofReal p f hf0 (pmf_weighted_summable_of_bounded p f hf0 hfB)]
  exact ENNReal.ofReal_le_ofReal hbound

theorem independentProduct_expectation_le {α : Type*} {m : ℕ} (p : Fin m → PMF α)
    (f : Fin m → α → ℝ≥0∞) (C : Fin m → ℝ≥0∞)
    (hC : ∀ i, (∑' x, p i x * f i x) ≤ C i) :
    (∑' z : Fin m → α, independentProduct p z * ∏ i, f i (z i)) ≤ ∏ i, C i := by
  rw [independentProduct_expectation]
  exact Finset.prod_le_prod' (fun i _ => hC i)

theorem independentProduct_event_all {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] {m : ℕ} (p : Fin m → PMF α) (A : Fin m → Set α) :
    (independentProduct p).toMeasure {z | ∀ i, z i ∈ A i} = ∏ i, (p i).toMeasure (A i) := by
  classical
  rw [PMF.toMeasure_apply_eq_tsum]
  simp_rw [PMF.toMeasure_apply_eq_tsum]
  calc
    _ = ∑' z : Fin m → α, ∏ i, (A i).indicator (p i) (z i) := by
      apply tsum_congr
      intro z
      by_cases hz : ∀ i, z i ∈ A i
      · simp [Set.indicator, hz, independentProduct_apply]
      · have hz' := hz
        push Not at hz'
        obtain ⟨i, hi⟩ := hz'
        rw [Set.indicator_of_notMem (show z ∉ {z | ∀ i, z i ∈ A i} from hz)]
        symm
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        exact Set.indicator_of_notMem hi _
    _ = _ := tsum_finite_product m (fun i x => (A i).indicator (p i) x)

theorem independentProduct_coordinate_measure {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] {m : ℕ} (p : Fin m → PMF α) (i : Fin m) (A : Set α) :
    (independentProduct p).toMeasure {z | z i ∈ A} = (p i).toMeasure A := by
  classical
  let events : Fin m → Set α := fun j => if j = i then A else Set.univ
  have heq : {z : Fin m → α | z i ∈ A} = {z | ∀ j, z j ∈ events j} := by
    ext z
    simp [events]
  rw [heq, independentProduct_event_all]
  simpa [events] using (Finset.prod_eq_single i
    (f := fun j => (p j).toMeasure (events j)) (s := Finset.univ)
    (fun j _ hji => by simp [events, hji]) (by simp))

theorem independentProduct_union_bound {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] {m : ℕ} (p : Fin m → PMF α) (A : Fin m → Set α) :
    (independentProduct p).toMeasure {z | ∃ i, z i ∈ A i} ≤ ∑ i, (p i).toMeasure (A i) := by
  have heq : {z : Fin m → α | ∃ i, z i ∈ A i} = ⋃ i, {z | z i ∈ A i} := by
    ext z
    simp
  rw [heq]
  have h := measure_iUnion_le (μ := (independentProduct p).toMeasure) (fun i => {z | z i ∈ A i})
  simpa only [tsum_fintype, independentProduct_coordinate_measure] using h

end GeometricGaussianLHL
end

end IndependentColumns

section GaussianNormTail

/-!
## Gaussian norm tails as probability-measure bounds

The exponential Markov inequality is proved for actual PMF measures and then applied to the
squared-norm moment. This gives the elementary Gaussian estimates lemma's third estimate with its
exact dimension-dependent prefactor.
-/

noncomputable section

open scoped ENNReal

namespace GeometricGaussianLHL

theorem pmf_exp_tail_le {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (p : PMF α) (f : α → ℝ) (a C : ℝ)
    (hmoment : (∑' x, p x * ENNReal.ofReal (Real.exp (f x))) ≤ ENNReal.ofReal C) :
    p.toMeasure {x | a ≤ f x} ≤ ENNReal.ofReal (C * Real.exp (-a)) := by
  classical
  rw [p.toMeasure_apply_eq_tsum]
  have hb (x : α) : ({x | a ≤ f x} : Set α).indicator p x ≤
      ENNReal.ofReal (Real.exp (-a)) * (p x * ENNReal.ofReal (Real.exp (f x))) := by
    by_cases hx : a ≤ f x
    · rw [Set.indicator_of_mem (show x ∈ {x | a ≤ f x} from hx)]
      have he : (1 : ℝ) ≤ Real.exp (-a) * Real.exp (f x) := by
        rw [← Real.exp_add, Real.one_le_exp_iff]
        linarith
      have he' := ENNReal.ofReal_le_ofReal he
      rw [ENNReal.ofReal_one, ENNReal.ofReal_mul (Real.exp_pos _).le] at he'
      have hm := mul_le_mul_right he' (p x)
      simpa only [mul_one, one_mul, mul_comm, mul_left_comm, mul_assoc] using hm
    · rw [Set.indicator_of_notMem (show x ∉ {x | a ≤ f x} from hx)]
      exact zero_le
  apply (ENNReal.tsum_le_tsum hb).trans
  rw [ENNReal.tsum_mul_left]
  have hh := mul_le_mul_right hmoment (ENNReal.ofReal (Real.exp (-a)))
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, mul_comm (Real.exp (-a)) C] at hh
  exact hh

theorem sqrt_two_pow_eq_rpow (R : ℕ) :
    Real.sqrt 2 ^ R = (2 : ℝ) ^ ((R : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  ring

/-- The elementary Gaussian estimates lemma, third estimate, with any positive upper bound on the
shape norm. -/
theorem ellipsoidalGaussian_norm_tail {R : ℕ}
    (S : Euclidean R ≃L[ℝ] Euclidean R) {b u : ℝ} (hb : 0 < b) (hu : 0 < u)
    (hS : ‖S.toContinuousLinearMap‖ ≤ b) :
    (ellipsoidalGaussian S 0).toMeasure {z : Coeff R | b * u < ‖integerEmbedding R z‖} ≤
      ENNReal.ofReal ((2 : ℝ) ^ ((R : ℝ) / 2) * Real.exp (-Real.pi * u ^ 2 / 2)) := by
  have hsubset : {z : Coeff R | b * u < ‖integerEmbedding R z‖} ⊆
      {z : Coeff R | Real.pi * u ^ 2 / 2 ≤ Real.pi * ‖integerEmbedding R z‖ ^ 2 / (2 * b ^ 2)} := by
    intro z hz
    have hs := (sq_le_sq₀ (mul_pos hb hu).le (norm_nonneg (integerEmbedding R z))).mpr hz.le
    apply (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) (sq_pos_of_pos hb))).mpr
    have hh := mul_le_mul_of_nonneg_left hs Real.pi_pos.le
    nlinarith only [hh]
  apply ((ellipsoidalGaussian S 0).toMeasure.mono hsubset).trans
  change (ellipsoidalGaussian S 0).toMeasure
    {z : Coeff R | Real.pi * u ^ 2 / 2 ≤ Real.pi * ‖integerEmbedding R z‖ ^ 2 / (2 * b ^ 2)} ≤ _
  have hh := pmf_exp_tail_le (ellipsoidalGaussian S 0)
    (fun z : Coeff R => Real.pi * ‖integerEmbedding R z‖ ^ 2 / (2 * b ^ 2))
    (Real.pi * u ^ 2 / 2) (Real.sqrt 2 ^ R)
    (ellipsoidalGaussian_norm_exp_moment S hb hS)
  simpa only [sqrt_two_pow_eq_rpow, neg_div, neg_mul] using hh

end GeometricGaussianLHL
end

end GaussianNormTail

section IndependentLinearMoment

/-!
## Gaussian linear moments of independent vector columns

Tonelli factors the actual exponential sum; the coefficient energy is
then the sum of squared norms of the test vectors. This statement allows
arbitrary discrete vector laws whose linear moments have been proved.
-/

noncomputable section

open scoped ENNReal InnerProductSpace

namespace GeometricGaussianLHL

variable {E α : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {m : ℕ}

theorem independentProduct_linear_mgf (p : Fin m → PMF α) (X : α → E)
    (b : ℝ) (hmgf : ∀ j, ∀ h : E,
      (∑' z, p j z * ENNReal.ofReal (Real.exp (⟪h, X z⟫_ℝ))) ≤
        ENNReal.ofReal (Real.exp (b ^ 2 * ‖h‖ ^ 2 / (4 * Real.pi))))
    (y : Fin m → E) (θ : ℝ) :
    (∑' z : Fin m → α, independentProduct p z *
      ENNReal.ofReal (Real.exp (θ * ∑ j, ⟪y j, X (z j)⟫_ℝ))) ≤
        ENNReal.ofReal (Real.exp (b ^ 2 * θ ^ 2 * (∑ j, ‖y j‖ ^ 2) / (4 * Real.pi))) := by
  have he (z : Fin m → α) : ENNReal.ofReal (Real.exp (θ * ∑ j, ⟪y j, X (z j)⟫_ℝ)) =
      ∏ j, ENNReal.ofReal (Real.exp (⟪θ • y j, X (z j)⟫_ℝ)) := by
    rw [← ENNReal.ofReal_prod_of_nonneg (fun _ _ => (Real.exp_pos _).le), ← Real.exp_sum]
    simp only [real_inner_smul_left, Finset.mul_sum]
  simp_rw [he]
  apply (independentProduct_expectation_le p
    (fun j z => ENNReal.ofReal (Real.exp (⟪θ • y j, X z⟫_ℝ)))
    (fun j => ENNReal.ofReal (Real.exp (b ^ 2 * ‖θ • y j‖ ^ 2 / (4 * Real.pi))))
    (fun j => hmgf j (θ • y j))).trans_eq
  rw [← ENNReal.ofReal_prod_of_nonneg (fun _ _ => (Real.exp_pos _).le), ← Real.exp_sum]
  congr 2
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, ← Finset.sum_div]
  simp_rw [← mul_assoc]
  rw [← Finset.mul_sum]

theorem independentProduct_linear_mgf_unit (p : Fin m → PMF α) (X : α → E)
    (b : ℝ) (hmgf : ∀ j, ∀ h : E,
      (∑' z, p j z * ENNReal.ofReal (Real.exp (⟪h, X z⟫_ℝ))) ≤
        ENNReal.ofReal (Real.exp (b ^ 2 * ‖h‖ ^ 2 / (4 * Real.pi))))
    (y : Fin m → E) (hy : (∑ j, ‖y j‖ ^ 2) ≤ 1) (θ : ℝ) :
    (∑' z : Fin m → α, independentProduct p z *
      ENNReal.ofReal (Real.exp (θ * ∑ j, ⟪y j, X (z j)⟫_ℝ))) ≤
        ENNReal.ofReal (Real.exp (b ^ 2 * θ ^ 2 / (4 * Real.pi))) := by
  apply (independentProduct_linear_mgf p X b hmgf y θ).trans
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  apply div_le_div_of_nonneg_right _ (by positivity)
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hy (mul_nonneg (sq_nonneg b) (sq_nonneg θ))

end GeometricGaussianLHL
end

end IndependentLinearMoment

section ColumnTails

/-!
## The column-norm exceptional event

The actual independent ellipsoidal Gaussian law and the Gaussian norm tail give the first
exceptional-event bound in the finite geometric smoothing theorem. The logarithmic height leaves a
factor of two of slack in the requested failure budget.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace GeometricGaussianLHL

def ellipsoidalColumnLaw {R : ℕ} (m : ℕ) (S : Euclidean R ≃L[ℝ] Euclidean R) :
    PMF (Fin m → Coeff R) := independentProduct (fun _ => ellipsoidalGaussian S 0)

def columnNormEvent {R m : ℕ} (U : ℝ) : Set (Fin m → Coeff R) :=
  {X | ∀ j, ‖integerEmbedding R (X j)‖ ≤ U}

theorem gaussian_tail_prefactor_bound (R : ℕ) {H : ℝ} (hH : 0 ≤ H) :
    (2 : ℝ) ^ ((R : ℝ) / 2) * Real.exp (-Real.pi * H / 2) ≤ Real.exp ((R : ℝ) - H) := by
  have hpow : (2 : ℝ) ^ ((R : ℝ) / 2) ≤ Real.exp R := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    apply Real.exp_le_exp.mpr
    have hlog := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ R by positivity)
      (show 0 ≤ 1 - Real.log 2 by linarith)]
  have hexp : Real.exp (-Real.pi * H / 2) ≤ Real.exp (-H) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr Real.two_le_pi) hH]
  calc
    _ ≤ Real.exp R * Real.exp (-H) :=
      mul_le_mul hpow hexp (Real.exp_pos _).le (Real.exp_pos _).le
    _ = _ := by simp only [← Real.exp_add, sub_eq_add_neg]

theorem logarithmic_gaussian_tail_budget {R m : ℕ} (hm : 0 < m) {δ H : ℝ}
    (hδ : 0 < δ) (hH : 0 ≤ H) (hheight : H = (R : ℝ) + Real.log (2 * m / δ)) :
    (m : ℝ) * ((2 : ℝ) ^ ((R : ℝ) / 2) * Real.exp (-Real.pi * H / 2)) ≤ δ / 2 := by
  have hmreal : (0 : ℝ) < m := by exact_mod_cast hm
  have heq : Real.exp ((R : ℝ) - H) = δ / (2 * m) := by
    rw [hheight, show (R : ℝ) - ((R : ℝ) + Real.log (2 * m / δ)) =
      -Real.log (2 * m / δ) by ring, Real.exp_neg, Real.exp_log (by positivity)]
    field_simp
  have h := mul_le_mul_of_nonneg_left (gaussian_tail_prefactor_bound R hH) hmreal.le
  rw [heq] at h
  have he : (m : ℝ) * (δ / (2 * m)) = δ / 2 := by field_simp
  rwa [he] at h

theorem ellipsoidalColumnLaw_norm_tail {R m : ℕ}
    (S : Euclidean R ≃L[ℝ] Euclidean R) {s₁ H : ℝ} (hs₁ : 0 < s₁) (hH : 0 < H)
    (hS : ‖S.toContinuousLinearMap‖ ≤ s₁) :
    (ellipsoidalColumnLaw m S).toMeasure (columnNormEvent (s₁ * Real.sqrt H))ᶜ ≤
      ENNReal.ofReal ((m : ℝ) * ((2 : ℝ) ^ ((R : ℝ) / 2) * Real.exp (-Real.pi * H / 2))) := by
  classical
  have heq : (columnNormEvent (s₁ * Real.sqrt H) : Set (Fin m → Coeff R))ᶜ =
      {X | ∃ j, s₁ * Real.sqrt H < ‖integerEmbedding R (X j)‖} := by
    ext X
    simp [columnNormEvent, not_forall]
  rw [heq]
  change (independentProduct (fun _ : Fin m => ellipsoidalGaussian S 0)).toMeasure _ ≤ _
  calc
    _ ≤ ∑ _j : Fin m, (ellipsoidalGaussian S 0).toMeasure
        {x : Coeff R | s₁ * Real.sqrt H < ‖integerEmbedding R x‖} :=
      independentProduct_union_bound _ (fun _ => {x | s₁ * Real.sqrt H < ‖integerEmbedding R x‖})
    _ ≤ ∑ _j : Fin m, ENNReal.ofReal
        ((2 : ℝ) ^ ((R : ℝ) / 2) * Real.exp (-Real.pi * H / 2)) := by
      apply Finset.sum_le_sum
      intro j _
      simpa only [Real.sq_sqrt hH.le] using
        ellipsoidalGaussian_norm_tail S hs₁ (Real.sqrt_pos.mpr hH) hS
    _ = _ := by simp [ENNReal.ofReal_mul, ENNReal.ofReal_natCast]

/-- The first exceptional-event bound in the finite geometric smoothing theorem, with a stronger
`δ/2` budget. -/
theorem polynomialWidth_columnNorm_failure {R m : ℕ} {ell : ℝ} (hR : 1 ≤ R) (hm : 1 ≤ m) (hell : 1 ≤ ell)
    (S : Euclidean R ≃L[ℝ] Euclidean R) {s₁ : ℝ} (hs₁ : 0 < s₁)
    (hS : ‖S.toContinuousLinearMap‖ ≤ s₁) :
    (ellipsoidalColumnLaw m S).toMeasure
      (columnNormEvent (s₁ * Real.sqrt (polynomialColumnHeight R m ell)))ᶜ ≤
        ENNReal.ofReal (realSecurityError (ell + 4) / 2) := by
  have hH : 0 < polynomialColumnHeight R m ell := by
    have hr : (0 : ℝ) < R := by exact_mod_cast (show 0 < R by omega)
    exact hr.trans_le (polynomialColumnHeight_ge_rank hm hell)
  apply (ellipsoidalColumnLaw_norm_tail S hs₁ hH hS).trans
  apply ENNReal.ofReal_le_ofReal
  exact logarithmic_gaussian_tail_budget (by omega) (realSecurityError_pos _) hH.le rfl

end GeometricGaussianLHL
end

end ColumnTails

section ElementaryGaussian

/-!
## Elementary ellipsoidal Gaussian estimates

The widths are expressed as operator-norm bounds. Taking `s₁` to be the
largest singular value and `s₀` the smallest gives the paper's parameters.
The law, translation, exponential expectation, and event probabilities
are the actual constructions used throughout the certificate. No Gaussian
estimate is assumed. The fourth conclusion holds for every positive lower
width, strengthening the paper's restriction `s₀ ≥ 1`.
-/

noncomputable section

namespace GeometricGaussianLHL

/-- All four conclusions of the elementary Gaussian estimates lemma, for arbitrary valid width
bounds.
-/
theorem elementary_ellipsoidal_gaussian_estimates {R : ℕ}
    (S : Euclidean R ≃L[ℝ] Euclidean R) (hself : IsSelfAdjoint S.toContinuousLinearMap)
    {s₀ s₁ : ℝ} (hs₀ : 0 < s₀) (hs₁ : 0 < s₁)
    (hlower : ‖S.symm.toContinuousLinearMap‖ ≤ 1 / s₀)
    (hupper : ‖S.toContinuousLinearMap‖ ≤ s₁) :
    (∀ v : Coeff R, discreteTotalVariation (ellipsoidalGaussian S 0)
      ((ellipsoidalGaussian S 0).map (fun z => z + v)) ≤
        Real.sqrt (Real.pi / 2) * ‖S.symm (integerEmbedding R v)‖) ∧
    (∀ h : Euclidean R, (∑' z : Coeff R, (ellipsoidalGaussian S 0 z).toReal *
      Real.exp (inner ℝ h (integerEmbedding R z))) ≤ Real.exp (‖S h‖ ^ 2 / (4 * Real.pi))) ∧
    (∀ u : ℝ, 0 < u → (ellipsoidalGaussian S 0).toMeasure
      {z : Coeff R | s₁ * u < ‖integerEmbedding R z‖} ≤
        ENNReal.ofReal ((2 : ℝ) ^ ((R : ℝ) / 2) * Real.exp (-Real.pi * u ^ 2 / 2))) ∧
    (∀ V : Submodule ℝ (Euclidean R), V ≠ ⊤ → (ellipsoidalGaussian S 0).toMeasure
      {z : Coeff R | integerEmbedding R z ∈ V} ≤ ENNReal.ofReal (2 / s₀)) := by
  exact ⟨ellipsoidalGaussian_translate_variation S,
    ellipsoidalGaussian_exp_moment_le_selfAdjoint S hself,
    fun u hu => ellipsoidalGaussian_norm_tail S hs₁ hu hupper,
    fun V hV => ellipsoidalGaussian_subspace_bound S hs₀ hlower V hV⟩

end GeometricGaussianLHL
end

end ElementaryGaussian

section GaussianStandardized

/-!
## Standardized Gaussian moments and tails

Applying the inverse shape to a centred discrete Gaussian gives a uniform
linear moment bound. The auxiliary-Gaussian argument then controls its
actual squared norm, independently of the shape's condition number.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace GeometricGaussianLHL

variable {R : ℕ}

theorem ellipsoidalGaussian_standardized_mgf
    (S : Euclidean R ≃L[ℝ] Euclidean R) (h : Euclidean R) :
    (∑' z : Coeff R, ellipsoidalGaussian S 0 z *
      ENNReal.ofReal (Real.exp (inner ℝ h (S.symm (integerEmbedding R z))))) ≤
        ENNReal.ofReal (Real.exp (‖h‖ ^ 2 / (4 * Real.pi))) := by
  have hc : S.symm.toContinuousLinearMap.comp S.toContinuousLinearMap = ContinuousLinearMap.id ℝ _ := by
    apply ContinuousLinearMap.ext
    intro x
    exact S.symm_apply_apply x
  have ha := congrArg (fun T : Euclidean R →L[ℝ] Euclidean R => T.adjoint h) hc
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_id, ContinuousLinearMap.id_apply] at ha
  have hh := ellipsoidalGaussian_exp_moment_ennreal_le S (S.symm.toContinuousLinearMap.adjoint h)
  simp only [ContinuousLinearMap.adjoint_inner_left, ha] at hh
  exact hh

theorem ellipsoidalGaussian_standardized_norm_moment
    (S : Euclidean R ≃L[ℝ] Euclidean R) :
    (∑' z : Coeff R, ellipsoidalGaussian S 0 z *
      ENNReal.ofReal (Real.exp (Real.pi * ‖S.symm (integerEmbedding R z)‖ ^ 2 / 2))) ≤
        ENNReal.ofReal (Real.sqrt 2 ^ R) := by
  simpa using norm_exp_moment_of_linear_mgf (ellipsoidalGaussian S 0)
    (fun z => S.symm (integerEmbedding R z)) (by norm_num : (0 : ℝ) < 1)
    (fun h => by simpa using ellipsoidalGaussian_standardized_mgf S h)

theorem standardizedGaussian_tail_budget {n : ℕ} {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) :
    Real.sqrt 2 ^ n * Real.exp (-Real.pi * (n + Real.log (1 / ξ))) ≤ ξ := by
  have hlog : 0 ≤ Real.log (1 / ξ) := Real.log_nonneg ((le_div_iff₀ hξ).mpr (by simpa))
  have htwo : Real.log (2 : ℝ) ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have h₁ := mul_le_mul_of_nonneg_right htwo (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have h₂ := mul_le_mul_of_nonneg_right Real.two_le_pi (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have h₃ := mul_le_mul_of_nonneg_right Real.two_le_pi hlog
  rw [sqrt_two_pow_eq_rpow, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), ← Real.exp_add]
  apply (Real.exp_le_exp.mpr ?_).trans_eq (Real.exp_log hξ)
  rw [Real.log_div one_ne_zero hξ.ne', Real.log_one, zero_sub] at hlog h₃ ⊢
  nlinarith

theorem ellipsoidalGaussian_standardized_tail
    (S : Euclidean R ≃L[ℝ] Euclidean R) {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) :
    (ellipsoidalGaussian S 0).toMeasure
      {z : Coeff R | 2 * (R + Real.log (1 / ξ)) < ‖S.symm (integerEmbedding R z)‖ ^ 2} ≤
        ENNReal.ofReal ξ := by
  have hsub : {z : Coeff R | 2 * (R + Real.log (1 / ξ)) < ‖S.symm (integerEmbedding R z)‖ ^ 2} ⊆
      {z : Coeff R | Real.pi * (R + Real.log (1 / ξ)) ≤
        Real.pi * ‖S.symm (integerEmbedding R z)‖ ^ 2 / 2} := by
    intro z hz
    change 2 * (R + Real.log (1 / ξ)) < ‖S.symm (integerEmbedding R z)‖ ^ 2 at hz
    change Real.pi * (R + Real.log (1 / ξ)) ≤ Real.pi * ‖S.symm (integerEmbedding R z)‖ ^ 2 / 2
    have h := mul_le_mul_of_nonneg_left hz.le Real.pi_pos.le
    nlinarith
  apply ((ellipsoidalGaussian S 0).toMeasure.mono hsub).trans
  have h := pmf_exp_tail_le (ellipsoidalGaussian S 0)
    (fun z : Coeff R => Real.pi * ‖S.symm (integerEmbedding R z)‖ ^ 2 / 2)
    (Real.pi * (R + Real.log (1 / ξ))) (Real.sqrt 2 ^ R)
    (ellipsoidalGaussian_standardized_norm_moment S)
  apply h.trans
  exact ENNReal.ofReal_le_ofReal (by simpa only [neg_mul] using standardizedGaussian_tail_budget hξ hξ1)

end GeometricGaussianLHL
end

end GaussianStandardized

section IndependentEscapeCount

/-!
## Lower tails for the number of independent escapes

An indicator with escape probability at least `p₀` has negative exponential
moment at most `exp(-p₀/2)`. Independence and exponential Markov then bound
the probability of at most `p₀ m/4` escapes by `exp(-p₀ m/4)`.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace GeometricGaussianLHL

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] {m : ℕ}

def escapeIndicator (A : Set α) (x : α) : ℝ := A.indicator (fun _ => 1) x

theorem pmf_escape_negative_mgf (p : PMF α) (A : Set α) {p₀ : ℝ}
    (hp : p₀ ≤ p.toMeasure.real A) :
    (∑' x, p x * ENNReal.ofReal (Real.exp (-escapeIndicator A x))) ≤
      ENNReal.ofReal (Real.exp (-p₀ / 2)) := by
  classical
  have hhalf : Real.exp (-1) ≤ (1 / 2 : ℝ) := by
    rw [Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2)
      (by linarith [Real.add_one_le_exp (1 : ℝ)])
  have hi (x : α) : (p x).toReal * Real.exp (-escapeIndicator A x) =
      (p x).toReal - (1 - Real.exp (-1)) * A.indicator (fun x => (p x).toReal) x := by
    by_cases hx : x ∈ A
    · simp only [escapeIndicator, Set.indicator_of_mem hx]
      ring
    · simp only [escapeIndicator, Set.indicator_of_notMem hx, neg_zero, Real.exp_zero, mul_one, mul_zero, sub_zero]
  have hs := (pmf_summable_toReal p).sub
    (((pmf_summable_toReal p).indicator A).mul_left (1 - Real.exp (-1)))
  have hsum : (∑' x, (p x).toReal * Real.exp (-escapeIndicator A x)) =
      1 - (1 - Real.exp (-1)) * p.toMeasure.real A := by
    simp_rw [hi]
    rw [Summable.tsum_sub (pmf_summable_toReal p)
      (((pmf_summable_toReal p).indicator A).mul_left (1 - Real.exp (-1))),
      tsum_mul_left, pmf_tsum_toReal, ← pmf_measureReal_eq_tsum]
  rw [pmf_ennreal_expectation_eq_ofReal p _ (fun _ => (Real.exp_pos _).le)
    (hs.congr (fun x => (hi x).symm)), hsum]
  apply ENNReal.ofReal_le_ofReal
  have hP := measureReal_nonneg (μ := p.toMeasure) (s := A)
  have hh := mul_le_mul_of_nonneg_right hhalf hP
  have he := Real.add_one_le_exp (-p₀ / 2)
  nlinarith

def independentEscapeCount (A : Fin m → Set α) (z : Fin m → α) : ℝ :=
  ∑ j, escapeIndicator (A j) (z j)

theorem independentEscapeCount_negative_mgf (p : Fin m → PMF α) (A : Fin m → Set α)
    {p₀ : ℝ} (hp : ∀ j, p₀ ≤ (p j).toMeasure.real (A j)) :
    (∑' z, independentProduct p z * ENNReal.ofReal (Real.exp (-independentEscapeCount A z))) ≤
      ENNReal.ofReal (Real.exp (-p₀ * m / 2)) := by
  have he (z : Fin m → α) : ENNReal.ofReal (Real.exp (-independentEscapeCount A z)) =
      ∏ j, ENNReal.ofReal (Real.exp (-escapeIndicator (A j) (z j))) := by
    rw [← ENNReal.ofReal_prod_of_nonneg (fun _ _ => (Real.exp_pos _).le), ← Real.exp_sum]
    simp only [independentEscapeCount, Finset.sum_neg_distrib]
  simp_rw [he]
  apply (independentProduct_expectation_le p _
    (fun _ => ENNReal.ofReal (Real.exp (-p₀ / 2))) (fun j => pmf_escape_negative_mgf (p j) (A j) (hp j))).trans_eq
  rw [← ENNReal.ofReal_prod_of_nonneg (fun _ _ => (Real.exp_pos _).le), ← Real.exp_sum]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  congr 2
  ring

theorem independentEscapeCount_lower_tail (p : Fin m → PMF α) (A : Fin m → Set α)
    {p₀ : ℝ} (hp : ∀ j, p₀ ≤ (p j).toMeasure.real (A j)) :
    (independentProduct p).toMeasure {z | independentEscapeCount A z ≤ p₀ * m / 4} ≤
      ENNReal.ofReal (Real.exp (-p₀ * m / 4)) := by
  have h := pmf_exp_tail_le (independentProduct p) (fun z => -independentEscapeCount A z)
    (-p₀ * m / 4) (Real.exp (-p₀ * m / 2)) (independentEscapeCount_negative_mgf p A hp)
  have hset : {z | independentEscapeCount A z ≤ p₀ * m / 4} =
      {z | -p₀ * m / 4 ≤ -independentEscapeCount A z} := by
    ext z
    simp only [Set.mem_setOf_eq]
    constructor <;> intro hz <;> linarith
  rw [hset]
  apply h.trans_eq
  rw [← Real.exp_add]
  congr 2
  ring


theorem independentNonnegativeSum_lower_tail (p : Fin m → PMF α) (f : Fin m → α → ℝ)
    (hf : ∀ j x, 0 ≤ f j x) {a p₀ : ℝ} (ha : 0 < a)
    (hp : ∀ j, p₀ ≤ (p j).toMeasure.real {x | a < f j x}) :
    (independentProduct p).toMeasure {z | (∑ j, f j (z j)) ≤ a * (p₀ * m / 4)} ≤
      ENNReal.ofReal (Real.exp (-p₀ * m / 4)) := by
  classical
  let A := fun j => {x | a < f j x}
  have hbound (z : Fin m → α) : a * independentEscapeCount A z ≤ ∑ j, f j (z j) := by
    rw [independentEscapeCount, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    by_cases hx : a < f j (z j)
    · simpa only [escapeIndicator, Set.indicator_of_mem (show z j ∈ A j from hx), mul_one] using hx.le
    · simpa only [escapeIndicator, Set.indicator_of_notMem (show z j ∉ A j from hx), mul_zero] using hf j (z j)
  apply (measure_mono (show {z | (∑ j, f j (z j)) ≤ a * (p₀ * m / 4)} ⊆
    {z | independentEscapeCount A z ≤ p₀ * m / 4} from ?_)).trans
      (independentEscapeCount_lower_tail p A hp)
  intro z hz
  have hh := (hbound z).trans hz
  exact (mul_le_mul_iff_right₀ ha).mp hh

end GeometricGaussianLHL
end

end IndependentEscapeCount

section ProductGaussianTail

/-!
## Chernoff tails of actual product Gaussian linear forms

Scalar exponential moments factor by Tonelli. The resulting two-sided
tail bound applies directly to the finite product PMF, including the
small-coordinate regime needed in the constant-width argument.
-/

noncomputable section

open MeasureTheory

namespace GeometricGaussianLHL

theorem productGaussian_mgf_ennreal_le {n : ℕ} (y : Fin n → ℝ) (s : ℝ) (hs : 0 < s) (u : ℝ) :
    (∑' z : Coeff n, productIntegerGaussian n s hs z *
      ENNReal.ofReal (Real.exp (u * integerLinearForm y z))) ≤
        ENNReal.ofReal (Real.exp (s ^ 2 * u ^ 2 * (∑ i, y i ^ 2) / (4 * Real.pi))) := by
  have he (z : Coeff n) : ENNReal.ofReal (Real.exp (u * integerLinearForm y z)) =
      ∏ i, ENNReal.ofReal (Real.exp ((u * y i) * (z i : ℝ))) := by
    rw [← ENNReal.ofReal_prod_of_nonneg (fun _ _ => (Real.exp_pos _).le), ← Real.exp_sum]
    congr 2
    simp only [integerLinearForm, Finset.mul_sum, mul_assoc]
  simp_rw [he]
  rw [productIntegerGaussian, independentProduct_expectation
    (fun _ : Fin n => integerGaussian s hs)
    (fun i (a : ℤ) => ENNReal.ofReal (Real.exp ((u * y i) * (a : ℝ))))]
  have hbound (i : Fin n) : (∑' a : ℤ, integerGaussian s hs a *
      ENNReal.ofReal (Real.exp ((u * y i) * (a : ℝ)))) ≤
        ENNReal.ofReal (Real.exp (s ^ 2 * (u * y i) ^ 2 / (4 * Real.pi))) := by
    rw [pmf_ennreal_expectation_eq_ofReal _ _ (fun _ => (Real.exp_pos _).le)
      (summable_integerGaussian_mgf s hs (u * y i))]
    exact ENNReal.ofReal_le_ofReal (integerGaussian_mgf_le s hs (u * y i))
  apply (Finset.prod_le_prod' (fun i _ => hbound i)).trans_eq
  rw [← ENNReal.ofReal_prod_of_nonneg (fun _ _ => (Real.exp_pos _).le), ← Real.exp_sum]
  congr 2
  simp only [← Finset.sum_div, mul_pow, ← Finset.mul_sum]
  ring

/-- A scalar Chernoff inequality stated with the paper's Gaussian parameter
convention. The hypothesis is an actual extended-real exponential moment.
-/
theorem pmf_gaussian_right_tail {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (p : PMF α) (f : α → ℝ) {B a : ℝ}
    (hB : 0 < B) (ha : 0 < a)
    (hmgf : ∀ u : ℝ, (∑' x, p x * ENNReal.ofReal (Real.exp (u * f x))) ≤
      ENNReal.ofReal (Real.exp (B * u ^ 2 / (4 * Real.pi)))) :
    p.toMeasure {x | a < f x} ≤ ENNReal.ofReal (Real.exp (-Real.pi * a ^ 2 / B)) := by
  let u := 2 * Real.pi * a / B
  have hu : 0 < u := by dsimp [u]; positivity
  have hh := pmf_exp_tail_le p (fun x => u * f x) (u * a)
    (Real.exp (B * u ^ 2 / (4 * Real.pi))) (hmgf u)
  have hset : {x | a < f x} ⊆ {x | u * a ≤ u * f x} :=
    fun x hx => mul_le_mul_of_nonneg_left hx.le hu.le
  apply ((measure_mono hset).trans hh).trans_eq
  rw [← Real.exp_add]
  congr 2
  dsimp [u]
  field_simp
  ring

theorem pmf_gaussian_abs_tail {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (p : PMF α) (f : α → ℝ) {B a : ℝ}
    (hB : 0 < B) (ha : 0 < a)
    (hmgf : ∀ u : ℝ, (∑' x, p x * ENNReal.ofReal (Real.exp (u * f x))) ≤
      ENNReal.ofReal (Real.exp (B * u ^ 2 / (4 * Real.pi)))) :
    p.toMeasure {x | a < |f x|} ≤ ENNReal.ofReal (2 * Real.exp (-Real.pi * a ^ 2 / B)) := by
  have hn : ∀ u : ℝ, (∑' x, p x * ENNReal.ofReal (Real.exp (u * -f x))) ≤
      ENNReal.ofReal (Real.exp (B * u ^ 2 / (4 * Real.pi))) := by
    intro u
    simpa only [neg_mul, mul_neg, neg_sq] using hmgf (-u)
  have he : {x | a < |f x|} = {x | a < f x} ∪ {x | a < -f x} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_union, lt_abs]
  rw [he]
  apply (measure_union_le _ _).trans
  have h := add_le_add (pmf_gaussian_right_tail p f hB ha hmgf)
    (pmf_gaussian_right_tail p (fun x => -f x) hB ha hn)
  apply h.trans_eq
  rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]
  congr 1
  ring

theorem productGaussian_abs_tail {n : ℕ} (y : Fin n → ℝ) (s : ℝ) (hs : 0 < s)
    {B a : ℝ} (hB : 0 < B) (ha : 0 < a) (hy : s ^ 2 * (∑ i, y i ^ 2) ≤ B) :
    (productIntegerGaussian n s hs).toMeasure {z | a < |integerLinearForm y z|} ≤
      ENNReal.ofReal (2 * Real.exp (-Real.pi * a ^ 2 / B)) := by
  apply pmf_gaussian_abs_tail _ _ hB ha
  intro u
  apply (productGaussian_mgf_ennreal_le y s hs u).trans
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_right hy (sq_nonneg u)
  apply (div_le_div_of_nonneg_right _ (by positivity))
  nlinarith only [h]

theorem gaussian_small_tail_constant : 2 * Real.exp (-400 * Real.pi) < (1 / 1000 : ℝ) := by
  have h := Real.pow_div_factorial_le_exp (400 * Real.pi) (by positivity) 2
  norm_num only [Nat.factorial, Nat.cast_ofNat] at h
  have he : 2000 < Real.exp (400 * Real.pi) := by nlinarith [Real.pi_gt_three]
  rw [show -400 * Real.pi = -(400 * Real.pi) by ring, Real.exp_neg]
  apply (mul_inv_lt_iff₀ (Real.exp_pos _)).mpr
  linarith

theorem productGaussian_quarter_tail {n : ℕ} (y : Fin n → ℝ) (s : ℝ) (hs : 0 < s)
    (hy : s ^ 2 * (∑ i, y i ^ 2) ≤ 1 / 6400) :
    (productIntegerGaussian n s hs).toMeasure.real {z | (1 / 4 : ℝ) < |integerLinearForm y z|} <
      1 / 1000 := by
  have h := productGaussian_abs_tail y s hs (by norm_num : (0 : ℝ) < 1 / 6400)
    (by norm_num : (0 : ℝ) < 1 / 4) hy
  have he : -Real.pi * (1 / 4 : ℝ) ^ 2 / (1 / 6400) = -400 * Real.pi := by ring
  rw [he] at h
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  rw [ENNReal.toReal_ofReal (by positivity)] at hr
  exact hr.trans_lt gaussian_small_tail_constant

end GeometricGaussianLHL
end

end ProductGaussianTail
