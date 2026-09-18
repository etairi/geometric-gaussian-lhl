import GeometricGaussianLHL.Probability
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.Semicontinuity.Basic

/-!
# Gaussian integrals, products, and periodization

This module collects the following proof sections, in dependency order.
- Periodic Gaussian sums (`PeriodicGaussian`).
- Explicit bounds near the origin (`PeriodicGaussianBounds`).
- Exact Gaussian normalization (`GaussianNormalization`).
- Existence of smoothing parameters (`SmoothingExistence`).
- Gaussian integrals over affine fibers (`AffineGaussian`).
- The near-origin contribution (`MainTerm`).
- Smoothing at the infimum (`SmoothingClosure`).
- Integer block columns (`BlockColumns`).
- Operator norm from coefficient-column bounds (`ColumnOperatorNorm`).
- Bounding the Gram determinant by column norms (`GramDeterminantBound`).
- Expanding the periodic Gaussian product (`ThetaExpansion`).
- Ellipsoidal discrete Gaussian distributions (`EllipsoidalGaussian`).
- Unfolding the integer fundamental cell (`FundamentalCell`).
- Isotropic coefficient Gaussians are product distributions (`GaussianProducts`).
- Exponential tilting and first moments (`GaussianTilting`).
- Complex-valued unfolding on the integer fundamental cell (`ComplexPeriodization`).
- Periodized ellipsoidal Gaussian kernels (`EllipsoidPeriodization`).
- Continuous Gaussian exponential moments (`ContinuousGaussianMoment`).
- Continuity of the periodized Gaussian (`EllipsoidContinuity`).
- Gaussian convolution with exact normalization (`GaussianConvolution`).
- Periodic integration on the integer fundamental cell (`PeriodicIntegration`).
- The Gaussian partition function on the integer torus (`EllipsoidTorus`).
- Maximum of the ellipsoidal partition function (`EllipsoidMaximum`).
- Integer Fourier characters in Euclidean coordinates (`TorusCharacters`).
- Torus Fourier coefficients in Euclidean coordinates (`TorusIntegration`).
-/

section PeriodicGaussian

/-!
## Periodic Gaussian sums

The function `periodicGaussian` is the paper's `φ_t`. Convergence is proved
for every positive `t` and every real centre before using the real-valued
infinite sum. This module supplies the one-dimensional ingredients of the
theta-integral method.
-/

noncomputable section

open scoped Topology FourierTransform
open Filter Asymptotics

namespace GeometricGaussianLHL

def periodicGaussian (t u : ℝ) : ℝ :=
  ∑' k : ℤ, Real.exp (-Real.pi * t ^ 2 * ((k : ℝ) - u) ^ 2)

theorem shifted_gaussian_le (a u x : ℝ) (ha : 0 ≤ a) :
    Real.exp (-a * (x - u) ^ 2) ≤
      Real.exp (a * u ^ 2) * Real.exp (-(a / 2) * x ^ 2) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_nonneg ha (sq_nonneg (x - 2 * u))]

theorem summable_shifted_integer_gaussian {a : ℝ} (ha : 0 < a) (u : ℝ) :
    Summable (fun k : ℤ => Real.exp (-a * ((k : ℝ) - u) ^ 2)) := by
  apply ((summable_integer_gaussian (half_pos ha)).mul_left (Real.exp (a * u ^ 2))).of_norm_bounded
  intro k
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact shifted_gaussian_le a u k ha.le

theorem periodicGaussian_summable {t : ℝ} (ht : 0 < t) (u : ℝ) :
    Summable (fun k : ℤ => Real.exp (-Real.pi * t ^ 2 * ((k : ℝ) - u) ^ 2)) := by
  simpa only [neg_mul] using
    summable_shifted_integer_gaussian (mul_pos Real.pi_pos (sq_pos_of_pos ht)) u

theorem periodicGaussian_pos {t : ℝ} (ht : 0 < t) (u : ℝ) : 0 < periodicGaussian t u := by
  exact (Real.exp_pos (-Real.pi * t ^ 2 * ((0 : ℤ) - u) ^ 2)).trans_le
    ((periodicGaussian_summable ht u).le_tsum 0 (fun _ _ => (Real.exp_pos _).le))

theorem periodicGaussian_add_int (t u : ℝ) (n : ℤ) :
    periodicGaussian t (u + n) = periodicGaussian t u := by
  unfold periodicGaussian
  rw [← (Equiv.addRight n).tsum_eq
    (fun k : ℤ => Real.exp (-Real.pi * t ^ 2 * ((k : ℝ) - (u + n)) ^ 2))]
  apply tsum_congr
  intro k
  change Real.exp (-Real.pi * t ^ 2 * (((k + n : ℤ) : ℝ) - (u + n)) ^ 2) = _
  push_cast
  congr 1
  ring

theorem periodicGaussian_periodic (t : ℝ) : Function.Periodic (periodicGaussian t) 1 := by
  intro u
  simpa only [Int.cast_one] using periodicGaussian_add_int t u 1

theorem periodicGaussian_even (t u : ℝ) : periodicGaussian t (-u) = periodicGaussian t u := by
  unfold periodicGaussian
  rw [← (Equiv.neg ℤ).tsum_eq
    (fun k : ℤ => Real.exp (-Real.pi * t ^ 2 * ((k : ℝ) - -u) ^ 2))]
  apply tsum_congr
  intro k
  change Real.exp (-Real.pi * t ^ 2 * (((-k : ℤ) : ℝ) - -u) ^ 2) = _
  push_cast
  congr 1
  ring

def gaussianFourierCoefficient (t : ℝ) (k : ℤ) : ℝ :=
  (1 / t) * Real.exp (-(Real.pi / t ^ 2) * (k : ℝ) ^ 2)

theorem gaussianFourierCoefficient_pos {t : ℝ} (ht : 0 < t) (k : ℤ) :
    0 < gaussianFourierCoefficient t k := mul_pos (one_div_pos.mpr ht) (Real.exp_pos _)

theorem summable_gaussianFourierCoefficient {t : ℝ} (ht : 0 < t) :
    Summable (gaussianFourierCoefficient t) :=
  (summable_integer_gaussian (div_pos Real.pi_pos (sq_pos_of_pos ht))).mul_left _

theorem fourier_gaussian_smoothing {t : ℝ} (ht : 0 < t) :
    (𝓕 (fun x : ℝ => (Real.exp (-Real.pi * t ^ 2 * x ^ 2) : ℂ))) =
      fun y : ℝ => (((1 / t) * Real.exp (-(Real.pi / t ^ 2) * y ^ 2) : ℝ) : ℂ) := by
  have hsqrt : ((t : ℂ) ^ 2) ^ (1 / 2 : ℂ) = (t : ℂ) := by
    calc
      ((t : ℂ) ^ 2) ^ (1 / 2 : ℂ) = (((t ^ 2) ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
        simpa only [Complex.ofReal_pow, Complex.ofReal_div, Complex.ofReal_one,
          Complex.ofReal_ofNat] using (Complex.ofReal_cpow (sq_nonneg t) (1 / 2 : ℝ)).symm
      _ = (t : ℂ) := by rw [← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs, abs_of_pos ht]
  have hf : (fun x : ℝ => (Real.exp (-Real.pi * t ^ 2 * x ^ 2) : ℂ)) =
      fun x : ℝ => Complex.exp (-(Real.pi : ℂ) * (t : ℂ) ^ 2 * (x : ℂ) ^ 2) := by
    funext x
    push_cast
    rfl
  rw [hf, fourier_gaussian_pi (by
    rw [← Complex.ofReal_pow, Complex.ofReal_re]
    exact sq_pos_of_pos ht : 0 < ((t : ℂ) ^ 2).re)]
  funext y
  rw [hsqrt]
  push_cast
  simp only [neg_div]

theorem norm_gaussianFourierTerm {t : ℝ} (ht : 0 < t) (u : ℝ) (k : ℤ) :
    ‖(gaussianFourierCoefficient t k : ℂ) * fourier k (u : UnitAddCircle)‖ =
      gaussianFourierCoefficient t k := by
  rw [norm_mul, fourier_apply, Circle.norm_coe, mul_one,
    Complex.norm_of_nonneg (gaussianFourierCoefficient_pos ht k).le]

theorem summable_gaussianFourierTerm {t : ℝ} (ht : 0 < t) (u : ℝ) :
    Summable (fun k : ℤ => (gaussianFourierCoefficient t k : ℂ) * fourier k (u : UnitAddCircle)) := by
  apply (summable_gaussianFourierCoefficient ht).of_norm_bounded
  intro k
  exact (norm_gaussianFourierTerm ht u k).le

/-- Poisson expansion of the periodic Gaussian. Using `-u` in the Fourier
phase is equivalent to the paper's sign by reindexing `k ↦ -k`.
-/
theorem periodicGaussian_fourier {t : ℝ} (ht : 0 < t) (u : ℝ) :
    (periodicGaussian t u : ℂ) =
      ∑' k : ℤ, (gaussianFourierCoefficient t k : ℂ) * fourier k ((-u : ℝ) : UnitAddCircle) := by
  let f : ℝ → ℂ := fun x => (Real.exp (-Real.pi * t ^ 2 * x ^ 2) : ℂ)
  have hf : f =O[cocompact ℝ] (fun x : ℝ => |x| ^ (-2 : ℝ)) := by
    have h := (isLittleO_exp_neg_mul_sq_cocompact
      (a := ((Real.pi * t ^ 2 : ℝ) : ℂ))
      (by simpa only [Complex.ofReal_re] using mul_pos Real.pi_pos (sq_pos_of_pos ht)) (-2)).isBigO
    simpa only [f, Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_neg,
      Complex.ofReal_pow, neg_mul] using h
  have hF : Summable (fun k : ℤ => 𝓕 f k) := by
    simp only [f, fourier_gaussian_smoothing ht]
    exact Complex.summable_ofReal.mpr (summable_gaussianFourierCoefficient ht)
  have h := Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable
    (show Continuous f by fun_prop) one_lt_two hf hF (-u)
  rw [show 𝓕 f = _ from fourier_gaussian_smoothing ht] at h
  rw [periodicGaussian, Complex.ofReal_tsum]
  convert h using 1
  · apply tsum_congr
    intro k
    simp only [f]
    congr 3
    ring
  · rfl

theorem periodicGaussian_zero_eq_fourier_sum {t : ℝ} (ht : 0 < t) :
    periodicGaussian t 0 = ∑' k : ℤ, gaussianFourierCoefficient t k := by
  have h := congrArg Complex.re (periodicGaussian_fourier ht 0)
  simp only [neg_zero] at h
  rw [Complex.ofReal_re, Complex.re_tsum (summable_gaussianFourierTerm ht 0)] at h
  simpa using h

/-- The maximum-at-zero inequality from the nonnegative Gaussian Fourier
coefficients, used in the moment-generating-function estimates. -/
theorem periodicGaussian_le_zero {t : ℝ} (ht : 0 < t) (u : ℝ) :
    periodicGaussian t u ≤ periodicGaussian t 0 := by
  have hs : Summable (fun k : ℤ =>
      ‖(gaussianFourierCoefficient t k : ℂ) * fourier k ((-u : ℝ) : UnitAddCircle)‖) := by
    simpa only [norm_gaussianFourierTerm ht] using summable_gaussianFourierCoefficient ht
  calc
    periodicGaussian t u = ‖(periodicGaussian t u : ℂ)‖ :=
      (Complex.norm_of_nonneg (periodicGaussian_pos ht u).le).symm
    _ = ‖∑' k : ℤ, (gaussianFourierCoefficient t k : ℂ) *
        fourier k ((-u : ℝ) : UnitAddCircle)‖ := congrArg norm (periodicGaussian_fourier ht u)
    _ ≤ ∑' k : ℤ, ‖(gaussianFourierCoefficient t k : ℂ) *
        fourier k ((-u : ℝ) : UnitAddCircle)‖ := norm_tsum_le_tsum_norm hs
    _ = ∑' k : ℤ, gaussianFourierCoefficient t k :=
      tsum_congr (norm_gaussianFourierTerm ht (-u))
    _ = periodicGaussian t 0 := (periodicGaussian_zero_eq_fourier_sum ht).symm

end GeometricGaussianLHL
end

end PeriodicGaussian

section PeriodicGaussianBounds

/-!
## Explicit bounds near the origin

The scalar estimate in the Gaussian main-term lemma. The two integer tails are bounded by geometric
series, with the constants and all convergence statements proved.
-/

noncomputable section

namespace GeometricGaussianLHL

theorem gaussian_tail_ratio_le_quarter {a : ℝ} (ha : 2 ≤ a) :
    Real.exp (-(3 * a / 2)) ≤ 1 / 4 := by
  have hexp : 4 ≤ Real.exp (3 * a / 2) := by
    linarith [Real.add_one_le_exp (3 * a / 2)]
  rw [Real.exp_neg]
  simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4) hexp

theorem gaussian_positive_tail_bound {a u : ℝ} (ha : 2 ≤ a) (hu : |u| ≤ 1 / 4) (n : ℕ) :
    Real.exp (-a * (((n : ℝ) + 1) - u) ^ 2) ≤
      (Real.exp (-a * u ^ 2) * Real.exp (-a / 2)) * (1 / 4 : ℝ) ^ n := by
  have ha0 : 0 ≤ a := by linarith
  have hpoly : u ^ 2 + 1 / 2 + (3 / 2 : ℝ) * n ≤ ((n : ℝ) + 1 - u) ^ 2 := by
    have h := mul_nonneg (show (0 : ℝ) ≤ (n : ℝ) + 1 by positivity)
      (sub_nonneg.mpr (abs_le.mp hu).2)
    nlinarith [sq_nonneg (n : ℝ)]
  calc
    Real.exp (-a * (((n : ℝ) + 1) - u) ^ 2) ≤
        (Real.exp (-a * u ^ 2) * Real.exp (-a / 2)) *
          (Real.exp (-(3 * a / 2))) ^ n := by
      rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left hpoly ha0]
    _ ≤ (Real.exp (-a * u ^ 2) * Real.exp (-a / 2)) * (1 / 4 : ℝ) ^ n := by
      have hq := gaussian_tail_ratio_le_quarter ha
      gcongr

theorem gaussian_negative_tail_bound {a u : ℝ} (ha : 2 ≤ a) (hu : |u| ≤ 1 / 4) (n : ℕ) :
    Real.exp (-a * (-((n : ℝ) + 1) - u) ^ 2) ≤
      (Real.exp (-a * u ^ 2) * Real.exp (-a / 2)) * (1 / 4 : ℝ) ^ n := by
  have h := gaussian_positive_tail_bound ha (u := -u) (by simpa using hu) n
  rw [show (-((n : ℝ) + 1) - u) ^ 2 = ((n : ℝ) + 1 - -u) ^ 2 by ring]
  simpa only [neg_sq] using h

private theorem tsum_le_four_thirds {f : ℕ → ℝ} (hf : Summable f) {C : ℝ}
    (h : ∀ n, f n ≤ C * (1 / 4 : ℝ) ^ n) : (∑' n, f n) ≤ C * (4 / 3) := by
  have hg := (hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (by norm_num : (1 / 4 : ℝ) < 1)).summable.mul_left C
  have hc := hf.tsum_le_tsum h hg
  simpa only [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (by norm_num : (1 / 4 : ℝ) < 1), show (1 - (1 / 4 : ℝ))⁻¹ = 4 / 3 by norm_num] using hc

theorem shifted_integer_gaussian_near_zero {a u : ℝ} (ha : 2 ≤ a) (hu : |u| ≤ 1 / 4) :
    (∑' k : ℤ, Real.exp (-a * ((k : ℝ) - u) ^ 2)) ≤
      Real.exp (-a * u ^ 2) * (1 + 3 * Real.exp (-a / 2)) := by
  let f : ℤ → ℝ := fun k => Real.exp (-a * ((k : ℝ) - u) ^ 2)
  have hf : Summable f := summable_shifted_integer_gaussian (by linarith) u
  have hnat : Summable (fun n : ℕ => f n) := hf.comp_injective Nat.cast_injective
  have hpos : Summable (fun n : ℕ => f ((n : ℤ) + 1)) :=
    hf.comp_injective (fun _ _ h => by omega)
  have hneg : Summable (fun n : ℕ => f (-((n : ℤ) + 1))) :=
    hf.comp_injective (fun _ _ h => by omega)
  have hp : (∑' n : ℕ, f ((n : ℤ) + 1)) ≤
      (Real.exp (-a * u ^ 2) * Real.exp (-a / 2)) * (4 / 3) := by
    apply tsum_le_four_thirds hpos
    intro n
    simpa only [f, Int.cast_add, Int.cast_natCast, Int.cast_one] using
      gaussian_positive_tail_bound ha hu n
  have hn : (∑' n : ℕ, f (-((n : ℤ) + 1))) ≤
      (Real.exp (-a * u ^ 2) * Real.exp (-a / 2)) * (4 / 3) := by
    apply tsum_le_four_thirds hneg
    intro n
    simpa only [f, Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one] using
      gaussian_negative_tail_bound ha hu n
  have hsum := tsum_of_nat_of_neg_add_one hnat hneg
  rw [hnat.tsum_eq_zero_add] at hsum
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero] at hsum
  change (∑' k : ℤ, f k) ≤ _
  rw [hsum]
  have hf0 : f 0 = Real.exp (-a * u ^ 2) := by simp [f]
  rw [hf0]
  nlinarith [mul_pos (Real.exp_pos (-a * u ^ 2)) (Real.exp_pos (-a / 2))]

/-- Equation `eq:phi-near-zero` in the Gaussian main-term lemma, with the paper's constant 3. -/
theorem periodicGaussian_near_zero {t u : ℝ} (ht : 1 ≤ t) (hu : |u| ≤ 1 / 4) :
    periodicGaussian t u ≤
      Real.exp (-Real.pi * t ^ 2 * u ^ 2) * (1 + 3 * Real.exp (-Real.pi * t ^ 2 / 2)) := by
  have ha : 2 ≤ Real.pi * t ^ 2 := by
    have hsq : 1 ≤ t ^ 2 := by nlinarith
    nlinarith [Real.two_le_pi, mul_le_mul_of_nonneg_left hsq Real.pi_pos.le]
  simpa only [periodicGaussian, neg_mul] using shifted_integer_gaussian_near_zero ha hu

end GeometricGaussianLHL
end

end PeriodicGaussianBounds

section GaussianNormalization

/-!
## Exact Gaussian normalization

The rectangular Jacobian is `LinearMap.normDet`, the square root of the
Gram determinant. Full rank suffices; no bound on conditioning is used.
-/

noncomputable section

open MeasureTheory

namespace GeometricGaussianLHL

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The Gaussian with exponent `-π t² ‖x‖²` has mass `t⁻dim`.
-/
theorem integral_gaussianWeight {t : ℝ} (ht : 0 < t) :
    (∫ x : E, gaussianWeight t x) = (t ^ Module.finrank ℝ E)⁻¹ := by
  have hbase : (∫ x : E, Real.exp (-Real.pi * ‖x‖ ^ 2)) = 1 := by
    simpa using GaussianFourier.integral_rexp_neg_mul_sq_norm (V := E) Real.pi_pos
  have h := Measure.integral_comp_smul_of_nonneg (volume : Measure E)
    (fun x : E => Real.exp (-Real.pi * ‖x‖ ^ 2)) t (hR := ht.le)
  rw [hbase, smul_eq_mul, mul_one] at h
  convert h using 1
  congr 1
  funext x
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
  unfold gaussianWeight
  congr 1
  ring

/-- Change of variables for a real linear equivalence. -/
theorem integral_comp_linearEquiv (e : E ≃ₗ[ℝ] E) (f : E → ℝ) :
    (∫ x, f (e x)) = |e.toLinearMap.det|⁻¹ * ∫ x, f x := by
  have h := integral_map_equiv
    e.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv f (μ := volume)
  have hm : Measure.map (fun x => e x) (volume : Measure E) =
      ENNReal.ofReal |e.toLinearMap.det⁻¹| • volume :=
    Measure.map_linearMap_addHaar_eq_smul_addHaar volume e.isUnit_det'.ne_zero
  change (∫ x, f x ∂Measure.map (fun x => e x) volume) = _ at h
  rw [hm, integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _),
    smul_eq_mul, abs_inv] at h
  exact h.symm

omit [MeasurableSpace E] [BorelSpace E] in
/-- An injective rectangular map has the same norm and Jacobian as a
square change of coordinates on its domain. -/
theorem exists_equiv_norm_eq_normDet (f : E →ₗ[ℝ] F) (hf : Function.Injective f) :
    ∃ e : E ≃ₗ[ℝ] E, (∀ x, ‖e x‖ = ‖f x‖) ∧ |e.toLinearMap.det| = f.normDet := by
  obtain ⟨b⟩ := (f.normDet_ne_zero_tfae.out 5 4).mp hf
  let g : E ≃ₗᵢ[ℝ] f.range :=
    (stdOrthonormalBasis ℝ E).equiv b (Equiv.refl _)
  let e : E ≃ₗ[ℝ] E := (LinearEquiv.ofInjective f hf).trans g.symm.toLinearEquiv
  have hr : Module.finrank ℝ E = Module.finrank ℝ f.range :=
    by symm; exact (f.normDet_ne_zero_tfae.out 5 3).mp hf
  refine ⟨e, ?_, ?_⟩
  · intro x
    exact g.symm.norm_map (⟨f x, ⟨x, rfl⟩⟩ : f.range)
  · rw [← LinearMap.normDet_eq_abs_det]
    change (g.symm.toLinearMap ∘ₗ f.rangeRestrict).normDet = f.normDet
    rw [LinearMap.normDet_comp_of_finrank_eq _ _ hr]
    have hg : g.symm.toLinearEquiv.toLinearMap.normDet = 1 :=
      g.symm.toLinearIsometry.normDet_eq_one
    rw [hg, one_mul]
    exact LinearMap.normDet_codRestrict _

/-- Exact normalization for an injective rectangular linear map. -/
theorem integral_gaussianWeight_comp_injective (f : E →ₗ[ℝ] F)
    (hf : Function.Injective f) {t : ℝ} (ht : 0 < t) :
    (∫ x : E, gaussianWeight t (f x)) =
      (t ^ Module.finrank ℝ E * f.normDet)⁻¹ := by
  obtain ⟨e, he, hd⟩ := exists_equiv_norm_eq_normDet f hf
  have heq : (fun x => gaussianWeight t (f x)) = fun x => gaussianWeight t (e x) := by
    funext x
    simp only [gaussianWeight, he]
  rw [heq, integral_comp_linearEquiv, integral_gaussianWeight ht, hd, mul_inv_rev]

omit [MeasurableSpace E] [BorelSpace E] in
theorem normDet_pos_of_injective (f : E →ₗ[ℝ] F) (hf : Function.Injective f) :
    0 < f.normDet :=
  lt_of_le_of_ne f.normDet_nonneg (Ne.symm ((f.normDet_ne_zero_tfae.out 5 1).mp hf))

theorem integrable_gaussianWeight_comp_injective (f : E →ₗ[ℝ] F)
    (hf : Function.Injective f) {t : ℝ} (ht : 0 < t) :
    Integrable (fun x : E => gaussianWeight t (f x)) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_gaussianWeight_comp_injective f hf ht]
  exact inv_ne_zero (mul_ne_zero (pow_ne_zero _ ht.ne')
    (normDet_pos_of_injective f hf).ne')

/-- The paper's `D_A = sqrt(det(A Aᵀ))`. -/
def gramDet {R M : ℕ} (A : Matrix (Fin R) (Fin M) ℤ) : ℝ :=
  Real.sqrt ((A.map (Int.cast : ℤ → ℝ) * A.transpose.map (Int.cast : ℤ → ℝ)).det)

theorem realCoefficientMap_transpose_normDet {R M : ℕ}
    (A : Matrix (Fin R) (Fin M) ℤ) :
    (realCoefficientMap A.transpose).normDet = gramDet A := by
  have hs := (realCoefficientMap A.transpose).normDet_sq
  change (realCoefficientMap A.transpose).normDet ^ 2 = _ at hs
  rw [realCoefficientMap_transpose, LinearMap.adjoint_adjoint] at hs
  rw [← realCoefficientMap_transpose] at hs
  unfold realCoefficientMap at hs
  rw [← Matrix.toLpLin_mul 2 2 2, LinearMap.det_toLpLin] at hs
  rw [gramDet, ← hs]
  exact (Real.sqrt_sq (realCoefficientMap A.transpose).normDet_nonneg).symm

theorem realCoefficientMap_transpose_injective {R M : ℕ}
    (A : Matrix (Fin R) (Fin M) ℤ) (hA : Function.Surjective (realCoefficientMap A)) :
    Function.Injective (realCoefficientMap A.transpose) := by
  rw [← LinearMap.ker_eq_bot, realCoefficientMap_transpose,
    ← LinearMap.orthogonal_range, LinearMap.range_eq_top.mpr hA]
  exact Submodule.top_orthogonal_eq_bot

theorem gramDet_pos {R M : ℕ} (A : Matrix (Fin R) (Fin M) ℤ)
    (hA : Function.Surjective (realCoefficientMap A)) : 0 < gramDet A := by
  rw [← realCoefficientMap_transpose_normDet]
  exact normDet_pos_of_injective _ (realCoefficientMap_transpose_injective A hA)

/-- The whole-space normalization in the Gaussian main-term lemma. -/
theorem integral_gaussian_transpose {R M : ℕ} (A : Matrix (Fin R) (Fin M) ℤ)
    (hA : Function.Surjective (realCoefficientMap A)) {t : ℝ} (ht : 0 < t) :
    (∫ y : Euclidean R, gaussianWeight t (realCoefficientMap A.transpose y)) =
      (t ^ R * gramDet A)⁻¹ := by
  simpa only [Euclidean, finrank_euclideanSpace, Fintype.card_fin,
    realCoefficientMap_transpose_normDet] using
    integral_gaussianWeight_comp_injective _ (realCoefficientMap_transpose_injective A hA) ht

theorem gaussian_transpose_normalization {R M : ℕ} (A : Matrix (Fin R) (Fin M) ℤ)
    (hA : Function.Surjective (realCoefficientMap A)) {t : ℝ} (ht : 0 < t) :
    (t ^ R * gramDet A) *
      (∫ y : Euclidean R, gaussianWeight t (realCoefficientMap A.transpose y)) = 1 := by
  rw [integral_gaussian_transpose A hA ht, mul_inv_cancel₀]
  exact mul_ne_zero (pow_ne_zero _ ht.ne') (gramDet_pos A hA).ne'

end GeometricGaussianLHL
end

end GaussianNormalization

section SmoothingExistence

/-!
## Existence of smoothing parameters

The standard integer lattice is self-dual. Its Gaussian sum factors into one-dimensional convergent
sums, and dominated convergence sends its nonzero dual mass to zero as the smoothing parameter tends
to infinity. Every finitely generated subgroup is a linear image of a standard integer lattice, so
metric transport yields smoothing existence and completes the metric-change lemma.
-/

noncomputable section

open scoped ENNReal Topology
open Filter

namespace GeometricGaussianLHL

theorem integerLattice_dual_eq (M : ℕ) : latticeDual (integerLattice M) = integerLattice M := by
  ext v
  constructor
  · intro hv
    have hc : ∀ i : Fin M, ∃ k : ℤ, (k : ℝ) = v i := by
      intro i
      have hb : EuclideanSpace.basisFun (Fin M) ℝ i ∈ integerLattice M :=
        ⟨Pi.basisFun ℤ (Fin M) i, integerEmbedding_basis M i⟩
      simpa only [EuclideanSpace.inner_basisFun_real] using (mem_latticeDual.mp hv).2 _ hb
    choose k hk using hc
    exact ⟨k, by ext i; exact hk i⟩
  · rintro ⟨k, rfl⟩
    rw [mem_latticeDual]
    refine ⟨by rw [integerLattice_span]; trivial, ?_⟩
    rintro z ⟨w, rfl⟩
    exact ⟨∑ i, k i * w i, (integerEmbedding_inner k w).symm⟩

theorem gaussianWeight_integer_product {M : ℕ} (t : ℝ) (z : Coeff M) :
    gaussianWeight t (integerEmbedding M z) =
      ∏ i, Real.exp (-(Real.pi * t ^ 2) * (z i : ℝ) ^ 2) := by
  rw [gaussianWeight, EuclideanSpace.real_norm_sq_eq]
  simp only [integerEmbedding_apply, Finset.mul_sum]
  rw [← Real.exp_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem integer_gaussian_mass_ne_top (M : ℕ) {t : ℝ} (ht : 0 < t) :
    (∑' z : Coeff M, ENNReal.ofReal (gaussianWeight t (integerEmbedding M z))) ≠ ⊤ := by
  simp_rw [gaussianWeight_integer_product,
    ENNReal.ofReal_prod_of_nonneg (fun _ _ => (Real.exp_pos _).le)]
  rw [tsum_finite_product M (fun _ => fun z : ℤ =>
    ENNReal.ofReal (Real.exp (-(Real.pi * t ^ 2) * (z : ℝ) ^ 2)))]
  exact ENNReal.prod_ne_top (fun _ _ =>
    (summable_integer_gaussian (mul_pos Real.pi_pos (sq_pos_of_pos ht))).tsum_ofReal_ne_top)

theorem summable_coefficient_gaussian (M : ℕ) {t : ℝ} (ht : 0 < t) :
    Summable (fun z : Coeff M => gaussianWeight t (integerEmbedding M z)) := by
  simpa only [ENNReal.toReal_ofReal (gaussianWeight_pos _ _).le] using
    ENNReal.summable_toReal (integer_gaussian_mass_ne_top M ht)

def nonzeroCoefficientWeight {M : ℕ} (t : ℝ) (z : Coeff M) : ℝ :=
  if z = 0 then 0 else gaussianWeight t (integerEmbedding M z)

theorem nonzeroCoefficientWeight_nonneg {M : ℕ} (t : ℝ) (z : Coeff M) :
    0 ≤ nonzeroCoefficientWeight t z := by
  unfold nonzeroCoefficientWeight
  split_ifs
  · rfl
  · exact (gaussianWeight_pos _ _).le

theorem summable_nonzeroCoefficientWeight (M : ℕ) {t : ℝ} (ht : 0 < t) :
    Summable (nonzeroCoefficientWeight (M := M) t) := by
  apply (summable_coefficient_gaussian M ht).of_norm_bounded
  intro z
  rw [Real.norm_eq_abs, abs_of_nonneg (nonzeroCoefficientWeight_nonneg t z)]
  unfold nonzeroCoefficientWeight
  split_ifs
  · exact (gaussianWeight_pos _ _).le
  · rfl

theorem integerLattice_nonzeroDualMass (M : ℕ) {t : ℝ} (ht : 0 < t) :
    nonzeroDualMass (integerLattice M) t =
      ENNReal.ofReal (∑' z : Coeff M, nonzeroCoefficientWeight t z) := by
  classical
  rw [nonzeroDualMass, integerLattice_dual_eq]
  let e : Coeff M ≃ₗ[ℤ] integerLattice M :=
    LinearEquiv.ofInjective (integerEmbedding M) (integerEmbedding_injective M)
  rw [← e.toEquiv.tsum_eq]
  rw [ENNReal.ofReal_tsum_of_nonneg (nonzeroCoefficientWeight_nonneg t)
    (summable_nonzeroCoefficientWeight M ht)]
  apply tsum_congr
  intro z
  have he : e.toEquiv z = 0 ↔ z = 0 := e.map_eq_zero_iff
  simp only [he, nonzeroCoefficientWeight]
  split_ifs
  · exact ENNReal.ofReal_zero.symm
  · rfl

theorem tendsto_gaussianWeight_atTop {E : Type*} [NormedAddCommGroup E] {v : E} (hv : v ≠ 0) :
    Tendsto (fun t : ℝ => gaussianWeight t v) atTop (𝓝 0) := by
  have hpoly : Tendsto (fun t : ℝ => (Real.pi * ‖v‖ ^ 2) * t ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by decide : 2 ≠ 0)).const_mul_atTop
      (mul_pos Real.pi_pos (sq_pos_of_pos (norm_pos_iff.mpr hv)))
  convert Real.tendsto_exp_neg_atTop_nhds_zero.comp hpoly using 1
  funext t
  simp only [Function.comp_apply, gaussianWeight]
  congr 1
  ring

theorem tendsto_nonzeroCoefficientMass (M : ℕ) :
    Tendsto (fun t : ℝ => ∑' z : Coeff M, nonzeroCoefficientWeight t z) atTop (𝓝 0) := by
  have hlim : ∀ z : Coeff M,
      Tendsto (fun t : ℝ => nonzeroCoefficientWeight t z) atTop (𝓝 (0 : ℝ)) := by
    intro z
    by_cases hz : z = 0
    · simp only [nonzeroCoefficientWeight, hz, ite_true]
      exact tendsto_const_nhds
    · simp only [nonzeroCoefficientWeight, hz, ite_false]
      apply tendsto_gaussianWeight_atTop
      intro h
      apply hz
      apply integerEmbedding_injective M
      simpa only [map_zero] using h
  have hbound : ∀ᶠ t : ℝ in atTop, ∀ z : Coeff M,
      ‖nonzeroCoefficientWeight t z‖ ≤ nonzeroCoefficientWeight 1 z := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    intro z
    rw [Real.norm_eq_abs, abs_of_nonneg (nonzeroCoefficientWeight_nonneg t z)]
    unfold nonzeroCoefficientWeight
    split_ifs
    · rfl
    · exact gaussianWeight_antitone (by norm_num) ht _
  simpa only [tsum_zero] using tendsto_tsum_of_dominated_convergence
    (summable_nonzeroCoefficientWeight M (by norm_num : (0 : ℝ) < 1)) hlim hbound

/-- The standard integer lattice has a smoothing certificate for every
positive error, in every dimension (including zero). -/
theorem integerLattice_exists_smoothAt (M : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ t, SmoothAt (integerLattice M) ε t := by
  have he := (tendsto_nonzeroCoefficientMass M).eventually (gt_mem_nhds hε)
  obtain ⟨t, ht, he⟩ := ((eventually_gt_atTop (0 : ℝ)).and he).exists
  refine ⟨t, ht, ?_⟩
  rw [integerLattice_nonzeroDualMass M ht]
  exact ENNReal.ofReal_le_ofReal he.le

section GeneralLattice

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ E] in
@[simp] theorem latticeDual_bot : latticeDual (⊥ : Submodule ℤ E) = ⊥ := by
  simp [latticeDual]

omit [FiniteDimensional ℝ E] in
@[simp] theorem nonzeroDualMass_bot (t : ℝ) : nonzeroDualMass (⊥ : Submodule ℤ E) t = 0 := by
  classical
  rw [nonzeroDualMass, latticeDual_bot]
  calc
    _ = ∑' _ : (⊥ : Submodule ℤ E), (0 : ℝ≥0∞) :=
      tsum_congr (fun v => ite_eq_left (Subsingleton.elim v 0))
    _ = 0 := tsum_zero

omit [FiniteDimensional ℝ E] in
theorem smoothAt_bot {ε t : ℝ} (ht : 0 < t) : SmoothAt (⊥ : Submodule ℤ E) ε t :=
  ⟨ht, by rw [nonzeroDualMass_bot]; exact zero_le⟩

omit [FiniteDimensional ℝ E] in
@[simp] theorem smoothingParameter_bot (ε : ℝ) :
    smoothingParameter (⊥ : Submodule ℤ E) ε = 0 := by
  apply le_antisymm
  · apply le_of_forall_gt
    intro t ht
    exact (smoothingParameter_le_of_smoothAt
      (smoothAt_bot (E := E) (ε := ε) (t := t / 2) (by linarith))).trans_lt (by linarith)
  · exact le_csInf ⟨1, smoothAt_bot (E := E) (ε := ε) (by norm_num)⟩ (fun t ht => ht.1.le)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
@[simp] theorem latticeImage_zero (L : Submodule ℤ E) :
    latticeImage (0 : E →L[ℝ] F) L = ⊥ := by
  change L.map (0 : E →ₗ[ℤ] F) = ⊥
  exact Submodule.map_zero _

omit [FiniteDimensional ℝ E] in
/-- Every finitely generated additive lattice is the actual linear image of
some standard integer lattice. -/
theorem exists_latticeImage_integerLattice (L : Submodule ℤ E) (hL : L.FG) :
    ∃ n : ℕ, ∃ T : Euclidean n →L[ℝ] E, latticeImage T (integerLattice n) = L := by
  obtain ⟨n, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hL
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let T : Euclidean n →L[ℝ] E := (b.constr ℝ g).toContinuousLinearMap
  refine ⟨n, T, ?_⟩
  rw [latticeImage, integerLattice_eq_basis_span, Submodule.map_span, ← Set.range_comp]
  have hb : (T.toLinearMap.restrictScalars ℤ) ∘ EuclideanSpace.basisFun (Fin n) ℝ = g := by
    funext i
    exact b.constr_basis ℝ g i
  rw [hb, hg]

/-- Smoothing exists for every finitely generated subgroup, without needing
to assume the existence of a shortest dual vector or a Gaussian tail bound. -/
theorem exists_smoothAt_of_fg (L : Submodule ℤ E) (hL : L.FG) {ε : ℝ} (hε : 0 < ε) :
    ∃ t, SmoothAt L ε t := by
  obtain ⟨n, T, hT⟩ := exists_latticeImage_integerLattice L hL
  rw [← hT]
  by_cases hzero : T = 0
  · rw [hzero, latticeImage_zero]
    exact ⟨1, smoothAt_bot (by norm_num)⟩
  · obtain ⟨t, ht⟩ := integerLattice_exists_smoothAt n hε
    exact ⟨‖T‖ * t, ht.metric_change T hzero⟩

theorem exists_smoothAt (L : Submodule ℤ E) [DiscreteTopology L] {ε : ℝ} (hε : 0 < ε) :
    ∃ t, SmoothAt L ε t := exists_smoothAt_of_fg L Submodule.FG.of_finite hε

/-- Every positive smoothing parameter has finite nonzero dual Gaussian mass
for a finitely generated subgroup. -/
theorem nonzeroDualMass_ne_top_of_fg (L : Submodule ℤ E) (hL : L.FG)
    {t : ℝ} (ht : 0 < t) : nonzeroDualMass L t ≠ ⊤ := by
  obtain ⟨n, T, hT⟩ := exists_latticeImage_integerLattice L hL
  rw [← hT]
  by_cases hzero : T = 0
  · simp [hzero]
  · have hn : 0 < ‖T‖ := norm_pos_iff.mpr hzero
    have hb := nonzeroDualMass_metric_change T (integerLattice n) (t / ‖T‖)
    rw [mul_div_cancel₀ t hn.ne', integerLattice_nonzeroDualMass n (div_pos ht hn)] at hb
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hb

theorem dualMass_ne_top_of_fg (L : Submodule ℤ E) (hL : L.FG)
    {t : ℝ} (ht : 0 < t) : dualMass L t ≠ ⊤ := by
  rw [dualMass_eq_one_add]
  exact ENNReal.add_ne_top.mpr ⟨by norm_num, nonzeroDualMass_ne_top_of_fg L hL ht⟩

theorem summable_dual_gaussian_of_fg (L : Submodule ℤ E) (hL : L.FG)
    {t : ℝ} (ht : 0 < t) :
    Summable (fun v : latticeDual L => gaussianWeight t (v : E)) := by
  have hmass := dualMass_ne_top_of_fg L hL ht
  change (∑' v : latticeDual L, ENNReal.ofReal (gaussianWeight t (v : E))) ≠ ⊤ at hmass
  have h := ENNReal.summable_toReal hmass
  simpa only [ENNReal.toReal_ofReal (gaussianWeight_pos _ _).le] using h

/-- The metric-change lemma, including existence of the smoothing parameters. The result even holds
for arbitrary continuous linear maps on finitely generated subgroups; an isomorphism is not required
for the upper bound. -/
theorem smoothingParameter_metric_change_of_fg (T : E →L[ℝ] F)
    (L : Submodule ℤ E) (hL : L.FG) {ε : ℝ} (hε : 0 < ε) :
    smoothingParameter (latticeImage T L) ε ≤ ‖T‖ * smoothingParameter L ε := by
  by_cases hT : T = 0
  · simp [hT]
  · exact smoothingParameter_metric_change T hT L ε (exists_smoothAt_of_fg L hL hε)

theorem smoothingParameter_metric_change_of_discrete (T : E →L[ℝ] F)
    (L : Submodule ℤ E) [DiscreteTopology L] {ε : ℝ} (hε : 0 < ε) :
    smoothingParameter (latticeImage T L) ε ≤ ‖T‖ * smoothingParameter L ε :=
  smoothingParameter_metric_change_of_fg T L Submodule.FG.of_finite hε

theorem coefficientKernel_exists_smoothAt {R M : ℕ}
    (A : Matrix (Fin R) (Fin M) ℤ) {ε : ℝ} (hε : 0 < ε) :
    ∃ t, SmoothAt (euclideanKernel A) ε t := by
  let : DiscreteTopology (euclideanKernel A) :=
    integerEmbedding_map_discreteTopology (coefficientKernel A)
  exact exists_smoothAt (euclideanKernel A) hε

end GeneralLattice

end GeometricGaussianLHL
end

end SmoothingExistence

section AffineGaussian

/-!
## Gaussian integrals over affine fibers

The contribution of one integer coset in the exact theta-integral proposition is the Gaussian weight
of its orthogonal projection, divided by the exact Jacobian.
-/

noncomputable section

open MeasureTheory

namespace GeometricGaussianLHL

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

omit [MeasurableSpace E] [BorelSpace E] in
theorem norm_sq_affine_fiber (f : E →ₗ[ℝ] F) (w : F) (u y : E)
    (hu : f u = f.range.starProjection w) :
    ‖w - f y‖ ^ 2 = ‖f.rangeᗮ.starProjection w‖ ^ 2 + ‖f (y - u)‖ ^ 2 := by
  have hp : f.range.starProjection (f y) = f y :=
    Submodule.starProjection_eq_self_iff.mpr ⟨y, rfl⟩
  have ho : f.rangeᗮ.starProjection (f y) = 0 :=
    Submodule.starProjection_orthogonal_apply_eq_zero ⟨y, rfl⟩
  rw [Submodule.norm_sq_eq_add_norm_sq_starProjection (w - f y) f.range,
    map_sub, map_sub, hp, ho, sub_zero, ← hu, map_sub, norm_sub_rev]
  exact add_comm _ _

omit [MeasurableSpace E] [BorelSpace E] in
theorem gaussianWeight_affine_fiber (f : E →ₗ[ℝ] F) (w : F) (u y : E)
    (hu : f u = f.range.starProjection w) (t : ℝ) :
    gaussianWeight t (w - f y) =
      gaussianWeight t (f.rangeᗮ.starProjection w) * gaussianWeight t (f (y - u)) := by
  simp only [gaussianWeight, norm_sq_affine_fiber f w u y hu, mul_add, Real.exp_add]

/-- The exact affine-fiber integral, without a conditioning assumption. -/
theorem integral_gaussianWeight_affine (f : E →ₗ[ℝ] F) (hf : Function.Injective f)
    (w : F) {t : ℝ} (ht : 0 < t) :
    (∫ y : E, gaussianWeight t (w - f y)) =
      gaussianWeight t (f.rangeᗮ.starProjection w) /
        (t ^ Module.finrank ℝ E * f.normDet) := by
  obtain ⟨u, hu⟩ := f.range.starProjection_apply_mem w
  simp_rw [gaussianWeight_affine_fiber f w u _ hu t]
  rw [integral_const_mul, integral_sub_right_eq_self (fun x : E => gaussianWeight t (f x)) u,
    integral_gaussianWeight_comp_injective f hf ht, div_eq_mul_inv]

/-- Absolute convergence of the integral associated with every coset. -/
theorem integrable_gaussianWeight_affine (f : E →ₗ[ℝ] F) (hf : Function.Injective f)
    (w : F) {t : ℝ} (ht : 0 < t) :
    Integrable (fun y : E => gaussianWeight t (w - f y)) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_gaussianWeight_affine f hf w ht]
  exact div_ne_zero (Real.exp_pos _).ne'
    (mul_ne_zero (pow_ne_zero _ ht.ne') (normDet_pos_of_injective f hf).ne')

/-- The integral appearing in the coset calculation in the exact theta-integral proposition. -/
theorem integral_coefficient_gaussian_fiber {R M : ℕ}
    (A : Matrix (Fin R) (Fin M) ℤ) (hA : Function.Surjective (realCoefficientMap A))
    (k : Coeff M) {t : ℝ} (ht : 0 < t) :
    (∫ y : Euclidean R, gaussianWeight t (integerEmbedding M k - realCoefficientMap A.transpose y)) =
      gaussianWeight t ((realCoefficientMap A).ker.starProjection (integerEmbedding M k)) /
        (t ^ R * gramDet A) := by
  have h := integral_gaussianWeight_affine _ (realCoefficientMap_transpose_injective A hA)
    (integerEmbedding M k) ht
  have hk : (realCoefficientMap A.transpose).rangeᗮ = (realCoefficientMap A).ker := by
    rw [realCoefficientMap_transpose, LinearMap.orthogonal_range, LinearMap.adjoint_adjoint]
  simpa only [hk, Euclidean, finrank_euclideanSpace, Fintype.card_fin,
    realCoefficientMap_transpose_normDet] using h

end GeometricGaussianLHL
end

end AffineGaussian

section MainTerm

/-!
## The near-origin contribution

The Gaussian main-term lemma: the product of periodic Gaussians on the small ball is bounded by a
Gaussian whose whole-space mass cancels the exact Gram determinant.
-/

noncomputable section

open MeasureTheory

namespace GeometricGaussianLHL

/-- The actual product integrand in the exact theta-integral proposition. -/
def thetaIntegrand {R M : ℕ} (A : Matrix (Fin R) (Fin M) ℤ) (t : ℝ)
    (y : Euclidean R) : ℝ :=
  ∏ j, periodicGaussian t (realCoefficientMap A.transpose y j)

/-- The small ball used to isolate the Gaussian main term. -/
def nearOriginBall (R : ℕ) (B : ℝ) : Set (Euclidean R) :=
  {y | ‖y‖ ≤ 1 / (4 * B)}

/-- The paper's centered unit cube, including its measure-zero boundary. -/
def centeredUnitCube (R : ℕ) : Set (Euclidean R) :=
  {y | ∀ i, |y i| ≤ 1 / 2}

theorem nearOriginBall_subset_centeredUnitCube {R : ℕ} {B : ℝ} (hB : 1 ≤ B) :
    nearOriginBall R B ⊆ centeredUnitCube R := by
  intro y hy i
  have hcoord : |y i| ≤ ‖y‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le y i
  have hdiv : 1 / (4 * B) ≤ (1 / 4 : ℝ) := by
    apply one_div_le_one_div_of_le (by norm_num)
    linarith
  have h := hcoord.trans (hy.trans hdiv)
  linarith

/-- Euclidean realization of a column of the integer coefficient matrix. -/
def realColumn {R M : ℕ} (A : Matrix (Fin R) (Fin M) ℤ) (j : Fin M) : Euclidean R :=
  realCoefficientMap A (EuclideanSpace.basisFun (Fin M) ℝ j)

theorem realColumn_apply {R M : ℕ} (A : Matrix (Fin R) (Fin M) ℤ)
    (j : Fin M) (i : Fin R) : realColumn A j i = (A i j : ℝ) := by
  simp [realColumn, realCoefficientMap, Matrix.toLpLin_apply, EuclideanSpace.basisFun_apply]

theorem transpose_coordinate_eq_inner {R M : ℕ} (A : Matrix (Fin R) (Fin M) ℤ)
    (y : Euclidean R) (j : Fin M) :
    realCoefficientMap A.transpose y j = inner ℝ (realColumn A j) y := by
  rw [realCoefficientMap_transpose, ← EuclideanSpace.basisFun_inner,
    LinearMap.adjoint_inner_right]
  rfl

theorem transpose_coordinates_small {R M : ℕ} (A : Matrix (Fin R) (Fin M) ℤ)
    {B : ℝ} (hB : 0 < B) (hcol : ∀ j, ‖realColumn A j‖ ≤ B)
    {y : Euclidean R} (hy : y ∈ nearOriginBall R B) (j : Fin M) :
    |realCoefficientMap A.transpose y j| ≤ 1 / 4 := by
  rw [transpose_coordinate_eq_inner]
  calc
    |inner ℝ (realColumn A j) y| ≤ ‖realColumn A j‖ * ‖y‖ := abs_real_inner_le_norm _ _
    _ ≤ B * (1 / (4 * B)) := mul_le_mul (hcol j) hy (norm_nonneg _) hB.le
    _ = 1 / 4 := by field_simp

@[fun_prop]
theorem periodicGaussian_measurable (t : ℝ) : Measurable (periodicGaussian t) := by
  unfold periodicGaussian
  apply Measurable.tsum
  intro k
  fun_prop

@[fun_prop]
theorem thetaIntegrand_measurable {R M : ℕ} (A : Matrix (Fin R) (Fin M) ℤ) (t : ℝ) :
    Measurable (thetaIntegrand A t) := by
  unfold thetaIntegrand
  fun_prop

theorem thetaIntegrand_nonneg {R M : ℕ} (A : Matrix (Fin R) (Fin M) ℤ)
    {t : ℝ} (ht : 0 < t) (y : Euclidean R) : 0 ≤ thetaIntegrand A t y := by
  exact Finset.prod_nonneg fun j _ => (periodicGaussian_pos ht _).le

theorem gaussianWeight_product {M : ℕ} (t : ℝ) (x : Euclidean M) :
    gaussianWeight t x = ∏ j, Real.exp (-Real.pi * t ^ 2 * (x j) ^ 2) := by
  rw [gaussianWeight, EuclideanSpace.real_norm_sq_eq, Finset.mul_sum, Real.exp_sum]

/-- The pointwise estimate for the full product in the Gaussian main-term lemma. -/
theorem thetaIntegrand_near_origin {R M : ℕ} (A : Matrix (Fin R) (Fin M) ℤ)
    {B t : ℝ} (hB : 0 < B) (ht : 1 ≤ t) (hcol : ∀ j, ‖realColumn A j‖ ≤ B)
    {y : Euclidean R} (hy : y ∈ nearOriginBall R B) :
    thetaIntegrand A t y ≤
      (1 + 3 * Real.exp (-Real.pi * t ^ 2 / 2)) ^ M *
        gaussianWeight t (realCoefficientMap A.transpose y) := by
  calc
    thetaIntegrand A t y ≤ ∏ j : Fin M,
        (Real.exp (-Real.pi * t ^ 2 * (realCoefficientMap A.transpose y j) ^ 2) *
          (1 + 3 * Real.exp (-Real.pi * t ^ 2 / 2))) := by
      apply Finset.prod_le_prod
      · intro j _
        exact (periodicGaussian_pos (by linarith) _).le
      · intro j _
        exact periodicGaussian_near_zero ht (transpose_coordinates_small A hB hcol hy j)
    _ = _ := by
      rw [Finset.prod_mul_distrib, ← gaussianWeight_product]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      exact mul_comm _ _

theorem nearOriginBall_measurable (R : ℕ) (B : ℝ) : MeasurableSet (nearOriginBall R B) :=
  measurableSet_le continuous_norm.measurable measurable_const

/-- In particular, the ball integral is an integral of an integrable function. -/
theorem thetaIntegrand_integrableOn_near_origin {R M : ℕ}
    (A : Matrix (Fin R) (Fin M) ℤ) (hA : Function.Surjective (realCoefficientMap A))
    {B t : ℝ} (hB : 0 < B) (ht : 1 ≤ t) (hcol : ∀ j, ‖realColumn A j‖ ≤ B) :
    IntegrableOn (thetaIntegrand A t) (nearOriginBall R B) := by
  have ht0 : 0 < t := by linarith
  have hi := (integrable_gaussianWeight_comp_injective _
    (realCoefficientMap_transpose_injective A hA) ht0).const_mul
      ((1 + 3 * Real.exp (-Real.pi * t ^ 2 / 2)) ^ M)
  apply hi.integrableOn.mono' (thetaIntegrand_measurable A t).aestronglyMeasurable
  filter_upwards [ae_restrict_mem (nearOriginBall_measurable R B)] with y hy
  rw [Real.norm_eq_abs, abs_of_nonneg (thetaIntegrand_nonneg A ht0 y)]
  exact thetaIntegrand_near_origin A hB ht hcol hy

/-- The Gaussian main-term lemma's bound for the normalized contribution of the small ball. -/
theorem normalized_near_origin_bound {R M : ℕ} (A : Matrix (Fin R) (Fin M) ℤ)
    (hA : Function.Surjective (realCoefficientMap A))
    {B t : ℝ} (hB : 0 < B) (ht : 1 ≤ t) (hcol : ∀ j, ‖realColumn A j‖ ≤ B) :
    (t ^ R * gramDet A) * (∫ y in nearOriginBall R B, thetaIntegrand A t y) ≤
      (1 + 3 * Real.exp (-Real.pi * t ^ 2 / 2)) ^ M := by
  let C := (1 + 3 * Real.exp (-Real.pi * t ^ 2 / 2)) ^ M
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have ht0 : 0 < t := by linarith
  have hi := (integrable_gaussianWeight_comp_injective _
    (realCoefficientMap_transpose_injective A hA) ht0).const_mul C
  have hle : (∫ y in nearOriginBall R B, thetaIntegrand A t y) ≤
      C * (∫ y : Euclidean R, gaussianWeight t (realCoefficientMap A.transpose y)) := by
    calc
      _ ≤ ∫ y in nearOriginBall R B,
          C * gaussianWeight t (realCoefficientMap A.transpose y) :=
        setIntegral_mono_on (thetaIntegrand_integrableOn_near_origin A hA hB ht hcol)
          hi.integrableOn (nearOriginBall_measurable R B)
          (fun _ hy => thetaIntegrand_near_origin A hB ht hcol hy)
      _ ≤ ∫ y : Euclidean R, C * gaussianWeight t (realCoefficientMap A.transpose y) :=
        setIntegral_le_integral hi (Filter.Eventually.of_forall
          (fun y => mul_nonneg hC (Real.exp_pos _).le))
      _ = _ := integral_const_mul _ _
  have hn := gaussian_transpose_normalization A hA ht0
  have hp : 0 ≤ t ^ R * gramDet A := mul_nonneg (pow_nonneg ht0.le _) (gramDet_pos A hA).le
  have h := mul_le_mul_of_nonneg_left hle hp
  calc
    _ ≤ (t ^ R * gramDet A) *
        (C * (∫ y : Euclidean R, gaussianWeight t (realCoefficientMap A.transpose y))) := h
    _ = C := by rw [mul_left_comm, hn, mul_one]

end GeometricGaussianLHL
end

end MainTerm

section SmoothingClosure

/-!
## Smoothing at the infimum

The nonzero dual Gaussian mass is lower semicontinuous, even without a
convergence hypothesis. Its sublevel sets are closed, so their bound holds
at the infimum of all positive smoothing widths. Every positive width at
least that infimum is therefore a genuine smoothing certificate. This
handles the non-strict width hypothesis of the Gaussian pushforward lemma.
-/

noncomputable section

open scoped ENNReal Topology

namespace GeometricGaussianLHL

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] in
@[fun_prop] theorem gaussianWeight_continuous_parameter (v : E) :
    Continuous (fun t : ℝ => gaussianWeight t v) := by
  unfold gaussianWeight
  fun_prop

/-- No finiteness of the infinite Gaussian sum is needed for this fact.
-/
theorem nonzeroDualMass_lowerSemicontinuous (L : Submodule ℤ E) :
    LowerSemicontinuous (nonzeroDualMass L) := by
  classical
  unfold nonzeroDualMass
  apply lowerSemicontinuous_tsum
  intro v
  by_cases hv : v = 0
  · simp only [hv, ite_true]
    exact continuous_const.lowerSemicontinuous
  · simp only [hv, ite_false]
    exact (ENNReal.continuous_ofReal.comp
      (gaussianWeight_continuous_parameter (v : E))).lowerSemicontinuous

theorem nonzeroDualMass_sublevel_closed (L : Submodule ℤ E) (ε : ℝ) :
    IsClosed {t : ℝ | nonzeroDualMass L t ≤ ENNReal.ofReal ε} :=
  (nonzeroDualMass_lowerSemicontinuous L).isClosed_preimage _

theorem smoothingParameter_nonneg_of_exists {L : Submodule ℤ E} {ε : ℝ}
    (hexists : ∃ t, SmoothAt L ε t) : 0 ≤ smoothingParameter L ε :=
  le_csInf hexists (fun _ ht => ht.1.le)

/-- The mass bound holds at the infimum, including a zero infimum. -/
theorem nonzeroDualMass_smoothingParameter_le {L : Submodule ℤ E} {ε : ℝ}
    (hexists : ∃ t, SmoothAt L ε t) :
    nonzeroDualMass L (smoothingParameter L ε) ≤ ENNReal.ofReal ε := by
  have hcl : smoothingParameter L ε ∈ closure {t : ℝ | SmoothAt L ε t} :=
    csInf_mem_closure hexists ⟨0, fun _ ht => ht.1.le⟩
  exact (closure_minimal (fun _ ht => ht.2) (nonzeroDualMass_sublevel_closed L ε)) hcl

/-- Equality with a positive smoothing parameter is allowed. -/
theorem smoothAt_of_smoothingParameter_le_of_exists {L : Submodule ℤ E} {ε t : ℝ}
    (hexists : ∃ s, SmoothAt L ε s) (ht : 0 < t)
    (hη : smoothingParameter L ε ≤ t) : SmoothAt L ε t :=
  ⟨ht, (nonzeroDualMass_antitone L (smoothingParameter_nonneg_of_exists hexists) hη).trans
    (nonzeroDualMass_smoothingParameter_le hexists)⟩

theorem smoothAt_iff_smoothingParameter_le_of_exists {L : Submodule ℤ E} {ε t : ℝ}
    (hexists : ∃ s, SmoothAt L ε s) (ht : 0 < t) :
    SmoothAt L ε t ↔ smoothingParameter L ε ≤ t :=
  ⟨smoothingParameter_le_of_smoothAt, smoothAt_of_smoothingParameter_le_of_exists hexists ht⟩

variable [FiniteDimensional ℝ E]

theorem smoothAt_of_smoothingParameter_le_of_discrete (L : Submodule ℤ E)
    [DiscreteTopology L] {ε t : ℝ} (hε : 0 < ε) (ht : 0 < t)
    (hη : smoothingParameter L ε ≤ t) : SmoothAt L ε t :=
  smoothAt_of_smoothingParameter_le_of_exists (exists_smoothAt L hε) ht hη

end GeometricGaussianLHL
end

end SmoothingClosure

section BlockColumns

/-!
## Integer block columns

An integer family of multiplication matrices acts on each independent
coefficient column. The resulting matrix has `m*d` actual integer columns;
its transpose integrand factors into the `m` ring-column contributions.
-/

noncomputable section

open scoped BigOperators

namespace GeometricGaussianLHL

def blockCoefficientMatrix {R d m : ℕ} (T : Fin d → Matrix (Fin R) (Fin R) ℤ)
    (X : Fin m → Coeff R) : Matrix (Fin R) (Fin (m * d)) ℤ :=
  fun i l => (T (finProdFinEquiv.symm l).2).mulVec (X (finProdFinEquiv.symm l).1) i

theorem blockCoefficientMatrix_column {R d m : ℕ}
    (T : Fin d → Matrix (Fin R) (Fin R) ℤ) (X : Fin m → Coeff R) (j : Fin m) (k : Fin d) :
    realColumn (blockCoefficientMatrix T X) (finProdFinEquiv (j, k)) =
      realCoefficientMap (T k) (integerEmbedding R (X j)) := by
  rw [realCoefficientMap_integerEmbedding]
  ext i
  simp only [realColumn_apply, blockCoefficientMatrix, Equiv.symm_apply_apply, integerEmbedding_apply]
  rfl

def operatorColumnFactor {R d : ℕ} (T : Fin d → Euclidean R →ₗ[ℝ] Euclidean R)
    (t : ℝ) (y : Euclidean R) (x : Coeff R) : ℝ :=
  ∏ k, periodicGaussian t (inner ℝ y (T k (integerEmbedding R x)))

theorem operatorColumnFactor_nonneg {R d : ℕ}
    (T : Fin d → Euclidean R →ₗ[ℝ] Euclidean R) {t : ℝ} (ht : 0 < t)
    (y : Euclidean R) (x : Coeff R) : 0 ≤ operatorColumnFactor T t y x :=
  Finset.prod_nonneg (fun _ _ => (periodicGaussian_pos ht _).le)

theorem operatorColumnFactor_le {R d : ℕ}
    (T : Fin d → Euclidean R →ₗ[ℝ] Euclidean R) {t : ℝ} (ht : 0 < t)
    (y : Euclidean R) (x : Coeff R) : operatorColumnFactor T t y x ≤ periodicGaussian t 0 ^ d := by
  simpa only [operatorColumnFactor, Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
    Finset.prod_le_prod (s := Finset.univ) (fun k _ => (periodicGaussian_pos ht
      (inner ℝ y (T k (integerEmbedding R x)))).le)
      (fun k _ => periodicGaussian_le_zero ht (inner ℝ y (T k (integerEmbedding R x))))

theorem thetaIntegrand_block_factorization {R d m : ℕ}
    (T : Fin d → Matrix (Fin R) (Fin R) ℤ) (X : Fin m → Coeff R) (t : ℝ) (y : Euclidean R) :
    thetaIntegrand (blockCoefficientMatrix T X) t y =
      ∏ j, operatorColumnFactor (fun k => realCoefficientMap (T k)) t y (X j) := by
  unfold thetaIntegrand
  rw [← finProdFinEquiv.prod_comp (fun l : Fin (m * d) =>
    periodicGaussian t (realCoefficientMap (blockCoefficientMatrix T X).transpose y l)),
    Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro j _
  apply Finset.prod_congr rfl
  intro k _
  rw [transpose_coordinate_eq_inner, blockCoefficientMatrix_column, real_inner_comm]

theorem blockCoefficientMatrix_column_norm {R d m : ℕ}
    (T : Fin d → Matrix (Fin R) (Fin R) ℤ) (X : Fin m → Coeff R) {μ U : ℝ}
    (hμ : 0 ≤ μ) (hT : ∀ k, ∀ x : Euclidean R, ‖realCoefficientMap (T k) x‖ ≤ μ * ‖x‖)
    (hX : ∀ j, ‖integerEmbedding R (X j)‖ ≤ U) :
    ∀ l, ‖realColumn (blockCoefficientMatrix T X) l‖ ≤ μ * U := by
  intro l
  obtain ⟨⟨j, k⟩, rfl⟩ := finProdFinEquiv.surjective l
  rw [blockCoefficientMatrix_column]
  exact (hT k _).trans (mul_le_mul_of_nonneg_left (hX j) hμ)

/-- The identity block embeds every sampled coefficient column into the matrix range.
-/
theorem blockCoefficientMatrix_fullRank_of_span {R d m : ℕ}
    (T : Fin d → Matrix (Fin R) (Fin R) ℤ) (X : Fin m → Coeff R)
    (k : Fin d) (hk : T k = 1)
    (hspan : Submodule.span ℝ (Set.range (fun j => integerEmbedding R (X j))) = ⊤) :
    Function.Surjective (realCoefficientMap (blockCoefficientMatrix T X)) := by
  apply LinearMap.range_eq_top.mp
  apply top_unique
  rw [← hspan]
  apply Submodule.span_le.mpr
  rintro x ⟨j, rfl⟩
  have heq := blockCoefficientMatrix_column T X j k
  rw [hk, realCoefficientMap_one, LinearMap.id_apply] at heq
  exact ⟨EuclideanSpace.basisFun (Fin (m * d)) ℝ (finProdFinEquiv (j, k)), heq⟩

end GeometricGaussianLHL
end

end BlockColumns

section ColumnOperatorNorm

/-!
## Operator norm from coefficient-column bounds

The transpose coordinates are the inner products with the columns.
Their squared sum gives the Euclidean operator-norm bound used to choose
the spherical output width.
-/

noncomputable section

namespace GeometricGaussianLHL

theorem coefficient_transpose_norm_le_columns {R M : ℕ}
    (A : Matrix (Fin R) (Fin M) ℤ) {B : ℝ} (hB : 0 ≤ B)
    (hcols : ∀ j, ‖realColumn A j‖ ≤ B) (y : Euclidean R) :
    ‖realCoefficientMap A.transpose y‖ ≤ B * Real.sqrt M * ‖y‖ := by
  have hc (j : Fin M) : |inner ℝ (realColumn A j) y| ≤ B * ‖y‖ :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hcols j) (norm_nonneg y))
  have hs : ‖realCoefficientMap A.transpose y‖ ^ 2 ≤ (M : ℝ) * (B ^ 2 * ‖y‖ ^ 2) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      _ ≤ ∑ _j : Fin M, B ^ 2 * ‖y‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro j _
        rw [transpose_coordinate_eq_inner]
        simpa only [sq_abs, mul_pow] using pow_le_pow_left₀ (abs_nonneg _) (hc j) 2
      _ = _ := by simp
  have hM : (Real.sqrt (M : ℝ)) ^ 2 = M := Real.sq_sqrt (Nat.cast_nonneg M)
  have hr : 0 ≤ B * Real.sqrt M * ‖y‖ := by positivity
  have hl := norm_nonneg (realCoefficientMap A.transpose y)
  have he : (B * Real.sqrt M * ‖y‖) ^ 2 = (M : ℝ) * (B ^ 2 * ‖y‖ ^ 2) := by
    rw [mul_pow, mul_pow, hM]
    ring
  rw [← he] at hs
  exact (sq_le_sq₀ hl hr).mp hs

theorem coefficient_opNorm_le_columns {R M : ℕ}
    (A : Matrix (Fin R) (Fin M) ℤ) {B : ℝ} (hB : 0 ≤ B)
    (hcols : ∀ j, ‖realColumn A j‖ ≤ B) :
    ‖(realCoefficientMap A).toContinuousLinearMap‖ ≤ B * Real.sqrt M := by
  have he : (realCoefficientMap A).toContinuousLinearMap.adjoint =
      (realCoefficientMap A.transpose).toContinuousLinearMap := by
    rw [realCoefficientMap_transpose, LinearMap.adjoint_toContinuousLinearMap]
  rw [← ContinuousLinearMap.adjoint.norm_map (realCoefficientMap A).toContinuousLinearMap, he]
  exact ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    (coefficient_transpose_norm_le_columns A hB hcols)

end GeometricGaussianLHL
end

end ColumnOperatorNorm

section GramDeterminantBound

/-!
## Bounding the Gram determinant by column norms

AM-GM applied to the nonnegative eigenvalues bounds a positive semidefinite determinant by the mean
trace. The trace of the Gram matrix is the sum of squared column norms. This proves the determinant
estimate in the finite geometric smoothing theorem, including singular matrices.
-/

noncomputable section

open scoped BigOperators

namespace GeometricGaussianLHL

theorem finite_product_le_mean_pow {R : ℕ} (hR : 0 < R) (f : Fin R → ℝ)
    (hf : ∀ i, 0 ≤ f i) : (∏ i, f i) ≤ ((∑ i, f i) / R) ^ R := by
  have hRreal : (0 : ℝ) < R := by exact_mod_cast hR
  have hmean := Real.geom_mean_le_arith_mean Finset.univ (fun _ : Fin R => (1 : ℝ)) f
    (by intros; norm_num) (by simpa using hRreal) (fun i _ => hf i)
  simp only [Real.rpow_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, one_mul] at hmean
  have hp : ((∏ i, f i) ^ ((R : ℝ)⁻¹)) ^ R ≤ ((∑ i, f i) / R) ^ R := by
    gcongr
    exact Real.rpow_nonneg (Finset.prod_nonneg (fun i _ => hf i)) _
  rw [Real.rpow_inv_natCast_pow (Finset.prod_nonneg (fun i _ => hf i)) hR.ne'] at hp
  exact hp

theorem positiveSemidefinite_det_le_mean_trace_pow {R : ℕ} (hR : 0 < R)
    (G : Matrix (Fin R) (Fin R) ℝ) (hG : G.PosSemidef) :
    G.det ≤ (G.trace / R) ^ R := by
  have h := finite_product_le_mean_pow hR hG.isHermitian.eigenvalues hG.eigenvalues_nonneg
  rw [hG.isHermitian.det_eq_prod_eigenvalues, hG.isHermitian.trace_eq_sum_eigenvalues]
  change (∏ i, hG.isHermitian.eigenvalues i) ≤ ((∑ i, hG.isHermitian.eigenvalues i) / R) ^ R
  exact h

theorem coefficientGram_posSemidef {R M : ℕ} (A : Matrix (Fin R) (Fin M) ℤ) :
    (A.map (Int.cast : ℤ → ℝ) * A.transpose.map (Int.cast : ℤ → ℝ)).PosSemidef := by
  have h := Matrix.posSemidef_self_mul_conjTranspose (A.map (Int.cast : ℤ → ℝ))
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  exact h

theorem coefficientGram_trace {R M : ℕ} (A : Matrix (Fin R) (Fin M) ℤ) :
    (A.map (Int.cast : ℤ → ℝ) * A.transpose.map (Int.cast : ℤ → ℝ)).trace =
      ∑ j, ‖realColumn A j‖ ^ 2 := by
  simp_rw [EuclideanSpace.real_norm_sq_eq, realColumn_apply]
  simpa only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply,
    Matrix.transpose_apply, pow_two] using
    (Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
      (f := fun (i : Fin R) (j : Fin M) => (A i j : ℝ) * (A i j : ℝ)))

theorem gramDet_sq_le_column_mean {R M : ℕ} (hR : 0 < R)
    (A : Matrix (Fin R) (Fin M) ℤ) :
    gramDet A ^ 2 ≤ ((∑ j, ‖realColumn A j‖ ^ 2) / R) ^ R := by
  rw [gramDet, Real.sq_sqrt (coefficientGram_posSemidef A).det_nonneg]
  rw [← coefficientGram_trace]
  exact positiveSemidefinite_det_le_mean_trace_pow hR _ (coefficientGram_posSemidef A)

theorem gramDet_le_column_bound {R M : ℕ} (hR : 0 < R)
    (A : Matrix (Fin R) (Fin M) ℤ) {B : ℝ} (hB : 0 ≤ B)
    (hcol : ∀ j, ‖realColumn A j‖ ≤ B) :
    gramDet A ≤ (B * Real.sqrt ((M : ℝ) / R)) ^ R := by
  have hsum : (∑ j, ‖realColumn A j‖ ^ 2) ≤ (M : ℝ) * B ^ 2 := by
    calc
      _ ≤ ∑ _j : Fin M, B ^ 2 := by
        apply Finset.sum_le_sum
        intro j _
        exact pow_le_pow_left₀ (norm_nonneg _) (hcol j) _
      _ = _ := by simp
  have hmean : ((∑ j, ‖realColumn A j‖ ^ 2) / R) ^ R ≤ ((M : ℝ) * B ^ 2 / R) ^ R := by
    gcongr
  have hsquare : ((B * Real.sqrt ((M : ℝ) / R)) ^ R) ^ 2 = ((M : ℝ) * B ^ 2 / R) ^ R := by
    rw [← pow_mul, mul_comm R 2, pow_mul, mul_pow,
      Real.sq_sqrt (show 0 ≤ (M : ℝ) / R by positivity)]
    congr 1
    ring
  have hbound := (gramDet_sq_le_column_mean hR A).trans hmean
  rw [← hsquare] at hbound
  have hrhs : 0 ≤ (B * Real.sqrt ((M : ℝ) / R)) ^ R := by positivity
  nlinarith

/-- The finite geometric smoothing theorem's determinant normalization, without a rank hypothesis.
-/
theorem normalized_gramDet_le_column_bound {R M : ℕ} (hR : 0 < R)
    (A : Matrix (Fin R) (Fin M) ℤ) {B t : ℝ} (hB : 0 ≤ B) (ht : 0 ≤ t)
    (hcol : ∀ j, ‖realColumn A j‖ ≤ B) :
    t ^ R * gramDet A ≤ (t * B * Real.sqrt ((M : ℝ) / R)) ^ R := by
  have h := mul_le_mul_of_nonneg_left (gramDet_le_column_bound hR A hB hcol) (pow_nonneg ht R)
  simpa only [← mul_pow, mul_assoc] using h

end GeometricGaussianLHL
end

end GramDeterminantBound

section ThetaExpansion

/-!
## Expanding the periodic Gaussian product

Tonelli's finite-product identity expands the actual theta integrand into a
nonnegative sum over integer coefficient vectors. Finiteness also supplies
the corresponding real-valued identity.
-/

noncomputable section

namespace GeometricGaussianLHL

theorem gaussianWeight_integer_shift_product {M : ℕ} (t : ℝ) (x : Euclidean M)
    (k : Coeff M) :
    gaussianWeight t (integerEmbedding M k - x) =
      ∏ j, Real.exp (-Real.pi * t ^ 2 * ((k j : ℝ) - x j) ^ 2) := by
  rw [gaussianWeight_product]
  simp only [PiLp.sub_apply, integerEmbedding_apply]

/-- Nonnegative expansion, with no convergence prerequisite.
-/
theorem shifted_coefficient_gaussian_tsum_product {M : ℕ} (t : ℝ) (x : Euclidean M) :
    (∑' k : Coeff M, ENNReal.ofReal (gaussianWeight t (integerEmbedding M k - x))) =
      ∏ j, ∑' z : ℤ, ENNReal.ofReal (Real.exp (-Real.pi * t ^ 2 * ((z : ℝ) - x j) ^ 2)) := by
  simp_rw [gaussianWeight_integer_shift_product,
    ENNReal.ofReal_prod_of_nonneg (fun _ _ => (Real.exp_pos _).le)]
  exact tsum_finite_product M (fun j => fun z : ℤ =>
    ENNReal.ofReal (Real.exp (-Real.pi * t ^ 2 * ((z : ℝ) - x j) ^ 2)))

theorem shifted_coefficient_gaussian_mass_ne_top {M : ℕ} (x : Euclidean M)
    {t : ℝ} (ht : 0 < t) :
    (∑' k : Coeff M, ENNReal.ofReal (gaussianWeight t (integerEmbedding M k - x))) ≠ ⊤ := by
  rw [shifted_coefficient_gaussian_tsum_product]
  exact ENNReal.prod_ne_top (fun j _ => (periodicGaussian_summable ht (x j)).tsum_ofReal_ne_top)

theorem summable_shifted_coefficient_gaussian {M : ℕ} (x : Euclidean M)
    {t : ℝ} (ht : 0 < t) :
    Summable (fun k : Coeff M => gaussianWeight t (integerEmbedding M k - x)) := by
  simpa only [ENNReal.toReal_ofReal (gaussianWeight_pos _ _).le] using
    ENNReal.summable_toReal (shifted_coefficient_gaussian_mass_ne_top x ht)

/-- The expansion used at the start of the exact theta-integral proposition's proof. -/
theorem thetaIntegrand_ennreal_eq_tsum {R M : ℕ} (A : Matrix (Fin R) (Fin M) ℤ)
    {t : ℝ} (ht : 0 < t) (y : Euclidean R) :
    ENNReal.ofReal (thetaIntegrand A t y) =
      ∑' k : Coeff M, ENNReal.ofReal
        (gaussianWeight t (integerEmbedding M k - realCoefficientMap A.transpose y)) := by
  rw [shifted_coefficient_gaussian_tsum_product, thetaIntegrand,
    ENNReal.ofReal_prod_of_nonneg (fun _ _ => (periodicGaussian_pos ht _).le)]
  apply Finset.prod_congr rfl
  intro j _
  exact ENNReal.ofReal_tsum_of_nonneg (fun _ => (Real.exp_pos _).le)
    (periodicGaussian_summable ht _)

/-- Absolute convergence makes the real-valued expansion valid as well. -/
theorem thetaIntegrand_eq_tsum {R M : ℕ} (A : Matrix (Fin R) (Fin M) ℤ)
    {t : ℝ} (ht : 0 < t) (y : Euclidean R) :
    thetaIntegrand A t y = ∑' k : Coeff M,
      gaussianWeight t (integerEmbedding M k - realCoefficientMap A.transpose y) := by
  have h := thetaIntegrand_ennreal_eq_tsum A ht y
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => (gaussianWeight_pos _ _).le)
    (summable_shifted_coefficient_gaussian _ ht)] at h
  have hr := congrArg ENNReal.toReal h
  simpa only [ENNReal.toReal_ofReal (thetaIntegrand_nonneg A ht y),
    ENNReal.toReal_ofReal (tsum_nonneg (fun _ => (gaussianWeight_pos _ _).le))] using hr

/-- The product is globally bounded by its value at the origin. -/
theorem thetaIntegrand_le_zero {R M : ℕ} (A : Matrix (Fin R) (Fin M) ℤ)
    {t : ℝ} (ht : 0 < t) (y : Euclidean R) :
    thetaIntegrand A t y ≤ periodicGaussian t 0 ^ M := by
  calc
    thetaIntegrand A t y ≤ ∏ _ : Fin M, periodicGaussian t 0 := by
      apply Finset.prod_le_prod
      · intro j _
        exact (periodicGaussian_pos ht _).le
      · intro j _
        exact periodicGaussian_le_zero ht _
    _ = _ := by simp

end GeometricGaussianLHL
end

end ThetaExpansion

section EllipsoidalGaussian

/-!
## Ellipsoidal discrete Gaussian distributions

The shape is an invertible real linear map `S`. The mass at an integer
vector `z` with centre `c` is proportional to
`exp (-π ‖S⁻¹ (z - c)‖²)`. In particular this includes every symmetric
positive definite shape in the paper. Convergence is proved by comparison
with an isotropic Gaussian, including in dimension zero.
-/

noncomputable section

open scoped ENNReal

namespace GeometricGaussianLHL

variable {R : ℕ}

def ellipsoidWeight (S : Euclidean R ≃L[ℝ] Euclidean R)
    (c : Euclidean R) (z : Coeff R) : ℝ :=
  gaussianWeight 1 (S.symm (integerEmbedding R z - c))

theorem ellipsoidWeight_pos (S : Euclidean R ≃L[ℝ] Euclidean R)
    (c : Euclidean R) (z : Coeff R) : 0 < ellipsoidWeight S c z :=
  gaussianWeight_pos _ _

theorem gaussianWeight_inverse_le (S : Euclidean R ≃L[ℝ] Euclidean R)
    {B : ℝ} (hB : 0 < B) (hS : ‖S.toContinuousLinearMap‖ ≤ B) (x : Euclidean R) :
    gaussianWeight 1 (S.symm x) ≤ gaussianWeight (1 / B) x := by
  have hn : ‖x‖ ≤ B * ‖S.symm x‖ := by
    calc
      ‖x‖ = ‖S (S.symm x)‖ := by rw [S.apply_symm_apply]
      _ ≤ ‖S.toContinuousLinearMap‖ * ‖S.symm x‖ :=
        S.toContinuousLinearMap.le_opNorm _
      _ ≤ B * ‖S.symm x‖ := mul_le_mul_of_nonneg_right hS (norm_nonneg _)
  have hd : ‖x‖ / B ≤ ‖S.symm x‖ := (div_le_iff₀ hB).mpr (by nlinarith [hn])
  have hsq := sq_le_sq₀ (div_nonneg (norm_nonneg _) hB.le) (norm_nonneg _) |>.mpr hd
  unfold gaussianWeight
  apply Real.exp_le_exp.mpr
  simp only [one_pow, mul_one]
  have heq : (1 / B) ^ 2 * ‖x‖ ^ 2 = (‖x‖ / B) ^ 2 := by ring
  calc
    -Real.pi * ‖S.symm x‖ ^ 2 ≤ -Real.pi * (‖x‖ / B) ^ 2 :=
      mul_le_mul_of_nonpos_left hsq (neg_nonpos.mpr Real.pi_pos.le)
    _ = -Real.pi * (1 / B) ^ 2 * ‖x‖ ^ 2 := by rw [← heq]; ring

theorem summable_ellipsoidWeight (S : Euclidean R ≃L[ℝ] Euclidean R)
    (c : Euclidean R) : Summable (ellipsoidWeight S c) := by
  let B : ℝ := max 1 ‖S.toContinuousLinearMap‖
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  apply (summable_shifted_coefficient_gaussian c (one_div_pos.mpr hB)).of_norm_bounded
  intro z
  rw [Real.norm_eq_abs, abs_of_pos (ellipsoidWeight_pos S c z)]
  exact gaussianWeight_inverse_le S hB (le_max_right _ _) _

def ellipsoidPartition (S : Euclidean R ≃L[ℝ] Euclidean R) (c : Euclidean R) : ℝ :=
  ∑' z : Coeff R, ellipsoidWeight S c z

theorem ellipsoidPartition_pos (S : Euclidean R ≃L[ℝ] Euclidean R)
    (c : Euclidean R) : 0 < ellipsoidPartition S c :=
  (ellipsoidWeight_pos S c 0).trans_le
    ((summable_ellipsoidWeight S c).le_tsum 0 (fun _ _ => (ellipsoidWeight_pos _ _ _).le))

theorem ellipsoidWeight_sum_ne_zero (S : Euclidean R ≃L[ℝ] Euclidean R)
    (c : Euclidean R) : (∑' z, ENNReal.ofReal (ellipsoidWeight S c z)) ≠ 0 := by
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => (ellipsoidWeight_pos S c _).le)
    (summable_ellipsoidWeight S c)]
  exact ne_of_gt (ENNReal.ofReal_pos.mpr (ellipsoidPartition_pos S c))

/-- The normalized, centred ellipsoidal Gaussian on actual integer vectors.
-/
def ellipsoidalGaussian (S : Euclidean R ≃L[ℝ] Euclidean R)
    (c : Euclidean R) : PMF (Coeff R) :=
  PMF.normalize (fun z => ENNReal.ofReal (ellipsoidWeight S c z))
    (ellipsoidWeight_sum_ne_zero S c) (summable_ellipsoidWeight S c).tsum_ofReal_ne_top

theorem ellipsoidalGaussian_apply (S : Euclidean R ≃L[ℝ] Euclidean R)
    (c : Euclidean R) (z : Coeff R) :
    ellipsoidalGaussian S c z =
      ENNReal.ofReal (ellipsoidWeight S c z / ellipsoidPartition S c) := by
  simp only [ellipsoidalGaussian, PMF.normalize_apply]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => (ellipsoidWeight_pos S c _).le)
    (summable_ellipsoidWeight S c), ← div_eq_mul_inv]
  change ENNReal.ofReal (ellipsoidWeight S c z) / ENNReal.ofReal (ellipsoidPartition S c) = _
  exact (ENNReal.ofReal_div_of_pos (ellipsoidPartition_pos S c)).symm

@[simp] theorem ellipsoidalGaussian_toReal (S : Euclidean R ≃L[ℝ] Euclidean R)
    (c : Euclidean R) (z : Coeff R) :
    (ellipsoidalGaussian S c z).toReal = ellipsoidWeight S c z / ellipsoidPartition S c := by
  rw [ellipsoidalGaussian_apply, ENNReal.toReal_ofReal
    (div_pos (ellipsoidWeight_pos S c z) (ellipsoidPartition_pos S c)).le]

theorem ellipsoidalGaussian_toReal_pos (S : Euclidean R ≃L[ℝ] Euclidean R)
    (c : Euclidean R) (z : Coeff R) : 0 < (ellipsoidalGaussian S c z).toReal := by
  rw [ellipsoidalGaussian_toReal]
  exact div_pos (ellipsoidWeight_pos S c z) (ellipsoidPartition_pos S c)

theorem ellipsoidWeight_add_center (S : Euclidean R ≃L[ℝ] Euclidean R)
    (c : Euclidean R) (z v : Coeff R) :
    ellipsoidWeight S (c + integerEmbedding R v) (z + v) = ellipsoidWeight S c z := by
  simp [ellipsoidWeight, map_add, add_sub_add_right_eq_sub]

theorem ellipsoidPartition_add_integer (S : Euclidean R ≃L[ℝ] Euclidean R)
    (c : Euclidean R) (v : Coeff R) :
    ellipsoidPartition S (c + integerEmbedding R v) = ellipsoidPartition S c := by
  unfold ellipsoidPartition
  rw [← (Equiv.addRight v).tsum_eq]
  exact tsum_congr (fun z => ellipsoidWeight_add_center S c z v)

theorem ellipsoidalGaussian_add_center (S : Euclidean R ≃L[ℝ] Euclidean R)
    (c : Euclidean R) (z v : Coeff R) :
    ellipsoidalGaussian S (c + integerEmbedding R v) (z + v) =
      ellipsoidalGaussian S c z := by
  rw [ellipsoidalGaussian_apply, ellipsoidalGaussian_apply,
    ellipsoidWeight_add_center, ellipsoidPartition_add_integer]

@[simp] theorem ellipsoidWeight_neg (S : Euclidean R ≃L[ℝ] Euclidean R) (z : Coeff R) :
    ellipsoidWeight S 0 (-z) = ellipsoidWeight S 0 z := by
  simp [ellipsoidWeight, gaussianWeight]

theorem ellipsoidalGaussian_symmetric (S : Euclidean R ≃L[ℝ] Euclidean R)
    (z : Coeff R) : ellipsoidalGaussian S 0 (-z) = ellipsoidalGaussian S 0 z := by
  simp only [ellipsoidalGaussian_apply, ellipsoidWeight_neg]

end GeometricGaussianLHL
end

end EllipsoidalGaussian

section FundamentalCell

/-!
## Unfolding the integer fundamental cell

A translated basis fundamental domain gives the centered half-open unit
cube. Nonnegative periodizations unfold to whole-space integrals.
-/

noncomputable section

open MeasureTheory
open scoped Pointwise

namespace GeometricGaussianLHL

/-- Translation from `[0,1)^R` to the centered fundamental cell.
-/
def cellShift (R : ℕ) : Euclidean R := WithLp.toLp 2 (fun _ => -(1 / 2 : ℝ))

def centeredCell (R : ℕ) : Set (Euclidean R) :=
  cellShift R +ᵥ ZSpan.fundamentalDomain (EuclideanSpace.basisFun (Fin R) ℝ).toBasis

theorem centeredCell_isAddFundamentalDomain (R : ℕ) :
    IsAddFundamentalDomain (integerLattice R) (centeredCell R) volume := by
  rw [integerLattice_eq_basis_span]
  exact (ZSpan.isAddFundamentalDomain (EuclideanSpace.basisFun (Fin R) ℝ).toBasis volume).vadd_of_comm
    (cellShift R)

/-- The boundary convention is explicit: the right face is excluded. -/
theorem mem_centeredCell_iff {R : ℕ} (y : Euclidean R) :
    y ∈ centeredCell R ↔ ∀ i, -(1 / 2 : ℝ) ≤ y i ∧ y i < 1 / 2 := by
  constructor
  · rintro ⟨x, hx, rfl⟩ i
    have hi := hx i
    change 0 ≤ x i ∧ x i < 1 at hi
    change -(1 / 2 : ℝ) ≤ -(1 / 2 : ℝ) + x i ∧ -(1 / 2 : ℝ) + x i < 1 / 2
    constructor <;> linarith [hi.1, hi.2]
  · intro hy
    refine ⟨y - cellShift R, ?_, ?_⟩
    · intro i
      change 0 ≤ y i - -(1 / 2 : ℝ) ∧ y i - -(1 / 2 : ℝ) < 1
      constructor <;> linarith [(hy i).1, (hy i).2]
    · change cellShift R + (y - cellShift R) = y
      abel

theorem centeredCell_measurable (R : ℕ) : MeasurableSet (centeredCell R) := by
  simp_rw [show centeredCell R = {y | ∀ i, -(1 / 2 : ℝ) ≤ y i ∧ y i < 1 / 2} by
    ext y; exact mem_centeredCell_iff y]
  have hcoord (i : Fin R) : Measurable (fun y : Euclidean R => y i) := by fun_prop
  simpa only [Set.ofPred_forall, Set.ofPred_and] using
    MeasurableSet.iInter (fun i : Fin R =>
      (measurableSet_le (measurable_const (a := -(1 / 2 : ℝ))) (hcoord i)).inter
        (measurableSet_lt (hcoord i) (measurable_const (a := (1 / 2 : ℝ)))))

instance integerLattice_vaddInvariantMeasure (R : ℕ) :
    VAddInvariantMeasure (integerLattice R) (Euclidean R) volume :=
  inferInstanceAs (VAddInvariantMeasure (integerLattice R).toAddSubgroup (Euclidean R) volume)

/-- Tonelli unfolding for the actual integer embedding. -/
theorem lintegral_integer_periodization (R : ℕ) (f : Euclidean R → ENNReal)
    (hf : Measurable f) :
    (∫⁻ y in centeredCell R, ∑' z : Coeff R, f (y - integerEmbedding R z)) =
      ∫⁻ y : Euclidean R, f y := by
  rw [lintegral_tsum (f := fun z : Coeff R => fun y : Euclidean R =>
    f (y - integerEmbedding R z)) (fun z =>
      (hf.comp (show Measurable (fun y : Euclidean R => y - integerEmbedding R z) by
        fun_prop)).aemeasurable)]
  let e : Coeff R ≃ₗ[ℤ] integerLattice R :=
    LinearEquiv.ofInjective (integerEmbedding R) (integerEmbedding_injective R)
  let : Countable (integerLattice R) := Countable.of_equiv (Coeff R) e.toEquiv
  have h := (centeredCell_isAddFundamentalDomain R).lintegral_eq_tsum' f
  rw [← e.toEquiv.tsum_eq (fun z : integerLattice R =>
    ∫⁻ y in centeredCell R, f (-z +ᵥ y))] at h
  change (∫⁻ y : Euclidean R, f y) =
    ∑' z : Coeff R, ∫⁻ y in centeredCell R, f (-(integerEmbedding R z) + y) at h
  simpa only [sub_eq_add_neg, add_comm] using h.symm

/-- A face of the centered cube has zero Euclidean volume. -/
theorem coordinate_half_face_volume_zero {R : ℕ} (i : Fin R) :
    volume {y : Euclidean R | y i = (1 / 2 : ℝ)} = 0 := by
  let p : Euclidean R →ₗ[ℝ] ℝ :=
    { toFun := fun y => y i
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let s : AffineSubspace ℝ (Euclidean R) :=
    (affineSpan ℝ ({(1 / 2 : ℝ)} : Set ℝ)).comap p.toAffineMap
  have hs : (s : Set (Euclidean R)) = {y | y i = (1 / 2 : ℝ)} := by
    ext y
    simp [s, p]
    rfl
  have hproper : s ≠ ⊤ := by
    intro h
    have hzero : (0 : Euclidean R) ∈ (s : Set (Euclidean R)) := by rw [h]; trivial
    rw [hs] at hzero
    norm_num at hzero
  rw [← hs]
  exact Measure.addHaar_affineSubspace volume s hproper

/-- Including the right faces does not change any integral. -/
theorem centeredCell_ae_eq_centeredUnitCube (R : ℕ) :
    centeredCell R =ᵐ[volume] centeredUnitCube R := by
  have hface (i : Fin R) : ∀ᵐ y : Euclidean R, y i ≠ (1 / 2 : ℝ) := by
    rw [ae_iff]
    simpa only [not_not] using coordinate_half_face_volume_zero i
  have hall : ∀ᵐ y : Euclidean R, ∀ i, y i ≠ (1 / 2 : ℝ) :=
    ae_all_iff.mpr hface
  filter_upwards [hall] with y hy
  apply propext
  rw [mem_centeredCell_iff]
  change (∀ i, -(1 / 2 : ℝ) ≤ y i ∧ y i < 1 / 2) ↔ ∀ i, |y i| ≤ 1 / 2
  constructor
  · intro h i
    exact abs_le.mpr ⟨(h i).1, (h i).2.le⟩
  · intro h i
    exact ⟨(abs_le.mp (h i)).1, lt_of_le_of_ne (abs_le.mp (h i)).2 (hy i)⟩

/-- Unfolding over the closed cube `Q_R` used in the paper. -/
theorem lintegral_integer_periodization_cube (R : ℕ) (f : Euclidean R → ENNReal)
    (hf : Measurable f) :
    (∫⁻ y in centeredUnitCube R, ∑' z : Coeff R, f (y - integerEmbedding R z)) =
      ∫⁻ y : Euclidean R, f y := by
  rw [← Measure.restrict_congr_set (centeredCell_ae_eq_centeredUnitCube R)]
  exact lintegral_integer_periodization R f hf

theorem centeredUnitCube_volume (R : ℕ) : volume (centeredUnitCube R) = 1 := by
  have hset : centeredUnitCube R = (WithLp.ofLp : Euclidean R → (Fin R → ℝ)) ⁻¹'
      Set.pi Set.univ (fun _ => Set.Icc (-(1 / 2 : ℝ)) (1 / 2)) := by
    ext y
    simp [centeredUnitCube, abs_le, Pi.le_def, forall_and]
  rw [hset, (PiLp.volume_preserving_ofLp (Fin R)).measure_preimage
    (MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Icc)).nullMeasurableSet, volume_pi_pi]
  norm_num

/-- The actual torus integrand is integrable for every positive parameter. -/
theorem thetaIntegrand_integrableOn_cube {R M : ℕ} (A : Matrix (Fin R) (Fin M) ℤ)
    {t : ℝ} (ht : 0 < t) : IntegrableOn (thetaIntegrand A t) (centeredUnitCube R) := by
  have hc : IntegrableOn (fun _ : Euclidean R => periodicGaussian t 0 ^ M) (centeredUnitCube R) :=
    integrableOn_const (by rw [centeredUnitCube_volume]; exact ENNReal.one_ne_top)
  apply hc.mono' (thetaIntegrand_measurable A t).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun y => by
    rw [Real.norm_eq_abs, abs_of_nonneg (thetaIntegrand_nonneg A ht y)]
    exact thetaIntegrand_le_zero A ht y)

end GeometricGaussianLHL
end

end FundamentalCell

section GaussianProducts

/-!
## Isotropic coefficient Gaussians are product distributions

Both the weights and their infinite normalizing sums factor. The result is
an equality of actual PMFs, so independence is supplied by the existing
finite-product construction.
-/

noncomputable section

open scoped ENNReal

namespace GeometricGaussianLHL

theorem gaussianWeight_integerGaussian_product {n : ℕ} (s : ℝ) (z : Coeff n) :
    ENNReal.ofReal (gaussianWeight (1 / s) (integerEmbedding n z)) =
      ∏ i, integerGaussianWeight s (z i) := by
  rw [gaussianWeight_integer_product,
    ENNReal.ofReal_prod_of_nonneg (fun _ _ => (Real.exp_pos _).le)]
  apply Finset.prod_congr rfl
  intro i hi
  unfold integerGaussianWeight
  congr 2
  ring

theorem ellipsoidalGaussian_eq_product_of_isotropic_weight {n : ℕ}
    (S : Euclidean n ≃L[ℝ] Euclidean n) {s : ℝ} (hs : 0 < s)
    (hweight : ∀ z : Coeff n, ellipsoidWeight S 0 z = gaussianWeight (1 / s) (integerEmbedding n z)) :
    ellipsoidalGaussian S 0 = productIntegerGaussian n s hs := by
  classical
  ext z
  simp only [ellipsoidalGaussian, PMF.normalize_apply, hweight, gaussianWeight_integerGaussian_product]
  rw [tsum_finite_product n (fun _ => integerGaussianWeight s), ← div_eq_mul_inv]
  simp only [productIntegerGaussian, independentProduct_apply, integerGaussian_apply,
    div_eq_mul_inv, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ENNReal.inv_pow]

end GeometricGaussianLHL
end

end GaussianProducts

section GaussianTilting

/-!
## Exponential tilting and first moments

Completing the square gives the exact moment generating function as a
ratio of convergent ellipsoidal Gaussian partition sums. This identity
does not assume a sub-Gaussian estimate. It also proves absolute
integrability and zero mean of every linear functional of the centred law.
-/

noncomputable section

namespace GeometricGaussianLHL

variable {R : ℕ}

def gaussianTiltCenter (S : Euclidean R ≃L[ℝ] Euclidean R)
    (h : Euclidean R) : Euclidean R :=
  S ((1 / (2 * Real.pi)) • S.toContinuousLinearMap.adjoint h)

theorem gaussian_complete_square (y a : Euclidean R) :
    inner ℝ a y - Real.pi * ‖y‖ ^ 2 =
      ‖a‖ ^ 2 / (4 * Real.pi) -
        Real.pi * ‖y - (1 / (2 * Real.pi)) • a‖ ^ 2 := by
  rw [norm_sub_sq_real, real_inner_smul_right, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs, real_inner_comm y a]
  field_simp
  ring

theorem ellipsoidWeight_tilt (S : Euclidean R ≃L[ℝ] Euclidean R)
    (h : Euclidean R) (z : Coeff R) :
    Real.exp (inner ℝ h (integerEmbedding R z)) * ellipsoidWeight S 0 z =
      Real.exp (‖S.toContinuousLinearMap.adjoint h‖ ^ 2 / (4 * Real.pi)) *
        ellipsoidWeight S (gaussianTiltCenter S h) z := by
  have hin : inner ℝ (S.toContinuousLinearMap.adjoint h)
      (S.symm (integerEmbedding R z)) = inner ℝ h (integerEmbedding R z) := by
    simpa only [ContinuousLinearEquiv.coe_coe, S.apply_symm_apply] using
      S.toContinuousLinearMap.adjoint_inner_left (S.symm (integerEmbedding R z)) h
  simp only [ellipsoidWeight, gaussianWeight, sub_zero, one_pow, mul_one,
    gaussianTiltCenter, map_sub, S.symm_apply_apply, ← Real.exp_add]
  congr 1
  rw [← hin]
  convert gaussian_complete_square (S.symm (integerEmbedding R z))
    (S.toContinuousLinearMap.adjoint h) using 1 <;> ring

theorem summable_ellipsoidWeight_exp (S : Euclidean R ≃L[ℝ] Euclidean R)
    (h : Euclidean R) : Summable (fun z : Coeff R =>
      Real.exp (inner ℝ h (integerEmbedding R z)) * ellipsoidWeight S 0 z) := by
  simp_rw [ellipsoidWeight_tilt]
  exact (summable_ellipsoidWeight S (gaussianTiltCenter S h)).mul_left _

theorem summable_ellipsoidalGaussian_exp (S : Euclidean R ≃L[ℝ] Euclidean R)
    (h : Euclidean R) : Summable (fun z : Coeff R =>
      (ellipsoidalGaussian S 0 z).toReal * Real.exp (inner ℝ h (integerEmbedding R z))) := by
  simpa only [ellipsoidalGaussian_toReal, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    using (summable_ellipsoidWeight_exp S h).div_const (ellipsoidPartition S 0)

/-- Exact exponential moment; the remaining Gaussian estimate is a bound
on the numerator partition function at the displayed centre.
-/
theorem ellipsoidalGaussian_exp_moment (S : Euclidean R ≃L[ℝ] Euclidean R)
    (h : Euclidean R) :
    (∑' z : Coeff R, (ellipsoidalGaussian S 0 z).toReal *
      Real.exp (inner ℝ h (integerEmbedding R z))) =
      Real.exp (‖S.toContinuousLinearMap.adjoint h‖ ^ 2 / (4 * Real.pi)) *
        (ellipsoidPartition S (gaussianTiltCenter S h) / ellipsoidPartition S 0) := by
  simp only [ellipsoidalGaussian_toReal]
  simp_rw [div_mul_eq_mul_div, mul_comm (ellipsoidWeight S 0 _), ellipsoidWeight_tilt]
  rw [tsum_div_const, tsum_mul_left]
  unfold ellipsoidPartition
  ring

theorem abs_le_exp_add_exp_neg (x : ℝ) : |x| ≤ Real.exp x + Real.exp (-x) := by
  apply abs_le.mpr
  constructor
  · linarith [Real.add_one_le_exp (-x), Real.exp_pos x]
  · linarith [Real.add_one_le_exp x, Real.exp_pos (-x)]

theorem summable_ellipsoidalGaussian_linear (S : Euclidean R ≃L[ℝ] Euclidean R)
    (h : Euclidean R) : Summable (fun z : Coeff R =>
      (ellipsoidalGaussian S 0 z).toReal * inner ℝ h (integerEmbedding R z)) := by
  apply ((summable_ellipsoidalGaussian_exp S h).add
    (summable_ellipsoidalGaussian_exp S (-h))).of_norm_bounded
  intro z
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (ellipsoidalGaussian_toReal_pos S 0 z),
    inner_neg_left, ← mul_add]
  exact mul_le_mul_of_nonneg_left (abs_le_exp_add_exp_neg _)
    (ellipsoidalGaussian_toReal_pos S 0 z).le

/-- Symmetry, together with the proved summability, gives genuine zero mean. -/
theorem ellipsoidalGaussian_linear_mean_zero (S : Euclidean R ≃L[ℝ] Euclidean R)
    (h : Euclidean R) :
    (∑' z : Coeff R, (ellipsoidalGaussian S 0 z).toReal *
      inner ℝ h (integerEmbedding R z)) = 0 := by
  have he := (Equiv.neg (Coeff R)).tsum_eq (fun z : Coeff R =>
    (ellipsoidalGaussian S 0 z).toReal * inner ℝ h (integerEmbedding R z))
  simp only [Equiv.neg_apply, ellipsoidalGaussian_symmetric, map_neg,
    inner_neg_right, mul_neg, tsum_neg] at he
  linarith

end GeometricGaussianLHL
end

end GaussianTilting

section ComplexPeriodization

/-!
## Complex-valued unfolding on the integer fundamental cell

Absolute integrability justifies exchanging the lattice sum and the
Bochner integral. A periodic complex factor then turns the Fourier
coefficient of a periodization into a whole-space Fourier integral.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal Pointwise

namespace GeometricGaussianLHL

variable {n : ℕ}

theorem integral_integer_periodization_complex (f : Euclidean n → ℂ)
    (hf : Continuous f) (hi : Integrable f) :
    (∫ x in centeredCell n, ∑' z : Coeff n, f (x - integerEmbedding n z)) = ∫ x, f x := by
  have hmeas (z : Coeff n) : Continuous (fun x => f (x - integerEmbedding n z)) := by fun_prop
  have hsum : (∑' z : Coeff n, ∫⁻ x in centeredCell n, ‖f (x - integerEmbedding n z)‖ₑ) ≠ ⊤ := by
    rw [← lintegral_tsum (fun z => (hmeas z).measurable.enorm.aemeasurable)]
    rw [lintegral_integer_periodization n (fun x => ‖f x‖ₑ) hf.measurable.enorm]
    exact hi.hasFiniteIntegral.ne
  rw [integral_tsum (fun z => (hmeas z).aestronglyMeasurable) hsum]
  let e : Coeff n ≃ₗ[ℤ] integerLattice n :=
    LinearEquiv.ofInjective (integerEmbedding n) (integerEmbedding_injective n)
  let : Countable (integerLattice n) := Countable.of_equiv (Coeff n) e.toEquiv
  have h := (centeredCell_isAddFundamentalDomain n).integral_eq_tsum' f hi
  rw [← e.toEquiv.tsum_eq (fun z : integerLattice n =>
    ∫ x in centeredCell n, f (-z +ᵥ x))] at h
  change (∫ x, f x) = ∑' z : Coeff n, ∫ x in centeredCell n, f (-(integerEmbedding n z) + x) at h
  simpa only [sub_eq_add_neg, add_comm] using h.symm

theorem integral_periodic_mul_periodization_complex (g : Euclidean n → ℂ) (f : Euclidean n → ℝ)
    (hg : Continuous g) (hf : Continuous f) (hi : Integrable (fun x => g x * (f x : ℂ)))
    (hper : ∀ x (z : Coeff n), g (x - integerEmbedding n z) = g x) :
    (∫ x in centeredCell n, g x * (∑' z : Coeff n, f (x - integerEmbedding n z) : ℝ)) =
      ∫ x, g x * (f x : ℂ) := by
  rw [← integral_integer_periodization_complex (fun x => g x * (f x : ℂ)) (by fun_prop) hi]
  simp only [hper, tsum_mul_left, ← Complex.ofReal_tsum]

end GeometricGaussianLHL
end

end ComplexPeriodization

section EllipsoidPeriodization

/-!
## Periodized ellipsoidal Gaussian kernels

The partition function is a measurable, bounded, integer-periodic function
of its centre. Its square is integrable on the fundamental cell. These
facts justify the autocorrelation proof of its maximum at the origin.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal Pointwise

namespace GeometricGaussianLHL

variable {R : ℕ}

def ellipsoidKernel (S : Euclidean R ≃L[ℝ] Euclidean R) (x : Euclidean R) : ℝ :=
  gaussianWeight 1 (S.symm x)

@[simp] theorem ellipsoidKernel_neg (S : Euclidean R ≃L[ℝ] Euclidean R)
    (x : Euclidean R) : ellipsoidKernel S (-x) = ellipsoidKernel S x := by
  simp [ellipsoidKernel, gaussianWeight]

theorem ellipsoidWeight_eq_kernel (S : Euclidean R ≃L[ℝ] Euclidean R)
    (c : Euclidean R) (z : Coeff R) :
    ellipsoidWeight S c z = ellipsoidKernel S (c - integerEmbedding R z) := by
  change ellipsoidKernel S (integerEmbedding R z - c) = _
  rw [← neg_sub c, ellipsoidKernel_neg]

theorem ellipsoidPartition_eq_tsum_kernel (S : Euclidean R ≃L[ℝ] Euclidean R)
    (c : Euclidean R) :
    ellipsoidPartition S c = ∑' z : Coeff R, ellipsoidKernel S (c - integerEmbedding R z) := by
  simp only [ellipsoidPartition, ellipsoidWeight_eq_kernel]

@[fun_prop] theorem ellipsoidKernel_measurable (S : Euclidean R ≃L[ℝ] Euclidean R) :
    Measurable (ellipsoidKernel S) := by
  unfold ellipsoidKernel gaussianWeight
  fun_prop

@[fun_prop] theorem ellipsoidPartition_measurable (S : Euclidean R ≃L[ℝ] Euclidean R) :
    Measurable (ellipsoidPartition S) := by
  unfold ellipsoidPartition
  apply Measurable.tsum
  intro z
  unfold ellipsoidWeight gaussianWeight
  fun_prop

/-- Multiplying the inverse shape by `t` narrows the Gaussian by that factor.
-/
def scaledInverseShape (S : Euclidean R ≃L[ℝ] Euclidean R) (t : ℝ) (ht : t ≠ 0) :
    Euclidean R ≃L[ℝ] Euclidean R :=
  (S.symm.trans (ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := Euclidean R)
    (Units.mk0 t ht))).symm

@[simp] theorem scaledInverseShape_symm_apply (S : Euclidean R ≃L[ℝ] Euclidean R)
    (t : ℝ) (ht : t ≠ 0) (x : Euclidean R) :
    (scaledInverseShape S t ht).symm x = t • S.symm x := rfl

theorem ellipsoidKernel_scaled (S : Euclidean R ≃L[ℝ] Euclidean R)
    (t : ℝ) (ht : t ≠ 0) (x : Euclidean R) :
    ellipsoidKernel (scaledInverseShape S t ht) x = gaussianWeight t (S.symm x) := by
  simp only [ellipsoidKernel, scaledInverseShape_symm_apply, gaussianWeight,
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  congr 1
  ring

theorem shifted_coefficient_gaussian_tsum {t : ℝ} (ht : 0 < t) (c : Euclidean R) :
    (∑' z : Coeff R, gaussianWeight t (integerEmbedding R z - c)) =
      ∏ i, periodicGaussian t (c i) := by
  apply (ENNReal.ofReal_eq_ofReal_iff
    (tsum_nonneg (fun _ => (gaussianWeight_pos _ _).le))
    (Finset.prod_nonneg (fun i _ => (periodicGaussian_pos ht (c i)).le))).mp
  rw [ENNReal.ofReal_tsum_of_nonneg (fun _ => (gaussianWeight_pos _ _).le)
    (summable_shifted_coefficient_gaussian c ht), shifted_coefficient_gaussian_tsum_product,
    ENNReal.ofReal_prod_of_nonneg (fun i _ => (periodicGaussian_pos ht (c i)).le)]
  apply Finset.prod_congr rfl
  intro i _
  exact (ENNReal.ofReal_tsum_of_nonneg (fun _ => (Real.exp_pos _).le)
    (periodicGaussian_summable ht (c i))).symm

theorem ellipsoidPartition_uniform_bound (S : Euclidean R ≃L[ℝ] Euclidean R)
    {B : ℝ} (hB : 0 < B) (hS : ‖S.toContinuousLinearMap‖ ≤ B) (c : Euclidean R) :
    ellipsoidPartition S c ≤ periodicGaussian (1 / B) 0 ^ R := by
  calc
    ellipsoidPartition S c ≤ ∑' z : Coeff R, gaussianWeight (1 / B) (integerEmbedding R z - c) :=
      (summable_ellipsoidWeight S c).tsum_le_tsum
        (fun z => gaussianWeight_inverse_le S hB hS _)
        (summable_shifted_coefficient_gaussian c (one_div_pos.mpr hB))
    _ = ∏ i, periodicGaussian (1 / B) (c i) :=
      shifted_coefficient_gaussian_tsum (one_div_pos.mpr hB) c
    _ ≤ ∏ _ : Fin R, periodicGaussian (1 / B) 0 := by
      apply Finset.prod_le_prod
      · intro i _; exact (periodicGaussian_pos (one_div_pos.mpr hB) (c i)).le
      · intro i _; exact periodicGaussian_le_zero (one_div_pos.mpr hB) (c i)
    _ = _ := by simp

theorem ellipsoidPartition_bounded (S : Euclidean R ≃L[ℝ] Euclidean R) :
    ∃ C : ℝ, 0 < C ∧ ∀ c, ellipsoidPartition S c ≤ C := by
  let B : ℝ := max 1 ‖S.toContinuousLinearMap‖
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  exact ⟨periodicGaussian (1 / B) 0 ^ R,
    pow_pos (periodicGaussian_pos (one_div_pos.mpr hB) 0) _,
    ellipsoidPartition_uniform_bound S hB (le_max_right _ _)⟩

theorem centeredCell_volume (R : ℕ) : volume (centeredCell R) = 1 := by
  rw [measure_congr (centeredCell_ae_eq_centeredUnitCube R), centeredUnitCube_volume]

theorem ellipsoidPartition_product_integrableOn (S : Euclidean R ≃L[ℝ] Euclidean R)
    (c : Euclidean R) : IntegrableOn
      (fun x => ellipsoidPartition S x * ellipsoidPartition S (x - c)) (centeredCell R) := by
  obtain ⟨C, hC, hbound⟩ := ellipsoidPartition_bounded S
  have hc : IntegrableOn (fun _ : Euclidean R => C * C) (centeredCell R) :=
    integrableOn_const (by rw [centeredCell_volume]; exact ENNReal.one_ne_top)
  apply hc.mono' (by fun_prop)
  apply Filter.Eventually.of_forall
  intro x
  rw [Real.norm_eq_abs, abs_of_pos (mul_pos (ellipsoidPartition_pos S x)
    (ellipsoidPartition_pos S (x - c)))]
  exact mul_le_mul (hbound x) (hbound (x - c)) (ellipsoidPartition_pos S _).le hC.le

theorem ellipsoidPartition_square_integrableOn (S : Euclidean R ≃L[ℝ] Euclidean R) :
    IntegrableOn (fun x => ellipsoidPartition S x ^ 2) (centeredCell R) := by
  simpa only [sub_zero, pow_two] using ellipsoidPartition_product_integrableOn S 0

end GeometricGaussianLHL
end

end EllipsoidPeriodization

section ContinuousGaussianMoment

/-!
## Continuous Gaussian exponential moments

These exact Lebesgue integral identities supply the auxiliary Gaussian integration in the elementary
Gaussian estimates lemma's norm-tail argument. All integral exchanges in that argument can therefore
be reduced to nonnegative Tonelli integrals.
-/

noncomputable section

open MeasureTheory

namespace GeometricGaussianLHL

variable {R : ℕ}

theorem gaussian_density_tilt (x h : Euclidean R) :
    gaussianWeight 1 x * Real.exp (inner ℝ h x) =
      Real.exp (‖h‖ ^ 2 / (4 * Real.pi)) *
        gaussianWeight 1 (x - (1 / (2 * Real.pi)) • h) := by
  simp only [gaussianWeight, one_pow, mul_one, ← Real.exp_add]
  apply congrArg Real.exp
  have hh := gaussian_complete_square x h
  linarith

theorem integral_gaussian_exp_inner (h : Euclidean R) :
    (∫ x, gaussianWeight 1 x * Real.exp (inner ℝ h x)) =
      Real.exp (‖h‖ ^ 2 / (4 * Real.pi)) := by
  simp_rw [gaussian_density_tilt]
  rw [integral_const_mul, integral_sub_right_eq_self (gaussianWeight 1)
    ((1 / (2 * Real.pi)) • h), integral_gaussianWeight (by norm_num : (0 : ℝ) < 1)]
  simp

theorem integrable_gaussian_exp_inner (h : Euclidean R) :
    Integrable (fun x => gaussianWeight 1 x * Real.exp (inner ℝ h x)) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_gaussian_exp_inner]
  exact (Real.exp_pos _).ne'

theorem gaussian_auxiliary_exponent {b : ℝ} (hb : 0 < b) (x : Euclidean R) :
    ‖(Real.pi * Real.sqrt 2 / b) • x‖ ^ 2 / (4 * Real.pi) =
      Real.pi * ‖x‖ ^ 2 / (2 * b ^ 2) := by
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, div_pow,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  field_simp
  ring

theorem integral_gaussian_auxiliary {b : ℝ} (hb : 0 < b) (z : Euclidean R) :
    (∫ x : Euclidean R, gaussianWeight 1 x *
      Real.exp (inner ℝ ((Real.pi * Real.sqrt 2 / b) • x) z)) =
        Real.exp (Real.pi * ‖z‖ ^ 2 / (2 * b ^ 2)) := by
  have he (x : Euclidean R) : inner ℝ ((Real.pi * Real.sqrt 2 / b) • x) z =
      inner ℝ ((Real.pi * Real.sqrt 2 / b) • z) x := by
    simp only [real_inner_smul_left, real_inner_comm x z]
  simp_rw [he]
  rw [integral_gaussian_exp_inner, gaussian_auxiliary_exponent hb]

theorem lintegral_gaussian_auxiliary {b : ℝ} (hb : 0 < b) (z : Euclidean R) :
    (∫⁻ x : Euclidean R, ENNReal.ofReal (gaussianWeight 1 x) *
      ENNReal.ofReal (Real.exp (inner ℝ ((Real.pi * Real.sqrt 2 / b) • x) z))) =
        ENNReal.ofReal (Real.exp (Real.pi * ‖z‖ ^ 2 / (2 * b ^ 2))) := by
  have hi : Integrable (fun x : Euclidean R => gaussianWeight 1 x *
      Real.exp (inner ℝ ((Real.pi * Real.sqrt 2 / b) • x) z)) := by
    apply Integrable.of_integral_ne_zero
    rw [integral_gaussian_auxiliary hb z]
    exact (Real.exp_pos _).ne'
  simp_rw [← ENNReal.ofReal_mul (gaussianWeight_pos _ _).le]
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall
    (fun x => mul_nonneg (gaussianWeight_pos _ _).le (Real.exp_pos _).le)),
    integral_gaussian_auxiliary hb z]

theorem gaussian_auxiliary_majorant {b : ℝ} (hb : 0 < b) (x : Euclidean R) :
    gaussianWeight 1 x * Real.exp
      (b ^ 2 * ‖(Real.pi * Real.sqrt 2 / b) • x‖ ^ 2 / (4 * Real.pi)) =
        gaussianWeight (1 / Real.sqrt 2) x := by
  rw [mul_div_assoc, gaussian_auxiliary_exponent hb]
  have he : b ^ 2 * (Real.pi * ‖x‖ ^ 2 / (2 * b ^ 2)) = Real.pi * ‖x‖ ^ 2 / 2 := by
    field_simp
  rw [he]
  simp only [gaussianWeight, ← Real.exp_add, one_pow, mul_one, div_pow,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  apply congrArg Real.exp
  ring

theorem integral_half_gaussian (R : ℕ) :
    (∫ x : Euclidean R, gaussianWeight (1 / Real.sqrt 2) x) = Real.sqrt 2 ^ R := by
  rw [integral_gaussianWeight (one_div_pos.mpr (Real.sqrt_pos.mpr (by norm_num)))]
  simp only [Euclidean, finrank_euclideanSpace, Fintype.card_fin, one_div, inv_pow, inv_inv]

end GeometricGaussianLHL
end

end ContinuousGaussianMoment

section EllipsoidContinuity

/-!
## Continuity of the periodized Gaussian

On a bounded set of whitened centres, each shifted weight is bounded by a
fixed multiple of a wider centred Gaussian. Its summable majorant gives
local uniform convergence and continuity of the actual partition sum.
-/

noncomputable section

open scoped Topology

namespace GeometricGaussianLHL

/-- A shift costs a constant factor and a factor of two in the precision.
-/
theorem gaussianWeight_shift_half_le {E : Type*} [NormedAddCommGroup E]
    (x c : E) : gaussianWeight 1 (x - c) ≤
      Real.exp (Real.pi * ‖c‖ ^ 2) * gaussianWeight (1 / Real.sqrt 2) x := by
  have hn : ‖x‖ ≤ ‖x - c‖ + ‖c‖ := by
    simpa only [sub_add_cancel] using norm_add_le (x - c) c
  have hs : ‖x‖ ^ 2 ≤ 2 * (‖x - c‖ ^ 2 + ‖c‖ ^ 2) := by
    nlinarith [norm_nonneg x, norm_nonneg (x - c), norm_nonneg c,
      sq_nonneg (‖x - c‖ - ‖c‖)]
  have ht : (1 / Real.sqrt 2) ^ 2 = (1 / 2 : ℝ) := by
    norm_num [div_pow, Real.sq_sqrt]
  simp only [gaussianWeight, one_pow, mul_one, ht, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hm := mul_le_mul_of_nonneg_left hs Real.pi_pos.le
  nlinarith only [hm]

variable {n : ℕ}

theorem ellipsoidWeight_uniform_majorant (S : Euclidean n ≃L[ℝ] Euclidean n)
    {B : ℝ} (hB : 0 ≤ B) (c : Euclidean n) (hc : ‖S.symm c‖ ≤ B) (z : Coeff n) :
    ellipsoidWeight S c z ≤ Real.exp (Real.pi * B ^ 2) *
      ellipsoidWeight (scaledInverseShape S (1 / Real.sqrt 2) (by positivity)) 0 z := by
  change gaussianWeight 1 (S.symm (integerEmbedding n z - c)) ≤ _
  rw [map_sub]
  apply (gaussianWeight_shift_half_le _ _).trans
  have he : Real.exp (Real.pi * ‖S.symm c‖ ^ 2) ≤ Real.exp (Real.pi * B ^ 2) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left ((sq_le_sq₀ (norm_nonneg _) hB).mpr hc) Real.pi_pos.le
  have hk : ellipsoidWeight (scaledInverseShape S (1 / Real.sqrt 2) (by positivity)) 0 z =
      gaussianWeight (1 / Real.sqrt 2) (S.symm (integerEmbedding n z)) := by
    rw [ellipsoidWeight, sub_zero]
    exact ellipsoidKernel_scaled S _ _ _
  rw [hk]
  exact mul_le_mul_of_nonneg_right he (gaussianWeight_pos _ _).le

theorem ellipsoidPartition_continuousOn_inverse_ball (S : Euclidean n ≃L[ℝ] Euclidean n)
    {B : ℝ} (hB : 0 ≤ B) :
    ContinuousOn (ellipsoidPartition S) {c | ‖S.symm c‖ ≤ B} := by
  unfold ellipsoidPartition
  apply continuousOn_tsum (fun z => (show Continuous (fun c => ellipsoidWeight S c z) by
    unfold ellipsoidWeight gaussianWeight
    fun_prop).continuousOn)
    ((summable_ellipsoidWeight (scaledInverseShape S (1 / Real.sqrt 2) (by positivity)) 0).mul_left
      (Real.exp (Real.pi * B ^ 2)))
  intro z c hc
  rw [Real.norm_eq_abs, abs_of_pos (ellipsoidWeight_pos _ _ _)]
  exact ellipsoidWeight_uniform_majorant S hB c hc z

@[fun_prop] theorem ellipsoidPartition_continuous (S : Euclidean n ≃L[ℝ] Euclidean n) :
    Continuous (ellipsoidPartition S) := by
  rw [continuous_iff_continuousAt]
  intro c
  have hB : 0 ≤ ‖S.symm c‖ + 1 := by positivity
  apply (ellipsoidPartition_continuousOn_inverse_ball S hB).continuousAt
  have hc : {x : Euclidean n | ‖S.symm x‖ < ‖S.symm c‖ + 1} ∈ 𝓝 c :=
    (isOpen_lt (by fun_prop) continuous_const).mem_nhds (by simp)
  refine Filter.mem_of_superset hc ?_
  intro x hx
  change ‖S.symm x‖ ≤ ‖S.symm c‖ + 1
  exact (show ‖S.symm x‖ < ‖S.symm c‖ + 1 from hx).le

end GeometricGaussianLHL
end

end EllipsoidContinuity

section GaussianConvolution

/-!
## Gaussian convolution with exact normalization

The product of two narrower Gaussian kernels separates into a Gaussian
in the displacement and a Gaussian about the midpoint. Integration gives
the positive constant used in the periodized autocorrelation identity.
-/

noncomputable section

open MeasureTheory

namespace GeometricGaussianLHL

variable {R : ℕ}

def narrowGaussianShape (S : Euclidean R ≃L[ℝ] Euclidean R) :
    Euclidean R ≃L[ℝ] Euclidean R :=
  scaledInverseShape S (Real.sqrt 2) (ne_of_gt (Real.sqrt_pos.mpr (by norm_num)))

theorem gaussian_midpoint_factor (x c : Euclidean R) :
    gaussianWeight (Real.sqrt 2) x * gaussianWeight (Real.sqrt 2) (x - c) =
      gaussianWeight 1 c * gaussianWeight 2 (x - (1 / 2 : ℝ) • c) := by
  simp only [gaussianWeight, ← Real.exp_add]
  apply congrArg Real.exp
  simp only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
    one_pow, mul_one, norm_sub_sq_real, real_inner_smul_right, norm_smul,
    Real.norm_eq_abs]
  norm_num
  ring

theorem ellipsoidKernel_midpoint_factor (S : Euclidean R ≃L[ℝ] Euclidean R)
    (x c : Euclidean R) :
    ellipsoidKernel (narrowGaussianShape S) x *
      ellipsoidKernel (narrowGaussianShape S) (x - c) =
        ellipsoidKernel S c * gaussianWeight 2 (S.symm (x - (1 / 2 : ℝ) • c)) := by
  simp only [narrowGaussianShape, ellipsoidKernel_scaled, map_sub, map_smul]
  exact gaussian_midpoint_factor (S.symm x) (S.symm c)

def gaussianConvolutionFactor (S : Euclidean R ≃L[ℝ] Euclidean R) : ℝ :=
  ((2 : ℝ) ^ R * S.symm.toLinearMap.normDet)⁻¹

theorem gaussianConvolutionFactor_pos (S : Euclidean R ≃L[ℝ] Euclidean R) :
    0 < gaussianConvolutionFactor S :=
  inv_pos.mpr (mul_pos (pow_pos (by norm_num) _)
    (normDet_pos_of_injective S.symm.toLinearMap S.symm.injective))

theorem integral_ellipsoidKernel_convolution (S : Euclidean R ≃L[ℝ] Euclidean R)
    (c : Euclidean R) :
    (∫ x, ellipsoidKernel (narrowGaussianShape S) x *
      ellipsoidKernel (narrowGaussianShape S) (x - c)) =
        ellipsoidKernel S c * gaussianConvolutionFactor S := by
  simp_rw [ellipsoidKernel_midpoint_factor]
  rw [integral_const_mul, integral_sub_right_eq_self
    (fun x : Euclidean R => gaussianWeight 2 (S.symm x)) ((1 / 2 : ℝ) • c)]
  congr 1
  change (∫ x : Euclidean R, gaussianWeight 2 (S.symm.toLinearMap x)) = _
  rw [integral_gaussianWeight_comp_injective S.symm.toLinearMap S.symm.injective
    (by norm_num : (0 : ℝ) < 2)]
  simp only [Euclidean, finrank_euclideanSpace, Fintype.card_fin, gaussianConvolutionFactor]

theorem integrable_ellipsoidKernel_convolution (S : Euclidean R ≃L[ℝ] Euclidean R)
    (c : Euclidean R) : Integrable (fun x => ellipsoidKernel (narrowGaussianShape S) x *
      ellipsoidKernel (narrowGaussianShape S) (x - c)) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_ellipsoidKernel_convolution]
  exact (mul_pos (gaussianWeight_pos _ _) (gaussianConvolutionFactor_pos S)).ne'

theorem lintegral_ellipsoidKernel_convolution (S : Euclidean R ≃L[ℝ] Euclidean R)
    (c : Euclidean R) :
    (∫⁻ x, ENNReal.ofReal (ellipsoidKernel (narrowGaussianShape S) x *
      ellipsoidKernel (narrowGaussianShape S) (x - c))) =
        ENNReal.ofReal (ellipsoidKernel S c * gaussianConvolutionFactor S) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_ellipsoidKernel_convolution S c)
    (Filter.Eventually.of_forall (fun x => mul_nonneg (gaussianWeight_pos _ _).le
      (gaussianWeight_pos _ _).le)), integral_ellipsoidKernel_convolution]

end GeometricGaussianLHL
end

end GaussianConvolution

section PeriodicIntegration

/-!
## Periodic integration on the integer fundamental cell

Unfolding is compatible with multiplication by a periodic weight. The
square integral of a periodic partition function is translation invariant,
so its autocorrelation is largest at zero by the elementary square inequality.
-/

noncomputable section

open MeasureTheory
open scoped Pointwise ENNReal

namespace GeometricGaussianLHL

variable {R : ℕ}

theorem ofReal_ellipsoidPartition (S : Euclidean R ≃L[ℝ] Euclidean R)
    (c : Euclidean R) :
    ENNReal.ofReal (ellipsoidPartition S c) =
      ∑' z : Coeff R, ENNReal.ofReal (ellipsoidKernel S (c - integerEmbedding R z)) := by
  rw [ellipsoidPartition, ENNReal.ofReal_tsum_of_nonneg
    (fun _ => (ellipsoidWeight_pos _ _ _).le) (summable_ellipsoidWeight S c)]
  simp only [ellipsoidWeight_eq_kernel]

theorem lintegral_periodic_mul_periodization (f g : Euclidean R → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g)
    (hper : ∀ x (z : Coeff R), f (x - integerEmbedding R z) = f x) :
    (∫⁻ x in centeredCell R, f x * ∑' z : Coeff R, g (x - integerEmbedding R z)) =
      ∫⁻ x, f x * g x := by
  rw [← lintegral_integer_periodization R (fun x => f x * g x) (hf.mul hg)]
  simp only [hper, ENNReal.tsum_mul_left]

theorem ellipsoidPartition_sub_integer (S : Euclidean R ≃L[ℝ] Euclidean R)
    (x : Euclidean R) (z : Coeff R) :
    ellipsoidPartition S (x - integerEmbedding R z) = ellipsoidPartition S x := by
  simpa only [map_neg, sub_eq_add_neg] using ellipsoidPartition_add_integer S x (-z)

theorem ellipsoidPartition_shift_square_integrableOn
    (S : Euclidean R ≃L[ℝ] Euclidean R) (c : Euclidean R) :
    IntegrableOn (fun x => ellipsoidPartition S (x - c) ^ 2) (centeredCell R) := by
  obtain ⟨C, hC, hb⟩ := ellipsoidPartition_bounded S
  have hc : IntegrableOn (fun _ : Euclidean R => C ^ 2) (centeredCell R) :=
    integrableOn_const (by rw [centeredCell_volume]; exact ENNReal.one_ne_top)
  apply hc.mono' (show Measurable (fun x => ellipsoidPartition S (x - c) ^ 2) by
    fun_prop).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact (sq_le_sq₀ (ellipsoidPartition_pos S _).le hC.le).mpr (hb _)

theorem ellipsoidPartition_square_integral_translate
    (S : Euclidean R ≃L[ℝ] Euclidean R) (c : Euclidean R) :
    (∫ x in centeredCell R, ellipsoidPartition S (x - c) ^ 2) =
      ∫ x in centeredCell R, ellipsoidPartition S x ^ 2 := by
  let e : Coeff R ≃ₗ[ℤ] integerLattice R :=
    LinearEquiv.ofInjective (integerEmbedding R) (integerEmbedding_injective R)
  let : Countable (integerLattice R) := Countable.of_equiv (Coeff R) e.toEquiv
  have hfd := centeredCell_isAddFundamentalDomain R
  have hper : ∀ (z : integerLattice R) (x : Euclidean R),
      ellipsoidPartition S (z +ᵥ x) ^ 2 = ellipsoidPartition S x ^ 2 := by
    intro z x
    obtain ⟨k, hk⟩ := z.property
    change ellipsoidPartition S ((z : Euclidean R) + x) ^ 2 = _
    rw [← hk, add_comm, ellipsoidPartition_add_integer]
  have htr := (measurePreserving_add_left (volume : Measure (Euclidean R)) (-c)).setIntegral_image_emb
    (MeasurableEquiv.addLeft (-c)).measurableEmbedding
    (fun x => ellipsoidPartition S x ^ 2) (centeredCell R)
  have himage : (fun x : Euclidean R => -c + x) '' centeredCell R =
      -c +ᵥ centeredCell R := rfl
  rw [himage] at htr
  calc
    (∫ x in centeredCell R, ellipsoidPartition S (x - c) ^ 2) =
        ∫ x in centeredCell R, ellipsoidPartition S (-c + x) ^ 2 := by
      simp only [sub_eq_add_neg, add_comm]
    _ = ∫ x in -c +ᵥ centeredCell R, ellipsoidPartition S x ^ 2 := htr.symm
    _ = ∫ x in centeredCell R, ellipsoidPartition S x ^ 2 :=
      (hfd.setIntegral_eq (hfd.vadd_of_comm (-c)) hper).symm

theorem ellipsoidPartition_autocorrelation_le_zero
    (S : Euclidean R ≃L[ℝ] Euclidean R) (c : Euclidean R) :
    (∫ x in centeredCell R, ellipsoidPartition S x * ellipsoidPartition S (x - c)) ≤
      ∫ x in centeredCell R, ellipsoidPartition S x ^ 2 := by
  have hp := ellipsoidPartition_product_integrableOn S c
  have h₀ := ellipsoidPartition_square_integrableOn S
  have hc := ellipsoidPartition_shift_square_integrableOn S c
  have hh := integral_mono (hp.const_mul 2) (h₀.add hc) (fun x =>
    show 2 * (ellipsoidPartition S x * ellipsoidPartition S (x - c)) ≤
      ellipsoidPartition S x ^ 2 + ellipsoidPartition S (x - c) ^ 2 by
        nlinarith [sq_nonneg (ellipsoidPartition S x - ellipsoidPartition S (x - c))])
  simp only [Pi.add_apply] at hh
  rw [integral_const_mul, integral_add h₀ hc,
    ellipsoidPartition_square_integral_translate] at hh
  linarith

end GeometricGaussianLHL
end

end PeriodicIntegration

section EllipsoidTorus

/-!
## The Gaussian partition function on the integer torus

The coordinate quotient map is an open quotient map. Equality in its
fibers is exactly equality modulo an integer vector, so the continuous
periodic Gaussian partition descends to the actual product torus.
-/

noncomputable section

namespace GeometricGaussianLHL

variable {n : ℕ}

def integerTorusMk (x : Euclidean n) : UnitAddTorus (Fin n) := fun i => (x i : UnitAddCircle)

theorem integerTorusMk_isOpenQuotientMap : IsOpenQuotientMap (@integerTorusMk n) := by
  exact (IsOpenQuotientMap.piMap (fun _ : Fin n =>
    (QuotientAddGroup.isOpenQuotientMap_mk :
      IsOpenQuotientMap (fun x : ℝ => (x : UnitAddCircle))))).comp
    (PiLp.homeomorph 2 (fun _ : Fin n => ℝ)).isOpenQuotientMap

@[fun_prop] theorem integerTorusMk_continuous : Continuous (@integerTorusMk n) :=
  integerTorusMk_isOpenQuotientMap.continuous

theorem integerTorusMk_eq_iff (x y : Euclidean n) :
    integerTorusMk x = integerTorusMk y ↔ ∃ z : Coeff n, x = y + integerEmbedding n z := by
  constructor
  · intro h
    have hi (i : Fin n) : ∃ z : ℤ, (z : ℝ) = x i - y i := by
      have hz : ((x i - y i : ℝ) : UnitAddCircle) = 0 := by
        rw [AddCircle.coe_sub]
        exact sub_eq_zero.mpr (congrFun h i)
      simpa only [zsmul_eq_mul, mul_one] using (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hz
    choose z hz using hi
    refine ⟨z, ?_⟩
    ext i
    change x i = y i + (z i : ℝ)
    linarith [hz i]
  · rintro ⟨z, rfl⟩
    funext i
    change (((y i + (z i : ℝ) : ℝ) : UnitAddCircle)) = _
    rw [AddCircle.coe_add]
    have hz : ((z i : ℝ) : UnitAddCircle) = 0 :=
      (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨z i, by simp⟩
    rw [hz, add_zero]
    rfl

def integerTorusRepresentative (x : UnitAddTorus (Fin n)) : Euclidean n :=
  WithLp.toLp 2 (fun i => (AddCircle.equivIoc 1 0 (x i) : ℝ))

@[simp] theorem integerTorusMk_representative (x : UnitAddTorus (Fin n)) :
    integerTorusMk (integerTorusRepresentative x) = x := by
  funext i
  exact AddCircle.coe_equivIoc

theorem ellipsoidPartition_eq_of_torus_eq (S : Euclidean n ≃L[ℝ] Euclidean n)
    {x y : Euclidean n} (h : integerTorusMk x = integerTorusMk y) :
    ellipsoidPartition S x = ellipsoidPartition S y := by
  obtain ⟨z, rfl⟩ := (integerTorusMk_eq_iff x y).mp h
  exact ellipsoidPartition_add_integer S y z

def ellipsoidTorusPartition (S : Euclidean n ≃L[ℝ] Euclidean n)
    (x : UnitAddTorus (Fin n)) : ℝ := ellipsoidPartition S (integerTorusRepresentative x)

@[simp] theorem ellipsoidTorusPartition_mk (S : Euclidean n ≃L[ℝ] Euclidean n)
    (x : Euclidean n) : ellipsoidTorusPartition S (integerTorusMk x) = ellipsoidPartition S x :=
  ellipsoidPartition_eq_of_torus_eq S (integerTorusMk_representative _)

@[fun_prop] theorem ellipsoidTorusPartition_continuous (S : Euclidean n ≃L[ℝ] Euclidean n) :
    Continuous (ellipsoidTorusPartition S) := by
  apply integerTorusMk_isOpenQuotientMap.continuous_comp_iff.mp
  simpa only [Function.comp_def, ellipsoidTorusPartition_mk] using ellipsoidPartition_continuous S

def ellipsoidTorus (S : Euclidean n ≃L[ℝ] Euclidean n) : C(UnitAddTorus (Fin n), ℂ) :=
  ⟨fun x => (ellipsoidTorusPartition S x : ℂ), by fun_prop⟩

@[simp] theorem ellipsoidTorus_mk (S : Euclidean n ≃L[ℝ] Euclidean n) (x : Euclidean n) :
    ellipsoidTorus S (integerTorusMk x) = (ellipsoidPartition S x : ℂ) := by
  exact congrArg (fun t : ℝ => (t : ℂ)) (ellipsoidTorusPartition_mk S x)

end GeometricGaussianLHL
end

end EllipsoidTorus

section EllipsoidMaximum

/-!
## Maximum of the ellipsoidal partition function

Unfolding the autocorrelation of a narrower periodized Gaussian gives a positive constant times the
original partition function. The square inequality proves the maximum at zero. Combined with exact
exponential tilting, this proves the second estimate in the elementary Gaussian estimates lemma
without requiring a separate multidimensional Poisson summation theorem.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace GeometricGaussianLHL

variable {R : ℕ}

theorem lintegral_ellipsoidPartition_autocorrelation
    (S : Euclidean R ≃L[ℝ] Euclidean R) (c : Euclidean R) :
    (∫⁻ x in centeredCell R, ENNReal.ofReal
      (ellipsoidPartition (narrowGaussianShape S) x *
        ellipsoidPartition (narrowGaussianShape S) (x - c))) =
      ENNReal.ofReal (gaussianConvolutionFactor S * ellipsoidPartition S c) := by
  let T := narrowGaussianShape S
  let f : Euclidean R → ℝ≥0∞ := fun x => ENNReal.ofReal (ellipsoidPartition T (x - c))
  let g : Euclidean R → ℝ≥0∞ := fun x => ENNReal.ofReal (ellipsoidKernel T x)
  have hf : Measurable f := by dsimp [f]; fun_prop
  have hg : Measurable g := by dsimp [g]; fun_prop
  have hper : ∀ x (z : Coeff R), f (x - integerEmbedding R z) = f x := by
    intro x z
    dsimp [f]
    rw [show x - integerEmbedding R z - c = (x - c) - integerEmbedding R z by abel,
      ellipsoidPartition_sub_integer]
  have hpoint (x : Euclidean R) : f x * g x = ∑' z : Coeff R,
      ENNReal.ofReal (ellipsoidKernel T x * ellipsoidKernel T (x - (c + integerEmbedding R z))) := by
    dsimp [f, g]
    rw [ofReal_ellipsoidPartition, ← ENNReal.tsum_mul_right]
    apply tsum_congr
    intro z
    rw [sub_add_eq_sub_sub, ENNReal.ofReal_mul
      (show 0 ≤ ellipsoidKernel T x from (gaussianWeight_pos _ _).le), mul_comm]
  calc
    (∫⁻ x in centeredCell R, ENNReal.ofReal
        (ellipsoidPartition T x * ellipsoidPartition T (x - c))) =
        ∫⁻ x in centeredCell R, f x * ∑' z : Coeff R, g (x - integerEmbedding R z) := by
      apply lintegral_congr
      intro x
      rw [ENNReal.ofReal_mul (ellipsoidPartition_pos T x).le, ofReal_ellipsoidPartition T x]
      exact mul_comm _ _
    _ = ∫⁻ x, f x * g x := lintegral_periodic_mul_periodization f g hf hg hper
    _ = ∑' z : Coeff R, ∫⁻ x, ENNReal.ofReal
        (ellipsoidKernel T x * ellipsoidKernel T (x - (c + integerEmbedding R z))) := by
      simp_rw [hpoint]
      exact lintegral_tsum (fun z => by fun_prop)
    _ = ∑' z : Coeff R, ENNReal.ofReal
        (ellipsoidKernel S (c + integerEmbedding R z) * gaussianConvolutionFactor S) := by
      apply tsum_congr
      intro z
      exact lintegral_ellipsoidKernel_convolution S (c + integerEmbedding R z)
    _ = ENNReal.ofReal (gaussianConvolutionFactor S * ellipsoidPartition S c) := by
      rw [← (Equiv.neg (Coeff R)).tsum_eq]
      simp only [Equiv.neg_apply, map_neg, ← sub_eq_add_neg]
      simp_rw [ENNReal.ofReal_mul
        (show 0 ≤ ellipsoidKernel S _ from (gaussianWeight_pos _ _).le)]
      rw [ENNReal.tsum_mul_right, ← ofReal_ellipsoidPartition]
      rw [ENNReal.ofReal_mul (gaussianConvolutionFactor_pos S).le, mul_comm]

theorem ellipsoidPartition_autocorrelation
    (S : Euclidean R ≃L[ℝ] Euclidean R) (c : Euclidean R) :
    (∫ x in centeredCell R, ellipsoidPartition (narrowGaussianShape S) x *
      ellipsoidPartition (narrowGaussianShape S) (x - c)) =
        gaussianConvolutionFactor S * ellipsoidPartition S c := by
  apply (ENNReal.ofReal_eq_ofReal_iff
    (integral_nonneg (fun x => mul_nonneg (ellipsoidPartition_pos _ _).le
      (ellipsoidPartition_pos _ _).le))
    (mul_pos (gaussianConvolutionFactor_pos S) (ellipsoidPartition_pos S c)).le).mp
  rw [ofReal_integral_eq_lintegral_ofReal
    (ellipsoidPartition_product_integrableOn (narrowGaussianShape S) c)
    (Filter.Eventually.of_forall (fun x => mul_nonneg (ellipsoidPartition_pos _ _).le
      (ellipsoidPartition_pos _ _).le))]
  exact lintegral_ellipsoidPartition_autocorrelation S c

/-- The shifted Gaussian partition is largest at zero, in every dimension
and for every invertible real shape. -/
theorem ellipsoidPartition_le_zero (S : Euclidean R ≃L[ℝ] Euclidean R)
    (c : Euclidean R) : ellipsoidPartition S c ≤ ellipsoidPartition S 0 := by
  have hh := ellipsoidPartition_autocorrelation_le_zero (narrowGaussianShape S) c
  have h₀ : (∫ x in centeredCell R, ellipsoidPartition (narrowGaussianShape S) x ^ 2) =
      gaussianConvolutionFactor S * ellipsoidPartition S 0 := by
    simpa only [sub_zero, pow_two] using ellipsoidPartition_autocorrelation S 0
  rw [ellipsoidPartition_autocorrelation S c, h₀] at hh
  nlinarith [gaussianConvolutionFactor_pos S]

/-- Exponential-moment bound for arbitrary shapes, expressed using the adjoint. -/
theorem ellipsoidalGaussian_exp_moment_le (S : Euclidean R ≃L[ℝ] Euclidean R)
    (h : Euclidean R) :
    (∑' z : Coeff R, (ellipsoidalGaussian S 0 z).toReal *
      Real.exp (inner ℝ h (integerEmbedding R z))) ≤
        Real.exp (‖S.toContinuousLinearMap.adjoint h‖ ^ 2 / (4 * Real.pi)) := by
  rw [ellipsoidalGaussian_exp_moment]
  exact mul_le_of_le_one_right (Real.exp_pos _).le
    ((div_le_one (ellipsoidPartition_pos S 0)).mpr (ellipsoidPartition_le_zero S _))

/-- The elementary Gaussian estimates lemma, second estimate, for the paper's self-adjoint shapes.
-/
theorem ellipsoidalGaussian_exp_moment_le_selfAdjoint
    (S : Euclidean R ≃L[ℝ] Euclidean R) (hS : IsSelfAdjoint S.toContinuousLinearMap)
    (h : Euclidean R) :
    (∑' z : Coeff R, (ellipsoidalGaussian S 0 z).toReal *
      Real.exp (inner ℝ h (integerEmbedding R z))) ≤ Real.exp (‖S h‖ ^ 2 / (4 * Real.pi)) := by
  have he : S.toContinuousLinearMap.adjoint h = S h := by rw [hS.adjoint_eq]; rfl
  simpa only [he] using ellipsoidalGaussian_exp_moment_le S h

end GeometricGaussianLHL
end

end EllipsoidMaximum

section TorusCharacters

/-!
## Integer Fourier characters in Euclidean coordinates

Product-torus monomials agree with the Euclidean Fourier character at the
actual integer frequency. Their modulus is one, and they are invariant
under every integer translation.
-/

noncomputable section

namespace GeometricGaussianLHL

variable {n : ℕ}

theorem mFourier_integerTorusMk (z : Coeff n) (x : Euclidean n) :
    UnitAddTorus.mFourier z (integerTorusMk x) =
      (Real.fourierChar (inner ℝ x (integerEmbedding n z)) : ℂ) := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, integerTorusMk,
    fourier_coe_apply, Complex.ofReal_one, div_one, Real.fourierChar_apply]
  rw [← Complex.exp_sum]
  congr 1
  simp only [PiLp.inner_apply, RCLike.inner_apply, integerEmbedding_apply,
    conj_trivial, Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_sum,
    Complex.ofReal_intCast, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem mFourier_norm_apply (z : Coeff n) (x : UnitAddTorus (Fin n)) :
    ‖UnitAddTorus.mFourier z x‖ = 1 := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, norm_prod,
    fourier_apply, Circle.norm_coe, Finset.prod_const_one]

theorem mFourier_integer_periodic (z k : Coeff n) (x : Euclidean n) :
    UnitAddTorus.mFourier z (integerTorusMk (x - integerEmbedding n k)) =
      UnitAddTorus.mFourier z (integerTorusMk x) := by
  congr 1
  apply (integerTorusMk_eq_iff _ _).mpr
  refine ⟨-k, ?_⟩
  simp only [map_neg, sub_eq_add_neg]

theorem mFourier_neg_integerTorusMk (z : Coeff n) (x : Euclidean n) :
    UnitAddTorus.mFourier (-z) (integerTorusMk x) =
      (Real.fourierChar (-inner ℝ x (integerEmbedding n z)) : ℂ) := by
  rw [mFourier_integerTorusMk, map_neg, inner_neg_right]

end GeometricGaussianLHL
end

end TorusCharacters

section TorusIntegration

/-!
## Torus Fourier coefficients in Euclidean coordinates

The product-torus Haar integral is transported to the actual Euclidean
fundamental cell. The two half-open boundary conventions differ only on
null coordinate hyperplanes, including in dimension zero.
-/

noncomputable section

open MeasureTheory

namespace GeometricGaussianLHL

variable {n : ℕ}

theorem coordinate_face_volume_zero (i : Fin n) (a : ℝ) :
    volume {x : Euclidean n | x i = a} = 0 := by
  let p : Euclidean n →ₗ[ℝ] ℝ :=
    { toFun := fun x => x i
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let s : AffineSubspace ℝ (Euclidean n) :=
    (affineSpan ℝ ({a} : Set ℝ)).comap p.toAffineMap
  have hs : (s : Set (Euclidean n)) = {x | x i = a} := by
    ext x
    simp [s, p]
    rfl
  have hp : s ≠ ⊤ := by
    intro h
    have hx : WithLp.toLp 2 (fun _ : Fin n => a + 1) ∈ (s : Set (Euclidean n)) := by rw [h]; trivial
    rw [hs] at hx
    change a + 1 = a at hx
    linarith
  rw [← hs]
  exact Measure.addHaar_affineSubspace volume s hp

def centeredIocCell (n : ℕ) : Set (Euclidean n) :=
  {x | ∀ i, -(1 / 2 : ℝ) < x i ∧ x i ≤ 1 / 2}

theorem centeredCell_ae_eq_centeredIocCell (n : ℕ) :
    centeredCell n =ᵐ[volume] centeredIocCell n := by
  have hface (i : Fin n) (a : ℝ) : ∀ᵐ x : Euclidean n, x i ≠ a := by
    rw [ae_iff]
    simpa only [not_not] using coordinate_face_volume_zero i a
  have hlo := ae_all_iff.mpr (fun i : Fin n => hface i (-(1 / 2 : ℝ)))
  have hhi := ae_all_iff.mpr (fun i : Fin n => hface i (1 / 2 : ℝ))
  filter_upwards [hlo, hhi] with x hxlo hxhi
  apply propext
  rw [mem_centeredCell_iff]
  change (∀ i, -(1 / 2 : ℝ) ≤ x i ∧ x i < 1 / 2) ↔
    ∀ i, -(1 / 2 : ℝ) < x i ∧ x i ≤ 1 / 2
  constructor
  · intro h i
    exact ⟨lt_of_le_of_ne (h i).1 (hxlo i).symm, (h i).2.le⟩
  · intro h i
    exact ⟨(h i).1.le, lt_of_le_of_ne (h i).2 (hxhi i)⟩

theorem mFourierCoeff_eq_centeredCell (f : UnitAddTorus (Fin n) → ℂ) (z : Coeff n) :
    UnitAddTorus.mFourierCoeff f z =
      ∫ x in centeredCell n, UnitAddTorus.mFourier (-z) (integerTorusMk x) * f (integerTorusMk x) := by
  let U : Set (Fin n → ℝ) := {x | ∀ i, -(1 / 2 : ℝ) < x i ∧ x i ≤ 1 / 2}
  let g : (Fin n → ℝ) → ℂ := fun x =>
    UnitAddTorus.mFourier (-z) (fun i => (x i : UnitAddCircle)) * f (fun i => (x i : UnitAddCircle))
  have h := UnitAddTorus.mFourierCoeff_eq_integral f z (fun _ => -(1 / 2 : ℝ))
  norm_num only [neg_add_cancel, show -(1 / 2 : ℝ) + 1 = 1 / 2 by norm_num, smul_eq_mul] at h
  change UnitAddTorus.mFourierCoeff f z = ∫ x in U, g x at h
  rw [h]
  have hm := (PiLp.volume_preserving_ofLp (Fin n)).setIntegral_preimage_emb
    (PiLp.homeomorph 2 (fun _ : Fin n => ℝ)).measurableEmbedding g U
  change (∫ x in centeredIocCell n, UnitAddTorus.mFourier (-z) (integerTorusMk x) *
    f (integerTorusMk x)) = ∫ x in U, g x at hm
  rw [← hm, ← Measure.restrict_congr_set (centeredCell_ae_eq_centeredIocCell n)]

end GeometricGaussianLHL
end

end TorusIntegration
