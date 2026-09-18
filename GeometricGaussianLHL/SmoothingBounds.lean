import GeometricGaussianLHL.LatticeGeometry
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Round
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Polynomial.Degree.Support
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Rat.Lemmas
import Mathlib.FieldTheory.Separable
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.Order.Lattice.Nat
import Mathlib.Probability.Distributions.Uniform
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Localization.Rat
import Mathlib.RingTheory.Polynomial.Tower
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Module
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Order.IntermediateValue

/-!
# Smoothing bounds and natural scales

This module collects the following proof sections, in dependency order.
- Changing the target error on the same event (`ErrorExtension`).
- Coefficient-kernel smoothing certificates (`CoefficientSmoothingBounds`).
- The normalized canonical kernel covolume (`KernelNaturalScale`).
- The covolume lower bound for smoothing (`SmoothingCovolume`).
- The deterministic natural-scale lower bound (`KernelNaturalLower`).
-/

section ErrorExtension

/-!
## Changing the target error on the same event

The error-extension inequality and the epsilon extensions in the polynomial-width and constant-width
smoothing theorems. These statements use the actual infinite nonzero dual Gaussian mass.
-/

open scoped ENNReal

noncomputable section

namespace GeometricGaussianLHL

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem nonzeroDualMass_mul_sqrt_le (L : Submodule ℤ E) (t : ℝ)
    {q : ℝ} (hq : 1 ≤ q) :
    nonzeroDualMass L (t * Real.sqrt q) ≤ (nonzeroDualMass L t) ^ q := by
  classical
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  calc
    nonzeroDualMass L (t * Real.sqrt q) =
        ∑' v : latticeDual L,
          (if v = 0 then 0 else ENNReal.ofReal (gaussianWeight t (v : E))) ^ q := by
      unfold nonzeroDualMass
      apply tsum_congr
      intro v
      by_cases hv : v = 0
      · simp [hv, ENNReal.zero_rpow_of_pos hqpos]
      · simp only [hv, ite_false, gaussianWeight_mul_sqrt t q hqpos.le]
        exact (ENNReal.ofReal_rpow_of_pos (gaussianWeight_pos t (v : E))).symm
    _ ≤ (nonzeroDualMass L t) ^ q := tsum_rpow_le_rpow_tsum _ hq

theorem SmoothAt.power {L : Submodule ℤ E} {ε t q : ℝ}
    (h : SmoothAt L ε t) (hε : 0 ≤ ε) (hq : 1 ≤ q) :
    SmoothAt L (ε ^ q) (t * Real.sqrt q) := by
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  refine ⟨mul_pos h.1 (Real.sqrt_pos.mpr hqpos), ?_⟩
  calc
    nonzeroDualMass L (t * Real.sqrt q) ≤ nonzeroDualMass L t ^ q :=
      nonzeroDualMass_mul_sqrt_le L t hq
    _ ≤ (ENNReal.ofReal ε) ^ q := ENNReal.rpow_le_rpow h.2 hqpos.le
    _ = ENNReal.ofReal (ε ^ q) := ENNReal.ofReal_rpow_of_nonneg hε hqpos.le

def errorExponent (ε₀ ε : ℝ) : ℝ :=
  max 1 (Real.log (1 / ε) / Real.log (1 / ε₀))

theorem one_le_errorExponent (ε₀ ε : ℝ) : 1 ≤ errorExponent ε₀ ε := le_max_left _ _

theorem rpow_errorExponent_le {ε₀ ε : ℝ} (h₀ : 0 < ε₀) (h₁ : ε₀ < 1)
    (hε : 0 < ε) : ε₀ ^ errorExponent ε₀ ε ≤ ε := by
  have hlog : 0 < Real.log (1 / ε₀) := Real.log_pos ((lt_div_iff₀ h₀).mpr (by simpa))
  have hq := (div_le_iff₀ hlog).mp (le_max_right 1
    (Real.log (1 / ε) / Real.log (1 / ε₀)))
  change Real.log (1 / ε) ≤ errorExponent ε₀ ε * Real.log (1 / ε₀) at hq
  rw [Real.log_div one_ne_zero hε.ne', Real.log_one, zero_sub,
    Real.log_div one_ne_zero h₀.ne', Real.log_one, zero_sub] at hq
  rw [Real.rpow_def_of_pos h₀]
  apply (Real.le_log_iff_exp_le hε).mp
  nlinarith

/-- One certified smoothing parameter gives every requested positive error,
without any new exceptional event. -/
theorem SmoothAt.error_extension {L : Submodule ℤ E} {ε₀ ε t : ℝ}
    (h : SmoothAt L ε₀ t) (h₀ : 0 < ε₀) (h₁ : ε₀ < 1) (hε : 0 < ε) :
    SmoothAt L ε (t * Real.sqrt (errorExponent ε₀ ε)) :=
  (h.power h₀.le (one_le_errorExponent ε₀ ε)).mono_error
    (rpow_errorExponent_le h₀ h₁ hε)

theorem smoothingParameter_error_extension {L : Submodule ℤ E} {ε₀ ε t : ℝ}
    (h : SmoothAt L ε₀ t) (h₀ : 0 < ε₀) (h₁ : ε₀ < 1) (hε : 0 < ε) :
    smoothingParameter L ε ≤ t * Real.sqrt (errorExponent ε₀ ε) :=
  smoothingParameter_le_of_smoothAt (h.error_extension h₀ h₁ hε)

end GeometricGaussianLHL
end

end ErrorExtension

section CoefficientSmoothingBounds

/-!
## Coefficient-kernel smoothing certificates
-/

namespace GeometricGaussianLHL

/-- The coefficient-kernel lower bound of the projected-dual-vector proposition is unconditional:
every integer matrix with more columns than rows has this smoothing bound.
-/
theorem coefficientKernel_smoothing_lower {R M : ℕ}
    (A : Matrix (Fin R) (Fin M) ℤ) (hRM : R < M) {ε : ℝ} (hε : 0 < ε) :
    Real.sqrt (Real.log (2 / ε) / Real.pi) ≤ smoothingParameter (euclideanKernel A) ε := by
  obtain ⟨v, hv, hv0, hvnorm⟩ := exists_short_coefficientKernel_dual A hRM
  have hv0' : (⟨v, hv⟩ : latticeDual (euclideanKernel A)) ≠ 0 := by
    intro h
    exact hv0 (congrArg Subtype.val h)
  simpa using smoothingParameter_lower_of_dual_vector (coefficientKernel_exists_smoothAt A hε)
    hε (by norm_num : (0 : ℝ) < 1) ⟨v, hv⟩ hv0' hvnorm

/-- Two-sided smoothing bounds for the actual coefficient kernel, after a
base smoothing estimate has been established. The lower bound uses a
projected integer vector, and all upper bounds hold on the same event as the
base estimate. `polynomial_matrix_certificate` supplies this upper estimate
for the polynomial-width coefficient model. `numberField_polynomial_certificate`
identifies this model with the actual number-field law and canonical metric;
`numberField_constantWidth_certificate` supplies the constant-width model. -/
theorem coefficientKernel_smoothing_bounds {R M : ℕ}
    (A : Matrix (Fin R) (Fin M) ℤ) (hRM : R < M) {ε₀ t : ℝ}
    (hbase : SmoothAt (euclideanKernel A) ε₀ t)
    (h₀ : 0 < ε₀) (h₁ : ε₀ < 1) {ε : ℝ} (hε : 0 < ε) :
    Real.sqrt (Real.log (2 / ε) / Real.pi) ≤ smoothingParameter (euclideanKernel A) ε ∧
      smoothingParameter (euclideanKernel A) ε ≤
        t * Real.sqrt (errorExponent ε₀ ε) := by
  have hext := hbase.error_extension h₀ h₁ hε
  exact ⟨coefficientKernel_smoothing_lower A hRM hε, smoothingParameter_le_of_smoothAt hext⟩

end GeometricGaussianLHL

end CoefficientSmoothingBounds

section KernelNaturalScale

/-!
## The normalized canonical kernel covolume

For positive kernel dimension, the covolume root splits into the square
root of the root discriminant and the normalized transverse Jacobian.
The latter is bounded by the operator norm to the power `r / (m - r)`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Module NumberField

namespace GeometricGaussianLHL

theorem kernelGram_det_eq_orthonormalMatrix {E F ι κ : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (o : OrthonormalBasis ι ℝ E) (p : OrthonormalBasis κ ℝ F) (f : E →ₗ[ℝ] F) :
    (f.comp f.adjoint).det =
      (LinearMap.toMatrix o.toBasis p.toBasis f *
        (LinearMap.toMatrix o.toBasis p.toBasis f).transpose).det := by
  rw [← LinearMap.det_toMatrix p.toBasis,
    LinearMap.toMatrix_comp p.toBasis o.toBasis p.toBasis,
    LinearMap.toMatrix_adjoint, Matrix.conjTranspose_eq_transpose_of_trivial]

variable (K : Type*) [Field K] [NumberField K] {d r m : ℕ}

local instance naturalScaleEmbeddingsFintype : Fintype (K →+* ℂ) := inferInstance
local instance naturalScaleAmbientInner : InnerProductSpace ℝ (CanonicalAmbient K) := inferInstance
local instance naturalScaleSpaceInner : InnerProductSpace ℝ (canonicalSpace K) := inferInstance
local instance naturalScalePowerInner (n : ℕ) : InnerProductSpace ℝ (CanonicalPower K n) := inferInstance

theorem canonical_discriminant_normalization (b : Basis (Fin d) ℤ (𝓞 K))
    {n : ℕ} (hn : 0 < n) :
    (Real.sqrt |(NumberField.discr K : ℝ)| ^ n) ^ (1 / ((d * n : ℕ) : ℝ)) =
      Real.sqrt (NumberField.rootDiscr K) := by
  have hd : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (integralBasis_dimension_pos K b).ne'
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  rw [← Real.rpow_natCast_mul (Real.sqrt_nonneg _), Real.sqrt_eq_rpow,
    ← Real.rpow_mul (abs_nonneg _), NumberField.rootDiscr_def,
    ← integralBasis_degree K b, Int.cast_abs, Real.sqrt_eq_rpow,
    ← Real.rpow_mul (abs_nonneg _)]
  congr 1
  push_cast
  field_simp

theorem canonicalKernel_normalized_covolume (b : Basis (Fin d) ℤ (𝓞 K))
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) (hX : Function.Surjective X.mulVec) (hmr : r < m) :
    intrinsicCovolume (canonicalKernel K X) ^ (1 / ((d * (m - r) : ℕ) : ℝ)) =
      Real.sqrt (NumberField.rootDiscr K) *
        ((canonicalMatrixMap K b X).comp (canonicalMatrixMap K b X).adjoint).det ^
          (1 / (2 * ((d * (m - r) : ℕ) : ℝ))) := by
  have hdet : 0 ≤ ((canonicalMatrixMap K b X).comp (canonicalMatrixMap K b X).adjoint).det := by
    have h := (canonicalMatrixMap K b X).adjoint.normDet_sq
    rw [LinearMap.adjoint_adjoint] at h
    exact h ▸ sq_nonneg _
  rw [canonicalKernel_covolume K b X hX,
    Real.mul_rpow (pow_nonneg (Real.sqrt_nonneg _) _) (Real.sqrt_nonneg _),
    canonical_discriminant_normalization K b (Nat.sub_pos_of_lt hmr)]
  congr 1
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hdet]
  congr 1
  ring

theorem canonicalKernel_normalized_covolume_le (b : Basis (Fin d) ℤ (𝓞 K))
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) (hX : Function.Surjective X.mulVec) (hmr : r < m) :
    intrinsicCovolume (canonicalKernel K X) ^ (1 / ((d * (m - r) : ℕ) : ℝ)) ≤
      Real.sqrt (NumberField.rootDiscr K) *
        ‖(canonicalMatrixMap K b X).toContinuousLinearMap‖ ^ ((r : ℝ) / ((m - r : ℕ) : ℝ)) := by
  have hn : 0 < m - r := Nat.sub_pos_of_lt hmr
  have hd : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (integralBasis_dimension_pos K b).ne'
  have hn' : ((m - r : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  rw [canonicalKernel_covolume K b X hX, ← kernelJacobian_eq_sqrt_det,
    Real.mul_rpow (pow_nonneg (Real.sqrt_nonneg _) _) (LinearMap.normDet_nonneg _),
    canonical_discriminant_normalization K b hn]
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  have h := Real.rpow_le_rpow (LinearMap.normDet_nonneg _)
    (kernelJacobian_le_opNorm_pow (canonicalMatrixMap K b X))
    (show 0 ≤ 1 / ((d * (m - r) : ℕ) : ℝ) by positivity)
  rw [canonicalPower_finrank K b r, ← Real.rpow_natCast_mul (norm_nonneg _)] at h
  convert h using 1
  congr 1
  push_cast
  field_simp

/-- The kernel covolume proposition for the actual ring matrix and canonical kernel. The operator
determinant equals `det(A Aᵀ)` in every orthonormal coordinate system by
`kernelGram_det_eq_orthonormalMatrix` .
-/
theorem canonical_kernel_covolume_certificate (b : Basis (Fin d) ℤ (𝓞 K))
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) (hX : Function.Surjective X.mulVec) (hmr : r < m) :
    finrank ℤ (canonicalKernel K X) = d * (m - r) ∧
    intrinsicCovolume (canonicalKernel K X) =
      Real.sqrt |(NumberField.discr K : ℝ)| ^ (m - r) *
        Real.sqrt ((canonicalMatrixMap K b X).comp (canonicalMatrixMap K b X).adjoint).det ∧
    intrinsicCovolume (canonicalKernel K X) ^ (1 / ((d * (m - r) : ℕ) : ℝ)) =
      Real.sqrt (NumberField.rootDiscr K) *
        ((canonicalMatrixMap K b X).comp (canonicalMatrixMap K b X).adjoint).det ^
          (1 / (2 * ((d * (m - r) : ℕ) : ℝ))) ∧
    intrinsicCovolume (canonicalKernel K X) ^ (1 / ((d * (m - r) : ℕ) : ℝ)) ≤
      Real.sqrt (NumberField.rootDiscr K) *
        ‖(canonicalMatrixMap K b X).toContinuousLinearMap‖ ^ ((r : ℝ) / ((m - r : ℕ) : ℝ)) :=
  ⟨canonicalKernel_rank K b X hX, canonicalKernel_covolume K b X hX,
    canonicalKernel_normalized_covolume K b X hX hmr,
    canonicalKernel_normalized_covolume_le K b X hX hmr⟩

end GeometricGaussianLHL
end

end KernelNaturalScale

section SmoothingCovolume

/-!
## The covolume lower bound for smoothing

The actual shortest nonzero dual vector gives the first bound in the smoothing lower-bound
proposition. Minkowski's theorem, intrinsic covolume reciprocity, and the ball-volume estimate give
the numerical constant `0.7` in every integer rank at least two.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Module MeasureTheory

namespace GeometricGaussianLHL

theorem smoothing_minkowski_constant {n ε c μ : ℝ} (hn : 0 < n) (hε : 0 < ε) (hε1 : ε < 1)
    (hμ : 0 < μ)
    (hbound : μ * c ≤ 2 * Real.sqrt (n / 2) / Real.sqrt Real.pi) :
    (7 / 10 : ℝ) * Real.sqrt (Real.log (1 / ε) / n) * c ≤
      Real.sqrt (Real.log (2 / ε) / Real.pi) / μ := by
  have ha : 0 ≤ Real.log (1 / ε) := Real.log_nonneg (by
    apply (le_div_iff₀ hε).mpr
    linarith)
  have hab : Real.log (1 / ε) ≤ Real.log (2 / ε) := Real.log_le_log (by positivity)
    (div_le_div_of_nonneg_right (by norm_num) hε.le)
  let C := 2 * Real.sqrt (n / 2) / Real.sqrt Real.pi
  have hC : C ^ 2 = 2 * n / Real.pi := by
    dsimp [C]
    rw [div_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt Real.pi_pos.le]
    ring
  have hs : ((7 / 10 : ℝ) * Real.sqrt (Real.log (1 / ε) / n) * C) ^ 2 =
      (49 / 50 : ℝ) * (Real.log (1 / ε) / Real.pi) := by
    rw [mul_pow, mul_pow, hC, Real.sq_sqrt (div_nonneg ha hn.le)]
    field_simp
    ring
  have hnum : (7 / 10 : ℝ) * Real.sqrt (Real.log (1 / ε) / n) * C ≤
      Real.sqrt (Real.log (1 / ε) / Real.pi) := by
    apply (sq_le_sq₀ (by dsimp [C]; positivity) (Real.sqrt_nonneg _)).mp
    rw [hs, Real.sq_sqrt (div_nonneg ha Real.pi_pos.le)]
    nlinarith [div_nonneg ha Real.pi_pos.le]
  apply (le_div_iff₀ hμ).mpr
  calc
    (7 / 10 : ℝ) * Real.sqrt (Real.log (1 / ε) / n) * c * μ =
        ((7 / 10 : ℝ) * Real.sqrt (Real.log (1 / ε) / n)) * (μ * c) := by ring
    _ ≤ ((7 / 10 : ℝ) * Real.sqrt (Real.log (1 / ε) / n)) * C :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ ≤ Real.sqrt (Real.log (1 / ε) / Real.pi) := hnum
    _ ≤ Real.sqrt (Real.log (2 / ε) / Real.pi) := by gcongr

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem smoothingParameter_lower_firstMinimum (L : Submodule ℤ E) [DiscreteTopology L]
    (hL : L ≠ ⊥) {ε : ℝ} (hε : 0 < ε) :
    Real.sqrt (Real.log (2 / ε) / Real.pi) / firstMinimum (latticeDual L) ≤ smoothingParameter L ε := by
  have hD : latticeDual L ≠ ⊥ := by
    intro h
    have hs := latticeDual_span L
    apply lattice_span_ne_bot hL
    simpa [h] using hs.symm
  obtain ⟨v, hv, hv0, heq⟩ := firstMinimum_attained (latticeDual L) hD
  apply smoothingParameter_lower_of_dual_vector (exists_smoothAt L hε) hε
    (firstMinimum_pos (latticeDual L) hD) ⟨v, hv⟩
    (fun h => hv0 (congrArg Subtype.val h)) heq.le

variable [MeasurableSpace E] [BorelSpace E]

theorem firstMinimum_dual_mul_covolume_root_le (L : Submodule ℤ E) [DiscreteTopology L]
    (hn : 2 ≤ finrank ℤ L) :
    firstMinimum (latticeDual L) * intrinsicCovolume L ^ (1 / (finrank ℤ L : ℝ)) ≤
      2 * Real.sqrt ((finrank ℤ L : ℝ) / 2) / Real.sqrt Real.pi := by
  let : IsZLattice ℝ (latticeDual (intrinsicLattice L)) := ⟨fullLattice_dual_span _⟩
  obtain ⟨v, hv, hv0, hnorm⟩ := exists_short_fullLattice_vector (latticeDual (intrinsicLattice L))
    (by rwa [← intrinsicLattice_rank L])
  let w : latticeDual L := intrinsicDualEquiv L ⟨v, hv⟩
  have hw0 : (w : E) ≠ 0 := by
    intro h
    exact hv0 (Subtype.ext h)
  have hmin : firstMinimum (latticeDual L) ≤ ‖v‖ := firstMinimum_le_norm _ w.property hw0
  rw [fullLattice_dual_covolume, ← intrinsicLattice_rank L] at hnorm
  change ‖v‖ ≤ (2 * Real.sqrt ((finrank ℤ L : ℝ) / 2) / Real.sqrt Real.pi) *
    (intrinsicCovolume L)⁻¹ ^ (1 / (finrank ℤ L : ℝ)) at hnorm
  rw [Real.inv_rpow (intrinsicCovolume_pos L).le] at hnorm
  have hroot : 0 < intrinsicCovolume L ^ (1 / (finrank ℤ L : ℝ)) :=
    Real.rpow_pos_of_pos (intrinsicCovolume_pos L) _
  have h := mul_le_mul_of_nonneg_right (hmin.trans hnorm) hroot.le
  simpa only [mul_assoc, inv_mul_cancel₀ hroot.ne', mul_one] using h

/-- Both inequalities of the smoothing lower-bound proposition, using the actual first minimum and
intrinsic lattice covolume. -/
theorem smoothing_covolume_certificate (L : Submodule ℤ E) [DiscreteTopology L]
    (hn : 2 ≤ finrank ℤ L) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    Real.sqrt (Real.log (2 / ε) / Real.pi) / firstMinimum (latticeDual L) ≤ smoothingParameter L ε ∧
    (7 / 10 : ℝ) * Real.sqrt (Real.log (1 / ε) / (finrank ℤ L : ℝ)) *
        intrinsicCovolume L ^ (1 / (finrank ℤ L : ℝ)) ≤
      Real.sqrt (Real.log (2 / ε) / Real.pi) / firstMinimum (latticeDual L) := by
  have hL : L ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hn
    omega
  have hD : latticeDual L ≠ ⊥ := by
    intro h
    have hr := latticeDual_rank L
    rw [h, finrank_bot] at hr
    omega
  refine ⟨smoothingParameter_lower_firstMinimum L hL hε, ?_⟩
  exact smoothing_minkowski_constant (by exact_mod_cast (show 0 < finrank ℤ L by omega))
    hε hε1 (firstMinimum_pos _ hD) (firstMinimum_dual_mul_covolume_root_le L hn)

theorem smoothingParameter_covolume_lower (L : Submodule ℤ E) [DiscreteTopology L]
    (hn : 2 ≤ finrank ℤ L) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    (7 / 10 : ℝ) * Real.sqrt (Real.log (1 / ε) / (finrank ℤ L : ℝ)) *
      intrinsicCovolume L ^ (1 / (finrank ℤ L : ℝ)) ≤ smoothingParameter L ε :=
  (smoothing_covolume_certificate L hn hε hε1).2.trans
    (smoothing_covolume_certificate L hn hε hε1).1

def gaussianHeuristic (L : Submodule ℤ E) : ℝ :=
  Real.sqrt ((finrank ℤ L : ℝ) / (2 * Real.pi * Real.exp 1)) *
    intrinsicCovolume L ^ (1 / (finrank ℤ L : ℝ))

theorem gaussianHeuristic_dual_mul (L : Submodule ℤ E) [DiscreteTopology L] :
    gaussianHeuristic (latticeDual L) * gaussianHeuristic L =
      (finrank ℤ L : ℝ) / (2 * Real.pi * Real.exp 1) := by
  rw [gaussianHeuristic, gaussianHeuristic, latticeDual_rank, intrinsicCovolume_dual,
    Real.inv_rpow (intrinsicCovolume_pos L).le]
  have hroot := (Real.rpow_pos_of_pos (intrinsicCovolume_pos L) (1 / (finrank ℤ L : ℝ))).ne'
  calc
    _ = Real.sqrt ((finrank ℤ L : ℝ) / (2 * Real.pi * Real.exp 1)) ^ 2 := by
      field_simp
    _ = _ := Real.sq_sqrt (by positivity)

end GeometricGaussianLHL
end

end SmoothingCovolume

section KernelNaturalLower

/-!
## The deterministic natural-scale lower bound

The canonical kernel's normalized covolume is bounded below by the root discriminant and the
smallest transverse stretch of the actual canonical matrix map. The smoothing lower-bound
proposition then gives the first assertion of the kernel natural-scale corollary, with its necessary
rank-at-least-two hypothesis made explicit. The probabilistic spectral assertion is a separate
obligation.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Module NumberField MeasureTheory

namespace GeometricGaussianLHL

variable (K : Type*) [Field K] [NumberField K] {d r m : ℕ}

local instance naturalLowerEmbeddingsFintype : Fintype (K →+* ℂ) := inferInstance
local instance naturalLowerAmbientInner : InnerProductSpace ℝ (CanonicalAmbient K) := inferInstance
local instance naturalLowerSpaceInner : InnerProductSpace ℝ (canonicalSpace K) := inferInstance
local instance naturalLowerPowerInner (n : ℕ) : InnerProductSpace ℝ (CanonicalPower K n) := inferInstance
local instance naturalLowerPowerMeasureSpace (n : ℕ) : MeasureSpace (CanonicalPower K n) :=
  measureSpaceOfInnerProductSpace

theorem canonicalKernel_normalized_covolume_ge (b : Basis (Fin d) ℤ (𝓞 K))
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) (hX : Function.Surjective X.mulVec) (hmr : r < m) :
    Real.sqrt (NumberField.rootDiscr K) *
        kernelMinimumStretch (canonicalMatrixMap K b X) (canonicalMatrixMap_surjective K b X hX) ^
          ((r : ℝ) / ((m - r : ℕ) : ℝ)) ≤
      intrinsicCovolume (canonicalKernel K X) ^ (1 / ((d * (m - r) : ℕ) : ℝ)) := by
  have hn : 0 < m - r := Nat.sub_pos_of_lt hmr
  have hd : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (integralBasis_dimension_pos K b).ne'
  have hn' : ((m - r : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  rw [canonicalKernel_covolume K b X hX, ← kernelJacobian_eq_sqrt_det,
    Real.mul_rpow (pow_nonneg (Real.sqrt_nonneg _) _) (LinearMap.normDet_nonneg _),
    canonical_discriminant_normalization K b hn]
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  have h := Real.rpow_le_rpow
    (pow_nonneg (kernelMinimumStretch_nonneg _ _) _)
    (kernelJacobian_ge_minimumStretch_pow (canonicalMatrixMap K b X)
      (canonicalMatrixMap_surjective K b X hX))
    (show 0 ≤ 1 / ((d * (m - r) : ℕ) : ℝ) by positivity)
  rw [canonicalPower_finrank K b r,
    ← Real.rpow_natCast_mul (kernelMinimumStretch_nonneg _ _)] at h
  convert h using 1
  congr 1
  push_cast
  field_simp

/-- The deterministic assertion of the kernel natural-scale corollary, corrected to require kernel
rank at least two. No probability estimate is assumed here. -/
theorem canonicalKernel_natural_smoothing_lower (b : Basis (Fin d) ℤ (𝓞 K))
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) (hX : Function.Surjective X.mulVec)
    (hN : 2 ≤ d * (m - r)) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    (7 / 10 : ℝ) * Real.sqrt (Real.log (1 / ε) / ((d * (m - r) : ℕ) : ℝ)) *
        Real.sqrt (NumberField.rootDiscr K) *
        kernelMinimumStretch (canonicalMatrixMap K b X) (canonicalMatrixMap_surjective K b X hX) ^
          ((r : ℝ) / ((m - r : ℕ) : ℝ)) ≤
      smoothingParameter (canonicalKernel K X) ε := by
  have hmr : r < m := by
    by_contra h
    have hz : m - r = 0 := Nat.sub_eq_zero_of_le (by omega)
    simp only [hz, mul_zero] at hN
    omega
  have hr := canonicalKernel_rank K b X hX
  let : DiscreteTopology (canonicalKernel K X) := canonicalKernel_discrete K b X
  have h := smoothingParameter_covolume_lower (canonicalKernel K X) (by rwa [hr]) hε hε1
  rw [hr] at h
  apply le_trans _ h
  have hg := mul_le_mul_of_nonneg_left
    (canonicalKernel_normalized_covolume_ge K b X hX hmr)
    (show 0 ≤ (7 / 10 : ℝ) * Real.sqrt (Real.log (1 / ε) / ((d * (m - r) : ℕ) : ℝ)) by positivity)
  simpa only [mul_assoc] using hg

end GeometricGaussianLHL
end

end KernelNaturalLower
