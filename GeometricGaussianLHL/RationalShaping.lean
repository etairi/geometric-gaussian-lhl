import GeometricGaussianLHL.MatrixApproximation
import GeometricGaussianLHL.ShapingGeometry
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Tactic.GCongr

/-!
# Rational shaping and metric normalization

This module collects the following proof sections, in dependency order.
- Completing a compressed Gram matrix to a positive square matrix (`MatrixGramCompletion`).
- A rational algebraic target for general shaping (`RationalShapingCovariance`).
- Positivity of the rational covariance candidate (`RationalShapingPositivity`).
- Strict positivity of the rational shaping covariance (`RationalShapingDefinite`).
- Positive square-root target for rational shaping inputs (`RationalShapingSquareRoot`).
- A covariance formula that preserves positivity with approximate inverses (`GramFilledCovariance`).
- Operator-error propagation through the positive covariance formula (`GramFilledCovarianceError`).
- The trace-average shaping target for real inputs (`RealShapingCovariance`).
- A dimension-independent square-root perturbation bound (`MatrixSquareRootStability`).
- An input-derived precision budget for rational shaping covariance (`RationalShapingApproximation`).
- Sharp admissible bounds for the rational kernel fill (`RationalShapingFillBounds`).
- Error from perturbing the shaping input (`ShapingInputStability`).
- The rational right inverse and the intrinsic kernel geometry (`RationalShapingGeometry`).
- Numerical inverse square roots using the existing inverse and root routines (`RationalInverseRoot`).
- Positive rational approximation to the shaping square root (`RationalShapingAlgorithm`).
- Shaping a real target from a sufficiently accurate rational input (`RealShapingInputCertificate`).
- Conditioning survives sufficiently accurate matrix input (`ShapingInputConditioning`).
- Leading-row embedding for square-buffer implementations (`MatrixRowEmbedding`).
- Numerical normalization from a rational metric and coefficient matrix (`RationalMetricNormalization`).
- Refining rectangular shaping through square matrix operations (`PaddedShapingCovariance`).
- Real-metric error in the normalized coefficient matrix (`MetricNormalizationStability`).
- Repeated metrics and rectangular normalization in square buffers (`MetricNormalizationPadding`).
- Intrinsic geometry of the real trace-average covariance (`RealShapingGeometry`).
- Costs of the positivity-preserving covariance formula (`GramFilledCovarianceCost`).
- Stored covariance construction from the computed inverse Gram matrix (`RationalCovarianceCost`).
- Arithmetic cost of the computed inverse square root (`RationalInverseRootCost`).
- Computing the shaping precision schedule (`RationalShapingScheduleCost`).
- Polynomial envelopes for the complete rational covariance construction (`RationalCovarianceBounds`).
- Stored repeated metric blocks (`RationalBlockCost`).
- Composing the inverse, covariance and square-root executions (`RationalShapingNumericalCost`).
- Stored positive-shaping output and its serialization cost (`RationalShapingOutputCost`).
- Stored metric normalization with complete arithmetic costs (`RationalMetricNormalizationCost`).
- Total arithmetic cost of the rational shaping algorithm (`RationalShapingCost`).
- Exact widths and numerical approximation of rational spherical shaping (`RationalShapingWidths`).
- Exact widths of the real target approximated by the shaping algorithm (`RealShapingWidths`).
- Metric normalization costs measured against finite input encodings (`RationalMetricCostCertificate`).
- Uniform polynomial-cost certificate for finite rational shaping input (`RationalShapingCostCertificate`).
- RationalShapingCertificate (`RationalShapingCertificate`).
- A dyadic input-precision budget for the real shaping target (`RealShapingPrecision`).
-/

section MatrixGramCompletion

/-!
## Completing a compressed Gram matrix to a positive square matrix

Adding the identity on the complementary coordinate subspace gives an
invertible square matrix. Its inverse restricts to the original Gram
inverse, so the existing square inverse routine can serve rectangular input.
-/

open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator

namespace GeometricGaussianLHL

def matrixGramCompletion {𝕜 : Type*} [CommRing 𝕜] {p q : ℕ}
    (J : Matrix (Fin q) (Fin p) 𝕜) (G : Matrix (Fin p) (Fin p) 𝕜) : Matrix (Fin q) (Fin q) 𝕜 :=
  J * G * J.transpose + (1 - J * J.transpose)

theorem matrixGramCompletion_mul {𝕜 : Type*} [CommRing 𝕜] {p q : ℕ}
    (J : Matrix (Fin q) (Fin p) 𝕜) (G H : Matrix (Fin p) (Fin p) 𝕜)
    (hJ : J.transpose * J = 1) (hGH : G * H = 1) :
    matrixGramCompletion J G * matrixGramCompletion J H = 1 := by
  let P := 1 - J * J.transpose
  have hJtP : J.transpose * P = 0 := by
    dsimp only [P]
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hJ, Matrix.one_mul, sub_self]
  have hPJ : P * J = 0 := by
    dsimp only [P]
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hJ, Matrix.mul_one, sub_self]
  have hPP : P * P = P := by
    change P * (1 - J * J.transpose) = P
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hPJ, Matrix.zero_mul, sub_zero]
  have hUV : (J * G * J.transpose) * (J * H * J.transpose) = J * J.transpose := by
    calc
      _ = J * G * (J.transpose * J) * H * J.transpose := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hJ, Matrix.mul_one, Matrix.mul_assoc J G H, hGH, Matrix.mul_one]
  have hUP : (J * G * J.transpose) * P = 0 := by
    rw [Matrix.mul_assoc, hJtP, Matrix.mul_zero]
  have hPV : P * (J * H * J.transpose) = 0 := by
    calc
      _ = (P * J) * H * J.transpose := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hPJ, Matrix.zero_mul, Matrix.zero_mul]
  change (J * G * J.transpose + P) * (J * H * J.transpose + P) = 1
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, hUV, hUP, hPV, hPP, add_zero, zero_add]
  exact add_sub_cancel (J * J.transpose) 1

theorem matrixGramCompletion_isUnit_det {𝕜 : Type*} [Field 𝕜] {p q : ℕ}
    (J : Matrix (Fin q) (Fin p) 𝕜) (G : Matrix (Fin p) (Fin p) 𝕜)
    (hJ : J.transpose * J = 1) (hG : IsUnit G.det) :
    IsUnit (matrixGramCompletion J G).det := by
  apply isUnit_iff_exists_inv.mpr
  refine ⟨(matrixGramCompletion J G⁻¹).det, ?_⟩
  simpa only [Matrix.det_mul, Matrix.det_one] using
    congrArg Matrix.det (matrixGramCompletion_mul J G G⁻¹ hJ (Matrix.mul_nonsing_inv G hG))

theorem matrixGramCompletion_inv {𝕜 : Type*} [Field 𝕜] {p q : ℕ}
    (J : Matrix (Fin q) (Fin p) 𝕜) (G : Matrix (Fin p) (Fin p) 𝕜)
    (hJ : J.transpose * J = 1) (hG : IsUnit G.det) :
    (matrixGramCompletion J G)⁻¹ = matrixGramCompletion J G⁻¹ := by
  apply Matrix.inv_eq_right_inv
  exact matrixGramCompletion_mul J G G⁻¹ hJ (Matrix.mul_nonsing_inv G hG)

theorem matrixGramCompletion_compress {𝕜 : Type*} [CommRing 𝕜] {p q : ℕ}
    (J : Matrix (Fin q) (Fin p) 𝕜) (G : Matrix (Fin p) (Fin p) 𝕜)
    (hJ : J.transpose * J = 1) :
    J.transpose * matrixGramCompletion J G * J = G := by
  have hP : (1 - J * J.transpose) * J = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hJ, Matrix.mul_one, sub_self]
  rw [matrixGramCompletion, Matrix.mul_add, Matrix.add_mul]
  have h₁ : (J.transpose * (J * G * J.transpose)) * J = G := by
    calc
      _ = (J.transpose * J) * G * (J.transpose * J) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hJ, Matrix.one_mul, Matrix.mul_one]
  rw [h₁, Matrix.mul_assoc, hP, Matrix.mul_zero, add_zero]

theorem matrixGramCompletion_posSemidef {p q : ℕ}
    (J : Matrix (Fin q) (Fin p) ℝ) (G : Matrix (Fin p) (Fin p) ℝ)
    (hJ : J.transpose * J = 1) (hG : G.PosSemidef) :
    (matrixGramCompletion J G).PosSemidef := by
  let P := 1 - J * J.transpose
  have hP : P * P.transpose = P := by
    have he : (J * J.transpose) * (J * J.transpose) = J * J.transpose := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc J.transpose, hJ, Matrix.one_mul]
    dsimp only [P]
    rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, he, sub_self, sub_zero]
  have hp : P.PosSemidef := by
    have h := Matrix.posSemidef_self_mul_conjTranspose P
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, hP] using h
  have hg := hG.mul_mul_conjTranspose_same J
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, matrixGramCompletion, P] using hg.add hp

theorem matrixGramCompletion_posDef {p q : ℕ}
    (J : Matrix (Fin q) (Fin p) ℝ) (G : Matrix (Fin p) (Fin p) ℝ)
    (hJ : J.transpose * J = 1) (hG : G.PosDef) :
    (matrixGramCompletion J G).PosDef := by
  apply (matrixGramCompletion_posSemidef J G hJ hG.posSemidef).posDef_iff_isUnit.mpr
  exact (Matrix.isUnit_iff_isUnit_det _).mpr
    (matrixGramCompletion_isUnit_det J G hJ ((Matrix.isUnit_iff_isUnit_det _).mp hG.isUnit))

theorem matrixGramCompletion_rat_cast {p q : ℕ}
    (J : Matrix (Fin q) (Fin p) ℚ) (G : Matrix (Fin p) (Fin p) ℚ) :
    (matrixGramCompletion J G).map (Rat.castHom ℝ) =
      matrixGramCompletion (J.map (Rat.castHom ℝ)) (G.map (Rat.castHom ℝ)) := by
  unfold matrixGramCompletion
  rw [Matrix.map_add (Rat.castHom ℝ) (map_add _), Matrix.map_sub (Rat.castHom ℝ) (map_sub _),
    Matrix.map_one (Rat.castHom ℝ) (map_zero _) (map_one _), Matrix.map_mul, Matrix.map_mul, Matrix.map_mul]
  rfl

end GeometricGaussianLHL

end MatrixGramCompletion

section RationalShapingCovariance

/-!
## A rational algebraic target for general shaping

For a rational full-row-rank matrix, the right inverse and kernel projection
are rational. Filling the kernel at the average eigenvalue of the inverse
Gram matrix also gives a rational candidate covariance. This file proves
its exact spherical-image identity. Positivity, sharp widths, an executable
inverse algorithm and polynomial-time refinement remain further obligations.
-/

noncomputable section

namespace GeometricGaussianLHL

def rationalRightInverseMatrix {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℚ) : Matrix (Fin q) (Fin p) ℚ :=
  A.transpose * (A * A.transpose)⁻¹

def rationalKernelProjectionMatrix {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℚ) : Matrix (Fin q) (Fin q) ℚ :=
  1 - rationalRightInverseMatrix A * A

def rationalShapingKernelFill {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℚ) : ℚ :=
  Matrix.trace ((A * A.transpose)⁻¹) / (p : ℚ)

def rationalShapingCovarianceMatrix {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℚ) (w : ℚ) :
    Matrix (Fin q) (Fin q) ℚ :=
  w ^ 2 • (rationalRightInverseMatrix A * (rationalRightInverseMatrix A).transpose +
    rationalShapingKernelFill A • rationalKernelProjectionMatrix A)

theorem rationalRightInverseMatrix_right_inverse {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℚ)
    (hA : IsUnit (A * A.transpose).det) : A * rationalRightInverseMatrix A = 1 := by
  rw [rationalRightInverseMatrix, ← Matrix.mul_assoc]
  exact Matrix.mul_nonsing_inv _ hA

theorem rationalKernelProjectionMatrix_killed {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℚ)
    (hA : IsUnit (A * A.transpose).det) : A * rationalKernelProjectionMatrix A = 0 := by
  rw [rationalKernelProjectionMatrix, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc,
    rationalRightInverseMatrix_right_inverse A hA, Matrix.one_mul, sub_self]

theorem rationalShapingCovarianceMatrix_image {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℚ) (w : ℚ)
    (hA : IsUnit (A * A.transpose).det) :
    A * rationalShapingCovarianceMatrix A w * A.transpose = w ^ 2 • (1 : Matrix (Fin p) (Fin p) ℚ) := by
  have hr := rationalRightInverseMatrix_right_inverse A hA
  have hk := rationalKernelProjectionMatrix_killed A hA
  have ht : A * (rationalRightInverseMatrix A * (rationalRightInverseMatrix A).transpose) * A.transpose = 1 := by
    calc
      _ = (A * rationalRightInverseMatrix A) * (A * rationalRightInverseMatrix A).transpose := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hr]; simp
  rw [rationalShapingCovarianceMatrix, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, ht, hk,
    Matrix.zero_mul, smul_zero, add_zero]

end GeometricGaussianLHL
end

end RationalShapingCovariance

section RationalShapingPositivity

/-!
## Positivity of the rational covariance candidate

The kernel projection is a symmetric idempotent and hence its own Gram
matrix. The inverse-Gram trace average is nonnegative. These facts prove
positive semidefiniteness of the candidate without choosing eigenvectors.
Strict positivity, sharp widths and computational refinement remain separate.
-/

noncomputable section

namespace GeometricGaussianLHL

private theorem rationalGram_positive {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℚ) :
    (A * A.transpose).PosSemidef := by
  have h : (A.transpose.conjTranspose * A.transpose).PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
      (Matrix.isHermitian_conjTranspose_mul_self _) fun x => ?_
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_conjTranspose, star_star]
    exact Finset.sum_nonneg fun i _ => by
      simpa only [star_trivial, pow_two] using sq_nonneg (Matrix.mulVec A.transpose x i)
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose] using h

private theorem rationalPosSemidef_smul {p : ℕ} {A : Matrix (Fin p) (Fin p) ℚ}
    (hA : A.PosSemidef) {c : ℚ} (hc : 0 ≤ c) : (c • A).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hA.isHermitian.smul (by rfl)) fun x => ?_
  rw [Matrix.smul_mulVec, dotProduct_smul]
  exact smul_nonneg hc (hA.dotProduct_mulVec_nonneg x)

theorem rationalKernelProjectionMatrix_transpose {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℚ) :
    (rationalKernelProjectionMatrix A).transpose = rationalKernelProjectionMatrix A := by
  simp only [rationalKernelProjectionMatrix, rationalRightInverseMatrix, Matrix.transpose_sub,
    Matrix.transpose_one, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.transpose_nonsing_inv, Matrix.mul_assoc]

theorem rationalKernelProjectionMatrix_gram {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℚ)
    (hA : IsUnit (A * A.transpose).det) :
    rationalKernelProjectionMatrix A * (rationalKernelProjectionMatrix A).transpose =
      rationalKernelProjectionMatrix A := by
  have hr := rationalRightInverseMatrix_right_inverse A hA
  have hi : (rationalRightInverseMatrix A * A) * (rationalRightInverseMatrix A * A) =
      rationalRightInverseMatrix A * A := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc A, hr, Matrix.one_mul]
  rw [rationalKernelProjectionMatrix_transpose]
  unfold rationalKernelProjectionMatrix
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hi, sub_self, sub_zero]

theorem rationalShapingKernelFill_nonneg {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℚ) :
    0 ≤ rationalShapingKernelFill A := by
  have hg := rationalGram_positive A
  exact div_nonneg hg.inv.trace_nonneg (Nat.cast_nonneg p)

theorem rationalShapingCovarianceMatrix_posSemidef {p q : ℕ}
    (A : Matrix (Fin p) (Fin q) ℚ) (w : ℚ) (hA : IsUnit (A * A.transpose).det) :
    (rationalShapingCovarianceMatrix A w).PosSemidef := by
  have hp : (rationalKernelProjectionMatrix A).PosSemidef := by
    have h := rationalGram_positive (rationalKernelProjectionMatrix A)
    simpa only [rationalKernelProjectionMatrix_gram A hA] using h
  have hr := rationalGram_positive (rationalRightInverseMatrix A)
  exact rationalPosSemidef_smul (hr.add (rationalPosSemidef_smul hp
    (rationalShapingKernelFill_nonneg A))) (sq_nonneg w)

theorem rationalShapingCovarianceMatrix_real_posSemidef {p q : ℕ}
    (A : Matrix (Fin p) (Fin q) ℚ) (w : ℚ) (hA : IsUnit (A * A.transpose).det) :
    ((rationalShapingCovarianceMatrix A w).map (fun x : ℚ => (x : ℝ))).PosSemidef := by
  let f : ℚ →+* ℝ := Rat.castHom ℝ
  have hpgram : (rationalKernelProjectionMatrix A).map f *
      ((rationalKernelProjectionMatrix A).map f).transpose = (rationalKernelProjectionMatrix A).map f := by
    have h := congrArg (fun M => M.map f) (rationalKernelProjectionMatrix_gram A hA)
    rw [Matrix.map_mul] at h
    exact h
  have hp : ((rationalKernelProjectionMatrix A).map f).PosSemidef := by
    have h := Matrix.posSemidef_self_mul_conjTranspose ((rationalKernelProjectionMatrix A).map f)
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, hpgram] using h
  have hr : ((rationalRightInverseMatrix A).map f *
      ((rationalRightInverseMatrix A).map f).transpose).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_self_mul_conjTranspose ((rationalRightInverseMatrix A).map f)
  have hc : 0 ≤ (rationalShapingKernelFill A : ℝ) := by
    exact_mod_cast rationalShapingKernelFill_nonneg A
  have he : (rationalShapingCovarianceMatrix A w).map f = (w : ℝ) ^ 2 •
      ((rationalRightInverseMatrix A).map f * ((rationalRightInverseMatrix A).map f).transpose +
        (rationalShapingKernelFill A : ℝ) • (rationalKernelProjectionMatrix A).map f) := by
    have hm : (rationalRightInverseMatrix A * (rationalRightInverseMatrix A).transpose).map f =
        (rationalRightInverseMatrix A).map f * ((rationalRightInverseMatrix A).map f).transpose :=
      Matrix.map_mul
    rw [← hm]
    ext i j
    simp [rationalShapingCovarianceMatrix, Matrix.map_apply, Matrix.smul_apply, Matrix.add_apply, f, mul_add]
  change ((rationalShapingCovarianceMatrix A w).map f).PosSemidef
  rw [he]
  exact (hr.add (hp.smul hc)).smul (sq_nonneg (w : ℝ))

end GeometricGaussianLHL
end

end RationalShapingPositivity

section RationalShapingDefinite

/-!
## Strict positivity of the rational shaping covariance

For a nonempty full-row-rank rational input and a nonzero width, the inverse
Gram trace average is strictly positive. Orthogonality of the right inverse
and kernel projection gives an explicit inverse for the unscaled covariance.
The real covariance is therefore positive definite. All inverse operations
here remain mathematical targets; this file makes no runtime claim.
-/

noncomputable section
namespace GeometricGaussianLHL

theorem rationalGram_real_posDef {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℚ)
    (hA : IsUnit (A * A.transpose).det) :
    ((A * A.transpose).map (Rat.castHom ℝ)).PosDef := by
  have hpsd : ((A * A.transpose).map (Rat.castHom ℝ)).PosSemidef := by
    rw [Matrix.map_mul]
    change (A.map (Rat.castHom ℝ) * (A.map (Rat.castHom ℝ)).transpose).PosSemidef
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_self_mul_conjTranspose (A.map (Rat.castHom ℝ))
  apply hpsd.posDef_iff_isUnit.mpr
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  change IsUnit ((Rat.castHom ℝ).mapMatrix (A * A.transpose)).det
  rw [← (Rat.castHom ℝ).map_det]
  exact hA.map (Rat.castHom ℝ)

theorem rationalGramInverse_real {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℚ)
    (hA : IsUnit (A * A.transpose).det) :
    ((A * A.transpose)⁻¹).map (Rat.castHom ℝ) =
      ((A * A.transpose).map (Rat.castHom ℝ))⁻¹ := by
  symm
  apply Matrix.inv_eq_right_inv
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hA]
  exact Matrix.map_one (Rat.castHom ℝ) (map_zero _) (map_one _)

theorem rationalShapingKernelFill_pos {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℚ)
    (hp : 0 < p) (hA : IsUnit (A * A.transpose).det) :
    0 < rationalShapingKernelFill A := by
  let : NeZero p := ⟨Nat.ne_of_gt hp⟩
  have htrace := (rationalGram_real_posDef A hA).inv.trace_pos
  rw [← rationalGramInverse_real A hA, ← AddMonoidHom.map_trace] at htrace
  change (0 : ℝ) < (Matrix.trace ((A * A.transpose)⁻¹) : ℚ) at htrace
  have hq : 0 < Matrix.trace ((A * A.transpose)⁻¹) := by exact_mod_cast htrace
  exact div_pos hq (by exact_mod_cast hp)

theorem rationalShaping_unscaled_right_inverse {p q : ℕ}
    (A : Matrix (Fin p) (Fin q) ℚ) (hA : IsUnit (A * A.transpose).det)
    (hc : rationalShapingKernelFill A ≠ 0) :
    (rationalRightInverseMatrix A * (rationalRightInverseMatrix A).transpose +
      rationalShapingKernelFill A • rationalKernelProjectionMatrix A) *
    (A.transpose * A + (rationalShapingKernelFill A)⁻¹ • rationalKernelProjectionMatrix A) = 1 := by
  let R := rationalRightInverseMatrix A
  let P := rationalKernelProjectionMatrix A
  let c := rationalShapingKernelFill A
  change (R * R.transpose + c • P) * (A.transpose * A + c⁻¹ • P) = 1
  have hr : A * R = 1 := rationalRightInverseMatrix_right_inverse A hA
  have hp : P.transpose = P := rationalKernelProjectionMatrix_transpose A
  have hpp : P * P = P := by
    simpa only [rationalKernelProjectionMatrix_transpose] using rationalKernelProjectionMatrix_gram A hA
  have hpr : P * R = 0 := by
    change (1 - R * A) * R = 0
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hr, Matrix.mul_one, sub_self]
  have hrtp : R.transpose * P = 0 := by
    simpa only [Matrix.transpose_mul, hp, Matrix.transpose_zero] using congrArg Matrix.transpose hpr
  have hpat : P * A.transpose = 0 := by
    simpa only [Matrix.transpose_mul, rationalKernelProjectionMatrix_transpose, Matrix.transpose_zero] using
      congrArg Matrix.transpose (rationalKernelProjectionMatrix_killed A hA)
  have hrr : (R * R.transpose) * (A.transpose * A) = R * A := by
    have hrat : R.transpose * A.transpose = 1 := by
      simpa only [Matrix.transpose_mul, Matrix.transpose_one] using congrArg Matrix.transpose hr
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc R.transpose, hrat, Matrix.one_mul]
  have hrp : (R * R.transpose) * P = 0 := by
    rw [Matrix.mul_assoc, hrtp, Matrix.mul_zero]
  have hpa : P * (A.transpose * A) = 0 := by
    rw [← Matrix.mul_assoc, hpat, Matrix.zero_mul]
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, hrr, hrp, hpa, hpp]
  simp only [smul_zero, add_zero, zero_add, smul_smul]
  have hc' : c ≠ 0 := hc
  rw [mul_inv_cancel₀ hc', one_smul]
  exact add_sub_cancel (R * A) 1

theorem rationalShapingCovarianceMatrix_isUnit {p q : ℕ}
    (A : Matrix (Fin p) (Fin q) ℚ) (w : ℚ) (hp : 0 < p)
    (hA : IsUnit (A * A.transpose).det) (hw : w ≠ 0) :
    IsUnit (rationalShapingCovarianceMatrix A w) := by
  let Q := A.transpose * A + (rationalShapingKernelFill A)⁻¹ • rationalKernelProjectionMatrix A
  have h : rationalShapingCovarianceMatrix A w * ((w ^ 2)⁻¹ • Q) = 1 := by
    rw [rationalShapingCovarianceMatrix, Matrix.smul_mul, Matrix.mul_smul,
      rationalShaping_unscaled_right_inverse A hA (ne_of_gt (rationalShapingKernelFill_pos A hp hA)),
      smul_smul, mul_inv_cancel₀ (pow_ne_zero 2 hw), one_smul]
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  apply isUnit_iff_exists_inv.mpr
  refine ⟨((w ^ 2)⁻¹ • Q).det, ?_⟩
  simpa only [Matrix.det_mul, Matrix.det_one] using congrArg Matrix.det h

theorem rationalShapingCovarianceMatrix_real_posDef {p q : ℕ}
    (A : Matrix (Fin p) (Fin q) ℚ) (w : ℚ) (hp : 0 < p)
    (hA : IsUnit (A * A.transpose).det) (hw : w ≠ 0) :
    ((rationalShapingCovarianceMatrix A w).map (Rat.castHom ℝ)).PosDef := by
  apply (rationalShapingCovarianceMatrix_real_posSemidef A w hA).posDef_iff_isUnit.mpr
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  change IsUnit ((Rat.castHom ℝ).mapMatrix (rationalShapingCovarianceMatrix A w)).det
  rw [← (Rat.castHom ℝ).map_det]
  exact ((Matrix.isUnit_iff_isUnit_det _).mp
    (rationalShapingCovarianceMatrix_isUnit A w hp hA hw)).map (Rat.castHom ℝ)

end GeometricGaussianLHL
end

end RationalShapingDefinite

section RationalShapingSquareRoot

/-!
## Positive square-root target for rational shaping inputs

The input covariance has rational entries. Its positive square root is a real
matrix, defined mathematically by continuous functional calculus. The image
identity below holds for this actual square root. It does not yet supply an
approximation algorithm, sharp extreme widths, or the Gaussian-law connection.
-/

noncomputable section

open scoped MatrixOrder

namespace GeometricGaussianLHL

def rationalShapingSquareRootMatrix {p q : ℕ}
    (A : Matrix (Fin p) (Fin q) ℚ) (w : ℚ) : Matrix (Fin q) (Fin q) ℝ :=
  CFC.sqrt ((rationalShapingCovarianceMatrix A w).map (Rat.castHom ℝ))

theorem rationalShapingCovarianceMatrix_real_image {p q : ℕ}
    (A : Matrix (Fin p) (Fin q) ℚ) (w : ℚ) (hA : IsUnit (A * A.transpose).det) :
    A.map (Rat.castHom ℝ) * (rationalShapingCovarianceMatrix A w).map (Rat.castHom ℝ) *
      (A.map (Rat.castHom ℝ)).transpose = (w : ℝ) ^ 2 • (1 : Matrix (Fin p) (Fin p) ℝ) := by
  have h := congrArg (fun M => M.map (Rat.castHom ℝ))
    (rationalShapingCovarianceMatrix_image A w hA)
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map] at h
  exact h.trans (by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.map_apply, Matrix.smul_apply, hij])

theorem rationalShapingSquareRootMatrix_posDef {p q : ℕ}
    (A : Matrix (Fin p) (Fin q) ℚ) (w : ℚ) (hp : 0 < p)
    (hA : IsUnit (A * A.transpose).det) (hw : w ≠ 0) :
    (rationalShapingSquareRootMatrix A w).PosDef := by
  have hc := rationalShapingCovarianceMatrix_real_posDef A w hp hA hw
  apply (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)).posDef_iff_isUnit.mpr
  exact (CFC.isUnit_sqrt_iff _ hc.posSemidef.nonneg).mpr hc.isUnit

theorem rationalShapingSquareRootMatrix_transpose {p q : ℕ}
    (A : Matrix (Fin p) (Fin q) ℚ) (w : ℚ) :
    (rationalShapingSquareRootMatrix A w).transpose = rationalShapingSquareRootMatrix A w := by
  have h := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg
    ((rationalShapingCovarianceMatrix A w).map (Rat.castHom ℝ)))).isHermitian
  simpa only [rationalShapingSquareRootMatrix, Matrix.conjTranspose_eq_transpose_of_trivial] using h.eq

theorem rationalShapingSquareRootMatrix_covariance {p q : ℕ}
    (A : Matrix (Fin p) (Fin q) ℚ) (w : ℚ) (hA : IsUnit (A * A.transpose).det) :
    rationalShapingSquareRootMatrix A w * (rationalShapingSquareRootMatrix A w).transpose =
      (rationalShapingCovarianceMatrix A w).map (Rat.castHom ℝ) := by
  rw [rationalShapingSquareRootMatrix_transpose]
  exact CFC.sqrt_mul_sqrt_self _ (rationalShapingCovarianceMatrix_real_posSemidef A w hA).nonneg

theorem rationalShapingSquareRootMatrix_image {p q : ℕ}
    (A : Matrix (Fin p) (Fin q) ℚ) (w : ℚ) (hA : IsUnit (A * A.transpose).det) :
    (A.map (Rat.castHom ℝ) * rationalShapingSquareRootMatrix A w) *
      (A.map (Rat.castHom ℝ) * rationalShapingSquareRootMatrix A w).transpose =
      (w : ℝ) ^ 2 • (1 : Matrix (Fin p) (Fin p) ℝ) := by
  rw [Matrix.transpose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc (rationalShapingSquareRootMatrix A w),
    rationalShapingSquareRootMatrix_covariance A w hA, ← Matrix.mul_assoc]
  exact rationalShapingCovarianceMatrix_real_image A w hA

end GeometricGaussianLHL
end

end RationalShapingSquareRoot

section GramFilledCovariance

/-!
## A covariance formula that preserves positivity with approximate inverses

Replacing the kernel term by its Gram matrix gives `RRᵀ + c PPᵀ`, with
`P = I - RA`. It is positive definite for every `R` when `c > 0`, and agrees
with the exact rational shaping target for the true right inverse. Thus an
approximate inverse can supply a positive input to the square-root routine.
Accuracy and execution costs of the full shaping construction remain separate.
-/

open Matrix

namespace GeometricGaussianLHL

def gramFilledCovariance {𝕜 : Type*} [CommRing 𝕜] {p q : ℕ}
    (A : Matrix (Fin p) (Fin q) 𝕜) (R : Matrix (Fin q) (Fin p) 𝕜) (c : 𝕜) :
    Matrix (Fin q) (Fin q) 𝕜 :=
  let P := 1 - R * A
  R * R.transpose + c • (P * P.transpose)

theorem gramFilledCovariance_posDef {p q : ℕ}
    (A : Matrix (Fin p) (Fin q) ℝ) (R : Matrix (Fin q) (Fin p) ℝ)
    {c : ℝ} (hc : 0 < c) : (gramFilledCovariance A R c).PosDef := by
  let P := 1 - R * A
  have hR : (R * R.transpose).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using Matrix.posSemidef_self_mul_conjTranspose R
  have hP : (P * P.transpose).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using Matrix.posSemidef_self_mul_conjTranspose P
  have hC := hR.add (hP.smul hc.le)
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hC.isHermitian
  intro x hx
  have hform {r : ℕ} (D : Matrix (Fin q) (Fin r) ℝ) :
      x ⬝ᵥ ((D * D.transpose) *ᵥ x) = (D.transpose *ᵥ x) ⬝ᵥ (D.transpose *ᵥ x) := by
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
  by_contra hn
  have hle := le_of_not_gt hn
  change star x ⬝ᵥ ((R * R.transpose + c • (P * P.transpose)) *ᵥ x) ≤ 0 at hle
  simp only [star_trivial, Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add,
    dotProduct_smul, smul_eq_mul, hform] at hle
  have hr0 : 0 ≤ (R.transpose *ᵥ x) ⬝ᵥ (R.transpose *ᵥ x) := by
    exact Finset.sum_nonneg fun _ _ => mul_self_nonneg _
  have hp0 : 0 ≤ (P.transpose *ᵥ x) ⬝ᵥ (P.transpose *ᵥ x) := by
    exact Finset.sum_nonneg fun _ _ => mul_self_nonneg _
  have hcp : c * ((P.transpose *ᵥ x) ⬝ᵥ (P.transpose *ᵥ x)) = 0 :=
    le_antisymm (by linarith) (mul_nonneg hc.le hp0)
  have hrx : R.transpose *ᵥ x = 0 := dotProduct_self_eq_zero.mp (by linarith)
  have hpx : P.transpose *ᵥ x = 0 :=
    dotProduct_self_eq_zero.mp ((mul_eq_zero.mp hcp).resolve_left hc.ne')
  have he : P.transpose *ᵥ x = x := by
    dsimp only [P]
    rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul,
      Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hrx,
      Matrix.mulVec_zero, sub_zero]
  exact hx (he.symm.trans hpx)

theorem gramFilledCovariance_exact {p q : ℕ}
    (A : Matrix (Fin p) (Fin q) ℚ) (w : ℚ) (hA : IsUnit (A * A.transpose).det) :
    w ^ 2 • gramFilledCovariance A (rationalRightInverseMatrix A) (rationalShapingKernelFill A) =
      rationalShapingCovarianceMatrix A w := by
  change w ^ 2 • (rationalRightInverseMatrix A * (rationalRightInverseMatrix A).transpose +
    rationalShapingKernelFill A • (rationalKernelProjectionMatrix A *
      (rationalKernelProjectionMatrix A).transpose)) = _
  rw [rationalKernelProjectionMatrix_gram A hA]
  rfl

theorem gramFilledCovariance_rat_cast {p q : ℕ}
    (A : Matrix (Fin p) (Fin q) ℚ) (R : Matrix (Fin q) (Fin p) ℚ) (c : ℚ) :
    (gramFilledCovariance A R c).map (Rat.castHom ℝ) =
      gramFilledCovariance (A.map (Rat.castHom ℝ)) (R.map (Rat.castHom ℝ)) (c : ℝ) := by
  let f := Rat.castHom ℝ
  have hP : (1 - R * A).map f = 1 - R.map f * A.map f := by
    change f.mapMatrix (1 - R * A) = _
    rw [map_sub, map_one]
    change 1 - (R * A).map f = _
    rw [Matrix.map_mul]
  have hR : (R * R.transpose).map f = R.map f * (R.map f).transpose := Matrix.map_mul
  have hPP : (((1 : Matrix (Fin q) (Fin q) ℚ) - R * A) *
      ((1 : Matrix (Fin q) (Fin q) ℚ) - R * A).transpose).map f =
      (1 - R.map f * A.map f) * (1 - R.map f * A.map f).transpose := by
    rw [Matrix.map_mul]
    change (1 - R * A).map f * ((1 - R * A).map f).transpose = _
    rw [hP]
  change (gramFilledCovariance A R c).map f = _
  dsimp only [gramFilledCovariance]
  rw [← hR, ← hPP]
  ext i j
  simp [Matrix.map_apply, Matrix.smul_apply, Matrix.add_apply, f]

def rationalShapingApproxCovariance {p q : ℕ} (t : ℕ)
    (A : Matrix (Fin p) (Fin q) ℚ) (w : ℚ) : Matrix (Fin q) (Fin q) ℚ :=
  let M := rationalInverseApprox t (A * A.transpose)
  materializeMatrix (w ^ 2 • gramFilledCovariance A (A.transpose * M) (M.trace / (p : ℚ)))

theorem rationalShapingApproxCovariance_real_posDef {p q : ℕ} (t : ℕ)
    (A : Matrix (Fin p) (Fin q) ℚ) (w : ℚ) (hp : 0 < p)
    (hA : IsUnit (A * A.transpose).det) (hw : w ≠ 0) :
    ((rationalShapingApproxCovariance t A w).map (Rat.castHom ℝ)).PosDef := by
  have : NeZero p := ⟨Nat.ne_of_gt hp⟩
  let M := rationalInverseApprox t (A * A.transpose)
  have hM : (M.map (Rat.castHom ℝ)).PosDef :=
    rationalInverseApprox_posDef t _ (rationalGram_real_posDef A hA)
  have hc : 0 < ((M.trace / (p : ℚ) : ℚ) : ℝ) := by
    have ht := hM.trace_pos
    rw [← AddMonoidHom.map_trace] at ht
    change (0 : ℝ) < (M.trace : ℚ) at ht
    simpa using div_pos ht (show (0 : ℝ) < p from by exact_mod_cast hp)
  have hC := gramFilledCovariance_posDef (A.map (Rat.castHom ℝ))
    ((A.transpose * M).map (Rat.castHom ℝ)) hc
  have he : (rationalShapingApproxCovariance t A w).map (Rat.castHom ℝ) =
      (w : ℝ) ^ 2 • (gramFilledCovariance A (A.transpose * M) (M.trace / (p : ℚ))).map
        (Rat.castHom ℝ) := by
    rw [rationalShapingApproxCovariance, materializeMatrix_eq]
    ext i j
    simp [Matrix.map_apply, Matrix.smul_apply, M]
  rw [he, gramFilledCovariance_rat_cast]
  exact hC.smul (sq_pos_of_ne_zero (by exact_mod_cast hw))

end GeometricGaussianLHL

end GramFilledCovariance

section GramFilledCovarianceError

/-!
## Operator-error propagation through the positive covariance formula

The estimates use the Euclidean operator norm, including for rectangular
matrices. They keep the inverse approximation, trace average, and kernel
remainder errors explicit for the subsequent precision budget.
-/

open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator

namespace GeometricGaussianLHL

theorem euclideanMatrix_transpose_norm {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℝ) :
    ‖A.transpose‖ = ‖A‖ := by
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using Matrix.l2_opNorm_conjTranspose A

theorem matrixGram_operator_error {p q : ℕ}
    (R S : Matrix (Fin q) (Fin p) ℝ) :
    ‖R * R.transpose - S * S.transpose‖ ≤ (‖R‖ + ‖S‖) * ‖R - S‖ := by
  have he : R * R.transpose - S * S.transpose =
      (R - S) * R.transpose + S * (R - S).transpose := by
    rw [Matrix.transpose_sub, Matrix.sub_mul, Matrix.mul_sub]
    abel
  rw [he]
  calc
    _ ≤ ‖(R - S) * R.transpose‖ + ‖S * (R - S).transpose‖ := norm_add_le _ _
    _ ≤ ‖R - S‖ * ‖R.transpose‖ + ‖S‖ * ‖(R - S).transpose‖ :=
      add_le_add (Matrix.l2_opNorm_mul _ _) (Matrix.l2_opNorm_mul _ _)
    _ = _ := by rw [euclideanMatrix_transpose_norm, euclideanMatrix_transpose_norm]; ring

theorem realMatrix_trace_average_norm {p : ℕ} (M : Matrix (Fin p) (Fin p) ℝ)
    (hp : 0 < p) : |M.trace / (p : ℝ)| ≤ ‖M‖ := by
  have htrace : |M.trace| ≤ (p : ℝ) * ‖M‖ := by
    calc
      _ ≤ ∑ i : Fin p, |M i i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin p, ‖M‖ :=
        Finset.sum_le_sum fun i _ => euclideanMatrix_entry_le_norm M i i
      _ = _ := by simp
  rw [abs_div, abs_of_nonneg (show (0 : ℝ) ≤ (p : ℝ) from Nat.cast_nonneg p)]
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  apply (div_le_iff₀ hpR).mpr
  simpa only [mul_comm] using htrace

theorem realMatrix_trace_average_error {p : ℕ} (M N : Matrix (Fin p) (Fin p) ℝ)
    (hp : 0 < p) : |M.trace / (p : ℝ) - N.trace / (p : ℝ)| ≤ ‖M - N‖ := by
  simpa only [Matrix.trace_sub, sub_div] using realMatrix_trace_average_norm (M - N) hp

theorem gramFilledCovariance_inputs_operator_error {p q : ℕ}
    (A B : Matrix (Fin p) (Fin q) ℝ) (R S : Matrix (Fin q) (Fin p) ℝ) (c d : ℝ) :
    let P := 1 - R * A
    let Q := 1 - S * B
    ‖gramFilledCovariance A R c - gramFilledCovariance B S d‖ ≤
      (‖R‖ + ‖S‖) * ‖R - S‖ + |c - d| * ‖P‖ ^ 2 +
        |d| * (‖P‖ + ‖Q‖) * ‖P - Q‖ := by
  let P := 1 - R * A
  let Q := 1 - S * B
  have he : gramFilledCovariance A R c - gramFilledCovariance B S d =
      (R * R.transpose - S * S.transpose) +
        ((c - d) • (P * P.transpose) + d • (P * P.transpose - Q * Q.transpose)) := by
    dsimp only [gramFilledCovariance, P, Q]
    module
  have hPP : ‖P * P.transpose‖ ≤ ‖P‖ ^ 2 := by
    simpa only [euclideanMatrix_transpose_norm, pow_two] using Matrix.l2_opNorm_mul P P.transpose
  have h₁ := matrixGram_operator_error R S
  have h₂ : ‖(c - d) • (P * P.transpose)‖ ≤ |c - d| * ‖P‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left hPP (abs_nonneg _)
  have h₃ : ‖d • (P * P.transpose - Q * Q.transpose)‖ ≤
      |d| * (‖P‖ + ‖Q‖) * ‖P - Q‖ := by
    rw [norm_smul, Real.norm_eq_abs, mul_assoc]
    exact mul_le_mul_of_nonneg_left (matrixGram_operator_error P Q) (abs_nonneg _)
  have hsum := norm_add_le (R * R.transpose - S * S.transpose)
    ((c - d) • (P * P.transpose) + d • (P * P.transpose - Q * Q.transpose))
  have htail := norm_add_le ((c - d) • (P * P.transpose)) (d • (P * P.transpose - Q * Q.transpose))
  dsimp only
  rw [he]
  linarith

theorem gramFilledCovariance_operator_error {p q : ℕ}
    (A : Matrix (Fin p) (Fin q) ℝ) (R S : Matrix (Fin q) (Fin p) ℝ) (c d : ℝ) :
    let P := 1 - R * A
    let Q := 1 - S * A
    ‖gramFilledCovariance A R c - gramFilledCovariance A S d‖ ≤
      (‖R‖ + ‖S‖) * ‖R - S‖ + |c - d| * ‖P‖ ^ 2 +
        |d| * (‖P‖ + ‖Q‖) * ‖P - Q‖ :=
  gramFilledCovariance_inputs_operator_error A A R S c d

theorem kernelRemainder_operator_error {p q : ℕ}
    (A : Matrix (Fin p) (Fin q) ℝ) (R S : Matrix (Fin q) (Fin p) ℝ) :
    ‖(1 - R * A) - (1 - S * A)‖ ≤ ‖R - S‖ * ‖A‖ := by
  have he : (1 - R * A) - (1 - S * A) = (S - R) * A := by
    rw [Matrix.sub_mul]
    abel
  rw [he, norm_sub_rev R S]
  exact Matrix.l2_opNorm_mul _ _

theorem euclideanMatrix_one_norm_le (q : ℕ) : ‖(1 : Matrix (Fin q) (Fin q) ℝ)‖ ≤ 1 := by
  rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro i
  norm_num

theorem kernelRemainder_norm_le {p q : ℕ}
    (A : Matrix (Fin p) (Fin q) ℝ) (R : Matrix (Fin q) (Fin p) ℝ) :
    ‖1 - R * A‖ ≤ 1 + ‖R‖ * ‖A‖ :=
  (norm_sub_le _ _).trans (add_le_add (euclideanMatrix_one_norm_le q) (Matrix.l2_opNorm_mul R A))

theorem gramFilledCovariance_inverse_error {p q : ℕ}
    (A : Matrix (Fin p) (Fin q) ℝ) (M N : Matrix (Fin p) (Fin p) ℝ)
    (hp : 0 < p) {L H : ℝ} (hL : 0 ≤ L) (hH : 0 ≤ H)
    (hA : ‖A‖ ≤ L) (hM : ‖M‖ ≤ H) (hN : ‖N‖ ≤ H) :
    ‖gramFilledCovariance A (A.transpose * M) (M.trace / (p : ℝ)) -
      gramFilledCovariance A (A.transpose * N) (N.trace / (p : ℝ))‖ ≤
      (2 * L ^ 2 * H + (1 + L ^ 2 * H) ^ 2 + 2 * H * (1 + L ^ 2 * H) * L ^ 2) * ‖M - N‖ := by
  let R := A.transpose * M
  let S := A.transpose * N
  let P := 1 - R * A
  let Q := 1 - S * A
  let K := 1 + L ^ 2 * H
  let ε := ‖M - N‖
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hε : 0 ≤ ε := norm_nonneg _
  have hAt : ‖A.transpose‖ ≤ L := by simpa only [euclideanMatrix_transpose_norm] using hA
  have hR : ‖R‖ ≤ L * H :=
    (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul hAt hM (norm_nonneg _) hL)
  have hS : ‖S‖ ≤ L * H :=
    (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul hAt hN (norm_nonneg _) hL)
  have hRS : ‖R - S‖ ≤ L * ε := by
    dsimp only [R, S]
    rw [← Matrix.mul_sub]
    exact (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right hAt hε)
  have hrem (T : Matrix (Fin q) (Fin p) ℝ) (hT : ‖T‖ ≤ L * H) : ‖1 - T * A‖ ≤ K := by
    calc
      _ ≤ 1 + ‖T‖ * ‖A‖ := kernelRemainder_norm_le A T
      _ ≤ 1 + (L * H) * L :=
        add_le_add (le_refl 1) (mul_le_mul hT hA (norm_nonneg _) (mul_nonneg hL hH))
      _ = K := by dsimp [K]; ring
  have hP : ‖P‖ ≤ K := hrem R hR
  have hQ : ‖Q‖ ≤ K := hrem S hS
  have hPQ : ‖P - Q‖ ≤ L ^ 2 * ε := by
    calc
      _ ≤ ‖R - S‖ * ‖A‖ := kernelRemainder_operator_error A R S
      _ ≤ (L * ε) * L := mul_le_mul hRS hA (norm_nonneg _) (mul_nonneg hL hε)
      _ = _ := by ring
  have hc : |M.trace / (p : ℝ) - N.trace / (p : ℝ)| ≤ ε := realMatrix_trace_average_error M N hp
  have hd : |N.trace / (p : ℝ)| ≤ H := (realMatrix_trace_average_norm N hp).trans hN
  have h₁ : (‖R‖ + ‖S‖) * ‖R - S‖ ≤ (2 * L * H) * (L * ε) :=
    mul_le_mul (by linarith) hRS (norm_nonneg _) (by positivity)
  have h₂ : |M.trace / (p : ℝ) - N.trace / (p : ℝ)| * ‖P‖ ^ 2 ≤ ε * K ^ 2 :=
    mul_le_mul hc (pow_le_pow_left₀ (norm_nonneg _) hP 2) (sq_nonneg _) hε
  have h₃ : |N.trace / (p : ℝ)| * (‖P‖ + ‖Q‖) * ‖P - Q‖ ≤ H * (2 * K) * (L ^ 2 * ε) :=
    mul_le_mul (mul_le_mul hd (by linarith) (by positivity) hH) hPQ (norm_nonneg _) (by positivity)
  calc
    _ ≤ (‖R‖ + ‖S‖) * ‖R - S‖ +
        |M.trace / (p : ℝ) - N.trace / (p : ℝ)| * ‖P‖ ^ 2 +
        |N.trace / (p : ℝ)| * (‖P‖ + ‖Q‖) * ‖P - Q‖ :=
      gramFilledCovariance_operator_error A R S _ _
    _ ≤ (2 * L * H) * (L * ε) + ε * K ^ 2 + H * (2 * K) * (L ^ 2 * ε) :=
      add_le_add (add_le_add h₁ h₂) h₃
    _ = _ := by dsimp only [K, ε]; ring

end GeometricGaussianLHL

end GramFilledCovarianceError

section RealShapingCovariance

/-!
## The trace-average shaping target for real inputs

This is the real-matrix extension of the target approximated by the rational
algorithm. Its exact covariance has spherical image and is positive definite.
The definitions are mathematical targets, not a representation of real input.
-/

noncomputable section

open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator

namespace GeometricGaussianLHL

def realShapingCovarianceMatrix {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℝ) (w : ℝ) :
    Matrix (Fin q) (Fin q) ℝ :=
  w ^ 2 • gramFilledCovariance A (A.transpose * (A * A.transpose)⁻¹)
    ((A * A.transpose)⁻¹.trace / (p : ℝ))

theorem realGram_posDef {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℝ)
    (hA : IsUnit (A * A.transpose).det) : (A * A.transpose).PosDef := by
  have hpsd : (A * A.transpose).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_self_mul_conjTranspose A
  exact hpsd.posDef_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr hA)

theorem realShapingCovarianceMatrix_posDef {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℝ)
    (w : ℝ) (hp : 0 < p) (hA : IsUnit (A * A.transpose).det) (hw : w ≠ 0) :
    (realShapingCovarianceMatrix A w).PosDef := by
  let : NeZero p := ⟨hp.ne'⟩
  apply Matrix.PosDef.smul _ (sq_pos_of_ne_zero hw)
  apply gramFilledCovariance_posDef
  exact div_pos (realGram_posDef A hA).inv.trace_pos (by exact_mod_cast hp)

theorem realShapingCovarianceMatrix_image {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℝ)
    (w : ℝ) (hA : IsUnit (A * A.transpose).det) :
    A * realShapingCovarianceMatrix A w * A.transpose =
      w ^ 2 • (1 : Matrix (Fin p) (Fin p) ℝ) := by
  let R := A.transpose * (A * A.transpose)⁻¹
  let P := 1 - R * A
  have hAR : A * R = 1 := by
    dsimp only [R]
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hA]
  have hAP : A * P = 0 := by
    dsimp only [P]
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hAR, Matrix.one_mul, sub_self]
  have hgram (T : Matrix (Fin q) (Fin p) ℝ) :
      A * (T * T.transpose) * A.transpose = (A * T) * (A * T).transpose := by
    rw [Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]
  have hproj : A * (P * P.transpose) * A.transpose = 0 := by
    rw [← Matrix.mul_assoc, hAP, Matrix.zero_mul, Matrix.zero_mul]
  change A * (w ^ 2 • (R * R.transpose + _ • (P * P.transpose))) * A.transpose = _
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_smul, Matrix.smul_mul, hgram, hAR, Matrix.transpose_one,
    Matrix.one_mul, hproj, smul_zero, add_zero]

theorem realShapingCovarianceMatrix_rat {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℚ)
    (w : ℚ) (hA : IsUnit (A * A.transpose).det) :
    realShapingCovarianceMatrix (A.map (Rat.castHom ℝ)) (w : ℝ) =
      (rationalShapingCovarianceMatrix A w).map (Rat.castHom ℝ) := by
  rw [← gramFilledCovariance_exact A w hA]
  rw [show (w ^ 2 • gramFilledCovariance A (rationalRightInverseMatrix A)
      (rationalShapingKernelFill A)).map (Rat.castHom ℝ) =
      (w : ℝ) ^ 2 • (gramFilledCovariance A (rationalRightInverseMatrix A)
        (rationalShapingKernelFill A)).map (Rat.castHom ℝ) by
    ext i j
    simp]
  rw [gramFilledCovariance_rat_cast]
  have hinv := rationalGramInverse_real A hA
  rw [Matrix.map_mul] at hinv
  change ((A * A.transpose)⁻¹).map (Rat.castHom ℝ) =
    (A.map (Rat.castHom ℝ) * (A.map (Rat.castHom ℝ)).transpose)⁻¹ at hinv
  have hr : (rationalRightInverseMatrix A).map (Rat.castHom ℝ) =
      (A.map (Rat.castHom ℝ)).transpose *
        (A.map (Rat.castHom ℝ) * (A.map (Rat.castHom ℝ)).transpose)⁻¹ := by
    rw [rationalRightInverseMatrix, Matrix.map_mul, hinv]
    rfl
  have hc : (rationalShapingKernelFill A : ℝ) =
      (A.map (Rat.castHom ℝ) * (A.map (Rat.castHom ℝ)).transpose)⁻¹.trace / (p : ℝ) := by
    rw [← hinv, ← AddMonoidHom.map_trace]
    simp only [rationalShapingKernelFill, Rat.cast_div, Rat.cast_natCast]
    rfl
  rw [hr, hc]
  rfl

end GeometricGaussianLHL
end

end RealShapingCovariance

section MatrixSquareRootStability

/-!
## A dimension-independent square-root perturbation bound

For positive semidefinite real matrices, the square-root map is one-half
Hölder in Euclidean operator norm. The proof tests the difference of squares
on an eigenvector of the difference of the positive square roots.
-/

open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator

namespace GeometricGaussianLHL

theorem realMatrix_quadratic_abs_le_norm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    |(x : Fin n → ℝ) ⬝ᵥ (A *ᵥ x)| ≤ ‖A‖ * ‖x‖ ^ 2 := by
  let T := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A
  rw [← Matrix.inner_toEuclideanCLM]
  calc
    _ ≤ ‖x‖ * ‖T x‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖T‖ * ‖x‖) := mul_le_mul_of_nonneg_left (T.le_opNorm x) (norm_nonneg _)
    _ = _ := by dsimp only [T]; rw [Matrix.l2_opNorm_toEuclideanCLM]; ring

private theorem nonneg_difference_sq_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a - b) ^ 2 ≤ |a ^ 2 - b ^ 2| := by
  by_cases hab : a ≤ b
  · have hs := pow_le_pow_left₀ ha hab 2
    rw [abs_of_nonpos (sub_nonpos.mpr hs)]
    nlinarith [mul_nonneg ha (sub_nonneg.mpr hab)]
  · have hba : b ≤ a := le_of_not_ge hab
    have hs := pow_le_pow_left₀ hb hba 2
    rw [abs_of_nonneg (sub_nonneg.mpr hs)]
    nlinarith [mul_nonneg hb (sub_nonneg.mpr hba)]

theorem posSemidef_square_difference_norm {n : ℕ}
    (X Y : Matrix (Fin n) (Fin n) ℝ) (hX : X.PosSemidef) (hY : Y.PosSemidef) :
    ‖X - Y‖ ≤ Real.sqrt ‖X ^ 2 - Y ^ 2‖ := by
  have hE := hX.isHermitian.sub hY.isHermitian
  have heach (i : Fin n) : |hE.eigenvalues i| ≤ Real.sqrt ‖X ^ 2 - Y ^ 2‖ := by
    let x := hE.eigenvectorBasis i
    let v : Fin n → ℝ := x
    let e := hE.eigenvalues i
    have hx : ‖x‖ = 1 := hE.eigenvectorBasis.orthonormal.1 i
    have hxx : v ⬝ᵥ v = 1 := by
      have h := EuclideanSpace.inner_eq_star_dotProduct x x
      simp only [star_trivial] at h
      rw [← h, real_inner_self_eq_norm_sq, hx]
      norm_num
    have he : (X - Y) *ᵥ v = e • v := hE.mulVec_eigenvectorBasis i
    have heleft : v ᵥ* (X - Y) = e • v := by
      rw [← Matrix.mulVec_transpose, Matrix.isHermitian_iff_isSymm.mp hE]
      exact he
    let a := v ⬝ᵥ (X *ᵥ v)
    let b := v ⬝ᵥ (Y *ᵥ v)
    have ha : 0 ≤ a := by simpa only [star_trivial] using hX.dotProduct_mulVec_nonneg v
    have hb : 0 ≤ b := by simpa only [star_trivial] using hY.dotProduct_mulVec_nonneg v
    have hab : a - b = e := by
      have h := congrArg (fun z => v ⬝ᵥ z) he
      simpa only [Matrix.sub_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul, hxx, mul_one] using h
    have h₁ : v ⬝ᵥ ((X * (X - Y)) *ᵥ v) = e * a := by
      rw [← Matrix.mulVec_mulVec, he, Matrix.mulVec_smul, dotProduct_smul]
      rfl
    have h₂ : v ⬝ᵥ (((X - Y) * Y) *ᵥ v) = e * b := by
      rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, heleft, smul_dotProduct]
      rfl
    have hquad : v ⬝ᵥ ((X ^ 2 - Y ^ 2) *ᵥ v) = a ^ 2 - b ^ 2 := by
      have hs : X ^ 2 - Y ^ 2 = X * (X - Y) + (X - Y) * Y := by noncomm_ring
      rw [hs, Matrix.add_mulVec, dotProduct_add, h₁, h₂, ← hab]
      ring
    have hbound := realMatrix_quadratic_abs_le_norm (X ^ 2 - Y ^ 2) x
    change |v ⬝ᵥ ((X ^ 2 - Y ^ 2) *ᵥ v)| ≤ _ at hbound
    rw [hquad, hx, one_pow, mul_one] at hbound
    have he2 : e ^ 2 ≤ ‖X ^ 2 - Y ^ 2‖ := by
      rw [← hab]
      exact (nonneg_difference_sq_le ha hb).trans hbound
    apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
    simpa only [sq_abs, Real.sq_sqrt (norm_nonneg _)] using he2
  rw [hE.spectral_theorem, unitaryConj_matrix_norm, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
  intro i
  exact heach i

theorem matrix_sqrt_operator_holder {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    ‖CFC.sqrt A - CFC.sqrt B‖ ≤ Real.sqrt ‖A - B‖ := by
  have h := posSemidef_square_difference_norm (CFC.sqrt A) (CFC.sqrt B)
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _))
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _))
  simpa only [pow_two, CFC.sqrt_mul_sqrt_self A hA.nonneg, CFC.sqrt_mul_sqrt_self B hB.nonneg] using h

theorem matrix_positive_shift_posDef {n : ℕ} (R S : Matrix (Fin n) (Fin n) ℝ)
    (hR : R.IsHermitian) (hS : S.PosDef) {ε : ℝ} (herr : ‖R - S‖ ≤ ε) :
    (R + ε • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef := by
  classical
  rcases isEmpty_or_nonempty (Fin n) with hn | hn
  · have := hn
    rw [show R + ε • (1 : Matrix (Fin n) (Fin n) ℝ) = S from Subsingleton.elim _ _]
    exact hS
  · have := hn
    have he : (-ε) • (1 : Matrix (Fin n) (Fin n) ℝ) ≤ R - S := by
      rw [← Algebra.algebraMap_eq_smul_one]
      apply algebraMap_le_of_le_spectrum (ha := hR.sub hS.isHermitian)
      intro x hx
      have hn : |x| ≤ ‖R - S‖ := by
        simpa only [Real.norm_eq_abs] using spectrum.norm_le_norm_of_mem hx
      linarith [neg_abs_le x]
    have hz : (0 : Matrix (Fin n) (Fin n) ℝ) ≤ R + ε • 1 - S := by
      calc
        (0 : Matrix (Fin n) (Fin n) ℝ) = (-ε) • 1 + ε • 1 := by module
        _ ≤ (R - S) + ε • 1 := add_le_add he le_rfl
        _ = _ := by abel
    have h := hS.add_posSemidef (Matrix.nonneg_iff_posSemidef.mp hz)
    convert h using 1
    abel

theorem matrix_positive_shift_error {n : ℕ} (R S : Matrix (Fin n) (Fin n) ℝ)
    {ε : ℝ} (hε : 0 ≤ ε) (herr : ‖R - S‖ ≤ ε) :
    ‖R + ε • (1 : Matrix (Fin n) (Fin n) ℝ) - S‖ ≤ 2 * ε := by
  have hI : ‖ε • (1 : Matrix (Fin n) (Fin n) ℝ)‖ ≤ ε := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hε]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (euclideanMatrix_one_norm_le n) hε
  have he : R + ε • (1 : Matrix (Fin n) (Fin n) ℝ) - S = (R - S) + ε • 1 := by abel
  rw [he]
  exact (norm_add_le _ _).trans (by linarith)

end GeometricGaussianLHL

end MatrixSquareRootStability

section RationalShapingApproximation

/-!
## An input-derived precision budget for rational shaping covariance

The covariance uses the computed positive inverse approximation. Its operator
error is controlled by a dyadic budget computed from the rational Gram input
and width, rather than unknown inverse norms or a supplied conditioning bound.
Square-root perturbation and arithmetic cost analysis are separate results.
-/

open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator

namespace GeometricGaussianLHL

theorem rationalRectangular_norm_le_gram_input {p q : ℕ}
    (A : Matrix (Fin p) (Fin q) ℚ) :
    ‖A.map (Rat.castHom ℝ)‖ ≤ (2 : ℝ) ^ rationalMatrixNormalizationExponent (A * A.transpose) := by
  let Ar := A.map (Rat.castHom ℝ)
  have he : ‖((A * A.transpose).map (Rat.castHom ℝ))‖ = ‖Ar‖ ^ 2 := by
    rw [Matrix.map_mul]
    change ‖Ar * Ar.transpose‖ = ‖Ar‖ ^ 2
    have h := Matrix.l2_opNorm_conjTranspose_mul_self Ar.transpose
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose,
      euclideanMatrix_transpose_norm, pow_two] using h
  have hg := rationalMatrix_real_norm_le_input_pow (A * A.transpose)
  change ‖((A * A.transpose).map (Rat.castHom ℝ))‖ ≤ _ at hg
  rw [he] at hg
  have h1 : 1 ≤ (2 : ℝ) ^ rationalMatrixNormalizationExponent (A * A.transpose) := one_le_pow₀ (by norm_num)
  change ‖Ar‖ ≤ _
  nlinarith [sq_nonneg (‖Ar‖ - 1)]

theorem shapingCovariance_dyadic_coefficient (q B s : ℕ) (w : ℝ)
    (hw : |w| ≤ (2 : ℝ) ^ (2 * s)) :
    let L := (2 : ℝ) ^ q
    let H := (2 : ℝ) ^ (B + 1)
    w ^ 2 * (2 * L ^ 2 * H + (1 + L ^ 2 * H) ^ 2 + 2 * H * (1 + L ^ 2 * H) * L ^ 2) ≤
      (2 : ℝ) ^ (4 * q + 2 * B + 4 * s + 6) := by
  let Z := (2 : ℝ) ^ (2 * q + B + 1)
  have hZ : 1 ≤ Z := one_le_pow₀ (by norm_num)
  have hZ2 : Z ≤ Z ^ 2 := by nlinarith [sq_nonneg (Z - 1)]
  have heZ : ((2 : ℝ) ^ q) ^ 2 * (2 : ℝ) ^ (B + 1) = Z := by
    simp only [Z, ← pow_mul, ← pow_add]
    congr 1
    ring
  have hF : 2 * ((2 : ℝ) ^ q) ^ 2 * (2 : ℝ) ^ (B + 1) +
      (1 + ((2 : ℝ) ^ q) ^ 2 * (2 : ℝ) ^ (B + 1)) ^ 2 +
      2 * (2 : ℝ) ^ (B + 1) * (1 + ((2 : ℝ) ^ q) ^ 2 * (2 : ℝ) ^ (B + 1)) * ((2 : ℝ) ^ q) ^ 2 ≤
      (2 : ℝ) ^ (4 * q + 2 * B + 6) := by
    calc
      _ = 1 + 6 * Z + 3 * Z ^ 2 := by rw [← heZ]; ring
      _ ≤ 16 * Z ^ 2 := by nlinarith
      _ = _ := by
        rw [show (16 : ℝ) = 2 ^ 4 by norm_num]
        dsimp only [Z]
        rw [← pow_mul, ← pow_add]
        congr 1
        ring
  have hW : w ^ 2 ≤ (2 : ℝ) ^ (4 * s) := by
    calc
      w ^ 2 = |w| ^ 2 := (sq_abs w).symm
      _ ≤ ((2 : ℝ) ^ (2 * s)) ^ 2 := pow_le_pow_left₀ (abs_nonneg w) hw 2
      _ = _ := by
        rw [← pow_mul]
        congr 1
        omega
  dsimp only
  calc
    _ ≤ (2 : ℝ) ^ (4 * s) * (2 : ℝ) ^ (4 * q + 2 * B + 6) :=
      mul_le_mul hW hF (by positivity) (by positivity)
    _ = _ := by rw [← pow_add]; congr 1; omega

theorem scaledGramFilledCovariance_rat_cast {p q : ℕ}
    (A : Matrix (Fin p) (Fin q) ℚ) (M : Matrix (Fin p) (Fin p) ℚ) (w : ℚ) :
    (w ^ 2 • gramFilledCovariance A (A.transpose * M) (M.trace / (p : ℚ))).map (Rat.castHom ℝ) =
      (w : ℝ) ^ 2 • gramFilledCovariance (A.map (Rat.castHom ℝ))
        ((A.map (Rat.castHom ℝ)).transpose * M.map (Rat.castHom ℝ))
        ((M.map (Rat.castHom ℝ)).trace / (p : ℝ)) := by
  have he : (w ^ 2 • gramFilledCovariance A (A.transpose * M) (M.trace / (p : ℚ))).map (Rat.castHom ℝ) =
      (w : ℝ) ^ 2 • (gramFilledCovariance A (A.transpose * M) (M.trace / (p : ℚ))).map (Rat.castHom ℝ) := by
    ext i j
    simp [Matrix.map_apply, Matrix.smul_apply]
  rw [he, gramFilledCovariance_rat_cast, Matrix.map_mul]
  have ht := AddMonoidHom.map_trace (Rat.castHom ℝ) M
  simp only [Rat.cast_div, Rat.cast_natCast]
  rw [← ht]
  rfl

def rationalShapingPrecisionGuard {p q : ℕ}
    (A : Matrix (Fin p) (Fin q) ℚ) (w : ℚ) : ℕ :=
  4 * rationalMatrixNormalizationExponent (A * A.transpose) +
    2 * rationalMatrixConditionExponent (A * A.transpose) + 4 * rationalMagnitudeBits w + 6

theorem rationalShapingApproxCovariance_prescribed_error {p q : ℕ} (t : ℕ)
    (A : Matrix (Fin p) (Fin q) ℚ) (w : ℚ) (hp : 0 < p)
    (hA : IsUnit (A * A.transpose).det) :
    ‖(rationalShapingApproxCovariance (t + rationalShapingPrecisionGuard A w) A w).map
        (Rat.castHom ℝ) - (rationalShapingCovarianceMatrix A w).map (Rat.castHom ℝ)‖ ≤
      1 / (2 : ℝ) ^ t := by
  let G := A * A.transpose
  let s := t + rationalShapingPrecisionGuard A w
  let M := rationalInverseApprox s G
  let N := G⁻¹
  let Ar := A.map (Rat.castHom ℝ)
  let Mr := M.map (Rat.castHom ℝ)
  let Nr := N.map (Rat.castHom ℝ)
  let L := (2 : ℝ) ^ rationalMatrixNormalizationExponent G
  let H := (2 : ℝ) ^ (rationalMatrixConditionExponent G + 1)
  let F := 2 * L ^ 2 * H + (1 + L ^ 2 * H) ^ 2 + 2 * H * (1 + L ^ 2 * H) * L ^ 2
  have hG : (G.map (Rat.castHom ℝ)).PosDef := rationalGram_real_posDef A hA
  have hNr : Nr = (G.map (Rat.castHom ℝ))⁻¹ := rationalGramInverse_real A hA
  have hMnorm : ‖Mr‖ ≤ H := rationalInverseApprox_norm_le s G hG
  have hNnorm : ‖Nr‖ ≤ H := by
    rw [hNr]
    exact (rationalInverseTarget_norm_le G hG).trans
      (pow_le_pow_right₀ (by norm_num) (by omega))
  have hAnorm : ‖Ar‖ ≤ L := rationalRectangular_norm_le_gram_input A
  have hMN : ‖Mr - Nr‖ ≤ 1 / (2 : ℝ) ^ s := by
    rw [hNr]
    exact rationalInverseApprox_matrix_error s G hG
  have hraw : ‖gramFilledCovariance Ar (Ar.transpose * Mr) (Mr.trace / (p : ℝ)) -
      gramFilledCovariance Ar (Ar.transpose * Nr) (Nr.trace / (p : ℝ))‖ ≤ F * ‖Mr - Nr‖ :=
    gramFilledCovariance_inverse_error Ar Mr Nr hp (by positivity) (by positivity) hAnorm hMnorm hNnorm
  have hcoef : (w : ℝ) ^ 2 * F ≤ (2 : ℝ) ^ rationalShapingPrecisionGuard A w :=
    shapingCovariance_dyadic_coefficient (rationalMatrixNormalizationExponent G)
      (rationalMatrixConditionExponent G) (rationalMagnitudeBits w) (w : ℝ)
      (rationalWidth_abs_le_input_pow w)
  have hCf : (rationalShapingApproxCovariance (t + rationalShapingPrecisionGuard A w) A w).map
      (Rat.castHom ℝ) = (w : ℝ) ^ 2 •
        gramFilledCovariance Ar (Ar.transpose * Mr) (Mr.trace / (p : ℝ)) := by
    change (materializeMatrix (w ^ 2 • gramFilledCovariance A (A.transpose * M)
      (M.trace / (p : ℚ)))).map (Rat.castHom ℝ) = _
    rw [materializeMatrix_eq]
    exact scaledGramFilledCovariance_rat_cast A M w
  have hCt : (rationalShapingCovarianceMatrix A w).map (Rat.castHom ℝ) = (w : ℝ) ^ 2 •
      gramFilledCovariance Ar (Ar.transpose * Nr) (Nr.trace / (p : ℝ)) := by
    rw [← gramFilledCovariance_exact A w hA]
    exact scaledGramFilledCovariance_rat_cast A N w
  rw [hCf, hCt, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (w : ℝ))]
  calc
    _ ≤ (w : ℝ) ^ 2 * (F * ‖Mr - Nr‖) := mul_le_mul_of_nonneg_left hraw (sq_nonneg _)
    _ = ((w : ℝ) ^ 2 * F) * ‖Mr - Nr‖ := by ring
    _ ≤ (2 : ℝ) ^ rationalShapingPrecisionGuard A w * (1 / (2 : ℝ) ^ s) :=
      mul_le_mul hcoef hMN (norm_nonneg _) (by positivity)
    _ = _ := by dsimp only [s]; rw [pow_add]; field_simp

end GeometricGaussianLHL

end RationalShapingApproximation

section RationalShapingFillBounds

/-!
## Sharp admissible bounds for the rational kernel fill

The inverse-Gram trace average lies between the reciprocal squared input
operator norm and the squared minimum-norm right inverse norm. These are
exact geometric bounds, independent of the approximation algorithm.
-/

open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator

namespace GeometricGaussianLHL

theorem matrix_gram_trace_average_le {p q : ℕ} (R : Matrix (Fin q) (Fin p) ℝ)
    (hp : 0 < p) : (R.transpose * R).trace / (p : ℝ) ≤ ‖R‖ ^ 2 := by
  calc
    _ ≤ |(R.transpose * R).trace / (p : ℝ)| := le_abs_self _
    _ ≤ ‖R.transpose * R‖ := realMatrix_trace_average_norm _ hp
    _ = _ := by simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, pow_two] using
      Matrix.l2_opNorm_conjTranspose_mul_self R

theorem matrix_rightInverse_trace_average_lower {p q : ℕ}
    (A : Matrix (Fin p) (Fin q) ℝ) (R : Matrix (Fin q) (Fin p) ℝ)
    (hp : 0 < p) (hAR : A * R = 1) :
    1 ≤ ‖A‖ ^ 2 * ((R.transpose * R).trace / (p : ℝ)) := by
  have heach (i : Fin p) : 1 ≤ ‖A‖ ^ 2 * (R.transpose * R) i i := by
    let e : EuclideanSpace ℝ (Fin p) := PiLp.single 2 i 1
    let x := Matrix.toEuclideanLin R e
    have he : ‖e‖ = 1 := by simp [e]
    have hAx : Matrix.toEuclideanLin A x = e := by
      change ((Matrix.toLpLin 2 2 A).comp (Matrix.toLpLin 2 2 R)) e = e
      rw [← Matrix.toLpLin_mul_same, hAR, Matrix.toLpLin_one]
      rfl
    have hx : (x : Fin q → ℝ) = fun j => R j i := by
      change R *ᵥ (Pi.single i 1) = _
      rw [Matrix.mulVec_single_one]
      rfl
    have hx2 : ‖x‖ ^ 2 = (R.transpose * R) i i := by
      rw [EuclideanSpace.real_norm_sq_eq]
      change (∑ j, (x j) ^ 2) = ∑ j, R j i * R j i
      simp only [congrFun hx, pow_two]
    have hb := (Matrix.toEuclideanLin A).toContinuousLinearMap.le_opNorm x
    change ‖Matrix.toEuclideanLin A x‖ ≤ ‖A‖ * ‖x‖ at hb
    rw [hAx, he] at hb
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hb 2
    simpa only [one_pow, mul_pow, hx2] using h
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => heach i)
  have hb : (p : ℝ) ≤ ‖A‖ ^ 2 * (R.transpose * R).trace := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one, ← Finset.mul_sum, Matrix.trace, Matrix.diag_apply] using hs
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  rw [← mul_div_assoc]
  exact (le_div_iff₀ hpR).mpr (by simpa only [one_mul] using hb)

theorem rationalRightInverseMatrix_gram {p q : ℕ}
    (A : Matrix (Fin p) (Fin q) ℚ) (hA : IsUnit (A * A.transpose).det) :
    (rationalRightInverseMatrix A).transpose * rationalRightInverseMatrix A =
      (A * A.transpose)⁻¹ := by
  have hg : ((A * A.transpose)⁻¹).transpose = (A * A.transpose)⁻¹ := by
    simp only [Matrix.transpose_nonsing_inv, Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [rationalRightInverseMatrix, Matrix.transpose_mul, Matrix.transpose_transpose, hg]
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc A, Matrix.mul_nonsing_inv _ hA, Matrix.mul_one]

theorem rationalShapingKernelFill_real_trace {p q : ℕ}
    (A : Matrix (Fin p) (Fin q) ℚ) (hA : IsUnit (A * A.transpose).det) :
    (rationalShapingKernelFill A : ℝ) =
      (((rationalRightInverseMatrix A).map (Rat.castHom ℝ)).transpose *
        (rationalRightInverseMatrix A).map (Rat.castHom ℝ)).trace / (p : ℝ) := by
  have hm := congrArg (fun M => M.map (Rat.castHom ℝ)) (rationalRightInverseMatrix_gram A hA)
  rw [Matrix.map_mul] at hm
  change ((rationalRightInverseMatrix A).map (Rat.castHom ℝ)).transpose *
      (rationalRightInverseMatrix A).map (Rat.castHom ℝ) = _ at hm
  rw [hm, ← AddMonoidHom.map_trace]
  simp only [rationalShapingKernelFill, Rat.cast_div, Rat.cast_natCast]
  rfl

theorem rationalShapingKernelFill_sharp_bounds {p q : ℕ}
    (A : Matrix (Fin p) (Fin q) ℚ) (hp : 0 < p) (hA : IsUnit (A * A.transpose).det) :
    1 ≤ ‖A.map (Rat.castHom ℝ)‖ ^ 2 * (rationalShapingKernelFill A : ℝ) ∧
      (rationalShapingKernelFill A : ℝ) ≤ ‖(rationalRightInverseMatrix A).map (Rat.castHom ℝ)‖ ^ 2 := by
  have hAR := congrArg (fun M => M.map (Rat.castHom ℝ)) (rationalRightInverseMatrix_right_inverse A hA)
  rw [Matrix.map_mul, Matrix.map_one (Rat.castHom ℝ) (map_zero _) (map_one _)] at hAR
  rw [rationalShapingKernelFill_real_trace A hA]
  exact ⟨matrix_rightInverse_trace_average_lower _ _ hp hAR, matrix_gram_trace_average_le _ hp⟩

end GeometricGaussianLHL

end RationalShapingFillBounds

section ShapingInputStability

/-!
## Error from perturbing the shaping input

All estimates use the Euclidean operator norm. Bounds on the input norm and
inverse-Gram norm are explicit; obtaining those bounds and the rational
approximation from an input representation is a separate computational task.
-/

open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator

namespace GeometricGaussianLHL

theorem matrixProduct_operator_error {p q r : ℕ}
    (A C : Matrix (Fin p) (Fin q) ℝ) (B D : Matrix (Fin q) (Fin r) ℝ) :
    ‖A * B - C * D‖ ≤ ‖A - C‖ * ‖B‖ + ‖C‖ * ‖B - D‖ := by
  have he : A * B - C * D = (A - C) * B + C * (B - D) := by
    rw [Matrix.sub_mul, Matrix.mul_sub]
    abel
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add (Matrix.l2_opNorm_mul _ _) (Matrix.l2_opNorm_mul _ _))

theorem kernelRemainder_inputs_operator_error {p q : ℕ}
    (A B : Matrix (Fin p) (Fin q) ℝ) (R S : Matrix (Fin q) (Fin p) ℝ) :
    ‖(1 - R * A) - (1 - S * B)‖ ≤ ‖R - S‖ * ‖A‖ + ‖S‖ * ‖A - B‖ := by
  have he : (1 - R * A) - (1 - S * B) = -(R * A - S * B) := by abel
  rw [he, norm_neg]
  exact matrixProduct_operator_error R S A B

theorem matrixInverse_operator_error {p : ℕ} (M N : Matrix (Fin p) (Fin p) ℝ)
    (hM : IsUnit M.det) (hN : IsUnit N.det) :
    ‖M⁻¹ - N⁻¹‖ ≤ ‖M⁻¹‖ * ‖N⁻¹‖ * ‖M - N‖ := by
  have hu : IsUnit M ↔ IsUnit N :=
    ⟨fun _ => (Matrix.isUnit_iff_isUnit_det _).mpr hN,
      fun _ => (Matrix.isUnit_iff_isUnit_det _).mpr hM⟩
  rw [Matrix.inv_sub_inv hu]
  calc
    _ ≤ ‖M⁻¹ * (N - M)‖ * ‖N⁻¹‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ (‖M⁻¹‖ * ‖N - M‖) * ‖N⁻¹‖ :=
      mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
    _ = _ := by rw [norm_sub_rev N M]; ring

theorem matrixGramInverse_input_error {p q : ℕ} (A B : Matrix (Fin p) (Fin q) ℝ)
    (hA : IsUnit (A * A.transpose).det) (hB : IsUnit (B * B.transpose).det)
    {L H : ℝ} (_hL : 0 ≤ L) (hH : 0 ≤ H) (hAn : ‖A‖ ≤ L) (hBn : ‖B‖ ≤ L)
    (hAi : ‖(A * A.transpose)⁻¹‖ ≤ H) (hBi : ‖(B * B.transpose)⁻¹‖ ≤ H) :
    ‖(A * A.transpose)⁻¹ - (B * B.transpose)⁻¹‖ ≤ 2 * L * H ^ 2 * ‖A - B‖ := by
  calc
    _ ≤ ‖(A * A.transpose)⁻¹‖ * ‖(B * B.transpose)⁻¹‖ *
        ‖A * A.transpose - B * B.transpose‖ := matrixInverse_operator_error _ _ hA hB
    _ ≤ H * H * ((L + L) * ‖A - B‖) := by
      gcongr
      exact (matrixGram_operator_error A B).trans
        (mul_le_mul_of_nonneg_right (add_le_add hAn hBn) (norm_nonneg _))
    _ = _ := by ring

theorem gramFilledCovariance_matrix_error {p q : ℕ}
    (A B : Matrix (Fin p) (Fin q) ℝ) (M : Matrix (Fin p) (Fin p) ℝ)
    (hp : 0 < p) {L H : ℝ} (hL : 0 ≤ L) (hH : 0 ≤ H)
    (hA : ‖A‖ ≤ L) (hB : ‖B‖ ≤ L) (hM : ‖M‖ ≤ H) :
    ‖gramFilledCovariance A (A.transpose * M) (M.trace / (p : ℝ)) -
      gramFilledCovariance B (B.transpose * M) (M.trace / (p : ℝ))‖ ≤
      (2 * L * H ^ 2 + 4 * L * H ^ 2 * (1 + L ^ 2 * H)) * ‖A - B‖ := by
  let R := A.transpose * M
  let S := B.transpose * M
  let P := 1 - R * A
  let Q := 1 - S * B
  let K := 1 + L ^ 2 * H
  let ε := ‖A - B‖
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hε : 0 ≤ ε := norm_nonneg _
  have hAt : ‖A.transpose‖ ≤ L := by simpa only [euclideanMatrix_transpose_norm] using hA
  have hBt : ‖B.transpose‖ ≤ L := by simpa only [euclideanMatrix_transpose_norm] using hB
  have hR : ‖R‖ ≤ L * H :=
    (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul hAt hM (norm_nonneg _) hL)
  have hS : ‖S‖ ≤ L * H :=
    (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul hBt hM (norm_nonneg _) hL)
  have hRS : ‖R - S‖ ≤ H * ε := by
    dsimp only [R, S]
    rw [← Matrix.sub_mul, ← Matrix.transpose_sub]
    calc
      _ ≤ ‖(A - B).transpose‖ * ‖M‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ ε * H := by rw [euclideanMatrix_transpose_norm]; exact mul_le_mul_of_nonneg_left hM hε
      _ = _ := mul_comm _ _
  have hrem (D : Matrix (Fin p) (Fin q) ℝ) (T : Matrix (Fin q) (Fin p) ℝ)
      (hD : ‖D‖ ≤ L) (hT : ‖T‖ ≤ L * H) : ‖1 - T * D‖ ≤ K := by
    calc
      _ ≤ 1 + ‖T‖ * ‖D‖ := kernelRemainder_norm_le D T
      _ ≤ 1 + (L * H) * L :=
        add_le_add (le_refl 1) (mul_le_mul hT hD (norm_nonneg _) (mul_nonneg hL hH))
      _ = K := by dsimp only [K]; ring
  have hP : ‖P‖ ≤ K := hrem A R hA hR
  have hQ : ‖Q‖ ≤ K := hrem B S hB hS
  have hPQ : ‖P - Q‖ ≤ 2 * L * H * ε := by
    calc
      _ ≤ ‖R - S‖ * ‖A‖ + ‖S‖ * ‖A - B‖ := kernelRemainder_inputs_operator_error A B R S
      _ ≤ (H * ε) * L + (L * H) * ε :=
        add_le_add (mul_le_mul hRS hA (norm_nonneg _) (mul_nonneg hH hε))
          (mul_le_mul_of_nonneg_right hS hε)
      _ = _ := by ring
  have hc : |M.trace / (p : ℝ)| ≤ H := (realMatrix_trace_average_norm M hp).trans hM
  have hmain := gramFilledCovariance_inputs_operator_error A B R S
    (M.trace / (p : ℝ)) (M.trace / (p : ℝ))
  dsimp only at hmain
  simp only [sub_self, abs_zero, zero_mul, add_zero] at hmain
  have h₁ : (‖R‖ + ‖S‖) * ‖R - S‖ ≤ (2 * L * H) * (H * ε) :=
    mul_le_mul (by linarith) hRS (norm_nonneg _) (by positivity)
  have h₂ : |M.trace / (p : ℝ)| * (‖P‖ + ‖Q‖) * ‖P - Q‖ ≤
      H * (2 * K) * (2 * L * H * ε) :=
    mul_le_mul (mul_le_mul hc (by linarith) (by positivity) hH) hPQ (norm_nonneg _) (by positivity)
  calc
    _ ≤ (‖R‖ + ‖S‖) * ‖R - S‖ + |M.trace / (p : ℝ)| * (‖P‖ + ‖Q‖) * ‖P - Q‖ := hmain
    _ ≤ (2 * L * H) * (H * ε) + H * (2 * K) * (2 * L * H * ε) := add_le_add h₁ h₂
    _ = _ := by dsimp only [K, ε]; ring

theorem gramFilledCovariance_inverse_norm_le {p q : ℕ}
    (A : Matrix (Fin p) (Fin q) ℝ) (M : Matrix (Fin p) (Fin p) ℝ)
    (hp : 0 < p) {L H : ℝ} (hL : 0 ≤ L) (hH : 0 ≤ H) (hA : ‖A‖ ≤ L) (hM : ‖M‖ ≤ H) :
    ‖gramFilledCovariance A (A.transpose * M) (M.trace / (p : ℝ))‖ ≤
      (L * H) ^ 2 + H * (1 + L ^ 2 * H) ^ 2 := by
  let R := A.transpose * M
  let P := 1 - R * A
  have hR : ‖R‖ ≤ L * H := by
    apply (Matrix.l2_opNorm_mul _ _).trans
    rw [euclideanMatrix_transpose_norm]
    exact mul_le_mul hA hM (norm_nonneg _) hL
  have hP : ‖P‖ ≤ 1 + L ^ 2 * H := by
    calc
      _ ≤ 1 + ‖R‖ * ‖A‖ := kernelRemainder_norm_le A R
      _ ≤ 1 + (L * H) * L :=
        add_le_add (le_refl 1) (mul_le_mul hR hA (norm_nonneg _) (mul_nonneg hL hH))
      _ = _ := by ring
  have hc : |M.trace / (p : ℝ)| ≤ H := (realMatrix_trace_average_norm M hp).trans hM
  change ‖R * R.transpose + (M.trace / (p : ℝ)) • (P * P.transpose)‖ ≤ _
  calc
    _ ≤ ‖R * R.transpose‖ + ‖(M.trace / (p : ℝ)) • (P * P.transpose)‖ := norm_add_le _ _
    _ ≤ ‖R‖ ^ 2 + |M.trace / (p : ℝ)| * ‖P‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs]
      apply add_le_add
      · simpa only [euclideanMatrix_transpose_norm, pow_two] using Matrix.l2_opNorm_mul R R.transpose
      · apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        simpa only [euclideanMatrix_transpose_norm, pow_two] using Matrix.l2_opNorm_mul P P.transpose
    _ ≤ _ := by gcongr

end GeometricGaussianLHL

end ShapingInputStability

section RationalShapingGeometry

/-!
## The rational right inverse and the intrinsic kernel geometry

The rational inverse-Gram formula is the minimum-norm right inverse after
conversion to real Euclidean coordinates. Its complementary projector is
the actual orthogonal projection onto the kernel.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace GeometricGaussianLHL

theorem rationalMatrix_real_surjective {p q : ℕ}
    (A : Matrix (Fin p) (Fin q) ℚ) (hA : IsUnit (A * A.transpose).det) :
    Function.Surjective (Matrix.toEuclideanLin (A.map (Rat.castHom ℝ))) := by
  have hAR := congrArg (fun M => M.map (Rat.castHom ℝ))
    (rationalRightInverseMatrix_right_inverse A hA)
  rw [Matrix.map_mul, Matrix.map_one (Rat.castHom ℝ) (map_zero _) (map_one _)] at hAR
  intro y
  refine ⟨Matrix.toEuclideanLin ((rationalRightInverseMatrix A).map (Rat.castHom ℝ)) y, ?_⟩
  change ((Matrix.toLpLin 2 2 (A.map (Rat.castHom ℝ))).comp
    (Matrix.toLpLin 2 2 ((rationalRightInverseMatrix A).map (Rat.castHom ℝ)))) y = y
  rw [← Matrix.toLpLin_mul_same, hAR, Matrix.toLpLin_one]
  rfl

theorem rationalRightInverseMatrix_minimumNorm {p q : ℕ}
    (A : Matrix (Fin p) (Fin q) ℚ) (hA : IsUnit (A * A.transpose).det) :
    (Matrix.toEuclideanLin ((rationalRightInverseMatrix A).map (Rat.castHom ℝ))).toContinuousLinearMap =
      minimumNormRightInverse (Matrix.toEuclideanLin (A.map (Rat.castHom ℝ))).toContinuousLinearMap
        (rationalMatrix_real_surjective A hA) := by
  let f := (Matrix.toEuclideanLin (A.map (Rat.castHom ℝ))).toContinuousLinearMap
  let R := (Matrix.toEuclideanLin ((rationalRightInverseMatrix A).map (Rat.castHom ℝ))).toContinuousLinearMap
  let M := Matrix.toEuclideanLin (((A * A.transpose)⁻¹).map (Rat.castHom ℝ))
  have hAR := congrArg (fun N => N.map (Rat.castHom ℝ))
    (rationalRightInverseMatrix_right_inverse A hA)
  rw [Matrix.map_mul, Matrix.map_one (Rat.castHom ℝ) (map_zero _) (map_one _)] at hAR
  have hr (y : Euclidean p) : f (R y) = y := by
    change ((Matrix.toLpLin 2 2 (A.map (Rat.castHom ℝ))).comp
      (Matrix.toLpLin 2 2 ((rationalRightInverseMatrix A).map (Rat.castHom ℝ)))) y = y
    rw [← Matrix.toLpLin_mul_same, hAR, Matrix.toLpLin_one]
    rfl
  have hrform (y : Euclidean p) : R y = f.adjoint (M y) := by
    change Matrix.toEuclideanLin ((A.transpose * (A * A.transpose)⁻¹).map (Rat.castHom ℝ)) y = _
    rw [Matrix.map_mul]
    change Matrix.toLpLin 2 2 (((A.map (Rat.castHom ℝ)).conjTranspose) *
      (((A * A.transpose)⁻¹).map (Rat.castHom ℝ))) y = _
    rw [Matrix.toLpLin_mul_same]
    change Matrix.toEuclideanLin (A.map (Rat.castHom ℝ)).conjTranspose (M y) = _
    rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    rfl
  have hmem (y : Euclidean p) : R y ∈ f.toLinearMap.kerᗮ := by
    rw [Submodule.mem_orthogonal]
    intro x hx
    rw [hrform, ContinuousLinearMap.adjoint_inner_right, show f x = 0 from hx, inner_zero_left]
  ext y : 1
  have he : (⟨R y, hmem y⟩ : f.toLinearMap.kerᗮ) =
      (kernelOrthogonalEquiv f.toLinearMap (rationalMatrix_real_surjective A hA)).symm y := by
    apply (kernelOrthogonalEquiv f.toLinearMap (rationalMatrix_real_surjective A hA)).injective
    rw [LinearEquiv.apply_symm_apply]
    change f (R y) = y
    exact hr y
  exact congrArg (fun z : f.toLinearMap.kerᗮ => (z : Euclidean q)) he

theorem rationalKernelProjectionMatrix_operator {p q : ℕ}
    (A : Matrix (Fin p) (Fin q) ℚ) (hA : IsUnit (A * A.transpose).det) :
    (Matrix.toEuclideanLin ((rationalKernelProjectionMatrix A).map (Rat.castHom ℝ))).toContinuousLinearMap =
      (Matrix.toEuclideanLin (A.map (Rat.castHom ℝ))).ker.starProjection := by
  let f := (Matrix.toEuclideanLin (A.map (Rat.castHom ℝ))).toContinuousLinearMap
  have hp := minimumNormRightInverse_comp_self f (rationalMatrix_real_surjective A hA)
  rw [← rationalRightInverseMatrix_minimumNorm A hA] at hp
  ext x : 1
  have he := congrArg (fun g : Euclidean q →L[ℝ] Euclidean q => g x) hp
  change (Matrix.toEuclideanLin ((rationalRightInverseMatrix A).map (Rat.castHom ℝ)))
    (Matrix.toEuclideanLin (A.map (Rat.castHom ℝ)) x) = f.toLinearMap.kerᗮ.starProjection x at he
  change Matrix.toEuclideanLin ((1 - rationalRightInverseMatrix A * A).map (Rat.castHom ℝ)) x = _
  rw [Matrix.map_sub (Rat.castHom ℝ) (map_sub _), Matrix.map_mul, Matrix.map_one (Rat.castHom ℝ) (map_zero _) (map_one _), map_sub]
  have hI : Matrix.toEuclideanLin (1 : Matrix (Fin q) (Fin q) ℝ) = LinearMap.id := Matrix.toLpLin_one 2
  rw [hI]
  change x - Matrix.toLpLin 2 2
    ((rationalRightInverseMatrix A).map (Rat.castHom ℝ) * A.map (Rat.castHom ℝ)) x = _
  rw [Matrix.toLpLin_mul_same]
  change x - (Matrix.toEuclideanLin ((rationalRightInverseMatrix A).map (Rat.castHom ℝ)))
    (Matrix.toEuclideanLin (A.map (Rat.castHom ℝ)) x) = _
  rw [he, Submodule.starProjection_orthogonal_val]
  abel

end GeometricGaussianLHL
end

end RationalShapingGeometry

section RationalInverseRoot

/-!
## Numerical inverse square roots using the existing inverse and root routines

The inverse routine returns a positive-definite matrix. Taking its numerical
square root avoids inverting an uncorrected root approximation. Allocating
twice the inverse precision controls the square-root perturbation error.
-/

open scoped MatrixOrder Matrix.Norms.L2Operator

namespace GeometricGaussianLHL

theorem matrix_sqrt_inverse {d : ℕ} (G : Matrix (Fin d) (Fin d) ℝ) :
    CFC.sqrt G⁻¹ = (CFC.sqrt G)⁻¹ := by
  simp only [Matrix.nonsing_inv_eq_ringInverse, CFC.sqrt_ringInverse]

def rationalInverseRootApprox {d : ℕ} (t : ℕ) (G : Matrix (Fin d) (Fin d) ℚ) :
    Matrix (Fin d) (Fin d) ℚ :=
  rationalSqrtApprox (t + 1) (rationalInverseApprox (2 * (t + 1)) G)

theorem rationalInverseRootApprox_error {d : ℕ} (t : ℕ)
    (G : Matrix (Fin d) (Fin d) ℚ) (hG : (G.map (Rat.castHom ℝ)).PosDef) :
    ‖(rationalInverseRootApprox t G).map (Rat.castHom ℝ) - (CFC.sqrt (G.map (Rat.castHom ℝ)))⁻¹‖ ≤
      1 / (2 : ℝ) ^ t := by
  let H := rationalInverseApprox (2 * (t + 1)) G
  have hH : (H.map (Rat.castHom ℝ)).PosDef := rationalInverseApprox_posDef _ _ hG
  have h₁ := rationalSqrtApprox_matrix_error (t + 1) H hH
  have h₂ : ‖CFC.sqrt (H.map (Rat.castHom ℝ)) - (CFC.sqrt (G.map (Rat.castHom ℝ)))⁻¹‖ ≤
      1 / (2 : ℝ) ^ (t + 1) := by
    rw [← matrix_sqrt_inverse]
    apply (matrix_sqrt_operator_holder _ _ hH.posSemidef hG.inv.posSemidef).trans
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity, ?_⟩
    exact (rationalInverseApprox_matrix_error (2 * (t + 1)) G hG).trans_eq
      (by rw [two_mul, pow_add]; ring)
  calc
    _ ≤ ‖(rationalSqrtApprox (t + 1) H).map (Rat.castHom ℝ) - CFC.sqrt (H.map (Rat.castHom ℝ))‖ +
        ‖CFC.sqrt (H.map (Rat.castHom ℝ)) - (CFC.sqrt (G.map (Rat.castHom ℝ)))⁻¹‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 1 / (2 : ℝ) ^ (t + 1) + 1 / (2 : ℝ) ^ (t + 1) := add_le_add h₁ h₂
    _ = _ := by rw [pow_succ]; ring

end GeometricGaussianLHL

end RationalInverseRoot

section RationalShapingAlgorithm

/-!
## Positive rational approximation to the shaping square root

The precision is computed from the rational input and requested accuracy.
Symmetrization and a small positive diagonal shift ensure positive definite
output. These numerical specifications do not assert arithmetic cost bounds or
the paper's exact extreme-width formulas for the trace-average target.
-/

open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator

namespace GeometricGaussianLHL

def rationalShapingRawApprox {p q : ℕ} (t : ℕ)
    (A : Matrix (Fin p) (Fin q) ℚ) (w : ℚ) : Matrix (Fin q) (Fin q) ℚ :=
  rationalSqrtApprox (t + 2) (rationalShapingApproxCovariance
    (2 * (t + 2) + rationalShapingPrecisionGuard A w) A w)

def rationalShapingApprox {p q : ℕ} (t : ℕ)
    (A : Matrix (Fin p) (Fin q) ℚ) (w : ℚ) : Matrix (Fin q) (Fin q) ℚ :=
  let R := rationalShapingRawApprox t A w
  materializeMatrix ((1 / 2 : ℚ) • (R + R.transpose) + (1 / (2 : ℚ) ^ (t + 1)) • 1)

theorem rationalShapingRawApprox_error {p q : ℕ} (t : ℕ)
    (A : Matrix (Fin p) (Fin q) ℚ) (w : ℚ) (hp : 0 < p)
    (hA : IsUnit (A * A.transpose).det) (hw : w ≠ 0) :
    ‖(rationalShapingRawApprox t A w).map (Rat.castHom ℝ) -
      rationalShapingSquareRootMatrix A w‖ ≤ 1 / (2 : ℝ) ^ (t + 1) := by
  let u := t + 2
  let C := rationalShapingApproxCovariance (2 * u + rationalShapingPrecisionGuard A w) A w
  let Cr := C.map (Rat.castHom ℝ)
  let D := (rationalShapingCovarianceMatrix A w).map (Rat.castHom ℝ)
  have hC : Cr.PosDef := rationalShapingApproxCovariance_real_posDef _ A w hp hA hw
  have hD : D.PosDef := rationalShapingCovarianceMatrix_real_posDef A w hp hA hw
  have hcov : ‖Cr - D‖ ≤ 1 / (2 : ℝ) ^ (2 * u) :=
    rationalShapingApproxCovariance_prescribed_error (2 * u) A w hp hA
  have hsqrt : ‖CFC.sqrt Cr - CFC.sqrt D‖ ≤ 1 / (2 : ℝ) ^ u := by
    apply (matrix_sqrt_operator_holder Cr D hC.posSemidef hD.posSemidef).trans
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity, hcov.trans_eq ?_⟩
    rw [two_mul, pow_add]
    ring
  have hraw : ‖(rationalSqrtApprox u C).map (Rat.castHom ℝ) - CFC.sqrt Cr‖ ≤
      1 / (2 : ℝ) ^ u := rationalSqrtApprox_matrix_error u C hC
  change ‖(rationalSqrtApprox u C).map (Rat.castHom ℝ) - CFC.sqrt D‖ ≤ _
  calc
    _ ≤ ‖(rationalSqrtApprox u C).map (Rat.castHom ℝ) - CFC.sqrt Cr‖ +
        ‖CFC.sqrt Cr - CFC.sqrt D‖ := by
          simpa only [dist_eq_norm] using dist_triangle
            ((rationalSqrtApprox u C).map (Rat.castHom ℝ)) (CFC.sqrt Cr) (CFC.sqrt D)
    _ ≤ 1 / (2 : ℝ) ^ u + 1 / (2 : ℝ) ^ u := add_le_add hraw hsqrt
    _ = _ := by dsimp only [u]; rw [show t + 2 = (t + 1) + 1 by omega, pow_add]; norm_num; ring

theorem rationalShapingApprox_real_formula {p q : ℕ} (t : ℕ)
    (A : Matrix (Fin p) (Fin q) ℚ) (w : ℚ) :
    (rationalShapingApprox t A w).map (Rat.castHom ℝ) =
      (1 / 2 : ℝ) • ((rationalShapingRawApprox t A w).map (Rat.castHom ℝ) +
        ((rationalShapingRawApprox t A w).map (Rat.castHom ℝ)).transpose) +
        (1 / (2 : ℝ) ^ (t + 1)) • 1 := by
  rw [rationalShapingApprox, materializeMatrix_eq]
  ext i j
  by_cases hij : i = j <;>
    simp [Matrix.map_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply, hij]

theorem rationalShapingApprox_matrix_error {p q : ℕ} (t : ℕ)
    (A : Matrix (Fin p) (Fin q) ℚ) (w : ℚ) (hp : 0 < p)
    (hA : IsUnit (A * A.transpose).det) (hw : w ≠ 0) :
    ‖(rationalShapingApprox t A w).map (Rat.castHom ℝ) -
      rationalShapingSquareRootMatrix A w‖ ≤ 1 / (2 : ℝ) ^ t := by
  have hS := rationalShapingSquareRootMatrix_posDef A w hp hA hw
  have he := (matrix_symmetrize_error _ _ hS.isHermitian).trans
    (rationalShapingRawApprox_error t A w hp hA hw)
  rw [rationalShapingApprox_real_formula]
  apply (matrix_positive_shift_error _ _ (by positivity) he).trans_eq
  rw [pow_add]
  norm_num
  field_simp

theorem rationalShapingApprox_posDef {p q : ℕ} (t : ℕ)
    (A : Matrix (Fin p) (Fin q) ℚ) (w : ℚ) (hp : 0 < p)
    (hA : IsUnit (A * A.transpose).det) (hw : w ≠ 0) :
    ((rationalShapingApprox t A w).map (Rat.castHom ℝ)).PosDef := by
  have hS := rationalShapingSquareRootMatrix_posDef A w hp hA hw
  have he := (matrix_symmetrize_error _ _ hS.isHermitian).trans
    (rationalShapingRawApprox_error t A w hp hA hw)
  rw [rationalShapingApprox_real_formula]
  apply matrix_positive_shift_posDef _ _ ?_ hS he
  apply Matrix.IsHermitian.ext
  intro i j
  simp [Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply, add_comm]

theorem rationalShapingApprox_operator_error {p q : ℕ} (t : ℕ)
    (A : Matrix (Fin p) (Fin q) ℚ) (w : ℚ) (hp : 0 < p)
    (hA : IsUnit (A * A.transpose).det) (hw : w ≠ 0) :
    ‖(Matrix.toEuclideanLin ((rationalShapingApprox t A w).map
        (Rat.castHom ℝ))).toContinuousLinearMap -
      (Matrix.toEuclideanLin (rationalShapingSquareRootMatrix A w)).toContinuousLinearMap‖ ≤
      1 / (2 : ℝ) ^ t := by
  rw [← euclideanMatrix_norm_sub_CLM]
  exact rationalShapingApprox_matrix_error t A w hp hA hw

end GeometricGaussianLHL

end RationalShapingAlgorithm

section RealShapingInputCertificate

/-!
## Shaping a real target from a sufficiently accurate rational input

Input norms and inverse-Gram norms control an explicit polynomial error
factor. This is an accuracy certificate for supplied rational data; it does
not assume that an arbitrary real input can be encoded or approximated for
free. The output is computed by the rational shaping algorithm.
-/

noncomputable section

open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator

namespace GeometricGaussianLHL

def shapingCovarianceInputFactor (L H : ℝ) : ℝ :=
  let K := 1 + L ^ 2 * H
  (2 * L * H ^ 2 + 4 * L * H ^ 2 * K) +
    (2 * L ^ 2 * H + K ^ 2 + 2 * H * K * L ^ 2) * (2 * L * H ^ 2)

def shapingRealInputFactor (L H W : ℝ) : ℝ :=
  W ^ 2 * shapingCovarianceInputFactor L H +
    2 * W * ((L * H) ^ 2 + H * (1 + L ^ 2 * H) ^ 2)

theorem shapingRealInputFactor_nonneg {L H W : ℝ} (hL : 0 ≤ L) (hH : 0 ≤ H) (hW : 0 ≤ W) :
    0 ≤ shapingRealInputFactor L H W := by
  unfold shapingRealInputFactor shapingCovarianceInputFactor
  positivity

theorem realShapingCovarianceMatrix_input_error {p q : ℕ}
    (A B : Matrix (Fin p) (Fin q) ℝ) (w v : ℝ) (hp : 0 < p)
    (hA : IsUnit (A * A.transpose).det) (hB : IsUnit (B * B.transpose).det)
    {L H W : ℝ} (hL : 0 ≤ L) (hH : 0 ≤ H) (hW : 0 ≤ W)
    (hAn : ‖A‖ ≤ L) (hBn : ‖B‖ ≤ L)
    (hAi : ‖(A * A.transpose)⁻¹‖ ≤ H) (hBi : ‖(B * B.transpose)⁻¹‖ ≤ H)
    (hw : |w| ≤ W) (hv : |v| ≤ W) :
    ‖realShapingCovarianceMatrix A w - realShapingCovarianceMatrix B v‖ ≤
      shapingRealInputFactor L H W * (‖A - B‖ + |w - v|) := by
  let M := (A * A.transpose)⁻¹
  let N := (B * B.transpose)⁻¹
  let CA := gramFilledCovariance A (A.transpose * M) (M.trace / (p : ℝ))
  let CB := gramFilledCovariance B (B.transpose * N) (N.trace / (p : ℝ))
  let CT := gramFilledCovariance B (B.transpose * M) (M.trace / (p : ℝ))
  let K := 1 + L ^ 2 * H
  let J := 2 * L ^ 2 * H + K ^ 2 + 2 * H * K * L ^ 2
  let V := (L * H) ^ 2 + H * K ^ 2
  let δ := ‖A - B‖
  let ξ := |w - v|
  have hδ : 0 ≤ δ := norm_nonneg _
  have hξ : 0 ≤ ξ := abs_nonneg _
  have hJ : 0 ≤ J := by dsimp only [J, K]; positivity
  have hV : 0 ≤ V := by dsimp only [V, K]; positivity
  have hF : 0 ≤ shapingCovarianceInputFactor L H := by
    dsimp only [shapingCovarianceInputFactor]
    positivity
  have hi : ‖M - N‖ ≤ 2 * L * H ^ 2 * δ :=
    matrixGramInverse_input_error A B hA hB hL hH hAn hBn hAi hBi
  have hmatrix : ‖CA - CT‖ ≤ (2 * L * H ^ 2 + 4 * L * H ^ 2 * K) * δ :=
    gramFilledCovariance_matrix_error A B M hp hL hH hAn hBn hAi
  have hinverse : ‖CT - CB‖ ≤ J * (2 * L * H ^ 2 * δ) :=
    (gramFilledCovariance_inverse_error B M N hp hL hH hBn hAi hBi).trans
      (mul_le_mul_of_nonneg_left hi hJ)
  have hc : ‖CA - CB‖ ≤ shapingCovarianceInputFactor L H * δ := by
    calc
      _ ≤ ‖CA - CT‖ + ‖CT - CB‖ := norm_sub_le_norm_sub_add_norm_sub CA CT CB
      _ ≤ (2 * L * H ^ 2 + 4 * L * H ^ 2 * K) * δ + J * (2 * L * H ^ 2 * δ) :=
        add_le_add hmatrix hinverse
      _ = _ := by dsimp only [shapingCovarianceInputFactor, J, K]; ring
  have hcb : ‖CB‖ ≤ V := gramFilledCovariance_inverse_norm_le B N hp hL hH hBn hBi
  have hwidth : |w ^ 2 - v ^ 2| ≤ 2 * W * ξ := by
    rw [show w ^ 2 - v ^ 2 = (w - v) * (w + v) by ring, abs_mul]
    calc
      _ ≤ |w - v| * (|w| + |v|) := mul_le_mul_of_nonneg_left (abs_add_le w v) hξ
      _ ≤ ξ * (W + W) := mul_le_mul_of_nonneg_left (add_le_add hw hv) hξ
      _ = _ := by ring
  have hwsq : w ^ 2 ≤ W ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg w) hw 2
  have he : realShapingCovarianceMatrix A w - realShapingCovarianceMatrix B v =
      w ^ 2 • (CA - CB) + (w ^ 2 - v ^ 2) • CB := by
    change w ^ 2 • CA - v ^ 2 • CB = _
    module
  have h₁ : ‖w ^ 2 • (CA - CB)‖ ≤ W ^ 2 * (shapingCovarianceInputFactor L H * δ) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg w)]
    exact mul_le_mul hwsq hc (norm_nonneg _) (sq_nonneg W)
  have h₂ : ‖(w ^ 2 - v ^ 2) • CB‖ ≤ (2 * W * ξ) * V := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul hwidth hcb (norm_nonneg _) (by positivity)
  rw [he]
  calc
    _ ≤ ‖w ^ 2 • (CA - CB)‖ + ‖(w ^ 2 - v ^ 2) • CB‖ := norm_add_le _ _
    _ ≤ W ^ 2 * (shapingCovarianceInputFactor L H * δ) + (2 * W * ξ) * V := add_le_add h₁ h₂
    _ ≤ (W ^ 2 * shapingCovarianceInputFactor L H + 2 * W * V) * (δ + ξ) := by
      nlinarith [mul_nonneg (mul_nonneg (sq_nonneg W) hF) hξ,
        mul_nonneg (mul_nonneg (by positivity : 0 ≤ 2 * W) hV) hδ]
    _ = _ := rfl

end GeometricGaussianLHL
end

end RealShapingInputCertificate

section ShapingInputConditioning

/-!
## Conditioning survives sufficiently accurate matrix input

An inverse-norm bound for the exact input controls the inverse of a nearby
matrix. This discharges rank and conditioning promises for approximations;
it does not produce or encode the approximation itself.
-/

noncomputable section
open scoped Matrix.Norms.L2Operator

namespace GeometricGaussianLHL

theorem matrixInverse_perturbation_bound {n : ℕ} [NeZero n]
    (M N : Matrix (Fin n) (Fin n) ℝ) (hM : IsUnit M.det) {H : ℝ}
    (hH : 0 < H) (hinv : ‖M⁻¹‖ ≤ H) (herr : ‖N - M‖ ≤ 1 / (2 * H)) :
    IsUnit N.det ∧ ‖N⁻¹‖ ≤ 2 * H := by
  have hu : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).mpr hM
  let u := hu.unit
  have huv : (u : Matrix (Fin n) (Fin n) ℝ) = M := hu.unit_spec
  have hui : (↑u⁻¹ : Matrix (Fin n) (Fin n) ℝ) = M⁻¹ := by
    rw [Matrix.nonsing_inv_eq_ringInverse, ← huv, Ring.inverse_unit]
  have hi : 0 < ‖M⁻¹‖ := hui ▸ Units.norm_pos u⁻¹
  have hnear : ‖N - (u : Matrix (Fin n) (Fin n) ℝ)‖ <
      ‖(↑u⁻¹ : Matrix (Fin n) (Fin n) ℝ)‖⁻¹ := by
    rw [huv, hui]
    apply herr.trans_lt
    rw [← one_div, lt_div_iff₀ hi]
    apply lt_of_le_of_lt (mul_le_mul_of_nonneg_left hinv (by positivity))
    have he : 1 / (2 * H) * H = (1 : ℝ) / 2 := by field_simp
    rw [he]
    norm_num
  have hN : IsUnit N.det := (Matrix.isUnit_iff_isUnit_det N).mp
    (by simpa only [Units.val_ofNearby] using (u.ofNearby N hnear).isUnit)
  refine ⟨hN, ?_⟩
  have hd : ‖N⁻¹ - M⁻¹‖ ≤ ‖N⁻¹‖ / 2 := by
    apply (matrixInverse_operator_error N M hN hM).trans
    calc
      _ ≤ ‖N⁻¹‖ * H * (1 / (2 * H)) := by gcongr
      _ = _ := by field_simp
  have ht := norm_le_norm_sub_add N⁻¹ M⁻¹
  linarith

/-- Full row rank and an inverse-Gram bound follow from the exact input and
an explicit approximation budget, without a separate rank promise on `B`. -/
theorem matrixGram_input_conditioning {p q : ℕ}
    (A B : Matrix (Fin p) (Fin q) ℝ) (hp : 0 < p)
    (hA : IsUnit (A * A.transpose).det) {L H : ℝ}
    (hL : 0 ≤ L) (hH : 0 < H) (hAn : ‖A‖ ≤ L) (hAi : ‖(A * A.transpose)⁻¹‖ ≤ H)
    (herr : ‖B - A‖ ≤ min 1 (1 / (2 * H * (2 * L + 1)))) :
    ‖B‖ ≤ L + 1 ∧ IsUnit (B * B.transpose).det ∧ ‖(B * B.transpose)⁻¹‖ ≤ 2 * H := by
  let : NeZero p := ⟨hp.ne'⟩
  obtain ⟨he₁, he₂⟩ := le_min_iff.mp herr
  have hn : ‖B‖ ≤ L + 1 := by
    have ht := norm_le_norm_sub_add B A
    linarith
  have hsmall : ‖B * B.transpose - A * A.transpose‖ ≤ 1 / (2 * H) := by
    apply (matrixGram_operator_error B A).trans
    calc
      _ ≤ (2 * L + 1) * (1 / (2 * H * (2 * L + 1))) := by
        exact mul_le_mul (by linarith) he₂ (norm_nonneg _) (by positivity)
      _ = _ := by
        have hpos : 0 < 2 * L + 1 := by positivity
        field_simp
  exact ⟨hn, matrixInverse_perturbation_bound _ _ hA hH hAi hsmall⟩

theorem matrixGram_dyadic_input_conditioning {p q : ℕ}
    (A B : Matrix (Fin p) (Fin q) ℝ) (hp : 0 < p)
    (hA : IsUnit (A * A.transpose).det) (b : ℕ)
    (hAn : ‖A‖ ≤ (2 : ℝ) ^ b) (hAi : ‖(A * A.transpose)⁻¹‖ ≤ (2 : ℝ) ^ b)
    (herr : ‖B - A‖ ≤ 1 / (2 : ℝ) ^ (2 * b + 3)) :
    ‖B‖ ≤ (2 : ℝ) ^ (b + 1) ∧ IsUnit (B * B.transpose).det ∧
      ‖(B * B.transpose)⁻¹‖ ≤ (2 : ℝ) ^ (b + 1) := by
  have hb : 1 ≤ (2 : ℝ) ^ b := one_le_pow₀ (by norm_num)
  have hden : 2 * (2 : ℝ) ^ b * (2 * (2 : ℝ) ^ b + 1) ≤ (2 : ℝ) ^ (2 * b + 3) := by
    rw [pow_add, two_mul b, pow_add]
    norm_num
    nlinarith [sq_nonneg ((2 : ℝ) ^ b - 1)]
  have he₁ : ‖B - A‖ ≤ 1 := herr.trans ((div_le_one (by positivity)).mpr
    (one_le_pow₀ (by norm_num)))
  have he₂ : ‖B - A‖ ≤ 1 / (2 * (2 : ℝ) ^ b * (2 * (2 : ℝ) ^ b + 1)) :=
    herr.trans (one_div_le_one_div_of_le (by positivity) hden)
  obtain ⟨hn, hrank, hi⟩ := matrixGram_input_conditioning A B hp hA
    (by positivity) (by positivity) hAn hAi (le_min he₁ he₂)
  rw [pow_succ]
  exact ⟨by linarith, hrank, by linarith⟩

end GeometricGaussianLHL
end

end ShapingInputConditioning

section MatrixRowEmbedding

/-!
## Leading-row embedding for square-buffer implementations

A rectangular input is embedded into a square buffer without changing its
operator norm. The embedding has orthonormal columns; its complementary
projector selects the unused rows. The full-row-rank input supplies the
required dimension inequality.
-/

open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator

namespace GeometricGaussianLHL

def leadingRowEmbedding {𝕜 : Type*} [Zero 𝕜] [One 𝕜] {p q : ℕ} (hpq : p ≤ q) :
    Matrix (Fin q) (Fin p) 𝕜 := fun i j => if i = Fin.castLE hpq j then 1 else 0

theorem leadingRowEmbedding_transpose_mul {𝕜 : Type*} [CommRing 𝕜]
    {p q : ℕ} (hpq : p ≤ q) :
    (leadingRowEmbedding (𝕜 := 𝕜) hpq).transpose * leadingRowEmbedding (𝕜 := 𝕜) hpq = 1 := by
  ext i j
  simp [Matrix.mul_apply, leadingRowEmbedding, Matrix.transpose_apply, Matrix.one_apply,
    mul_ite, Fin.castLE_inj, eq_comm]

def padMatrixRows {𝕜 : Type*} [CommRing 𝕜] {p q : ℕ}
    (hpq : p ≤ q) (A : Matrix (Fin p) (Fin q) 𝕜) : Matrix (Fin q) (Fin q) 𝕜 :=
  leadingRowEmbedding hpq * A

theorem padMatrixRows_leading {𝕜 : Type*} [CommRing 𝕜] {p q : ℕ}
    (hpq : p ≤ q) (A : Matrix (Fin p) (Fin q) 𝕜) (i : Fin p) (j : Fin q) :
    padMatrixRows hpq A (Fin.castLE hpq i) j = A i j := by
  simp [padMatrixRows, Matrix.mul_apply, leadingRowEmbedding, Fin.castLE_inj, ite_mul]

theorem padMatrixRows_trailing {𝕜 : Type*} [CommRing 𝕜] {p q : ℕ}
    (hpq : p ≤ q) (A : Matrix (Fin p) (Fin q) 𝕜) (i j : Fin q) (hi : p ≤ i.val) :
    padMatrixRows hpq A i j = 0 := by
  have hn (k : Fin p) : i ≠ Fin.castLE hpq k := by
    intro h
    have hv := congrArg Fin.val h
    have hk := k.isLt
    simp only [Fin.val_castLE] at hv
    omega
  simp [padMatrixRows, Matrix.mul_apply, leadingRowEmbedding, hn]

theorem leadingRowEmbedding_complement_gram {𝕜 : Type*} [CommRing 𝕜]
    {p q : ℕ} (hpq : p ≤ q) :
    let J := leadingRowEmbedding (𝕜 := 𝕜) hpq
    (1 - J * J.transpose) * (1 - J * J.transpose).transpose = 1 - J * J.transpose := by
  let J := leadingRowEmbedding (𝕜 := 𝕜) hpq
  have hJ : J.transpose * J = 1 := leadingRowEmbedding_transpose_mul hpq
  have he : (J * J.transpose) * (J * J.transpose) = J * J.transpose := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc J.transpose, hJ, Matrix.one_mul]
  dsimp only
  change (1 - J * J.transpose) * (1 - J * J.transpose).transpose = _
  rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, he, sub_self, sub_zero]

theorem leadingRowEmbedding_norm {p q : ℕ} (hpq : p ≤ q) (hp : 0 < p) :
    ‖leadingRowEmbedding (𝕜 := ℝ) hpq‖ = 1 := by
  let : NeZero p := ⟨Nat.ne_of_gt hp⟩
  have h := Matrix.l2_opNorm_conjTranspose_mul_self (leadingRowEmbedding (𝕜 := ℝ) hpq)
  rw [Matrix.conjTranspose_eq_transpose_of_trivial, leadingRowEmbedding_transpose_mul, norm_one] at h
  nlinarith [norm_nonneg (leadingRowEmbedding (𝕜 := ℝ) hpq)]

theorem padMatrixRows_norm {p q : ℕ} (hpq : p ≤ q) (hp : 0 < p)
    (A : Matrix (Fin p) (Fin q) ℝ) : ‖padMatrixRows hpq A‖ = ‖A‖ := by
  let J := leadingRowEmbedding (𝕜 := ℝ) hpq
  have hJ : ‖J‖ = 1 := leadingRowEmbedding_norm hpq hp
  have ht : ‖J.transpose‖ = 1 := (euclideanMatrix_transpose_norm J).trans hJ
  apply le_antisymm
  · exact (Matrix.l2_opNorm_mul J A).trans_eq (by rw [hJ, one_mul])
  · have he : J.transpose * padMatrixRows hpq A = A := by
      rw [padMatrixRows, ← Matrix.mul_assoc, leadingRowEmbedding_transpose_mul, Matrix.one_mul]
    calc
      ‖A‖ = ‖J.transpose * padMatrixRows hpq A‖ := congrArg norm he.symm
      _ ≤ ‖J.transpose‖ * ‖padMatrixRows hpq A‖ := Matrix.l2_opNorm_mul _ _
      _ = _ := by rw [ht, one_mul]

theorem rationalMatrix_rows_le_cols {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℚ)
    (hA : IsUnit (A * A.transpose).det) : p ≤ q := by
  have h := LinearMap.finrank_le_finrank_of_surjective (rationalMatrix_real_surjective A hA)
  simpa using h

end GeometricGaussianLHL

end MatrixRowEmbedding

section RationalMetricNormalization

/-!
## Numerical normalization from a rational metric and coefficient matrix

The output is computed from one root, one inverse, another root, repeated
blocks, and two matrix products. The approximation error uses operator norms
and has no extra factor from repeating the metric on the ring coordinates.
Machine composition and field-to-metric conversion costs are separate.
-/

open scoped MatrixOrder Matrix.Norms.L2Operator

namespace GeometricGaussianLHL

noncomputable def metricNormalizedMatrix {d r m : ℕ} (G : Matrix (Fin d) (Fin d) ℝ)
    (C : Matrix (Fin (r * d)) (Fin (m * d)) ℝ) : Matrix (Fin (r * d)) (Fin (m * d)) ℝ :=
  repeatedEuclideanMatrix r (CFC.sqrt G) * C * repeatedEuclideanMatrix m (CFC.sqrt G)⁻¹

def rationalMetricNormalizedApprox {d r m : ℕ} (t : ℕ) (G : Matrix (Fin d) (Fin d) ℚ)
    (C : Matrix (Fin (r * d)) (Fin (m * d)) ℚ) : Matrix (Fin (r * d)) (Fin (m * d)) ℚ :=
  repeatedEuclideanMatrix r (rationalSqrtApprox t G) * C *
    repeatedEuclideanMatrix m (rationalInverseRootApprox t G)

theorem rationalMetricNormalizedApprox_real {d r m : ℕ} (t : ℕ) (G : Matrix (Fin d) (Fin d) ℚ)
    (C : Matrix (Fin (r * d)) (Fin (m * d)) ℚ) :
    (rationalMetricNormalizedApprox t G C).map (Rat.castHom ℝ) =
      repeatedEuclideanMatrix r ((rationalSqrtApprox t G).map (Rat.castHom ℝ)) * C.map (Rat.castHom ℝ) *
        repeatedEuclideanMatrix m ((rationalInverseRootApprox t G).map (Rat.castHom ℝ)) := by
  rw [rationalMetricNormalizedApprox, Matrix.map_mul, Matrix.map_mul,
    repeatedEuclideanMatrix_map _ _ _ (map_zero _), repeatedEuclideanMatrix_map _ _ _ (map_zero _)]

theorem matrixSandwich_operator_error {p q : ℕ}
    (R S : Matrix (Fin p) (Fin p) ℝ) (U V : Matrix (Fin q) (Fin q) ℝ)
    (C : Matrix (Fin p) (Fin q) ℝ) {ε L H : ℝ}
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hL : 0 ≤ L) (_hH : 0 ≤ H)
    (hR : ‖R - S‖ ≤ ε) (hU : ‖U - V‖ ≤ ε) (hS : ‖S‖ ≤ L) (hV : ‖V‖ ≤ H) :
    ‖R * C * U - S * C * V‖ ≤ ‖C‖ * (L + H + 1) * ε := by
  have hUn : ‖U‖ ≤ ε + H := (norm_le_norm_sub_add U V).trans (add_le_add hU hV)
  have hRC : ‖R * C - S * C‖ ≤ ε * ‖C‖ := by
    rw [← Matrix.sub_mul]
    exact (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right hR (norm_nonneg _))
  have hSC : ‖S * C‖ ≤ L * ‖C‖ :=
    (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right hS (norm_nonneg _))
  apply (matrixProduct_operator_error (R * C) (S * C) U V).trans
  calc
    _ ≤ ε * ‖C‖ * (ε + H) + (L * ‖C‖) * ε :=
      add_le_add (mul_le_mul hRC hUn (norm_nonneg _) (by positivity))
        (mul_le_mul hSC hU (norm_nonneg _) (by positivity))
    _ = ‖C‖ * (L + H + ε) * ε := by ring
    _ ≤ _ := by gcongr

theorem rationalMetricNormalizedApprox_error {d r m : ℕ} (t : ℕ)
    (G : Matrix (Fin d) (Fin d) ℚ) (C : Matrix (Fin (r * d)) (Fin (m * d)) ℚ)
    (hG : (G.map (Rat.castHom ℝ)).PosDef) {L H : ℝ} (hL : 0 ≤ L) (hH : 0 ≤ H)
    (hroot : ‖CFC.sqrt (G.map (Rat.castHom ℝ))‖ ≤ L)
    (hinv : ‖(CFC.sqrt (G.map (Rat.castHom ℝ)))⁻¹‖ ≤ H) :
    ‖(rationalMetricNormalizedApprox t G C).map (Rat.castHom ℝ) -
      metricNormalizedMatrix (G.map (Rat.castHom ℝ)) (C.map (Rat.castHom ℝ))‖ ≤
      ‖C.map (Rat.castHom ℝ)‖ * (L + H + 1) * (1 / (2 : ℝ) ^ t) := by
  rw [rationalMetricNormalizedApprox_real, metricNormalizedMatrix]
  apply matrixSandwich_operator_error _ _ _ _ _ (by positivity)
    ((div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num))) hL hH
  · exact (repeatedEuclideanMatrix_error _ _ _).trans (rationalSqrtApprox_matrix_error t G hG)
  · exact (repeatedEuclideanMatrix_error _ _ _).trans (rationalInverseRootApprox_error t G hG)
  · exact (repeatedEuclideanMatrix_norm_le _ _).trans hroot
  · exact (repeatedEuclideanMatrix_norm_le _ _).trans hinv

theorem rationalMetricNormalizedApprox_prescribed_error {d r m : ℕ} (t b : ℕ)
    (G : Matrix (Fin d) (Fin d) ℚ) (C : Matrix (Fin (r * d)) (Fin (m * d)) ℚ)
    (hG : (G.map (Rat.castHom ℝ)).PosDef)
    (hroot : ‖CFC.sqrt (G.map (Rat.castHom ℝ))‖ ≤ (2 : ℝ) ^ b)
    (hinv : ‖(CFC.sqrt (G.map (Rat.castHom ℝ)))⁻¹‖ ≤ (2 : ℝ) ^ b)
    (hC : ‖C.map (Rat.castHom ℝ)‖ ≤ (2 : ℝ) ^ b) :
    ‖(rationalMetricNormalizedApprox (t + 2 * b + 2) G C).map (Rat.castHom ℝ) -
      metricNormalizedMatrix (G.map (Rat.castHom ℝ)) (C.map (Rat.castHom ℝ))‖ ≤ 1 / (2 : ℝ) ^ t := by
  have hb : 1 ≤ (2 : ℝ) ^ b := one_le_pow₀ (by norm_num)
  have hfactor : ‖C.map (Rat.castHom ℝ)‖ * ((2 : ℝ) ^ b + 2 ^ b + 1) ≤ 2 ^ (2 * b + 2) := by
    apply (mul_le_mul_of_nonneg_right hC (by positivity)).trans
    rw [pow_add, two_mul b, pow_add]
    norm_num
    nlinarith [sq_nonneg ((2 : ℝ) ^ b - 1)]
  apply (rationalMetricNormalizedApprox_error _ G C hG (by positivity) (by positivity) hroot hinv).trans
  calc
    _ ≤ (2 : ℝ) ^ (2 * b + 2) * (1 / (2 : ℝ) ^ (t + 2 * b + 2)) :=
      mul_le_mul_of_nonneg_right hfactor (by positivity)
    _ = _ := by
      rw [show t + 2 * b + 2 = t + (2 * b + 2) by omega, pow_add]
      field_simp
      simp only [pow_add]
      ring

end GeometricGaussianLHL

end RationalMetricNormalization

section PaddedShapingCovariance

/-!
## Refining rectangular shaping through square matrix operations

The completed square Gram inverse compresses to the original Gram inverse.
A mask after the computed right-inverse factor makes the covariance agree
with shaping through the compressed inverse, even for inexact iterates.
-/

open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator

namespace GeometricGaussianLHL

theorem leadingRowEmbedding_rat_cast {p q : ℕ} (hpq : p ≤ q) :
    (leadingRowEmbedding (𝕜 := ℚ) hpq).map (Rat.castHom ℝ) = leadingRowEmbedding (𝕜 := ℝ) hpq := by
  ext i j
  by_cases h : i = Fin.castLE hpq j <;> simp [leadingRowEmbedding, Matrix.map_apply, h]

theorem leadingRowEmbedding_compress_apply {𝕜 : Type*} [CommRing 𝕜] {p q : ℕ}
    (hpq : p ≤ q) (M : Matrix (Fin q) (Fin q) 𝕜) (i j : Fin p) :
    ((leadingRowEmbedding (𝕜 := 𝕜) hpq).transpose * M * leadingRowEmbedding (𝕜 := 𝕜) hpq) i j =
      M (Fin.castLE hpq i) (Fin.castLE hpq j) := by
  simp [Matrix.mul_apply, Matrix.transpose_apply, leadingRowEmbedding, ite_mul, mul_ite]

theorem leadingRowEmbedding_compress_posDef {p q : ℕ} (hpq : p ≤ q)
    (M : Matrix (Fin q) (Fin q) ℝ) (hM : M.PosDef) :
    ((leadingRowEmbedding hpq).transpose * M * leadingRowEmbedding hpq).PosDef := by
  have he : (leadingRowEmbedding hpq).transpose * M * leadingRowEmbedding hpq =
      M.submatrix (Fin.castLE hpq) (Fin.castLE hpq) := by
    ext i j
    exact leadingRowEmbedding_compress_apply hpq M i j
  rw [he]
  exact hM.submatrix (fun _ _ h => Fin.castLE_inj.mp h)

theorem leadingRowEmbedding_compress_norm_le {p q : ℕ} (hpq : p ≤ q) (hp : 0 < p)
    (M : Matrix (Fin q) (Fin q) ℝ) :
    ‖(leadingRowEmbedding hpq).transpose * M * leadingRowEmbedding hpq‖ ≤ ‖M‖ := by
  let J := leadingRowEmbedding (𝕜 := ℝ) hpq
  have hJ : ‖J‖ = 1 := leadingRowEmbedding_norm hpq hp
  have ht : ‖J.transpose‖ = 1 := (euclideanMatrix_transpose_norm J).trans hJ
  calc
    _ ≤ ‖J.transpose * M‖ * ‖J‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ (‖J.transpose‖ * ‖M‖) * ‖J‖ :=
      mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
    _ = _ := by rw [hJ, ht, one_mul, mul_one]

def paddedGramMatrix {p q : ℕ} (hpq : p ≤ q) (A : Matrix (Fin p) (Fin q) ℚ) :
    Matrix (Fin q) (Fin q) ℚ := matrixGramCompletion (leadingRowEmbedding hpq) (A * A.transpose)

theorem paddedGramMatrix_real_posDef {p q : ℕ} (hpq : p ≤ q)
    (A : Matrix (Fin p) (Fin q) ℚ) (hA : IsUnit (A * A.transpose).det) :
    ((paddedGramMatrix hpq A).map (Rat.castHom ℝ)).PosDef := by
  rw [paddedGramMatrix, matrixGramCompletion_rat_cast, leadingRowEmbedding_rat_cast]
  exact matrixGramCompletion_posDef _ _ (leadingRowEmbedding_transpose_mul hpq) (rationalGram_real_posDef A hA)

theorem paddedGramMatrix_inv_compress {p q : ℕ} (hpq : p ≤ q)
    (A : Matrix (Fin p) (Fin q) ℚ) (hA : IsUnit (A * A.transpose).det) :
    (leadingRowEmbedding hpq).transpose * (paddedGramMatrix hpq A)⁻¹ * leadingRowEmbedding hpq =
      (A * A.transpose)⁻¹ := by
  rw [paddedGramMatrix, matrixGramCompletion_inv _ _ (leadingRowEmbedding_transpose_mul hpq) hA,
    matrixGramCompletion_compress _ _ (leadingRowEmbedding_transpose_mul hpq)]

def paddedShapingRightInverse {p q : ℕ} (hpq : p ≤ q)
    (A : Matrix (Fin p) (Fin q) ℚ) (M : Matrix (Fin q) (Fin q) ℚ) : Matrix (Fin q) (Fin q) ℚ :=
  (padMatrixRows hpq A).transpose * M * (leadingRowEmbedding hpq * (leadingRowEmbedding hpq).transpose)

def paddedShapingKernelFill {p q : ℕ} (hpq : p ≤ q) (M : Matrix (Fin q) (Fin q) ℚ) : ℚ :=
  ((leadingRowEmbedding hpq).transpose * M * leadingRowEmbedding hpq).trace / (p : ℚ)

def paddedShapingCovariance {p q : ℕ} (hpq : p ≤ q)
    (A : Matrix (Fin p) (Fin q) ℚ) (M : Matrix (Fin q) (Fin q) ℚ) (w : ℚ) :
    Matrix (Fin q) (Fin q) ℚ :=
  w ^ 2 • gramFilledCovariance (padMatrixRows hpq A) (paddedShapingRightInverse hpq A M)
    (paddedShapingKernelFill hpq M)

theorem paddedShapingKernelFill_leading_sum {p q : ℕ} (hpq : p ≤ q)
    (M : Matrix (Fin q) (Fin q) ℚ) :
    paddedShapingKernelFill hpq M = (∑ i : Fin p, M (Fin.castLE hpq i) (Fin.castLE hpq i)) / (p : ℚ) := by
  simp only [paddedShapingKernelFill, Matrix.trace, Matrix.diag_apply, leadingRowEmbedding_compress_apply]

theorem paddedShapingRightInverse_factor {p q : ℕ} (hpq : p ≤ q)
    (A : Matrix (Fin p) (Fin q) ℚ) (M : Matrix (Fin q) (Fin q) ℚ) :
    paddedShapingRightInverse hpq A M =
      (A.transpose * ((leadingRowEmbedding hpq).transpose * M * leadingRowEmbedding hpq)) *
        (leadingRowEmbedding hpq).transpose := by
  simp only [paddedShapingRightInverse, padMatrixRows, Matrix.transpose_mul, Matrix.mul_assoc]

theorem paddedShapingCovariance_refines {p q : ℕ} (hpq : p ≤ q)
    (A : Matrix (Fin p) (Fin q) ℚ) (M : Matrix (Fin q) (Fin q) ℚ) (w : ℚ) :
    let N := (leadingRowEmbedding hpq).transpose * M * leadingRowEmbedding hpq
    paddedShapingCovariance hpq A M w =
      w ^ 2 • gramFilledCovariance A (A.transpose * N) (N.trace / (p : ℚ)) := by
  let J := leadingRowEmbedding (𝕜 := ℚ) hpq
  let N := J.transpose * M * J
  let R := A.transpose * N
  have hJ : J.transpose * J = 1 := leadingRowEmbedding_transpose_mul hpq
  have hRA : (R * J.transpose) * (J * A) = R * A := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc J.transpose, hJ, Matrix.one_mul]
  have hRR : (R * J.transpose) * (R * J.transpose).transpose = R * R.transpose := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.mul_assoc, ← Matrix.mul_assoc J.transpose, hJ, Matrix.one_mul]
  rw [paddedShapingCovariance, paddedShapingRightInverse_factor]
  change w ^ 2 • gramFilledCovariance (J * A) (R * J.transpose) (N.trace / (p : ℚ)) = _
  simp only [gramFilledCovariance, hRA, hRR]
  rfl

theorem paddedShapingCovariance_exact {p q : ℕ} (hpq : p ≤ q)
    (A : Matrix (Fin p) (Fin q) ℚ) (w : ℚ) (hA : IsUnit (A * A.transpose).det) :
    paddedShapingCovariance hpq A (paddedGramMatrix hpq A)⁻¹ w = rationalShapingCovarianceMatrix A w := by
  rw [paddedShapingCovariance_refines, paddedGramMatrix_inv_compress hpq A hA]
  exact gramFilledCovariance_exact A w hA

theorem leadingRowEmbedding_compress_rat_cast {p q : ℕ} (hpq : p ≤ q)
    (M : Matrix (Fin q) (Fin q) ℚ) :
    ((leadingRowEmbedding hpq).transpose * M * leadingRowEmbedding hpq).map (Rat.castHom ℝ) =
      (leadingRowEmbedding hpq).transpose * M.map (Rat.castHom ℝ) * leadingRowEmbedding hpq := by
  ext i j
  simp only [Matrix.map_apply, leadingRowEmbedding_compress_apply]

theorem paddedGramMatrix_inverse_real {p q : ℕ} (hpq : p ≤ q)
    (A : Matrix (Fin p) (Fin q) ℚ) (hA : IsUnit (A * A.transpose).det) :
    ((paddedGramMatrix hpq A)⁻¹).map (Rat.castHom ℝ) =
      ((paddedGramMatrix hpq A).map (Rat.castHom ℝ))⁻¹ := by
  have hu : IsUnit (paddedGramMatrix hpq A).det :=
    matrixGramCompletion_isUnit_det _ _ (leadingRowEmbedding_transpose_mul hpq) hA
  symm
  apply Matrix.inv_eq_right_inv
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hu]
  exact Matrix.map_one (Rat.castHom ℝ) (map_zero _) (map_one _)

theorem paddedGramMatrix_inverse_real_compress {p q : ℕ} (hpq : p ≤ q)
    (A : Matrix (Fin p) (Fin q) ℚ) (hA : IsUnit (A * A.transpose).det) :
    (leadingRowEmbedding hpq).transpose * ((paddedGramMatrix hpq A).map (Rat.castHom ℝ))⁻¹ *
      leadingRowEmbedding hpq = ((A * A.transpose).map (Rat.castHom ℝ))⁻¹ := by
  rw [← paddedGramMatrix_inverse_real hpq A hA, ← leadingRowEmbedding_compress_rat_cast,
    paddedGramMatrix_inv_compress hpq A hA, rationalGramInverse_real A hA]

def compressedPaddedInverseApprox {p q : ℕ} (t : ℕ) (hpq : p ≤ q)
    (A : Matrix (Fin p) (Fin q) ℚ) : Matrix (Fin p) (Fin p) ℚ :=
  (leadingRowEmbedding hpq).transpose * rationalInverseApprox t (paddedGramMatrix hpq A) * leadingRowEmbedding hpq

theorem compressedPaddedInverseApprox_posDef {p q : ℕ} (t : ℕ) (hpq : p ≤ q)
    (A : Matrix (Fin p) (Fin q) ℚ) (hA : IsUnit (A * A.transpose).det) :
    ((compressedPaddedInverseApprox t hpq A).map (Rat.castHom ℝ)).PosDef := by
  rw [compressedPaddedInverseApprox, leadingRowEmbedding_compress_rat_cast]
  exact leadingRowEmbedding_compress_posDef hpq _
    (rationalInverseApprox_posDef t _ (paddedGramMatrix_real_posDef hpq A hA))

theorem compressedPaddedInverseApprox_error {p q : ℕ} (t : ℕ) (hpq : p ≤ q)
    (A : Matrix (Fin p) (Fin q) ℚ) (hp : 0 < p) (hA : IsUnit (A * A.transpose).det) :
    ‖(compressedPaddedInverseApprox t hpq A).map (Rat.castHom ℝ) -
      ((A * A.transpose).map (Rat.castHom ℝ))⁻¹‖ ≤ 1 / (2 : ℝ) ^ t := by
  rw [compressedPaddedInverseApprox, leadingRowEmbedding_compress_rat_cast,
    ← paddedGramMatrix_inverse_real_compress hpq A hA]
  have h := leadingRowEmbedding_compress_norm_le hpq hp
    ((rationalInverseApprox t (paddedGramMatrix hpq A)).map (Rat.castHom ℝ) -
      ((paddedGramMatrix hpq A).map (Rat.castHom ℝ))⁻¹)
  simp only [Matrix.mul_sub, Matrix.sub_mul] at h
  exact h.trans (rationalInverseApprox_matrix_error t _ (paddedGramMatrix_real_posDef hpq A hA))

theorem paddedShapingCovariance_real_posDef {p q : ℕ} (hpq : p ≤ q)
    (A : Matrix (Fin p) (Fin q) ℚ) (M : Matrix (Fin q) (Fin q) ℚ) (w : ℚ)
    (hp : 0 < p) (hM : (M.map (Rat.castHom ℝ)).PosDef) (hw : w ≠ 0) :
    ((paddedShapingCovariance hpq A M w).map (Rat.castHom ℝ)).PosDef := by
  let : NeZero p := ⟨Nat.ne_of_gt hp⟩
  let N := (leadingRowEmbedding hpq).transpose * M * leadingRowEmbedding hpq
  have hN : (N.map (Rat.castHom ℝ)).PosDef := by
    change (((leadingRowEmbedding hpq).transpose * M * leadingRowEmbedding hpq).map (Rat.castHom ℝ)).PosDef
    rw [leadingRowEmbedding_compress_rat_cast]
    exact leadingRowEmbedding_compress_posDef hpq _ hM
  have hc : 0 < (N.map (Rat.castHom ℝ)).trace / (p : ℝ) :=
    div_pos hN.trace_pos (by exact_mod_cast hp)
  rw [paddedShapingCovariance_refines]
  change ((w ^ 2 • gramFilledCovariance A (A.transpose * N) (N.trace / (p : ℚ))).map (Rat.castHom ℝ)).PosDef
  rw [scaledGramFilledCovariance_rat_cast]
  apply (gramFilledCovariance_posDef _ _ hc).smul
  exact sq_pos_of_ne_zero (by exact_mod_cast hw)

end GeometricGaussianLHL

end PaddedShapingCovariance

section MetricNormalizationStability

/-!
## Real-metric error in the normalized coefficient matrix

The root and inverse-root perturbations are controlled together. An explicit
dyadic metric budget gives a normalized-matrix budget using the same block
and product estimates as the numerical conversion.
-/

open scoped MatrixOrder Matrix.Norms.L2Operator

namespace GeometricGaussianLHL

theorem matrix_sqrt_dyadic_error {d : ℕ} (t : ℕ)
    (G H : Matrix (Fin d) (Fin d) ℝ) (hG : G.PosSemidef) (hH : H.PosSemidef)
    (herr : ‖G - H‖ ≤ 1 / (2 : ℝ) ^ (2 * t)) :
    ‖CFC.sqrt G - CFC.sqrt H‖ ≤ 1 / (2 : ℝ) ^ t := by
  apply (matrix_sqrt_operator_holder G H hG hH).trans
  apply (Real.sqrt_le_iff).mpr
  refine ⟨by positivity, ?_⟩
  exact herr.trans_eq (by rw [two_mul, pow_add]; ring)

theorem metricNormalizedMatrix_metric_error {d r m : ℕ} (t b : ℕ)
    (G H : Matrix (Fin d) (Fin d) ℝ) (C : Matrix (Fin (r * d)) (Fin (m * d)) ℝ)
    (hG : G.PosDef) (hH : H.PosDef) {L V : ℝ} (hL : 0 ≤ L) (hV : 0 ≤ V)
    (hroot : ‖CFC.sqrt G‖ ≤ L) (hinvroot : ‖(CFC.sqrt G)⁻¹‖ ≤ V)
    (hGi : ‖G⁻¹‖ ≤ (2 : ℝ) ^ b) (hHi : ‖H⁻¹‖ ≤ (2 : ℝ) ^ b)
    (herr : ‖H - G‖ ≤ 1 / (2 : ℝ) ^ (2 * t + 2 * b)) :
    ‖metricNormalizedMatrix H C - metricNormalizedMatrix G C‖ ≤
      ‖C‖ * (L + V + 1) * (1 / (2 : ℝ) ^ t) := by
  have hsmall : ‖H - G‖ ≤ 1 / (2 : ℝ) ^ (2 * t) := by
    apply herr.trans
    apply one_div_le_one_div_of_le (by positivity)
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hi : ‖H⁻¹ - G⁻¹‖ ≤ 1 / (2 : ℝ) ^ (2 * t) := by
    apply (matrixInverse_operator_error H G
      ((Matrix.isUnit_iff_isUnit_det _).mp hH.isUnit)
      ((Matrix.isUnit_iff_isUnit_det _).mp hG.isUnit)).trans
    calc
      _ ≤ (2 : ℝ) ^ b * 2 ^ b * (1 / (2 : ℝ) ^ (2 * t + 2 * b)) := by gcongr
      _ = _ := by
        rw [pow_add, two_mul b, pow_add]
        field_simp
  have hS := matrix_sqrt_dyadic_error t H G hH.posSemidef hG.posSemidef hsmall
  have hI := matrix_sqrt_dyadic_error t H⁻¹ G⁻¹ hH.inv.posSemidef hG.inv.posSemidef hi
  rw [matrix_sqrt_inverse, matrix_sqrt_inverse] at hI
  unfold metricNormalizedMatrix
  apply matrixSandwich_operator_error _ _ _ _ _ (by positivity)
    ((div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num))) hL hV
  · exact (repeatedEuclideanMatrix_error _ _ _).trans hS
  · exact (repeatedEuclideanMatrix_error _ _ _).trans hI
  · exact (repeatedEuclideanMatrix_norm_le _ _).trans hroot
  · exact (repeatedEuclideanMatrix_norm_le _ _).trans hinvroot

theorem metricNormalizedMatrix_metric_prescribed_error {d r m : ℕ} (t b : ℕ)
    (G H : Matrix (Fin d) (Fin d) ℝ) (C : Matrix (Fin (r * d)) (Fin (m * d)) ℝ)
    (hG : G.PosDef) (hH : H.PosDef)
    (hroot : ‖CFC.sqrt G‖ ≤ (2 : ℝ) ^ b) (hinvroot : ‖(CFC.sqrt G)⁻¹‖ ≤ (2 : ℝ) ^ b)
    (hGi : ‖G⁻¹‖ ≤ (2 : ℝ) ^ b) (hHi : ‖H⁻¹‖ ≤ (2 : ℝ) ^ b)
    (hC : ‖C‖ ≤ (2 : ℝ) ^ b)
    (herr : ‖H - G‖ ≤ 1 / (2 : ℝ) ^ (2 * (t + 2 * b + 2) + 2 * b)) :
    ‖metricNormalizedMatrix H C - metricNormalizedMatrix G C‖ ≤ 1 / (2 : ℝ) ^ t := by
  apply (metricNormalizedMatrix_metric_error (t + 2 * b + 2) b G H C hG hH
    (by positivity) (by positivity) hroot hinvroot hGi hHi herr).trans
  have hb : 1 ≤ (2 : ℝ) ^ b := one_le_pow₀ (by norm_num)
  have hf : ‖C‖ * ((2 : ℝ) ^ b + 2 ^ b + 1) ≤ 2 ^ (2 * b + 2) := by
    apply (mul_le_mul_of_nonneg_right hC (by positivity)).trans
    rw [pow_add, two_mul b, pow_add]
    norm_num
    nlinarith [sq_nonneg ((2 : ℝ) ^ b - 1)]
  calc
    _ ≤ (2 : ℝ) ^ (2 * b + 2) * (1 / (2 : ℝ) ^ (t + 2 * b + 2)) :=
      mul_le_mul_of_nonneg_right hf (by positivity)
    _ = _ := by
      rw [show t + 2 * b + 2 = t + (2 * b + 2) by omega, pow_add]
      field_simp
      simp only [pow_add]
      ring

/-- The rational conversion output approximates a real metric target. The
metric approximation is supplied; the normalized coefficient matrix is computed. -/
theorem rationalMetricNormalizedApprox_real_target {d r m : ℕ} (t b : ℕ)
    (G : Matrix (Fin d) (Fin d) ℝ) (H : Matrix (Fin d) (Fin d) ℚ)
    (C : Matrix (Fin (r * d)) (Fin (m * d)) ℚ)
    (hG : G.PosDef) (hH : (H.map (Rat.castHom ℝ)).PosDef)
    (hGroot : ‖CFC.sqrt G‖ ≤ (2 : ℝ) ^ b) (hGinvroot : ‖(CFC.sqrt G)⁻¹‖ ≤ (2 : ℝ) ^ b)
    (hHroot : ‖CFC.sqrt (H.map (Rat.castHom ℝ))‖ ≤ (2 : ℝ) ^ b)
    (hHinvroot : ‖(CFC.sqrt (H.map (Rat.castHom ℝ)))⁻¹‖ ≤ (2 : ℝ) ^ b)
    (hGi : ‖G⁻¹‖ ≤ (2 : ℝ) ^ b) (hHi : ‖(H.map (Rat.castHom ℝ))⁻¹‖ ≤ (2 : ℝ) ^ b)
    (hC : ‖C.map (Rat.castHom ℝ)‖ ≤ (2 : ℝ) ^ b)
    (hmetric : ‖H.map (Rat.castHom ℝ) - G‖ ≤ 1 / (2 : ℝ) ^ (2 * (t + 2 * b + 3) + 2 * b)) :
    ‖(rationalMetricNormalizedApprox (t + 2 * b + 3) H C).map (Rat.castHom ℝ) -
      metricNormalizedMatrix G (C.map (Rat.castHom ℝ))‖ ≤ 1 / (2 : ℝ) ^ t := by
  have hn : ‖(rationalMetricNormalizedApprox (t + 2 * b + 3) H C).map (Rat.castHom ℝ) -
      metricNormalizedMatrix (H.map (Rat.castHom ℝ)) (C.map (Rat.castHom ℝ))‖ ≤
      1 / (2 : ℝ) ^ (t + 1) := by
    simpa only [show t + 1 + 2 * b + 2 = t + 2 * b + 3 by omega] using
      rationalMetricNormalizedApprox_prescribed_error (t + 1) b H C hH hHroot hHinvroot hC
  have hm : ‖metricNormalizedMatrix (H.map (Rat.castHom ℝ)) (C.map (Rat.castHom ℝ)) -
      metricNormalizedMatrix G (C.map (Rat.castHom ℝ))‖ ≤ 1 / (2 : ℝ) ^ (t + 1) := by
    exact metricNormalizedMatrix_metric_prescribed_error (t + 1) b G _ _ hG hH
      hGroot hGinvroot hGi hHi hC
      (by simpa only [show t + 1 + 2 * b + 2 = t + 2 * b + 3 by omega] using hmetric)
  calc
    _ ≤ ‖(rationalMetricNormalizedApprox (t + 2 * b + 3) H C).map (Rat.castHom ℝ) -
          metricNormalizedMatrix (H.map (Rat.castHom ℝ)) (C.map (Rat.castHom ℝ))‖ +
        ‖metricNormalizedMatrix (H.map (Rat.castHom ℝ)) (C.map (Rat.castHom ℝ)) -
          metricNormalizedMatrix G (C.map (Rat.castHom ℝ))‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 1 / (2 : ℝ) ^ (t + 1) + 1 / (2 : ℝ) ^ (t + 1) := add_le_add hn hm
    _ = _ := by rw [pow_succ]; ring

end GeometricGaussianLHL

end MetricNormalizationStability

section MetricNormalizationPadding

/-!
## Repeated metrics and rectangular normalization in square buffers

The repeated metric is a reindexed Kronecker product. Mathlib supplies its
positivity; square-root uniqueness identifies its exact normalization factors.
Leading-row compression then recovers the rectangular metric product.
-/

noncomputable section
open scoped MatrixOrder Matrix.Norms.L2Operator Kronecker

namespace GeometricGaussianLHL

theorem repeatedEuclideanMatrix_kronecker {𝕜 : Type*} [CommRing 𝕜] {d : ℕ}
    (n : ℕ) (M : Matrix (Fin d) (Fin d) 𝕜) :
    repeatedEuclideanMatrix n M = ((1 : Matrix (Fin n) (Fin n) 𝕜) ⊗ₖ M).submatrix
      finProdFinEquiv.symm finProdFinEquiv.symm := by
  ext i j
  simp only [repeatedEuclideanMatrix, Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
    Matrix.one_apply]
  split_ifs <;> simp

theorem repeatedEuclideanMatrix_mul {𝕜 : Type*} [CommRing 𝕜] {d : ℕ}
    (n : ℕ) (M N : Matrix (Fin d) (Fin d) 𝕜) :
    repeatedEuclideanMatrix n (M * N) = repeatedEuclideanMatrix n M * repeatedEuclideanMatrix n N := by
  simp only [repeatedEuclideanMatrix_kronecker, Matrix.submatrix_mul_equiv,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul]

theorem repeatedEuclideanMatrix_one {𝕜 : Type*} [CommRing 𝕜] (n d : ℕ) :
    repeatedEuclideanMatrix n (1 : Matrix (Fin d) (Fin d) 𝕜) = 1 := by
  rw [repeatedEuclideanMatrix_kronecker, Matrix.one_kronecker_one, Matrix.submatrix_one_equiv]

theorem repeatedEuclideanMatrix_posSemidef {d : ℕ} (n : ℕ)
    (M : Matrix (Fin d) (Fin d) ℝ) (hM : M.PosSemidef) : (repeatedEuclideanMatrix n M).PosSemidef := by
  rw [repeatedEuclideanMatrix_kronecker]
  exact ((Matrix.PosSemidef.one : (1 : Matrix (Fin n) (Fin n) ℝ).PosSemidef).kronecker hM).submatrix _

theorem repeatedEuclideanMatrix_posDef {d : ℕ} (n : ℕ)
    (M : Matrix (Fin d) (Fin d) ℝ) (hM : M.PosDef) : (repeatedEuclideanMatrix n M).PosDef := by
  rw [repeatedEuclideanMatrix_kronecker]
  exact ((Matrix.PosDef.one : (1 : Matrix (Fin n) (Fin n) ℝ).PosDef).kronecker hM).submatrix
    finProdFinEquiv.symm.injective

theorem repeatedEuclideanMatrix_sqrt {d : ℕ} (n : ℕ)
    (M : Matrix (Fin d) (Fin d) ℝ) (hM : M.PosSemidef) :
    CFC.sqrt (repeatedEuclideanMatrix n M) = repeatedEuclideanMatrix n (CFC.sqrt M) := by
  apply CFC.sqrt_unique
  · rw [← repeatedEuclideanMatrix_mul, CFC.sqrt_mul_sqrt_self M hM.nonneg]
  · exact (repeatedEuclideanMatrix_posSemidef n _
      (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg M))).nonneg

theorem repeatedEuclideanMatrix_inverse {d : ℕ} (n : ℕ)
    (M : Matrix (Fin d) (Fin d) ℝ) (hM : IsUnit M) :
    (repeatedEuclideanMatrix n M)⁻¹ = repeatedEuclideanMatrix n M⁻¹ := by
  apply Matrix.inv_eq_right_inv
  rw [← repeatedEuclideanMatrix_mul, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hM),
    repeatedEuclideanMatrix_one]

theorem padMatrixRows_map {𝕜 𝕝 : Type*} [CommRing 𝕜] [CommRing 𝕝] {p q : ℕ}
    (hpq : p ≤ q) (C : Matrix (Fin p) (Fin q) 𝕜) (f : 𝕜 →+* 𝕝) :
    (padMatrixRows hpq C).map f = padMatrixRows hpq (C.map f) := by
  rw [padMatrixRows, padMatrixRows, Matrix.map_mul]
  congr 1
  ext i j
  by_cases h : i = Fin.castLE hpq j <;> simp [leadingRowEmbedding, Matrix.map_apply, h]

theorem leadingRowEmbedding_repeated_compress {𝕜 : Type*} [CommRing 𝕜] {d r m : ℕ}
    (hrm : r ≤ m) (H : Matrix (Fin d) (Fin d) 𝕜) :
    let J := leadingRowEmbedding (𝕜 := 𝕜) (Nat.mul_le_mul_right d hrm)
    J.transpose * repeatedEuclideanMatrix m H * J = repeatedEuclideanMatrix r H := by
  ext i j
  rw [leadingRowEmbedding_compress_apply]
  have hf (k : Fin (r * d)) : (Fin.castLE (Nat.mul_le_mul_right d hrm) k).modNat = k.modNat :=
    Fin.ext rfl
  simp [repeatedEuclideanMatrix, finProdFinEquiv, Fin.ext_iff, hf]

theorem metricNormalizedMatrix_padding {d r m : ℕ} (hrm : r ≤ m)
    (H : Matrix (Fin d) (Fin d) ℝ) (hH : H.PosDef)
    (C : Matrix (Fin (r * d)) (Fin (m * d)) ℝ) :
    let J := leadingRowEmbedding (𝕜 := ℝ) (Nat.mul_le_mul_right d hrm)
    J.transpose * (CFC.sqrt (repeatedEuclideanMatrix m H) *
      padMatrixRows (Nat.mul_le_mul_right d hrm) C * (CFC.sqrt (repeatedEuclideanMatrix m H))⁻¹) =
        metricNormalizedMatrix H C := by
  rw [repeatedEuclideanMatrix_sqrt m H hH.posSemidef,
    repeatedEuclideanMatrix_inverse m _ ((CFC.isUnit_sqrt_iff H hH.posSemidef.nonneg).mpr hH.isUnit)]
  dsimp only [padMatrixRows, metricNormalizedMatrix]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    leadingRowEmbedding_repeated_compress hrm]

theorem leadingRowEmbedding_restrict_error {p q : ℕ} (hpq : p ≤ q) (hp : 0 < p)
    (A B : Matrix (Fin q) (Fin q) ℝ) :
    ‖(leadingRowEmbedding hpq).transpose * A - (leadingRowEmbedding hpq).transpose * B‖ ≤ ‖A - B‖ := by
  rw [← Matrix.mul_sub]
  exact (Matrix.l2_opNorm_mul _ _).trans_eq (by
    rw [euclideanMatrix_transpose_norm, leadingRowEmbedding_norm hpq hp, one_mul])

end GeometricGaussianLHL
end

end MetricNormalizationPadding

section RealShapingGeometry

/-!
## Intrinsic geometry of the real trace-average covariance

The inverse-Gram right inverse is the minimum-norm right inverse. Its
remainder is the orthogonal kernel projection, so the Gram-filled target
agrees with the intrinsic kernel-filled covariance. The trace average
satisfies the two sharp bounds needed for the extreme-width identities.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped MatrixOrder Matrix.Norms.L2Operator

namespace GeometricGaussianLHL

def realRightInverseMatrix {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℝ) :
    Matrix (Fin q) (Fin p) ℝ := A.transpose * (A * A.transpose)⁻¹

theorem realRightInverseMatrix_right_inverse {p q : ℕ}
    (A : Matrix (Fin p) (Fin q) ℝ) (hA : IsUnit (A * A.transpose).det) :
    A * realRightInverseMatrix A = 1 := by
  rw [realRightInverseMatrix, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hA]

theorem realMatrix_gram_surjective {p q : ℕ}
    (A : Matrix (Fin p) (Fin q) ℝ) (hA : IsUnit (A * A.transpose).det) :
    Function.Surjective (Matrix.toEuclideanLin A) := by
  intro y
  refine ⟨Matrix.toEuclideanLin (realRightInverseMatrix A) y, ?_⟩
  change ((Matrix.toLpLin 2 2 A).comp (Matrix.toLpLin 2 2 (realRightInverseMatrix A))) y = y
  rw [← Matrix.toLpLin_mul_same, realRightInverseMatrix_right_inverse A hA, Matrix.toLpLin_one]
  rfl

theorem realRightInverseMatrix_minimumNorm {p q : ℕ}
    (A : Matrix (Fin p) (Fin q) ℝ) (hA : IsUnit (A * A.transpose).det) :
    (Matrix.toEuclideanLin (realRightInverseMatrix A)).toContinuousLinearMap =
      minimumNormRightInverse (Matrix.toEuclideanLin A).toContinuousLinearMap
        (realMatrix_gram_surjective A hA) := by
  let f := (Matrix.toEuclideanLin A).toContinuousLinearMap
  let R := (Matrix.toEuclideanLin (realRightInverseMatrix A)).toContinuousLinearMap
  let M := Matrix.toEuclideanLin ((A * A.transpose)⁻¹)
  have hr (y : Euclidean p) : f (R y) = y := by
    change ((Matrix.toLpLin 2 2 A).comp (Matrix.toLpLin 2 2 (realRightInverseMatrix A))) y = y
    rw [← Matrix.toLpLin_mul_same, realRightInverseMatrix_right_inverse A hA, Matrix.toLpLin_one]
    rfl
  have hrform (y : Euclidean p) : R y = f.adjoint (M y) := by
    change Matrix.toLpLin 2 2 (A.conjTranspose * (A * A.transpose)⁻¹) y = _
    rw [Matrix.toLpLin_mul_same]
    change Matrix.toEuclideanLin A.conjTranspose (M y) = _
    rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    rfl
  have hmem (y : Euclidean p) : R y ∈ f.toLinearMap.kerᗮ := by
    rw [Submodule.mem_orthogonal]
    intro x hx
    rw [hrform, ContinuousLinearMap.adjoint_inner_right, show f x = 0 from hx, inner_zero_left]
  ext y : 1
  have he : (⟨R y, hmem y⟩ : f.toLinearMap.kerᗮ) =
      (kernelOrthogonalEquiv f.toLinearMap (realMatrix_gram_surjective A hA)).symm y := by
    apply (kernelOrthogonalEquiv f.toLinearMap (realMatrix_gram_surjective A hA)).injective
    rw [LinearEquiv.apply_symm_apply]
    exact hr y
  exact congrArg (fun z : f.toLinearMap.kerᗮ => (z : Euclidean q)) he

theorem realMatrix_rows_le_cols {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℝ)
    (hA : IsUnit (A * A.transpose).det) : p ≤ q := by
  simpa using LinearMap.finrank_le_finrank_of_surjective (realMatrix_gram_surjective A hA)

theorem realKernelProjectionMatrix_operator {p q : ℕ}
    (A : Matrix (Fin p) (Fin q) ℝ) (hA : IsUnit (A * A.transpose).det) :
    (Matrix.toEuclideanLin (1 - realRightInverseMatrix A * A)).toContinuousLinearMap =
      (Matrix.toEuclideanLin A).ker.starProjection := by
  let f := (Matrix.toEuclideanLin A).toContinuousLinearMap
  have hp := minimumNormRightInverse_comp_self f (realMatrix_gram_surjective A hA)
  rw [← realRightInverseMatrix_minimumNorm A hA] at hp
  ext x : 1
  have he := congrArg (fun g : Euclidean q →L[ℝ] Euclidean q => g x) hp
  change Matrix.toEuclideanLin (realRightInverseMatrix A) (Matrix.toEuclideanLin A x) =
    f.toLinearMap.kerᗮ.starProjection x at he
  rw [map_sub]
  have hI : Matrix.toEuclideanLin (1 : Matrix (Fin q) (Fin q) ℝ) = LinearMap.id := Matrix.toLpLin_one 2
  rw [hI]
  change x - Matrix.toLpLin 2 2 (realRightInverseMatrix A * A) x = _
  rw [Matrix.toLpLin_mul_same]
  change x - Matrix.toEuclideanLin (realRightInverseMatrix A) (Matrix.toEuclideanLin A x) = _
  rw [he, Submodule.starProjection_orthogonal_val]
  abel

theorem realRightInverseMatrix_gram {p q : ℕ}
    (A : Matrix (Fin p) (Fin q) ℝ) (hA : IsUnit (A * A.transpose).det) :
    (realRightInverseMatrix A).transpose * realRightInverseMatrix A = (A * A.transpose)⁻¹ := by
  have hg : ((A * A.transpose)⁻¹).transpose = (A * A.transpose)⁻¹ := by
    simp only [Matrix.transpose_nonsing_inv, Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [realRightInverseMatrix, Matrix.transpose_mul, Matrix.transpose_transpose, hg]
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc A, Matrix.mul_nonsing_inv _ hA, Matrix.mul_one]

theorem realShapingKernelFill_sharp_bounds {p q : ℕ}
    (A : Matrix (Fin p) (Fin q) ℝ) (hp : 0 < p) (hA : IsUnit (A * A.transpose).det) :
    1 ≤ ‖A‖ ^ 2 * ((A * A.transpose)⁻¹.trace / (p : ℝ)) ∧
      (A * A.transpose)⁻¹.trace / (p : ℝ) ≤ ‖realRightInverseMatrix A‖ ^ 2 := by
  rw [← realRightInverseMatrix_gram A hA]
  exact ⟨matrix_rightInverse_trace_average_lower _ _ hp (realRightInverseMatrix_right_inverse A hA),
    matrix_gram_trace_average_le _ hp⟩

set_option maxHeartbeats 800000 in
theorem realShapingCovarianceMatrix_operator {p q : ℕ}
    (A : Matrix (Fin p) (Fin q) ℝ) (w : ℝ) (hA : IsUnit (A * A.transpose).det) :
    (Matrix.toEuclideanLin (realShapingCovarianceMatrix A w)).toContinuousLinearMap =
      kernelFilledCovariance (Matrix.toEuclideanLin A).toContinuousLinearMap
        (realMatrix_gram_surjective A hA) w ((A * A.transpose)⁻¹.trace / (p : ℝ)) := by
  have hgram {r : ℕ} (T : Matrix (Fin q) (Fin r) ℝ) :
      (Matrix.toEuclideanLin (T * T.transpose)).toContinuousLinearMap =
        (Matrix.toEuclideanLin T).toContinuousLinearMap.comp
          (Matrix.toEuclideanLin T).toContinuousLinearMap.adjoint := by
    ext x : 1
    change Matrix.toLpLin 2 2 (T * T.conjTranspose) x = _
    rw [Matrix.toLpLin_mul_same]
    change Matrix.toEuclideanLin T (Matrix.toEuclideanLin T.conjTranspose x) = _
    rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    rfl
  have hp := realKernelProjectionMatrix_operator A hA
  have hproj : (Matrix.toEuclideanLin
      ((1 - realRightInverseMatrix A * A) * (1 - realRightInverseMatrix A * A).transpose)).toContinuousLinearMap =
      (Matrix.toEuclideanLin A).ker.starProjection := by
    rw [hgram, hp, (Matrix.toEuclideanLin A).ker.starProjection_isSymmetric.clm_adjoint_eq]
    exact Submodule.starProjection_comp_starProjection_of_le (le_refl _)
  have hr := hgram (realRightInverseMatrix A)
  rw [realRightInverseMatrix_minimumNorm A hA] at hr
  rw [realShapingCovarianceMatrix, gramFilledCovariance]
  change (Matrix.toEuclideanLin (w ^ 2 •
    (realRightInverseMatrix A * (realRightInverseMatrix A).transpose +
      ((A * A.transpose)⁻¹.trace / (p : ℝ)) •
        ((1 - realRightInverseMatrix A * A) * (1 - realRightInverseMatrix A * A).transpose)))).toContinuousLinearMap = _
  simp only [map_smul, map_add]
  change w ^ 2 • ((Matrix.toEuclideanLin
    (realRightInverseMatrix A * (realRightInverseMatrix A).transpose)).toContinuousLinearMap +
    ((A * A.transpose)⁻¹.trace / (p : ℝ)) • (Matrix.toEuclideanLin
      ((1 - realRightInverseMatrix A * A) * (1 - realRightInverseMatrix A * A).transpose)).toContinuousLinearMap) = _
  rw [hr, hproj]
  rfl

end GeometricGaussianLHL
end

end RealShapingGeometry

section GramFilledCovarianceCost

/-!
## Costs of the positivity-preserving covariance formula

The kernel residual, two Gram matrices, scalar multiplication and addition
are computed as stored data. Explicit intermediate bit bounds control every
primitive cost in the composition.
-/

set_option backward.isDefEq.respectTransparency false
namespace GeometricGaussianLHL

def costedRationalKernelMatrix {p q : ℕ} (X : RationalRectData p q) (R : RationalRectData q p) : Costed (RationalMatrixData q) :=
  (costedRationalIdentity q).bind fun I =>
    (costedRationalRectMul R X).bind (costedRationalRectSub I)

theorem costedRationalKernelMatrix_data {p q : ℕ} (X : RationalRectData p q) (R : RationalRectData q p) :
    (costedRationalKernelMatrix X R).value = rationalRectMatrixData (1 - rationalRectMatrixOfData R * rationalRectMatrixOfData X) := by
  rw [costedRationalKernelMatrix, Costed.bind_value, costedRationalIdentity_data,
    Costed.bind_value, costedRationalRectMul_data, costedRationalRectSub_data]
  simp only [rationalRectMatrixOfData_data]

def rationalKernelMatrixBits (p L : ℕ) : ℕ := 5 * (rationalDotOperandBudget p L + 3) + 4
def rationalKernelMatrixBudget (p q L : ℕ) : ℕ :=
  rationalRectTraversalBudget q q (q + 2) + rationalRectMulBudget q p q L +
    rationalRectTraversalBudget q q ((2 * (rationalDotOperandBudget p L + 3) + 1) ^ 3)

theorem costedRationalKernelMatrix_steps_le {p q : ℕ} (X : RationalRectData p q) (R : RationalRectData q p) (L : ℕ)
    (hX : ∀ i j, rationalMagnitudeBits (rationalRectMatrixOfData X i j) ≤ L)
    (hR : ∀ i j, rationalMagnitudeBits (rationalRectMatrixOfData R i j) ≤ L) :
    (costedRationalKernelMatrix X R).steps ≤ rationalKernelMatrixBudget p q L := by
  have hI := costedRationalIdentity_steps_le q
  have hM := costedRationalRectMul_steps_le R X L hR hX
  have hS := costedRationalRectSub_steps_le (costedRationalIdentity q).value (costedRationalRectMul R X).value
    (rationalDotOperandBudget p L + 3)
    (fun i j => (costedRationalIdentity_size q i j).trans (by omega))
    (fun i j => (costedRationalRectMul_size R X L hR hX i j).trans (by omega))
  rw [costedRationalKernelMatrix, Costed.bind_steps, Costed.bind_steps]
  unfold rationalKernelMatrixBudget
  omega

theorem costedRationalKernelMatrix_size {p q : ℕ} (X : RationalRectData p q) (R : RationalRectData q p) (L : ℕ)
    (hX : ∀ i j, rationalMagnitudeBits (rationalRectMatrixOfData X i j) ≤ L)
    (hR : ∀ i j, rationalMagnitudeBits (rationalRectMatrixOfData R i j) ≤ L) (i j : Fin q) :
    rationalMagnitudeBits (rationalMatrixOfData (costedRationalKernelMatrix X R).value i j) ≤ rationalKernelMatrixBits p L := by
  rw [costedRationalKernelMatrix, Costed.bind_value, Costed.bind_value]
  exact costedRationalRectSub_size _ _ (rationalDotOperandBudget p L + 3)
    (fun i j => (costedRationalIdentity_size q i j).trans (by omega))
    (fun i j => (costedRationalRectMul_size R X L hR hX i j).trans (by omega)) i j

def costedRationalGramSum {p q : ℕ} (R : RationalRectData q p) (P : RationalMatrixData q) (c : ℚ) : Costed (RationalMatrixData q) :=
  (costedRationalRowGram R).bind fun RR =>
    (costedRationalRowGram P).bind fun PP =>
      (costedRationalRectScale c PP).bind (costedRationalRectAdd RR)

theorem costedRationalGramSum_data {p q : ℕ} (R : RationalRectData q p) (P : RationalMatrixData q) (c : ℚ) :
    (costedRationalGramSum R P c).value = rationalRectMatrixData
      (rationalRectMatrixOfData R * (rationalRectMatrixOfData R).transpose +
        c • (rationalMatrixOfData P * (rationalMatrixOfData P).transpose)) := by
  rw [costedRationalGramSum, Costed.bind_value, costedRationalRowGram_data,
    Costed.bind_value, costedRationalRowGram_data, Costed.bind_value, costedRationalRectScale_data,
    costedRationalRectAdd_data]
  simp only [rationalRectMatrixOfData_data]
  rfl

def rationalGramSumScaledBits (q L : ℕ) : ℕ := 6 * (L + rationalDotOperandBudget q L) + 3
def rationalGramSumBits (p q L : ℕ) : ℕ := 5 * (rationalDotOperandBudget p L + rationalGramSumScaledBits q L) + 4
def rationalGramSumBudget (p q L : ℕ) : ℕ :=
  rationalRowGramBudget q p L + rationalRowGramBudget q q L +
    rationalRectTraversalBudget q q ((2 * (L + rationalDotOperandBudget q L) + 1) ^ 3) +
    rationalRectTraversalBudget q q ((2 * (rationalDotOperandBudget p L + rationalGramSumScaledBits q L) + 1) ^ 3)

theorem costedRationalGramSum_bounds {p q : ℕ} (R : RationalRectData q p) (P : RationalMatrixData q) (c : ℚ) (L : ℕ)
    (hR : ∀ i j, rationalMagnitudeBits (rationalRectMatrixOfData R i j) ≤ L)
    (hP : ∀ i j, rationalMagnitudeBits (rationalMatrixOfData P i j) ≤ L)
    (hc : rationalMagnitudeBits c ≤ L) :
    (costedRationalGramSum R P c).steps ≤ rationalGramSumBudget p q L ∧
      ∀ i j, rationalMagnitudeBits (rationalMatrixOfData (costedRationalGramSum R P c).value i j) ≤ rationalGramSumBits p q L := by
  let RR := costedRationalRowGram R
  let PP := costedRationalRowGram P
  let S := costedRationalRectScale c PP.value
  have hRR : ∀ i j, rationalMagnitudeBits (rationalMatrixOfData RR.value i j) ≤ rationalDotOperandBudget p L := costedRationalRowGram_size R L hR
  have hPP : ∀ i j, rationalMagnitudeBits (rationalMatrixOfData PP.value i j) ≤ rationalDotOperandBudget q L := costedRationalRowGram_size P L hP
  have hc' : rationalMagnitudeBits c ≤ L + rationalDotOperandBudget q L := hc.trans (by omega)
  have hPP' : ∀ i j, rationalMagnitudeBits (rationalMatrixOfData PP.value i j) ≤ L + rationalDotOperandBudget q L := fun i j => (hPP i j).trans (by omega)
  have hS : ∀ i j, rationalMagnitudeBits (rationalMatrixOfData S.value i j) ≤ rationalGramSumScaledBits q L := costedRationalRectScale_size c PP.value _ hc' hPP'
  have hRR' : ∀ i j, rationalMagnitudeBits (rationalMatrixOfData RR.value i j) ≤ rationalDotOperandBudget p L + rationalGramSumScaledBits q L := fun i j => (hRR i j).trans (by omega)
  have hS' : ∀ i j, rationalMagnitudeBits (rationalMatrixOfData S.value i j) ≤ rationalDotOperandBudget p L + rationalGramSumScaledBits q L := fun i j => (hS i j).trans (by omega)
  constructor
  · have h₁ := costedRationalRowGram_steps_le R L hR
    have h₂ := costedRationalRowGram_steps_le P L hP
    have h₃ := costedRationalRectScale_steps_le c PP.value _ hc' hPP'
    have h₄ := costedRationalRectAdd_steps_le RR.value S.value _ hRR' hS'
    change RR.steps ≤ _ at h₁
    change PP.steps ≤ _ at h₂
    change S.steps ≤ _ at h₃
    rw [costedRationalGramSum, Costed.bind_steps, Costed.bind_steps, Costed.bind_steps]
    change RR.steps + (PP.steps + (S.steps + (costedRationalRectAdd RR.value S.value).steps)) ≤ _
    unfold rationalGramSumBudget
    omega
  · intro i j
    rw [costedRationalGramSum, Costed.bind_value, Costed.bind_value, Costed.bind_value]
    exact costedRationalRectAdd_size RR.value S.value _ hRR' hS' i j

def costedGramFilledCovariance {p q : ℕ} (X : RationalRectData p q) (R : RationalRectData q p) (c : ℚ) : Costed (RationalMatrixData q) :=
  (costedRationalKernelMatrix X R).bind (fun P => costedRationalGramSum R P c)

theorem costedGramFilledCovariance_data {p q : ℕ} (X : RationalRectData p q) (R : RationalRectData q p) (c : ℚ) :
    (costedGramFilledCovariance X R c).value = rationalRectMatrixData (gramFilledCovariance (rationalRectMatrixOfData X) (rationalRectMatrixOfData R) c) := by
  rw [costedGramFilledCovariance, Costed.bind_value, costedRationalKernelMatrix_data, costedRationalGramSum_data]
  change rationalRectMatrixData (_ + c • (rationalRectMatrixOfData _ * (rationalRectMatrixOfData _).transpose)) = _
  rw [rationalRectMatrixOfData_data]
  rfl

def gramFilledCovarianceBudget (p q L : ℕ) : ℕ :=
  rationalKernelMatrixBudget p q L + rationalGramSumBudget p q (L + rationalKernelMatrixBits p L)

def gramFilledCovarianceBits (p q L : ℕ) : ℕ := rationalGramSumBits p q (L + rationalKernelMatrixBits p L)

theorem costedGramFilledCovariance_bounds {p q : ℕ} (X : RationalRectData p q) (R : RationalRectData q p) (c : ℚ) (L : ℕ)
    (hX : ∀ i j, rationalMagnitudeBits (rationalRectMatrixOfData X i j) ≤ L)
    (hR : ∀ i j, rationalMagnitudeBits (rationalRectMatrixOfData R i j) ≤ L)
    (hc : rationalMagnitudeBits c ≤ L) :
    (costedGramFilledCovariance X R c).steps ≤ gramFilledCovarianceBudget p q L ∧
      ∀ i j, rationalMagnitudeBits (rationalMatrixOfData (costedGramFilledCovariance X R c).value i j) ≤ gramFilledCovarianceBits p q L := by
  let P := costedRationalKernelMatrix X R
  have hPs := costedRationalKernelMatrix_steps_le X R L hX hR
  have hP := costedRationalKernelMatrix_size X R L hX hR
  have hG := costedRationalGramSum_bounds R P.value c (L + rationalKernelMatrixBits p L)
    (fun i j => (hR i j).trans (by omega)) (fun i j => (hP i j).trans (by omega)) (hc.trans (by omega))
  constructor
  · rw [costedGramFilledCovariance, Costed.bind_steps]
    exact Nat.add_le_add hPs hG.1
  · rw [costedGramFilledCovariance, Costed.bind_value]
    exact hG.2

theorem polyBound_rationalKernelMatrixBits {p L : ℕ → ℕ} (hp : PolynomialCostBound p) (hL : PolynomialCostBound L) :
    PolynomialCostBound (fun x => rationalKernelMatrixBits (p x) (L x)) :=
  ((PolynomialCostBound.const 5).mul ((polyBound_rationalDotOperandBudget hp hL).add (PolynomialCostBound.const 3))).add (PolynomialCostBound.const 4)

theorem polyBound_rationalKernelMatrixBudget {p q L : ℕ → ℕ}
    (hp : PolynomialCostBound p) (hq : PolynomialCostBound q) (hL : PolynomialCostBound L) :
    PolynomialCostBound (fun x => rationalKernelMatrixBudget (p x) (q x) (L x)) :=
  ((polyBound_rationalRectTraversalBudget hq hq (hq.add (PolynomialCostBound.const 2))).add (polyBound_rationalRectMulBudget hq hp hq hL)).add
    (polyBound_rationalRectTraversalBudget hq hq ((((PolynomialCostBound.const 2).mul
      ((polyBound_rationalDotOperandBudget hp hL).add (PolynomialCostBound.const 3))).add (PolynomialCostBound.const 1)).pow 3))

theorem polyBound_rationalGramSumScaledBits {q L : ℕ → ℕ} (hq : PolynomialCostBound q) (hL : PolynomialCostBound L) :
    PolynomialCostBound (fun x => rationalGramSumScaledBits (q x) (L x)) :=
  ((PolynomialCostBound.const 6).mul (hL.add (polyBound_rationalDotOperandBudget hq hL))).add (PolynomialCostBound.const 3)

theorem polyBound_rationalGramSumBits {p q L : ℕ → ℕ}
    (hp : PolynomialCostBound p) (hq : PolynomialCostBound q) (hL : PolynomialCostBound L) :
    PolynomialCostBound (fun x => rationalGramSumBits (p x) (q x) (L x)) :=
  ((PolynomialCostBound.const 5).mul ((polyBound_rationalDotOperandBudget hp hL).add (polyBound_rationalGramSumScaledBits hq hL))).add (PolynomialCostBound.const 4)

theorem polyBound_rationalGramSumBudget {p q L : ℕ → ℕ}
    (hp : PolynomialCostBound p) (hq : PolynomialCostBound q) (hL : PolynomialCostBound L) :
    PolynomialCostBound (fun x => rationalGramSumBudget (p x) (q x) (L x)) := by
  have hA := hL.add (polyBound_rationalDotOperandBudget hq hL)
  have hB := (polyBound_rationalDotOperandBudget hp hL).add (polyBound_rationalGramSumScaledBits hq hL)
  exact (((polyBound_rationalRowGramBudget hq hp hL).add (polyBound_rationalRowGramBudget hq hq hL)).add
    (polyBound_rationalRectTraversalBudget hq hq ((((PolynomialCostBound.const 2).mul hA).add (PolynomialCostBound.const 1)).pow 3))).add
      (polyBound_rationalRectTraversalBudget hq hq ((((PolynomialCostBound.const 2).mul hB).add (PolynomialCostBound.const 1)).pow 3))

theorem polyBound_gramFilledCovarianceBudget {p q L : ℕ → ℕ}
    (hp : PolynomialCostBound p) (hq : PolynomialCostBound q) (hL : PolynomialCostBound L) :
    PolynomialCostBound (fun x => gramFilledCovarianceBudget (p x) (q x) (L x)) :=
  (polyBound_rationalKernelMatrixBudget hp hq hL).add (polyBound_rationalGramSumBudget hp hq (hL.add (polyBound_rationalKernelMatrixBits hp hL)))

theorem polyBound_gramFilledCovarianceBits {p q L : ℕ → ℕ}
    (hp : PolynomialCostBound p) (hq : PolynomialCostBound q) (hL : PolynomialCostBound L) :
    PolynomialCostBound (fun x => gramFilledCovarianceBits (p x) (q x) (L x)) :=
  polyBound_rationalGramSumBits hp hq (hL.add (polyBound_rationalKernelMatrixBits hp hL))

end GeometricGaussianLHL

end GramFilledCovarianceCost

section RationalCovarianceCost

/-!
## Stored covariance construction from the computed inverse Gram matrix

The inverse approximation feeds the actual right-inverse product and trace
average. Its output-size certificate supplies all later operand bounds.
-/

set_option backward.isDefEq.respectTransparency false
open scoped MatrixOrder Matrix.Norms.L2Operator
namespace GeometricGaussianLHL

def costedRationalRightApprox {p q : ℕ} (X : RationalRectData p q) (M : RationalMatrixData p) : Costed (RationalRectData q p) :=
  (costedRationalRectTranspose X).bind (fun XT => costedRationalRectMul XT M)

theorem costedRationalRightApprox_data {p q : ℕ} (X : RationalRectData p q) (M : RationalMatrixData p) :
    (costedRationalRightApprox X M).value = rationalRectMatrixData ((rationalRectMatrixOfData X).transpose * rationalMatrixOfData M) := by
  rw [costedRationalRightApprox, Costed.bind_value, costedRationalRectTranspose_data, costedRationalRectMul_data, rationalRectMatrixOfData_data]
  rfl

def rationalRightApproxBudget (p q L : ℕ) : ℕ := rationalRectTraversalBudget q p (L + 1) + rationalRectMulBudget q p p L

theorem costedRationalRightApprox_bounds {p q : ℕ} (X : RationalRectData p q) (M : RationalMatrixData p) (L : ℕ)
    (hX : ∀ i j, rationalMagnitudeBits (rationalRectMatrixOfData X i j) ≤ L)
    (hM : ∀ i j, rationalMagnitudeBits (rationalMatrixOfData M i j) ≤ L) :
    (costedRationalRightApprox X M).steps ≤ rationalRightApproxBudget p q L ∧
      ∀ i j, rationalMagnitudeBits (rationalRectMatrixOfData (costedRationalRightApprox X M).value i j) ≤ rationalDotOperandBudget p L := by
  have ht := costedRationalRectTranspose_size X L hX
  constructor
  · exact Nat.add_le_add (costedRationalRectTranspose_steps_le X L hX) (costedRationalRectMul_steps_le _ M L ht hM)
  · rw [costedRationalRightApprox, Costed.bind_value]
    exact costedRationalRectMul_size _ M L ht hM

def costedCovarianceFromInverse {p q : ℕ} (X : RationalRectData p q) (M : RationalMatrixData p) (w : ℚ) : Costed (RationalMatrixData q) :=
  (costedRationalRightApprox X M).bind fun R =>
    (costedRationalTraceMean M).bind fun c =>
      (costedGramFilledCovariance X R c).bind fun F =>
        (costedRatMul w w).bind (fun v => costedRationalRectScale v F)

theorem costedCovarianceFromInverse_data {p q : ℕ} (X : RationalRectData p q) (M : RationalMatrixData p) (w : ℚ) :
    (costedCovarianceFromInverse X M w).value = rationalRectMatrixData (w ^ 2 •
      gramFilledCovariance (rationalRectMatrixOfData X) ((rationalRectMatrixOfData X).transpose * rationalMatrixOfData M)
        ((rationalMatrixOfData M).trace / p)) := by
  rw [costedCovarianceFromInverse, Costed.bind_value, costedRationalRightApprox_data,
    Costed.bind_value, costedRationalTraceMean_value, Costed.bind_value, costedGramFilledCovariance_data, Costed.bind_value]
  dsimp only [costedRatMul]
  rw [costedRationalRectScale_data]
  simp only [rationalRectMatrixOfData_data, pow_two]

def covarianceFromInverseInputBits (p L : ℕ) : ℕ := L + rationalDotOperandBudget p L + (6 * rationalTraceMeanOperandBudget p L + 3)
def covarianceFromInverseScaleBits (p q L : ℕ) : ℕ := 6 * L + 3 + gramFilledCovarianceBits p q (covarianceFromInverseInputBits p L)
def covarianceFromInverseBits (p q L : ℕ) : ℕ := 6 * covarianceFromInverseScaleBits p q L + 3
def covarianceFromInverseBudget (p q L : ℕ) : ℕ :=
  rationalRightApproxBudget p q L + rationalTraceMeanBudget p L +
    gramFilledCovarianceBudget p q (covarianceFromInverseInputBits p L) + (2 * L + 1) ^ 3 +
    rationalRectTraversalBudget q q ((2 * covarianceFromInverseScaleBits p q L + 1) ^ 3)

theorem costedCovarianceFromInverse_bounds {p q : ℕ} (X : RationalRectData p q) (M : RationalMatrixData p) (w : ℚ) (L : ℕ)
    (hX : ∀ i j, rationalMagnitudeBits (rationalRectMatrixOfData X i j) ≤ L)
    (hM : ∀ i j, rationalMagnitudeBits (rationalMatrixOfData M i j) ≤ L)
    (hw : rationalMagnitudeBits w ≤ L) :
    (costedCovarianceFromInverse X M w).steps ≤ covarianceFromInverseBudget p q L ∧
      ∀ i j, rationalMagnitudeBits (rationalMatrixOfData (costedCovarianceFromInverse X M w).value i j) ≤ covarianceFromInverseBits p q L := by
  let R := costedRationalRightApprox X M
  let c := costedRationalTraceMean M
  let F := costedGramFilledCovariance X R.value c.value
  let J := covarianceFromInverseInputBits p L
  let T := covarianceFromInverseScaleBits p q L
  have hR := costedRationalRightApprox_bounds X M L hX hM
  have hc := costedRationalTraceMean_size M L hM
  have hF := costedGramFilledCovariance_bounds X R.value c.value J
    (fun i j => (hX i j).trans (by dsimp [J, covarianceFromInverseInputBits]; omega))
    (fun i j => (hR.2 i j).trans (by dsimp [J, covarianceFromInverseInputBits]; omega))
    (hc.trans (by dsimp [J, covarianceFromInverseInputBits]; omega))
  have hw2 : rationalMagnitudeBits (w * w) ≤ T := (rational_mul_bits_le w w L hw hw).trans
    (by dsimp [T, covarianceFromInverseScaleBits]; omega)
  have hF' : ∀ i j, rationalMagnitudeBits (rationalMatrixOfData F.value i j) ≤ T :=
    fun i j => (hF.2 i j).trans (by dsimp [J, T, covarianceFromInverseScaleBits]; omega)
  constructor
  · have hRs := hR.1
    have hcs := costedRationalTraceMean_steps_le M L hM
    have hFs := hF.1
    have hws := rationalArithmeticCost_le w w hw hw
    have hscale := costedRationalRectScale_steps_le (w * w) F.value T hw2 hF'
    change R.steps ≤ _ at hRs
    change c.steps ≤ _ at hcs
    change F.steps ≤ _ at hFs
    rw [costedCovarianceFromInverse, Costed.bind_steps, Costed.bind_steps, Costed.bind_steps, Costed.bind_steps]
    change R.steps + (c.steps + (F.steps + (rationalArithmeticCost w w + (costedRationalRectScale (w * w) F.value).steps))) ≤ _
    change _ ≤ rationalRightApproxBudget p q L + rationalTraceMeanBudget p L + gramFilledCovarianceBudget p q J +
      (2 * L + 1) ^ 3 + rationalRectTraversalBudget q q ((2 * T + 1) ^ 3)
    omega
  · intro i j
    rw [costedCovarianceFromInverse, Costed.bind_value, Costed.bind_value, Costed.bind_value, Costed.bind_value]
    dsimp only [costedRatMul]
    exact costedRationalRectScale_size (w * w) F.value T hw2 hF' i j

def costedRationalShapingCovariance {p q : ℕ} (t : ℕ) (X : RationalRectData p q) (w : ℚ) : Costed (RationalMatrixData q) :=
  (costedRationalRowGram X).bind fun G =>
    (costedRationalSpectralApprox true t G).bind (fun M => costedCovarianceFromInverse X M w)

theorem costedRationalShapingCovariance_data {p q : ℕ} (t : ℕ) (X : RationalRectData p q) (w : ℚ) :
    (costedRationalShapingCovariance t X w).value = rationalRectMatrixData (rationalShapingApproxCovariance t (rationalRectMatrixOfData X) w) := by
  rw [costedRationalShapingCovariance, Costed.bind_value, costedRationalRowGram_data]
  change ((costedRationalSpectralApprox true t (rationalMatrixData
    (rationalRectMatrixOfData X * (rationalRectMatrixOfData X).transpose))).bind
      (fun M => costedCovarianceFromInverse X M w)).value = _
  rw [Costed.bind_value, costedRationalSpectralApprox_data, rationalMatrixOfData_data,
    ite_eq_left rfl, costedCovarianceFromInverse_data, rationalMatrixOfData_data]
  simp only [rationalShapingApproxCovariance, materializeMatrix_eq]

def rationalCovarianceInverseBudget (p q L t : ℕ) : ℕ := rationalSpectralBudget p (p * p * rationalDotOperandBudget q L) t
def rationalShapingCovarianceBudget (p q L t : ℕ) : ℕ :=
  rationalRowGramBudget p q L + rationalCovarianceInverseBudget p q L t +
    covarianceFromInverseBudget p q (L + rationalCovarianceInverseBudget p q L t)
def rationalShapingCovarianceBits (p q L t : ℕ) : ℕ := covarianceFromInverseBits p q (L + rationalCovarianceInverseBudget p q L t)

theorem costedRationalShapingCovariance_bounds {p q : ℕ} (t : ℕ) (X : RationalRectData p q) (w : ℚ) (L : ℕ)
    (hX : ∀ i j, rationalMagnitudeBits (rationalRectMatrixOfData X i j) ≤ L)
    (hw : rationalMagnitudeBits w ≤ L)
    (hA : IsUnit (rationalRectMatrixOfData X * (rationalRectMatrixOfData X).transpose).det) :
    (costedRationalShapingCovariance t X w).steps ≤ rationalShapingCovarianceBudget p q L t ∧
      ∀ i j, rationalMagnitudeBits (rationalMatrixOfData (costedRationalShapingCovariance t X w).value i j) ≤ rationalShapingCovarianceBits p q L t := by
  let G := costedRationalRowGram X
  let M := costedRationalSpectralApprox true t G.value
  let B := rationalCovarianceInverseBudget p q L t
  have hG : ((rationalMatrixOfData G.value).map (fun r : ℚ => (r : ℝ))).PosDef := by
    change ((rationalRectMatrixOfData G.value).map (Rat.castHom ℝ)).PosDef
    rw [costedRationalRowGram_data, rationalRectMatrixOfData_data]
    exact rationalGram_real_posDef _ hA
  have hGsize : rationalMatrixMagnitudeBits (rationalMatrixOfData G.value) ≤ p * p * rationalDotOperandBudget q L := by
    calc
      _ ≤ ∑ i : Fin p, ∑ j : Fin p, rationalDotOperandBudget q L :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => costedRationalRowGram_size X L hX i j))
      _ = _ := by simp; ring
  have hMs : M.steps ≤ B := (costedRationalSpectralApprox_steps_le true t G.value hG).trans
    (rationalSpectralBudget_mono le_rfl hGsize le_rfl)
  have hMlen := (costedRationalSpectralApprox_length_le_steps true t G.value).trans hMs
  have hF := costedCovarianceFromInverse_bounds X M.value w (L + B)
    (fun i j => (hX i j).trans (by omega))
    (fun i j => ((rationalMatrixEntryBits_le_encoded M.value i j).trans hMlen).trans (by omega))
    (hw.trans (by omega))
  have hGs := costedRationalRowGram_steps_le X L hX
  constructor
  · rw [costedRationalShapingCovariance, Costed.bind_steps, Costed.bind_steps]
    change G.steps + (M.steps + (costedCovarianceFromInverse X M.value w).steps) ≤ _
    change _ ≤ rationalRowGramBudget p q L + B + covarianceFromInverseBudget p q (L + B)
    change G.steps ≤ _ at hGs
    omega
  · rw [costedRationalShapingCovariance, Costed.bind_value, Costed.bind_value]
    exact hF.2

end GeometricGaussianLHL

end RationalCovarianceCost

section RationalInverseRootCost

/-!
## Arithmetic cost of the computed inverse square root

Both precisions are computed by charged natural arithmetic. The positive
inverse output supplies the next routine's validity, and its serialized length
bounds every entry of the square-root input.
-/

open scoped MatrixOrder Matrix.Norms.L2Operator
namespace GeometricGaussianLHL

def costedRationalInverseRoot {n : ℕ} (t : ℕ) (D : RationalMatrixData n) : Costed (RationalMatrixData n) :=
  (costedNatAdd t 1).bind fun u =>
    (costedNatMul 2 u).bind fun z =>
      (costedRationalSpectralApprox true z D).bind (costedRationalSpectralApprox false u)

theorem costedRationalInverseRoot_data {n : ℕ} (t : ℕ) (D : RationalMatrixData n) :
    (costedRationalInverseRoot t D).value = rationalMatrixData (rationalInverseRootApprox t (rationalMatrixOfData D)) := by
  rw [costedRationalInverseRoot, Costed.bind_value]
  dsimp only [costedNatAdd]
  rw [Costed.bind_value]
  dsimp only [costedNatMul]
  rw [Costed.bind_value, costedRationalSpectralApprox_data true (2 * (t + 1)) D, ite_eq_left rfl,
    costedRationalSpectralApprox_data, rationalMatrixOfData_data, ite_eq_right (by decide)]
  rfl

def rationalInverseRootOutputBudget (n S t : ℕ) : ℕ :=
  rationalSpectralBudget n (n * n * rationalSpectralBudget n S (2 * (t + 1))) (t + 1)
def rationalInverseRootBudget (n S t : ℕ) : ℕ :=
  2 * (2 * (t + 3) + 1) ^ 2 + rationalSpectralBudget n S (2 * (t + 1)) + rationalInverseRootOutputBudget n S t

theorem costedRationalInverseRoot_bounds {n : ℕ} (t : ℕ) (D : RationalMatrixData n)
    (hD : ((rationalMatrixOfData D).map (fun q : ℚ => (q : ℝ))).PosDef) :
    (costedRationalInverseRoot t D).steps ≤ rationalInverseRootBudget n (rationalMatrixMagnitudeBits (rationalMatrixOfData D)) t ∧
      (encodeRationalMatrixData (costedRationalInverseRoot t D).value).length ≤
        rationalInverseRootOutputBudget n (rationalMatrixMagnitudeBits (rationalMatrixOfData D)) t := by
  let S := rationalMatrixMagnitudeBits (rationalMatrixOfData D)
  let I := costedRationalSpectralApprox true (2 * (t + 1)) D
  let R := costedRationalSpectralApprox false (t + 1) I.value
  let B := rationalSpectralBudget n S (2 * (t + 1))
  have hI : I.steps ≤ B := costedRationalSpectralApprox_steps_le true (2 * (t + 1)) D hD
  have hIl := (costedRationalSpectralApprox_length_le_steps true (2 * (t + 1)) D).trans hI
  have hsize : rationalMatrixMagnitudeBits (rationalMatrixOfData I.value) ≤ n * n * B := by
    calc
      _ ≤ ∑ i : Fin n, ∑ j : Fin n, B := Finset.sum_le_sum (fun i _ => Finset.sum_le_sum
        (fun j _ => (rationalMatrixEntryBits_le_encoded I.value i j).trans hIl))
      _ = _ := by simp; ring
  have hR : R.steps ≤ rationalInverseRootOutputBudget n S t :=
    (costedRationalSpectralApprox_steps_le false (t + 1) I.value (costedRationalSpectralInverse_posDef _ D hD)).trans
      (rationalSpectralBudget_mono le_rfl hsize le_rfl)
  constructor
  · have ha := costedNatAdd_steps_le t 1 (t + 3) (by omega) (by omega)
    have hm := costedNatMul_steps_le 2 (t + 1) (t + 3) (by omega) (by omega)
    rw [costedRationalInverseRoot, Costed.bind_steps]
    dsimp only [costedNatAdd]
    rw [Costed.bind_steps]
    dsimp only [costedNatMul]
    rw [Costed.bind_steps]
    change t.size + 1 + 1 + (((2 : ℕ).size + (t + 1).size + 1) ^ 2 + (I.steps + R.steps)) ≤ _
    change _ ≤ 2 * (2 * (t + 3) + 1) ^ 2 + B + rationalInverseRootOutputBudget n S t
    dsimp only [costedNatAdd, costedNatMul] at ha hm
    simp only [Nat.size_one] at ha
    omega
  · rw [costedRationalInverseRoot, Costed.bind_value]
    dsimp only [costedNatAdd]
    rw [Costed.bind_value]
    dsimp only [costedNatMul]
    rw [Costed.bind_value]
    exact (costedRationalSpectralApprox_length_le_steps false (t + 1) I.value).trans hR

theorem polyBound_rationalInverseRootOutputBudget {n S t : ℕ → ℕ}
    (hn : PolynomialCostBound n) (hS : PolynomialCostBound S) (ht : PolynomialCostBound t) :
    PolynomialCostBound (fun x => rationalInverseRootOutputBudget (n x) (S x) (t x)) := by
  have hu := ht.add (PolynomialCostBound.const 1)
  exact polyBound_rationalSpectralBudget hn ((hn.mul hn).mul
    (polyBound_rationalSpectralBudget hn hS ((PolynomialCostBound.const 2).mul hu))) hu

theorem polyBound_rationalInverseRootBudget {n S t : ℕ → ℕ}
    (hn : PolynomialCostBound n) (hS : PolynomialCostBound S) (ht : PolynomialCostBound t) :
    PolynomialCostBound (fun x => rationalInverseRootBudget (n x) (S x) (t x)) :=
  (((PolynomialCostBound.const 2).mul ((((PolynomialCostBound.const 2).mul
    (ht.add (PolynomialCostBound.const 3))).add (PolynomialCostBound.const 1)).pow 2)).add
      (polyBound_rationalSpectralBudget hn hS ((PolynomialCostBound.const 2).mul (ht.add (PolynomialCostBound.const 1))))).add
        (polyBound_rationalInverseRootOutputBudget hn hS ht)

theorem rationalInverseRootOutputBudget_mono {n n' S S' t t' : ℕ}
    (hn : n ≤ n') (hS : S ≤ S') (ht : t ≤ t') :
    rationalInverseRootOutputBudget n S t ≤ rationalInverseRootOutputBudget n' S' t' := by
  apply rationalSpectralBudget_mono hn _ (by omega)
  have h := rationalSpectralBudget_mono hn hS (show 2 * (t + 1) ≤ 2 * (t' + 1) by omega)
  gcongr

theorem rationalInverseRootBudget_mono {n n' S S' t t' : ℕ}
    (hn : n ≤ n') (hS : S ≤ S') (ht : t ≤ t') :
    rationalInverseRootBudget n S t ≤ rationalInverseRootBudget n' S' t' := by
  apply Nat.add_le_add
  · exact Nat.add_le_add (by gcongr) (rationalSpectralBudget_mono hn hS (by omega))
  · exact rationalInverseRootOutputBudget_mono hn hS ht

end GeometricGaussianLHL

end RationalInverseRootCost

section RationalShapingScheduleCost

/-!
## Computing the shaping precision schedule

The matrix scan, width-size measurement and natural arithmetic are charged.
The three returned precisions agree with the existing numerical algorithm.
-/

namespace GeometricGaussianLHL

structure RationalShapingSchedule where
  inversePrecision : ℕ
  rootPrecision : ℕ
  shiftPrecision : ℕ

def rationalShapingSchedule (t E B b : ℕ) : RationalShapingSchedule :=
  ⟨2 * (t + 2) + (4 * E + 2 * B + 4 * b + 6), t + 2, t + 1⟩

def costedShapingScheduleArithmetic (t E B b : ℕ) : Costed RationalShapingSchedule :=
  let e := costedNatMul 4 E
  let c := costedNatMul 2 B
  let z := costedNatMul 4 b
  let a := costedNatAdd e.value c.value
  let d := costedNatAdd a.value z.value
  let g := costedNatAdd d.value 6
  let r := costedNatAdd t 2
  let u := costedNatMul 2 r.value
  let i := costedNatAdd u.value g.value
  let s := costedNatAdd t 1
  ⟨⟨i.value, r.value, s.value⟩,
    e.steps + c.steps + z.steps + a.steps + d.steps + g.steps + r.steps + u.steps + i.steps + s.steps⟩

theorem costedShapingScheduleArithmetic_value (t E B b : ℕ) :
    (costedShapingScheduleArithmetic t E B b).value = rationalShapingSchedule t E B b := rfl

def shapingScheduleArithmeticBudget (t E B b : ℕ) : ℕ :=
  10 * (2 * (4 * E + 2 * B + 4 * b + 2 * t + 12) + 1) ^ 2

theorem costedShapingScheduleArithmetic_steps_le (t E B b : ℕ) :
    (costedShapingScheduleArithmetic t E B b).steps ≤ shapingScheduleArithmeticBudget t E B b := by
  let H := 4 * E + 2 * B + 4 * b + 2 * t + 12
  have h₁ := costedNatMul_steps_le 4 E H (by dsimp [H]; omega) (by dsimp [H]; omega)
  have h₂ := costedNatMul_steps_le 2 B H (by dsimp [H]; omega) (by dsimp [H]; omega)
  have h₃ := costedNatMul_steps_le 4 b H (by dsimp [H]; omega) (by dsimp [H]; omega)
  have h₄ := costedNatAdd_steps_le (4 * E) (2 * B) H (by dsimp [H]; omega) (by dsimp [H]; omega)
  have h₅ := costedNatAdd_steps_le (4 * E + 2 * B) (4 * b) H (by dsimp [H]; omega) (by dsimp [H]; omega)
  have h₆ := costedNatAdd_steps_le (4 * E + 2 * B + 4 * b) 6 H (by dsimp [H]; omega) (by dsimp [H]; omega)
  have h₇ := costedNatAdd_steps_le t 2 H (by dsimp [H]; omega) (by dsimp [H]; omega)
  have h₈ := costedNatMul_steps_le 2 (t + 2) H (by dsimp [H]; omega) (by dsimp [H]; omega)
  have h₉ := costedNatAdd_steps_le (2 * (t + 2)) (4 * E + 2 * B + 4 * b + 6) H (by dsimp [H]; omega) (by dsimp [H]; omega)
  have h₁₀ := costedNatAdd_steps_le t 1 H (by dsimp [H]; omega) (by dsimp [H]; omega)
  dsimp only [costedShapingScheduleArithmetic, costedNatMul, costedNatAdd] at *
  change _ ≤ 10 * (2 * H + 1) ^ 2
  omega

def costedRationalShapingSchedule {p : ℕ} (t : ℕ) (G : RationalMatrixData p) (w : ℚ) : Costed RationalShapingSchedule :=
  (costedRationalMagnitude G).bind fun S =>
    (costedRationalNormalizationSchedule p S).bind fun N =>
      (Costed.charge (rationalMagnitudeBits w + 1) (rationalMagnitudeBits w)).bind fun b =>
        costedShapingScheduleArithmetic t N.normalizationExponent N.conditionExponent b

theorem costedRationalShapingSchedule_value {p : ℕ} (t : ℕ) (G : RationalMatrixData p) (w : ℚ) :
    (costedRationalShapingSchedule t G w).value = rationalShapingSchedule t
      (rationalMatrixNormalizationExponent (rationalMatrixOfData G))
      (rationalMatrixConditionExponent (rationalMatrixOfData G)) (rationalMagnitudeBits w) := by
  rw [costedRationalShapingSchedule, Costed.bind_value, costedRationalMagnitude_value,
    Costed.bind_value, costedRationalNormalizationSchedule_value, Costed.bind_value]
  rfl

def rationalShapingScheduleBudget (p S b t : ℕ) : ℕ :=
  rationalMagnitudeBudget p S + rationalNormalizationScheduleBudget p S + (b + 1) +
    shapingScheduleArithmeticBudget t (2 * (p + 2 * S)) (p * (S + 2 * (p + 2 * S))) b

theorem costedRationalShapingSchedule_steps_le {p : ℕ} (t : ℕ) (G : RationalMatrixData p) (w : ℚ) :
    (costedRationalShapingSchedule t G w).steps ≤ rationalShapingScheduleBudget p
      (rationalMatrixMagnitudeBits (rationalMatrixOfData G)) (rationalMagnitudeBits w) t := by
  let S := rationalMatrixMagnitudeBits (rationalMatrixOfData G)
  have h₁ := costedRationalMagnitude_steps_le G
  have h₂ := costedRationalNormalizationSchedule_steps_le p S
  have h₃ := costedShapingScheduleArithmetic_steps_le t (2 * (p + 2 * S))
    (p * (S + 2 * (p + 2 * S))) (rationalMagnitudeBits w)
  rw [costedRationalShapingSchedule, Costed.bind_steps, costedRationalMagnitude_value,
    Costed.bind_steps, costedRationalNormalizationSchedule_value, Costed.bind_steps]
  dsimp only [Costed.charge, rationalNormalizationSchedule]
  change _ ≤ rationalMagnitudeBudget p S + rationalNormalizationScheduleBudget p S +
    (rationalMagnitudeBits w + 1) + shapingScheduleArithmeticBudget t (2 * (p + 2 * S))
      (p * (S + 2 * (p + 2 * S))) (rationalMagnitudeBits w)
  change (costedRationalMagnitude G).steps ≤ rationalMagnitudeBudget p S at h₁
  dsimp only [S] at *
  omega

theorem polyBound_shapingScheduleArithmeticBudget {t E B b : ℕ → ℕ}
    (ht : PolynomialCostBound t) (hE : PolynomialCostBound E) (hB : PolynomialCostBound B) (hb : PolynomialCostBound b) :
    PolynomialCostBound (fun x => shapingScheduleArithmeticBudget (t x) (E x) (B x) (b x)) :=
  (PolynomialCostBound.const 10).mul ((((PolynomialCostBound.const 2).mul
    ((((((PolynomialCostBound.const 4).mul hE).add ((PolynomialCostBound.const 2).mul hB)).add
      ((PolynomialCostBound.const 4).mul hb)).add ((PolynomialCostBound.const 2).mul ht)).add
        (PolynomialCostBound.const 12))).add (PolynomialCostBound.const 1)).pow 2)

theorem polyBound_rationalShapingScheduleBudget {p S b t : ℕ → ℕ}
    (hp : PolynomialCostBound p) (hS : PolynomialCostBound S) (hb : PolynomialCostBound b) (ht : PolynomialCostBound t) :
    PolynomialCostBound (fun x => rationalShapingScheduleBudget (p x) (S x) (b x) (t x)) := by
  have hE := (PolynomialCostBound.const 2).mul (hp.add ((PolynomialCostBound.const 2).mul hS))
  exact (((polyBound_rationalMagnitudeBudget hp hS).add (polyBound_rationalNormalizationScheduleBudget hp hS)).add
    (hb.add (PolynomialCostBound.const 1))).add (polyBound_shapingScheduleArithmeticBudget ht hE (hp.mul (hS.add hE)) hb)

theorem rationalShapingScheduleBudget_mono {p p' S S' b b' t t' : ℕ}
    (hp : p ≤ p') (hS : S ≤ S') (hb : b ≤ b') (ht : t ≤ t') :
    rationalShapingScheduleBudget p S b t ≤ rationalShapingScheduleBudget p' S' b' t' := by
  unfold rationalShapingScheduleBudget rationalMagnitudeBudget natSumBudget
    rationalNormalizationScheduleBudget shapingScheduleArithmeticBudget
  gcongr

end GeometricGaussianLHL

end RationalShapingScheduleCost

section RationalCovarianceBounds

/-!
## Polynomial envelopes for the complete rational covariance construction

The bounds compose through the stored inverse output, whose serialized length
already has a polynomial bound. No separate intermediate-size hypothesis is
required from the caller.
-/

namespace GeometricGaussianLHL

theorem polyBound_rationalRightApproxBudget {p q L : ℕ → ℕ}
    (hp : PolynomialCostBound p) (hq : PolynomialCostBound q) (hL : PolynomialCostBound L) :
    PolynomialCostBound (fun x => rationalRightApproxBudget (p x) (q x) (L x)) :=
  (polyBound_rationalRectTraversalBudget hq hp (hL.add (PolynomialCostBound.const 1))).add
    (polyBound_rationalRectMulBudget hq hp hp hL)

theorem polyBound_covarianceFromInverseInputBits {p L : ℕ → ℕ}
    (hp : PolynomialCostBound p) (hL : PolynomialCostBound L) :
    PolynomialCostBound (fun x => covarianceFromInverseInputBits (p x) (L x)) :=
  (hL.add (polyBound_rationalDotOperandBudget hp hL)).add
    (((PolynomialCostBound.const 6).mul (polyBound_rationalTraceMeanOperandBudget hp hL)).add (PolynomialCostBound.const 3))

theorem polyBound_covarianceFromInverseScaleBits {p q L : ℕ → ℕ}
    (hp : PolynomialCostBound p) (hq : PolynomialCostBound q) (hL : PolynomialCostBound L) :
    PolynomialCostBound (fun x => covarianceFromInverseScaleBits (p x) (q x) (L x)) :=
  (((PolynomialCostBound.const 6).mul hL).add (PolynomialCostBound.const 3)).add
    (polyBound_gramFilledCovarianceBits hp hq (polyBound_covarianceFromInverseInputBits hp hL))

theorem polyBound_covarianceFromInverseBits {p q L : ℕ → ℕ}
    (hp : PolynomialCostBound p) (hq : PolynomialCostBound q) (hL : PolynomialCostBound L) :
    PolynomialCostBound (fun x => covarianceFromInverseBits (p x) (q x) (L x)) :=
  ((PolynomialCostBound.const 6).mul (polyBound_covarianceFromInverseScaleBits hp hq hL)).add (PolynomialCostBound.const 3)

theorem polyBound_covarianceFromInverseBudget {p q L : ℕ → ℕ}
    (hp : PolynomialCostBound p) (hq : PolynomialCostBound q) (hL : PolynomialCostBound L) :
    PolynomialCostBound (fun x => covarianceFromInverseBudget (p x) (q x) (L x)) :=
  ((((polyBound_rationalRightApproxBudget hp hq hL).add (polyBound_rationalTraceMeanBudget hp hL)).add
    (polyBound_gramFilledCovarianceBudget hp hq (polyBound_covarianceFromInverseInputBits hp hL))).add
      ((((PolynomialCostBound.const 2).mul hL).add (PolynomialCostBound.const 1)).pow 3)).add
        (polyBound_rationalRectTraversalBudget hq hq ((((PolynomialCostBound.const 2).mul
          (polyBound_covarianceFromInverseScaleBits hp hq hL)).add (PolynomialCostBound.const 1)).pow 3))

theorem polyBound_rationalCovarianceInverseBudget {p q L t : ℕ → ℕ}
    (hp : PolynomialCostBound p) (hq : PolynomialCostBound q) (hL : PolynomialCostBound L) (ht : PolynomialCostBound t) :
    PolynomialCostBound (fun x => rationalCovarianceInverseBudget (p x) (q x) (L x) (t x)) :=
  polyBound_rationalSpectralBudget hp ((hp.mul hp).mul (polyBound_rationalDotOperandBudget hq hL)) ht

theorem polyBound_rationalShapingCovarianceBudget {p q L t : ℕ → ℕ}
    (hp : PolynomialCostBound p) (hq : PolynomialCostBound q) (hL : PolynomialCostBound L) (ht : PolynomialCostBound t) :
    PolynomialCostBound (fun x => rationalShapingCovarianceBudget (p x) (q x) (L x) (t x)) := by
  have hB := polyBound_rationalCovarianceInverseBudget hp hq hL ht
  exact ((polyBound_rationalRowGramBudget hp hq hL).add hB).add
    (polyBound_covarianceFromInverseBudget hp hq (hL.add hB))

theorem polyBound_rationalShapingCovarianceBits {p q L t : ℕ → ℕ}
    (hp : PolynomialCostBound p) (hq : PolynomialCostBound q) (hL : PolynomialCostBound L) (ht : PolynomialCostBound t) :
    PolynomialCostBound (fun x => rationalShapingCovarianceBits (p x) (q x) (L x) (t x)) :=
  polyBound_covarianceFromInverseBits hp hq (hL.add (polyBound_rationalCovarianceInverseBudget hp hq hL ht))

theorem rationalDotOperandBudget_mono {m m' L L' : ℕ} (hm : m ≤ m') (hL : L ≤ L') :
    rationalDotOperandBudget m L ≤ rationalDotOperandBudget m' L' := by
  unfold rationalDotOperandBudget
  gcongr

theorem rationalDotBudget_mono {m m' L L' : ℕ} (hm : m ≤ m') (hL : L ≤ L') :
    rationalDotBudget m L ≤ rationalDotBudget m' L' := by
  unfold rationalDotBudget
  gcongr
  exact rationalDotOperandBudget_mono hm hL

theorem rationalRectTraversalBudget_mono {p p' q q' L L' : ℕ}
    (hp : p ≤ p') (hq : q ≤ q') (hL : L ≤ L') :
    rationalRectTraversalBudget p q L ≤ rationalRectTraversalBudget p' q' L' := by
  unfold rationalRectTraversalBudget
  gcongr

theorem rationalRectMulBudget_mono {p p' q q' r r' L L' : ℕ}
    (hp : p ≤ p') (hq : q ≤ q') (hr : r ≤ r') (hL : L ≤ L') :
    rationalRectMulBudget p q r L ≤ rationalRectMulBudget p' q' r' L' :=
  rationalRectTraversalBudget_mono hp hr (Nat.add_le_add (by omega) (rationalDotBudget_mono hq hL))

theorem rationalRowGramBudget_mono {p p' q q' L L' : ℕ}
    (hp : p ≤ p') (hq : q ≤ q') (hL : L ≤ L') :
    rationalRowGramBudget p q L ≤ rationalRowGramBudget p' q' L' :=
  Nat.add_le_add (rationalRectTraversalBudget_mono hq hp (by omega)) (rationalRectMulBudget_mono hp hq hp hL)

theorem rationalTraceMeanOperandBudget_mono {n n' L L' : ℕ} (hn : n ≤ n') (hL : L ≤ L') :
    rationalTraceMeanOperandBudget n L ≤ rationalTraceMeanOperandBudget n' L' :=
  Nat.add_le_add_right (Nat.add_le_add (rationalDotOperandBudget_mono hn (by omega)) hn) 2

theorem rationalTraceMeanBudget_mono {n n' L L' : ℕ} (hn : n ≤ n') (hL : L ≤ L') :
    rationalTraceMeanBudget n L ≤ rationalTraceMeanBudget n' L' := by
  have hd := rationalDotBudget_mono hn (show L + 3 ≤ L' + 3 by omega)
  have ho := rationalTraceMeanOperandBudget_mono hn hL
  unfold rationalTraceMeanBudget rationalTraceBudget
  gcongr

theorem rationalKernelMatrixBits_mono {p p' L L' : ℕ} (hp : p ≤ p') (hL : L ≤ L') :
    rationalKernelMatrixBits p L ≤ rationalKernelMatrixBits p' L' := by
  unfold rationalKernelMatrixBits
  gcongr
  exact rationalDotOperandBudget_mono hp hL

theorem rationalKernelMatrixBudget_mono {p p' q q' L L' : ℕ}
    (hp : p ≤ p') (hq : q ≤ q') (hL : L ≤ L') :
    rationalKernelMatrixBudget p q L ≤ rationalKernelMatrixBudget p' q' L' := by
  apply Nat.add_le_add
  · exact Nat.add_le_add (rationalRectTraversalBudget_mono hq hq (by omega)) (rationalRectMulBudget_mono hq hp hq hL)
  · apply rationalRectTraversalBudget_mono hq hq
    have hd := rationalDotOperandBudget_mono hp hL
    gcongr

theorem rationalGramSumScaledBits_mono {q q' L L' : ℕ} (hq : q ≤ q') (hL : L ≤ L') :
    rationalGramSumScaledBits q L ≤ rationalGramSumScaledBits q' L' := by
  have hd := rationalDotOperandBudget_mono hq hL
  unfold rationalGramSumScaledBits
  gcongr

theorem rationalGramSumBits_mono {p p' q q' L L' : ℕ}
    (hp : p ≤ p') (hq : q ≤ q') (hL : L ≤ L') :
    rationalGramSumBits p q L ≤ rationalGramSumBits p' q' L' := by
  have hd := rationalDotOperandBudget_mono hp hL
  have hs := rationalGramSumScaledBits_mono hq hL
  unfold rationalGramSumBits
  gcongr

theorem rationalGramSumBudget_mono {p p' q q' L L' : ℕ}
    (hp : p ≤ p') (hq : q ≤ q') (hL : L ≤ L') :
    rationalGramSumBudget p q L ≤ rationalGramSumBudget p' q' L' := by
  have hd := rationalDotOperandBudget_mono hp hL
  have hdq := rationalDotOperandBudget_mono hq hL
  have hs := rationalGramSumScaledBits_mono hq hL
  apply Nat.add_le_add
  · apply Nat.add_le_add
    · exact Nat.add_le_add (rationalRowGramBudget_mono hq hp hL) (rationalRowGramBudget_mono hq hq hL)
    · apply rationalRectTraversalBudget_mono hq hq
      gcongr
  · apply rationalRectTraversalBudget_mono hq hq
    gcongr

theorem gramFilledCovarianceBudget_mono {p p' q q' L L' : ℕ}
    (hp : p ≤ p') (hq : q ≤ q') (hL : L ≤ L') :
    gramFilledCovarianceBudget p q L ≤ gramFilledCovarianceBudget p' q' L' :=
  Nat.add_le_add (rationalKernelMatrixBudget_mono hp hq hL)
    (rationalGramSumBudget_mono hp hq (Nat.add_le_add hL (rationalKernelMatrixBits_mono hp hL)))

theorem gramFilledCovarianceBits_mono {p p' q q' L L' : ℕ}
    (hp : p ≤ p') (hq : q ≤ q') (hL : L ≤ L') :
    gramFilledCovarianceBits p q L ≤ gramFilledCovarianceBits p' q' L' :=
  rationalGramSumBits_mono hp hq (Nat.add_le_add hL (rationalKernelMatrixBits_mono hp hL))

theorem covarianceFromInverseInputBits_mono {p p' L L' : ℕ} (hp : p ≤ p') (hL : L ≤ L') :
    covarianceFromInverseInputBits p L ≤ covarianceFromInverseInputBits p' L' := by
  have hd := rationalDotOperandBudget_mono hp hL
  have ht := rationalTraceMeanOperandBudget_mono hp hL
  unfold covarianceFromInverseInputBits
  gcongr

theorem covarianceFromInverseScaleBits_mono {p p' q q' L L' : ℕ}
    (hp : p ≤ p') (hq : q ≤ q') (hL : L ≤ L') :
    covarianceFromInverseScaleBits p q L ≤ covarianceFromInverseScaleBits p' q' L' :=
  Nat.add_le_add (by gcongr) (gramFilledCovarianceBits_mono hp hq (covarianceFromInverseInputBits_mono hp hL))

theorem covarianceFromInverseBits_mono {p p' q q' L L' : ℕ}
    (hp : p ≤ p') (hq : q ≤ q') (hL : L ≤ L') :
    covarianceFromInverseBits p q L ≤ covarianceFromInverseBits p' q' L' := by
  unfold covarianceFromInverseBits
  have h := covarianceFromInverseScaleBits_mono hp hq hL
  gcongr

theorem covarianceFromInverseBudget_mono {p p' q q' L L' : ℕ}
    (hp : p ≤ p') (hq : q ≤ q') (hL : L ≤ L') :
    covarianceFromInverseBudget p q L ≤ covarianceFromInverseBudget p' q' L' := by
  apply Nat.add_le_add
  · apply Nat.add_le_add
    · apply Nat.add_le_add
      · exact Nat.add_le_add (Nat.add_le_add (rationalRectTraversalBudget_mono hq hp (by omega))
          (rationalRectMulBudget_mono hq hp hp hL)) (rationalTraceMeanBudget_mono hp hL)
      · exact gramFilledCovarianceBudget_mono hp hq (covarianceFromInverseInputBits_mono hp hL)
    · gcongr
  · apply rationalRectTraversalBudget_mono hq hq
    have h := covarianceFromInverseScaleBits_mono hp hq hL
    exact Nat.pow_le_pow_left (Nat.add_le_add_right (Nat.mul_le_mul_left 2 h) 1) 3

theorem rationalCovarianceInverseBudget_mono {p p' q q' L L' t t' : ℕ}
    (hp : p ≤ p') (hq : q ≤ q') (hL : L ≤ L') (ht : t ≤ t') :
    rationalCovarianceInverseBudget p q L t ≤ rationalCovarianceInverseBudget p' q' L' t' := by
  apply rationalSpectralBudget_mono hp _ ht
  have hd := rationalDotOperandBudget_mono hq hL
  gcongr

theorem rationalShapingCovarianceBudget_mono {p p' q q' L L' t t' : ℕ}
    (hp : p ≤ p') (hq : q ≤ q') (hL : L ≤ L') (ht : t ≤ t') :
    rationalShapingCovarianceBudget p q L t ≤ rationalShapingCovarianceBudget p' q' L' t' := by
  have hB := rationalCovarianceInverseBudget_mono hp hq hL ht
  exact Nat.add_le_add (Nat.add_le_add (rationalRowGramBudget_mono hp hq hL) hB)
    (covarianceFromInverseBudget_mono hp hq (Nat.add_le_add hL hB))

theorem rationalShapingCovarianceBits_mono {p p' q q' L L' t t' : ℕ}
    (hp : p ≤ p') (hq : q ≤ q') (hL : L ≤ L') (ht : t ≤ t') :
    rationalShapingCovarianceBits p q L t ≤ rationalShapingCovarianceBits p' q' L' t' :=
  covarianceFromInverseBits_mono hp hq (Nat.add_le_add hL (rationalCovarianceInverseBudget_mono hp hq hL ht))

end GeometricGaussianLHL

end RationalCovarianceBounds

section RationalBlockCost

/-!
## Stored repeated metric blocks

Each entry charges two quotient/remainder pairs, the block-index comparison,
and copying its rational value. Stored vector traversal is charged separately.
-/

namespace GeometricGaussianLHL

def costedRationalBlockEntry {d n : ℕ} (D : RationalMatrixData d) (i j : Fin (n * d)) : Costed ℚ :=
  let a : Fin n × Fin d := finProdFinEquiv.symm i
  let b : Fin n × Fin d := finProdFinEquiv.symm j
  let x := if a.1 = b.1 then rationalMatrixOfData D a.2 b.2 else 0
  ⟨x, 2 * (i.val.size + d.size + 1) ^ 2 + 2 * (j.val.size + d.size + 1) ^ 2 +
    (a.1.val.size + b.1.val.size + 1) + (rationalMagnitudeBits x + 1)⟩

theorem costedRationalBlockEntry_size {d n : ℕ} (D : RationalMatrixData d) (L : ℕ)
    (hD : ∀ i j, rationalMagnitudeBits (rationalMatrixOfData D i j) ≤ L) (i j : Fin (n * d)) :
    rationalMagnitudeBits (costedRationalBlockEntry D i j).value ≤ L + 2 := by
  change rationalMagnitudeBits (if (finProdFinEquiv.symm i).1 = (finProdFinEquiv.symm j).1 then
    rationalMatrixOfData D (finProdFinEquiv.symm i).2 (finProdFinEquiv.symm j).2 else 0) ≤ _
  split_ifs
  · exact (hD _ _).trans (by omega)
  · have hz : rationalMagnitudeBits (0 : ℚ) = 2 := by decide
    omega

def rationalBlockEntryBudget (n d L : ℕ) : ℕ := 4 * (2 * (n * d + d) + 1) ^ 2 + 2 * n + L + 4
def rationalBlockBudget (n d L : ℕ) : ℕ := rationalRectTraversalBudget (n * d) (n * d) (rationalBlockEntryBudget n d L)

theorem costedRationalBlockEntry_steps_le {d n : ℕ} (D : RationalMatrixData d) (L : ℕ)
    (hD : ∀ i j, rationalMagnitudeBits (rationalMatrixOfData D i j) ≤ L) (i j : Fin (n * d)) :
    (costedRationalBlockEntry D i j).steps ≤ rationalBlockEntryBudget n d L := by
  have size_le (k : ℕ) : k.size ≤ k := Nat.size_le.mpr Nat.lt_two_pow_self
  have hi : i.val.size ≤ n * d := (size_le i.val).trans i.isLt.le
  have hj : j.val.size ≤ n * d := (size_le j.val).trans j.isLt.le
  have hd := size_le d
  have ha : (finProdFinEquiv.symm i).1.val.size ≤ n :=
    (size_le _).trans (finProdFinEquiv.symm i).1.isLt.le
  have hb : (finProdFinEquiv.symm j).1.val.size ≤ n :=
    (size_le _).trans (finProdFinEquiv.symm j).1.isLt.le
  have hpi : (i.val.size + d.size + 1) ^ 2 ≤ (2 * (n * d + d) + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hpj : (j.val.size + d.size + 1) ^ 2 ≤ (2 * (n * d + d) + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hx := costedRationalBlockEntry_size D L hD i j
  dsimp only [costedRationalBlockEntry] at hx ⊢
  unfold rationalBlockEntryBudget
  omega

def costedRationalBlock {d : ℕ} (n : ℕ) (D : RationalMatrixData d) : Costed (RationalMatrixData (n * d)) :=
  costedRationalRectOfFn (costedRationalBlockEntry D)

theorem costedRationalBlock_data {d : ℕ} (n : ℕ) (D : RationalMatrixData d) :
    (costedRationalBlock n D).value = rationalMatrixData (repeatedEuclideanMatrix n (rationalMatrixOfData D)) := by
  rw [costedRationalBlock, costedRationalRectOfFn_data]
  rfl

theorem costedRationalBlock_steps_le {d : ℕ} (n L : ℕ) (D : RationalMatrixData d)
    (hD : ∀ i j, rationalMagnitudeBits (rationalMatrixOfData D i j) ≤ L) :
    (costedRationalBlock n D).steps ≤ rationalBlockBudget n d L :=
  costedRationalRectOfFn_steps_le _ _ (costedRationalBlockEntry_steps_le D L hD)

theorem costedRationalBlock_size {d : ℕ} (n L : ℕ) (D : RationalMatrixData d)
    (hD : ∀ i j, rationalMagnitudeBits (rationalMatrixOfData D i j) ≤ L) (i j : Fin (n * d)) :
    rationalMagnitudeBits (rationalMatrixOfData (costedRationalBlock n D).value i j) ≤ L + 2 := by
  rw [costedRationalBlock_data, rationalMatrixOfData_data]
  exact costedRationalBlockEntry_size D L hD i j

theorem polyBound_rationalBlockEntryBudget {n d L : ℕ → ℕ}
    (hn : PolynomialCostBound n) (hd : PolynomialCostBound d) (hL : PolynomialCostBound L) :
    PolynomialCostBound (fun x => rationalBlockEntryBudget (n x) (d x) (L x)) :=
  ((((PolynomialCostBound.const 4).mul ((((PolynomialCostBound.const 2).mul
    ((hn.mul hd).add hd)).add (PolynomialCostBound.const 1)).pow 2)).add ((PolynomialCostBound.const 2).mul hn)).add hL).add (PolynomialCostBound.const 4)

theorem polyBound_rationalBlockBudget {n d L : ℕ → ℕ}
    (hn : PolynomialCostBound n) (hd : PolynomialCostBound d) (hL : PolynomialCostBound L) :
    PolynomialCostBound (fun x => rationalBlockBudget (n x) (d x) (L x)) :=
  polyBound_rationalRectTraversalBudget (hn.mul hd) (hn.mul hd) (polyBound_rationalBlockEntryBudget hn hd hL)

theorem rationalBlockBudget_mono {n n' d d' L L' : ℕ} (hn : n ≤ n') (hd : d ≤ d') (hL : L ≤ L') :
    rationalBlockBudget n d L ≤ rationalBlockBudget n' d' L' := by
  apply rationalRectTraversalBudget_mono (Nat.mul_le_mul hn hd) (Nat.mul_le_mul hn hd)
  unfold rationalBlockEntryBudget
  gcongr

end GeometricGaussianLHL

end RationalBlockCost

section RationalShapingNumericalCost

/-!
## Composing the inverse, covariance and square-root executions

Positive definiteness of the computed covariance supplies the validity needed
by the square-root algorithm. Its input sizes are derived from the preceding
execution, rather than assumed separately.
-/

open scoped MatrixOrder Matrix.Norms.L2Operator
namespace GeometricGaussianLHL

def costedRationalShapingNumerical {p q : ℕ} (z t : ℕ) (X : RationalRectData p q) (w : ℚ) : Costed (RationalMatrixData q) :=
  (costedRationalShapingCovariance z X w).bind (costedRationalSpectralApprox false t)

theorem costedRationalShapingNumerical_data {p q : ℕ} (z t : ℕ) (X : RationalRectData p q) (w : ℚ) :
    (costedRationalShapingNumerical z t X w).value = rationalMatrixData
      (rationalSqrtApprox t (rationalShapingApproxCovariance z (rationalRectMatrixOfData X) w)) := by
  rw [costedRationalShapingNumerical, Costed.bind_value, costedRationalShapingCovariance_data]
  change (costedRationalSpectralApprox false t (rationalMatrixData
    (rationalShapingApproxCovariance z (rationalRectMatrixOfData X) w))).value = _
  rw [costedRationalSpectralApprox_data, rationalMatrixOfData_data, ite_eq_right (by decide)]

def rationalShapingRootBudget (p q L z t : ℕ) : ℕ :=
  rationalSpectralBudget q (q * q * rationalShapingCovarianceBits p q L z) t
def rationalShapingNumericalBudget (p q L z t : ℕ) : ℕ :=
  rationalShapingCovarianceBudget p q L z + rationalShapingRootBudget p q L z t

theorem costedRationalShapingNumerical_bounds {p q : ℕ} (z t : ℕ) (X : RationalRectData p q) (w : ℚ) (L : ℕ)
    (hX : ∀ i j, rationalMagnitudeBits (rationalRectMatrixOfData X i j) ≤ L)
    (hwL : rationalMagnitudeBits w ≤ L) (hp : 0 < p)
    (hA : IsUnit (rationalRectMatrixOfData X * (rationalRectMatrixOfData X).transpose).det) (hw : w ≠ 0) :
    (costedRationalShapingNumerical z t X w).steps ≤ rationalShapingNumericalBudget p q L z t ∧
      (encodeRationalMatrixData (costedRationalShapingNumerical z t X w).value).length ≤ rationalShapingRootBudget p q L z t := by
  let C := costedRationalShapingCovariance z X w
  let R := costedRationalSpectralApprox false t C.value
  have hC := costedRationalShapingCovariance_bounds z X w L hX hwL hA
  have hpos : ((rationalMatrixOfData C.value).map (fun r : ℚ => (r : ℝ))).PosDef := by
    change ((rationalRectMatrixOfData (costedRationalShapingCovariance z X w).value).map (Rat.castHom ℝ)).PosDef
    rw [costedRationalShapingCovariance_data, rationalRectMatrixOfData_data]
    exact rationalShapingApproxCovariance_real_posDef z _ w hp hA hw
  have hsize : rationalMatrixMagnitudeBits (rationalMatrixOfData C.value) ≤ q * q * rationalShapingCovarianceBits p q L z := by
    calc
      _ ≤ ∑ i : Fin q, ∑ j : Fin q, rationalShapingCovarianceBits p q L z :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hC.2 i j))
      _ = _ := by simp; ring
  have hR : R.steps ≤ rationalShapingRootBudget p q L z t :=
    (costedRationalSpectralApprox_steps_le false t C.value hpos).trans (rationalSpectralBudget_mono le_rfl hsize le_rfl)
  constructor
  · rw [costedRationalShapingNumerical, Costed.bind_steps]
    exact Nat.add_le_add hC.1 hR
  · rw [costedRationalShapingNumerical, Costed.bind_value]
    exact (costedRationalSpectralApprox_length_le_steps false t C.value).trans hR

theorem polyBound_rationalShapingRootBudget {p q L z t : ℕ → ℕ}
    (hp : PolynomialCostBound p) (hq : PolynomialCostBound q) (hL : PolynomialCostBound L)
    (hz : PolynomialCostBound z) (ht : PolynomialCostBound t) :
    PolynomialCostBound (fun x => rationalShapingRootBudget (p x) (q x) (L x) (z x) (t x)) :=
  polyBound_rationalSpectralBudget hq ((hq.mul hq).mul (polyBound_rationalShapingCovarianceBits hp hq hL hz)) ht

theorem polyBound_rationalShapingNumericalBudget {p q L z t : ℕ → ℕ}
    (hp : PolynomialCostBound p) (hq : PolynomialCostBound q) (hL : PolynomialCostBound L)
    (hz : PolynomialCostBound z) (ht : PolynomialCostBound t) :
    PolynomialCostBound (fun x => rationalShapingNumericalBudget (p x) (q x) (L x) (z x) (t x)) :=
  (polyBound_rationalShapingCovarianceBudget hp hq hL hz).add (polyBound_rationalShapingRootBudget hp hq hL hz ht)

theorem rationalShapingRootBudget_mono {p p' q q' L L' z z' t t' : ℕ}
    (hp : p ≤ p') (hq : q ≤ q') (hL : L ≤ L') (hz : z ≤ z') (ht : t ≤ t') :
    rationalShapingRootBudget p q L z t ≤ rationalShapingRootBudget p' q' L' z' t' := by
  apply rationalSpectralBudget_mono hq _ ht
  have h := rationalShapingCovarianceBits_mono hp hq hL hz
  gcongr

theorem rationalShapingNumericalBudget_mono {p p' q q' L L' z z' t t' : ℕ}
    (hp : p ≤ p') (hq : q ≤ q') (hL : L ≤ L') (hz : z ≤ z') (ht : t ≤ t') :
    rationalShapingNumericalBudget p q L z t ≤ rationalShapingNumericalBudget p' q' L' z' t' :=
  Nat.add_le_add (rationalShapingCovarianceBudget_mono hp hq hL hz) (rationalShapingRootBudget_mono hp hq hL hz ht)

end GeometricGaussianLHL

end RationalShapingNumericalCost

section RationalShapingOutputCost

/-!
## Stored positive-shaping output and its serialization cost

Transpose averaging and the dyadic identity shift produce the exact output of
the numerical specification. Both stored intermediate and final serialization
costs are included.
-/

namespace GeometricGaussianLHL

def costedRationalShapingFinish {n : ℕ} (e : ℕ) (D : RationalMatrixData n) : Costed (RationalMatrixData n) :=
  (costedRationalSymmetrize D).bind fun S =>
    (costedRationalIdentity n).bind fun I =>
      (costedRationalDyadicOutput true e I).bind fun K =>
        (costedRationalRectAdd S K).bind fun H => Costed.charge (encodeRationalMatrixData H).length H

theorem costedRationalShapingFinish_data {n : ℕ} (e : ℕ) (D : RationalMatrixData n) :
    (costedRationalShapingFinish e D).value = rationalMatrixData
      ((1 / 2 : ℚ) • (rationalMatrixOfData D + (rationalMatrixOfData D).transpose) + (1 / (2 : ℚ) ^ e) • 1) := by
  rw [costedRationalShapingFinish, Costed.bind_value, costedRationalSymmetrize_data,
    Costed.bind_value, costedRationalIdentity_data, Costed.bind_value, costedRationalDyadicOutput_data,
    ite_eq_left rfl, Costed.bind_value]
  dsimp only [Costed.charge]
  rw [costedRationalRectAdd_data]
  change rationalMatrixData (rationalMatrixOfData (rationalMatrixData _) +
    rationalMatrixOfData (rationalMatrixData ((1 / (2 : ℚ) ^ e) • rationalMatrixOfData (rationalMatrixData 1)))) = _
  rw [rationalMatrixOfData_data, rationalMatrixOfData_data, rationalMatrixOfData_data]

def rationalShapingFinishOperandBudget (n e L : ℕ) : ℕ := 15 * L + 17 + rationalDyadicOutputBudget n e 3
def rationalShapingFinishBudget (n e L : ℕ) : ℕ :=
  rationalSymmetrizeBudget n L + rationalRectTraversalBudget n n (n + 2) + rationalDyadicOutputBudget n e 3 +
    rationalRectTraversalBudget n n ((2 * rationalShapingFinishOperandBudget n e L + 1) ^ 3) +
    rationalMatrixEncodingBudget n (5 * rationalShapingFinishOperandBudget n e L + 4)

theorem costedRationalShapingFinish_steps_le {n : ℕ} (e L : ℕ) (D : RationalMatrixData n)
    (hD : ∀ i j, rationalMagnitudeBits (rationalMatrixOfData D i j) ≤ L) :
    (costedRationalShapingFinish e D).steps ≤ rationalShapingFinishBudget n e L := by
  let S := costedRationalSymmetrize D
  let I := costedRationalIdentity n
  let K := costedRationalDyadicOutput true e I.value
  let H := costedRationalRectAdd S.value K.value
  let U := rationalShapingFinishOperandBudget n e L
  have hSs := costedRationalSymmetrize_steps_le D L hD
  have hIs := costedRationalIdentity_steps_le n
  have hKs := costedRationalDyadicOutput_steps_le true e 3 I.value (costedRationalIdentity_size n)
  have hKl := (costedRationalDyadicOutput_length_le_steps true e I.value).trans hKs
  have hS : ∀ i j, rationalMagnitudeBits (rationalMatrixOfData S.value i j) ≤ U :=
    fun i j => (costedRationalSymmetrize_size D L hD i j).trans (by dsimp [U, rationalShapingFinishOperandBudget]; omega)
  have hK : ∀ i j, rationalMagnitudeBits (rationalMatrixOfData K.value i j) ≤ U :=
    fun i j => ((rationalMatrixEntryBits_le_encoded K.value i j).trans hKl).trans
      (by dsimp [U, rationalShapingFinishOperandBudget]; omega)
  have hHs := costedRationalRectAdd_steps_le S.value K.value U hS hK
  have hHl := rationalMatrixEncoded_length_le H.value (5 * U + 4) (costedRationalRectAdd_size S.value K.value U hS hK)
  change S.steps ≤ _ at hSs
  change I.steps ≤ _ at hIs
  change K.steps ≤ _ at hKs
  change H.steps ≤ _ at hHs
  rw [costedRationalShapingFinish, Costed.bind_steps, Costed.bind_steps, Costed.bind_steps, Costed.bind_steps]
  change S.steps + (I.steps + (K.steps + (H.steps + (encodeRationalMatrixData H.value).length))) ≤ _
  change _ ≤ rationalSymmetrizeBudget n L + rationalRectTraversalBudget n n (n + 2) + rationalDyadicOutputBudget n e 3 +
    rationalRectTraversalBudget n n ((2 * U + 1) ^ 3) + rationalMatrixEncodingBudget n (5 * U + 4)
  omega

theorem costedRationalShapingFinish_length_le_steps {n : ℕ} (e : ℕ) (D : RationalMatrixData n) :
    (encodeRationalMatrixData (costedRationalShapingFinish e D).value).length ≤ (costedRationalShapingFinish e D).steps := by
  rw [costedRationalShapingFinish, Costed.bind_value, Costed.bind_steps, Costed.bind_value, Costed.bind_steps,
    Costed.bind_value, Costed.bind_steps, Costed.bind_value, Costed.bind_steps]
  dsimp only [Costed.charge]
  omega

theorem polyBound_rationalShapingFinishOperandBudget {n e L : ℕ → ℕ}
    (hn : PolynomialCostBound n) (he : PolynomialCostBound e) (hL : PolynomialCostBound L) :
    PolynomialCostBound (fun x => rationalShapingFinishOperandBudget (n x) (e x) (L x)) :=
  (((PolynomialCostBound.const 15).mul hL).add (PolynomialCostBound.const 17)).add
    (polyBound_rationalDyadicOutputBudget hn he (PolynomialCostBound.const 3))

theorem polyBound_rationalShapingFinishBudget {n e L : ℕ → ℕ}
    (hn : PolynomialCostBound n) (he : PolynomialCostBound e) (hL : PolynomialCostBound L) :
    PolynomialCostBound (fun x => rationalShapingFinishBudget (n x) (e x) (L x)) := by
  have hU := polyBound_rationalShapingFinishOperandBudget hn he hL
  exact ((((polyBound_rationalSymmetrizeBudget hn hL).add
    (polyBound_rationalRectTraversalBudget hn hn (hn.add (PolynomialCostBound.const 2)))).add
      (polyBound_rationalDyadicOutputBudget hn he (PolynomialCostBound.const 3))).add
        (polyBound_rationalRectTraversalBudget hn hn ((((PolynomialCostBound.const 2).mul hU).add (PolynomialCostBound.const 1)).pow 3))).add
          (polyBound_rationalMatrixEncodingBudget hn (((PolynomialCostBound.const 5).mul hU).add (PolynomialCostBound.const 4)))

theorem rationalShapingFinishBudget_mono {n n' e e' L L' : ℕ}
    (hn : n ≤ n') (he : e ≤ e') (hL : L ≤ L') :
    rationalShapingFinishBudget n e L ≤ rationalShapingFinishBudget n' e' L' := by
  have hK := rationalDyadicOutputBudget_mono hn he (show 3 ≤ 3 by omega)
  have hU : rationalShapingFinishOperandBudget n e L ≤ rationalShapingFinishOperandBudget n' e' L' := by
    unfold rationalShapingFinishOperandBudget
    gcongr
  apply Nat.add_le_add
  · apply Nat.add_le_add
    · apply Nat.add_le_add
      · apply Nat.add_le_add
        · unfold rationalSymmetrizeBudget integerMatrixTraversalBudget
          gcongr
        · exact rationalRectTraversalBudget_mono hn hn (by omega)
      · exact hK
    · apply rationalRectTraversalBudget_mono hn hn
      gcongr
  · unfold rationalMatrixEncodingBudget
    gcongr

end GeometricGaussianLHL

end RationalShapingOutputCost

section RationalMetricNormalizationCost

/-!
## Stored metric normalization with complete arithmetic costs

The computed square root and inverse square root feed repeated blocks and two
stored rectangular products. Output serialization and all intermediate operand
sizes are included in the composed bound.
-/

open scoped MatrixOrder Matrix.Norms.L2Operator
namespace GeometricGaussianLHL

def rationalRectEncodingBudget (p q L : ℕ) : ℕ := 2 * p + 2 * q + 2 + 2 * (p * q * L) + p * q

theorem rationalRectEncoded_length_le {p q : ℕ} (D : RationalRectData p q) (L : ℕ)
    (hD : ∀ i j, rationalMagnitudeBits (rationalRectMatrixOfData D i j) ≤ L) :
    (encodeRationalRectData D).length ≤ rationalRectEncodingBudget p q L := by
  have hs : rationalRectMagnitudeBits D ≤ p * q * L := by
    calc
      _ ≤ ∑ i : Fin p, ∑ j : Fin q, L := Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hD i j))
      _ = _ := by simp; ring
  have hp : p.size ≤ p := Nat.size_le.mpr Nat.lt_two_pow_self
  have hq : q.size ≤ q := Nat.size_le.mpr Nat.lt_two_pow_self
  rw [encodeRationalRectData_length]
  unfold rationalRectEncodingBudget
  omega

theorem rationalRect_entry_bits_le_encoded {p q : ℕ} (D : RationalRectData p q) (i : Fin p) (j : Fin q) :
    rationalMagnitudeBits (rationalRectMatrixOfData D i j) ≤ (encodeRationalRectData D).length := by
  have h := rationalRect_entry_bits_le D i j
  rw [encodeRationalRectData_length]
  omega

def costedRationalMetricSandwich {d r m : ℕ} (C : RationalRectData (r * d) (m * d))
    (R U : RationalMatrixData d) : Costed (RationalRectData (r * d) (m * d)) :=
  (costedRationalBlock r R).bind fun P =>
    (costedRationalBlock m U).bind fun Q =>
      (costedRationalRectMul P C).bind fun H =>
        (costedRationalRectMul H Q).bind fun D => Costed.charge (encodeRationalRectData D).length D

theorem costedRationalMetricSandwich_data {d r m : ℕ} (C : RationalRectData (r * d) (m * d)) (R U : RationalMatrixData d) :
    (costedRationalMetricSandwich C R U).value = rationalRectMatrixData
      (repeatedEuclideanMatrix r (rationalMatrixOfData R) * rationalRectMatrixOfData C * repeatedEuclideanMatrix m (rationalMatrixOfData U)) := by
  rw [costedRationalMetricSandwich, Costed.bind_value, costedRationalBlock_data,
    Costed.bind_value, costedRationalBlock_data, Costed.bind_value, costedRationalRectMul_data,
    Costed.bind_value]
  dsimp only [Costed.charge]
  rw [costedRationalRectMul_data, rationalRectMatrixOfData_data]
  change rationalRectMatrixData (rationalMatrixOfData (rationalMatrixData _) * rationalRectMatrixOfData C *
    rationalMatrixOfData (rationalMatrixData _)) = _
  rw [rationalMatrixOfData_data, rationalMatrixOfData_data]

def rationalMetricSandwichOperandBudget (d r L : ℕ) : ℕ := rationalDotOperandBudget (r * d) (L + 2) + L + 2
def rationalMetricSandwichBudget (d r m L : ℕ) : ℕ :=
  let H := rationalMetricSandwichOperandBudget d r L
  rationalBlockBudget r d L + rationalBlockBudget m d L + rationalRectMulBudget (r * d) (r * d) (m * d) (L + 2) +
    rationalRectMulBudget (r * d) (m * d) (m * d) H + rationalRectEncodingBudget (r * d) (m * d) (rationalDotOperandBudget (m * d) H)

theorem costedRationalMetricSandwich_steps_le {d r m : ℕ} (C : RationalRectData (r * d) (m * d)) (R U : RationalMatrixData d) (L : ℕ)
    (hC : ∀ i j, rationalMagnitudeBits (rationalRectMatrixOfData C i j) ≤ L)
    (hR : ∀ i j, rationalMagnitudeBits (rationalMatrixOfData R i j) ≤ L)
    (hU : ∀ i j, rationalMagnitudeBits (rationalMatrixOfData U i j) ≤ L) :
    (costedRationalMetricSandwich C R U).steps ≤ rationalMetricSandwichBudget d r m L := by
  let P := costedRationalBlock r R
  let Q := costedRationalBlock m U
  let H := costedRationalRectMul P.value C
  let D := costedRationalRectMul H.value Q.value
  let B := rationalMetricSandwichOperandBudget d r L
  have hP := costedRationalBlock_size r L R hR
  have hQ := costedRationalBlock_size m L U hU
  have hC' : ∀ i j, rationalMagnitudeBits (rationalRectMatrixOfData C i j) ≤ L + 2 := fun i j => (hC i j).trans (by omega)
  have hH : ∀ i j, rationalMagnitudeBits (rationalRectMatrixOfData H.value i j) ≤ B :=
    fun i j => (costedRationalRectMul_size P.value C (L + 2) hP hC' i j).trans (by dsimp [B, rationalMetricSandwichOperandBudget]; omega)
  have hQ' : ∀ i j, rationalMagnitudeBits (rationalMatrixOfData Q.value i j) ≤ B :=
    fun i j => (hQ i j).trans (by dsimp [B, rationalMetricSandwichOperandBudget]; omega)
  have hPs := costedRationalBlock_steps_le r L R hR
  have hQs := costedRationalBlock_steps_le m L U hU
  have hHs := costedRationalRectMul_steps_le P.value C (L + 2) hP hC'
  have hDs := costedRationalRectMul_steps_le H.value Q.value B hH hQ'
  have hDl := rationalRectEncoded_length_le D.value (rationalDotOperandBudget (m * d) B)
    (costedRationalRectMul_size H.value Q.value B hH hQ')
  change P.steps ≤ _ at hPs
  change Q.steps ≤ _ at hQs
  change H.steps ≤ _ at hHs
  change D.steps ≤ _ at hDs
  rw [costedRationalMetricSandwich, Costed.bind_steps, Costed.bind_steps, Costed.bind_steps, Costed.bind_steps]
  change P.steps + (Q.steps + (H.steps + (D.steps + (encodeRationalRectData D.value).length))) ≤ _
  change _ ≤ rationalBlockBudget r d L + rationalBlockBudget m d L + rationalRectMulBudget (r * d) (r * d) (m * d) (L + 2) +
    rationalRectMulBudget (r * d) (m * d) (m * d) B + rationalRectEncodingBudget (r * d) (m * d) (rationalDotOperandBudget (m * d) B)
  omega

theorem costedRationalMetricSandwich_length_le_steps {d r m : ℕ} (C : RationalRectData (r * d) (m * d)) (R U : RationalMatrixData d) :
    (encodeRationalRectData (costedRationalMetricSandwich C R U).value).length ≤ (costedRationalMetricSandwich C R U).steps := by
  rw [costedRationalMetricSandwich, Costed.bind_value, Costed.bind_steps, Costed.bind_value, Costed.bind_steps,
    Costed.bind_value, Costed.bind_steps, Costed.bind_value, Costed.bind_steps]
  dsimp only [Costed.charge]
  omega

def costedRationalMetricNormalization {d r m : ℕ} (t : ℕ) (G : RationalMatrixData d)
    (C : RationalRectData (r * d) (m * d)) : Costed (RationalRectData (r * d) (m * d)) :=
  (costedRationalSpectralApprox false t G).bind fun R =>
    (costedRationalInverseRoot t G).bind (costedRationalMetricSandwich C R)

theorem costedRationalMetricNormalization_data {d r m : ℕ} (t : ℕ) (G : RationalMatrixData d) (C : RationalRectData (r * d) (m * d)) :
    (costedRationalMetricNormalization t G C).value = rationalRectMatrixData
      (rationalMetricNormalizedApprox t (rationalMatrixOfData G) (rationalRectMatrixOfData C)) := by
  rw [costedRationalMetricNormalization, Costed.bind_value, costedRationalSpectralApprox_data, ite_eq_right (by decide),
    Costed.bind_value, costedRationalInverseRoot_data, costedRationalMetricSandwich_data,
    rationalMatrixOfData_data, rationalMatrixOfData_data]
  rfl

def rationalMetricNormalizationOperandBudget (d S L t : ℕ) : ℕ :=
  L + rationalSpectralBudget d S t + rationalInverseRootOutputBudget d S t
def rationalMetricNormalizationBudget (d r m S L t : ℕ) : ℕ :=
  rationalSpectralBudget d S t + rationalInverseRootBudget d S t +
    rationalMetricSandwichBudget d r m (rationalMetricNormalizationOperandBudget d S L t)

theorem costedRationalMetricNormalization_steps_le {d r m : ℕ} (t : ℕ) (G : RationalMatrixData d)
    (C : RationalRectData (r * d) (m * d)) (L : ℕ)
    (hG : ((rationalMatrixOfData G).map (fun q : ℚ => (q : ℝ))).PosDef)
    (hC : ∀ i j, rationalMagnitudeBits (rationalRectMatrixOfData C i j) ≤ L) :
    (costedRationalMetricNormalization t G C).steps ≤ rationalMetricNormalizationBudget d r m
      (rationalMatrixMagnitudeBits (rationalMatrixOfData G)) L t := by
  let R := costedRationalSpectralApprox false t G
  let U := costedRationalInverseRoot t G
  let S := rationalMatrixMagnitudeBits (rationalMatrixOfData G)
  let B := rationalMetricNormalizationOperandBudget d S L t
  have hR := costedRationalSpectralApprox_steps_le false t G hG
  have hRl := (costedRationalSpectralApprox_length_le_steps false t G).trans hR
  have hU := costedRationalInverseRoot_bounds t G hG
  have hB := costedRationalMetricSandwich_steps_le C R.value U.value B
    (fun i j => (hC i j).trans (by dsimp [B, rationalMetricNormalizationOperandBudget]; omega))
    (fun i j => ((rationalMatrixEntryBits_le_encoded R.value i j).trans hRl).trans
      (by dsimp [B, S, rationalMetricNormalizationOperandBudget]; omega))
    (fun i j => ((rationalMatrixEntryBits_le_encoded U.value i j).trans hU.2).trans
      (by dsimp [B, S, rationalMetricNormalizationOperandBudget]; omega))
  rw [costedRationalMetricNormalization, Costed.bind_steps, Costed.bind_steps]
  change R.steps + (U.steps + (costedRationalMetricSandwich C R.value U.value).steps) ≤ _
  exact (Nat.add_le_add hR (Nat.add_le_add hU.1 hB)).trans_eq (Nat.add_assoc _ _ _).symm

theorem costedRationalMetricNormalization_length_le_steps {d r m : ℕ} (t : ℕ) (G : RationalMatrixData d) (C : RationalRectData (r * d) (m * d)) :
    (encodeRationalRectData (costedRationalMetricNormalization t G C).value).length ≤ (costedRationalMetricNormalization t G C).steps := by
  let R := costedRationalSpectralApprox false t G
  let U := costedRationalInverseRoot t G
  have h := costedRationalMetricSandwich_length_le_steps C R.value U.value
  rw [costedRationalMetricNormalization, Costed.bind_value, Costed.bind_steps, Costed.bind_value, Costed.bind_steps]
  change (encodeRationalRectData (costedRationalMetricSandwich C R.value U.value).value).length ≤
    R.steps + (U.steps + (costedRationalMetricSandwich C R.value U.value).steps)
  omega

end GeometricGaussianLHL

end RationalMetricNormalizationCost

section RationalShapingCost

/-!
## Total arithmetic cost of the rational shaping algorithm

The complete stored execution computes its precisions, inverse, covariance,
square root and positive output. A Gram matrix is computed for the schedule and
again in the covariance routine; both computations are charged.
-/

open scoped MatrixOrder Matrix.Norms.L2Operator
namespace GeometricGaussianLHL

def costedRationalShapingApprox {p q : ℕ} (t : ℕ) (X : RationalRectData p q) (w : ℚ) : Costed (RationalMatrixData q) :=
  (costedRationalRowGram X).bind fun G =>
    (costedRationalShapingSchedule t G w).bind fun N =>
      (costedRationalShapingNumerical N.inversePrecision N.rootPrecision X w).bind
        (costedRationalShapingFinish N.shiftPrecision)

theorem costedRationalShapingApprox_data {p q : ℕ} (t : ℕ) (X : RationalRectData p q) (w : ℚ) :
    (costedRationalShapingApprox t X w).value = rationalMatrixData (rationalShapingApprox t (rationalRectMatrixOfData X) w) := by
  rw [costedRationalShapingApprox, Costed.bind_value, costedRationalRowGram_data]
  change ((costedRationalShapingSchedule t (rationalMatrixData
    (rationalRectMatrixOfData X * (rationalRectMatrixOfData X).transpose)) w).bind fun N =>
      (costedRationalShapingNumerical N.inversePrecision N.rootPrecision X w).bind
        (costedRationalShapingFinish N.shiftPrecision)).value = _
  rw [Costed.bind_value, costedRationalShapingSchedule_value, rationalMatrixOfData_data,
    Costed.bind_value, costedRationalShapingNumerical_data, costedRationalShapingFinish_data, rationalMatrixOfData_data]
  simp only [rationalShapingSchedule, rationalShapingApprox, rationalShapingRawApprox,
    rationalShapingPrecisionGuard, materializeMatrix_eq]

def rationalShapingPrecisionBudget (p q L t : ℕ) : ℕ :=
  let S := p * p * rationalDotOperandBudget q L
  2 * (t + 2) + (4 * (2 * (p + 2 * S)) + 2 * (p * (S + 2 * (p + 2 * S))) + 4 * L + 6)

def rationalShapingBudget (p q L t : ℕ) : ℕ :=
  let S := p * p * rationalDotOperandBudget q L
  let z := rationalShapingPrecisionBudget p q L t
  rationalRowGramBudget p q L + rationalShapingScheduleBudget p S L t +
    rationalShapingNumericalBudget p q L z (t + 2) +
    rationalShapingFinishBudget q (t + 1) (rationalShapingRootBudget p q L z (t + 2))

theorem costedRationalShapingApprox_steps_le {p q : ℕ} (t : ℕ) (X : RationalRectData p q) (w : ℚ) (L : ℕ)
    (hX : ∀ i j, rationalMagnitudeBits (rationalRectMatrixOfData X i j) ≤ L)
    (hwL : rationalMagnitudeBits w ≤ L) (hp : 0 < p)
    (hA : IsUnit (rationalRectMatrixOfData X * (rationalRectMatrixOfData X).transpose).det) (hw : w ≠ 0) :
    (costedRationalShapingApprox t X w).steps ≤ rationalShapingBudget p q L t := by
  let G := costedRationalRowGram X
  let N := costedRationalShapingSchedule t G.value w
  let M := costedRationalShapingNumerical N.value.inversePrecision N.value.rootPrecision X w
  let S := p * p * rationalDotOperandBudget q L
  let z := rationalShapingPrecisionBudget p q L t
  let R := rationalShapingRootBudget p q L z (t + 2)
  have hGsize : rationalMatrixMagnitudeBits (rationalMatrixOfData G.value) ≤ S := by
    calc
      _ ≤ ∑ i : Fin p, ∑ j : Fin p, rationalDotOperandBudget q L :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => costedRationalRowGram_size X L hX i j))
      _ = _ := by simp [S]; ring
  have hNv : N.value = rationalShapingSchedule t
      (rationalMatrixNormalizationExponent (rationalMatrixOfData G.value))
      (rationalMatrixConditionExponent (rationalMatrixOfData G.value)) (rationalMagnitudeBits w) :=
    costedRationalShapingSchedule_value t G.value w
  have hNz : N.value.inversePrecision ≤ z := by
    rw [hNv]
    change 2 * (t + 2) + (4 * (2 * (p + 2 * rationalMatrixMagnitudeBits (rationalMatrixOfData G.value))) +
      2 * (p * (rationalMatrixMagnitudeBits (rationalMatrixOfData G.value) + 2 * (p + 2 * rationalMatrixMagnitudeBits (rationalMatrixOfData G.value)))) +
      4 * rationalMagnitudeBits w + 6) ≤
        2 * (t + 2) + (4 * (2 * (p + 2 * S)) + 2 * (p * (S + 2 * (p + 2 * S))) + 4 * L + 6)
    gcongr
  have hNt : N.value.rootPrecision = t + 2 := by rw [hNv]; rfl
  have hNe : N.value.shiftPrecision = t + 1 := by rw [hNv]; rfl
  have hGs := costedRationalRowGram_steps_le X L hX
  have hNs := (costedRationalShapingSchedule_steps_le t G.value w).trans
    (rationalShapingScheduleBudget_mono le_rfl hGsize hwL le_rfl)
  have hM := costedRationalShapingNumerical_bounds N.value.inversePrecision N.value.rootPrecision X w L hX hwL hp hA hw
  have hMs := hM.1.trans (rationalShapingNumericalBudget_mono le_rfl le_rfl le_rfl hNz hNt.le)
  have hMl : (encodeRationalMatrixData M.value).length ≤ R := hM.2.trans
    (rationalShapingRootBudget_mono le_rfl le_rfl le_rfl hNz hNt.le)
  have hFs := (costedRationalShapingFinish_steps_le N.value.shiftPrecision R M.value
    (fun i j => (rationalMatrixEntryBits_le_encoded M.value i j).trans hMl)).trans
      (rationalShapingFinishBudget_mono le_rfl hNe.le le_rfl)
  change G.steps ≤ _ at hGs
  change N.steps ≤ _ at hNs
  change M.steps ≤ _ at hMs
  rw [costedRationalShapingApprox, Costed.bind_steps, Costed.bind_steps, Costed.bind_steps]
  change G.steps + (N.steps + (M.steps + (costedRationalShapingFinish N.value.shiftPrecision M.value).steps)) ≤ _
  change _ ≤ rationalRowGramBudget p q L + rationalShapingScheduleBudget p S L t +
    rationalShapingNumericalBudget p q L z (t + 2) + rationalShapingFinishBudget q (t + 1) R
  omega

theorem costedRationalShapingApprox_length_le_steps {p q : ℕ} (t : ℕ) (X : RationalRectData p q) (w : ℚ) :
    (encodeRationalMatrixData (costedRationalShapingApprox t X w).value).length ≤ (costedRationalShapingApprox t X w).steps := by
  let G := costedRationalRowGram X
  let N := costedRationalShapingSchedule t G.value w
  let M := costedRationalShapingNumerical N.value.inversePrecision N.value.rootPrecision X w
  have h := costedRationalShapingFinish_length_le_steps N.value.shiftPrecision M.value
  rw [costedRationalShapingApprox, Costed.bind_value, Costed.bind_steps,
    Costed.bind_value, Costed.bind_steps, Costed.bind_value, Costed.bind_steps]
  change (encodeRationalMatrixData (costedRationalShapingFinish N.value.shiftPrecision M.value).value).length ≤
    G.steps + (N.steps + (M.steps + (costedRationalShapingFinish N.value.shiftPrecision M.value).steps))
  omega

theorem polyBound_rationalShapingPrecisionBudget {p q L t : ℕ → ℕ}
    (hp : PolynomialCostBound p) (hq : PolynomialCostBound q) (hL : PolynomialCostBound L) (ht : PolynomialCostBound t) :
    PolynomialCostBound (fun x => rationalShapingPrecisionBudget (p x) (q x) (L x) (t x)) := by
  have hS := (hp.mul hp).mul (polyBound_rationalDotOperandBudget hq hL)
  have hE := (PolynomialCostBound.const 2).mul (hp.add ((PolynomialCostBound.const 2).mul hS))
  exact ((PolynomialCostBound.const 2).mul (ht.add (PolynomialCostBound.const 2))).add
    (((((PolynomialCostBound.const 4).mul hE).add ((PolynomialCostBound.const 2).mul (hp.mul (hS.add hE)))).add
      ((PolynomialCostBound.const 4).mul hL)).add (PolynomialCostBound.const 6))

theorem polyBound_rationalShapingBudget {p q L t : ℕ → ℕ}
    (hp : PolynomialCostBound p) (hq : PolynomialCostBound q) (hL : PolynomialCostBound L) (ht : PolynomialCostBound t) :
    PolynomialCostBound (fun x => rationalShapingBudget (p x) (q x) (L x) (t x)) := by
  have hS := (hp.mul hp).mul (polyBound_rationalDotOperandBudget hq hL)
  have hz := polyBound_rationalShapingPrecisionBudget hp hq hL ht
  have hu := ht.add (PolynomialCostBound.const 2)
  exact (((polyBound_rationalRowGramBudget hp hq hL).add (polyBound_rationalShapingScheduleBudget hp hS hL ht)).add
    (polyBound_rationalShapingNumericalBudget hp hq hL hz hu)).add
      (polyBound_rationalShapingFinishBudget hq (ht.add (PolynomialCostBound.const 1)) (polyBound_rationalShapingRootBudget hp hq hL hz hu))

theorem rationalShapingPrecisionBudget_mono {p p' q q' L L' t t' : ℕ}
    (hp : p ≤ p') (hq : q ≤ q') (hL : L ≤ L') (ht : t ≤ t') :
    rationalShapingPrecisionBudget p q L t ≤ rationalShapingPrecisionBudget p' q' L' t' := by
  have hD := rationalDotOperandBudget_mono hq hL
  unfold rationalShapingPrecisionBudget
  dsimp only
  gcongr

theorem rationalShapingBudget_mono {p p' q q' L L' t t' : ℕ}
    (hp : p ≤ p') (hq : q ≤ q') (hL : L ≤ L') (ht : t ≤ t') :
    rationalShapingBudget p q L t ≤ rationalShapingBudget p' q' L' t' := by
  have hS : p * p * rationalDotOperandBudget q L ≤ p' * p' * rationalDotOperandBudget q' L' := by
    have hD := rationalDotOperandBudget_mono hq hL
    gcongr
  have hz := rationalShapingPrecisionBudget_mono hp hq hL ht
  exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (rationalRowGramBudget_mono hp hq hL)
    (rationalShapingScheduleBudget_mono hp hS hL ht))
      (rationalShapingNumericalBudget_mono hp hq hL hz (by omega)))
        (rationalShapingFinishBudget_mono hq (by omega) (rationalShapingRootBudget_mono hp hq hL hz (by omega)))

end GeometricGaussianLHL

end RationalShapingCost

section RationalShapingWidths

/-!
## Exact widths and numerical approximation of rational spherical shaping

The trace-average construction satisfies all three analytic identities in
the paper’s Gaussian-shaping remark. Its positive square root is the target of the computable rational
approximation. These results do not claim the full bit-complexity theorem.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped MatrixOrder Matrix.Norms.L2Operator

namespace GeometricGaussianLHL

theorem rationalShapingCovarianceMatrix_real_formula {p q : ℕ}
    (A : Matrix (Fin p) (Fin q) ℚ) (w : ℚ) :
    (rationalShapingCovarianceMatrix A w).map (Rat.castHom ℝ) = (w : ℝ) ^ 2 •
      ((rationalRightInverseMatrix A).map (Rat.castHom ℝ) *
        ((rationalRightInverseMatrix A).map (Rat.castHom ℝ)).transpose +
        (rationalShapingKernelFill A : ℝ) • (rationalKernelProjectionMatrix A).map (Rat.castHom ℝ)) := by
  have hm : (rationalRightInverseMatrix A * (rationalRightInverseMatrix A).transpose).map (Rat.castHom ℝ) =
      (rationalRightInverseMatrix A).map (Rat.castHom ℝ) *
        ((rationalRightInverseMatrix A).map (Rat.castHom ℝ)).transpose := Matrix.map_mul
  rw [← hm]
  ext i j
  simp [rationalShapingCovarianceMatrix, Matrix.map_apply, Matrix.smul_apply, Matrix.add_apply, mul_add]

theorem rationalShapingCovarianceMatrix_operator {p q : ℕ}
    (A : Matrix (Fin p) (Fin q) ℚ) (w : ℚ) (hA : IsUnit (A * A.transpose).det) :
    (Matrix.toEuclideanLin ((rationalShapingCovarianceMatrix A w).map (Rat.castHom ℝ))).toContinuousLinearMap =
      kernelFilledCovariance (Matrix.toEuclideanLin (A.map (Rat.castHom ℝ))).toContinuousLinearMap
        (rationalMatrix_real_surjective A hA) (w : ℝ) (rationalShapingKernelFill A : ℝ) := by
  have hp := rationalKernelProjectionMatrix_operator A hA
  change (Matrix.toEuclideanLin ((rationalKernelProjectionMatrix A).map (Rat.castHom ℝ))).toContinuousLinearMap =
    (Matrix.toEuclideanLin (A.map (Rat.castHom ℝ))).toContinuousLinearMap.toLinearMap.ker.starProjection at hp
  rw [rationalShapingCovarianceMatrix_real_formula, kernelFilledCovariance,
    ← rationalRightInverseMatrix_minimumNorm A hA, ← hp]
  ext x : 1
  simp only [map_smul, map_add]
  change (w : ℝ) ^ 2 • (Matrix.toEuclideanLin
      ((rationalRightInverseMatrix A).map (Rat.castHom ℝ) *
        ((rationalRightInverseMatrix A).map (Rat.castHom ℝ)).transpose) x +
      (rationalShapingKernelFill A : ℝ) •
        Matrix.toEuclideanLin ((rationalKernelProjectionMatrix A).map (Rat.castHom ℝ)) x) = _
  congr 2
  change Matrix.toLpLin 2 2
    ((rationalRightInverseMatrix A).map (Rat.castHom ℝ) *
      ((rationalRightInverseMatrix A).map (Rat.castHom ℝ)).conjTranspose) x = _
  rw [Matrix.toLpLin_mul_same]
  change Matrix.toEuclideanLin ((rationalRightInverseMatrix A).map (Rat.castHom ℝ))
    (Matrix.toEuclideanLin ((rationalRightInverseMatrix A).map (Rat.castHom ℝ)).conjTranspose x) = _
  rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  rfl

def rationalShapingShape {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℚ) (w : ℚ)
    (hp : 0 < p) (hA : IsUnit (A * A.transpose).det) (hw : 0 < w) : Euclidean q ≃L[ℝ] Euclidean q :=
  positiveSquareRootShape ((rationalShapingCovarianceMatrix A w).map (Rat.castHom ℝ))
    (rationalShapingCovarianceMatrix_real_posDef A w hp hA hw.ne')

theorem rationalShapingShape_matrix {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℚ) (w : ℚ)
    (hp : 0 < p) (hA : IsUnit (A * A.transpose).det) (hw : 0 < w) :
    Matrix.toEuclideanLin.symm (rationalShapingShape A w hp hA hw).toLinearMap =
      rationalShapingSquareRootMatrix A w := positiveSquareRootShape_matrix _ _

theorem rationalShapingShape_covariance {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℚ) (w : ℚ)
    (hp : 0 < p) (hA : IsUnit (A * A.transpose).det) (hw : 0 < w) :
    shapeCovariance (rationalShapingShape A w hp hA hw) =
      kernelFilledCovariance (Matrix.toEuclideanLin (A.map (Rat.castHom ℝ))).toContinuousLinearMap
        (rationalMatrix_real_surjective A hA) (w : ℝ) (rationalShapingKernelFill A : ℝ) := by
  rw [rationalShapingShape, positiveSquareRootShape_covariance, rationalShapingCovarianceMatrix_operator A w hA]

theorem rationalShapingShape_norm_sq {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℚ) (w : ℚ)
    (hp : 0 < p) (hA : IsUnit (A * A.transpose).det) (hw : 0 < w) (x : Euclidean q) :
    ‖rationalShapingShape A w hp hA hw x‖ ^ 2 =
      inner ℝ x (kernelFilledCovariance (Matrix.toEuclideanLin (A.map (Rat.castHom ℝ))).toContinuousLinearMap
        (rationalMatrix_real_surjective A hA) (w : ℝ) (rationalShapingKernelFill A : ℝ) x) := by
  have hs : (rationalShapingShape A w hp hA hw).toContinuousLinearMap.adjoint =
      (rationalShapingShape A w hp hA hw).toContinuousLinearMap :=
    (positiveSquareRootShape_positive _
      (rationalShapingCovarianceMatrix_real_posDef A w hp hA hw.ne')).isSymmetric.clm_adjoint_eq
  have hc := rationalShapingShape_covariance A w hp hA hw
  change (rationalShapingShape A w hp hA hw).toContinuousLinearMap.comp
    (rationalShapingShape A w hp hA hw).toContinuousLinearMap.adjoint = _ at hc
  rw [hs] at hc
  change ‖(rationalShapingShape A w hp hA hw).toContinuousLinearMap x‖ ^ 2 = _
  rw [ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right, hs, hc]
  rfl

theorem rationalShapingShape_extrema {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℚ) (w : ℚ)
    (hp : 0 < p) (hA : IsUnit (A * A.transpose).det) (hw : 0 < w) :
    let f := (Matrix.toEuclideanLin (A.map (Rat.castHom ℝ))).toContinuousLinearMap
    shapeMinimumStretch (rationalShapingShape A w hp hA hw) = (w : ℝ) / ‖f‖ ∧
      ‖(rationalShapingShape A w hp hA hw).toContinuousLinearMap‖ =
        (w : ℝ) / kernelMinimumStretch f.toLinearMap (rationalMatrix_real_surjective A hA) := by
  let : NeZero p := ⟨Nat.ne_of_gt hp⟩
  have hb := rationalShapingKernelFill_sharp_bounds A hp hA
  have hR : ‖(rationalRightInverseMatrix A).map (Rat.castHom ℝ)‖ =
      ‖minimumNormRightInverse (Matrix.toEuclideanLin (A.map (Rat.castHom ℝ))).toContinuousLinearMap
        (rationalMatrix_real_surjective A hA)‖ := by
    change ‖(Matrix.toEuclideanLin ((rationalRightInverseMatrix A).map (Rat.castHom ℝ))).toContinuousLinearMap‖ = _
    rw [rationalRightInverseMatrix_minimumNorm A hA]
  rw [hR] at hb
  exact kernelFilledShape_extrema _ (rationalMatrix_real_surjective A hA)
    (by exact_mod_cast hw) hb.1 hb.2 _ (rationalShapingShape_norm_sq A w hp hA hw)

theorem rationalShapingShape_image_covariance {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℚ) (w : ℚ)
    (hp : 0 < p) (hA : IsUnit (A * A.transpose).det) (hw : 0 < w) :
    gaussianPushforwardCovariance (Matrix.toEuclideanLin (A.map (Rat.castHom ℝ))).toContinuousLinearMap
      (rationalShapingShape A w hp hA hw) = (w : ℝ) ^ 2 • ContinuousLinearMap.id ℝ (Euclidean p) := by
  rw [gaussianPushforwardCovariance, rationalShapingShape_covariance, kernelFilledCovariance_image]

theorem rationalShapingShape_approximation {p q : ℕ} (t : ℕ)
    (A : Matrix (Fin p) (Fin q) ℚ) (w : ℚ) (hp : 0 < p)
    (hA : IsUnit (A * A.transpose).det) (hw : 0 < w) :
    ‖(Matrix.toEuclideanLin ((rationalShapingApprox t A w).map (Rat.castHom ℝ))).toContinuousLinearMap -
      (rationalShapingShape A w hp hA hw).toContinuousLinearMap‖ ≤ 1 / (2 : ℝ) ^ t := by
  exact rationalShapingApprox_operator_error t A w hp hA hw.ne'


/-- The three exact shaping identities together with a computable positive
rational approximation. The complete arithmetic bit-cost proof is
separate from this numerical certificate. -/
theorem rational_spherical_shaping_numerical_certificate {p q : ℕ} (t : ℕ)
    (A : Matrix (Fin p) (Fin q) ℚ) (w : ℚ) (hp : 0 < p)
    (hA : IsUnit (A * A.transpose).det) (hw : 0 < w) :
    let Ar := A.map (Rat.castHom ℝ)
    let f := (Matrix.toEuclideanLin Ar).toContinuousLinearMap
    let C := (rationalShapingCovarianceMatrix A w).map (Rat.castHom ℝ)
    let S := rationalShapingShape A w hp hA hw
    let R := (rationalShapingApprox t A w).map (Rat.castHom ℝ)
    C.PosDef ∧ Ar * C * Ar.transpose = (w : ℝ) ^ 2 • (1 : Matrix (Fin p) (Fin p) ℝ) ∧
      shapeMinimumStretch S = (w : ℝ) / ‖f‖ ∧
      ‖S.toContinuousLinearMap‖ =
        (w : ℝ) / kernelMinimumStretch f.toLinearMap (rationalMatrix_real_surjective A hA) ∧
      R.PosDef ∧ ‖(Matrix.toEuclideanLin R).toContinuousLinearMap - S.toContinuousLinearMap‖ ≤
        1 / (2 : ℝ) ^ t := by
  obtain ⟨hmin, hmax⟩ := rationalShapingShape_extrema A w hp hA hw
  exact ⟨rationalShapingCovarianceMatrix_real_posDef A w hp hA hw.ne',
    rationalShapingCovarianceMatrix_real_image A w hA, hmin, hmax,
    rationalShapingApprox_posDef t A w hp hA hw.ne', rationalShapingShape_approximation t A w hp hA hw⟩

end GeometricGaussianLHL
end

end RationalShapingWidths

section RealShapingWidths

/-!
## Exact widths of the real target approximated by the shaping algorithm

The actual positive square root of the real trace-average covariance has
the spherical image and both extreme widths of the paper’s Gaussian-shaping remark. Its matrix is
exactly the target appearing in the supplied-input approximation theorem.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped MatrixOrder Matrix.Norms.L2Operator

namespace GeometricGaussianLHL

def realShapingShape {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℝ) (w : ℝ)
    (hp : 0 < p) (hA : IsUnit (A * A.transpose).det) (hw : 0 < w) :
    Euclidean q ≃L[ℝ] Euclidean q :=
  positiveSquareRootShape (realShapingCovarianceMatrix A w)
    (realShapingCovarianceMatrix_posDef A w hp hA hw.ne')

theorem realShapingShape_matrix {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℝ) (w : ℝ)
    (hp : 0 < p) (hA : IsUnit (A * A.transpose).det) (hw : 0 < w) :
    Matrix.toEuclideanLin.symm (realShapingShape A w hp hA hw).toLinearMap =
      CFC.sqrt (realShapingCovarianceMatrix A w) := positiveSquareRootShape_matrix _ _

theorem realShapingShape_positive {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℝ) (w : ℝ)
    (hp : 0 < p) (hA : IsUnit (A * A.transpose).det) (hw : 0 < w) :
    (realShapingShape A w hp hA hw).toLinearMap.IsPositive := positiveSquareRootShape_positive _ _

theorem realShapingShape_covariance {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℝ) (w : ℝ)
    (hp : 0 < p) (hA : IsUnit (A * A.transpose).det) (hw : 0 < w) :
    shapeCovariance (realShapingShape A w hp hA hw) =
      kernelFilledCovariance (Matrix.toEuclideanLin A).toContinuousLinearMap
        (realMatrix_gram_surjective A hA) w ((A * A.transpose)⁻¹.trace / (p : ℝ)) := by
  rw [realShapingShape, positiveSquareRootShape_covariance, realShapingCovarianceMatrix_operator A w hA]

theorem realShapingShape_norm_sq {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℝ) (w : ℝ)
    (hp : 0 < p) (hA : IsUnit (A * A.transpose).det) (hw : 0 < w) (x : Euclidean q) :
    ‖realShapingShape A w hp hA hw x‖ ^ 2 =
      inner ℝ x (kernelFilledCovariance (Matrix.toEuclideanLin A).toContinuousLinearMap
        (realMatrix_gram_surjective A hA) w ((A * A.transpose)⁻¹.trace / (p : ℝ)) x) := by
  have hs : (realShapingShape A w hp hA hw).toContinuousLinearMap.adjoint =
      (realShapingShape A w hp hA hw).toContinuousLinearMap :=
    (realShapingShape_positive A w hp hA hw).isSymmetric.clm_adjoint_eq
  have hc := realShapingShape_covariance A w hp hA hw
  change (realShapingShape A w hp hA hw).toContinuousLinearMap.comp
    (realShapingShape A w hp hA hw).toContinuousLinearMap.adjoint = _ at hc
  rw [hs] at hc
  change ‖(realShapingShape A w hp hA hw).toContinuousLinearMap x‖ ^ 2 = _
  rw [ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right, hs, hc]
  rfl

theorem realShapingShape_extrema {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℝ) (w : ℝ)
    (hp : 0 < p) (hA : IsUnit (A * A.transpose).det) (hw : 0 < w) :
    let f := (Matrix.toEuclideanLin A).toContinuousLinearMap
    shapeMinimumStretch (realShapingShape A w hp hA hw) = w / ‖f‖ ∧
      ‖(realShapingShape A w hp hA hw).toContinuousLinearMap‖ =
        w / kernelMinimumStretch f.toLinearMap (realMatrix_gram_surjective A hA) := by
  let : NeZero p := ⟨hp.ne'⟩
  have hb := realShapingKernelFill_sharp_bounds A hp hA
  have hR : ‖realRightInverseMatrix A‖ =
      ‖minimumNormRightInverse (Matrix.toEuclideanLin A).toContinuousLinearMap
        (realMatrix_gram_surjective A hA)‖ := by
    change ‖(Matrix.toEuclideanLin (realRightInverseMatrix A)).toContinuousLinearMap‖ = _
    rw [realRightInverseMatrix_minimumNorm A hA]
  rw [hR] at hb
  exact kernelFilledShape_extrema _ (realMatrix_gram_surjective A hA)
    hw hb.1 hb.2 _ (realShapingShape_norm_sq A w hp hA hw)

theorem realShapingShape_image_covariance {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℝ) (w : ℝ)
    (hp : 0 < p) (hA : IsUnit (A * A.transpose).det) (hw : 0 < w) :
    gaussianPushforwardCovariance (Matrix.toEuclideanLin A).toContinuousLinearMap
      (realShapingShape A w hp hA hw) = w ^ 2 • ContinuousLinearMap.id ℝ (Euclidean p) := by
  rw [gaussianPushforwardCovariance, realShapingShape_covariance, kernelFilledCovariance_image]

/-- Matrix error and geometric operator error refer to the same shape. -/
theorem realShapingShape_error {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℝ) (w : ℝ)
    (hp : 0 < p) (hA : IsUnit (A * A.transpose).det) (hw : 0 < w)
    (R : Matrix (Fin q) (Fin q) ℝ) :
    ‖(Matrix.toEuclideanLin R).toContinuousLinearMap -
      (realShapingShape A w hp hA hw).toContinuousLinearMap‖ =
      ‖R - CFC.sqrt (realShapingCovarianceMatrix A w)‖ := by
  change ‖(Matrix.toEuclideanLin R).toContinuousLinearMap -
    (Matrix.toEuclideanLin (CFC.sqrt (realShapingCovarianceMatrix A w))).toContinuousLinearMap‖ = _
  exact (euclideanMatrix_norm_sub_CLM _ _).symm

end GeometricGaussianLHL
end

end RealShapingWidths

section RationalMetricCostCertificate

/-!
## Metric normalization costs measured against finite input encodings

Positive dimensions cover the canonical application. They ensure that the
coefficient table bounds both block multiplicities in the input-length theorem.
-/

open scoped MatrixOrder Matrix.Norms.L2Operator
namespace GeometricGaussianLHL

theorem polyBound_rationalRectEncodingBudget {p q L : ℕ → ℕ}
    (hp : PolynomialCostBound p) (hq : PolynomialCostBound q) (hL : PolynomialCostBound L) :
    PolynomialCostBound (fun x => rationalRectEncodingBudget (p x) (q x) (L x)) :=
  (((((PolynomialCostBound.const 2).mul hp).add ((PolynomialCostBound.const 2).mul hq)).add (PolynomialCostBound.const 2)).add
    ((PolynomialCostBound.const 2).mul ((hp.mul hq).mul hL))).add (hp.mul hq)

theorem polyBound_rationalMetricSandwichOperandBudget {d r L : ℕ → ℕ}
    (hd : PolynomialCostBound d) (hr : PolynomialCostBound r) (hL : PolynomialCostBound L) :
    PolynomialCostBound (fun x => rationalMetricSandwichOperandBudget (d x) (r x) (L x)) :=
  ((polyBound_rationalDotOperandBudget (hr.mul hd) (hL.add (PolynomialCostBound.const 2))).add hL).add (PolynomialCostBound.const 2)

theorem polyBound_rationalMetricSandwichBudget {d r m L : ℕ → ℕ}
    (hd : PolynomialCostBound d) (hr : PolynomialCostBound r) (hm : PolynomialCostBound m) (hL : PolynomialCostBound L) :
    PolynomialCostBound (fun x => rationalMetricSandwichBudget (d x) (r x) (m x) (L x)) := by
  have hH := polyBound_rationalMetricSandwichOperandBudget hd hr hL
  exact ((((polyBound_rationalBlockBudget hr hd hL).add (polyBound_rationalBlockBudget hm hd hL)).add
    (polyBound_rationalRectMulBudget (hr.mul hd) (hr.mul hd) (hm.mul hd) (hL.add (PolynomialCostBound.const 2)))).add
      (polyBound_rationalRectMulBudget (hr.mul hd) (hm.mul hd) (hm.mul hd) hH)).add
        (polyBound_rationalRectEncodingBudget (hr.mul hd) (hm.mul hd) (polyBound_rationalDotOperandBudget (hm.mul hd) hH))

theorem polyBound_rationalMetricNormalizationOperandBudget {d S L t : ℕ → ℕ}
    (hd : PolynomialCostBound d) (hS : PolynomialCostBound S) (hL : PolynomialCostBound L) (ht : PolynomialCostBound t) :
    PolynomialCostBound (fun x => rationalMetricNormalizationOperandBudget (d x) (S x) (L x) (t x)) :=
  (hL.add (polyBound_rationalSpectralBudget hd hS ht)).add (polyBound_rationalInverseRootOutputBudget hd hS ht)

theorem polyBound_rationalMetricNormalizationBudget {d r m S L t : ℕ → ℕ}
    (hd : PolynomialCostBound d) (hr : PolynomialCostBound r) (hm : PolynomialCostBound m)
    (hS : PolynomialCostBound S) (hL : PolynomialCostBound L) (ht : PolynomialCostBound t) :
    PolynomialCostBound (fun x => rationalMetricNormalizationBudget (d x) (r x) (m x) (S x) (L x) (t x)) :=
  ((polyBound_rationalSpectralBudget hd hS ht).add (polyBound_rationalInverseRootBudget hd hS ht)).add
    (polyBound_rationalMetricSandwichBudget hd hr hm (polyBound_rationalMetricNormalizationOperandBudget hd hS hL ht))

theorem rationalMetricSandwichBudget_mono {d d' r r' m m' L L' : ℕ}
    (hd : d ≤ d') (hr : r ≤ r') (hm : m ≤ m') (hL : L ≤ L') :
    rationalMetricSandwichBudget d r m L ≤ rationalMetricSandwichBudget d' r' m' L' := by
  have hrd := Nat.mul_le_mul hr hd
  have hmd := Nat.mul_le_mul hm hd
  have hH : rationalMetricSandwichOperandBudget d r L ≤ rationalMetricSandwichOperandBudget d' r' L' := by
    have hD := rationalDotOperandBudget_mono hrd (show L + 2 ≤ L' + 2 by omega)
    unfold rationalMetricSandwichOperandBudget
    omega
  apply Nat.add_le_add
  · apply Nat.add_le_add
    · exact Nat.add_le_add (Nat.add_le_add (rationalBlockBudget_mono hr hd hL) (rationalBlockBudget_mono hm hd hL))
        (rationalRectMulBudget_mono hrd hrd hmd (by omega))
    · exact rationalRectMulBudget_mono hrd hmd hmd hH
  · have hO := rationalDotOperandBudget_mono hmd hH
    unfold rationalRectEncodingBudget
    gcongr

theorem rationalMetricNormalizationBudget_mono {d d' r r' m m' S S' L L' t t' : ℕ}
    (hd : d ≤ d') (hr : r ≤ r') (hm : m ≤ m') (hS : S ≤ S') (hL : L ≤ L') (ht : t ≤ t') :
    rationalMetricNormalizationBudget d r m S L t ≤ rationalMetricNormalizationBudget d' r' m' S' L' t' :=
  Nat.add_le_add (Nat.add_le_add (rationalSpectralBudget_mono hd hS ht) (rationalInverseRootBudget_mono hd hS ht))
    (rationalMetricSandwichBudget_mono hd hr hm (Nat.add_le_add
      (Nat.add_le_add hL (rationalSpectralBudget_mono hd hS ht)) (rationalInverseRootOutputBudget_mono hd hS ht)))

def rationalMetricInputLength {d r m : ℕ} (G : RationalMatrixData d) (C : RationalRectData (r * d) (m * d)) : ℕ :=
  (encodeRationalMatrixData G).length + (encodeRationalRectData C).length

theorem rationalMetricInputLength_bounds {d r m : ℕ} (G : RationalMatrixData d) (C : RationalRectData (r * d) (m * d))
    (hd : 0 < d) (hr : 0 < r) (hm : 0 < m) :
    d ≤ rationalMetricInputLength G C ∧ r ≤ rationalMetricInputLength G C ∧ m ≤ rationalMetricInputLength G C ∧
      rationalMatrixMagnitudeBits (rationalMatrixOfData G) ≤ rationalMetricInputLength G C ∧
      ∀ i j, rationalMagnitudeBits (rationalRectMatrixOfData C i j) ≤ rationalMetricInputLength G C := by
  have hg := encodeRationalMatrixData_length G
  have hc := encodeRationalRectData_length C
  have hd2 := Nat.le_mul_self d
  have hrd : r ≤ r * d := by nlinarith
  have hmd : m ≤ m * d := by nlinarith
  have hp := Nat.mul_pos hr hd
  have hq := Nat.mul_pos hm hd
  have hprod : r * d ≤ (r * d) * (m * d) := by nlinarith
  have hprod' : m * d ≤ (r * d) * (m * d) := by nlinarith
  refine ⟨?_, ?_, ?_, ?_, fun i j => (rationalRect_entry_bits_le_encoded C i j).trans (by unfold rationalMetricInputLength; omega)⟩ <;>
    unfold rationalMetricInputLength <;> omega

theorem rationalMetricNormalization_polynomial_cost : ∃ C e : ℕ,
    ∀ (d r m t : ℕ) (G : RationalMatrixData d) (X : RationalRectData (r * d) (m * d)),
      0 < d → 0 < r → 0 < m → ((rationalMatrixOfData G).map (fun q : ℚ => (q : ℝ))).PosDef →
      (costedRationalMetricNormalization t G X).steps ≤ C * (rationalMetricInputLength G X + t + 1) ^ e := by
  obtain ⟨C, e, hCe⟩ := (polyBound_rationalMetricNormalizationBudget PolynomialCostBound.id PolynomialCostBound.id
    PolynomialCostBound.id PolynomialCostBound.id PolynomialCostBound.id PolynomialCostBound.id).exists_mul_pow_bound
  refine ⟨C, e, fun d r m t G X hd hr hm hG => ?_⟩
  have hb := rationalMetricInputLength_bounds G X hd hr hm
  exact (costedRationalMetricNormalization_steps_le t G X (rationalMetricInputLength G X) hG hb.2.2.2.2).trans
    ((rationalMetricNormalizationBudget_mono (hb.1.trans (by omega)) (hb.2.1.trans (by omega))
      (hb.2.2.1.trans (by omega)) (hb.2.2.2.1.trans (by omega))
      (show rationalMetricInputLength G X ≤ rationalMetricInputLength G X + t by omega)
      (show t ≤ rationalMetricInputLength G X + t by omega)).trans (hCe (rationalMetricInputLength G X + t)))

theorem costedRationalMetricNormalization_error {d r m : ℕ} (t : ℕ) (G : RationalMatrixData d) (C : RationalRectData (r * d) (m * d))
    (hG : ((rationalMatrixOfData G).map (Rat.castHom ℝ)).PosDef) :
    let Gr := (rationalMatrixOfData G).map (Rat.castHom ℝ)
    let Cr := (rationalRectMatrixOfData C).map (Rat.castHom ℝ)
    ‖(rationalRectMatrixOfData (costedRationalMetricNormalization t G C).value).map (Rat.castHom ℝ) - metricNormalizedMatrix Gr Cr‖ ≤
      ‖Cr‖ * (‖CFC.sqrt Gr‖ + ‖(CFC.sqrt Gr)⁻¹‖ + 1) * (1 / (2 : ℝ) ^ t) := by
  rw [costedRationalMetricNormalization_data, rationalRectMatrixOfData_data]
  exact rationalMetricNormalizedApprox_error t _ _ hG (norm_nonneg _) (norm_nonneg _) le_rfl le_rfl

theorem rationalMetricNormalization_computational_certificate : ∃ C e : ℕ,
    ∀ (d r m t : ℕ) (G : RationalMatrixData d) (X : RationalRectData (r * d) (m * d)),
      0 < d → 0 < r → 0 < m → ((rationalMatrixOfData G).map (Rat.castHom ℝ)).PosDef →
      let run := costedRationalMetricNormalization t G X
      run.steps ≤ C * (rationalMetricInputLength G X + t + 1) ^ e ∧
      (encodeRationalRectData run.value).length ≤ C * (rationalMetricInputLength G X + t + 1) ^ e ∧
      let Gr := (rationalMatrixOfData G).map (Rat.castHom ℝ)
      let Xr := (rationalRectMatrixOfData X).map (Rat.castHom ℝ)
      ‖(rationalRectMatrixOfData run.value).map (Rat.castHom ℝ) - metricNormalizedMatrix Gr Xr‖ ≤
        ‖Xr‖ * (‖CFC.sqrt Gr‖ + ‖(CFC.sqrt Gr)⁻¹‖ + 1) * (1 / (2 : ℝ) ^ t) := by
  obtain ⟨C, e, hCe⟩ := rationalMetricNormalization_polynomial_cost
  refine ⟨C, e, fun d r m t G X hd hr hm hG => ?_⟩
  have hc := hCe d r m t G X hd hr hm hG
  exact ⟨hc, (costedRationalMetricNormalization_length_le_steps t G X).trans hc,
    costedRationalMetricNormalization_error t G X hG⟩

end GeometricGaussianLHL

end RationalMetricCostCertificate

section RationalShapingCostCertificate

/-!
## Uniform polynomial-cost certificate for finite rational shaping input

The same computed output has a polynomial cost and encoded length, decodes
exactly, is positive definite and approximates the shaping operator to the
requested accuracy. The input size includes the matrix and rational width.
-/

open scoped MatrixOrder Matrix.Norms.L2Operator
namespace GeometricGaussianLHL

def rationalShapingInputLength {p q : ℕ} (X : RationalRectData p q) (w : ℚ) : ℕ :=
  (encodeRationalRectData X).length + (encodeRatBits w).length

theorem rationalRect_cols_pos {p q : ℕ} (X : RationalRectData p q) (hp : 0 < p)
    (hA : IsUnit (rationalRectMatrixOfData X * (rationalRectMatrixOfData X).transpose).det) : 0 < q := by
  by_contra! hq
  have hq0 : q = 0 := by omega
  subst q
  let : NeZero p := ⟨hp.ne'⟩
  have hz : rationalRectMatrixOfData X * (rationalRectMatrixOfData X).transpose = 0 := by
    ext i j
    simp [Matrix.mul_apply]
  rw [hz, Matrix.det_zero] at hA
  exact not_isUnit_zero hA

theorem rationalShapingInputLength_bounds {p q : ℕ} (X : RationalRectData p q) (w : ℚ) (hp : 0 < p)
    (hA : IsUnit (rationalRectMatrixOfData X * (rationalRectMatrixOfData X).transpose).det) :
    p ≤ rationalShapingInputLength X w ∧ q ≤ rationalShapingInputLength X w ∧
      rationalMagnitudeBits w ≤ rationalShapingInputLength X w ∧
      ∀ i j, rationalMagnitudeBits (rationalRectMatrixOfData X i j) ≤ rationalShapingInputLength X w := by
  have hq := rationalRect_cols_pos X hp hA
  have hplen : p ≤ p * q := by nlinarith
  have hqlen : q ≤ p * q := by nlinarith
  have hl := encodeRationalRectData_length X
  have hw := encodeRatBits_length w
  have hM : rationalRectMagnitudeBits X ≤ rationalShapingInputLength X w := by
    unfold rationalShapingInputLength
    omega
  refine ⟨?_, ?_, ?_, fun i j => (rationalRect_entry_bits_le X i j).trans hM⟩ <;>
    unfold rationalShapingInputLength <;> omega

theorem rationalShapingApprox_polynomial_cost : ∃ C e : ℕ,
    ∀ (p q t : ℕ) (X : RationalRectData p q) (w : ℚ), 0 < p →
      IsUnit (rationalRectMatrixOfData X * (rationalRectMatrixOfData X).transpose).det → w ≠ 0 →
      (costedRationalShapingApprox t X w).steps ≤ C * (rationalShapingInputLength X w + t + 1) ^ e := by
  obtain ⟨C, e, hCe⟩ := (polyBound_rationalShapingBudget PolynomialCostBound.id PolynomialCostBound.id
    PolynomialCostBound.id PolynomialCostBound.id).exists_mul_pow_bound
  refine ⟨C, e, fun p q t X w hp hA hw => ?_⟩
  have hsize := rationalShapingInputLength_bounds X w hp hA
  exact (costedRationalShapingApprox_steps_le t X w (rationalShapingInputLength X w) hsize.2.2.2 hsize.2.2.1 hp hA hw).trans
    ((rationalShapingBudget_mono (hsize.1.trans (by omega)) (hsize.2.1.trans (by omega))
      (show rationalShapingInputLength X w ≤ rationalShapingInputLength X w + t by omega)
      (show t ≤ rationalShapingInputLength X w + t by omega)).trans (hCe (rationalShapingInputLength X w + t)))

theorem rationalShapingApprox_polynomialTime (p q : ℕ) :
    Costed.PolynomialTime (fun a t => costedRationalShapingApprox t (a : RationalRectData p q × ℚ).1 a.2)
      (fun a => 0 < p ∧ IsUnit (rationalRectMatrixOfData a.1 * (rationalRectMatrixOfData a.1).transpose).det ∧ a.2 ≠ 0)
      (fun a => rationalShapingInputLength a.1 a.2) := by
  obtain ⟨C, e, hCe⟩ := rationalShapingApprox_polynomial_cost
  exact ⟨C, e, fun a ha t => hCe p q t a.1 a.2 ha.1 ha.2.1 ha.2.2⟩

theorem costedRationalShapingApprox_posDef {p q : ℕ} (t : ℕ) (X : RationalRectData p q) (w : ℚ) (hp : 0 < p)
    (hA : IsUnit (rationalRectMatrixOfData X * (rationalRectMatrixOfData X).transpose).det) (hw : w ≠ 0) :
    ((rationalMatrixOfData (costedRationalShapingApprox t X w).value).map (Rat.castHom ℝ)).PosDef := by
  rw [costedRationalShapingApprox_data, rationalMatrixOfData_data]
  exact rationalShapingApprox_posDef t _ w hp hA hw

theorem costedRationalShapingApprox_operator_error {p q : ℕ} (t : ℕ) (X : RationalRectData p q) (w : ℚ) (hp : 0 < p)
    (hA : IsUnit (rationalRectMatrixOfData X * (rationalRectMatrixOfData X).transpose).det) (hw : w ≠ 0) :
    ‖(Matrix.toEuclideanLin ((rationalMatrixOfData (costedRationalShapingApprox t X w).value).map
        (Rat.castHom ℝ))).toContinuousLinearMap -
      (Matrix.toEuclideanLin (rationalShapingSquareRootMatrix (rationalRectMatrixOfData X) w)).toContinuousLinearMap‖ ≤
        1 / (2 : ℝ) ^ t := by
  rw [costedRationalShapingApprox_data, rationalMatrixOfData_data]
  exact rationalShapingApprox_operator_error t _ w hp hA hw

theorem rationalShaping_computational_certificate : ∃ C e : ℕ,
    ∀ (p q t : ℕ) (X : RationalRectData p q) (w : ℚ), 0 < p →
      IsUnit (rationalRectMatrixOfData X * (rationalRectMatrixOfData X).transpose).det → w ≠ 0 →
      let run := costedRationalShapingApprox t X w
      run.steps ≤ C * (rationalShapingInputLength X w + t + 1) ^ e ∧
      (encodeRationalMatrixData run.value).length ≤ C * (rationalShapingInputLength X w + t + 1) ^ e ∧
      decodeRationalMatrixDataPrefix (encodeRationalMatrixData run.value) = some (⟨q, run.value⟩, []) ∧
      ((rationalMatrixOfData run.value).map (Rat.castHom ℝ)).PosDef ∧
      ‖(Matrix.toEuclideanLin ((rationalMatrixOfData run.value).map (Rat.castHom ℝ))).toContinuousLinearMap -
        (Matrix.toEuclideanLin (rationalShapingSquareRootMatrix (rationalRectMatrixOfData X) w)).toContinuousLinearMap‖ ≤
          1 / (2 : ℝ) ^ t := by
  obtain ⟨C, e, hCe⟩ := rationalShapingApprox_polynomial_cost
  refine ⟨C, e, fun p q t X w hp hA hw => ?_⟩
  have hc := hCe p q t X w hp hA hw
  refine ⟨hc, (costedRationalShapingApprox_length_le_steps t X w).trans hc, ?_,
    costedRationalShapingApprox_posDef t X w hp hA hw, costedRationalShapingApprox_operator_error t X w hp hA hw⟩
  simpa only [List.append_nil] using decodeRationalMatrixData_append (costedRationalShapingApprox t X w).value []

end GeometricGaussianLHL

end RationalShapingCostCertificate

section RationalShapingCertificate

/-! # Rational shaping: exact identities and computed approximation

The matrix is returned directly by the rational numerical algorithm. Costs
are analyzed in the declared arithmetic model; no machine simulation is used.
-/
open scoped MatrixOrder Matrix.Norms.L2Operator
namespace GeometricGaussianLHL

theorem rational_spherical_shaping_approximation_certificate
    {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℚ) (w : ℚ)
    (hp : 0 < p) (hA : IsUnit (A * A.transpose).det) (hw : 0 < w) :
    let Ar := A.map (Rat.castHom ℝ)
    let f := (Matrix.toEuclideanLin Ar).toContinuousLinearMap
    let Cov := (rationalShapingCovarianceMatrix A w).map (Rat.castHom ℝ)
    let S := rationalShapingShape A w hp hA hw
    Cov.PosDef ∧ Ar * Cov * Ar.transpose = (w : ℝ) ^ 2 • (1 : Matrix (Fin p) (Fin p) ℝ) ∧
      Matrix.toEuclideanLin.symm S.toLinearMap = rationalShapingSquareRootMatrix A w ∧
      shapeMinimumStretch S = (w : ℝ) / ‖f‖ ∧
      ‖S.toContinuousLinearMap‖ =
        (w : ℝ) / kernelMinimumStretch f.toLinearMap (rationalMatrix_real_surjective A hA) ∧
      gaussianPushforwardCovariance f S = (w : ℝ) ^ 2 • ContinuousLinearMap.id ℝ (Euclidean p) ∧
      ∀ t : ℕ, ((rationalShapingApprox t A w).map (Rat.castHom ℝ)).PosDef ∧
        ‖(Matrix.toEuclideanLin ((rationalShapingApprox t A w).map (Rat.castHom ℝ))).toContinuousLinearMap -
          S.toContinuousLinearMap‖ ≤ 1 / (2 : ℝ) ^ t := by
  dsimp only
  obtain ⟨hmin, hmax⟩ := rationalShapingShape_extrema A w hp hA hw
  refine ⟨rationalShapingCovarianceMatrix_real_posDef A w hp hA hw.ne',
    rationalShapingCovarianceMatrix_real_image A w hA,
    rationalShapingShape_matrix A w hp hA hw, hmin, hmax,
    rationalShapingShape_image_covariance A w hp hA hw, ?_⟩
  intro t
  exact ⟨rationalShapingApprox_posDef t A w hp hA hw.ne',
    rationalShapingApprox_operator_error t A w hp hA hw.ne'⟩

end GeometricGaussianLHL

end RationalShapingCertificate

section RealShapingPrecision

/-!
## A dyadic input-precision budget for the real shaping target

If matrix norms, inverse-Gram norms and widths are bounded by `2^b`, an
explicit input error budget suffices for output error `2^-t`. The theorem
uses the rational algorithm output at precision `t+1`,
approximating the same shape whose two extreme widths and image are proved.
Rank and conditioning of the approximation follow from the exact input and
the error budget. Supplying that approximation remains an input-representation
obligation; no real-input conversion cost is hidden.
-/

noncomputable section

open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator

namespace GeometricGaussianLHL

theorem shapingRealInputFactor_self_le {H : ℝ} (hH : 1 ≤ H) :
    shapingRealInputFactor H H H ≤ 40 * H ^ 11 := by
  have h₂ : H ^ 2 ≤ H ^ 11 := pow_le_pow_right₀ hH (by omega)
  have h₅ : H ^ 5 ≤ H ^ 11 := pow_le_pow_right₀ hH (by omega)
  have h₈ : H ^ 8 ≤ H ^ 11 := pow_le_pow_right₀ hH (by omega)
  have he : shapingRealInputFactor H H H = 2 * H ^ 2 + 14 * H ^ 5 + 18 * H ^ 8 + 6 * H ^ 11 := by
    unfold shapingRealInputFactor shapingCovarianceInputFactor
    ring
  rw [he]
  linarith

theorem shapingRealInputFactor_dyadic_le (b : ℕ) :
    shapingRealInputFactor ((2 : ℝ) ^ b) ((2 : ℝ) ^ b) ((2 : ℝ) ^ b) ≤
      (2 : ℝ) ^ (11 * b + 6) := by
  apply (shapingRealInputFactor_self_le (one_le_pow₀ (by norm_num))).trans
  calc
    40 * ((2 : ℝ) ^ b) ^ 11 ≤ 64 * ((2 : ℝ) ^ b) ^ 11 := by gcongr; norm_num
    _ = _ := by rw [← pow_mul, Nat.mul_comm b 11, pow_add]; norm_num; ring

theorem realShapingCovarianceMatrix_dyadic_input_error {p q : ℕ}
    (A B : Matrix (Fin p) (Fin q) ℝ) (w v : ℝ) (hp : 0 < p)
    (hA : IsUnit (A * A.transpose).det) (hB : IsUnit (B * B.transpose).det) (t b : ℕ)
    (hAn : ‖A‖ ≤ (2 : ℝ) ^ b) (hBn : ‖B‖ ≤ (2 : ℝ) ^ b)
    (hAi : ‖(A * A.transpose)⁻¹‖ ≤ (2 : ℝ) ^ b)
    (hBi : ‖(B * B.transpose)⁻¹‖ ≤ (2 : ℝ) ^ b)
    (hw : |w| ≤ (2 : ℝ) ^ b) (hv : |v| ≤ (2 : ℝ) ^ b)
    (hinput : ‖A - B‖ + |w - v| ≤ 1 / (2 : ℝ) ^ (2 * (t + 1) + 11 * b + 6)) :
    ‖realShapingCovarianceMatrix A w - realShapingCovarianceMatrix B v‖ ≤
      1 / (2 : ℝ) ^ (2 * (t + 1)) := by
  apply (realShapingCovarianceMatrix_input_error A B w v hp hA hB
    (by positivity) (by positivity) (by positivity) hAn hBn hAi hBi hw hv).trans
  calc
    _ ≤ (2 : ℝ) ^ (11 * b + 6) * (1 / (2 : ℝ) ^ (2 * (t + 1) + 11 * b + 6)) :=
      mul_le_mul (shapingRealInputFactor_dyadic_le b) hinput (by positivity) (by positivity)
    _ = _ := by
      rw [show 2 * (t + 1) + 11 * b + 6 = 2 * (t + 1) + (11 * b + 6) by omega, pow_add]
      field_simp
      simp only [pow_add]
      ring

/-- The shared precision argument derives rational full row rank and square-root
accuracy from exact-input bounds. It is independent of the program that
produced the rational approximation. -/
theorem realShapingInput_approximation_data {p q : ℕ}
    (A : Matrix (Fin p) (Fin q) ℝ) (w : ℝ)
    (Q : Matrix (Fin p) (Fin q) ℚ) (v : ℚ) (hp : 0 < p)
    (hA : IsUnit (A * A.transpose).det) (hw : 0 < w) (hv : 0 < v) (t b : ℕ)
    (hAn : ‖A‖ ≤ (2 : ℝ) ^ b) (hAi : ‖(A * A.transpose)⁻¹‖ ≤ (2 : ℝ) ^ b)
    (hwn : |w| ≤ (2 : ℝ) ^ b)
    (hinput : ‖A - Q.map (Rat.castHom ℝ)‖ + |w - (v : ℝ)| ≤
      1 / (2 : ℝ) ^ (2 * (t + 1) + 11 * (b + 1) + 6)) :
    IsUnit (Q * Q.transpose).det ∧
      ‖rationalShapingSquareRootMatrix Q v - CFC.sqrt (realShapingCovarianceMatrix A w)‖ ≤
        1 / (2 : ℝ) ^ (t + 1) := by
  have hCov := realShapingCovarianceMatrix_posDef A w hp hA hw.ne'
  have hsmall : ‖Q.map (Rat.castHom ℝ) - A‖ ≤ 1 / (2 : ℝ) ^ (2 * b + 3) := by
    rw [norm_sub_rev]
    apply (le_add_of_nonneg_right (abs_nonneg _)).trans (hinput.trans _)
    apply one_div_le_one_div_of_le (by positivity)
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  obtain ⟨hQn, hQr, hQi⟩ := matrixGram_dyadic_input_conditioning A (Q.map (Rat.castHom ℝ))
    hp hA b hAn hAi hsmall
  have hQ : IsUnit (Q * Q.transpose).det := by
    apply isUnit_iff_ne_zero.mpr
    intro hz
    have he := congrArg (Rat.castHom ℝ) hz
    rw [map_zero, (Rat.castHom ℝ).map_det] at he
    have hm : (Rat.castHom ℝ).mapMatrix (Q * Q.transpose) =
        Q.map (Rat.castHom ℝ) * (Q.map (Rat.castHom ℝ)).transpose := Matrix.map_mul
    rw [hm] at he
    exact (isUnit_iff_ne_zero.mp hQr) he
  have hb : (2 : ℝ) ^ b ≤ (2 : ℝ) ^ (b + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hinput1 : ‖A - Q.map (Rat.castHom ℝ)‖ + |w - (v : ℝ)| ≤ 1 :=
    hinput.trans ((div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num)))
  have hvn : |(v : ℝ)| ≤ (2 : ℝ) ^ (b + 1) := by
    have ht := abs_add_le ((v : ℝ) - w) w
    rw [sub_add_cancel, abs_sub_comm] at ht
    have hb1 : 1 ≤ (2 : ℝ) ^ b := one_le_pow₀ (by norm_num)
    rw [pow_succ]
    linarith [norm_nonneg (A - Q.map (Rat.castHom ℝ))]
  have hcov : ‖realShapingCovarianceMatrix A w -
      (rationalShapingCovarianceMatrix Q v).map (Rat.castHom ℝ)‖ ≤
      1 / (2 : ℝ) ^ (2 * (t + 1)) := by
    rw [← realShapingCovarianceMatrix_rat Q v hQ]
    exact realShapingCovarianceMatrix_dyadic_input_error A (Q.map (Rat.castHom ℝ)) w (v : ℝ)
      hp hA hQr t (b + 1) (hAn.trans hb) hQn (hAi.trans hb) hQi (hwn.trans hb) hvn hinput
  have hsqrt : ‖rationalShapingSquareRootMatrix Q v - CFC.sqrt (realShapingCovarianceMatrix A w)‖ ≤
      1 / (2 : ℝ) ^ (t + 1) := by
    apply (matrix_sqrt_operator_holder _ _
      (rationalShapingCovarianceMatrix_real_posDef Q v hp hQ hv.ne').posSemidef hCov.posSemidef).trans
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity, ?_⟩
    rw [norm_sub_rev]
    exact hcov.trans_eq (by rw [two_mul, pow_add]; ring)
  exact ⟨hQ, hsqrt⟩

/-- Accuracy of the actual rational algorithm on a real target. -/
theorem realShapingInput_approximation_certificate
    (p q t b : ℕ) (A : Matrix (Fin p) (Fin q) ℝ) (w : ℝ)
    (Q : Matrix (Fin p) (Fin q) ℚ) (v : ℚ) (hp : 0 < p)
    (hA : IsUnit (A * A.transpose).det) (hw : 0 < w)
    (hv : 0 < v) (hAn : ‖A‖ ≤ (2 : ℝ) ^ b)
    (hAi : ‖(A * A.transpose)⁻¹‖ ≤ (2 : ℝ) ^ b)
    (hwn : |w| ≤ (2 : ℝ) ^ b)
    (hinput : ‖A - Q.map (Rat.castHom ℝ)‖ + |w - (v : ℝ)| ≤
      1 / (2 : ℝ) ^ (2 * (t + 1) + 11 * (b + 1) + 6)) :
    let R := (rationalShapingApprox (t + 1) Q v).map (Rat.castHom ℝ)
    R.PosDef ∧ ‖R - CFC.sqrt (realShapingCovarianceMatrix A w)‖ ≤ 1 / (2 : ℝ) ^ t ∧
      ‖(Matrix.toEuclideanLin R).toContinuousLinearMap -
        (realShapingShape A w hp hA hw).toContinuousLinearMap‖ ≤ 1 / (2 : ℝ) ^ t := by
  obtain ⟨hQ, hsqrt⟩ := realShapingInput_approximation_data A w Q v hp hA hw hv t b hAn hAi hwn hinput
  have herr := rationalShapingApprox_matrix_error (t + 1) Q v hp hQ hv.ne'
  have htotal : ‖(rationalShapingApprox (t + 1) Q v).map (Rat.castHom ℝ) -
      CFC.sqrt (realShapingCovarianceMatrix A w)‖ ≤ 1 / (2 : ℝ) ^ t := by
    calc
      _ ≤ ‖(rationalShapingApprox (t + 1) Q v).map (Rat.castHom ℝ) - rationalShapingSquareRootMatrix Q v‖ +
          ‖rationalShapingSquareRootMatrix Q v - CFC.sqrt (realShapingCovarianceMatrix A w)‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ 1 / (2 : ℝ) ^ (t + 1) + 1 / (2 : ℝ) ^ (t + 1) := add_le_add herr hsqrt
      _ = _ := by rw [pow_succ]; ring
  exact ⟨rationalShapingApprox_posDef (t + 1) Q v hp hQ hv.ne', htotal,
    (realShapingShape_error A w hp hA hw _).symm ▸ htotal⟩

end GeometricGaussianLHL
end

end RealShapingPrecision
