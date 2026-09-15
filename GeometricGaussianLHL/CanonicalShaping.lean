import GeometricGaussianLHL.RationalShaping
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric

/-!
# Canonical shaping from finite algebraic input

This module collects the following proof sections, in dependency order.
- Algebraicity of the complete canonical metric (`CanonicalAlgebraicAvailability`).
- Conditioning from finite canonical metric data (`CanonicalMetricConditioning`).
- Rational shaping in explicit scalar-Gram number-field coordinates (`ScalarGramShaping`).
- Numerical metric conversion for the actual canonical matrix (`CanonicalMetricApproximation`).
- Trace-average shaping for general canonical number-field geometry (`CanonicalGramShaping`).
- ScalarGramShapingCertificate (`ScalarGramShapingCertificate`).
- Gaussian guarantees from actual shape approximation (`ApproximateShapingGaussian`).
- CanonicalGramShapingCertificate (`CanonicalGramShapingCertificate`).
- CanonicalInputBounds (`CanonicalInputBounds`).
- CanonicalMetricShapingCertificate (`CanonicalMetricShapingCertificate`).
- Preparing a positive rational metric from algebraic entries (`AlgebraicMetricPreparation`).
- Finite prepared inputs and the canonical approximation algorithm (`CanonicalShapingInput`).
- Stored integral coefficients and the canonical conversion schedule (`PreparedShapingScheduleCost`).
- Canonical shaping from finite algebraic metric and width data (`CanonicalAlgebraicInput`).
- Composing finite prepared data with the complete shaping execution (`PreparedShapingCost`).
- Stored finite algebraic input for the canonical algorithm (`CanonicalAlgebraicData`).
- Canonical accuracy and cost of the same prepared execution (`CanonicalPreparedCost`).
- Scanning the finite canonical input (`CanonicalInputScanCost`).
- Computing the canonical conditioning and shaping budgets (`CanonicalBudgetCost`).
- Charged preparation of algebraic metric entries and width (`AlgebraicPreparationCost`).
- Complete preparation from the original finite canonical input (`CanonicalFinitePreparationCost`).
- Canonical shaping cost from the original finite algebraic input (`CanonicalFiniteCost`).
- Availability of the finite inputs used by canonical shaping (`CanonicalEncodingExistence`).
-/

section CanonicalAlgebraicAvailability

/-!
## Algebraicity of the complete canonical metric

Every canonical Gram entry is integral over the integers: it is a real sum of
products of algebraic integers and their conjugates. This covers arbitrary
number fields and integral bases, without a special Gram-matrix assumption.
-/
noncomputable section
open Module NumberField
open scoped ComplexConjugate
namespace GeometricGaussianLHL

variable (K : Type*) [Field K] [NumberField K]

local instance : Fintype (K →+* ℂ) := inferInstance

theorem canonicalGram_isIntegral {ι : Type*} [Fintype ι]
    (b : Basis ι ℤ (𝓞 K)) (i j : ι) : IsIntegral ℤ (canonicalGram K b i j) := by
  apply (isIntegral_algebraMap_iff (R := ℤ) (A := ℝ) (B := ℂ)).mp
  change IsIntegral ℤ (canonicalGram K b i j : ℂ)
  rw [canonicalGram_complex]
  apply IsIntegral.sum
  intro τ _
  have hi := IsIntegral.map τ.toIntAlgHom (RingOfIntegers.isIntegral_coe (b i))
  have hj := IsIntegral.map τ.toIntAlgHom (RingOfIntegers.isIntegral_coe (b j))
  exact hj.mul (IsIntegral.map (starRingEnd ℂ).toIntAlgHom hi)

theorem canonicalGram_isAlgebraic {ι : Type*} [Fintype ι]
    (b : Basis ι ℤ (𝓞 K)) (i j : ι) : IsAlgebraic ℤ (canonicalGram K b i j) :=
  (canonicalGram_isIntegral K b i j).isAlgebraic

end GeometricGaussianLHL
end

end CanonicalAlgebraicAvailability

section CanonicalMetricConditioning

/-!
## Conditioning from finite canonical metric data

The determinant of an integral basis's canonical Gram matrix is the absolute
field discriminant, hence at least one. Bounds on the encoded entries then
bound the inverse and both square roots. No conditioning parameter is supplied
as an extra input, and no algorithm for finding an integral basis is assumed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Module NumberField
open scoped MatrixOrder Matrix.Norms.L2Operator
namespace GeometricGaussianLHL

theorem AlgebraicRealInput.ValidFor.abs_le {I : AlgebraicRealInput} {x : ℝ}
    (hI : I.ValidFor x) : |x| ≤ (2 : ℝ) ^ I.endpointBits := by
  have hl : |(I.lower : ℝ)| ≤ (2 : ℝ) ^ I.endpointBits := by
    exact_mod_cast (I.refine_abs_le 0).1
  have hu : |(I.upper : ℝ)| ≤ (2 : ℝ) ^ I.endpointBits := by
    exact_mod_cast (I.refine_abs_le 0).2
  exact _root_.abs_le.mpr ⟨(_root_.abs_le.mp hl).1.trans hI.lower_le,
    hI.le_upper.trans (_root_.abs_le.mp hu).2⟩

theorem positiveMatrix_det_le_eigenvalue_mul {n : ℕ}
    (G : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosDef) {H : ℝ}
    (hH : 1 ≤ H) (hhi : ‖G‖ ≤ H) (i : Fin n) :
    G.det ≤ H ^ n * hG.isHermitian.eigenvalues i := by
  let : NeZero n := ⟨by have hi := i.isLt; omega⟩
  have he (j : Fin n) : hG.isHermitian.eigenvalues j ≤ H := by
    have hj := spectrum.norm_le_norm_of_mem (hG.isHermitian.eigenvalues_mem_spectrum_real j)
    rw [Real.norm_eq_abs, abs_of_pos (hG.eigenvalues_pos j)] at hj
    exact hj.trans hhi
  have hp : (∏ j ∈ Finset.univ.erase i, hG.isHermitian.eigenvalues j) ≤ H ^ n := by
    calc
      _ ≤ ∏ _j ∈ Finset.univ.erase i, H :=
        Finset.prod_le_prod (fun j _ => (hG.eigenvalues_pos j).le) (fun j _ => he j)
      _ = H ^ (n - 1) := by simp
      _ ≤ H ^ n := pow_le_pow_right₀ hH (Nat.sub_le _ _)
  calc
    G.det = (∏ j ∈ Finset.univ.erase i, hG.isHermitian.eigenvalues j) *
        hG.isHermitian.eigenvalues i := by
      rw [hG.isHermitian.det_eq_prod_eigenvalues]
      simpa using (Finset.prod_erase_mul Finset.univ hG.isHermitian.eigenvalues (Finset.mem_univ i)).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right hp (hG.eigenvalues_pos i).le

theorem positiveMatrix_inverse_bound_of_det {n : ℕ}
    (G : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosDef) (E : ℕ)
    (hdet : 1 ≤ G.det) (hnorm : ‖G‖ ≤ (2 : ℝ) ^ E) :
    ‖G⁻¹‖ ≤ (2 : ℝ) ^ (n * E) := by
  apply normalizedInverse_norm_le _ G hG
  intro i
  have hi := hdet.trans (positiveMatrix_det_le_eigenvalue_mul G hG
    (one_le_pow₀ (by norm_num)) hnorm i)
  rw [← pow_mul, Nat.mul_comm E n] at hi
  exact (div_le_iff₀ (by positivity)).mpr (by simpa only [mul_comm] using hi)

theorem positiveMatrix_sqrt_norm_bound {n : ℕ}
    (G : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosSemidef) (E : ℕ)
    (hnorm : ‖G‖ ≤ (2 : ℝ) ^ E) : ‖CFC.sqrt G‖ ≤ (2 : ℝ) ^ E := by
  rw [CFC.norm_sqrt G hG.nonneg]
  apply Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
  exact hnorm.trans (by nlinarith [one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) (n := E)])

theorem positiveMatrix_inverse_sqrt_norm_bound {n : ℕ}
    (G : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosDef) (E : ℕ)
    (hnorm : ‖G⁻¹‖ ≤ (2 : ℝ) ^ E) : ‖(CFC.sqrt G)⁻¹‖ ≤ (2 : ℝ) ^ E := by
  rw [hG.posSemidef.inv_sqrt]
  exact positiveMatrix_sqrt_norm_bound G⁻¹ hG.posSemidef.inv E hnorm

theorem matrix_norm_bound_of_entry_bits {n : ℕ}
    (G : Matrix (Fin n) (Fin n) ℝ) (E : ℕ) (hG : ∀ i j, |G i j| ≤ (2 : ℝ) ^ E) :
    ‖G‖ ≤ (2 : ℝ) ^ (n + E) := by
  change ‖(Matrix.toEuclideanLin G).toContinuousLinearMap‖ ≤ _
  apply (euclideanMatrix_opNorm_le_entries G (by positivity) hG).trans
  rw [pow_add]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast (Nat.lt_two_pow_self (n := n)).le) (by positivity)

theorem canonicalGram_det_ge_one (K : Type*) [Field K] [NumberField K]
    {n : ℕ} (b : Basis (Fin n) ℤ (𝓞 K)) : 1 ≤ (canonicalGram K b).det := by
  have hp := (canonicalGram_posDef K b).det_pos
  rw [canonicalGram_det] at hp ⊢
  have hz : (0 : ℤ) < |NumberField.discr K| := by exact_mod_cast hp
  exact_mod_cast (show (1 : ℤ) ≤ |NumberField.discr K| by omega)

/-- Dimension and total lengths of the finite entry encodings. -/
def algebraicMatrixDataSize {n : ℕ} (I : Matrix (Fin n) (Fin n) AlgebraicRealInput) : ℕ :=
  n + 1 + ∑ i, ∑ j, (I i j).encode.length

theorem algebraicMatrixDataSize_entry {n : ℕ}
    (I : Matrix (Fin n) (Fin n) AlgebraicRealInput) (i j : Fin n) :
    (I i j).encode.length ≤ algebraicMatrixDataSize I := by
  have h := (Finset.single_le_sum (fun k _ => Nat.zero_le (I i k).encode.length) (Finset.mem_univ j)).trans
    (Finset.single_le_sum (fun k _ => Nat.zero_le (∑ l, (I k l).encode.length)) (Finset.mem_univ i))
  unfold algebraicMatrixDataSize
  omega

def algebraicMetricConditionExponent {n : ℕ}
    (I : Matrix (Fin n) (Fin n) AlgebraicRealInput) : ℕ :=
  (n + 1) * (n + algebraicMatrixDataSize I)

theorem canonicalGram_encoded_conditioning (K : Type*) [Field K] [NumberField K]
    {n : ℕ} (b : Basis (Fin n) ℤ (𝓞 K))
    (I : Matrix (Fin n) (Fin n) AlgebraicRealInput)
    (hI : ∀ i j, (I i j).ValidFor (canonicalGram K b i j)) :
    let h := algebraicMetricConditionExponent I
    ‖canonicalGram K b‖ ≤ (2 : ℝ) ^ h ∧
    ‖(canonicalGram K b)⁻¹‖ ≤ (2 : ℝ) ^ h ∧
    ‖CFC.sqrt (canonicalGram K b)‖ ≤ (2 : ℝ) ^ h ∧
    ‖(CFC.sqrt (canonicalGram K b))⁻¹‖ ≤ (2 : ℝ) ^ h := by
  have he (i j : Fin n) : |canonicalGram K b i j| ≤ (2 : ℝ) ^ algebraicMatrixDataSize I :=
    (hI i j).abs_le.trans (pow_le_pow_right₀ (by norm_num)
      ((I i j).endpointBits_le.trans ((I i j).inputSize_le_encode_length.trans
        (algebraicMatrixDataSize_entry I i j))))
  have hn := matrix_norm_bound_of_entry_bits _ _ he
  have hi := positiveMatrix_inverse_bound_of_det _ (canonicalGram_posDef K b) _
    (canonicalGram_det_ge_one K b) hn
  have hn' : ‖canonicalGram K b‖ ≤ (2 : ℝ) ^ algebraicMetricConditionExponent I := hn.trans
    (pow_le_pow_right₀ (by norm_num) (by unfold algebraicMetricConditionExponent; nlinarith))
  have hi' : ‖(canonicalGram K b)⁻¹‖ ≤ (2 : ℝ) ^ algebraicMetricConditionExponent I := hi.trans
    (pow_le_pow_right₀ (by norm_num) (by unfold algebraicMetricConditionExponent; nlinarith))
  exact ⟨hn', hi', positiveMatrix_sqrt_norm_bound _ (canonicalGram_posDef K b).posSemidef _ hn',
    positiveMatrix_inverse_sqrt_norm_bound _ (canonicalGram_posDef K b) _ hi'⟩

end GeometricGaussianLHL
end

end CanonicalMetricConditioning

section ScalarGramShaping

/-!
## Rational shaping in explicit scalar-Gram number-field coordinates

The algorithm takes the integer coefficient matrix as a rational matrix. Its
output is interpreted in the normalized integral basis, and then transported
to the canonical coordinates used by the ring-Gaussian theorems. No entries
of the arbitrary chosen orthonormal basis are part of the algorithm input.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Module NumberField
open scoped MatrixOrder Matrix.Norms.L2Operator

namespace GeometricGaussianLHL

def integerRationalMatrix {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℤ) :
    Matrix (Fin p) (Fin q) ℚ := A.map (Int.castRingHom ℚ)

theorem integerRationalMatrix_real {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℤ) :
    (integerRationalMatrix A).map (Rat.castHom ℝ) = A.map (Int.cast : ℤ → ℝ) := by
  ext i j
  simp [integerRationalMatrix]

theorem integerRationalMatrix_realMap {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℤ) :
    (Matrix.toEuclideanLin ((integerRationalMatrix A).map (Rat.castHom ℝ))).toContinuousLinearMap =
      (realCoefficientMap A).toContinuousLinearMap := by
  rw [integerRationalMatrix_real]
  rfl

theorem integerRationalMatrix_gram_isUnit {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℤ)
    (hA : Function.Surjective (realCoefficientMap A)) :
    IsUnit (integerRationalMatrix A * (integerRationalMatrix A).transpose).det := by
  have hpos := Real.sqrt_pos.mp (gramDet_pos A hA)
  have hmap : (Rat.castHom ℝ).mapMatrix
      (integerRationalMatrix A * (integerRationalMatrix A).transpose) =
      A.map (Int.cast : ℤ → ℝ) * A.transpose.map (Int.cast : ℤ → ℝ) := by
    change (integerRationalMatrix A * (integerRationalMatrix A).transpose).map (Rat.castHom ℝ) = _
    rw [Matrix.map_mul, integerRationalMatrix_real]
    congr 1
  apply isUnit_iff_ne_zero.mpr
  intro hz
  have he := congrArg (Rat.castHom ℝ) hz
  rw [map_zero, (Rat.castHom ℝ).map_det, hmap] at he
  exact hpos.ne' he

variable (K : Type*) [Field K] [NumberField K] {d r m : ℕ}

omit [NumberField K] in
theorem ringCoefficientMatrix_rational_gram_isUnit (b : Basis (Fin d) ℤ (𝓞 K))
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) (hX : Function.Surjective X.mulVec) :
    IsUnit (integerRationalMatrix (ringCoefficientMatrix b X) *
      (integerRationalMatrix (ringCoefficientMatrix b X)).transpose).det :=
  integerRationalMatrix_gram_isUnit _ (realCoefficientMap_surjective_of_integer_surjective _
    ((ringCoefficientMatrix_surjective_iff b X).mpr hX))

def scalarGramShapingShape (b : Basis (Fin d) ℤ (𝓞 K)) {c : ℝ} (hc : 0 < c)
    (hGram : ∀ i j, canonicalGram K b i j = if i = j then c else 0)
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) (hX : Function.Surjective X.mulVec)
    (hr : 0 < r) (w : ℚ) (hw : 0 < w) : Euclidean (m * d) ≃L[ℝ] Euclidean (m * d) :=
  isometricTransportShape (scalarGramEuclideanIsometry K b hc hGram m)
    (rationalShapingShape (integerRationalMatrix (ringCoefficientMatrix b X)) w
      (Nat.mul_pos hr (integralBasis_dimension_pos K b))
      (ringCoefficientMatrix_rational_gram_isUnit K b X hX) hw)

theorem scalarGramShapingShape_positive (b : Basis (Fin d) ℤ (𝓞 K)) {c : ℝ} (hc : 0 < c)
    (hGram : ∀ i j, canonicalGram K b i j = if i = j then c else 0)
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) (hX : Function.Surjective X.mulVec)
    (hr : 0 < r) (w : ℚ) (hw : 0 < w) :
    (scalarGramShapingShape K b hc hGram X hX hr w hw).toLinearMap.IsPositive :=
  (LinearMap.isPositive_linearIsometryEquiv_conj_iff (scalarGramEuclideanIsometry K b hc hGram m)).mpr
    (positiveSquareRootShape_positive _ _)

theorem scalarGramShapingShape_covariance (b : Basis (Fin d) ℤ (𝓞 K)) {c : ℝ} (hc : 0 < c)
    (hGram : ∀ i j, canonicalGram K b i j = if i = j then c else 0)
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) (hX : Function.Surjective X.mulVec)
    (hr : 0 < r) (w : ℚ) (hw : 0 < w) :
    gaussianPushforwardCovariance (canonicalEuclideanMatrix K b X).toContinuousLinearMap
      (scalarGramShapingShape K b hc hGram X hX hr w hw) =
      (w : ℝ) ^ 2 • ContinuousLinearMap.id ℝ (Euclidean (r * d)) := by
  rw [canonicalEuclideanMatrix_scalarGram_transport K b hc hGram, scalarGramShapingShape]
  apply isometricTransportShape_spherical_covariance
  rw [← integerRationalMatrix_realMap]
  exact rationalShapingShape_image_covariance _ w _ _ hw

theorem scalarGramShapingShape_minimumStretch (b : Basis (Fin d) ℤ (𝓞 K))
    {c : ℝ} (hc : 0 < c) (hGram : ∀ i j, canonicalGram K b i j = if i = j then c else 0)
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) (hX : Function.Surjective X.mulVec)
    (hr : 0 < r) (w : ℚ) (hw : 0 < w) :
    shapeMinimumStretch (scalarGramShapingShape K b hc hGram X hX hr w hw) =
      (w : ℝ) / ‖(canonicalEuclideanMatrix K b X).toContinuousLinearMap‖ := by
  rw [scalarGramShapingShape, isometricTransportShape_minimumStretch,
    canonicalEuclideanMatrix_scalarGram_norm K b hc hGram]
  simpa only [integerRationalMatrix_realMap] using
    (rationalShapingShape_extrema (integerRationalMatrix (ringCoefficientMatrix b X)) w
      (Nat.mul_pos hr (integralBasis_dimension_pos K b))
      (ringCoefficientMatrix_rational_gram_isUnit K b X hX) hw).1

end GeometricGaussianLHL
end

end ScalarGramShaping

section CanonicalMetricApproximation

/-!
## Numerical metric conversion for the actual canonical matrix

The rational metric-normalization formula approximates the actual canonical
Gram-normalized matrix. The integer coefficient matrix is supplied through
the integral-basis coordinates. Computing those coordinates and the metric
from another field presentation still requires an input model and cost proof.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Module NumberField
open scoped MatrixOrder Matrix.Norms.L2Operator

namespace GeometricGaussianLHL

variable (K : Type*) [Field K] [NumberField K] {d r m : ℕ}

theorem canonicalGramRootMatrix_inverse (b : Basis (Fin d) ℤ (𝓞 K)) (n : ℕ) :
    (canonicalGramRootMatrix K b n)⁻¹ =
      repeatedEuclideanMatrix n (CFC.sqrt (canonicalGram K b))⁻¹ := by
  apply Matrix.toEuclideanLin.injective
  rw [canonicalGramRootMatrix_inv_operator]
  have he := repeatedEuclideanMatrix_equiv n
    (positiveSquareRootShape (canonicalGram K b) (canonicalGram_posDef K b)).symm
  rw [euclideanEquiv_matrix_symm, positiveSquareRootShape_matrix] at he
  rw [he]
  ext x : 1
  change (euclideanBlocks n d).symm
    ((repeatedContinuousEquiv (positiveSquareRootShape (canonicalGram K b) (canonicalGram_posDef K b)) n).symm
      (euclideanBlocks n d x)) = _
  rw [repeatedContinuousEquiv_symm]
  rfl

theorem canonicalGramNormalizedMatrix_metric (b : Basis (Fin d) ℤ (𝓞 K))
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) :
    canonicalGramNormalizedMatrix K b X =
      metricNormalizedMatrix (canonicalGram K b) ((ringCoefficientMatrix b X).map (Int.cast : ℤ → ℝ)) := by
  rw [canonicalGramNormalizedMatrix, canonicalGramRootMatrix_inverse]
  rfl

theorem rationalMetricNormalizedApprox_canonical_error (b : Basis (Fin d) ℤ (𝓞 K))
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) (t c : ℕ) (H : Matrix (Fin d) (Fin d) ℚ)
    (hH : (H.map (Rat.castHom ℝ)).PosDef)
    (hGroot : ‖CFC.sqrt (canonicalGram K b)‖ ≤ (2 : ℝ) ^ c)
    (hGinvroot : ‖(CFC.sqrt (canonicalGram K b))⁻¹‖ ≤ (2 : ℝ) ^ c)
    (hHroot : ‖CFC.sqrt (H.map (Rat.castHom ℝ))‖ ≤ (2 : ℝ) ^ c)
    (hHinvroot : ‖(CFC.sqrt (H.map (Rat.castHom ℝ)))⁻¹‖ ≤ (2 : ℝ) ^ c)
    (hGi : ‖(canonicalGram K b)⁻¹‖ ≤ (2 : ℝ) ^ c)
    (hHi : ‖(H.map (Rat.castHom ℝ))⁻¹‖ ≤ (2 : ℝ) ^ c)
    (hC : ‖(ringCoefficientMatrix b X).map (Int.cast : ℤ → ℝ)‖ ≤ (2 : ℝ) ^ c)
    (hmetric : ‖H.map (Rat.castHom ℝ) - canonicalGram K b‖ ≤
      1 / (2 : ℝ) ^ (2 * (t + 2 * c + 3) + 2 * c)) :
    ‖(rationalMetricNormalizedApprox (t + 2 * c + 3) H
        ((ringCoefficientMatrix b X).map (Int.castRingHom ℚ))).map (Rat.castHom ℝ) -
      canonicalGramNormalizedMatrix K b X‖ ≤ 1 / (2 : ℝ) ^ t := by
  have hcast : ((ringCoefficientMatrix b X).map (Int.castRingHom ℚ)).map (Rat.castHom ℝ) =
      (ringCoefficientMatrix b X).map (Int.cast : ℤ → ℝ) := by
    ext i j
    simp
  rw [canonicalGramNormalizedMatrix_metric]
  have hC' : ‖((ringCoefficientMatrix b X).map (Int.castRingHom ℚ)).map (Rat.castHom ℝ)‖ ≤ (2 : ℝ) ^ c := by
    simpa only [hcast] using hC
  simpa only [hcast] using rationalMetricNormalizedApprox_real_target t c (canonicalGram K b) H _
    (canonicalGram_posDef K b) hH hGroot hGinvroot hHroot hHinvroot hGi hHi hC' hmetric

end GeometricGaussianLHL
end

end CanonicalMetricApproximation

section CanonicalGramShaping

/-!
## Trace-average shaping for general canonical number-field geometry

The shape is the real numerical target in Gram-normalized coordinates,
transported isometrically to the canonical ring lattice. Its widths and
Gaussian image apply to every integral basis, without a scalar-Gram promise.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Module NumberField
open scoped MatrixOrder Matrix.Norms.L2Operator

namespace GeometricGaussianLHL

theorem realMatrix_gram_isUnit_of_surjective {p q : ℕ}
    (A : Matrix (Fin p) (Fin q) ℝ) (hA : Function.Surjective (Matrix.toEuclideanLin A)) :
    IsUnit (A * A.transpose).det := by
  have hp := gaussianGramMatrix_posDef (Matrix.toEuclideanLin A).toContinuousLinearMap hA
  have he : gaussianGramMatrix (Matrix.toEuclideanLin A).toContinuousLinearMap = A * A.transpose := by
    rw [gaussianGramMatrix]
    change (Matrix.toLpLin 2 2).symm
      ((Matrix.toEuclideanLin A).comp (Matrix.toEuclideanLin A).adjoint) = _
    rw [Matrix.toLpLin_symm_comp, euclideanMatrix_adjoint, LinearEquiv.symm_apply_apply]
    rfl
  rw [he] at hp
  exact (Matrix.isUnit_iff_isUnit_det _).mp hp.isUnit

variable (K : Type*) [Field K] [NumberField K] {d r m : ℕ}

theorem canonicalGramNormalizedMatrix_gram_isUnit (b : Basis (Fin d) ℤ (𝓞 K))
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) (hX : Function.Surjective X.mulVec) :
    IsUnit (canonicalGramNormalizedMatrix K b X * (canonicalGramNormalizedMatrix K b X).transpose).det :=
  realMatrix_gram_isUnit_of_surjective _ (canonicalGramNormalizedMatrix_surjective K b X hX)

def canonicalGramShapingShape (b : Basis (Fin d) ℤ (𝓞 K))
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) (hX : Function.Surjective X.mulVec)
    (hr : 0 < r) (w : ℝ) (hw : 0 < w) : Euclidean (m * d) ≃L[ℝ] Euclidean (m * d) :=
  isometricTransportShape (canonicalGramEuclideanIsometry K b m)
    (realShapingShape (canonicalGramNormalizedMatrix K b X) w
      (Nat.mul_pos hr (integralBasis_dimension_pos K b))
      (canonicalGramNormalizedMatrix_gram_isUnit K b X hX) hw)

theorem canonicalGramShapingShape_positive (b : Basis (Fin d) ℤ (𝓞 K))
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) (hX : Function.Surjective X.mulVec)
    (hr : 0 < r) (w : ℝ) (hw : 0 < w) :
    (canonicalGramShapingShape K b X hX hr w hw).toLinearMap.IsPositive :=
  (LinearMap.isPositive_linearIsometryEquiv_conj_iff (canonicalGramEuclideanIsometry K b m)).mpr
    (realShapingShape_positive _ _ _ _ _)

theorem canonicalGramShapingShape_covariance (b : Basis (Fin d) ℤ (𝓞 K))
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) (hX : Function.Surjective X.mulVec)
    (hr : 0 < r) (w : ℝ) (hw : 0 < w) :
    gaussianPushforwardCovariance (canonicalEuclideanMatrix K b X).toContinuousLinearMap
      (canonicalGramShapingShape K b X hX hr w hw) =
      w ^ 2 • ContinuousLinearMap.id ℝ (Euclidean (r * d)) := by
  rw [canonicalEuclideanMatrix_gram_transport, canonicalGramShapingShape]
  apply isometricTransportShape_spherical_covariance
  exact realShapingShape_image_covariance _ _ _ _ _

theorem canonicalGramShapingShape_minimumStretch (b : Basis (Fin d) ℤ (𝓞 K))
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) (hX : Function.Surjective X.mulVec)
    (hr : 0 < r) (w : ℝ) (hw : 0 < w) :
    shapeMinimumStretch (canonicalGramShapingShape K b X hX hr w hw) =
      w / ‖(canonicalEuclideanMatrix K b X).toContinuousLinearMap‖ := by
  rw [canonicalGramShapingShape, isometricTransportShape_minimumStretch, canonicalEuclideanMatrix_gram_norm]
  exact (realShapingShape_extrema _ _ _ _ _).1

theorem canonicalGramShapingShape_norm (b : Basis (Fin d) ℤ (𝓞 K))
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) (hX : Function.Surjective X.mulVec)
    (hr : 0 < r) (w : ℝ) (hw : 0 < w) :
    ‖(canonicalGramShapingShape K b X hX hr w hw).toContinuousLinearMap‖ =
      w / kernelMinimumStretch (canonicalEuclideanMatrix K b X)
        (canonicalEuclideanMatrix_surjective K b X hX) := by
  have hA := canonicalGramNormalizedMatrix_surjective K b X hX
  have hmin := isometricTransportMap_kernelMinimumStretch
    (canonicalGramEuclideanIsometry K b m) (canonicalGramEuclideanIsometry K b r)
    (Matrix.toEuclideanLin (canonicalGramNormalizedMatrix K b X)).toContinuousLinearMap hA
  have hmin' : kernelMinimumStretch (canonicalEuclideanMatrix K b X)
      (canonicalEuclideanMatrix_surjective K b X hX) =
      kernelMinimumStretch (Matrix.toEuclideanLin (canonicalGramNormalizedMatrix K b X)) hA := by
    simpa only [← canonicalEuclideanMatrix_gram_transport K b,
      LinearMap.coe_toContinuousLinearMap] using hmin
  rw [canonicalGramShapingShape, isometricTransportShape_norm, hmin']
  exact (realShapingShape_extrema _ _ _ _ _).2

theorem canonicalGramShapingShape_gaussian_pushforward (b : Basis (Fin d) ℤ (𝓞 K))
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) (hX : Function.Surjective X.mulVec)
    (hr : 0 < r) (w : ℝ) (hw : 0 < w) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hwidth : smoothingParameter (canonicalKernel K X) ε *
      ‖(canonicalEuclideanMatrix K b X).toContinuousLinearMap‖ ≤ w) (z : Fin m → 𝓞 K) :
    discreteTotalVariation
      ((numberFieldEllipsoidalGaussian K b m (canonicalGramShapingShape K b X hX hr w hw) z).map X.mulVec)
      ((numberFieldGaussian K b r w hw.ne').map (Equiv.addRight (X.mulVec z))) ≤ ε / (1 - ε) := by
  let : NeZero (r * d) := ⟨(Nat.mul_pos hr (integralBasis_dimension_pos K b)).ne'⟩
  have hn := surjective_operator_norm_pos (canonicalEuclideanMatrix K b X).toContinuousLinearMap
    (canonicalEuclideanMatrix_surjective K b X hX)
  apply numberField_gaussian_spherical_pushforward_of_shape K b X hX _ hw hε hε1 _
    (canonicalGramShapingShape_covariance K b X hX hr w hw) z
  rw [canonicalGramShapingShape_minimumStretch]
  exact (le_div_iff₀ hn).mpr hwidth

end GeometricGaussianLHL
end

end CanonicalGramShaping

section ScalarGramShapingCertificate

/-! # Computed approximations and ring-Gaussian guarantees for scalar-Gram shaping -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Module NumberField
open scoped MatrixOrder Matrix.Norms.L2Operator

namespace GeometricGaussianLHL

variable (K : Type*) [Field K] [NumberField K] {d r m : ℕ}

theorem scalarGramShapingShape_norm (b : Basis (Fin d) ℤ (𝓞 K))
    {c : ℝ} (hc : 0 < c) (hGram : ∀ i j, canonicalGram K b i j = if i = j then c else 0)
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) (hX : Function.Surjective X.mulVec)
    (hr : 0 < r) (w : ℚ) (hw : 0 < w) :
    ‖(scalarGramShapingShape K b hc hGram X hX hr w hw).toContinuousLinearMap‖ =
      (w : ℝ) / kernelMinimumStretch (canonicalEuclideanMatrix K b X)
        (canonicalEuclideanMatrix_surjective K b X hX) := by
  have hA := realCoefficientMap_surjective_of_integer_surjective _
    ((ringCoefficientMatrix_surjective_iff b X).mpr hX)
  have hmin := isometricTransportMap_kernelMinimumStretch
    (scalarGramEuclideanIsometry K b hc hGram m)
    (scalarGramEuclideanIsometry K b hc hGram r)
    (realCoefficientMap (ringCoefficientMatrix b X)).toContinuousLinearMap hA
  have hmin' : kernelMinimumStretch (canonicalEuclideanMatrix K b X)
      (canonicalEuclideanMatrix_surjective K b X hX) =
      kernelMinimumStretch (realCoefficientMap (ringCoefficientMatrix b X)) hA := by
    simpa only [← canonicalEuclideanMatrix_scalarGram_transport K b hc hGram,
      LinearMap.coe_toContinuousLinearMap] using hmin
  rw [scalarGramShapingShape, isometricTransportShape_norm, hmin']
  simpa only [integerRationalMatrix_realMap, LinearMap.coe_toContinuousLinearMap] using
    (rationalShapingShape_extrema (integerRationalMatrix (ringCoefficientMatrix b X)) w
      (Nat.mul_pos hr (integralBasis_dimension_pos K b))
      (ringCoefficientMatrix_rational_gram_isUnit K b X hX) hw).2

theorem scalarGramShapingShape_approximation_certificate
    (d r m : ℕ) (b : Basis (Fin d) ℤ (𝓞 K)) (c : ℝ) (hc : 0 < c)
      (hGram : ∀ i j, canonicalGram K b i j = if i = j then c else 0)
      (X : Matrix (Fin r) (Fin m) (𝓞 K)) (hX : Function.Surjective X.mulVec)
      (hr : 0 < r) (w : ℚ) (hw : 0 < w) (t : ℕ) :
      let A := integerRationalMatrix (ringCoefficientMatrix b X)
      let e := scalarGramEuclideanIsometry K b hc hGram m
      let S := scalarGramShapingShape K b hc hGram X hX hr w hw
      let R := (rationalShapingApprox t A w).map (Rat.castHom ℝ)
      R.PosDef ∧ ‖isometricTransportMap e e (Matrix.toEuclideanLin R).toContinuousLinearMap -
        S.toContinuousLinearMap‖ ≤ 1 / (2 : ℝ) ^ t := by
  dsimp only
  let A := integerRationalMatrix (ringCoefficientMatrix b X)
  have hA := ringCoefficientMatrix_rational_gram_isUnit K b X hX
  have hp := Nat.mul_pos hr (integralBasis_dimension_pos K b)
  refine ⟨rationalShapingApprox_posDef t A w hp hA hw.ne', ?_⟩
  rw [scalarGramShapingShape, isometricTransportShape_error]
  exact rationalShapingApprox_operator_error t A w hp hA hw.ne'

theorem scalarGramShapingShape_gaussian_pushforward (b : Basis (Fin d) ℤ (𝓞 K))
    {c : ℝ} (hc : 0 < c) (hGram : ∀ i j, canonicalGram K b i j = if i = j then c else 0)
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) (hX : Function.Surjective X.mulVec)
    (hr : 0 < r) (w : ℚ) (hw : 0 < w) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hwidth : smoothingParameter (canonicalKernel K X) ε *
      ‖(canonicalEuclideanMatrix K b X).toContinuousLinearMap‖ ≤ (w : ℝ))
    (z : Fin m → 𝓞 K) :
    discreteTotalVariation
      ((numberFieldEllipsoidalGaussian K b m (scalarGramShapingShape K b hc hGram X hX hr w hw) z).map
        X.mulVec)
      ((numberFieldGaussian K b r (w : ℝ) (by exact_mod_cast hw.ne')).map
        (Equiv.addRight (X.mulVec z))) ≤ ε / (1 - ε) := by
  let : NeZero (r * d) := ⟨(Nat.mul_pos hr (integralBasis_dimension_pos K b)).ne'⟩
  have hnorm := surjective_operator_norm_pos (canonicalEuclideanMatrix K b X).toContinuousLinearMap
    (canonicalEuclideanMatrix_surjective K b X hX)
  apply numberField_gaussian_spherical_pushforward_of_shape K b X hX _
    (by exact_mod_cast hw) hε hε1 _ (scalarGramShapingShape_covariance K b hc hGram X hX hr w hw) z
  rw [scalarGramShapingShape_minimumStretch]
  exact (le_div_iff₀ hnorm).mpr hwidth

end GeometricGaussianLHL
end

end ScalarGramShapingCertificate

section ApproximateShapingGaussian

/-!
## Gaussian guarantees from actual shape approximation

Absolute operator error is converted to relative precision using the inverse
of the exact shape. The resulting bound applies to normalized lattice and
ring Gaussian laws and to the spherical image of the computed shape.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Module NumberField
open scoped MatrixOrder Matrix.Norms.L2Operator

namespace GeometricGaussianLHL

theorem discreteTotalVariation_map_le {α β : Type*} (p q : PMF α) (f : α → β) :
    discreteTotalVariation (p.map f) (q.map f) ≤ discreteTotalVariation p q := by
  classical
  have hm (p : PMF α) (b : β) :
      ((p.map f) b).toReal = ∑' a : f ⁻¹' {b}, (p a).toReal := by
    rw [PMF.map_apply, ENNReal.tsum_toReal_eq]
    · rw [tsum_subtype (f ⁻¹' {b}) (fun a => (p a).toReal)]
      apply tsum_congr
      intro a
      by_cases ha : b = f a <;> simp [ha, eq_comm, Set.indicator]
    · intro a
      split_ifs <;> simp [p.apply_ne_top]
  have hs := (pmf_summable_abs_sub p q).hasSum.tsum_fiberwise f
  have hb (b : β) : |((p.map f) b).toReal - ((q.map f) b).toReal| ≤
      ∑' a : f ⁻¹' {b}, |(p a).toReal - (q a).toReal| := by
    have hp : Summable (fun a : f ⁻¹' {b} => (p a).toReal) := (pmf_summable_toReal p).subtype _
    have hq : Summable (fun a : f ⁻¹' {b} => (q a).toReal) := (pmf_summable_toReal q).subtype _
    rw [hm, hm, ← hp.tsum_sub hq]
    simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm
      (hp.sub hq).norm
  have h := (pmf_summable_abs_sub (p.map f) (q.map f)).tsum_le_tsum hb hs.summable
  rw [hs.tsum_eq] at h
  exact div_le_div_of_nonneg_right h (by norm_num)

section OperatorError

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Reversing the comparison uses only the exact shape's inverse norm. -/
theorem relativePrecision_shape_error (S T : E ≃L[ℝ] E) {δ : ℝ}
    (herr : ‖T.toContinuousLinearMap - S.toContinuousLinearMap‖ ≤ δ) :
    ‖relativePrecision T S‖ ≤ 2 * (‖S.symm.toContinuousLinearMap‖ * δ) +
      (‖S.symm.toContinuousLinearMap‖ * δ) ^ 2 := by
  let D := S.symm.toContinuousLinearMap.comp (T.toContinuousLinearMap - S.toContinuousLinearMap)
  have hD : ‖D‖ ≤ ‖S.symm.toContinuousLinearMap‖ * δ :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left herr (norm_nonneg _))
  have hTS : S.symm.toContinuousLinearMap.comp T.toContinuousLinearMap = ContinuousLinearMap.id ℝ E + D := by
    ext x
    simp [D]
  have he : relativePrecision T S = D.adjoint + D + D.adjoint.comp D := by
    rw [relativePrecision_eq_relative_gram, hTS]
    simp only [map_add, ContinuousLinearMap.adjoint_id, ContinuousLinearMap.add_comp,
      ContinuousLinearMap.comp_add, ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id]
    abel
  calc
    _ ≤ (‖D‖ + ‖D‖) + ‖D‖ * ‖D‖ := by
      rw [he]
      simpa only [LinearIsometryEquiv.norm_map, ContinuousLinearMap.norm_adjoint_comp_self] using
        (norm_add_le (D.adjoint + D) (D.adjoint.comp D)).trans
          (add_le_add (norm_add_le D.adjoint D) le_rfl)
    _ = 2 * ‖D‖ + ‖D‖ ^ 2 := by ring
    _ ≤ _ := by gcongr

end OperatorError

theorem latticeGaussian_shape_error {n : ℕ} (L : Submodule ℤ (Euclidean n))
    [DiscreteTopology L] [IsZLattice ℝ L] (S T : Euclidean n ≃L[ℝ] Euclidean n)
    {δ τ : ℝ} (hδ : 0 ≤ δ) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (herr : ‖T.toContinuousLinearMap - S.toContinuousLinearMap‖ ≤ δ)
    (hprec : 3 * (‖S.symm.toContinuousLinearMap‖ * δ) ≤ gaussianTargetPrecision n τ) :
    discreteTotalVariation (latticeGaussian L T) (latticeGaussian L S) ≤ τ := by
  have hb := (gaussianTargetPrecision_admissible (n := n) hτ hτ1).2.2.2
  have hnonneg : 0 ≤ ‖S.symm.toContinuousLinearMap‖ * δ := mul_nonneg (norm_nonneg _) hδ
  have hsmall : ‖S.symm.toContinuousLinearMap‖ * δ ≤ 1 := by linarith
  have hsq := mul_nonneg hnonneg (sub_nonneg.mpr hsmall)
  apply latticeGaussian_target_precision L T S hτ hτ1
  exact (relativePrecision_shape_error S T herr).trans (by nlinarith)

theorem gaussianTargetPrecision_dyadic_lower (n k : ℕ) :
    1 / (2 : ℝ) ^ (n + 2 * k + 16) ≤ gaussianTargetPrecision n (1 / (2 : ℝ) ^ k) := by
  have hlog : Real.log (256 / (1 / (2 : ℝ) ^ k)) = (k + 8) * Real.log 2 := by
    rw [div_div_eq_mul_div, div_one, Real.log_mul (by norm_num : (256 : ℝ) ≠ 0) (by positivity),
      Real.log_pow, show Real.log (256 : ℝ) = 8 * Real.log 2 by
        rw [show (256 : ℝ) = 2 ^ (8 : ℕ) by norm_num, Real.log_pow]; norm_num]
    ring
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hh : (n : ℝ) + Real.log (256 / (1 / (2 : ℝ) ^ k)) ≤ n + k + 8 := by
    rw [hlog]
    nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hpow : (n : ℝ) + k + 8 ≤ (2 : ℝ) ^ (n + k + 8) := by
    exact_mod_cast (show n + k + 8 < 2 ^ (n + k + 8) from Nat.lt_two_pow_self).le
  have hden : 256 * ((n : ℝ) + Real.log (256 / (1 / (2 : ℝ) ^ k))) ≤
      (2 : ℝ) ^ (n + k + 16) := by
    calc
      _ ≤ 256 * ((2 : ℝ) ^ (n + k + 8)) := mul_le_mul_of_nonneg_left (hh.trans hpow) (by norm_num)
      _ = _ := by rw [show n + k + 16 = n + k + 8 + 8 by omega, pow_add]; norm_num; ring
  have hτ1 : 1 / (2 : ℝ) ^ k ≤ 1 := (div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num))
  have hheight := gaussianTargetPrecision_height_ge_one (n := n) (by positivity : 0 < 1 / (2 : ℝ) ^ k) hτ1
  calc
    _ = (1 / (2 : ℝ) ^ k) / (2 : ℝ) ^ (n + k + 16) := by
      rw [show n + 2 * k + 16 = k + (n + k + 16) by omega, pow_add]
      ring
    _ ≤ gaussianTargetPrecision n (1 / (2 : ℝ) ^ k) :=
      div_le_div_of_nonneg_left (by positivity) (by linarith) hden

/-- A sufficient bit count for statistical error `2^-k` when the exact
inverse-shape norm is at most `2^h`. This budget is linear in `n,h,k`. -/
def gaussianShapeBits (n h k : ℕ) : ℕ := h + n + 2 * k + 18

theorem gaussianShapeBits_precision (n h k : ℕ) {η : ℝ} (hη : η ≤ (2 : ℝ) ^ h) :
    3 * (η * (1 / (2 : ℝ) ^ gaussianShapeBits n h k)) ≤
      gaussianTargetPrecision n (1 / (2 : ℝ) ^ k) := by
  calc
    _ ≤ 3 * ((2 : ℝ) ^ h * (1 / (2 : ℝ) ^ gaussianShapeBits n h k)) := by gcongr
    _ = (3 / 4 : ℝ) * (1 / (2 : ℝ) ^ (n + 2 * k + 16)) := by
      rw [gaussianShapeBits, show h + n + 2 * k + 18 = h + ((n + 2 * k + 16) + 2) by omega,
        pow_add, pow_add]
      field_simp
      ring
    _ ≤ 1 / (2 : ℝ) ^ (n + 2 * k + 16) := mul_le_of_le_one_left (by positivity) (by norm_num)
    _ ≤ _ := gaussianTargetPrecision_dyadic_lower n k

variable (K : Type*) [Field K] [NumberField K]

theorem numberFieldEllipsoidalGaussian_shape_error {d n : ℕ} (b : Basis (Fin d) ℤ (𝓞 K))
    (S T : Euclidean (n * d) ≃L[ℝ] Euclidean (n * d)) (z : Fin n → 𝓞 K)
    {δ τ : ℝ} (hδ : 0 ≤ δ) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (herr : ‖T.toContinuousLinearMap - S.toContinuousLinearMap‖ ≤ δ)
    (hprec : 3 * (‖S.symm.toContinuousLinearMap‖ * δ) ≤ gaussianTargetPrecision (n * d) τ) :
    discreteTotalVariation (numberFieldEllipsoidalGaussian K b n T z)
      (numberFieldEllipsoidalGaussian K b n S z) ≤ τ := by
  have he := discreteTotalVariation_map_equiv
    (latticeGaussianCentered (canonicalEuclideanLattice K b n) T (canonicalEuclideanLatticeEquiv K b n z))
    (latticeGaussianCentered (canonicalEuclideanLattice K b n) S (canonicalEuclideanLatticeEquiv K b n z))
    (canonicalEuclideanLatticeEquiv K b n).symm.toEquiv
  rw [latticeGaussianCentered_totalVariation] at he
  exact he.le.trans (latticeGaussian_shape_error _ S T hδ hτ hτ1 herr hprec)

/-- Interpret a positive-definite output matrix as an invertible shape,
without applying another square-root operation. -/
def positiveMatrixShape {n : ℕ} (R : Matrix (Fin n) (Fin n) ℝ) (hR : R.PosDef) :
    Euclidean n ≃L[ℝ] Euclidean n :=
  (LinearEquiv.ofBijective (Matrix.toEuclideanLin R) ((Module.End.isUnit_iff _).mp
    (hR.isUnit.map (Matrix.toLpLinAlgEquiv 2 : Matrix (Fin n) (Fin n) ℝ ≃ₐ[ℝ]
      Module.End ℝ (Euclidean n)).toMonoidHom))).toContinuousLinearEquiv

theorem positiveMatrixShape_map {n : ℕ} (R : Matrix (Fin n) (Fin n) ℝ) (hR : R.PosDef) :
    (positiveMatrixShape R hR).toContinuousLinearMap = (Matrix.toEuclideanLin R).toContinuousLinearMap := rfl

def canonicalComputedShape {d n : ℕ} (b : Basis (Fin d) ℤ (𝓞 K))
    (R : Matrix (Fin (n * d)) (Fin (n * d)) ℝ) (hR : R.PosDef) :
    Euclidean (n * d) ≃L[ℝ] Euclidean (n * d) :=
  isometricTransportShape (canonicalGramEuclideanIsometry K b n) (positiveMatrixShape R hR)

theorem canonicalComputedShape_map {d n : ℕ} (b : Basis (Fin d) ℤ (𝓞 K))
    (R : Matrix (Fin (n * d)) (Fin (n * d)) ℝ) (hR : R.PosDef) :
    (canonicalComputedShape K b R hR).toContinuousLinearMap =
      isometricTransportMap (canonicalGramEuclideanIsometry K b n) (canonicalGramEuclideanIsometry K b n)
        (Matrix.toEuclideanLin R).toContinuousLinearMap := rfl

theorem canonicalGramShapingShape_inverse_norm {d r m : ℕ} (b : Basis (Fin d) ℤ (𝓞 K))
    (A : Matrix (Fin r) (Fin m) (𝓞 K)) (hA : Function.Surjective A.mulVec)
    (hr : 0 < r) (w : ℝ) (hw : 0 < w) :
    ‖(canonicalGramShapingShape K b A hA hr w hw).symm.toContinuousLinearMap‖ =
      ‖(canonicalEuclideanMatrix K b A).toContinuousLinearMap‖ / w := by
  have h := canonicalGramShapingShape_minimumStretch K b A hA hr w hw
  simpa only [shapeMinimumStretch, inv_inv, inv_div] using congrArg (fun x : ℝ => x⁻¹) h

theorem canonicalComputedShape_gaussian {d r m : ℕ} (b : Basis (Fin d) ℤ (𝓞 K))
    (A : Matrix (Fin r) (Fin m) (𝓞 K)) (hA : Function.Surjective A.mulVec)
    (hr : 0 < r) (w : ℝ) (hw : 0 < w)
    (R : Matrix (Fin (m * d)) (Fin (m * d)) ℝ) (hR : R.PosDef)
    {δ τ ε : ℝ} (hδ : 0 ≤ δ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hε : 0 < ε) (hε1 : ε < 1)
    (herr : ‖isometricTransportMap (canonicalGramEuclideanIsometry K b m)
      (canonicalGramEuclideanIsometry K b m) (Matrix.toEuclideanLin R).toContinuousLinearMap -
      (canonicalGramShapingShape K b A hA hr w hw).toContinuousLinearMap‖ ≤ δ)
    (hprec : 3 * (‖(canonicalEuclideanMatrix K b A).toContinuousLinearMap‖ / w * δ) ≤
      gaussianTargetPrecision (m * d) τ)
    (hwidth : smoothingParameter (canonicalKernel K A) ε *
      ‖(canonicalEuclideanMatrix K b A).toContinuousLinearMap‖ ≤ w) (z : Fin m → 𝓞 K) :
    let T := canonicalComputedShape K b R hR
    discreteTotalVariation (numberFieldEllipsoidalGaussian K b m T z)
      (numberFieldEllipsoidalGaussian K b m (canonicalGramShapingShape K b A hA hr w hw) z) ≤ τ ∧
    discreteTotalVariation ((numberFieldEllipsoidalGaussian K b m T z).map A.mulVec)
      ((numberFieldGaussian K b r w hw.ne').map (Equiv.addRight (A.mulVec z))) ≤ τ + ε / (1 - ε) := by
  have hclose := numberFieldEllipsoidalGaussian_shape_error K b
    (canonicalGramShapingShape K b A hA hr w hw) (canonicalComputedShape K b R hR) z hδ hτ hτ1
    (by simpa only [canonicalComputedShape_map] using herr)
    (by simpa only [canonicalGramShapingShape_inverse_norm] using hprec)
  refine ⟨hclose, ?_⟩
  exact (discreteTotalVariation_triangle _
    ((numberFieldEllipsoidalGaussian K b m (canonicalGramShapingShape K b A hA hr w hw) z).map A.mulVec) _).trans
    (add_le_add ((discreteTotalVariation_map_le _ _ A.mulVec).trans hclose)
      (canonicalGramShapingShape_gaussian_pushforward K b A hA hr w hw hε hε1 hwidth z))

end GeometricGaussianLHL
end

end ApproximateShapingGaussian

section CanonicalGramShapingCertificate

/-! # Computed rational approximation in canonical Gram coordinates -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Module NumberField
open scoped MatrixOrder Matrix.Norms.L2Operator
namespace GeometricGaussianLHL
variable (K : Type*) [Field K] [NumberField K]

theorem canonicalGramShapingShape_approximation_certificate
    (d r m : ℕ) (b : Basis (Fin d) ℤ (𝓞 K))
      (X : Matrix (Fin r) (Fin m) (𝓞 K)) (hX : Function.Surjective X.mulVec)
      (hr : 0 < r) (w : ℝ) (hw : 0 < w) (t B : ℕ)
      (Q : Matrix (Fin (r * d)) (Fin (m * d)) ℚ) (v : ℚ) (hv : 0 < v)
      (hAn : ‖canonicalGramNormalizedMatrix K b X‖ ≤ (2 : ℝ) ^ B)
      (hAi : ‖(canonicalGramNormalizedMatrix K b X *
        (canonicalGramNormalizedMatrix K b X).transpose)⁻¹‖ ≤ (2 : ℝ) ^ B)
      (hwn : |w| ≤ (2 : ℝ) ^ B)
      (hinput : ‖canonicalGramNormalizedMatrix K b X - Q.map (Rat.castHom ℝ)‖ + |w - (v : ℝ)| ≤
        1 / (2 : ℝ) ^ (2 * (t + 1) + 11 * (B + 1) + 6)) :
      let e := canonicalGramEuclideanIsometry K b m
      let S := canonicalGramShapingShape K b X hX hr w hw
      let R := (rationalShapingApprox (t + 1) Q v).map (Rat.castHom ℝ)
      R.PosDef ∧
        ‖isometricTransportMap e e (Matrix.toEuclideanLin R).toContinuousLinearMap -
          S.toContinuousLinearMap‖ ≤ 1 / (2 : ℝ) ^ t := by
  dsimp only
  have hp := Nat.mul_pos hr (integralBasis_dimension_pos K b)
  have hA := canonicalGramNormalizedMatrix_gram_isUnit K b X hX
  have h := realShapingInput_approximation_certificate (r * d) (m * d) t B
    (canonicalGramNormalizedMatrix K b X) w Q v hp hA hw hv hAn hAi hwn hinput
  refine ⟨h.1, ?_⟩
  rw [canonicalGramShapingShape, isometricTransportShape_error]
  exact h.2.2

end GeometricGaussianLHL
end

end CanonicalGramShapingCertificate

section CanonicalInputBounds

/-! # Dyadic approximation and coefficient-dependent conditioning bounds

These are mathematical bounds reused by finite input preparation. Real floor
and ceiling establish existence only; the executable approximation procedure
is in `AlgebraicInput`. Its bit-cost analysis remains separate.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Module NumberField
open scoped MatrixOrder Matrix.Norms.L2Operator
namespace GeometricGaussianLHL
private theorem nat_size_le_of_pow {n b : ℕ} (h : n ≤ 2 ^ b) : n.size ≤ b + 1 := by
  apply Nat.size_le.mpr
  exact h.trans_lt (Nat.pow_lt_pow_right (by omega) (by omega))

private theorem exists_dyadic_bound (x : ℝ) : ∃ c : ℕ, x ≤ (2 : ℝ) ^ c := by
  obtain ⟨c, hc⟩ := exists_nat_ge x
  exact ⟨c, hc.trans (by exact_mod_cast (Nat.lt_two_pow_self (n := c)).le)⟩

private theorem exists_dyadic_error {ε : ℝ} (hε : 0 < ε) :
    ∃ q : ℕ, 1 / (2 : ℝ) ^ q ≤ ε := by
  obtain ⟨q, hq⟩ := exists_dyadic_bound (1 / ε)
  exact ⟨q, (one_div_le (by positivity) hε).mpr hq⟩

def realDyadicMatrixNumerators {n : ℕ} (q : ℕ) (G : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℤ := fun i j => ⌊G i j * (2 : ℝ) ^ q⌋

theorem realDyadicMatrix_entry_error {n : ℕ} (q : ℕ)
    (G : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    |((integerMatrixQuotient (2 ^ q) (realDyadicMatrixNumerators q G) i j : ℚ) : ℝ) - G i j| <
      1 / (2 : ℝ) ^ q := by
  have hp : 0 < (2 : ℝ) ^ q := by positivity
  have hlo := Int.floor_le (G i j * (2 : ℝ) ^ q)
  have hhi := Int.lt_floor_add_one (G i j * (2 : ℝ) ^ q)
  rw [integerMatrixQuotient_apply]
  dsimp only [realDyadicMatrixNumerators]
  push_cast
  rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr ((div_le_iff₀ hp).mpr hlo))]
  rw [sub_lt_iff_lt_add, ← add_div, lt_div_iff₀ hp]
  linarith

theorem realDyadicMatrix_isHermitian {n : ℕ} (q : ℕ)
    (G : Matrix (Fin n) (Fin n) ℝ) (hG : G.IsHermitian) :
    ((integerMatrixQuotient (2 ^ q) (realDyadicMatrixNumerators q G)).map (Rat.castHom ℝ)).IsHermitian := by
  have hsym := Matrix.isHermitian_iff_isSymm.mp hG
  apply Matrix.IsHermitian.ext
  intro i j
  simp only [Matrix.map_apply, integerMatrixQuotient_apply, realDyadicMatrixNumerators, star_trivial]
  rw [hsym.apply]

theorem realDyadicMatrix_operator_error {n : ℕ} (q : ℕ)
    (G : Matrix (Fin n) (Fin n) ℝ) :
    ‖(integerMatrixQuotient (2 ^ q) (realDyadicMatrixNumerators q G)).map (Rat.castHom ℝ) - G‖ ≤
      (n : ℝ) * (1 / (2 : ℝ) ^ q) := by
  rw [euclideanMatrix_norm_sub_CLM]
  exact euclideanMatrix_opNorm_sub_le_entries _ _ (by positivity)
    (fun i j => (realDyadicMatrix_entry_error q G i j).le)

theorem exists_positive_dyadic_metric {n : ℕ} (hn : 0 < n)
    (G : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosDef) {H : ℝ}
    (hH : 0 < H) (hinv : ‖G⁻¹‖ ≤ H) :
    ∃ s : ℕ, ∀ t : ℕ,
      let R := (integerMatrixQuotient (2 ^ (t + s))
        (realDyadicMatrixNumerators (t + s) G)).map (Rat.castHom ℝ)
      R.PosDef ∧ ‖R⁻¹‖ ≤ 2 * H ∧ ‖R - G‖ ≤ 1 / (2 : ℝ) ^ t := by
  let : NeZero n := ⟨hn.ne'⟩
  obtain ⟨δ, hδ, hgap⟩ := (CFC.exists_pos_algebraMap_le_iff G hG.isHermitian).mpr
    (fun _ hx => hG.isStrictlyPositive.spectrum_pos hx)
  let η := min (δ / 2) (1 / (2 * H))
  have hη : 0 < η := by dsimp only [η]; positivity
  obtain ⟨q, hq⟩ := exists_dyadic_error hη
  refine ⟨q + n, fun t => ?_⟩
  let R := (integerMatrixQuotient (2 ^ (t + (q + n)))
    (realDyadicMatrixNumerators (t + (q + n)) G)).map (Rat.castHom ℝ)
  have he : ‖R - G‖ ≤ 1 / (2 : ℝ) ^ (t + q) := by
    simpa only [Nat.add_assoc] using (realDyadicMatrix_operator_error (t + q + n) G).trans
      (dimension_guard_precision n (t + q))
  have hem : ‖R - G‖ ≤ η := he.trans ((one_div_le_one_div_of_le (by positivity)
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : q ≤ t + q))).trans hq)
  have heε : ‖R - G‖ ≤ 1 / (2 : ℝ) ^ t := he.trans (one_div_le_one_div_of_le (by positivity)
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : t ≤ t + q)))
  have heδ := hem.trans (min_le_left (δ / 2) _)
  have heH := hem.trans (min_le_right (δ / 2) _)
  refine ⟨?_, (matrixInverse_perturbation_bound G R
    (Matrix.isUnit_iff_isUnit_det G |>.mp hG.isUnit) hH hinv heH).2, heε⟩
  apply matrix_posDef_of_operator_error R G (realDyadicMatrix_isHermitian (t + (q + n)) G hG.isHermitian)
    hG.isHermitian (δ := δ) (ε := δ / 2) _ heδ (by linarith)
  simpa only [Algebra.algebraMap_eq_smul_one] using hgap

theorem positive_dyadic_width (w : ℝ) (hw : 0 < w) (q : ℕ) :
    0 < ⌈w * (2 : ℝ) ^ q⌉₊ ∧
      |w - (((⌈w * (2 : ℝ) ^ q⌉₊ : ℚ) / (2 ^ q : ℕ) : ℚ) : ℝ)| ≤ 1 / (2 : ℝ) ^ q := by
  have hp : 0 < (2 : ℝ) ^ q := by positivity
  have hlo := Nat.le_ceil (w * (2 : ℝ) ^ q)
  have hhi := Nat.ceil_lt_add_one (le_of_lt (mul_pos hw hp))
  refine ⟨Nat.ceil_pos.mpr (mul_pos hw hp), ?_⟩
  push_cast
  rw [abs_of_nonpos (sub_nonpos.mpr ((le_div_iff₀ hp).mpr hlo)), neg_sub]
  apply le_of_lt
  rw [sub_lt_iff_lt_add, div_lt_iff₀ hp]
  have he : (1 / (2 : ℝ) ^ q + w) * (2 : ℝ) ^ q = 1 + w * (2 : ℝ) ^ q := by
    field_simp
  rw [he]
  linarith

theorem positive_matrix_dyadic_gap {n : ℕ} (hn : 0 < n)
    (G : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosDef) (c : ℕ)
    (hinv : ‖G⁻¹‖ ≤ (2 : ℝ) ^ c) :
    (1 / (2 : ℝ) ^ c) • (1 : Matrix (Fin n) (Fin n) ℝ) ≤ G := by
  let : NeZero n := ⟨hn.ne'⟩
  rw [← Algebra.algebraMap_eq_smul_one]
  apply algebraMap_le_of_le_spectrum (ha := hG.isHermitian)
  intro x hx
  obtain ⟨i, rfl⟩ := hG.isHermitian.spectrum_real_eq_range_eigenvalues ▸ hx
  rw [schulzInverseTarget_spectral_form G hG, unitaryConj_matrix_norm,
    Matrix.l2_opNorm_diagonal] at hinv
  have hi := (norm_le_pi_norm (fun j => (hG.isHermitian.eigenvalues j)⁻¹) i).trans hinv
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hG.eigenvalues_pos i)), ← one_div] at hi
  exact (one_div_le (by positivity) (hG.eigenvalues_pos i)).mpr hi

theorem positive_dyadic_metric_explicit {n : ℕ} (hn : 0 < n)
    (G : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosDef) (c t : ℕ)
    (hinv : ‖G⁻¹‖ ≤ (2 : ℝ) ^ c) :
    let R := (integerMatrixQuotient (2 ^ (t + (c + 1 + n)))
      (realDyadicMatrixNumerators (t + (c + 1 + n)) G)).map (Rat.castHom ℝ)
    R.PosDef ∧ ‖R⁻¹‖ ≤ (2 : ℝ) ^ (c + 1) ∧ ‖R - G‖ ≤ 1 / (2 : ℝ) ^ t := by
  let : NeZero n := ⟨hn.ne'⟩
  let R := (integerMatrixQuotient (2 ^ (t + (c + 1 + n)))
    (realDyadicMatrixNumerators (t + (c + 1 + n)) G)).map (Rat.castHom ℝ)
  have he : ‖R - G‖ ≤ 1 / (2 : ℝ) ^ (t + (c + 1)) := by
    simpa only [R, Nat.add_assoc] using (realDyadicMatrix_operator_error (t + (c + 1) + n) G).trans
      (dimension_guard_precision n (t + (c + 1)))
  have hec : ‖R - G‖ ≤ 1 / (2 : ℝ) ^ (c + 1) := he.trans
    (one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) (by omega)))
  have het : ‖R - G‖ ≤ 1 / (2 : ℝ) ^ t := he.trans
    (one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) (by omega)))
  have hsmall : 1 / (2 : ℝ) ^ (c + 1) < 1 / (2 : ℝ) ^ c :=
    one_div_lt_one_div_of_lt (by positivity) (pow_lt_pow_right₀ (by norm_num) (by omega))
  refine ⟨matrix_posDef_of_operator_error R G
    (realDyadicMatrix_isHermitian _ G hG.isHermitian) hG.isHermitian
    (positive_matrix_dyadic_gap hn G hG c hinv) hec hsmall, ?_, het⟩
  have hi := (matrixInverse_perturbation_bound G R
    (Matrix.isUnit_iff_isUnit_det G |>.mp hG.isUnit) (by positivity) hinv
    (by simpa only [pow_succ, mul_comm] using hec)).2
  simpa only [pow_succ, mul_comm] using hi

variable (K : Type*) [Field K] [NumberField K] {d r m : ℕ}

/-- Explicit dyadic data from fixed norm bounds; no preparation cost is asserted. -/
theorem realDyadicMatrix_numerator_size {n : ℕ} (q b : ℕ)
    (G : Matrix (Fin n) (Fin n) ℝ) (hG : ‖G‖ ≤ (2 : ℝ) ^ b) (i j : Fin n) :
    (realDyadicMatrixNumerators q G i j).natAbs.size ≤ b + q + 2 := by
  have hx := (euclideanMatrix_entry_le_norm G i j).trans hG
  have hscaled : |G i j * (2 : ℝ) ^ q| ≤ (2 : ℝ) ^ (b + q) := by
    rw [abs_mul, abs_of_pos (by positivity : 0 < (2 : ℝ) ^ q), pow_add]
    exact mul_le_mul_of_nonneg_right hx (by positivity)
  have hlo := Int.floor_le (G i j * (2 : ℝ) ^ q)
  have hhi := Int.lt_floor_add_one (G i j * (2 : ℝ) ^ q)
  have hf : |(realDyadicMatrixNumerators q G i j : ℝ)| ≤ (2 : ℝ) ^ (b + q) + 1 := by
    dsimp only [realDyadicMatrixNumerators]
    exact abs_le.mpr ⟨by linarith [(abs_le.mp hscaled).1], by linarith [(abs_le.mp hscaled).2]⟩
  have hn : (realDyadicMatrixNumerators q G i j).natAbs ≤ 2 ^ (b + q) + 1 := by
    rw [← Int.cast_abs, ← Nat.cast_natAbs] at hf
    exact_mod_cast hf
  apply Nat.size_le.mpr
  apply hn.trans_lt
  rw [pow_add (2 : ℕ) (b + q) 2]
  have hp : 0 < 2 ^ (b + q) := by positivity
  norm_num
  omega

theorem dyadicWidth_numerator_size (w : ℝ) (b q : ℕ) (hw : |w| ≤ (2 : ℝ) ^ b) :
    ⌈w * (2 : ℝ) ^ q⌉₊.size ≤ b + q + 1 := by
  apply nat_size_le_of_pow
  apply Nat.ceil_le.mpr
  push_cast
  rw [pow_add]
  exact mul_le_mul_of_nonneg_right ((le_abs_self w).trans hw) (by positivity)

private theorem integerMatrix_entry_size {n : ℕ} (X : Matrix (Fin n) (Fin n) ℤ)
    (b : ℕ) (hX : ‖X.map (Int.castRingHom ℝ)‖ ≤ (2 : ℝ) ^ b) (i j : Fin n) :
    (X i j).natAbs.size ≤ b + 1 := by
  apply nat_size_le_of_pow
  have h := (euclideanMatrix_entry_le_norm (X.map (Int.castRingHom ℝ)) i j).trans hX
  change |(X i j : ℝ)| ≤ (2 : ℝ) ^ b at h
  rw [← Int.cast_abs, ← Nat.cast_natAbs] at h
  exact_mod_cast h

theorem minimumNormRightInverse_norm_le_candidate
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (A : E →L[ℝ] F) (hA : Function.Surjective A) (R : F →L[ℝ] E)
    (hR : A.comp R = ContinuousLinearMap.id ℝ F) :
    ‖minimumNormRightInverse A hA‖ ≤ ‖R‖ := by
  have he : minimumNormRightInverse A hA = A.toLinearMap.kerᗮ.starProjection.comp R := by
    rw [← minimumNormRightInverse_comp_self A hA, ContinuousLinearMap.comp_assoc,
      hR, ContinuousLinearMap.comp_id]
  rw [he]
  calc
    _ ≤ ‖A.toLinearMap.kerᗮ.starProjection‖ * ‖R‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * ‖R‖ := mul_le_mul_of_nonneg_right (Submodule.starProjection_norm_le _) (norm_nonneg _)
    _ = _ := one_mul _

theorem matrixGramInverse_norm_le_rightInverse {p q : ℕ}
    (A : Matrix (Fin p) (Fin q) ℝ) (R : Matrix (Fin q) (Fin p) ℝ)
    (hA : IsUnit (A * A.transpose).det) (hR : A * R = 1) :
    ‖(A * A.transpose)⁻¹‖ ≤ ‖R‖ ^ 2 := by
  have he : (Matrix.toEuclideanLin A).toContinuousLinearMap.comp
      (Matrix.toEuclideanLin R).toContinuousLinearMap = ContinuousLinearMap.id ℝ (Euclidean p) := by
    ext x : 1
    change ((Matrix.toLpLin 2 2 A).comp (Matrix.toLpLin 2 2 R)) x = x
    rw [← Matrix.toLpLin_mul_same, hR, Matrix.toLpLin_one]
    rfl
  have hn : ‖realRightInverseMatrix A‖ ≤ ‖R‖ := by
    change ‖(Matrix.toEuclideanLin (realRightInverseMatrix A)).toContinuousLinearMap‖ ≤ _
    rw [realRightInverseMatrix_minimumNorm A hA]
    exact minimumNormRightInverse_norm_le_candidate _ (realMatrix_gram_surjective A hA) _ he
  have hg := Matrix.l2_opNorm_conjTranspose_mul_self (realRightInverseMatrix A)
  rw [Matrix.conjTranspose_eq_transpose_of_trivial, realRightInverseMatrix_gram A hA] at hg
  rw [hg]
  simpa only [pow_two] using pow_le_pow_left₀ (norm_nonneg _) hn 2

/-- A coefficient-size majorant for the rational Gram encoding. -/
def coefficientGramBitsBound (p q U : ℕ) : ℕ := p * p * (q + 2 * U + 4)

theorem integerCoefficientGram_bits {p q : ℕ} (C : Matrix (Fin p) (Fin q) ℤ)
    (U : ℕ) (hC : ∀ i j, (C i j).natAbs.size ≤ U) :
    rationalMatrixMagnitudeBits (integerRationalMatrix C * (integerRationalMatrix C).transpose) ≤
      coefficientGramBitsBound p q U := by
  have he : integerRationalMatrix C * (integerRationalMatrix C).transpose =
      (C * C.transpose).map (Int.castRingHom ℚ) := by
    rw [Matrix.map_mul]
    rfl
  have hb (i j : Fin p) : ((C * C.transpose) i j).natAbs.size ≤ q + U + U + 2 := by
    have hentry (i : Fin p) (j : Fin q) : (C i j).natAbs ≤ 2 ^ U :=
      (Nat.size_le.mp (hC i j)).le
    have hsum : ((C * C.transpose) i j).natAbs ≤ q * (2 ^ U * 2 ^ U) := by
      rw [Matrix.mul_apply]
      apply (Int.natAbs_sum_le _ _).trans
      calc
        _ ≤ ∑ _k : Fin q, 2 ^ U * 2 ^ U := by
          apply Finset.sum_le_sum
          intro k _
          simpa only [Int.natAbs_mul, Matrix.transpose_apply] using
            Nat.mul_le_mul (hentry i k) (hentry j k)
        _ = _ := by simp
    apply Nat.size_le.mpr
    have hbound : q * (2 ^ U * 2 ^ U) ≤ 2 ^ (q + U + U) := by
      simpa only [pow_add, Nat.mul_assoc] using
        Nat.mul_le_mul_right (2 ^ U * 2 ^ U) (Nat.lt_two_pow_self (n := q)).le
    exact (hsum.trans hbound).trans_lt
      (Nat.pow_lt_pow_right (by omega) (by omega))
  rw [he, rationalMatrixMagnitudeBits]
  calc
    _ ≤ ∑ _i : Fin p, ∑ _j : Fin p, (q + 2 * U + 4) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      have hj := hb i j
      change (((C * C.transpose) i j : ℚ).num.natAbs.size + 1 +
        ((C * C.transpose) i j : ℚ).den.size) ≤ q + 2 * U + 4
      simp only [Rat.num_intCast, Rat.den_intCast, Nat.size_one]
      omega
    _ = _ := by simp [coefficientGramBitsBound, Nat.mul_assoc]

def coefficientNormBudget (p q U : ℕ) : ℕ := 2 * p + 4 * coefficientGramBitsBound p q U

def coefficientInverseBudget (p q U : ℕ) : ℕ :=
  2 * p * p + 5 * p * coefficientGramBitsBound p q U

theorem integerCoefficient_norm_budgets {p q : ℕ} (C : Matrix (Fin p) (Fin q) ℤ)
    (U : ℕ) (hC : ∀ i j, (C i j).natAbs.size ≤ U)
    (hsurj : Function.Surjective (realCoefficientMap C)) :
    ‖C.map (Int.cast : ℤ → ℝ)‖ ≤ (2 : ℝ) ^ coefficientNormBudget p q U ∧
    ‖(C.map (Int.cast : ℤ → ℝ) * (C.map (Int.cast : ℤ → ℝ)).transpose)⁻¹‖ ≤
      (2 : ℝ) ^ coefficientInverseBudget p q U := by
  let Q := integerRationalMatrix C
  let G := Q * Q.transpose
  have hb := integerCoefficientGram_bits C U hC
  have hn := rationalRectangular_norm_le_gram_input Q
  have hi := rationalInverseTarget_norm_le G
    (rationalGram_real_posDef Q (integerRationalMatrix_gram_isUnit C hsurj))
  have hnexp : rationalMatrixNormalizationExponent G ≤ coefficientNormBudget p q U := by
    dsimp [rationalMatrixNormalizationExponent, rationalMatrixScaleExponent, coefficientNormBudget]
    dsimp only [G, Q]
    omega
  have hiexp : rationalMatrixConditionExponent G ≤ coefficientInverseBudget p q U := by
    rw [rationalMatrixConditionExponent_eq]
    exact Nat.add_le_add_left (Nat.mul_le_mul_left (5 * p) hb) _
  constructor
  · rw [integerRationalMatrix_real] at hn
    exact hn.trans (pow_le_pow_right₀ (by norm_num) hnexp)
  · have he : G.map (Rat.castHom ℝ) = C.map (Int.cast : ℤ → ℝ) *
        (C.map (Int.cast : ℤ → ℝ)).transpose := by
      dsimp only [G, Q]
      rw [Matrix.map_mul, integerRationalMatrix_real]
      rfl
    change ‖(G.map (Rat.castHom ℝ))⁻¹‖ ≤ _ at hi
    rw [he] at hi
    exact hi.trans (pow_le_pow_right₀ (by norm_num) hiexp)

variable (K : Type*) [Field K] [NumberField K] {d r m : ℕ}

theorem canonicalGramRootMatrix_cancel (b : Basis (Fin d) ℤ (𝓞 K)) (n : ℕ) :
    canonicalGramRootMatrix K b n * (canonicalGramRootMatrix K b n)⁻¹ = 1 ∧
      (canonicalGramRootMatrix K b n)⁻¹ * canonicalGramRootMatrix K b n = 1 := by
  constructor <;> apply Matrix.toEuclideanLin.injective
  · change Matrix.toLpLin 2 2 (_ * _) = _
    rw [Matrix.toLpLin_mul_same, canonicalGramRootMatrix_operator,
      canonicalGramRootMatrix_inv_operator, Matrix.toLpLin_one]
    ext x : 1
    exact (canonicalGramPowerRoot K b n).apply_symm_apply x
  · change Matrix.toLpLin 2 2 (_ * _) = _
    rw [Matrix.toLpLin_mul_same, canonicalGramRootMatrix_operator,
      canonicalGramRootMatrix_inv_operator, Matrix.toLpLin_one]
    ext x : 1
    exact (canonicalGramPowerRoot K b n).symm_apply_apply x

theorem canonicalGramNormalizedMatrix_explicit_bounds (b : Basis (Fin d) ℤ (𝓞 K))
    (A : Matrix (Fin r) (Fin m) (𝓞 K)) (hA : Function.Surjective A.mulVec)
    (h U : ℕ) (hroot : ‖CFC.sqrt (canonicalGram K b)‖ ≤ (2 : ℝ) ^ h)
    (hinvroot : ‖(CFC.sqrt (canonicalGram K b))⁻¹‖ ≤ (2 : ℝ) ^ h)
    (hC : ∀ i j, (ringCoefficientMatrix b A i j).natAbs.size ≤ U) :
    ‖canonicalGramNormalizedMatrix K b A‖ ≤
        (2 : ℝ) ^ (2 * h + coefficientNormBudget (r * d) (m * d) U) ∧
      ‖(canonicalGramNormalizedMatrix K b A * (canonicalGramNormalizedMatrix K b A).transpose)⁻¹‖ ≤
        (2 : ℝ) ^ (4 * h + 2 * coefficientNormBudget (r * d) (m * d) U +
          2 * coefficientInverseBudget (r * d) (m * d) U) := by
  let C := (ringCoefficientMatrix b A).map (Int.cast : ℤ → ℝ)
  let S := canonicalGramRootMatrix K b r
  let T := canonicalGramRootMatrix K b m
  let R := T * realRightInverseMatrix C * S⁻¹
  have hc := integerCoefficient_norm_budgets (ringCoefficientMatrix b A) U hC
    (realCoefficientMap_surjective_of_integer_surjective _ ((ringCoefficientMatrix_surjective_iff b A).mpr hA))
  have hn (n : ℕ) : ‖canonicalGramRootMatrix K b n‖ ≤ (2 : ℝ) ^ h :=
    (repeatedEuclideanMatrix_norm_le n _).trans hroot
  have hi (n : ℕ) : ‖(canonicalGramRootMatrix K b n)⁻¹‖ ≤ (2 : ℝ) ^ h := by
    rw [canonicalGramRootMatrix_inverse]
    exact (repeatedEuclideanMatrix_norm_le n _).trans hinvroot
  have hcunit : IsUnit (C * C.transpose).det := realMatrix_gram_isUnit_of_surjective _
    (realCoefficientMap_surjective_of_integer_surjective _ ((ringCoefficientMatrix_surjective_iff b A).mpr hA))
  have hR : canonicalGramNormalizedMatrix K b A * R = 1 := by
    change (S * C * T⁻¹) * (T * realRightInverseMatrix C * S⁻¹) = 1
    calc
      _ = S * C * (T⁻¹ * T) * realRightInverseMatrix C * S⁻¹ := by simp only [Matrix.mul_assoc]
      _ = S * (C * realRightInverseMatrix C) * S⁻¹ := by
        rw [(canonicalGramRootMatrix_cancel K b m).2, Matrix.mul_one, Matrix.mul_assoc S C]
      _ = 1 := by rw [realRightInverseMatrix_right_inverse C hcunit, Matrix.mul_one,
        (canonicalGramRootMatrix_cancel K b r).1]
  have hRn : ‖R‖ ≤ (2 : ℝ) ^ (2 * h + coefficientNormBudget (r * d) (m * d) U +
      coefficientInverseBudget (r * d) (m * d) U) := by
    calc
      _ ≤ ‖T‖ * (‖C‖ * ‖(C * C.transpose)⁻¹‖) * ‖S⁻¹‖ := by
        exact (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right
          ((Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_left
            (by simpa only [realRightInverseMatrix, euclideanMatrix_transpose_norm] using
              Matrix.l2_opNorm_mul C.transpose (C * C.transpose)⁻¹) (norm_nonneg _))) (norm_nonneg _))
      _ ≤ (2 : ℝ) ^ h * ((2 : ℝ) ^ coefficientNormBudget (r * d) (m * d) U *
          (2 : ℝ) ^ coefficientInverseBudget (r * d) (m * d) U) * (2 : ℝ) ^ h := by
        gcongr
        · exact hn m
        · exact hc.1
        · exact hc.2
        · exact hi r
      _ = _ := by simp only [← pow_add]; congr 1; omega
  constructor
  · calc
      _ ≤ ‖S‖ * ‖C‖ * ‖T⁻¹‖ := (Matrix.l2_opNorm_mul _ _).trans
          (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
      _ ≤ (2 : ℝ) ^ h * (2 : ℝ) ^ coefficientNormBudget (r * d) (m * d) U * (2 : ℝ) ^ h := by
        gcongr
        · exact hn r
        · exact hc.1
        · exact hi m
      _ = _ := by simp only [← pow_add]; congr 1; omega
  · apply (matrixGramInverse_norm_le_rightInverse _ R
      (canonicalGramNormalizedMatrix_gram_isUnit K b A hA) hR).trans
    convert pow_le_pow_left₀ (norm_nonneg R) hRn 2 using 1
    rw [← pow_mul]
    congr 1
    omega


/-- Total bit magnitude of the given integral coefficient entries. -/
def integerCoefficientMagnitudeBits {p q : ℕ} (C : Matrix (Fin p) (Fin q) ℤ) : ℕ :=
  ∑ i, ∑ j, (C i j).natAbs.size

theorem integerCoefficientMagnitudeBits_entry {p q : ℕ}
    (C : Matrix (Fin p) (Fin q) ℤ) (i : Fin p) (j : Fin q) :
    (C i j).natAbs.size ≤ integerCoefficientMagnitudeBits C :=
  (Finset.single_le_sum (fun k _ => Nat.zero_le (C i k).natAbs.size) (Finset.mem_univ j)).trans
    (Finset.single_le_sum (fun k _ => Nat.zero_le (∑ l, (C k l).natAbs.size)) (Finset.mem_univ i))

def canonicalShapingBudget (p q U h W : ℕ) : ℕ :=
  4 * h + 2 * coefficientNormBudget p q U + 2 * coefficientInverseBudget p q U + W

def canonicalMetricBudget (p q U h : ℕ) : ℕ := 2 * h + coefficientNormBudget p q U + 1


end GeometricGaussianLHL
end

end CanonicalInputBounds

section CanonicalMetricShapingCertificate

/-! # Canonical accuracy of the metric conversion and shaping algorithms -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Module NumberField
open scoped MatrixOrder Matrix.Norms.L2Operator
namespace GeometricGaussianLHL

def metricShapingConversionPrecision (t B c : ℕ) : ℕ :=
  (2 * (t + 1) + 11 * (B + 1) + 7) + 2 * c + 3

theorem polyBound_gaussianShapeBits {n h k : ℕ → ℕ}
    (hn : PolynomialCostBound n) (hh : PolynomialCostBound h) (hk : PolynomialCostBound k) :
    PolynomialCostBound (fun x => gaussianShapeBits (n x) (h x) (k x)) :=
  (((hh.add hn).add ((PolynomialCostBound.const 2).mul hk)).add (PolynomialCostBound.const 18))

variable (K : Type*) [Field K] [NumberField K]
theorem canonicalMetricShaping_approximation_certificate
    (d r m : ℕ) (b : Basis (Fin d) ℤ (𝓞 K))
      (X : Matrix (Fin r) (Fin m) (𝓞 K)) (hX : Function.Surjective X.mulVec)
      (hr : 0 < r) (w : ℝ) (hw : 0 < w) (t B c : ℕ)
      (H : Matrix (Fin d) (Fin d) ℚ) (hH : (H.map (Rat.castHom ℝ)).PosDef)
      (hGroot : ‖CFC.sqrt (canonicalGram K b)‖ ≤ (2 : ℝ) ^ c)
      (hGinvroot : ‖(CFC.sqrt (canonicalGram K b))⁻¹‖ ≤ (2 : ℝ) ^ c)
      (hHroot : ‖CFC.sqrt (H.map (Rat.castHom ℝ))‖ ≤ (2 : ℝ) ^ c)
      (hHinvroot : ‖(CFC.sqrt (H.map (Rat.castHom ℝ)))⁻¹‖ ≤ (2 : ℝ) ^ c)
      (hGi : ‖(canonicalGram K b)⁻¹‖ ≤ (2 : ℝ) ^ c)
      (hHi : ‖(H.map (Rat.castHom ℝ))⁻¹‖ ≤ (2 : ℝ) ^ c)
      (hC : ‖(ringCoefficientMatrix b X).map (Int.cast : ℤ → ℝ)‖ ≤ (2 : ℝ) ^ c)
      (hmetric : ‖H.map (Rat.castHom ℝ) - canonicalGram K b‖ ≤
        1 / (2 : ℝ) ^ (2 * metricShapingConversionPrecision t B c + 2 * c))
      (v : ℚ) (hv : 0 < v)
      (hwidth : |w - (v : ℝ)| ≤ 1 / (2 : ℝ) ^ (2 * (t + 1) + 11 * (B + 1) + 7))
      (hAn : ‖canonicalGramNormalizedMatrix K b X‖ ≤ (2 : ℝ) ^ B)
      (hAi : ‖(canonicalGramNormalizedMatrix K b X *
        (canonicalGramNormalizedMatrix K b X).transpose)⁻¹‖ ≤ (2 : ℝ) ^ B)
      (hwn : |w| ≤ (2 : ℝ) ^ B) :
      let Q := rationalMetricNormalizedApprox (metricShapingConversionPrecision t B c) H
        ((ringCoefficientMatrix b X).map (Int.castRingHom ℚ))
      let e := canonicalGramEuclideanIsometry K b m
      let S := canonicalGramShapingShape K b X hX hr w hw
      let R := (rationalShapingApprox (t + 1) Q v).map (Rat.castHom ℝ)
      R.PosDef ∧ ‖isometricTransportMap e e (Matrix.toEuclideanLin R).toContinuousLinearMap -
        S.toContinuousLinearMap‖ ≤ 1 / (2 : ℝ) ^ t := by
  dsimp only
  let s := 2 * (t + 1) + 11 * (B + 1) + 7
  let Q := rationalMetricNormalizedApprox (metricShapingConversionPrecision t B c) H
    ((ringCoefficientMatrix b X).map (Int.castRingHom ℚ))
  have hQ : ‖Q.map (Rat.castHom ℝ) - canonicalGramNormalizedMatrix K b X‖ ≤ 1 / (2 : ℝ) ^ s :=
    rationalMetricNormalizedApprox_canonical_error K b X s c H hH hGroot hGinvroot hHroot hHinvroot
      hGi hHi hC hmetric
  have hinput : ‖canonicalGramNormalizedMatrix K b X - Q.map (Rat.castHom ℝ)‖ + |w - (v : ℝ)| ≤
      1 / (2 : ℝ) ^ (2 * (t + 1) + 11 * (B + 1) + 6) := by
    rw [norm_sub_rev]
    apply (add_le_add hQ hwidth).trans_eq
    dsimp only [s]
    rw [show 2 * (t + 1) + 11 * (B + 1) + 7 = (2 * (t + 1) + 11 * (B + 1) + 6) + 1 by omega,
      pow_succ]
    ring
  exact canonicalGramShapingShape_approximation_certificate K d r m b X hX hr w hw t B Q v hv hAn hAi hwn hinput

end GeometricGaussianLHL
end

end CanonicalMetricShapingCertificate

section AlgebraicMetricPreparation

/-!
## Preparing a positive rational metric from algebraic entries

Approximate the upper triangle and mirror it to preserve symmetry exactly.
The precision guard is computed from the finite input conditioning bound.
The resulting metric is positive definite and has controlled inverse and
square-root norms at every requested precision.
-/

set_option backward.isDefEq.respectTransparency false
open scoped MatrixOrder Matrix.Norms.L2Operator
namespace GeometricGaussianLHL

def algebraicSymmetricApprox {n : ℕ}
    (I : Matrix (Fin n) (Fin n) AlgebraicRealInput) (t : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j => if i ≤ j then (I i j).approx t else (I j i).approx t

theorem algebraicSymmetricApprox_isHermitian {n : ℕ}
    (I : Matrix (Fin n) (Fin n) AlgebraicRealInput) (t : ℕ) :
    ((algebraicSymmetricApprox I t).map (Rat.castHom ℝ)).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp only [Matrix.map_apply, star_trivial, algebraicSymmetricApprox]
  split_ifs with hji hij
  · have he : i = j := le_antisymm hij hji
    subst j
    rfl
  · rfl
  · rfl
  · omega

theorem algebraicSymmetricApprox_entry_error {n : ℕ}
    (I : Matrix (Fin n) (Fin n) AlgebraicRealInput) (G : Matrix (Fin n) (Fin n) ℝ)
    (hI : ∀ i j, (I i j).ValidFor (G i j)) (hG : G.IsHermitian) (t : ℕ) (i j : Fin n) :
    |(algebraicSymmetricApprox I t i j : ℝ) - G i j| ≤ 1 / (2 : ℝ) ^ t := by
  unfold algebraicSymmetricApprox
  split_ifs
  · exact (hI i j).approx_error t
  · rw [← (Matrix.isHermitian_iff_isSymm.mp hG).apply i j]
    exact (hI j i).approx_error t

theorem algebraicSymmetricApprox_operator_error {n : ℕ}
    (I : Matrix (Fin n) (Fin n) AlgebraicRealInput) (G : Matrix (Fin n) (Fin n) ℝ)
    (hI : ∀ i j, (I i j).ValidFor (G i j)) (hG : G.IsHermitian) (t : ℕ) :
    ‖(algebraicSymmetricApprox I t).map (Rat.castHom ℝ) - G‖ ≤ (n : ℝ) * (1 / (2 : ℝ) ^ t) := by
  rw [euclideanMatrix_norm_sub_CLM]
  exact euclideanMatrix_opNorm_sub_le_entries _ _ (by positivity)
    (algebraicSymmetricApprox_entry_error I G hI hG t)

def algebraicPositiveMetricApprox {n : ℕ}
    (I : Matrix (Fin n) (Fin n) AlgebraicRealInput) (h t : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  algebraicSymmetricApprox I (t + (h + 1) + n)

theorem algebraicPositiveMetricApprox_bounds {n : ℕ} (hn : 0 < n)
    (I : Matrix (Fin n) (Fin n) AlgebraicRealInput) (G : Matrix (Fin n) (Fin n) ℝ)
    (hI : ∀ i j, (I i j).ValidFor (G i j)) (hG : G.PosDef) (h t : ℕ)
    (hGn : ‖G‖ ≤ (2 : ℝ) ^ h) (hGi : ‖G⁻¹‖ ≤ (2 : ℝ) ^ h) :
    let R := (algebraicPositiveMetricApprox I h t).map (Rat.castHom ℝ)
    R.PosDef ∧ ‖R‖ ≤ (2 : ℝ) ^ (h + 1) ∧ ‖R⁻¹‖ ≤ (2 : ℝ) ^ (h + 1) ∧
      ‖CFC.sqrt R‖ ≤ (2 : ℝ) ^ (h + 1) ∧
      ‖(CFC.sqrt R)⁻¹‖ ≤ (2 : ℝ) ^ (h + 1) ∧ ‖R - G‖ ≤ 1 / (2 : ℝ) ^ t := by
  let : NeZero n := ⟨hn.ne'⟩
  let R := (algebraicPositiveMetricApprox I h t).map (Rat.castHom ℝ)
  have he : ‖R - G‖ ≤ 1 / (2 : ℝ) ^ (t + (h + 1)) :=
    (algebraicSymmetricApprox_operator_error I G hI hG.isHermitian _).trans
      (dimension_guard_precision n (t + (h + 1)))
  have heh : ‖R - G‖ ≤ 1 / (2 : ℝ) ^ (h + 1) := he.trans
    (one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) (by omega)))
  have het : ‖R - G‖ ≤ 1 / (2 : ℝ) ^ t := he.trans
    (one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) (by omega)))
  have hp : R.PosDef := matrix_posDef_of_operator_error R G
    (algebraicSymmetricApprox_isHermitian I _) hG.isHermitian
    (positive_matrix_dyadic_gap hn G hG h hGi) heh
    (one_div_lt_one_div_of_lt (by positivity) (pow_lt_pow_right₀ (by norm_num) (by omega)))
  have hi : ‖R⁻¹‖ ≤ (2 : ℝ) ^ (h + 1) := by
    have hb := (matrixInverse_perturbation_bound G R
      (Matrix.isUnit_iff_isUnit_det G |>.mp hG.isUnit) (by positivity) hGi
      (by simpa only [pow_succ, mul_comm] using heh)).2
    simpa only [pow_succ, mul_comm] using hb
  have hR : ‖R‖ ≤ (2 : ℝ) ^ (h + 1) := by
    have heone : ‖R - G‖ ≤ 1 := heh.trans
      ((div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num)))
    have hb := norm_add_le (R - G) G
    rw [sub_add_cancel] at hb
    rw [pow_succ]
    linarith [one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) (n := h)]
  exact ⟨hp, hR, hi, positiveMatrix_sqrt_norm_bound R hp.posSemidef _ hR,
    positiveMatrix_inverse_sqrt_norm_bound R hp _ hi, het⟩

end GeometricGaussianLHL

end AlgebraicMetricPreparation

section CanonicalShapingInput

/-!
## Finite prepared inputs and the canonical approximation algorithm

The executed data are rational metric/width entries and integer coefficients.
The validity fields relate these data to canonical geometry; they make no
claim about the output or its cost. `CanonicalAlgebraicInput` derives every
field here from finite algebraic metric/width data and integer coefficients.
Composing the complete bit-cost bounds remains a separate obligation.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Module NumberField
open scoped MatrixOrder Matrix.Norms.L2Operator
namespace GeometricGaussianLHL

/-- Pure numerical composition, independent of an abstract number field. -/
def preparedShapingApprox {d r m : ℕ} (t B c : ℕ)
    (metric : Matrix (Fin d) (Fin d) ℚ)
    (coefficients : Matrix (Fin (r * d)) (Fin (m * d)) ℤ) (width : ℚ) :
    Matrix (Fin (m * d)) (Fin (m * d)) ℚ :=
  rationalShapingApprox (t + 1)
    (rationalMetricNormalizedApprox (metricShapingConversionPrecision t B c)
      metric (coefficients.map (Int.castRingHom ℚ))) width

variable (K : Type*) [Field K] [NumberField K] {d r m : ℕ}

structure CanonicalShapingInput (b : Basis (Fin d) ℤ (𝓞 K))
    (A : Matrix (Fin r) (Fin m) (𝓞 K)) (_hrm : r ≤ m) (w : ℝ) (t : ℕ) where
  B : ℕ
  c : ℕ
  metric : Matrix (Fin d) (Fin d) ℚ
  coefficients : Matrix (Fin (r * d)) (Fin (m * d)) ℤ
  width : ℚ
  hcoeff : coefficients = ringCoefficientMatrix b A
  hwidthPos : 0 < width
  hmetricPos : (metric.map (Rat.castHom ℝ)).PosDef
  hroot : ‖CFC.sqrt (canonicalGram K b)‖ ≤ (2 : ℝ) ^ c
  hinvroot : ‖(CFC.sqrt (canonicalGram K b))⁻¹‖ ≤ (2 : ℝ) ^ c
  hmetricRoot : ‖CFC.sqrt (metric.map (Rat.castHom ℝ))‖ ≤ (2 : ℝ) ^ c
  hmetricInvroot : ‖(CFC.sqrt (metric.map (Rat.castHom ℝ)))⁻¹‖ ≤ (2 : ℝ) ^ c
  hGi : ‖(canonicalGram K b)⁻¹‖ ≤ (2 : ℝ) ^ c
  hXi : ‖(metric.map (Rat.castHom ℝ))⁻¹‖ ≤ (2 : ℝ) ^ c
  hC : ‖(ringCoefficientMatrix b A).map (Int.cast : ℤ → ℝ)‖ ≤ (2 : ℝ) ^ c
  hmetric : ‖metric.map (Rat.castHom ℝ) - canonicalGram K b‖ ≤
    1 / (2 : ℝ) ^ (2 * metricShapingConversionPrecision t B c + 2 * c)
  hwidth : |w - (width : ℝ)| ≤ 1 / (2 : ℝ) ^ (2 * (t + 1) + 11 * (B + 1) + 7)
  hAn : ‖canonicalGramNormalizedMatrix K b A‖ ≤ (2 : ℝ) ^ B
  hAi : ‖(canonicalGramNormalizedMatrix K b A *
    (canonicalGramNormalizedMatrix K b A).transpose)⁻¹‖ ≤ (2 : ℝ) ^ B
  hwB : |w| ≤ (2 : ℝ) ^ B

namespace CanonicalShapingInput
variable {K} {b : Basis (Fin d) ℤ (𝓞 K)} {A : Matrix (Fin r) (Fin m) (𝓞 K)}
  {hrm : r ≤ m} {w : ℝ} {t : ℕ} (I : CanonicalShapingInput K b A hrm w t)

def output : Matrix (Fin (m * d)) (Fin (m * d)) ℝ :=
  (preparedShapingApprox t I.B I.c I.metric I.coefficients I.width).map (Rat.castHom ℝ)

def Accuracy (hA : Function.Surjective A.mulVec) (hr : 0 < r) (hw : 0 < w) : Prop :=
  I.output.PosDef ∧
    ‖isometricTransportMap (canonicalGramEuclideanIsometry K b m) (canonicalGramEuclideanIsometry K b m)
      (Matrix.toEuclideanLin I.output).toContinuousLinearMap -
      (canonicalGramShapingShape K b A hA hr w hw).toContinuousLinearMap‖ ≤ 1 / (2 : ℝ) ^ t

theorem output_certificate (hA : Function.Surjective A.mulVec) (hr : 0 < r) (hw : 0 < w) :
    I.Accuracy hA hr hw := by
  dsimp only [Accuracy, output, preparedShapingApprox]
  rw [I.hcoeff]
  exact canonicalMetricShaping_approximation_certificate K d r m b A hA hr w hw t I.B I.c
    I.metric I.hmetricPos I.hroot I.hinvroot I.hmetricRoot I.hmetricInvroot I.hGi I.hXi I.hC
    I.hmetric I.width I.hwidthPos I.hwidth I.hAn I.hAi I.hwB

end CanonicalShapingInput
end GeometricGaussianLHL
end

end CanonicalShapingInput

section PreparedShapingScheduleCost

/-!
## Stored integral coefficients and the canonical conversion schedule

The integral coefficient table is finite stored data. Its rational conversion
and the arithmetic choosing normalization and output precisions are charged.
-/

namespace GeometricGaussianLHL

abbrev IntegerRectData (p q : ℕ) := Vector (Vector ℤ q) p

def integerRectMatrixData {p q : ℕ} (C : Matrix (Fin p) (Fin q) ℤ) : IntegerRectData p q :=
  Vector.ofFn (fun i => Vector.ofFn (C i))

def integerRectMatrixOfData {p q : ℕ} (C : IntegerRectData p q) : Matrix (Fin p) (Fin q) ℤ :=
  fun i j => (C.get i).get j

theorem integerRectMatrixOfData_data {p q : ℕ} (C : Matrix (Fin p) (Fin q) ℤ) :
    integerRectMatrixOfData (integerRectMatrixData C) = C := by
  ext i j
  simp [integerRectMatrixOfData, integerRectMatrixData, Vector.get]
  rfl

def encodeIntegerRectData {p q : ℕ} (C : IntegerRectData p q) : List Bool :=
  encodeNatBits p ++ encodeNatBits q ++ encodeVectorBits (encodeVectorBits encodeIntBits) C

theorem encodeIntegerRectData_length {p q : ℕ} (C : IntegerRectData p q) :
    (encodeIntegerRectData C).length = 2 * p.size + 2 * q.size + 2 +
      2 * (∑ i, ∑ j, (integerRectMatrixOfData C i j).natAbs.size) + 2 * (p * q) := by
  simp only [encodeIntegerRectData, List.length_append, encodeNatBits_length, encodeVectorBits_length_sum,
    encodeIntBits_length, integerRectMatrixOfData]
  simp [Finset.sum_add_distrib, Finset.mul_sum]
  ring

def costedIntegerRectToRational {p q : ℕ} (C : IntegerRectData p q) : Costed (RationalRectData p q) :=
  costedRationalRectOfFn fun i j => Costed.charge ((integerRectMatrixOfData C i j).natAbs.size + 1) (integerRectMatrixOfData C i j : ℚ)

theorem costedIntegerRectToRational_data {p q : ℕ} (C : IntegerRectData p q) :
    (costedIntegerRectToRational C).value = rationalRectMatrixData ((integerRectMatrixOfData C).map (Int.castRingHom ℚ)) := by
  rw [costedIntegerRectToRational, costedRationalRectOfFn_data]
  rfl

theorem costedIntegerRectToRational_steps_le {p q : ℕ} (C : IntegerRectData p q) (L : ℕ)
    (hC : ∀ i j, (integerRectMatrixOfData C i j).natAbs.size ≤ L) :
    (costedIntegerRectToRational C).steps ≤ rationalRectTraversalBudget p q (L + 1) :=
  costedRationalRectOfFn_steps_le _ _ (fun i j => Nat.add_le_add_right (hC i j) 1)

theorem costedIntegerRectToRational_size {p q : ℕ} (C : IntegerRectData p q) (L : ℕ)
    (hC : ∀ i j, (integerRectMatrixOfData C i j).natAbs.size ≤ L) (i j) :
    rationalMagnitudeBits (rationalRectMatrixOfData (costedIntegerRectToRational C).value i j) ≤ L + 2 := by
  rw [costedIntegerRectToRational_data, rationalRectMatrixOfData_data]
  exact (intCast_rational_bits _).le.trans (Nat.add_le_add_right (hC i j) 2)

structure PreparedShapingSchedule where
  normalizationPrecision : ℕ
  shapingPrecision : ℕ

def costedPreparedShapingSchedule (t B c : ℕ) : Costed PreparedShapingSchedule :=
  let u := costedNatAdd t 1
  let v := costedNatAdd B 1
  let a := costedNatMul 2 u.value
  let b := costedNatMul 11 v.value
  let s := costedNatAdd a.value b.value
  let e := costedNatAdd s.value 7
  let f := costedNatMul 2 c
  let h := costedNatAdd e.value f.value
  let q := costedNatAdd h.value 3
  ⟨⟨q.value, u.value⟩, u.steps + v.steps + a.steps + b.steps + s.steps + e.steps + f.steps + h.steps + q.steps⟩

theorem costedPreparedShapingSchedule_value (t B c : ℕ) :
    (costedPreparedShapingSchedule t B c).value = ⟨metricShapingConversionPrecision t B c, t + 1⟩ := rfl

def preparedShapingScheduleBudget (t B c : ℕ) : ℕ :=
  9 * (2 * (2 * (t + 1) + 11 * (B + 1) + 2 * c + 10) + 1) ^ 2

theorem costedPreparedShapingSchedule_steps_le (t B c : ℕ) :
    (costedPreparedShapingSchedule t B c).steps ≤ preparedShapingScheduleBudget t B c := by
  let H := 2 * (t + 1) + 11 * (B + 1) + 2 * c + 10
  have h₁ := costedNatAdd_steps_le t 1 H (by dsimp [H]; omega) (by dsimp [H]; omega)
  have h₂ := costedNatAdd_steps_le B 1 H (by dsimp [H]; omega) (by dsimp [H]; omega)
  have h₃ := costedNatMul_steps_le 2 (t + 1) H (by dsimp [H]; omega) (by dsimp [H]; omega)
  have h₄ := costedNatMul_steps_le 11 (B + 1) H (by dsimp [H]; omega) (by dsimp [H]; omega)
  have h₅ := costedNatAdd_steps_le (2 * (t + 1)) (11 * (B + 1)) H (by dsimp [H]; omega) (by dsimp [H]; omega)
  have h₆ := costedNatAdd_steps_le (2 * (t + 1) + 11 * (B + 1)) 7 H (by dsimp [H]; omega) (by dsimp [H]; omega)
  have h₇ := costedNatMul_steps_le 2 c H (by dsimp [H]; omega) (by dsimp [H]; omega)
  have h₈ := costedNatAdd_steps_le (2 * (t + 1) + 11 * (B + 1) + 7) (2 * c) H (by dsimp [H]; omega) (by dsimp [H]; omega)
  have h₉ := costedNatAdd_steps_le (2 * (t + 1) + 11 * (B + 1) + 7 + 2 * c) 3 H (by dsimp [H]; omega) (by dsimp [H]; omega)
  dsimp only [costedPreparedShapingSchedule, costedNatAdd, costedNatMul] at *
  change _ ≤ 9 * (2 * H + 1) ^ 2
  omega

theorem polyBound_metricShapingConversionPrecision {t B c : ℕ → ℕ}
    (ht : PolynomialCostBound t) (hB : PolynomialCostBound B) (hc : PolynomialCostBound c) :
    PolynomialCostBound (fun x => metricShapingConversionPrecision (t x) (B x) (c x)) :=
  (((((PolynomialCostBound.const 2).mul (ht.add (PolynomialCostBound.const 1))).add
    ((PolynomialCostBound.const 11).mul (hB.add (PolynomialCostBound.const 1)))).add (PolynomialCostBound.const 7)).add
      ((PolynomialCostBound.const 2).mul hc)).add (PolynomialCostBound.const 3)

theorem polyBound_preparedShapingScheduleBudget {t B c : ℕ → ℕ}
    (ht : PolynomialCostBound t) (hB : PolynomialCostBound B) (hc : PolynomialCostBound c) :
    PolynomialCostBound (fun x => preparedShapingScheduleBudget (t x) (B x) (c x)) :=
  (PolynomialCostBound.const 9).mul ((((PolynomialCostBound.const 2).mul
    (((((PolynomialCostBound.const 2).mul (ht.add (PolynomialCostBound.const 1))).add
      ((PolynomialCostBound.const 11).mul (hB.add (PolynomialCostBound.const 1)))).add
        ((PolynomialCostBound.const 2).mul hc)).add (PolynomialCostBound.const 10))).add (PolynomialCostBound.const 1)).pow 2)

end GeometricGaussianLHL

end PreparedShapingScheduleCost

section CanonicalAlgebraicInput

/-!
## Canonical shaping from finite algebraic metric and width data

The input contains algebraic encodings of the canonical Gram entries and the
width, together with the integral coefficient matrix. Every precision and
conditioning budget is computed from this data. The validity predicate only
identifies the represented mathematical input; it contains no approximation,
output, inverse-norm, or runtime hypothesis.

The preparation theorem supplies the previously separate rational-input
obligations for every precision. The complete cost composition is proved in `CanonicalFiniteCost`;
`CanonicalEncodingExistence` establishes representation availability.
-/

set_option backward.isDefEq.respectTransparency false
open Module NumberField
open scoped MatrixOrder Matrix.Norms.L2Operator
namespace GeometricGaussianLHL

structure CanonicalAlgebraicInput (d r m : ℕ) where
  metric : Matrix (Fin d) (Fin d) AlgebraicRealInput
  coefficients : Matrix (Fin (r * d)) (Fin (m * d)) ℤ
  width : AlgebraicRealInput

namespace CanonicalAlgebraicInput
variable {d r m : ℕ} (I : CanonicalAlgebraicInput d r m)

def conditioning : ℕ := algebraicMetricConditionExponent I.metric

def coefficientBits : ℕ := integerCoefficientMagnitudeBits I.coefficients

def shapingBudget : ℕ :=
  canonicalShapingBudget (r * d) (m * d) I.coefficientBits I.conditioning I.width.endpointBits

def metricBudget : ℕ := canonicalMetricBudget (r * d) (m * d) I.coefficientBits I.conditioning

def prepareMetric (t : ℕ) : Matrix (Fin d) (Fin d) ℚ :=
  algebraicPositiveMetricApprox I.metric I.conditioning
    (2 * metricShapingConversionPrecision t I.shapingBudget I.metricBudget + 2 * I.metricBudget)

def prepareWidth (t : ℕ) : ℚ :=
  I.width.approx (2 * (t + 1) + 11 * (I.shapingBudget + 1) + 7)

def output (t : ℕ) : Matrix (Fin (m * d)) (Fin (m * d)) ℚ :=
  preparedShapingApprox t I.shapingBudget I.metricBudget (I.prepareMetric t) I.coefficients (I.prepareWidth t)

variable (K : Type*) [Field K] [NumberField K]

structure ValidFor (b : Basis (Fin d) ℤ (𝓞 K))
    (A : Matrix (Fin r) (Fin m) (𝓞 K)) (w : ℝ) : Prop where
  metric_valid : ∀ i j, (I.metric i j).ValidFor (canonicalGram K b i j)
  coefficients_eq : I.coefficients = ringCoefficientMatrix b A
  width_valid : I.width.ValidFor w

variable {I K} {b : Basis (Fin d) ℤ (𝓞 K)}
  {A : Matrix (Fin r) (Fin m) (𝓞 K)} {w : ℝ}

theorem ValidFor.conditioning_bounds (hI : I.ValidFor K b A w) :
    ‖canonicalGram K b‖ ≤ (2 : ℝ) ^ I.conditioning ∧
    ‖(canonicalGram K b)⁻¹‖ ≤ (2 : ℝ) ^ I.conditioning ∧
    ‖CFC.sqrt (canonicalGram K b)‖ ≤ (2 : ℝ) ^ I.conditioning ∧
    ‖(CFC.sqrt (canonicalGram K b))⁻¹‖ ≤ (2 : ℝ) ^ I.conditioning :=
  canonicalGram_encoded_conditioning K b I.metric hI.metric_valid

theorem ValidFor.shaping_bounds (hI : I.ValidFor K b A w)
    (hA : Function.Surjective A.mulVec) :
    ‖canonicalGramNormalizedMatrix K b A‖ ≤ (2 : ℝ) ^ I.shapingBudget ∧
    ‖(canonicalGramNormalizedMatrix K b A *
      (canonicalGramNormalizedMatrix K b A).transpose)⁻¹‖ ≤ (2 : ℝ) ^ I.shapingBudget ∧
    |w| ≤ (2 : ℝ) ^ I.shapingBudget := by
  have he (i j) : (ringCoefficientMatrix b A i j).natAbs.size ≤ I.coefficientBits := by
    rw [← hI.coefficients_eq]
    exact integerCoefficientMagnitudeBits_entry I.coefficients i j
  have hb := canonicalGramNormalizedMatrix_explicit_bounds K b A hA I.conditioning I.coefficientBits
    hI.conditioning_bounds.2.2.1 hI.conditioning_bounds.2.2.2 he
  refine ⟨hb.1.trans (pow_le_pow_right₀ (by norm_num) ?_),
    hb.2.trans (pow_le_pow_right₀ (by norm_num) ?_),
    hI.width_valid.abs_le.trans (pow_le_pow_right₀ (by norm_num) ?_)⟩ <;>
    unfold shapingBudget canonicalShapingBudget <;> omega

theorem ValidFor.metric_bounds (hI : I.ValidFor K b A w) (t : ℕ) :
    let R := (I.prepareMetric t).map (Rat.castHom ℝ)
    R.PosDef ∧ ‖R⁻¹‖ ≤ (2 : ℝ) ^ I.metricBudget ∧
      ‖CFC.sqrt R‖ ≤ (2 : ℝ) ^ I.metricBudget ∧
      ‖(CFC.sqrt R)⁻¹‖ ≤ (2 : ℝ) ^ I.metricBudget ∧
      ‖R - canonicalGram K b‖ ≤
        1 / (2 : ℝ) ^ (2 * metricShapingConversionPrecision t I.shapingBudget I.metricBudget + 2 * I.metricBudget) := by
  have hb := algebraicPositiveMetricApprox_bounds (integralBasis_dimension_pos K b) I.metric
    (canonicalGram K b) hI.metric_valid (canonicalGram_posDef K b) I.conditioning
    (2 * metricShapingConversionPrecision t I.shapingBudget I.metricBudget + 2 * I.metricBudget)
    hI.conditioning_bounds.1 hI.conditioning_bounds.2.1
  have hexp : I.conditioning + 1 ≤ I.metricBudget := by
    unfold metricBudget canonicalMetricBudget
    omega
  have hp := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hexp
  exact ⟨hb.1, hb.2.2.1.trans hp, hb.2.2.2.1.trans hp, hb.2.2.2.2.1.trans hp, hb.2.2.2.2.2⟩

/-- All finite data are the displayed executable preparation functions. -/
def ValidFor.toPrepared (hI : I.ValidFor K b A w) (hrm : r ≤ m)
    (hA : Function.Surjective A.mulVec) (hw : 0 < w) (t : ℕ) :
    CanonicalShapingInput K b A hrm w t := by
  have hc := hI.conditioning_bounds
  have hm := hI.metric_bounds t
  have hb := hI.shaping_bounds hA
  have hexp : I.conditioning ≤ I.metricBudget := by
    unfold metricBudget canonicalMetricBudget
    omega
  have hC := integerCoefficient_norm_budgets (ringCoefficientMatrix b A) I.coefficientBits
    (by intro i j; rw [← hI.coefficients_eq]; exact integerCoefficientMagnitudeBits_entry I.coefficients i j)
    (realCoefficientMap_surjective_of_integer_surjective _ ((ringCoefficientMatrix_surjective_iff b A).mpr hA))
  exact {
    B := I.shapingBudget
    c := I.metricBudget
    metric := I.prepareMetric t
    coefficients := I.coefficients
    width := I.prepareWidth t
    hcoeff := hI.coefficients_eq
    hwidthPos := hI.width_valid.approx_pos hw _
    hmetricPos := hm.1
    hroot := hc.2.2.1.trans (pow_le_pow_right₀ (by norm_num) hexp)
    hinvroot := hc.2.2.2.trans (pow_le_pow_right₀ (by norm_num) hexp)
    hmetricRoot := hm.2.2.1
    hmetricInvroot := hm.2.2.2.1
    hGi := hc.2.1.trans (pow_le_pow_right₀ (by norm_num) hexp)
    hXi := hm.2.1
    hC := hC.1.trans (pow_le_pow_right₀ (by norm_num) (by unfold metricBudget canonicalMetricBudget; omega))
    hmetric := hm.2.2.2.2
    hwidth := by rw [abs_sub_comm]; exact hI.width_valid.approx_error _
    hAn := hb.1
    hAi := hb.2.1
    hwB := hb.2.2 }

theorem ValidFor.toPrepared_output (hI : I.ValidFor K b A w) (hrm : r ≤ m)
    (hA : Function.Surjective A.mulVec) (hw : 0 < w) (t : ℕ) :
    (hI.toPrepared hrm hA hw t).output = (I.output t).map (Rat.castHom ℝ) := rfl

/-- The same finite input works at every requested precision. -/
theorem ValidFor.output_certificate (hI : I.ValidFor K b A w) (hrm : r ≤ m)
    (hA : Function.Surjective A.mulVec) (hr : 0 < r) (hw : 0 < w) (t : ℕ) :
    ((I.output t).map (Rat.castHom ℝ)).PosDef ∧
      ‖isometricTransportMap (canonicalGramEuclideanIsometry K b m) (canonicalGramEuclideanIsometry K b m)
        (Matrix.toEuclideanLin ((I.output t).map (Rat.castHom ℝ))).toContinuousLinearMap -
        (canonicalGramShapingShape K b A hA hr w hw).toContinuousLinearMap‖ ≤ 1 / (2 : ℝ) ^ t :=
  (hI.toPrepared hrm hA hw t).output_certificate hA hr hw

end CanonicalAlgebraicInput
end GeometricGaussianLHL

end CanonicalAlgebraicInput

section PreparedShapingCost

/-!
## Composing finite prepared data with the complete shaping execution

The stored integer conversion, metric normalization and rational shaping run
share the computed schedule. This internal cost bound requires full row rank
of the normalized input; the canonical interface derives it from its proved
input-accuracy and conditioning bounds.
-/

open scoped MatrixOrder Matrix.Norms.L2Operator
namespace GeometricGaussianLHL

def costedPreparedShaping {d r m : ℕ} (t B c : ℕ) (G : RationalMatrixData d)
    (C : IntegerRectData (r * d) (m * d)) (w : ℚ) : Costed (RationalMatrixData (m * d)) :=
  (costedPreparedShapingSchedule t B c).bind fun P =>
    (costedIntegerRectToRational C).bind fun D =>
      (costedRationalMetricNormalization P.normalizationPrecision G D).bind fun Q =>
        costedRationalShapingApprox P.shapingPrecision Q w

theorem costedPreparedShaping_data {d r m : ℕ} (t B c : ℕ) (G : RationalMatrixData d)
    (C : IntegerRectData (r * d) (m * d)) (w : ℚ) :
    (costedPreparedShaping t B c G C w).value = rationalMatrixData
      (preparedShapingApprox t B c (rationalMatrixOfData G) (integerRectMatrixOfData C) w) := by
  rw [costedPreparedShaping, Costed.bind_value, costedPreparedShapingSchedule_value,
    Costed.bind_value, costedIntegerRectToRational_data, Costed.bind_value,
    costedRationalMetricNormalization_data, rationalRectMatrixOfData_data,
    costedRationalShapingApprox_data, rationalRectMatrixOfData_data]
  rfl

def preparedNormalizationBudget (d r m L t B c : ℕ) : ℕ :=
  rationalMetricNormalizationBudget d r m (d * d * L) (L + 2) (metricShapingConversionPrecision t B c)
def preparedShapingBudget (d r m L t B c : ℕ) : ℕ :=
  let N := preparedNormalizationBudget d r m L t B c
  preparedShapingScheduleBudget t B c + rationalRectTraversalBudget (r * d) (m * d) (L + 1) + N +
    rationalShapingBudget (r * d) (m * d) (L + N) (t + 1)

theorem costedPreparedShaping_steps_le {d r m : ℕ} (t B c : ℕ) (G : RationalMatrixData d)
    (C : IntegerRectData (r * d) (m * d)) (w : ℚ) (L : ℕ)
    (hG : ((rationalMatrixOfData G).map (Rat.castHom ℝ)).PosDef)
    (hGs : ∀ i j, rationalMagnitudeBits (rationalMatrixOfData G i j) ≤ L)
    (hCs : ∀ i j, (integerRectMatrixOfData C i j).natAbs.size ≤ L)
    (hwL : rationalMagnitudeBits w ≤ L) (hp : 0 < r * d) (hw : w ≠ 0)
    (hQ :
      let Q := rationalMetricNormalizedApprox (metricShapingConversionPrecision t B c)
        (rationalMatrixOfData G) ((integerRectMatrixOfData C).map (Int.castRingHom ℚ))
      IsUnit (Q * Q.transpose).det) :
    (costedPreparedShaping t B c G C w).steps ≤ preparedShapingBudget d r m L t B c := by
  let D := costedIntegerRectToRational C
  let N := costedRationalMetricNormalization (metricShapingConversionPrecision t B c) G D.value
  let K := preparedNormalizationBudget d r m L t B c
  have hsum : rationalMatrixMagnitudeBits (rationalMatrixOfData G) ≤ d * d * L := by
    calc
      _ ≤ ∑ i : Fin d, ∑ j : Fin d, L := Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hGs i j))
      _ = _ := by simp; ring
  have hDs := costedIntegerRectToRational_steps_le C L hCs
  have hNs : N.steps ≤ K :=
    (costedRationalMetricNormalization_steps_le _ G D.value (L + 2) hG (costedIntegerRectToRational_size C L hCs)).trans
      (rationalMetricNormalizationBudget_mono le_rfl le_rfl le_rfl hsum le_rfl le_rfl)
  have hNl : (encodeRationalRectData N.value).length ≤ K :=
    (costedRationalMetricNormalization_length_le_steps _ G D.value).trans hNs
  have hNdata : N.value = rationalRectMatrixData (rationalMetricNormalizedApprox (metricShapingConversionPrecision t B c)
      (rationalMatrixOfData G) ((integerRectMatrixOfData C).map (Int.castRingHom ℚ))) := by
    rw [costedRationalMetricNormalization_data, costedIntegerRectToRational_data, rationalRectMatrixOfData_data]
  have hQr : IsUnit (rationalRectMatrixOfData N.value * (rationalRectMatrixOfData N.value).transpose).det := by
    rw [hNdata, rationalRectMatrixOfData_data]
    exact hQ
  have hSs := costedRationalShapingApprox_steps_le (t + 1) N.value w (L + K)
    (fun i j => ((rationalRect_entry_bits_le_encoded N.value i j).trans hNl).trans (by omega))
    (hwL.trans (by omega)) hp hQr hw
  have hPs := costedPreparedShapingSchedule_steps_le t B c
  change D.steps ≤ _ at hDs
  rw [costedPreparedShaping, Costed.bind_steps, costedPreparedShapingSchedule_value, Costed.bind_steps, Costed.bind_steps]
  change (costedPreparedShapingSchedule t B c).steps + (D.steps + (N.steps + (costedRationalShapingApprox (t + 1) N.value w).steps)) ≤ _
  change _ ≤ preparedShapingScheduleBudget t B c + rationalRectTraversalBudget (r * d) (m * d) (L + 1) + K +
    rationalShapingBudget (r * d) (m * d) (L + K) (t + 1)
  omega

theorem costedPreparedShaping_length_le_steps {d r m : ℕ} (t B c : ℕ) (G : RationalMatrixData d)
    (C : IntegerRectData (r * d) (m * d)) (w : ℚ) :
    (encodeRationalMatrixData (costedPreparedShaping t B c G C w).value).length ≤ (costedPreparedShaping t B c G C w).steps := by
  let P := costedPreparedShapingSchedule t B c
  let D := costedIntegerRectToRational C
  let N := costedRationalMetricNormalization P.value.normalizationPrecision G D.value
  have h := costedRationalShapingApprox_length_le_steps P.value.shapingPrecision N.value w
  rw [costedPreparedShaping, Costed.bind_value, Costed.bind_steps, Costed.bind_value, Costed.bind_steps, Costed.bind_value, Costed.bind_steps]
  change (encodeRationalMatrixData (costedRationalShapingApprox P.value.shapingPrecision N.value w).value).length ≤
    P.steps + (D.steps + (N.steps + (costedRationalShapingApprox P.value.shapingPrecision N.value w).steps))
  omega

theorem polyBound_preparedNormalizationBudget {d r m L t B c : ℕ → ℕ}
    (hd : PolynomialCostBound d) (hr : PolynomialCostBound r) (hm : PolynomialCostBound m) (hL : PolynomialCostBound L)
    (ht : PolynomialCostBound t) (hB : PolynomialCostBound B) (hc : PolynomialCostBound c) :
    PolynomialCostBound (fun x => preparedNormalizationBudget (d x) (r x) (m x) (L x) (t x) (B x) (c x)) :=
  polyBound_rationalMetricNormalizationBudget hd hr hm ((hd.mul hd).mul hL) (hL.add (PolynomialCostBound.const 2))
    (polyBound_metricShapingConversionPrecision ht hB hc)

theorem polyBound_preparedShapingBudget {d r m L t B c : ℕ → ℕ}
    (hd : PolynomialCostBound d) (hr : PolynomialCostBound r) (hm : PolynomialCostBound m) (hL : PolynomialCostBound L)
    (ht : PolynomialCostBound t) (hB : PolynomialCostBound B) (hc : PolynomialCostBound c) :
    PolynomialCostBound (fun x => preparedShapingBudget (d x) (r x) (m x) (L x) (t x) (B x) (c x)) := by
  have hN := polyBound_preparedNormalizationBudget hd hr hm hL ht hB hc
  exact (((polyBound_preparedShapingScheduleBudget ht hB hc).add
    (polyBound_rationalRectTraversalBudget (hr.mul hd) (hm.mul hd) (hL.add (PolynomialCostBound.const 1)))).add hN).add
      (polyBound_rationalShapingBudget (hr.mul hd) (hm.mul hd) (hL.add hN) (ht.add (PolynomialCostBound.const 1)))

theorem preparedNormalizationBudget_mono {d d' r r' m m' L L' t t' B B' c c' : ℕ}
    (hd : d ≤ d') (hr : r ≤ r') (hm : m ≤ m') (hL : L ≤ L') (ht : t ≤ t') (hB : B ≤ B') (hc : c ≤ c') :
    preparedNormalizationBudget d r m L t B c ≤ preparedNormalizationBudget d' r' m' L' t' B' c' :=
  rationalMetricNormalizationBudget_mono hd hr hm (by gcongr) (by omega) (by unfold metricShapingConversionPrecision; omega)

theorem preparedShapingBudget_mono {d d' r r' m m' L L' t t' B B' c c' : ℕ}
    (hd : d ≤ d') (hr : r ≤ r') (hm : m ≤ m') (hL : L ≤ L') (ht : t ≤ t') (hB : B ≤ B') (hc : c ≤ c') :
    preparedShapingBudget d r m L t B c ≤ preparedShapingBudget d' r' m' L' t' B' c' := by
  have hN := preparedNormalizationBudget_mono hd hr hm hL ht hB hc
  apply Nat.add_le_add
  · apply Nat.add_le_add
    · apply Nat.add_le_add
      · unfold preparedShapingScheduleBudget
        gcongr
      · exact rationalRectTraversalBudget_mono (Nat.mul_le_mul hr hd) (Nat.mul_le_mul hm hd) (by omega)
    · exact hN
  · exact rationalShapingBudget_mono (Nat.mul_le_mul hr hd) (Nat.mul_le_mul hm hd) (Nat.add_le_add hL hN) (by omega)

end GeometricGaussianLHL

end PreparedShapingCost

section CanonicalAlgebraicData

/-!
## Stored finite algebraic input for the canonical algorithm

The data contain algebraic metric entries, an integral coefficient table and an
algebraic width. Their semantic view is the existing canonical input. All size
bounds below refer to the actual binary encoding of these data.
-/

namespace GeometricGaussianLHL

abbrev AlgebraicMatrixData (d : ℕ) := Vector (Vector AlgebraicRealInput d) d

def algebraicMatrixOfData {d : ℕ} (D : AlgebraicMatrixData d) : Matrix (Fin d) (Fin d) AlgebraicRealInput :=
  fun i j => (D.get i).get j

def algebraicMatrixData {d : ℕ} (M : Matrix (Fin d) (Fin d) AlgebraicRealInput) : AlgebraicMatrixData d :=
  Vector.ofFn (fun i => Vector.ofFn (M i))

theorem algebraicMatrixOfData_data {d : ℕ} (M : Matrix (Fin d) (Fin d) AlgebraicRealInput) :
    algebraicMatrixOfData (algebraicMatrixData M) = M := by
  ext i j
  simp [algebraicMatrixOfData, algebraicMatrixData, Vector.get]
  rfl

structure CanonicalAlgebraicData (d r m : ℕ) where
  metric : AlgebraicMatrixData d
  coefficients : IntegerRectData (r * d) (m * d)
  width : AlgebraicRealInput

namespace CanonicalAlgebraicData
variable {d r m : ℕ} (I : CanonicalAlgebraicData d r m)

def toInput : CanonicalAlgebraicInput d r m :=
  ⟨algebraicMatrixOfData I.metric, integerRectMatrixOfData I.coefficients, I.width⟩

def encode : List Bool :=
  encodeNatBits d ++ encodeNatBits r ++ encodeNatBits m ++
    encodeVectorBits (encodeVectorBits AlgebraicRealInput.encode) I.metric ++
    encodeIntegerRectData I.coefficients ++ I.width.encode

def inputLength : ℕ := I.encode.length

def metricLength : ℕ := ∑ i, ∑ j, (algebraicMatrixOfData I.metric i j).encode.length

theorem encode_length : I.inputLength = 2 * d.size + 2 * r.size + 2 * m.size + 3 +
    I.metricLength + (encodeIntegerRectData I.coefficients).length + I.width.encode.length := by
  simp only [inputLength, encode, List.length_append, encodeNatBits_length, encodeVectorBits_length_sum,
    metricLength, algebraicMatrixOfData]
  omega

theorem parts_le : I.metricLength ≤ I.inputLength ∧
    (encodeIntegerRectData I.coefficients).length ≤ I.inputLength ∧ I.width.encode.length ≤ I.inputLength := by
  rw [I.encode_length]
  omega

theorem metric_entry_length_le (i j : Fin d) :
    (algebraicMatrixOfData I.metric i j).encode.length ≤ I.inputLength := by
  have h := (Finset.single_le_sum (fun k _ => Nat.zero_le (algebraicMatrixOfData I.metric i k).encode.length) (Finset.mem_univ j)).trans
    (Finset.single_le_sum (fun k _ => Nat.zero_le (∑ l, (algebraicMatrixOfData I.metric k l).encode.length)) (Finset.mem_univ i))
  exact h.trans I.parts_le.1

theorem metric_count_le : d * d ≤ I.inputLength := by
  have h : d * d ≤ I.metricLength := by
    calc
      _ = ∑ _i : Fin d, ∑ _j : Fin d, 1 := by simp
      _ ≤ _ := Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => by
        have h := (algebraicMatrixOfData I.metric i j).encode_length
        omega))
  exact h.trans I.parts_le.1

theorem dimension_le : d ≤ I.inputLength := (Nat.le_mul_self d).trans I.metric_count_le

theorem coefficient_count_le : (r * d) * (m * d) ≤ I.inputLength := by
  have h := encodeIntegerRectData_length I.coefficients
  have h' := I.parts_le.2.1
  omega

theorem coefficientBits_le : I.toInput.coefficientBits ≤ I.inputLength := by
  have h := encodeIntegerRectData_length I.coefficients
  have h' := I.parts_le.2.1
  change (∑ i, ∑ j, (integerRectMatrixOfData I.coefficients i j).natAbs.size) ≤ _
  omega

theorem widthBits_le : I.width.endpointBits ≤ I.inputLength :=
  (I.width.endpointBits_le.trans I.width.inputSize_le_encode_length).trans I.parts_le.2.2

theorem metricSize_le : algebraicMatrixDataSize I.toInput.metric ≤ 2 * I.inputLength + 1 := by
  have hd := I.dimension_le
  have hm := I.parts_le.1
  change d + 1 + I.metricLength ≤ _
  omega

theorem multiplicities_le (hd : 0 < d) (hr : 0 < r) (hm : 0 < m) :
    r ≤ I.inputLength ∧ m ≤ I.inputLength := by
  have hrd : r ≤ r * d := by nlinarith
  have hmd : m ≤ m * d := by nlinarith
  have hp := Nat.mul_pos hr hd
  have hq := Nat.mul_pos hm hd
  have hleft : r * d ≤ (r * d) * (m * d) := by nlinarith
  have hright : m * d ≤ (r * d) * (m * d) := by nlinarith
  exact ⟨(hrd.trans hleft).trans I.coefficient_count_le, (hmd.trans hright).trans I.coefficient_count_le⟩

def metricLengths : List ℕ := I.metric.toList.flatMap (fun row => row.toList.map (fun x => x.encode.length))
def coefficientSizes : List ℕ := I.coefficients.toList.flatMap (fun row => row.toList.map (fun x => x.natAbs.size))

theorem metricLengths_length : I.metricLengths.length = d * d := by
  simp [metricLengths, List.length_flatMap]

theorem coefficientSizes_length : I.coefficientSizes.length = (r * d) * (m * d) := by
  simp [coefficientSizes, List.length_flatMap]

private theorem sum_flatMap_nat {α : Type*} (xs : List α) (f : α → List ℕ) :
    (xs.flatMap f).sum = (xs.map (fun x => (f x).sum)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

private theorem vector_sum_map {α : Type*} {n : ℕ} (v : Vector α n) (f : α → ℕ) :
    (v.toList.map f).sum = ∑ i, f (v.get i) := by
  have hv : v.toList = List.ofFn (fun i => v.get i) := by
    rw [← Vector.toList_ofFn]
    congr 1
    ext i
    simp [Vector.get]
  rw [hv, List.map_ofFn, List.sum_ofFn]
  rfl

theorem metricLengths_sum : I.metricLengths.sum = I.metricLength := by
  simp only [metricLengths, sum_flatMap_nat, vector_sum_map, metricLength, algebraicMatrixOfData]

theorem coefficientSizes_sum : I.coefficientSizes.sum = I.toInput.coefficientBits := by
  simp only [coefficientSizes, sum_flatMap_nat, vector_sum_map, toInput,
    CanonicalAlgebraicInput.coefficientBits, integerCoefficientMagnitudeBits, integerRectMatrixOfData]

end CanonicalAlgebraicData

theorem PolynomialCostBound.comp {f g : ℕ → ℕ} (hf : PolynomialCostBound f) (hg : PolynomialCostBound g) :
    PolynomialCostBound (fun x => f (g x)) := by
  obtain ⟨C, e, h⟩ := hf.exists_mul_pow_bound
  exact ((PolynomialCostBound.const C).mul ((hg.add (PolynomialCostBound.const 1)).pow e)).mono (fun x => h (g x))

end GeometricGaussianLHL

end CanonicalAlgebraicData

section CanonicalPreparedCost

/-!
## Canonical accuracy and cost of the same prepared execution

The existing canonical input bounds imply full row rank of the computed
normalized matrix. The execution then satisfies both the composed arithmetic
cost bound and the canonical approximation theorem. `CanonicalFiniteCost` also composes the preceding
finite algebraic input preparation.
-/

open Module NumberField
open scoped MatrixOrder Matrix.Norms.L2Operator
namespace GeometricGaussianLHL

theorem integerRect_entry_bits_le_encoded {p q : ℕ} (C : IntegerRectData p q) (i : Fin p) (j : Fin q) :
    (integerRectMatrixOfData C i j).natAbs.size ≤ (encodeIntegerRectData C).length := by
  have h := (Finset.single_le_sum (fun k _ => Nat.zero_le (integerRectMatrixOfData C i k).natAbs.size) (Finset.mem_univ j)).trans
    (Finset.single_le_sum (fun k _ => Nat.zero_le (∑ l, (integerRectMatrixOfData C k l).natAbs.size)) (Finset.mem_univ i))
  rw [encodeIntegerRectData_length]
  omega

namespace CanonicalShapingInput
variable {K : Type*} [Field K] [NumberField K] {d r m : ℕ} {b : Basis (Fin d) ℤ (𝓞 K)}
  {A : Matrix (Fin r) (Fin m) (𝓞 K)} {hrm : r ≤ m} {w : ℝ} {t : ℕ}
  (I : CanonicalShapingInput K b A hrm w t)

theorem normalized_gram_isUnit (hA : Function.Surjective A.mulVec) (hr : 0 < r) (hw : 0 < w) :
    let Q := rationalMetricNormalizedApprox (metricShapingConversionPrecision t I.B I.c) I.metric
      (I.coefficients.map (Int.castRingHom ℚ))
    IsUnit (Q * Q.transpose).det := by
  rw [I.hcoeff]
  let s := 2 * (t + 1) + 11 * (I.B + 1) + 7
  let Q := rationalMetricNormalizedApprox (metricShapingConversionPrecision t I.B I.c) I.metric
    ((ringCoefficientMatrix b A).map (Int.castRingHom ℚ))
  have hQ : ‖Q.map (Rat.castHom ℝ) - canonicalGramNormalizedMatrix K b A‖ ≤ 1 / (2 : ℝ) ^ s :=
    rationalMetricNormalizedApprox_canonical_error K b A s I.c I.metric I.hmetricPos
      I.hroot I.hinvroot I.hmetricRoot I.hmetricInvroot I.hGi I.hXi I.hC I.hmetric
  have hinput : ‖canonicalGramNormalizedMatrix K b A - Q.map (Rat.castHom ℝ)‖ + |w - (I.width : ℝ)| ≤
      1 / (2 : ℝ) ^ (2 * (t + 1) + 11 * (I.B + 1) + 6) := by
    rw [norm_sub_rev]
    apply (add_le_add hQ I.hwidth).trans_eq
    dsimp only [s]
    rw [show 2 * (t + 1) + 11 * (I.B + 1) + 7 = (2 * (t + 1) + 11 * (I.B + 1) + 6) + 1 by omega,
      pow_succ]
    ring
  exact (realShapingInput_approximation_data (canonicalGramNormalizedMatrix K b A) w Q I.width
    (Nat.mul_pos hr (integralBasis_dimension_pos K b)) (canonicalGramNormalizedMatrix_gram_isUnit K b A hA)
    hw I.hwidthPos t I.B I.hAn I.hAi I.hwB hinput).1

def execution : Costed (RationalMatrixData (m * d)) :=
  costedPreparedShaping t I.B I.c (rationalMatrixData I.metric) (integerRectMatrixData I.coefficients) I.width

def operandBits : ℕ :=
  (encodeRationalMatrixData (rationalMatrixData I.metric)).length +
    (encodeIntegerRectData (integerRectMatrixData I.coefficients)).length + (encodeRatBits I.width).length

theorem execution_output : (rationalMatrixOfData I.execution.value).map (Rat.castHom ℝ) = I.output := by
  rw [execution, costedPreparedShaping_data, rationalMatrixOfData_data, rationalMatrixOfData_data, integerRectMatrixOfData_data]
  rfl

theorem execution_steps_le (hA : Function.Surjective A.mulVec) (hr : 0 < r) (hw : 0 < w) :
    I.execution.steps ≤ preparedShapingBudget d r m I.operandBits t I.B I.c := by
  have hm (i j) : rationalMagnitudeBits (I.metric i j) ≤ I.operandBits := by
    have h := rationalMatrixEntryBits_le_encoded (rationalMatrixData I.metric) i j
    rw [rationalMatrixOfData_data] at h
    unfold operandBits
    omega
  have hc (i j) : (I.coefficients i j).natAbs.size ≤ I.operandBits := by
    have h := integerRect_entry_bits_le_encoded (integerRectMatrixData I.coefficients) i j
    rw [integerRectMatrixOfData_data] at h
    unfold operandBits
    omega
  have hwL : rationalMagnitudeBits I.width ≤ I.operandBits := by
    have h := encodeRatBits_length I.width
    unfold operandBits
    omega
  apply costedPreparedShaping_steps_le t I.B I.c (rationalMatrixData I.metric) (integerRectMatrixData I.coefficients) I.width I.operandBits
  · rw [rationalMatrixOfData_data]
    exact I.hmetricPos
  · rw [rationalMatrixOfData_data]
    exact hm
  · rw [integerRectMatrixOfData_data]
    exact hc
  · exact hwL
  · exact Nat.mul_pos hr (integralBasis_dimension_pos K b)
  · exact I.hwidthPos.ne'
  · rw [rationalMatrixOfData_data, integerRectMatrixOfData_data]
    exact I.normalized_gram_isUnit hA hr hw

theorem execution_certificate (hA : Function.Surjective A.mulVec) (hr : 0 < r) (hw : 0 < w) :
    I.execution.steps ≤ preparedShapingBudget d r m I.operandBits t I.B I.c ∧
      (encodeRationalMatrixData I.execution.value).length ≤ preparedShapingBudget d r m I.operandBits t I.B I.c ∧
      ((rationalMatrixOfData I.execution.value).map (Rat.castHom ℝ)).PosDef ∧
      ‖isometricTransportMap (canonicalGramEuclideanIsometry K b m) (canonicalGramEuclideanIsometry K b m)
        (Matrix.toEuclideanLin ((rationalMatrixOfData I.execution.value).map (Rat.castHom ℝ))).toContinuousLinearMap -
          (canonicalGramShapingShape K b A hA hr w hw).toContinuousLinearMap‖ ≤ 1 / (2 : ℝ) ^ t := by
  have hs := I.execution_steps_le hA hr hw
  refine ⟨hs, (costedPreparedShaping_length_le_steps t I.B I.c (rationalMatrixData I.metric)
    (integerRectMatrixData I.coefficients) I.width).trans hs, ?_⟩
  rw [I.execution_output]
  exact I.output_certificate hA hr hw

end CanonicalShapingInput
end GeometricGaussianLHL

end CanonicalPreparedCost

section CanonicalInputScanCost

/-!
## Scanning the finite canonical input

The scan measures encoded metric lengths, integral coefficient bits and width
endpoint bits. Charged sums and two additions produce the exact quantities
used by the existing conditioning and precision definitions.
-/

namespace GeometricGaussianLHL

structure CanonicalInputMeasures where
  metricSize : ℕ
  coefficientBits : ℕ
  widthBits : ℕ

def canonicalInputMeasures {d r m : ℕ} (I : CanonicalAlgebraicData d r m) : CanonicalInputMeasures :=
  ⟨algebraicMatrixDataSize I.toInput.metric, I.toInput.coefficientBits, I.width.endpointBits⟩

def costedCanonicalInputScan {d r m : ℕ} (I : CanonicalAlgebraicData d r m) : Costed CanonicalInputMeasures :=
  let ms := costedNatSum I.metricLengths
  let cs := costedNatSum I.coefficientSizes
  let dim := costedNatAdd d 1
  let total := costedNatAdd dim.value ms.value
  ⟨⟨total.value, cs.value, I.width.endpointBits⟩,
    4 * I.inputLength + 1 + ms.steps + cs.steps + dim.steps + total.steps⟩

theorem costedCanonicalInputScan_value {d r m : ℕ} (I : CanonicalAlgebraicData d r m) :
    (costedCanonicalInputScan I).value = canonicalInputMeasures I := by
  simp only [costedCanonicalInputScan, costedNatSum_value, CanonicalAlgebraicData.metricLengths_sum,
    CanonicalAlgebraicData.coefficientSizes_sum, costedNatAdd]
  rfl

def canonicalInputScanBudget (N : ℕ) : ℕ :=
  4 * N + 1 + 2 * natSumBudget N N + 2 * (2 * (2 * N + 1) + 1) ^ 2

theorem costedCanonicalInputScan_steps_le {d r m : ℕ} (I : CanonicalAlgebraicData d r m) :
    (costedCanonicalInputScan I).steps ≤ canonicalInputScanBudget I.inputLength := by
  let N := I.inputLength
  have hml : I.metricLengths.length ≤ N := by rw [I.metricLengths_length]; exact I.metric_count_le
  have hcl : I.coefficientSizes.length ≤ N := by rw [I.coefficientSizes_length]; exact I.coefficient_count_le
  have hms : I.metricLengths.sum ≤ N := by rw [I.metricLengths_sum]; exact I.parts_le.1
  have hcs : I.coefficientSizes.sum ≤ N := by rw [I.coefficientSizes_sum]; exact I.coefficientBits_le
  have hm := (costedNatSum_steps_le I.metricLengths N hms).trans
    (show natSumBudget I.metricLengths.length N ≤ natSumBudget N N by unfold natSumBudget; gcongr)
  have hc := (costedNatSum_steps_le I.coefficientSizes N hcs).trans
    (show natSumBudget I.coefficientSizes.length N ≤ natSumBudget N N by unfold natSumBudget; gcongr)
  have hd := I.dimension_le
  have hs := I.parts_le.1
  have h₁ := costedNatAdd_steps_le d 1 (2 * N + 1) (by dsimp [N]; omega) (by omega)
  have h₂ := costedNatAdd_steps_le (d + 1) I.metricLength (2 * N + 1) (by dsimp [N]; omega) (by dsimp [N]; omega)
  unfold costedCanonicalInputScan
  dsimp only
  rw [costedNatSum_value, I.metricLengths_sum]
  dsimp only [costedNatAdd] at h₁ h₂ ⊢
  change _ ≤ 4 * N + 1 + 2 * natSumBudget N N + 2 * (2 * (2 * N + 1) + 1) ^ 2
  dsimp only [N] at *
  omega

theorem polyBound_canonicalInputScanBudget : PolynomialCostBound canonicalInputScanBudget :=
  (((((PolynomialCostBound.const 4).mul PolynomialCostBound.id).add (PolynomialCostBound.const 1)).add
    ((PolynomialCostBound.const 2).mul (polyBound_natSumBudget PolynomialCostBound.id PolynomialCostBound.id)))).add
      ((PolynomialCostBound.const 2).mul ((((PolynomialCostBound.const 2).mul
        (((PolynomialCostBound.const 2).mul PolynomialCostBound.id).add (PolynomialCostBound.const 1))).add (PolynomialCostBound.const 1)).pow 2))

end GeometricGaussianLHL

end CanonicalInputScanCost

section CanonicalBudgetCost

/-!
## Computing the canonical conditioning and shaping budgets

Twenty-six charged natural additions and multiplications compute the budgets
from the measured finite input. Monotonicity and polynomial closure apply to
the actual sum of those primitive costs.
-/
namespace GeometricGaussianLHL

structure CanonicalBudgets where
  conditioning : ℕ
  shaping : ℕ
  metric : ℕ

def canonicalBudgets (d r m : ℕ) (M : CanonicalInputMeasures) : CanonicalBudgets :=
  let h := (d + 1) * (d + M.metricSize)
  ⟨h, canonicalShapingBudget (r * d) (m * d) M.coefficientBits h M.widthBits,
    canonicalMetricBudget (r * d) (m * d) M.coefficientBits h⟩

def costedCanonicalBudgets (d r m : ℕ) (M : CanonicalInputMeasures) : Costed CanonicalBudgets :=
  let p := costedNatMul r d
  let q := costedNatMul m d
  let d1 := costedNatAdd d 1
  let ds := costedNatAdd d M.metricSize
  let h := costedNatMul d1.value ds.value
  let pp := costedNatMul p.value p.value
  let u2 := costedNatMul 2 M.coefficientBits
  let qu := costedNatAdd q.value u2.value
  let qu4 := costedNatAdd qu.value 4
  let g := costedNatMul pp.value qu4.value
  let p2 := costedNatMul 2 p.value
  let g4 := costedNatMul 4 g.value
  let norm := costedNatAdd p2.value g4.value
  let pp2 := costedNatMul 2 pp.value
  let p5 := costedNatMul 5 p.value
  let pg5 := costedNatMul p5.value g.value
  let inv := costedNatAdd pp2.value pg5.value
  let h4 := costedNatMul 4 h.value
  let norm2 := costedNatMul 2 norm.value
  let inv2 := costedNatMul 2 inv.value
  let hs := costedNatAdd h4.value norm2.value
  let hsi := costedNatAdd hs.value inv2.value
  let B := costedNatAdd hsi.value M.widthBits
  let h2 := costedNatMul 2 h.value
  let c0 := costedNatAdd h2.value norm.value
  let c := costedNatAdd c0.value 1
  ⟨⟨h.value, B.value, c.value⟩,
    p.steps + q.steps + d1.steps + ds.steps + h.steps + pp.steps + u2.steps + qu.steps + qu4.steps +
    g.steps + p2.steps + g4.steps + norm.steps + pp2.steps + p5.steps + pg5.steps + inv.steps + h4.steps +
    norm2.steps + inv2.steps + hs.steps + hsi.steps + B.steps + h2.steps + c0.steps + c.steps⟩

theorem costedCanonicalBudgets_value (d r m : ℕ) (M : CanonicalInputMeasures) :
    (costedCanonicalBudgets d r m M).value = canonicalBudgets d r m M := by
  simp only [costedCanonicalBudgets, costedNatAdd, costedNatMul, canonicalBudgets,
    canonicalShapingBudget, canonicalMetricBudget, coefficientNormBudget, coefficientInverseBudget,
    coefficientGramBitsBound, Nat.mul_assoc]

theorem canonicalBudgets_input {d r m : ℕ} (I : CanonicalAlgebraicData d r m) :
    canonicalBudgets d r m (canonicalInputMeasures I) =
      ⟨I.toInput.conditioning, I.toInput.shapingBudget, I.toInput.metricBudget⟩ := rfl

theorem PolynomialCostBound.natSize {f : ℕ → ℕ} (hf : PolynomialCostBound f) :
    PolynomialCostBound (fun n => (f n).size) :=
  hf.mono (fun _ => Nat.size_le.mpr (Nat.lt_two_pow_self))

theorem polyBound_costedCanonicalBudgets {d r m S U W : ℕ → ℕ}
    (hd : PolynomialCostBound d) (hr : PolynomialCostBound r) (hm : PolynomialCostBound m)
    (hS : PolynomialCostBound S) (hU : PolynomialCostBound U) (hW : PolynomialCostBound W) :
    PolynomialCostBound (fun n => (costedCanonicalBudgets (d n) (r n) (m n) ⟨S n, U n, W n⟩).steps) := by
  have cost_p := ((hr.natSize.add hd.natSize).add (PolynomialCostBound.const 1)).pow 2
  have value_p := hr.mul hd
  have cost_q := ((hm.natSize.add hd.natSize).add (PolynomialCostBound.const 1)).pow 2
  have value_q := hm.mul hd
  have cost_d1 := (hd.natSize.add (PolynomialCostBound.const 1).natSize).add (PolynomialCostBound.const 1)
  have value_d1 := hd.add (PolynomialCostBound.const 1)
  have cost_ds := (hd.natSize.add hS.natSize).add (PolynomialCostBound.const 1)
  have value_ds := hd.add hS
  have cost_h := ((value_d1.natSize.add value_ds.natSize).add (PolynomialCostBound.const 1)).pow 2
  have value_h := value_d1.mul value_ds
  have cost_pp := ((value_p.natSize.add value_p.natSize).add (PolynomialCostBound.const 1)).pow 2
  have value_pp := value_p.mul value_p
  have cost_u2 := (((PolynomialCostBound.const 2).natSize.add hU.natSize).add (PolynomialCostBound.const 1)).pow 2
  have value_u2 := (PolynomialCostBound.const 2).mul hU
  have cost_qu := (value_q.natSize.add value_u2.natSize).add (PolynomialCostBound.const 1)
  have value_qu := value_q.add value_u2
  have cost_qu4 := (value_qu.natSize.add (PolynomialCostBound.const 4).natSize).add (PolynomialCostBound.const 1)
  have value_qu4 := value_qu.add (PolynomialCostBound.const 4)
  have cost_g := ((value_pp.natSize.add value_qu4.natSize).add (PolynomialCostBound.const 1)).pow 2
  have value_g := value_pp.mul value_qu4
  have cost_p2 := (((PolynomialCostBound.const 2).natSize.add value_p.natSize).add (PolynomialCostBound.const 1)).pow 2
  have value_p2 := (PolynomialCostBound.const 2).mul value_p
  have cost_g4 := (((PolynomialCostBound.const 4).natSize.add value_g.natSize).add (PolynomialCostBound.const 1)).pow 2
  have value_g4 := (PolynomialCostBound.const 4).mul value_g
  have cost_norm := (value_p2.natSize.add value_g4.natSize).add (PolynomialCostBound.const 1)
  have value_norm := value_p2.add value_g4
  have cost_pp2 := (((PolynomialCostBound.const 2).natSize.add value_pp.natSize).add (PolynomialCostBound.const 1)).pow 2
  have value_pp2 := (PolynomialCostBound.const 2).mul value_pp
  have cost_p5 := (((PolynomialCostBound.const 5).natSize.add value_p.natSize).add (PolynomialCostBound.const 1)).pow 2
  have value_p5 := (PolynomialCostBound.const 5).mul value_p
  have cost_pg5 := ((value_p5.natSize.add value_g.natSize).add (PolynomialCostBound.const 1)).pow 2
  have value_pg5 := value_p5.mul value_g
  have cost_inv := (value_pp2.natSize.add value_pg5.natSize).add (PolynomialCostBound.const 1)
  have value_inv := value_pp2.add value_pg5
  have cost_h4 := (((PolynomialCostBound.const 4).natSize.add value_h.natSize).add (PolynomialCostBound.const 1)).pow 2
  have value_h4 := (PolynomialCostBound.const 4).mul value_h
  have cost_norm2 := (((PolynomialCostBound.const 2).natSize.add value_norm.natSize).add (PolynomialCostBound.const 1)).pow 2
  have value_norm2 := (PolynomialCostBound.const 2).mul value_norm
  have cost_inv2 := (((PolynomialCostBound.const 2).natSize.add value_inv.natSize).add (PolynomialCostBound.const 1)).pow 2
  have value_inv2 := (PolynomialCostBound.const 2).mul value_inv
  have cost_hs := (value_h4.natSize.add value_norm2.natSize).add (PolynomialCostBound.const 1)
  have value_hs := value_h4.add value_norm2
  have cost_hsi := (value_hs.natSize.add value_inv2.natSize).add (PolynomialCostBound.const 1)
  have value_hsi := value_hs.add value_inv2
  have cost_B := (value_hsi.natSize.add hW.natSize).add (PolynomialCostBound.const 1)
  have cost_h2 := (((PolynomialCostBound.const 2).natSize.add value_h.natSize).add (PolynomialCostBound.const 1)).pow 2
  have value_h2 := (PolynomialCostBound.const 2).mul value_h
  have cost_c0 := (value_h2.natSize.add value_norm.natSize).add (PolynomialCostBound.const 1)
  have value_c0 := value_h2.add value_norm
  have cost_c := (value_c0.natSize.add (PolynomialCostBound.const 1).natSize).add (PolynomialCostBound.const 1)
  exact (((((((((((((((((((((((((cost_p.add cost_q).add cost_d1).add cost_ds).add cost_h).add cost_pp).add cost_u2).add cost_qu).add cost_qu4).add cost_g).add cost_p2).add cost_g4).add cost_norm).add cost_pp2).add cost_p5).add cost_pg5).add cost_inv).add cost_h4).add cost_norm2).add cost_inv2).add cost_hs).add cost_hsi).add cost_B).add cost_h2).add cost_c0).add cost_c)

theorem costedCanonicalBudgets_steps_mono {d e r s m n S T U V W X : ℕ}
    (hd : d ≤ e) (hr : r ≤ s) (hm : m ≤ n) (hS : S ≤ T) (hU : U ≤ V) (hW : W ≤ X) :
    (costedCanonicalBudgets d r m ⟨S, U, W⟩).steps ≤
      (costedCanonicalBudgets e s n ⟨T, V, X⟩).steps := by
  dsimp only [costedCanonicalBudgets, costedNatAdd, costedNatMul]
  gcongr <;> apply Nat.size_le_size <;> gcongr

def canonicalBudgetArithmeticBudget (N : ℕ) : ℕ :=
  (costedCanonicalBudgets N N N ⟨2 * N + 1, N, N⟩).steps

theorem polyBound_canonicalBudgetArithmeticBudget : PolynomialCostBound canonicalBudgetArithmeticBudget :=
  polyBound_costedCanonicalBudgets PolynomialCostBound.id PolynomialCostBound.id PolynomialCostBound.id
    (((PolynomialCostBound.const 2).mul PolynomialCostBound.id).add (PolynomialCostBound.const 1))
    PolynomialCostBound.id PolynomialCostBound.id

theorem costedCanonicalBudgets_input_steps_le {d r m : ℕ} (I : CanonicalAlgebraicData d r m)
    (hd : 0 < d) (hr : 0 < r) (hm : 0 < m) :
    (costedCanonicalBudgets d r m (canonicalInputMeasures I)).steps ≤ canonicalBudgetArithmeticBudget I.inputLength :=
  costedCanonicalBudgets_steps_mono I.dimension_le (I.multiplicities_le hd hr hm).1
    (I.multiplicities_le hd hr hm).2 I.metricSize_le I.coefficientBits_le I.widthBits_le

theorem canonicalBudgets_mono {d e r s m n S T U V W X : ℕ}
    (hd : d ≤ e) (hr : r ≤ s) (hm : m ≤ n) (hS : S ≤ T) (hU : U ≤ V) (hW : W ≤ X) :
    (canonicalBudgets d r m ⟨S, U, W⟩).conditioning ≤ (canonicalBudgets e s n ⟨T, V, X⟩).conditioning ∧
    (canonicalBudgets d r m ⟨S, U, W⟩).shaping ≤ (canonicalBudgets e s n ⟨T, V, X⟩).shaping ∧
    (canonicalBudgets d r m ⟨S, U, W⟩).metric ≤ (canonicalBudgets e s n ⟨T, V, X⟩).metric := by
  dsimp only [canonicalBudgets, canonicalShapingBudget, canonicalMetricBudget,
    coefficientNormBudget, coefficientInverseBudget, coefficientGramBitsBound]
  constructor
  · gcongr
  constructor <;> gcongr

theorem polyBound_canonicalBudgets {d r m S U W : ℕ → ℕ}
    (hd : PolynomialCostBound d) (hr : PolynomialCostBound r) (hm : PolynomialCostBound m)
    (hS : PolynomialCostBound S) (hU : PolynomialCostBound U) (hW : PolynomialCostBound W) :
    PolynomialCostBound (fun n => (canonicalBudgets (d n) (r n) (m n) ⟨S n, U n, W n⟩).conditioning) ∧
    PolynomialCostBound (fun n => (canonicalBudgets (d n) (r n) (m n) ⟨S n, U n, W n⟩).shaping) ∧
    PolynomialCostBound (fun n => (canonicalBudgets (d n) (r n) (m n) ⟨S n, U n, W n⟩).metric) := by
  have hp := hr.mul hd
  have hq := hm.mul hd
  have hh := (hd.add (PolynomialCostBound.const 1)).mul (hd.add hS)
  have hg := (hp.mul hp).mul ((hq.add ((PolynomialCostBound.const 2).mul hU)).add (PolynomialCostBound.const 4))
  have hn := ((PolynomialCostBound.const 2).mul hp).add ((PolynomialCostBound.const 4).mul hg)
  have hi := (((PolynomialCostBound.const 2).mul hp).mul hp).add (((PolynomialCostBound.const 5).mul hp).mul hg)
  exact ⟨hh, ((((PolynomialCostBound.const 4).mul hh).add ((PolynomialCostBound.const 2).mul hn)).add
    ((PolynomialCostBound.const 2).mul hi)).add hW,
    (((PolynomialCostBound.const 2).mul hh).add hn).add (PolynomialCostBound.const 1)⟩

end GeometricGaussianLHL

end CanonicalBudgetCost

section AlgebraicPreparationCost

/-!
## Charged preparation of algebraic metric entries and width

The schedule computes both bisection precisions. Each matrix entry charges its
index comparison and root approximation, including recomputation below the
diagonal. Stored matrix traversal and serialization are charged explicitly.
-/
set_option backward.isDefEq.respectTransparency false
namespace GeometricGaussianLHL

structure AlgebraicPreparationPrecisions where
  metric : ℕ
  width : ℕ

def algebraicPreparationPrecisions (d h B c t : ℕ) : AlgebraicPreparationPrecisions :=
  ⟨(2 * metricShapingConversionPrecision t B c + 2 * c) + (h + 1) + d,
    2 * (t + 1) + 11 * (B + 1) + 7⟩

def costedAlgebraicPreparationPrecisions (d h B c t : ℕ) : Costed AlgebraicPreparationPrecisions :=
  let u := costedNatAdd t 1
  let v := costedNatAdd B 1
  let a := costedNatMul 2 u.value
  let b := costedNatMul 11 v.value
  let w0 := costedNatAdd a.value b.value
  let w := costedNatAdd w0.value 7
  let cc := costedNatMul 2 c
  let q0 := costedNatAdd w.value cc.value
  let q := costedNatAdd q0.value 3
  let q2 := costedNatMul 2 q.value
  let p0 := costedNatAdd q2.value cc.value
  let hp := costedNatAdd h 1
  let p1 := costedNatAdd p0.value hp.value
  let p := costedNatAdd p1.value d
  ⟨⟨p.value, w.value⟩,
    u.steps + v.steps + a.steps + b.steps + w0.steps + w.steps + cc.steps + q0.steps + q.steps +
    q2.steps + p0.steps + hp.steps + p1.steps + p.steps⟩

theorem costedAlgebraicPreparationPrecisions_value (d h B c t : ℕ) :
    (costedAlgebraicPreparationPrecisions d h B c t).value = algebraicPreparationPrecisions d h B c t := rfl

theorem polyBound_costedAlgebraicPreparationPrecisions {d h B c t : ℕ → ℕ}
    (hd : PolynomialCostBound d) (hh : PolynomialCostBound h) (hB : PolynomialCostBound B)
    (hc : PolynomialCostBound c) (ht : PolynomialCostBound t) :
    PolynomialCostBound (fun n => (costedAlgebraicPreparationPrecisions (d n) (h n) (B n) (c n) (t n)).steps) := by
  have cost_u := (ht.natSize.add (PolynomialCostBound.const 1).natSize).add (PolynomialCostBound.const 1)
  have value_u := ht.add (PolynomialCostBound.const 1)
  have cost_v := (hB.natSize.add (PolynomialCostBound.const 1).natSize).add (PolynomialCostBound.const 1)
  have value_v := hB.add (PolynomialCostBound.const 1)
  have cost_a := (((PolynomialCostBound.const 2).natSize.add value_u.natSize).add (PolynomialCostBound.const 1)).pow 2
  have value_a := (PolynomialCostBound.const 2).mul value_u
  have cost_b := (((PolynomialCostBound.const 11).natSize.add value_v.natSize).add (PolynomialCostBound.const 1)).pow 2
  have value_b := (PolynomialCostBound.const 11).mul value_v
  have cost_w0 := (value_a.natSize.add value_b.natSize).add (PolynomialCostBound.const 1)
  have value_w0 := value_a.add value_b
  have cost_w := (value_w0.natSize.add (PolynomialCostBound.const 7).natSize).add (PolynomialCostBound.const 1)
  have value_w := value_w0.add (PolynomialCostBound.const 7)
  have cost_cc := (((PolynomialCostBound.const 2).natSize.add hc.natSize).add (PolynomialCostBound.const 1)).pow 2
  have value_cc := (PolynomialCostBound.const 2).mul hc
  have cost_q0 := (value_w.natSize.add value_cc.natSize).add (PolynomialCostBound.const 1)
  have value_q0 := value_w.add value_cc
  have cost_q := (value_q0.natSize.add (PolynomialCostBound.const 3).natSize).add (PolynomialCostBound.const 1)
  have value_q := value_q0.add (PolynomialCostBound.const 3)
  have cost_q2 := (((PolynomialCostBound.const 2).natSize.add value_q.natSize).add (PolynomialCostBound.const 1)).pow 2
  have value_q2 := (PolynomialCostBound.const 2).mul value_q
  have cost_p0 := (value_q2.natSize.add value_cc.natSize).add (PolynomialCostBound.const 1)
  have value_p0 := value_q2.add value_cc
  have cost_hp := (hh.natSize.add (PolynomialCostBound.const 1).natSize).add (PolynomialCostBound.const 1)
  have value_hp := hh.add (PolynomialCostBound.const 1)
  have cost_p1 := (value_p0.natSize.add value_hp.natSize).add (PolynomialCostBound.const 1)
  have value_p1 := value_p0.add value_hp
  have cost_p := (value_p1.natSize.add hd.natSize).add (PolynomialCostBound.const 1)
  exact (((((((((((((cost_u.add cost_v).add cost_a).add cost_b).add cost_w0).add cost_w).add cost_cc).add cost_q0).add cost_q).add cost_q2).add cost_p0).add cost_hp).add cost_p1).add cost_p)

theorem costedAlgebraicPreparationPrecisions_steps_mono {d e h i B D c k t u : ℕ}
    (hd : d ≤ e) (hh : h ≤ i) (hB : B ≤ D) (hc : c ≤ k) (ht : t ≤ u) :
    (costedAlgebraicPreparationPrecisions d h B c t).steps ≤
      (costedAlgebraicPreparationPrecisions e i D k u).steps := by
  dsimp only [costedAlgebraicPreparationPrecisions, costedNatAdd, costedNatMul]
  gcongr <;> apply Nat.size_le_size <;> gcongr

theorem algebraicPreparationPrecisions_mono {d e h i B D c k t u : ℕ}
    (hd : d ≤ e) (hh : h ≤ i) (hB : B ≤ D) (hc : c ≤ k) (ht : t ≤ u) :
    (algebraicPreparationPrecisions d h B c t).metric ≤ (algebraicPreparationPrecisions e i D k u).metric ∧
    (algebraicPreparationPrecisions d h B c t).width ≤ (algebraicPreparationPrecisions e i D k u).width := by
  dsimp only [algebraicPreparationPrecisions, metricShapingConversionPrecision]
  constructor <;> gcongr

theorem polyBound_algebraicPreparationPrecisions {d h B c t : ℕ → ℕ}
    (hd : PolynomialCostBound d) (hh : PolynomialCostBound h) (hB : PolynomialCostBound B)
    (hc : PolynomialCostBound c) (ht : PolynomialCostBound t) :
    PolynomialCostBound (fun n => (algebraicPreparationPrecisions (d n) (h n) (B n) (c n) (t n)).metric) ∧
    PolynomialCostBound (fun n => (algebraicPreparationPrecisions (d n) (h n) (B n) (c n) (t n)).width) := by
  have hw := (((PolynomialCostBound.const 2).mul (ht.add (PolynomialCostBound.const 1))).add
    ((PolynomialCostBound.const 11).mul (hB.add (PolynomialCostBound.const 1)))).add (PolynomialCostBound.const 7)
  exact ⟨((((PolynomialCostBound.const 2).mul (polyBound_metricShapingConversionPrecision ht hB hc)).add
    ((PolynomialCostBound.const 2).mul hc)).add (hh.add (PolynomialCostBound.const 1))).add hd, hw⟩

theorem algebraicPreparationBudget_mono {N M : ℕ} (h : N ≤ M) :
    algebraicPreparationBudget N ≤ algebraicPreparationBudget M := by
  unfold algebraicPreparationBudget
  gcongr
  exact algebraicBisectBudget_mono (by omega) (by omega) (by omega)

def costedAlgebraicSymmetricEntry {d : ℕ} (D : AlgebraicMatrixData d) (t : ℕ) (i j : Fin d) : Costed ℚ :=
  (Costed.charge (i.val.size + j.val.size + 1) ()).bind fun _ =>
    if i ≤ j then costedAlgebraicApprox (algebraicMatrixOfData D i j) t
    else costedAlgebraicApprox (algebraicMatrixOfData D j i) t

theorem costedAlgebraicSymmetricEntry_value {d : ℕ} (D : AlgebraicMatrixData d) (t : ℕ) (i j : Fin d) :
    (costedAlgebraicSymmetricEntry D t i j).value = algebraicSymmetricApprox (algebraicMatrixOfData D) t i j := by
  simp only [costedAlgebraicSymmetricEntry, Costed.bind_value, algebraicSymmetricApprox]
  split_ifs <;> exact costedAlgebraicApprox_value _ _

theorem costedAlgebraicSymmetricEntry_steps_le {d : ℕ} (D : AlgebraicMatrixData d) (L t : ℕ)
    (hD : ∀ i j, (algebraicMatrixOfData D i j).encode.length ≤ L) (i j : Fin d) :
    (costedAlgebraicSymmetricEntry D t i j).steps ≤ 2 * d + 1 + algebraicPreparationBudget (L + t) := by
  have hi : i.val.size ≤ d := (Nat.size_le.mpr Nat.lt_two_pow_self).trans i.isLt.le
  have hj : j.val.size ≤ d := (Nat.size_le.mpr Nat.lt_two_pow_self).trans j.isLt.le
  have hb (a b) := (costedAlgebraicApprox_steps_le (algebraicMatrixOfData D a b) t).trans
    (algebraicPreparationBudget_mono (Nat.add_le_add_right (hD a b) t))
  simp only [costedAlgebraicSymmetricEntry, Costed.bind_steps, Costed.charge]
  split_ifs <;> (have h := hb i j; have h' := hb j i; omega)

theorem costedAlgebraicSymmetricEntry_bits {d : ℕ} (D : AlgebraicMatrixData d) (L t : ℕ)
    (hD : ∀ i j, (algebraicMatrixOfData D i j).encode.length ≤ L) (i j : Fin d) :
    rationalMagnitudeBits (costedAlgebraicSymmetricEntry D t i j).value ≤ 14 * L + 4 * t + 11 := by
  have hb (a b) := costedAlgebraicApprox_output_length (algebraicMatrixOfData D a b) t
  simp only [encodeRatBits_length, costedAlgebraicApprox_value] at hb
  rw [costedAlgebraicSymmetricEntry_value]
  unfold algebraicSymmetricApprox
  split_ifs
  · have h := hb i j; have h' := hD i j; omega
  · have h := hb j i; have h' := hD j i; omega

def costedAlgebraicSymmetricMatrix {d : ℕ} (D : AlgebraicMatrixData d) (t : ℕ) : Costed (RationalMatrixData d) :=
  (costedRationalRectOfFn (costedAlgebraicSymmetricEntry D t)).bind fun R =>
    Costed.charge (encodeRationalRectData R).length R

theorem costedAlgebraicSymmetricMatrix_data {d : ℕ} (D : AlgebraicMatrixData d) (t : ℕ) :
    (costedAlgebraicSymmetricMatrix D t).value = rationalMatrixData (algebraicSymmetricApprox (algebraicMatrixOfData D) t) := by
  simp only [costedAlgebraicSymmetricMatrix, Costed.bind_value, Costed.charge,
    costedRationalRectOfFn_data, costedAlgebraicSymmetricEntry_value]
  rfl

def algebraicSymmetricMatrixBudget (d L t : ℕ) : ℕ :=
  rationalRectTraversalBudget d d (2 * d + 1 + algebraicPreparationBudget (L + t)) +
    rationalRectEncodingBudget d d (14 * L + 4 * t + 11)

theorem costedAlgebraicSymmetricMatrix_steps_le {d : ℕ} (D : AlgebraicMatrixData d) (L t : ℕ)
    (hD : ∀ i j, (algebraicMatrixOfData D i j).encode.length ≤ L) :
    (costedAlgebraicSymmetricMatrix D t).steps ≤ algebraicSymmetricMatrixBudget d L t := by
  have hs := costedRationalRectOfFn_steps_le (costedAlgebraicSymmetricEntry D t) _
    (costedAlgebraicSymmetricEntry_steps_le D L t hD)
  have he := rationalRectEncoded_length_le (costedRationalRectOfFn (costedAlgebraicSymmetricEntry D t)).value
    (14 * L + 4 * t + 11) (by
      rw [costedRationalRectOfFn_data]
      rw [rationalRectMatrixOfData_data (fun i j => (costedAlgebraicSymmetricEntry D t i j).value)]
      exact costedAlgebraicSymmetricEntry_bits D L t hD)
  exact Nat.add_le_add hs he

theorem costedAlgebraicSymmetricMatrix_bits {d : ℕ} (D : AlgebraicMatrixData d) (L t : ℕ)
    (hD : ∀ i j, (algebraicMatrixOfData D i j).encode.length ≤ L) (i j : Fin d) :
    rationalMagnitudeBits (rationalMatrixOfData (costedAlgebraicSymmetricMatrix D t).value i j) ≤ 14 * L + 4 * t + 11 := by
  rw [costedAlgebraicSymmetricMatrix_data, rationalMatrixOfData_data]
  rw [← costedAlgebraicSymmetricEntry_value]
  exact costedAlgebraicSymmetricEntry_bits D L t hD i j

theorem algebraicSymmetricMatrixBudget_mono {d e L M t u : ℕ} (hd : d ≤ e) (hL : L ≤ M) (ht : t ≤ u) :
    algebraicSymmetricMatrixBudget d L t ≤ algebraicSymmetricMatrixBudget e M u := by
  unfold algebraicSymmetricMatrixBudget rationalRectTraversalBudget rationalRectEncodingBudget
  gcongr
  exact algebraicPreparationBudget_mono (by omega)

theorem polyBound_algebraicSymmetricMatrixBudget {d L t : ℕ → ℕ}
    (hd : PolynomialCostBound d) (hL : PolynomialCostBound L) (ht : PolynomialCostBound t) :
    PolynomialCostBound (fun n => algebraicSymmetricMatrixBudget (d n) (L n) (t n)) := by
  have ha := polyBound_algebraicPreparationBudget.comp (hL.add ht)
  exact (polyBound_rationalRectTraversalBudget hd hd
    ((((PolynomialCostBound.const 2).mul hd).add (PolynomialCostBound.const 1)).add ha)).add
      (polyBound_rationalRectEncodingBudget hd hd
        ((((PolynomialCostBound.const 14).mul hL).add ((PolynomialCostBound.const 4).mul ht)).add
          (PolynomialCostBound.const 11)))

end GeometricGaussianLHL

end AlgebraicPreparationCost

section CanonicalFinitePreparationCost

/-!
## Complete preparation from the original finite canonical input

The execution scans the input, computes every budget and precision, prepares
the stored rational metric, and approximates the width. Uniform bounds use
only the original encoding length plus requested precision.
-/
namespace GeometricGaussianLHL

structure CanonicalPreparedData (d : ℕ) where
  metric : RationalMatrixData d
  width : ℚ
  budgets : CanonicalBudgets

def canonicalInputBudgetBound (N : ℕ) : CanonicalBudgets :=
  canonicalBudgets N N N ⟨2 * N + 1, N, N⟩

def canonicalInputPrecisionBound (N : ℕ) : AlgebraicPreparationPrecisions :=
  let H := canonicalInputBudgetBound N
  algebraicPreparationPrecisions N H.conditioning H.shaping H.metric N

def canonicalFinitePreparationBudget (N : ℕ) : ℕ :=
  let H := canonicalInputBudgetBound N
  let P := canonicalInputPrecisionBound N
  canonicalInputScanBudget N + canonicalBudgetArithmeticBudget N +
    (costedAlgebraicPreparationPrecisions N H.conditioning H.shaping H.metric N).steps +
    algebraicSymmetricMatrixBudget N N P.metric + algebraicPreparationBudget (N + P.width)

def canonicalPreparedOperandBudget (N : ℕ) : ℕ :=
  let P := canonicalInputPrecisionBound N
  N + (14 * N + 4 * P.metric + 11) + (14 * N + 4 * P.width + 11)

namespace CanonicalAlgebraicData
variable {d r m : ℕ} (I : CanonicalAlgebraicData d r m)

def preparation (t : ℕ) : Costed (CanonicalPreparedData d) :=
  (costedCanonicalInputScan I).bind fun M =>
    (costedCanonicalBudgets d r m M).bind fun H =>
      (costedAlgebraicPreparationPrecisions d H.conditioning H.shaping H.metric t).bind fun P =>
        (costedAlgebraicSymmetricMatrix I.metric P.metric).bind fun G =>
          (costedAlgebraicApprox I.width P.width).bind fun w => Costed.pure ⟨G, w, H⟩

theorem preparation_value (t : ℕ) :
    (I.preparation t).value = ⟨rationalMatrixData (I.toInput.prepareMetric t), I.toInput.prepareWidth t,
      ⟨I.toInput.conditioning, I.toInput.shapingBudget, I.toInput.metricBudget⟩⟩ := by
  simp only [preparation, Costed.bind_value, costedCanonicalInputScan_value, costedCanonicalBudgets_value,
    canonicalBudgets_input, costedAlgebraicPreparationPrecisions_value,
    costedAlgebraicSymmetricMatrix_data, costedAlgebraicApprox_value, Costed.pure]
  rfl

theorem budgets_le (N : ℕ) (hN : I.inputLength ≤ N) (hd : 0 < d) (hr : 0 < r) (hm : 0 < m) :
    I.toInput.conditioning ≤ (canonicalInputBudgetBound N).conditioning ∧
    I.toInput.shapingBudget ≤ (canonicalInputBudgetBound N).shaping ∧
    I.toInput.metricBudget ≤ (canonicalInputBudgetBound N).metric := by
  have h := canonicalBudgets_mono (I.dimension_le.trans hN)
    ((I.multiplicities_le hd hr hm).1.trans hN) ((I.multiplicities_le hd hr hm).2.trans hN)
    (I.metricSize_le.trans (show 2 * I.inputLength + 1 ≤ 2 * N + 1 by omega)) (I.coefficientBits_le.trans hN) (I.widthBits_le.trans hN)
  change (canonicalBudgets d r m (canonicalInputMeasures I)).conditioning ≤ _ ∧
    (canonicalBudgets d r m (canonicalInputMeasures I)).shaping ≤ _ ∧
    (canonicalBudgets d r m (canonicalInputMeasures I)).metric ≤ _ at h
  rw [canonicalBudgets_input] at h
  exact h

theorem precisions_le (t N : ℕ) (hN : I.inputLength ≤ N) (ht : t ≤ N)
    (hd : 0 < d) (hr : 0 < r) (hm : 0 < m) :
    let P := algebraicPreparationPrecisions d I.toInput.conditioning I.toInput.shapingBudget I.toInput.metricBudget t
    P.metric ≤ (canonicalInputPrecisionBound N).metric ∧ P.width ≤ (canonicalInputPrecisionBound N).width := by
  have h := I.budgets_le N hN hd hr hm
  exact algebraicPreparationPrecisions_mono (I.dimension_le.trans hN) h.1 h.2.1 h.2.2 ht

theorem preparation_steps_le (t N : ℕ) (hN : I.inputLength ≤ N) (ht : t ≤ N)
    (hd : 0 < d) (hr : 0 < r) (hm : 0 < m) :
    (I.preparation t).steps ≤ canonicalFinitePreparationBudget N := by
  let H := canonicalInputBudgetBound N
  let P := algebraicPreparationPrecisions d I.toInput.conditioning I.toInput.shapingBudget I.toInput.metricBudget t
  let U := canonicalInputPrecisionBound N
  have hB := I.budgets_le N hN hd hr hm
  have hP := I.precisions_le t N hN ht hd hr hm
  have hs := (costedCanonicalInputScan_steps_le I).trans (show canonicalInputScanBudget I.inputLength ≤ canonicalInputScanBudget N by
    unfold canonicalInputScanBudget natSumBudget; gcongr)
  have hb := costedCanonicalBudgets_steps_mono (I.dimension_le.trans hN)
    ((I.multiplicities_le hd hr hm).1.trans hN) ((I.multiplicities_le hd hr hm).2.trans hN)
    (I.metricSize_le.trans (show 2 * I.inputLength + 1 ≤ 2 * N + 1 by omega)) (I.coefficientBits_le.trans hN) (I.widthBits_le.trans hN)
  change (costedCanonicalBudgets d r m (canonicalInputMeasures I)).steps ≤ canonicalBudgetArithmeticBudget N at hb
  have hp := costedAlgebraicPreparationPrecisions_steps_mono (I.dimension_le.trans hN) hB.1 hB.2.1 hB.2.2 ht
  have hg := (costedAlgebraicSymmetricMatrix_steps_le I.metric N P.metric (fun i j => (I.metric_entry_length_le i j).trans hN)).trans
    (algebraicSymmetricMatrixBudget_mono (I.dimension_le.trans hN) le_rfl hP.1)
  have hw := (costedAlgebraicApprox_steps_le I.width P.width).trans
    (algebraicPreparationBudget_mono (Nat.add_le_add (I.parts_le.2.2.trans hN) hP.2))
  simp only [preparation, Costed.bind_steps, costedCanonicalInputScan_value, costedCanonicalBudgets_value,
    canonicalBudgets_input, costedAlgebraicPreparationPrecisions_value, Costed.pure]
  change _ ≤ canonicalInputScanBudget N + canonicalBudgetArithmeticBudget N +
    (costedAlgebraicPreparationPrecisions N H.conditioning H.shaping H.metric N).steps +
    algebraicSymmetricMatrixBudget N N U.metric + algebraicPreparationBudget (N + U.width)
  change (costedAlgebraicSymmetricMatrix I.metric P.metric).steps ≤ _ at hg
  dsimp only [P, H, U] at *
  omega

theorem prepared_operand_bits (t N : ℕ) (hN : I.inputLength ≤ N) (ht : t ≤ N)
    (hd : 0 < d) (hr : 0 < r) (hm : 0 < m) :
    (∀ i j, rationalMagnitudeBits (I.toInput.prepareMetric t i j) ≤ canonicalPreparedOperandBudget N) ∧
    (∀ i j, (I.toInput.coefficients i j).natAbs.size ≤ canonicalPreparedOperandBudget N) ∧
    rationalMagnitudeBits (I.toInput.prepareWidth t) ≤ canonicalPreparedOperandBudget N := by
  let P := algebraicPreparationPrecisions d I.toInput.conditioning I.toInput.shapingBudget I.toInput.metricBudget t
  have hP := I.precisions_le t N hN ht hd hr hm
  have hG (i j) := costedAlgebraicSymmetricMatrix_bits I.metric N P.metric
    (fun i j => (I.metric_entry_length_le i j).trans hN) i j
  simp only [costedAlgebraicSymmetricMatrix_data, rationalMatrixOfData_data] at hG
  have hw := costedAlgebraicApprox_output_length I.width P.width
  simp only [encodeRatBits_length, costedAlgebraicApprox_value] at hw
  have hW := I.parts_le.2.2.trans hN
  refine ⟨fun i j => ?_, fun i j => ?_, ?_⟩
  · have h := hG i j
    change rationalMagnitudeBits (I.toInput.prepareMetric t i j) ≤ 14 * N + 4 * P.metric + 11 at h
    unfold canonicalPreparedOperandBudget
    dsimp only [P] at *
    omega
  · have h := (integerRect_entry_bits_le_encoded I.coefficients i j).trans (I.parts_le.2.1.trans hN)
    change (integerRectMatrixOfData I.coefficients i j).natAbs.size ≤ _
    unfold canonicalPreparedOperandBudget
    dsimp only
    omega
  · change 2 * rationalMagnitudeBits (I.toInput.prepareWidth t) + 1 ≤ 14 * I.width.encode.length + 4 * P.width + 11 at hw
    unfold canonicalPreparedOperandBudget
    dsimp only [P] at *
    omega

end CanonicalAlgebraicData

theorem polyBound_canonicalInputBudgetBound :
    PolynomialCostBound (fun N => (canonicalInputBudgetBound N).conditioning) ∧
    PolynomialCostBound (fun N => (canonicalInputBudgetBound N).shaping) ∧
    PolynomialCostBound (fun N => (canonicalInputBudgetBound N).metric) :=
  polyBound_canonicalBudgets PolynomialCostBound.id PolynomialCostBound.id PolynomialCostBound.id
    (((PolynomialCostBound.const 2).mul PolynomialCostBound.id).add (PolynomialCostBound.const 1))
    PolynomialCostBound.id PolynomialCostBound.id

theorem polyBound_canonicalInputPrecisionBound :
    PolynomialCostBound (fun N => (canonicalInputPrecisionBound N).metric) ∧
    PolynomialCostBound (fun N => (canonicalInputPrecisionBound N).width) :=
  polyBound_algebraicPreparationPrecisions PolynomialCostBound.id polyBound_canonicalInputBudgetBound.1
    polyBound_canonicalInputBudgetBound.2.1 polyBound_canonicalInputBudgetBound.2.2 PolynomialCostBound.id

theorem polyBound_canonicalFinitePreparationBudget : PolynomialCostBound canonicalFinitePreparationBudget := by
  have hP := polyBound_costedAlgebraicPreparationPrecisions PolynomialCostBound.id polyBound_canonicalInputBudgetBound.1
    polyBound_canonicalInputBudgetBound.2.1 polyBound_canonicalInputBudgetBound.2.2 PolynomialCostBound.id
  exact (((polyBound_canonicalInputScanBudget.add polyBound_canonicalBudgetArithmeticBudget).add hP).add
    (polyBound_algebraicSymmetricMatrixBudget PolynomialCostBound.id PolynomialCostBound.id polyBound_canonicalInputPrecisionBound.1)).add
      (polyBound_algebraicPreparationBudget.comp (PolynomialCostBound.id.add polyBound_canonicalInputPrecisionBound.2))

theorem polyBound_canonicalPreparedOperandBudget : PolynomialCostBound canonicalPreparedOperandBudget := by
  have hm := polyBound_canonicalInputPrecisionBound.1
  have hw := polyBound_canonicalInputPrecisionBound.2
  exact (PolynomialCostBound.id.add
    (((((PolynomialCostBound.const 14).mul PolynomialCostBound.id).add ((PolynomialCostBound.const 4).mul hm))).add
      (PolynomialCostBound.const 11))).add
        (((((PolynomialCostBound.const 14).mul PolynomialCostBound.id).add ((PolynomialCostBound.const 4).mul hw))).add
          (PolynomialCostBound.const 11))

end GeometricGaussianLHL

end CanonicalFinitePreparationCost

section CanonicalFiniteCost

/-!
## Canonical shaping cost from the original finite algebraic input

A single execution includes input scanning, budget and precision arithmetic,
algebraic preparation, metric normalization and the complete rational shaping
algorithm. Its cost and serialized output length are polynomial in the actual
input encoding length plus precision. Positivity and canonical operator error
are proved for this same output.
-/
open Module NumberField
open scoped MatrixOrder Matrix.Norms.L2Operator
namespace GeometricGaussianLHL

def canonicalFiniteShapingBudget (N : ℕ) : ℕ :=
  let H := canonicalInputBudgetBound N
  canonicalFinitePreparationBudget N +
    preparedShapingBudget N N N (canonicalPreparedOperandBudget N) N H.shaping H.metric

theorem polyBound_canonicalFiniteShapingBudget : PolynomialCostBound canonicalFiniteShapingBudget :=
  polyBound_canonicalFinitePreparationBudget.add
    (polyBound_preparedShapingBudget PolynomialCostBound.id PolynomialCostBound.id PolynomialCostBound.id
      polyBound_canonicalPreparedOperandBudget PolynomialCostBound.id
      polyBound_canonicalInputBudgetBound.2.1 polyBound_canonicalInputBudgetBound.2.2)

namespace CanonicalAlgebraicData
variable {d r m : ℕ} (I : CanonicalAlgebraicData d r m)

def execution (t : ℕ) : Costed (RationalMatrixData (m * d)) :=
  (I.preparation t).bind fun J =>
    costedPreparedShaping t J.budgets.shaping J.budgets.metric J.metric I.coefficients J.width

theorem execution_data (t : ℕ) :
    (I.execution t).value = rationalMatrixData (I.toInput.output t) := by
  rw [execution, Costed.bind_value, I.preparation_value, costedPreparedShaping_data, rationalMatrixOfData_data]
  rfl

theorem execution_length_le_steps (t : ℕ) :
    (encodeRationalMatrixData (I.execution t).value).length ≤ (I.execution t).steps := by
  let J := (I.preparation t).value
  have h := costedPreparedShaping_length_le_steps t J.budgets.shaping J.budgets.metric J.metric I.coefficients J.width
  rw [execution, Costed.bind_value, Costed.bind_steps]
  exact h.trans (Nat.le_add_left _ _)

variable {K : Type*} [Field K] [NumberField K] {b : Basis (Fin d) ℤ (𝓞 K)}
  {A : Matrix (Fin r) (Fin m) (𝓞 K)} {w : ℝ}

theorem execution_steps_le (hI : I.toInput.ValidFor K b A w) (hrm : r ≤ m)
    (hA : Function.Surjective A.mulVec) (hr : 0 < r) (hw : 0 < w) (t : ℕ) :
    (I.execution t).steps ≤ canonicalFiniteShapingBudget (I.inputLength + t) := by
  let N := I.inputLength + t
  let L := canonicalPreparedOperandBudget N
  have hd := integralBasis_dimension_pos K b
  have hm : 0 < m := hr.trans_le hrm
  have hN : I.inputLength ≤ N := Nat.le_add_right _ _
  have ht : t ≤ N := Nat.le_add_left _ _
  have hB := I.budgets_le N hN hd hr hm
  have hO := I.prepared_operand_bits t N hN ht hd hr hm
  have hG := (hI.metric_bounds t).1
  have hQ := (hI.toPrepared hrm hA hw t).normalized_gram_isUnit hA hr hw
  have hrun := costedPreparedShaping_steps_le t I.toInput.shapingBudget I.toInput.metricBudget
    (rationalMatrixData (I.toInput.prepareMetric t)) I.coefficients (I.toInput.prepareWidth t) L
    (by rw [rationalMatrixOfData_data]; exact hG)
    (by rw [rationalMatrixOfData_data]; exact hO.1)
    hO.2.1 hO.2.2 (Nat.mul_pos hr hd) (hI.width_valid.approx_pos hw _).ne'
    (by rw [rationalMatrixOfData_data]; exact hQ)
  have hupper := hrun.trans (preparedShapingBudget_mono (I.dimension_le.trans hN)
    ((I.multiplicities_le hd hr hm).1.trans hN) ((I.multiplicities_le hd hr hm).2.trans hN)
    le_rfl ht hB.2.1 hB.2.2)
  have hp := I.preparation_steps_le t N hN ht hd hr hm
  rw [execution, Costed.bind_steps, I.preparation_value]
  exact Nat.add_le_add hp hupper

theorem execution_accuracy (hI : I.toInput.ValidFor K b A w) (hrm : r ≤ m)
    (hA : Function.Surjective A.mulVec) (hr : 0 < r) (hw : 0 < w) (t : ℕ) :
    ((rationalMatrixOfData (I.execution t).value).map (Rat.castHom ℝ)).PosDef ∧
      ‖isometricTransportMap (canonicalGramEuclideanIsometry K b m) (canonicalGramEuclideanIsometry K b m)
        (Matrix.toEuclideanLin ((rationalMatrixOfData (I.execution t).value).map (Rat.castHom ℝ))).toContinuousLinearMap -
          (canonicalGramShapingShape K b A hA hr w hw).toContinuousLinearMap‖ ≤ 1 / (2 : ℝ) ^ t := by
  rw [I.execution_data, rationalMatrixOfData_data]
  exact hI.output_certificate hrm hA hr hw t

end CanonicalAlgebraicData

/-- Uniform constants cover every represented number field, basis, coefficient
matrix and positive width. Input validity contains only semantic identification
of the finite data, with no approximation or runtime promise. -/
theorem canonicalFinite_computational_certificate :
    ∃ C e : ℕ, ∀ (K : Type*) [Field K] [NumberField K] (d r m : ℕ)
      (b : Basis (Fin d) ℤ (𝓞 K)) (A : Matrix (Fin r) (Fin m) (𝓞 K))
      (I : CanonicalAlgebraicData d r m) (w : ℝ),
      I.toInput.ValidFor K b A w → ∀ (_hrm : r ≤ m) (hA : Function.Surjective A.mulVec) (hr : 0 < r) (hw : 0 < w) (t : ℕ),
      let run := I.execution t
      run.steps ≤ C * (I.inputLength + t + 1) ^ e ∧
      (encodeRationalMatrixData run.value).length ≤ C * (I.inputLength + t + 1) ^ e ∧
      rationalMatrixOfData run.value = I.toInput.output t ∧
      ((rationalMatrixOfData run.value).map (Rat.castHom ℝ)).PosDef ∧
      ‖isometricTransportMap (canonicalGramEuclideanIsometry K b m) (canonicalGramEuclideanIsometry K b m)
        (Matrix.toEuclideanLin ((rationalMatrixOfData run.value).map (Rat.castHom ℝ))).toContinuousLinearMap -
          (canonicalGramShapingShape K b A hA hr w hw).toContinuousLinearMap‖ ≤ 1 / (2 : ℝ) ^ t := by
  obtain ⟨C, e, h⟩ := polyBound_canonicalFiniteShapingBudget.exists_mul_pow_bound
  refine ⟨C, e, fun K _ _ d r m b A I w hI hrm hA hr hw t => ?_⟩
  have hs := (I.execution_steps_le hI hrm hA hr hw t).trans (h (I.inputLength + t))
  refine ⟨hs, (I.execution_length_le_steps t).trans hs, ?_, I.execution_accuracy hI hrm hA hr hw t⟩
  rw [I.execution_data, rationalMatrixOfData_data]

end GeometricGaussianLHL

end CanonicalFiniteCost

section CanonicalEncodingExistence

/-!
## Availability of the finite inputs used by canonical shaping

Every number field and integral basis admit the stored algebraic metric data.
Every algebraic real width admits the required width encoding. These are
representation-existence theorems; the algorithm starts from the supplied
finite data and charges their full preparation cost.
-/
set_option backward.isDefEq.respectTransparency false
open Module NumberField
open scoped MatrixOrder Matrix.Norms.L2Operator
namespace GeometricGaussianLHL

theorem canonicalAlgebraicData_exists (K : Type*) [Field K] [NumberField K]
    {d r m : ℕ} (b : Basis (Fin d) ℤ (𝓞 K)) (A : Matrix (Fin r) (Fin m) (𝓞 K))
    {w : ℝ} (hw : IsAlgebraic ℚ w) :
    ∃ I : CanonicalAlgebraicData d r m, I.toInput.ValidFor K b A w := by
  have hg (i j : Fin d) : IsAlgebraic ℚ (canonicalGram K b i j) :=
    (show IsIntegral ℚ (canonicalGram K b i j) from (canonicalGram_isIntegral K b i j).tower_top).isAlgebraic
  choose M hM using fun i j => AlgebraicRealInput.exists_valid (hg i j)
  obtain ⟨W, hW⟩ := AlgebraicRealInput.exists_valid hw
  let I : CanonicalAlgebraicData d r m :=
    ⟨algebraicMatrixData M, integerRectMatrixData (ringCoefficientMatrix b A), W⟩
  refine ⟨I, ⟨?_, ?_, hW⟩⟩
  · change ∀ i j, (algebraicMatrixOfData (algebraicMatrixData M) i j).ValidFor (canonicalGram K b i j)
    rw [algebraicMatrixOfData_data]
    exact hM
  · exact integerRectMatrixOfData_data _

theorem canonicalAlgebraicFamily_exists (K : Type*) [Field K] [NumberField K]
    {d r m : ℕ} (b : Basis (Fin d) ℤ (𝓞 K)) {w : ℝ} (hw : IsAlgebraic ℚ w) :
    ∃ I : Matrix (Fin r) (Fin m) (𝓞 K) → CanonicalAlgebraicData d r m,
      ∀ A, (I A).toInput.ValidFor K b A w := by
  choose I hI using fun A : Matrix (Fin r) (Fin m) (𝓞 K) => canonicalAlgebraicData_exists K b A hw
  exact ⟨I, hI⟩

theorem rationalWidth_isAlgebraic (w : ℚ) : IsAlgebraic ℚ (w : ℝ) :=
  (isIntegral_algebraMap : IsIntegral ℚ (algebraMap ℚ ℝ w)).isAlgebraic

/-- A finite width can be chosen above any positive analytic lower bound
without increasing it by more than a factor of two. -/
theorem exists_rational_width_between {B : ℝ} (hB : 0 < B) :
    ∃ w : ℚ, 0 < w ∧ B ≤ (w : ℝ) ∧ (w : ℝ) ≤ 2 * B := by
  obtain ⟨w, hBw, hwB⟩ := exists_rat_btwn (show B < 2 * B by linarith)
  exact ⟨w, Rat.cast_pos.mp (hB.trans hBw), hBw.le, hwB.le⟩

/-- Available representations and the complete execution-cost theorem are
joined here, uniformly across number fields and integral bases. -/
theorem canonicalFinite_endToEnd_certificate :
    ∃ C e : ℕ, ∀ (K : Type*) [Field K] [NumberField K] (d r m : ℕ)
      (b : Basis (Fin d) ℤ (𝓞 K)) (A : Matrix (Fin r) (Fin m) (𝓞 K)) (w : ℝ),
      IsAlgebraic ℚ w → ∀ (_hrm : r ≤ m) (hA : Function.Surjective A.mulVec) (hr : 0 < r) (hw : 0 < w),
      ∃ I : CanonicalAlgebraicData d r m, I.toInput.ValidFor K b A w ∧ ∀ t : ℕ,
      let run := I.execution t
      run.steps ≤ C * (I.inputLength + t + 1) ^ e ∧
      (encodeRationalMatrixData run.value).length ≤ C * (I.inputLength + t + 1) ^ e ∧
      rationalMatrixOfData run.value = I.toInput.output t ∧
      ((rationalMatrixOfData run.value).map (Rat.castHom ℝ)).PosDef ∧
      ‖isometricTransportMap (canonicalGramEuclideanIsometry K b m) (canonicalGramEuclideanIsometry K b m)
        (Matrix.toEuclideanLin ((rationalMatrixOfData run.value).map (Rat.castHom ℝ))).toContinuousLinearMap -
          (canonicalGramShapingShape K b A hA hr w hw).toContinuousLinearMap‖ ≤ 1 / (2 : ℝ) ^ t := by
  obtain ⟨C, e, hcost⟩ := canonicalFinite_computational_certificate
  refine ⟨C, e, fun K _ _ d r m b A w hwalg hrm hA hr hw => ?_⟩
  obtain ⟨I, hI⟩ := canonicalAlgebraicData_exists K b A hwalg
  exact ⟨I, hI, fun t => hcost K d r m b A I w hI hrm hA hr hw t⟩

end GeometricGaussianLHL

end CanonicalEncodingExistence
