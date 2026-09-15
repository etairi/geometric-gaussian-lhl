import GeometricGaussianLHL.ConstantWidth
import GeometricGaussianLHL.ShapingGeometry
import GeometricGaussianLHL.SpectralBounds

/-!
# Spherical leftover-hash theorems and simultaneous hints

This module collects the following proof sections, in dependency order.
- The polynomial geometric event with its spherical output width (`PolynomialSphericalEvent`).
- The constant-width geometric event with its spherical output width (`ConstantSphericalEvent`).
- Spherical joint laws on a certified matrix event (`NumberFieldSphericalJoint`).
- Constant-width spherical Gaussian consequences (`NumberFieldConstantSphericalLHL`).
- Polynomial-width spherical Gaussian leftover hashing (`NumberFieldSphericalLHL`).
- Simultaneous spherical hints over a number field (`NumberFieldSphericalHints`).
- Constant-width spherical Gaussian consequences (`NumberFieldConstantSphericalHints`).
- Simultaneous hints with a separate spectral event (`SphericalHintEvents`).
- A joint certificate for spherical output and simultaneous hints (`SphericalOutputCertificate`).
- Spectral spherical output and hints at constant coefficient width (`ConstantSpectralSpherical`).
- Spectral spherical output and hints at polynomial coefficient width (`PolynomialSpectralSpherical`).
-/

section PolynomialSphericalEvent

/-!
## The polynomial geometric event with its spherical output width

The width is exactly `B V₀` from Corollary 5.2, where `V₀ = κ μ U √M`.
Both the smoothing and operator-norm bounds hold on the same event of
the proved finite number-field Gaussian matrix theorem.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Module NumberField

namespace GeometricGaussianLHL

variable (K : Type*) [Field K] [NumberField K] {d r m : ℕ}

def numberFieldPolynomialSmoothingBound (b : Basis (Fin d) ℤ (𝓞 K)) (r m : ℕ) (ell : ℝ) : ℝ :=
  basisAlpha K b * polynomialThetaWidth (basisKappa K b) (basisMu K b)
    (polynomialColumnHeight (r * d) m ell)

def numberFieldPolynomialOperatorBound (b : Basis (Fin d) ℤ (𝓞 K)) (r m : ℕ) (s ell : ℝ) : ℝ :=
  basisKappa K b * (basisMu K b * (s * basisBeta K b * Real.sqrt (polynomialColumnHeight (r * d) m ell))) *
    Real.sqrt ((m * d : ℕ) : ℝ)

def numberFieldPolynomialSphericalWidth (b : Basis (Fin d) ℤ (𝓞 K)) (r m : ℕ) (s ell : ℝ) : ℝ :=
  numberFieldPolynomialSmoothingBound K b r m ell * numberFieldPolynomialOperatorBound K b r m s ell

theorem numberFieldPolynomialSpherical_parameters_pos (b : Basis (Fin d) ℤ (𝓞 K))
    (i : Fin d) (hidentity : b i = 1) (hr : 1 ≤ r) (hm : 1 ≤ m)
    {ell s : ℝ} (hell : 1 ≤ ell) (hs : 0 < s) :
    0 < numberFieldPolynomialSmoothingBound K b r m ell ∧
    0 < numberFieldPolynomialOperatorBound K b r m s ell ∧
    0 < numberFieldPolynomialSphericalWidth K b r m s ell := by
  have hd := integralBasis_dimension_pos K b
  have hR : (0 : ℝ) < (r * d : ℕ) := by exact_mod_cast Nat.mul_pos (by omega : 0 < r) hd
  have hM : (0 : ℝ) < (m * d : ℕ) := by exact_mod_cast Nat.mul_pos (by omega : 0 < m) hd
  have hH : 0 < polynomialColumnHeight (r * d) m ell := hR.trans_le (polynomialColumnHeight_ge_rank hm hell)
  have hα := basisAlpha_pos K b
  have hβ := basisBeta_pos K b
  have hκ : 0 < basisKappa K b := lt_of_lt_of_le zero_lt_one (basisKappa_ge_one K b)
  have hμ : 0 < basisMu K b := lt_of_lt_of_le zero_lt_one (basisMu_ge_one K b i hidentity)
  have hB : 0 < numberFieldPolynomialSmoothingBound K b r m ell := by
    unfold numberFieldPolynomialSmoothingBound polynomialThetaWidth
    positivity
  have hV : 0 < numberFieldPolynomialOperatorBound K b r m s ell := by
    unfold numberFieldPolynomialOperatorBound
    positivity
  exact ⟨hB, hV, mul_pos hB hV⟩

theorem numberField_polynomial_spherical_event (b : Basis (Fin d) ℤ (𝓞 K))
    (i : Fin d) (hidentity : b i = 1) (hr : 1 ≤ r) (hmr : r < m)
    {ell s : ℝ} (hell : 1 ≤ ell) (hs : 0 < s)
    (hwidth : 8 * Real.sqrt (r * d) ≤ s / basisAlpha K b)
    (hbudget : ((r * d : ℕ) : ℝ) * Real.log (numberFieldPolynomialScale K b r m s ell) +
      2 * Real.log (1 / realSecurityError (ell + 4)) ≤ (m : ℝ) * Real.log (8 / 7)) :
    ∃ G : Set (Matrix (Fin r) (Fin m) (𝓞 K)),
      ENNReal.ofReal (1 - 3 * realSecurityError (ell + 4)) ≤
        (numberFieldMatrixLaw K b r m s hs.ne').toOuterMeasure G ∧
      ∀ X ∈ G, Function.Surjective X.mulVec ∧
        smoothingParameter (canonicalKernel K X) (2 * realSecurityError (ell + 4)) ≤
          numberFieldPolynomialSmoothingBound K b r m ell ∧
        ‖(canonicalEuclideanMatrix K b X).toContinuousLinearMap‖ ≤
          numberFieldPolynomialOperatorBound K b r m s ell := by
  obtain ⟨G, hprob, hgood⟩ := numberField_polynomial_certificate K b i hidentity hr hmr hell hs hwidth hbudget
  refine ⟨G, hprob, ?_⟩
  intro X hX
  refine ⟨(hgood X hX).1, (hgood X hX).2.2.1, ?_⟩
  have hβ := basisBeta_pos K b
  have hn := canonicalEuclideanMatrix_norm_le_columns K b X
    (show 0 ≤ s * basisBeta K b * Real.sqrt (polynomialColumnHeight (r * d) m ell) by positivity)
    (hgood X hX).2.2.2.1
  simpa only [numberFieldPolynomialOperatorBound, Nat.cast_mul] using hn

end GeometricGaussianLHL
end

end PolynomialSphericalEvent

section ConstantSphericalEvent

/-!
## The constant-width geometric event with its spherical output width

The literal width in Corollary 5.2 is `B V₀`, where `B = 640 √(d H)`
and `V₀ = (s/√d) √H √M`. The smoothing and operator estimates hold on
the same event under the actual power-of-two ring-Gaussian matrix law.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Module NumberField

namespace GeometricGaussianLHL

def powerTwoConstantSmoothingBound (d r m : ℕ) (ell : ℝ) : ℝ :=
  640 * Real.sqrt (d * constantColumnHeight (r * d) m (realSecurityError (ell + 6)))

def powerTwoConstantOperatorBound (d r m : ℕ) (s ell : ℝ) : ℝ :=
  constantColumnThreshold (s / Real.sqrt d) (constantColumnHeight (r * d) m (realSecurityError (ell + 6))) *
    Real.sqrt ((m * d : ℕ) : ℝ)

def powerTwoConstantSphericalWidth (d r m : ℕ) (s ell : ℝ) : ℝ :=
  powerTwoConstantSmoothingBound d r m ell * powerTwoConstantOperatorBound d r m s ell

theorem powerTwoConstantSpherical_parameters_pos {d r m : ℕ} (hd : 0 < d)
    (hr : 1 ≤ r) (hm : 1 ≤ m) {ell s : ℝ} (hell : 1 ≤ ell) (hs : 0 < s) :
    0 < powerTwoConstantSmoothingBound d r m ell ∧
    0 < powerTwoConstantOperatorBound d r m s ell ∧
    0 < powerTwoConstantSphericalWidth d r m s ell := by
  have hdreal : (0 : ℝ) < d := by exact_mod_cast hd
  have hR : (0 : ℝ) < (r * d : ℕ) := by exact_mod_cast Nat.mul_pos (by omega : 0 < r) hd
  have hM : (0 : ℝ) < (m * d : ℕ) := by exact_mod_cast Nat.mul_pos (by omega : 0 < m) hd
  have hH : 0 < constantColumnHeight (r * d) m (realSecurityError (ell + 6)) :=
    hR.trans_le (constantColumnHeight_ge_rank hm (realSecurityError_pos _)
      (by have h := real_constant_failureBudget_le hell; linarith))
  have hB : 0 < powerTwoConstantSmoothingBound d r m ell := by
    unfold powerTwoConstantSmoothingBound
    positivity
  have hV : 0 < powerTwoConstantOperatorBound d r m s ell := by
    unfold powerTwoConstantOperatorBound constantColumnThreshold
    positivity
  exact ⟨hB, hV, mul_pos hB hV⟩

variable (K : Type*) [Field K] [NumberField K] {k r m : ℕ}
  [IsCyclotomicExtension {2 ^ (k + 1)} ℚ K] {ζ : K}

theorem numberField_constantWidth_spherical_event (hζ : IsPrimitiveRoot ζ (2 ^ (k + 1)))
    (hr : 1 ≤ r) (hmr : r < m) {ell s : ℝ} (hell : 1 ≤ ell) (hs : 0 < s)
    (hwidth : Real.sqrt (2 ^ (k + 1)).totient ≤ s)
    (hbudget : ((r * (2 ^ (k + 1)).totient : ℕ) : ℝ) *
      Real.log (powerTwoConstantScale (2 ^ (k + 1)).totient r m s ell) +
      2 * Real.log (1 / realSecurityError (ell + 6)) ≤ (m : ℝ) * Real.log (50 / 49)) :
    let d := (2 ^ (k + 1)).totient
    let b := cyclotomicIntegralBasis K hζ
    ∃ G : Set (Matrix (Fin r) (Fin m) (𝓞 K)),
      ENNReal.ofReal (1 - 3 * realSecurityError (ell + 6)) ≤
        (numberFieldMatrixLaw K b r m s hs.ne').toOuterMeasure G ∧
      ∀ X ∈ G, Function.Surjective X.mulVec ∧
        smoothingParameter (canonicalKernel K X) (2 * realSecurityError (ell + 6)) ≤
          powerTwoConstantSmoothingBound d r m ell ∧
        ‖(canonicalEuclideanMatrix K b X).toContinuousLinearMap‖ ≤
          powerTwoConstantOperatorBound d r m s ell := by
  dsimp only
  obtain ⟨G, hprob, hgood⟩ := numberField_constantWidth_certificate K hζ hr hmr hell hs hwidth hbudget
  refine ⟨G, hprob, ?_⟩
  intro X hX
  refine ⟨(hgood X hX).1, (hgood X hX).2.2.1, ?_⟩
  have hU : 0 ≤ constantColumnThreshold (s / Real.sqrt (2 ^ (k + 1)).totient)
      (constantColumnHeight (r * (2 ^ (k + 1)).totient) m (realSecurityError (ell + 6))) := by
    unfold constantColumnThreshold
    positivity
  have hn := canonicalEuclideanMatrix_norm_le_columns K (cyclotomicIntegralBasis K hζ) X hU
    (hgood X hX).2.2.2.1
  obtain ⟨_, _, hκ, hμ⟩ := powerTwoBasis_constants K hζ
  simpa only [hκ, hμ, one_mul, powerTwoConstantOperatorBound, Nat.cast_mul] using hn

end GeometricGaussianLHL
end

end ConstantSphericalEvent

section NumberFieldSphericalJoint

/-!
## Spherical joint laws on a certified matrix event

The input is explicitly shaped on the good event and has identity shape
off that event. The output is compared with the actual centered spherical
ring Gaussian. A second event carries its own failure budget.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Module NumberField

namespace GeometricGaussianLHL

variable (K : Type*) [Field K] [NumberField K] {d r m : ℕ}
  [Nontrivial (Euclidean (r * d))]

def numberFieldSphericalEventShape (b : Basis (Fin d) ℤ (𝓞 K))
    (G : Set (Matrix (Fin r) (Fin m) (𝓞 K)))
    (hsurj : ∀ X ∈ G, Function.Surjective X.mulVec) {w : ℝ} (hw : 0 < w)
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) : Euclidean (m * d) ≃L[ℝ] Euclidean (m * d) := by
  classical
  exact if hX : X ∈ G then numberFieldSphericalInputShape K b X (hsurj X hX) hw
    else ContinuousLinearEquiv.refl ℝ (Euclidean (m * d))

theorem numberFieldSphericalEventShape_of_mem (b : Basis (Fin d) ℤ (𝓞 K))
    (G : Set (Matrix (Fin r) (Fin m) (𝓞 K)))
    (hsurj : ∀ X ∈ G, Function.Surjective X.mulVec) {w : ℝ} (hw : 0 < w)
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) (hX : X ∈ G) :
    numberFieldSphericalEventShape K b G hsurj hw X = numberFieldSphericalInputShape K b X (hsurj X hX) hw := by
  simp only [numberFieldSphericalEventShape, dite_eq_left hX]

theorem numberFieldSphericalEventShape_of_not_mem (b : Basis (Fin d) ℤ (𝓞 K))
    (G : Set (Matrix (Fin r) (Fin m) (𝓞 K)))
    (hsurj : ∀ X ∈ G, Function.Surjective X.mulVec) {w : ℝ} (hw : 0 < w)
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) (hX : X ∉ G) :
    numberFieldSphericalEventShape K b G hsurj hw X = ContinuousLinearEquiv.refl ℝ (Euclidean (m * d)) := by
  simp only [numberFieldSphericalEventShape, dite_eq_right hX]

theorem numberFieldSphericalEventShape_positive (b : Basis (Fin d) ℤ (𝓞 K))
    (G : Set (Matrix (Fin r) (Fin m) (𝓞 K)))
    (hsurj : ∀ X ∈ G, Function.Surjective X.mulVec) {w : ℝ} (hw : 0 < w)
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) :
    (numberFieldSphericalEventShape K b G hsurj hw X).toLinearMap.IsPositive := by
  classical
  by_cases hX : X ∈ G
  · rw [numberFieldSphericalEventShape_of_mem K b G hsurj hw X hX]
    exact sphericalShapingShape_positive _ _ _
  · rw [numberFieldSphericalEventShape_of_not_mem K b G hsurj hw X hX]
    exact LinearMap.isPositive_id

theorem numberField_spherical_joint_good_event (b : Basis (Fin d) ℤ (𝓞 K))
    (p : PMF (Matrix (Fin r) (Fin m) (𝓞 K)))
    (G : Set (Matrix (Fin r) (Fin m) (𝓞 K)))
    (hsurj : ∀ X ∈ G, Function.Surjective X.mulVec) {δ ε w : ℝ} (hw : 0 < w)
    (hprob : ENNReal.ofReal (1 - δ) ≤ p.toOuterMeasure G) (hε : 0 < ε) (hε1 : ε < 1)
    (hwidth : ∀ X ∈ G, smoothingParameter (canonicalKernel K X) ε *
      ‖(canonicalEuclideanMatrix K b X).toContinuousLinearMap‖ ≤ w)
    (c : Matrix (Fin r) (Fin m) (𝓞 K) → Fin m → 𝓞 K) :
    discreteTotalVariation
      (jointPMF p (fun X => (numberFieldEllipsoidalGaussian K b m
        (numberFieldSphericalEventShape K b G hsurj hw X) (c X)).map X.mulVec))
      (jointPMF p (fun X => (numberFieldGaussian K b r w hw.ne').map (Equiv.addRight (X.mulVec (c X))))) ≤
      δ + ε / (1 - ε) := by
  apply discreteTotalVariation_joint_le_of_event_mass p _ _ G hprob
    (div_nonneg hε.le (sub_pos.mpr hε1).le)
  intro X hX
  rw [numberFieldSphericalEventShape_of_mem K b G hsurj hw X hX]
  exact numberField_gaussian_spherical_pushforward K b X (hsurj X hX) hw hε hε1 (hwidth X hX) (c X)

/-- The separate spectral-event version explicitly adds its exceptional
probability. No independence of the two events is required. -/
theorem numberField_spherical_joint_two_events (b : Basis (Fin d) ℤ (𝓞 K))
    (p : PMF (Matrix (Fin r) (Fin m) (𝓞 K)))
    (G H : Set (Matrix (Fin r) (Fin m) (𝓞 K)))
    (hsurj : ∀ X ∈ G, Function.Surjective X.mulVec) {δG δH ε B V w : ℝ} (hw : 0 < w)
    (hG : ENNReal.ofReal (1 - δG) ≤ p.toOuterMeasure G)
    (hH : ENNReal.ofReal (1 - δH) ≤ p.toOuterMeasure H) (hε : 0 < ε) (hε1 : ε < 1)
    (hB : 0 ≤ B) (hBV : B * V ≤ w)
    (hsmooth : ∀ X ∈ G, smoothingParameter (canonicalKernel K X) ε ≤ B)
    (hnorm : ∀ X ∈ H, ‖(canonicalEuclideanMatrix K b X).toContinuousLinearMap‖ ≤ V)
    (c : Matrix (Fin r) (Fin m) (𝓞 K) → Fin m → 𝓞 K) :
    discreteTotalVariation
      (jointPMF p (fun X => (numberFieldEllipsoidalGaussian K b m
        (numberFieldSphericalEventShape K b (G ∩ H) (fun X hX => hsurj X hX.1) hw X) (c X)).map X.mulVec))
      (jointPMF p (fun X => (numberFieldGaussian K b r w hw.ne').map (Equiv.addRight (X.mulVec (c X))))) ≤
      δG + δH + ε / (1 - ε) := by
  apply numberField_spherical_joint_good_event K b p (G ∩ H) (fun X hX => hsurj X hX.1) hw
    (pmf_intersection_event_mass p G H hG hH) hε hε1
  intro X hX
  exact (mul_le_mul_of_nonneg_right (hsmooth X hX.1) (norm_nonneg _)).trans
    ((mul_le_mul_of_nonneg_left (hnorm X hX.2) hB).trans hBV)

end GeometricGaussianLHL
end

end NumberFieldSphericalJoint

section NumberFieldConstantSphericalLHL

/-!
## Constant-width spherical Gaussian consequences

The actual positive square root is used on the proved constant-width
geometric event, with identity shape outside. The spherical width is
exactly `B V₀`, and the joint error is strictly below `2^(-ell)`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Module NumberField
open scoped MatrixOrder

namespace GeometricGaussianLHL

variable (K : Type*) [Field K] [NumberField K] {k r m : ℕ}
  [IsCyclotomicExtension {2 ^ (k + 1)} ℚ K] {ζ : K}

theorem numberField_constantWidth_spherical_certificate (hζ : IsPrimitiveRoot ζ (2 ^ (k + 1))) (hr : 1 ≤ r) (hmr : r < m)
    {ell s : ℝ} (hell : 1 ≤ ell) (hs : 0 < s)
    (hwidth : Real.sqrt (2 ^ (k + 1)).totient ≤ s)
    (hbudget : ((r * (2 ^ (k + 1)).totient : ℕ) : ℝ) * Real.log (powerTwoConstantScale (2 ^ (k + 1)).totient r m s ell) +
      2 * Real.log (1 / realSecurityError (ell + 6)) ≤ (m : ℝ) * Real.log (50 / 49)) :
    let w := powerTwoConstantSphericalWidth (2 ^ (k + 1)).totient r m s ell
    ∃ hw : 0 < w, ∃ G : Set (Matrix (Fin r) (Fin m) (𝓞 K)),
      ∃ S : Matrix (Fin r) (Fin m) (𝓞 K) → Euclidean (m * (2 ^ (k + 1)).totient) ≃L[ℝ] Euclidean (m * (2 ^ (k + 1)).totient),
        ENNReal.ofReal (1 - 3 * realSecurityError (ell + 6)) ≤
          (numberFieldMatrixLaw K (cyclotomicIntegralBasis K hζ) r m s hs.ne').toOuterMeasure G ∧
        (∀ X, (S X).toLinearMap.IsPositive) ∧
        (∀ X ∉ G, S X = ContinuousLinearEquiv.refl ℝ (Euclidean (m * (2 ^ (k + 1)).totient))) ∧
        ∀ X ∈ G, ∃ hX : Function.Surjective X.mulVec,
          Matrix.toEuclideanLin.symm (S X).toLinearMap = CFC.sqrt
            (sphericalShapingMatrix (canonicalEuclideanMatrix K (cyclotomicIntegralBasis K hζ) X).toContinuousLinearMap
              (canonicalEuclideanMatrix_surjective K (cyclotomicIntegralBasis K hζ) X hX) w) ∧
          powerTwoConstantSmoothingBound (2 ^ (k + 1)).totient r m ell ≤ shapeMinimumStretch (S X) ∧
          ∀ c : Fin m → 𝓞 K,
            discreteTotalVariation ((numberFieldEllipsoidalGaussian K (cyclotomicIntegralBasis K hζ) m (S X) c).map X.mulVec)
              ((numberFieldGaussian K (cyclotomicIntegralBasis K hζ) r w hw.ne').map (Equiv.addRight (X.mulVec c))) ≤
                (2 * realSecurityError (ell + 6)) / (1 - 2 * realSecurityError (ell + 6)) := by
  dsimp only
  let : Nonempty (Fin (r * (2 ^ (k + 1)).totient)) :=
    ⟨⟨0, Nat.mul_pos (by omega : 0 < r) (integralBasis_dimension_pos K (cyclotomicIntegralBasis K hζ))⟩⟩
  obtain ⟨hB, hV, hw⟩ := powerTwoConstantSpherical_parameters_pos (m := m) (integralBasis_dimension_pos K (cyclotomicIntegralBasis K hζ)) hr
    (by omega) hell hs
  obtain ⟨G, hprob, hgood⟩ := numberField_constantWidth_spherical_event K hζ hr hmr
    hell hs hwidth hbudget
  let hsurj := fun X hX => (hgood X hX).1
  let S := numberFieldSphericalEventShape K (cyclotomicIntegralBasis K hζ) G hsurj hw
  refine ⟨hw, G, S, hprob, numberFieldSphericalEventShape_positive K (cyclotomicIntegralBasis K hζ) G hsurj hw,
    numberFieldSphericalEventShape_of_not_mem K (cyclotomicIntegralBasis K hζ) G hsurj hw, ?_⟩
  intro X hX
  have hSX : S X = numberFieldSphericalInputShape K (cyclotomicIntegralBasis K hζ) X (hsurj X hX) hw :=
    numberFieldSphericalEventShape_of_mem K (cyclotomicIntegralBasis K hζ) G hsurj hw X hX
  have hA := canonicalEuclideanMatrix_surjective K (cyclotomicIntegralBasis K hζ) X (hsurj X hX)
  have hn := surjective_operator_norm_pos (canonicalEuclideanMatrix K (cyclotomicIntegralBasis K hζ) X).toContinuousLinearMap hA
  have hBV : powerTwoConstantSmoothingBound (2 ^ (k + 1)).totient r m ell *
      ‖(canonicalEuclideanMatrix K (cyclotomicIntegralBasis K hζ) X).toContinuousLinearMap‖ ≤
        powerTwoConstantSphericalWidth (2 ^ (k + 1)).totient r m s ell :=
    mul_le_mul_of_nonneg_left (hgood X hX).2.2 hB.le
  refine ⟨hsurj X hX, ?_, ?_, ?_⟩
  · rw [hSX]
    exact sphericalShapingShape_matrix _ _ _
  · rw [hSX, numberFieldSphericalInputShape_minimumStretch]
    exact (le_div_iff₀ hn).mpr hBV
  · intro c
    rw [hSX]
    have hδ := real_constant_failureBudget_le hell
    exact numberField_gaussian_spherical_pushforward K (cyclotomicIntegralBasis K hζ) X (hsurj X hX) hw
      (mul_pos (by norm_num) (realSecurityError_pos (ell + 6))) (by linarith)
      ((mul_le_mul_of_nonneg_right (hgood X hX).2.1 (norm_nonneg _)).trans hBV) c

theorem numberField_constantWidth_spherical_lhl (hζ : IsPrimitiveRoot ζ (2 ^ (k + 1))) (hr : 1 ≤ r) (hmr : r < m)
    {ell s : ℝ} (hell : 1 ≤ ell) (hs : 0 < s)
    (hwidth : Real.sqrt (2 ^ (k + 1)).totient ≤ s)
    (hbudget : ((r * (2 ^ (k + 1)).totient : ℕ) : ℝ) * Real.log (powerTwoConstantScale (2 ^ (k + 1)).totient r m s ell) +
      2 * Real.log (1 / realSecurityError (ell + 6)) ≤ (m : ℝ) * Real.log (50 / 49)) :
    let w := powerTwoConstantSphericalWidth (2 ^ (k + 1)).totient r m s ell
    ∃ hw : 0 < w,
      ∃ S : Matrix (Fin r) (Fin m) (𝓞 K) → Euclidean (m * (2 ^ (k + 1)).totient) ≃L[ℝ] Euclidean (m * (2 ^ (k + 1)).totient),
        ∀ c : Matrix (Fin r) (Fin m) (𝓞 K) → Fin m → 𝓞 K,
          let p := numberFieldMatrixLaw K (cyclotomicIntegralBasis K hζ) r m s hs.ne'
          let D := discreteTotalVariation
            (jointPMF p (fun X => (numberFieldEllipsoidalGaussian K (cyclotomicIntegralBasis K hζ) m (S X) (c X)).map X.mulVec))
            (jointPMF p (fun X => (numberFieldGaussian K (cyclotomicIntegralBasis K hζ) r w hw.ne').map
              (Equiv.addRight (X.mulVec (c X)))))
          D ≤ jointErrorBound (realSecurityError (ell + 6)) 1 ∧ D < realSecurityError ell := by
  dsimp only
  obtain ⟨hw, G, S, hprob, _, _, hgood⟩ :=
    numberField_constantWidth_spherical_certificate K hζ hr hmr hell hs hwidth hbudget
  refine ⟨hw, S, ?_⟩
  intro c
  have hδ := real_constant_failureBudget_le hell
  have hε : 0 ≤ (2 * realSecurityError (ell + 6)) / (1 - 2 * realSecurityError (ell + 6)) :=
    div_nonneg (mul_nonneg (by norm_num) (realSecurityError_pos (ell + 6)).le) (by linarith)
  have hb := discreteTotalVariation_joint_le_of_event_mass
    (numberFieldMatrixLaw K (cyclotomicIntegralBasis K hζ) r m s hs.ne') _ _ G hprob hε
    (fun X hX => (hgood X hX).choose_spec.2.2 (c X))
  have he : 3 * realSecurityError (ell + 6) +
      2 * realSecurityError (ell + 6) / (1 - 2 * realSecurityError (ell + 6)) =
        jointErrorBound (realSecurityError (ell + 6)) 1 := by
    simp only [jointErrorBound, Nat.cast_one, mul_one]
  rw [he] at hb
  exact ⟨hb, hb.trans_lt (real_constant_jointError_lt hell)⟩


end GeometricGaussianLHL
end

end NumberFieldConstantSphericalLHL

section NumberFieldSphericalLHL

/-!
## Polynomial-width spherical Gaussian leftover hashing

The good event comes from the proved number-field matrix theorem. The
input uses the actual positive square root prescribed in Corollary 5.2,
with identity shape on the complement. The width is exactly `B V₀`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Module NumberField
open scoped MatrixOrder

namespace GeometricGaussianLHL

variable (K : Type*) [Field K] [NumberField K] {d r m : ℕ}

theorem numberField_polynomial_spherical_certificate (b : Basis (Fin d) ℤ (𝓞 K))
    (i : Fin d) (hidentity : b i = 1) (hr : 1 ≤ r) (hmr : r < m)
    {ell s : ℝ} (hell : 1 ≤ ell) (hs : 0 < s)
    (hwidth : 8 * Real.sqrt (r * d) ≤ s / basisAlpha K b)
    (hbudget : ((r * d : ℕ) : ℝ) * Real.log (numberFieldPolynomialScale K b r m s ell) +
      2 * Real.log (1 / realSecurityError (ell + 4)) ≤ (m : ℝ) * Real.log (8 / 7)) :
    let w := numberFieldPolynomialSphericalWidth K b r m s ell
    ∃ hw : 0 < w, ∃ G : Set (Matrix (Fin r) (Fin m) (𝓞 K)),
      ∃ S : Matrix (Fin r) (Fin m) (𝓞 K) → Euclidean (m * d) ≃L[ℝ] Euclidean (m * d),
        ENNReal.ofReal (1 - 3 * realSecurityError (ell + 4)) ≤
          (numberFieldMatrixLaw K b r m s hs.ne').toOuterMeasure G ∧
        (∀ X, (S X).toLinearMap.IsPositive) ∧
        (∀ X ∉ G, S X = ContinuousLinearEquiv.refl ℝ (Euclidean (m * d))) ∧
        ∀ X ∈ G, ∃ hX : Function.Surjective X.mulVec,
          Matrix.toEuclideanLin.symm (S X).toLinearMap = CFC.sqrt
            (sphericalShapingMatrix (canonicalEuclideanMatrix K b X).toContinuousLinearMap
              (canonicalEuclideanMatrix_surjective K b X hX) w) ∧
          numberFieldPolynomialSmoothingBound K b r m ell ≤ shapeMinimumStretch (S X) ∧
          ∀ c : Fin m → 𝓞 K,
            discreteTotalVariation ((numberFieldEllipsoidalGaussian K b m (S X) c).map X.mulVec)
              ((numberFieldGaussian K b r w hw.ne').map (Equiv.addRight (X.mulVec c))) ≤
                (2 * realSecurityError (ell + 4)) / (1 - 2 * realSecurityError (ell + 4)) := by
  dsimp only
  let : Nonempty (Fin (r * d)) :=
    ⟨⟨0, Nat.mul_pos (by omega : 0 < r) (integralBasis_dimension_pos K b)⟩⟩
  obtain ⟨hB, hV, hw⟩ := numberFieldPolynomialSpherical_parameters_pos K b (r := r) (m := m) i hidentity hr
    (by omega) hell hs
  obtain ⟨G, hprob, hgood⟩ := numberField_polynomial_spherical_event K b i hidentity hr hmr
    hell hs hwidth hbudget
  let hsurj := fun X hX => (hgood X hX).1
  let S := numberFieldSphericalEventShape K b G hsurj hw
  refine ⟨hw, G, S, hprob, numberFieldSphericalEventShape_positive K b G hsurj hw,
    numberFieldSphericalEventShape_of_not_mem K b G hsurj hw, ?_⟩
  intro X hX
  have hSX : S X = numberFieldSphericalInputShape K b X (hsurj X hX) hw :=
    numberFieldSphericalEventShape_of_mem K b G hsurj hw X hX
  have hA := canonicalEuclideanMatrix_surjective K b X (hsurj X hX)
  have hn := surjective_operator_norm_pos (canonicalEuclideanMatrix K b X).toContinuousLinearMap hA
  have hBV : numberFieldPolynomialSmoothingBound K b r m ell *
      ‖(canonicalEuclideanMatrix K b X).toContinuousLinearMap‖ ≤
        numberFieldPolynomialSphericalWidth K b r m s ell :=
    mul_le_mul_of_nonneg_left (hgood X hX).2.2 hB.le
  refine ⟨hsurj X hX, ?_, ?_, ?_⟩
  · rw [hSX]
    exact sphericalShapingShape_matrix _ _ _
  · rw [hSX, numberFieldSphericalInputShape_minimumStretch]
    exact (le_div_iff₀ hn).mpr hBV
  · intro c
    rw [hSX]
    have hδ := real_polynomial_failureBudget_le hell
    exact numberField_gaussian_spherical_pushforward K b X (hsurj X hX) hw
      (mul_pos (by norm_num) (realSecurityError_pos (ell + 4))) (by linarith)
      ((mul_le_mul_of_nonneg_right (hgood X hX).2.1 (norm_nonneg _)).trans hBV) c

theorem numberField_polynomial_spherical_lhl (b : Basis (Fin d) ℤ (𝓞 K))
    (i : Fin d) (hidentity : b i = 1) (hr : 1 ≤ r) (hmr : r < m)
    {ell s : ℝ} (hell : 1 ≤ ell) (hs : 0 < s)
    (hwidth : 8 * Real.sqrt (r * d) ≤ s / basisAlpha K b)
    (hbudget : ((r * d : ℕ) : ℝ) * Real.log (numberFieldPolynomialScale K b r m s ell) +
      2 * Real.log (1 / realSecurityError (ell + 4)) ≤ (m : ℝ) * Real.log (8 / 7)) :
    let w := numberFieldPolynomialSphericalWidth K b r m s ell
    ∃ hw : 0 < w,
      ∃ S : Matrix (Fin r) (Fin m) (𝓞 K) → Euclidean (m * d) ≃L[ℝ] Euclidean (m * d),
        ∀ c : Matrix (Fin r) (Fin m) (𝓞 K) → Fin m → 𝓞 K,
          let p := numberFieldMatrixLaw K b r m s hs.ne'
          let D := discreteTotalVariation
            (jointPMF p (fun X => (numberFieldEllipsoidalGaussian K b m (S X) (c X)).map X.mulVec))
            (jointPMF p (fun X => (numberFieldGaussian K b r w hw.ne').map
              (Equiv.addRight (X.mulVec (c X)))))
          D ≤ jointErrorBound (realSecurityError (ell + 4)) 1 ∧ D < realSecurityError ell := by
  dsimp only
  obtain ⟨hw, G, S, hprob, _, _, hgood⟩ :=
    numberField_polynomial_spherical_certificate K b i hidentity hr hmr hell hs hwidth hbudget
  refine ⟨hw, S, ?_⟩
  intro c
  have hδ := real_polynomial_failureBudget_le hell
  have hε : 0 ≤ (2 * realSecurityError (ell + 4)) / (1 - 2 * realSecurityError (ell + 4)) :=
    div_nonneg (mul_nonneg (by norm_num) (realSecurityError_pos (ell + 4)).le) (by linarith)
  have hb := discreteTotalVariation_joint_le_of_event_mass
    (numberFieldMatrixLaw K b r m s hs.ne') _ _ G hprob hε
    (fun X hX => (hgood X hX).choose_spec.2.2 (c X))
  have he : 3 * realSecurityError (ell + 4) +
      2 * realSecurityError (ell + 4) / (1 - 2 * realSecurityError (ell + 4)) =
        jointErrorBound (realSecurityError (ell + 4)) 1 := by
    simp only [jointErrorBound, Nat.cast_one, mul_one]
  rw [he] at hb
  exact ⟨hb, hb.trans_lt (real_polynomial_jointError_lt hell)⟩

end GeometricGaussianLHL
end

end NumberFieldSphericalLHL

section NumberFieldSphericalHints

/-!
## Simultaneous spherical hints over a number field

The source law samples the columns of `R` independently from the shaped
ring Gaussian and returns the actual matrix `X * R + 1`. The target has
independent spherical columns centered at the identity columns. For the
finite polynomial parameters the distance is exactly budgeted by
`3δ + 2rδ/(1-2δ)`, as in Corollary 5.3.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Module NumberField

namespace GeometricGaussianLHL

theorem pmf_map_addRight_zero {A : Type*} [AddGroup A] (p : PMF A) :
    p.map (Equiv.addRight (0 : A)) = p := by
  have h : (Equiv.addRight (0 : A) : A → A) = id := by
    funext x
    exact add_zero x
  rw [h, PMF.map_id]

variable (K : Type*) [Field K] [NumberField K] {d r m : ℕ}

theorem numberField_spherical_hints_good_event [Nontrivial (Euclidean (r * d))]
    (b : Basis (Fin d) ℤ (𝓞 K)) (p : PMF (Matrix (Fin r) (Fin m) (𝓞 K)))
    (G : Set (Matrix (Fin r) (Fin m) (𝓞 K)))
    (hsurj : ∀ X ∈ G, Function.Surjective X.mulVec) {δ ε w : ℝ} (hw : 0 < w)
    (hprob : ENNReal.ofReal (1 - δ) ≤ p.toOuterMeasure G) (hε : 0 < ε) (hε1 : ε < 1)
    (hwidth : ∀ X ∈ G, smoothingParameter (canonicalKernel K X) ε *
      ‖(canonicalEuclideanMatrix K b X).toContinuousLinearMap‖ ≤ w) :
    discreteTotalVariation
      (jointPMF p (fun X => (independentMatrixColumns (fun _ : Fin r =>
        numberFieldEllipsoidalGaussian K b m (numberFieldSphericalEventShape K b G hsurj hw X) 0)).map
          (fun R => X * R + (1 : Matrix (Fin r) (Fin r) (𝓞 K)))))
      (jointPMF p (fun _ => independentMatrixColumns (fun j : Fin r =>
        (numberFieldGaussian K b r w hw.ne').map (Equiv.addRight (matrixIdentityColumn j))))) ≤
      δ + (r : ℝ) * (ε / (1 - ε)) := by
  apply discreteTotalVariation_matrixHint_joint_good_event p _ _ G hprob
    (div_nonneg hε.le (sub_pos.mpr hε1).le)
  intro X hX j
  rw [numberFieldSphericalEventShape_of_mem K b G hsurj hw X hX]
  have h := numberField_gaussian_spherical_pushforward K b X (hsurj X hX) hw hε hε1 (hwidth X hX) 0
  simpa only [Matrix.mulVec_zero, pmf_map_addRight_zero] using h

theorem numberField_polynomial_spherical_hints (b : Basis (Fin d) ℤ (𝓞 K))
    (i : Fin d) (hidentity : b i = 1) (hr : 1 ≤ r) (hmr : r < m)
    {ell s : ℝ} (hell : 1 ≤ ell) (hs : 0 < s)
    (hwidth : 8 * Real.sqrt (r * d) ≤ s / basisAlpha K b)
    (hbudget : ((r * d : ℕ) : ℝ) * Real.log (numberFieldPolynomialScale K b r m s ell) +
      2 * Real.log (1 / realSecurityError (ell + 4)) ≤ (m : ℝ) * Real.log (8 / 7)) :
    let w := numberFieldPolynomialSphericalWidth K b r m s ell
    ∃ hw : 0 < w,
      ∃ S : Matrix (Fin r) (Fin m) (𝓞 K) → Euclidean (m * d) ≃L[ℝ] Euclidean (m * d),
        let p := numberFieldMatrixLaw K b r m s hs.ne'
        discreteTotalVariation
          (jointPMF p (fun X => (independentMatrixColumns (fun _ : Fin r =>
            numberFieldEllipsoidalGaussian K b m (S X) 0)).map
              (fun R => X * R + (1 : Matrix (Fin r) (Fin r) (𝓞 K)))))
          (jointPMF p (fun _ => independentMatrixColumns (fun j : Fin r =>
            (numberFieldGaussian K b r w hw.ne').map (Equiv.addRight (matrixIdentityColumn j))))) ≤
          jointErrorBound (realSecurityError (ell + 4)) r := by
  dsimp only
  obtain ⟨hw, G, S, hprob, _, _, hgood⟩ :=
    numberField_polynomial_spherical_certificate K b i hidentity hr hmr hell hs hwidth hbudget
  refine ⟨hw, S, ?_⟩
  have hδ := real_polynomial_failureBudget_le hell
  have hε : 0 ≤ (2 * realSecurityError (ell + 4)) / (1 - 2 * realSecurityError (ell + 4)) :=
    div_nonneg (mul_nonneg (by norm_num) (realSecurityError_pos (ell + 4)).le) (by linarith)
  have hb := discreteTotalVariation_matrixHint_joint_good_event
    (numberFieldMatrixLaw K b r m s hs.ne')
    (fun X _ => numberFieldEllipsoidalGaussian K b m (S X) 0)
    (fun _ _ => numberFieldGaussian K b r _ hw.ne') G hprob hε (by
      intro X hX j
      have h := (hgood X hX).choose_spec.2.2 0
      simpa only [Matrix.mulVec_zero, pmf_map_addRight_zero] using h)
  convert hb using 1
  unfold jointErrorBound
  ring

end GeometricGaussianLHL
end

end NumberFieldSphericalHints

section NumberFieldConstantSphericalHints

/-!
## Constant-width spherical Gaussian consequences

Independent columns of the shaped ring Gaussian give the literal hint
matrix `X * R + 1`. The target consists of independent spherical columns
centered at the identity columns, with error `3δ + 2rδ/(1-2δ)`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Module NumberField
open scoped MatrixOrder

namespace GeometricGaussianLHL

variable (K : Type*) [Field K] [NumberField K] {k r m : ℕ}
  [IsCyclotomicExtension {2 ^ (k + 1)} ℚ K] {ζ : K}

theorem numberField_constantWidth_spherical_hints (hζ : IsPrimitiveRoot ζ (2 ^ (k + 1))) (hr : 1 ≤ r) (hmr : r < m)
    {ell s : ℝ} (hell : 1 ≤ ell) (hs : 0 < s)
    (hwidth : Real.sqrt (2 ^ (k + 1)).totient ≤ s)
    (hbudget : ((r * (2 ^ (k + 1)).totient : ℕ) : ℝ) * Real.log (powerTwoConstantScale (2 ^ (k + 1)).totient r m s ell) +
      2 * Real.log (1 / realSecurityError (ell + 6)) ≤ (m : ℝ) * Real.log (50 / 49)) :
    let w := powerTwoConstantSphericalWidth (2 ^ (k + 1)).totient r m s ell
    ∃ hw : 0 < w,
      ∃ S : Matrix (Fin r) (Fin m) (𝓞 K) → Euclidean (m * (2 ^ (k + 1)).totient) ≃L[ℝ] Euclidean (m * (2 ^ (k + 1)).totient),
        let p := numberFieldMatrixLaw K (cyclotomicIntegralBasis K hζ) r m s hs.ne'
        discreteTotalVariation
          (jointPMF p (fun X => (independentMatrixColumns (fun _ : Fin r =>
            numberFieldEllipsoidalGaussian K (cyclotomicIntegralBasis K hζ) m (S X) 0)).map
              (fun R => X * R + (1 : Matrix (Fin r) (Fin r) (𝓞 K)))))
          (jointPMF p (fun _ => independentMatrixColumns (fun j : Fin r =>
            (numberFieldGaussian K (cyclotomicIntegralBasis K hζ) r w hw.ne').map (Equiv.addRight (matrixIdentityColumn j))))) ≤
          jointErrorBound (realSecurityError (ell + 6)) r := by
  dsimp only
  obtain ⟨hw, G, S, hprob, _, _, hgood⟩ :=
    numberField_constantWidth_spherical_certificate K hζ hr hmr hell hs hwidth hbudget
  refine ⟨hw, S, ?_⟩
  have hδ := real_constant_failureBudget_le hell
  have hε : 0 ≤ (2 * realSecurityError (ell + 6)) / (1 - 2 * realSecurityError (ell + 6)) :=
    div_nonneg (mul_nonneg (by norm_num) (realSecurityError_pos (ell + 6)).le) (by linarith)
  have hb := discreteTotalVariation_matrixHint_joint_good_event
    (numberFieldMatrixLaw K (cyclotomicIntegralBasis K hζ) r m s hs.ne')
    (fun X _ => numberFieldEllipsoidalGaussian K (cyclotomicIntegralBasis K hζ) m (S X) 0)
    (fun _ _ => numberFieldGaussian K (cyclotomicIntegralBasis K hζ) r _ hw.ne') G hprob hε (by
      intro X hX j
      have h := (hgood X hX).choose_spec.2.2 0
      simpa only [Matrix.mulVec_zero, pmf_map_addRight_zero] using h)
  convert hb using 1
  unfold jointErrorBound
  ring


end GeometricGaussianLHL
end

end NumberFieldConstantSphericalHints

section SphericalHintEvents

/-!
## Simultaneous hints with a separate spectral event

The geometric and spectral events may be dependent. Their exceptional
probabilities are each paid once, while only the conditional Gaussian error
is multiplied by the number of hint columns. These separate budgets apply
to the spectral specialization of Corollary 5.3.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Module NumberField

namespace GeometricGaussianLHL

variable (K : Type*) [Field K] [NumberField K] {d r m : ℕ}
  [Nontrivial (Euclidean (r * d))]

theorem numberField_spherical_hints_two_events (b : Basis (Fin d) ℤ (𝓞 K))
    (p : PMF (Matrix (Fin r) (Fin m) (𝓞 K)))
    (G H : Set (Matrix (Fin r) (Fin m) (𝓞 K)))
    (hsurj : ∀ X ∈ G, Function.Surjective X.mulVec) {δG δH ε B V w : ℝ} (hw : 0 < w)
    (hG : ENNReal.ofReal (1 - δG) ≤ p.toOuterMeasure G)
    (hH : ENNReal.ofReal (1 - δH) ≤ p.toOuterMeasure H) (hε : 0 < ε) (hε1 : ε < 1)
    (hB : 0 ≤ B) (hBV : B * V ≤ w)
    (hsmooth : ∀ X ∈ G, smoothingParameter (canonicalKernel K X) ε ≤ B)
    (hnorm : ∀ X ∈ H, ‖(canonicalEuclideanMatrix K b X).toContinuousLinearMap‖ ≤ V) :
    discreteTotalVariation
      (jointPMF p (fun X => (independentMatrixColumns (fun _ : Fin r =>
        numberFieldEllipsoidalGaussian K b m
          (numberFieldSphericalEventShape K b (G ∩ H) (fun X hX => hsurj X hX.1) hw X) 0)).map
            (fun R => X * R + (1 : Matrix (Fin r) (Fin r) (𝓞 K)))))
      (jointPMF p (fun _ => independentMatrixColumns (fun j : Fin r =>
        (numberFieldGaussian K b r w hw.ne').map (Equiv.addRight (matrixIdentityColumn j))))) ≤
      δG + δH + (r : ℝ) * (ε / (1 - ε)) := by
  apply numberField_spherical_hints_good_event K b p (G ∩ H) (fun X hX => hsurj X hX.1) hw
    (pmf_intersection_event_mass p G H hG hH) hε hε1
  intro X hX
  exact (mul_le_mul_of_nonneg_right (hsmooth X hX.1) (norm_nonneg _)).trans
    ((mul_le_mul_of_nonneg_left (hnorm X hX.2) hB).trans hBV)

end GeometricGaussianLHL
end

end SphericalHintEvents

section SphericalOutputCertificate

/-!
## A joint certificate for spherical output and simultaneous hints

The proposition below records constructed outputs: the actual shaped law,
its positive square-root formula on a proved event, the identity fallback,
and both joint-distribution bounds. Its constructor proves every field
from the event; no desired probability or distribution conclusion is assumed.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Module NumberField
open scoped MatrixOrder

namespace GeometricGaussianLHL

variable (K : Type*) [Field K] [NumberField K] {d r m : ℕ}

def SphericalOutputCertificate (b : Basis (Fin d) ℤ (𝓞 K))
    (p : PMF (Matrix (Fin r) (Fin m) (𝓞 K))) (δ ε B w : ℝ) : Prop :=
  ∃ hw : 0 < w, ∃ G : Set (Matrix (Fin r) (Fin m) (𝓞 K)),
    ∃ S : Matrix (Fin r) (Fin m) (𝓞 K) → Euclidean (m * d) ≃L[ℝ] Euclidean (m * d),
      ENNReal.ofReal (1 - δ) ≤ p.toOuterMeasure G ∧
      (∀ X, (S X).toLinearMap.IsPositive) ∧
      (∀ X ∉ G, S X = ContinuousLinearEquiv.refl ℝ (Euclidean (m * d))) ∧
      (∀ X ∈ G, ∃ hX : Function.Surjective X.mulVec,
        Matrix.toEuclideanLin.symm (S X).toLinearMap = CFC.sqrt
          (sphericalShapingMatrix (canonicalEuclideanMatrix K b X).toContinuousLinearMap
            (canonicalEuclideanMatrix_surjective K b X hX) w) ∧
        B ≤ shapeMinimumStretch (S X) ∧
        smoothingParameter (canonicalKernel K X) ε ≤ B ∧
        ∀ c : Fin m → 𝓞 K,
          discreteTotalVariation ((numberFieldEllipsoidalGaussian K b m (S X) c).map X.mulVec)
            ((numberFieldGaussian K b r w hw.ne').map (Equiv.addRight (X.mulVec c))) ≤
              ε / (1 - ε)) ∧
      (∀ c : Matrix (Fin r) (Fin m) (𝓞 K) → Fin m → 𝓞 K,
        discreteTotalVariation
          (jointPMF p (fun X => (numberFieldEllipsoidalGaussian K b m (S X) (c X)).map X.mulVec))
          (jointPMF p (fun X => (numberFieldGaussian K b r w hw.ne').map
            (Equiv.addRight (X.mulVec (c X))))) ≤ δ + ε / (1 - ε)) ∧
      discreteTotalVariation
        (jointPMF p (fun X => (independentMatrixColumns (fun _ : Fin r =>
          numberFieldEllipsoidalGaussian K b m (S X) 0)).map
            (fun R => X * R + (1 : Matrix (Fin r) (Fin r) (𝓞 K)))))
        (jointPMF p (fun _ => independentMatrixColumns (fun j : Fin r =>
          (numberFieldGaussian K b r w hw.ne').map (Equiv.addRight (matrixIdentityColumn j))))) ≤
        δ + (r : ℝ) * (ε / (1 - ε))

theorem sphericalOutputCertificate_of_event [Nontrivial (Euclidean (r * d))]
    (b : Basis (Fin d) ℤ (𝓞 K)) (p : PMF (Matrix (Fin r) (Fin m) (𝓞 K)))
    (G : Set (Matrix (Fin r) (Fin m) (𝓞 K)))
    (hsurj : ∀ X ∈ G, Function.Surjective X.mulVec) {δ ε B w : ℝ} (hw : 0 < w)
    (hprob : ENNReal.ofReal (1 - δ) ≤ p.toOuterMeasure G) (hε : 0 < ε) (hε1 : ε < 1)
    (hsmooth : ∀ X ∈ G, smoothingParameter (canonicalKernel K X) ε ≤ B)
    (hwidth : ∀ X ∈ G, B * ‖(canonicalEuclideanMatrix K b X).toContinuousLinearMap‖ ≤ w) :
    SphericalOutputCertificate K b p δ ε B w := by
  let S := numberFieldSphericalEventShape K b G hsurj hw
  have hactual : ∀ X ∈ G, smoothingParameter (canonicalKernel K X) ε *
      ‖(canonicalEuclideanMatrix K b X).toContinuousLinearMap‖ ≤ w := by
    intro X hX
    exact (mul_le_mul_of_nonneg_right (hsmooth X hX) (norm_nonneg _)).trans (hwidth X hX)
  refine ⟨hw, G, S, hprob, numberFieldSphericalEventShape_positive K b G hsurj hw,
    numberFieldSphericalEventShape_of_not_mem K b G hsurj hw, ?_, ?_, ?_⟩
  · intro X hX
    have hSX : S X = numberFieldSphericalInputShape K b X (hsurj X hX) hw :=
      numberFieldSphericalEventShape_of_mem K b G hsurj hw X hX
    have hn := surjective_operator_norm_pos (canonicalEuclideanMatrix K b X).toContinuousLinearMap
      (canonicalEuclideanMatrix_surjective K b X (hsurj X hX))
    refine ⟨hsurj X hX, ?_, ?_, hsmooth X hX, ?_⟩
    · rw [hSX]
      exact sphericalShapingShape_matrix _ _ _
    · rw [hSX, numberFieldSphericalInputShape_minimumStretch]
      exact (le_div_iff₀ hn).mpr (hwidth X hX)
    · intro c
      rw [hSX]
      exact numberField_gaussian_spherical_pushforward K b X (hsurj X hX) hw hε hε1 (hactual X hX) c
  · exact numberField_spherical_joint_good_event K b p G hsurj hw hprob hε hε1 hactual
  · exact numberField_spherical_hints_good_event K b p G hsurj hw hprob hε hε1 hactual

/-- The spectral event is proved for the actual matrix PMF, with its
exceptional probability charged once in both joint laws. -/
theorem numberField_spectral_spherical_certificate [Nontrivial (Euclidean (r * d))]
    (b : Basis (Fin d) ℤ (𝓞 K)) (G : Set (Matrix (Fin r) (Fin m) (𝓞 K)))
    (hsurj : ∀ X ∈ G, Function.Surjective X.mulVec)
    {s δG δsp ε B w : ℝ} (hs : 0 < s) (hw : 0 < w)
    (hG : ENNReal.ofReal (1 - δG) ≤ (numberFieldMatrixLaw K b r m s hs.ne').toOuterMeasure G)
    (hsp : 0 < δsp) (hsp1 : δsp < 1) (hrm : r ≤ m)
    (hlog : Real.log (2 * d / δsp) ≤ m) (hε : 0 < ε) (hε1 : ε < 1)
    (hB : 0 ≤ B) (hBw : B * (4 * s * Real.sqrt m) ≤ w)
    (hsmooth : ∀ X ∈ G, smoothingParameter (canonicalKernel K X) ε ≤ B) :
    SphericalOutputCertificate K b (numberFieldMatrixLaw K b r m s hs.ne')
      (δG + δsp) ε B w := by
  let H := {X : Matrix (Fin r) (Fin m) (𝓞 K) |
    ‖(canonicalEuclideanMatrix K b X).toContinuousLinearMap‖ ≤ 4 * s * Real.sqrt m}
  have hH := numberField_spherical_spectral_four K b hs hsp hsp1 hrm hlog
  apply sphericalOutputCertificate_of_event K b _ (G ∩ H) (fun X hX => hsurj X hX.1) hw
    (pmf_intersection_event_mass _ G H hG hH) hε hε1 (fun X hX => hsmooth X hX.1)
  intro X hX
  exact (mul_le_mul_of_nonneg_left hX.2 hB).trans hBw

end GeometricGaussianLHL
end

end SphericalOutputCertificate

section ConstantSpectralSpherical

/-!
## Spectral spherical output and hints at constant coefficient width

The actual power-of-two Gaussian law and geometric event supply the input
for the spectral certificate. All widths at least `4 s sqrt(m) B` work,
including equality. The corrected joint budgets charge the spectral failure
once; the single-output error remains strictly below `2^(-ell)`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Module NumberField

namespace GeometricGaussianLHL

variable (K : Type*) [Field K] [NumberField K] {k r m : ℕ}
  [IsCyclotomicExtension {2 ^ (k + 1)} ℚ K] {ζ : K}

theorem numberField_constantWidth_spectral_spherical (hζ : IsPrimitiveRoot ζ (2 ^ (k + 1)))
    (hr : 1 ≤ r) (hmr : r < m) {ell s w : ℝ} (hell : 1 ≤ ell) (hs : 0 < s)
    (hwidth : Real.sqrt (2 ^ (k + 1)).totient ≤ s)
    (hbudget : ((r * (2 ^ (k + 1)).totient : ℕ) : ℝ) *
      Real.log (powerTwoConstantScale (2 ^ (k + 1)).totient r m s ell) +
      2 * Real.log (1 / realSecurityError (ell + 6)) ≤ (m : ℝ) * Real.log (50 / 49))
    (hspectral : lowerSpectralColumnConstant *
      ((r : ℝ) + Real.log (2 * (2 ^ (k + 1)).totient / realSecurityError (ell + 6))) ≤ m)
    (hw : powerTwoConstantSmoothingBound (2 ^ (k + 1)).totient r m ell *
      (4 * s * Real.sqrt m) ≤ w) :
    SphericalOutputCertificate K (cyclotomicIntegralBasis K hζ)
      (numberFieldMatrixLaw K (cyclotomicIntegralBasis K hζ) r m s hs.ne')
      (4 * realSecurityError (ell + 6)) (2 * realSecurityError (ell + 6))
      (powerTwoConstantSmoothingBound (2 ^ (k + 1)).totient r m ell) w ∧
    4 * realSecurityError (ell + 6) +
      2 * realSecurityError (ell + 6) / (1 - 2 * realSecurityError (ell + 6)) < realSecurityError ell := by
  let b := cyclotomicIntegralBasis K hζ
  have hd := integralBasis_dimension_pos K b
  let : Nonempty (Fin (r * (2 ^ (k + 1)).totient)) := ⟨⟨0, Nat.mul_pos (by omega : 0 < r) hd⟩⟩
  have hm : (0 : ℝ) < m := Nat.cast_pos.mpr (by omega)
  have hB := (powerTwoConstantSpherical_parameters_pos (r := r) (m := m)
    hd hr (by omega) hell hs).1
  have hwpos : 0 < w := (mul_pos hB (by positivity : 0 < 4 * s * Real.sqrt m)).trans_le hw
  have hδ := realSecurityError_pos (ell + 6)
  have hδsmall := real_constant_failureBudget_le hell
  obtain ⟨G, hprob, hgood⟩ := numberField_constantWidth_spherical_event K hζ
    hr hmr hell hs hwidth hbudget
  refine ⟨?_, constant_spectral_joint_error_lt hell⟩
  have h := numberField_spectral_spherical_certificate K b G (fun X hX => (hgood X hX).1)
    hs hwpos hprob hδ (by linarith) hmr.le
    (spectral_columns_log_condition hd hδ (by linarith) hspectral)
    (mul_pos (by norm_num) hδ) (by linarith) hB.le hw (fun X hX => (hgood X hX).2.1)
  convert h using 1; ring

end GeometricGaussianLHL
end

end ConstantSpectralSpherical

section PolynomialSpectralSpherical

/-!
## Spectral spherical output and hints at polynomial coefficient width

This proves the spectral specializations of Corollaries 5.2 and 5.3 from
the actual finite geometric theorem and the actual spectral probability.
Every width at least `4 s sqrt(m) B` is allowed, including equality. The
extra spectral failure is paid once: `4δ + 2δ/(1-2δ)` for one output and
`4δ + 2rδ/(1-2δ)` for hints. The first is still strictly below `2^(-ell)`.
The result applies to all number fields, hence to the stated power-of-two case.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Module NumberField

namespace GeometricGaussianLHL

variable (K : Type*) [Field K] [NumberField K] {d r m : ℕ}

theorem numberField_polynomial_spectral_spherical (b : Basis (Fin d) ℤ (𝓞 K))
    (i : Fin d) (hidentity : b i = 1) (hr : 1 ≤ r) (hmr : r < m)
    {ell s w : ℝ} (hell : 1 ≤ ell) (hs : 0 < s)
    (hwidth : 8 * Real.sqrt (r * d) ≤ s / basisAlpha K b)
    (hbudget : ((r * d : ℕ) : ℝ) * Real.log (numberFieldPolynomialScale K b r m s ell) +
      2 * Real.log (1 / realSecurityError (ell + 4)) ≤ (m : ℝ) * Real.log (8 / 7))
    (hspectral : lowerSpectralColumnConstant *
      ((r : ℝ) + Real.log (2 * d / realSecurityError (ell + 4))) ≤ m)
    (hw : numberFieldPolynomialSmoothingBound K b r m ell * (4 * s * Real.sqrt m) ≤ w) :
    SphericalOutputCertificate K b (numberFieldMatrixLaw K b r m s hs.ne')
      (4 * realSecurityError (ell + 4)) (2 * realSecurityError (ell + 4))
      (numberFieldPolynomialSmoothingBound K b r m ell) w ∧
    4 * realSecurityError (ell + 4) +
      2 * realSecurityError (ell + 4) / (1 - 2 * realSecurityError (ell + 4)) < realSecurityError ell := by
  have hd := integralBasis_dimension_pos K b
  let : Nonempty (Fin (r * d)) := ⟨⟨0, Nat.mul_pos (by omega : 0 < r) hd⟩⟩
  have hm : (0 : ℝ) < m := Nat.cast_pos.mpr (by omega)
  have hB := (numberFieldPolynomialSpherical_parameters_pos K b (r := r) (m := m)
    i hidentity hr (by omega) hell hs).1
  have hwpos : 0 < w := (mul_pos hB (by positivity : 0 < 4 * s * Real.sqrt m)).trans_le hw
  have hδ := realSecurityError_pos (ell + 4)
  have hδsmall := real_polynomial_failureBudget_le hell
  obtain ⟨G, hprob, hgood⟩ := numberField_polynomial_spherical_event K b i hidentity
    hr hmr hell hs hwidth hbudget
  refine ⟨?_, polynomial_spectral_joint_error_lt hell⟩
  have h := numberField_spectral_spherical_certificate K b G (fun X hX => (hgood X hX).1)
    hs hwpos hprob hδ (by linarith) hmr.le
    (spectral_columns_log_condition hd hδ (by linarith) hspectral)
    (mul_pos (by norm_num) hδ) (by linarith) hB.le hw (fun X hX => (hgood X hX).2.1)
  convert h using 1; ring

end GeometricGaussianLHL
end

end PolynomialSpectralSpherical
