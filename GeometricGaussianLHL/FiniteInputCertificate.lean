import GeometricGaussianLHL.CanonicalShaping
import GeometricGaussianLHL.SphericalLHL

/-!
# Finite-input Gaussian application certificates

This module collects the following proof sections, in dependency order.
- Joint output and simultaneous hints from certified computed shapes (`ComputedSphericalEvents`).
- ComputedSphericalCertificate (`ComputedSphericalCertificate`).
- Four parameter specializations of the computed spherical certificate (`ComputedSphericalParameters`).
- Gaussian certificates with an available finite input representation (`FiniteSphericalCertificate`).
- Four Gaussian regimes with available finite inputs (`FiniteSphericalParameters`).
-/

section ComputedSphericalEvents

/-!
## Joint output and simultaneous hints from certified computed shapes

The same positive-definite output matrix defines every input law. The bad
matrix event is paid once; numerical approximation is paid per hint column.
The identity completion outside the event defines a total mathematical law.
It does not assert that membership in the analytic event is executable.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Module NumberField
open scoped MatrixOrder Matrix.Norms.L2Operator

namespace GeometricGaussianLHL

variable (K : Type*) [Field K] [NumberField K] {d r m : ℕ}

/-- The literal joint laws, with separate exceptional and conditional errors. -/
def SphericalLawBounds (b : Basis (Fin d) ℤ (𝓞 K))
    (p : PMF (Matrix (Fin r) (Fin m) (𝓞 K)))
    (S : Matrix (Fin r) (Fin m) (𝓞 K) → Euclidean (m * d) ≃L[ℝ] Euclidean (m * d))
    (δ ν w : ℝ) (hw : 0 < w) : Prop :=
  (∀ c : Matrix (Fin r) (Fin m) (𝓞 K) → Fin m → 𝓞 K,
    discreteTotalVariation
      (jointPMF p (fun X => (numberFieldEllipsoidalGaussian K b m (S X) (c X)).map X.mulVec))
      (jointPMF p (fun X => (numberFieldGaussian K b r w hw.ne').map
        (Equiv.addRight (X.mulVec (c X))))) ≤ δ + ν) ∧
  discreteTotalVariation
    (jointPMF p (fun X => (independentMatrixColumns (fun _ : Fin r =>
      numberFieldEllipsoidalGaussian K b m (S X) 0)).map
        (fun R => X * R + (1 : Matrix (Fin r) (Fin r) (𝓞 K)))))
    (jointPMF p (fun _ => independentMatrixColumns (fun j : Fin r =>
      (numberFieldGaussian K b r w hw.ne').map (Equiv.addRight (matrixIdentityColumn j))))) ≤
    δ + (r : ℝ) * ν

theorem sphericalLawBounds_of_event (b : Basis (Fin d) ℤ (𝓞 K))
    (p : PMF (Matrix (Fin r) (Fin m) (𝓞 K))) (G : Set (Matrix (Fin r) (Fin m) (𝓞 K)))
    (S : Matrix (Fin r) (Fin m) (𝓞 K) → Euclidean (m * d) ≃L[ℝ] Euclidean (m * d))
    {δ ν w : ℝ} (hw : 0 < w) (hν : 0 ≤ ν)
    (hprob : ENNReal.ofReal (1 - δ) ≤ p.toOuterMeasure G)
    (himage : ∀ X ∈ G, ∀ z : Fin m → 𝓞 K,
      discreteTotalVariation ((numberFieldEllipsoidalGaussian K b m (S X) z).map X.mulVec)
        ((numberFieldGaussian K b r w hw.ne').map (Equiv.addRight (X.mulVec z))) ≤ ν) :
    SphericalLawBounds K b p S δ ν w hw := by
  constructor
  · intro c
    exact discreteTotalVariation_joint_le_of_event_mass p _ _ G hprob hν
      (fun X hX => himage X hX (c X))
  · apply discreteTotalVariation_matrixHint_joint_good_event p _ _ G hprob hν
    intro X hX j
    simpa only [Matrix.mulVec_zero, pmf_map_addRight_zero] using himage X hX 0

def computedShapeOnEvent (b : Basis (Fin d) ℤ (𝓞 K))
    (G : Set (Matrix (Fin r) (Fin m) (𝓞 K)))
    (R : Matrix (Fin r) (Fin m) (𝓞 K) → Matrix (Fin (m * d)) (Fin (m * d)) ℝ)
    (hR : ∀ X ∈ G, (R X).PosDef) (X : Matrix (Fin r) (Fin m) (𝓞 K)) :
    Euclidean (m * d) ≃L[ℝ] Euclidean (m * d) := by
  classical
  exact if hX : X ∈ G then canonicalComputedShape K b (R X) (hR X hX)
    else ContinuousLinearEquiv.refl ℝ (Euclidean (m * d))

theorem computedShapeOnEvent_of_mem (b : Basis (Fin d) ℤ (𝓞 K))
    (G : Set (Matrix (Fin r) (Fin m) (𝓞 K)))
    (R : Matrix (Fin r) (Fin m) (𝓞 K) → Matrix (Fin (m * d)) (Fin (m * d)) ℝ)
    (hR : ∀ X ∈ G, (R X).PosDef) (X : Matrix (Fin r) (Fin m) (𝓞 K)) (hX : X ∈ G) :
    computedShapeOnEvent K b G R hR X = canonicalComputedShape K b (R X) (hR X hX) := by
  simp only [computedShapeOnEvent, dite_eq_left hX]

theorem computedShapeOnEvent_of_not_mem (b : Basis (Fin d) ℤ (𝓞 K))
    (G : Set (Matrix (Fin r) (Fin m) (𝓞 K)))
    (R : Matrix (Fin r) (Fin m) (𝓞 K) → Matrix (Fin (m * d)) (Fin (m * d)) ℝ)
    (hR : ∀ X ∈ G, (R X).PosDef) (X : Matrix (Fin r) (Fin m) (𝓞 K)) (hX : X ∉ G) :
    computedShapeOnEvent K b G R hR X = ContinuousLinearEquiv.refl ℝ (Euclidean (m * d)) := by
  simp only [computedShapeOnEvent, dite_eq_right hX]

theorem computedShapeOnEvent_positive (b : Basis (Fin d) ℤ (𝓞 K))
    (G : Set (Matrix (Fin r) (Fin m) (𝓞 K)))
    (R : Matrix (Fin r) (Fin m) (𝓞 K) → Matrix (Fin (m * d)) (Fin (m * d)) ℝ)
    (hR : ∀ X ∈ G, (R X).PosDef) (X : Matrix (Fin r) (Fin m) (𝓞 K)) :
    (computedShapeOnEvent K b G R hR X).toLinearMap.IsPositive := by
  by_cases hX : X ∈ G
  · rw [computedShapeOnEvent_of_mem K b G R hR X hX]
    apply (LinearMap.isPositive_linearIsometryEquiv_conj_iff (canonicalGramEuclideanIsometry K b m)).mpr
    exact Matrix.isPositive_toEuclideanLin_iff.mpr (hR X hX).posSemidef
  · rw [computedShapeOnEvent_of_not_mem K b G R hR X hX]
    exact LinearMap.isPositive_id

theorem computedSphericalLawBounds_of_event (b : Basis (Fin d) ℤ (𝓞 K))
    (p : PMF (Matrix (Fin r) (Fin m) (𝓞 K))) (G : Set (Matrix (Fin r) (Fin m) (𝓞 K)))
    (hsurj : ∀ X ∈ G, Function.Surjective X.mulVec) (hr : 0 < r)
    (R : Matrix (Fin r) (Fin m) (𝓞 K) → Matrix (Fin (m * d)) (Fin (m * d)) ℝ)
    (hR : ∀ X ∈ G, (R X).PosDef) {δ σ τ ε w : ℝ} (hw : 0 < w)
    (hprob : ENNReal.ofReal (1 - δ) ≤ p.toOuterMeasure G)
    (hσ : 0 ≤ σ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hε : 0 < ε) (hε1 : ε < 1)
    (herr : ∀ X (hX : X ∈ G),
      ‖isometricTransportMap (canonicalGramEuclideanIsometry K b m) (canonicalGramEuclideanIsometry K b m)
        (Matrix.toEuclideanLin (R X)).toContinuousLinearMap -
        (canonicalGramShapingShape K b X (hsurj X hX) hr w hw).toContinuousLinearMap‖ ≤ σ)
    (hprec : ∀ X ∈ G, 3 * (‖(canonicalEuclideanMatrix K b X).toContinuousLinearMap‖ / w * σ) ≤
      gaussianTargetPrecision (m * d) τ)
    (hsmooth : ∀ X ∈ G, smoothingParameter (canonicalKernel K X) ε *
      ‖(canonicalEuclideanMatrix K b X).toContinuousLinearMap‖ ≤ w) :
    SphericalLawBounds K b p (computedShapeOnEvent K b G R hR) δ (τ + ε / (1 - ε)) w hw := by
  apply sphericalLawBounds_of_event K b p G _ hw (by positivity) hprob
  intro X hX z
  rw [computedShapeOnEvent_of_mem K b G R hR X hX]
  exact (canonicalComputedShape_gaussian K b X (hsurj X hX) hr w hw (R X) (hR X hX)
    hσ hτ hτ1 hε hε1 (herr X hX) (hprec X hX) (hsmooth X hX) z).2

theorem computedSphericalLawBounds_two_events (b : Basis (Fin d) ℤ (𝓞 K))
    (p : PMF (Matrix (Fin r) (Fin m) (𝓞 K))) (G H : Set (Matrix (Fin r) (Fin m) (𝓞 K)))
    (hsurj : ∀ X ∈ G, Function.Surjective X.mulVec) (hr : 0 < r)
    (R : Matrix (Fin r) (Fin m) (𝓞 K) → Matrix (Fin (m * d)) (Fin (m * d)) ℝ)
    (hR : ∀ X ∈ G ∩ H, (R X).PosDef) {δG δH σ τ ε B V w : ℝ} (hw : 0 < w)
    (hG : ENNReal.ofReal (1 - δG) ≤ p.toOuterMeasure G)
    (hH : ENNReal.ofReal (1 - δH) ≤ p.toOuterMeasure H)
    (hσ : 0 ≤ σ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hε : 0 < ε) (hε1 : ε < 1)
    (hB : 0 ≤ B) (hBV : B * V ≤ w)
    (hsmooth : ∀ X ∈ G, smoothingParameter (canonicalKernel K X) ε ≤ B)
    (hnorm : ∀ X ∈ H, ‖(canonicalEuclideanMatrix K b X).toContinuousLinearMap‖ ≤ V)
    (hprec : 3 * (V / w * σ) ≤ gaussianTargetPrecision (m * d) τ)
    (herr : ∀ X (hX : X ∈ G ∩ H),
      ‖isometricTransportMap (canonicalGramEuclideanIsometry K b m) (canonicalGramEuclideanIsometry K b m)
        (Matrix.toEuclideanLin (R X)).toContinuousLinearMap -
        (canonicalGramShapingShape K b X (hsurj X hX.1) hr w hw).toContinuousLinearMap‖ ≤ σ) :
    SphericalLawBounds K b p (computedShapeOnEvent K b (G ∩ H) R hR)
      (δG + δH) (τ + ε / (1 - ε)) w hw := by
  apply computedSphericalLawBounds_of_event K b p (G ∩ H) (fun X hX => hsurj X hX.1)
    hr R hR hw (pmf_intersection_event_mass p G H hG hH) hσ hτ hτ1 hε hε1 herr
  · intro X hX
    exact (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (hnorm X hX.2) hw.le) hσ) (by norm_num)).trans hprec
  · intro X hX
    exact (mul_le_mul_of_nonneg_right (hsmooth X hX.1) (norm_nonneg _)).trans
      ((mul_le_mul_of_nonneg_left (hnorm X hX.2) hB).trans hBV)

end GeometricGaussianLHL
end

end ComputedSphericalEvents

section ComputedSphericalCertificate

/-! # Gaussian laws from the actual numerical algorithm on a proved event

These laws use the rational algorithm's computed matrices, starting from
finite algebraic metric/width data and the integral coefficient table. Preparation, arithmetic cost and accuracy refer to the same execution.
`FiniteSphericalCertificate` instantiates these results with proved available
algebraic representations.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Module NumberField
open scoped MatrixOrder Matrix.Norms.L2Operator

namespace GeometricGaussianLHL

variable (K : Type*) [Field K] [NumberField K] {d r m : ℕ}

def ComputedSphericalCertificate (b : Basis (Fin d) ℤ (𝓞 K))
    (p : PMF (Matrix (Fin r) (Fin m) (𝓞 K))) (_hrm : r ≤ m) (hr : 0 < r)
    (w : ℝ) (hw : 0 < w) (δ ε τ : ℝ) (t : ℕ) : Prop :=
  ∃ G : Set (Matrix (Fin r) (Fin m) (𝓞 K)),
    ∃ hsurj : ∀ X ∈ G, Function.Surjective X.mulVec,
    ENNReal.ofReal (1 - δ) ≤ p.toOuterMeasure G ∧
    (∃ C e : ℕ, ∀ I : Matrix (Fin r) (Fin m) (𝓞 K) → CanonicalAlgebraicData d r m,
      (∀ X, (I X).toInput.ValidFor K b X w) →
      ∃ hR : ∀ X ∈ G, ((rationalMatrixOfData ((I X).execution t).value).map (Rat.castHom ℝ)).PosDef,
        (∀ X, X ∈ G →
          ((I X).execution t).steps ≤ C * ((I X).inputLength + t + 1) ^ e ∧
          (encodeRationalMatrixData ((I X).execution t).value).length ≤ C * ((I X).inputLength + t + 1) ^ e) ∧
        (∀ X (hX : X ∈ G),
          ‖isometricTransportMap (canonicalGramEuclideanIsometry K b m) (canonicalGramEuclideanIsometry K b m)
            (Matrix.toEuclideanLin ((rationalMatrixOfData ((I X).execution t).value).map (Rat.castHom ℝ))).toContinuousLinearMap -
            (canonicalGramShapingShape K b X (hsurj X hX) hr w hw).toContinuousLinearMap‖ ≤
              1 / (2 : ℝ) ^ t) ∧
        SphericalLawBounds K b p
          (computedShapeOnEvent K b G (fun X => (rationalMatrixOfData ((I X).execution t).value).map (Rat.castHom ℝ)) hR)
          δ (τ + ε / (1 - ε)) w hw)

theorem computedSphericalCertificate_of_event (b : Basis (Fin d) ℤ (𝓞 K))
    (p : PMF (Matrix (Fin r) (Fin m) (𝓞 K))) (G : Set (Matrix (Fin r) (Fin m) (𝓞 K)))
    (hsurj : ∀ X ∈ G, Function.Surjective X.mulVec) (hrm : r ≤ m) (hr : 0 < r)
    {δ τ ε B V w : ℝ} (t : ℕ) (hw : 0 < w)
    (hprob : ENNReal.ofReal (1 - δ) ≤ p.toOuterMeasure G)
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hε : 0 < ε) (hε1 : ε < 1)
    (hB : 0 ≤ B) (hBV : B * V ≤ w)
    (hsmooth : ∀ X ∈ G, smoothingParameter (canonicalKernel K X) ε ≤ B)
    (hnorm : ∀ X ∈ G, ‖(canonicalEuclideanMatrix K b X).toContinuousLinearMap‖ ≤ V)
    (hprec : 3 * (V / w * (1 / (2 : ℝ) ^ t)) ≤ gaussianTargetPrecision (m * d) τ) :
    ComputedSphericalCertificate K b p hrm hr w hw δ ε τ t := by
  have hprecision : ∀ X ∈ G,
      3 * (‖(canonicalEuclideanMatrix K b X).toContinuousLinearMap‖ / w *
        (1 / (2 : ℝ) ^ t)) ≤ gaussianTargetPrecision (m * d) τ := by
    intro X hX
    exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (hnorm X hX) hw.le) (by positivity)) (by norm_num)).trans hprec
  have hwidth : ∀ X ∈ G, smoothingParameter (canonicalKernel K X) ε *
      ‖(canonicalEuclideanMatrix K b X).toContinuousLinearMap‖ ≤ w := by
    intro X hX
    exact (mul_le_mul_of_nonneg_right (hsmooth X hX) (norm_nonneg _)).trans
      ((mul_le_mul_of_nonneg_left (hnorm X hX) hB).trans hBV)
  obtain ⟨C, e, hcost⟩ := canonicalFinite_computational_certificate
  refine ⟨G, hsurj, hprob, C, e, ?_⟩
  intro I hI
  have hrun := fun X hX => (I X).execution_accuracy (hI X) hrm (hsurj X hX) hr hw t
  let hR : ∀ X ∈ G, ((rationalMatrixOfData ((I X).execution t).value).map (Rat.castHom ℝ)).PosDef := fun X hX => (hrun X hX).1
  refine ⟨hR, ?_, fun X hX => (hrun X hX).2, ?_⟩
  · intro X hX
    have h := hcost K d r m b X (I X) w (hI X) hrm (hsurj X hX) hr hw t
    exact ⟨h.1, h.2.1⟩
  · exact computedSphericalLawBounds_of_event K b p G hsurj hr _ hR hw hprob
      (by positivity) hτ hτ1 hε hε1 (fun X hX => (hrun X hX).2) hprecision hwidth

theorem computedSphericalCertificate_of_spectral_event (b : Basis (Fin d) ℤ (𝓞 K))
    (G : Set (Matrix (Fin r) (Fin m) (𝓞 K)))
    (hsurj : ∀ X ∈ G, Function.Surjective X.mulVec) (hrm : r ≤ m) (hr : 0 < r)
    {s δG δsp τ ε B w : ℝ} (t : ℕ) (hs : 0 < s) (hw : 0 < w)
    (hG : ENNReal.ofReal (1 - δG) ≤ (numberFieldMatrixLaw K b r m s hs.ne').toOuterMeasure G)
    (hsp : 0 < δsp) (hsp1 : δsp < 1) (hlog : Real.log (2 * d / δsp) ≤ m)
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hε : 0 < ε) (hε1 : ε < 1)
    (hB : 0 ≤ B) (hBw : B * (4 * s * Real.sqrt m) ≤ w)
    (hsmooth : ∀ X ∈ G, smoothingParameter (canonicalKernel K X) ε ≤ B)
    (hprec : 3 * ((4 * s * Real.sqrt m) / w * (1 / (2 : ℝ) ^ t)) ≤
      gaussianTargetPrecision (m * d) τ) :
    ComputedSphericalCertificate K b (numberFieldMatrixLaw K b r m s hs.ne') hrm hr w hw
      (δG + δsp) ε τ t := by
  let H := {X : Matrix (Fin r) (Fin m) (𝓞 K) |
    ‖(canonicalEuclideanMatrix K b X).toContinuousLinearMap‖ ≤ 4 * s * Real.sqrt m}
  have hH := numberField_spherical_spectral_four K b hs hsp hsp1 hrm hlog
  exact computedSphericalCertificate_of_event K b _ (G ∩ H) (fun X hX => hsurj X hX.1) hrm hr t hw
    (pmf_intersection_event_mass _ G H hG hH) hτ hτ1 hε hε1 hB hBw
    (fun X hX => hsmooth X hX.1) (fun _ hX => hX.2) hprec

end GeometricGaussianLHL
end

end ComputedSphericalCertificate

section ComputedSphericalParameters

/-!
## Four parameter specializations of the computed spherical certificate

These results use the actual finite-input execution with proved canonical
accuracy, Gaussian-law bounds and polynomial arithmetic cost. The cost includes
input preparation and is measured in the original encoding length plus precision.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Module NumberField

namespace GeometricGaussianLHL

variable (K : Type*) [Field K] [NumberField K] {d r m : ℕ}

theorem numberField_polynomial_computed_spherical (b : Basis (Fin d) ℤ (𝓞 K))
    (i : Fin d) (hidentity : b i = 1) (hr : 1 ≤ r) (hmr : r < m)
    {ell s τ : ℝ} (hell : 1 ≤ ell) (hs : 0 < s) (t : ℕ)
    (hwidth : 8 * Real.sqrt (r * d) ≤ s / basisAlpha K b)
    (hbudget : ((r * d : ℕ) : ℝ) * Real.log (numberFieldPolynomialScale K b r m s ell) +
      2 * Real.log (1 / realSecurityError (ell + 4)) ≤ (m : ℝ) * Real.log (8 / 7))
    (hτ : 0 < τ) (hτδ : τ ≤ realSecurityError (ell + 4))
    (hprec : 3 * (numberFieldPolynomialOperatorBound K b r m s ell /
      numberFieldPolynomialSphericalWidth K b r m s ell * (1 / (2 : ℝ) ^ t)) ≤
        gaussianTargetPrecision (m * d) τ) :
    let w := numberFieldPolynomialSphericalWidth K b r m s ell
    ∃ hw : 0 < w,
      ComputedSphericalCertificate K b (numberFieldMatrixLaw K b r m s hs.ne') hmr.le hr w hw
        (3 * realSecurityError (ell + 4)) (2 * realSecurityError (ell + 4)) τ t ∧
      3 * realSecurityError (ell + 4) + (τ +
        2 * realSecurityError (ell + 4) / (1 - 2 * realSecurityError (ell + 4))) < realSecurityError ell := by
  obtain ⟨hB, _, hw⟩ := numberFieldPolynomialSpherical_parameters_pos K b i hidentity
    hr (by omega : 1 ≤ m) hell hs
  have hδ := realSecurityError_pos (ell + 4)
  have hδsmall := real_polynomial_failureBudget_le hell
  obtain ⟨G, hprob, hgood⟩ := numberField_polynomial_spherical_event K b i hidentity
    hr hmr hell hs hwidth hbudget
  refine ⟨hw, ?_, ?_⟩
  · exact computedSphericalCertificate_of_event K b _ G (fun X hX => (hgood X hX).1)
      hmr.le hr t hw hprob hτ (by linarith) (by positivity) (by linarith) hB.le le_rfl
      (fun X hX => (hgood X hX).2.1) (fun X hX => (hgood X hX).2.2) hprec
  · linarith [polynomial_spectral_joint_error_lt hell]

theorem numberField_polynomial_computed_spectral (b : Basis (Fin d) ℤ (𝓞 K))
    (i : Fin d) (hidentity : b i = 1) (hr : 1 ≤ r) (hmr : r < m)
    {ell s w τ : ℝ} (hell : 1 ≤ ell) (hs : 0 < s) (t : ℕ)
    (hwidth : 8 * Real.sqrt (r * d) ≤ s / basisAlpha K b)
    (hbudget : ((r * d : ℕ) : ℝ) * Real.log (numberFieldPolynomialScale K b r m s ell) +
      2 * Real.log (1 / realSecurityError (ell + 4)) ≤ (m : ℝ) * Real.log (8 / 7))
    (hspectral : lowerSpectralColumnConstant *
      ((r : ℝ) + Real.log (2 * d / realSecurityError (ell + 4))) ≤ m)
    (hw : numberFieldPolynomialSmoothingBound K b r m ell * (4 * s * Real.sqrt m) ≤ w)
    (hτ : 0 < τ) (hτδ : τ ≤ realSecurityError (ell + 4))
    (hprec : 3 * ((4 * s * Real.sqrt m) / w * (1 / (2 : ℝ) ^ t)) ≤
      gaussianTargetPrecision (m * d) τ) :
    ∃ hwpos : 0 < w,
      ComputedSphericalCertificate K b (numberFieldMatrixLaw K b r m s hs.ne') hmr.le hr w hwpos
        (4 * realSecurityError (ell + 4)) (2 * realSecurityError (ell + 4)) τ t ∧
      4 * realSecurityError (ell + 4) + (τ +
        2 * realSecurityError (ell + 4) / (1 - 2 * realSecurityError (ell + 4))) < realSecurityError ell := by
  have hd := integralBasis_dimension_pos K b
  have hm : (0 : ℝ) < m := Nat.cast_pos.mpr (by omega)
  have hB := (numberFieldPolynomialSpherical_parameters_pos K b (r := r) (m := m)
    i hidentity hr (by omega) hell hs).1
  have hwpos : 0 < w := (mul_pos hB (by positivity : 0 < 4 * s * Real.sqrt m)).trans_le hw
  have hδ := realSecurityError_pos (ell + 4)
  have hδsmall := real_polynomial_failureBudget_le hell
  obtain ⟨G, hprob, hgood⟩ := numberField_polynomial_spherical_event K b i hidentity
    hr hmr hell hs hwidth hbudget
  refine ⟨hwpos, ?_, polynomial_computed_spectral_error_lt hell hτδ⟩
  have h := computedSphericalCertificate_of_spectral_event K b G (fun X hX => (hgood X hX).1)
    hmr.le hr t hs hwpos hprob hδ (by linarith)
    (spectral_columns_log_condition hd hδ (by linarith) hspectral)
    hτ (by linarith) (by positivity) (by linarith) hB.le hw (fun X hX => (hgood X hX).2.1) hprec
  convert h using 1
  ring

variable {k : ℕ} [IsCyclotomicExtension {2 ^ (k + 1)} ℚ K] {ζ : K}

theorem numberField_constantWidth_computed_spherical (hζ : IsPrimitiveRoot ζ (2 ^ (k + 1)))
    (hr : 1 ≤ r) (hmr : r < m) {ell s τ : ℝ} (hell : 1 ≤ ell) (hs : 0 < s) (t : ℕ)
    (hwidth : Real.sqrt (2 ^ (k + 1)).totient ≤ s)
    (hbudget : ((r * (2 ^ (k + 1)).totient : ℕ) : ℝ) *
      Real.log (powerTwoConstantScale (2 ^ (k + 1)).totient r m s ell) +
      2 * Real.log (1 / realSecurityError (ell + 6)) ≤ (m : ℝ) * Real.log (50 / 49))
    (hτ : 0 < τ) (hτδ : τ ≤ realSecurityError (ell + 6))
    (hprec : 3 * (powerTwoConstantOperatorBound (2 ^ (k + 1)).totient r m s ell /
      powerTwoConstantSphericalWidth (2 ^ (k + 1)).totient r m s ell * (1 / (2 : ℝ) ^ t)) ≤
        gaussianTargetPrecision (m * (2 ^ (k + 1)).totient) τ) :
    let b := cyclotomicIntegralBasis K hζ
    let w := powerTwoConstantSphericalWidth (2 ^ (k + 1)).totient r m s ell
    ∃ hw : 0 < w,
      ComputedSphericalCertificate K b (numberFieldMatrixLaw K b r m s hs.ne') hmr.le hr w hw
        (3 * realSecurityError (ell + 6)) (2 * realSecurityError (ell + 6)) τ t ∧
      3 * realSecurityError (ell + 6) + (τ +
        2 * realSecurityError (ell + 6) / (1 - 2 * realSecurityError (ell + 6))) < realSecurityError ell := by
  let b := cyclotomicIntegralBasis K hζ
  have hd := integralBasis_dimension_pos K b
  obtain ⟨hB, _, hw⟩ := powerTwoConstantSpherical_parameters_pos (r := r) (m := m)
    hd hr (by omega) hell hs
  have hδ := realSecurityError_pos (ell + 6)
  have hδsmall := real_constant_failureBudget_le hell
  obtain ⟨G, hprob, hgood⟩ := numberField_constantWidth_spherical_event K hζ
    hr hmr hell hs hwidth hbudget
  refine ⟨hw, ?_, ?_⟩
  · exact computedSphericalCertificate_of_event K b _ G (fun X hX => (hgood X hX).1)
      hmr.le hr t hw hprob hτ (by linarith) (by positivity) (by linarith) hB.le le_rfl
      (fun X hX => (hgood X hX).2.1) (fun X hX => (hgood X hX).2.2) hprec
  · linarith [constant_spectral_joint_error_lt hell]

theorem numberField_constantWidth_computed_spectral (hζ : IsPrimitiveRoot ζ (2 ^ (k + 1)))
    (hr : 1 ≤ r) (hmr : r < m) {ell s w τ : ℝ} (hell : 1 ≤ ell) (hs : 0 < s) (t : ℕ)
    (hwidth : Real.sqrt (2 ^ (k + 1)).totient ≤ s)
    (hbudget : ((r * (2 ^ (k + 1)).totient : ℕ) : ℝ) *
      Real.log (powerTwoConstantScale (2 ^ (k + 1)).totient r m s ell) +
      2 * Real.log (1 / realSecurityError (ell + 6)) ≤ (m : ℝ) * Real.log (50 / 49))
    (hspectral : lowerSpectralColumnConstant *
      ((r : ℝ) + Real.log (2 * (2 ^ (k + 1)).totient / realSecurityError (ell + 6))) ≤ m)
    (hw : powerTwoConstantSmoothingBound (2 ^ (k + 1)).totient r m ell * (4 * s * Real.sqrt m) ≤ w)
    (hτ : 0 < τ) (hτδ : τ ≤ realSecurityError (ell + 6))
    (hprec : 3 * ((4 * s * Real.sqrt m) / w * (1 / (2 : ℝ) ^ t)) ≤
      gaussianTargetPrecision (m * (2 ^ (k + 1)).totient) τ) :
    let b := cyclotomicIntegralBasis K hζ
    ∃ hwpos : 0 < w,
      ComputedSphericalCertificate K b (numberFieldMatrixLaw K b r m s hs.ne') hmr.le hr w hwpos
        (4 * realSecurityError (ell + 6)) (2 * realSecurityError (ell + 6)) τ t ∧
      4 * realSecurityError (ell + 6) + (τ +
        2 * realSecurityError (ell + 6) / (1 - 2 * realSecurityError (ell + 6))) < realSecurityError ell := by
  let b := cyclotomicIntegralBasis K hζ
  have hd := integralBasis_dimension_pos K b
  have hm : (0 : ℝ) < m := Nat.cast_pos.mpr (by omega)
  have hB := (powerTwoConstantSpherical_parameters_pos (r := r) (m := m)
    hd hr (by omega) hell hs).1
  have hwpos : 0 < w := (mul_pos hB (by positivity : 0 < 4 * s * Real.sqrt m)).trans_le hw
  have hδ := realSecurityError_pos (ell + 6)
  have hδsmall := real_constant_failureBudget_le hell
  obtain ⟨G, hprob, hgood⟩ := numberField_constantWidth_spherical_event K hζ
    hr hmr hell hs hwidth hbudget
  refine ⟨hwpos, ?_, constant_computed_spectral_error_lt hell hτδ⟩
  have h := computedSphericalCertificate_of_spectral_event K b G (fun X hX => (hgood X hX).1)
    hmr.le hr t hs hwpos hprob hδ (by linarith)
    (spectral_columns_log_condition hd hδ (by linarith) hspectral)
    hτ (by linarith) (by positivity) (by linarith) hB.le hw (fun X hX => (hgood X hX).2.1) hprec
  convert h using 1
  ring

end GeometricGaussianLHL
end

end ComputedSphericalParameters

section FiniteSphericalCertificate

/-!
## Gaussian certificates with an available finite input representation

The certificate exhibits a valid input family and uses its actual execution
in the cost, accuracy and Gaussian-law conclusions. It is obtained by
instantiating the uniform computed certificate with proved available encodings.
-/
noncomputable section
open Module NumberField
open scoped MatrixOrder Matrix.Norms.L2Operator
namespace GeometricGaussianLHL

variable (K : Type*) [Field K] [NumberField K] {d r m : ℕ}

def FiniteSphericalCertificate (b : Basis (Fin d) ℤ (𝓞 K))
    (p : PMF (Matrix (Fin r) (Fin m) (𝓞 K))) (_hrm : r ≤ m) (hr : 0 < r)
    (w : ℝ) (hw : 0 < w) (δ ε τ : ℝ) (t : ℕ) : Prop :=
  ∃ I : Matrix (Fin r) (Fin m) (𝓞 K) → CanonicalAlgebraicData d r m,
    (∀ X, (I X).toInput.ValidFor K b X w) ∧
    ∃ G : Set (Matrix (Fin r) (Fin m) (𝓞 K)),
    ∃ hsurj : ∀ X ∈ G, Function.Surjective X.mulVec,
    ENNReal.ofReal (1 - δ) ≤ p.toOuterMeasure G ∧
    ∃ C e : ℕ,
    ∃ hR : ∀ X ∈ G, ((rationalMatrixOfData ((I X).execution t).value).map (Rat.castHom ℝ)).PosDef,
      (∀ X, X ∈ G →
        ((I X).execution t).steps ≤ C * ((I X).inputLength + t + 1) ^ e ∧
        (encodeRationalMatrixData ((I X).execution t).value).length ≤ C * ((I X).inputLength + t + 1) ^ e) ∧
      (∀ X (hX : X ∈ G),
        ‖isometricTransportMap (canonicalGramEuclideanIsometry K b m) (canonicalGramEuclideanIsometry K b m)
          (Matrix.toEuclideanLin ((rationalMatrixOfData ((I X).execution t).value).map (Rat.castHom ℝ))).toContinuousLinearMap -
          (canonicalGramShapingShape K b X (hsurj X hX) hr w hw).toContinuousLinearMap‖ ≤ 1 / (2 : ℝ) ^ t) ∧
      SphericalLawBounds K b p
        (computedShapeOnEvent K b G (fun X => (rationalMatrixOfData ((I X).execution t).value).map (Rat.castHom ℝ)) hR)
        δ (τ + ε / (1 - ε)) w hw

theorem ComputedSphericalCertificate.realize {b : Basis (Fin d) ℤ (𝓞 K)}
    {p : PMF (Matrix (Fin r) (Fin m) (𝓞 K))} {hrm : r ≤ m} {hr : 0 < r}
    {w : ℝ} {hw : 0 < w} {δ ε τ : ℝ} {t : ℕ}
    (h : ComputedSphericalCertificate K b p hrm hr w hw δ ε τ t) (hwalg : IsAlgebraic ℚ w) :
    FiniteSphericalCertificate K b p hrm hr w hw δ ε τ t := by
  obtain ⟨G, hsurj, hprob, C, e, hrun⟩ := h
  obtain ⟨I, hI⟩ := canonicalAlgebraicFamily_exists K b hwalg
  obtain ⟨hR, hcost, herr, hlaw⟩ := hrun I hI
  exact ⟨I, hI, G, hsurj, hprob, C, e, hR, hcost, herr, hlaw⟩

end GeometricGaussianLHL
end

end FiniteSphericalCertificate

section FiniteSphericalParameters

/-!
## Four Gaussian regimes with available finite inputs

Each theorem exhibits a rational output width between the analytic threshold
and twice that threshold. Its finite input representation, complete execution,
polynomial cost, numerical accuracy and Gaussian laws are therefore available
under the displayed parameter assumptions.
-/
noncomputable section
open Module NumberField
namespace GeometricGaussianLHL

theorem gaussianPrecision_mono_width {V u w ε : ℝ} (hV : 0 ≤ V) (hu : 0 < u) (huw : u ≤ w)
    (t : ℕ) (h : 3 * (V / u * (1 / (2 : ℝ) ^ t)) ≤ ε) :
    3 * (V / w * (1 / (2 : ℝ) ^ t)) ≤ ε :=
  (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_left hV hu huw) (by positivity)) (by norm_num)).trans h

variable (K : Type*) [Field K] [NumberField K] {d r m : ℕ}

theorem numberField_polynomial_finite_spherical (b : Basis (Fin d) ℤ (𝓞 K))
    (i : Fin d) (hidentity : b i = 1) (hr : 1 ≤ r) (hmr : r < m)
    {ell s τ : ℝ} (hell : 1 ≤ ell) (hs : 0 < s) (t : ℕ)
    (hwidth : 8 * Real.sqrt (r * d) ≤ s / basisAlpha K b)
    (hbudget : ((r * d : ℕ) : ℝ) * Real.log (numberFieldPolynomialScale K b r m s ell) +
      2 * Real.log (1 / realSecurityError (ell + 4)) ≤ (m : ℝ) * Real.log (8 / 7))
    (hτ : 0 < τ) (hτδ : τ ≤ realSecurityError (ell + 4))
    (hprec : 3 * (numberFieldPolynomialOperatorBound K b r m s ell /
      numberFieldPolynomialSphericalWidth K b r m s ell * (1 / (2 : ℝ) ^ t)) ≤
        gaussianTargetPrecision (m * d) τ) :
    ∃ w : ℚ, numberFieldPolynomialSphericalWidth K b r m s ell ≤ (w : ℝ) ∧
      (w : ℝ) ≤ 2 * numberFieldPolynomialSphericalWidth K b r m s ell ∧
      ∃ hw : 0 < (w : ℝ),
      FiniteSphericalCertificate K b (numberFieldMatrixLaw K b r m s hs.ne') hmr.le hr w hw
        (3 * realSecurityError (ell + 4)) (2 * realSecurityError (ell + 4)) τ t ∧
      3 * realSecurityError (ell + 4) + (τ +
        2 * realSecurityError (ell + 4) / (1 - 2 * realSecurityError (ell + 4))) < realSecurityError ell := by
  obtain ⟨hB, hV, hW⟩ := numberFieldPolynomialSpherical_parameters_pos K b i hidentity
    hr (by omega : 1 ≤ m) hell hs
  obtain ⟨w, hw, hWw, hwW⟩ := exists_rational_width_between hW
  have hwpos : 0 < (w : ℝ) := Rat.cast_pos.mpr hw
  have hp := gaussianPrecision_mono_width hV.le hW hWw t hprec
  have hδ := realSecurityError_pos (ell + 4)
  have hδsmall := real_polynomial_failureBudget_le hell
  obtain ⟨G, hprob, hgood⟩ := numberField_polynomial_spherical_event K b i hidentity
    hr hmr hell hs hwidth hbudget
  refine ⟨w, hWw, hwW, hwpos, ?_, ?_⟩
  · apply ComputedSphericalCertificate.realize K ?_ (rationalWidth_isAlgebraic w)
    exact computedSphericalCertificate_of_event K b _ G (fun X hX => (hgood X hX).1)
      hmr.le hr t hwpos hprob hτ (by linarith) (by positivity) (by linarith) hB.le hWw
      (fun X hX => (hgood X hX).2.1) (fun X hX => (hgood X hX).2.2) hp
  · linarith [polynomial_spectral_joint_error_lt hell]

theorem numberField_polynomial_finite_spectral (b : Basis (Fin d) ℤ (𝓞 K))
    (i : Fin d) (hidentity : b i = 1) (hr : 1 ≤ r) (hmr : r < m)
    {ell s τ : ℝ} (hell : 1 ≤ ell) (hs : 0 < s) (t : ℕ)
    (hwidth : 8 * Real.sqrt (r * d) ≤ s / basisAlpha K b)
    (hbudget : ((r * d : ℕ) : ℝ) * Real.log (numberFieldPolynomialScale K b r m s ell) +
      2 * Real.log (1 / realSecurityError (ell + 4)) ≤ (m : ℝ) * Real.log (8 / 7))
    (hspectral : lowerSpectralColumnConstant *
      ((r : ℝ) + Real.log (2 * d / realSecurityError (ell + 4))) ≤ m)
    (hτ : 0 < τ) (hτδ : τ ≤ realSecurityError (ell + 4))
    (hprec : 3 * ((4 * s * Real.sqrt m) /
      (numberFieldPolynomialSmoothingBound K b r m ell * (4 * s * Real.sqrt m)) * (1 / (2 : ℝ) ^ t)) ≤
        gaussianTargetPrecision (m * d) τ) :
    ∃ w : ℚ, numberFieldPolynomialSmoothingBound K b r m ell * (4 * s * Real.sqrt m) ≤ (w : ℝ) ∧
      (w : ℝ) ≤ 2 * (numberFieldPolynomialSmoothingBound K b r m ell * (4 * s * Real.sqrt m)) ∧
      ∃ hw : 0 < (w : ℝ),
      FiniteSphericalCertificate K b (numberFieldMatrixLaw K b r m s hs.ne') hmr.le hr w hw
        (4 * realSecurityError (ell + 4)) (2 * realSecurityError (ell + 4)) τ t ∧
      4 * realSecurityError (ell + 4) + (τ +
        2 * realSecurityError (ell + 4) / (1 - 2 * realSecurityError (ell + 4))) < realSecurityError ell := by
  have hm : (0 : ℝ) < m := Nat.cast_pos.mpr (by omega)
  have hB := (numberFieldPolynomialSpherical_parameters_pos K b (r := r) (m := m)
    i hidentity hr (by omega) hell hs).1
  have hV : 0 < 4 * s * Real.sqrt m := by positivity
  have hW := mul_pos hB hV
  obtain ⟨w, _, hWw, hwW⟩ := exists_rational_width_between hW
  have hp := gaussianPrecision_mono_width hV.le hW hWw t hprec
  obtain ⟨hw, hcert, herr⟩ := numberField_polynomial_computed_spectral K b i hidentity hr hmr
    hell hs t hwidth hbudget hspectral hWw hτ hτδ hp
  exact ⟨w, hWw, hwW, hw, hcert.realize K (rationalWidth_isAlgebraic w), herr⟩

variable {k : ℕ} [IsCyclotomicExtension {2 ^ (k + 1)} ℚ K] {ζ : K}

theorem numberField_constantWidth_finite_spherical (hζ : IsPrimitiveRoot ζ (2 ^ (k + 1)))
    (hr : 1 ≤ r) (hmr : r < m) {ell s τ : ℝ} (hell : 1 ≤ ell) (hs : 0 < s) (t : ℕ)
    (hwidth : Real.sqrt (2 ^ (k + 1)).totient ≤ s)
    (hbudget : ((r * (2 ^ (k + 1)).totient : ℕ) : ℝ) *
      Real.log (powerTwoConstantScale (2 ^ (k + 1)).totient r m s ell) +
      2 * Real.log (1 / realSecurityError (ell + 6)) ≤ (m : ℝ) * Real.log (50 / 49))
    (hτ : 0 < τ) (hτδ : τ ≤ realSecurityError (ell + 6))
    (hprec : 3 * (powerTwoConstantOperatorBound (2 ^ (k + 1)).totient r m s ell /
      powerTwoConstantSphericalWidth (2 ^ (k + 1)).totient r m s ell * (1 / (2 : ℝ) ^ t)) ≤
        gaussianTargetPrecision (m * (2 ^ (k + 1)).totient) τ) :
    ∃ w : ℚ, powerTwoConstantSphericalWidth (2 ^ (k + 1)).totient r m s ell ≤ (w : ℝ) ∧
      (w : ℝ) ≤ 2 * powerTwoConstantSphericalWidth (2 ^ (k + 1)).totient r m s ell ∧
      ∃ hw : 0 < (w : ℝ),
      FiniteSphericalCertificate K (cyclotomicIntegralBasis K hζ)
        (numberFieldMatrixLaw K (cyclotomicIntegralBasis K hζ) r m s hs.ne') hmr.le hr w hw
        (3 * realSecurityError (ell + 6)) (2 * realSecurityError (ell + 6)) τ t ∧
      3 * realSecurityError (ell + 6) + (τ +
        2 * realSecurityError (ell + 6) / (1 - 2 * realSecurityError (ell + 6))) < realSecurityError ell := by
  let b := cyclotomicIntegralBasis K hζ
  have hd := integralBasis_dimension_pos K b
  obtain ⟨hB, hV, hW⟩ := powerTwoConstantSpherical_parameters_pos (r := r) (m := m)
    hd hr (by omega) hell hs
  obtain ⟨w, hw, hWw, hwW⟩ := exists_rational_width_between hW
  have hwpos : 0 < (w : ℝ) := Rat.cast_pos.mpr hw
  have hp := gaussianPrecision_mono_width hV.le hW hWw t hprec
  have hδ := realSecurityError_pos (ell + 6)
  have hδsmall := real_constant_failureBudget_le hell
  obtain ⟨G, hprob, hgood⟩ := numberField_constantWidth_spherical_event K hζ
    hr hmr hell hs hwidth hbudget
  refine ⟨w, hWw, hwW, hwpos, ?_, ?_⟩
  · apply ComputedSphericalCertificate.realize K ?_ (rationalWidth_isAlgebraic w)
    exact computedSphericalCertificate_of_event K b _ G (fun X hX => (hgood X hX).1)
      hmr.le hr t hwpos hprob hτ (by linarith) (by positivity) (by linarith) hB.le hWw
      (fun X hX => (hgood X hX).2.1) (fun X hX => (hgood X hX).2.2) hp
  · linarith [constant_spectral_joint_error_lt hell]

theorem numberField_constantWidth_finite_spectral (hζ : IsPrimitiveRoot ζ (2 ^ (k + 1)))
    (hr : 1 ≤ r) (hmr : r < m) {ell s τ : ℝ} (hell : 1 ≤ ell) (hs : 0 < s) (t : ℕ)
    (hwidth : Real.sqrt (2 ^ (k + 1)).totient ≤ s)
    (hbudget : ((r * (2 ^ (k + 1)).totient : ℕ) : ℝ) *
      Real.log (powerTwoConstantScale (2 ^ (k + 1)).totient r m s ell) +
      2 * Real.log (1 / realSecurityError (ell + 6)) ≤ (m : ℝ) * Real.log (50 / 49))
    (hspectral : lowerSpectralColumnConstant *
      ((r : ℝ) + Real.log (2 * (2 ^ (k + 1)).totient / realSecurityError (ell + 6))) ≤ m)
    (hτ : 0 < τ) (hτδ : τ ≤ realSecurityError (ell + 6))
    (hprec : 3 * ((4 * s * Real.sqrt m) /
      (powerTwoConstantSmoothingBound (2 ^ (k + 1)).totient r m ell * (4 * s * Real.sqrt m)) * (1 / (2 : ℝ) ^ t)) ≤
        gaussianTargetPrecision (m * (2 ^ (k + 1)).totient) τ) :
    ∃ w : ℚ, powerTwoConstantSmoothingBound (2 ^ (k + 1)).totient r m ell * (4 * s * Real.sqrt m) ≤ (w : ℝ) ∧
      (w : ℝ) ≤ 2 * (powerTwoConstantSmoothingBound (2 ^ (k + 1)).totient r m ell * (4 * s * Real.sqrt m)) ∧
      ∃ hw : 0 < (w : ℝ),
      FiniteSphericalCertificate K (cyclotomicIntegralBasis K hζ)
        (numberFieldMatrixLaw K (cyclotomicIntegralBasis K hζ) r m s hs.ne') hmr.le hr w hw
        (4 * realSecurityError (ell + 6)) (2 * realSecurityError (ell + 6)) τ t ∧
      4 * realSecurityError (ell + 6) + (τ +
        2 * realSecurityError (ell + 6) / (1 - 2 * realSecurityError (ell + 6))) < realSecurityError ell := by
  let b := cyclotomicIntegralBasis K hζ
  have hd := integralBasis_dimension_pos K b
  have hm : (0 : ℝ) < m := Nat.cast_pos.mpr (by omega)
  have hB := (powerTwoConstantSpherical_parameters_pos (r := r) (m := m)
    hd hr (by omega) hell hs).1
  have hV : 0 < 4 * s * Real.sqrt m := by positivity
  have hW := mul_pos hB hV
  obtain ⟨w, _, hWw, hwW⟩ := exists_rational_width_between hW
  have hp := gaussianPrecision_mono_width hV.le hW hWw t hprec
  obtain ⟨hw, hcert, herr⟩ := numberField_constantWidth_computed_spectral K hζ hr hmr
    hell hs t hwidth hbudget hspectral hWw hτ hτδ hp
  exact ⟨w, hWw, hwW, hw, hcert.realize K (rationalWidth_isAlgebraic w), herr⟩

end GeometricGaussianLHL
end

end FiniteSphericalParameters
