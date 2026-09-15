import GeometricGaussianLHL.ConstantWidth

/-!
# Geometric Gaussian leftover-hash theorems

This module collects the following proof sections, in dependency order.
- Polynomial-width geometric Gaussian leftover hashing (`NumberFieldLHL`).
- Reusing a Gaussian matrix for independent inputs (`NumberFieldRepeatedLHL`).
- Constant-width geometric Gaussian leftover hashing (`NumberFieldConstantLHL`).
-/

section NumberFieldLHL

/-!
## Polynomial-width geometric Gaussian leftover hashing

The finite and growing-rank polynomial-width cases of Corollary 5.1.
The matrix marginal is the actual independent number-field Gaussian law;
the conditional target is total and uses the actual image square root.
The constant-width specialization depends on the still separate
constant-width geometric theorem and is not asserted here.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Module NumberField

namespace GeometricGaussianLHL

variable (K : Type*) [Field K] [NumberField K] {d r m : ℕ}

theorem numberField_polynomial_lhl (b : Basis (Fin d) ℤ (𝓞 K))
    (i : Fin d) (hidentity : b i = 1) (hr : 1 ≤ r) (hmr : r < m)
    {ell s : ℝ} (hell : 1 ≤ ell) (hs : 0 < s)
    (hwidth : 8 * Real.sqrt (r * d) ≤ s / basisAlpha K b)
    (hbudget : ((r * d : ℕ) : ℝ) * Real.log (numberFieldPolynomialScale K b r m s ell) +
      2 * Real.log (1 / realSecurityError (ell + 4)) ≤ (m : ℝ) * Real.log (8 / 7))
    (S : Euclidean (m * d) ≃L[ℝ] Euclidean (m * d))
    (hS : basisAlpha K b * polynomialThetaWidth (basisKappa K b) (basisMu K b)
      (polynomialColumnHeight (r * d) m ell) ≤ shapeMinimumStretch S)
    (c : Matrix (Fin r) (Fin m) (𝓞 K) → Fin m → 𝓞 K) :
    let p := numberFieldMatrixLaw K b r m s hs.ne'
    let D := discreteTotalVariation
      (jointPMF p (fun X => (numberFieldEllipsoidalGaussian K b m S (c X)).map X.mulVec))
      (jointPMF p (fun X => numberFieldConditionalTarget K b X S (c X)))
    D ≤ jointErrorBound (realSecurityError (ell + 4)) 1 ∧ D < realSecurityError ell := by
  dsimp only
  obtain ⟨G, hprob, hgood⟩ := numberField_polynomial_certificate K b i hidentity hr hmr
    hell hs hwidth hbudget
  have hδ := real_polynomial_failureBudget_le hell
  have hb := numberField_gaussian_joint_errorBudget K b
    (numberFieldMatrixLaw K b r m s hs.ne') (fun _ => S) c G hprob
    (realSecurityError_pos (ell + 4)) (by linarith) (fun X hX =>
      ⟨(hgood X hX).1, (hgood X hX).2.2.1.trans hS⟩)
  exact ⟨hb, hb.trans_lt (real_polynomial_jointError_lt hell)⟩

/-- The `C √ell` source-width prescription in the growing-rank family,
with constants independent of the real security parameter. -/
theorem numberField_polynomial_asymptotic_lhl (b : Basis (Fin d) ℤ (𝓞 K))
    (i : Fin d) (hidentity : b i = 1) {p : ℝ} (hp : 1 / 2 ≤ p) :
    ∃ cX cm C ell₀ : ℝ, 0 < cX ∧ 0 < cm ∧ 0 < C ∧
      ∀ ell : ℝ, ell₀ ≤ ell →
        let r := polynomialFamilyRows d ell
        let R := r * d
        let s := cX * (R : ℝ) ^ p
        let m := polynomialFamilyColumns cm R
        r < m ∧ ∃ hs : 0 < s,
          ∀ S : Euclidean (m * d) ≃L[ℝ] Euclidean (m * d),
          C * Real.sqrt ell ≤ shapeMinimumStretch S →
          ∀ c : Matrix (Fin r) (Fin m) (𝓞 K) → Fin m → 𝓞 K,
            let P := numberFieldMatrixLaw K b r m s hs.ne'
            let D := discreteTotalVariation
              (jointPMF P (fun X => (numberFieldEllipsoidalGaussian K b m S (c X)).map X.mulVec))
              (jointPMF P (fun X => numberFieldConditionalTarget K b X S (c X)))
            D ≤ jointErrorBound (realSecurityError (ell + 4)) 1 ∧ D < realSecurityError ell := by
  obtain ⟨cX, cm, C, ell₀, hcX, hcm, hC, hfamily⟩ :=
    numberField_polynomial_asymptotic K b i hidentity hp
  refine ⟨cX, cm, C, max ell₀ 1, hcX, hcm, hC, ?_⟩
  intro ell hell
  have hell1 : 1 ≤ ell := (le_max_right _ _).trans hell
  obtain ⟨hmr, hs, G, hprob, hgood⟩ := hfamily ell ((le_max_left _ _).trans hell)
  refine ⟨hmr, hs, ?_⟩
  intro S hS c
  dsimp only
  have hδ := real_polynomial_failureBudget_le hell1
  have hb := numberField_gaussian_joint_errorBudget K b _ (fun _ => S) c G hprob
    (realSecurityError_pos (ell + 4)) (by linarith)
    (fun X hX => ⟨(hgood X hX).1, (hgood X hX).2.1.trans hS⟩)
  exact ⟨hb, hb.trans_lt (real_polynomial_jointError_lt hell1)⟩

end GeometricGaussianLHL
end

end NumberFieldLHL

section NumberFieldRepeatedLHL

/-!
## Reusing a Gaussian matrix for independent inputs

The source law first samples independent ring-Gaussian inputs and then
applies the same matrix to each. Its actual joint law is compared with
independent conditional image Gaussians. The error is `3δ + 2Jδ/(1-2δ)`;
the bad-matrix contribution is independent of the number of inputs.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Module NumberField

namespace GeometricGaussianLHL

variable (K : Type*) [Field K] [NumberField K] {d r m J : ℕ}

theorem numberField_gaussian_repeated_good_event (b : Basis (Fin d) ℤ (𝓞 K))
    (p : PMF (Matrix (Fin r) (Fin m) (𝓞 K)))
    (S : Matrix (Fin r) (Fin m) (𝓞 K) → Fin J →
      Euclidean (m * d) ≃L[ℝ] Euclidean (m * d))
    (c : Matrix (Fin r) (Fin m) (𝓞 K) → Fin J → Fin m → 𝓞 K)
    (G : Set (Matrix (Fin r) (Fin m) (𝓞 K))) {δ ε : ℝ}
    (hprob : ENNReal.ofReal (1 - δ) ≤ p.toOuterMeasure G)
    (hε : 0 < ε) (hε1 : ε < 1)
    (hgood : ∀ X ∈ G, Function.Surjective X.mulVec ∧
      ∀ j, smoothingParameter (canonicalKernel K X) ε ≤ shapeMinimumStretch (S X j)) :
    discreteTotalVariation
      (jointPMF p (fun X =>
        (independentProduct (fun j => numberFieldEllipsoidalGaussian K b m (S X j) (c X j))).map
          (fun z j => X.mulVec (z j))))
      (jointPMF p (fun X => independentProduct
        (fun j => numberFieldConditionalTarget K b X (S X j) (c X j)))) ≤
      δ + (J : ℝ) * (ε / (1 - ε)) := by
  simp_rw [independentProduct_map]
  apply discreteTotalVariation_joint_independent_good_event p _ _ G hprob
    (div_nonneg hε.le (sub_pos.mpr hε1).le)
  intro X hX j
  obtain ⟨hsurj, hwidth⟩ := hgood X hX
  rw [numberFieldConditionalTarget_of_surjective K b X hsurj]
  exact numberField_gaussian_pushforward K b X hsurj (S X j) hε hε1 (hwidth j) (c X j)

theorem numberField_polynomial_repeated_lhl (b : Basis (Fin d) ℤ (𝓞 K))
    (i : Fin d) (hidentity : b i = 1) (hr : 1 ≤ r) (hmr : r < m)
    {ell s : ℝ} (hell : 1 ≤ ell) (hs : 0 < s)
    (hwidth : 8 * Real.sqrt (r * d) ≤ s / basisAlpha K b)
    (hbudget : ((r * d : ℕ) : ℝ) * Real.log (numberFieldPolynomialScale K b r m s ell) +
      2 * Real.log (1 / realSecurityError (ell + 4)) ≤ (m : ℝ) * Real.log (8 / 7))
    (S : Euclidean (m * d) ≃L[ℝ] Euclidean (m * d))
    (hS : basisAlpha K b * polynomialThetaWidth (basisKappa K b) (basisMu K b)
      (polynomialColumnHeight (r * d) m ell) ≤ shapeMinimumStretch S)
    (c : Matrix (Fin r) (Fin m) (𝓞 K) → Fin J → Fin m → 𝓞 K) :
    let p := numberFieldMatrixLaw K b r m s hs.ne'
    discreteTotalVariation
      (jointPMF p (fun X =>
        (independentProduct (fun j => numberFieldEllipsoidalGaussian K b m S (c X j))).map
          (fun z j => X.mulVec (z j))))
      (jointPMF p (fun X => independentProduct
        (fun j => numberFieldConditionalTarget K b X S (c X j)))) ≤
      jointErrorBound (realSecurityError (ell + 4)) J := by
  dsimp only
  obtain ⟨G, hprob, hgood⟩ := numberField_polynomial_certificate K b i hidentity hr hmr
    hell hs hwidth hbudget
  have hδ := real_polynomial_failureBudget_le hell
  have hb := numberField_gaussian_repeated_good_event K b
    (numberFieldMatrixLaw K b r m s hs.ne') (fun _ _ => S) c G hprob
    (mul_pos (by norm_num) (realSecurityError_pos (ell + 4))) (by linarith)
    (fun X hX => ⟨(hgood X hX).1, fun _ => (hgood X hX).2.2.1.trans hS⟩)
  convert hb using 1
  unfold jointErrorBound
  ring

end GeometricGaussianLHL
end

end NumberFieldRepeatedLHL

section NumberFieldConstantLHL

/-!
## Constant-width geometric Gaussian leftover hashing

The constant-width case completes Corollary 5.1. Both joint laws use the
actual number-field Gaussian matrix marginal. The target is the total
conditional image law, and centres can be arbitrary functions of the
matrix. Independent reuse pays the bad-matrix probability only once.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Module NumberField

namespace GeometricGaussianLHL

variable (K : Type*) [Field K] [NumberField K] {k r m J : ℕ}
  [IsCyclotomicExtension {2 ^ (k + 1)} ℚ K] {ζ : K}

theorem numberField_constantWidth_lhl (hζ : IsPrimitiveRoot ζ (2 ^ (k + 1))) (hr : 1 ≤ r) (hmr : r < m)
    {ell s : ℝ} (hell : 1 ≤ ell) (hs : 0 < s)
    (hwidth : Real.sqrt (2 ^ (k + 1)).totient ≤ s)
    (hbudget : ((r * (2 ^ (k + 1)).totient : ℕ) : ℝ) * Real.log (powerTwoConstantScale (2 ^ (k + 1)).totient r m s ell) +
      2 * Real.log (1 / realSecurityError (ell + 6)) ≤ (m : ℝ) * Real.log (50 / 49))
    (S : Euclidean (m * (2 ^ (k + 1)).totient) ≃L[ℝ] Euclidean (m * (2 ^ (k + 1)).totient))
    (hS : 640 * Real.sqrt ((2 ^ (k + 1)).totient * constantColumnHeight (r * (2 ^ (k + 1)).totient) m (realSecurityError (ell + 6))) ≤ shapeMinimumStretch S)
    (c : Matrix (Fin r) (Fin m) (𝓞 K) → Fin m → 𝓞 K) :
    let p := numberFieldMatrixLaw K (cyclotomicIntegralBasis K hζ) r m s hs.ne'
    let D := discreteTotalVariation
      (jointPMF p (fun X => (numberFieldEllipsoidalGaussian K (cyclotomicIntegralBasis K hζ) m S (c X)).map X.mulVec))
      (jointPMF p (fun X => numberFieldConditionalTarget K (cyclotomicIntegralBasis K hζ) X S (c X)))
    D ≤ jointErrorBound (realSecurityError (ell + 6)) 1 ∧ D < realSecurityError ell := by
  dsimp only
  obtain ⟨G, hprob, hgood⟩ := numberField_constantWidth_certificate K hζ hr hmr
    hell hs hwidth hbudget
  have hδ := real_constant_failureBudget_le hell
  have hb := numberField_gaussian_joint_errorBudget K (cyclotomicIntegralBasis K hζ)
    (numberFieldMatrixLaw K (cyclotomicIntegralBasis K hζ) r m s hs.ne') (fun _ => S) c G hprob
    (realSecurityError_pos (ell + 6)) (by linarith) (fun X hX =>
      ⟨(hgood X hX).1, (hgood X hX).2.2.1.trans hS⟩)
  exact ⟨hb, hb.trans_lt (real_constant_jointError_lt hell)⟩

theorem numberField_constantWidth_repeated_lhl (hζ : IsPrimitiveRoot ζ (2 ^ (k + 1))) (hr : 1 ≤ r) (hmr : r < m)
    {ell s : ℝ} (hell : 1 ≤ ell) (hs : 0 < s)
    (hwidth : Real.sqrt (2 ^ (k + 1)).totient ≤ s)
    (hbudget : ((r * (2 ^ (k + 1)).totient : ℕ) : ℝ) * Real.log (powerTwoConstantScale (2 ^ (k + 1)).totient r m s ell) +
      2 * Real.log (1 / realSecurityError (ell + 6)) ≤ (m : ℝ) * Real.log (50 / 49))
    (S : Euclidean (m * (2 ^ (k + 1)).totient) ≃L[ℝ] Euclidean (m * (2 ^ (k + 1)).totient))
    (hS : 640 * Real.sqrt ((2 ^ (k + 1)).totient * constantColumnHeight (r * (2 ^ (k + 1)).totient) m (realSecurityError (ell + 6))) ≤ shapeMinimumStretch S)
    (c : Matrix (Fin r) (Fin m) (𝓞 K) → Fin J → Fin m → 𝓞 K) :
    let p := numberFieldMatrixLaw K (cyclotomicIntegralBasis K hζ) r m s hs.ne'
    discreteTotalVariation
      (jointPMF p (fun X =>
        (independentProduct (fun j => numberFieldEllipsoidalGaussian K (cyclotomicIntegralBasis K hζ) m S (c X j))).map
          (fun z j => X.mulVec (z j))))
      (jointPMF p (fun X => independentProduct
        (fun j => numberFieldConditionalTarget K (cyclotomicIntegralBasis K hζ) X S (c X j)))) ≤
      jointErrorBound (realSecurityError (ell + 6)) J := by
  dsimp only
  obtain ⟨G, hprob, hgood⟩ := numberField_constantWidth_certificate K hζ hr hmr
    hell hs hwidth hbudget
  have hδ := real_constant_failureBudget_le hell
  have hb := numberField_gaussian_repeated_good_event K (cyclotomicIntegralBasis K hζ)
    (numberFieldMatrixLaw K (cyclotomicIntegralBasis K hζ) r m s hs.ne') (fun _ _ => S) c G hprob
    (mul_pos (by norm_num) (realSecurityError_pos (ell + 6))) (by linarith)
    (fun X hX => ⟨(hgood X hX).1, fun _ => (hgood X hX).2.2.1.trans hS⟩)
  convert hb using 1
  unfold jointErrorBound
  ring

end GeometricGaussianLHL
end

end NumberFieldConstantLHL
