import GeometricGaussianLHL.SphericalLHL
import GeometricGaussianLHL.CanonicalShaping

/-!
# Geometric Gaussian hints with explicit implementation error

This extends the existing spherical LHL to independent approximate preimage
samplers. The geometric and spectral failures are charged once for the common
matrix; per-column LHL and sampling errors are then added. The sampler accuracy
premise remains explicit until a finite sampler is constructed.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Module NumberField GeometricGaussianLHL

namespace SISToKSIS

theorem column_sampler_error {α : Type*} (implemented approximate exact : PMF α)
    {ε : ℝ}
    (himplementation : discreteTotalVariation implemented approximate ≤ ε / 2)
    (hprecision : discreteTotalVariation approximate exact ≤ ε / 2) :
    discreteTotalVariation implemented exact ≤ ε := by
  have ht := discreteTotalVariation_triangle implemented approximate exact
  linarith

variable (K : Type*) [Field K] [NumberField K] {d k m : ℕ}

/-- The paper's trace-average shape on the event where the input is surjective.
The identity outside that event only completes the analytical target law. -/
def traceAverageHintEventShape (b : Basis (Fin d) ℤ (𝓞 K)) (hk : 0 < k)
    (G : Set (Matrix (Fin k) (Fin m) (𝓞 K)))
    (hsurj : ∀ X ∈ G, Function.Surjective X.mulVec) {w : ℝ} (hw : 0 < w)
    (X : Matrix (Fin k) (Fin m) (𝓞 K)) : Euclidean (m * d) ≃L[ℝ] Euclidean (m * d) := by
  classical
  exact if hX : X ∈ G then canonicalGramShapingShape K b X (hsurj X hX) hk w hw
    else ContinuousLinearEquiv.refl ℝ (Euclidean (m * d))

theorem traceAverageHintEventShape_of_mem (b : Basis (Fin d) ℤ (𝓞 K)) (hk : 0 < k)
    (G : Set (Matrix (Fin k) (Fin m) (𝓞 K)))
    (hsurj : ∀ X ∈ G, Function.Surjective X.mulVec) {w : ℝ} (hw : 0 < w)
    (X : Matrix (Fin k) (Fin m) (𝓞 K)) (hX : X ∈ G) :
    traceAverageHintEventShape K b hk G hsurj hw X =
      canonicalGramShapingShape K b X (hsurj X hX) hk w hw := by
  simp only [traceAverageHintEventShape, dite_eq_left hX]

/-- The distribution guarantee in the spectral hint-generator lemma, conditional
on the explicit per-column sampler accuracy guarantee. -/
theorem approximate_geometric_hint_law
    (b : Basis (Fin d) ℤ (𝓞 K)) (hk : 0 < k)
    (p : PMF (Matrix (Fin k) (Fin m) (𝓞 K)))
    (G H : Set (Matrix (Fin k) (Fin m) (𝓞 K)))
    (hsurj : ∀ X ∈ G, Function.Surjective X.mulVec)
    {pB δsp ε εs B V s₂ : ℝ} (hs₂ : 0 < s₂)
    (hG : ENNReal.ofReal (1 - pB) ≤ p.toOuterMeasure G)
    (hH : ENNReal.ofReal (1 - δsp) ≤ p.toOuterMeasure H)
    (hε : 0 < ε) (hεone : ε < 1) (hεs : 0 ≤ εs)
    (hB : 0 ≤ B) (hwidth : B * V ≤ s₂)
    (hsmooth : ∀ X ∈ G, smoothingParameter (canonicalKernel K X) ε ≤ B)
    (hnorm : ∀ X ∈ H,
      ‖(canonicalEuclideanMatrix K b X).toContinuousLinearMap‖ ≤ V)
    (sampler : Matrix (Fin k) (Fin m) (𝓞 K) → Fin k → PMF (Fin m → 𝓞 K))
    (haccuracy : ∀ X ∈ G ∩ H, ∀ j,
      discreteTotalVariation (sampler X j)
        (numberFieldEllipsoidalGaussian K b m
          (traceAverageHintEventShape K b hk (G ∩ H)
            (fun X hX => hsurj X hX.1) hs₂ X) 0) ≤ εs) :
    discreteTotalVariation
      (jointPMF p (fun X => (independentMatrixColumns (sampler X)).map
        (fun R => X * R + (1 : Matrix (Fin k) (Fin k) (𝓞 K)))))
      (jointPMF p (fun _ => independentMatrixColumns (fun j : Fin k =>
        (numberFieldGaussian K b k s₂ hs₂.ne').map
          (Equiv.addRight (matrixIdentityColumn j))))) ≤
      pB + δsp + (k : ℝ) * (ε / (1 - ε)) + (k : ℝ) * εs := by
  have hprob := pmf_intersection_event_mass p G H hG hH
  have herr : 0 ≤ ε / (1 - ε) + εs :=
    add_nonneg (div_nonneg hε.le (sub_pos.mpr hεone).le) hεs
  have h := discreteTotalVariation_matrixHint_joint_good_event p sampler
    (fun _ _ => numberFieldGaussian K b k s₂ hs₂.ne') (G ∩ H) hprob herr (by
      intro X hX j
      let ideal := numberFieldEllipsoidalGaussian K b m
        (traceAverageHintEventShape K b hk (G ∩ H)
          (fun X hX => hsurj X hX.1) hs₂ X) 0
      have hi : discreteTotalVariation (ideal.map X.mulVec)
          (numberFieldGaussian K b k s₂ hs₂.ne') ≤ ε / (1 - ε) := by
        dsimp [ideal]
        rw [traceAverageHintEventShape_of_mem K b hk (G ∩ H)
          (fun X hX => hsurj X hX.1) hs₂ X hX]
        have hb := (mul_le_mul_of_nonneg_right (hsmooth X hX.1) (norm_nonneg _)).trans
          ((mul_le_mul_of_nonneg_left (hnorm X hX.2) hB).trans hwidth)
        have hpush := canonicalGramShapingShape_gaussian_pushforward K b X
          (hsurj X hX.1) hk s₂ hs₂ hε hεone hb 0
        simpa only [Matrix.mulVec_zero, pmf_map_addRight_zero] using hpush
      have hs := (discreteTotalVariation_map_le (sampler X j) ideal X.mulVec).trans
        (haccuracy X hX j)
      have ht := discreteTotalVariation_triangle ((sampler X j).map X.mulVec)
        (ideal.map X.mulVec) (numberFieldGaussian K b k s₂ hs₂.ne')
      linarith)
  exact h.trans_eq (by ring)

end SISToKSIS
