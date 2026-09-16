import «SIS-to-kSIS».OperatorBounds
import «SIS-to-kSIS».SolutionExtraction
import «SIS-to-kSIS».Parameters
import GeometricGaussianLHL.SpectralBounds

/-!
# Canonical norms for extraction

Complex transpose and adjoint have the same operator norm. Applying this at
each embedding supplies the bounds for the transposed blocks in extraction.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Module NumberField GeometricGaussianLHL

namespace SISToKSIS

def conjugateVector {n : ℕ} (v : EuclideanSpace ℂ (Fin n)) : EuclideanSpace ℂ (Fin n) :=
  WithLp.toLp 2 (fun i => star (v i))

@[simp] theorem conjugateVector_apply {n : ℕ} (v : EuclideanSpace ℂ (Fin n)) (i : Fin n) :
    conjugateVector v i = star (v i) := rfl

theorem conjugateVector_norm {n : ℕ} (v : EuclideanSpace ℂ (Fin n)) :
    ‖conjugateVector v‖ = ‖v‖ := by
  have h : ‖conjugateVector v‖ ^ 2 = ‖v‖ ^ 2 := by
    simp only [EuclideanSpace.norm_sq_eq, conjugateVector_apply, norm_star]
  nlinarith [norm_nonneg (conjugateVector v), norm_nonneg v]

variable (K : Type*) [Field K] [NumberField K] {d r m : ℕ}

local instance extractionAmbientInner : InnerProductSpace ℝ (CanonicalAmbient K) := inferInstance
local instance extractionSpaceInner : InnerProductSpace ℝ (canonicalSpace K) := inferInstance
local instance extractionPowerInner (n : ℕ) : InnerProductSpace ℝ (CanonicalPower K n) := inferInstance

def canonicalRingNorm {n : ℕ} (v : Fin n → 𝓞 K) : ℝ :=
  ‖canonicalPowerEmbedding K n v‖

theorem canonicalRingNorm_nonneg {n : ℕ} (v : Fin n → 𝓞 K) : 0 ≤ canonicalRingNorm K v :=
  norm_nonneg _

theorem canonicalRingNorm_eq_euclidean (b : Basis (Fin d) ℤ (𝓞 K))
    {n : ℕ} (v : Fin n → 𝓞 K) :
    canonicalRingNorm K v = ‖canonicalEuclideanEmbedding K b n v‖ := by
  change _ = ‖canonicalOrthonormalCoordinates K b n (canonicalPowerEmbedding K n v)‖
  rw [LinearIsometryEquiv.norm_map]
  rfl

theorem canonicalRingNorm_neg {n : ℕ} (v : Fin n → 𝓞 K) :
    canonicalRingNorm K (-v) = canonicalRingNorm K v := by
  simp only [canonicalRingNorm, map_neg, norm_neg]

theorem canonicalRingNorm_add_le {n : ℕ} (v w : Fin n → 𝓞 K) :
    canonicalRingNorm K (v + w) ≤ canonicalRingNorm K v + canonicalRingNorm K w := by
  unfold canonicalRingNorm
  rw [map_add]
  exact norm_add_le _ _

theorem canonicalRingNorm_sub_le {n : ℕ} (v w : Fin n → 𝓞 K) :
    canonicalRingNorm K (v - w) ≤ canonicalRingNorm K v + canonicalRingNorm K w := by
  unfold canonicalRingNorm
  rw [map_sub]
  exact norm_sub_le _ _

theorem canonicalRingNorm_append_sq {a c : ℕ} (v : Fin a → 𝓞 K) (w : Fin c → 𝓞 K) :
    canonicalRingNorm K (Fin.append v w) ^ 2 =
      canonicalRingNorm K v ^ 2 + canonicalRingNorm K w ^ 2 := by
  simp only [canonicalRingNorm, PiLp.norm_sq_eq_of_L2, canonicalPowerEmbedding_apply,
    Fin.sum_univ_add, Fin.append_left, Fin.append_right]

def splitCanonicalNorm {a c : ℕ} (v : Fin a ⊕ Fin c → 𝓞 K) : ℝ :=
  canonicalRingNorm K (Fin.append (v ∘ Sum.inl) (v ∘ Sum.inr))

theorem splitCanonicalNorm_projections {a c : ℕ} (v : Fin a ⊕ Fin c → 𝓞 K) :
    canonicalRingNorm K (v ∘ Sum.inl) ≤ splitCanonicalNorm K v ∧
      canonicalRingNorm K (v ∘ Sum.inr) ≤ splitCanonicalNorm K v := by
  have h := canonicalRingNorm_append_sq K (v ∘ Sum.inl) (v ∘ Sum.inr)
  have hp := canonicalRingNorm_nonneg K (Fin.append (v ∘ Sum.inl) (v ∘ Sum.inr))
  have hl := canonicalRingNorm_nonneg K (v ∘ Sum.inl)
  have hr := canonicalRingNorm_nonneg K (v ∘ Sum.inr)
  unfold splitCanonicalNorm
  constructor <;> nlinarith [sq_nonneg (canonicalRingNorm K (v ∘ Sum.inl)),
    sq_nonneg (canonicalRingNorm K (v ∘ Sum.inr))]

theorem canonicalRingNorm_mulVec_le (b : Basis (Fin d) ℤ (𝓞 K))
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) {U : ℝ}
    (hX : ‖(canonicalEuclideanMatrix K b X).toContinuousLinearMap‖ ≤ U)
    (v : Fin m → 𝓞 K) : canonicalRingNorm K (X.mulVec v) ≤ U * canonicalRingNorm K v := by
  rw [canonicalRingNorm_eq_euclidean K b, canonicalRingNorm_eq_euclidean K b,
    ← canonicalEuclideanMatrix_integer]
  exact ((canonicalEuclideanMatrix K b X).toContinuousLinearMap.le_opNorm _).trans
    (mul_le_mul_of_nonneg_right hX (norm_nonneg _))

omit [NumberField K] in
theorem complexEmbeddingOperator_transpose_apply (τ : K →+* ℂ)
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) (v : EuclideanSpace ℂ (Fin r)) :
    complexEmbeddingOperator K τ X.transpose v =
      conjugateVector ((complexEmbeddingOperator K τ X).adjoint (conjugateVector v)) := by
  ext j
  change (∑ i, τ (algebraMap (𝓞 K) K (X i j)) * v i) =
    star ((complexEmbeddingOperator K τ X).adjoint (conjugateVector v) j)
  rw [complexEmbeddingOperator_adjoint_apply]
  simp [conjugateVector_apply, mul_comm]

omit [NumberField K] in
theorem complexEmbeddingOperator_transpose_norm_le (τ : K →+* ℂ)
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) :
    ‖complexEmbeddingOperator K τ X.transpose‖ ≤ ‖complexEmbeddingOperator K τ X‖ := by
  apply (complexEmbeddingOperator K τ X.transpose).opNorm_le_bound (norm_nonneg _)
  intro v
  rw [complexEmbeddingOperator_transpose_apply, conjugateVector_norm]
  simpa only [ContinuousLinearMap.adjoint.norm_map, conjugateVector_norm] using
    (complexEmbeddingOperator K τ X).adjoint.le_opNorm (conjugateVector v)

omit [NumberField K] in
theorem complexEmbeddingOperator_transpose_norm (τ : K →+* ℂ)
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) :
    ‖complexEmbeddingOperator K τ X.transpose‖ = ‖complexEmbeddingOperator K τ X‖ := by
  apply le_antisymm (complexEmbeddingOperator_transpose_norm_le K τ X)
  simpa only [Matrix.transpose_transpose] using
    complexEmbeddingOperator_transpose_norm_le K τ X.transpose

omit [NumberField K] in
theorem complexEmbeddingMatrix_transpose_norm (τ : K →+* ℂ)
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) :
    ‖(complexEmbeddingMatrix K τ X.transpose).toContinuousLinearMap‖ =
      ‖(complexEmbeddingMatrix K τ X).toContinuousLinearMap‖ := by
  rw [← complexEmbeddingOperator_restrict, ← complexEmbeddingOperator_restrict,
    ContinuousLinearMap.norm_restrictScalars, ContinuousLinearMap.norm_restrictScalars,
    complexEmbeddingOperator_transpose_norm]

theorem canonicalTranspose_norm_le_embeddings (b : Basis (Fin d) ℤ (𝓞 K))
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) {U : ℝ} (hU : 0 ≤ U)
    (h : ∀ τ : K →+* ℂ, ‖(complexEmbeddingMatrix K τ X).toContinuousLinearMap‖ ≤ U) :
    ‖(canonicalEuclideanMatrix K b X.transpose).toContinuousLinearMap‖ ≤ U := by
  apply canonicalEuclideanMatrix_norm_le_embeddings K b X.transpose hU
  intro τ
  rw [complexEmbeddingMatrix_transpose_norm]
  exact h τ

theorem canonical_extraction_norm_bound (b : Basis (Fin d) ℤ (𝓞 K))
    {k : ℕ} (X : Matrix (Fin k) (Fin m) (𝓞 K)) (R : Matrix (Fin m) (Fin k) (𝓞 K))
    {a t : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t)
    (hX : ∀ τ : K →+* ℂ, ‖(complexEmbeddingMatrix K τ X).toContinuousLinearMap‖ ≤ a)
    (hR : ∀ τ : K →+* ℂ, ‖(complexEmbeddingMatrix K τ R).toContinuousLinearMap‖ ≤ t)
    (v : Fin m ⊕ Fin k → 𝓞 K) :
    canonicalRingNorm K ((extractionMatrix X R).mulVec v) ≤
      (1 + a * t + a) * splitCanonicalNorm K v := by
  let v₀ := v ∘ Sum.inl
  let v₁ := v ∘ Sum.inr
  have hXT := canonicalTranspose_norm_le_embeddings K b X ha hX
  have hRT := canonicalTranspose_norm_le_embeddings K b R ht hR
  have hR₀ := canonicalRingNorm_mulVec_le K b R.transpose hRT v₀
  have hXR₀ := (canonicalRingNorm_mulVec_le K b X.transpose hXT (R.transpose.mulVec v₀)).trans
    (mul_le_mul_of_nonneg_left hR₀ ha)
  have hX₁ := canonicalRingNorm_mulVec_le K b X.transpose hXT v₁
  have htri := (canonicalRingNorm_add_le K (-v₀ - X.transpose.mulVec (R.transpose.mulVec v₀))
    (X.transpose.mulVec v₁)).trans
      (add_le_add (canonicalRingNorm_sub_le K (-v₀) (X.transpose.mulVec (R.transpose.mulVec v₀))) le_rfl)
  rw [canonicalRingNorm_neg] at htri
  have hv := splitCanonicalNorm_projections K v
  have hv₀ : canonicalRingNorm K v₀ ≤ splitCanonicalNorm K v := hv.1
  have hv₁ : canonicalRingNorm K v₁ ≤ splitCanonicalNorm K v := hv.2
  have hw₀ := mul_le_mul_of_nonneg_left hv₀ (mul_nonneg ha ht)
  have hw₁ := mul_le_mul_of_nonneg_left hv₁ ha
  rw [extractionMatrix_apply]
  change canonicalRingNorm K (-v₀ - X.transpose.mulVec (R.transpose.mulVec v₀) + X.transpose.mulVec v₁) ≤ _
  nlinarith

/-- Exact SIS extraction with the paper's canonical norm, rather than an abstract norm premise. -/
theorem extract_canonical_solution {Q : Type*} [CommRing Q]
    (b : Basis (Fin d) ℤ (𝓞 K)) (modQ : 𝓞 K →+* Q)
    {k n : ℕ} (A : Matrix (Fin n) (Fin m) Q)
    (X : Matrix (Fin k) (Fin m) (𝓞 K)) (R : Matrix (Fin m) (Fin k) (𝓞 K))
    {a t β₀ β₁ : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t)
    (hX : ∀ τ : K →+* ℂ, ‖(complexEmbeddingMatrix K τ X).toContinuousLinearMap‖ ≤ a)
    (hR : ∀ τ : K →+* ℂ, ‖(complexEmbeddingMatrix K τ R).toContinuousLinearMap‖ ≤ t)
    (hβ : (1 + a * t + a) * β₁ ≤ β₀) (v : Fin m ⊕ Fin k → 𝓞 K)
    (hv : IsKSISSolution modQ (algebraMap (𝓞 K) K) (splitCanonicalNorm K) β₁
      (A * (extractionMatrix X R).map modQ) (columnHints X R) v) :
    IsSISSolution modQ (canonicalRingNorm K) β₀ A ((extractionMatrix X R).mulVec v) :=
  extract_solution modQ (algebraMap (𝓞 K) K) _ _ A X R
    (by nlinarith [mul_nonneg ha ht]) hβ (canonical_extraction_norm_bound K b X R ha ht hX hR) v hv

/-- The improved norm loss, with the existing spectral constants made explicit. -/
theorem improved_canonical_extraction_norm (b : Basis (Fin d) ℤ (𝓞 K))
    {k : ℕ} (X : Matrix (Fin k) (Fin m) (𝓞 K)) (R : Matrix (Fin m) (Fin k) (𝓞 K))
    (hm : 1 ≤ m) {s₁ s₂ : ℝ} (hs₁ : 0 < s₁) (hs : s₁ ≤ s₂)
    (hscale : 1 ≤ s₂ * Real.sqrt m)
    (hX : ∀ τ : K →+* ℂ, ‖(complexEmbeddingMatrix K τ X).toContinuousLinearMap‖ ≤
      4 * s₁ * Real.sqrt m)
    (hR : ∀ τ : K →+* ℂ, ‖(complexEmbeddingMatrix K τ R).toContinuousLinearMap‖ ≤
      8192 * s₂ / s₁) (v : Fin m ⊕ Fin k → 𝓞 K) :
    canonicalRingNorm K ((extractionMatrix X R).mulVec v) ≤ normLoss m s₂ * splitCanonicalNorm K v := by
  have hs₂ : 0 < s₂ := hs₁.trans_le hs
  have hr : 0 ≤ 8192 * s₂ / s₁ := by positivity
  have hb := canonical_extraction_norm_bound K b X R (by positivity) hr hX hR v
  have hc := normLoss_of_spectral hm hr hs₁ hs hscale (le_refl _) (le_refl _)
  exact hb.trans (mul_le_mul_of_nonneg_right hc (canonicalRingNorm_nonneg K _))

theorem extract_canonical_solution_improved {Q : Type*} [CommRing Q]
    (b : Basis (Fin d) ℤ (𝓞 K)) (modQ : 𝓞 K →+* Q)
    {k n : ℕ} (A : Matrix (Fin n) (Fin m) Q)
    (X : Matrix (Fin k) (Fin m) (𝓞 K)) (R : Matrix (Fin m) (Fin k) (𝓞 K))
    (hm : 1 ≤ m) {s₁ s₂ β₀ β₁ : ℝ} (hs₁ : 0 < s₁) (hs : s₁ ≤ s₂)
    (hscale : 1 ≤ s₂ * Real.sqrt m)
    (hX : ∀ τ : K →+* ℂ, ‖(complexEmbeddingMatrix K τ X).toContinuousLinearMap‖ ≤
      4 * s₁ * Real.sqrt m)
    (hR : ∀ τ : K →+* ℂ, ‖(complexEmbeddingMatrix K τ R).toContinuousLinearMap‖ ≤
      8192 * s₂ / s₁)
    (hβ : normLoss m s₂ * β₁ ≤ β₀) (v : Fin m ⊕ Fin k → 𝓞 K)
    (hv : IsKSISSolution modQ (algebraMap (𝓞 K) K) (splitCanonicalNorm K) β₁
      (A * (extractionMatrix X R).map modQ) (columnHints X R) v) :
    IsSISSolution modQ (canonicalRingNorm K) β₀ A ((extractionMatrix X R).mulVec v) :=
  extract_solution modQ (algebraMap (𝓞 K) K) _ _ A X R
    (normLoss_pos hm (hs₁.trans_le hs)) hβ
    (improved_canonical_extraction_norm K b X R hm hs₁ hs hscale hX hR) v hv

end SISToKSIS
