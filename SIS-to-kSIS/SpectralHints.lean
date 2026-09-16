import «SIS-to-kSIS».FiniteSampling
import «SIS-to-kSIS».GeometricHints
import «SIS-to-kSIS».CanonicalExtraction
import «SIS-to-kSIS».GameBounds
import «SIS-to-kSIS».GaussianFactorization

/-!
# Spectral events for geometric hints

The input event retains all complex embedding bounds. The shaped preimage
Gaussian then has the operator norm required for the improved extraction loss.
The stored finite sampler satisfies its column-accuracy premise using the
existing canonical shaping constructor and the Section 5.2 width window. The
full stored hint program has exactly the joint law used by the reduction.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Module NumberField GeometricGaussianLHL MeasureTheory

namespace SISToKSIS

variable (K : Type*) [Field K] [NumberField K] {d k m : ℕ}

def hintSpectralEvent (b : Basis (Fin d) ℤ (𝓞 K)) (s : ℝ) :
    Set (Matrix (Fin k) (Fin m) (𝓞 K)) :=
  {X | (∀ τ : K →+* ℂ, ‖(complexEmbeddingMatrix K τ X).toContinuousLinearMap‖ ≤
      4 * s * Real.sqrt m) ∧
    ∃ hX : Function.Surjective (canonicalEuclideanMatrix K b X),
      s * Real.sqrt m / 2048 ≤ kernelMinimumStretch (canonicalEuclideanMatrix K b X) hX}

theorem hintSpectralEvent_canonical_upper (b : Basis (Fin d) ℤ (𝓞 K))
    {s : ℝ} (hs : 0 ≤ s) (X : Matrix (Fin k) (Fin m) (𝓞 K))
    (hX : X ∈ hintSpectralEvent K b s) :
    ‖(canonicalEuclideanMatrix K b X).toContinuousLinearMap‖ ≤ 4 * s * Real.sqrt m :=
  canonicalEuclideanMatrix_norm_le_embeddings K b X (by positivity) hX.1

theorem shaped_preimage_norm
    (b : Basis (Fin d) ℤ (𝓞 K)) (hk : 0 < k) (hm : 0 < m)
    {s₁ s₂ : ℝ} (hs₁ : 0 < s₁) (hs₂ : 0 < s₂)
    (X : Matrix (Fin k) (Fin m) (𝓞 K)) (hX : Function.Surjective X.mulVec)
    (hsp : X ∈ hintSpectralEvent K b s₁) :
    ‖(canonicalGramShapingShape K b X hX hk s₂ hs₂).toContinuousLinearMap‖ ≤
      2048 * s₂ / (s₁ * Real.sqrt m) := by
  obtain ⟨_, hf, hmin⟩ := hsp
  rw [canonicalGramShapingShape_norm]
  have hlow : 0 < s₁ * Real.sqrt m / 2048 := by positivity
  have hb := div_le_div_of_nonneg_left hs₂.le hlow hmin
  exact hb.trans_eq (by ring)

theorem ellipsoidal_embedding_four_failure (b : Basis (Fin d) ℤ (𝓞 K))
    (S : Euclidean (m * d) ≃L[ℝ] Euclidean (m * d))
    {B δ : ℝ} (hB : 0 < B) (hS : ‖S.toContinuousLinearMap‖ ≤ B)
    (hδ : 0 < δ) (hδone : δ < 1)
    (hkm : k ≤ m) (hlog : Real.log (2 * d / δ) ≤ m) :
    (independentMatrixColumns (fun _ : Fin k => numberFieldEllipsoidalGaussian K b m S 0)).toOuterMeasure
      {R | ∃ τ : K →+* ℂ, 4 * B * Real.sqrt m <
        ‖(complexEmbeddingMatrix K τ R).toContinuousLinearMap‖} ≤ ENNReal.ofReal δ := by
  apply le_trans ((independentMatrixColumns
    (fun _ : Fin k => numberFieldEllipsoidalGaussian K b m S 0)).toOuterMeasure.mono ?_)
    (numberField_ellipsoidal_embedding_union_failure K b (fun _ => S) hB (fun _ => hS) hδ hδone)
  rintro R ⟨τ, hτ⟩
  exact ⟨τ, (numberFieldSpectralThreshold_le_four hB.le (Nat.cast_nonneg m)
    le_rfl (by exact_mod_cast hkm) hlog).trans_lt hτ⟩

/-- Independent approximate columns inherit the exact Gaussian operator tail. -/
theorem approximate_preimage_embedding_failure
    (b : Basis (Fin d) ℤ (𝓞 K)) (hk : 0 < k) (hm : 0 < m)
    {s₁ s₂ δ εs : ℝ} (hs₁ : 0 < s₁) (hs₂ : 0 < s₂)
    (X : Matrix (Fin k) (Fin m) (𝓞 K)) (hX : Function.Surjective X.mulVec)
    (hsp : X ∈ hintSpectralEvent K b s₁)
    (hδ : 0 < δ) (hδone : δ < 1)
    (hkm : k ≤ m) (hlog : Real.log (2 * d / δ) ≤ m)
    (sampler : Fin k → PMF (Fin m → 𝓞 K))
    (haccuracy : ∀ j, discreteTotalVariation (sampler j)
      (numberFieldEllipsoidalGaussian K b m
        (canonicalGramShapingShape K b X hX hk s₂ hs₂) 0) ≤ εs) :
    (independentMatrixColumns sampler).toOuterMeasure
      {R | ∃ τ : K →+* ℂ, 8192 * s₂ / s₁ <
        ‖(complexEmbeddingMatrix K τ R).toContinuousLinearMap‖} ≤
      ENNReal.ofReal (δ + (k : ℝ) * εs) := by
  let S := canonicalGramShapingShape K b X hX hk s₂ hs₂
  have hb : 0 < 2048 * s₂ / (s₁ * Real.sqrt m) := by positivity
  have ht := ellipsoidal_embedding_four_failure K b S hb
    (shaped_preimage_norm K b hk hm hs₁ hs₂ X hX hsp) hδ hδone hkm hlog
  have hmroot : Real.sqrt (m : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hm)).ne'
  have hc : 4 * (2048 * s₂ / (s₁ * Real.sqrt m)) * Real.sqrt m = 8192 * s₂ / s₁ := by
    field_simp
    ring
  rw [hc] at ht
  exact pmf_outer_failure_transfer _ _ _ hδ.le ht
    (discreteTotalVariation_independentMatrixColumns_le_uniform _ _ haccuracy)

/-- A single exceptional input charge suffices for the simultaneous norm bound
for every possible adversarial output vector. -/
theorem approximate_hint_extraction_failure
    (b : Basis (Fin d) ℤ (𝓞 K)) (hk : 0 < k)
    (p : PMF (Matrix (Fin k) (Fin m) (𝓞 K)))
    (G : Set (Matrix (Fin k) (Fin m) (𝓞 K)))
    (hsurj : ∀ X ∈ G, Function.Surjective X.mulVec)
    (hm : 1 ≤ m) {s₁ s₂ pB δsp δop εs : ℝ}
    (hs₁ : 0 < s₁) (hs : s₁ ≤ s₂) (hscale : 1 ≤ s₂ * Real.sqrt m)
    (hG : ENNReal.ofReal (1 - pB) ≤ p.toOuterMeasure G)
    (hH : ENNReal.ofReal (1 - δsp) ≤ p.toOuterMeasure (hintSpectralEvent K b s₁))
    (hδop : 0 < δop) (hδopone : δop < 1) (hεs : 0 ≤ εs)
    (hkm : k ≤ m) (hlog : Real.log (2 * d / δop) ≤ m)
    (sampler : Matrix (Fin k) (Fin m) (𝓞 K) → Fin k → PMF (Fin m → 𝓞 K))
    (haccuracy : ∀ X ∈ G ∩ hintSpectralEvent K b s₁, ∀ j,
      discreteTotalVariation (sampler X j)
        (numberFieldEllipsoidalGaussian K b m
          (traceAverageHintEventShape K b hk (G ∩ hintSpectralEvent K b s₁)
            (fun X hX => hsurj X hX.1) (hs₁.trans_le hs) X) 0) ≤ εs) :
    (jointPMF p (fun X => independentMatrixColumns (sampler X))).toOuterMeasure
      {z | ∃ v : Fin m ⊕ Fin k → 𝓞 K,
        normLoss m s₂ * splitCanonicalNorm K v <
          canonicalRingNorm K ((extractionMatrix z.1 z.2).mulVec v)} ≤
      ENNReal.ofReal (pB + δsp + δop + (k : ℝ) * εs) := by
  have hbound := joint_bad_outer_probability p (fun X => independentMatrixColumns (sampler X))
    (G ∩ hintSpectralEvent K b s₁)
    {z | ∃ v : Fin m ⊕ Fin k → 𝓞 K,
      normLoss m s₂ * splitCanonicalNorm K v <
        canonicalRingNorm K ((extractionMatrix z.1 z.2).mulVec v)}
    (pmf_intersection_event_mass p G (hintSpectralEvent K b s₁) hG hH)
    (show 0 ≤ δop + (k : ℝ) * εs by positivity) (by
      intro X hX
      have hacc (j : Fin k) := haccuracy X hX j
      simp only [traceAverageHintEventShape_of_mem K b hk
        (G ∩ hintSpectralEvent K b s₁) (fun X hX => hsurj X hX.1)
        (hs₁.trans_le hs) X hX] at hacc
      have ht := approximate_preimage_embedding_failure K b hk hm hs₁ (hs₁.trans_le hs)
        X (hsurj X hX.1) hX.2 hδop hδopone hkm hlog (sampler X) hacc
      apply le_trans ((independentMatrixColumns (sampler X)).toOuterMeasure.mono ?_) ht
      rintro R ⟨v, hv⟩
      by_contra hR
      have hR' : ∀ τ : K →+* ℂ,
          ‖(complexEmbeddingMatrix K τ R).toContinuousLinearMap‖ ≤ 8192 * s₂ / s₁ :=
        fun τ => le_of_not_gt (fun ht => hR ⟨τ, ht⟩)
      exact (not_lt_of_ge (improved_canonical_extraction_norm K b X R hm hs₁ hs
        hscale hX.2.1 hR' v)) hv)
  simpa only [add_assoc] using hbound

/-- Distribution and simultaneous norm conclusions. This proposition does not
assert that the supplied sampler has a finite implementation. -/
structure HintGeneratorBounds (b : Basis (Fin d) ℤ (𝓞 K))
    (p : PMF (Matrix (Fin k) (Fin m) (𝓞 K))) {s₂ : ℝ} (hs₂ : 0 < s₂)
    (sampler : Matrix (Fin k) (Fin m) (𝓞 K) → Fin k → PMF (Fin m → 𝓞 K))
    (δlaw δnorm : ℝ) : Prop where
  law : discreteTotalVariation
    (jointPMF p (fun X => (independentMatrixColumns (sampler X)).map
      (fun R => X * R + (1 : Matrix (Fin k) (Fin k) (𝓞 K)))))
    (jointPMF p (fun _ => independentMatrixColumns (fun j : Fin k =>
      (numberFieldGaussian K b k s₂ hs₂.ne').map
        (Equiv.addRight (matrixIdentityColumn j))))) ≤ δlaw
  norm : (jointPMF p (fun X => independentMatrixColumns (sampler X))).toOuterMeasure
    {z | ∃ v : Fin m ⊕ Fin k → 𝓞 K,
      normLoss m s₂ * splitCanonicalNorm K v <
        canonicalRingNorm K ((extractionMatrix z.1 z.2).mulVec v)} ≤ ENNReal.ofReal δnorm

theorem hintBlocksEquiv_columnHints {R : Type*} [CommRing R] {m k : ℕ}
    (X : Matrix (Fin k) (Fin m) R) (Z : Matrix (Fin m) (Fin k) R)
    (i : Fin m ⊕ Fin k) (j : Fin k) :
    hintBlocksEquiv m k (X, X * Z + 1) (finSumFinEquiv i) j = columnHints X Z i j := by
  cases i <;> simp [hintBlocksEquiv, columnHints, rowHints]

/-- The same distribution guarantee in the column format of the k-SIS game. -/
theorem HintGeneratorBounds.column_law (b : Basis (Fin d) ℤ (𝓞 K))
    {s₁ s₂ δlaw δnorm : ℝ} (h₁ : s₁ ≠ 0) (hs₂ : 0 < s₂)
    (sampler : Matrix (Fin k) (Fin m) (𝓞 K) → Fin k → PMF (Fin m → 𝓞 K))
    (h : HintGeneratorBounds K b (numberFieldMatrixLaw K b k m s₁ h₁) hs₂ sampler δlaw δnorm) :
    discreteTotalVariation
      ((jointPMF (numberFieldMatrixLaw K b k m s₁ h₁)
        (fun X => (independentMatrixColumns (sampler X)).map
          (fun R => X * R + (1 : Matrix (Fin k) (Fin k) (𝓞 K))))).map
            (hintBlocksEquiv m k))
      (independentMatrixColumns (fun j : Fin k => numberFieldEllipsoidalGaussian K b (m + k)
        (paperHintShape K b m k h₁ hs₂.ne') (matrixIdentityColumn (Fin.natAdd m j)))) ≤ δlaw := by
  rw [← paperHint_blocks_law K b m k h₁ hs₂.ne', discreteTotalVariation_map_equiv]
  exact h.law

/-- The distribution guarantee for the hint matrix actually paired with the
extraction matrix, under the joint law of the sampled blocks. -/
theorem HintGeneratorBounds.generated_column_law (b : Basis (Fin d) ℤ (𝓞 K))
    {s₁ s₂ δlaw δnorm : ℝ} (h₁ : s₁ ≠ 0) (hs₂ : 0 < s₂)
    (sampler : Matrix (Fin k) (Fin m) (𝓞 K) → Fin k → PMF (Fin m → 𝓞 K))
    (h : HintGeneratorBounds K b (numberFieldMatrixLaw K b k m s₁ h₁) hs₂ sampler δlaw δnorm) :
    discreteTotalVariation
      ((jointPMF (numberFieldMatrixLaw K b k m s₁ h₁)
        (fun X => independentMatrixColumns (sampler X))).map
          (fun z => (columnHints z.1 z.2).submatrix finSumFinEquiv.symm id))
      (independentMatrixColumns (fun j : Fin k => numberFieldEllipsoidalGaussian K b (m + k)
        (paperHintShape K b m k h₁ hs₂.ne') (matrixIdentityColumn (Fin.natAdd m j)))) ≤ δlaw := by
  have he (X : Matrix (Fin k) (Fin m) (𝓞 K)) (Z : Matrix (Fin m) (Fin k) (𝓞 K)) :
      hintBlocksEquiv m k (X, X * Z + 1) =
        (columnHints X Z).submatrix finSumFinEquiv.symm id := by
    funext i j
    simpa only [Equiv.apply_symm_apply, Matrix.submatrix_apply, id_eq] using
      hintBlocksEquiv_columnHints X Z (finSumFinEquiv.symm i) j
  simpa only [jointPMF_map_second, PMF.map_comp, Function.comp_def, he] using
    h.column_law K b h₁ hs₂ sampler

section PowerTwo

variable {a : ℕ} [IsCyclotomicExtension {2 ^ (a + 1)} ℚ K] {ζ : K}

theorem powerTwo_hintSpectralEvent (hζ : IsPrimitiveRoot ζ (2 ^ (a + 1)))
    (hk : 0 < k) {s δ : ℝ} (hs : 0 < s)
    (hσ : 1 ≤ s / Real.sqrt (2 ^ (a + 1)).totient) (hδ : 0 < δ) (hδone : δ < 1)
    (hcols : lowerSpectralColumnConstant *
      ((k : ℝ) + Real.log (2 * (2 ^ (a + 1)).totient / δ)) ≤ m) :
    ENNReal.ofReal (1 - δ) ≤
      (numberFieldMatrixLaw K (cyclotomicIntegralBasis K hζ) k m s hs.ne').toOuterMeasure
        (hintSpectralEvent K (cyclotomicIntegralBasis K hζ) s) := by
  let b := cyclotomicIntegralBasis K hζ
  let d := (2 ^ (a + 1)).totient
  have hd : 0 < d := integralBasis_dimension_pos K b
  let : Nonempty (Fin (k * d)) := ⟨⟨0, Nat.mul_pos hk hd⟩⟩
  have hkm : (k : ℝ) ≤ m := by
    exact_mod_cast (lowerSpectral_columns_upper_conditions hd hδ hδone hcols).1
  have hm : (0 : ℝ) < m := (Nat.cast_pos.mpr hk).trans_le hkm
  have hc : 0 < s * Real.sqrt m / 2048 := by positivity
  apply (powerTwo_complex_spectral_event K hζ hs hσ hδ hδone hcols).trans
  apply OuterMeasure.mono
  rintro X ⟨hu, hl⟩
  let f := canonicalEuclideanMatrix K b X
  have hlow : ∀ y, (s * Real.sqrt m / 2048) * ‖y‖ ≤ ‖f.adjoint y‖ :=
    canonicalEuclideanMatrix_adjoint_lower K b X hc.le hl
  have hf : Function.Surjective f := surjective_of_adjoint_lower f hc hlow
  refine ⟨?_, hf, minimumStretch_of_adjoint_lower f hf hc hlow⟩
  simpa only [complexSpectralUpperBound, mul_assoc] using hu

/-- The two analytical conclusions of the spectral hint-generator lemma, under
the actual power-of-two matrix law and an explicit column-accuracy premise. -/
theorem powerTwo_hint_generator_bounds
    (hζ : IsPrimitiveRoot ζ (2 ^ (a + 1)))
    (hk : 0 < k) {s₁ s₂ pB δsp δop ε εs B : ℝ}
    (hs₁ : 0 < s₁) (hs : s₁ ≤ s₂)
    (hσ : 1 ≤ s₁ / Real.sqrt (2 ^ (a + 1)).totient)
    (hδsp : 0 < δsp) (hδspone : δsp < 1)
    (hcols : lowerSpectralColumnConstant *
      ((k : ℝ) + Real.log (2 * (2 ^ (a + 1)).totient / δsp)) ≤ m)
    (hδop : 0 < δop) (hδopone : δop < 1)
    (hlogop : Real.log (2 * (2 ^ (a + 1)).totient / δop) ≤ m)
    (hε : 0 < ε) (hεone : ε < 1) (hεs : 0 ≤ εs) (hB : 0 ≤ B)
    (hwidth : B * (4 * s₁ * Real.sqrt m) ≤ s₂)
    (G : Set (Matrix (Fin k) (Fin m) (𝓞 K)))
    (hsurj : ∀ X ∈ G, Function.Surjective X.mulVec)
    (hG : ENNReal.ofReal (1 - pB) ≤
      (numberFieldMatrixLaw K (cyclotomicIntegralBasis K hζ) k m s₁ hs₁.ne').toOuterMeasure G)
    (hsmooth : ∀ X ∈ G, smoothingParameter (canonicalKernel K X) ε ≤ B)
    (sampler : Matrix (Fin k) (Fin m) (𝓞 K) → Fin k → PMF (Fin m → 𝓞 K))
    (haccuracy : ∀ X ∈ G ∩ hintSpectralEvent K (cyclotomicIntegralBasis K hζ) s₁, ∀ j,
      discreteTotalVariation (sampler X j)
        (numberFieldEllipsoidalGaussian K (cyclotomicIntegralBasis K hζ) m
          (traceAverageHintEventShape K (cyclotomicIntegralBasis K hζ) hk
            (G ∩ hintSpectralEvent K (cyclotomicIntegralBasis K hζ) s₁)
            (fun X hX => hsurj X hX.1) (hs₁.trans_le hs) X) 0) ≤ εs) :
    HintGeneratorBounds K (cyclotomicIntegralBasis K hζ)
      (numberFieldMatrixLaw K (cyclotomicIntegralBasis K hζ) k m s₁ hs₁.ne')
      (hs₁.trans_le hs) sampler
      (hintDistributionError k pB δsp ε εs) (hintNormFailure k pB δsp δop εs) := by
  let b := cyclotomicIntegralBasis K hζ
  let d := (2 ^ (a + 1)).totient
  have hd : 0 < d := integralBasis_dimension_pos K b
  let : Nonempty (Fin (k * d)) := ⟨⟨0, Nat.mul_pos hk hd⟩⟩
  have hkm : k ≤ m := (lowerSpectral_columns_upper_conditions hd hδsp hδspone hcols).1
  have hm : 1 ≤ m := hk.trans_le hkm
  have hdroot : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hd)
  have hsqrt : Real.sqrt (d : ℝ) ≤ s₁ := by
    simpa only [one_mul] using (le_div_iff₀ hdroot).mp hσ
  have hone : 1 ≤ s₁ := (Real.one_le_sqrt.mpr (by exact_mod_cast hd)).trans hsqrt
  have hscale : 1 ≤ s₂ * Real.sqrt m := by
    simpa only [one_mul] using mul_le_mul (hone.trans hs)
      (Real.one_le_sqrt.mpr (by exact_mod_cast hm)) (by norm_num : (0 : ℝ) ≤ 1)
      (hs₁.trans_le hs).le
  have hH := powerTwo_hintSpectralEvent K hζ hk hs₁ hσ hδsp hδspone hcols
  refine ⟨?_, ?_⟩
  · exact approximate_geometric_hint_law K b hk _ G (hintSpectralEvent K b s₁)
      hsurj (hs₁.trans_le hs) hG hH hε hεone hεs hB hwidth hsmooth
      (fun X hX => hintSpectralEvent_canonical_upper K b hs₁.le X hX) sampler haccuracy
  · exact approximate_hint_extraction_failure K b hk _ G hsurj hm hs₁ hs hscale hG hH
      hδop hδopone hεs hkm hlogop sampler haccuracy

end PowerTwo

end SISToKSIS

noncomputable section
namespace SISToKSIS

/-- The modular lower bound already implies the geometric theorem's input
width in a power-of-two cyclotomic field. -/
theorem arithmeticWindow_geometric_input_width {d m n k q g : ℕ} {u s₁ s₂ : ℝ}
    (hd : 0 < d) (hkm : k ≤ m) (hq : 1 ≤ q)
    (hw : ArithmeticWindow d m n k q g u s₁ s₂) :
    8 * Real.sqrt ((k : ℝ) * d) ≤ s₁ / Real.sqrt d := by
  have hl : 8 * d * Real.sqrt m ≤ s₁ :=
    (modularWidthFloor_lower d m n hq).trans (arithmeticWindow_first_lower hw).1
  have he : 8 * Real.sqrt ((k : ℝ) * d) * Real.sqrt d = 8 * d * Real.sqrt k := by
    rw [Real.sqrt_mul (Nat.cast_nonneg k)]
    calc
      _ = 8 * Real.sqrt k * (Real.sqrt d) ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt (Nat.cast_nonneg d)]; ring
  apply (le_div_iff₀ (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hd))).mpr
  rw [he]
  exact (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by exact_mod_cast hkm))
    (by positivity)).trans hl

/-- The same window also implies the constant-width theorem's input width. -/
theorem arithmeticWindow_constant_input_width {d m n k q g : ℕ} {u s₁ s₂ : ℝ}
    (hd : 0 < d) (hk : 0 < k) (hkm : k ≤ m) (hq : 1 ≤ q)
    (hw : ArithmeticWindow d m n k q g u s₁ s₂) : Real.sqrt d ≤ s₁ := by
  have hroot : 1 ≤ Real.sqrt ((k : ℝ) * d) := by
    apply Real.one_le_sqrt.mpr
    have hkd : 1 ≤ k * d := Nat.mul_pos hk hd
    exact_mod_cast hkd
  have hσ : 1 ≤ s₁ / Real.sqrt d :=
    (by linarith : (1 : ℝ) ≤ 8 * Real.sqrt ((k : ℝ) * d)).trans
      (arithmeticWindow_geometric_input_width hd hkm hq hw)
  exact (one_le_div (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hd))).mp hσ

end SISToKSIS

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Module NumberField GeometricGaussianLHL
namespace SISToKSIS
variable (K : Type*) [Field K] [NumberField K] {d m k : ℕ}

/-- Column accuracy is specified on the spectral event, independently of the
geometric event used to prove leftover hashing. The generic interface separates
this property from the implementation; the stored sampler below proves it. -/
def SpectralSamplerAccuracy (b : Basis (Fin d) ℤ (𝓞 K)) (hk : 0 < k)
    (s₁ : ℝ) {s₂ : ℝ} (hs₂ : 0 < s₂)
    (sampler : Matrix (Fin k) (Fin m) (𝓞 K) → Fin k → PMF (Fin m → 𝓞 K)) (εs : ℝ) : Prop :=
  ∀ X ∈ hintSpectralEvent K b s₁, ∀ hX : Function.Surjective X.mulVec, ∀ j,
    discreteTotalVariation (sampler X j)
      (numberFieldEllipsoidalGaussian K b m (canonicalGramShapingShape K b X hX hk s₂ hs₂) 0) ≤ εs

theorem SpectralSamplerAccuracy.on_event
    (b : Basis (Fin d) ℤ (𝓞 K)) (hk : 0 < k)
    {s₁ s₂ εs : ℝ} (hs₂ : 0 < s₂)
    (sampler : Matrix (Fin k) (Fin m) (𝓞 K) → Fin k → PMF (Fin m → 𝓞 K))
    (haccuracy : SpectralSamplerAccuracy K b hk s₁ hs₂ sampler εs)
    (G : Set (Matrix (Fin k) (Fin m) (𝓞 K)))
    (hsurj : ∀ X ∈ G, Function.Surjective X.mulVec) :
    ∀ X ∈ G ∩ hintSpectralEvent K b s₁, ∀ j,
      discreteTotalVariation (sampler X j)
        (numberFieldEllipsoidalGaussian K b m
          (traceAverageHintEventShape K b hk (G ∩ hintSpectralEvent K b s₁)
            (fun X hX => hsurj X hX.1) hs₂ X) 0) ≤ εs := by
  intro X hX j
  rw [traceAverageHintEventShape_of_mem K b hk _ _ hs₂ X hX]
  exact haccuracy X hX.2 (hsurj X hX.1) j

section PowerTwo
variable {a : ℕ} [IsCyclotomicExtension {2 ^ (a + 1)} ℚ K] {ζ : K}

theorem powerTwo_polynomial_hint_generator_bounds
    (hζ : IsPrimitiveRoot ζ (2 ^ (a + 1)))
    (hk : 0 < k) (hkm : k < m) {ell s₁ s₂ δsp δop εs : ℝ}
    (hell : 1 ≤ ell) (hs₁ : 0 < s₁) (hs : s₁ ≤ s₂)
    (hwidthX : 8 * Real.sqrt (k * (2 ^ (a + 1)).totient) ≤
      s₁ / basisAlpha K (cyclotomicIntegralBasis K hζ))
    (hbudget : ((k * (2 ^ (a + 1)).totient : ℕ) : ℝ) *
      Real.log (numberFieldPolynomialScale K (cyclotomicIntegralBasis K hζ) k m s₁ ell) +
      2 * Real.log (1 / realSecurityError (ell + 4)) ≤ (m : ℝ) * Real.log (8 / 7))
    (hδsp : 0 < δsp) (hδspone : δsp < 1)
    (hcols : lowerSpectralColumnConstant *
      ((k : ℝ) + Real.log (2 * (2 ^ (a + 1)).totient / δsp)) ≤ m)
    (hδop : 0 < δop) (hδopone : δop < 1)
    (hlogop : Real.log (2 * (2 ^ (a + 1)).totient / δop) ≤ m) (hεs : 0 ≤ εs)
    (hwidth : numberFieldPolynomialSmoothingBound K (cyclotomicIntegralBasis K hζ) k m ell *
      (4 * s₁ * Real.sqrt m) ≤ s₂)
    (sampler : Matrix (Fin k) (Fin m) (𝓞 K) → Fin k → PMF (Fin m → 𝓞 K))
    (haccuracy : SpectralSamplerAccuracy K (cyclotomicIntegralBasis K hζ) hk s₁
      (hs₁.trans_le hs) sampler εs) :
    HintGeneratorBounds K (cyclotomicIntegralBasis K hζ)
      (numberFieldMatrixLaw K (cyclotomicIntegralBasis K hζ) k m s₁ hs₁.ne')
      (hs₁.trans_le hs) sampler
      (hintDistributionError k (3 * realSecurityError (ell + 4)) δsp
        (2 * realSecurityError (ell + 4)) εs)
      (hintNormFailure k (3 * realSecurityError (ell + 4)) δsp δop εs) := by
  let b := cyclotomicIntegralBasis K hζ
  let d := (2 ^ (a + 1)).totient
  have hd := integralBasis_dimension_pos K b
  let : Nonempty (Fin (k * d)) := ⟨⟨0, Nat.mul_pos hk hd⟩⟩
  have hm : 1 ≤ m := by omega
  have hB := (numberFieldPolynomialSpherical_parameters_pos K b 0
    (cyclotomicIntegralBasis_one K hζ 0 rfl) hk hm hell hs₁).1
  have hδ := realSecurityError_pos (ell + 4)
  have hsmall := real_polynomial_failureBudget_le hell
  have hσ : 1 ≤ s₁ / Real.sqrt d := by
    have hkd : (1 : ℝ) ≤ (k * d : ℕ) := by exact_mod_cast Nat.mul_pos hk hd
    have hroot := Real.one_le_sqrt.mpr hkd
    have hα := (powerTwoBasis_constants K hζ).1
    rw [hα] at hwidthX
    exact (by linarith : (1 : ℝ) ≤ 8 * Real.sqrt (k * d : ℕ)).trans
      (by simpa only [Nat.cast_mul] using hwidthX)
  obtain ⟨G, hG, hgood⟩ := numberField_polynomial_spherical_event K b 0
    (cyclotomicIntegralBasis_one K hζ 0 rfl) hk hkm hell hs₁ hwidthX hbudget
  let hsurj := fun X (hX : X ∈ G) => (hgood X hX).1
  exact powerTwo_hint_generator_bounds K hζ hk hs₁ hs hσ hδsp hδspone hcols
    hδop hδopone hlogop (by positivity) (by linarith) hεs hB.le hwidth G hsurj hG
    (fun X hX => (hgood X hX).2.1) sampler
    (haccuracy.on_event K b hk (hs₁.trans_le hs) sampler G hsurj)

theorem powerTwo_constant_hint_generator_bounds
    (hζ : IsPrimitiveRoot ζ (2 ^ (a + 1)))
    (hk : 0 < k) (hkm : k < m) {ell s₁ s₂ δsp δop εs : ℝ}
    (hell : 1 ≤ ell) (hs₁ : 0 < s₁) (hs : s₁ ≤ s₂)
    (hwidthX : Real.sqrt (2 ^ (a + 1)).totient ≤ s₁)
    (hbudget : ((k * (2 ^ (a + 1)).totient : ℕ) : ℝ) *
      Real.log (powerTwoConstantScale (2 ^ (a + 1)).totient k m s₁ ell) +
      2 * Real.log (1 / realSecurityError (ell + 6)) ≤ (m : ℝ) * Real.log (50 / 49))
    (hδsp : 0 < δsp) (hδspone : δsp < 1)
    (hcols : lowerSpectralColumnConstant *
      ((k : ℝ) + Real.log (2 * (2 ^ (a + 1)).totient / δsp)) ≤ m)
    (hδop : 0 < δop) (hδopone : δop < 1)
    (hlogop : Real.log (2 * (2 ^ (a + 1)).totient / δop) ≤ m) (hεs : 0 ≤ εs)
    (hwidth : powerTwoConstantSmoothingBound (2 ^ (a + 1)).totient k m ell *
      (4 * s₁ * Real.sqrt m) ≤ s₂)
    (sampler : Matrix (Fin k) (Fin m) (𝓞 K) → Fin k → PMF (Fin m → 𝓞 K))
    (haccuracy : SpectralSamplerAccuracy K (cyclotomicIntegralBasis K hζ) hk s₁
      (hs₁.trans_le hs) sampler εs) :
    HintGeneratorBounds K (cyclotomicIntegralBasis K hζ)
      (numberFieldMatrixLaw K (cyclotomicIntegralBasis K hζ) k m s₁ hs₁.ne')
      (hs₁.trans_le hs) sampler
      (hintDistributionError k (3 * realSecurityError (ell + 6)) δsp
        (2 * realSecurityError (ell + 6)) εs)
      (hintNormFailure k (3 * realSecurityError (ell + 6)) δsp δop εs) := by
  let b := cyclotomicIntegralBasis K hζ
  let d := (2 ^ (a + 1)).totient
  have hd := integralBasis_dimension_pos K b
  let : Nonempty (Fin (k * d)) := ⟨⟨0, Nat.mul_pos hk hd⟩⟩
  have hm : 1 ≤ m := by omega
  have hB := (powerTwoConstantSpherical_parameters_pos hd hk hm hell hs₁).1
  have hδ := realSecurityError_pos (ell + 6)
  have hsmall := real_constant_failureBudget_le hell
  have hσ : 1 ≤ s₁ / Real.sqrt d :=
    (one_le_div (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hd))).mpr hwidthX
  obtain ⟨G, hG, hgood⟩ := numberField_constantWidth_spherical_event K hζ
    hk hkm hell hs₁ hwidthX hbudget
  let hsurj := fun X (hX : X ∈ G) => (hgood X hX).1
  exact powerTwo_hint_generator_bounds K hζ hk hs₁ hs hσ hδsp hδspone hcols
    hδop hδopone hlogop (by positivity) (by linarith) hεs hB.le hwidth G hsurj hG
    (fun X hX => (hgood X hX).2.1) sampler
    (haccuracy.on_event K b hk (hs₁.trans_le hs) sampler G hsurj)

end PowerTwo
end SISToKSIS

open Module NumberField GeometricGaussianLHL
namespace SISToKSIS
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable (K : Type*) [Field K] [NumberField K] {d : ℕ}

/-- Interpretation of stored sampled coefficients through the supplied integral
basis. All executable sampling occurs on finite integer vectors. -/
def finiteInitialMatrixLaw (basis : Basis (Fin d) ℤ (𝓞 K)) (a b r m s : ℕ) :
    PMF (Matrix (Fin r) (Fin m) (𝓞 K)) :=
  (initialGaussianRunLaw a b d r m s).map (matrixColumnCoordinates K basis r m).symm

theorem numberFieldMatrix_product_of_diagonal (basis : Basis (Fin d) ℤ (𝓞 K))
    {c : ℝ} (hc : 0 < c)
    (hGram : ∀ i j, canonicalGram K basis i j = if i = j then c else 0)
    (r m : ℕ) {width : ℝ} (hw : 0 < width) :
    (numberFieldMatrixLaw K basis r m width hw.ne').map (matrixColumnCoordinates K basis r m) =
      coefficientColumnLaw (r * d) m (width / Real.sqrt c) (div_pos hw (Real.sqrt_pos.mpr hc)) := by
  have h := numberFieldGaussian_product_of_diagonal K basis hc hGram r hw
  rw [numberFieldGaussian_coordinate_law] at h
  rw [numberFieldMatrixLaw_coordinate_law]
  simp only [ellipsoidalColumnLaw, coefficientColumnLaw, h]

/-- Full initial-matrix accuracy for a finite encoded rational canonical width. -/
theorem finiteInitialMatrixLaw_error (basis : Basis (Fin d) ℤ (𝓞 K))
    (hGram : ∀ i j, canonicalGram K basis i j = if i = j then (d : ℝ) else 0)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hwidth : Real.sqrt d ≤ (a : ℝ) / b) (r m s : ℕ) :
    discreteTotalVariation (finiteInitialMatrixLaw K basis a b r m s)
      (numberFieldMatrixLaw K basis r m ((a : ℝ) / b)
        (div_pos (Nat.cast_pos.mpr ha) (Nat.cast_pos.mpr hb)).ne') ≤ (1 / 2 : ℝ) ^ s := by
  have hd := integralBasis_dimension_pos K basis
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hcoords := numberFieldMatrix_product_of_diagonal K basis hdR hGram r m
    (div_pos (Nat.cast_pos.mpr ha) (Nat.cast_pos.mpr hb))
  have htarget : (coefficientColumnLaw (r * d) m ((a : ℝ) / b / Real.sqrt d)
      (div_pos (div_pos (Nat.cast_pos.mpr ha) (Nat.cast_pos.mpr hb)) (Real.sqrt_pos.mpr hdR))).map
      (matrixColumnCoordinates K basis r m).symm =
      numberFieldMatrixLaw K basis r m ((a : ℝ) / b)
        (div_pos (Nat.cast_pos.mpr ha) (Nat.cast_pos.mpr hb)).ne' := by
    rw [← hcoords, PMF.map_comp]
    simp only [Function.comp_def, Equiv.symm_apply_apply]
    exact PMF.map_id _
  rw [← htarget]
  exact (discreteTotalVariation_map_le _ _ _).trans
    (initialGaussianRunLaw_error ha hb hd hwidth r m s)

/-- The scalar width requirement follows from the supplied arithmetic window. -/
theorem finiteInitialMatrixLaw_error_of_window (basis : Basis (Fin d) ℤ (𝓞 K))
    (hGram : ∀ i j, canonicalGram K basis i j = if i = j then (d : ℝ) else 0)
    {a b m n k q g : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hk : 0 < k) (hkm : k ≤ m) (hq : 1 ≤ q) {u s₂ : ℝ}
    (hw : ArithmeticWindow d m n k q g u ((a : ℝ) / b) s₂) (s : ℕ) :
    discreteTotalVariation (finiteInitialMatrixLaw K basis a b k m s)
      (numberFieldMatrixLaw K basis k m ((a : ℝ) / b)
        (div_pos (Nat.cast_pos.mpr ha) (Nat.cast_pos.mpr hb)).ne') ≤ (1 / 2 : ℝ) ^ s :=
  finiteInitialMatrixLaw_error K basis hGram ha hb
    (arithmeticWindow_constant_input_width (integralBasis_dimension_pos K basis) hk hkm hq hw) k m s

end
end SISToKSIS


open Module NumberField GeometricGaussianLHL Matrix
open scoped MatrixOrder
namespace SISToKSIS
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable (K : Type*) [Field K] [NumberField K] {d : ℕ}

theorem canonicalGramPowerRoot_symm_scalar (b : Basis (Fin d) ℤ (𝓞 K)) {c : ℝ}
    (hc : 0 < c) (hGram : ∀ i j, canonicalGram K b i j = if i = j then c else 0)
    (n : ℕ) (x : Euclidean (n * d)) :
    (canonicalGramPowerRoot K b n).symm x = (Real.sqrt c)⁻¹ • x := by
  apply (canonicalGramPowerRoot K b n).injective
  rw [ContinuousLinearEquiv.apply_symm_apply, canonicalGramPowerRoot_scalar K b hc hGram,
    smul_smul, mul_inv_cancel₀ (Real.sqrt_pos.mpr hc).ne', one_smul]

theorem canonicalGramNormalizedMatrix_scalar (b : Basis (Fin d) ℤ (𝓞 K)) {c : ℝ}
    (hc : 0 < c) (hGram : ∀ i j, canonicalGram K b i j = if i = j then c else 0)
    {k m : ℕ} (X : Matrix (Fin k) (Fin m) (𝓞 K)) :
    canonicalGramNormalizedMatrix K b X = (ringCoefficientMatrix b X).map (Int.cast : ℤ → ℝ) := by
  apply Matrix.toEuclideanLin.injective
  rw [canonicalGramNormalizedMatrix_operator]
  ext x : 1
  change canonicalGramPowerRoot K b k
    (realCoefficientMap (ringCoefficientMatrix b X) ((canonicalGramPowerRoot K b m).symm x)) =
      realCoefficientMap (ringCoefficientMatrix b X) x
  rw [canonicalGramPowerRoot_scalar K b hc hGram, canonicalGramPowerRoot_symm_scalar K b hc hGram,
    map_smul, smul_smul, mul_inv_cancel₀ (Real.sqrt_pos.mpr hc).ne', one_smul]

theorem canonicalGramNormalizedMatrix_rational (b : Basis (Fin d) ℤ (𝓞 K)) {c : ℝ}
    (hc : 0 < c) (hGram : ∀ i j, canonicalGram K b i j = if i = j then c else 0)
    {k m : ℕ} (X : Matrix (Fin k) (Fin m) (𝓞 K))
    (Q : RationalRectData (k * d) (m * d))
    (hQ : rationalRectMatrixOfData Q = integerRationalMatrix (ringCoefficientMatrix b X)) :
    canonicalGramNormalizedMatrix K b X = (rationalRectMatrixOfData Q).map (Rat.castHom ℝ) := by
  rw [canonicalGramNormalizedMatrix_scalar K b hc hGram, hQ]
  ext i j
  simp [integerRationalMatrix]

/-- In a scalar-Gram basis the parent's rational constructor has exactly the canonical target. -/
theorem canonicalGramShapingShape_rational_map (b : Basis (Fin d) ℤ (𝓞 K)) {c : ℝ}
    (hc : 0 < c) (hGram : ∀ i j, canonicalGram K b i j = if i = j then c else 0)
    {k m : ℕ} (X : Matrix (Fin k) (Fin m) (𝓞 K))
    (hX : Function.Surjective X.mulVec) (hk : 0 < k) (w : ℚ) (hw : 0 < w)
    (Q : RationalRectData (k * d) (m * d))
    (hQ : rationalRectMatrixOfData Q = integerRationalMatrix (ringCoefficientMatrix b X)) :
    (canonicalGramShapingShape K b X hX hk (w : ℝ) (by exact_mod_cast hw)).toContinuousLinearMap =
      isometricTransportMap (canonicalGramEuclideanIsometry K b m) (canonicalGramEuclideanIsometry K b m)
        (Matrix.toEuclideanLin (rationalShapingSquareRootMatrix (rationalRectMatrixOfData Q) w)).toContinuousLinearMap := by
  have hunit : IsUnit (rationalRectMatrixOfData Q * (rationalRectMatrixOfData Q).transpose).det := by
    rw [hQ]
    exact ringCoefficientMatrix_rational_gram_isUnit K b X hX
  change isometricTransportMap (canonicalGramEuclideanIsometry K b m)
    (canonicalGramEuclideanIsometry K b m) (Matrix.toEuclideanLin
    (CFC.sqrt (realShapingCovarianceMatrix (canonicalGramNormalizedMatrix K b X) (w : ℝ)))).toContinuousLinearMap = _
  rw [canonicalGramNormalizedMatrix_rational K b hc hGram X Q hQ,
    realShapingCovarianceMatrix_rat _ w hunit]
  rfl

theorem rationalHintShape_accuracy (b : Basis (Fin d) ℤ (𝓞 K))
    (hGram : ∀ i j, canonicalGram K b i j = if i = j then (d : ℝ) else 0)
    {k m : ℕ} (X : Matrix (Fin k) (Fin m) (𝓞 K))
    (hX : Function.Surjective X.mulVec) (hk : 0 < k) (w : ℚ) (hw : 0 < w)
    (Q : RationalRectData (k * d) (m * d))
    (hQ : rationalRectMatrixOfData Q = integerRationalMatrix (ringCoefficientMatrix b X)) (t : ℕ) :
    let R := (costedRationalShapingApprox t Q w).value
    ∃ hR : ((rationalMatrixOfData R).map (fun q : ℚ => (q : ℝ))).PosDef,
      ‖(canonicalComputedShape K b _ hR).toContinuousLinearMap -
        (canonicalGramShapingShape K b X hX hk (w : ℝ) (by exact_mod_cast hw)).toContinuousLinearMap‖ ≤
          1 / (2 : ℝ) ^ t := by
  have hd := integralBasis_dimension_pos K b
  have hunit : IsUnit (rationalRectMatrixOfData Q * (rationalRectMatrixOfData Q).transpose).det := by
    rw [hQ]
    exact ringCoefficientMatrix_rational_gram_isUnit K b X hX
  have hR := costedRationalShapingApprox_posDef t Q w (Nat.mul_pos hk hd) hunit hw.ne'
  refine ⟨hR, ?_⟩
  rw [canonicalComputedShape_map, canonicalGramShapingShape_rational_map K b
    (by exact_mod_cast hd : (0 : ℝ) < d) hGram X hX hk w hw Q hQ,
    ← isometricTransportMap_sub, isometricTransportMap_norm]
  exact costedRationalShapingApprox_operator_error t Q w (Nat.mul_pos hk hd) hunit hw.ne'

/-- Shape and scalar sampling precisions for per-column error `2^-p`. -/
def hintShapingBits (N p : ℕ) : ℕ := gaussianShapeBits N 0 (p + 1)

theorem hintShapingBits_precision (N p : ℕ) {η : ℝ} (hη : η ≤ 1) :
    3 * (η * (1 / (2 : ℝ) ^ hintShapingBits N p)) ≤
      gaussianTargetPrecision N ((1 / 2 : ℝ) ^ p / 2) := by
  have h := gaussianShapeBits_precision N 0 (p + 1) (by simpa using hη)
  simpa [hintShapingBits, _root_.one_div_pow, pow_succ, div_eq_mul_inv, mul_comm] using h

theorem hintSamplingBits_precision (p : ℕ) :
    (1 / 2 : ℝ) ^ (p + 2) ≤ (1 / 2 : ℝ) ^ p / 4 := by
  rw [pow_add]
  norm_num
  exact le_of_eq (by ring)


theorem sampling_radius_ge_half {N : ℕ} (hN : 2 ≤ N) {ε C : ℝ}
    (hε : 0 < ε) (hεone : ε ≤ 1) (hC : 1 ≤ C) :
    1 / 2 ≤ C * Real.sqrt (Real.log ((N : ℝ) / ε)) := by
  have hquot : (2 : ℝ) ≤ N / ε := by
    apply (le_div_iff₀ hε).mpr
    have hn : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hquot
  have hlpos : 0 ≤ Real.log ((N : ℝ) / ε) := by linarith [Real.log_two_gt_d9]
  have hroot := Real.sq_sqrt hlpos
  have hrootpos := Real.sqrt_nonneg (Real.log ((N : ℝ) / ε))
  have hh : 1 / 2 ≤ Real.sqrt (Real.log ((N : ℝ) / ε)) := by
    nlinarith [Real.log_two_gt_d9]
  exact hh.trans (le_mul_of_one_le_left hrootpos hC)

def rationalHintSampleLaw (b : Basis (Fin d) ℤ (𝓞 K)) {k m : ℕ}
    (Q : RationalRectData (k * d) (m * d)) (w : ℚ) (p : ℕ) : PMF (Fin m → 𝓞 K) :=
  computedNumberFieldSampleLaw K b m
    (costedRationalShapingApprox (hintShapingBits (m * d) p) Q w).value (p + 2)

/-- The supplied paper window discharges the shape, width and sampling precision premises. -/
theorem rationalHintSampleLaw_error (b : Basis (Fin d) ℤ (𝓞 K))
    (hGram : ∀ i j, canonicalGram K b i j = if i = j then (d : ℝ) else 0)
    {k m : ℕ} (hN : 2 ≤ m * d) (hk : 0 < k) (X : Matrix (Fin k) (Fin m) (𝓞 K))
    (hX : Function.Surjective X.mulVec) (w : ℚ) (hw : 0 < w)
    (Q : RationalRectData (k * d) (m * d))
    (hQ : rationalRectMatrixOfData Q = integerRationalMatrix (ringCoefficientMatrix b X))
    (p : ℕ) {r B V : ℝ} (hr : 1 / 2 ≤ r)
    (hB : 4 * r * Real.sqrt (d : ℝ) ≤ B) (hwB : B * V ≤ (w : ℝ))
    (hnorm : ‖(canonicalEuclideanMatrix K b X).toContinuousLinearMap‖ ≤ V)
    (hlog : 4 * Real.log ((m * d : ℕ) / (1 / 2 : ℝ) ^ p) ≤ 4 * r ^ 2) :
    discreteTotalVariation (rationalHintSampleLaw K b Q w p)
      (numberFieldEllipsoidalGaussian K b m
        (canonicalGramShapingShape K b X hX hk (w : ℝ) (by exact_mod_cast hw)) 0) ≤
          (1 / 2 : ℝ) ^ p := by
  let t := hintShapingBits (m * d) p
  have hd := integralBasis_dimension_pos K b
  have hm : 0 < m := by nlinarith
  have hwreal : (0 : ℝ) < w := by exact_mod_cast hw
  have hrpos : 0 < r := by linarith
  have hdreal : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hroot : 1 ≤ Real.sqrt (d : ℝ) := (Real.one_le_sqrt).mpr hdreal
  have hmargin : 1 ≤ 2 * r * Real.sqrt (d : ℝ) := by nlinarith
  have hBpos : 1 ≤ B := by nlinarith
  obtain ⟨hR, herror⟩ := rationalHintShape_accuracy K b hGram X hX hk w hw Q hQ t
  have hδ : 1 / (2 : ℝ) ^ t ≤ 2 * r * Real.sqrt (d : ℝ) :=
    ((div_le_one (by positivity : (0 : ℝ) < 2 ^ t)).mpr (one_le_pow₀ (by norm_num))).trans hmargin
  have hwidth := canonicalComputedShape_width_of_paper_window K b hm hk X hX
    hwreal hrpos hB hwB hnorm _ hR herror hδ
  have hη : ‖(canonicalEuclideanMatrix K b X).toContinuousLinearMap‖ / (w : ℝ) ≤ 1 := by
    apply (div_le_one hwreal).mpr
    calc
      _ ≤ B * ‖(canonicalEuclideanMatrix K b X).toContinuousLinearMap‖ :=
        le_mul_of_one_le_left (norm_nonneg _) hBpos
      _ ≤ B * V := mul_le_mul_of_nonneg_left hnorm (by linarith)
      _ ≤ _ := hwB
  exact computedNumberFieldSampleLaw_traceAverage_error K b hGram hN X hX hk hwreal _ hR
    hrpos.le (by positivity) (pow_le_one₀ (by norm_num) (by norm_num)) (by positivity)
    hwidth hlog herror (hintShapingBits_precision (m * d) p hη) (p + 2) (hintSamplingBits_precision p)

theorem rationalHintSampleLaw_error_paper_radius (b : Basis (Fin d) ℤ (𝓞 K))
    (hGram : ∀ i j, canonicalGram K b i j = if i = j then (d : ℝ) else 0)
    {k m : ℕ} (hN : 2 ≤ m * d) (hk : 0 < k) (X : Matrix (Fin k) (Fin m) (𝓞 K))
    (hX : Function.Surjective X.mulVec) (w : ℚ) (hw : 0 < w)
    (Q : RationalRectData (k * d) (m * d))
    (hQ : rationalRectMatrixOfData Q = integerRationalMatrix (ringCoefficientMatrix b X))
    (p : ℕ) {C B V : ℝ} (hC : 1 ≤ C)
    (hB : 4 * (C * Real.sqrt (Real.log ((m * d : ℕ) / (1 / 2 : ℝ) ^ p))) * Real.sqrt (d : ℝ) ≤ B)
    (hwB : B * V ≤ (w : ℝ))
    (hnorm : ‖(canonicalEuclideanMatrix K b X).toContinuousLinearMap‖ ≤ V) :
    discreteTotalVariation (rationalHintSampleLaw K b Q w p)
      (numberFieldEllipsoidalGaussian K b m
        (canonicalGramShapingShape K b X hX hk (w : ℝ) (by exact_mod_cast hw)) 0) ≤
          (1 / 2 : ℝ) ^ p :=
  rationalHintSampleLaw_error K b hGram hN hk X hX w hw Q hQ p
    (sampling_radius_ge_half hN (by positivity) (pow_le_one₀ (by norm_num) (by norm_num)) hC)
    hB hwB hnorm
    (sampling_radius_log_budget hN (by positivity) (pow_le_one₀ (by norm_num) (by norm_num)) hC)

/-- Number-field interpretation of the stored, rank-checked column sampler. -/
def guardedNumberFieldHintLaw (b : Basis (Fin d) ℤ (𝓞 K)) {k m : ℕ}
    (Q : RationalRectData (k * d) (m * d)) (w : ℚ) (p : ℕ) : PMF (Fin m → 𝓞 K) :=
  (guardedHintColumnLaw d (hintShapingBits (m * d) p) (p + 2) Q w).map (ringPowerCoordinates b m).symm

omit [NumberField K] in
theorem guardedNumberFieldHintLaw_eq (b : Basis (Fin d) ℤ (𝓞 K)) {k m : ℕ}
    (Q : RationalRectData (k * d) (m * d)) (w : ℚ) (p : ℕ) :
    guardedNumberFieldHintLaw K b Q w p = computedNumberFieldSampleLaw K b m
      (guardedRationalShapeRun (hintShapingBits (m * d) p) Q w).value (p + 2) := rfl

omit [NumberField K] in
theorem guardedNumberFieldHintLaw_fullRank (b : Basis (Fin d) ℤ (𝓞 K)) {k m : ℕ}
    (Q : RationalRectData (k * d) (m * d)) (w : ℚ) (p : ℕ)
    (hQ : IsUnit (rationalRectMatrixOfData Q * (rationalRectMatrixOfData Q).transpose).det) :
    guardedNumberFieldHintLaw K b Q w p = rationalHintSampleLaw K b Q w p := by
  rw [guardedNumberFieldHintLaw_eq, guardedRationalShapeRun_value_of_fullRank _ Q w hQ]
  rfl

theorem guardedNumberFieldHintLaw_error (b : Basis (Fin d) ℤ (𝓞 K))
    (hGram : ∀ i j, canonicalGram K b i j = if i = j then (d : ℝ) else 0)
    {k m : ℕ} (hN : 2 ≤ m * d) (hk : 0 < k) (X : Matrix (Fin k) (Fin m) (𝓞 K))
    (hX : Function.Surjective X.mulVec) (w : ℚ) (hw : 0 < w)
    (Q : RationalRectData (k * d) (m * d))
    (hQ : rationalRectMatrixOfData Q = integerRationalMatrix (ringCoefficientMatrix b X))
    (p : ℕ) {C B V : ℝ} (hC : 1 ≤ C)
    (hB : 4 * (C * Real.sqrt (Real.log ((m * d : ℕ) / (1 / 2 : ℝ) ^ p))) * Real.sqrt (d : ℝ) ≤ B)
    (hwB : B * V ≤ (w : ℝ))
    (hnorm : ‖(canonicalEuclideanMatrix K b X).toContinuousLinearMap‖ ≤ V) :
    discreteTotalVariation (guardedNumberFieldHintLaw K b Q w p)
      (numberFieldEllipsoidalGaussian K b m
        (canonicalGramShapingShape K b X hX hk (w : ℝ) (by exact_mod_cast hw)) 0) ≤
          (1 / 2 : ℝ) ^ p := by
  have hunit : IsUnit (rationalRectMatrixOfData Q * (rationalRectMatrixOfData Q).transpose).det := by
    rw [hQ]
    exact ringCoefficientMatrix_rational_gram_isUnit K b X hX
  rw [guardedNumberFieldHintLaw_fullRank K b Q w p hunit]
  exact rationalHintSampleLaw_error_paper_radius K b hGram hN hk X hX w hw Q hQ p hC hB hwB hnorm

def storedSpectralHintSampler (b : Basis (Fin d) ℤ (𝓞 K)) {k m : ℕ}
    (Q : Matrix (Fin k) (Fin m) (𝓞 K) → RationalRectData (k * d) (m * d)) (w : ℚ) (p : ℕ) :
    Matrix (Fin k) (Fin m) (𝓞 K) → Fin k → PMF (Fin m → 𝓞 K) :=
  fun X _ => guardedNumberFieldHintLaw K b (Q X) w p

/-- Discharge column-sampler accuracy from the finite algorithm and the paper's parameter window. -/
theorem storedSpectralHintSampler_accuracy (b : Basis (Fin d) ℤ (𝓞 K))
    (hGram : ∀ i j, canonicalGram K b i j = if i = j then (d : ℝ) else 0)
    {k m : ℕ} (hN : 2 ≤ m * d) (hk : 0 < k)
    (Q : Matrix (Fin k) (Fin m) (𝓞 K) → RationalRectData (k * d) (m * d))
    (hQ : ∀ X, rationalRectMatrixOfData (Q X) = integerRationalMatrix (ringCoefficientMatrix b X))
    (w : ℚ) (hw : 0 < w) (p : ℕ) {s₁ C B : ℝ} (hs₁ : 0 ≤ s₁) (hC : 1 ≤ C)
    (hB : 4 * (C * Real.sqrt (Real.log ((m * d : ℕ) / (1 / 2 : ℝ) ^ p))) * Real.sqrt (d : ℝ) ≤ B)
    (hwB : B * (4 * s₁ * Real.sqrt m) ≤ (w : ℝ)) :
    SpectralSamplerAccuracy K b hk s₁ (by exact_mod_cast hw : (0 : ℝ) < w)
      (storedSpectralHintSampler K b Q w p) ((1 / 2 : ℝ) ^ p) := by
  intro X hsp hX j
  exact guardedNumberFieldHintLaw_error K b hGram hN hk X hX w hw (Q X) (hQ X) p hC hB hwB
    (hintSpectralEvent_canonical_upper K b hs₁ X hsp)

/-- A requested error need not be dyadic: the supplied bit precision only has to dominate it. -/
theorem guardedNumberFieldHintLaw_error_of_budget (b : Basis (Fin d) ℤ (𝓞 K))
    (hGram : ∀ i j, canonicalGram K b i j = if i = j then (d : ℝ) else 0)
    {k m : ℕ} (hN : 2 ≤ m * d) (hk : 0 < k) (X : Matrix (Fin k) (Fin m) (𝓞 K))
    (hX : Function.Surjective X.mulVec) (w : ℚ) (hw : 0 < w)
    (Q : RationalRectData (k * d) (m * d))
    (hQ : rationalRectMatrixOfData Q = integerRationalMatrix (ringCoefficientMatrix b X))
    (p : ℕ) {ε C B V : ℝ} (hε : 0 < ε) (hεone : ε ≤ 1) (hprec : (1 / 2 : ℝ) ^ p ≤ ε)
    (hC : 1 ≤ C)
    (hB : 4 * (C * Real.sqrt (Real.log ((m * d : ℕ) / ε))) * Real.sqrt (d : ℝ) ≤ B)
    (hwB : B * V ≤ (w : ℝ))
    (hnorm : ‖(canonicalEuclideanMatrix K b X).toContinuousLinearMap‖ ≤ V) :
    discreteTotalVariation (guardedNumberFieldHintLaw K b Q w p)
      (numberFieldEllipsoidalGaussian K b m
        (canonicalGramShapingShape K b X hX hk (w : ℝ) (by exact_mod_cast hw)) 0) ≤ ε := by
  let t := hintShapingBits (m * d) p
  let r := C * Real.sqrt (Real.log ((m * d : ℕ) / ε))
  have hr : 1 / 2 ≤ r := sampling_radius_ge_half hN hε hεone hC
  have hd := integralBasis_dimension_pos K b
  have hm : 0 < m := by nlinarith
  have hwreal : (0 : ℝ) < w := by exact_mod_cast hw
  have hrpos : 0 < r := by linarith
  have hdreal : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hroot : 1 ≤ Real.sqrt (d : ℝ) := Real.one_le_sqrt.mpr hdreal
  have hmargin : 1 ≤ 2 * r * Real.sqrt (d : ℝ) := by nlinarith
  have hBpos : 1 ≤ B := by change 4 * r * Real.sqrt (d : ℝ) ≤ B at hB; nlinarith
  have hunit : IsUnit (rationalRectMatrixOfData Q * (rationalRectMatrixOfData Q).transpose).det := by
    rw [hQ]
    exact ringCoefficientMatrix_rational_gram_isUnit K b X hX
  rw [guardedNumberFieldHintLaw_fullRank K b Q w p hunit]
  obtain ⟨hR, herror⟩ := rationalHintShape_accuracy K b hGram X hX hk w hw Q hQ t
  have hδ : 1 / (2 : ℝ) ^ t ≤ 2 * r * Real.sqrt (d : ℝ) :=
    ((div_le_one (by positivity : (0 : ℝ) < 2 ^ t)).mpr (one_le_pow₀ (by norm_num))).trans hmargin
  have hwidth := canonicalComputedShape_width_of_paper_window K b hm hk X hX
    hwreal hrpos hB hwB hnorm _ hR herror hδ
  have hη : ‖(canonicalEuclideanMatrix K b X).toContinuousLinearMap‖ / (w : ℝ) ≤ 1 := by
    apply (div_le_one hwreal).mpr
    calc
      _ ≤ B * ‖(canonicalEuclideanMatrix K b X).toContinuousLinearMap‖ :=
        le_mul_of_one_le_left (norm_nonneg _) hBpos
      _ ≤ B * V := mul_le_mul_of_nonneg_left hnorm (by linarith)
      _ ≤ _ := hwB
  have hbits : (1 / 2 : ℝ) ^ (p + 2) ≤ ε / 4 :=
    (hintSamplingBits_precision p).trans (by linarith)
  have hs := computedNumberFieldSampleLaw_error_of_width K b hGram m hN _ hR hrpos.le hε hεone
    hwidth (sampling_radius_log_budget hN hε hεone hC) (p + 2) hbits
  have hp := numberFieldEllipsoidalGaussian_shape_error K b
    (canonicalGramShapingShape K b X hX hk (w : ℝ) hwreal) (canonicalComputedShape K b _ hR) 0
    (by positivity : 0 ≤ 1 / (2 : ℝ) ^ t) (by positivity : 0 < (1 / 2 : ℝ) ^ p / 2)
    (by have h := pow_le_one₀ (n := p) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num); linarith)
    herror (by simpa only [canonicalGramShapingShape_inverse_norm] using hintShapingBits_precision (m * d) p hη)
  have ht := discreteTotalVariation_triangle
    (computedNumberFieldSampleLaw K b m (costedRationalShapingApprox t Q w).value (p + 2))
    (numberFieldEllipsoidalGaussian K b m (canonicalComputedShape K b _ hR) 0)
    (numberFieldEllipsoidalGaussian K b m (canonicalGramShapingShape K b X hX hk (w : ℝ) hwreal) 0)
  change discreteTotalVariation
    (computedNumberFieldSampleLaw K b m (costedRationalShapingApprox t Q w).value (p + 2)) _ ≤ ε
  linarith

theorem storedSpectralHintSampler_accuracy_of_budget (b : Basis (Fin d) ℤ (𝓞 K))
    (hGram : ∀ i j, canonicalGram K b i j = if i = j then (d : ℝ) else 0)
    {k m : ℕ} (hN : 2 ≤ m * d) (hk : 0 < k)
    (Q : Matrix (Fin k) (Fin m) (𝓞 K) → RationalRectData (k * d) (m * d))
    (hQ : ∀ X, rationalRectMatrixOfData (Q X) = integerRationalMatrix (ringCoefficientMatrix b X))
    (w : ℚ) (hw : 0 < w) (p : ℕ) {s₁ ε C B : ℝ}
    (hs₁ : 0 ≤ s₁) (hε : 0 < ε) (hεone : ε ≤ 1) (hprec : (1 / 2 : ℝ) ^ p ≤ ε) (hC : 1 ≤ C)
    (hB : 4 * (C * Real.sqrt (Real.log ((m * d : ℕ) / ε))) * Real.sqrt (d : ℝ) ≤ B)
    (hwB : B * (4 * s₁ * Real.sqrt m) ≤ (w : ℝ)) :
    SpectralSamplerAccuracy K b hk s₁ (by exact_mod_cast hw : (0 : ℝ) < w)
      (storedSpectralHintSampler K b Q w p) ε := by
  intro X hsp hX j
  exact guardedNumberFieldHintLaw_error_of_budget K b hGram hN hk X hX w hw (Q X) (hQ X) p
    hε hεone hprec hC hB hwB (hintSpectralEvent_canonical_upper K b hs₁ X hsp)

end
end SISToKSIS

namespace SISToKSIS
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

section StoredPowerTwo
variable {a k m : ℕ} [IsCyclotomicExtension {2 ^ (a + 1)} ℚ K] {ζ : K}

/-- The spectral hint generator uses the actual finite stored sampler, with no column-accuracy assumption. -/
theorem powerTwo_stored_hint_generator_bounds
    (hζ : IsPrimitiveRoot ζ (2 ^ (a + 1))) (hk : 0 < k)
    (hN : 2 ≤ m * (2 ^ (a + 1)).totient)
    (Q : Matrix (Fin k) (Fin m) (𝓞 K) →
      RationalRectData (k * (2 ^ (a + 1)).totient) (m * (2 ^ (a + 1)).totient))
    (hQ : ∀ X, rationalRectMatrixOfData (Q X) =
      integerRationalMatrix (ringCoefficientMatrix (cyclotomicIntegralBasis K hζ) X))
    (w : ℚ) (hw : 0 < w) (p : ℕ) {s₁ pB δsp δop ε εs B C : ℝ}
    (hs₁ : 0 < s₁) (hs : s₁ ≤ (w : ℝ))
    (hσ : 1 ≤ s₁ / Real.sqrt (2 ^ (a + 1)).totient)
    (hδsp : 0 < δsp) (hδspone : δsp < 1)
    (hcols : lowerSpectralColumnConstant *
      ((k : ℝ) + Real.log (2 * (2 ^ (a + 1)).totient / δsp)) ≤ m)
    (hδop : 0 < δop) (hδopone : δop < 1)
    (hlogop : Real.log (2 * (2 ^ (a + 1)).totient / δop) ≤ m)
    (hε : 0 < ε) (hεone : ε < 1)
    (hεs : 0 < εs) (hεsone : εs ≤ 1) (hprec : (1 / 2 : ℝ) ^ p ≤ εs) (hC : 1 ≤ C)
    (hB : 4 * (C * Real.sqrt (Real.log ((m * (2 ^ (a + 1)).totient : ℕ) / εs))) *
      Real.sqrt (2 ^ (a + 1)).totient ≤ B)
    (hwidth : B * (4 * s₁ * Real.sqrt m) ≤ (w : ℝ))
    (G : Set (Matrix (Fin k) (Fin m) (𝓞 K)))
    (hsurj : ∀ X ∈ G, Function.Surjective X.mulVec)
    (hG : ENNReal.ofReal (1 - pB) ≤
      (numberFieldMatrixLaw K (cyclotomicIntegralBasis K hζ) k m s₁ hs₁.ne').toOuterMeasure G)
    (hsmooth : ∀ X ∈ G, smoothingParameter (canonicalKernel K X) ε ≤ B) :
    HintGeneratorBounds K (cyclotomicIntegralBasis K hζ)
      (numberFieldMatrixLaw K (cyclotomicIntegralBasis K hζ) k m s₁ hs₁.ne')
      (by exact_mod_cast hw : (0 : ℝ) < w)
      (storedSpectralHintSampler K (cyclotomicIntegralBasis K hζ) Q w p)
      (hintDistributionError k pB δsp ε εs)
      (hintNormFailure k pB δsp δop εs) := by
  let b := cyclotomicIntegralBasis K hζ
  have hacc := storedSpectralHintSampler_accuracy_of_budget (k := k) (m := m)
    K b (powerTwoGram_diagonal K hζ) hN hk Q hQ w hw p
    hs₁.le hεs hεsone hprec hC hB hwidth
  have hCzero : 0 ≤ C := (by norm_num : (0 : ℝ) ≤ 1).trans hC
  have hBzero : 0 ≤ B := (mul_nonneg
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4)
      (mul_nonneg hCzero (Real.sqrt_nonneg _))) (Real.sqrt_nonneg _)).trans hB
  exact powerTwo_hint_generator_bounds (k := k) (m := m) K hζ hk hs₁ hs hσ hδsp hδspone hcols
    hδop hδopone hlogop hε hεone hεs.le hBzero hwidth G hsurj hG hsmooth
    (storedSpectralHintSampler K b Q w p)
    (SpectralSamplerAccuracy.on_event K b hk (hs₁.trans_le hs)
      (storedSpectralHintSampler K b Q w p) hacc G hsurj)

end StoredPowerTwo

end
end SISToKSIS

namespace SISToKSIS

section StoredBasisAccuracy
open NumberField
variable (K : Type*) [Field K] [NumberField K] {d k m : ℕ}
noncomputable section

/-- The sampler law attached to the supplied finite multiplication table. -/
def basisDataHintSampler (basis : Basis (Fin d) ℤ (𝓞 K))
    (T : BasisMultiplicationData d) (w : ℚ) (p : ℕ) :
    Matrix (Fin k) (Fin m) (𝓞 K) → Fin k → PMF (Fin m → 𝓞 K) :=
  storedSpectralHintSampler K basis
    (fun X => (storedRingCoefficientRun T (encodedRingMatrix basis X)).value) w p

theorem basisDataHintSampler_accuracy (basis : Basis (Fin d) ℤ (𝓞 K))
    (hGram : ∀ i j, canonicalGram K basis i j = if i = j then (d : ℝ) else 0)
    (hN : 2 ≤ m * d) (hk : 0 < k) (T : BasisMultiplicationData d) (hT : T.Represents basis)
    (w : ℚ) (hw : 0 < w) (p : ℕ) {s₁ ε C B : ℝ}
    (hs₁ : 0 ≤ s₁) (hε : 0 < ε) (hεone : ε ≤ 1) (hprec : (1 / 2 : ℝ) ^ p ≤ ε) (hC : 1 ≤ C)
    (hB : 4 * (C * Real.sqrt (Real.log ((m * d : ℕ) / ε))) * Real.sqrt (d : ℝ) ≤ B)
    (hwB : B * (4 * s₁ * Real.sqrt m) ≤ (w : ℝ)) :
    SpectralSamplerAccuracy (m := m) K basis hk s₁ (by exact_mod_cast hw : (0 : ℝ) < w)
      (basisDataHintSampler K basis T w p) ε :=
  storedSpectralHintSampler_accuracy_of_budget K basis hGram hN hk _
    (storedRingCoefficientRun_encoded_correct T basis hT) w hw p hs₁ hε hεone hprec hC hB hwB

omit [NumberField K] in
theorem basisDataHintSampler_decoded (basis : Basis (Fin d) ℤ (𝓞 K))
    (T : BasisMultiplicationData d) (D : GaussianColumnData (k * d) m) (w : ℚ) (p : ℕ) (j : Fin k) :
    basisDataHintSampler K basis T w p (decodedCoefficientMatrix basis D) j =
      guardedNumberFieldHintLaw K basis (storedRingCoefficientRun T D).value w p := by
  simp only [basisDataHintSampler, storedSpectralHintSampler, encodedRingMatrix_decodedCoefficientMatrix]

omit [NumberField K] in
theorem initialCoefficientRun_hint_law (basis : Basis (Fin d) ℤ (𝓞 K))
    (T : BasisMultiplicationData d) (a b k m s : ℕ)
    (tape : InitialGaussianTape a b d k m s) (w : ℚ) (p : ℕ) (j : Fin k) :
    guardedNumberFieldHintLaw K basis (initialCoefficientRun T a b k m s tape).value.2 w p =
      basisDataHintSampler K basis T w p
        (decodedCoefficientMatrix basis (initialCoefficientRun T a b k m s tape).value.1) j := by
  rw [basisDataHintSampler_decoded]
  rfl

omit [NumberField K] in
/-- Preparing the stored coefficient matrix preserves the actual finite initial matrix law. -/
theorem initialCoefficientRun_initial_law (basis : Basis (Fin d) ℤ (𝓞 K))
    (T : BasisMultiplicationData d) (a b k m s : ℕ) :
    (gaussianColumnTapeLaw (initialGaussianData a b d) (k * d) m s).map
      (fun tape => decodedCoefficientMatrix basis (initialCoefficientRun T a b k m s tape).value.1) =
        finiteInitialMatrixLaw K basis a b k m s := by
  rw [finiteInitialMatrixLaw, initialGaussianRunLaw, PMF.map_comp]
  rfl

theorem hintPrecisionRun_shapingBits (m d p : ℕ) :
    (hintPrecisionRun m d p).value.shapingBits = hintShapingBits (m * d) p := rfl

omit [NumberField K] in
/-- Shared shape preparation gives exactly the independent column law used by the reduction. -/
theorem basisHintColumnsRun_field_law (basis : Basis (Fin d) ℤ (𝓞 K))
    (T : BasisMultiplicationData d) (D : GaussianColumnData (k * d) m) (w : ℚ) (p : ℕ) :
    (basisHintColumnsRunLaw T D w p).map (matrixColumnCoordinates K basis m k).symm =
      independentMatrixColumns (basisDataHintSampler K basis T w p (decodedCoefficientMatrix basis D)) := by
  rw [basisHintColumnsRun_law]
  have hs : basisDataHintSampler K basis T w p (decodedCoefficientMatrix basis D) =
      fun _ : Fin k => guardedNumberFieldHintLaw K basis (storedRingCoefficientRun T D).value w p :=
    funext (basisDataHintSampler_decoded K basis T D w p)
  rw [hs]
  have h := congrArg (fun q : PMF (Fin k → Fin m → 𝓞 K) => q.map (fun X i j => X j i))
    (independentProduct_map (fun _ : Fin k => guardedHintColumnLaw d
      (gaussianShapeBits (m * d) 0 (p + 1)) (p + 2) (storedRingCoefficientRun T D).value w)
      (fun _ => (ringPowerCoordinates basis m).symm))
  let P := guardedHintColumnLaw d (gaussianShapeBits (m * d) 0 (p + 1)) (p + 2)
    (storedRingCoefficientRun T D).value w
  let E := (ringPowerCoordinates basis m).symm
  change (independentProduct (fun _ : Fin k => P)).map (fun z i j => E (z j) i) =
    (independentProduct (fun _ : Fin k => P.map E)).map (fun z i j => z j i)
  simpa only [PMF.map_comp, Function.comp_def] using h

omit [NumberField K] in
theorem basisHintColumnsRun_decoded_law (basis : Basis (Fin d) ℤ (𝓞 K))
    (T : BasisMultiplicationData d) (D : GaussianColumnData (k * d) m) (w : ℚ) (p : ℕ) :
    (basisHintColumnsTapeLaw T D w p).map
      (fun tape => decodedCoefficientMatrix basis (basisHintColumnsRun T D w p tape).value) =
        independentMatrixColumns (basisDataHintSampler K basis T w p (decodedCoefficientMatrix basis D)) := by
  have h := basisHintColumnsRun_field_law K basis T D w p
  have he (E : GaussianColumnData (m * d) k) :
      (matrixColumnCoordinates K basis m k).symm (gaussianColumnsOfData E) =
        decodedCoefficientMatrix basis E := rfl
  simpa only [basisHintColumnsRunLaw, PMF.map_comp, Function.comp_def, he] using h

omit [NumberField K] in
/-- The full finite hint program has exactly the joint law used in the SIS reduction. -/
theorem gaussianHintRun_field_law (basis : Basis (Fin d) ℤ (𝓞 K))
    (T : BasisMultiplicationData d) (a b k m s : ℕ) (w : ℚ) (p : ℕ) :
    (gaussianHintRunLaw T a b k m s w p).map
      (fun z => (decodedCoefficientMatrix basis z.1, decodedCoefficientMatrix basis z.2)) =
        jointPMF (finiteInitialMatrixLaw K basis a b k m s)
          (fun X => independentMatrixColumns (basisDataHintSampler K basis T w p X)) := by
  simp only [gaussianHintRunLaw_eq, PMF.map_bind, PMF.map_comp, Function.comp_def,
    jointPMF, finiteInitialMatrixLaw, initialGaussianRunLaw, PMF.bind_map]
  apply congrArg (fun f => (gaussianColumnTapeLaw (initialGaussianData a b d) (k * d) m s).bind f)
  funext initial
  let D := (initialGaussianRun a b d k m s initial).value
  change (basisHintColumnsTapeLaw T D w p).map
    (fun columns => (decodedCoefficientMatrix basis D,
      decodedCoefficientMatrix basis (basisHintColumnsRun T D w p columns).value)) =
    (independentMatrixColumns (basisDataHintSampler K basis T w p (decodedCoefficientMatrix basis D))).map
      (fun R => (decodedCoefficientMatrix basis D, R))
  rw [← basisHintColumnsRun_decoded_law K basis T D w p, PMF.map_comp]
  rfl

end
end StoredBasisAccuracy

end SISToKSIS
