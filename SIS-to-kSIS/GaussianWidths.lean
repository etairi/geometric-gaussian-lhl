import «SIS-to-kSIS».HintGames
import «SIS-to-kSIS».Parameters

/-!
# Diagonal widths and the actual unit shifts

Widths act separately on the ring coordinates in the canonical embedding.
Orthonormal Euclidean coordinates preserve these norms and Gaussian shapes.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Module NumberField GeometricGaussianLHL

namespace SISToKSIS

variable (K : Type*) [Field K] [NumberField K] {d n k : ℕ}

local instance widthsAmbientInner : InnerProductSpace ℝ (CanonicalAmbient K) := inferInstance
local instance widthsSpaceInner : InnerProductSpace ℝ (canonicalSpace K) := inferInstance
local instance widthsPowerInner (m : ℕ) : InnerProductSpace ℝ (CanonicalPower K m) := inferInstance

def canonicalDiagonalEquiv (w : Fin n → ℝ) (hw : ∀ i, w i ≠ 0) :
    CanonicalPower K n ≃ₗ[ℝ] CanonicalPower K n where
  toFun x := WithLp.toLp 2 (fun i => w i • x i)
  invFun x := WithLp.toLp 2 (fun i => (w i)⁻¹ • x i)
  left_inv x := by ext i; simp [smul_smul, hw]
  right_inv x := by ext i; simp [smul_smul, hw]
  map_add' x y := by
    ext i : 1
    exact smul_add (w i) (x i) (y i)
  map_smul' a x := by
    ext i : 1
    exact smul_comm (w i) a (x i)

omit [NumberField K] in
@[simp] theorem canonicalDiagonalEquiv_apply (w : Fin n → ℝ) (hw : ∀ i, w i ≠ 0)
    (x : CanonicalPower K n) (i : Fin n) : canonicalDiagonalEquiv K w hw x i = w i • x i := rfl

omit [NumberField K] in
@[simp] theorem canonicalDiagonalEquiv_symm_apply (w : Fin n → ℝ) (hw : ∀ i, w i ≠ 0)
    (x : CanonicalPower K n) (i : Fin n) :
    (canonicalDiagonalEquiv K w hw).symm x i = (w i)⁻¹ • x i := rfl

def canonicalDiagonalShape (b : Basis (Fin d) ℤ (𝓞 K)) (w : Fin n → ℝ)
    (hw : ∀ i, w i ≠ 0) : Euclidean (n * d) ≃L[ℝ] Euclidean (n * d) :=
  (canonicalOrthonormalCoordinates K b n).symm.toContinuousLinearEquiv.trans
    ((canonicalDiagonalEquiv K w hw).toContinuousLinearEquiv.trans
      (canonicalOrthonormalCoordinates K b n).toContinuousLinearEquiv)

theorem canonicalDiagonalShape_symm_coordinates (b : Basis (Fin d) ℤ (𝓞 K))
    (w : Fin n → ℝ) (hw : ∀ i, w i ≠ 0) (x : CanonicalPower K n) :
    (canonicalDiagonalShape K b w hw).symm (canonicalOrthonormalCoordinates K b n x) =
      canonicalOrthonormalCoordinates K b n ((canonicalDiagonalEquiv K w hw).symm x) := by
  change canonicalOrthonormalCoordinates K b n ((canonicalDiagonalEquiv K w hw).symm
    ((canonicalOrthonormalCoordinates K b n).symm (canonicalOrthonormalCoordinates K b n x))) = _
  rw [LinearIsometryEquiv.symm_apply_apply]

theorem canonicalIntegerEmbedding_one_norm_sq (b : Basis (Fin d) ℤ (𝓞 K)) :
    ‖canonicalIntegerEmbedding K 1‖ ^ 2 = d := by
  change ‖canonicalIntegerVector K 1‖ ^ 2 = (d : ℝ)
  rw [EuclideanSpace.norm_sq_eq]
  simp only [canonicalIntegerVector_apply, map_one, norm_one, one_pow, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one]
  rw [Embeddings.card K ℂ, ← integralBasis_degree K b]

def canonicalUnitCenter (b : Basis (Fin d) ℤ (𝓞 K)) (j : Fin n) : Euclidean (n * d) :=
  canonicalEuclideanEmbedding K b n (matrixIdentityColumn j)

theorem canonicalDiagonalShape_unit_shift_norm_sq (b : Basis (Fin d) ℤ (𝓞 K))
    (w : Fin n → ℝ) (hw : ∀ i, w i ≠ 0) (j : Fin n) :
    ‖(canonicalDiagonalShape K b w hw).symm (canonicalUnitCenter K b j)‖ ^ 2 =
      d / w j ^ 2 := by
  change ‖(canonicalDiagonalShape K b w hw).symm
    (canonicalOrthonormalCoordinates K b n (canonicalPowerEmbedding K n
      (matrixIdentityColumn j)))‖ ^ 2 = _
  rw [canonicalDiagonalShape_symm_coordinates, LinearIsometryEquiv.norm_map,
    PiLp.norm_sq_eq_of_L2]
  have hcoord (i : Fin n) :
      ‖(canonicalDiagonalEquiv K w hw).symm
        (canonicalPowerEmbedding K n (matrixIdentityColumn j)) i‖ ^ 2 =
        if i = j then (w j)⁻¹ ^ 2 * (d : ℝ) else 0 := by
    by_cases h : i = j
    · subst i
      simp only [canonicalDiagonalEquiv_symm_apply, canonicalPowerEmbedding_apply,
        matrixIdentityColumn, Matrix.one_apply_eq, norm_smul, Real.norm_eq_abs,
        mul_pow, sq_abs, canonicalIntegerEmbedding_one_norm_sq K b, ite_true]
    · simp [canonicalDiagonalEquiv_symm_apply, canonicalPowerEmbedding_apply,
        matrixIdentityColumn, Matrix.one_apply_ne h, h]
  simp_rw [hcoord]
  simp [div_eq_mul_inv, inv_pow, mul_comm]

theorem canonicalDiagonalShape_shiftEnergy (b : Basis (Fin d) ℤ (𝓞 K))
    (w : Fin n → ℝ) (hw : ∀ i, w i ≠ 0) (positions : Fin k → Fin n) :
    shiftEnergy (canonicalDiagonalShape K b w hw)
      (fun j => canonicalUnitCenter K b (positions j)) =
        ∑ j, (d : ℝ) / w (positions j) ^ 2 := by
  simp only [shiftEnergy, canonicalDiagonalShape_unit_shift_norm_sq]

theorem canonicalDiagonalShape_shiftEnergy_le_one (b : Basis (Fin d) ℤ (𝓞 K))
    (w : Fin n → ℝ) (hw : ∀ i, w i ≠ 0) (positions : Fin k → Fin n)
    {s : ℝ} (hs : s ≠ 0) (hwidth : ∀ j, w (positions j) = s)
    (hsize : (k : ℝ) * d ≤ s ^ 2) :
    shiftEnergy (canonicalDiagonalShape K b w hw)
      (fun j => canonicalUnitCenter K b (positions j)) ≤ 1 := by
  rw [canonicalDiagonalShape_shiftEnergy]
  simp_rw [hwidth]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_div_assoc]
  exact (div_le_one (sq_pos_of_ne_zero hs)).mpr hsize

def blockWidths (m k : ℕ) (s₁ s₂ : ℝ) : Fin (m + k) → ℝ :=
  Fin.append (fun _ => s₁) (fun _ => s₂)

theorem blockWidths_ne_zero (m k : ℕ) {s₁ s₂ : ℝ} (h₁ : s₁ ≠ 0) (h₂ : s₂ ≠ 0) :
    ∀ i, blockWidths m k s₁ s₂ i ≠ 0 := by
  refine Fin.addCases (fun i => ?_) (fun j => ?_)
  · simpa only [blockWidths, Fin.append_left] using h₁
  · simpa only [blockWidths, Fin.append_right] using h₂

/-- The paper's width matrix `diag(s₁ I_m, s₂ I_k)` in canonical Euclidean coordinates. -/
def paperHintShape (b : Basis (Fin d) ℤ (𝓞 K)) (m k : ℕ)
    {s₁ s₂ : ℝ} (h₁ : s₁ ≠ 0) (h₂ : s₂ ≠ 0) :
    Euclidean ((m + k) * d) ≃L[ℝ] Euclidean ((m + k) * d) :=
  canonicalDiagonalShape K b (blockWidths m k s₁ s₂) (blockWidths_ne_zero m k h₁ h₂)

def paperHintCenters (b : Basis (Fin d) ℤ (𝓞 K)) (m k : ℕ) :
    Fin k → Euclidean ((m + k) * d) :=
  fun j => canonicalUnitCenter K b (Fin.natAdd m j)

/-- Only the second width enters: every shifted coordinate lies in the second block. -/
theorem paperHint_shiftEnergy (b : Basis (Fin d) ℤ (𝓞 K)) (m k : ℕ)
    {s₁ s₂ : ℝ} (h₁ : s₁ ≠ 0) (h₂ : s₂ ≠ 0) :
    shiftEnergy (paperHintShape K b m k h₁ h₂) (paperHintCenters K b m k) =
      (k : ℝ) * d / s₂ ^ 2 := by
  unfold paperHintShape paperHintCenters
  rw [canonicalDiagonalShape_shiftEnergy]
  simp only [blockWidths, Fin.append_right, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_div_assoc]

theorem paperHint_shiftEnergy_le_one (b : Basis (Fin d) ℤ (𝓞 K))
    {m k n q g : ℕ} {s₁ s₂ u : ℝ} (h₁ : s₁ ≠ 0) (h₂ : s₂ ≠ 0)
    (hkm : k ≤ m) (hq : 1 ≤ q) (hwindow : ArithmeticWindow d m n k q g u s₁ s₂) :
    shiftEnergy (paperHintShape K b m k h₁ h₂) (paperHintCenters K b m k) ≤ 1 := by
  rw [paperHint_shiftEnergy]
  apply (div_le_one (sq_pos_of_ne_zero h₂)).mpr
  exact arithmeticWindow_shift_width (integralBasis_dimension_pos K b) hkm hq hwindow

/-- The paper's actual centered and shifted games, with the numerical width premise discharged. -/
theorem paper_modularGameSuccess_shift_bound {β : Type*} [MeasurableSpace β]
    [MeasurableSingletonClass β] (b : Basis (Fin d) ℤ (𝓞 K))
    {m k n q g : ℕ} [NeZero q] {s₁ s₂ u : ℝ} (h₁ : s₁ ≠ 0) (h₂ : s₂ ≠ 0)
    (hkm : k ≤ m) (hwindow : ArithmeticWindow d m n k q g u s₁ s₂)
    (adversary : Matrix (Fin n) (Fin (m + k)) (ResidueRing K q) →
      Matrix (Fin (m + k)) (Fin k) (𝓞 K) → PMF β)
    (wins : Matrix (Fin n) (Fin (m + k)) (ResidueRing K q) →
      Matrix (Fin (m + k)) (Fin k) (𝓞 K) → β → Prop) :
    modularGameSuccess K b q (paperHintShape K b m k h₁ h₂) (fun _ => 0) adversary wins ^ 2 /
      Real.exp (2 * Real.pi) ≤
        modularGameSuccess K b q (paperHintShape K b m k h₁ h₂)
          (paperHintCenters K b m k) adversary wins :=
  modularGameSuccess_shift_bound K b q _ _
    (paperHint_shiftEnergy_le_one K b h₁ h₂ hkm (Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)) hwindow)
    adversary wins

theorem canonicalDiagonalEquiv_norm_le (w : Fin n → ℝ) (hw : ∀ i, w i ≠ 0)
    {σ : ℝ} (hσ : 0 ≤ σ) (hbound : ∀ i, |w i| ≤ σ) (x : CanonicalPower K n) :
    ‖canonicalDiagonalEquiv K w hw x‖ ≤ σ * ‖x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hσ (norm_nonneg _))).mp
  rw [PiLp.norm_sq_eq_of_L2, mul_pow, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [canonicalDiagonalEquiv_apply, norm_smul, Real.norm_eq_abs, mul_pow]
  exact mul_le_mul_of_nonneg_right ((sq_le_sq₀ (abs_nonneg _) hσ).mpr (hbound i)) (sq_nonneg _)

theorem canonicalDiagonalShape_norm_le (b : Basis (Fin d) ℤ (𝓞 K))
    (w : Fin n → ℝ) (hw : ∀ i, w i ≠ 0) {σ : ℝ} (hσ : 0 ≤ σ)
    (hbound : ∀ i, |w i| ≤ σ) :
    ‖(canonicalDiagonalShape K b w hw).toContinuousLinearMap‖ ≤ σ := by
  apply ContinuousLinearMap.opNorm_le_bound _ hσ
  intro x
  change ‖canonicalOrthonormalCoordinates K b n (canonicalDiagonalEquiv K w hw
    ((canonicalOrthonormalCoordinates K b n).symm x))‖ ≤ σ * ‖x‖
  rw [LinearIsometryEquiv.norm_map]
  simpa only [LinearIsometryEquiv.norm_map] using
    canonicalDiagonalEquiv_norm_le K w hw hσ hbound ((canonicalOrthonormalCoordinates K b n).symm x)

theorem canonicalDiagonalShape_inverse_norm_le (b : Basis (Fin d) ℤ (𝓞 K))
    (w : Fin n → ℝ) (hw : ∀ i, w i ≠ 0) {σ : ℝ} (hσ : 0 < σ)
    (hbound : ∀ i, σ ≤ |w i|) :
    ‖(canonicalDiagonalShape K b w hw).symm.toContinuousLinearMap‖ ≤ σ⁻¹ := by
  have he : (canonicalDiagonalShape K b w hw).symm =
      canonicalDiagonalShape K b (fun i => (w i)⁻¹) (fun i => inv_ne_zero (hw i)) := by
    apply ContinuousLinearEquiv.ext
    funext x
    rfl
  rw [he]
  apply canonicalDiagonalShape_norm_le K b _ _ (inv_nonneg.mpr hσ.le)
  intro i
  rw [abs_inv]
  exact inv_anti₀ hσ (hbound i)

theorem canonicalDiagonalEquiv_det (b : Basis (Fin d) ℤ (𝓞 K))
    (w : Fin n → ℝ) (hw : ∀ i, w i ≠ 0) :
    (canonicalDiagonalEquiv K w hw).toLinearMap.det = ∏ i, w i ^ d := by
  let T : (Fin n → canonicalSpace K) →ₗ[ℝ] (Fin n → canonicalSpace K) :=
    LinearMap.pi (fun i => (w i • LinearMap.id).comp (LinearMap.proj i))
  have he : (canonicalDiagonalEquiv K w hw).toLinearMap =
      (WithLp.linearEquiv 2 ℝ (Fin n → canonicalSpace K)).symm.toLinearMap.comp
        (T.comp (WithLp.linearEquiv 2 ℝ (Fin n → canonicalSpace K)).toLinearMap) := rfl
  rw [he]
  have hconj := LinearMap.det_conj T (WithLp.linearEquiv 2 ℝ (Fin n → canonicalSpace K)).symm
  trans T.det
  · simpa only [LinearEquiv.symm_symm, LinearMap.comp_assoc] using hconj
  dsimp [T]
  rw [LinearMap.det_pi]
  simp only [LinearMap.det_smul, LinearMap.det_id, mul_one, canonicalSpace_finrank,
    ← integralBasis_degree K b]

theorem canonicalDiagonalShape_det (b : Basis (Fin d) ℤ (𝓞 K))
    (w : Fin n → ℝ) (hw : ∀ i, w i ≠ 0) :
    (canonicalDiagonalShape K b w hw).toLinearMap.det = ∏ i, w i ^ d := by
  change LinearMap.det ((canonicalOrthonormalCoordinates K b n).toLinearEquiv.toLinearMap.comp
    ((canonicalDiagonalEquiv K w hw).toLinearMap.comp
      (canonicalOrthonormalCoordinates K b n).symm.toLinearEquiv.toLinearMap)) = _
  have hconj := LinearMap.det_conj (canonicalDiagonalEquiv K w hw).toLinearMap
    (canonicalOrthonormalCoordinates K b n).toLinearEquiv
  have he : (canonicalOrthonormalCoordinates K b n).symm.toLinearEquiv =
      (canonicalOrthonormalCoordinates K b n).toLinearEquiv.symm := by
    ext x
    rfl
  rw [he]
  simpa only [LinearMap.comp_assoc] using hconj.trans (canonicalDiagonalEquiv_det K b w hw)

theorem paperHintShape_norm_le (b : Basis (Fin d) ℤ (𝓞 K)) (m k : ℕ)
    {s₁ s₂ : ℝ} (h₁ : 0 < s₁) (h₂ : 0 < s₂) (hs : s₁ ≤ s₂) :
    ‖(paperHintShape K b m k h₁.ne' h₂.ne').toContinuousLinearMap‖ ≤ s₂ := by
  apply canonicalDiagonalShape_norm_le K b _ _ h₂.le
  refine Fin.addCases (fun i => ?_) (fun j => ?_)
  · simpa only [blockWidths, Fin.append_left, abs_of_pos h₁] using hs
  · simp only [blockWidths, Fin.append_right, abs_of_pos h₂, le_refl]

theorem paperHintShape_inverse_norm_le (b : Basis (Fin d) ℤ (𝓞 K)) (m k : ℕ)
    {s₁ s₂ : ℝ} (h₁ : 0 < s₁) (h₂ : 0 < s₂) (hs : s₁ ≤ s₂) :
    ‖(paperHintShape K b m k h₁.ne' h₂.ne').symm.toContinuousLinearMap‖ ≤ s₁⁻¹ := by
  apply canonicalDiagonalShape_inverse_norm_le K b _ _ h₁
  refine Fin.addCases (fun i => ?_) (fun j => ?_)
  · simp only [blockWidths, Fin.append_left, abs_of_pos h₁, le_refl]
  · simpa only [blockWidths, Fin.append_right, abs_of_pos h₂] using hs

theorem paperHintShape_det (b : Basis (Fin d) ℤ (𝓞 K)) (m k : ℕ)
    {s₁ s₂ : ℝ} (h₁ : s₁ ≠ 0) (h₂ : s₂ ≠ 0) :
    (paperHintShape K b m k h₁ h₂).toLinearMap.det = s₁ ^ (m * d) * s₂ ^ (k * d) := by
  rw [paperHintShape, canonicalDiagonalShape_det, Fin.prod_univ_add]
  simp only [blockWidths, Fin.append_left, Fin.append_right, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, ← pow_mul]
  simp only [Nat.mul_comm]

theorem paperHintShape_normDet (b : Basis (Fin d) ℤ (𝓞 K)) (m k : ℕ)
    {s₁ s₂ : ℝ} (h₁ : 0 < s₁) (h₂ : 0 < s₂) :
    (paperHintShape K b m k h₁.ne' h₂.ne').toLinearMap.normDet =
      s₁ ^ (m * d) * s₂ ^ (k * d) := by
  rw [LinearMap.normDet_eq_norm_det, paperHintShape_det, Real.norm_eq_abs,
    abs_of_pos (mul_pos (pow_pos h₁ _) (pow_pos h₂ _))]

theorem paperHintShape_symm_normDet (b : Basis (Fin d) ℤ (𝓞 K)) (m k : ℕ)
    {s₁ s₂ : ℝ} (h₁ : 0 < s₁) (h₂ : 0 < s₂) :
    (paperHintShape K b m k h₁.ne' h₂.ne').symm.toLinearMap.normDet =
      1 / (s₁ ^ (m * d) * s₂ ^ (k * d)) := by
  apply (eq_div_iff (mul_ne_zero (pow_ne_zero _ h₁.ne') (pow_ne_zero _ h₂.ne'))).mpr
  simpa only [paperHintShape_normDet K b m k h₁ h₂] using
    normDet_symm_mul (paperHintShape K b m k h₁.ne' h₂.ne')

/-- The full modular-kernel volume bound for the paper's two diagonal widths. -/
theorem paperHint_whitened_covolume_le (b : Basis (Fin d) ℤ (𝓞 K)) (m k r : ℕ)
    (q : ℕ) [NeZero q] (A : Matrix (Fin r) (Fin (m + k)) (ResidueRing K q))
    {s₁ s₂ : ℝ} (h₁ : 0 < s₁) (h₂ : 0 < s₂) :
    ZLattice.covolume (latticeImage
      (paperHintShape K b m k h₁.ne' h₂.ne').symm.toContinuousLinearMap
      (numberFieldModularLattice K b q A)) ≤
      (q : ℝ) ^ (d * r) * Real.sqrt |(NumberField.discr K : ℝ)| ^ (m + k) /
        (s₁ ^ (m * d) * s₂ ^ (k * d)) := by
  rw [covolume_latticeImage_equiv, paperHintShape_symm_normDet K b m k h₁ h₂]
  have h := div_le_div_of_nonneg_right (numberFieldModularLattice_covolume_le_discr K b q A)
    (mul_pos (pow_pos h₁ (m * d)) (pow_pos h₂ (k * d))).le
  simpa only [div_eq_mul_inv, one_div, mul_comm, mul_one] using h

end SISToKSIS
