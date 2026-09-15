import GeometricGaussianLHL.CyclotomicGeometry
import GeometricGaussianLHL.GaussianMoments
import GeometricGaussianLHL.GaussianPoisson
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.Matrix.Mul

/-!
# Gaussian pushforwards and parameter stability

This module collects the following proof sections, in dependency order.
- The Gaussian transverse to a linear kernel (`TransverseGaussian`).
- The coefficient Gaussian shape of a number field (`NumberFieldShape`).
- Total variation of independent coordinates (`IndependentVariation`).
- The actual number-field Gaussian law (`NumberFieldGaussian`).
- Independent hint columns and their actual matrix law (`MatrixHintLaw`).
- The orthogonal right inverse of a surjection (`MinimumNormRightInverse`).
- From an adjoint lower bound to the smallest nonzero singular value (`AdjointMinimumStretch`).
- Linear exponential moments on actual full lattices (`LatticeGaussianMoment`).
- Orthonormal Euclidean coordinates for the canonical ring lattice (`CanonicalEuclidean`).
- Complex-embedding projections of the canonical space (`CanonicalEmbeddingProjection`).
- Ellipsoidal Gaussians on the actual ring lattice (`NumberFieldEllipsoid`).
- Independent number-field matrices in coefficient coordinates (`NumberFieldMatrixLaw`).
- Parameter stability for coefficient Gaussian distributions (`GaussianParameterStability`).
- Actual number-field Gaussian exponential moments (`NumberFieldGaussianMoment`).
- Spherical ring Gaussians and covariance invariance (`NumberFieldSphericalGaussian`).
- Product coefficient laws for power-of-two number fields (`NumberFieldProducts`).
- Parameter stability on every full Euclidean lattice (`LatticeParameterStability`).
- Actual Gaussian pushforward point masses (`GaussianLatticeFibers`).
- Gaussian pushforward with its actual covariance (`LatticeGaussianPushforward`).
- The positive square root of the Gaussian image covariance (`GaussianImageSquareRoot`).
- Number-field Gaussian pushforward (`NumberFieldPushforward`).
- Joint number-field Gaussian pushforward laws (`NumberFieldJointGaussian`).
-/

section TransverseGaussian

/-!
## The Gaussian transverse to a linear kernel

The inverse of a surjective map restricted to its kernel's orthogonal
complement selects the orthogonal lift. Its covariance is exactly the
map composed with its adjoint. Consequently any shape with that covariance
has the same Gaussian quadratic form as the transverse component.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace GeometricGaussianLHL

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ F] in
theorem kernelOrthogonalEquiv_symm_apply_map (f : E →ₗ[ℝ] F)
    (hf : Function.Surjective f) (x : E) :
    (kernelOrthogonalEquiv f hf).symm (f x) = f.kerᗮ.orthogonalProjectionOnto x := by
  apply (kernelOrthogonalEquiv f hf).injective
  rw [LinearEquiv.apply_symm_apply, kernelOrthogonalEquiv_apply,
    map_orthogonalProjection_kernel]

theorem kernelOrthogonalEquiv_adjoint_coe (f : E →ₗ[ℝ] F)
    (hf : Function.Surjective f) (y : F) :
    (((kernelOrthogonalEquiv f hf).toLinearMap.adjoint y : f.kerᗮ) : E) = f.adjoint y := by
  have hr (x : F) : f.adjoint x ∈ f.kerᗮ := by
    rw [f.orthogonal_ker]
    exact ⟨x, rfl⟩
  have ha : f.adjoint.codRestrict f.kerᗮ hr = (kernelOrthogonalEquiv f hf).toLinearMap.adjoint := by
    apply (LinearMap.eq_adjoint_iff _ _).mpr
    intro x z
    change inner ℝ (f.adjoint x) (z : E) = inner ℝ x (kernelOrthogonalEquiv f hf z)
    rw [kernelOrthogonalEquiv_apply, LinearMap.adjoint_inner_left]
  rw [← ha]
  rfl

theorem kernelOrthogonalEquiv_covariance (f : E →L[ℝ] F)
    (hf : Function.Surjective f) :
    let B := (kernelOrthogonalEquiv f.toLinearMap hf).toContinuousLinearEquiv
    B.toContinuousLinearMap.comp B.toContinuousLinearMap.adjoint = f.comp f.adjoint := by
  ext y
  change kernelOrthogonalEquiv f.toLinearMap hf
    ((kernelOrthogonalEquiv f.toLinearMap hf).toLinearMap.adjoint y) =
      f (f.toLinearMap.adjoint y)
  rw [kernelOrthogonalEquiv_apply, kernelOrthogonalEquiv_adjoint_coe]
  rfl

/-- Equal covariances give the same inverse quadratic form, even when the
two source inner-product spaces are different. -/
theorem equiv_symm_norm_sq_eq_of_covariance_eq (B : E ≃L[ℝ] F) (T : F ≃L[ℝ] F)
    (h : B.toContinuousLinearMap.comp B.toContinuousLinearMap.adjoint = shapeCovariance T)
    (y : F) : ‖B.symm y‖ ^ 2 = ‖T.symm y‖ ^ 2 := by
  let Q := B.symm.toContinuousLinearMap.adjoint.comp B.symm.toContinuousLinearMap
  have hc : B.toContinuousLinearMap.adjoint.comp B.symm.toContinuousLinearMap.adjoint =
      ContinuousLinearMap.id ℝ E := by
    rw [← ContinuousLinearMap.adjoint_comp, B.coe_symm_comp_coe, ContinuousLinearMap.adjoint_id]
  have hPQ : (shapeCovariance T).comp Q = ContinuousLinearMap.id ℝ F := by
    rw [← h]
    dsimp only [Q]
    rw [ContinuousLinearMap.comp_assoc,
      ← ContinuousLinearMap.comp_assoc B.toContinuousLinearMap.adjoint,
      hc, ContinuousLinearMap.id_comp, B.coe_comp_coe_symm]
  have hQ : Q = shapePrecision T := by
    calc
      Q = (ContinuousLinearMap.id ℝ F).comp Q := (ContinuousLinearMap.id_comp Q).symm
      _ = ((shapePrecision T).comp (shapeCovariance T)).comp Q := by
        rw [shapePrecision_comp_covariance]
      _ = (shapePrecision T).comp ((shapeCovariance T).comp Q) := ContinuousLinearMap.comp_assoc _ _ _
      _ = shapePrecision T := by rw [hPQ, ContinuousLinearMap.comp_id]
  calc
    ‖B.symm y‖ ^ 2 = inner ℝ y (Q y) := by
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
        real_inner_self_eq_norm_sq]
      rfl
    _ = ‖T.symm y‖ ^ 2 := by rw [hQ, shapePrecision_inner]

/-- The target covariance determines the exact transverse Gaussian exponent. -/
theorem norm_sq_kernel_projection_eq_inverse_shape (f : E →L[ℝ] F)
    (hf : Function.Surjective f) (T : F ≃L[ℝ] F)
    (h : shapeCovariance T = f.comp f.adjoint) (x : E) :
    ‖f.toLinearMap.kerᗮ.starProjection x‖ ^ 2 = ‖T.symm (f x)‖ ^ 2 := by
  let B := (kernelOrthogonalEquiv f.toLinearMap hf).toContinuousLinearEquiv
  have hc : B.toContinuousLinearMap.comp B.toContinuousLinearMap.adjoint = shapeCovariance T :=
    (kernelOrthogonalEquiv_covariance f hf).trans h.symm
  have hn := equiv_symm_norm_sq_eq_of_covariance_eq B T hc (f x)
  change ‖(kernelOrthogonalEquiv f.toLinearMap hf).symm (f x)‖ ^ 2 = _ at hn
  exact (congrArg (fun z : f.toLinearMap.kerᗮ => ‖z‖ ^ 2)
    (kernelOrthogonalEquiv_symm_apply_map f.toLinearMap hf x)).symm.trans hn

theorem gaussianWeight_kernel_projection_eq_inverse_shape (f : E →L[ℝ] F)
    (hf : Function.Surjective f) (T : F ≃L[ℝ] F)
    (h : shapeCovariance T = f.comp f.adjoint) (x : E) :
    gaussianWeight 1 (f.toLinearMap.kerᗮ.starProjection x) =
      gaussianWeight 1 (T.symm (f x)) := by
  simp only [gaussianWeight, norm_sq_kernel_projection_eq_inverse_shape f hf T h]

end GeometricGaussianLHL
end

end TransverseGaussian

section NumberFieldShape

/-!
## The coefficient Gaussian shape of a number field

Orthonormal coordinates in the actual canonical space turn the inverse
basis map, scaled by `s`, into an invertible Euclidean shape. Its Gaussian
weight equals the number-field Gaussian weight exactly. The construction
does not require choosing a matrix square root of the Gram matrix.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Module NumberField

namespace GeometricGaussianLHL

variable (K : Type*) [Field K] [NumberField K] {d : ℕ}

def canonicalOrthonormalCoordinates (b : Basis (Fin d) ℤ (𝓞 K)) (n : ℕ) :
    CanonicalPower K n ≃ₗᵢ[ℝ] Euclidean (n * d) :=
  ((stdOrthonormalBasis ℝ (CanonicalPower K n)).reindex (finCongr (by
    simpa using (powerCanonicalEquiv K b n).toLinearEquiv.finrank_eq.symm))).repr

def numberFieldGaussianShape (b : Basis (Fin d) ℤ (𝓞 K)) (n : ℕ)
    (s : ℝ) (hs : s ≠ 0) : Euclidean (n * d) ≃L[ℝ] Euclidean (n * d) :=
  ((ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := Euclidean (n * d)) (Units.mk0 s hs)).trans
    (canonicalOrthonormalCoordinates K b n).symm.toContinuousLinearEquiv).trans
    (powerCanonicalEquiv K b n).symm

theorem numberFieldGaussianShape_apply (b : Basis (Fin d) ℤ (𝓞 K)) (n : ℕ)
    (s : ℝ) (hs : s ≠ 0) (x : Euclidean (n * d)) :
    numberFieldGaussianShape K b n s hs x = (powerCanonicalEquiv K b n).symm
      ((canonicalOrthonormalCoordinates K b n).symm (s • x)) := rfl

theorem numberFieldGaussianShape_symm_apply (b : Basis (Fin d) ℤ (𝓞 K)) (n : ℕ)
    (s : ℝ) (hs : s ≠ 0) (x : Euclidean (n * d)) :
    (numberFieldGaussianShape K b n s hs).symm x =
      s⁻¹ • canonicalOrthonormalCoordinates K b n (powerCanonicalEquiv K b n x) := rfl

theorem numberFieldGaussianShape_norm_le (b : Basis (Fin d) ℤ (𝓞 K)) (n : ℕ)
    {s : ℝ} (hs : 0 < s) :
    ‖(numberFieldGaussianShape K b n s hs.ne').toContinuousLinearMap‖ ≤ s * basisBeta K b := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hs.le (basisBeta_pos K b).le)
  intro x
  change ‖numberFieldGaussianShape K b n s hs.ne' x‖ ≤ _
  rw [numberFieldGaussianShape_apply]
  have h := powerCanonicalEquiv_symm_norm_apply_le K b n
    ((canonicalOrthonormalCoordinates K b n).symm (s • x))
  simpa only [LinearIsometryEquiv.norm_map, norm_smul, Real.norm_eq_abs, abs_of_pos hs,
    mul_left_comm, mul_assoc] using h

theorem numberFieldGaussianShape_symm_norm_le (b : Basis (Fin d) ℤ (𝓞 K)) (n : ℕ)
    {s : ℝ} (hs : 0 < s) :
    ‖(numberFieldGaussianShape K b n s hs.ne').symm.toContinuousLinearMap‖ ≤ basisAlpha K b / s := by
  apply ContinuousLinearMap.opNorm_le_bound _ (div_nonneg (basisAlpha_pos K b).le hs.le)
  intro x
  change ‖(numberFieldGaussianShape K b n s hs.ne').symm x‖ ≤ _
  rw [numberFieldGaussianShape_symm_apply, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hs,
    LinearIsometryEquiv.norm_map]
  have h := mul_le_mul_of_nonneg_left (powerCanonicalEquiv_norm_apply_le K b n x) (inv_nonneg.mpr hs.le)
  calc
    _ ≤ s⁻¹ * (basisAlpha K b * ‖x‖) := h
    _ = _ := by ring

def numberFieldGaussianWeight (n : ℕ) (s : ℝ) (x : Fin n → 𝓞 K) : ℝ :=
  gaussianWeight (1 / s) (canonicalPowerEmbedding K n x)

theorem numberFieldGaussianShape_weight (b : Basis (Fin d) ℤ (𝓞 K)) (n : ℕ)
    (s : ℝ) (hs : s ≠ 0) (x : Fin n → 𝓞 K) :
    ellipsoidWeight (numberFieldGaussianShape K b n s hs) 0 (ringPowerCoordinates b n x) =
      numberFieldGaussianWeight K n s x := by
  simp only [ellipsoidWeight, sub_zero, numberFieldGaussianShape_symm_apply,
    powerCanonicalEquiv_integer, numberFieldGaussianWeight, gaussianWeight, norm_smul,
    LinearIsometryEquiv.norm_map, Real.norm_eq_abs, mul_pow, sq_abs, one_pow, one_div]
  congr 1
  ring

end GeometricGaussianLHL
end

end NumberFieldShape

section IndependentVariation

/-!
## Total variation of independent coordinates

Finite tensorization for the actual product PMF, followed by its joint-law
good-event version. Coordinate errors add; the exceptional marginal event
is paid once.
-/

noncomputable section

namespace GeometricGaussianLHL

theorem discreteTotalVariation_triangle {α : Type*} (p q r : PMF α) :
    discreteTotalVariation p r ≤ discreteTotalVariation p q + discreteTotalVariation q r := by
  have h := (pmf_summable_abs_sub p r).tsum_le_tsum
    (fun x => abs_sub_le (p x).toReal (q x).toReal (r x).toReal)
    ((pmf_summable_abs_sub p q).add (pmf_summable_abs_sub q r))
  rw [Summable.tsum_add (pmf_summable_abs_sub p q) (pmf_summable_abs_sub q r)] at h
  unfold discreteTotalVariation
  linarith

theorem discreteTotalVariation_joint_const {α β : Type*} (p : PMF α) (q r : PMF β) :
    discreteTotalVariation (jointPMF p (fun _ => q)) (jointPMF p (fun _ => r)) =
      discreteTotalVariation q r := by
  rw [discreteTotalVariation_joint, tsum_mul_right, pmf_tsum_toReal, one_mul]

theorem jointPMF_const_swap {α β : Type*} (p : PMF α) (q : PMF β) :
    (jointPMF p (fun _ => q)).map (Equiv.prodComm α β) = jointPMF q (fun _ => p) := by
  ext ⟨b, a⟩
  change (jointPMF p (fun _ => q)).map (Equiv.prodComm α β)
    ((Equiv.prodComm α β) (a, b)) = _
  rw [pmf_map_equiv_apply, jointPMF_apply, jointPMF_apply, mul_comm]

theorem discreteTotalVariation_product_le {α β : Type*} (p p' : PMF α) (q q' : PMF β) :
    discreteTotalVariation (jointPMF p (fun _ => q)) (jointPMF p' (fun _ => q')) ≤
      discreteTotalVariation p p' + discreteTotalVariation q q' := by
  have hfirst : discreteTotalVariation (jointPMF p (fun _ => q'))
      (jointPMF p' (fun _ => q')) = discreteTotalVariation p p' := by
    rw [← discreteTotalVariation_map_equiv _ _ (Equiv.prodComm α β),
      jointPMF_const_swap, jointPMF_const_swap, discreteTotalVariation_joint_const]
  have h := discreteTotalVariation_triangle (jointPMF p (fun _ => q))
    (jointPMF p (fun _ => q')) (jointPMF p' (fun _ => q'))
  rw [discreteTotalVariation_joint_const, hfirst, add_comm] at h
  exact h

theorem independentProduct_cons {α : Type*} {n : ℕ} (p : Fin (n + 1) → PMF α) :
    (jointPMF (p 0) (fun _ => independentProduct (fun i : Fin n => p i.succ))).map
      (Fin.consEquiv (fun _ : Fin (n + 1) => α)) = independentProduct p := by
  let e := Fin.consEquiv (fun _ : Fin (n + 1) => α)
  ext x
  obtain ⟨⟨a, z⟩, rfl⟩ := e.surjective x
  rw [pmf_map_equiv_apply, jointPMF_apply]
  simp only [independentProduct_apply, Fin.prod_univ_succ, e, Fin.consEquiv,
    Equiv.coe_fn_mk, Fin.cons_zero, Fin.cons_succ]

/-- Applying separate, arbitrary functions preserves independence. -/
theorem independentProduct_map {α β : Type*} {n : ℕ} (p : Fin n → PMF α)
    (f : Fin n → α → β) :
    (independentProduct p).map (fun z i => f i (z i)) =
      independentProduct (fun i => (p i).map (f i)) := by
  classical
  ext y
  rw [PMF.map_apply]
  calc
    _ = ∑' z : Fin n → α, ∏ i, if y i = f i (z i) then p i (z i) else 0 := by
      apply tsum_congr
      intro z
      by_cases h : ∀ i, y i = f i (z i)
      · simp only [funext h, ↓reduceIte, independentProduct_apply]
      · obtain ⟨i, hi⟩ := not_forall.mp h
        have hn : y ≠ (fun i => f i (z i)) := fun heq => hi (congrFun heq i)
        rw [ite_eq_right hn]
        symm
        exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)
    _ = ∏ i, ∑' x, if y i = f i x then p i x else 0 :=
      tsum_finite_product n (fun i x => if y i = f i x then p i x else 0)
    _ = _ := by simp only [independentProduct_apply, PMF.map_apply]

theorem discreteTotalVariation_independentProduct_le {α : Type*} {n : ℕ}
    (p q : Fin n → PMF α) :
    discreteTotalVariation (independentProduct p) (independentProduct q) ≤
      ∑ i, discreteTotalVariation (p i) (q i) := by
  induction n with
  | zero =>
    have he : independentProduct p = independentProduct q := by ext x; simp
    simp [he, discreteTotalVariation]
  | succ n ih =>
    rw [← independentProduct_cons p, ← independentProduct_cons q,
      discreteTotalVariation_map_equiv, Fin.sum_univ_succ]
    exact (discreteTotalVariation_product_le _ _ _ _).trans
      (add_le_add le_rfl (ih (fun i => p i.succ) (fun i => q i.succ)))

theorem discreteTotalVariation_independentProduct_le_uniform {α : Type*} {n : ℕ}
    (p q : Fin n → PMF α) {ε : ℝ}
    (h : ∀ i, discreteTotalVariation (p i) (q i) ≤ ε) :
    discreteTotalVariation (independentProduct p) (independentProduct q) ≤ (n : ℝ) * ε := by
  have hs := (discreteTotalVariation_independentProduct_le p q).trans
    (Finset.sum_le_sum (fun i _ => h i))
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using hs

theorem discreteTotalVariation_joint_independent_good_event {α β : Type*} {n : ℕ}
    (p : PMF α) (q r : α → Fin n → PMF β) (G : Set α) {δ ε : ℝ}
    (hprob : ENNReal.ofReal (1 - δ) ≤ p.toOuterMeasure G) (hε : 0 ≤ ε)
    (h : ∀ a ∈ G, ∀ i, discreteTotalVariation (q a i) (r a i) ≤ ε) :
    discreteTotalVariation (jointPMF p (fun a => independentProduct (q a)))
      (jointPMF p (fun a => independentProduct (r a))) ≤ δ + (n : ℝ) * ε := by
  apply discreteTotalVariation_joint_le_of_event_mass p _ _ G hprob (by positivity)
  intro a ha
  exact discreteTotalVariation_independentProduct_le_uniform (q a) (r a) (h a ha)

end GeometricGaussianLHL
end

end IndependentVariation

section NumberFieldGaussian

/-!
## The actual number-field Gaussian law

The law is normalized directly from the canonical Gaussian weights.
Convergence and normalization follow from the proved coordinate identity.
Pushing this PMF through the integral-basis coordinates gives exactly the
ellipsoidal Gaussian used in the matrix certificate.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Module NumberField
open scoped ENNReal

namespace GeometricGaussianLHL

variable (K : Type*) [Field K] [NumberField K] {d : ℕ}

theorem numberFieldGaussianWeight_pos (n : ℕ) (s : ℝ) (x : Fin n → 𝓞 K) :
    0 < numberFieldGaussianWeight K n s x := gaussianWeight_pos _ _

theorem summable_numberFieldGaussianWeight (b : Basis (Fin d) ℤ (𝓞 K))
    (n : ℕ) (s : ℝ) (hs : s ≠ 0) : Summable (numberFieldGaussianWeight K n s) := by
  have h := (summable_ellipsoidWeight (numberFieldGaussianShape K b n s hs) 0).comp_injective
    (ringPowerCoordinates b n).injective
  simpa only [Function.comp_def, numberFieldGaussianShape_weight] using h

def numberFieldGaussianPartition (n : ℕ) (s : ℝ) : ℝ :=
  ∑' x : Fin n → 𝓞 K, numberFieldGaussianWeight K n s x

theorem numberFieldGaussianPartition_pos (b : Basis (Fin d) ℤ (𝓞 K))
    (n : ℕ) (s : ℝ) (hs : s ≠ 0) : 0 < numberFieldGaussianPartition K n s :=
  (numberFieldGaussianWeight_pos K n s 0).trans_le
    ((summable_numberFieldGaussianWeight K b n s hs).le_tsum 0
      (fun _ _ => (numberFieldGaussianWeight_pos K n s _).le))

theorem numberFieldGaussianWeight_sum_ne_zero (b : Basis (Fin d) ℤ (𝓞 K))
    (n : ℕ) (s : ℝ) (hs : s ≠ 0) :
    (∑' x, ENNReal.ofReal (numberFieldGaussianWeight K n s x)) ≠ 0 := by
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => (numberFieldGaussianWeight_pos K n s _).le)
    (summable_numberFieldGaussianWeight K b n s hs)]
  exact ne_of_gt (ENNReal.ofReal_pos.mpr (numberFieldGaussianPartition_pos K b n s hs))

def numberFieldGaussian (b : Basis (Fin d) ℤ (𝓞 K)) (n : ℕ) (s : ℝ) (hs : s ≠ 0) :
    PMF (Fin n → 𝓞 K) :=
  PMF.normalize (fun x => ENNReal.ofReal (numberFieldGaussianWeight K n s x))
    (numberFieldGaussianWeight_sum_ne_zero K b n s hs)
    (summable_numberFieldGaussianWeight K b n s hs).tsum_ofReal_ne_top

theorem numberFieldGaussian_apply (b : Basis (Fin d) ℤ (𝓞 K))
    (n : ℕ) (s : ℝ) (hs : s ≠ 0) (x : Fin n → 𝓞 K) :
    numberFieldGaussian K b n s hs x =
      ENNReal.ofReal (numberFieldGaussianWeight K n s x / numberFieldGaussianPartition K n s) := by
  simp only [numberFieldGaussian, PMF.normalize_apply]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => (numberFieldGaussianWeight_pos K n s _).le)
    (summable_numberFieldGaussianWeight K b n s hs), ← div_eq_mul_inv]
  exact (ENNReal.ofReal_div_of_pos (numberFieldGaussianPartition_pos K b n s hs)).symm

/-- The basis is used to prove convergence; it does not change the law. -/
theorem numberFieldGaussian_basis_independent {d' : ℕ}
    (b : Basis (Fin d) ℤ (𝓞 K)) (b' : Basis (Fin d') ℤ (𝓞 K))
    (n : ℕ) (s : ℝ) (hs : s ≠ 0) :
    numberFieldGaussian K b n s hs = numberFieldGaussian K b' n s hs := rfl

theorem numberFieldGaussianPartition_eq_ellipsoid (b : Basis (Fin d) ℤ (𝓞 K))
    (n : ℕ) (s : ℝ) (hs : s ≠ 0) :
    ellipsoidPartition (numberFieldGaussianShape K b n s hs) 0 = numberFieldGaussianPartition K n s := by
  unfold ellipsoidPartition numberFieldGaussianPartition
  rw [← (ringPowerCoordinates b n).toEquiv.tsum_eq]
  exact tsum_congr (numberFieldGaussianShape_weight K b n s hs)

theorem numberFieldGaussian_coordinate_law (b : Basis (Fin d) ℤ (𝓞 K))
    (n : ℕ) (s : ℝ) (hs : s ≠ 0) :
    (numberFieldGaussian K b n s hs).map (ringPowerCoordinates b n) =
      ellipsoidalGaussian (numberFieldGaussianShape K b n s hs) 0 := by
  classical
  ext z
  obtain ⟨x, rfl⟩ := (ringPowerCoordinates b n).surjective z
  rw [PMF.map_apply]
  simp only [(ringPowerCoordinates b n).injective.eq_iff, tsum_ite_eq']
  rw [numberFieldGaussian_apply, ellipsoidalGaussian_apply, numberFieldGaussianShape_weight,
    numberFieldGaussianPartition_eq_ellipsoid]

end GeometricGaussianLHL
end

end NumberFieldGaussian

section MatrixHintLaw

/-!
## Independent hint columns and their actual matrix law

Sampling the columns of `R` independently and returning `X * R + 1`
gives independent translated pushforward columns. Their total variation
adds, and the good-event joint theorem pays the matrix failure once.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace GeometricGaussianLHL

def independentMatrixColumns {A : Type*} {r m : ℕ} (p : Fin m → PMF (Fin r → A)) :
    PMF (Matrix (Fin r) (Fin m) A) := (independentProduct p).map Matrix.transpose

def matrixIdentityColumn {A : Type*} [Zero A] [One A] {r : ℕ} (j : Fin r) : Fin r → A :=
  fun i => (1 : Matrix (Fin r) (Fin r) A) i j

theorem matrixHint_column {A : Type*} [Semiring A] {r m : ℕ}
    (X : Matrix (Fin r) (Fin m) A) (R : Matrix (Fin m) (Fin r) A) (j : Fin r) :
    (X * R + 1).transpose j = X.mulVec (R.transpose j) + matrixIdentityColumn j := rfl

theorem independentMatrixColumns_hint_law {A : Type*} [Semiring A] {r m : ℕ}
    (X : Matrix (Fin r) (Fin m) A) (p : Fin r → PMF (Fin m → A)) :
    (independentMatrixColumns p).map (fun R => X * R + (1 : Matrix (Fin r) (Fin r) A)) =
      independentMatrixColumns (fun j => (p j).map (fun z => X.mulVec z + matrixIdentityColumn j)) := by
  rw [independentMatrixColumns, PMF.map_comp, independentMatrixColumns, ← independentProduct_map,
    PMF.map_comp]
  rfl

theorem discreteTotalVariation_independentMatrixColumns_le_uniform {A : Type*} {r m : ℕ}
    (p q : Fin m → PMF (Fin r → A)) {ε : ℝ}
    (h : ∀ j, discreteTotalVariation (p j) (q j) ≤ ε) :
    discreteTotalVariation (independentMatrixColumns p) (independentMatrixColumns q) ≤ (m : ℝ) * ε := by
  change discreteTotalVariation ((independentProduct p).map (Equiv.piComm (fun _ _ => A)))
    ((independentProduct q).map (Equiv.piComm (fun _ _ => A))) ≤ _
  rw [discreteTotalVariation_map_equiv]
  exact discreteTotalVariation_independentProduct_le_uniform p q h

theorem discreteTotalVariation_matrixHint_le {A : Type*} [Ring A] {r m : ℕ}
    (X : Matrix (Fin r) (Fin m) A) (p : Fin r → PMF (Fin m → A))
    (q : Fin r → PMF (Fin r → A)) {ε : ℝ}
    (h : ∀ j, discreteTotalVariation ((p j).map X.mulVec) (q j) ≤ ε) :
    discreteTotalVariation ((independentMatrixColumns p).map (fun R => X * R + (1 : Matrix (Fin r) (Fin r) A)))
      (independentMatrixColumns (fun j => (q j).map (Equiv.addRight (matrixIdentityColumn j)))) ≤
        (r : ℝ) * ε := by
  rw [independentMatrixColumns_hint_law]
  apply discreteTotalVariation_independentMatrixColumns_le_uniform
  intro j
  have ht := discreteTotalVariation_map_equiv ((p j).map X.mulVec) (q j)
    (Equiv.addRight (matrixIdentityColumn j))
  rw [PMF.map_comp] at ht
  exact ht.le.trans (h j)

theorem discreteTotalVariation_matrixHint_joint_good_event {A : Type*} [Ring A] {r m : ℕ}
    (p : PMF (Matrix (Fin r) (Fin m) A))
    (u : Matrix (Fin r) (Fin m) A → Fin r → PMF (Fin m → A))
    (q : Matrix (Fin r) (Fin m) A → Fin r → PMF (Fin r → A))
    (G : Set (Matrix (Fin r) (Fin m) A)) {δ ε : ℝ}
    (hprob : ENNReal.ofReal (1 - δ) ≤ p.toOuterMeasure G) (hε : 0 ≤ ε)
    (h : ∀ X ∈ G, ∀ j, discreteTotalVariation ((u X j).map X.mulVec) (q X j) ≤ ε) :
    discreteTotalVariation
      (jointPMF p (fun X => (independentMatrixColumns (u X)).map
        (fun R => X * R + (1 : Matrix (Fin r) (Fin r) A))))
      (jointPMF p (fun X => independentMatrixColumns
        (fun j => (q X j).map (Equiv.addRight (matrixIdentityColumn j))))) ≤ δ + (r : ℝ) * ε := by
  apply discreteTotalVariation_joint_le_of_event_mass p _ _ G hprob (by positivity)
  intro X hX
  exact discreteTotalVariation_matrixHint_le X (u X) (q X) (h X hX)

end GeometricGaussianLHL
end

end MatrixHintLaw

section MinimumNormRightInverse

/-!
## The orthogonal right inverse of a surjection

The inverse on the kernel's orthogonal complement, included into the
ambient domain, is the minimum-norm right inverse used in spherical
Gaussian shaping. Its two composition identities retain the actual
orthogonal projection and its operator norm is the transverse inverse norm.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace GeometricGaussianLHL

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

def minimumNormRightInverse (A : E →L[ℝ] F) (hA : Function.Surjective A) : F →L[ℝ] E :=
  A.toLinearMap.kerᗮ.subtypeL.comp
    (kernelOrthogonalEquiv A.toLinearMap hA).symm.toContinuousLinearEquiv.toContinuousLinearMap

theorem minimumNormRightInverse_apply (A : E →L[ℝ] F) (hA : Function.Surjective A) (y : F) :
    minimumNormRightInverse A hA y =
      ((kernelOrthogonalEquiv A.toLinearMap hA).symm y : E) := rfl

theorem self_comp_minimumNormRightInverse (A : E →L[ℝ] F) (hA : Function.Surjective A) :
    A.comp (minimumNormRightInverse A hA) = ContinuousLinearMap.id ℝ F := by
  ext y
  change A.toLinearMap ((kernelOrthogonalEquiv A.toLinearMap hA).symm y : E) = y
  rw [← kernelOrthogonalEquiv_apply A.toLinearMap hA, LinearEquiv.apply_symm_apply]

theorem minimumNormRightInverse_comp_self (A : E →L[ℝ] F) (hA : Function.Surjective A) :
    (minimumNormRightInverse A hA).comp A = A.toLinearMap.kerᗮ.starProjection := by
  ext x
  exact congrArg (fun z : A.toLinearMap.kerᗮ => (z : E))
    (kernelOrthogonalEquiv_symm_apply_map A.toLinearMap hA x)

theorem minimumNormRightInverse_adjoint_comp_adjoint (A : E →L[ℝ] F)
    (hA : Function.Surjective A) :
    (minimumNormRightInverse A hA).adjoint.comp A.adjoint = ContinuousLinearMap.id ℝ F := by
  rw [← ContinuousLinearMap.adjoint_comp, self_comp_minimumNormRightInverse,
    ContinuousLinearMap.adjoint_id]

theorem adjoint_comp_minimumNormRightInverse_adjoint (A : E →L[ℝ] F)
    (hA : Function.Surjective A) :
    A.adjoint.comp (minimumNormRightInverse A hA).adjoint = A.toLinearMap.kerᗮ.starProjection := by
  rw [← ContinuousLinearMap.adjoint_comp, minimumNormRightInverse_comp_self,
    A.toLinearMap.kerᗮ.starProjection_isSymmetric.clm_adjoint_eq]

theorem kernelProjection_comp_adjoint (A : E →L[ℝ] F) :
    A.toLinearMap.ker.starProjection.comp A.adjoint = 0 := by
  have h : A.comp A.toLinearMap.ker.starProjection = 0 := by
    ext x
    exact (A.toLinearMap.ker.orthogonalProjectionOnto x).property
  have ha := congrArg ContinuousLinearMap.adjoint h
  simpa only [ContinuousLinearMap.adjoint_comp,
    A.toLinearMap.ker.starProjection_isSymmetric.clm_adjoint_eq,
    map_zero] using ha

theorem minimumNormRightInverse_adjoint_comp_projection (A : E →L[ℝ] F)
    (hA : Function.Surjective A) :
    (minimumNormRightInverse A hA).adjoint.comp A.toLinearMap.kerᗮ.starProjection =
      (minimumNormRightInverse A hA).adjoint := by
  have h : A.toLinearMap.kerᗮ.starProjection.comp (minimumNormRightInverse A hA) =
      minimumNormRightInverse A hA := by
    ext y
    exact Submodule.starProjection_eq_self_iff.mpr
      ((kernelOrthogonalEquiv A.toLinearMap hA).symm y).property
  have ha := congrArg ContinuousLinearMap.adjoint h
  simpa only [ContinuousLinearMap.adjoint_comp,
    A.toLinearMap.kerᗮ.starProjection_isSymmetric.clm_adjoint_eq] using ha

theorem minimumNormRightInverse_norm (A : E →L[ℝ] F) (hA : Function.Surjective A) :
    ‖minimumNormRightInverse A hA‖ =
      ‖(kernelOrthogonalEquiv A.toLinearMap hA).symm.toContinuousLinearEquiv.toContinuousLinearMap‖ :=
  A.toLinearMap.kerᗮ.subtypeₗᵢ.norm_toContinuousLinearMap_comp

theorem minimumNormRightInverse_norm_inverse (A : E →L[ℝ] F) (hA : Function.Surjective A) :
    ‖minimumNormRightInverse A hA‖⁻¹ = kernelMinimumStretch A.toLinearMap hA := by
  rw [minimumNormRightInverse_norm]
  rfl

theorem one_le_norm_mul_rightInverse [Nontrivial F] (A : E →L[ℝ] F)
    (hA : Function.Surjective A) : 1 ≤ ‖A‖ * ‖minimumNormRightInverse A hA‖ := by
  have h := ContinuousLinearMap.opNorm_comp_le A (minimumNormRightInverse A hA)
  rwa [self_comp_minimumNormRightInverse, ContinuousLinearMap.norm_id] at h

theorem surjective_operator_norm_pos [Nontrivial F] (A : E →L[ℝ] F)
    (hA : Function.Surjective A) : 0 < ‖A‖ := by
  have h := one_le_norm_mul_rightInverse A hA
  by_contra hn
  have hz := le_antisymm (le_of_not_gt hn) (norm_nonneg A)
  rw [hz, zero_mul] at h
  norm_num at h

theorem minimumNormRightInverse_norm_pos [Nontrivial F] (A : E →L[ℝ] F)
    (hA : Function.Surjective A) : 0 < ‖minimumNormRightInverse A hA‖ := by
  rw [minimumNormRightInverse_norm]
  exact (kernelOrthogonalEquiv A.toLinearMap hA).symm.toContinuousLinearEquiv.norm_pos

end GeometricGaussianLHL
end

end MinimumNormRightInverse

section AdjointMinimumStretch

/-!
## From an adjoint lower bound to the smallest nonzero singular value

A positive uniform lower bound on the adjoint forces surjectivity. The
same constant bounds the map on the orthogonal complement of its kernel,
and hence bounds its coordinate-free smallest nonzero singular value.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open scoped InnerProductSpace

namespace GeometricGaussianLHL

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

theorem surjective_of_adjoint_lower (f : E →ₗ[ℝ] F) {c : ℝ} (hc : 0 < c)
    (h : ∀ y, c * ‖y‖ ≤ ‖f.adjoint y‖) : Function.Surjective f := by
  have hk : f.adjoint.ker = ⊥ := by
    apply LinearMap.ker_eq_bot.mpr
    apply (injective_iff_map_eq_zero _).mpr
    intro y hy
    have hb := h y
    rw [hy, norm_zero] at hb
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg y])
  apply LinearMap.range_eq_top.mp
  have he := congrArg (fun U : Submodule ℝ F => Uᗮ) hk
  rwa [← LinearMap.orthogonal_range, Submodule.orthogonal_orthogonal,
    Submodule.bot_orthogonal_eq_top] at he

theorem transverse_lower_of_adjoint_lower (f : E →ₗ[ℝ] F) {c : ℝ} (hc : 0 < c)
    (h : ∀ y, c * ‖y‖ ≤ ‖f.adjoint y‖) (x : f.kerᗮ) :
    c * ‖x‖ ≤ ‖f (x : E)‖ := by
  have hx : (x : E) ∈ f.adjoint.range := by
    simpa only [← LinearMap.orthogonal_ker] using x.property
  obtain ⟨y, hy⟩ := hx
  have hb := h y
  rw [hy] at hb
  have hi : ‖(x : E)‖ ^ 2 ≤ ‖f (x : E)‖ * ‖y‖ := by
    rw [← real_inner_self_eq_norm_sq]
    conv_lhs => lhs; rw [← hy]
    rw [LinearMap.adjoint_inner_left]
    exact real_inner_le_norm _ _ |>.trans_eq (mul_comm _ _)
  by_cases hx0 : (x : E) = 0
  · simp [hx0]
  · have hp : 0 < ‖(x : E)‖ := norm_pos_iff.mpr hx0
    change c * ‖(x : E)‖ ≤ ‖f (x : E)‖
    apply (mul_le_mul_iff_left₀ hp).mp
    calc
      (c * ‖(x : E)‖) * ‖(x : E)‖ = c * ‖(x : E)‖ ^ 2 := by ring
      _ ≤ c * (‖f (x : E)‖ * ‖y‖) := mul_le_mul_of_nonneg_left hi hc.le
      _ = ‖f (x : E)‖ * (c * ‖y‖) := by ring
      _ ≤ ‖f (x : E)‖ * ‖(x : E)‖ := mul_le_mul_of_nonneg_left hb (norm_nonneg _)

theorem minimumStretch_of_adjoint_lower [Nontrivial F] (f : E →ₗ[ℝ] F)
    (hf : Function.Surjective f) {c : ℝ} (hc : 0 < c)
    (h : ∀ y, c * ‖y‖ ≤ ‖f.adjoint y‖) : c ≤ kernelMinimumStretch f hf :=
  (le_kernelMinimumStretch_iff f hf hc).mpr (transverse_lower_of_adjoint_lower f hc h)

theorem kernelMinimumStretch_le_opNorm [Nontrivial F] (f : E →ₗ[ℝ] F)
    (hf : Function.Surjective f) : kernelMinimumStretch f hf ≤ ‖f.toContinuousLinearMap‖ := by
  have he := minimumNormRightInverse_norm_inverse f.toContinuousLinearMap hf
  change ‖minimumNormRightInverse f.toContinuousLinearMap hf‖⁻¹ = kernelMinimumStretch f hf at he
  rw [← he, ← one_div]
  exact (div_le_iff₀ (minimumNormRightInverse_norm_pos f.toContinuousLinearMap hf)).mpr
    (one_le_norm_mul_rightInverse f.toContinuousLinearMap hf)

end GeometricGaussianLHL
end

end AdjointMinimumStretch

section LatticeGaussianMoment

/-!
## Linear exponential moments on actual full lattices

Transporting the coefficient Gaussian through an integral basis cancels
that basis from the adjoint quadratic form. The resulting moment bound
uses the physical shape, without a basis condition number.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open scoped ENNReal InnerProductSpace

namespace GeometricGaussianLHL

variable {n : ℕ} (L : Submodule ℤ (Euclidean n)) [DiscreteTopology L] [IsZLattice ℝ L]

theorem latticeGaussian_exp_moment (S : Euclidean n ≃L[ℝ] Euclidean n)
    (h : Euclidean n) :
    (∑' v : L, latticeGaussian L S v * ENNReal.ofReal (Real.exp (⟪h, (v : Euclidean n)⟫_ℝ))) ≤
      ENNReal.ofReal (Real.exp (‖S.toContinuousLinearMap.adjoint h‖ ^ 2 / (4 * Real.pi))) := by
  have hmass (z : Coeff n) : latticeGaussian L S (fullLatticeCoordinateEquiv L z) =
      ellipsoidalGaussian (latticeCoefficientShape L S) 0 z := by
    have he := pmf_map_equiv_apply (latticeGaussian L S)
      (fullLatticeCoordinateEquiv L).symm.toEquiv (fullLatticeCoordinateEquiv L z)
    simpa only [LinearEquiv.coe_toEquiv, LinearEquiv.symm_apply_apply,
      latticeGaussian_coordinate_law] using he.symm
  have hc : (fullLatticeRealEquiv L).toContinuousLinearMap.comp
      (latticeCoefficientShape L S).toContinuousLinearMap = S.toContinuousLinearMap := by
    ext x : 1
    exact (fullLatticeRealEquiv L).apply_symm_apply (S x)
  have ha := congrArg (fun T : Euclidean n →L[ℝ] Euclidean n => T.adjoint h) hc
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_apply] at ha
  rw [← (fullLatticeCoordinateEquiv L).toEquiv.tsum_eq]
  simp only [LinearEquiv.coe_toEquiv, hmass, ← fullLatticeRealEquiv_integer]
  simpa only [ha, ContinuousLinearMap.adjoint_inner_left, ContinuousLinearEquiv.coe_coe] using ellipsoidalGaussian_exp_moment_ennreal_le
    (latticeCoefficientShape L S) ((fullLatticeRealEquiv L).toContinuousLinearMap.adjoint h)

theorem latticeGaussian_exp_moment_opNorm (S : Euclidean n ≃L[ℝ] Euclidean n)
    {b : ℝ} (hb : 0 ≤ b) (hS : ‖S.toContinuousLinearMap‖ ≤ b) (h : Euclidean n) :
    (∑' v : L, latticeGaussian L S v * ENNReal.ofReal (Real.exp (⟪h, (v : Euclidean n)⟫_ℝ))) ≤
      ENNReal.ofReal (Real.exp (b ^ 2 * ‖h‖ ^ 2 / (4 * Real.pi))) := by
  apply (latticeGaussian_exp_moment L S h).trans
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hn : ‖S.toContinuousLinearMap.adjoint h‖ ≤ b * ‖h‖ := by
    calc
      _ ≤ ‖S.toContinuousLinearMap.adjoint‖ * ‖h‖ := S.toContinuousLinearMap.adjoint.le_opNorm h
      _ = ‖S.toContinuousLinearMap‖ * ‖h‖ := by rw [ContinuousLinearMap.adjoint.norm_map]
      _ ≤ b * ‖h‖ := mul_le_mul_of_nonneg_right hS (norm_nonneg _)
  simpa only [mul_pow] using (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hb (norm_nonneg _))).mpr hn

end GeometricGaussianLHL
end

end LatticeGaussianMoment

section CanonicalEuclidean

/-!
## Orthonormal Euclidean coordinates for the canonical ring lattice

The ring lattice, matrix action, and kernel are transported through the
actual canonical orthonormal coordinates. The intrinsic smoothing parameter
is unchanged, so no basis-condition factor enters Gaussian pushforward.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Module NumberField

namespace GeometricGaussianLHL

variable (K : Type*) [Field K] [NumberField K] {d r m : ℕ}

local instance euclideanEmbeddingsFintype : Fintype (K →+* ℂ) := inferInstance
local instance euclideanAmbientInner : InnerProductSpace ℝ (CanonicalAmbient K) := inferInstance
local instance euclideanSpaceInner : InnerProductSpace ℝ (canonicalSpace K) := inferInstance
local instance euclideanPowerInner (n : ℕ) : InnerProductSpace ℝ (CanonicalPower K n) := inferInstance

def canonicalEuclideanEmbedding (b : Basis (Fin d) ℤ (𝓞 K)) (n : ℕ) :
    (Fin n → 𝓞 K) →ₗ[ℤ] Euclidean (n * d) :=
  ((canonicalOrthonormalCoordinates K b n).toLinearMap.restrictScalars ℤ).comp
    (canonicalPowerEmbedding K n)

theorem canonicalEuclideanEmbedding_injective (b : Basis (Fin d) ℤ (𝓞 K)) (n : ℕ) :
    Function.Injective (canonicalEuclideanEmbedding K b n) :=
  (canonicalOrthonormalCoordinates K b n).injective.comp (canonicalPowerEmbedding_injective K n)

def canonicalEuclideanLattice (b : Basis (Fin d) ℤ (𝓞 K)) (n : ℕ) :
    Submodule ℤ (Euclidean (n * d)) := (canonicalEuclideanEmbedding K b n).range

theorem canonicalEuclideanLattice_eq_image (b : Basis (Fin d) ℤ (𝓞 K)) (n : ℕ) :
    canonicalEuclideanLattice K b n =
      latticeImage (canonicalOrthonormalCoordinates K b n).toContinuousLinearEquiv.toContinuousLinearMap
        (canonicalLattice K n) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨canonicalPowerEmbedding K n x, ⟨x, rfl⟩, rfl⟩
  · rintro ⟨z, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, rfl⟩

instance canonicalEuclideanLattice_discrete (b : Basis (Fin d) ℤ (𝓞 K)) (n : ℕ) :
    DiscreteTopology (canonicalEuclideanLattice K b n) := by
  letI := canonicalLattice_discrete K b n
  rw [canonicalEuclideanLattice_eq_image]
  exact latticeImage_discrete (canonicalOrthonormalCoordinates K b n).toContinuousLinearEquiv _

instance canonicalEuclideanLattice_isZLattice (b : Basis (Fin d) ℤ (𝓞 K)) (n : ℕ) :
    IsZLattice ℝ (canonicalEuclideanLattice K b n) := by
  constructor
  rw [canonicalEuclideanLattice_eq_image]
  exact latticeImage_equiv_span_top _ (canonicalLattice_span K b n)
    (canonicalOrthonormalCoordinates K b n).toContinuousLinearEquiv

def canonicalEuclideanLatticeEquiv (b : Basis (Fin d) ℤ (𝓞 K)) (n : ℕ) :
    (Fin n → 𝓞 K) ≃ₗ[ℤ] canonicalEuclideanLattice K b n :=
  LinearEquiv.ofInjective (canonicalEuclideanEmbedding K b n)
    (canonicalEuclideanEmbedding_injective K b n)

@[simp] theorem canonicalEuclideanLatticeEquiv_apply (b : Basis (Fin d) ℤ (𝓞 K))
    (n : ℕ) (x : Fin n → 𝓞 K) :
    (canonicalEuclideanLatticeEquiv K b n x : Euclidean (n * d)) =
      canonicalEuclideanEmbedding K b n x := rfl

def canonicalEuclideanMatrix (b : Basis (Fin d) ℤ (𝓞 K))
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) : Euclidean (m * d) →ₗ[ℝ] Euclidean (r * d) :=
  (canonicalOrthonormalCoordinates K b r).toLinearMap.comp
    ((canonicalMatrixMap K b X).comp (canonicalOrthonormalCoordinates K b m).symm.toLinearMap)

theorem canonicalEuclideanMatrix_integer (b : Basis (Fin d) ℤ (𝓞 K))
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) (x : Fin m → 𝓞 K) :
    canonicalEuclideanMatrix K b X (canonicalEuclideanEmbedding K b m x) =
      canonicalEuclideanEmbedding K b r (X.mulVec x) := by
  change canonicalOrthonormalCoordinates K b r (canonicalMatrixMap K b X
    ((canonicalOrthonormalCoordinates K b m).symm
      (canonicalOrthonormalCoordinates K b m (canonicalPowerEmbedding K m x)))) = _
  rw [LinearIsometryEquiv.symm_apply_apply, canonicalMatrixMap_integer]
  rfl

theorem canonicalEuclideanMatrix_surjective (b : Basis (Fin d) ℤ (𝓞 K))
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) (hX : Function.Surjective X.mulVec) :
    Function.Surjective (canonicalEuclideanMatrix K b X) :=
  (canonicalOrthonormalCoordinates K b r).surjective.comp
    ((canonicalMatrixMap_surjective K b X hX).comp (canonicalOrthonormalCoordinates K b m).symm.surjective)

theorem canonicalEuclideanMatrix_lattice (b : Basis (Fin d) ℤ (𝓞 K))
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) :
    ∀ x ∈ canonicalEuclideanLattice K b m,
      canonicalEuclideanMatrix K b X x ∈ canonicalEuclideanLattice K b r := by
  rintro _ ⟨x, rfl⟩
  exact ⟨X.mulVec x, (canonicalEuclideanMatrix_integer K b X x).symm⟩

theorem canonicalEuclideanRestriction_apply (b : Basis (Fin d) ℤ (𝓞 K))
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) (x : Fin m → 𝓞 K) :
    latticeRestriction (canonicalEuclideanLattice K b m) (canonicalEuclideanLattice K b r)
      (canonicalEuclideanMatrix K b X) (canonicalEuclideanMatrix_lattice K b X)
      (canonicalEuclideanLatticeEquiv K b m x) = canonicalEuclideanLatticeEquiv K b r (X.mulVec x) :=
  Subtype.ext (canonicalEuclideanMatrix_integer K b X x)

theorem canonicalEuclideanRestriction_surjective (b : Basis (Fin d) ℤ (𝓞 K))
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) (hX : Function.Surjective X.mulVec) :
    Function.Surjective (latticeRestriction (canonicalEuclideanLattice K b m)
      (canonicalEuclideanLattice K b r) (canonicalEuclideanMatrix K b X)
      (canonicalEuclideanMatrix_lattice K b X)) := by
  intro y
  obtain ⟨z, rfl⟩ := (canonicalEuclideanLatticeEquiv K b r).surjective y
  obtain ⟨x, rfl⟩ := hX z
  exact ⟨canonicalEuclideanLatticeEquiv K b m x, canonicalEuclideanRestriction_apply K b X x⟩

set_option maxRecDepth 2000 in
theorem canonicalEuclideanKernel_eq_image (b : Basis (Fin d) ℤ (𝓞 K))
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) :
    latticeKernel (canonicalEuclideanLattice K b m) (canonicalEuclideanMatrix K b X) =
      latticeImage (canonicalOrthonormalCoordinates K b m).toContinuousLinearEquiv.toContinuousLinearMap
        (canonicalKernel K X) := by
  ext y
  constructor
  · rintro ⟨⟨x, rfl⟩, hx⟩
    refine ⟨canonicalPowerEmbedding K m x, ⟨x, ?_, rfl⟩, rfl⟩
    apply canonicalEuclideanEmbedding_injective K b r
    change canonicalEuclideanEmbedding K b r (X.mulVec x) = canonicalEuclideanEmbedding K b r 0
    rw [map_zero, ← canonicalEuclideanMatrix_integer]
    exact hx
  · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨⟨x, rfl⟩, ?_⟩
    change canonicalEuclideanMatrix K b X (canonicalEuclideanEmbedding K b m x) = 0
    rw [canonicalEuclideanMatrix_integer, show X.mulVec x = 0 from hx, map_zero]

set_option maxRecDepth 2000 in
theorem canonicalEuclideanKernel_span (b : Basis (Fin d) ℤ (𝓞 K))
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) :
    Submodule.span ℝ
      (latticeKernel (canonicalEuclideanLattice K b m) (canonicalEuclideanMatrix K b X) : Set _) =
        (canonicalEuclideanMatrix K b X).ker := by
  rw [canonicalEuclideanKernel_eq_image, latticeImage_real_span, canonicalKernel_span_eq_ker K b X]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change canonicalOrthonormalCoordinates K b r (canonicalMatrixMap K b X
      ((canonicalOrthonormalCoordinates K b m).symm (canonicalOrthonormalCoordinates K b m x))) = 0
    rw [LinearIsometryEquiv.symm_apply_apply, show canonicalMatrixMap K b X x = 0 from hx, map_zero]
  · intro hy
    refine ⟨(canonicalOrthonormalCoordinates K b m).symm y, ?_,
      (canonicalOrthonormalCoordinates K b m).apply_symm_apply y⟩
    apply (canonicalOrthonormalCoordinates K b r).injective
    change canonicalEuclideanMatrix K b X y = canonicalOrthonormalCoordinates K b r 0
    rw [map_zero]
    exact hy

theorem canonicalEuclideanKernel_smoothing (b : Basis (Fin d) ℤ (𝓞 K))
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) (ε : ℝ) :
    smoothingParameter
      (latticeKernel (canonicalEuclideanLattice K b m) (canonicalEuclideanMatrix K b X)) ε =
        smoothingParameter (canonicalKernel K X) ε := by
  rw [canonicalEuclideanKernel_eq_image, smoothingParameter_isometry_all]

end GeometricGaussianLHL
end

end CanonicalEuclidean

section CanonicalEmbeddingProjection

/-!
## Complex-embedding projections of the canonical space

Evaluation at each complex embedding is a real linear contraction. The
sum of the projected squared norms is exactly the canonical squared norm,
including both members of each nonreal conjugate pair and all real places.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Module NumberField

namespace GeometricGaussianLHL

variable (K : Type*) [Field K] [NumberField K] {d : ℕ}

local instance projectionEmbeddingsFintype : Fintype (K →+* ℂ) := inferInstance
local instance projectionAmbientInner : InnerProductSpace ℝ (CanonicalAmbient K) := inferInstance
local instance projectionSpaceInner : InnerProductSpace ℝ (canonicalSpace K) := inferInstance
local instance projectionPowerInner (n : ℕ) : InnerProductSpace ℝ (CanonicalPower K n) := inferInstance

def canonicalEmbeddingProjection (n : ℕ) (τ : K →+* ℂ) :
    CanonicalPower K n →ₗ[ℝ] EuclideanSpace ℂ (Fin n) where
  toFun Y := WithLp.toLp 2 (fun j => (Y j : CanonicalAmbient K) τ)
  map_add' Y Z := by ext j; simp
  map_smul' c Y := by ext j; simp

omit [NumberField K] in
theorem canonicalEmbeddingProjection_apply (n : ℕ) (τ : K →+* ℂ)
    (Y : CanonicalPower K n) (j : Fin n) :
    canonicalEmbeddingProjection K n τ Y j = (Y j : CanonicalAmbient K) τ := rfl

theorem canonicalPower_norm_sq_sum_embeddings (n : ℕ) (Y : CanonicalPower K n) :
    ‖Y‖ ^ 2 = ∑ τ : K →+* ℂ, ‖canonicalEmbeddingProjection K n τ Y‖ ^ 2 := by
  calc
    ‖Y‖ ^ 2 = ∑ j : Fin n, ∑ τ : K →+* ℂ, ‖(Y j : CanonicalAmbient K) τ‖ ^ 2 := by
      rw [PiLp.norm_sq_eq_of_L2]
      apply Finset.sum_congr rfl
      intro j _
      exact EuclideanSpace.norm_sq_eq (Y j : CanonicalAmbient K)
    _ = _ := by
      simp only [EuclideanSpace.norm_sq_eq, canonicalEmbeddingProjection_apply]
      exact Finset.sum_comm

theorem canonicalEmbeddingProjection_norm_le (n : ℕ) (τ : K →+* ℂ) (Y : CanonicalPower K n) :
    ‖canonicalEmbeddingProjection K n τ Y‖ ≤ ‖Y‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [canonicalPower_norm_sq_sum_embeddings K n Y]
  exact Finset.single_le_sum (fun σ _ => sq_nonneg ‖canonicalEmbeddingProjection K n σ Y‖)
    (Finset.mem_univ τ)

theorem canonicalEmbeddingProjection_opNorm_le (n : ℕ) (τ : K →+* ℂ) :
    ‖(canonicalEmbeddingProjection K n τ).toContinuousLinearMap‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro Y
  simpa only [one_mul, LinearMap.coe_toContinuousLinearMap'] using canonicalEmbeddingProjection_norm_le K n τ Y

def canonicalEuclideanProjection (b : Basis (Fin d) ℤ (𝓞 K)) (n : ℕ) (τ : K →+* ℂ) :
    Euclidean (n * d) →L[ℝ] EuclideanSpace ℂ (Fin n) :=
  (canonicalEmbeddingProjection K n τ).toContinuousLinearMap.comp
    (canonicalOrthonormalCoordinates K b n).symm.toContinuousLinearEquiv.toContinuousLinearMap

theorem canonicalEuclideanProjection_opNorm_le (b : Basis (Fin d) ℤ (𝓞 K)) (n : ℕ)
    (τ : K →+* ℂ) : ‖canonicalEuclideanProjection K b n τ‖ ≤ 1 := by
  rw [canonicalEuclideanProjection, ContinuousLinearMap.opNorm_comp_linearIsometryEquiv]
  exact canonicalEmbeddingProjection_opNorm_le K n τ

theorem canonicalEuclideanProjection_integer (b : Basis (Fin d) ℤ (𝓞 K)) (n : ℕ)
    (τ : K →+* ℂ) (x : Fin n → 𝓞 K) (j : Fin n) :
    canonicalEuclideanProjection K b n τ (canonicalEuclideanEmbedding K b n x) j =
      τ (algebraMap (𝓞 K) K (x j)) := by
  change canonicalEmbeddingProjection K n τ
    ((canonicalOrthonormalCoordinates K b n).symm
      (canonicalOrthonormalCoordinates K b n (canonicalPowerEmbedding K n x))) j = _
  rw [LinearIsometryEquiv.symm_apply_apply]
  rfl

end GeometricGaussianLHL
end

end CanonicalEmbeddingProjection

section NumberFieldEllipsoid

/-!
## Ellipsoidal Gaussians on the actual ring lattice

The law is a PMF on ring vectors. Its point masses are the canonical
Euclidean Gaussian weights divided by their actual sum. Orthonormal
coordinates identify the law with the normalized lattice Gaussian and
intertwine ring-matrix multiplication with the canonical real matrix.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Module NumberField

namespace GeometricGaussianLHL

variable (K : Type*) [Field K] [NumberField K] {d r m : ℕ}

local instance ellipsoidEmbeddingsFintype : Fintype (K →+* ℂ) := inferInstance
local instance ellipsoidAmbientInner : InnerProductSpace ℝ (CanonicalAmbient K) := inferInstance
local instance ellipsoidSpaceInner : InnerProductSpace ℝ (canonicalSpace K) := inferInstance
local instance ellipsoidPowerInner (n : ℕ) : InnerProductSpace ℝ (CanonicalPower K n) := inferInstance

def numberFieldEllipsoidPartition (b : Basis (Fin d) ℤ (𝓞 K)) (n : ℕ)
    (S : Euclidean (n * d) ≃L[ℝ] Euclidean (n * d)) : ℝ :=
  ∑' x : Fin n → 𝓞 K, gaussianWeight 1 (S.symm (canonicalEuclideanEmbedding K b n x))

theorem numberFieldEllipsoidPartition_eq (b : Basis (Fin d) ℤ (𝓞 K)) (n : ℕ)
    (S : Euclidean (n * d) ≃L[ℝ] Euclidean (n * d)) :
    latticeGaussianPartition (canonicalEuclideanLattice K b n) S =
      numberFieldEllipsoidPartition K b n S := by
  unfold latticeGaussianPartition numberFieldEllipsoidPartition
  rw [← (canonicalEuclideanLatticeEquiv K b n).toEquiv.tsum_eq]
  rfl

theorem summable_numberFieldEllipsoidWeight (b : Basis (Fin d) ℤ (𝓞 K)) (n : ℕ)
    (S : Euclidean (n * d) ≃L[ℝ] Euclidean (n * d)) :
    Summable (fun x : Fin n → 𝓞 K => gaussianWeight 1 (S.symm (canonicalEuclideanEmbedding K b n x))) := by
  have h := (summable_latticeGaussianWeight (canonicalEuclideanLattice K b n) S).comp_injective
    (canonicalEuclideanLatticeEquiv K b n).injective
  apply h.congr
  intro x
  rfl

theorem numberFieldEllipsoidPartition_pos (b : Basis (Fin d) ℤ (𝓞 K)) (n : ℕ)
    (S : Euclidean (n * d) ≃L[ℝ] Euclidean (n * d)) :
    0 < numberFieldEllipsoidPartition K b n S := by
  rw [← numberFieldEllipsoidPartition_eq]
  exact latticeGaussianPartition_pos _ _

def numberFieldEllipsoidalGaussian (b : Basis (Fin d) ℤ (𝓞 K)) (n : ℕ)
    (S : Euclidean (n * d) ≃L[ℝ] Euclidean (n * d)) (c : Fin n → 𝓞 K) : PMF (Fin n → 𝓞 K) :=
  (latticeGaussianCentered (canonicalEuclideanLattice K b n) S (canonicalEuclideanLatticeEquiv K b n c)).map
    (canonicalEuclideanLatticeEquiv K b n).symm

/-- The defining Gaussian point masses, with a proved positive and convergent normalization. -/
theorem numberFieldEllipsoidalGaussian_apply (b : Basis (Fin d) ℤ (𝓞 K)) (n : ℕ)
    (S : Euclidean (n * d) ≃L[ℝ] Euclidean (n * d)) (c x : Fin n → 𝓞 K) :
    numberFieldEllipsoidalGaussian K b n S c x = ENNReal.ofReal
      (gaussianWeight 1 (S.symm (canonicalEuclideanEmbedding K b n x - canonicalEuclideanEmbedding K b n c)) /
        numberFieldEllipsoidPartition K b n S) := by
  have he := pmf_map_equiv_apply
    (latticeGaussianCentered (canonicalEuclideanLattice K b n) S (canonicalEuclideanLatticeEquiv K b n c))
    (canonicalEuclideanLatticeEquiv K b n).symm.toEquiv (canonicalEuclideanLatticeEquiv K b n x)
  simp only [LinearEquiv.coe_toEquiv, LinearEquiv.symm_apply_apply] at he
  rw [numberFieldEllipsoidalGaussian, he, latticeGaussianCentered_apply,
    canonicalEuclideanLatticeEquiv_apply, canonicalEuclideanLatticeEquiv_apply,
    numberFieldEllipsoidPartition_eq]

theorem numberFieldEllipsoidPartition_shift (b : Basis (Fin d) ℤ (𝓞 K)) (n : ℕ)
    (S : Euclidean (n * d) ≃L[ℝ] Euclidean (n * d)) (c : Fin n → 𝓞 K) :
    (∑' x : Fin n → 𝓞 K, gaussianWeight 1
      (S.symm (canonicalEuclideanEmbedding K b n x - canonicalEuclideanEmbedding K b n c))) =
        numberFieldEllipsoidPartition K b n S := by
  rw [← (Equiv.addRight c).tsum_eq]
  change (∑' x : Fin n → 𝓞 K, gaussianWeight 1
    (S.symm (canonicalEuclideanEmbedding K b n (x + c) - canonicalEuclideanEmbedding K b n c))) = _
  simp only [map_add, add_sub_cancel_right]
  rfl

theorem numberFieldEllipsoidalGaussian_coordinate_law (b : Basis (Fin d) ℤ (𝓞 K)) (n : ℕ)
    (S : Euclidean (n * d) ≃L[ℝ] Euclidean (n * d)) (c : Fin n → 𝓞 K) :
    (numberFieldEllipsoidalGaussian K b n S c).map (canonicalEuclideanLatticeEquiv K b n) =
      latticeGaussianCentered (canonicalEuclideanLattice K b n) S (canonicalEuclideanLatticeEquiv K b n c) := by
  rw [numberFieldEllipsoidalGaussian, PMF.map_comp]
  have h : (canonicalEuclideanLatticeEquiv K b n ∘ (canonicalEuclideanLatticeEquiv K b n).symm) = id := by
    funext x
    exact (canonicalEuclideanLatticeEquiv K b n).apply_symm_apply x
  rw [h, PMF.map_id]

theorem numberFieldEllipsoidalGaussian_map_matrix (b : Basis (Fin d) ℤ (𝓞 K))
    (X : Matrix (Fin r) (Fin m) (𝓞 K))
    (S : Euclidean (m * d) ≃L[ℝ] Euclidean (m * d)) (c : Fin m → 𝓞 K) :
    ((numberFieldEllipsoidalGaussian K b m S c).map X.mulVec).map (canonicalEuclideanLatticeEquiv K b r) =
      (latticeGaussianCentered (canonicalEuclideanLattice K b m) S (canonicalEuclideanLatticeEquiv K b m c)).map
        (latticeRestriction (canonicalEuclideanLattice K b m) (canonicalEuclideanLattice K b r)
          (canonicalEuclideanMatrix K b X) (canonicalEuclideanMatrix_lattice K b X)) := by
  rw [numberFieldEllipsoidalGaussian, PMF.map_comp, PMF.map_comp]
  congr 1
  funext v
  obtain ⟨x, rfl⟩ := (canonicalEuclideanLatticeEquiv K b m).surjective v
  simp only [Function.comp_apply, LinearEquiv.symm_apply_apply]
  exact (canonicalEuclideanRestriction_apply K b X x).symm

end GeometricGaussianLHL
end

end NumberFieldEllipsoid

section NumberFieldMatrixLaw

/-!
## Independent number-field matrices in coefficient coordinates

The matrix distribution has independent actual ring-Gaussian columns.
Its pushforward through the integral-basis coordinate map is exactly the
independent ellipsoidal PMF in the coefficient certificate.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Module NumberField
open scoped ENNReal

namespace GeometricGaussianLHL

theorem independentProduct_map_equiv {α β : Type*} {n : ℕ}
    (p : Fin n → PMF α) (e : α ≃ β) :
    (independentProduct p).map (fun X i => e (X i)) = independentProduct (fun i => (p i).map e) := by
  let E := Equiv.piCongrRight (fun _ : Fin n => e)
  ext Y
  obtain ⟨X, rfl⟩ := E.surjective Y
  change (independentProduct p).map E (E X) = _
  rw [pmf_map_equiv_apply]
  simp only [independentProduct_apply]
  apply Finset.prod_congr rfl
  intro i _
  exact (pmf_map_equiv_apply (p i) e (X i)).symm

variable (K : Type*) [Field K] [NumberField K] {d r m : ℕ}

def numberFieldMatrixLaw (b : Basis (Fin d) ℤ (𝓞 K)) (r m : ℕ) (s : ℝ) (hs : s ≠ 0) :
    PMF (Matrix (Fin r) (Fin m) (𝓞 K)) :=
  (independentProduct (fun _ : Fin m => numberFieldGaussian K b r s hs)).map Matrix.transpose

def matrixColumnCoordinates (b : Basis (Fin d) ℤ (𝓞 K)) (r m : ℕ) :
    Matrix (Fin r) (Fin m) (𝓞 K) ≃ (Fin m → Coeff (r * d)) where
  toFun X j := ringPowerCoordinates b r (fun i => X i j)
  invFun Z i j := (ringPowerCoordinates b r).symm (Z j) i
  left_inv X := by
    funext i j
    exact congrFun ((ringPowerCoordinates b r).symm_apply_apply (fun i => X i j)) i
  right_inv Z := by
    funext j
    exact (ringPowerCoordinates b r).apply_symm_apply (Z j)

omit [NumberField K] in
@[simp] theorem matrixColumnCoordinates_apply (b : Basis (Fin d) ℤ (𝓞 K))
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) (j : Fin m) :
    matrixColumnCoordinates K b r m X j = ringPowerCoordinates b r (fun i => X i j) := rfl

theorem numberFieldMatrixLaw_coordinate_law (b : Basis (Fin d) ℤ (𝓞 K))
    (r m : ℕ) (s : ℝ) (hs : s ≠ 0) :
    (numberFieldMatrixLaw K b r m s hs).map (matrixColumnCoordinates K b r m) =
      ellipsoidalColumnLaw m (numberFieldGaussianShape K b r s hs) := by
  rw [numberFieldMatrixLaw, PMF.map_comp]
  change (independentProduct (fun _ : Fin m => numberFieldGaussian K b r s hs)).map
    (fun X j => (ringPowerCoordinates b r).toEquiv (X j)) = _
  rw [independentProduct_map_equiv]
  simp only [LinearEquiv.coe_toEquiv, numberFieldGaussian_coordinate_law]
  rfl

end GeometricGaussianLHL
end

end NumberFieldMatrixLaw

section GaussianParameterStability

/-!
## Parameter stability for coefficient Gaussian distributions

The paper's relative precision error gives a common ellipsoid containing
all but `ξ` of each distribution. The normalization argument proves an
absolute constant `128` for the actual coefficient Gaussian PMFs. Transport
to arbitrary full lattices is handled separately.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory
open scoped ENNReal

namespace GeometricGaussianLHL

variable {R : ℕ}

def gaussianStabilityHeight (R : ℕ) (ξ : ℝ) : ℝ := R + Real.log (1 / ξ)

theorem gaussianStabilityHeight_pos {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1) :
    0 < gaussianStabilityHeight R ξ := by
  have h := Real.log_pos ((lt_div_iff₀ hξ).mpr (show (1 : ℝ) * ξ < 1 by simpa))
  unfold gaussianStabilityHeight
  positivity

def gaussianStabilityRegion (S : Euclidean R ≃L[ℝ] Euclidean R) (ξ : ℝ) : Set (Coeff R) :=
  {z | ‖S.symm (integerEmbedding R z)‖ ^ 2 ≤ 4 * gaussianStabilityHeight R ξ}

theorem ellipsoidalGaussian_common_tail (S T : Euclidean R ≃L[ℝ] Euclidean R)
    {ξ θ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1) (hθhalf : θ ≤ 1 / 2)
    (hrel : ‖relativePrecision S T‖ ≤ θ) :
    (ellipsoidalGaussian T 0).toMeasure (gaussianStabilityRegion S ξ)ᶜ ≤ ENNReal.ofReal ξ := by
  have hsub : (gaussianStabilityRegion S ξ)ᶜ ⊆
      {z : Coeff R | 2 * (R + Real.log (1 / ξ)) < ‖T.symm (integerEmbedding R z)‖ ^ 2} := by
    intro z hz
    change ¬‖S.symm (integerEmbedding R z)‖ ^ 2 ≤ 4 * gaussianStabilityHeight R ξ at hz
    have hz' := lt_of_not_ge hz
    have hl := relativePrecision_lower S T hrel (integerEmbedding R z)
    have hθsq := mul_le_mul_of_nonneg_right hθhalf (sq_nonneg ‖S.symm (integerEmbedding R z)‖)
    change 2 * (R + Real.log (1 / ξ)) < ‖T.symm (integerEmbedding R z)‖ ^ 2
    dsimp only [gaussianStabilityHeight] at hz'
    nlinarith
  exact ((ellipsoidalGaussian T 0).toMeasure.mono hsub).trans
    (ellipsoidalGaussian_standardized_tail T hξ hξ1.le)

theorem ellipsoidWeight_relative_on (S T : Euclidean R ≃L[ℝ] Euclidean R)
    {ξ θ : ℝ} (hθ : 0 ≤ θ) (hrel : ‖relativePrecision S T‖ ≤ θ)
    (z : Coeff R) (hz : z ∈ gaussianStabilityRegion S ξ) :
    ellipsoidWeight S 0 z ≤ Real.exp (4 * Real.pi * θ * gaussianStabilityHeight R ξ) * ellipsoidWeight T 0 z ∧
    ellipsoidWeight T 0 z ≤ Real.exp (4 * Real.pi * θ * gaussianStabilityHeight R ξ) * ellipsoidWeight S 0 z := by
  have h := relativePrecision_quadratic_bound S T hrel (integerEmbedding R z)
  have hh := mul_le_mul_of_nonneg_left (show ‖S.symm (integerEmbedding R z)‖ ^ 2 ≤
    4 * gaussianStabilityHeight R ξ from hz) hθ
  have hb : |‖T.symm (integerEmbedding R z)‖ ^ 2 - ‖S.symm (integerEmbedding R z)‖ ^ 2| ≤
      4 * θ * gaussianStabilityHeight R ξ := by nlinarith
  obtain ⟨hl, hu⟩ := abs_le.mp hb
  have h₁ := mul_le_mul_of_nonneg_left hl Real.pi_pos.le
  have h₂ := mul_le_mul_of_nonneg_left hu Real.pi_pos.le
  simp only [ellipsoidWeight, sub_zero, gaussianWeight, one_pow, mul_one]
  constructor <;> rw [← Real.exp_add, Real.exp_le_exp] <;> nlinarith

theorem ellipsoidalGaussian_relative_on (S T : Euclidean R ≃L[ℝ] Euclidean R)
    {ξ θ : ℝ} (hθ : 0 ≤ θ) (hrel : ‖relativePrecision S T‖ ≤ θ)
    (z : Coeff R) (hz : z ∈ gaussianStabilityRegion S ξ) :
    (ellipsoidalGaussian S 0 z).toReal ≤
        Real.exp (4 * Real.pi * θ * gaussianStabilityHeight R ξ) *
          (ellipsoidPartition T 0 / ellipsoidPartition S 0) * (ellipsoidalGaussian T 0 z).toReal ∧
    (ellipsoidPartition T 0 / ellipsoidPartition S 0) * (ellipsoidalGaussian T 0 z).toReal ≤
        Real.exp (4 * Real.pi * θ * gaussianStabilityHeight R ξ) * (ellipsoidalGaussian S 0 z).toReal := by
  obtain ⟨h₁, h₂⟩ := ellipsoidWeight_relative_on S T hθ hrel z hz
  have hS := ellipsoidPartition_pos S 0
  have hT := ellipsoidPartition_pos T 0
  rw [ellipsoidalGaussian_toReal, ellipsoidalGaussian_toReal]
  constructor
  · calc
      _ ≤ (Real.exp (4 * Real.pi * θ * gaussianStabilityHeight R ξ) * ellipsoidWeight T 0 z) /
          ellipsoidPartition S 0 := div_le_div_of_nonneg_right h₁ hS.le
      _ = _ := by field_simp
  · calc
      _ = ellipsoidWeight T 0 z / ellipsoidPartition S 0 := by field_simp
      _ ≤ (Real.exp (4 * Real.pi * θ * gaussianStabilityHeight R ξ) * ellipsoidWeight S 0 z) /
          ellipsoidPartition S 0 := div_le_div_of_nonneg_right h₂ hS.le
      _ = _ := by ring

theorem ellipsoidalGaussian_parameter_stability (S T : Euclidean R ≃L[ℝ] Euclidean R)
    {ξ θ : ℝ} (hξ : 0 < ξ) (hξhalf : ξ < 1 / 2) (hθ : 0 < θ) (hθhalf : θ ≤ 1 / 2)
    (hrel : ‖relativePrecision S T‖ ≤ θ) :
    discreteTotalVariation (ellipsoidalGaussian S 0) (ellipsoidalGaussian T 0) ≤
      128 * (ξ + θ * (R + Real.log (1 / ξ))) := by
  have hξ1 : ξ < 1 := by linarith
  have hH : 0 < gaussianStabilityHeight R ξ := gaussianStabilityHeight_pos hξ hξ1
  have hself : ‖relativePrecision S S‖ ≤ θ := by simpa [relativePrecision] using hθ.le
  have hp := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (ellipsoidalGaussian_common_tail S S hξ hξ1 hθhalf hself)
  have hq := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (ellipsoidalGaussian_common_tail S T hξ hξ1 hθhalf hrel)
  rw [ENNReal.toReal_ofReal hξ.le] at hp hq
  have h := discreteTotalVariation_le_of_reweight_on (ellipsoidalGaussian S 0) (ellipsoidalGaussian T 0)
    (gaussianStabilityRegion S ξ) hξ.le hξhalf.le
    (show 0 ≤ 4 * Real.pi * θ * gaussianStabilityHeight R ξ by positivity)
    (div_pos (ellipsoidPartition_pos T 0) (ellipsoidPartition_pos S 0)) hp hq
    (fun z hz => ellipsoidalGaussian_relative_on S T hθ.le hrel z hz)
  have hprod : 0 ≤ θ * gaussianStabilityHeight R ξ := mul_nonneg hθ.le hH.le
  have hpi := mul_le_mul_of_nonneg_right Real.pi_lt_four.le hprod
  change discreteTotalVariation _ _ ≤ 128 * (ξ + θ * gaussianStabilityHeight R ξ)
  nlinarith

end GeometricGaussianLHL
end

end GaussianParameterStability

section NumberFieldGaussianMoment

/-!
## Actual number-field Gaussian exponential moments

The normalized ring-vector law inherits the full-lattice moment bound
through its proved coordinate equivalence. The shape and test vector are
both measured in canonical orthonormal coordinates.
-/

noncomputable section

open Module NumberField
open scoped ENNReal InnerProductSpace

namespace GeometricGaussianLHL

variable (K : Type*) [Field K] [NumberField K] {d : ℕ}

theorem numberFieldEllipsoidalGaussian_exp_moment (b : Basis (Fin d) ℤ (𝓞 K)) (n : ℕ)
    (S : Euclidean (n * d) ≃L[ℝ] Euclidean (n * d)) (h : Euclidean (n * d)) :
    (∑' x : Fin n → 𝓞 K, numberFieldEllipsoidalGaussian K b n S 0 x *
      ENNReal.ofReal (Real.exp (⟪h, canonicalEuclideanEmbedding K b n x⟫_ℝ))) ≤
        ENNReal.ofReal (Real.exp (‖S.toContinuousLinearMap.adjoint h‖ ^ 2 / (4 * Real.pi))) := by
  let e := canonicalEuclideanLatticeEquiv K b n
  have hmass (v : canonicalEuclideanLattice K b n) :
      numberFieldEllipsoidalGaussian K b n S 0 (e.symm v) =
        latticeGaussian (canonicalEuclideanLattice K b n) S v := by
    unfold numberFieldEllipsoidalGaussian
    rw [map_zero, latticeGaussianCentered_zero]
    exact pmf_map_equiv_apply _ e.symm.toEquiv v
  have he (v : canonicalEuclideanLattice K b n) :
      canonicalEuclideanEmbedding K b n (e.symm v) = (v : Euclidean (n * d)) := by
    exact congrArg Subtype.val (e.apply_symm_apply v)
  rw [← e.symm.toEquiv.tsum_eq]
  simpa only [LinearEquiv.coe_toEquiv, hmass, he] using
    latticeGaussian_exp_moment (canonicalEuclideanLattice K b n) S h

theorem numberFieldEllipsoidalGaussian_exp_moment_opNorm (b : Basis (Fin d) ℤ (𝓞 K)) (n : ℕ)
    (S : Euclidean (n * d) ≃L[ℝ] Euclidean (n * d)) {B : ℝ} (hB : 0 ≤ B)
    (hS : ‖S.toContinuousLinearMap‖ ≤ B) (h : Euclidean (n * d)) :
    (∑' x : Fin n → 𝓞 K, numberFieldEllipsoidalGaussian K b n S 0 x *
      ENNReal.ofReal (Real.exp (⟪h, canonicalEuclideanEmbedding K b n x⟫_ℝ))) ≤
        ENNReal.ofReal (Real.exp (B ^ 2 * ‖h‖ ^ 2 / (4 * Real.pi))) := by
  apply (numberFieldEllipsoidalGaussian_exp_moment K b n S h).trans
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hn : ‖S.toContinuousLinearMap.adjoint h‖ ≤ B * ‖h‖ := by
    calc
      _ ≤ ‖S.toContinuousLinearMap.adjoint‖ * ‖h‖ := S.toContinuousLinearMap.adjoint.le_opNorm h
      _ = ‖S.toContinuousLinearMap‖ * ‖h‖ := by rw [ContinuousLinearMap.adjoint.norm_map]
      _ ≤ B * ‖h‖ := mul_le_mul_of_nonneg_right hS (norm_nonneg _)
  simpa only [mul_pow] using (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hB (norm_nonneg _))).mpr hn

end GeometricGaussianLHL
end

end NumberFieldGaussianMoment

section NumberFieldSphericalGaussian

/-!
## Spherical ring Gaussians and covariance invariance

Scalar Euclidean shapes recover the actual spherical ring Gaussian.
Equal covariances give equal normalized ring-vector laws, including every
ring-valued center. These identities identify the shaped image with the
spherical target in Corollary 5.2.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Module NumberField

namespace GeometricGaussianLHL

def euclideanScalarShape (n : ℕ) (w : ℝ) (hw : w ≠ 0) : Euclidean n ≃L[ℝ] Euclidean n :=
  ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := Euclidean n) (Units.mk0 w hw)

theorem euclideanScalarShape_apply (n : ℕ) (w : ℝ) (hw : w ≠ 0) (x : Euclidean n) :
    euclideanScalarShape n w hw x = w • x := rfl

theorem euclideanScalarShape_symm_apply (n : ℕ) (w : ℝ) (hw : w ≠ 0) (x : Euclidean n) :
    (euclideanScalarShape n w hw).symm x = w⁻¹ • x := rfl

theorem euclideanScalarShape_toCLM (n : ℕ) (w : ℝ) (hw : w ≠ 0) :
    (euclideanScalarShape n w hw).toContinuousLinearMap = w • ContinuousLinearMap.id ℝ (Euclidean n) := by
  ext x : 1
  rfl

theorem euclideanScalarShape_covariance (n : ℕ) (w : ℝ) (hw : w ≠ 0) :
    shapeCovariance (euclideanScalarShape n w hw) = w ^ 2 • ContinuousLinearMap.id ℝ (Euclidean n) := by
  unfold shapeCovariance
  rw [euclideanScalarShape_toCLM, map_smul, ContinuousLinearMap.adjoint_id,
    ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul,
    ContinuousLinearMap.id_comp, smul_smul]
  rw [pow_two]

variable (K : Type*) [Field K] [NumberField K] {d : ℕ}

local instance sphericalEmbeddingsFintype : Fintype (K →+* ℂ) := inferInstance
local instance sphericalAmbientInner : InnerProductSpace ℝ (CanonicalAmbient K) := inferInstance
local instance sphericalSpaceInner : InnerProductSpace ℝ (canonicalSpace K) := inferInstance
local instance sphericalPowerInner (n : ℕ) : InnerProductSpace ℝ (CanonicalPower K n) := inferInstance

theorem numberFieldScalarShape_weight (b : Basis (Fin d) ℤ (𝓞 K)) (n : ℕ)
    (w : ℝ) (hw : w ≠ 0) (x : Fin n → 𝓞 K) :
    gaussianWeight 1 ((euclideanScalarShape (n * d) w hw).symm (canonicalEuclideanEmbedding K b n x)) =
      numberFieldGaussianWeight K n w x := by
  rw [euclideanScalarShape_symm_apply]
  change gaussianWeight 1 (w⁻¹ • canonicalOrthonormalCoordinates K b n (canonicalPowerEmbedding K n x)) =
    gaussianWeight (1 / w) (canonicalPowerEmbedding K n x)
  simp only [gaussianWeight, norm_smul, Real.norm_eq_abs, LinearIsometryEquiv.norm_map,
    mul_pow, sq_abs, inv_pow, one_pow, one_div]
  congr 1
  ring

theorem numberFieldScalarShape_partition (b : Basis (Fin d) ℤ (𝓞 K)) (n : ℕ)
    (w : ℝ) (hw : w ≠ 0) :
    numberFieldEllipsoidPartition K b n (euclideanScalarShape (n * d) w hw) =
      numberFieldGaussianPartition K n w := by
  unfold numberFieldEllipsoidPartition numberFieldGaussianPartition
  exact tsum_congr (numberFieldScalarShape_weight K b n w hw)

theorem numberFieldScalarShape_gaussian_zero (b : Basis (Fin d) ℤ (𝓞 K)) (n : ℕ)
    (w : ℝ) (hw : w ≠ 0) :
    numberFieldEllipsoidalGaussian K b n (euclideanScalarShape (n * d) w hw) 0 =
      numberFieldGaussian K b n w hw := by
  ext x
  rw [numberFieldEllipsoidalGaussian_apply, map_zero, sub_zero,
    numberFieldScalarShape_weight, numberFieldScalarShape_partition, numberFieldGaussian_apply]

theorem numberFieldEllipsoidalGaussian_translate (b : Basis (Fin d) ℤ (𝓞 K)) (n : ℕ)
    (S : Euclidean (n * d) ≃L[ℝ] Euclidean (n * d)) (c : Fin n → 𝓞 K) :
    (numberFieldEllipsoidalGaussian K b n S 0).map (Equiv.addRight c) =
      numberFieldEllipsoidalGaussian K b n S c := by
  ext y
  obtain ⟨x, rfl⟩ := (Equiv.addRight c).surjective y
  rw [pmf_map_equiv_apply, numberFieldEllipsoidalGaussian_apply, numberFieldEllipsoidalGaussian_apply]
  change ENNReal.ofReal (gaussianWeight 1 (S.symm (canonicalEuclideanEmbedding K b n x -
    canonicalEuclideanEmbedding K b n 0)) / _) = ENNReal.ofReal
      (gaussianWeight 1 (S.symm (canonicalEuclideanEmbedding K b n (x + c) -
        canonicalEuclideanEmbedding K b n c)) / _)
  rw [map_zero, sub_zero, map_add, add_sub_cancel_right]

theorem numberFieldEllipsoidalGaussian_covariance_congr (b : Basis (Fin d) ℤ (𝓞 K)) (n : ℕ)
    (S T : Euclidean (n * d) ≃L[ℝ] Euclidean (n * d))
    (h : shapeCovariance S = shapeCovariance T) (c : Fin n → 𝓞 K) :
    numberFieldEllipsoidalGaussian K b n S c = numberFieldEllipsoidalGaussian K b n T c := by
  have hw (x : Euclidean (n * d)) : gaussianWeight 1 (S.symm x) = gaussianWeight 1 (T.symm x) := by
    have hn := equiv_symm_norm_sq_eq_of_covariance_eq S T h x
    simp only [gaussianWeight, hn]
  have hp : numberFieldEllipsoidPartition K b n S = numberFieldEllipsoidPartition K b n T := by
    unfold numberFieldEllipsoidPartition
    exact tsum_congr (fun x => hw (canonicalEuclideanEmbedding K b n x))
  ext x
  rw [numberFieldEllipsoidalGaussian_apply, numberFieldEllipsoidalGaussian_apply, hw, hp]

theorem numberFieldScalarShape_gaussian (b : Basis (Fin d) ℤ (𝓞 K)) (n : ℕ)
    (w : ℝ) (hw : w ≠ 0) (c : Fin n → 𝓞 K) :
    numberFieldEllipsoidalGaussian K b n (euclideanScalarShape (n * d) w hw) c =
      (numberFieldGaussian K b n w hw).map (Equiv.addRight c) := by
  rw [← numberFieldScalarShape_gaussian_zero K b n w hw, numberFieldEllipsoidalGaussian_translate]

end GeometricGaussianLHL
end

end NumberFieldSphericalGaussian

section NumberFieldProducts

/-!
## Product coefficient laws for power-of-two number fields

Corollary 2.2 is an equality of the actual canonical ring-Gaussian PMF with
independent integer Gaussians in power-basis coordinates. The same equality
is proved for vectors and independently sampled ring-matrix columns.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Module NumberField

namespace GeometricGaussianLHL

variable (K : Type*) [Field K] [NumberField K] {d : ℕ}

theorem numberFieldGaussianShape_weight_of_diagonal (b : Basis (Fin d) ℤ (𝓞 K))
    {c : ℝ} (hc : 0 < c) (hGram : ∀ i j, canonicalGram K b i j = if i = j then c else 0)
    (n : ℕ) {s : ℝ} (hs : 0 < s) (z : Coeff (n * d)) :
    ellipsoidWeight (numberFieldGaussianShape K b n s hs.ne') 0 z =
      gaussianWeight (1 / (s / Real.sqrt c)) (integerEmbedding (n * d) z) := by
  have hsqrt : Real.sqrt c ≠ 0 := (Real.sqrt_pos.mpr hc).ne'
  unfold ellipsoidWeight gaussianWeight
  rw [sub_zero, numberFieldGaussianShape_symm_apply, norm_smul, Real.norm_eq_abs,
    abs_inv, abs_of_pos hs, LinearIsometryEquiv.norm_map,
    powerCanonicalEquiv_norm_of_diagonal K b hc.le hGram]
  congr 1
  field_simp

theorem numberFieldGaussian_product_of_diagonal (b : Basis (Fin d) ℤ (𝓞 K))
    {c : ℝ} (hc : 0 < c) (hGram : ∀ i j, canonicalGram K b i j = if i = j then c else 0)
    (n : ℕ) {s : ℝ} (hs : 0 < s) :
    (numberFieldGaussian K b n s hs.ne').map (ringPowerCoordinates b n) =
      productIntegerGaussian (n * d) (s / Real.sqrt c) (div_pos hs (Real.sqrt_pos.mpr hc)) := by
  rw [numberFieldGaussian_coordinate_law]
  exact ellipsoidalGaussian_eq_product_of_isotropic_weight _ (div_pos hs (Real.sqrt_pos.mpr hc))
    (numberFieldGaussianShape_weight_of_diagonal K b hc hGram n hs)

variable {k : ℕ} [IsCyclotomicExtension {2 ^ (k + 1)} ℚ K] {ζ : K}

/-- Corollary 2.2, including the coordinatewise law on arbitrary powers of
the ring of integers and the degree-one field. -/
theorem powerTwoGaussian_product (hζ : IsPrimitiveRoot ζ (2 ^ (k + 1)))
    (n : ℕ) {s : ℝ} (hs : 0 < s) :
    (numberFieldGaussian K (cyclotomicIntegralBasis K hζ) n s hs.ne').map
      (ringPowerCoordinates (cyclotomicIntegralBasis K hζ) n) =
      productIntegerGaussian (n * (2 ^ (k + 1)).totient)
        (s / Real.sqrt (2 ^ (k + 1)).totient) (by positivity) := by
  have hd : (0 : ℝ) < (2 ^ (k + 1)).totient := by
    exact_mod_cast Nat.totient_pos.mpr (pow_pos (by norm_num : 0 < (2 : ℕ)) _)
  exact numberFieldGaussian_product_of_diagonal K _ hd (powerTwoGram_diagonal K hζ) n hs

theorem powerTwoMatrix_product (hζ : IsPrimitiveRoot ζ (2 ^ (k + 1)))
    (r m : ℕ) {s : ℝ} (hs : 0 < s) :
    (numberFieldMatrixLaw K (cyclotomicIntegralBasis K hζ) r m s hs.ne').map
      (matrixColumnCoordinates K (cyclotomicIntegralBasis K hζ) r m) =
      coefficientColumnLaw (r * (2 ^ (k + 1)).totient) m
        (s / Real.sqrt (2 ^ (k + 1)).totient) (by positivity) := by
  have h := powerTwoGaussian_product K hζ r hs
  rw [numberFieldGaussian_coordinate_law] at h
  rw [numberFieldMatrixLaw_coordinate_law]
  simp only [ellipsoidalColumnLaw, coefficientColumnLaw, h]

end GeometricGaussianLHL
end

end NumberFieldProducts

section LatticeParameterStability

/-!
## Parameter stability on every full Euclidean lattice

Lemma 2.5, with the universal constant `128`, for Gaussian PMFs normalized
on the actual lattice. A concrete precision prescription gives any target
distance in `(0,1]`; explicit comparisons justify its asserted asymptotic
scale as the target distance tends to zero.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Module

namespace GeometricGaussianLHL

variable {n : ℕ}

theorem latticeGaussian_parameter_stability (L : Submodule ℤ (Euclidean n))
    [DiscreteTopology L] [IsZLattice ℝ L] (S T : Euclidean n ≃L[ℝ] Euclidean n)
    {ξ θ : ℝ} (hξ : 0 < ξ) (hξhalf : ξ < 1 / 2) (hθ : 0 < θ) (hθhalf : θ ≤ 1 / 2)
    (hrel : ‖relativePrecision S T‖ ≤ θ) :
    discreteTotalVariation (latticeGaussian L S) (latticeGaussian L T) ≤
      128 * (ξ + θ * (n + Real.log (1 / ξ))) := by
  rw [latticeGaussian_totalVariation_coordinates]
  apply ellipsoidalGaussian_parameter_stability _ _ hξ hξhalf hθ hθhalf
  simpa only [latticeCoefficientShape, relativePrecision_change_coordinates] using hrel

/-- The exact covariance-inverse formulation in Lemma 2.5. Invertible
shapes include all the positive-definite parameter matrices in the paper. -/
theorem lattice_parameter_stability_certificate (L : Submodule ℤ (Euclidean n))
    [DiscreteTopology L] [IsZLattice ℝ L] (S T : Euclidean n ≃L[ℝ] Euclidean n)
    {ξ θ : ℝ} (hξ : 0 < ξ) (hξhalf : ξ < 1 / 2) (hθ : 0 < θ) (hθhalf : θ ≤ 1 / 2)
    (hQ : ‖S.toContinuousLinearMap.adjoint.comp
      ((Ring.inverse (shapeCovariance T) - Ring.inverse (shapeCovariance S)).comp S.toContinuousLinearMap)‖ ≤ θ) :
    discreteTotalVariation (latticeGaussian L S) (latticeGaussian L T) ≤
      128 * (ξ + θ * (n + Real.log (1 / ξ))) := by
  apply latticeGaussian_parameter_stability L S T hξ hξhalf hθ hθhalf
  simpa only [relativePrecision, shapePrecision_eq_covariance_inverse] using hQ

def gaussianTargetPrecision (n : ℕ) (τ : ℝ) : ℝ := τ / (256 * (n + Real.log (256 / τ)))

theorem gaussianTargetPrecision_height_ge_one {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    1 ≤ (n : ℝ) + Real.log (256 / τ) := by
  have hd : 0 < (256 : ℝ) / τ := by positivity
  have he : Real.exp 1 ≤ 256 / τ := Real.exp_one_lt_three.le.trans
    ((le_div_iff₀ hτ).mpr (by linarith))
  have hl := (Real.le_log_iff_exp_le hd).mpr he
  linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

theorem gaussianTargetPrecision_admissible {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    0 < τ / 256 ∧ τ / 256 < 1 / 2 ∧
      0 < gaussianTargetPrecision n τ ∧ gaussianTargetPrecision n τ ≤ 1 / 2 := by
  have hh : 1 ≤ (n : ℝ) + Real.log (256 / τ) := gaussianTargetPrecision_height_ge_one hτ hτ1
  refine ⟨by positivity, by linarith, ?_, ?_⟩
  · unfold gaussianTargetPrecision
    positivity
  · unfold gaussianTargetPrecision
    apply (div_le_iff₀ (show 0 < 256 * ((n : ℝ) + Real.log (256 / τ)) by positivity)).mpr
    linarith

theorem latticeGaussian_target_precision (L : Submodule ℤ (Euclidean n))
    [DiscreteTopology L] [IsZLattice ℝ L] (S T : Euclidean n ≃L[ℝ] Euclidean n)
    {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hrel : ‖relativePrecision S T‖ ≤ gaussianTargetPrecision n τ) :
    discreteTotalVariation (latticeGaussian L S) (latticeGaussian L T) ≤ τ := by
  obtain ⟨hξ, hξhalf, hθ, hθhalf⟩ := gaussianTargetPrecision_admissible (n := n) hτ hτ1
  have hh : 1 ≤ (n : ℝ) + Real.log (256 / τ) := gaussianTargetPrecision_height_ge_one hτ hτ1
  have hh0 : (n : ℝ) + Real.log (256 / τ) ≠ 0 := by linarith
  have hi : 1 / (τ / 256) = 256 / τ := by field_simp
  have hm : gaussianTargetPrecision n τ * ((n : ℝ) + Real.log (1 / (τ / 256))) = τ / 256 := by
    rw [hi, gaussianTargetPrecision]
    field_simp
  calc
    _ ≤ 128 * (τ / 256 + gaussianTargetPrecision n τ * (n + Real.log (1 / (τ / 256)))) :=
      latticeGaussian_parameter_stability L S T hξ hξhalf hθ hθhalf hrel
    _ = τ := by rw [hm]; ring

/-- Explicit constants for the paper's `Θ(τ/(n+log(1/τ)))` prescription. -/
theorem gaussianTargetPrecision_comparable {τ : ℝ} (hτ : 0 < τ) (hτhalf : τ ≤ 1 / 2) :
    τ / (2304 * (n + Real.log (1 / τ))) ≤ gaussianTargetPrecision n τ ∧
      gaussianTargetPrecision n τ ≤ τ / (256 * (n + Real.log (1 / τ))) := by
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlog : Real.log 2 ≤ Real.log (1 / τ) := Real.log_le_log (by norm_num)
    ((le_div_iff₀ hτ).mpr (by linarith))
  have hbase : 0 < (n : ℝ) + Real.log (1 / τ) := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have h256 : Real.log (256 : ℝ) = 8 * Real.log 2 := by
    rw [show (256 : ℝ) = 2 ^ (8 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have he : (n : ℝ) + Real.log (256 / τ) = (n + Real.log (1 / τ)) + 8 * Real.log 2 := by
    rw [Real.log_div (by norm_num : (256 : ℝ) ≠ 0) hτ.ne',
      Real.log_div one_ne_zero hτ.ne', Real.log_one, h256]
    ring
  have hlow : (n : ℝ) + Real.log (1 / τ) ≤ n + Real.log (256 / τ) := by rw [he]; linarith
  have hupp : (n : ℝ) + Real.log (256 / τ) ≤ 9 * (n + Real.log (1 / τ)) := by
    rw [he]
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hheight : 0 < (n : ℝ) + Real.log (256 / τ) := hbase.trans_le hlow
  unfold gaussianTargetPrecision
  constructor
  · exact div_le_div_of_nonneg_left hτ.le (by positivity) (by nlinarith)
  · exact div_le_div_of_nonneg_left hτ.le (by positivity) (by linarith)

end GeometricGaussianLHL
end

end LatticeParameterStability

section GaussianLatticeFibers

/-!
## Actual Gaussian pushforward point masses

A fiber of an integral linear map is a coset of its kernel. Reindexing the
PMF's nonnegative sum by that coset yields the shifted Gaussian partition
of the transformed kernel, divided by the original Gaussian partition.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open scoped ENNReal

namespace GeometricGaussianLHL

def linearKernelCosetEquiv {P Q : Type*} [AddCommGroup P] [AddCommGroup Q]
    (f : P →ₗ[ℤ] Q) (x : P) : f.ker ≃ {v : P // f v = f x} where
  toFun v := ⟨(v : P) + x, by rw [map_add, v.property, zero_add]⟩
  invFun v := ⟨(v : P) - x, by
    change f ((v : P) - x) = 0
    rw [map_sub, v.property, sub_self]⟩
  left_inv v := by apply Subtype.ext; exact add_sub_cancel_right _ _
  right_inv v := by apply Subtype.ext; exact sub_add_cancel _ _

theorem pmf_map_fiber {α β : Type*} (p : PMF α) (f : α → β) (b : β) :
    p.map f b = ∑' v : {a : α // f a = b}, p (v : α) := by
  classical
  rw [PMF.map_apply]
  change (∑' a : α, if b = f a then p a else 0) =
    ∑' v : ({a : α | f a = b} : Set α), p (v : α)
  rw [tsum_subtype {a : α | f a = b} (fun a => p a)]
  apply tsum_congr
  intro a
  simp only [Set.indicator_apply, Set.mem_setOf_eq, eq_comm]

theorem pmf_map_linear_kernel_coset {P Q : Type*} [AddCommGroup P] [AddCommGroup Q]
    (p : PMF P) (f : P →ₗ[ℤ] Q) (x : P) :
    p.map f (f x) = ∑' v : f.ker, p ((v : P) + x) := by
  rw [pmf_map_fiber, ← (linearKernelCosetEquiv f x).tsum_eq]
  rfl

variable {n r : ℕ} (L : Submodule ℤ (Euclidean n)) [DiscreteTopology L] [IsZLattice ℝ L]
  (M : Submodule ℤ (Euclidean r)) (A : Euclidean n →ₗ[ℝ] Euclidean r)
  (hmap : ∀ x ∈ L, A x ∈ M) (S : Euclidean n ≃L[ℝ] Euclidean n)

/-- Point mass at the image of any lattice vector, expressed as a convergent kernel sum. -/
theorem latticeGaussian_map_kernel_sum (x : L) :
    (latticeGaussian L S).map (latticeRestriction L M A hmap)
        (latticeRestriction L M A hmap x) =
      ENNReal.ofReal ((∑' v : latticeKernel L A,
        gaussianWeight 1 (S.symm ((v : Euclidean n) + (x : Euclidean n)))) /
          latticeGaussianPartition L S) := by
  rw [pmf_map_linear_kernel_coset,
    ← (latticeRestrictionKernelEquiv L M A hmap).symm.toEquiv.tsum_eq]
  have hs : Summable (fun v : latticeKernel L A =>
      gaussianWeight 1 (S.symm ((v : Euclidean n) + (x : Euclidean n)))) := by
    simpa only [sub_neg_eq_add] using
      summable_gaussianWeight_equiv_shift S.symm (latticeKernel L A) (-(x : Euclidean n))
  have hn (v : latticeKernel L A) :
      0 ≤ gaussianWeight 1 (S.symm ((v : Euclidean n) + (x : Euclidean n))) /
        latticeGaussianPartition L S :=
    div_nonneg (gaussianWeight_pos _ _).le (latticeGaussianPartition_pos L S).le
  simp only [latticeGaussian_apply]
  change (∑' v : latticeKernel L A, ENNReal.ofReal
    (gaussianWeight 1 (S.symm ((v : Euclidean n) + (x : Euclidean n))) /
      latticeGaussianPartition L S)) = _
  rw [← ENNReal.ofReal_tsum_of_nonneg hn (hs.div_const _), tsum_div_const]

/-- The same exact probability, using the actual transformed kernel partition. -/
theorem latticeGaussian_map_shifted_kernel (x : L) :
    (latticeGaussian L S).map (latticeRestriction L M A hmap)
        (latticeRestriction L M A hmap x) =
      ENNReal.ofReal
        (shiftedLatticePartition (latticeImage S.symm.toContinuousLinearMap (latticeKernel L A))
          (-(S.symm (x : Euclidean n))) / latticeGaussianPartition L S) := by
  rw [latticeGaussian_map_kernel_sum]
  have he := sum_gaussianWeight_equiv_shift S.symm (latticeKernel L A) (-(x : Euclidean n))
  simp only [sub_neg_eq_add, map_neg] at he
  rw [he]

omit [DiscreteTopology L] [IsZLattice ℝ L] in
theorem whitened_latticeKernel_span
    (hspan : Submodule.span ℝ (latticeKernel L A : Set (Euclidean n)) = A.ker) :
    Submodule.span ℝ
        (latticeImage S.symm.toContinuousLinearMap (latticeKernel L A) : Set (Euclidean n)) =
      (A.comp S.toLinearMap).ker := by
  change Submodule.span ℝ (S.symm.toLinearMap '' (latticeKernel L A : Set (Euclidean n))) = _
  rw [Submodule.span_image, hspan]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change A x = 0 at hx
    change A (S (S.symm x)) = 0
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using hx
  · intro hy
    exact ⟨S y, hy, S.symm_apply_apply y⟩

end GeometricGaussianLHL
end

end GaussianLatticeFibers

section LatticeGaussianPushforward

/-!
## Gaussian pushforward with its actual covariance

The exact kernel-fiber formula and intrinsic flatness bound the normalized
pushforward law. The transverse Gaussian is identified with any target
shape whose covariance is the actual image covariance. The positive square
root construction and number-field specialization are separate steps.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace GeometricGaussianLHL

section Covariance

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

def gaussianPushforwardCovariance (A : E →L[ℝ] F) (S : E ≃L[ℝ] E) : F →L[ℝ] F :=
  A.comp ((shapeCovariance S).comp A.adjoint)

theorem gaussianPushforwardCovariance_eq_gram (A : E →L[ℝ] F) (S : E ≃L[ℝ] E) :
    gaussianPushforwardCovariance A S =
      (A.comp S.toContinuousLinearMap).comp (A.comp S.toContinuousLinearMap).adjoint := by
  rw [ContinuousLinearMap.adjoint_comp]
  rfl

end Covariance

variable {n r : ℕ} (L : Submodule ℤ (Euclidean n)) [DiscreteTopology L] [IsZLattice ℝ L]
  (M : Submodule ℤ (Euclidean r)) [DiscreteTopology M] [IsZLattice ℝ M]
  (A : Euclidean n →ₗ[ℝ] Euclidean r) (hmap : ∀ x ∈ L, A x ∈ M)
  (S : Euclidean n ≃L[ℝ] Euclidean n) (T : Euclidean r ≃L[ℝ] Euclidean r)

omit [DiscreteTopology L] [IsZLattice ℝ L] in
theorem latticeRestriction_surjective_real
    (hsurj : Function.Surjective (latticeRestriction L M A hmap)) : Function.Surjective A := by
  apply LinearMap.range_eq_top.mp
  apply top_unique
  rw [← IsZLattice.span_top (K := ℝ) (L := M)]
  apply Submodule.span_le.mpr
  intro y hy
  obtain ⟨x, hx⟩ := hsurj ⟨y, hy⟩
  exact ⟨x, congrArg Subtype.val hx⟩

/-- The centred Gaussian pushforward bound for the actual lattice laws. -/
theorem latticeGaussian_pushforward
    (hsurj : Function.Surjective (latticeRestriction L M A hmap))
    (hspan : Submodule.span ℝ (latticeKernel L A : Set (Euclidean n)) = A.ker)
    (hcov : shapeCovariance T = gaussianPushforwardCovariance A.toContinuousLinearMap S)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hwidth : ‖S.symm.toContinuousLinearMap‖ * smoothingParameter (latticeKernel L A) ε ≤ 1) :
    discreteTotalVariation ((latticeGaussian L S).map (latticeRestriction L M A hmap))
      (latticeGaussian M T) ≤ ε / (1 - ε) := by
  let W := latticeImage S.symm.toContinuousLinearMap (latticeKernel L A)
  let : DiscreteTopology W := latticeImage_discrete S.symm (latticeKernel L A)
  let Z := latticeGaussianPartition L S
  let R := latticeGaussianPartition M T
  let V := intrinsicCovolume W
  have hZ : 0 < Z := latticeGaussianPartition_pos L S
  have hR : 0 < R := latticeGaussianPartition_pos M T
  have hV : 0 < V := intrinsicCovolume_pos W
  have hs : SmoothAt W ε 1 :=
    smoothAt_image_one_of_norm_mul_smoothingParameter_le S.symm.toContinuousLinearMap
      (latticeKernel L A) hε hwidth
  let f := A.toContinuousLinearMap.comp S.toContinuousLinearMap
  have hf : Function.Surjective f :=
    (latticeRestriction_surjective_real L M A hmap hsurj).comp S.surjective
  have hc : shapeCovariance T = f.comp f.adjoint :=
    hcov.trans (gaussianPushforwardCovariance_eq_gram A.toContinuousLinearMap S)
  apply discreteTotalVariation_le_of_flat_reweight _ _ (c := R / (V * Z)) hε.le hε1
  intro y
  obtain ⟨x, rfl⟩ := hsurj y
  let w := gaussianWeight 1 (T.symm (A (x : Euclidean n)))
  have hw : gaussianWeight 1 ((Submodule.span ℝ (W : Set (Euclidean n)))ᗮ.starProjection
      (-(S.symm (x : Euclidean n)))) = w := by
    rw [show Submodule.span ℝ (W : Set (Euclidean n)) = (A.comp S.toLinearMap).ker from
      whitened_latticeKernel_span L A S hspan, map_neg, gaussianWeight_neg]
    have he := gaussianWeight_kernel_projection_eq_inverse_shape f hf T hc (S.symm (x : Euclidean n))
    change gaussianWeight 1 ((A.comp S.toLinearMap).kerᗮ.starProjection (S.symm (x : Euclidean n))) =
      gaussianWeight 1 (T.symm (A (S (S.symm (x : Euclidean n))))) at he
    simpa only [S.apply_symm_apply, w] using he
  have hb := shiftedLatticePartition_flat W hε.le hs (-(S.symm (x : Euclidean n)))
  rw [hw] at hb
  have hmass : 0 ≤ shiftedLatticePartition W (-(S.symm (x : Euclidean n))) :=
    tsum_nonneg (fun v => (gaussianWeight_pos 1 ((v : Euclidean n) -
      (-(S.symm (x : Euclidean n))))).le)
  rw [latticeGaussian_map_shifted_kernel, ENNReal.toReal_ofReal (div_nonneg hmass hZ.le),
    latticeGaussian_apply, ENNReal.toReal_ofReal
      (div_nonneg (latticeGaussianWeight_pos M T _).le hR.le)]
  change (1 - ε) * (R / (V * Z)) * (w / R) ≤
      shiftedLatticePartition W (-(S.symm (x : Euclidean n))) / Z ∧
    shiftedLatticePartition W (-(S.symm (x : Euclidean n))) / Z ≤
      (1 + ε) * (R / (V * Z)) * (w / R)
  have he (a : ℝ) : a * (R / (V * Z)) * (w / R) = (w * (a / V)) / Z := by
    field_simp
  rw [he, he]
  exact ⟨div_le_div_of_nonneg_right hb.1 hZ.le, div_le_div_of_nonneg_right hb.2 hZ.le⟩

/-- The inverse-norm minimum-width hypothesis permits equality. -/
theorem latticeGaussian_pushforward_of_inv_norm
    (hsurj : Function.Surjective (latticeRestriction L M A hmap))
    (hspan : Submodule.span ℝ (latticeKernel L A : Set (Euclidean n)) = A.ker)
    (hcov : shapeCovariance T = gaussianPushforwardCovariance A.toContinuousLinearMap S)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hwidth : smoothingParameter (latticeKernel L A) ε ≤ ‖S.symm.toContinuousLinearMap‖⁻¹) :
    discreteTotalVariation ((latticeGaussian L S).map (latticeRestriction L M A hmap))
      (latticeGaussian M T) ≤ ε / (1 - ε) := by
  apply latticeGaussian_pushforward L M A hmap S T hsurj hspan hcov hε hε1
  by_cases hz : ‖S.symm.toContinuousLinearMap‖ = 0
  · simp only [hz, zero_mul, zero_le_one]
  · exact (mul_le_mul_of_nonneg_left hwidth (norm_nonneg _)).trans_eq (mul_inv_cancel₀ hz)

theorem latticeGaussianCentered_pushforward_bound
    (hsurj : Function.Surjective (latticeRestriction L M A hmap))
    (hspan : Submodule.span ℝ (latticeKernel L A : Set (Euclidean n)) = A.ker)
    (hcov : shapeCovariance T = gaussianPushforwardCovariance A.toContinuousLinearMap S)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hwidth : smoothingParameter (latticeKernel L A) ε ≤ ‖S.symm.toContinuousLinearMap‖⁻¹)
    (c : L) :
    discreteTotalVariation ((latticeGaussianCentered L S c).map (latticeRestriction L M A hmap))
      (latticeGaussianCentered M T (latticeRestriction L M A hmap c)) ≤ ε / (1 - ε) := by
  change discreteTotalVariation
    ((latticeGaussianCentered L S c).map (latticeRestriction L M A hmap).toAddMonoidHom)
    (latticeGaussianCentered M T ((latticeRestriction L M A hmap).toAddMonoidHom c)) ≤ _
  rw [latticeGaussianCentered_pushforward]
  exact latticeGaussian_pushforward_of_inv_norm L M A hmap S T hsurj hspan hcov hε hε1 hwidth

end GeometricGaussianLHL
end

end LatticeGaussianPushforward

section GaussianImageSquareRoot

/-!
## The positive square root of the Gaussian image covariance

The target shape is constructed from the actual positive matrix square
root. Surjectivity proves that the image covariance is positive definite;
invertibility and the covariance identity of its square root are derived.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open scoped MatrixOrder

namespace GeometricGaussianLHL

variable {n r : ℕ}

theorem positive_matrix_sqrt_bijective (C : Matrix (Fin r) (Fin r) ℝ) (hC : C.PosDef) :
    Function.Bijective (Matrix.toEuclideanLin (CFC.sqrt C)) := by
  have hu := (CFC.isUnit_sqrt_iff C hC.posSemidef.nonneg).mpr hC.isUnit
  exact (Module.End.isUnit_iff _).mp (hu.map
    (Matrix.toLpLinAlgEquiv 2 : Matrix (Fin r) (Fin r) ℝ ≃ₐ[ℝ] Module.End ℝ (Euclidean r)).toMonoidHom)

def positiveSquareRootShape (C : Matrix (Fin r) (Fin r) ℝ) (hC : C.PosDef) :
    Euclidean r ≃L[ℝ] Euclidean r :=
  (LinearEquiv.ofBijective (Matrix.toEuclideanLin (CFC.sqrt C))
    (positive_matrix_sqrt_bijective C hC)).toContinuousLinearEquiv

theorem positiveSquareRootShape_matrix (C : Matrix (Fin r) (Fin r) ℝ) (hC : C.PosDef) :
    Matrix.toEuclideanLin.symm (positiveSquareRootShape C hC).toLinearMap = CFC.sqrt C :=
  Matrix.toEuclideanLin.symm_apply_apply _

theorem positiveSquareRootShape_positive (C : Matrix (Fin r) (Fin r) ℝ) (hC : C.PosDef) :
    (positiveSquareRootShape C hC).toLinearMap.IsPositive :=
  Matrix.isPositive_toEuclideanLin_iff.mpr (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg C))

theorem positiveSquareRootShape_covariance (C : Matrix (Fin r) (Fin r) ℝ) (hC : C.PosDef) :
    shapeCovariance (positiveSquareRootShape C hC) =
      (Matrix.toEuclideanLin C).toContinuousLinearMap := by
  have hh : (CFC.sqrt C).IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg C)).isHermitian
  ext x : 1
  change Matrix.toEuclideanLin (CFC.sqrt C) ((Matrix.toEuclideanLin (CFC.sqrt C)).adjoint x) =
    Matrix.toEuclideanLin C x
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, hh.eq]
  change ((Matrix.toLpLin 2 2 (CFC.sqrt C)).comp (Matrix.toLpLin 2 2 (CFC.sqrt C))) x = _
  rw [← Matrix.toLpLin_mul_same, CFC.sqrt_mul_sqrt_self C hC.posSemidef.nonneg]

section Gram

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def gaussianGramMatrix (f : E →L[ℝ] Euclidean r) : Matrix (Fin r) (Fin r) ℝ :=
  Matrix.toEuclideanLin.symm (f.toLinearMap.comp f.toLinearMap.adjoint)

theorem gaussianGramMatrix_posDef (f : E →L[ℝ] Euclidean r) (hf : Function.Surjective f) :
    (gaussianGramMatrix f).PosDef := by
  have hp : (gaussianGramMatrix f).PosSemidef := by
    apply Matrix.isPositive_toEuclideanLin_iff.mp
    rw [gaussianGramMatrix, LinearEquiv.apply_symm_apply]
    exact LinearMap.isPositive_self_comp_adjoint f.toLinearMap
  apply hp.posDef_iff_isUnit.mpr
  have hu : IsUnit (f.toLinearMap.comp f.toLinearMap.adjoint) := by
    apply (LinearMap.isUnit_iff_ker_eq_bot _).mpr
    rw [LinearMap.ker_self_comp_adjoint, ← LinearMap.orthogonal_range,
      LinearMap.range_eq_top.mpr hf, Submodule.top_orthogonal_eq_bot]
  exact hu.map (Matrix.toLpLinAlgEquiv 2).symm.toMonoidHom

end Gram

theorem euclideanMatrix_adjoint (f : Euclidean n →ₗ[ℝ] Euclidean r) :
    Matrix.toEuclideanLin.symm f.adjoint = (Matrix.toEuclideanLin.symm f).conjTranspose := by
  apply Matrix.toEuclideanLin.injective
  rw [LinearEquiv.apply_symm_apply, Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
    LinearEquiv.apply_symm_apply]

/-- The covariance matrix is the paper's literal `A S Sᵀ Aᵀ` product. -/
theorem gaussianPushforwardCovariance_matrix (A : Euclidean n →L[ℝ] Euclidean r)
    (S : Euclidean n ≃L[ℝ] Euclidean n) :
    Matrix.toEuclideanLin.symm (gaussianPushforwardCovariance A S).toLinearMap =
      Matrix.toEuclideanLin.symm A.toLinearMap * Matrix.toEuclideanLin.symm S.toLinearMap *
        (Matrix.toEuclideanLin.symm S.toLinearMap).transpose *
        (Matrix.toEuclideanLin.symm A.toLinearMap).transpose := by
  change (Matrix.toLpLin 2 2).symm
    (A.toLinearMap.comp ((S.toLinearMap.comp S.toLinearMap.adjoint).comp A.toLinearMap.adjoint)) = _
  rw [Matrix.toLpLin_symm_comp, Matrix.toLpLin_symm_comp, Matrix.toLpLin_symm_comp,
    euclideanMatrix_adjoint, euclideanMatrix_adjoint]
  simp only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.mul_assoc]

def gaussianImageSquareRoot (A : Euclidean n →L[ℝ] Euclidean r)
    (S : Euclidean n ≃L[ℝ] Euclidean n) (hA : Function.Surjective A) :
    Euclidean r ≃L[ℝ] Euclidean r :=
  positiveSquareRootShape (gaussianGramMatrix (A.comp S.toContinuousLinearMap))
    (gaussianGramMatrix_posDef _ (hA.comp S.surjective))

theorem gaussianImageSquareRoot_matrix (A : Euclidean n →L[ℝ] Euclidean r)
    (S : Euclidean n ≃L[ℝ] Euclidean n) (hA : Function.Surjective A) :
    Matrix.toEuclideanLin.symm (gaussianImageSquareRoot A S hA).toLinearMap =
      CFC.sqrt (gaussianGramMatrix (A.comp S.toContinuousLinearMap)) :=
  positiveSquareRootShape_matrix _ _

theorem gaussianImageSquareRoot_covariance (A : Euclidean n →L[ℝ] Euclidean r)
    (S : Euclidean n ≃L[ℝ] Euclidean n) (hA : Function.Surjective A) :
    shapeCovariance (gaussianImageSquareRoot A S hA) = gaussianPushforwardCovariance A S := by
  rw [gaussianImageSquareRoot, positiveSquareRootShape_covariance, gaussianGramMatrix,
    LinearEquiv.apply_symm_apply, gaussianPushforwardCovariance_eq_gram]
  rfl

/-- The lattice pushforward theorem with the actual positive square-root target. -/
theorem latticeGaussianCentered_pushforward_sqrt
    (L : Submodule ℤ (Euclidean n)) [DiscreteTopology L] [IsZLattice ℝ L]
    (M : Submodule ℤ (Euclidean r)) [DiscreteTopology M] [IsZLattice ℝ M]
    (A : Euclidean n →ₗ[ℝ] Euclidean r) (hmap : ∀ x ∈ L, A x ∈ M)
    (hsurj : Function.Surjective (latticeRestriction L M A hmap))
    (hspan : Submodule.span ℝ (latticeKernel L A : Set (Euclidean n)) = A.ker)
    (S : Euclidean n ≃L[ℝ] Euclidean n) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hwidth : smoothingParameter (latticeKernel L A) ε ≤ ‖S.symm.toContinuousLinearMap‖⁻¹)
    (c : L) :
    discreteTotalVariation ((latticeGaussianCentered L S c).map (latticeRestriction L M A hmap))
      (latticeGaussianCentered M
        (gaussianImageSquareRoot A.toContinuousLinearMap S
          (latticeRestriction_surjective_real L M A hmap hsurj))
        (latticeRestriction L M A hmap c)) ≤ ε / (1 - ε) :=
  latticeGaussianCentered_pushforward_bound L M A hmap S _ hsurj hspan
    (gaussianImageSquareRoot_covariance _ _ _) hε hε1 hwidth c

end GeometricGaussianLHL
end

end GaussianImageSquareRoot

section NumberFieldPushforward

/-!
## Number-field Gaussian pushforward

Lemma 2.4, with the necessary error range `0 < ε < 1`.
Both distributions are actual PMFs on ring vectors. The target shape is
the positive matrix square root of the canonical image covariance, and
the smoothing hypothesis uses the original canonical kernel lattice.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Module NumberField
open scoped MatrixOrder

namespace GeometricGaussianLHL

variable (K : Type*) [Field K] [NumberField K] {d r m : ℕ}

def numberFieldImageShape (b : Basis (Fin d) ℤ (𝓞 K))
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) (hX : Function.Surjective X.mulVec)
    (S : Euclidean (m * d) ≃L[ℝ] Euclidean (m * d)) :
    Euclidean (r * d) ≃L[ℝ] Euclidean (r * d) :=
  gaussianImageSquareRoot (canonicalEuclideanMatrix K b X).toContinuousLinearMap S
    (canonicalEuclideanMatrix_surjective K b X hX)

set_option maxRecDepth 2000 in
theorem numberFieldImageShape_matrix (b : Basis (Fin d) ℤ (𝓞 K))
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) (hX : Function.Surjective X.mulVec)
    (S : Euclidean (m * d) ≃L[ℝ] Euclidean (m * d)) :
    Matrix.toEuclideanLin.symm (numberFieldImageShape K b X hX S).toLinearMap =
      CFC.sqrt (Matrix.toEuclideanLin.symm
        (gaussianPushforwardCovariance (canonicalEuclideanMatrix K b X).toContinuousLinearMap S).toLinearMap) := by
  rw [numberFieldImageShape, gaussianImageSquareRoot_matrix, gaussianPushforwardCovariance_eq_gram]
  rfl

theorem numberFieldImageShape_covariance (b : Basis (Fin d) ℤ (𝓞 K))
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) (hX : Function.Surjective X.mulVec)
    (S : Euclidean (m * d) ≃L[ℝ] Euclidean (m * d)) :
    shapeCovariance (numberFieldImageShape K b X hX S) =
      gaussianPushforwardCovariance (canonicalEuclideanMatrix K b X).toContinuousLinearMap S :=
  gaussianImageSquareRoot_covariance _ _ _

theorem numberFieldImageShape_matrix_formula (b : Basis (Fin d) ℤ (𝓞 K))
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) (hX : Function.Surjective X.mulVec)
    (S : Euclidean (m * d) ≃L[ℝ] Euclidean (m * d)) :
    Matrix.toEuclideanLin.symm (numberFieldImageShape K b X hX S).toLinearMap =
      CFC.sqrt (Matrix.toEuclideanLin.symm (canonicalEuclideanMatrix K b X) *
        Matrix.toEuclideanLin.symm S.toLinearMap * (Matrix.toEuclideanLin.symm S.toLinearMap).transpose *
          (Matrix.toEuclideanLin.symm (canonicalEuclideanMatrix K b X)).transpose) := by
  rw [numberFieldImageShape_matrix, gaussianPushforwardCovariance_matrix]
  rfl

/-- The corrected complete number-field pushforward statement. The inverse
operator norm is the minimum-width form of the smoothing hypothesis. -/
theorem numberField_gaussian_pushforward (b : Basis (Fin d) ℤ (𝓞 K))
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) (hX : Function.Surjective X.mulVec)
    (S : Euclidean (m * d) ≃L[ℝ] Euclidean (m * d)) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1)
    (hwidth : smoothingParameter (canonicalKernel K X) ε ≤ shapeMinimumStretch S)
    (c : Fin m → 𝓞 K) :
    discreteTotalVariation ((numberFieldEllipsoidalGaussian K b m S c).map X.mulVec)
      (numberFieldEllipsoidalGaussian K b r (numberFieldImageShape K b X hX S) (X.mulVec c)) ≤
        ε / (1 - ε) := by
  have hb := latticeGaussianCentered_pushforward_bound
    (canonicalEuclideanLattice K b m) (canonicalEuclideanLattice K b r)
    (canonicalEuclideanMatrix K b X) (canonicalEuclideanMatrix_lattice K b X)
    S (numberFieldImageShape K b X hX S) (canonicalEuclideanRestriction_surjective K b X hX)
    (canonicalEuclideanKernel_span K b X) (numberFieldImageShape_covariance K b X hX S)
    hε hε1 (by simpa only [canonicalEuclideanKernel_smoothing, shapeMinimumStretch] using hwidth)
    (canonicalEuclideanLatticeEquiv K b m c)
  rw [canonicalEuclideanRestriction_apply] at hb
  have he := discreteTotalVariation_map_equiv
    ((numberFieldEllipsoidalGaussian K b m S c).map X.mulVec)
    (numberFieldEllipsoidalGaussian K b r (numberFieldImageShape K b X hX S) (X.mulVec c))
    (canonicalEuclideanLatticeEquiv K b r).toEquiv
  change discreteTotalVariation
    (((numberFieldEllipsoidalGaussian K b m S c).map X.mulVec).map (canonicalEuclideanLatticeEquiv K b r))
    ((numberFieldEllipsoidalGaussian K b r (numberFieldImageShape K b X hX S) (X.mulVec c)).map
      (canonicalEuclideanLatticeEquiv K b r)) = _ at he
  rw [numberFieldEllipsoidalGaussian_map_matrix, numberFieldEllipsoidalGaussian_coordinate_law] at he
  exact he ▸ hb

end GeometricGaussianLHL
end

end NumberFieldPushforward

section NumberFieldJointGaussian

/-!
## Joint number-field Gaussian pushforward laws

The conditional comparison law is defined at every matrix: the actual
positive square-root image Gaussian on surjective matrices, and the
width-one spherical Gaussian otherwise. Both the source shape and its
ring-valued center may depend on the sampled matrix. The good-event
theorem counts the exceptional probability once.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Module NumberField

namespace GeometricGaussianLHL

variable (K : Type*) [Field K] [NumberField K] {d r m : ℕ}

def numberFieldConditionalTarget (b : Basis (Fin d) ℤ (𝓞 K))
    (X : Matrix (Fin r) (Fin m) (𝓞 K))
    (S : Euclidean (m * d) ≃L[ℝ] Euclidean (m * d)) (c : Fin m → 𝓞 K) :
    PMF (Fin r → 𝓞 K) := by
  classical
  exact if hX : Function.Surjective X.mulVec then
    numberFieldEllipsoidalGaussian K b r (numberFieldImageShape K b X hX S) (X.mulVec c)
  else numberFieldGaussian K b r 1 one_ne_zero

theorem numberFieldConditionalTarget_of_surjective (b : Basis (Fin d) ℤ (𝓞 K))
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) (hX : Function.Surjective X.mulVec)
    (S : Euclidean (m * d) ≃L[ℝ] Euclidean (m * d)) (c : Fin m → 𝓞 K) :
    numberFieldConditionalTarget K b X S c =
      numberFieldEllipsoidalGaussian K b r (numberFieldImageShape K b X hX S) (X.mulVec c) := by
  simp only [numberFieldConditionalTarget, dite_eq_left hX]

theorem numberFieldConditionalTarget_of_not_surjective (b : Basis (Fin d) ℤ (𝓞 K))
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) (hX : ¬ Function.Surjective X.mulVec)
    (S : Euclidean (m * d) ≃L[ℝ] Euclidean (m * d)) (c : Fin m → 𝓞 K) :
    numberFieldConditionalTarget K b X S c = numberFieldGaussian K b r 1 one_ne_zero := by
  simp only [numberFieldConditionalTarget, dite_eq_right hX]

theorem numberField_gaussian_joint_good_event (b : Basis (Fin d) ℤ (𝓞 K))
    (p : PMF (Matrix (Fin r) (Fin m) (𝓞 K)))
    (S : Matrix (Fin r) (Fin m) (𝓞 K) → Euclidean (m * d) ≃L[ℝ] Euclidean (m * d))
    (c : Matrix (Fin r) (Fin m) (𝓞 K) → Fin m → 𝓞 K)
    (G : Set (Matrix (Fin r) (Fin m) (𝓞 K))) {δ ε : ℝ}
    (hprob : ENNReal.ofReal (1 - δ) ≤ p.toOuterMeasure G)
    (hε : 0 < ε) (hε1 : ε < 1)
    (hgood : ∀ X ∈ G, Function.Surjective X.mulVec ∧
      smoothingParameter (canonicalKernel K X) ε ≤ shapeMinimumStretch (S X)) :
    discreteTotalVariation
      (jointPMF p (fun X => (numberFieldEllipsoidalGaussian K b m (S X) (c X)).map X.mulVec))
      (jointPMF p (fun X => numberFieldConditionalTarget K b X (S X) (c X))) ≤
        δ + ε / (1 - ε) := by
  apply discreteTotalVariation_joint_le_of_event_mass p _ _ G hprob
    (div_nonneg hε.le (sub_pos.mpr hε1).le)
  intro X hX
  obtain ⟨hsurj, hwidth⟩ := hgood X hX
  rw [numberFieldConditionalTarget_of_surjective K b X hsurj]
  exact numberField_gaussian_pushforward K b X hsurj (S X) hε hε1 hwidth (c X)

theorem numberField_gaussian_joint_errorBudget (b : Basis (Fin d) ℤ (𝓞 K))
    (p : PMF (Matrix (Fin r) (Fin m) (𝓞 K)))
    (S : Matrix (Fin r) (Fin m) (𝓞 K) → Euclidean (m * d) ≃L[ℝ] Euclidean (m * d))
    (c : Matrix (Fin r) (Fin m) (𝓞 K) → Fin m → 𝓞 K)
    (G : Set (Matrix (Fin r) (Fin m) (𝓞 K))) {δ : ℝ}
    (hprob : ENNReal.ofReal (1 - 3 * δ) ≤ p.toOuterMeasure G)
    (hδ : 0 < δ) (hδ1 : 2 * δ < 1)
    (hgood : ∀ X ∈ G, Function.Surjective X.mulVec ∧
      smoothingParameter (canonicalKernel K X) (2 * δ) ≤ shapeMinimumStretch (S X)) :
    discreteTotalVariation
      (jointPMF p (fun X => (numberFieldEllipsoidalGaussian K b m (S X) (c X)).map X.mulVec))
      (jointPMF p (fun X => numberFieldConditionalTarget K b X (S X) (c X))) ≤
        jointErrorBound δ 1 := by
  simpa only [jointErrorBound, Nat.cast_one, mul_one] using
    numberField_gaussian_joint_good_event K b p S c G hprob (mul_pos (by norm_num) hδ) hδ1 hgood

end GeometricGaussianLHL
end

end NumberFieldJointGaussian
