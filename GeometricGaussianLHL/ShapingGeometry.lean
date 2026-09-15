import GeometricGaussianLHL.GaussianPushforward
import GeometricGaussianLHL.MatrixArithmetic
import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# Exact spherical shaping and canonical Gram coordinates

This module collects the following proof sections, in dependency order.
- The covariance used for spherical Gaussian shaping (`SphericalCovariance`).
- Sharp quadratic bounds for the shaping covariance (`SphericalCovarianceBounds`).
- Spherical shaping with an admissible kernel fill (`KernelFilledCovariance`).
- Exact extreme widths for every admissible kernel fill (`KernelFilledShapeExtrema`).
- Shaping guarantees under isometric coordinate changes (`IsometricShapingTransport`).
- Explicit orthonormal coordinates from the canonical Gram matrix (`CanonicalGramCoordinates`).
- The positive square-root spherical input shape (`SphericalShape`).
- Explicit orthonormal coordinates for a scalar Gram matrix (`ScalarGramCoordinates`).
- Canonical matrix action in Gram-normalized integral-basis coordinates (`CanonicalGramMatrix`).
- Exact extreme widths of the spherical input shape (`SphericalShapeExtrema`).
- Spherical output from an explicitly shaped ring Gaussian (`NumberFieldSphericalPushforward`).
- Matrix form of exact spherical shaping (`SphericalMatrixCertificate`).
-/

section SphericalCovariance

/-!
## The covariance used for spherical Gaussian shaping

This is the paper's explicit covariance: the Gram operator of the
minimum-norm right inverse, with the kernel filled at its largest scale.
Its image covariance is exactly spherical.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace GeometricGaussianLHL

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

def sphericalShapingCovariance (A : E →L[ℝ] F) (hA : Function.Surjective A) (w : ℝ) : E →L[ℝ] E :=
  w ^ 2 • ((minimumNormRightInverse A hA).comp (minimumNormRightInverse A hA).adjoint +
    ‖minimumNormRightInverse A hA‖ ^ 2 • A.toLinearMap.ker.starProjection)

theorem sphericalShapingCovariance_positive (A : E →L[ℝ] F) (hA : Function.Surjective A) (w : ℝ) :
    (sphericalShapingCovariance A hA w).IsPositive := by
  have hp : A.toLinearMap.ker.starProjection.IsPositive := by
    apply (ContinuousLinearMap.isPositive_iff _).mpr
    refine ⟨A.toLinearMap.ker.starProjection_isSymmetric, fun x => ?_⟩
    simpa only [RCLike.re_to_real] using A.toLinearMap.ker.re_inner_starProjection_nonneg x
  exact ((ContinuousLinearMap.isPositive_self_comp_adjoint (minimumNormRightInverse A hA)).add
    (hp.smul_of_nonneg (sq_nonneg _))).smul_of_nonneg (sq_nonneg w)

theorem sphericalShapingCovariance_inner (A : E →L[ℝ] F) (hA : Function.Surjective A)
    (w : ℝ) (x : E) :
    inner ℝ x (sphericalShapingCovariance A hA w x) =
      w ^ 2 * (‖(minimumNormRightInverse A hA).adjoint x‖ ^ 2 +
        ‖minimumNormRightInverse A hA‖ ^ 2 * ‖A.toLinearMap.ker.starProjection x‖ ^ 2) := by
  have hp : inner ℝ x (A.toLinearMap.ker.starProjection x) =
      ‖A.toLinearMap.ker.starProjection x‖ ^ 2 := by
    rw [real_inner_comm]
    exact A.toLinearMap.ker.re_inner_starProjection_eq_normSq x
  change inner ℝ x (w ^ 2 • ((minimumNormRightInverse A hA)
    ((minimumNormRightInverse A hA).adjoint x) +
      ‖minimumNormRightInverse A hA‖ ^ 2 • A.toLinearMap.ker.starProjection x)) = _
  rw [inner_smul_right, inner_add_right, inner_smul_right,
    ← ContinuousLinearMap.adjoint_inner_left, real_inner_self_eq_norm_sq, hp]

theorem sphericalShapingCovariance_comp_adjoint (A : E →L[ℝ] F)
    (hA : Function.Surjective A) (w : ℝ) :
    (sphericalShapingCovariance A hA w).comp A.adjoint = w ^ 2 • minimumNormRightInverse A hA := by
  rw [sphericalShapingCovariance, ContinuousLinearMap.smul_comp, ContinuousLinearMap.add_comp,
    ContinuousLinearMap.comp_assoc, minimumNormRightInverse_adjoint_comp_adjoint,
    ContinuousLinearMap.comp_id, ContinuousLinearMap.smul_comp, kernelProjection_comp_adjoint,
    smul_zero, add_zero]

theorem sphericalShapingCovariance_image (A : E →L[ℝ] F)
    (hA : Function.Surjective A) (w : ℝ) :
    A.comp ((sphericalShapingCovariance A hA w).comp A.adjoint) =
      w ^ 2 • ContinuousLinearMap.id ℝ F := by
  rw [sphericalShapingCovariance_comp_adjoint, ContinuousLinearMap.comp_smul,
    self_comp_minimumNormRightInverse]

end GeometricGaussianLHL
end

end SphericalCovariance

section SphericalCovarianceBounds

/-!
## Sharp quadratic bounds for the shaping covariance

Orthogonal decomposition controls the kernel and transverse contributions
separately. These bounds imply positivity and the exact extreme widths of
the positive square-root shape.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace GeometricGaussianLHL

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

theorem rightInverse_adjoint_norm_le_projection (A : E →L[ℝ] F)
    (hA : Function.Surjective A) (x : E) :
    ‖(minimumNormRightInverse A hA).adjoint x‖ ≤
      ‖minimumNormRightInverse A hA‖ * ‖A.toLinearMap.kerᗮ.starProjection x‖ := by
  have he := congrArg (fun f : E →L[ℝ] F => f x)
    (minimumNormRightInverse_adjoint_comp_projection A hA)
  change (minimumNormRightInverse A hA).adjoint (A.toLinearMap.kerᗮ.starProjection x) =
    (minimumNormRightInverse A hA).adjoint x at he
  rw [← he]
  simpa only [LinearIsometryEquiv.norm_map] using
    (minimumNormRightInverse A hA).adjoint.le_opNorm (A.toLinearMap.kerᗮ.starProjection x)

theorem projection_norm_le_rightInverse_adjoint (A : E →L[ℝ] F)
    (hA : Function.Surjective A) (x : E) :
    ‖A.toLinearMap.kerᗮ.starProjection x‖ ≤
      ‖A‖ * ‖(minimumNormRightInverse A hA).adjoint x‖ := by
  have he := congrArg (fun f : E →L[ℝ] E => f x)
    (adjoint_comp_minimumNormRightInverse_adjoint A hA)
  change A.adjoint ((minimumNormRightInverse A hA).adjoint x) =
    A.toLinearMap.kerᗮ.starProjection x at he
  rw [← he]
  simpa only [LinearIsometryEquiv.norm_map] using
    A.adjoint.le_opNorm ((minimumNormRightInverse A hA).adjoint x)

theorem sphericalShapingCovariance_inner_le (A : E →L[ℝ] F)
    (hA : Function.Surjective A) (w : ℝ) (x : E) :
    inner ℝ x (sphericalShapingCovariance A hA w x) ≤
      w ^ 2 * ‖minimumNormRightInverse A hA‖ ^ 2 * ‖x‖ ^ 2 := by
  have hb := pow_le_pow_left₀ (norm_nonneg _) (rightInverse_adjoint_norm_le_projection A hA x) 2
  rw [mul_pow] at hb
  rw [sphericalShapingCovariance_inner,
    Submodule.norm_sq_eq_add_norm_sq_starProjection x A.toLinearMap.ker]
  apply (mul_le_mul_of_nonneg_left (add_le_add hb le_rfl) (sq_nonneg w)).trans_eq
  ring

theorem sphericalShapingCovariance_inner_lower_scaled [Nontrivial F]
    (A : E →L[ℝ] F) (hA : Function.Surjective A) (w : ℝ) (x : E) :
    w ^ 2 * ‖x‖ ^ 2 ≤ ‖A‖ ^ 2 * inner ℝ x (sphericalShapingCovariance A hA w x) := by
  have ht := pow_le_pow_left₀ (norm_nonneg _) (projection_norm_le_rightInverse_adjoint A hA x) 2
  rw [mul_pow] at ht
  have hn := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) (one_le_norm_mul_rightInverse A hA) 2
  rw [one_pow, mul_pow] at hn
  have hk := mul_le_mul_of_nonneg_right hn (sq_nonneg ‖A.toLinearMap.ker.starProjection x‖)
  rw [one_mul] at hk
  have hb := mul_le_mul_of_nonneg_left (add_le_add hk ht) (sq_nonneg w)
  rw [sphericalShapingCovariance_inner,
    Submodule.norm_sq_eq_add_norm_sq_starProjection x A.toLinearMap.ker]
  exact hb.trans_eq (by ring)

theorem sphericalShapingCovariance_inner_pos [Nontrivial F]
    (A : E →L[ℝ] F) (hA : Function.Surjective A) {w : ℝ} (hw : 0 < w) {x : E} (hx : x ≠ 0) :
    0 < inner ℝ x (sphericalShapingCovariance A hA w x) := by
  have hp : 0 < w ^ 2 * ‖x‖ ^ 2 := mul_pos (sq_pos_of_pos hw) (sq_pos_of_pos (norm_pos_iff.mpr hx))
  have hb := hp.trans_le (sphericalShapingCovariance_inner_lower_scaled A hA w x)
  exact (mul_pos_iff_of_pos_left (sq_pos_of_pos (surjective_operator_norm_pos A hA))).mp hb

end GeometricGaussianLHL
end

end SphericalCovarianceBounds

section KernelFilledCovariance

/-!
## Spherical shaping with an admissible kernel fill

Any kernel variance between the reciprocal squared input norm and the
squared minimum-norm right inverse norm has the same sharp quadratic bounds
as the paper's maximal fill. This includes the rational trace-average fill.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace GeometricGaussianLHL

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

def kernelFilledCovariance (A : E →L[ℝ] F) (hA : Function.Surjective A) (w c : ℝ) : E →L[ℝ] E :=
  w ^ 2 • ((minimumNormRightInverse A hA).comp (minimumNormRightInverse A hA).adjoint +
    c • A.toLinearMap.ker.starProjection)

theorem kernelFilledCovariance_inner (A : E →L[ℝ] F) (hA : Function.Surjective A)
    (w c : ℝ) (x : E) :
    inner ℝ x (kernelFilledCovariance A hA w c x) =
      w ^ 2 * (‖(minimumNormRightInverse A hA).adjoint x‖ ^ 2 +
        c * ‖A.toLinearMap.ker.starProjection x‖ ^ 2) := by
  have hp : inner ℝ x (A.toLinearMap.ker.starProjection x) =
      ‖A.toLinearMap.ker.starProjection x‖ ^ 2 := by
    rw [real_inner_comm]
    exact A.toLinearMap.ker.re_inner_starProjection_eq_normSq x
  change inner ℝ x (w ^ 2 • ((minimumNormRightInverse A hA)
    ((minimumNormRightInverse A hA).adjoint x) + c • A.toLinearMap.ker.starProjection x)) = _
  rw [inner_smul_right, inner_add_right, inner_smul_right,
    ← ContinuousLinearMap.adjoint_inner_left, real_inner_self_eq_norm_sq, hp]

theorem kernelFilledCovariance_comp_adjoint (A : E →L[ℝ] F)
    (hA : Function.Surjective A) (w c : ℝ) :
    (kernelFilledCovariance A hA w c).comp A.adjoint = w ^ 2 • minimumNormRightInverse A hA := by
  rw [kernelFilledCovariance, ContinuousLinearMap.smul_comp, ContinuousLinearMap.add_comp,
    ContinuousLinearMap.comp_assoc, minimumNormRightInverse_adjoint_comp_adjoint,
    ContinuousLinearMap.comp_id, ContinuousLinearMap.smul_comp, kernelProjection_comp_adjoint,
    smul_zero, add_zero]

theorem kernelFilledCovariance_image (A : E →L[ℝ] F)
    (hA : Function.Surjective A) (w c : ℝ) :
    A.comp ((kernelFilledCovariance A hA w c).comp A.adjoint) =
      w ^ 2 • ContinuousLinearMap.id ℝ F := by
  rw [kernelFilledCovariance_comp_adjoint, ContinuousLinearMap.comp_smul,
    self_comp_minimumNormRightInverse]

theorem kernelFilledCovariance_inner_le (A : E →L[ℝ] F)
    (hA : Function.Surjective A) (w : ℝ) {c : ℝ}
    (hc : c ≤ ‖minimumNormRightInverse A hA‖ ^ 2) (x : E) :
    inner ℝ x (kernelFilledCovariance A hA w c x) ≤
      w ^ 2 * ‖minimumNormRightInverse A hA‖ ^ 2 * ‖x‖ ^ 2 := by
  have hb := pow_le_pow_left₀ (norm_nonneg _) (rightInverse_adjoint_norm_le_projection A hA x) 2
  rw [mul_pow] at hb
  have hk := mul_le_mul_of_nonneg_right hc (sq_nonneg ‖A.toLinearMap.ker.starProjection x‖)
  rw [kernelFilledCovariance_inner,
    Submodule.norm_sq_eq_add_norm_sq_starProjection x A.toLinearMap.ker]
  apply (mul_le_mul_of_nonneg_left (add_le_add hb hk) (sq_nonneg w)).trans_eq
  ring

theorem kernelFilledCovariance_inner_lower_scaled (A : E →L[ℝ] F)
    (hA : Function.Surjective A) (w : ℝ) {c : ℝ} (hc : 1 ≤ ‖A‖ ^ 2 * c) (x : E) :
    w ^ 2 * ‖x‖ ^ 2 ≤ ‖A‖ ^ 2 * inner ℝ x (kernelFilledCovariance A hA w c x) := by
  have ht := pow_le_pow_left₀ (norm_nonneg _) (projection_norm_le_rightInverse_adjoint A hA x) 2
  rw [mul_pow] at ht
  have hk := mul_le_mul_of_nonneg_right hc (sq_nonneg ‖A.toLinearMap.ker.starProjection x‖)
  rw [one_mul] at hk
  have hb := mul_le_mul_of_nonneg_left (add_le_add hk ht) (sq_nonneg w)
  rw [kernelFilledCovariance_inner,
    Submodule.norm_sq_eq_add_norm_sq_starProjection x A.toLinearMap.ker]
  exact hb.trans_eq (by ring)

theorem kernelFilledCovariance_inner_ge_rightInverse (A : E →L[ℝ] F)
    (hA : Function.Surjective A) (w : ℝ) {c : ℝ} (hc : 0 ≤ c) (x : E) :
    w ^ 2 * ‖(minimumNormRightInverse A hA).adjoint x‖ ^ 2 ≤
      inner ℝ x (kernelFilledCovariance A hA w c x) := by
  rw [kernelFilledCovariance_inner]
  exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (mul_nonneg hc (sq_nonneg _))) (sq_nonneg w)

end GeometricGaussianLHL
end

end KernelFilledCovariance

section KernelFilledShapeExtrema

/-!
## Exact extreme widths for every admissible kernel fill

A square root of the filled covariance has the paper's two exact extreme
widths whenever the kernel fill lies in the sharp interval. The quadratic
identity is the only square-root property used by this geometric argument.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace GeometricGaussianLHL

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [Nontrivial F]

theorem kernelFilledShape_extrema (A : E →L[ℝ] F) (hA : Function.Surjective A)
    {w c : ℝ} (hw : 0 < w) (hlo : 1 ≤ ‖A‖ ^ 2 * c)
    (hhi : c ≤ ‖minimumNormRightInverse A hA‖ ^ 2) (S : E ≃L[ℝ] E)
    (hquad : ∀ x, ‖S x‖ ^ 2 = inner ℝ x (kernelFilledCovariance A hA w c x)) :
    shapeMinimumStretch S = w / ‖A‖ ∧
      ‖S.toContinuousLinearMap‖ = w / kernelMinimumStretch A.toLinearMap hA := by
  let : Nontrivial E := hA.nontrivial
  have hApos := surjective_operator_norm_pos A hA
  have hc : 0 ≤ c := by
    have h := (by norm_num : (0 : ℝ) < 1).trans_le hlo
    exact ((mul_pos_iff_of_pos_left (sq_pos_of_pos hApos)).mp h).le
  have hnormle : ‖S.toContinuousLinearMap‖ ≤ w * ‖minimumNormRightInverse A hA‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hw.le (norm_nonneg _))
    intro x
    have hb := kernelFilledCovariance_inner_le A hA w hhi x
    rw [← hquad x] at hb
    change ‖S x‖ ≤ w * ‖minimumNormRightInverse A hA‖ * ‖x‖
    have hr : 0 ≤ w * ‖minimumNormRightInverse A hA‖ * ‖x‖ := by positivity
    nlinarith [norm_nonneg (S x)]
  have hge (x : E) : w * ‖(minimumNormRightInverse A hA).adjoint x‖ ≤ ‖S x‖ := by
    apply (sq_le_sq₀ (by positivity) (norm_nonneg _)).mp
    rw [hquad, mul_pow]
    exact kernelFilledCovariance_inner_ge_rightInverse A hA w hc x
  have hnorm : ‖S.toContinuousLinearMap‖ = w * ‖minimumNormRightInverse A hA‖ := by
    apply le_antisymm hnormle
    have hb : ‖(minimumNormRightInverse A hA).adjoint‖ ≤ ‖S.toContinuousLinearMap‖ / w := by
      apply ContinuousLinearMap.opNorm_le_bound _ (div_nonneg (norm_nonneg _) hw.le)
      intro x
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hw).mpr
      have h := (hge x).trans (S.toContinuousLinearMap.le_opNorm x)
      simpa only [mul_comm] using h
    rw [LinearIsometryEquiv.norm_map] at hb
    simpa only [mul_comm] using (le_div_iff₀ hw).mp hb
  have hminle : w / ‖A‖ ≤ shapeMinimumStretch S := by
    apply (le_shapeMinimumStretch_iff _ (div_pos hw hApos)).mpr
    intro x
    apply (sq_le_sq₀ (by positivity) (norm_nonneg _)).mp
    have he : (w / ‖A‖ * ‖x‖) ^ 2 = w ^ 2 * ‖x‖ ^ 2 / ‖A‖ ^ 2 := by ring
    rw [he]
    apply (div_le_iff₀ (sq_pos_of_pos hApos)).mpr
    have hb := kernelFilledCovariance_inner_lower_scaled A hA w hlo x
    rw [← hquad x] at hb
    exact hb.trans_eq (mul_comm _ _)
  have hadj (y : F) : ‖S (A.adjoint y)‖ = w * ‖y‖ := by
    have he := congrArg (fun f : F →L[ℝ] F => f y) (kernelFilledCovariance_image A hA w c)
    change A (kernelFilledCovariance A hA w c (A.adjoint y)) = w ^ 2 • y at he
    apply (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [hquad, ContinuousLinearMap.adjoint_inner_left, he, inner_smul_right,
      real_inner_self_eq_norm_sq, mul_pow]
  have hmin : shapeMinimumStretch S = w / ‖A‖ := by
    apply le_antisymm _ hminle
    have hSpos := shapeMinimumStretch_pos S
    have hb : ‖A.adjoint‖ ≤ w / shapeMinimumStretch S := by
      apply ContinuousLinearMap.opNorm_le_bound _ (div_nonneg hw.le hSpos.le)
      intro y
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hSpos).mpr
      have h := shapeMinimumStretch_mul_norm_le S (A.adjoint y)
      rw [hadj] at h
      simpa only [mul_comm] using h
    rw [LinearIsometryEquiv.norm_map] at hb
    apply (le_div_iff₀ hApos).mpr
    simpa only [mul_comm] using (le_div_iff₀ hSpos).mp hb
  refine ⟨hmin, ?_⟩
  rw [hnorm, ← minimumNormRightInverse_norm_inverse, div_inv_eq_mul]

end GeometricGaussianLHL
end

end KernelFilledShapeExtrema

section IsometricShapingTransport

/-!
## Shaping guarantees under isometric coordinate changes

The numerical matrix can be stored in one explicitly represented orthonormal
coordinate system and interpreted in another. Operator error, shape widths
and spherical image covariance are preserved without a condition-number loss.
-/

noncomputable section

namespace GeometricGaussianLHL

section Norms

variable {E F E' F' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [NormedAddCommGroup F'] [NormedSpace ℝ F']

def isometricTransportMap (e : E ≃ₗᵢ[ℝ] E') (f : F ≃ₗᵢ[ℝ] F')
    (A : E →L[ℝ] F) : E' →L[ℝ] F' :=
  (f : F →L[ℝ] F').comp (A.comp (e.symm : E' →L[ℝ] E))

theorem isometricTransportMap_apply (e : E ≃ₗᵢ[ℝ] E') (f : F ≃ₗᵢ[ℝ] F')
    (A : E →L[ℝ] F) (x : E') : isometricTransportMap e f A x = f (A (e.symm x)) := rfl

theorem isometricTransportMap_norm (e : E ≃ₗᵢ[ℝ] E') (f : F ≃ₗᵢ[ℝ] F')
    (A : E →L[ℝ] F) : ‖isometricTransportMap e f A‖ = ‖A‖ := by
  simp only [isometricTransportMap, ContinuousLinearMap.opNorm_linearIsometryEquiv_comp,
    ContinuousLinearMap.opNorm_comp_linearIsometryEquiv]

theorem isometricTransportMap_sub (e : E ≃ₗᵢ[ℝ] E') (f : F ≃ₗᵢ[ℝ] F')
    (A B : E →L[ℝ] F) :
    isometricTransportMap e f (A - B) = isometricTransportMap e f A - isometricTransportMap e f B := by
  ext x
  simp only [isometricTransportMap_apply, sub_apply, map_sub]

theorem isometricTransportMap_surjective (e : E ≃ₗᵢ[ℝ] E') (f : F ≃ₗᵢ[ℝ] F')
    (A : E →L[ℝ] F) (hA : Function.Surjective A) :
    Function.Surjective (isometricTransportMap e f A) :=
  f.surjective.comp (hA.comp e.symm.surjective)

def isometricTransportShape (e : E ≃ₗᵢ[ℝ] F) (S : E ≃L[ℝ] E) : F ≃L[ℝ] F :=
  (e.symm.toContinuousLinearEquiv.trans S).trans e.toContinuousLinearEquiv

theorem isometricTransportShape_apply (e : E ≃ₗᵢ[ℝ] F) (S : E ≃L[ℝ] E) (x : F) :
    isometricTransportShape e S x = e (S (e.symm x)) := rfl

theorem isometricTransportShape_map (e : E ≃ₗᵢ[ℝ] F) (S : E ≃L[ℝ] E) :
    (isometricTransportShape e S).toContinuousLinearMap =
      isometricTransportMap e e S.toContinuousLinearMap := rfl

theorem isometricTransportShape_symm (e : E ≃ₗᵢ[ℝ] F) (S : E ≃L[ℝ] E) :
    (isometricTransportShape e S).symm = isometricTransportShape e S.symm := by
  ext x
  rfl

theorem isometricTransportShape_norm (e : E ≃ₗᵢ[ℝ] F) (S : E ≃L[ℝ] E) :
    ‖(isometricTransportShape e S).toContinuousLinearMap‖ = ‖S.toContinuousLinearMap‖ := by
  rw [isometricTransportShape_map, isometricTransportMap_norm]

theorem isometricTransportShape_minimumStretch (e : E ≃ₗᵢ[ℝ] F) (S : E ≃L[ℝ] E) :
    shapeMinimumStretch (isometricTransportShape e S) = shapeMinimumStretch S := by
  rw [shapeMinimumStretch, isometricTransportShape_symm, isometricTransportShape_norm,
    shapeMinimumStretch]

theorem isometricTransportShape_error (e : E ≃ₗᵢ[ℝ] F)
    (S : E ≃L[ℝ] E) (R : E →L[ℝ] E) :
    ‖isometricTransportMap e e R - (isometricTransportShape e S).toContinuousLinearMap‖ =
      ‖R - S.toContinuousLinearMap‖ := by
  rw [isometricTransportShape_map, ← isometricTransportMap_sub, isometricTransportMap_norm]

theorem isometricTransportMap_shape_comp (e : E ≃ₗᵢ[ℝ] E') (f : F ≃ₗᵢ[ℝ] F')
    (A : E →L[ℝ] F) (S : E ≃L[ℝ] E) :
    (isometricTransportMap e f A).comp (isometricTransportShape e S).toContinuousLinearMap =
      isometricTransportMap e f (A.comp S.toContinuousLinearMap) := by
  ext x
  simp only [ContinuousLinearMap.comp_apply, isometricTransportMap_apply,
    ContinuousLinearEquiv.coe_coe, isometricTransportShape_apply, LinearIsometryEquiv.symm_apply_apply]

end Norms

section Covariance

variable {E F E' F' : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']
  [NormedAddCommGroup F'] [InnerProductSpace ℝ F'] [FiniteDimensional ℝ F']

theorem isometricTransportMap_adjoint (e : E ≃ₗᵢ[ℝ] E') (f : F ≃ₗᵢ[ℝ] F')
    (A : E →L[ℝ] F) :
    (isometricTransportMap e f A).adjoint = isometricTransportMap f e A.adjoint := by
  simp only [isometricTransportMap, ContinuousLinearMap.adjoint_comp,
    LinearIsometryEquiv.adjoint_eq_symm, LinearIsometryEquiv.symm_symm,
    ContinuousLinearMap.comp_assoc]

theorem isometricTransportMap_positive (e : E ≃ₗᵢ[ℝ] F) (R : E →L[ℝ] E)
    (hR : R.IsPositive) : (isometricTransportMap e e R).IsPositive := by
  simpa only [isometricTransportMap, LinearIsometryEquiv.adjoint_eq_symm,
    ContinuousLinearMap.comp_assoc] using hR.conj_adjoint (e : E →L[ℝ] F)

theorem isometricTransportShape_covariance (e : E ≃ₗᵢ[ℝ] F) (S : E ≃L[ℝ] E) :
    shapeCovariance (isometricTransportShape e S) = isometricTransportMap e e (shapeCovariance S) := by
  rw [shapeCovariance, isometricTransportShape_map, isometricTransportMap_adjoint]
  ext x
  simp only [ContinuousLinearMap.comp_apply, isometricTransportMap_apply,
    LinearIsometryEquiv.symm_apply_apply, shapeCovariance]

theorem isometricTransportShape_image_covariance (e : E ≃ₗᵢ[ℝ] E') (f : F ≃ₗᵢ[ℝ] F')
    (A : E →L[ℝ] F) (S : E ≃L[ℝ] E) :
    gaussianPushforwardCovariance (isometricTransportMap e f A) (isometricTransportShape e S) =
      isometricTransportMap f f (gaussianPushforwardCovariance A S) := by
  rw [gaussianPushforwardCovariance_eq_gram, isometricTransportMap_shape_comp,
    isometricTransportMap_adjoint, gaussianPushforwardCovariance_eq_gram]
  ext x
  simp only [ContinuousLinearMap.comp_apply, isometricTransportMap_apply,
    LinearIsometryEquiv.symm_apply_apply]

theorem isometricTransportShape_spherical_covariance (e : E ≃ₗᵢ[ℝ] E') (f : F ≃ₗᵢ[ℝ] F')
    (A : E →L[ℝ] F) (S : E ≃L[ℝ] E) {w : ℝ}
    (h : gaussianPushforwardCovariance A S = w ^ 2 • ContinuousLinearMap.id ℝ F) :
    gaussianPushforwardCovariance (isometricTransportMap e f A) (isometricTransportShape e S) =
      w ^ 2 • ContinuousLinearMap.id ℝ F' := by
  rw [isometricTransportShape_image_covariance, h]
  ext x
  simp only [isometricTransportMap_apply, smul_apply,
    ContinuousLinearMap.id_apply, map_smul, LinearIsometryEquiv.apply_symm_apply]

theorem isometricTransportMap_minimumNormRightInverse (e : E ≃ₗᵢ[ℝ] E')
    (f : F ≃ₗᵢ[ℝ] F') (A : E →L[ℝ] F) (hA : Function.Surjective A) :
    minimumNormRightInverse (isometricTransportMap e f A)
        (isometricTransportMap_surjective e f A hA) =
      isometricTransportMap f e (minimumNormRightInverse A hA) := by
  let B := isometricTransportMap e f A
  let hB := isometricTransportMap_surjective e f A hA
  let R := minimumNormRightInverse A hA
  ext y : 1
  have hx : e (R (f.symm y)) ∈ B.toLinearMap.kerᗮ := by
    rw [Submodule.mem_orthogonal]
    intro z hz
    change B z = 0 at hz
    have hz0 : A (e.symm z) = 0 := by
      apply f.injective
      change B z = f 0
      simpa only [map_zero] using hz
    rw [← e.apply_symm_apply z, e.inner_map_map]
    exact ((Submodule.mem_orthogonal _ _).mp
      ((kernelOrthogonalEquiv A.toLinearMap hA).symm (f.symm y)).property) (e.symm z) hz0
  let v : B.toLinearMap.kerᗮ := ⟨e (R (f.symm y)), hx⟩
  have hv : kernelOrthogonalEquiv B.toLinearMap hB v = y := by
    have hr : A (R (f.symm y)) = f.symm y :=
      congrArg (fun g : F →L[ℝ] F => g (f.symm y)) (self_comp_minimumNormRightInverse A hA)
    change f (A (e.symm (e (R (f.symm y))))) = y
    rw [LinearIsometryEquiv.symm_apply_apply, hr, LinearIsometryEquiv.apply_symm_apply]
  have he : (kernelOrthogonalEquiv B.toLinearMap hB).symm y = v := by
    apply (kernelOrthogonalEquiv B.toLinearMap hB).injective
    rw [LinearEquiv.apply_symm_apply, hv]
  exact congrArg (fun z : B.toLinearMap.kerᗮ => (z : E')) he

theorem isometricTransportMap_kernelMinimumStretch (e : E ≃ₗᵢ[ℝ] E')
    (f : F ≃ₗᵢ[ℝ] F') (A : E →L[ℝ] F) (hA : Function.Surjective A) :
    kernelMinimumStretch (isometricTransportMap e f A).toLinearMap
        (isometricTransportMap_surjective e f A hA) = kernelMinimumStretch A.toLinearMap hA := by
  rw [← minimumNormRightInverse_norm_inverse, isometricTransportMap_minimumNormRightInverse,
    isometricTransportMap_norm, minimumNormRightInverse_norm_inverse]

end Covariance

end GeometricGaussianLHL
end

end IsometricShapingTransport

section CanonicalGramCoordinates

/-!
## Explicit orthonormal coordinates from the canonical Gram matrix

Normalizing the integral-basis map by the inverse positive square root of
its actual Gram matrix gives an isometry, for every number field and basis.
The construction uses explicit metric data and does not select an arbitrary
orthonormal basis. Approximating that metric data remains a separate task.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Module NumberField
open scoped MatrixOrder

namespace GeometricGaussianLHL

theorem positiveSquareRootShape_norm_sq {n : ℕ}
    (G : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosDef) (x : Euclidean n) :
    ‖positiveSquareRootShape G hG x‖ ^ 2 = inner ℝ x (Matrix.toEuclideanLin G x) := by
  have hs : (positiveSquareRootShape G hG).toContinuousLinearMap.adjoint =
      (positiveSquareRootShape G hG).toContinuousLinearMap :=
    (positiveSquareRootShape_positive G hG).isSymmetric.clm_adjoint_eq
  have hc := positiveSquareRootShape_covariance G hG
  change (positiveSquareRootShape G hG).toContinuousLinearMap.comp
    (positiveSquareRootShape G hG).toContinuousLinearMap.adjoint = _ at hc
  rw [hs] at hc
  change ‖(positiveSquareRootShape G hG).toContinuousLinearMap x‖ ^ 2 = _
  rw [ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right, hs, hc]
  rfl

variable (K : Type*) [Field K] [NumberField K] {d : ℕ}

local instance gramCoordinatesEmbeddingsFintype : Fintype (K →+* ℂ) := inferInstance
local instance gramCoordinatesAmbientInner : InnerProductSpace ℝ (CanonicalAmbient K) := inferInstance
local instance gramCoordinatesSpaceInner : InnerProductSpace ℝ (canonicalSpace K) := inferInstance
local instance gramCoordinatesPowerInner (n : ℕ) : InnerProductSpace ℝ (CanonicalPower K n) := inferInstance

theorem canonicalGram_posDef (b : Basis (Fin d) ℤ (𝓞 K)) : (canonicalGram K b).PosDef := by
  have he : canonicalGram K b = Matrix.gram ℝ (canonicalBasis K b) := by
    ext i j
    exact (canonicalBasis_inner K b i j).symm
  rw [he]
  exact Matrix.posDef_gram_of_linearIndependent (canonicalBasis K b).linearIndependent

theorem canonicalGramSquareRoot_norm (b : Basis (Fin d) ℤ (𝓞 K)) (x : Euclidean d) :
    ‖positiveSquareRootShape (canonicalGram K b) (canonicalGram_posDef K b) x‖ =
      ‖coefficientCanonicalEquiv K b x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [positiveSquareRootShape_norm_sq, coefficientCanonicalEquiv_norm_sq_mulVec,
    EuclideanSpace.inner_eq_star_dotProduct]
  simp only [star_trivial]
  rw [dotProduct_comm]
  rfl

def canonicalGramIsometry (b : Basis (Fin d) ℤ (𝓞 K)) :
    Euclidean d ≃ₗᵢ[ℝ] canonicalSpace K :=
  { ((positiveSquareRootShape (canonicalGram K b) (canonicalGram_posDef K b)).symm.trans
      (coefficientCanonicalEquiv K b)).toLinearEquiv with
    norm_map' := by
      intro x
      change ‖coefficientCanonicalEquiv K b
        ((positiveSquareRootShape (canonicalGram K b) (canonicalGram_posDef K b)).symm x)‖ = ‖x‖
      rw [← canonicalGramSquareRoot_norm, ContinuousLinearEquiv.apply_symm_apply] }

theorem canonicalGramIsometry_apply (b : Basis (Fin d) ℤ (𝓞 K)) (x : Euclidean d) :
    canonicalGramIsometry K b x = coefficientCanonicalEquiv K b
      ((positiveSquareRootShape (canonicalGram K b) (canonicalGram_posDef K b)).symm x) := rfl

theorem canonicalGramIsometry_symm_apply (b : Basis (Fin d) ℤ (𝓞 K)) (x : canonicalSpace K) :
    (canonicalGramIsometry K b).symm x =
      positiveSquareRootShape (canonicalGram K b) (canonicalGram_posDef K b)
        ((coefficientCanonicalEquiv K b).symm x) := rfl

def canonicalGramPowerRoot (b : Basis (Fin d) ℤ (𝓞 K)) (n : ℕ) :
    Euclidean (n * d) ≃L[ℝ] Euclidean (n * d) :=
  ((euclideanBlocks n d).toContinuousLinearEquiv.trans
    (repeatedContinuousEquiv (positiveSquareRootShape (canonicalGram K b) (canonicalGram_posDef K b)) n)).trans
      (euclideanBlocks n d).symm.toContinuousLinearEquiv

def canonicalGramPowerIsometry (b : Basis (Fin d) ℤ (𝓞 K)) (n : ℕ) :
    Euclidean (n * d) ≃ₗᵢ[ℝ] CanonicalPower K n :=
  (euclideanBlocks n d).trans (LinearIsometryEquiv.piLpCongrRight 2 (fun _ => canonicalGramIsometry K b))

theorem canonicalGramPowerRoot_apply (b : Basis (Fin d) ℤ (𝓞 K))
    (n : ℕ) (x : Euclidean (n * d)) :
    euclideanBlocks n d (canonicalGramPowerRoot K b n x) =
      repeatedContinuousEquiv (positiveSquareRootShape (canonicalGram K b) (canonicalGram_posDef K b)) n
        (euclideanBlocks n d x) := by
  exact (euclideanBlocks n d).apply_symm_apply _

theorem canonicalGramPowerIsometry_apply (b : Basis (Fin d) ℤ (𝓞 K))
    (n : ℕ) (x : Euclidean (n * d)) :
    canonicalGramPowerIsometry K b n x =
      powerCanonicalEquiv K b n ((canonicalGramPowerRoot K b n).symm x) := by
  ext j : 1
  change coefficientCanonicalEquiv K b
    ((positiveSquareRootShape (canonicalGram K b) (canonicalGram_posDef K b)).symm (euclideanBlocks n d x j)) =
    coefficientCanonicalEquiv K b (euclideanBlocks n d ((canonicalGramPowerRoot K b n).symm x) j)
  congr 1
  change _ = euclideanBlocks n d ((euclideanBlocks n d).symm _) j
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

theorem canonicalGramPowerIsometry_symm_apply (b : Basis (Fin d) ℤ (𝓞 K))
    (n : ℕ) (x : CanonicalPower K n) :
    (canonicalGramPowerIsometry K b n).symm x =
      canonicalGramPowerRoot K b n ((powerCanonicalEquiv K b n).symm x) := by
  apply (canonicalGramPowerIsometry K b n).injective
  rw [LinearIsometryEquiv.apply_symm_apply, canonicalGramPowerIsometry_apply,
    ContinuousLinearEquiv.symm_apply_apply, ContinuousLinearEquiv.apply_symm_apply]

end GeometricGaussianLHL
end

end CanonicalGramCoordinates

section SphericalShape

/-!
## The positive square-root spherical input shape

Strict positivity is proved from the covariance's quadratic lower bound.
The input shape is the actual positive matrix square root, with exact
spherical image covariance and quantitative extreme-width bounds.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open scoped MatrixOrder

namespace GeometricGaussianLHL

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

def sphericalShapingMatrix (A : Euclidean n →L[ℝ] F) (hA : Function.Surjective A)
    (w : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.toEuclideanLin.symm (sphericalShapingCovariance A hA w).toLinearMap

theorem sphericalShapingMatrix_posDef [Nontrivial F] (A : Euclidean n →L[ℝ] F)
    (hA : Function.Surjective A) {w : ℝ} (hw : 0 < w) :
    (sphericalShapingMatrix A hA w).PosDef := by
  have hp : (sphericalShapingMatrix A hA w).PosSemidef := by
    apply Matrix.isPositive_toEuclideanLin_iff.mp
    rw [sphericalShapingMatrix, LinearEquiv.apply_symm_apply]
    exact (sphericalShapingCovariance_positive A hA w).toLinearMap
  apply hp.posDef_iff_isUnit.mpr
  have hu : IsUnit (sphericalShapingCovariance A hA w).toLinearMap := by
    apply (LinearMap.isUnit_iff_ker_eq_bot _).mpr
    apply eq_bot_iff.mpr
    intro x hx
    change x = 0
    by_contra hn
    have h := sphericalShapingCovariance_inner_pos A hA hw hn
    change sphericalShapingCovariance A hA w x = 0 at hx
    rw [hx, inner_zero_right] at h
    exact lt_irrefl 0 h
  exact hu.map (Matrix.toLpLinAlgEquiv 2).symm.toMonoidHom

def sphericalShapingShape [Nontrivial F] (A : Euclidean n →L[ℝ] F)
    (hA : Function.Surjective A) {w : ℝ} (hw : 0 < w) : Euclidean n ≃L[ℝ] Euclidean n :=
  positiveSquareRootShape (sphericalShapingMatrix A hA w) (sphericalShapingMatrix_posDef A hA hw)

theorem sphericalShapingShape_matrix [Nontrivial F] (A : Euclidean n →L[ℝ] F)
    (hA : Function.Surjective A) {w : ℝ} (hw : 0 < w) :
    Matrix.toEuclideanLin.symm (sphericalShapingShape A hA hw).toLinearMap =
      CFC.sqrt (sphericalShapingMatrix A hA w) :=
  positiveSquareRootShape_matrix _ _

theorem sphericalShapingShape_positive [Nontrivial F] (A : Euclidean n →L[ℝ] F)
    (hA : Function.Surjective A) {w : ℝ} (hw : 0 < w) :
    (sphericalShapingShape A hA hw).toLinearMap.IsPositive :=
  positiveSquareRootShape_positive _ _

theorem sphericalShapingShape_adjoint [Nontrivial F] (A : Euclidean n →L[ℝ] F)
    (hA : Function.Surjective A) {w : ℝ} (hw : 0 < w) :
    (sphericalShapingShape A hA hw).toContinuousLinearMap.adjoint =
      (sphericalShapingShape A hA hw).toContinuousLinearMap :=
  (sphericalShapingShape_positive A hA hw).isSymmetric.clm_adjoint_eq

theorem sphericalShapingShape_covariance [Nontrivial F] (A : Euclidean n →L[ℝ] F)
    (hA : Function.Surjective A) {w : ℝ} (hw : 0 < w) :
    shapeCovariance (sphericalShapingShape A hA hw) = sphericalShapingCovariance A hA w := by
  rw [sphericalShapingShape, positiveSquareRootShape_covariance, sphericalShapingMatrix,
    LinearEquiv.apply_symm_apply]
  rfl

theorem sphericalShapingShape_norm_sq [Nontrivial F] (A : Euclidean n →L[ℝ] F)
    (hA : Function.Surjective A) {w : ℝ} (hw : 0 < w) (x : Euclidean n) :
    ‖sphericalShapingShape A hA hw x‖ ^ 2 = inner ℝ x (sphericalShapingCovariance A hA w x) := by
  have hc := sphericalShapingShape_covariance A hA hw
  change (sphericalShapingShape A hA hw).toContinuousLinearMap.comp
    (sphericalShapingShape A hA hw).toContinuousLinearMap.adjoint = _ at hc
  rw [sphericalShapingShape_adjoint] at hc
  change ‖(sphericalShapingShape A hA hw).toContinuousLinearMap x‖ ^ 2 = _
  rw [ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right, sphericalShapingShape_adjoint, hc]
  rfl

theorem sphericalShapingShape_image_covariance [Nontrivial F] (A : Euclidean n →L[ℝ] F)
    (hA : Function.Surjective A) {w : ℝ} (hw : 0 < w) :
    gaussianPushforwardCovariance A (sphericalShapingShape A hA hw) =
      w ^ 2 • ContinuousLinearMap.id ℝ F := by
  rw [gaussianPushforwardCovariance, sphericalShapingShape_covariance, sphericalShapingCovariance_image]

theorem sphericalShapingShape_norm_le [Nontrivial F] (A : Euclidean n →L[ℝ] F)
    (hA : Function.Surjective A) {w : ℝ} (hw : 0 < w) :
    ‖(sphericalShapingShape A hA hw).toContinuousLinearMap‖ ≤ w * ‖minimumNormRightInverse A hA‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hw.le (norm_nonneg _))
  intro x
  have hb := sphericalShapingCovariance_inner_le A hA w x
  rw [← sphericalShapingShape_norm_sq A hA hw] at hb
  change ‖sphericalShapingShape A hA hw x‖ ≤ w * ‖minimumNormRightInverse A hA‖ * ‖x‖
  have hn := norm_nonneg (sphericalShapingShape A hA hw x)
  have hr : 0 ≤ w * ‖minimumNormRightInverse A hA‖ * ‖x‖ := by positivity
  nlinarith

theorem sphericalShapingShape_minimumStretch_ge [Nontrivial F] (A : Euclidean n →L[ℝ] F)
    (hA : Function.Surjective A) {w : ℝ} (hw : 0 < w) :
    w / ‖A‖ ≤ shapeMinimumStretch (sphericalShapingShape A hA hw) := by
  let : Nontrivial (Euclidean n) := hA.nontrivial
  have hApos := surjective_operator_norm_pos A hA
  apply (le_shapeMinimumStretch_iff _ (div_pos hw hApos)).mpr
  intro x
  apply (sq_le_sq₀ (by positivity) (norm_nonneg _)).mp
  have he : (w / ‖A‖ * ‖x‖) ^ 2 = w ^ 2 * ‖x‖ ^ 2 / ‖A‖ ^ 2 := by ring
  rw [he]
  apply (div_le_iff₀ (sq_pos_of_pos hApos)).mpr
  have hb := sphericalShapingCovariance_inner_lower_scaled A hA w x
  rw [← sphericalShapingShape_norm_sq A hA hw] at hb
  exact hb.trans_eq (mul_comm _ _)

end GeometricGaussianLHL
end

end SphericalShape

section ScalarGramCoordinates

/-!
## Explicit orthonormal coordinates for a scalar Gram matrix

When the integral basis has Gram matrix `c I`, normalizing its canonical
map by `1 / sqrt c` gives an isometry. The common scalar cancels from the
matrix action, so the integer coefficient matrix is also its matrix in these
orthonormal coordinates. The isometry into the previously chosen coordinates
is used only to interpret numerical output, not as encoded machine input.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Module NumberField

namespace GeometricGaussianLHL

variable (K : Type*) [Field K] [NumberField K] {d r m : ℕ}

local instance scalarGramEmbeddingsFintype : Fintype (K →+* ℂ) := inferInstance
local instance scalarGramAmbientInner : InnerProductSpace ℝ (CanonicalAmbient K) := inferInstance
local instance scalarGramSpaceInner : InnerProductSpace ℝ (canonicalSpace K) := inferInstance
local instance scalarGramPowerInner (n : ℕ) : InnerProductSpace ℝ (CanonicalPower K n) := inferInstance

def scalarGramCanonicalIsometry (b : Basis (Fin d) ℤ (𝓞 K)) {c : ℝ} (hc : 0 < c)
    (hGram : ∀ i j, canonicalGram K b i j = if i = j then c else 0) (n : ℕ) :
    Euclidean (n * d) ≃ₗᵢ[ℝ] CanonicalPower K n :=
  { ((powerCanonicalEquiv K b n).trans
      (ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := CanonicalPower K n)
        (Units.mk0 (Real.sqrt c)⁻¹ (inv_ne_zero (Real.sqrt_pos.mpr hc).ne')))).toLinearEquiv with
    norm_map' := by
      intro x
      change ‖(Real.sqrt c)⁻¹ • powerCanonicalEquiv K b n x‖ = ‖x‖
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (Real.sqrt_pos.mpr hc)),
        powerCanonicalEquiv_norm_of_diagonal K b hc.le hGram, ← mul_assoc,
        inv_mul_cancel₀ (Real.sqrt_pos.mpr hc).ne', one_mul] }

theorem scalarGramCanonicalIsometry_apply (b : Basis (Fin d) ℤ (𝓞 K)) {c : ℝ} (hc : 0 < c)
    (hGram : ∀ i j, canonicalGram K b i j = if i = j then c else 0)
    (n : ℕ) (x : Euclidean (n * d)) :
    scalarGramCanonicalIsometry K b hc hGram n x =
      (Real.sqrt c)⁻¹ • powerCanonicalEquiv K b n x := rfl

theorem scalarGramCanonicalIsometry_symm_apply (b : Basis (Fin d) ℤ (𝓞 K))
    {c : ℝ} (hc : 0 < c) (hGram : ∀ i j, canonicalGram K b i j = if i = j then c else 0)
    (n : ℕ) (y : CanonicalPower K n) :
    (scalarGramCanonicalIsometry K b hc hGram n).symm y =
      (powerCanonicalEquiv K b n).symm (Real.sqrt c • y) := by
  change (powerCanonicalEquiv K b n).symm ((Real.sqrt c)⁻¹⁻¹ • y) = _
  rw [inv_inv]

theorem canonicalMatrixMap_scalarGram (b : Basis (Fin d) ℤ (𝓞 K))
    {c : ℝ} (hc : 0 < c) (hGram : ∀ i j, canonicalGram K b i j = if i = j then c else 0)
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) (x : Euclidean (m * d)) :
    canonicalMatrixMap K b X (scalarGramCanonicalIsometry K b hc hGram m x) =
      scalarGramCanonicalIsometry K b hc hGram r (realCoefficientMap (ringCoefficientMatrix b X) x) := by
  change powerCanonicalEquiv K b r
    (realCoefficientMap (ringCoefficientMatrix b X)
      ((powerCanonicalEquiv K b m).symm ((Real.sqrt c)⁻¹ • powerCanonicalEquiv K b m x))) =
    (Real.sqrt c)⁻¹ • powerCanonicalEquiv K b r (realCoefficientMap (ringCoefficientMatrix b X) x)
  rw [map_smul, ContinuousLinearEquiv.symm_apply_apply, map_smul, map_smul]

def scalarGramEuclideanIsometry (b : Basis (Fin d) ℤ (𝓞 K)) {c : ℝ} (hc : 0 < c)
    (hGram : ∀ i j, canonicalGram K b i j = if i = j then c else 0) (n : ℕ) :
    Euclidean (n * d) ≃ₗᵢ[ℝ] Euclidean (n * d) :=
  (scalarGramCanonicalIsometry K b hc hGram n).trans (canonicalOrthonormalCoordinates K b n)

theorem scalarGramEuclideanIsometry_apply (b : Basis (Fin d) ℤ (𝓞 K)) {c : ℝ} (hc : 0 < c)
    (hGram : ∀ i j, canonicalGram K b i j = if i = j then c else 0)
    (n : ℕ) (x : Euclidean (n * d)) :
    scalarGramEuclideanIsometry K b hc hGram n x =
      canonicalOrthonormalCoordinates K b n (scalarGramCanonicalIsometry K b hc hGram n x) := rfl

theorem canonicalEuclideanMatrix_scalarGram (b : Basis (Fin d) ℤ (𝓞 K))
    {c : ℝ} (hc : 0 < c) (hGram : ∀ i j, canonicalGram K b i j = if i = j then c else 0)
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) (x : Euclidean (m * d)) :
    canonicalEuclideanMatrix K b X (scalarGramEuclideanIsometry K b hc hGram m x) =
      scalarGramEuclideanIsometry K b hc hGram r (realCoefficientMap (ringCoefficientMatrix b X) x) := by
  change canonicalOrthonormalCoordinates K b r
    (canonicalMatrixMap K b X ((canonicalOrthonormalCoordinates K b m).symm
      (canonicalOrthonormalCoordinates K b m (scalarGramCanonicalIsometry K b hc hGram m x)))) = _
  rw [LinearIsometryEquiv.symm_apply_apply, canonicalMatrixMap_scalarGram]
  rfl

theorem canonicalEuclideanMatrix_scalarGram_transport (b : Basis (Fin d) ℤ (𝓞 K))
    {c : ℝ} (hc : 0 < c) (hGram : ∀ i j, canonicalGram K b i j = if i = j then c else 0)
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) :
    (canonicalEuclideanMatrix K b X).toContinuousLinearMap =
      isometricTransportMap (scalarGramEuclideanIsometry K b hc hGram m)
        (scalarGramEuclideanIsometry K b hc hGram r)
        (realCoefficientMap (ringCoefficientMatrix b X)).toContinuousLinearMap := by
  ext x : 1
  obtain ⟨y, rfl⟩ := (scalarGramEuclideanIsometry K b hc hGram m).surjective x
  change canonicalEuclideanMatrix K b X (scalarGramEuclideanIsometry K b hc hGram m y) = _
  rw [canonicalEuclideanMatrix_scalarGram, isometricTransportMap_apply,
    LinearIsometryEquiv.symm_apply_apply]
  rfl

theorem canonicalEuclideanMatrix_scalarGram_norm (b : Basis (Fin d) ℤ (𝓞 K))
    {c : ℝ} (hc : 0 < c) (hGram : ∀ i j, canonicalGram K b i j = if i = j then c else 0)
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) :
    ‖(canonicalEuclideanMatrix K b X).toContinuousLinearMap‖ =
      ‖(realCoefficientMap (ringCoefficientMatrix b X)).toContinuousLinearMap‖ := by
  rw [canonicalEuclideanMatrix_scalarGram_transport K b hc hGram, isometricTransportMap_norm]

end GeometricGaussianLHL
end

end ScalarGramCoordinates

section CanonicalGramMatrix

/-!
## Canonical matrix action in Gram-normalized integral-basis coordinates

The real matrix is the coefficient matrix conjugated by explicit diagonal
copies of the positive square root of the integral-basis Gram matrix. The
isometry to the older canonical coordinates interprets output and preserves
all norms. Computing metric approximations and conversion costs is separate.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Module NumberField
open scoped MatrixOrder

namespace GeometricGaussianLHL

variable (K : Type*) [Field K] [NumberField K] {d r m : ℕ}

def canonicalGramRootMatrix (b : Basis (Fin d) ℤ (𝓞 K)) (n : ℕ) :
    Matrix (Fin (n * d)) (Fin (n * d)) ℝ :=
  repeatedEuclideanMatrix n (CFC.sqrt (canonicalGram K b))

theorem canonicalGramRootMatrix_operator (b : Basis (Fin d) ℤ (𝓞 K)) (n : ℕ) :
    Matrix.toEuclideanLin (canonicalGramRootMatrix K b n) = (canonicalGramPowerRoot K b n).toLinearMap := by
  rw [canonicalGramRootMatrix, ← positiveSquareRootShape_matrix _ (canonicalGram_posDef K b)]
  exact repeatedEuclideanMatrix_equiv _ _

theorem canonicalGramRootMatrix_matrix (b : Basis (Fin d) ℤ (𝓞 K)) (n : ℕ) :
    Matrix.toEuclideanLin.symm (canonicalGramPowerRoot K b n).toLinearMap = canonicalGramRootMatrix K b n := by
  rw [← canonicalGramRootMatrix_operator, LinearEquiv.symm_apply_apply]

theorem canonicalGramRootMatrix_inv_operator (b : Basis (Fin d) ℤ (𝓞 K)) (n : ℕ) :
    Matrix.toEuclideanLin (canonicalGramRootMatrix K b n)⁻¹ = (canonicalGramPowerRoot K b n).symm.toLinearMap := by
  rw [← canonicalGramRootMatrix_matrix, ← euclideanEquiv_matrix_symm, LinearEquiv.apply_symm_apply]

def canonicalGramNormalizedMatrix (b : Basis (Fin d) ℤ (𝓞 K))
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) : Matrix (Fin (r * d)) (Fin (m * d)) ℝ :=
  canonicalGramRootMatrix K b r * (ringCoefficientMatrix b X).map (Int.cast : ℤ → ℝ) *
    (canonicalGramRootMatrix K b m)⁻¹

theorem canonicalGramNormalizedMatrix_operator (b : Basis (Fin d) ℤ (𝓞 K))
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) :
    Matrix.toEuclideanLin (canonicalGramNormalizedMatrix K b X) =
      (canonicalGramPowerRoot K b r).toLinearMap.comp
        ((realCoefficientMap (ringCoefficientMatrix b X)).comp (canonicalGramPowerRoot K b m).symm.toLinearMap) := by
  unfold canonicalGramNormalizedMatrix
  change Matrix.toLpLin 2 2 (_ * _ * _) = _
  rw [Matrix.toLpLin_mul_same, Matrix.toLpLin_mul_same,
    canonicalGramRootMatrix_operator, canonicalGramRootMatrix_inv_operator]
  rfl

set_option maxRecDepth 2000 in
theorem canonicalMatrixMap_gram_coordinates (b : Basis (Fin d) ℤ (𝓞 K))
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) (x : Euclidean (m * d)) :
    canonicalMatrixMap K b X (canonicalGramPowerIsometry K b m x) =
      canonicalGramPowerIsometry K b r (Matrix.toEuclideanLin (canonicalGramNormalizedMatrix K b X) x) := by
  rw [canonicalGramPowerIsometry_apply, canonicalGramPowerIsometry_apply, canonicalGramNormalizedMatrix_operator]
  change powerCanonicalEquiv K b r (realCoefficientMap (ringCoefficientMatrix b X)
      ((powerCanonicalEquiv K b m).symm
        (powerCanonicalEquiv K b m ((canonicalGramPowerRoot K b m).symm x)))) =
    powerCanonicalEquiv K b r ((canonicalGramPowerRoot K b r).symm
      (canonicalGramPowerRoot K b r (realCoefficientMap (ringCoefficientMatrix b X)
        ((canonicalGramPowerRoot K b m).symm x))))
  rw [ContinuousLinearEquiv.symm_apply_apply, ContinuousLinearEquiv.symm_apply_apply]

def canonicalGramEuclideanIsometry (b : Basis (Fin d) ℤ (𝓞 K)) (n : ℕ) :
    Euclidean (n * d) ≃ₗᵢ[ℝ] Euclidean (n * d) :=
  (canonicalGramPowerIsometry K b n).trans (canonicalOrthonormalCoordinates K b n)

theorem canonicalEuclideanMatrix_gram_coordinates (b : Basis (Fin d) ℤ (𝓞 K))
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) (x : Euclidean (m * d)) :
    canonicalEuclideanMatrix K b X (canonicalGramEuclideanIsometry K b m x) =
      canonicalGramEuclideanIsometry K b r (Matrix.toEuclideanLin (canonicalGramNormalizedMatrix K b X) x) := by
  change canonicalOrthonormalCoordinates K b r (canonicalMatrixMap K b X
      ((canonicalOrthonormalCoordinates K b m).symm
        (canonicalOrthonormalCoordinates K b m (canonicalGramPowerIsometry K b m x)))) = _
  rw [LinearIsometryEquiv.symm_apply_apply, canonicalMatrixMap_gram_coordinates]
  rfl

theorem canonicalEuclideanMatrix_gram_transport (b : Basis (Fin d) ℤ (𝓞 K))
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) :
    (canonicalEuclideanMatrix K b X).toContinuousLinearMap =
      isometricTransportMap (canonicalGramEuclideanIsometry K b m) (canonicalGramEuclideanIsometry K b r)
        (Matrix.toEuclideanLin (canonicalGramNormalizedMatrix K b X)).toContinuousLinearMap := by
  ext x : 1
  obtain ⟨y, rfl⟩ := (canonicalGramEuclideanIsometry K b m).surjective x
  rw [isometricTransportMap_apply, LinearIsometryEquiv.symm_apply_apply]
  exact canonicalEuclideanMatrix_gram_coordinates K b X y

theorem canonicalGramNormalizedMatrix_surjective (b : Basis (Fin d) ℤ (𝓞 K))
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) (hX : Function.Surjective X.mulVec) :
    Function.Surjective (Matrix.toEuclideanLin (canonicalGramNormalizedMatrix K b X)) := by
  rw [canonicalGramNormalizedMatrix_operator]
  exact (canonicalGramPowerRoot K b r).surjective.comp
    ((realCoefficientMap_surjective_of_integer_surjective _ ((ringCoefficientMatrix_surjective_iff b X).mpr hX)).comp
      (canonicalGramPowerRoot K b m).symm.surjective)

theorem canonicalEuclideanMatrix_gram_norm (b : Basis (Fin d) ℤ (𝓞 K))
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) :
    ‖(canonicalEuclideanMatrix K b X).toContinuousLinearMap‖ =
      ‖(Matrix.toEuclideanLin (canonicalGramNormalizedMatrix K b X)).toContinuousLinearMap‖ := by
  rw [canonicalEuclideanMatrix_gram_transport, isometricTransportMap_norm]

end GeometricGaussianLHL
end

end CanonicalGramMatrix

section SphericalShapeExtrema

/-!
## Exact extreme widths of the spherical input shape

The maximum width is the output width times the transverse inverse norm.
The minimum width is the output width divided by the original operator
norm. Both equalities are proved from the actual covariance and its
orthogonal decomposition, without assuming singular-value identities.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace GeometricGaussianLHL

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [Nontrivial F]

theorem sphericalShapingShape_norm_ge_rightInverse_adjoint (A : Euclidean n →L[ℝ] F)
    (hA : Function.Surjective A) {w : ℝ} (hw : 0 < w) (x : Euclidean n) :
    w * ‖(minimumNormRightInverse A hA).adjoint x‖ ≤ ‖sphericalShapingShape A hA hw x‖ := by
  apply (sq_le_sq₀ (by positivity) (norm_nonneg _)).mp
  rw [sphericalShapingShape_norm_sq, sphericalShapingCovariance_inner, mul_pow]
  have h := mul_nonneg (sq_nonneg w)
    (mul_nonneg (sq_nonneg ‖minimumNormRightInverse A hA‖)
      (sq_nonneg ‖A.toLinearMap.ker.starProjection x‖))
  nlinarith

theorem sphericalShapingShape_norm (A : Euclidean n →L[ℝ] F)
    (hA : Function.Surjective A) {w : ℝ} (hw : 0 < w) :
    ‖(sphericalShapingShape A hA hw).toContinuousLinearMap‖ = w * ‖minimumNormRightInverse A hA‖ := by
  apply le_antisymm (sphericalShapingShape_norm_le A hA hw)
  have hb : ‖(minimumNormRightInverse A hA).adjoint‖ ≤
      ‖(sphericalShapingShape A hA hw).toContinuousLinearMap‖ / w := by
    apply ContinuousLinearMap.opNorm_le_bound _ (div_nonneg (norm_nonneg _) hw.le)
    intro x
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hw).mpr
    have h := (sphericalShapingShape_norm_ge_rightInverse_adjoint A hA hw x).trans
      ((sphericalShapingShape A hA hw).toContinuousLinearMap.le_opNorm x)
    simpa only [mul_comm] using h
  rw [LinearIsometryEquiv.norm_map] at hb
  simpa only [mul_comm] using (le_div_iff₀ hw).mp hb

theorem sphericalShapingShape_norm_eq_div_minimumStretch (A : Euclidean n →L[ℝ] F)
    (hA : Function.Surjective A) {w : ℝ} (hw : 0 < w) :
    ‖(sphericalShapingShape A hA hw).toContinuousLinearMap‖ =
      w / kernelMinimumStretch A.toLinearMap hA := by
  rw [sphericalShapingShape_norm, ← minimumNormRightInverse_norm_inverse, div_inv_eq_mul]

theorem sphericalShapingShape_norm_adjoint_apply (A : Euclidean n →L[ℝ] F)
    (hA : Function.Surjective A) {w : ℝ} (hw : 0 < w) (y : F) :
    ‖sphericalShapingShape A hA hw (A.adjoint y)‖ = w * ‖y‖ := by
  have he := congrArg (fun f : F →L[ℝ] F => f y) (sphericalShapingCovariance_image A hA w)
  change A (sphericalShapingCovariance A hA w (A.adjoint y)) = w ^ 2 • y at he
  apply (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [sphericalShapingShape_norm_sq, ContinuousLinearMap.adjoint_inner_left, he,
    inner_smul_right, real_inner_self_eq_norm_sq, mul_pow]

theorem sphericalShapingShape_minimumStretch (A : Euclidean n →L[ℝ] F)
    (hA : Function.Surjective A) {w : ℝ} (hw : 0 < w) :
    shapeMinimumStretch (sphericalShapingShape A hA hw) = w / ‖A‖ := by
  let : Nontrivial (Euclidean n) := hA.nontrivial
  apply le_antisymm _ (sphericalShapingShape_minimumStretch_ge A hA hw)
  have hc := shapeMinimumStretch_pos (sphericalShapingShape A hA hw)
  have hApos := surjective_operator_norm_pos A hA
  have hb : ‖A.adjoint‖ ≤ w / shapeMinimumStretch (sphericalShapingShape A hA hw) := by
    apply ContinuousLinearMap.opNorm_le_bound _ (div_nonneg hw.le hc.le)
    intro y
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hc).mpr
    have h := shapeMinimumStretch_mul_norm_le (sphericalShapingShape A hA hw) (A.adjoint y)
    rw [sphericalShapingShape_norm_adjoint_apply] at h
    simpa only [mul_comm] using h
  rw [LinearIsometryEquiv.norm_map] at hb
  apply (le_div_iff₀ hApos).mpr
  simpa only [mul_comm] using (le_div_iff₀ hc).mp hb

/-- All three exact analytic identities of the paper’s Gaussian-shaping remark, for the explicit
positive square-root construction. Computational complexity is separate. -/
theorem spherical_shaping_analytic_certificate (A : Euclidean n →L[ℝ] F)
    (hA : Function.Surjective A) {w : ℝ} (hw : 0 < w) :
    (sphericalShapingMatrix A hA w).PosDef ∧
    (sphericalShapingShape A hA hw).toLinearMap.IsPositive ∧
    gaussianPushforwardCovariance A (sphericalShapingShape A hA hw) =
      w ^ 2 • ContinuousLinearMap.id ℝ F ∧
    shapeMinimumStretch (sphericalShapingShape A hA hw) = w / ‖A‖ ∧
    ‖(sphericalShapingShape A hA hw).toContinuousLinearMap‖ =
      w / kernelMinimumStretch A.toLinearMap hA :=
  ⟨sphericalShapingMatrix_posDef A hA hw, sphericalShapingShape_positive A hA hw,
    sphericalShapingShape_image_covariance A hA hw, sphericalShapingShape_minimumStretch A hA hw,
    sphericalShapingShape_norm_eq_div_minimumStretch A hA hw⟩

end GeometricGaussianLHL
end

end SphericalShapeExtrema

section NumberFieldSphericalPushforward

/-!
## Spherical output from an explicitly shaped ring Gaussian

Apply the proved shaping construction to the actual canonical matrix.
The minimum-width condition follows from its exact norm formula, and
the image Gaussian is identified with the actual spherical ring law.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Module NumberField

namespace GeometricGaussianLHL

variable (K : Type*) [Field K] [NumberField K] {d r m : ℕ}
  [Nontrivial (Euclidean (r * d))]

def numberFieldSphericalInputShape (b : Basis (Fin d) ℤ (𝓞 K))
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) (hX : Function.Surjective X.mulVec)
    {w : ℝ} (hw : 0 < w) : Euclidean (m * d) ≃L[ℝ] Euclidean (m * d) :=
  sphericalShapingShape (canonicalEuclideanMatrix K b X).toContinuousLinearMap
    (canonicalEuclideanMatrix_surjective K b X hX) hw

theorem numberFieldSphericalInputShape_minimumStretch (b : Basis (Fin d) ℤ (𝓞 K))
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) (hX : Function.Surjective X.mulVec)
    {w : ℝ} (hw : 0 < w) :
    shapeMinimumStretch (numberFieldSphericalInputShape K b X hX hw) =
      w / ‖(canonicalEuclideanMatrix K b X).toContinuousLinearMap‖ :=
  sphericalShapingShape_minimumStretch _ _ _

theorem numberFieldSphericalInputShape_covariance (b : Basis (Fin d) ℤ (𝓞 K))
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) (hX : Function.Surjective X.mulVec)
    {w : ℝ} (hw : 0 < w) :
    gaussianPushforwardCovariance (canonicalEuclideanMatrix K b X).toContinuousLinearMap
      (numberFieldSphericalInputShape K b X hX hw) =
        w ^ 2 • ContinuousLinearMap.id ℝ (Euclidean (r * d)) :=
  sphericalShapingShape_image_covariance _ _ _

omit [Nontrivial (Euclidean (r * d))] in
/-- Any input shape with spherical image covariance gives the actual spherical
ring-Gaussian target. This interface does not prescribe the kernel fill. -/
theorem numberFieldImageShape_spherical_target (b : Basis (Fin d) ℤ (𝓞 K))
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) (hX : Function.Surjective X.mulVec)
    (S : Euclidean (m * d) ≃L[ℝ] Euclidean (m * d))
    {w : ℝ} (hw : 0 < w)
    (hcov : gaussianPushforwardCovariance (canonicalEuclideanMatrix K b X).toContinuousLinearMap S =
      w ^ 2 • ContinuousLinearMap.id ℝ (Euclidean (r * d))) (c : Fin m → 𝓞 K) :
    numberFieldEllipsoidalGaussian K b r (numberFieldImageShape K b X hX S) (X.mulVec c) =
      (numberFieldGaussian K b r w hw.ne').map (Equiv.addRight (X.mulVec c)) := by
  rw [← numberFieldScalarShape_gaussian K b r w hw.ne' (X.mulVec c)]
  apply numberFieldEllipsoidalGaussian_covariance_congr
  rw [numberFieldImageShape_covariance, hcov, euclideanScalarShape_covariance]

omit [Nontrivial (Euclidean (r * d))] in
theorem numberField_gaussian_spherical_pushforward_of_shape (b : Basis (Fin d) ℤ (𝓞 K))
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) (hX : Function.Surjective X.mulVec)
    (S : Euclidean (m * d) ≃L[ℝ] Euclidean (m * d))
    {w ε : ℝ} (hw : 0 < w) (hε : 0 < ε) (hε1 : ε < 1)
    (hwidth : smoothingParameter (canonicalKernel K X) ε ≤ shapeMinimumStretch S)
    (hcov : gaussianPushforwardCovariance (canonicalEuclideanMatrix K b X).toContinuousLinearMap S =
      w ^ 2 • ContinuousLinearMap.id ℝ (Euclidean (r * d))) (c : Fin m → 𝓞 K) :
    discreteTotalVariation ((numberFieldEllipsoidalGaussian K b m S c).map X.mulVec)
      ((numberFieldGaussian K b r w hw.ne').map (Equiv.addRight (X.mulVec c))) ≤ ε / (1 - ε) := by
  have h := numberField_gaussian_pushforward K b X hX S hε hε1 hwidth c
  rwa [numberFieldImageShape_spherical_target K b X hX S hw hcov c] at h

theorem numberFieldSphericalInputShape_target (b : Basis (Fin d) ℤ (𝓞 K))
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) (hX : Function.Surjective X.mulVec)
    {w : ℝ} (hw : 0 < w) (c : Fin m → 𝓞 K) :
    numberFieldEllipsoidalGaussian K b r
      (numberFieldImageShape K b X hX (numberFieldSphericalInputShape K b X hX hw)) (X.mulVec c) =
        (numberFieldGaussian K b r w hw.ne').map (Equiv.addRight (X.mulVec c)) := by
  exact numberFieldImageShape_spherical_target K b X hX _ hw
    (numberFieldSphericalInputShape_covariance K b X hX hw) c

theorem numberField_gaussian_spherical_pushforward (b : Basis (Fin d) ℤ (𝓞 K))
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) (hX : Function.Surjective X.mulVec)
    {w ε : ℝ} (hw : 0 < w) (hε : 0 < ε) (hε1 : ε < 1)
    (hwidth : smoothingParameter (canonicalKernel K X) ε *
      ‖(canonicalEuclideanMatrix K b X).toContinuousLinearMap‖ ≤ w)
    (c : Fin m → 𝓞 K) :
    discreteTotalVariation
      ((numberFieldEllipsoidalGaussian K b m (numberFieldSphericalInputShape K b X hX hw) c).map X.mulVec)
      ((numberFieldGaussian K b r w hw.ne').map (Equiv.addRight (X.mulVec c))) ≤ ε / (1 - ε) := by
  have hA := canonicalEuclideanMatrix_surjective K b X hX
  have hnorm := surjective_operator_norm_pos (canonicalEuclideanMatrix K b X).toContinuousLinearMap hA
  have hS : smoothingParameter (canonicalKernel K X) ε ≤
      shapeMinimumStretch (numberFieldSphericalInputShape K b X hX hw) := by
    rw [numberFieldSphericalInputShape_minimumStretch]
    exact (le_div_iff₀ hnorm).mpr hwidth
  exact numberField_gaussian_spherical_pushforward_of_shape K b X hX
    (numberFieldSphericalInputShape K b X hX hw) hw hε hε1 hS
    (numberFieldSphericalInputShape_covariance K b X hX hw) c

end GeometricGaussianLHL
end

end NumberFieldSphericalPushforward

section SphericalMatrixCertificate

/-!
## Matrix form of exact spherical shaping

The explicit positive covariance has the paper's literal matrix identity
`A Σ Aᵀ = w² I`. Together with the positive-square-root construction and
the two exact extreme-width formulas, this supplies the analytic part of
the paper’s Gaussian-shaping remark. The polynomial-time approximation claim is separate.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace GeometricGaussianLHL

theorem euclideanMatrix_smul_id (n : ℕ) (a : ℝ) :
    Matrix.toEuclideanLin.symm (a • (ContinuousLinearMap.id ℝ (Euclidean n))).toLinearMap =
      a • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  change (Matrix.toLpLin 2 2).symm (a • LinearMap.id) = _
  rw [map_smul]
  congr 1
  apply (Matrix.toLpLin 2 2).injective
  rw [LinearEquiv.apply_symm_apply, Matrix.toLpLin_one]

theorem sphericalShapingMatrix_image {n r : ℕ} (A : Euclidean n →L[ℝ] Euclidean r)
    (hA : Function.Surjective A) (w : ℝ) :
    Matrix.toEuclideanLin.symm A.toLinearMap * sphericalShapingMatrix A hA w *
      (Matrix.toEuclideanLin.symm A.toLinearMap).transpose =
        w ^ 2 • (1 : Matrix (Fin r) (Fin r) ℝ) := by
  have h := congrArg (fun f : Euclidean r →L[ℝ] Euclidean r => Matrix.toEuclideanLin.symm f.toLinearMap)
    (sphericalShapingCovariance_image A hA w)
  rw [euclideanMatrix_smul_id] at h
  change (Matrix.toLpLin 2 2).symm
    (A.toLinearMap.comp ((sphericalShapingCovariance A hA w).toLinearMap.comp A.toLinearMap.adjoint)) = _ at h
  rw [Matrix.toLpLin_symm_comp, Matrix.toLpLin_symm_comp, euclideanMatrix_adjoint] at h
  simpa only [sphericalShapingMatrix, Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.mul_assoc] using h

theorem spherical_matrix_shaping_analytic_certificate {n r : ℕ} [Nontrivial (Euclidean r)]
    (A : Matrix (Fin r) (Fin n) ℝ) (hA : Function.Surjective (Matrix.toEuclideanLin A))
    {w : ℝ} (hw : 0 < w) :
    let f := (Matrix.toEuclideanLin A).toContinuousLinearMap
    let C := sphericalShapingMatrix f hA w
    let S := sphericalShapingShape f hA hw
    C.PosDef ∧ A * C * A.transpose = w ^ 2 • (1 : Matrix (Fin r) (Fin r) ℝ) ∧
      shapeMinimumStretch S = w / ‖f‖ ∧
      ‖S.toContinuousLinearMap‖ = w / kernelMinimumStretch f.toLinearMap hA := by
  dsimp only
  refine ⟨sphericalShapingMatrix_posDef _ hA hw, ?_, sphericalShapingShape_minimumStretch _ hA hw,
    sphericalShapingShape_norm_eq_div_minimumStretch _ hA hw⟩
  simpa only [LinearMap.coe_toContinuousLinearMap, LinearEquiv.symm_apply_apply] using
    sphericalShapingMatrix_image (Matrix.toEuclideanLin A).toContinuousLinearMap hA w

end GeometricGaussianLHL
end

end SphericalMatrixCertificate
