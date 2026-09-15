import GeometricGaussianLHL.LatticeGeometry

/-!
# Poisson summation and lattice Gaussian flatness

This module collects the following proof sections, in dependency order.
- Actual Gaussian PMFs on full Euclidean lattices (`LatticeGaussian`).
- Lattice-valued centres and translation of Gaussian laws (`LatticeGaussianShift`).
- The dual mass of the whitened integer lattice (`EllipsoidDualMass`).
- Fourier transform of an ellipsoidal Gaussian (`EllipsoidFourier`).
- Poisson summation for shifted ellipsoidal lattice Gaussians (`EllipsoidPoisson`).
- Shifted theta flatness from actual dual Gaussian mass (`EllipsoidFlatness`).
- Shifted Gaussian flatness on full lattices (`LatticeFlatness`).
- Shifted Gaussian flatness in finite-dimensional inner-product spaces (`LatticeIsotropicFlatness`).
- Shifted Gaussian masses of lower-rank lattices (`IntrinsicFlatness`).
- Flatness after a Gaussian shape transformation (`WhitenedFlatness`).
-/

section LatticeGaussian

/-!
## Actual Gaussian PMFs on full Euclidean lattices

The probability mass is normalized directly on the lattice subtype.
An integral basis proves convergence and identifies its coefficient law;
the basis does not enter the Gaussian weight or partition function.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Module
open scoped ENNReal

namespace GeometricGaussianLHL

theorem pmf_map_equiv_apply {α β : Type*} (p : PMF α) (e : α ≃ β) (x : α) :
    p.map e (e x) = p x := by
  classical
  rw [PMF.map_apply]
  simp only [e.injective.eq_iff, tsum_ite_eq']

theorem discreteTotalVariation_map_equiv {α β : Type*} (p q : PMF α) (e : α ≃ β) :
    discreteTotalVariation (p.map e) (q.map e) = discreteTotalVariation p q := by
  unfold discreteTotalVariation
  rw [← e.tsum_eq]
  simp only [pmf_map_equiv_apply]

variable {n : ℕ} (L : Submodule ℤ (Euclidean n)) [DiscreteTopology L] [IsZLattice ℝ L]

def fullLatticeIntegralBasis : Basis (Fin n) ℤ L :=
  (Module.finBasis ℤ L).reindex (finCongr (by rw [ZLattice.rank ℝ L]; simp))

def fullLatticeCoordinateEquiv : Coeff n ≃ₗ[ℤ] L := (fullLatticeIntegralBasis L).equivFun.symm

def fullLatticeRealEquiv : Euclidean n ≃L[ℝ] Euclidean n :=
  (basisEuclideanEquiv ((fullLatticeIntegralBasis L).ofZLatticeBasis ℝ L)).toContinuousLinearEquiv

theorem fullLatticeRealEquiv_integer (z : Coeff n) :
    fullLatticeRealEquiv L (integerEmbedding n z) = (fullLatticeCoordinateEquiv L z : Euclidean n) := by
  change ((fullLatticeIntegralBasis L).ofZLatticeBasis ℝ L).equivFun.symm (fun i => (z i : ℝ)) =
    ((fullLatticeIntegralBasis L).equivFun.symm z : Euclidean n)
  rw [Basis.equivFun_symm_apply, Basis.equivFun_symm_apply]
  simp only [Submodule.coe_sum, Submodule.coe_smul, Basis.ofZLatticeBasis_apply, Int.cast_smul_eq_zsmul]

def latticeCoefficientShape (S : Euclidean n ≃L[ℝ] Euclidean n) : Euclidean n ≃L[ℝ] Euclidean n :=
  S.trans (fullLatticeRealEquiv L).symm

theorem latticeCoefficientShape_symm_integer (S : Euclidean n ≃L[ℝ] Euclidean n) (z : Coeff n) :
    (latticeCoefficientShape L S).symm (integerEmbedding n z) =
      S.symm (fullLatticeCoordinateEquiv L z : Euclidean n) := by
  change S.symm (fullLatticeRealEquiv L (integerEmbedding n z)) = _
  rw [fullLatticeRealEquiv_integer]

def latticeGaussianWeight (S : Euclidean n ≃L[ℝ] Euclidean n) (v : L) : ℝ :=
  gaussianWeight 1 (S.symm (v : Euclidean n))

omit [DiscreteTopology L] [IsZLattice ℝ L] in
theorem latticeGaussianWeight_pos (S : Euclidean n ≃L[ℝ] Euclidean n) (v : L) :
    0 < latticeGaussianWeight L S v := gaussianWeight_pos _ _

theorem latticeGaussianWeight_coordinates (S : Euclidean n ≃L[ℝ] Euclidean n) (z : Coeff n) :
    latticeGaussianWeight L S (fullLatticeCoordinateEquiv L z) =
      ellipsoidWeight (latticeCoefficientShape L S) 0 z := by
  rw [ellipsoidWeight, sub_zero, latticeCoefficientShape_symm_integer]
  rfl

theorem summable_latticeGaussianWeight (S : Euclidean n ≃L[ℝ] Euclidean n) :
    Summable (latticeGaussianWeight L S) := by
  have h := (summable_ellipsoidWeight (latticeCoefficientShape L S) 0).comp_injective
    (fullLatticeCoordinateEquiv L).symm.injective
  apply h.congr
  intro v
  simpa only [Function.comp_def, LinearEquiv.apply_symm_apply] using
    (latticeGaussianWeight_coordinates L S ((fullLatticeCoordinateEquiv L).symm v)).symm

def latticeGaussianPartition (S : Euclidean n ≃L[ℝ] Euclidean n) : ℝ := ∑' v : L, latticeGaussianWeight L S v

theorem latticeGaussianPartition_eq (S : Euclidean n ≃L[ℝ] Euclidean n) :
    latticeGaussianPartition L S = ellipsoidPartition (latticeCoefficientShape L S) 0 := by
  unfold latticeGaussianPartition ellipsoidPartition
  rw [← (fullLatticeCoordinateEquiv L).toEquiv.tsum_eq]
  exact tsum_congr (latticeGaussianWeight_coordinates L S)

theorem latticeGaussianPartition_pos (S : Euclidean n ≃L[ℝ] Euclidean n) :
    0 < latticeGaussianPartition L S := by
  rw [latticeGaussianPartition_eq]
  exact ellipsoidPartition_pos _ _

theorem latticeGaussianWeight_sum_ne_zero (S : Euclidean n ≃L[ℝ] Euclidean n) :
    (∑' v : L, ENNReal.ofReal (latticeGaussianWeight L S v)) ≠ 0 := by
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun v => (latticeGaussianWeight_pos L S v).le)
    (summable_latticeGaussianWeight L S)]
  exact ne_of_gt (ENNReal.ofReal_pos.mpr (latticeGaussianPartition_pos L S))

def latticeGaussian (S : Euclidean n ≃L[ℝ] Euclidean n) : PMF L :=
  PMF.normalize (fun v => ENNReal.ofReal (latticeGaussianWeight L S v))
    (latticeGaussianWeight_sum_ne_zero L S) (summable_latticeGaussianWeight L S).tsum_ofReal_ne_top

theorem latticeGaussian_apply (S : Euclidean n ≃L[ℝ] Euclidean n) (v : L) :
    latticeGaussian L S v = ENNReal.ofReal (latticeGaussianWeight L S v / latticeGaussianPartition L S) := by
  simp only [latticeGaussian, PMF.normalize_apply]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun v => (latticeGaussianWeight_pos L S v).le)
    (summable_latticeGaussianWeight L S), ← div_eq_mul_inv]
  exact (ENNReal.ofReal_div_of_pos (latticeGaussianPartition_pos L S)).symm

theorem latticeGaussian_coordinate_law (S : Euclidean n ≃L[ℝ] Euclidean n) :
    (latticeGaussian L S).map (fullLatticeCoordinateEquiv L).symm =
      ellipsoidalGaussian (latticeCoefficientShape L S) 0 := by
  classical
  ext z
  rw [PMF.map_apply, ← (fullLatticeCoordinateEquiv L).toEquiv.tsum_eq]
  simp only [LinearEquiv.coe_toEquiv, LinearEquiv.symm_apply_apply, tsum_ite_eq']
  rw [latticeGaussian_apply, latticeGaussianWeight_coordinates, latticeGaussianPartition_eq,
    ellipsoidalGaussian_apply]

theorem latticeGaussian_totalVariation_coordinates (S T : Euclidean n ≃L[ℝ] Euclidean n) :
    discreteTotalVariation (latticeGaussian L S) (latticeGaussian L T) =
      discreteTotalVariation (ellipsoidalGaussian (latticeCoefficientShape L S) 0)
        (ellipsoidalGaussian (latticeCoefficientShape L T) 0) := by
  have h := discreteTotalVariation_map_equiv (latticeGaussian L S) (latticeGaussian L T)
    (fullLatticeCoordinateEquiv L).symm.toEquiv
  change discreteTotalVariation ((latticeGaussian L S).map (fullLatticeCoordinateEquiv L).symm)
    ((latticeGaussian L T).map (fullLatticeCoordinateEquiv L).symm) = _ at h
  rw [latticeGaussian_coordinate_law, latticeGaussian_coordinate_law] at h
  exact h.symm

end GeometricGaussianLHL
end

end LatticeGaussian

section LatticeGaussianShift

/-!
## Lattice-valued centres and translation of Gaussian laws

The Gaussian centred at a lattice point is its translated centred law.
Its point masses have the actual shifted Gaussian weights, with unchanged
partition sum. Additive pushforwards commute with this translation and
preserve the distance from a correspondingly translated target law.
-/

noncomputable section

namespace GeometricGaussianLHL

theorem pmf_map_add_right {A B : Type*} [AddGroup A] [AddGroup B]
    (p : PMF A) (f : A →+ B) (c : A) :
    (p.map (Equiv.addRight c)).map f = (p.map f).map (Equiv.addRight (f c)) := by
  rw [PMF.map_comp, PMF.map_comp]
  congr 1
  funext x
  exact f.map_add x c

theorem discreteTotalVariation_map_translate {A B : Type*} [AddGroup A] [AddGroup B]
    (p : PMF A) (q : PMF B) (f : A →+ B) (c : A) :
    discreteTotalVariation ((p.map (Equiv.addRight c)).map f)
      (q.map (Equiv.addRight (f c))) = discreteTotalVariation (p.map f) q := by
  rw [pmf_map_add_right, discreteTotalVariation_map_equiv]

variable {n : ℕ} (L : Submodule ℤ (Euclidean n)) [DiscreteTopology L] [IsZLattice ℝ L]

def latticeGaussianCentered (S : Euclidean n ≃L[ℝ] Euclidean n) (c : L) : PMF L :=
  (latticeGaussian L S).map (Equiv.addRight c)

theorem latticeGaussianCentered_apply (S : Euclidean n ≃L[ℝ] Euclidean n) (c v : L) :
    latticeGaussianCentered L S c v =
      ENNReal.ofReal (gaussianWeight 1 (S.symm ((v : Euclidean n) - (c : Euclidean n))) /
        latticeGaussianPartition L S) := by
  have h := pmf_map_equiv_apply (latticeGaussian L S) (Equiv.addRight c) (v - c)
  change ((latticeGaussian L S).map (Equiv.addRight c)) ((v - c) + c) = _ at h
  rw [sub_add_cancel] at h
  change latticeGaussianCentered L S c v = latticeGaussian L S (v - c) at h
  rw [h, latticeGaussian_apply]
  rfl

omit [DiscreteTopology L] [IsZLattice ℝ L] in
theorem latticeGaussianCentered_partition (S : Euclidean n ≃L[ℝ] Euclidean n) (c : L) :
    (∑' v : L, gaussianWeight 1 (S.symm ((v : Euclidean n) - (c : Euclidean n)))) =
      latticeGaussianPartition L S := by
  rw [← (Equiv.addRight c).tsum_eq]
  change (∑' v : L, gaussianWeight 1 (S.symm (((v + c : L) : Euclidean n) -
    (c : Euclidean n)))) = _
  simp only [Submodule.coe_add, add_sub_cancel_right]
  rfl

@[simp] theorem latticeGaussianCentered_zero (S : Euclidean n ≃L[ℝ] Euclidean n) :
    latticeGaussianCentered L S 0 = latticeGaussian L S := by
  unfold latticeGaussianCentered
  have h : (Equiv.addRight (0 : L) : L → L) = id := by funext x; simp
  rw [h, PMF.map_id]

theorem latticeGaussianCentered_totalVariation (S T : Euclidean n ≃L[ℝ] Euclidean n) (c : L) :
    discreteTotalVariation (latticeGaussianCentered L S c) (latticeGaussianCentered L T c) =
      discreteTotalVariation (latticeGaussian L S) (latticeGaussian L T) :=
  discreteTotalVariation_map_equiv _ _ _

theorem latticeGaussianCentered_pushforward {m : ℕ}
    (L' : Submodule ℤ (Euclidean m)) [DiscreteTopology L'] [IsZLattice ℝ L']
    (S : Euclidean n ≃L[ℝ] Euclidean n) (T : Euclidean m ≃L[ℝ] Euclidean m)
    (f : L →+ L') (c : L) :
    discreteTotalVariation ((latticeGaussianCentered L S c).map f)
      (latticeGaussianCentered L' T (f c)) =
      discreteTotalVariation ((latticeGaussian L S).map f) (latticeGaussian L' T) :=
  discreteTotalVariation_map_translate _ _ _ _

end GeometricGaussianLHL
end

end LatticeGaussianShift

section EllipsoidDualMass

/-!
## The dual mass of the whitened integer lattice

The Fourier remainder is the actual nonzero Gaussian mass of the intrinsic
dual of `S⁻¹ ℤⁿ`. The identification uses the inverse-adjoint lattice formula
and a proved bijection, including the zero vector and dimension zero.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open scoped ENNReal

namespace GeometricGaussianLHL

variable {n : ℕ}

def integerImageEquiv (T : Euclidean n ≃L[ℝ] Euclidean n) :
    Coeff n ≃ₗ[ℤ] latticeImage T.toContinuousLinearMap (integerLattice n) :=
  (LinearEquiv.ofInjective (integerEmbedding n) (integerEmbedding_injective n)).trans
    (Submodule.equivMapOfInjective (T.toLinearMap.restrictScalars ℤ) T.injective (integerLattice n))

@[simp] theorem integerImageEquiv_apply (T : Euclidean n ≃L[ℝ] Euclidean n) (z : Coeff n) :
    (integerImageEquiv T z : Euclidean n) = T (integerEmbedding n z) := rfl

open scoped Classical in
def ellipsoidDualWeight (S : Euclidean n ≃L[ℝ] Euclidean n) (z : Coeff n) : ℝ :=
  if z = 0 then 0 else ellipsoidWeight (inverseAdjointEquiv S) 0 z

theorem ellipsoidDualWeight_nonneg (S : Euclidean n ≃L[ℝ] Euclidean n) (z : Coeff n) :
    0 ≤ ellipsoidDualWeight S z := by
  classical
  unfold ellipsoidDualWeight
  split_ifs
  · rfl
  · exact (ellipsoidWeight_pos _ _ _).le

theorem summable_ellipsoidDualWeight (S : Euclidean n ≃L[ℝ] Euclidean n) :
    Summable (ellipsoidDualWeight S) := by
  classical
  apply (summable_ellipsoidWeight (inverseAdjointEquiv S) 0).of_norm_bounded
  intro z
  rw [Real.norm_eq_abs, abs_of_nonneg (ellipsoidDualWeight_nonneg S z)]
  unfold ellipsoidDualWeight
  split_ifs
  · exact (ellipsoidWeight_pos _ _ _).le
  · rfl

def ellipsoidDualRemainder (S : Euclidean n ≃L[ℝ] Euclidean n) : ℝ := ∑' z, ellipsoidDualWeight S z

theorem ellipsoidDualRemainder_nonneg (S : Euclidean n ≃L[ℝ] Euclidean n) :
    0 ≤ ellipsoidDualRemainder S := tsum_nonneg (ellipsoidDualWeight_nonneg S)

def whitenedIntegerLattice (S : Euclidean n ≃L[ℝ] Euclidean n) : Submodule ℤ (Euclidean n) :=
  latticeImage S.symm.toContinuousLinearMap (integerLattice n)

theorem nonzeroDualMass_whitenedIntegerLattice (S : Euclidean n ≃L[ℝ] Euclidean n) :
    nonzeroDualMass (whitenedIntegerLattice S) 1 = ENNReal.ofReal (ellipsoidDualRemainder S) := by
  classical
  rw [nonzeroDualMass, whitenedIntegerLattice,
    latticeDual_image_equiv (integerLattice n) (integerLattice_span n) S.symm, integerLattice_dual_eq]
  let e := integerImageEquiv (inverseAdjointEquiv S.symm)
  rw [← e.toEquiv.tsum_eq]
  rw [ellipsoidDualRemainder, ENNReal.ofReal_tsum_of_nonneg (ellipsoidDualWeight_nonneg S)
    (summable_ellipsoidDualWeight S)]
  apply tsum_congr
  intro z
  have he : e.toEquiv z = 0 ↔ z = 0 := e.map_eq_zero_iff
  simp only [he, ellipsoidDualWeight]
  split_ifs
  · exact ENNReal.ofReal_zero.symm
  · congr 1
    rw [ellipsoidWeight, sub_zero]
    change gaussianWeight 1 ((inverseAdjointEquiv S.symm) (integerEmbedding n z)) =
      gaussianWeight 1 ((inverseAdjointEquiv S).symm (integerEmbedding n z))
    rfl

theorem ellipsoidDualRemainder_le_of_smoothAt (S : Euclidean n ≃L[ℝ] Euclidean n)
    {ε : ℝ} (hε : 0 ≤ ε) (h : SmoothAt (whitenedIntegerLattice S) ε 1) :
    ellipsoidDualRemainder S ≤ ε := by
  have hb := h.2
  rw [nonzeroDualMass_whitenedIntegerLattice] at hb
  exact (ENNReal.ofReal_le_ofReal_iff hε).mp hb

end GeometricGaussianLHL
end

end EllipsoidDualMass

section EllipsoidFourier

/-!
## Fourier transform of an ellipsoidal Gaussian

Whitening is a genuine complex-valued change of variables. The resulting
Fourier transform has the exact volume factor and the adjoint shape in its
Gaussian exponent. These are the coefficients needed for shifted theta
flatness on the integer torus.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory
open scoped FourierTransform

namespace GeometricGaussianLHL

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Complex-valued change of variables with the actual determinant. -/
theorem integral_comp_linearEquiv_complex (e : E ≃ₗ[ℝ] E) (f : E → ℂ) :
    (∫ x, f (e x)) = |e.toLinearMap.det|⁻¹ • ∫ x, f x := by
  have h := integral_map_equiv
    e.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv f (μ := volume)
  have hm : Measure.map (fun x => e x) (volume : Measure E) =
      ENNReal.ofReal |e.toLinearMap.det⁻¹| • volume :=
    Measure.map_linearMap_addHaar_eq_smul_addHaar volume e.isUnit_det'.ne_zero
  change (∫ x, f x ∂Measure.map (fun x => e x) volume) = _ at h
  rw [hm, integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _), abs_inv] at h
  exact h.symm

theorem fourier_gaussianWeight_one (w : E) :
    𝓕 (fun x : E => (gaussianWeight 1 x : ℂ)) w = (gaussianWeight 1 w : ℂ) := by
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h := fourier_gaussian_innerProductSpace
    (by simpa only [Complex.ofReal_re] using Real.pi_pos : 0 < (Real.pi : ℂ).re) w
  simp only [div_self hp, Complex.one_cpow, one_mul] at h
  have he : -(Real.pi : ℂ) ^ 2 * (‖w‖ : ℂ) ^ 2 / Real.pi =
      -(Real.pi : ℂ) * (‖w‖ : ℂ) ^ 2 := by field_simp
  rw [he] at h
  simpa only [gaussianWeight, one_pow, mul_one, Complex.ofReal_exp,
    Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_pow] using h

variable {n : ℕ}

def ellipsoidVolume (S : Euclidean n ≃L[ℝ] Euclidean n) : ℝ :=
  S.symm.toLinearMap.normDet⁻¹

theorem ellipsoidVolume_pos (S : Euclidean n ≃L[ℝ] Euclidean n) : 0 < ellipsoidVolume S :=
  inv_pos.mpr (normDet_pos_of_injective _ S.symm.injective)

theorem ellipsoidVolume_eq_normDet (S : Euclidean n ≃L[ℝ] Euclidean n) :
    ellipsoidVolume S = S.toLinearMap.normDet := by
  have h := normDet_symm_mul S
  have hn := (normDet_pos_of_injective _ S.symm.injective).ne'
  have hh : S.toLinearMap.normDet = 1 / S.symm.toLinearMap.normDet :=
    (eq_div_iff hn).mpr (by nlinarith only [h])
  simpa only [ellipsoidVolume, one_div] using hh.symm

theorem integral_ellipsoidKernel (S : Euclidean n ≃L[ℝ] Euclidean n) :
    (∫ x, ellipsoidKernel S x) = ellipsoidVolume S := by
  change (∫ x, gaussianWeight 1 (S.symm.toLinearMap x)) = _
  rw [integral_gaussianWeight_comp_injective _ S.symm.injective (by norm_num : (0 : ℝ) < 1)]
  simp only [one_pow, one_mul, ellipsoidVolume]

theorem fourier_ellipsoidKernel (S : Euclidean n ≃L[ℝ] Euclidean n) (w : Euclidean n) :
    𝓕 (fun x => (ellipsoidKernel S x : ℂ)) w =
      (ellipsoidVolume S : ℂ) * (gaussianWeight 1 (S.toContinuousLinearMap.adjoint w) : ℂ) := by
  let g : Euclidean n → ℂ := fun y =>
    Real.fourierChar (-inner ℝ y (S.toContinuousLinearMap.adjoint w)) • (gaussianWeight 1 y : ℂ)
  have he (x : Euclidean n) : inner ℝ (S.symm x) (S.toContinuousLinearMap.adjoint w) = inner ℝ x w := by
    rw [ContinuousLinearMap.adjoint_inner_right]
    exact congrArg (fun y => inner ℝ y w) (S.apply_symm_apply x)
  rw [Real.fourier_eq]
  have hfun : (fun x => Real.fourierChar (-inner ℝ x w) • (ellipsoidKernel S x : ℂ)) =
      fun x => g (S.symm x) := by
    funext x
    simp only [g, he, ellipsoidKernel]
  rw [hfun]
  change (∫ x, g (S.symm.toLinearEquiv x)) = _
  rw [integral_comp_linearEquiv_complex S.symm.toLinearEquiv g]
  change |S.symm.toLinearMap.det|⁻¹ •
    𝓕 (fun x : Euclidean n => (gaussianWeight 1 x : ℂ)) (S.toContinuousLinearMap.adjoint w) = _
  rw [fourier_gaussianWeight_one, ← LinearMap.normDet_eq_abs_det]
  rfl

/-- Positive Fourier coefficients at the actual integer frequencies. -/
def ellipsoidFourierCoefficient (S : Euclidean n ≃L[ℝ] Euclidean n) (z : Coeff n) : ℝ :=
  ellipsoidVolume S * gaussianWeight 1 (S.toContinuousLinearMap.adjoint (integerEmbedding n z))

theorem ellipsoidFourierCoefficient_pos (S : Euclidean n ≃L[ℝ] Euclidean n) (z : Coeff n) :
    0 < ellipsoidFourierCoefficient S z :=
  mul_pos (ellipsoidVolume_pos S) (gaussianWeight_pos _ _)

theorem summable_ellipsoidFourierCoefficient (S : Euclidean n ≃L[ℝ] Euclidean n) :
    Summable (ellipsoidFourierCoefficient S) := by
  have he (z : Coeff n) : gaussianWeight 1 (S.toContinuousLinearMap.adjoint (integerEmbedding n z)) =
      ellipsoidWeight (inverseAdjointEquiv S) 0 z := by
    rw [ellipsoidWeight, sub_zero]
    rfl
  unfold ellipsoidFourierCoefficient
  simp only [he]
  exact (summable_ellipsoidWeight (inverseAdjointEquiv S) 0).mul_left _

theorem fourier_ellipsoidKernel_integer (S : Euclidean n ≃L[ℝ] Euclidean n) (z : Coeff n) :
    𝓕 (fun x => (ellipsoidKernel S x : ℂ)) (integerEmbedding n z) =
      (ellipsoidFourierCoefficient S z : ℂ) := by
  rw [fourier_ellipsoidKernel, ellipsoidFourierCoefficient, Complex.ofReal_mul]

end GeometricGaussianLHL
end

end EllipsoidFourier

section EllipsoidPoisson

/-!
## Poisson summation for shifted ellipsoidal lattice Gaussians

Unfolding identifies the Fourier coefficients of the actual continuous
partition function on the torus. Their summability gives pointwise Fourier
inversion, with the exact volume factor and no assumed theta identity.
-/

noncomputable section

open MeasureTheory
open scoped FourierTransform

namespace GeometricGaussianLHL

variable {n : ℕ}

theorem ellipsoidTorus_fourierCoeff (S : Euclidean n ≃L[ℝ] Euclidean n) (z : Coeff n) :
    UnitAddTorus.mFourierCoeff (ellipsoidTorus S) z = (ellipsoidFourierCoefficient S z : ℂ) := by
  let g : Euclidean n → ℂ := fun x => UnitAddTorus.mFourier (-z) (integerTorusMk x)
  have hg : Continuous g := by fun_prop
  have hk : Continuous (ellipsoidKernel S) := by unfold ellipsoidKernel gaussianWeight; fun_prop
  have hi : Integrable (fun x => g x * (ellipsoidKernel S x : ℂ)) := by
    have hbase : Integrable (ellipsoidKernel S) :=
      integrable_gaussianWeight_comp_injective S.symm.toLinearMap S.symm.injective (by norm_num)
    apply hbase.ofReal.bdd_mul hg.aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun x => (mFourier_norm_apply (-z) (integerTorusMk x)).le)
  rw [mFourierCoeff_eq_centeredCell]
  simp only [ellipsoidTorus_mk, ellipsoidPartition_eq_tsum_kernel]
  rw [integral_periodic_mul_periodization_complex g (ellipsoidKernel S) hg hk hi
    (fun x k => mFourier_integer_periodic (-z) k x)]
  simp only [g, mFourier_neg_integerTorusMk]
  simpa only [Real.fourier_eq, Circle.smul_def, smul_eq_mul] using fourier_ellipsoidKernel_integer S z

theorem summable_ellipsoidTorus_fourierCoeff (S : Euclidean n ≃L[ℝ] Euclidean n) :
    Summable (UnitAddTorus.mFourierCoeff (ellipsoidTorus S)) := by
  have he : UnitAddTorus.mFourierCoeff (ellipsoidTorus S) =
      fun z => (ellipsoidFourierCoefficient S z : ℂ) := funext (ellipsoidTorus_fourierCoeff S)
  rw [he]
  exact Complex.summable_ofReal.mpr (summable_ellipsoidFourierCoefficient S)

theorem summable_ellipsoidFourierTerm (S : Euclidean n ≃L[ℝ] Euclidean n)
    (c : Euclidean n) : Summable (fun z : Coeff n =>
      (ellipsoidFourierCoefficient S z : ℂ) * UnitAddTorus.mFourier z (integerTorusMk c)) := by
  apply (summable_ellipsoidFourierCoefficient S).of_norm_bounded
  intro z
  rw [norm_mul, mFourier_norm_apply, mul_one,
    Complex.norm_of_nonneg (ellipsoidFourierCoefficient_pos S z).le]

/-- The full shifted theta identity, in every finite dimension. -/
theorem ellipsoidPartition_poisson (S : Euclidean n ≃L[ℝ] Euclidean n) (c : Euclidean n) :
    (ellipsoidPartition S c : ℂ) = ∑' z : Coeff n,
      (ellipsoidFourierCoefficient S z : ℂ) * UnitAddTorus.mFourier z (integerTorusMk c) := by
  have h := UnitAddTorus.hasSum_mFourier_series_apply_of_summable
    (summable_ellipsoidTorus_fourierCoeff S) (integerTorusMk c)
  simpa only [ellipsoidTorus_fourierCoeff, smul_eq_mul, ellipsoidTorus_mk] using h.tsum_eq.symm

end GeometricGaussianLHL
end

end EllipsoidPoisson

section EllipsoidFlatness

/-!
## Shifted theta flatness from actual dual Gaussian mass

The zero Fourier coefficient is the Gaussian volume. Every other
character has modulus one, so the shifted partition differs from that
volume by at most the nonzero Gaussian mass of the whitened lattice dual.
-/

noncomputable section

open scoped ENNReal

namespace GeometricGaussianLHL

variable {n : ℕ}

theorem ellipsoidPartition_sub_volume_le (S : Euclidean n ≃L[ℝ] Euclidean n) (c : Euclidean n) :
    |ellipsoidPartition S c - ellipsoidVolume S| ≤ ellipsoidVolume S * ellipsoidDualRemainder S := by
  classical
  let f : Coeff n → ℂ := fun z =>
    (ellipsoidFourierCoefficient S z : ℂ) * UnitAddTorus.mFourier z (integerTorusMk c)
  let g : Coeff n → ℂ := fun z => if z = 0 then 0 else f z
  have hzero : f 0 = (ellipsoidVolume S : ℂ) := by
    simp [f, ellipsoidFourierCoefficient, UnitAddTorus.mFourier_zero]
  have hid : (ellipsoidPartition S c : ℂ) - (ellipsoidVolume S : ℂ) = ∑' z, g z := by
    rw [ellipsoidPartition_poisson, (summable_ellipsoidFourierTerm S c).tsum_eq_add_tsum_ite 0]
    change f 0 + (∑' z, g z) - (ellipsoidVolume S : ℂ) = _
    rw [hzero, add_sub_cancel_left]
  have hnorm (z : Coeff n) : ‖g z‖ = ellipsoidVolume S * ellipsoidDualWeight S z := by
    by_cases hz : z = 0
    · simp [g, ellipsoidDualWeight, hz]
    · simp only [g, hz, ite_false, f, norm_mul, mFourier_norm_apply, mul_one,
        Complex.norm_of_nonneg (ellipsoidFourierCoefficient_pos S z).le, ellipsoidDualWeight]
      rw [ellipsoidWeight, sub_zero]
      rfl
  have hg : Summable (fun z => ‖g z‖) := by
    simp only [hnorm]
    exact (summable_ellipsoidDualWeight S).mul_left _
  have h := norm_tsum_le_tsum_norm hg
  rw [← hid] at h
  simpa only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, hnorm,
    tsum_mul_left, ellipsoidDualRemainder] using h

theorem ellipsoidPartition_relative_flatness (S : Euclidean n ≃L[ℝ] Euclidean n)
    (c : Euclidean n) :
    |ellipsoidPartition S c / ellipsoidVolume S - 1| ≤ ellipsoidDualRemainder S := by
  have hv := ellipsoidVolume_pos S
  have he : ellipsoidPartition S c / ellipsoidVolume S - 1 =
      (ellipsoidPartition S c - ellipsoidVolume S) / ellipsoidVolume S := by field_simp
  rw [he, abs_div, abs_of_pos hv]
  exact (div_le_iff₀ hv).mpr (by simpa only [mul_comm] using ellipsoidPartition_sub_volume_le S c)

/-- A smoothing certificate gives both uniform shifted-mass bounds. -/
theorem ellipsoidPartition_flat_of_smoothAt (S : Euclidean n ≃L[ℝ] Euclidean n)
    {ε : ℝ} (hε : 0 ≤ ε) (h : SmoothAt (whitenedIntegerLattice S) ε 1) (c : Euclidean n) :
    (1 - ε) * ellipsoidVolume S ≤ ellipsoidPartition S c ∧
      ellipsoidPartition S c ≤ (1 + ε) * ellipsoidVolume S := by
  have hb := (ellipsoidPartition_relative_flatness S c).trans
    (ellipsoidDualRemainder_le_of_smoothAt S hε h)
  obtain ⟨hl, hu⟩ := abs_le.mp hb
  have hv := ellipsoidVolume_pos S
  constructor
  · apply (le_div_iff₀ hv).mp
    linarith
  · apply (div_le_iff₀ hv).mp
    linarith

end GeometricGaussianLHL
end

end EllipsoidFlatness

section LatticeFlatness

/-!
## Shifted Gaussian flatness on full lattices

Coordinates identify both the shifted Gaussian partition and the actual
whitened lattice. Thus theta flatness is stated using the intrinsic dual
mass and the actual covolume, independently of the chosen integral basis.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace GeometricGaussianLHL

variable {n : ℕ} (L : Submodule ℤ (Euclidean n)) [DiscreteTopology L] [IsZLattice ℝ L]

def latticeShiftedWeight (S : Euclidean n ≃L[ℝ] Euclidean n) (c : Euclidean n) (v : L) : ℝ :=
  gaussianWeight 1 (S.symm ((v : Euclidean n) - c))

def latticeShiftedPartition (S : Euclidean n ≃L[ℝ] Euclidean n) (c : Euclidean n) : ℝ :=
  ∑' v : L, latticeShiftedWeight L S c v

theorem latticeShiftedWeight_coordinates (S : Euclidean n ≃L[ℝ] Euclidean n)
    (c : Euclidean n) (z : Coeff n) :
    latticeShiftedWeight L S c (fullLatticeCoordinateEquiv L z) =
      ellipsoidWeight (latticeCoefficientShape L S) ((fullLatticeRealEquiv L).symm c) z := by
  unfold latticeShiftedWeight ellipsoidWeight latticeCoefficientShape
  change gaussianWeight 1 (S.symm ((fullLatticeCoordinateEquiv L z : Euclidean n) - c)) =
    gaussianWeight 1 (S.symm (fullLatticeRealEquiv L
      (integerEmbedding n z - (fullLatticeRealEquiv L).symm c)))
  simp only [map_sub, ContinuousLinearEquiv.apply_symm_apply, fullLatticeRealEquiv_integer]

theorem summable_latticeShiftedWeight (S : Euclidean n ≃L[ℝ] Euclidean n) (c : Euclidean n) :
    Summable (latticeShiftedWeight L S c) := by
  have h := (summable_ellipsoidWeight (latticeCoefficientShape L S)
    ((fullLatticeRealEquiv L).symm c)).comp_injective (fullLatticeCoordinateEquiv L).symm.injective
  apply h.congr
  intro v
  simpa only [Function.comp_def, LinearEquiv.apply_symm_apply] using
    (latticeShiftedWeight_coordinates L S c ((fullLatticeCoordinateEquiv L).symm v)).symm

theorem latticeShiftedPartition_coordinates (S : Euclidean n ≃L[ℝ] Euclidean n) (c : Euclidean n) :
    latticeShiftedPartition L S c =
      ellipsoidPartition (latticeCoefficientShape L S) ((fullLatticeRealEquiv L).symm c) := by
  unfold latticeShiftedPartition ellipsoidPartition
  rw [← (fullLatticeCoordinateEquiv L).toEquiv.tsum_eq]
  exact tsum_congr (latticeShiftedWeight_coordinates L S c)

theorem whitened_lattice_coordinates (S : Euclidean n ≃L[ℝ] Euclidean n) :
    whitenedIntegerLattice (latticeCoefficientShape L S) = latticeImage S.symm.toContinuousLinearMap L := by
  have hL : L = latticeImage (fullLatticeRealEquiv L).toContinuousLinearMap (integerLattice n) :=
    fullLattice_eq_basis_image L (fullLatticeIntegralBasis L)
  calc
    whitenedIntegerLattice (latticeCoefficientShape L S) =
        latticeImage S.symm.toContinuousLinearMap
          (latticeImage (fullLatticeRealEquiv L).toContinuousLinearMap (integerLattice n)) := by
      unfold whitenedIntegerLattice latticeImage
      rw [← Submodule.map_comp]
      rfl
    _ = latticeImage S.symm.toContinuousLinearMap L := by rw [← hL]

theorem latticeCoefficientShape_volume (S : Euclidean n ≃L[ℝ] Euclidean n) :
    ellipsoidVolume (latticeCoefficientShape L S) =
      (ZLattice.covolume (latticeImage S.symm.toContinuousLinearMap L))⁻¹ := by
  rw [← whitened_lattice_coordinates L S, whitenedIntegerLattice,
    covolume_latticeImage_equiv, integerLattice_covolume, mul_one]
  rfl

/-- Uniform flatness for every centre and every full Euclidean lattice. -/
theorem latticeShiftedPartition_flat_of_smoothAt (S : Euclidean n ≃L[ℝ] Euclidean n)
    {ε : ℝ} (hε : 0 ≤ ε) (h : SmoothAt (latticeImage S.symm.toContinuousLinearMap L) ε 1)
    (c : Euclidean n) :
    (1 - ε) / ZLattice.covolume (latticeImage S.symm.toContinuousLinearMap L) ≤
        latticeShiftedPartition L S c ∧
      latticeShiftedPartition L S c ≤
        (1 + ε) / ZLattice.covolume (latticeImage S.symm.toContinuousLinearMap L) := by
  have hw : SmoothAt (whitenedIntegerLattice (latticeCoefficientShape L S)) ε 1 := by
    rw [whitened_lattice_coordinates]
    exact h
  have hb := ellipsoidPartition_flat_of_smoothAt (latticeCoefficientShape L S) hε hw
    ((fullLatticeRealEquiv L).symm c)
  rw [← latticeShiftedPartition_coordinates, latticeCoefficientShape_volume] at hb
  simpa only [div_eq_mul_inv] using hb

end GeometricGaussianLHL
end

end LatticeFlatness

section LatticeIsotropicFlatness

/-!
## Shifted Gaussian flatness in finite-dimensional inner-product spaces

An orthonormal coordinate map transports the actual Gaussian partition,
dual mass, and covolume. This removes any choice of Euclidean coordinates
from the full-lattice flatness theorem.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace GeometricGaussianLHL

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

def shiftedLatticeWeight (L : Submodule ℤ E) (c : E) (v : L) : ℝ :=
  gaussianWeight 1 ((v : E) - c)

def shiftedLatticePartition (L : Submodule ℤ E) (c : E) : ℝ :=
  ∑' v : L, shiftedLatticeWeight L c v

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem shiftedLatticeWeight_isometry (L : Submodule ℤ E) (e : E ≃ₗᵢ[ℝ] F)
    (c : E) (v : L) :
    shiftedLatticeWeight (latticeImage e.toContinuousLinearEquiv.toContinuousLinearMap L)
        (e c) (latticeImageEquiv e.toContinuousLinearEquiv L v) =
      shiftedLatticeWeight L c v := by
  change gaussianWeight 1 (e (v : E) - e c) = gaussianWeight 1 ((v : E) - c)
  rw [← map_sub]
  simp only [gaussianWeight, e.norm_map]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem shiftedLatticePartition_isometry (L : Submodule ℤ E) (e : E ≃ₗᵢ[ℝ] F) (c : E) :
    shiftedLatticePartition (latticeImage e.toContinuousLinearEquiv.toContinuousLinearMap L)
        (e c) = shiftedLatticePartition L c := by
  unfold shiftedLatticePartition
  rw [← (latticeImageEquiv e.toContinuousLinearEquiv L).toEquiv.tsum_eq]
  exact tsum_congr (shiftedLatticeWeight_isometry L e c)

theorem summable_shiftedLatticeWeight_full (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L] (c : E) :
    Summable (shiftedLatticeWeight L c) := by
  let e := (stdOrthonormalBasis ℝ E).repr
  let M := latticeImage e.toContinuousLinearEquiv.toContinuousLinearMap L
  let : DiscreteTopology M := latticeImage_discrete e.toContinuousLinearEquiv L
  let : IsZLattice ℝ M := ⟨latticeImage_equiv_span_top L
    (IsZLattice.span_top (K := ℝ) (L := L)) e.toContinuousLinearEquiv⟩
  have h := (summable_latticeShiftedWeight M (ContinuousLinearEquiv.refl ℝ _) (e c)).comp_injective
    (latticeImageEquiv e.toContinuousLinearEquiv L).injective
  apply h.congr
  intro v
  exact shiftedLatticeWeight_isometry L e c v

variable [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]

theorem covolume_latticeImage_isometry (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L] (e : E ≃ₗᵢ[ℝ] F) :
    ZLattice.covolume (latticeImage e.toContinuousLinearEquiv.toContinuousLinearMap L) =
      ZLattice.covolume L := by
  rw [covolume_latticeImage_equiv]
  change e.toLinearIsometry.toLinearMap.normDet * ZLattice.covolume L = _
  rw [e.toLinearIsometry.normDet_eq_one, one_mul]

/-- Full-lattice flatness, with no distinguished coordinates or positive-rank assumption. -/
theorem shiftedLatticePartition_flat_full (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L] {ε : ℝ} (hε : 0 ≤ ε)
    (h : SmoothAt L ε 1) (c : E) :
    (1 - ε) / ZLattice.covolume L ≤ shiftedLatticePartition L c ∧
      shiftedLatticePartition L c ≤ (1 + ε) / ZLattice.covolume L := by
  let e := (stdOrthonormalBasis ℝ E).repr
  let M := latticeImage e.toContinuousLinearEquiv.toContinuousLinearMap L
  let : DiscreteTopology M := latticeImage_discrete e.toContinuousLinearEquiv L
  let : IsZLattice ℝ M := ⟨latticeImage_equiv_span_top L
    (IsZLattice.span_top (K := ℝ) (L := L)) e.toContinuousLinearEquiv⟩
  have hs : SmoothAt M ε 1 := (smoothAt_isometry_iff L
    (IsZLattice.span_top (K := ℝ) (L := L)) e ε 1).mpr h
  have hm : latticeImage (ContinuousLinearEquiv.refl ℝ (Euclidean (Module.finrank ℝ E))).symm.toContinuousLinearMap M = M := by
    change M.map (LinearMap.id : Euclidean (Module.finrank ℝ E) →ₗ[ℤ] _) = M
    exact Submodule.map_id M
  have hb := latticeShiftedPartition_flat_of_smoothAt M (ContinuousLinearEquiv.refl ℝ _) hε
    (by simpa only [hm] using hs) (e c)
  rw [hm] at hb
  change (1 - ε) / ZLattice.covolume M ≤ shiftedLatticePartition M (e c) ∧
    shiftedLatticePartition M (e c) ≤ (1 + ε) / ZLattice.covolume M at hb
  simpa only [M, shiftedLatticePartition_isometry, covolume_latticeImage_isometry] using hb

end GeometricGaussianLHL
end

end LatticeIsotropicFlatness

section IntrinsicFlatness

/-!
## Shifted Gaussian masses of lower-rank lattices

Inside the real span, flatness uses the intrinsic dual and covolume. For
arbitrary ambient centres, orthogonal decomposition gives the exact
transverse Gaussian factor. All partitions are convergent lattice sums.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace GeometricGaussianLHL

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem shiftedLatticeWeight_intrinsic (L : Submodule ℤ E)
    (c : Submodule.span ℝ (L : Set E)) (v : intrinsicLattice L) :
    shiftedLatticeWeight (intrinsicLattice L) c v =
      shiftedLatticeWeight L (c : E) (intrinsicLatticeEquiv L v) := rfl

omit [FiniteDimensional ℝ E] in
theorem shiftedLatticePartition_intrinsic (L : Submodule ℤ E)
    (c : Submodule.span ℝ (L : Set E)) :
    shiftedLatticePartition (intrinsicLattice L) c = shiftedLatticePartition L (c : E) := by
  unfold shiftedLatticePartition
  rw [← (intrinsicLatticeEquiv L).toEquiv.tsum_eq]
  rfl

theorem summable_shiftedLatticeWeight_in_span (L : Submodule ℤ E) [DiscreteTopology L]
    (c : Submodule.span ℝ (L : Set E)) :
    Summable (shiftedLatticeWeight L (c : E)) := by
  apply (intrinsicLatticeEquiv L).toEquiv.summable_iff.mp
  exact summable_shiftedLatticeWeight_full (intrinsicLattice L) c

theorem shiftedLatticeWeight_orthogonal_factor (L : Submodule ℤ E) (c : E) (v : L) :
    shiftedLatticeWeight L c v =
      gaussianWeight 1 ((Submodule.span ℝ (L : Set E))ᗮ.starProjection c) *
        shiftedLatticeWeight L ((Submodule.span ℝ (L : Set E)).starProjection c) v := by
  let S := Submodule.span ℝ (L : Set E)
  have hv : (v : E) ∈ S := Submodule.subset_span v.property
  have hp : S.starProjection (v : E) = v := Submodule.starProjection_eq_self_iff.mpr hv
  have ho : Sᗮ.starProjection (v : E) = 0 :=
    Submodule.starProjection_orthogonal_apply_eq_zero hv
  have hn := Submodule.norm_sq_eq_add_norm_sq_starProjection ((v : E) - c) S
  simp only [map_sub, hp, ho, zero_sub, norm_neg] at hn
  change gaussianWeight 1 ((v : E) - c) =
    gaussianWeight 1 (Sᗮ.starProjection c) * gaussianWeight 1 ((v : E) - S.starProjection c)
  simp only [gaussianWeight, hn, mul_add, Real.exp_add]
  exact mul_comm _ _

/-- Absolute convergence for every ambient centre, without a full-rank assumption. -/
theorem summable_shiftedLatticeWeight (L : Submodule ℤ E) [DiscreteTopology L] (c : E) :
    Summable (shiftedLatticeWeight L c) := by
  let S := Submodule.span ℝ (L : Set E)
  have h := (summable_shiftedLatticeWeight_in_span L (S.orthogonalProjectionOnto c)).mul_left
    (gaussianWeight 1 (Sᗮ.starProjection c))
  apply h.congr
  intro v
  exact (shiftedLatticeWeight_orthogonal_factor L c v).symm

/-- The exact dependence on the component of the centre perpendicular to the lattice span. -/
theorem shiftedLatticePartition_orthogonal_factor (L : Submodule ℤ E) (c : E) :
    shiftedLatticePartition L c =
      gaussianWeight 1 ((Submodule.span ℝ (L : Set E))ᗮ.starProjection c) *
        shiftedLatticePartition L ((Submodule.span ℝ (L : Set E)).starProjection c) := by
  unfold shiftedLatticePartition
  simp_rw [shiftedLatticeWeight_orthogonal_factor L c]
  rw [tsum_mul_left]

variable [MeasurableSpace E] [BorelSpace E]

theorem shiftedLatticePartition_flat_in_span (L : Submodule ℤ E) [DiscreteTopology L]
    {ε : ℝ} (hε : 0 ≤ ε) (h : SmoothAt L ε 1)
    (c : Submodule.span ℝ (L : Set E)) :
    (1 - ε) / intrinsicCovolume L ≤ shiftedLatticePartition L (c : E) ∧
      shiftedLatticePartition L (c : E) ≤ (1 + ε) / intrinsicCovolume L := by
  have hb := shiftedLatticePartition_flat_full (intrinsicLattice L) hε
    ((smoothAt_intrinsic_iff L ε 1).mpr h) c
  rw [shiftedLatticePartition_intrinsic] at hb
  exact hb

/-- Intrinsic flatness for every ambient centre, retaining the transverse Gaussian. -/
theorem shiftedLatticePartition_flat (L : Submodule ℤ E) [DiscreteTopology L]
    {ε : ℝ} (hε : 0 ≤ ε) (h : SmoothAt L ε 1) (c : E) :
    gaussianWeight 1 ((Submodule.span ℝ (L : Set E))ᗮ.starProjection c) *
          ((1 - ε) / intrinsicCovolume L) ≤ shiftedLatticePartition L c ∧
      shiftedLatticePartition L c ≤
        gaussianWeight 1 ((Submodule.span ℝ (L : Set E))ᗮ.starProjection c) *
          ((1 + ε) / intrinsicCovolume L) := by
  let S := Submodule.span ℝ (L : Set E)
  have hb := shiftedLatticePartition_flat_in_span L hε h (S.orthogonalProjectionOnto c)
  rw [shiftedLatticePartition_orthogonal_factor]
  exact ⟨mul_le_mul_of_nonneg_left hb.1 (gaussianWeight_pos _ _).le,
    mul_le_mul_of_nonneg_left hb.2 (gaussianWeight_pos _ _).le⟩

end GeometricGaussianLHL
end

end IntrinsicFlatness

section WhitenedFlatness

/-!
## Flatness after a Gaussian shape transformation

The non-strict smoothing hypothesis is applied at its infimum and then
transported by the inverse shape. The proof allows a zero operator norm
and a zero smoothing infimum. Shifted shaped sums are identified with the
actual isotropic partition of the image lattice.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace GeometricGaussianLHL

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

theorem smoothAt_image_one_of_norm_mul_smoothingParameter_le (T : E →L[ℝ] F)
    (L : Submodule ℤ E) [DiscreteTopology L] {ε : ℝ} (hε : 0 < ε)
    (h : ‖T‖ * smoothingParameter L ε ≤ 1) : SmoothAt (latticeImage T L) ε 1 := by
  have hex := exists_smoothAt L hε
  refine ⟨zero_lt_one, ?_⟩
  exact (nonzeroDualMass_antitone (latticeImage T L)
    (mul_nonneg (norm_nonneg T) (smoothingParameter_nonneg_of_exists hex)) h).trans
      ((nonzeroDualMass_metric_change T L (smoothingParameter L ε)).trans
        (nonzeroDualMass_smoothingParameter_le hex))

theorem smoothAt_image_one_of_smoothingParameter_le_inv_norm (T : E →L[ℝ] F)
    (L : Submodule ℤ E) [DiscreteTopology L] {ε : ℝ} (hε : 0 < ε)
    (h : smoothingParameter L ε ≤ ‖T‖⁻¹) : SmoothAt (latticeImage T L) ε 1 := by
  apply smoothAt_image_one_of_norm_mul_smoothingParameter_le T L hε
  by_cases hz : ‖T‖ = 0
  · simp only [hz, zero_mul, zero_le_one]
  · calc
      ‖T‖ * smoothingParameter L ε ≤ ‖T‖ * ‖T‖⁻¹ :=
        mul_le_mul_of_nonneg_left h (norm_nonneg T)
      _ = 1 := mul_inv_cancel₀ hz

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem sum_gaussianWeight_equiv_shift (T : E ≃L[ℝ] F) (L : Submodule ℤ E) (c : E) :
    (∑' v : L, gaussianWeight 1 (T ((v : E) - c))) =
      shiftedLatticePartition (latticeImage T.toContinuousLinearMap L) (T c) := by
  unfold shiftedLatticePartition
  rw [← (latticeImageEquiv T L).toEquiv.tsum_eq]
  apply tsum_congr
  intro v
  change gaussianWeight 1 (T ((v : E) - c)) = gaussianWeight 1 (T (v : E) - T c)
  rw [map_sub]

omit [FiniteDimensional ℝ E] in
theorem summable_gaussianWeight_equiv_shift (T : E ≃L[ℝ] F)
    (L : Submodule ℤ E) [DiscreteTopology L] (c : E) :
    Summable (fun v : L => gaussianWeight 1 (T ((v : E) - c))) := by
  let := latticeImage_discrete T L
  have h := (summable_shiftedLatticeWeight (latticeImage T.toContinuousLinearMap L) (T c)).comp_injective
    (latticeImageEquiv T L).injective
  apply h.congr
  intro v
  change gaussianWeight 1 (T (v : E) - T c) = gaussianWeight 1 (T ((v : E) - c))
  rw [map_sub]

variable [MeasurableSpace F] [BorelSpace F]

/-- Uniform bounds for the actual transformed Gaussian sum at every ambient centre. -/
theorem sum_gaussianWeight_equiv_shift_flat (T : E ≃L[ℝ] F)
    (L : Submodule ℤ E) [DiscreteTopology L] {ε : ℝ} (hε : 0 < ε)
    (h : ‖T.toContinuousLinearMap‖ * smoothingParameter L ε ≤ 1) (c : E) :
    let M := latticeImage T.toContinuousLinearMap L
    let g := gaussianWeight 1 ((Submodule.span ℝ (M : Set F))ᗮ.starProjection (T c))
    g * ((1 - ε) / intrinsicCovolume M) ≤
        (∑' v : L, gaussianWeight 1 (T ((v : E) - c))) ∧
      (∑' v : L, gaussianWeight 1 (T ((v : E) - c))) ≤
        g * ((1 + ε) / intrinsicCovolume M) := by
  let := latticeImage_discrete T L
  rw [sum_gaussianWeight_equiv_shift]
  exact shiftedLatticePartition_flat _ hε.le
    (smoothAt_image_one_of_norm_mul_smoothingParameter_le T.toContinuousLinearMap L hε h) (T c)

/-- Inverse-shape form of the paper's non-strict minimum-width hypothesis. -/
theorem sum_gaussianWeight_equiv_shift_flat_of_inv_norm (T : E ≃L[ℝ] F)
    (L : Submodule ℤ E) [DiscreteTopology L] {ε : ℝ} (hε : 0 < ε)
    (h : smoothingParameter L ε ≤ ‖T.toContinuousLinearMap‖⁻¹) (c : E) :
    let M := latticeImage T.toContinuousLinearMap L
    let g := gaussianWeight 1 ((Submodule.span ℝ (M : Set F))ᗮ.starProjection (T c))
    g * ((1 - ε) / intrinsicCovolume M) ≤
        (∑' v : L, gaussianWeight 1 (T ((v : E) - c))) ∧
      (∑' v : L, gaussianWeight 1 (T ((v : E) - c))) ≤
        g * ((1 + ε) / intrinsicCovolume M) := by
  let := latticeImage_discrete T L
  rw [sum_gaussianWeight_equiv_shift]
  exact shiftedLatticePartition_flat _ hε.le
    (smoothAt_image_one_of_smoothingParameter_le_inv_norm T.toContinuousLinearMap L hε h) (T c)

end GeometricGaussianLHL
end

end WhitenedFlatness
