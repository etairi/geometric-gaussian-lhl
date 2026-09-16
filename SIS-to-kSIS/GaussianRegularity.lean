import «SIS-to-kSIS».PrimeResidueBounds

/-!
# Gaussian mass estimates for modular regularity

The Gaussian norm tail bounds the nonzero probability. The atom at zero then
bounds the partition, giving explicit exponentially small errors from a
lower bound on lattice-vector length. Poisson summation interpolates to
arbitrary widths, including for the actual embedded ideal lattices.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Module GeometricGaussianLHL MeasureTheory
open scoped ENNReal Classical
namespace SISToKSIS
variable {n : ℕ} (L : Submodule ℤ (Euclidean n)) [DiscreteTopology L] [IsZLattice ℝ L]

/-- If every nonzero point lies in a small Gaussian tail, the partition is close to one. -/
theorem latticeGaussianPartition_le_of_separation
    (S : Euclidean n ≃L[ℝ] Euclidean n) {σ u δ : ℝ}
    (hσ : 0 < σ) (hu : 0 ≤ u) (hS : ‖S.toContinuousLinearMap‖ ≤ σ)
    (hshort : ∀ x : L, x ≠ 0 → σ * u ≤ ‖(x : Euclidean n)‖)
    (hδ : 0 ≤ δ) (hδone : δ < 1)
    (hbudget : Real.sqrt 2 ^ n * Real.exp (-Real.pi * u ^ 2 / 2) ≤ δ) :
    latticeGaussianPartition L S ≤ 1 / (1 - δ) := by
  let p := latticeGaussian L S
  have htail : p.toOuterMeasure {x : L | x ≠ 0} ≤ ENNReal.ofReal δ := by
    apply le_trans (p.toOuterMeasure.mono (fun x hx => hshort x hx))
    exact (latticeGaussian_norm_tail L S hσ hu hS).trans (ENNReal.ofReal_le_ofReal hbudget)
  have hadd : p 0 + p.toOuterMeasure {x : L | x ≠ 0} = 1 := by
    rw [PMF.toOuterMeasure_apply]
    calc
      _ = p 0 + ∑' x : L, if x = 0 then 0 else p x := by
        congr 1
        apply tsum_congr
        intro x
        by_cases hx : x = 0 <;> simp [Set.indicator, hx]
      _ = ∑' x : L, p x := by
        rw [ENNReal.tsum_eq_add_tsum_ite (f := fun x => p x) 0]
        congr 1
        apply tsum_congr
        intro x
        by_cases hx : x = 0 <;> simp [hx]
      _ = 1 := p.tsum_coe
  have hp0 : p 0 = ENNReal.ofReal (1 / latticeGaussianPartition L S) := by
    rw [latticeGaussian_apply]
    simp [latticeGaussianWeight]
  have hZ := latticeGaussianPartition_pos L S
  have hle : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (1 / latticeGaussianPartition L S + δ) := by
    rw [ENNReal.ofReal_add (by positivity) hδ, ← hp0, ← hadd]
    exact add_le_add le_rfl htail
  have hreal : 1 ≤ 1 / latticeGaussianPartition L S + δ := by
    apply (ENNReal.ofReal_le_ofReal_iff (show 0 ≤ 1 / latticeGaussianPartition L S + δ by positivity)).mp
    simpa only [ENNReal.ofReal_one] using hle
  have hm := mul_le_mul_of_nonneg_right hreal hZ.le
  simp only [add_mul, div_mul_cancel₀ _ hZ.ne', one_mul] at hm
  apply (le_div_iff₀ (sub_pos.mpr hδone)).mpr
  nlinarith

/-- Scalar Gaussian mass from a lower bound on every nonzero lattice length. -/
theorem gaussianMass_le_of_separation {t a δ : ℝ} (ht : 0 < t) (ha : 0 ≤ a)
    (hshort : ∀ x : L, x ≠ 0 → a ≤ ‖(x : Euclidean n)‖)
    (hδ : 0 ≤ δ) (hδone : δ < 1)
    (hbudget : Real.sqrt 2 ^ n * Real.exp (-Real.pi * (t * a) ^ 2 / 2) ≤ δ) :
    gaussianMass t (L : Set (Euclidean n)) ≤ ENNReal.ofReal (1 / (1 - δ)) := by
  let S := euclideanScalarShape n t⁻¹ (inv_ne_zero ht.ne')
  have hw (x : L) : latticeGaussianWeight L S x = gaussianWeight t (x : Euclidean n) := by
    simp only [latticeGaussianWeight, S, euclideanScalarShape_symm_apply, inv_inv,
      gaussianWeight, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, one_pow]
    congr 1
    ring
  have hS : ‖S.toContinuousLinearMap‖ ≤ t⁻¹ := by
    rw [euclideanScalarShape_toCLM, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht)]
    exact mul_le_of_le_one_right (inv_pos.mpr ht).le (ContinuousLinearMap.norm_id_le)
  have hZ := latticeGaussianPartition_le_of_separation L S (inv_pos.mpr ht)
    (mul_nonneg ht.le ha) hS
    (fun x hx => by simpa only [inv_mul_cancel_left₀ ht.ne'] using hshort x hx)
    hδ hδone hbudget
  have he : gaussianMass t (L : Set (Euclidean n)) = ENNReal.ofReal (latticeGaussianPartition L S) := by
    unfold gaussianMass latticeGaussianPartition
    rw [ENNReal.ofReal_tsum_of_nonneg (fun x => (latticeGaussianWeight_pos L S x).le)
      (summable_latticeGaussianWeight L S)]
    exact tsum_congr (fun x => congrArg ENNReal.ofReal (hw x).symm)
  rw [he]
  exact ENNReal.ofReal_le_ofReal hZ

theorem gaussianMass_le_one_add_of_separation {t a δ : ℝ} (ht : 0 < t) (ha : 0 ≤ a)
    (hshort : ∀ x : L, x ≠ 0 → a ≤ ‖(x : Euclidean n)‖)
    (hδ : 0 ≤ δ) (hδhalf : δ ≤ 1 / 2)
    (hbudget : Real.sqrt 2 ^ n * Real.exp (-Real.pi * (t * a) ^ 2 / 2) ≤ δ) :
    gaussianMass t (L : Set (Euclidean n)) ≤ ENNReal.ofReal (1 + 2 * δ) := by
  have hδone : δ < 1 := by linarith
  apply (gaussianMass_le_of_separation L ht ha hshort hδ hδone hbudget).trans
  apply ENNReal.ofReal_le_ofReal
  apply (div_le_iff₀ (sub_pos.mpr hδone)).mpr
  nlinarith

/-- A dual minimum yields an explicit smoothing certificate through the Gaussian tail. -/
theorem smoothAt_of_dual_separation {t a δ : ℝ} (ht : 0 < t) (ha : 0 ≤ a)
    (hshort : ∀ x : latticeDual L, x ≠ 0 → a ≤ ‖(x : Euclidean n)‖)
    (hδ : 0 ≤ δ) (hδhalf : δ ≤ 1 / 2)
    (hbudget : Real.sqrt 2 ^ n * Real.exp (-Real.pi * (t * a) ^ 2 / 2) ≤ δ) :
    SmoothAt L (2 * δ) t := by
  let : DiscreteTopology (latticeDual L) := fullLattice_dual_discrete L
  let : IsZLattice ℝ (latticeDual L) := ⟨fullLattice_dual_span L⟩
  have h := gaussianMass_le_one_add_of_separation (latticeDual L) ht ha hshort hδ hδhalf hbudget
  change dualMass L t ≤ _ at h
  rw [dualMass_eq_one_add, ENNReal.ofReal_add (by positivity) (mul_nonneg (by norm_num) hδ),
    ENNReal.ofReal_one] at h
  exact ⟨ht, (ENNReal.add_le_add_iff_left (by simp)).mp h⟩

theorem gaussian_separation_tail_budget (d m : ℕ) (hm : 1 ≤ m) {u : ℝ}
    (hu : 4 * Real.sqrt ((d : ℝ) * m) ≤ u) :
    Real.sqrt 2 ^ d * Real.exp (-Real.pi * u ^ 2 / 2) ≤
      (2 : ℝ) ^ (-(3 * (d : ℝ) * m)) := by
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hdm : (d : ℝ) ≤ (d : ℝ) * m := le_mul_of_one_le_right hd hmR
  have hlog : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hleft := mul_le_mul_of_nonneg_right hlog (show 0 ≤ (d : ℝ) / 2 by positivity)
  have hright := mul_le_mul_of_nonpos_right hlog (show -(3 * (d : ℝ) * m) ≤ 0 from neg_nonpos.mpr (by positivity))
  have hu0 : 0 ≤ u := (by positivity : 0 ≤ 4 * Real.sqrt ((d : ℝ) * m)).trans hu
  have hsq := (sq_le_sq₀ (by positivity : 0 ≤ 4 * Real.sqrt ((d : ℝ) * m)) hu0).mpr hu
  rw [mul_pow, Real.sq_sqrt (by positivity)] at hsq
  have hpi := mul_le_mul_of_nonneg_right Real.two_le_pi (sq_nonneg u)
  rw [sqrt_two_pow_eq_rpow, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith

theorem gaussianMass_explicit_separation (m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m)
    {t a : ℝ} (ht : 0 < t) (ha : 0 ≤ a)
    (hshort : ∀ x : L, x ≠ 0 → a ≤ ‖(x : Euclidean n)‖)
    (hscale : 4 * Real.sqrt ((n : ℝ) * m) ≤ t * a) :
    gaussianMass t (L : Set (Euclidean n)) ≤
      ENNReal.ofReal (1 + 2 * (2 : ℝ) ^ (-(3 * (n : ℝ) * m))) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hprod : (1 : ℝ) ≤ (n : ℝ) * m := one_le_mul_of_one_le_of_one_le hnR hmR
  have hhalf : (2 : ℝ) ^ (-(3 * (n : ℝ) * m)) ≤ 1 / 2 := by
    calc
      _ ≤ (2 : ℝ) ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)
      _ = _ := by norm_num
  exact gaussianMass_le_one_add_of_separation L ht ha hshort (by positivity) hhalf
    (gaussian_separation_tail_budget n m hm hscale)

end SISToKSIS

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Module GeometricGaussianLHL MeasureTheory
open scoped ENNReal Classical
namespace SISToKSIS
variable {n : ℕ}

theorem ellipsoidPartition_zero_poisson (S : Euclidean n ≃L[ℝ] Euclidean n) :
    ellipsoidPartition S 0 = ∑' z : Coeff n, ellipsoidFourierCoefficient S z := by
  have h := ellipsoidPartition_poisson S 0
  have hz : integerTorusMk (0 : Euclidean n) = 0 := by ext i; simp [integerTorusMk]
  rw [hz] at h
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Pi.zero_apply,
    fourier_eval_zero, Finset.prod_const_one, mul_one] at h
  exact_mod_cast h

theorem ellipsoidVolume_of_scalar (S T : Euclidean n ≃L[ℝ] Euclidean n)
    {r : ℝ} (hr : 0 ≤ r) (hT : T.toContinuousLinearMap = r • S.toContinuousLinearMap) :
    ellipsoidVolume T = r ^ n * ellipsoidVolume S := by
  have hl : T.toLinearMap = r • S.toLinearMap := by
    ext x : 1
    exact congrArg (fun f : Euclidean n →L[ℝ] Euclidean n => f x) hT
  rw [ellipsoidVolume_eq_normDet, ellipsoidVolume_eq_normDet,
    LinearMap.normDet_eq_abs_det, LinearMap.normDet_eq_abs_det, hl, LinearMap.det_smul]
  simp only [Euclidean, finrank_euclideanSpace, Fintype.card_fin, abs_mul, abs_pow, abs_of_nonneg hr]

theorem ellipsoidPartition_scalar_le (S T : Euclidean n ≃L[ℝ] Euclidean n)
    {r : ℝ} (hr : 1 ≤ r) (hT : T.toContinuousLinearMap = r • S.toContinuousLinearMap) :
    ellipsoidPartition T 0 ≤ r ^ n * ellipsoidPartition S 0 := by
  rw [ellipsoidPartition_zero_poisson, ellipsoidPartition_zero_poisson, ← tsum_mul_left]
  apply (summable_ellipsoidFourierCoefficient T).tsum_le_tsum _
    ((summable_ellipsoidFourierCoefficient S).mul_left (r ^ n))
  intro z
  rw [ellipsoidFourierCoefficient, ellipsoidVolume_of_scalar S T (by linarith) hT, hT, map_smul]
  change r ^ n * ellipsoidVolume S * gaussianWeight 1
    (r • S.toContinuousLinearMap.adjoint (integerEmbedding n z)) ≤ _
  have hg : gaussianWeight 1 (r • S.toContinuousLinearMap.adjoint (integerEmbedding n z)) =
      gaussianWeight r (S.toContinuousLinearMap.adjoint (integerEmbedding n z)) := by
    simp only [gaussianWeight, one_pow, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    congr 1
    ring
  rw [hg, ellipsoidFourierCoefficient, ← mul_assoc]
  exact mul_le_mul_of_nonneg_left (gaussianWeight_antitone (by norm_num) hr _)
    (mul_nonneg (pow_nonneg (by linarith) _) (ellipsoidVolume_pos S).le)

variable (L : Submodule ℤ (Euclidean n)) [DiscreteTopology L] [IsZLattice ℝ L]

theorem gaussianMass_eq_coefficientPartition {t : ℝ} (ht : 0 < t) :
    gaussianMass t (L : Set (Euclidean n)) = ENNReal.ofReal
      (ellipsoidPartition (latticeCoefficientShape L (euclideanScalarShape n t⁻¹ (inv_ne_zero ht.ne'))) 0) := by
  let S := euclideanScalarShape n t⁻¹ (inv_ne_zero ht.ne')
  rw [← latticeGaussianPartition_eq L S]
  unfold gaussianMass latticeGaussianPartition
  rw [ENNReal.ofReal_tsum_of_nonneg (fun x => (latticeGaussianWeight_pos L S x).le)
    (summable_latticeGaussianWeight L S)]
  apply tsum_congr
  intro x
  congr 1
  simp only [latticeGaussianWeight, S, euclideanScalarShape_symm_apply, inv_inv,
    gaussianWeight, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, one_pow]
  congr 1
  ring

theorem gaussianMass_scalar_ratio_le {t t₀ : ℝ} (ht : 0 < t) (ht₀ : 0 < t₀) (hle : t ≤ t₀) :
    gaussianMass t (L : Set (Euclidean n)) ≤ ENNReal.ofReal ((t₀ / t) ^ n) *
      gaussianMass t₀ (L : Set (Euclidean n)) := by
  let S := latticeCoefficientShape L (euclideanScalarShape n t₀⁻¹ (inv_ne_zero ht₀.ne'))
  let T := latticeCoefficientShape L (euclideanScalarShape n t⁻¹ (inv_ne_zero ht.ne'))
  have he : T.toContinuousLinearMap = (t₀ / t) • S.toContinuousLinearMap := by
    ext x : 1
    change (fullLatticeRealEquiv L).symm (t⁻¹ • x) =
      (t₀ / t) • (fullLatticeRealEquiv L).symm (t₀⁻¹ • x)
    rw [map_smul, map_smul, smul_smul]
    congr 1
    field_simp
  have h := ellipsoidPartition_scalar_le S T ((one_le_div ht).mpr hle) he
  rw [gaussianMass_eq_coefficientPartition L ht, gaussianMass_eq_coefficientPartition L ht₀]
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (t₀ / t) ^ n)]
  exact ENNReal.ofReal_le_ofReal h

theorem gaussianMass_width_interpolation {t t₀ : ℝ} (ht : 0 < t) (ht₀ : 0 < t₀) :
    gaussianMass t (L : Set (Euclidean n)) ≤ ENNReal.ofReal (max 1 ((t₀ / t) ^ n)) *
      gaussianMass t₀ (L : Set (Euclidean n)) := by
  rcases le_total t t₀ with h | h
  · apply (gaussianMass_scalar_ratio_le L ht ht₀ h).trans
    gcongr
    exact le_max_right _ _
  · have hm : gaussianMass t (L : Set (Euclidean n)) ≤ gaussianMass t₀ (L : Set (Euclidean n)) := by
      exact ENNReal.tsum_le_tsum (fun x => ENNReal.ofReal_le_ofReal (gaussianWeight_antitone ht₀.le h x))
    apply hm.trans
    have hc : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (max 1 ((t₀ / t) ^ n)) := by
      simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (le_max_left (1 : ℝ) ((t₀ / t) ^ n))
    calc
      _ = 1 * gaussianMass t₀ (L : Set (Euclidean n)) := (one_mul _).symm
      _ ≤ _ := by gcongr

omit [DiscreteTopology L] [IsZLattice ℝ L] in
theorem gaussianMass_scalar_image (t a : ℝ) (ha : a ≠ 0) :
    gaussianMass t (latticeImage (euclideanScalarShape n a ha).toContinuousLinearMap L : Set (Euclidean n)) =
      gaussianMass (t * a) (L : Set (Euclidean n)) := by
  unfold gaussianMass
  change (∑' x : latticeImage (euclideanScalarShape n a ha).toContinuousLinearMap L,
      ENNReal.ofReal (gaussianWeight t (x : Euclidean n))) =
    ∑' x : L, ENNReal.ofReal (gaussianWeight (t * a) (x : Euclidean n))
  rw [← (latticeImageEquiv (euclideanScalarShape n a ha) L).toEquiv.tsum_eq]
  apply tsum_congr
  intro x
  congr 1
  simp only [LinearEquiv.coe_toEquiv, latticeImageEquiv_apply, euclideanScalarShape_apply,
    gaussianWeight, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  congr 1
  ring

section Ideals
open NumberField
variable (K : Type*) [Field K] [NumberField K] {d r : ℕ}

/-- Integral vectors whose coordinates lie in a fixed ideal. -/
def idealPowerModule (I : Ideal (𝓞 K)) (r : ℕ) : Submodule ℤ (Fin r → 𝓞 K) :=
  Submodule.pi Set.univ (fun _ => I.restrictScalars ℤ)

omit [NumberField K] in
@[simp] theorem mem_idealPowerModule (I : Ideal (𝓞 K)) (r : ℕ) (v : Fin r → 𝓞 K) :
    v ∈ idealPowerModule K I r ↔ ∀ i, v i ∈ I := by
  simp [idealPowerModule]

def idealEuclideanLattice (b : Basis (Fin d) ℤ (𝓞 K)) (I : Ideal (𝓞 K)) (r : ℕ) :
    Submodule ℤ (Euclidean (r * d)) :=
  (idealPowerModule K I r).map (canonicalEuclideanEmbedding K b r)

theorem idealEuclideanLattice_le (b : Basis (Fin d) ℤ (𝓞 K)) (I : Ideal (𝓞 K)) (r : ℕ) :
    idealEuclideanLattice K b I r ≤ canonicalEuclideanLattice K b r := by
  rintro x ⟨v, _, rfl⟩
  exact ⟨v, rfl⟩

instance idealEuclideanLattice_discrete (b : Basis (Fin d) ℤ (𝓞 K)) (I : Ideal (𝓞 K)) (r : ℕ) :
    DiscreteTopology (idealEuclideanLattice K b I r) := by
  let f : idealEuclideanLattice K b I r → canonicalEuclideanLattice K b r :=
    fun x => ⟨x, idealEuclideanLattice_le K b I r x.2⟩
  apply DiscreteTopology.of_continuous_injective (f := f)
  · exact continuous_subtype_val.subtype_mk _
  · intro x y h
    exact Subtype.ext (congrArg
      (fun z : canonicalEuclideanLattice K b r => (z : Euclidean (r * d))) h)

theorem idealEuclideanLattice_full (b : Basis (Fin d) ℤ (𝓞 K)) (I : Ideal (𝓞 K)) (r : ℕ)
    (q : ℕ) [NeZero q] (hqI : (q : 𝓞 K) ∈ I) : IsZLattice ℝ (idealEuclideanLattice K b I r) := by
  constructor
  apply top_unique
  rw [← IsZLattice.span_top (K := ℝ) (L := canonicalEuclideanLattice K b r)]
  apply Submodule.span_le.mpr
  rintro x ⟨v, rfl⟩
  have hqv : (q : ℤ) • v ∈ idealPowerModule K I r := by
    rw [mem_idealPowerModule]
    intro i
    change (q : ℤ) • v i ∈ I
    rw [zsmul_eq_mul, Int.cast_natCast]
    exact I.mul_mem_right (v i) hqI
  have hscaled : (q : ℝ) • canonicalEuclideanEmbedding K b r v ∈
      Submodule.span ℝ (idealEuclideanLattice K b I r : Set (Euclidean (r * d))) := by
    apply Submodule.subset_span
    refine ⟨(q : ℤ) • v, hqv, ?_⟩
    rw [map_smul]
    simpa only [Int.cast_natCast] using
      (Int.cast_smul_eq_zsmul ℝ (q : ℤ) (canonicalEuclideanEmbedding K b r v)).symm
  have hq : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hs := (Submodule.span ℝ (idealEuclideanLattice K b I r : Set (Euclidean (r * d)))).smul_mem
    (q : ℝ)⁻¹ hscaled
  change canonicalEuclideanEmbedding K b r v ∈
    Submodule.span ℝ (idealEuclideanLattice K b I r : Set (Euclidean (r * d)))
  simpa only [smul_smul, inv_mul_cancel₀ hq, one_smul] using hs

theorem idealEuclideanLattice_norm_lower (b : Basis (Fin d) ℤ (𝓞 K)) (I : Ideal (𝓞 K))
    (r : ℕ) (x : idealEuclideanLattice K b I r) (hx : x ≠ 0) :
    Real.sqrt d * (Ideal.absNorm I : ℝ) ^ (1 / (d : ℝ)) ≤ ‖(x : Euclidean (r * d))‖ := by
  obtain ⟨v, hv, he⟩ := x.2
  have hv0 : v ≠ 0 := by
    intro h
    apply hx
    apply Subtype.ext
    change (x : Euclidean (r * d)) = 0
    simpa only [h, map_zero] using he.symm
  rw [← he]
  change _ ≤ ‖canonicalOrthonormalCoordinates K b r (canonicalPowerEmbedding K r v)‖
  rw [LinearIsometryEquiv.norm_map]
  exact ideal_power_canonical_norm_lower K b I ((mem_idealPowerModule K I r v).mp hv) hv0

theorem idealGaussianMass_explicit_separation (b : Basis (Fin d) ℤ (𝓞 K))
    (I : Ideal (𝓞 K)) (q : ℕ) [NeZero q] (hqI : (q : 𝓞 K) ∈ I)
    (m : ℕ) (hm : 1 ≤ m) {t : ℝ} (ht : 0 < t)
    (hscale : 4 * Real.sqrt ((d : ℝ) * m) ≤
      t * (Real.sqrt d * (Ideal.absNorm I : ℝ) ^ (1 / (d : ℝ)))) :
    gaussianMass t (idealEuclideanLattice K b I 1 : Set (Euclidean (1 * d))) ≤
      ENNReal.ofReal (1 + 2 * (2 : ℝ) ^ (-(3 * (d : ℝ) * m))) := by
  let : IsZLattice ℝ (idealEuclideanLattice K b I 1) := idealEuclideanLattice_full K b I 1 q hqI
  have hd : 1 ≤ 1 * d := by simpa only [one_mul] using Nat.succ_le_of_lt (integralBasis_dimension_pos K b)
  have h := gaussianMass_explicit_separation (idealEuclideanLattice K b I 1) m hd hm ht
    (show 0 ≤ Real.sqrt d * (Ideal.absNorm I : ℝ) ^ (1 / (d : ℝ)) by positivity)
    (idealEuclideanLattice_norm_lower K b I 1) (by simpa only [one_mul] using hscale)
  simpa only [one_mul] using h

/-- Strong-error ideal theta estimate at every positive inverse width. -/
theorem idealGaussianMass_all_widths (b : Basis (Fin d) ℤ (𝓞 K))
    (I : Ideal (𝓞 K)) (q : ℕ) [NeZero q] (hqI : (q : 𝓞 K) ∈ I)
    (m : ℕ) (hm : 1 ≤ m) {t : ℝ} (ht : 0 < t) :
    gaussianMass t (idealEuclideanLattice K b I 1 : Set (Euclidean (1 * d))) ≤
      ENNReal.ofReal (max 1 ((4 * Real.sqrt m /
        (t * (Ideal.absNorm I : ℝ) ^ (1 / (d : ℝ)))) ^ d) *
          (1 + 2 * (2 : ℝ) ^ (-(3 * (d : ℝ) * m)))) := by
  let : IsZLattice ℝ (idealEuclideanLattice K b I 1) := idealEuclideanLattice_full K b I 1 q hqI
  have hI : I ≠ ⊥ := by
    intro h
    rw [h] at hqI
    exact (Nat.cast_ne_zero.mpr (NeZero.ne q) : (q : 𝓞 K) ≠ 0) hqI
  have hN : (0 : ℝ) < Ideal.absNorm I := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hroot : 0 < (Ideal.absNorm I : ℝ) ^ (1 / (d : ℝ)) := Real.rpow_pos_of_pos hN _
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  let t₀ := 4 * Real.sqrt m / (Ideal.absNorm I : ℝ) ^ (1 / (d : ℝ))
  have ht₀ : 0 < t₀ := by dsimp [t₀]; positivity
  have hscale : 4 * Real.sqrt ((d : ℝ) * m) ≤
      t₀ * (Real.sqrt d * (Ideal.absNorm I : ℝ) ^ (1 / (d : ℝ))) := by
    rw [Real.sqrt_mul (Nat.cast_nonneg d)]
    dsimp [t₀]
    apply le_of_eq
    field_simp
  have hsmall := idealGaussianMass_explicit_separation K b I q hqI m hm ht₀ hscale
  have hinter := gaussianMass_width_interpolation (idealEuclideanLattice K b I 1) ht ht₀
  simp only [one_mul] at hinter
  have hratio : t₀ / t = 4 * Real.sqrt m /
      (t * (Ideal.absNorm I : ℝ) ^ (1 / (d : ℝ))) := by
    dsimp [t₀]
    ring
  rw [hratio] at hinter
  apply hinter.trans
  rw [ENNReal.ofReal_mul (by positivity)]
  gcongr

end Ideals

end SISToKSIS

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Module NumberField GeometricGaussianLHL
open scoped ENNReal Classical
namespace SISToKSIS
variable (K : Type*) [Field K] [NumberField K] {d : ℕ}

def idealCoordinateEquiv (I : Ideal (𝓞 K)) (r : ℕ) :
    (Fin r → I) ≃ idealPowerModule K I r where
  toFun v := ⟨fun i => (v i : 𝓞 K), (mem_idealPowerModule K I r _).mpr (fun i => (v i).2)⟩
  invFun v i := ⟨v.1 i, (mem_idealPowerModule K I r _).mp v.2 i⟩
  left_inv v := by rfl
  right_inv v := by rfl

def idealEuclideanLatticeEquiv (b : Basis (Fin d) ℤ (𝓞 K)) (I : Ideal (𝓞 K)) (r : ℕ) :
    (Fin r → I) ≃ idealEuclideanLattice K b I r :=
  (idealCoordinateEquiv K I r).trans
    (Submodule.equivMapOfInjective (canonicalEuclideanEmbedding K b r)
      (canonicalEuclideanEmbedding_injective K b r) (idealPowerModule K I r)).toEquiv

@[simp] theorem idealEuclideanLatticeEquiv_apply (b : Basis (Fin d) ℤ (𝓞 K))
    (I : Ideal (𝓞 K)) (r : ℕ) (v : Fin r → I) :
    (idealEuclideanLatticeEquiv K b I r v : Euclidean (r * d)) =
      canonicalEuclideanEmbedding K b r (fun i => (v i : 𝓞 K)) := rfl

theorem gaussianWeight_canonical_product (b : Basis (Fin d) ℤ (𝓞 K))
    (r : ℕ) (t : ℝ) (v : Fin r → 𝓞 K) :
    gaussianWeight t (canonicalEuclideanEmbedding K b r v) =
      ∏ i, gaussianWeight t (canonicalIntegerEmbedding K (v i)) := by
  change gaussianWeight t (canonicalOrthonormalCoordinates K b r (canonicalPowerEmbedding K r v)) = _
  simp only [gaussianWeight, LinearIsometryEquiv.norm_map, PiLp.norm_sq_eq_of_L2,
    canonicalPowerEmbedding_apply, Finset.mul_sum, Real.exp_sum]

theorem idealGaussianMass_coordinate_product (b : Basis (Fin d) ℤ (𝓞 K))
    (I : Ideal (𝓞 K)) (r : ℕ) (t : ℝ) :
    gaussianMass t (idealEuclideanLattice K b I r : Set (Euclidean (r * d))) =
      (∑' x : I, ENNReal.ofReal (gaussianWeight t (canonicalIntegerEmbedding K (x : 𝓞 K)))) ^ r := by
  change (∑' x : idealEuclideanLattice K b I r,
    ENNReal.ofReal (gaussianWeight t (x : Euclidean (r * d)))) = _
  rw [← (idealEuclideanLatticeEquiv K b I r).tsum_eq]
  simp only [idealEuclideanLatticeEquiv_apply, gaussianWeight_canonical_product,
    ENNReal.ofReal_prod_of_nonneg (fun _ _ => (gaussianWeight_pos _ _).le)]
  rw [tsum_finite_product r (fun _ => fun x : I =>
    ENNReal.ofReal (gaussianWeight t (canonicalIntegerEmbedding K (x : 𝓞 K))))]
  simp

theorem idealGaussianMass_power (b : Basis (Fin d) ℤ (𝓞 K))
    (I : Ideal (𝓞 K)) (r : ℕ) (t : ℝ) :
    gaussianMass t (idealEuclideanLattice K b I r : Set (Euclidean (r * d))) =
      gaussianMass t (idealEuclideanLattice K b I 1 : Set (Euclidean (1 * d))) ^ r := by
  rw [idealGaussianMass_coordinate_product, idealGaussianMass_coordinate_product, pow_one]

theorem idealGaussianMass_all_widths_power (b : Basis (Fin d) ℤ (𝓞 K))
    (I : Ideal (𝓞 K)) (q : ℕ) [NeZero q] (hqI : (q : 𝓞 K) ∈ I)
    (m : ℕ) (hm : 1 ≤ m) (r : ℕ) {t : ℝ} (ht : 0 < t) :
    gaussianMass t (idealEuclideanLattice K b I r : Set (Euclidean (r * d))) ≤
      ENNReal.ofReal ((max 1 ((4 * Real.sqrt m / (t * (Ideal.absNorm I : ℝ) ^ (1 / (d : ℝ)))) ^ d) *
        (1 + 2 * (2 : ℝ) ^ (-(3 * (d : ℝ) * m)))) ^ r) := by
  rw [idealGaussianMass_power, ENNReal.ofReal_pow (by positivity)]
  exact pow_le_pow_left' (idealGaussianMass_all_widths K b I q hqI m hm ht) r

end SISToKSIS
