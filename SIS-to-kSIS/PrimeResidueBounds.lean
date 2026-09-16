import «SIS-to-kSIS».GaussianFactorization
import «SIS-to-kSIS».IdealGeometry
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.RingTheory.Ideal.Quotient.Basic

/-!
# Coordinate projections for a prime residue field

A basis of the row span selects at most as many coordinates as there are
columns. Equality on these coordinates determines every vector in the column
image. This argument is over a field and does not assume a common invertible
minor over a product of residue fields.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Module NumberField GeometricGaussianLHL
open scoped Matrix

namespace SISToKSIS

/-- A coordinate projection of size at most the column count is injective on
the column image over a field, including for a rank-deficient matrix. -/
theorem exists_injective_column_projection {F : Type*} [Field F] {m k : ℕ}
    (U : Matrix (Fin m) (Fin k) F) :
    ∃ r ≤ k, ∃ a : Fin r → Fin m, Function.Injective a ∧
      ∀ c d : Fin k → F,
        (∀ j, U.mulVec c (a j) = U.mulVec d (a j)) → U.mulVec c = U.mulVec d := by
  classical
  obtain ⟨ι, a, ha, hspan, hli⟩ := exists_linearIndependent' F U
  let : Fintype ι := Fintype.ofInjective a ha
  let e := Fintype.equivFin ι
  refine ⟨Fintype.card ι, ?_, a ∘ e.symm, ha.comp e.symm.injective, ?_⟩
  · simpa only [Module.finrank_pi, Module.finrank_self, Fintype.card_fin, mul_one]
      using hli.fintype_card_le_finrank
  · intro c d hcd
    have hselected (i : ι) : (U (a i)) ⬝ᵥ c = (U (a i)) ⬝ᵥ d := by
      have h := hcd (e i)
      simpa only [Function.comp_apply, Equiv.symm_apply_apply, Matrix.mulVec] using h
    have hrow (w : Fin k → F) (hw : w ∈ Submodule.span F (Set.range (U ∘ a))) :
        w ⬝ᵥ c = w ⬝ᵥ d := by
      induction hw using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨i, rfl⟩ := hw
        exact hselected i
      | zero => simp
      | add x y hx hy hxc hyc => simp only [add_dotProduct, hxc, hyc]
      | smul t x hx hxc => simp only [smul_dotProduct, hxc]
    funext i
    apply hrow
    rw [hspan]
    exact Submodule.subset_span ⟨i, rfl⟩

/-- Integral vectors whose residues lie in the column image. -/
def residueColumnEvent {R F : Type*} [CommRing R] [Field F] {m k : ℕ}
    (modQ : R →+* F) (U : Matrix (Fin m) (Fin k) F) : Set (Fin m → R) :=
  {x | ∃ c, U.mulVec c = fun i => modQ (x i)}

theorem residueColumnEvent_zero {R F : Type*} [CommRing R] [Field F] {m k : ℕ}
    (modQ : R →+* F) (U : Matrix (Fin m) (Fin k) F) :
    0 ∈ residueColumnEvent modQ U := by
  exact ⟨0, by ext i; simp⟩

def residueColumnModule {R F : Type*} [CommRing R] [Field F] {m k : ℕ}
    (modQ : R →+* F) (U : Matrix (Fin m) (Fin k) F) : Submodule ℤ (Fin m → R) :=
  ((LinearMap.range U.mulVecLin).restrictScalars ℤ).comap (quotientVectorMap modQ)

theorem mem_residueColumnModule {R F : Type*} [CommRing R] [Field F] {m k : ℕ}
    (modQ : R →+* F) (U : Matrix (Fin m) (Fin k) F) (x : Fin m → R) :
    x ∈ residueColumnModule modQ U ↔ x ∈ residueColumnEvent modQ U := Iff.rfl

section ColumnLattice

variable (K : Type*) [Field K] [NumberField K] {d m k : ℕ} {F : Type*} [Field F]

def residueColumnLattice (b : Basis (Fin d) ℤ (𝓞 K))
    (modQ : 𝓞 K →+* F) (U : Matrix (Fin m) (Fin k) F) : Submodule ℤ (Euclidean (m * d)) :=
  (residueColumnModule modQ U).map (canonicalEuclideanEmbedding K b m)

theorem residueColumnLattice_le (b : Basis (Fin d) ℤ (𝓞 K))
    (modQ : 𝓞 K →+* F) (U : Matrix (Fin m) (Fin k) F) :
    residueColumnLattice K b modQ U ≤ canonicalEuclideanLattice K b m := by
  rintro x ⟨v, _, rfl⟩
  exact ⟨v, rfl⟩

instance residueColumnLattice_discrete (b : Basis (Fin d) ℤ (𝓞 K))
    (modQ : 𝓞 K →+* F) (U : Matrix (Fin m) (Fin k) F) :
    DiscreteTopology (residueColumnLattice K b modQ U) := by
  let f : residueColumnLattice K b modQ U → canonicalEuclideanLattice K b m :=
    fun x => ⟨x, residueColumnLattice_le K b modQ U x.2⟩
  have hf : Continuous f := continuous_subtype_val.subtype_mk _
  have hi : Function.Injective f := fun x y h => Subtype.ext
    (congrArg (fun z : canonicalEuclideanLattice K b m => (z : Euclidean (m * d))) h)
  exact DiscreteTopology.of_continuous_injective hf hi

theorem residueColumnLattice_full (b : Basis (Fin d) ℤ (𝓞 K))
    (modQ : 𝓞 K →+* F) (U : Matrix (Fin m) (Fin k) F)
    (q : ℤ) (hq : q ≠ 0) (hchar : (q : F) = 0) :
    IsZLattice ℝ (residueColumnLattice K b modQ U) := by
  constructor
  apply top_unique
  rw [← IsZLattice.span_top (K := ℝ) (L := canonicalEuclideanLattice K b m)]
  apply Submodule.span_le.mpr
  rintro x ⟨v, rfl⟩
  have hqv : q • v ∈ residueColumnModule modQ U := by
    rw [mem_residueColumnModule]
    refine ⟨0, ?_⟩
    ext i
    simp [Pi.smul_apply, zsmul_eq_mul, hchar]
  have hmul : (q : ℝ) • canonicalEuclideanEmbedding K b m v ∈
      Submodule.span ℝ (residueColumnLattice K b modQ U : Set (Euclidean (m * d))) := by
    apply Submodule.subset_span
    refine ⟨q • v, hqv, ?_⟩
    simp only [LinearMap.map_smul, Int.cast_smul_eq_zsmul]
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  have hs := (Submodule.span ℝ (residueColumnLattice K b modQ U : Set (Euclidean (m * d)))).smul_mem
    (q : ℝ)⁻¹ hmul
  change canonicalEuclideanEmbedding K b m v ∈
    Submodule.span ℝ (residueColumnLattice K b modQ U : Set (Euclidean (m * d)))
  simpa only [smul_smul, inv_mul_cancel₀ hqR, one_smul] using hs

/-- The integral residue-image vectors and their actual Euclidean lattice are
in bijection; the Gaussian mass can be transported without a counting factor. -/
def residueColumnLatticeEquiv (b : Basis (Fin d) ℤ (𝓞 K))
    (modQ : 𝓞 K →+* F) (U : Matrix (Fin m) (Fin k) F) :
    residueColumnEvent modQ U ≃ residueColumnLattice K b modQ U :=
  Equiv.ofBijective
    (fun x => ⟨canonicalEuclideanEmbedding K b m x,
      ⟨x, (mem_residueColumnModule modQ U x).mpr x.2, rfl⟩⟩)
    ⟨by
      intro x y h
      apply Subtype.ext
      exact canonicalEuclideanEmbedding_injective K b m (congrArg Subtype.val h), by
      intro z
      obtain ⟨x, hx, hz⟩ := z.2
      exact ⟨⟨x, (mem_residueColumnModule modQ U x).mp hx⟩, Subtype.ext hz⟩⟩

theorem residueColumnLatticeEquiv_coe (b : Basis (Fin d) ℤ (𝓞 K))
    (modQ : 𝓞 K →+* F) (U : Matrix (Fin m) (Fin k) F) (x : residueColumnEvent modQ U) :
    (residueColumnLatticeEquiv K b modQ U x : Euclidean (m * d)) =
      canonicalEuclideanEmbedding K b m x := rfl

end ColumnLattice

/-- On any set with unique residue representatives, the selected integral
coordinates give an injective map into `R^r`. -/
theorem residue_column_projection_injective {R F : Type*} [CommRing R] [Field F]
    {m k r : ℕ} (modQ : R →+* F) (U : Matrix (Fin m) (Fin k) F)
    (a : Fin r → Fin m)
    (ha : ∀ c d : Fin k → F,
      (∀ j, U.mulVec c (a j) = U.mulVec d (a j)) → U.mulVec c = U.mulVec d)
    (C : Set (Fin m → R))
    (hC : ∀ x ∈ C, ∀ y ∈ C, (∀ i, modQ (x i) = modQ (y i)) → x = y) :
    Function.Injective (fun x : {x // x ∈ C ∩ residueColumnEvent modQ U} =>
      fun j => x.1 (a j)) := by
  intro x y hxy
  obtain ⟨c, hc⟩ := x.2.2
  obtain ⟨d, hd⟩ := y.2.2
  have hcd : U.mulVec c = U.mulVec d := ha c d (fun j => by
    rw [hc, hd]
    exact congrArg modQ (congrFun hxy j))
  apply Subtype.ext
  apply hC x x.2.1 y y.2.1
  intro i
  simpa only [hc, hd] using congrFun hcd i

section GaussianProjection

variable (K : Type*) [Field K] [NumberField K] {d m r : ℕ}

local instance residueAmbientInner : InnerProductSpace ℝ (CanonicalAmbient K) := inferInstance
local instance residueSpaceInner : InnerProductSpace ℝ (canonicalSpace K) := inferInstance
local instance residuePowerInner (n : ℕ) : InnerProductSpace ℝ (CanonicalPower K n) := inferInstance
local instance residueIdealField (I : Ideal (𝓞 K)) [I.IsMaximal] : Field ((𝓞 K) ⧸ I) :=
  Ideal.Quotient.field I

theorem canonical_coordinate_projection_norm (a : Fin r → Fin m) (ha : Function.Injective a)
    (x : Fin m → 𝓞 K) :
    ‖canonicalPowerEmbedding K r (x ∘ a)‖ ≤ ‖canonicalPowerEmbedding K m x‖ := by
  classical
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [PiLp.norm_sq_eq_of_L2, canonicalPowerEmbedding_apply, Function.comp_apply]
  calc
    _ = ∑ i ∈ Finset.univ.image a, ‖canonicalIntegerEmbedding K (x i)‖ ^ 2 := by
      rw [Finset.sum_image]
      exact fun _ _ _ _ h => ha h
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun _ _ _ => sq_nonneg _)

theorem numberFieldGaussianWeight_projection (a : Fin r → Fin m) (ha : Function.Injective a)
    (s : ℝ) (x : Fin m → 𝓞 K) :
    numberFieldGaussianWeight K m s x ≤ numberFieldGaussianWeight K r s (x ∘ a) := by
  have hsq := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
    (canonical_coordinate_projection_norm K a ha x)
  unfold numberFieldGaussianWeight gaussianWeight
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonpos_left hsq
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr Real.pi_pos.le) (sq_nonneg _))

theorem ellipsoidWeight_coordinate_projection (b : Basis (Fin d) ℤ (𝓞 K))
    (a : Fin r → Fin m) (ha : Function.Injective a)
    (S : Euclidean (m * d) ≃L[ℝ] Euclidean (m * d))
    {σ : ℝ} (hσ : 0 < σ) (hS : ‖S.toContinuousLinearMap‖ ≤ σ) (x : Fin m → 𝓞 K) :
    gaussianWeight 1 (S.symm (canonicalEuclideanEmbedding K b m x)) ≤
      numberFieldGaussianWeight K r σ (x ∘ a) := by
  apply (gaussianWeight_inverse_le S hσ hS (canonicalEuclideanEmbedding K b m x)).trans
  have he : gaussianWeight (1 / σ) (canonicalEuclideanEmbedding K b m x) =
      numberFieldGaussianWeight K m σ x := by
    change gaussianWeight (1 / σ) (canonicalOrthonormalCoordinates K b m
      (canonicalPowerEmbedding K m x)) = _
    simp only [gaussianWeight, LinearIsometryEquiv.norm_map, numberFieldGaussianWeight]
  rw [he]
  exact numberFieldGaussianWeight_projection K a ha σ x

/-- The Gaussian mass on any set admitting an injective coordinate projection
is bounded by the lower-dimensional spherical partition sum. -/
theorem ellipsoidMass_le_projected_partition (b : Basis (Fin d) ℤ (𝓞 K))
    (a : Fin r → Fin m) (ha : Function.Injective a)
    (S : Euclidean (m * d) ≃L[ℝ] Euclidean (m * d))
    {σ : ℝ} (hσ : 0 < σ) (hS : ‖S.toContinuousLinearMap‖ ≤ σ)
    (C : Set (Fin m → 𝓞 K))
    (hC : Function.Injective (fun x : C => x.1 ∘ a)) :
    (∑' x : C, gaussianWeight 1 (S.symm (canonicalEuclideanEmbedding K b m x))) ≤
      numberFieldGaussianPartition K r σ := by
  have hs : Summable (fun x : C => gaussianWeight 1
      (S.symm (canonicalEuclideanEmbedding K b m x))) :=
    (summable_numberFieldEllipsoidWeight K b m S).comp_injective Subtype.val_injective
  have hp := (summable_numberFieldGaussianWeight K b r σ hσ.ne').comp_injective hC
  calc
    _ ≤ ∑' x : C, numberFieldGaussianWeight K r σ (x.1 ∘ a) :=
      hs.tsum_le_tsum (fun x => ellipsoidWeight_coordinate_projection K b a ha S hσ hS x) hp
    _ ≤ _ := hp.tsum_le_tsum_of_inj
      (fun x : C => x.1 ∘ a) hC (fun x _ => (numberFieldGaussianWeight_pos K r σ x).le)
      (fun _ => le_rfl) (summable_numberFieldGaussianWeight K b r σ hσ.ne')

theorem ringGaussianPartition_ge_one (b : Basis (Fin d) ℤ (𝓞 K))
    (s : ℝ) (hs : s ≠ 0) : 1 ≤ ringGaussianPartition K s := by
  have h := (summable_ringGaussianWeight K b s hs).le_tsum 0
    (fun _ _ => (ringGaussianWeight_pos K s _).le)
  simpa only [ringGaussianWeight, ringGaussianPartition, map_zero, gaussianWeight, norm_zero, zero_pow (by omega : 2 ≠ 0),
    mul_zero, Real.exp_zero] using h

theorem numberFieldGaussianPartition_dimension_mono (b : Basis (Fin d) ℤ (𝓞 K))
    (s : ℝ) (hs : s ≠ 0) (hrm : r ≤ m) :
    numberFieldGaussianPartition K r s ≤ numberFieldGaussianPartition K m s := by
  rw [numberFieldGaussianPartition_product K b s hs, numberFieldGaussianPartition_product K b s hs]
  exact pow_le_pow_right₀ (ringGaussianPartition_ge_one K b s hs) hrm

/-- The small-region estimate only needs a prime residue field, as in its
application to the independence bound. -/
theorem prime_residue_small_region_mass {F : Type*} [Field F] {k : ℕ}
    (b : Basis (Fin d) ℤ (𝓞 K)) (modQ : 𝓞 K →+* F)
    (U : Matrix (Fin m) (Fin k) F)
    (S : Euclidean (m * d) ≃L[ℝ] Euclidean (m * d))
    {σ : ℝ} (hσ : 0 < σ) (hS : ‖S.toContinuousLinearMap‖ ≤ σ)
    (C : Set (Fin m → 𝓞 K))
    (hC : ∀ x ∈ C, ∀ y ∈ C, (∀ i, modQ (x i) = modQ (y i)) → x = y) :
    (∑' x : {x // x ∈ C ∩ residueColumnEvent modQ U},
      gaussianWeight 1 (S.symm (canonicalEuclideanEmbedding K b m x))) ≤
      numberFieldGaussianPartition K k σ := by
  obtain ⟨r, hr, a, ha, hp⟩ := exists_injective_column_projection U
  exact (ellipsoidMass_le_projected_partition K b a ha S hσ hS _
    (residue_column_projection_injective modQ U a hp C hC)).trans
    (numberFieldGaussianPartition_dimension_mono K b σ hσ.ne' hr)

theorem prime_ideal_open_ball_mass {k : ℕ}
    (b : Basis (Fin d) ℤ (𝓞 K)) (I : Ideal (𝓞 K)) [I.IsMaximal]
    (U : Matrix (Fin m) (Fin k) ((𝓞 K) ⧸ I))
    (S : Euclidean (m * d) ≃L[ℝ] Euclidean (m * d))
    {σ R : ℝ} (hσ : 0 < σ) (hS : ‖S.toContinuousLinearMap‖ ≤ σ)
    (hR : 2 * R ≤ Real.sqrt d * (Ideal.absNorm I : ℝ) ^ (1 / (d : ℝ))) :
    (∑' x : {x // x ∈ {x | ‖canonicalPowerEmbedding K m x‖ < R} ∩
      residueColumnEvent (Ideal.Quotient.mk I) U},
        gaussianWeight 1 (S.symm (canonicalEuclideanEmbedding K b m x))) ≤
      numberFieldGaussianPartition K k σ := by
  apply prime_residue_small_region_mass K b (Ideal.Quotient.mk I) U S hσ hS
  intro x hx y hy hxy
  exact ideal_open_ball_residue_injective K b I hR x y hx hy hxy

end GaussianProjection

section LatticeTail

variable {n : ℕ} (L : Submodule ℤ (Euclidean n))
  [DiscreteTopology L] [IsZLattice ℝ L]

theorem latticeGaussian_standardized_norm_moment
    (S : Euclidean n ≃L[ℝ] Euclidean n) :
    (∑' x : L, latticeGaussian L S x *
      ENNReal.ofReal (Real.exp (Real.pi * ‖S.symm (x : Euclidean n)‖ ^ 2 / 2))) ≤
        ENNReal.ofReal (Real.sqrt 2 ^ n) := by
  rw [← (fullLatticeCoordinateEquiv L).toEquiv.tsum_eq]
  simp only [LinearEquiv.coe_toEquiv, latticeGaussian_apply,
    latticeGaussianWeight_coordinates, latticeGaussianPartition_eq,
    ← latticeCoefficientShape_symm_integer, ← ellipsoidalGaussian_apply]
  exact ellipsoidalGaussian_standardized_norm_moment (latticeCoefficientShape L S)

/-- A non-strict tail is used so that the complementary region is an open
ball, where the residue representatives are unambiguously distinct. -/
theorem latticeGaussian_norm_tail (S : Euclidean n ≃L[ℝ] Euclidean n)
    {σ u : ℝ} (hσ : 0 < σ) (hu : 0 ≤ u) (hS : ‖S.toContinuousLinearMap‖ ≤ σ) :
    (latticeGaussian L S).toOuterMeasure {x : L | σ * u ≤ ‖(x : Euclidean n)‖} ≤
      ENNReal.ofReal (Real.sqrt 2 ^ n * Real.exp (-Real.pi * u ^ 2 / 2)) := by
  have hsub : {x : L | σ * u ≤ ‖(x : Euclidean n)‖} ⊆
      {x : L | Real.pi * u ^ 2 / 2 ≤ Real.pi * ‖S.symm (x : Euclidean n)‖ ^ 2 / 2} := by
    intro x hx
    have hb : ‖(x : Euclidean n)‖ ≤ σ * ‖S.symm (x : Euclidean n)‖ := by
      calc
        _ = ‖S (S.symm (x : Euclidean n))‖ := by rw [S.apply_symm_apply]
        _ ≤ ‖S.toContinuousLinearMap‖ * ‖S.symm (x : Euclidean n)‖ :=
          S.toContinuousLinearMap.le_opNorm _
        _ ≤ _ := mul_le_mul_of_nonneg_right hS (norm_nonneg _)
    have hu' : u ≤ ‖S.symm (x : Euclidean n)‖ := (mul_le_mul_iff_right₀ hσ).mp (hx.trans hb)
    have hsq := (sq_le_sq₀ hu (norm_nonneg _)).mpr hu'
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq Real.pi_pos.le) (by norm_num)
  apply ((latticeGaussian L S).toOuterMeasure.mono hsub).trans
  change (latticeGaussian L S).toOuterMeasure
    {x : L | Real.pi * u ^ 2 / 2 ≤ Real.pi * ‖S.symm (x : Euclidean n)‖ ^ 2 / 2} ≤ _
  have h := pmf_exp_tail_le (latticeGaussian L S)
    (fun x : L => Real.pi * ‖S.symm (x : Euclidean n)‖ ^ 2 / 2)
    (Real.pi * u ^ 2 / 2) (Real.sqrt 2 ^ n) (latticeGaussian_standardized_norm_moment L S)
  rw [PMF.toMeasure_apply_eq_toOuterMeasure] at h
  convert h using 1
  rw [show -Real.pi * u ^ 2 / 2 = -(Real.pi * u ^ 2 / 2) by ring]

end LatticeTail

/-- The full hint vector has `m + k` ring coordinates, while the paper's
width ceiling uses `sqrt(m)`. The dimension slack `64*k ≤ m` suffices for
an exponentially small tail at the resulting separation radius. -/
theorem residue_tail_budget (d m k : ℕ) (hkm : 64 * k ≤ m) :
    Real.sqrt 2 ^ ((m + k) * d) * Real.exp (-Real.pi * (m : ℝ) * d / 8) ≤
      Real.exp (-((m : ℝ) * d) / 32) := by
  have hlog : Real.log 2 ≤ 7 / 10 := by linarith [Real.log_two_lt_d9]
  have hpi : (314 : ℝ) / 100 ≤ Real.pi := by linarith [Real.pi_gt_d2]
  have hkmR : (64 : ℝ) * k ≤ m := by exact_mod_cast hkm
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hlogmul := mul_le_mul_of_nonneg_right hlog (show 0 ≤ ((m : ℝ) + k) / 2 by positivity)
  have hpimul := mul_le_mul_of_nonneg_right hpi (show 0 ≤ (m : ℝ) / 8 by positivity)
  have hc : Real.log 2 * (((m : ℝ) + k) / 2) - Real.pi * ((m : ℝ) / 8) ≤ -(m : ℝ) / 32 := by
    nlinarith
  have h := mul_le_mul_of_nonneg_right hc hd
  rw [sqrt_two_pow_eq_rpow, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  push_cast
  nlinarith only [h]

end SISToKSIS
