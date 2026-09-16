import «SIS-to-kSIS».PrimeResidueBounds
import «SIS-to-kSIS».GaussianConditioning

/-!
# Total Gaussian mass of a prime-residue column image

The small-ball projection estimate and the lattice Gaussian tail bound are
combined on the actual full residue-image lattice, with an explicit error.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Module NumberField GeometricGaussianLHL MeasureTheory

namespace SISToKSIS

section LatticeMass

variable {n : ℕ} (L : Submodule ℤ (Euclidean n))
  [DiscreteTopology L] [IsZLattice ℝ L]

theorem latticeGaussian_event_mass [MeasurableSpace L] [MeasurableSingletonClass L]
    (S : Euclidean n ≃L[ℝ] Euclidean n) (E : Set L) :
    (latticeGaussian L S).toMeasure.real E * latticeGaussianPartition L S =
      ∑' x : E, latticeGaussianWeight L S x := by
  rw [pmf_measureReal_eq_tsum, ← tsum_subtype E (fun x => (latticeGaussian L S x).toReal)]
  simp_rw [latticeGaussian_apply, ENNReal.toReal_ofReal (div_nonneg
    (latticeGaussianWeight_pos L S _).le (latticeGaussianPartition_pos L S).le)]
  rw [tsum_div_const, div_mul_cancel₀ _ (latticeGaussianPartition_pos L S).ne']

theorem latticeGaussianPartition_le_of_ball_mass
    (S : Euclidean n ≃L[ℝ] Euclidean n) {R B δ : ℝ} (hδ : 0 ≤ δ) (hδone : δ < 1)
    (hsmall : (∑' x : {x : L // ‖(x : Euclidean n)‖ < R}, latticeGaussianWeight L S x) ≤ B)
    (htail : (latticeGaussian L S).toOuterMeasure {x : L | R ≤ ‖(x : Euclidean n)‖} ≤
      ENNReal.ofReal δ) :
    latticeGaussianPartition L S ≤ B / (1 - δ) := by
  let : MeasurableSpace L := ⊤
  let E : Set L := {x | ‖(x : Euclidean n)‖ < R}
  have he : Eᶜ = {x : L | R ≤ ‖(x : Euclidean n)‖} := by
    ext x
    change (¬‖(x : Euclidean n)‖ < R) ↔ R ≤ ‖(x : Euclidean n)‖
    exact not_lt
  have hbad : (latticeGaussian L S).toMeasure.real Eᶜ ≤ δ := by
    rw [Measure.real, PMF.toMeasure_apply_eq_toOuterMeasure, he]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top htail).trans_eq (ENNReal.toReal_ofReal hδ)
  rw [measureReal_compl (show MeasurableSet E from trivial), probReal_univ] at hbad
  have hgood : 1 - δ ≤ (latticeGaussian L S).toMeasure.real E := by linarith
  have hmass := mul_le_mul_of_nonneg_right hgood (latticeGaussianPartition_pos L S).le
  rw [latticeGaussian_event_mass L S E] at hmass
  apply (le_div_iff₀ (sub_pos.mpr hδone)).mpr
  have h := hmass.trans hsmall
  nlinarith

end LatticeMass

section ResidueMass

variable (K : Type*) [Field K] [NumberField K] {d m k : ℕ} {F : Type*} [Field F]

def residueColumnBallEquiv (b : Basis (Fin d) ℤ (𝓞 K))
    (modQ : 𝓞 K →+* F) (U : Matrix (Fin m) (Fin k) F) (R : ℝ) :
    {x // x ∈ {x | ‖canonicalPowerEmbedding K m x‖ < R} ∩ residueColumnEvent modQ U} ≃
      {z : residueColumnLattice K b modQ U // ‖(z : Euclidean (m * d))‖ < R} :=
  Equiv.ofBijective
    (fun x => ⟨residueColumnLatticeEquiv K b modQ U ⟨x, x.2.2⟩, by
      change ‖canonicalOrthonormalCoordinates K b m (canonicalPowerEmbedding K m x)‖ < R
      rw [LinearIsometryEquiv.norm_map]
      exact x.2.1⟩)
    ⟨by
      intro x y h
      apply Subtype.ext
      apply canonicalEuclideanEmbedding_injective K b m
      exact congrArg (fun z : {z : residueColumnLattice K b modQ U //
        ‖(z : Euclidean (m * d))‖ < R} => (z.1 : Euclidean (m * d))) h, by
      intro y
      obtain ⟨v, hv⟩ := (residueColumnLatticeEquiv K b modQ U).surjective y.1
      have hn : ‖canonicalPowerEmbedding K m v‖ < R := by
        have h := y.2
        rw [← hv] at h
        change ‖canonicalOrthonormalCoordinates K b m (canonicalPowerEmbedding K m v)‖ < R at h
        simpa only [LinearIsometryEquiv.norm_map] using h
      exact ⟨⟨v, hn, v.2⟩, Subtype.ext hv⟩⟩

local instance massResidueIdealField (I : Ideal (𝓞 K)) [I.IsMaximal] : Field ((𝓞 K) ⧸ I) :=
  Ideal.Quotient.field I

/-- A quantitative replacement for the prime-ideal instance of the supporting
Gaussian mass lemma. All analytical premises are explicit numerical bounds. -/
theorem prime_ideal_residue_mass (b : Basis (Fin d) ℤ (𝓞 K))
    (I : Ideal (𝓞 K)) [I.IsMaximal] (hI : Ideal.absNorm I ≠ 0)
    (U : Matrix (Fin m) (Fin k) ((𝓞 K) ⧸ I))
    (S : Euclidean (m * d) ≃L[ℝ] Euclidean (m * d))
    {σ u : ℝ} (hσ : 0 < σ) (hu : 0 ≤ u) (hS : ‖S.toContinuousLinearMap‖ ≤ σ)
    (hsep : 2 * (σ * u) ≤ Real.sqrt d * (Ideal.absNorm I : ℝ) ^ (1 / (d : ℝ)))
    (htail : Real.sqrt 2 ^ (m * d) * Real.exp (-Real.pi * u ^ 2 / 2) < 1) :
    (∑' x : residueColumnEvent (Ideal.Quotient.mk I) U,
      gaussianWeight 1 (S.symm (canonicalEuclideanEmbedding K b m x))) ≤
      numberFieldGaussianPartition K k σ /
        (1 - Real.sqrt 2 ^ (m * d) * Real.exp (-Real.pi * u ^ 2 / 2)) := by
  let L := residueColumnLattice K b (Ideal.Quotient.mk I) U
  have hq : (Ideal.absNorm I : ℤ) ≠ 0 := by exact_mod_cast hI
  have hchar : ((Ideal.absNorm I : ℤ) : (𝓞 K) ⧸ I) = 0 := by
    have h := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.absNorm_mem I)
    simpa only [map_natCast, Int.cast_natCast] using h
  let : IsZLattice ℝ L := residueColumnLattice_full K b (Ideal.Quotient.mk I) U _ hq hchar
  have hm : (∑' x : {z : L // ‖(z : Euclidean (m * d))‖ < σ * u},
      latticeGaussianWeight L S x) ≤ numberFieldGaussianPartition K k σ := by
    rw [← (residueColumnBallEquiv K b (Ideal.Quotient.mk I) U (σ * u)).tsum_eq]
    exact prime_ideal_open_ball_mass K b I U S hσ hS hsep
  have h := latticeGaussianPartition_le_of_ball_mass L S (by positivity) htail hm
    (latticeGaussian_norm_tail L S hσ hu hS)
  have he : (∑' x : residueColumnEvent (Ideal.Quotient.mk I) U,
      gaussianWeight 1 (S.symm (canonicalEuclideanEmbedding K b m x))) =
      latticeGaussianPartition L S := by
    unfold latticeGaussianPartition
    rw [← (residueColumnLatticeEquiv K b (Ideal.Quotient.mk I) U).tsum_eq]
    rfl
  rwa [he]

/-- The paper's literal width ceiling suffices in the full `m + k` ambient
dimension, with the explicit loss `1 / (1 - exp(-m*d/32))`. -/
theorem prime_ideal_residue_mass_of_width (b : Basis (Fin d) ℤ (𝓞 K))
    (I : Ideal (𝓞 K)) [I.IsMaximal] (hI : Ideal.absNorm I ≠ 0)
    (U : Matrix (Fin (m + k)) (Fin k) ((𝓞 K) ⧸ I))
    (S : Euclidean ((m + k) * d) ≃L[ℝ] Euclidean ((m + k) * d))
    (hm : 0 < m) (hkm : 64 * k ≤ m)
    {σ : ℝ} (hσ : 0 < σ) (hS : ‖S.toContinuousLinearMap‖ ≤ σ)
    (hwidth : σ * Real.sqrt m ≤ (Ideal.absNorm I : ℝ) ^ (1 / (d : ℝ))) :
    (∑' x : residueColumnEvent (Ideal.Quotient.mk I) U,
      gaussianWeight 1 (S.symm (canonicalEuclideanEmbedding K b (m + k) x))) ≤
      numberFieldGaussianPartition K k σ / (1 - Real.exp (-((m : ℝ) * d) / 32)) := by
  have hd : (0 : ℝ) < d := Nat.cast_pos.mpr (integralBasis_dimension_pos K b)
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  let u : ℝ := Real.sqrt ((m : ℝ) * d) / 2
  have hu : 0 ≤ u := by positivity
  have hsep : 2 * (σ * u) ≤ Real.sqrt d * (Ideal.absNorm I : ℝ) ^ (1 / (d : ℝ)) := by
    have h := mul_le_mul_of_nonneg_right hwidth (Real.sqrt_nonneg (d : ℝ))
    dsimp [u]
    rw [Real.sqrt_mul hmR.le]
    nlinarith only [h]
  have he : -Real.pi * u ^ 2 / 2 = -Real.pi * (m : ℝ) * d / 8 := by
    dsimp [u]
    rw [div_pow, Real.sq_sqrt (mul_nonneg hmR.le hd.le)]
    ring
  have hδ : Real.sqrt 2 ^ ((m + k) * d) * Real.exp (-Real.pi * u ^ 2 / 2) ≤
      Real.exp (-((m : ℝ) * d) / 32) := by
    rw [he]
    exact residue_tail_budget d m k hkm
  have hδone : Real.exp (-((m : ℝ) * d) / 32) < 1 := by
    apply Real.exp_lt_one_iff.mpr
    exact div_neg_of_neg_of_pos (neg_neg_of_pos (mul_pos hmR hd)) (by norm_num)
  have h := prime_ideal_residue_mass K b I hI U S hσ hu hS hsep (hδ.trans_lt hδone)
  exact h.trans (div_le_div_of_nonneg_left
    (numberFieldGaussianPartition_pos K b k σ hσ.ne').le
    (sub_pos.mpr hδone) (sub_le_sub_left hδ 1))

end ResidueMass

end SISToKSIS
