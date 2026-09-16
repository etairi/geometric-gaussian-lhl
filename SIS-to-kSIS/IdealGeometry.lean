import GeometricGaussianLHL.NumberFieldGeometry
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.Analysis.MeanInequalities

/-!
# Canonical length of nonzero ideal elements

Divisibility of the algebraic norm and the arithmetic–geometric mean inequality
give the ideal separation scale used in the prime-residue Gaussian estimate.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Module NumberField GeometricGaussianLHL

namespace SISToKSIS

variable (K : Type*) [Field K] [NumberField K] {d : ℕ}

theorem integral_norm_eq_embedding_product (x : 𝓞 K) :
    |(Algebra.norm ℤ x : ℝ)| = ∏ τ : K →+* ℂ, ‖τ (algebraMap (𝓞 K) K x)‖ := by
  classical
  have h := congrArg (fun z : ℂ => ‖z‖) (Algebra.norm_eq_prod_embeddings ℚ ℂ (x : K))
  rw [norm_prod] at h
  rw [← Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ)
    (fun f => ‖f (x : K)‖) (fun φ => ‖φ (x : K)‖)
    (fun _ => by simp [RingHom.equivRatAlgHom_apply])] at h
  rw [← Algebra.coe_norm_int] at h
  simpa only [map_intCast, Complex.norm_intCast, Int.norm_eq_abs] using h

theorem ideal_absNorm_le_integral_norm (I : Ideal (𝓞 K)) {x : 𝓞 K}
    (hx : x ∈ I) (hx₀ : x ≠ 0) : (Ideal.absNorm I : ℝ) ≤ |(Algebra.norm ℤ x : ℝ)| := by
  have h := Int.le_abs_of_dvd (Algebra.norm_ne_zero_iff.mpr hx₀)
    (Ideal.absNorm_dvd_norm_of_mem hx)
  exact_mod_cast h

theorem integral_norm_root_le_canonical_norm_sq (b : Basis (Fin d) ℤ (𝓞 K)) (x : 𝓞 K) :
    |(Algebra.norm ℤ x : ℝ)| ^ (2 / (d : ℝ)) ≤ ‖canonicalIntegerEmbedding K x‖ ^ 2 / d := by
  classical
  have hd : (0 : ℝ) < d := Nat.cast_pos.mpr (integralBasis_dimension_pos K b)
  have hcard : Fintype.card (K →+* ℂ) = d := by
    rw [Embeddings.card K ℂ, ← integralBasis_degree K b]
  have hw : ∑ _ : K →+* ℂ, (1 / (d : ℝ)) = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
    field_simp
  have h := Real.geom_mean_le_arith_mean_weighted Finset.univ
    (fun _ : K →+* ℂ => 1 / (d : ℝ))
    (fun τ => ‖τ (algebraMap (𝓞 K) K x)‖ ^ 2) (fun _ _ => by positivity) hw
    (fun _ _ => sq_nonneg _)
  rw [Real.finsetProd_rpow _ _ (fun _ _ => sq_nonneg _), Finset.prod_pow,
    ← integral_norm_eq_embedding_product K x, ← Real.rpow_natCast_mul (abs_nonneg _) 2,
    ← Finset.mul_sum] at h
  norm_num only [Nat.cast_ofNat] at h
  have he : (2 : ℝ) * (1 / (d : ℝ)) = 2 / (d : ℝ) := by ring
  rw [he] at h
  change |(Algebra.norm ℤ x : ℝ)| ^ (2 / (d : ℝ)) ≤ ‖canonicalIntegerVector K x‖ ^ 2 / d
  rw [canonicalIntegerVector_norm_sq]
  simpa only [div_eq_mul_inv, one_div, mul_comm, mul_one] using h

/-- Every nonzero element of an integral ideal has canonical length at least
`sqrt(d) * Norm(I)^(1/d)`. No choice of integral basis changes this length. -/
theorem ideal_canonical_norm_lower (b : Basis (Fin d) ℤ (𝓞 K))
    (I : Ideal (𝓞 K)) {x : 𝓞 K} (hx : x ∈ I) (hx₀ : x ≠ 0) :
    Real.sqrt d * (Ideal.absNorm I : ℝ) ^ (1 / (d : ℝ)) ≤ ‖canonicalIntegerEmbedding K x‖ := by
  have hd : (0 : ℝ) < d := Nat.cast_pos.mpr (integralBasis_dimension_pos K b)
  have hpow := Real.rpow_le_rpow (Nat.cast_nonneg (Ideal.absNorm I))
    (ideal_absNorm_le_integral_norm K I hx hx₀) (show 0 ≤ 2 / (d : ℝ) by positivity)
  have hsq := hpow.trans (integral_norm_root_le_canonical_norm_sq K b x)
  apply (sq_le_sq₀ (by positivity) (norm_nonneg _)).mp
  rw [mul_pow, Real.sq_sqrt hd.le, ← Real.rpow_mul_natCast (Nat.cast_nonneg (Ideal.absNorm I))]
  norm_num only [Nat.cast_ofNat]
  have he : 1 / (d : ℝ) * (2 : ℝ) = 2 / (d : ℝ) := by ring
  rw [he]
  have hb := (le_div_iff₀ hd).mp hsq
  nlinarith

theorem ideal_power_canonical_norm_lower {m : ℕ} (b : Basis (Fin d) ℤ (𝓞 K))
    (I : Ideal (𝓞 K)) {x : Fin m → 𝓞 K} (hx : ∀ i, x i ∈ I) (hx₀ : x ≠ 0) :
    Real.sqrt d * (Ideal.absNorm I : ℝ) ^ (1 / (d : ℝ)) ≤ ‖canonicalPowerEmbedding K m x‖ := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx₀
  have hi₀ : x i ≠ 0 := hi
  exact (ideal_canonical_norm_lower K b I (hx i) hi₀).trans
    (PiLp.norm_apply_le (canonicalPowerEmbedding K m x) i)

/-- Use an open ball of at most half the ideal separation scale. Its residue
representatives are unique; boundary points belong to the tail event. -/
theorem ideal_open_ball_residue_injective {m : ℕ} (b : Basis (Fin d) ℤ (𝓞 K))
    (I : Ideal (𝓞 K)) {R : ℝ}
    (hR : 2 * R ≤ Real.sqrt d * (Ideal.absNorm I : ℝ) ^ (1 / (d : ℝ)))
    (x y : Fin m → 𝓞 K)
    (hx : ‖canonicalPowerEmbedding K m x‖ < R) (hy : ‖canonicalPowerEmbedding K m y‖ < R)
    (hxy : ∀ i, Ideal.Quotient.mk I (x i) = Ideal.Quotient.mk I (y i)) : x = y := by
  by_contra hne
  have hmem : ∀ i, (x - y) i ∈ I := by
    intro i
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simp only [Pi.sub_apply, map_sub, hxy i, sub_self]
  have hlow := ideal_power_canonical_norm_lower K b I hmem (sub_ne_zero.mpr hne)
  have hu : ‖canonicalPowerEmbedding K m (x - y)‖ ≤
      ‖canonicalPowerEmbedding K m x‖ + ‖canonicalPowerEmbedding K m y‖ := by
    rw [map_sub]
    exact norm_sub_le _ _
  linarith

end SISToKSIS
