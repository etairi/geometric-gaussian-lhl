import GeometricGaussianLHL.GaussianAnalysis
import Mathlib.GroupTheory.Coset.Basic

/-!
# Theta integrals and coset decomposition

This module collects the following proof sections, in dependency order.
- The saturated row lattice and the projected dual quotient (`RowSaturation`).
- Exact contribution of one row-lattice coset (`CosetIntegral`).
- Decomposing the theta integral into row-lattice cosets (`CosetDecomposition`).
- Counting row-lattice cosets in the saturation (`RowIndex`).
- Finite multiplicity of projected cosets (`QuotientMultiplicity`).
- The exact theta integral (`ThetaIntegral`).
- From a remainder bound to surjectivity and smoothing (`NearFarIntegral`).
-/

section RowSaturation

/-!
## The saturated row lattice and the projected dual quotient

Integer vectors in the real row space form the saturation of `Aᵀ ℤ^R`.
Projection onto the real kernel identifies the quotient by that saturation
with the actual intrinsic dual lattice.
-/

noncomputable section

namespace GeometricGaussianLHL

def rowSaturation {R M : ℕ} (A : Matrix (Fin R) (Fin M) ℤ) : Submodule ℤ (Coeff M) :=
  ((realCoefficientMap A.transpose).range.restrictScalars ℤ).comap (integerEmbedding M)

@[simp] theorem mem_rowSaturation {R M : ℕ} (A : Matrix (Fin R) (Fin M) ℤ) (k : Coeff M) :
    k ∈ rowSaturation A ↔ integerEmbedding M k ∈ (realCoefficientMap A.transpose).range := Iff.rfl

def projectedIntegerMap {R M : ℕ} (A : Matrix (Fin R) (Fin M) ℤ) :
    Coeff M →ₗ[ℤ] latticeDual (euclideanKernel A) :=
  (((realCoefficientMap A).ker.starProjection.toLinearMap.restrictScalars ℤ).comp
    (integerEmbedding M)).codRestrict _ (fun k =>
      (mem_dual_kernel_iff_real_projection A _).mpr ⟨k, rfl⟩)

@[simp] theorem projectedIntegerMap_apply {R M : ℕ}
    (A : Matrix (Fin R) (Fin M) ℤ) (k : Coeff M) :
    (projectedIntegerMap A k : Euclidean M) =
      (realCoefficientMap A).ker.starProjection (integerEmbedding M k) := rfl

theorem projectedIntegerMap_surjective {R M : ℕ} (A : Matrix (Fin R) (Fin M) ℤ) :
    Function.Surjective (projectedIntegerMap A) := by
  intro v
  obtain ⟨k, hk⟩ := (mem_dual_kernel_iff_real_projection A v).mp v.property
  exact ⟨k, Subtype.ext hk⟩

theorem projectedIntegerMap_ker {R M : ℕ} (A : Matrix (Fin R) (Fin M) ℤ) :
    (projectedIntegerMap A).ker = rowSaturation A := by
  ext k
  change projectedIntegerMap A k = 0 ↔ _
  rw [Subtype.ext_iff, projectedIntegerMap_apply, Submodule.coe_zero, mem_rowSaturation,
    ← realCoefficientMap_ker_orthogonal]
  change integerEmbedding M k ∈ (realCoefficientMap A).ker.starProjection.ker ↔ _
  rw [Submodule.ker_starProjection]

theorem rowImage_le_saturation {R M : ℕ} (A : Matrix (Fin R) (Fin M) ℤ) :
    (coefficientMap A.transpose).range ≤ rowSaturation A := by
  rintro k ⟨z, rfl⟩
  exact ⟨integerEmbedding R z, realCoefficientMap_integerEmbedding A.transpose z⟩

/-- Saturation expressed directly by divisibility of integer vectors. -/
theorem rowSaturation_saturated {R M : ℕ} (A : Matrix (Fin R) (Fin M) ℤ)
    {a : ℤ} (ha : a ≠ 0) {k : Coeff M} (hk : a • k ∈ rowSaturation A) :
    k ∈ rowSaturation A := by
  rw [← projectedIntegerMap_ker] at hk ⊢
  change projectedIntegerMap A k = 0
  have h : a • projectedIntegerMap A k = 0 := by
    simpa only [LinearMap.mem_ker, map_smul] using hk
  apply Subtype.ext
  have hc := congrArg (fun v : latticeDual (euclideanKernel A) => (v : Euclidean M)) h
  change a • (projectedIntegerMap A k : Euclidean M) = 0 at hc
  have hc' : (a : ℝ) • (projectedIntegerMap A k : Euclidean M) = 0 := by
    simpa only [Int.cast_smul_eq_zsmul] using hc
  exact (smul_eq_zero.mp hc').resolve_left (by exact_mod_cast ha)

/-- The quotient by the saturated row lattice is exactly the intrinsic dual. -/
def rowSaturationQuotientEquiv {R M : ℕ} (A : Matrix (Fin R) (Fin M) ℤ) :
    (Coeff M ⧸ rowSaturation A) ≃ₗ[ℤ] latticeDual (euclideanKernel A) :=
  (Submodule.quotEquivOfEq _ _ (projectedIntegerMap_ker A).symm).trans
    ((projectedIntegerMap A).quotKerEquivOfSurjective (projectedIntegerMap_surjective A))

@[simp] theorem rowSaturationQuotientEquiv_mk {R M : ℕ}
    (A : Matrix (Fin R) (Fin M) ℤ) (k : Coeff M) :
    rowSaturationQuotientEquiv A (Submodule.Quotient.mk k) = projectedIntegerMap A k := by
  rfl

end GeometricGaussianLHL
end

end RowSaturation

section CosetIntegral

/-!
## Exact contribution of one row-lattice coset

Translation by an integer row-lattice vector unfolds the cube integral to
the affine-fiber integral. The result retains the exact Gram determinant.
-/

noncomputable section

open MeasureTheory

namespace GeometricGaussianLHL

theorem row_coset_displacement {R M : ℕ} (A : Matrix (Fin R) (Fin M) ℤ)
    (k : Coeff M) (z : Coeff R) (y : Euclidean R) :
    integerEmbedding M (k + coefficientMap A.transpose z) - realCoefficientMap A.transpose y =
      integerEmbedding M k - realCoefficientMap A.transpose (y - integerEmbedding R z) := by
  rw [map_add, map_sub, realCoefficientMap_integerEmbedding]
  abel

/-- The complete analytic contribution of a row-lattice coset, before
counting how many cosets give the same projected dual vector. -/
theorem lintegral_row_coset {R M : ℕ} (A : Matrix (Fin R) (Fin M) ℤ)
    (hA : Function.Surjective (realCoefficientMap A)) (k : Coeff M)
    {t : ℝ} (ht : 0 < t) :
    (∫⁻ y in centeredUnitCube R, ∑' z : Coeff R,
      ENNReal.ofReal (gaussianWeight t
        (integerEmbedding M (k + coefficientMap A.transpose z) - realCoefficientMap A.transpose y))) =
      ENNReal.ofReal
        (gaussianWeight t ((realCoefficientMap A).ker.starProjection (integerEmbedding M k)) /
          (t ^ R * gramDet A)) := by
  simp_rw [row_coset_displacement]
  have h := lintegral_integer_periodization_cube R
    (fun y : Euclidean R => ENNReal.ofReal
      (gaussianWeight t (integerEmbedding M k - realCoefficientMap A.transpose y))) (by
        unfold gaussianWeight
        fun_prop)
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrable_gaussianWeight_affine _ (realCoefficientMap_transpose_injective A hA)
      (integerEmbedding M k) ht) (Filter.Eventually.of_forall (fun _ => (gaussianWeight_pos _ _).le)),
    integral_coefficient_gaussian_fiber A hA k ht] at h
  exact h

end GeometricGaussianLHL
end

end CosetIntegral

section CosetDecomposition

/-!
## Decomposing the theta integral into row-lattice cosets

A concrete choice of coset representatives gives a bijection with a quotient
product. Nonnegative sums are reindexed without finiteness assumptions.
-/

noncomputable section

open MeasureTheory

namespace GeometricGaussianLHL

section Quotient
variable {G : Type*} [AddCommGroup G]

def cosetProductMap (H : AddSubgroup G) (qz : (G ⧸ H) × H) : G :=
  qz.1.out + qz.2

theorem cosetProductMap_quotient (H : AddSubgroup G) (qz : (G ⧸ H) × H) :
    (QuotientAddGroup.mk' H) (cosetProductMap H qz) = qz.1 := by
  rw [QuotientAddGroup.mk'_apply, cosetProductMap, QuotientAddGroup.mk_add,
    (QuotientAddGroup.eq_zero_iff (qz.2 : G)).mpr qz.2.property, add_zero]
  exact Quotient.out_eq' qz.1

theorem cosetProductMap_bijective (H : AddSubgroup G) : Function.Bijective (cosetProductMap H) := by
  constructor
  · rintro ⟨q, z⟩ ⟨q', z'⟩ h
    have hq := congrArg (QuotientAddGroup.mk' H) h
    simp only [cosetProductMap_quotient] at hq
    change q = q' at hq
    subst q'
    have hz : z = z' := Subtype.ext (add_left_cancel h)
    exact Prod.ext rfl hz
  · intro x
    let q : G ⧸ H := (x : G ⧸ H)
    have hz : x - q.out ∈ H := QuotientAddGroup.eq_iff_sub_mem.mp (Quotient.out_eq' q).symm
    refine ⟨(q, ⟨x - q.out, hz⟩), ?_⟩
    change q.out + (x - q.out) = x
    abel

def cosetProductEquiv (H : AddSubgroup G) : (G ⧸ H) × H ≃ G :=
  Equiv.ofBijective (cosetProductMap H) (cosetProductMap_bijective H)

theorem ennreal_tsum_cosets (H : AddSubgroup G) (f : G → ENNReal) :
    (∑' x : G, f x) = ∑' q : G ⧸ H, ∑' z : H, f (q.out + z) := by
  rw [← (cosetProductEquiv H).tsum_eq f, ENNReal.tsum_prod']
  rfl

end Quotient

theorem coefficientMap_transpose_injective {R M : ℕ} (A : Matrix (Fin R) (Fin M) ℤ)
    (hA : Function.Surjective (realCoefficientMap A)) : Function.Injective (coefficientMap A.transpose) := by
  intro x y h
  apply integerEmbedding_injective R
  apply realCoefficientMap_transpose_injective A hA
  rw [realCoefficientMap_integerEmbedding, realCoefficientMap_integerEmbedding, h]

/-- The integer sum is partitioned into actual cosets of `Aᵀ ℤ^R`. -/
theorem ennreal_tsum_row_cosets {R M : ℕ} (A : Matrix (Fin R) (Fin M) ℤ)
    (hA : Function.Surjective (realCoefficientMap A)) (f : Coeff M → ENNReal) :
    (∑' k : Coeff M, f k) = ∑' q : Coeff M ⧸ coefficientImage A.transpose,
      ∑' z : Coeff R, f (q.out + coefficientMap A.transpose z) := by
  rw [ennreal_tsum_cosets (coefficientImage A.transpose) f]
  apply tsum_congr
  intro q
  let e : Coeff R ≃ₗ[ℤ] coefficientImage A.transpose :=
    LinearEquiv.ofInjective (coefficientMap A.transpose) (coefficientMap_transpose_injective A hA)
  exact (e.toEquiv.tsum_eq (fun z => f (q.out + z))).symm

/-- The theta integral equals the sum of the proved coset contributions.
The remaining step of Proposition 4.1 is their finite multiplicity over
each projected intrinsic dual vector. -/
theorem theta_integral_eq_coset_sum {R M : ℕ} (A : Matrix (Fin R) (Fin M) ℤ)
    (hA : Function.Surjective (realCoefficientMap A)) {t : ℝ} (ht : 0 < t) :
    ENNReal.ofReal (∫ y in centeredUnitCube R, thetaIntegrand A t y) =
      ∑' q : Coeff M ⧸ coefficientImage A.transpose,
        ENNReal.ofReal
          (gaussianWeight t ((realCoefficientMap A).ker.starProjection (integerEmbedding M q.out)) /
            (t ^ R * gramDet A)) := by
  let : Countable (Coeff M ⧸ coefficientImage A.transpose) :=
    (QuotientAddGroup.mk'_surjective (coefficientImage A.transpose)).countable
  rw [ofReal_integral_eq_lintegral_ofReal (thetaIntegrand_integrableOn_cube A ht)
    (Filter.Eventually.of_forall (thetaIntegrand_nonneg A ht))]
  simp_rw [thetaIntegrand_ennreal_eq_tsum A ht, ennreal_tsum_row_cosets A hA]
  rw [lintegral_tsum]
  · exact tsum_congr (fun q => lintegral_row_coset A hA q.out ht)
  · intro q
    apply Measurable.aemeasurable
    apply Measurable.tsum
    intro z
    unfold gaussianWeight
    fun_prop

end GeometricGaussianLHL
end

end CosetDecomposition

section RowIndex

/-!
## Counting row-lattice cosets in the saturation

Factoring the integer image reduces the multiplicity to a square matrix.
An integer right inverse makes the remaining row lattice primitive; the
square matrix and its transpose have the same absolute determinant.
-/

noncomputable section

namespace GeometricGaussianLHL

def rowMultiplicity {R M : ℕ} (A : Matrix (Fin R) (Fin M) ℤ) : ℕ :=
  (coefficientImage A.transpose).relIndex (rowSaturation A).toAddSubgroup

/-- The row lattice of an integer split surjection is already saturated. -/
theorem rowSaturation_eq_rowImage_of_right_inverse {R M : ℕ}
    (B : Matrix (Fin R) (Fin M) ℤ) (D : Matrix (Fin M) (Fin R) ℤ) (hBD : B * D = 1) :
    rowSaturation B = (coefficientMap B.transpose).range := by
  apply le_antisymm
  · intro k hk
    obtain ⟨y, hy⟩ := hk
    have hleft : (realCoefficientMap D.transpose).comp (realCoefficientMap B.transpose) =
        LinearMap.id := by
      rw [← realCoefficientMap_mul, ← Matrix.transpose_mul, hBD, Matrix.transpose_one,
        realCoefficientMap_one]
    have hy' : integerEmbedding R (coefficientMap D.transpose k) = y := by
      rw [← realCoefficientMap_integerEmbedding, ← hy]
      exact LinearMap.congr_fun hleft y
    refine ⟨coefficientMap D.transpose k, integerEmbedding_injective M ?_⟩
    rw [← realCoefficientMap_integerEmbedding, hy', hy]
  · exact rowImage_le_saturation B

/-- An injective square factor changes the row lattice but not its saturation. -/
theorem rowSaturation_mul_square {R M : ℕ} (C : Matrix (Fin R) (Fin R) ℤ)
    (B : Matrix (Fin R) (Fin M) ℤ) (hC : Function.Injective (coefficientMap C)) :
    rowSaturation (C * B) = rowSaturation B := by
  have hCt : Function.Injective (coefficientMap C.transpose) :=
    (coefficientMap_square_injective_iff_det_ne_zero C.transpose).mpr
      (by simpa using (coefficientMap_square_injective_iff_det_ne_zero C).mp hC)
  have hr := realCoefficientMap_square_surjective_of_injective C.transpose hCt
  ext k
  rw [mem_rowSaturation, Matrix.transpose_mul, realCoefficientMap_mul,
    LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr hr), mem_rowSaturation]

theorem rowMultiplicity_factor {R M : ℕ} (C : Matrix (Fin R) (Fin R) ℤ)
    (B : Matrix (Fin R) (Fin M) ℤ) (hC : Function.Injective (coefficientMap C))
    (hB : Function.Surjective (coefficientMap B)) :
    rowMultiplicity (C * B) = imageIndex C.transpose := by
  obtain ⟨D, hBD⟩ := exists_integer_right_inverse B hB
  have hs : rowSaturation (C * B) = (coefficientMap B.transpose).range :=
    (rowSaturation_mul_square C B hC).trans (rowSaturation_eq_rowImage_of_right_inverse B D hBD)
  have hb : Function.Injective (coefficientMap B.transpose) :=
    coefficientMap_transpose_injective B (realCoefficientMap_surjective_of_integer_surjective B hB)
  have htop : (⊤ : AddSubgroup (Coeff R)).map (coefficientMap B.transpose).toAddMonoidHom =
      coefficientImage B.transpose := by
    ext y
    change (∃ x : Coeff R, x ∈ (⊤ : AddSubgroup (Coeff R)) ∧ coefficientMap B.transpose x = y) ↔
      ∃ x : Coeff R, coefficientMap B.transpose x = y
    simp
  rw [rowMultiplicity, hs]
  change (coefficientImage (C * B).transpose).relIndex (coefficientImage B.transpose) = _
  rw [Matrix.transpose_mul, coefficientImage_mul, ← htop,
    AddSubgroup.relIndex_map_map_of_injective _ _ hb, AddSubgroup.relIndex_top_right]
  rfl

/-- The exact multiplicity asserted in Proposition 4.1. -/
theorem rowMultiplicity_eq_imageIndex {R M : ℕ} (A : Matrix (Fin R) (Fin M) ℤ)
    (hA : Function.Surjective (realCoefficientMap A)) : rowMultiplicity A = imageIndex A := by
  obtain ⟨C, B, rfl, hB, hC⟩ := exists_integer_image_factorization A hA
  rw [rowMultiplicity_factor C B hC hB, imageIndex_transpose_square C hC,
    imageIndex_mul_of_surjective C B hB]

theorem rowMultiplicity_pos {R M : ℕ} (A : Matrix (Fin R) (Fin M) ℤ)
    (hA : Function.Surjective (realCoefficientMap A)) : 0 < rowMultiplicity A := by
  rw [rowMultiplicity_eq_imageIndex A hA]
  exact imageIndex_pos_of_real_surjective A hA

end GeometricGaussianLHL
end

end RowIndex

section QuotientMultiplicity

/-!
## Finite multiplicity of projected cosets

The quotient by a subgroup splits as a set into the quotient by a larger
subgroup and a relative quotient. When that relative quotient is finite,
a nonnegative sum of a function of the first component gains its cardinality.
-/

noncomputable section

namespace GeometricGaussianLHL

section Group
variable {G : Type*} [AddCommGroup G]

theorem quotientProduct_first (H S : AddSubgroup G) (hHS : H ≤ S) (q : G ⧸ H) :
    (AddSubgroup.quotientEquivProdOfLE hHS q).1 = (QuotientAddGroup.mk' S) q.out := by
  let e := AddSubgroup.quotientEquivProdOfLE hHS
  calc
    (e q).1 = (e ((QuotientAddGroup.mk' H) q.out)).1 :=
      congrArg (fun a => (e a).1) (Quotient.out_eq' q).symm
    _ = _ := rfl

/-- Every fiber contributes its actual finite cardinality. -/
theorem ennreal_tsum_quotient_multiplicity (H S : AddSubgroup G) (hHS : H ≤ S)
    [Finite (S ⧸ H.addSubgroupOf S)] (f : G ⧸ S → ENNReal) :
    (∑' q : G ⧸ H, f ((QuotientAddGroup.mk' S) q.out)) =
      (H.relIndex S : ENNReal) * ∑' q : G ⧸ S, f q := by
  let e := AddSubgroup.quotientEquivProdOfLE hHS
  rw [← e.symm.tsum_eq (fun q => f ((QuotientAddGroup.mk' S) q.out)), ENNReal.tsum_prod']
  have he (q : G ⧸ S) (z : S ⧸ H.addSubgroupOf S) :
      (QuotientAddGroup.mk' S) (e.symm (q, z)).out = q := by
    rw [← quotientProduct_first H S hHS, e.apply_symm_apply]
  simp_rw [he, ENNReal.tsum_const, ENat.card_eq_coe_natCard]
  rw [ENNReal.tsum_mul_left]
  rfl

end Group

/-- The relative quotient is finite because its index is the positive image index. -/
theorem finite_row_relative_quotient {R M : ℕ} (A : Matrix (Fin R) (Fin M) ℤ)
    (hA : Function.Surjective (realCoefficientMap A)) :
    Finite ((rowSaturation A).toAddSubgroup ⧸
      (coefficientImage A.transpose).addSubgroupOf (rowSaturation A).toAddSubgroup) := by
  apply AddSubgroup.index_ne_zero_iff_finite.mp
  exact (rowMultiplicity_pos A hA).ne'

/-- Reindexing by intrinsic dual vectors counts each vector exactly `imageIndex A` times. -/
theorem projected_coset_tsum_eq_index_mul {R M : ℕ} (A : Matrix (Fin R) (Fin M) ℤ)
    (hA : Function.Surjective (realCoefficientMap A))
    (f : latticeDual (euclideanKernel A) → ENNReal) :
    (∑' q : Coeff M ⧸ coefficientImage A.transpose, f (projectedIntegerMap A q.out)) =
      (imageIndex A : ENNReal) * ∑' v : latticeDual (euclideanKernel A), f v := by
  let := finite_row_relative_quotient A hA
  let H := coefficientImage A.transpose
  let S := (rowSaturation A).toAddSubgroup
  let e : (Coeff M ⧸ S) ≃ₗ[ℤ] latticeDual (euclideanKernel A) := rowSaturationQuotientEquiv A
  have he (k : Coeff M) : e ((QuotientAddGroup.mk' S) k) = projectedIntegerMap A k :=
    rowSaturationQuotientEquiv_mk A k
  have h := ennreal_tsum_quotient_multiplicity H S (rowImage_le_saturation A) (fun q => f (e q))
  simp only [he] at h
  have hsum : (∑' q : Coeff M ⧸ S, f (e q)) = ∑' v : latticeDual (euclideanKernel A), f v :=
    e.toEquiv.tsum_eq f
  rw [hsum] at h
  change _ = (rowMultiplicity A : ENNReal) * _ at h
  rw [rowMultiplicity_eq_imageIndex A hA] at h
  exact h

end GeometricGaussianLHL
end

end QuotientMultiplicity

section ThetaIntegral

/-!
## The exact theta integral

Proposition 4.1 for every full-row-rank integer matrix and every positive
parameter. The integrand, infinite dual mass, and finite image index are the
actual objects defined in the certificate, with all convergence and
multiplicity arguments proved in the preceding modules.
-/

noncomputable section

open MeasureTheory

namespace GeometricGaussianLHL

theorem theta_integral_divided {R M : ℕ} (A : Matrix (Fin R) (Fin M) ℤ)
    (hA : Function.Surjective (realCoefficientMap A)) {t : ℝ} (ht : 0 < t) :
    ENNReal.ofReal (∫ y in centeredUnitCube R, thetaIntegrand A t y) =
      (imageIndex A : ENNReal) *
        (dualMass (euclideanKernel A) t / ENNReal.ofReal (t ^ R * gramDet A)) := by
  have hD : 0 < t ^ R * gramDet A := mul_pos (pow_pos ht _) (gramDet_pos A hA)
  rw [theta_integral_eq_coset_sum A hA ht]
  have h := projected_coset_tsum_eq_index_mul A hA
    (fun v => ENNReal.ofReal (gaussianWeight t (v : Euclidean M) / (t ^ R * gramDet A)))
  simp only [projectedIntegerMap_apply] at h
  rw [h]
  congr 1
  simp_rw [ENNReal.ofReal_div_of_pos hD, div_eq_mul_inv]
  rw [ENNReal.tsum_mul_right]
  rfl

/-- Proposition 4.1: the index-weighted intrinsic dual Gaussian mass is
exactly the normalized torus integral. -/
theorem theta_integral_identity {R M : ℕ} (A : Matrix (Fin R) (Fin M) ℤ)
    (hA : Function.Surjective (realCoefficientMap A)) {t : ℝ} (ht : 0 < t) :
    (imageIndex A : ENNReal) * dualMass (euclideanKernel A) t =
      ENNReal.ofReal ((t ^ R * gramDet A) *
        (∫ y in centeredUnitCube R, thetaIntegrand A t y)) := by
  have hD : 0 < t ^ R * gramDet A := mul_pos (pow_pos ht _) (gramDet_pos A hA)
  have hD0 : ENNReal.ofReal (t ^ R * gramDet A) ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hD
  symm
  rw [ENNReal.ofReal_mul hD.le, theta_integral_divided A hA ht, div_eq_mul_inv]
  calc
    _ = ((imageIndex A : ENNReal) * dualMass (euclideanKernel A) t) *
        (ENNReal.ofReal (t ^ R * gramDet A) * (ENNReal.ofReal (t ^ R * gramDet A))⁻¹) := by ac_rfl
    _ = _ := by rw [ENNReal.mul_inv_cancel hD0 ENNReal.ofReal_ne_top, mul_one]

/-- A bound below two on the actual theta integral simultaneously certifies
integer surjectivity and smoothing, as stated after Proposition 4.1. -/
theorem surjective_and_smoothAt_of_theta_bound {R M : ℕ}
    (A : Matrix (Fin R) (Fin M) ℤ) (hA : Function.Surjective (realCoefficientMap A))
    {t ε : ℝ} (ht : 0 < t) (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hbound : (t ^ R * gramDet A) *
      (∫ y in centeredUnitCube R, thetaIntegrand A t y) ≤ 1 + ε) :
    Function.Surjective (coefficientMap A) ∧ SmoothAt (euclideanKernel A) ε t := by
  apply surjective_and_smoothAt_of_full_rank_mass_bound A hA ht hε1
  rw [theta_integral_identity A hA ht]
  calc
    _ ≤ ENNReal.ofReal (1 + ε) := ENNReal.ofReal_le_ofReal hbound
    _ = 1 + ENNReal.ofReal ε := by rw [ENNReal.ofReal_add zero_le_one hε0, ENNReal.ofReal_one]

end GeometricGaussianLHL
end

end ThetaIntegral

section NearFarIntegral

/-!
## From a remainder bound to surjectivity and smoothing

The actual torus integral splits into the small ball and its complement.
Together with the exact theta identity and Lemma 4.2, this gives the
deterministic deduction used by both finite random-matrix theorems.
-/

noncomputable section

open MeasureTheory

namespace GeometricGaussianLHL

def thetaRemainder {R M : ℕ} (A : Matrix (Fin R) (Fin M) ℤ) (B t : ℝ) : ℝ :=
  (t ^ R * gramDet A) * ∫ y in centeredUnitCube R \ nearOriginBall R B, thetaIntegrand A t y

theorem normalized_theta_le_main_add_remainder {R M : ℕ}
    (A : Matrix (Fin R) (Fin M) ℤ) (hA : Function.Surjective (realCoefficientMap A))
    {B t : ℝ} (hB : 1 ≤ B) (ht : 1 ≤ t) (hcol : ∀ j, ‖realColumn A j‖ ≤ B) :
    (t ^ R * gramDet A) * (∫ y in centeredUnitCube R, thetaIntegrand A t y) ≤
      (1 + 3 * Real.exp (-Real.pi * t ^ 2 / 2)) ^ M + thetaRemainder A B t := by
  have hs := integral_inter_add_sdiff (nearOriginBall_measurable R B)
    (thetaIntegrand_integrableOn_cube A (by linarith : 0 < t))
  rw [Set.inter_eq_right.mpr (nearOriginBall_subset_centeredUnitCube hB)] at hs
  rw [← hs, mul_add]
  exact add_le_add (normalized_near_origin_bound A hA (by linarith) ht hcol) le_rfl

theorem exp_half_le_one_add {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    Real.exp (δ / 2) ≤ 1 + δ := by
  have hx : |δ / 2| ≤ 1 := by rw [abs_of_nonneg (by positivity)]; linarith
  have h := (le_abs_self (Real.exp (δ / 2) - 1 - δ / 2)).trans
    (Real.abs_exp_sub_one_sub_id_le hx)
  nlinarith [mul_nonneg hδ0 (sub_nonneg.mpr hδ1)]

theorem mainTermFactor_le_one_add {M : ℕ} {t δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hsmall : 3 * (M : ℝ) * Real.exp (-Real.pi * t ^ 2 / 2) ≤ δ / 2) :
    (1 + 3 * Real.exp (-Real.pi * t ^ 2 / 2)) ^ M ≤ 1 + δ := by
  calc
    _ ≤ (Real.exp (3 * Real.exp (-Real.pi * t ^ 2 / 2))) ^ M := by
      gcongr
      linarith [Real.add_one_le_exp (3 * Real.exp (-Real.pi * t ^ 2 / 2))]
    _ = Real.exp ((M : ℝ) * (3 * Real.exp (-Real.pi * t ^ 2 / 2))) := (Real.exp_nat_mul _ M).symm
    _ ≤ Real.exp (δ / 2) := Real.exp_le_exp.mpr (by nlinarith)
    _ ≤ 1 + δ := exp_half_le_one_add hδ0 hδ1

theorem mainTerm_small_of_log_bound {M : ℕ} (hM : 0 < M) {t δ : ℝ} (hδ : 0 < δ)
    (hparam : 2 * Real.log (6 * (M : ℝ) / δ) ≤ Real.pi * t ^ 2) :
    3 * (M : ℝ) * Real.exp (-Real.pi * t ^ 2 / 2) ≤ δ / 2 := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have he : Real.exp (-Real.pi * t ^ 2 / 2) ≤ δ / (6 * (M : ℝ)) := by
    calc
      _ ≤ Real.exp (-Real.log (6 * (M : ℝ) / δ)) := Real.exp_le_exp.mpr (by linarith)
      _ = _ := by rw [Real.exp_neg, Real.exp_log (by positivity)]; field_simp
  calc
    _ ≤ 3 * (M : ℝ) * (δ / (6 * (M : ℝ))) := mul_le_mul_of_nonneg_left he (by positivity)
    _ = _ := by field_simp; ring

/-- The analytic conclusion once the actual remainder has been bounded.
The probabilistic estimate supplying `hrem` remains a separate obligation. -/
theorem surjective_and_smoothAt_of_remainder_bound {R M : ℕ}
    (A : Matrix (Fin R) (Fin M) ℤ) (hA : Function.Surjective (realCoefficientMap A))
    {B t δ : ℝ} (hB : 1 ≤ B) (ht : 1 ≤ t) (hcol : ∀ j, ‖realColumn A j‖ ≤ B)
    (hδ0 : 0 ≤ δ) (hδ1 : 2 * δ < 1)
    (hsmall : 3 * (M : ℝ) * Real.exp (-Real.pi * t ^ 2 / 2) ≤ δ / 2)
    (hrem : thetaRemainder A B t ≤ δ) :
    Function.Surjective (coefficientMap A) ∧ SmoothAt (euclideanKernel A) (2 * δ) t := by
  apply surjective_and_smoothAt_of_theta_bound A hA (by linarith) (by positivity) hδ1
  have h := normalized_theta_le_main_add_remainder A hA hB ht hcol
  have hm := mainTermFactor_le_one_add hδ0 (by linarith : δ ≤ 1) hsmall
  linarith

end GeometricGaussianLHL
end

end NearFarIntegral
