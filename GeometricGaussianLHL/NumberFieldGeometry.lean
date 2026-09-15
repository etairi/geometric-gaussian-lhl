import GeometricGaussianLHL.GaussianAnalysis
import Mathlib.Algebra.Algebra.Hom.Rat
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Canonical number-field coordinates and Gram geometry

This module collects the following proof sections, in dependency order.
- The canonical number-field space with the t₂ norm (`CanonicalSpace`).
- Prime-power sums of roots of unity (`RootSums`).
- The canonical coefficient isomorphism (`CanonicalCoordinates`).
- Integral power-basis coordinates and cyclotomic embeddings (`CyclotomicCoordinates`).
- The canonical Gram matrix for prime-power power bases (`PrimePowerGram`).
- Canonical coordinates on powers and kernel lattices (`CanonicalPowers`).
- Canonical Gram determinant and field discriminant (`CanonicalDiscriminant`).
- Recovering the canonical metric from its Gram matrix (`CanonicalGramNorm`).
- Canonical inner products in integral-basis coordinates (`CanonicalGramPairing`).
- Sharp basis constants from Gram eigenvalues (`CanonicalGramSpectrum`).
- Ring matrices are the coefficient block matrices (`RingBlocks`).
- Norms of the repeated coefficient multiplication operators (`RingOperatorNorms`).
- The integral-basis multiplication constant (`NumberFieldOperators`).
- Multiplication and the canonical norm (`CanonicalMultiplication`).
-/

section CanonicalSpace

/-!
## The canonical number-field space with the t₂ norm

We use the real span of all complex embeddings inside complex Euclidean
space. Its inherited real inner product counts both embeddings of each
nonreal conjugate pair, exactly as in the paper. It has real dimension
equal to the field degree; an integral basis gives a real basis of this span.
-/

noncomputable section

open Module NumberField

namespace GeometricGaussianLHL

variable (K : Type*) [Field K] [NumberField K]

abbrev CanonicalAmbient := EuclideanSpace ℂ (K →+* ℂ)

def canonicalIntegerVector : 𝓞 K →ₗ[ℤ] CanonicalAmbient K :=
  ((WithLp.linearEquiv 2 ℂ ((K →+* ℂ) → ℂ)).symm.toLinearMap.restrictScalars ℤ).comp
    (((NumberField.canonicalEmbedding K).comp (algebraMap (𝓞 K) K)).toIntAlgHom.toLinearMap)

omit [NumberField K] in
@[simp] theorem canonicalIntegerVector_apply (x : 𝓞 K) (τ : K →+* ℂ) :
    canonicalIntegerVector K x τ = τ (algebraMap (𝓞 K) K x) := rfl

theorem canonicalIntegerVector_injective : Function.Injective (canonicalIntegerVector K) := by
  intro x y h
  apply NumberField.RingOfIntegers.coe_injective
  apply NumberField.canonicalEmbedding_injective
  funext τ
  exact congrArg (fun z : CanonicalAmbient K => z τ) h

/-- The squared norm is the sum over all complex embeddings, without
discarding a conjugate or silently using the function-space maximum norm. -/
theorem canonicalIntegerVector_norm_sq (x : 𝓞 K) :
    ‖canonicalIntegerVector K x‖ ^ 2 =
      ∑ τ : K →+* ℂ, ‖τ (algebraMap (𝓞 K) K x)‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq, canonicalIntegerVector_apply]

def canonicalSpace : Submodule ℝ (CanonicalAmbient K) :=
  Submodule.span ℝ (Set.range (canonicalIntegerVector K))

omit [NumberField K] in
theorem canonicalSpace_span_basis {ι : Type*} [Fintype ι]
    (b : Basis ι ℤ (𝓞 K)) :
    Submodule.span ℝ (Set.range (fun i => canonicalIntegerVector K (b i))) = canonicalSpace K := by
  have hz : Submodule.span ℤ (Set.range (fun i => canonicalIntegerVector K (b i))) =
      (canonicalIntegerVector K).range := by
    change Submodule.span ℤ (Set.range (canonicalIntegerVector K ∘ b)) = _
    rw [Set.range_comp, ← Submodule.map_span, b.span_eq, Submodule.map_top]
  rw [← Submodule.span_span_of_tower ℤ ℝ, hz]
  rfl

theorem canonicalIntegerVector_basis_independent :
    LinearIndependent ℝ (fun i => canonicalIntegerVector K (NumberField.RingOfIntegers.basis K i)) := by
  let b := (NumberField.canonicalEmbedding.latticeBasis K).map
    (WithLp.linearEquiv 2 ℂ ((K →+* ℂ) → ℂ)).symm
  have h := LinearIndependent.restrict_scalars
    (R := ℝ) (by simpa only [Complex.real_smul, mul_one] using Complex.ofReal_injective)
    b.linearIndependent
  have heq : (fun i => b i) =
      (fun i => canonicalIntegerVector K (NumberField.RingOfIntegers.basis K i)) := by
    funext i
    simp only [b, Basis.map_apply, NumberField.canonicalEmbedding.latticeBasis_apply,
      NumberField.integralBasis_apply]
    rfl
  exact heq ▸ h

theorem canonicalSpace_finrank : finrank ℝ (canonicalSpace K) = finrank ℚ K := by
  rw [← canonicalSpace_span_basis K (NumberField.RingOfIntegers.basis K),
    finrank_span_eq_card (canonicalIntegerVector_basis_independent K),
    ← finrank_eq_card_chooseBasisIndex, NumberField.RingOfIntegers.rank]

theorem canonicalIntegerVector_basis_independent_of_basis {ι : Type*} [Fintype ι]
    (b : Basis ι ℤ (𝓞 K)) : LinearIndependent ℝ (fun i => canonicalIntegerVector K (b i)) := by
  apply linearIndependent_iff_card_eq_finrank_span.mpr
  change Fintype.card ι = finrank ℝ (Submodule.span ℝ (Set.range (fun i => canonicalIntegerVector K (b i))))
  rw [canonicalSpace_span_basis, canonicalSpace_finrank, ← NumberField.RingOfIntegers.rank]
  exact (finrank_eq_card_basis b).symm

def canonicalBasis {ι : Type*} [Fintype ι] (b : Basis ι ℤ (𝓞 K)) :
    Basis ι ℝ (canonicalSpace K) :=
  (Basis.span (canonicalIntegerVector_basis_independent_of_basis K b)).map
    (LinearEquiv.ofEq _ _ (canonicalSpace_span_basis K b))

@[simp] theorem canonicalBasis_apply {ι : Type*} [Fintype ι]
    (b : Basis ι ℤ (𝓞 K)) (i : ι) :
    (canonicalBasis K b i : CanonicalAmbient K) = canonicalIntegerVector K (b i) := by
  simp only [canonicalBasis, Basis.map_apply, LinearEquiv.coe_ofEq_apply, Basis.coe_span_apply]

end GeometricGaussianLHL
end

end CanonicalSpace

section RootSums

/-!
## Prime-power sums of roots of unity

The Gram calculation in Proposition 2.1 uses a Ramanujan sum. We prove its
prime-power formula by subtracting the powers with exponent divisible by
the prime from the full geometric sum.
-/

noncomputable section

open Finset

namespace GeometricGaussianLHL

theorem sum_primitiveRoots_eq_coprime_powers {n : ℕ} [NeZero n] {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ n) (f : ℂ → ℂ) :
    ∑ z ∈ primitiveRoots n ℂ, f z =
      ∑ j ∈ (range n).filter (fun j => Nat.Coprime j n), f (ζ ^ j) := by
  classical
  symm
  apply Finset.sum_bij (fun j _ => ζ ^ j)
  · intro j hj
    exact (mem_primitiveRoots (NeZero.pos n)).mpr (hζ.pow_of_coprime j (mem_filter.mp hj).2)
  · intro i hi j hj hij
    exact hζ.pow_inj (mem_range.mp (mem_filter.mp hi).1) (mem_range.mp (mem_filter.mp hj).1) hij
  · intro z hz
    obtain ⟨j, hj, hcop, rfl⟩ := hζ.isPrimitiveRoot_iff.mp ((mem_primitiveRoots (NeZero.pos n)).mp hz)
    exact ⟨j, mem_filter.mpr ⟨mem_range.mpr hj, hcop⟩, rfl⟩
  · intro j hj
    rfl

theorem sum_root_powers {n : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ n) (a : ℕ) :
    ∑ j ∈ range n, (ζ ^ j) ^ a = if n ∣ a then (n : ℂ) else 0 := by
  have hpow : ∀ j : ℕ, (ζ ^ j) ^ a = (ζ ^ a) ^ j := by intro j; simp only [← pow_mul, Nat.mul_comm j a]
  simp_rw [hpow]
  by_cases h : n ∣ a
  · simp [h, (hζ.pow_eq_one_iff_dvd a).mpr h]
  · rw [ite_eq_right h, geom_sum_eq ((hζ.pow_eq_one_iff_dvd a).not.mpr h)]
    have hroot : (ζ ^ a) ^ n = 1 := by rw [← pow_mul, Nat.mul_comm a n, pow_mul, hζ.pow_eq_one, one_pow]
    rw [hroot, sub_self, zero_div]

theorem sum_range_divisible {p h : ℕ} (hp : 0 < p) (f : ℕ → ℂ) :
    ∑ i ∈ (range (p * h)).filter (fun i => p ∣ i), f i = ∑ j ∈ range h, f (p * j) := by
  classical
  symm
  apply Finset.sum_bij (fun j _ => p * j)
  · intro j hj
    exact mem_filter.mpr ⟨mem_range.mpr (Nat.mul_lt_mul_of_pos_left (mem_range.mp hj) hp), dvd_mul_right _ _⟩
  · intro i hi j hj hij
    exact Nat.eq_of_mul_eq_mul_left hp hij
  · intro i hi
    obtain ⟨hi, j, rfl⟩ := mem_filter.mp hi
    exact ⟨j, mem_range.mpr ((Nat.mul_lt_mul_left hp).mp (mem_range.mp hi)), rfl⟩
  · intro j hj
    rfl

/-- The prime-power Ramanujan sum, including the zero exponent and degree-one
case. The two divisibility indicators give all three usual cases. -/
theorem sum_primitiveRoots_pow_prime_pow {p k : ℕ} (hp : p.Prime) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) (a : ℕ) :
    ∑ z ∈ primitiveRoots (p ^ (k + 1)) ℂ, z ^ a =
      (if p ^ (k + 1) ∣ a then ((p ^ (k + 1) : ℕ) : ℂ) else 0) -
      (if p ^ k ∣ a then ((p ^ k : ℕ) : ℂ) else 0) := by
  classical
  let : NeZero (p ^ (k + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hcop : ∀ j : ℕ, Nat.Coprime j (p ^ (k + 1)) ↔ ¬p ∣ j := by
    intro j
    rw [Nat.coprime_pow_right_iff (by omega), Nat.coprime_comm, hp.coprime_iff_not_dvd]
  rw [sum_primitiveRoots_eq_coprime_powers hζ]
  simp_rw [hcop]
  have hsmall : IsPrimitiveRoot (ζ ^ p) (p ^ k) :=
    hζ.pow (pow_pos hp.pos _) (pow_succ' p k)
  have hdiv : ∑ j ∈ (range (p ^ (k + 1))).filter (fun j => p ∣ j), (ζ ^ j) ^ a =
      if p ^ k ∣ a then ((p ^ k : ℕ) : ℂ) else 0 := by
    rw [pow_succ', sum_range_divisible hp.pos]
    simpa only [pow_mul] using sum_root_powers hsmall a
  have hsum := Finset.sum_filter_add_sum_filter_not (range (p ^ (k + 1)))
    (fun j => p ∣ j) (fun j => (ζ ^ j) ^ a)
  rw [hdiv, sum_root_powers hζ a] at hsum
  linear_combination hsum

end GeometricGaussianLHL
end

end RootSums

section CanonicalCoordinates

/-!
## The canonical coefficient isomorphism

The paper's basis map is constructed from the actual integral basis and the
all-embeddings t₂ space. Its action on every integer coefficient vector is
the canonical embedding, not an assumed compatibility relation.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Module NumberField

namespace GeometricGaussianLHL

variable (K : Type*) [Field K] [NumberField K] {d : ℕ}

def canonicalIntegerEmbedding : 𝓞 K →ₗ[ℤ] canonicalSpace K :=
  (canonicalIntegerVector K).codRestrict ((canonicalSpace K).restrictScalars ℤ)
    (fun x => Submodule.subset_span (Set.mem_range_self x))

omit [NumberField K] in
@[simp] theorem canonicalIntegerEmbedding_coe (x : 𝓞 K) :
    (canonicalIntegerEmbedding K x : CanonicalAmbient K) = canonicalIntegerVector K x := rfl

theorem canonicalIntegerEmbedding_injective : Function.Injective (canonicalIntegerEmbedding K) := by
  intro x y h
  exact canonicalIntegerVector_injective K (congrArg Subtype.val h)

def coefficientCanonicalEquiv (b : Basis (Fin d) ℤ (𝓞 K)) :
    Euclidean d ≃L[ℝ] canonicalSpace K :=
  ((WithLp.linearEquiv 2 ℝ (Fin d → ℝ)).trans (canonicalBasis K b).equivFun.symm).toContinuousLinearEquiv

theorem coefficientCanonicalEquiv_integer (b : Basis (Fin d) ℤ (𝓞 K)) (x : 𝓞 K) :
    coefficientCanonicalEquiv K b (integerEmbedding d (b.equivFun x)) = canonicalIntegerEmbedding K x := by
  apply Subtype.ext
  change (((canonicalBasis K b).equivFun.symm (fun i => (b.equivFun x i : ℝ)) : canonicalSpace K) :
    CanonicalAmbient K) = canonicalIntegerVector K x
  rw [Basis.equivFun_symm_apply]
  simp only [Submodule.coe_sum, Submodule.coe_smul, canonicalBasis_apply]
  simpa only [map_sum, map_smul, Int.cast_smul_eq_zsmul] using
    congrArg (canonicalIntegerVector K) (b.sum_equivFun x)

theorem coefficientCanonicalEquiv_integer_coefficients (b : Basis (Fin d) ℤ (𝓞 K))
    (z : Coeff d) :
    coefficientCanonicalEquiv K b (integerEmbedding d z) = canonicalIntegerEmbedding K (b.equivFun.symm z) := by
  simpa only [LinearEquiv.apply_symm_apply] using coefficientCanonicalEquiv_integer K b (b.equivFun.symm z)

def basisAlpha (b : Basis (Fin d) ℤ (𝓞 K)) : ℝ := ‖(coefficientCanonicalEquiv K b).toContinuousLinearMap‖

def basisBeta (b : Basis (Fin d) ℤ (𝓞 K)) : ℝ := ‖(coefficientCanonicalEquiv K b).symm.toContinuousLinearMap‖

def basisKappa (b : Basis (Fin d) ℤ (𝓞 K)) : ℝ := basisAlpha K b * basisBeta K b

theorem integralBasis_degree (b : Basis (Fin d) ℤ (𝓞 K)) : d = finrank ℚ K := by
  rw [← NumberField.RingOfIntegers.rank, finrank_eq_card_basis b, Fintype.card_fin]

theorem integralBasis_dimension_pos (b : Basis (Fin d) ℤ (𝓞 K)) : 0 < d := by
  rw [integralBasis_degree K b]
  exact Module.finrank_pos

end GeometricGaussianLHL
end

end CanonicalCoordinates

section CyclotomicCoordinates

/-!
## Integral power-basis coordinates and cyclotomic embeddings

The power basis is Mathlib's proved integral basis of the actual ring of
integers. Summing over all field embeddings is equivalent to summing over
all primitive roots, so its canonical Gram entries are actual root sums.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Module NumberField

namespace GeometricGaussianLHL

variable (K : Type*) [Field K] [NumberField K] {n : ℕ} [NeZero n]
  [IsCyclotomicExtension {n} ℚ K] {ζ : K}

def cyclotomicIntegralBasis (hζ : IsPrimitiveRoot ζ n) :
    Basis (Fin n.totient) ℤ (𝓞 K) :=
  hζ.integralPowerBasis.basis.reindex (finCongr hζ.integralPowerBasis_dim)

theorem cyclotomicIntegralBasis_coe (hζ : IsPrimitiveRoot ζ n) (i : Fin n.totient) :
    algebraMap (𝓞 K) K (cyclotomicIntegralBasis K hζ i) = ζ ^ (i : ℕ) := by
  simp only [cyclotomicIntegralBasis, Basis.reindex_apply, PowerBasis.coe_basis,
    IsPrimitiveRoot.integralPowerBasis_gen, map_pow]
  rfl

theorem cyclotomicIntegralBasis_eq_pow (hζ : IsPrimitiveRoot ζ n) (i : Fin n.totient) :
    cyclotomicIntegralBasis K hζ i = hζ.toInteger ^ (i : ℕ) := by
  apply NumberField.RingOfIntegers.coe_injective
  exact cyclotomicIntegralBasis_coe K hζ i

theorem cyclotomicIntegralBasis_one (hζ : IsPrimitiveRoot ζ n)
    (i : Fin n.totient) (hi : (i : ℕ) = 0) : cyclotomicIntegralBasis K hζ i = 1 := by
  rw [cyclotomicIntegralBasis_eq_pow, hi, pow_zero]

def cyclotomicEmbeddingsEquiv (hζ : IsPrimitiveRoot ζ n) :
    (K →+* ℂ) ≃ primitiveRoots n ℂ :=
  (RingHom.equivRatAlgHom K ℂ).trans (hζ.embeddingsEquivPrimitiveRoots ℂ
    (Polynomial.cyclotomic.irreducible_rat (NeZero.pos n)))

@[simp] theorem cyclotomicEmbeddingsEquiv_apply (hζ : IsPrimitiveRoot ζ n) (τ : K →+* ℂ) :
    (cyclotomicEmbeddingsEquiv K hζ τ : ℂ) = τ ζ := rfl

theorem sum_cyclotomic_embeddings (hζ : IsPrimitiveRoot ζ n) (f : ℂ → ℂ) :
    ∑ τ : K →+* ℂ, f (τ ζ) = ∑ z ∈ primitiveRoots n ℂ, f z := by
  classical
  calc
    _ = ∑ z : primitiveRoots n ℂ, f z := by
      simpa only [cyclotomicEmbeddingsEquiv_apply] using
        (cyclotomicEmbeddingsEquiv K hζ).sum_comp (fun z : primitiveRoots n ℂ => f z)
    _ = _ := Finset.sum_coe_sort _ _

omit [NumberField K] [IsCyclotomicExtension {n} ℚ K] in
theorem cyclotomic_embedding_norm (hζ : IsPrimitiveRoot ζ n) (τ : K →+* ℂ) :
    ‖τ ζ‖ = 1 :=
  Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, hζ.pow_eq_one, map_one]) (NeZero.ne n)

theorem cyclotomicIntegralBasis_embedding_norm (hζ : IsPrimitiveRoot ζ n)
    (i : Fin n.totient) (τ : K →+* ℂ) :
    ‖τ (algebraMap (𝓞 K) K (cyclotomicIntegralBasis K hζ i))‖ = 1 := by
  rw [cyclotomicIntegralBasis_coe, map_pow, norm_pow, cyclotomic_embedding_norm K hζ, one_pow]

theorem cyclotomicPower_inner_of_le (hζ : IsPrimitiveRoot ζ n) (i j : ℕ) (hij : i ≤ j) :
    inner ℝ (canonicalIntegerVector K (hζ.toInteger ^ i))
      (canonicalIntegerVector K (hζ.toInteger ^ j)) =
      (∑ z ∈ primitiveRoots n ℂ, z ^ (j - i)).re := by
  have hterm : ∀ τ : K →+* ℂ,
      inner ℝ (τ ζ ^ i) (τ ζ ^ j) = (τ ζ ^ (j - i)).re := by
    intro τ
    change ((τ ζ ^ j) * (starRingEnd ℂ) (τ ζ ^ i)).re = _
    rw [← Complex.inv_eq_conj (by rw [norm_pow, cyclotomic_embedding_norm K hζ, one_pow])]
    have hne : τ ζ ≠ 0 := norm_pos_iff.mp (by rw [cyclotomic_embedding_norm K hζ]; norm_num)
    rw [← pow_sub₀ (τ ζ) hne hij]
  rw [PiLp.inner_apply]
  simp only [canonicalIntegerVector_apply, map_pow]
  change (∑ τ : K →+* ℂ, inner ℝ (τ ζ ^ i) (τ ζ ^ j)) = _
  simp_rw [hterm]
  rw [← Complex.re_sum, sum_cyclotomic_embeddings K hζ (fun z => z ^ (j - i))]

end GeometricGaussianLHL
end

end CyclotomicCoordinates

section PrimePowerGram

/-!
## The canonical Gram matrix for prime-power power bases

The entries are computed from the actual embeddings. Reindexing exponents
by their residue modulo `p^k` exhibits the blocks in Proposition 2.1.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Module NumberField
open scoped Kronecker

namespace GeometricGaussianLHL

variable (K : Type*) [Field K] [NumberField K]

def canonicalGram {ι : Type*} [Fintype ι] (b : Basis ι ℤ (𝓞 K)) : Matrix ι ι ℝ :=
  fun i j => inner ℝ (canonicalIntegerVector K (b i)) (canonicalIntegerVector K (b j))

theorem canonicalGram_symm {ι : Type*} [Fintype ι] (b : Basis ι ℤ (𝓞 K)) (i j : ι) :
    canonicalGram K b i j = canonicalGram K b j i := real_inner_comm _ _

variable {p k : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p ^ (k + 1)} ℚ K] {ζ : K}

theorem primePowerGram_entry (hζ : IsPrimitiveRoot ζ (p ^ (k + 1)))
    (i j : Fin (p ^ (k + 1)).totient) :
    canonicalGram K (cyclotomicIntegralBasis K hζ) i j =
      if i = j then ((p ^ (k + 1)).totient : ℝ)
      else if (i : ℕ) % p ^ k = (j : ℕ) % p ^ k then -((p ^ k : ℕ) : ℝ) else 0 := by
  have hp : p.Prime := Fact.out
  have hle : ∀ i j : Fin (p ^ (k + 1)).totient, (i : ℕ) ≤ (j : ℕ) →
      canonicalGram K (cyclotomicIntegralBasis K hζ) i j =
        if i = j then ((p ^ (k + 1)).totient : ℝ)
        else if (i : ℕ) % p ^ k = (j : ℕ) % p ^ k then -((p ^ k : ℕ) : ℝ) else 0 := by
    intro i j hij
    unfold canonicalGram
    rw [cyclotomicIntegralBasis_eq_pow, cyclotomicIntegralBasis_eq_pow,
      cyclotomicPower_inner_of_le K hζ i j hij]
    have τ : K →+* ℂ := Classical.choice inferInstance
    have hroot : IsPrimitiveRoot (τ ζ) (p ^ (k + 1)) := hζ.map_of_injective τ.injective
    rw [sum_primitiveRoots_pow_prime_pow hp hroot]
    have hdiff : (j : ℕ) - (i : ℕ) < p ^ (k + 1) :=
      (Nat.sub_le _ _).trans_lt (j.isLt.trans_le (Nat.totient_le _))
    have hbig : p ^ (k + 1) ∣ (j : ℕ) - (i : ℕ) ↔ i = j := by
      constructor
      · intro h
        have hz := Nat.eq_zero_of_dvd_of_lt h hdiff
        exact Fin.ext (by omega : (i : ℕ) = j)
      · rintro rfl
        simp
    have hsmall : p ^ k ∣ (j : ℕ) - (i : ℕ) ↔ (i : ℕ) % p ^ k = (j : ℕ) % p ^ k :=
      (Nat.modEq_iff_dvd' hij).symm
    simp only [hbig, hsmall]
    by_cases heq : i = j
    · subst j
      simp only [ite_true, Complex.sub_re, Complex.natCast_re]
      rw [Nat.totient_prime_pow_succ hp, pow_succ]
      push_cast
      rw [Nat.cast_sub hp.one_le]
      ring
    · simp only [heq, ite_false, zero_sub]
      split_ifs <;> simp only [Complex.neg_re, Complex.natCast_re, Complex.zero_re, neg_zero]
  rcases le_total (i : ℕ) (j : ℕ) with hij | hji
  · exact hle i j hij
  · rw [canonicalGram_symm]
    simpa only [eq_comm] using hle j i hji

def primePowerIndex (p k : ℕ) [Fact p.Prime] :
    Fin (p ^ k) × Fin (p - 1) ≃ Fin (p ^ (k + 1)).totient :=
  (Equiv.prodComm _ _).trans (finProdFinEquiv.trans
    (finCongr (by rw [Nat.totient_prime_pow_succ (Fact.out : p.Prime), Nat.mul_comm])))

@[simp] theorem primePowerIndex_val (p k : ℕ) [Fact p.Prime]
    (i : Fin (p ^ k) × Fin (p - 1)) :
    (primePowerIndex p k i : ℕ) = (i.1 : ℕ) + p ^ k * (i.2 : ℕ) := rfl

theorem primePowerIndex_mod (p k : ℕ) [Fact p.Prime]
    (i : Fin (p ^ k) × Fin (p - 1)) :
    (primePowerIndex p k i : ℕ) % p ^ k = (i.1 : ℕ) := by
  rw [primePowerIndex_val, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt i.1.isLt]

theorem primePowerGram_block_entry (hζ : IsPrimitiveRoot ζ (p ^ (k + 1)))
    (i j : Fin (p ^ k) × Fin (p - 1)) :
    canonicalGram K (cyclotomicIntegralBasis K hζ) (primePowerIndex p k i) (primePowerIndex p k j) =
      if i.1 = j.1 then
        (if i.2 = j.2 then ((p ^ (k + 1) : ℕ) : ℝ) else 0) - ((p ^ k : ℕ) : ℝ)
      else 0 := by
  have hp : p.Prime := Fact.out
  have hdim : ((p ^ (k + 1)).totient : ℝ) =
      ((p ^ (k + 1) : ℕ) : ℝ) - ((p ^ k : ℕ) : ℝ) := by
    rw [Nat.totient_prime_pow_succ hp, pow_succ]
    push_cast
    rw [Nat.cast_sub hp.one_le]
    ring
  rw [primePowerGram_entry, primePowerIndex_mod, primePowerIndex_mod]
  simp only [(primePowerIndex p k).injective.eq_iff, Prod.ext_iff, Fin.val_inj, hdim]
  by_cases hu : i.1 = j.1 <;> by_cases hv : i.2 = j.2 <;> simp [hu, hv]

def primePowerGramBlock (p k : ℕ) : Matrix (Fin (p - 1)) (Fin (p - 1)) ℝ :=
  ((p ^ (k + 1) : ℕ) : ℝ) • (1 : Matrix (Fin (p - 1)) (Fin (p - 1)) ℝ) -
    ((p ^ k : ℕ) : ℝ) • Matrix.of (fun _ _ => 1)

/-- The simultaneous row and column permutation in Proposition 2.1 is the
explicit equivalence `primePowerIndex`, grouping exponents by residue. -/
theorem primePowerGram_blocks (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) :
    canonicalGram K ((cyclotomicIntegralBasis K hζ).reindex (primePowerIndex p k).symm) =
      (1 : Matrix (Fin (p ^ k)) (Fin (p ^ k)) ℝ) ⊗ₖ primePowerGramBlock p k := by
  ext i j
  unfold canonicalGram
  simp only [Basis.reindex_apply, Equiv.symm_symm]
  change canonicalGram K (cyclotomicIntegralBasis K hζ) (primePowerIndex p k i) (primePowerIndex p k j) = _
  rw [primePowerGram_block_entry]
  simp only [Matrix.kroneckerMap_apply, primePowerGramBlock, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.one_apply, Matrix.of_apply, smul_eq_mul, mul_one]
  by_cases hu : i.1 = j.1 <;> by_cases hv : i.2 = j.2 <;> simp [hu, hv]

end GeometricGaussianLHL
end

end PrimePowerGram

section CanonicalPowers

/-!
## Canonical coordinates on powers and kernel lattices

The repeated canonical map is the direct sum of the integral-basis maps.
Its integer action and the actual ring kernel agree with the coefficient
construction used by the finite matrix theorem.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Module NumberField

namespace GeometricGaussianLHL

variable (K : Type*) [Field K] [NumberField K] {d r m : ℕ}

abbrev CanonicalPower (n : ℕ) := PiLp 2 (fun _ : Fin n => canonicalSpace K)

def canonicalPowerEmbedding (n : ℕ) : (Fin n → 𝓞 K) →ₗ[ℤ] CanonicalPower K n :=
  (WithLp.linearEquiv 2 ℤ (Fin n → canonicalSpace K)).symm.toLinearMap.comp
    (LinearMap.pi (fun j => (canonicalIntegerEmbedding K).comp (LinearMap.proj j)))

omit [NumberField K] in
@[simp] theorem canonicalPowerEmbedding_apply (n : ℕ) (x : Fin n → 𝓞 K) (j : Fin n) :
    canonicalPowerEmbedding K n x j = canonicalIntegerEmbedding K (x j) := rfl

def powerCanonicalEquiv (b : Basis (Fin d) ℤ (𝓞 K)) (n : ℕ) :
    Euclidean (n * d) ≃L[ℝ] CanonicalPower K n :=
  (euclideanBlocks n d).toContinuousLinearEquiv.trans
    (repeatedContinuousEquiv (coefficientCanonicalEquiv K b) n)

@[simp] theorem powerCanonicalEquiv_apply (b : Basis (Fin d) ℤ (𝓞 K)) (n : ℕ)
    (x : Euclidean (n * d)) (j : Fin n) :
    powerCanonicalEquiv K b n x j = coefficientCanonicalEquiv K b (euclideanBlocks n d x j) := rfl

theorem powerCanonicalEquiv_integer (b : Basis (Fin d) ℤ (𝓞 K))
    (n : ℕ) (x : Fin n → 𝓞 K) :
    powerCanonicalEquiv K b n (integerEmbedding (n * d) (ringPowerCoordinates b n x)) =
      canonicalPowerEmbedding K n x := by
  have hblocks := euclideanBlocks_integer (ringPowerCoordinates b n) b.equivFun
    (ringPowerCoordinates_apply b n) x
  apply PiLp.ext
  intro j
  rw [powerCanonicalEquiv_apply, hblocks]
  exact coefficientCanonicalEquiv_integer K b (x j)

theorem basisAlpha_pos (b : Basis (Fin d) ℤ (𝓞 K)) : 0 < basisAlpha K b := by
  let : Nonempty (Fin d) := ⟨⟨0, integralBasis_dimension_pos K b⟩⟩
  exact (coefficientCanonicalEquiv K b).norm_pos

theorem basisBeta_pos (b : Basis (Fin d) ℤ (𝓞 K)) : 0 < basisBeta K b := by
  let : Nonempty (Fin d) := ⟨⟨0, integralBasis_dimension_pos K b⟩⟩
  exact (coefficientCanonicalEquiv K b).norm_symm_pos

theorem basisKappa_ge_one (b : Basis (Fin d) ℤ (𝓞 K)) : 1 ≤ basisKappa K b := by
  let : Nonempty (Fin d) := ⟨⟨0, integralBasis_dimension_pos K b⟩⟩
  exact (coefficientCanonicalEquiv K b).one_le_norm_mul_norm_symm

theorem powerCanonicalEquiv_norm_apply_le (b : Basis (Fin d) ℤ (𝓞 K)) (n : ℕ)
    (x : Euclidean (n * d)) : ‖powerCanonicalEquiv K b n x‖ ≤ basisAlpha K b * ‖x‖ := by
  have h := repeatedContinuousEquiv_norm_apply_le (coefficientCanonicalEquiv K b) n
    (euclideanBlocks n d x)
  change ‖repeatedContinuousEquiv (coefficientCanonicalEquiv K b) n (euclideanBlocks n d x)‖ ≤
    ‖(coefficientCanonicalEquiv K b).toContinuousLinearMap‖ * ‖x‖
  simpa only [LinearIsometryEquiv.norm_map] using h

theorem powerCanonicalEquiv_norm_le (b : Basis (Fin d) ℤ (𝓞 K)) (n : ℕ) :
    ‖(powerCanonicalEquiv K b n).toContinuousLinearMap‖ ≤ basisAlpha K b :=
  ContinuousLinearMap.opNorm_le_bound _ (basisAlpha_pos K b).le (powerCanonicalEquiv_norm_apply_le K b n)

theorem powerCanonicalEquiv_symm_norm_apply_le (b : Basis (Fin d) ℤ (𝓞 K)) (n : ℕ)
    (x : CanonicalPower K n) : ‖(powerCanonicalEquiv K b n).symm x‖ ≤ basisBeta K b * ‖x‖ := by
  change ‖(euclideanBlocks n d).symm ((repeatedContinuousEquiv (coefficientCanonicalEquiv K b) n).symm x)‖ ≤ _
  rw [LinearIsometryEquiv.norm_map, repeatedContinuousEquiv_symm]
  exact repeatedContinuousEquiv_norm_apply_le (coefficientCanonicalEquiv K b).symm n x

theorem powerCanonicalEquiv_symm_norm_le (b : Basis (Fin d) ℤ (𝓞 K)) (n : ℕ) :
    ‖(powerCanonicalEquiv K b n).symm.toContinuousLinearMap‖ ≤ basisBeta K b :=
  ContinuousLinearMap.opNorm_le_bound _ (basisBeta_pos K b).le (powerCanonicalEquiv_symm_norm_apply_le K b n)

def canonicalKernel (X : Matrix (Fin r) (Fin m) (𝓞 K)) : Submodule ℤ (CanonicalPower K m) :=
  (ringMatrixMap X).ker.map (canonicalPowerEmbedding K m)

theorem canonicalKernel_eq_image (b : Basis (Fin d) ℤ (𝓞 K))
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) :
    canonicalKernel K X = latticeImage (powerCanonicalEquiv K b m).toContinuousLinearMap
      (euclideanKernel (ringCoefficientMatrix b X)) := by
  rw [latticeImage, euclideanKernel, ringCoefficientMatrix_kernel, ← Submodule.map_comp, ← Submodule.map_comp]
  unfold canonicalKernel
  congr 1
  apply LinearMap.ext
  intro x
  exact (powerCanonicalEquiv_integer K b m x).symm

end GeometricGaussianLHL
end

end CanonicalPowers

section CanonicalDiscriminant

/-!
## Canonical Gram determinant and field discriminant

The all-embeddings t₂ Gram determinant equals the absolute discriminant of
the field. Conjugation of the embeddings proves that the Hermitian Gram
entries are real; the determinant then follows from the embeddings formula
for the algebraic discriminant.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Module NumberField
open scoped ComplexConjugate

namespace GeometricGaussianLHL

variable (K : Type*) [Field K] [NumberField K]

theorem canonical_pair_sum_real (x y : 𝓞 K) :
    ((∑ τ : K →+* ℂ, τ (y : K) * conj (τ (x : K))).re : ℂ) =
      ∑ τ : K →+* ℂ, τ (y : K) * conj (τ (x : K)) := by
  apply Complex.conj_eq_iff_re.mp
  let e := (ComplexEmbedding.involutive_conjugate K).toPerm
  rw [map_sum]
  rw [← Equiv.sum_comp e (fun τ : K →+* ℂ => τ (y : K) * conj (τ (x : K)))]
  apply Finset.sum_congr rfl
  intro τ hτ
  change conj (τ (y : K) * conj (τ (x : K))) = conj (τ (y : K)) * conj (conj (τ (x : K)))
  exact map_mul (starRingEnd ℂ) _ _

theorem canonicalGram_complex {ι : Type*} [Fintype ι] (b : Basis ι ℤ (𝓞 K)) (i j : ι) :
    (canonicalGram K b i j : ℂ) = ∑ τ : K →+* ℂ, τ (b j : K) * conj (τ (b i : K)) := by
  unfold canonicalGram
  rw [PiLp.inner_apply]
  change (((∑ τ : K →+* ℂ, (τ (b j : K) * conj (τ (b i : K))).re) : ℝ) : ℂ) = _
  rw [← Complex.re_sum, canonical_pair_sum_real]

def canonicalEmbeddingsMatrix {ι : Type*} [Fintype ι] (b : Basis ι ℤ (𝓞 K))
    (e : ι ≃ (K →+* ℂ)) : Matrix ι ι ℂ := fun i j => e j (b i : K)

theorem canonicalGram_eq_embeddings_gram {ι : Type*} [Fintype ι] (b : Basis ι ℤ (𝓞 K))
    (e : ι ≃ (K →+* ℂ)) :
    (canonicalGram K b).map (algebraMap ℝ ℂ) =
      (canonicalEmbeddingsMatrix K b e).map conj * (canonicalEmbeddingsMatrix K b e).transpose := by
  ext i j
  change (canonicalGram K b i j : ℂ) = _
  rw [canonicalGram_complex, Matrix.mul_apply]
  rw [← e.sum_comp (fun τ : K →+* ℂ => τ (b j : K) * conj (τ (b i : K)))]
  apply Finset.sum_congr rfl
  intro l hl
  change e l (b j : K) * conj (e l (b i : K)) = conj (e l (b i : K)) * e l (b j : K)
  exact mul_comm _ _

theorem canonicalEmbeddingsMatrix_det_sq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℤ (𝓞 K)) (e : ι ≃ (K →+* ℂ)) :
    (canonicalEmbeddingsMatrix K b e).det ^ 2 = (NumberField.discr K : ℂ) := by
  let bQ := b.localizationLocalization ℚ (nonZeroDivisors ℤ) K
  have h := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ ℂ
    (fun i => (b i : K)) (e.trans (RingHom.equivRatAlgHom K ℂ))
  have hd : Algebra.discr ℚ (fun i => (b i : K)) = (NumberField.discr K : ℚ) := by
    have hbQ : (fun i => (b i : K)) = (bQ : ι → K) := by
      funext i
      exact (Basis.localizationLocalization_apply ℚ (nonZeroDivisors ℤ) K b i).symm
    rw [hbQ, Algebra.discr_localizationLocalization, NumberField.discr_eq_discr]
    rfl
  rw [hd] at h
  exact h.symm

theorem canonicalGram_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℤ (𝓞 K)) :
    (canonicalGram K b).det = |(NumberField.discr K : ℝ)| := by
  let e : ι ≃ (K →+* ℂ) := Fintype.equivOfCardEq (by
    rw [Embeddings.card K ℂ, ← NumberField.RingOfIntegers.rank, finrank_eq_card_basis b])
  have hG : ((canonicalGram K b).det : ℂ) =
      conj (canonicalEmbeddingsMatrix K b e).det * (canonicalEmbeddingsMatrix K b e).det := by
    change (algebraMap ℝ ℂ) (canonicalGram K b).det = _
    rw [(algebraMap ℝ ℂ).map_det]
    change ((canonicalGram K b).map (algebraMap ℝ ℂ)).det = _
    rw [canonicalGram_eq_embeddings_gram K b e, Matrix.det_mul, Matrix.det_transpose]
    congr 1
    exact ((starRingEnd ℂ).map_det _).symm
  have hnorm := congrArg norm hG
  rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_conj, ← pow_two,
    ← norm_pow, canonicalEmbeddingsMatrix_det_sq, Complex.norm_intCast] at hnorm
  have hpos : 0 ≤ (canonicalGram K b).det :=
    (Matrix.posSemidef_gram ℝ (fun i => canonicalIntegerVector K (b i))).det_nonneg
  rw [abs_of_nonneg hpos] at hnorm
  simpa only [Int.cast_abs] using hnorm

end GeometricGaussianLHL
end

end CanonicalDiscriminant

section CanonicalGramNorm

/-!
## Recovering the canonical metric from its Gram matrix

These identities connect the embedding Gram calculation to the actual
coefficient isomorphism. In the orthogonal case they give an exact scaled
isometry, including the norm of the inverse map.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Module NumberField

namespace GeometricGaussianLHL

variable (K : Type*) [Field K] [NumberField K] {d : ℕ}

local instance gramNormEmbeddingsFintype : Fintype (K →+* ℂ) := inferInstance
local instance gramNormAmbientInner : InnerProductSpace ℝ (CanonicalAmbient K) := inferInstance
local instance gramNormSpaceInner : InnerProductSpace ℝ (canonicalSpace K) := inferInstance

theorem canonicalBasis_inner {ι : Type*} [Fintype ι] (b : Basis ι ℤ (𝓞 K)) (i j : ι) :
    inner ℝ (canonicalBasis K b i) (canonicalBasis K b j) = canonicalGram K b i j := by
  change inner ℝ (↑(canonicalBasis K b i) : CanonicalAmbient K) (↑(canonicalBasis K b j) : CanonicalAmbient K) = _
  rw [canonicalBasis_apply, canonicalBasis_apply]
  rfl

theorem coefficientCanonicalEquiv_eq_sum (b : Basis (Fin d) ℤ (𝓞 K)) (x : Euclidean d) :
    coefficientCanonicalEquiv K b x = ∑ i, (x i) • canonicalBasis K b i := by
  change (canonicalBasis K b).equivFun.symm (fun i => x i) = _
  exact Basis.equivFun_symm_apply _ _

theorem coefficientCanonicalEquiv_norm_sq (b : Basis (Fin d) ℤ (𝓞 K)) (x : Euclidean d) :
    ‖coefficientCanonicalEquiv K b x‖ ^ 2 =
      ∑ i, ∑ j, (x i) * (x j) * canonicalGram K b i j := by
  rw [← real_inner_self_eq_norm_sq, coefficientCanonicalEquiv_eq_sum]
  simp only [sum_inner, inner_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [real_inner_smul_left, real_inner_smul_right, canonicalBasis_inner, canonicalGram_symm K b j i]
  ring

theorem coefficientCanonicalEquiv_norm_sq_of_diagonal (b : Basis (Fin d) ℤ (𝓞 K))
    {c : ℝ} (hGram : ∀ i j, canonicalGram K b i j = if i = j then c else 0) (x : Euclidean d) :
    ‖coefficientCanonicalEquiv K b x‖ ^ 2 = c * ‖x‖ ^ 2 := by
  classical
  rw [coefficientCanonicalEquiv_norm_sq, EuclideanSpace.norm_sq_eq]
  simp_rw [hGram, mul_ite, mul_zero]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, Real.norm_eq_abs, sq_abs]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem coefficientCanonicalEquiv_norm_of_diagonal (b : Basis (Fin d) ℤ (𝓞 K))
    {c : ℝ} (hc : 0 ≤ c) (hGram : ∀ i j, canonicalGram K b i j = if i = j then c else 0)
    (x : Euclidean d) : ‖coefficientCanonicalEquiv K b x‖ = Real.sqrt c * ‖x‖ := by
  calc
    _ = Real.sqrt (‖coefficientCanonicalEquiv K b x‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ = _ := by rw [coefficientCanonicalEquiv_norm_sq_of_diagonal K b hGram,
      Real.sqrt_mul hc, Real.sqrt_sq (norm_nonneg x)]

theorem basisAlpha_eq_sqrt_of_diagonal (b : Basis (Fin d) ℤ (𝓞 K))
    {c : ℝ} (hc : 0 ≤ c) (hGram : ∀ i j, canonicalGram K b i j = if i = j then c else 0) :
    basisAlpha K b = Real.sqrt c := by
  let i : Fin d := ⟨0, integralBasis_dimension_pos K b⟩
  apply le_antisymm
  · exact ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg c)
      (fun x => (coefficientCanonicalEquiv_norm_of_diagonal K b hc hGram x).le)
  · have h := (coefficientCanonicalEquiv K b).toContinuousLinearMap.le_opNorm
      (EuclideanSpace.basisFun (Fin d) ℝ i)
    change ‖coefficientCanonicalEquiv K b (EuclideanSpace.basisFun (Fin d) ℝ i)‖ ≤ _ at h
    rw [coefficientCanonicalEquiv_norm_of_diagonal K b hc hGram,
      (EuclideanSpace.basisFun (Fin d) ℝ).norm_eq_one, mul_one, mul_one] at h
    exact h

theorem basisBeta_eq_inv_sqrt_of_diagonal (b : Basis (Fin d) ℤ (𝓞 K))
    {c : ℝ} (hc : 0 < c) (hGram : ∀ i j, canonicalGram K b i j = if i = j then c else 0) :
    basisBeta K b = 1 / Real.sqrt c := by
  have hsqrt : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  let B := coefficientCanonicalEquiv K b
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro y
    have h := coefficientCanonicalEquiv_norm_of_diagonal K b hc.le hGram (B.symm y)
    change ‖B (B.symm y)‖ = Real.sqrt c * ‖B.symm y‖ at h
    rw [B.apply_symm_apply] at h
    change ‖B.symm y‖ ≤ 1 / Real.sqrt c * ‖y‖
    calc
      _ = ‖y‖ / Real.sqrt c := (eq_div_iff hsqrt.ne').mpr (by simpa only [mul_comm] using h.symm)
      _ ≤ 1 / Real.sqrt c * ‖y‖ := le_of_eq (by ring)
  · have h := basisKappa_ge_one K b
    unfold basisKappa at h
    rw [basisAlpha_eq_sqrt_of_diagonal K b hc.le hGram] at h
    exact (div_le_iff₀ hsqrt).mpr (by nlinarith)

theorem basisKappa_eq_one_of_diagonal (b : Basis (Fin d) ℤ (𝓞 K))
    {c : ℝ} (hc : 0 < c) (hGram : ∀ i j, canonicalGram K b i j = if i = j then c else 0) :
    basisKappa K b = 1 := by
  unfold basisKappa
  rw [basisAlpha_eq_sqrt_of_diagonal K b hc.le hGram,
    basisBeta_eq_inv_sqrt_of_diagonal K b hc hGram]
  field_simp

theorem powerCanonicalEquiv_norm_of_diagonal (b : Basis (Fin d) ℤ (𝓞 K))
    {c : ℝ} (hc : 0 ≤ c) (hGram : ∀ i j, canonicalGram K b i j = if i = j then c else 0)
    (n : ℕ) (x : Euclidean (n * d)) :
    ‖powerCanonicalEquiv K b n x‖ = Real.sqrt c * ‖x‖ := by
  have hsq : ‖powerCanonicalEquiv K b n x‖ ^ 2 = (Real.sqrt c * ‖x‖) ^ 2 := by
    calc
      _ = ∑ j : Fin n, ‖powerCanonicalEquiv K b n x j‖ ^ 2 := PiLp.norm_sq_eq_of_L2 _ _
      _ = c * ∑ j : Fin n, ‖euclideanBlocks n d x j‖ ^ 2 := by
        simp_rw [powerCanonicalEquiv_apply, coefficientCanonicalEquiv_norm_sq_of_diagonal K b hGram]
        rw [Finset.mul_sum]
      _ = c * ‖x‖ ^ 2 := by rw [← PiLp.norm_sq_eq_of_L2, LinearIsometryEquiv.norm_map]
      _ = _ := by rw [mul_pow, Real.sq_sqrt hc]
  exact (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg c) (norm_nonneg x))).mp hsq

theorem coefficientCanonicalEquiv_norm_sq_reindex {ι : Type*} [Fintype ι]
    (b : Basis (Fin d) ℤ (𝓞 K)) (e : ι ≃ Fin d) (x : Euclidean d) :
    ‖coefficientCanonicalEquiv K b x‖ ^ 2 =
      ∑ i : ι, x (e i) * (canonicalGram K (b.reindex e.symm)).mulVec (fun j => x (e j)) i := by
  classical
  rw [coefficientCanonicalEquiv_norm_sq]
  rw [← e.sum_comp (fun i : Fin d => ∑ j : Fin d, x i * x j * canonicalGram K b i j)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← e.sum_comp (fun j : Fin d => x (e i) * x j * canonicalGram K b (e i) j)]
  simp only [Matrix.mulVec, dotProduct, canonicalGram, Basis.reindex_apply, Equiv.symm_symm]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

end GeometricGaussianLHL
end

end CanonicalGramNorm

section CanonicalGramPairing

/-!
## Canonical inner products in integral-basis coordinates

These bilinear identities recover the actual embedding metric, including
its off-diagonal entries, in integral-basis coordinates.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Module NumberField

namespace GeometricGaussianLHL

variable (K : Type*) [Field K] [NumberField K] {d : ℕ}

local instance gramPairEmbeddingsFintype : Fintype (K →+* ℂ) := inferInstance
local instance gramPairAmbientInner : InnerProductSpace ℝ (CanonicalAmbient K) := inferInstance
local instance gramPairSpaceInner : InnerProductSpace ℝ (canonicalSpace K) := inferInstance
local instance gramPairPowerInner (n : ℕ) : InnerProductSpace ℝ (CanonicalPower K n) := inferInstance

theorem coefficientCanonicalEquiv_inner (b : Basis (Fin d) ℤ (𝓞 K))
    (x y : Euclidean d) :
    inner ℝ (coefficientCanonicalEquiv K b x) (coefficientCanonicalEquiv K b y) =
      ∑ i, ∑ j, (x i) * (y j) * canonicalGram K b i j := by
  rw [coefficientCanonicalEquiv_eq_sum, coefficientCanonicalEquiv_eq_sum]
  rw [sum_inner]
  simp_rw [inner_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [real_inner_smul_left, real_inner_smul_right, canonicalBasis_inner]
  ring

theorem powerCanonicalEquiv_inner (b : Basis (Fin d) ℤ (𝓞 K)) (n : ℕ)
    (x y : Euclidean (n * d)) :
    inner ℝ (powerCanonicalEquiv K b n x) (powerCanonicalEquiv K b n y) =
      ∑ l : Fin n, ∑ i : Fin d, ∑ j : Fin d,
        x (finProdFinEquiv (l, i)) * y (finProdFinEquiv (l, j)) *
          canonicalGram K b i j := by
  rw [PiLp.inner_apply]
  simp_rw [powerCanonicalEquiv_apply, coefficientCanonicalEquiv_inner, euclideanBlocks_apply]

end GeometricGaussianLHL
end

end CanonicalGramPairing

section CanonicalGramSpectrum

/-!
## Sharp basis constants from Gram eigenvalues

A characteristic-polynomial root supplies an actual nonzero coefficient
vector attaining the corresponding norm ratio. Together with a bound on
all vectors, this identifies the operator norm or inverse operator norm.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Module NumberField

namespace GeometricGaussianLHL

variable (K : Type*) [Field K] [NumberField K] {d : ℕ}

local instance gramSpectrumEmbeddingsFintype : Fintype (K →+* ℂ) := inferInstance
local instance gramSpectrumAmbientInner : InnerProductSpace ℝ (CanonicalAmbient K) := inferInstance
local instance gramSpectrumSpaceInner : InnerProductSpace ℝ (canonicalSpace K) := inferInstance

theorem coefficientCanonicalEquiv_norm_sq_mulVec (b : Basis (Fin d) ℤ (𝓞 K)) (x : Euclidean d) :
    ‖coefficientCanonicalEquiv K b x‖ ^ 2 =
      ∑ i, x i * (canonicalGram K b).mulVec (fun j => x j) i := by
  rw [coefficientCanonicalEquiv_norm_sq]
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem exists_norm_eq_sqrt_of_gram_root (b : Basis (Fin d) ℤ (𝓞 K))
    {c : ℝ} (hc : 0 ≤ c) (hroot : (canonicalGram K b).charpoly.IsRoot c) :
    ∃ x : Euclidean d, x ≠ 0 ∧ ‖coefficientCanonicalEquiv K b x‖ = Real.sqrt c * ‖x‖ := by
  have hev : Module.End.HasEigenvalue (canonicalGram K b).toLin' c := by
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin']
    exact hroot
  obtain ⟨v, hv⟩ := hev.exists_hasEigenvector
  let x : Euclidean d := WithLp.toLp 2 v
  have hx : x ≠ 0 := by
    intro hx
    apply hv.2
    exact congrArg (WithLp.ofLp) hx
  have he : (canonicalGram K b).mulVec (fun j => x j) = fun j => c * x j :=
    hv.apply_eq_smul
  refine ⟨x, hx, ?_⟩
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg c) (norm_nonneg x))).mp
  rw [coefficientCanonicalEquiv_norm_sq_mulVec, he, mul_pow, Real.sq_sqrt hc,
    EuclideanSpace.real_norm_sq_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem basisAlpha_eq_sqrt_of_gram_root (b : Basis (Fin d) ℤ (𝓞 K))
    {c : ℝ} (hc : 0 ≤ c) (hroot : (canonicalGram K b).charpoly.IsRoot c)
    (hbound : ∀ x : Euclidean d, ‖coefficientCanonicalEquiv K b x‖ ≤ Real.sqrt c * ‖x‖) :
    basisAlpha K b = Real.sqrt c := by
  apply le_antisymm
  · exact ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg c) hbound
  · obtain ⟨x, hx, he⟩ := exists_norm_eq_sqrt_of_gram_root K b hc hroot
    have h := (coefficientCanonicalEquiv K b).toContinuousLinearMap.le_opNorm x
    change ‖coefficientCanonicalEquiv K b x‖ ≤ basisAlpha K b * ‖x‖ at h
    rw [he] at h
    have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
    nlinarith

theorem basisBeta_eq_inv_sqrt_of_gram_root (b : Basis (Fin d) ℤ (𝓞 K))
    {c : ℝ} (hc : 0 < c) (hroot : (canonicalGram K b).charpoly.IsRoot c)
    (hbound : ∀ x : Euclidean d, Real.sqrt c * ‖x‖ ≤ ‖coefficientCanonicalEquiv K b x‖) :
    basisBeta K b = 1 / Real.sqrt c := by
  have hsqrt : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  let B := coefficientCanonicalEquiv K b
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro y
    have h := hbound (B.symm y)
    change Real.sqrt c * ‖B.symm y‖ ≤ ‖B (B.symm y)‖ at h
    rw [B.apply_symm_apply] at h
    change ‖B.symm y‖ ≤ 1 / Real.sqrt c * ‖y‖
    calc
      _ ≤ ‖y‖ / Real.sqrt c := (le_div_iff₀ hsqrt).mpr (by simpa only [mul_comm] using h)
      _ = _ := by ring
  · obtain ⟨x, hx, he⟩ := exists_norm_eq_sqrt_of_gram_root K b hc.le hroot
    have h := B.symm.toContinuousLinearMap.le_opNorm (B x)
    change ‖B.symm (B x)‖ ≤ basisBeta K b * ‖B x‖ at h
    rw [B.symm_apply_apply] at h
    change ‖B x‖ = Real.sqrt c * ‖x‖ at he
    rw [he] at h
    apply (div_le_iff₀ hsqrt).mpr
    have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
    nlinarith

end GeometricGaussianLHL
end

end CanonicalGramSpectrum

section RingBlocks

/-!
## Ring matrices are the coefficient block matrices

Multiplication by a basis element acts on all ring coordinates. Its integer
matrix gives exactly the block operator used in the finite probabilistic
certificate. The equality is proved on actual matrix entries, using the
integral-basis coordinate equivalence.
-/

noncomputable section

open Module

namespace GeometricGaussianLHL

variable {O : Type*} [CommRing O] {d r m : ℕ}

theorem ringPowerCoordinates_single_basis (b : Basis (Fin d) ℤ O)
    (n : ℕ) (j : Fin n) (k : Fin d) :
    ringPowerCoordinates b n (Pi.single j (b k)) = Pi.single (finProdFinEquiv (j, k)) 1 := by
  ext l
  obtain ⟨⟨j', k'⟩, rfl⟩ := finProdFinEquiv.surjective l
  rw [ringPowerCoordinates_apply]
  by_cases hj : j = j'
  · subst j'
    simp [Pi.single_apply, eq_comm]
  · simp [hj]

theorem ringPowerCoordinates_symm_single (b : Basis (Fin d) ℤ O)
    (n : ℕ) (j : Fin n) (k : Fin d) :
    (ringPowerCoordinates b n).symm (Pi.single (finProdFinEquiv (j, k)) 1) = Pi.single j (b k) := by
  rw [← ringPowerCoordinates_single_basis b n j k, LinearEquiv.symm_apply_apply]

def ringPowerMultiply (n : ℕ) (a : O) : (Fin n → O) →ₗ[ℤ] (Fin n → O) :=
  LinearMap.pi (fun j => (LinearMap.mulLeft ℤ a).comp (LinearMap.proj j))

@[simp] theorem ringPowerMultiply_apply (n : ℕ) (a : O) (x : Fin n → O) (j : Fin n) :
    ringPowerMultiply n a x j = a * x j := rfl

def ringPowerMultiplicationMatrix (b : Basis (Fin d) ℤ O) (n : ℕ) (a : O) :
    Matrix (Fin (n * d)) (Fin (n * d)) ℤ :=
  LinearMap.toMatrix' ((ringPowerCoordinates b n).toLinearMap ∘ₗ ringPowerMultiply n a ∘ₗ
    (ringPowerCoordinates b n).symm.toLinearMap)

theorem ringPowerMultiplicationMatrix_map (b : Basis (Fin d) ℤ O)
    (n : ℕ) (a : O) (x : Fin n → O) :
    coefficientMap (ringPowerMultiplicationMatrix b n a) (ringPowerCoordinates b n x) =
      ringPowerCoordinates b n (fun j => a * x j) := by
  simp only [coefficientMap, ringPowerMultiplicationMatrix, Matrix.toLin'_toMatrix',
    LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  rfl

@[simp] theorem ringPowerMultiplicationMatrix_one (b : Basis (Fin d) ℤ O) (n : ℕ) :
    ringPowerMultiplicationMatrix b n 1 = 1 := by
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_one]
  apply LinearMap.ext
  intro z
  obtain ⟨x, rfl⟩ := (ringPowerCoordinates b n).surjective z
  change coefficientMap (ringPowerMultiplicationMatrix b n 1) (ringPowerCoordinates b n x) =
    ringPowerCoordinates b n x
  rw [ringPowerMultiplicationMatrix_map]
  simp only [one_mul]

theorem ringCoefficientMatrix_column (b : Basis (Fin d) ℤ O)
    (X : Matrix (Fin r) (Fin m) O) (j : Fin m) (k : Fin d) :
    (fun l => ringCoefficientMatrix b X l (finProdFinEquiv (j, k))) =
      ringPowerCoordinates b r (fun i => b k * X i j) := by
  ext l
  simp only [ringCoefficientMatrix, LinearMap.toMatrix'_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, ringPowerCoordinates_symm_single, ringMatrixMap_apply,
    Matrix.mulVec_single]
  apply congrArg (fun x : Fin r → O => ringPowerCoordinates b r x l)
  funext i
  exact mul_comm _ _

/-- The block matrix in the probabilistic theorem is the actual coefficient
matrix of the ring-linear map, once its columns are expressed in the basis. -/
theorem ringCoefficientMatrix_eq_block (b : Basis (Fin d) ℤ O)
    (X : Matrix (Fin r) (Fin m) O) :
    ringCoefficientMatrix b X = blockCoefficientMatrix
      (fun k => ringPowerMultiplicationMatrix b r (b k))
      (fun j => ringPowerCoordinates b r (fun i => X i j)) := by
  ext l q
  obtain ⟨⟨j, k⟩, rfl⟩ := finProdFinEquiv.surjective q
  have hcol := congrFun (ringCoefficientMatrix_column b X j k) l
  rw [blockCoefficientMatrix, Equiv.symm_apply_apply]
  change _ = coefficientMap (ringPowerMultiplicationMatrix b r (b k))
    (ringPowerCoordinates b r (fun i => X i j)) l
  rw [ringPowerMultiplicationMatrix_map]
  exact hcol

end GeometricGaussianLHL
end

end RingBlocks

section RingOperatorNorms

/-!
## Norms of the repeated coefficient multiplication operators

The coefficient action on a vector of ring elements is the direct sum of
the scalar multiplication matrix. An integral spanning set proves the
intertwining identity over the reals, and the Euclidean sum of squares
preserves the scalar operator bound.
-/

noncomputable section

open Module

namespace GeometricGaussianLHL

variable {O : Type*} [CommRing O] {d : ℕ}

def euclideanBlockProjection (n d : ℕ) (j : Fin n) : Euclidean (n * d) →ₗ[ℝ] Euclidean d :=
  (LinearMap.proj j).comp ((WithLp.linearEquiv 2 ℝ (Fin n → Euclidean d)).toLinearMap.comp
    (euclideanBlocks n d).toLinearMap)

@[simp] theorem euclideanBlockProjection_apply (n d : ℕ) (j : Fin n) (x : Euclidean (n * d)) :
    euclideanBlockProjection n d j x = euclideanBlocks n d x j := rfl

theorem euclideanBlockProjection_integer (b : Basis (Fin d) ℤ O)
    (n : ℕ) (x : Fin n → O) (j : Fin n) :
    euclideanBlockProjection n d j (integerEmbedding (n * d) (ringPowerCoordinates b n x)) =
      integerEmbedding d (b.equivFun (x j)) := by
  have h := euclideanBlocks_integer (ringPowerCoordinates b n) b.equivFun
    (ringPowerCoordinates_apply b n) x
  exact congrArg (fun y : PiLp 2 (fun _ : Fin n => Euclidean d) => y j) h

theorem leftMulMatrix_coefficient_map (b : Basis (Fin d) ℤ O) (a x : O) :
    coefficientMap (Algebra.leftMulMatrix b a) (b.equivFun x) = b.equivFun (a * x) :=
  Algebra.leftMulMatrix_mulVec_repr b a x

theorem ringPowerMultiplicationMatrix_block (b : Basis (Fin d) ℤ O)
    (n : ℕ) (a : O) (x : Euclidean (n * d)) (j : Fin n) :
    euclideanBlocks n d (realCoefficientMap (ringPowerMultiplicationMatrix b n a) x) j =
      realCoefficientMap (Algebra.leftMulMatrix b a) (euclideanBlocks n d x j) := by
  have h : (euclideanBlockProjection n d j).comp (realCoefficientMap (ringPowerMultiplicationMatrix b n a)) =
      (realCoefficientMap (Algebra.leftMulMatrix b a)).comp (euclideanBlockProjection n d j) := by
    apply LinearMap.ext_on (integerLattice_span (n * d))
    rintro _ ⟨z, rfl⟩
    obtain ⟨v, rfl⟩ := (ringPowerCoordinates b n).surjective z
    simp only [LinearMap.comp_apply, realCoefficientMap_integerEmbedding,
      ringPowerMultiplicationMatrix_map, euclideanBlockProjection_integer, leftMulMatrix_coefficient_map]
  exact LinearMap.congr_fun h x

theorem ringPowerMultiplicationMatrix_norm_le (b : Basis (Fin d) ℤ O)
    (n : ℕ) (a : O) {μ : ℝ} (hμ : 0 ≤ μ)
    (ha : ∀ x : Euclidean d, ‖realCoefficientMap (Algebra.leftMulMatrix b a) x‖ ≤ μ * ‖x‖)
    (x : Euclidean (n * d)) :
    ‖realCoefficientMap (ringPowerMultiplicationMatrix b n a) x‖ ≤ μ * ‖x‖ := by
  let y := euclideanBlocks n d x
  let z := euclideanBlocks n d (realCoefficientMap (ringPowerMultiplicationMatrix b n a) x)
  have hsq : ‖z‖ ^ 2 ≤ (μ * ‖y‖) ^ 2 := by
    calc
      ‖z‖ ^ 2 = ∑ j : Fin n, ‖z j‖ ^ 2 := PiLp.norm_sq_eq_of_L2 _ z
      _ ≤ ∑ j : Fin n, μ ^ 2 * ‖y j‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro j _
        change ‖euclideanBlocks n d (realCoefficientMap (ringPowerMultiplicationMatrix b n a) x) j‖ ^ 2 ≤ _
        rw [ringPowerMultiplicationMatrix_block, ← mul_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (ha (y j)) 2
      _ = μ ^ 2 * ‖y‖ ^ 2 := by rw [PiLp.norm_sq_eq_of_L2 _ y, Finset.mul_sum]
      _ = (μ * ‖y‖) ^ 2 := (mul_pow _ _ _).symm
  have h := (sq_le_sq₀ (norm_nonneg z) (mul_nonneg hμ (norm_nonneg y))).mp hsq
  simpa only [y, z, LinearIsometryEquiv.norm_map] using h

end GeometricGaussianLHL
end

end RingOperatorNorms

section NumberFieldOperators

/-!
## The integral-basis multiplication constant

The constant μ is the maximum operator norm of the actual multiplication
matrices of the basis elements. It bounds their repeated action on every
power of the ring. A basis element equal to one proves μ ≥ 1.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Module NumberField

namespace GeometricGaussianLHL

variable (K : Type*) [Field K] [NumberField K] {d : ℕ}

def basisMu (b : Basis (Fin d) ℤ (𝓞 K)) : ℝ :=
  Finset.univ.sup' (show (Finset.univ : Finset (Fin d)).Nonempty from
    ⟨⟨0, integralBasis_dimension_pos K b⟩, Finset.mem_univ _⟩)
    (fun k => ‖(realCoefficientMap (Algebra.leftMulMatrix b (b k))).toContinuousLinearMap‖)

theorem basisMultiplication_norm_le_mu (b : Basis (Fin d) ℤ (𝓞 K)) (k : Fin d) :
    ‖(realCoefficientMap (Algebra.leftMulMatrix b (b k))).toContinuousLinearMap‖ ≤ basisMu K b :=
  Finset.le_sup' (fun j => ‖(realCoefficientMap (Algebra.leftMulMatrix b (b j))).toContinuousLinearMap‖)
    (Finset.mem_univ k)

theorem basisMu_nonneg (b : Basis (Fin d) ℤ (𝓞 K)) : 0 ≤ basisMu K b :=
  (norm_nonneg _).trans (basisMultiplication_norm_le_mu K b ⟨0, integralBasis_dimension_pos K b⟩)

theorem basisMu_ge_one (b : Basis (Fin d) ℤ (𝓞 K)) (i : Fin d) (hi : b i = 1) :
    1 ≤ basisMu K b := by
  let : Nonempty (Fin d) := ⟨i⟩
  have h := basisMultiplication_norm_le_mu K b i
  rw [hi, map_one, realCoefficientMap_one] at h
  change ‖ContinuousLinearMap.id ℝ (Euclidean d)‖ ≤ basisMu K b at h
  simpa only [ContinuousLinearMap.norm_id] using h

theorem basisPowerMultiplication_norm_le_mu (b : Basis (Fin d) ℤ (𝓞 K))
    (n : ℕ) (k : Fin d) (x : Euclidean (n * d)) :
    ‖realCoefficientMap (ringPowerMultiplicationMatrix b n (b k)) x‖ ≤ basisMu K b * ‖x‖ := by
  apply ringPowerMultiplicationMatrix_norm_le b n (b k) (basisMu_nonneg K b)
  intro y
  exact ((realCoefficientMap (Algebra.leftMulMatrix b (b k))).toContinuousLinearMap.le_opNorm y).trans
    (mul_le_mul_of_nonneg_right (basisMultiplication_norm_le_mu K b k) (norm_nonneg y))

end GeometricGaussianLHL
end

end NumberFieldOperators

section CanonicalMultiplication

/-!
## Multiplication and the canonical norm

Multiplication acts diagonally on the actual complex embeddings. If all
conjugates of an integer have modulus one, this action is isometric and
its coefficient multiplication matrix has norm at most the basis condition
number. This supplies the multiplication bound in Proposition 2.1.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Module NumberField

namespace GeometricGaussianLHL

variable (K : Type*) [Field K] [NumberField K] {d : ℕ}

def canonicalAmbientMultiply (a : 𝓞 K) : CanonicalAmbient K →ₗ[ℝ] CanonicalAmbient K :=
  let e := WithLp.linearEquiv 2 ℂ ((K →+* ℂ) → ℂ)
  let A : ((K →+* ℂ) → ℂ) →ₗ[ℂ] ((K →+* ℂ) → ℂ) :=
    { toFun := fun x τ => τ (algebraMap (𝓞 K) K a) * x τ
      map_add' := by intro x y; funext τ; exact mul_add _ _ _
      map_smul' := by
        intro c x
        funext τ
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring }
  (e.symm.toLinearMap.comp (A.comp e.toLinearMap)).restrictScalars ℝ

omit [NumberField K] in
@[simp] theorem canonicalAmbientMultiply_apply (a : 𝓞 K) (x : CanonicalAmbient K) (τ : K →+* ℂ) :
    canonicalAmbientMultiply K a x τ = τ (algebraMap (𝓞 K) K a) * x τ := rfl

omit [NumberField K] in
theorem canonicalAmbientMultiply_integer (a x : 𝓞 K) :
    canonicalAmbientMultiply K a (canonicalIntegerVector K x) = canonicalIntegerVector K (a * x) := by
  ext τ
  simp only [canonicalAmbientMultiply_apply, canonicalIntegerVector_apply, map_mul]

theorem coefficientCanonicalEquiv_multiplication (b : Basis (Fin d) ℤ (𝓞 K))
    (a : 𝓞 K) (x : Euclidean d) :
    (coefficientCanonicalEquiv K b (realCoefficientMap (Algebra.leftMulMatrix b a) x) : CanonicalAmbient K) =
      canonicalAmbientMultiply K a (coefficientCanonicalEquiv K b x : CanonicalAmbient K) := by
  let C := (canonicalSpace K).subtype.comp (coefficientCanonicalEquiv K b).toLinearMap
  have h : C.comp (realCoefficientMap (Algebra.leftMulMatrix b a)) =
      (canonicalAmbientMultiply K a).comp C := by
    apply LinearMap.ext_on (integerLattice_span d)
    rintro _ ⟨z, rfl⟩
    obtain ⟨v, rfl⟩ := b.equivFun.surjective z
    change (coefficientCanonicalEquiv K b
      (realCoefficientMap (Algebra.leftMulMatrix b a) (integerEmbedding d (b.equivFun v))) : CanonicalAmbient K) = _
    rw [realCoefficientMap_integerEmbedding, leftMulMatrix_coefficient_map,
      coefficientCanonicalEquiv_integer]
    change canonicalIntegerVector K (a * v) =
      canonicalAmbientMultiply K a (coefficientCanonicalEquiv K b (integerEmbedding d (b.equivFun v)) : CanonicalAmbient K)
    rw [coefficientCanonicalEquiv_integer]
    exact (canonicalAmbientMultiply_integer K a v).symm
  exact LinearMap.congr_fun h x

theorem canonicalAmbientMultiply_norm (a : 𝓞 K)
    (ha : ∀ τ : K →+* ℂ, ‖τ (algebraMap (𝓞 K) K a)‖ = 1) (x : CanonicalAmbient K) :
    ‖canonicalAmbientMultiply K a x‖ = ‖x‖ := by
  have hsq : ‖canonicalAmbientMultiply K a x‖ ^ 2 = ‖x‖ ^ 2 := by
    simp only [EuclideanSpace.norm_sq_eq, canonicalAmbientMultiply_apply, norm_mul, ha, one_mul]
  nlinarith [norm_nonneg (canonicalAmbientMultiply K a x), norm_nonneg x]

theorem canonical_multiplication_norm (b : Basis (Fin d) ℤ (𝓞 K)) (a : 𝓞 K)
    (ha : ∀ τ : K →+* ℂ, ‖τ (algebraMap (𝓞 K) K a)‖ = 1) (x : Euclidean d) :
    ‖coefficientCanonicalEquiv K b (realCoefficientMap (Algebra.leftMulMatrix b a) x)‖ =
      ‖coefficientCanonicalEquiv K b x‖ := by
  change ‖(coefficientCanonicalEquiv K b (realCoefficientMap (Algebra.leftMulMatrix b a) x) : CanonicalAmbient K)‖ =
    ‖(coefficientCanonicalEquiv K b x : CanonicalAmbient K)‖
  rw [coefficientCanonicalEquiv_multiplication, canonicalAmbientMultiply_norm K a ha]

theorem coefficient_multiplication_norm_le_kappa (b : Basis (Fin d) ℤ (𝓞 K)) (a : 𝓞 K)
    (ha : ∀ τ : K →+* ℂ, ‖τ (algebraMap (𝓞 K) K a)‖ = 1) (x : Euclidean d) :
    ‖realCoefficientMap (Algebra.leftMulMatrix b a) x‖ ≤ basisKappa K b * ‖x‖ := by
  let B := coefficientCanonicalEquiv K b
  let T := realCoefficientMap (Algebra.leftMulMatrix b a)
  calc
    ‖T x‖ = ‖B.symm (B (T x))‖ := by rw [B.symm_apply_apply]
    _ ≤ basisBeta K b * ‖B (T x)‖ := B.symm.toContinuousLinearMap.le_opNorm _
    _ = basisBeta K b * ‖B x‖ := by rw [canonical_multiplication_norm K b a ha]
    _ ≤ basisBeta K b * (basisAlpha K b * ‖x‖) :=
      mul_le_mul_of_nonneg_left (B.toContinuousLinearMap.le_opNorm x) (basisBeta_pos K b).le
    _ = _ := by unfold basisKappa; ring

theorem basisMu_le_kappa (b : Basis (Fin d) ℤ (𝓞 K))
    (hb : ∀ i, ∀ τ : K →+* ℂ, ‖τ (algebraMap (𝓞 K) K (b i))‖ = 1) :
    basisMu K b ≤ basisKappa K b := by
  apply Finset.sup'_le
  intro i hi
  exact ContinuousLinearMap.opNorm_le_bound _ ((by linarith [basisKappa_ge_one K b]) : 0 ≤ basisKappa K b)
    (coefficient_multiplication_norm_le_kappa K b (b i) (hb i))

end GeometricGaussianLHL
end

end CanonicalMultiplication
