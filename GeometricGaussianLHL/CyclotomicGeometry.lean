import GeometricGaussianLHL.NumberFieldGeometry
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fin.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.NumberTheory.NumberField.Discriminant.Basic

/-!
# Prime-power and power-of-two geometry

This module collects the following proof sections, in dependency order.
- Quadratic forms of the prime-power Gram blocks (`BlockGram`).
- Exact characteristic polynomial of the Gram blocks (`BlockSpectrum`).
- Signed coefficient permutations for powers of two (`PowerTwoPermutation`).
- Spectrum of the actual prime-power canonical Gram matrix (`PrimePowerSpectrum`).
- Singular-value bounds for the prime-power basis map (`PrimePowerNorms`).
- Exact geometry of the power-of-two integral basis (`PowerTwoGeometry`).
- The exact root discriminant of a power-of-two cyclotomic field (`PowerTwoDiscriminant`).
- Exact prime-power basis constants (`PrimePowerGeometry`).
-/

section BlockGram

/-!
## Quadratic forms of the prime-power Gram blocks

The block matrix is a scalar identity minus a rank-one all-ones matrix.
Its action and quadratic-form bounds follow from finite sums and
Cauchy–Schwarz, without an unproved spectral estimate.
-/

noncomputable section

open scoped Kronecker

namespace GeometricGaussianLHL

def blockGramMatrix (h q : ℕ) (a b : ℝ) : Matrix (Fin h × Fin q) (Fin h × Fin q) ℝ :=
  (1 : Matrix (Fin h) (Fin h) ℝ) ⊗ₖ
    (a • (1 : Matrix (Fin q) (Fin q) ℝ) - b • Matrix.of (fun _ _ => 1))

theorem blockGramMatrix_apply (h q : ℕ) (a b : ℝ) (i j : Fin h × Fin q) :
    blockGramMatrix h q a b i j =
      if i.1 = j.1 then (if i.2 = j.2 then a else 0) - b else 0 := by
  simp only [blockGramMatrix, Matrix.kroneckerMap_apply, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.one_apply, Matrix.of_apply, smul_eq_mul, mul_one]
  split_ifs <;> simp_all

theorem blockGramMatrix_mulVec (h q : ℕ) (a b : ℝ) (x : Fin h × Fin q → ℝ)
    (i : Fin h × Fin q) :
    (blockGramMatrix h q a b).mulVec x i = a * x i - b * ∑ j, x (i.1, j) := by
  classical
  simp only [Matrix.mulVec, dotProduct, blockGramMatrix_apply, Fintype.sum_prod_type]
  simp only [ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true, ← Finset.mul_sum]

theorem blockGramMatrix_quadratic (h q : ℕ) (a b : ℝ) (x : Fin h × Fin q → ℝ) :
    ∑ i, x i * (blockGramMatrix h q a b).mulVec x i =
      a * (∑ i, (x i) ^ 2) - b * ∑ u : Fin h, (∑ v : Fin q, x (u, v)) ^ 2 := by
  classical
  simp_rw [blockGramMatrix_mulVec, mul_sub, Finset.sum_sub_distrib]
  congr 1
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  · rw [Fintype.sum_prod_type, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u hu
    simp only
    rw [← Finset.sum_mul]
    ring

theorem block_sum_sq_le (h q : ℕ) (x : Fin h × Fin q → ℝ) :
    (∑ u : Fin h, (∑ v : Fin q, x (u, v)) ^ 2) ≤ (q : ℝ) * ∑ i, (x i) ^ 2 := by
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro u hu
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin q))
    (fun _ => (1 : ℝ)) (fun v => x (u, v))
  simpa using hc

theorem blockGramMatrix_quadratic_bounds (h q : ℕ) (a b : ℝ) (hb : 0 ≤ b)
    (x : Fin h × Fin q → ℝ) :
    (a - b * q) * (∑ i, (x i) ^ 2) ≤ ∑ i, x i * (blockGramMatrix h q a b).mulVec x i ∧
      (∑ i, x i * (blockGramMatrix h q a b).mulVec x i) ≤ a * ∑ i, (x i) ^ 2 := by
  rw [blockGramMatrix_quadratic]
  have hs := mul_le_mul_of_nonneg_left (block_sum_sq_le h q x) hb
  have hp : 0 ≤ b * ∑ u : Fin h, (∑ v : Fin q, x (u, v)) ^ 2 :=
    mul_nonneg hb (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  constructor <;> nlinarith

end GeometricGaussianLHL
end

end BlockGram

section BlockSpectrum

/-!
## Exact characteristic polynomial of the Gram blocks

The rank-one characteristic-polynomial formula gives each block's two
eigenvalues. Taking the Kronecker product with an identity repeats their
multiplicities by the number of blocks.
-/

noncomputable section

open Polynomial
open scoped Kronecker

namespace GeometricGaussianLHL

theorem scalar_sub_ones_charpoly {q : ℕ} (hq : 1 ≤ q) (a b : ℝ) :
    (a • (1 : Matrix (Fin q) (Fin q) ℝ) - b • Matrix.of (fun _ _ => 1)).charpoly =
      (X - C a) ^ (q - 1) * (X - C (a - b * q)) := by
  classical
  have he : a • (1 : Matrix (Fin q) (Fin q) ℝ) - b • Matrix.of (fun _ _ => 1) =
      Matrix.vecMulVec (fun _ : Fin q => -b) (fun _ : Fin q => 1) - Matrix.scalar (Fin q) (-a) := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.of_apply,
      smul_eq_mul, mul_one, Matrix.vecMulVec_apply, Matrix.scalar_apply, Matrix.diagonal_apply]
    by_cases hij : i = j <;> simp [hij]
    ring
  rw [he, Matrix.charpoly_sub_scalar, Matrix.charpoly_vecMulVec]
  simp only [dotProduct, mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Polynomial.sub_comp, Polynomial.pow_comp, Polynomial.X_comp,
    Polynomial.smul_eq_C_mul, Polynomial.mul_comp, Polynomial.C_comp]
  have hpow : (X + C (-a)) ^ q = (X + C (-a)) ^ (q - 1) * (X + C (-a)) := by
    rw [← pow_succ, Nat.sub_add_cancel hq]
  rw [hpow]
  simp only [map_neg, map_mul, map_sub, map_natCast]
  ring

theorem charpoly_one_kronecker {h q : ℕ} (B : Matrix (Fin q) (Fin q) ℝ) :
    ((1 : Matrix (Fin h) (Fin h) ℝ) ⊗ₖ B).charpoly = B.charpoly ^ h := by
  classical
  have hmat : ((1 : Matrix (Fin h) (Fin h) ℝ) ⊗ₖ B).charmatrix =
      (1 : Matrix (Fin h) (Fin h) ℝ[X]) ⊗ₖ B.charmatrix := by
    ext i j
    simp only [Matrix.charmatrix_apply, Matrix.kroneckerMap_apply, Matrix.one_apply,
      Matrix.diagonal_apply, Prod.ext_iff]
    by_cases hu : i.1 = j.1 <;> by_cases hv : i.2 = j.2 <;> simp [hu, hv]
  rw [Matrix.charpoly, hmat, Matrix.det_kronecker]
  simp only [Matrix.det_one, one_pow, one_mul, Fintype.card_fin]
  rfl

theorem blockGramMatrix_charpoly {h q : ℕ} (hq : 1 ≤ q) (a b : ℝ) :
    (blockGramMatrix h q a b).charpoly =
      (X - C (a - b * q)) ^ h * (X - C a) ^ (h * (q - 1)) := by
  rw [blockGramMatrix, charpoly_one_kronecker, scalar_sub_ones_charpoly hq,
    mul_pow, ← pow_mul]
  rw [Nat.mul_comm (q - 1) h]
  exact mul_comm _ _

end GeometricGaussianLHL
end

end BlockSpectrum

section PowerTwoPermutation

/-!
## Signed coefficient permutations for powers of two

Multiplication by every power of the cyclotomic generator sends each power
basis vector to a signed basis vector. The permutation is addition modulo
the degree; the sign records the quotient by the degree.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Module NumberField
open Fin.NatCast

namespace GeometricGaussianLHL

def IsSignedPermutation {d : ℕ} (A : Matrix (Fin d) (Fin d) ℤ) : Prop :=
  ∃ e : Equiv.Perm (Fin d), ∃ signs : Fin d → ℤ,
    (∀ j, signs j = 1 ∨ signs j = -1) ∧
    ∀ i j, A i j = if i = e j then signs j else 0

variable (K : Type*) [Field K] [NumberField K] {k : ℕ}
  [IsCyclotomicExtension {2 ^ (k + 1)} ℚ K] {ζ : K}

omit [NumberField K] [IsCyclotomicExtension {2 ^ (k + 1)} ℚ K] in
theorem powerTwo_root_half (hζ : IsPrimitiveRoot ζ (2 ^ (k + 1))) :
    hζ.toInteger ^ (2 ^ k) = -1 := by
  apply NumberField.RingOfIntegers.coe_injective
  change ζ ^ (2 ^ k) = -1
  exact (hζ.pow (by positivity) (pow_succ 2 k)).eq_neg_one_of_two_right

theorem powerTwo_basis_multiply (hζ : IsPrimitiveRoot ζ (2 ^ (k + 1)))
    (a : ℕ) (j : Fin (2 ^ (k + 1)).totient) :
    hζ.toInteger ^ a * cyclotomicIntegralBasis K hζ j =
      ((-1 : ℤ) ^ ((a + j) / (2 ^ (k + 1)).totient)) •
        cyclotomicIntegralBasis K hζ (j + (a : Fin (2 ^ (k + 1)).totient)) := by
  have hd : (2 ^ (k + 1)).totient = 2 ^ k := by
    rw [Nat.totient_prime_pow_succ Nat.prime_two]
    norm_num
  have hhalf : hζ.toInteger ^ (2 ^ (k + 1)).totient = -1 := by
    rw [hd]
    exact powerTwo_root_half K hζ
  rw [cyclotomicIntegralBasis_eq_pow, cyclotomicIntegralBasis_eq_pow,
    ← pow_add, Fin.val_add, Fin.val_natCast, Nat.add_mod_mod, Nat.add_comm (j : ℕ) a]
  calc
    _ = hζ.toInteger ^ ((a + j) % (2 ^ (k + 1)).totient +
        (2 ^ (k + 1)).totient * ((a + j) / (2 ^ (k + 1)).totient)) := by
      rw [Nat.mod_add_div]
    _ = _ := by
      rw [pow_add, pow_mul, hhalf]
      simp only [zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one]
      ring

/-- The signed-permutation assertion following the prime-power basis geometry proposition.
-/
theorem powerTwo_multiplication_signedPermutation (hζ : IsPrimitiveRoot ζ (2 ^ (k + 1)))
    (a : ℕ) :
    IsSignedPermutation (Algebra.leftMulMatrix (cyclotomicIntegralBasis K hζ) (hζ.toInteger ^ a)) := by
  classical
  let d := (2 ^ (k + 1)).totient
  refine ⟨Equiv.addRight (a : Fin d), (fun j => (-1) ^ ((a + j) / d)), ?_, ?_⟩
  · intro j
    exact neg_one_pow_eq_or ℤ _
  · intro i j
    rw [Algebra.leftMulMatrix_eq_repr_mul, powerTwo_basis_multiply K hζ]
    simp only [map_smul, Basis.repr_self, Finsupp.smul_apply, smul_eq_mul,
      Finsupp.single_apply]
    change _ = if i = j + (a : Fin d) then (-1) ^ ((a + j) / d) else 0
    split_ifs <;> simp_all [d]

end GeometricGaussianLHL
end

end PowerTwoPermutation

section PrimePowerSpectrum

/-!
## Spectrum of the actual prime-power canonical Gram matrix

The characteristic polynomial records both eigenvalues and their algebraic
multiplicities, including the degenerate power-of-two case.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Module NumberField Polynomial

namespace GeometricGaussianLHL

variable (K : Type*) [Field K] [NumberField K]

theorem canonicalGram_reindex {ι ι' : Type*} [Fintype ι] [Fintype ι']
    (b : Basis ι ℤ (𝓞 K)) (e : ι ≃ ι') :
    canonicalGram K (b.reindex e) = Matrix.reindex e e (canonicalGram K b) := by
  ext i j
  simp only [canonicalGram, Basis.reindex_apply, Matrix.reindex_apply]
  rfl

variable {p k : ℕ} [Fact p.Prime]
  [IsCyclotomicExtension {p ^ (k + 1)} ℚ K] {ζ : K}

theorem primePowerGram_charpoly (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) :
    (canonicalGram K (cyclotomicIntegralBasis K hζ)).charpoly =
      (X - C (p ^ k : ℝ)) ^ (p ^ k) *
        (X - C (p ^ (k + 1) : ℝ)) ^ (p ^ k * (p - 2)) := by
  have hp : p.Prime := Fact.out
  have he := primePowerGram_blocks K hζ
  rw [canonicalGram_reindex] at he
  have hc := congrArg Matrix.charpoly he
  rw [Matrix.charpoly_reindex] at hc
  change (canonicalGram K (cyclotomicIntegralBasis K hζ)).charpoly =
    (blockGramMatrix (p ^ k) (p - 1) ((p ^ (k + 1) : ℕ) : ℝ) ((p ^ k : ℕ) : ℝ)).charpoly at hc
  rw [hc, blockGramMatrix_charpoly (show 1 ≤ p - 1 by have := hp.two_le; omega)]
  have heig : ((p ^ (k + 1) : ℕ) : ℝ) - ((p ^ k : ℕ) : ℝ) * (p - 1 : ℕ) = (p ^ k : ℝ) := by
    rw [pow_succ]
    push_cast
    rw [Nat.cast_sub hp.one_le]
    ring
  rw [heig]
  simp only [Nat.cast_pow, Nat.sub_sub, Nat.reduceAdd]

theorem primePowerGram_small_root (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) :
    (canonicalGram K (cyclotomicIntegralBasis K hζ)).charpoly.IsRoot (p ^ k : ℝ) := by
  have hp : p.Prime := Fact.out
  rw [Polynomial.IsRoot, primePowerGram_charpoly]
  simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C, sub_self, zero_pow (pow_ne_zero _ hp.ne_zero), zero_mul]

theorem primePowerGram_large_root (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) (hp2 : 2 < p) :
    (canonicalGram K (cyclotomicIntegralBasis K hζ)).charpoly.IsRoot (p ^ (k + 1) : ℝ) := by
  have hp : p.Prime := Fact.out
  rw [Polynomial.IsRoot, primePowerGram_charpoly]
  simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C, sub_self,
    zero_pow (mul_ne_zero (pow_ne_zero _ hp.ne_zero) (by omega : p - 2 ≠ 0)), mul_zero]

end GeometricGaussianLHL
end

end PrimePowerSpectrum

section PrimePowerNorms

/-!
## Singular-value bounds for the prime-power basis map

The bounds follow from the proved canonical Gram matrix and the finite
block quadratic form. The constants therefore apply to the actual
canonical coefficient isomorphism.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Module NumberField

namespace GeometricGaussianLHL

variable (K : Type*) [Field K] [NumberField K] {p k : ℕ} [Fact p.Prime]
  [IsCyclotomicExtension {p ^ (k + 1)} ℚ K] {ζ : K}

theorem primePowerCanonical_quadratic (hζ : IsPrimitiveRoot ζ (p ^ (k + 1)))
    (x : Euclidean (p ^ (k + 1)).totient) :
    ‖coefficientCanonicalEquiv K (cyclotomicIntegralBasis K hζ) x‖ ^ 2 =
      ((p ^ (k + 1) : ℕ) : ℝ) * ‖x‖ ^ 2 - ((p ^ k : ℕ) : ℝ) *
        ∑ u : Fin (p ^ k), (∑ v : Fin (p - 1), x (primePowerIndex p k (u, v))) ^ 2 := by
  rw [coefficientCanonicalEquiv_norm_sq_reindex K _ (primePowerIndex p k)]
  have hG := primePowerGram_blocks K hζ
  change canonicalGram K ((cyclotomicIntegralBasis K hζ).reindex (primePowerIndex p k).symm) =
    blockGramMatrix (p ^ k) (p - 1) ((p ^ (k + 1) : ℕ) : ℝ) ((p ^ k : ℕ) : ℝ) at hG
  rw [hG, blockGramMatrix_quadratic]
  rw [(primePowerIndex p k).sum_comp (fun i => (x i) ^ 2), EuclideanSpace.real_norm_sq_eq]

theorem primePowerCanonical_norm_sq_bounds (hζ : IsPrimitiveRoot ζ (p ^ (k + 1)))
    (x : Euclidean (p ^ (k + 1)).totient) :
    ((p ^ k : ℕ) : ℝ) * ‖x‖ ^ 2 ≤ ‖coefficientCanonicalEquiv K (cyclotomicIntegralBasis K hζ) x‖ ^ 2 ∧
      ‖coefficientCanonicalEquiv K (cyclotomicIntegralBasis K hζ) x‖ ^ 2 ≤
        ((p ^ (k + 1) : ℕ) : ℝ) * ‖x‖ ^ 2 := by
  have hp : p.Prime := Fact.out
  rw [coefficientCanonicalEquiv_norm_sq_reindex K _ (primePowerIndex p k)]
  have hG := primePowerGram_blocks K hζ
  change canonicalGram K ((cyclotomicIntegralBasis K hζ).reindex (primePowerIndex p k).symm) =
    blockGramMatrix (p ^ k) (p - 1) ((p ^ (k + 1) : ℕ) : ℝ) ((p ^ k : ℕ) : ℝ) at hG
  rw [hG]
  have h := blockGramMatrix_quadratic_bounds (p ^ k) (p - 1)
    ((p ^ (k + 1) : ℕ) : ℝ) ((p ^ k : ℕ) : ℝ) (by positivity) (fun i => x (primePowerIndex p k i))
  rw [(primePowerIndex p k).sum_comp (fun i => (x i) ^ 2), ← EuclideanSpace.real_norm_sq_eq] at h
  have he : ((p ^ (k + 1) : ℕ) : ℝ) - ((p ^ k : ℕ) : ℝ) * (p - 1 : ℕ) = ((p ^ k : ℕ) : ℝ) := by
    rw [pow_succ]
    push_cast
    rw [Nat.cast_sub hp.one_le]
    ring
  rw [he] at h
  exact h

theorem primePowerCanonical_norm_bounds (hζ : IsPrimitiveRoot ζ (p ^ (k + 1)))
    (x : Euclidean (p ^ (k + 1)).totient) :
    Real.sqrt (p ^ k) * ‖x‖ ≤ ‖coefficientCanonicalEquiv K (cyclotomicIntegralBasis K hζ) x‖ ∧
      ‖coefficientCanonicalEquiv K (cyclotomicIntegralBasis K hζ) x‖ ≤ Real.sqrt (p ^ (k + 1)) * ‖x‖ := by
  have h := primePowerCanonical_norm_sq_bounds K hζ x
  constructor
  · apply (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg x)) (norm_nonneg _)).mp
    simpa only [mul_pow, Real.sq_sqrt (show (0 : ℝ) ≤ p ^ k by positivity), Nat.cast_pow] using h.1
  · apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg x))).mp
    simpa only [mul_pow, Real.sq_sqrt (show (0 : ℝ) ≤ p ^ (k + 1) by positivity), Nat.cast_pow] using h.2

end GeometricGaussianLHL
end

end PrimePowerNorms

section PowerTwoGeometry

/-!
## Exact geometry of the power-of-two integral basis

All constants refer to the actual integral power basis and canonical norm.
The exponent is written `k + 1`, including `Q(ζ₂) = Q` at `k = 0`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Module NumberField

namespace GeometricGaussianLHL

variable (K : Type*) [Field K] [NumberField K] {k : ℕ}
  [IsCyclotomicExtension {2 ^ (k + 1)} ℚ K] {ζ : K}

theorem powerTwoGram_diagonal (hζ : IsPrimitiveRoot ζ (2 ^ (k + 1)))
    (i j : Fin (2 ^ (k + 1)).totient) :
    canonicalGram K (cyclotomicIntegralBasis K hζ) i j =
      if i = j then ((2 ^ (k + 1)).totient : ℝ) else 0 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hd : (2 ^ (k + 1)).totient = 2 ^ k := by
    rw [Nat.totient_prime_pow_succ Nat.prime_two]
    norm_num
  have hi : (i : ℕ) < 2 ^ k := by simpa only [hd] using i.isLt
  have hj : (j : ℕ) < 2 ^ k := by simpa only [hd] using j.isLt
  rw [primePowerGram_entry]
  by_cases heq : i = j
  · simp only [heq, ite_true]
  · have hmod : (i : ℕ) % 2 ^ k ≠ (j : ℕ) % 2 ^ k := by
      rw [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj]
      exact fun h => heq (Fin.ext h)
    simp only [heq, hmod, ite_false]

theorem powerTwoBasis_constants (hζ : IsPrimitiveRoot ζ (2 ^ (k + 1))) :
    basisAlpha K (cyclotomicIntegralBasis K hζ) = Real.sqrt (2 ^ (k + 1)).totient ∧
    basisBeta K (cyclotomicIntegralBasis K hζ) = 1 / Real.sqrt (2 ^ (k + 1)).totient ∧
    basisKappa K (cyclotomicIntegralBasis K hζ) = 1 ∧
    basisMu K (cyclotomicIntegralBasis K hζ) = 1 := by
  let b := cyclotomicIntegralBasis K hζ
  have hd : (0 : ℝ) < (2 ^ (k + 1)).totient := by
    exact_mod_cast Nat.totient_pos.mpr (pow_pos (by norm_num : 0 < (2 : ℕ)) _)
  have hG := powerTwoGram_diagonal K hζ
  have hκ : basisKappa K b = 1 := basisKappa_eq_one_of_diagonal K b hd hG
  have hμ : basisMu K b ≤ 1 := by
    rw [← hκ]
    exact basisMu_le_kappa K b (cyclotomicIntegralBasis_embedding_norm K hζ)
  have hμ' : 1 ≤ basisMu K b :=
    basisMu_ge_one K b 0 (cyclotomicIntegralBasis_one K hζ 0 rfl)
  exact ⟨basisAlpha_eq_sqrt_of_diagonal K b hd.le hG,
    basisBeta_eq_inv_sqrt_of_diagonal K b hd hG, hκ, le_antisymm hμ hμ'⟩

theorem powerTwoCanonical_norm (hζ : IsPrimitiveRoot ζ (2 ^ (k + 1)))
    (n : ℕ) (x : Euclidean (n * (2 ^ (k + 1)).totient)) :
    ‖powerCanonicalEquiv K (cyclotomicIntegralBasis K hζ) n x‖ =
      Real.sqrt (2 ^ (k + 1)).totient * ‖x‖ :=
  powerCanonicalEquiv_norm_of_diagonal K _ (by positivity) (powerTwoGram_diagonal K hζ) n x

end GeometricGaussianLHL
end

end PowerTwoGeometry

section PowerTwoDiscriminant

/-!
## The exact root discriminant of a power-of-two cyclotomic field

The actual canonical Gram matrix is `d I`. Its determinant is the absolute
field discriminant, hence the root discriminant is exactly `d`, including
`d = 1`. No discriminant formula is assumed as an extra hypothesis.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Module NumberField

namespace GeometricGaussianLHL

variable (K : Type*) [Field K] [NumberField K] {k : ℕ}
  [IsCyclotomicExtension {2 ^ (k + 1)} ℚ K] {ζ : K}

theorem powerTwo_abs_discr (hζ : IsPrimitiveRoot ζ (2 ^ (k + 1))) :
    |(NumberField.discr K : ℝ)| =
      ((2 ^ (k + 1)).totient : ℝ) ^ (2 ^ (k + 1)).totient := by
  classical
  let b := cyclotomicIntegralBasis K hζ
  have hG : canonicalGram K b = Matrix.diagonal (fun _ : Fin (2 ^ (k + 1)).totient =>
      ((2 ^ (k + 1)).totient : ℝ)) := by
    ext i j
    rw [powerTwoGram_diagonal K hζ, Matrix.diagonal_apply]
  rw [← canonicalGram_det K b, hG, Matrix.det_diagonal]
  simp

theorem powerTwo_rootDiscr (hζ : IsPrimitiveRoot ζ (2 ^ (k + 1))) :
    NumberField.rootDiscr K = ((2 ^ (k + 1)).totient : ℝ) := by
  let b := cyclotomicIntegralBasis K hζ
  have hd := integralBasis_dimension_pos K b
  have hdegree : finrank ℚ K = (2 ^ (k + 1)).totient := by
    rw [← NumberField.RingOfIntegers.rank, finrank_eq_card_basis b, Fintype.card_fin]
  rw [NumberField.rootDiscr_def, hdegree, Int.cast_abs, powerTwo_abs_discr K hζ]
  exact Real.pow_rpow_inv_natCast (Nat.cast_nonneg _) hd.ne'

end GeometricGaussianLHL
end

end PowerTwoDiscriminant

section PrimePowerGeometry

/-!
## Exact prime-power basis constants

The Gram computation, characteristic polynomial, and attaining vectors are
combined for the actual integral power basis. All prime conductors and the
degree-one power-of-two field are included.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Module NumberField

namespace GeometricGaussianLHL

def primePowerKappa (p : ℕ) : ℝ := if p = 2 then 1 else p

variable (K : Type*) [Field K] [NumberField K] {p k : ℕ} [Fact p.Prime]
  [IsCyclotomicExtension {p ^ (k + 1)} ℚ K] {ζ : K}

theorem primePowerBasis_beta (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) :
    basisBeta K (cyclotomicIntegralBasis K hζ) = 1 / Real.sqrt (p ^ k : ℝ) := by
  have hp : p.Prime := Fact.out
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  exact basisBeta_eq_inv_sqrt_of_gram_root K _ (by positivity)
    (primePowerGram_small_root K hζ) (fun x => (primePowerCanonical_norm_bounds K hζ x).1)

theorem primePowerBasis_alpha (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) :
    basisAlpha K (cyclotomicIntegralBasis K hζ) = Real.sqrt (primePowerKappa p * (p ^ k : ℝ)) := by
  have hp : p.Prime := Fact.out
  by_cases hp2 : p = 2
  · subst p
    rw [(powerTwoBasis_constants K hζ).1, Nat.totient_prime_pow_succ Nat.prime_two]
    simp [primePowerKappa]
  · have hp2' : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hp2)
    have he := basisAlpha_eq_sqrt_of_gram_root K (cyclotomicIntegralBasis K hζ)
      (by positivity : (0 : ℝ) ≤ p ^ (k + 1)) (primePowerGram_large_root K hζ hp2')
      (fun x => (primePowerCanonical_norm_bounds K hζ x).2)
    simpa only [primePowerKappa, ite_eq_right hp2, pow_succ, mul_comm] using he

theorem primePowerBasis_kappa (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) :
    basisKappa K (cyclotomicIntegralBasis K hζ) = Real.sqrt (primePowerKappa p) := by
  have hp : p.Prime := Fact.out
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hk : 0 ≤ primePowerKappa p := by unfold primePowerKappa; split_ifs <;> positivity
  have hh : Real.sqrt (p ^ k : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  rw [basisKappa, primePowerBasis_alpha, primePowerBasis_beta, Real.sqrt_mul hk]
  field_simp

/-- The four displayed constants of the prime-power basis geometry proposition, in the paper's
degree notation.
-/
theorem primePowerBasis_constants (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) :
    basisAlpha K (cyclotomicIntegralBasis K hζ) =
      Real.sqrt (primePowerKappa p * (p ^ (k + 1)).totient / (p - 1 : ℕ)) ∧
    basisBeta K (cyclotomicIntegralBasis K hζ) =
      Real.sqrt ((p - 1 : ℕ) / ((p ^ (k + 1)).totient : ℝ)) ∧
    basisKappa K (cyclotomicIntegralBasis K hζ) = Real.sqrt (primePowerKappa p) ∧
    basisMu K (cyclotomicIntegralBasis K hζ) ≤ Real.sqrt (primePowerKappa p) := by
  have hp : p.Prime := Fact.out
  have hq : ((p - 1 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (by have := hp.two_le; omega : p - 1 ≠ 0)
  have hh : (p ^ k : ℝ) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.ne_zero)
  have hd : ((p ^ (k + 1)).totient : ℝ) = (p ^ k : ℝ) * (p - 1 : ℕ) := by
    rw [Nat.totient_prime_pow_succ hp, Nat.cast_mul, Nat.cast_pow]
  refine ⟨?_, ?_, primePowerBasis_kappa K hζ, ?_⟩
  · rw [primePowerBasis_alpha, hd]
    congr 1
    field_simp
  · rw [primePowerBasis_beta, hd]
    have he : ((p - 1 : ℕ) : ℝ) / ((p ^ k : ℝ) * (p - 1 : ℕ)) = 1 / (p ^ k : ℝ) := by
      field_simp
    rw [he, Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one]
  · rw [← primePowerBasis_kappa K hζ]
    exact basisMu_le_kappa K _ (cyclotomicIntegralBasis_embedding_norm K hζ)

end GeometricGaussianLHL
end

end PrimePowerGeometry
