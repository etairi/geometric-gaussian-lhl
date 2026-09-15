import GeometricGaussianLHL.MatrixArithmetic

/-!
# Matrix square-root algorithms, accuracy, and costs

This module collects the following proof sections, in dependency order.
- A guard-bit budget for accumulating rounding errors (`DyadicErrorBudget`).
- Scalar residual of the multiplication-only inverse-square-root iteration (`SchulzScalar`).
- An executable matrix square-root iteration (`SchulzMatrixIteration`).
- Explicit precision for the scalar square-root iteration (`SchulzScalarPrecision`).
- Propagation of one matrix-iteration error (`SchulzMatrixPerturbation`).
- Explicit inverse accuracy of the scalar Schulz iteration (`SchulzInverseScalar`).
- Accuracy of the actual rational matrix iteration (`SchulzMatrixPrecision`).
- Integer matrices with a common denominator (`IntegerMatrixQuotient`).
- Executable iteration with rounding after every step (`RoundedSchulz`).
- Matrix inverse accuracy of the squared Schulz iterate (`SchulzInverseMatrix`).
- Uniform bounds for the exact square-root iteration (`SchulzMatrixBounds`).
- Magnitude bounds for integer matrix arithmetic (`IntegerArithmeticBounds`).
- Forward error of the bounded-precision rational iteration (`RoundedSchulzPrecision`).
- Computing the Schulz precision schedule (`SchulzScheduleCost`).
- Rounded inverse approximation (`RoundedSchulzInverse`).
- An executable rational square-root approximation (`RoundedSchulzSquareRoot`).
- Symmetric inverse approximation and stability of positive definiteness (`SymmetricSchulzInverse`).
- Stored-data implementation of the certified square-root algorithm (`StoredSchulz`).
- Rational square-root and inverse approximations for general positive inputs (`RationalSpectralApproximation`).
- Encoded length of the actual square-root output (`SchulzOutputSize`).
- Binary magnitude bounds for every stored iterate (`SchulzStateSize`).
- Stored-data inverse approximation (`StoredSchulzInverse`).
- The square-root iteration using stored integer numerators (`IntegerSchulz`).
- Encoded lengths of stored Schulz states (`StoredSchulzEncoding`).
- Arithmetic costs of the stored integer Schulz step (`IntegerSchulzCost`).
- Stored integer inverse approximation (`IntegerSchulzInverse`).
- Integer sizes throughout the stored iteration (`IntegerSchulzSize`).
- Converting arbitrary rational matrices to integer input data (`RationalMatrixDenominator`).
- Total costs along the actual stored Schulz trajectory (`StoredSchulzCost`).
- A binary input/output interface for the integer square-root algorithm (`EncodedIntegerSquareRoot`).
- Costs of complete normalized square-root and inverse approximation (`SchulzApproximationCost`).
- Polynomial costs of normalized numerical approximation (`SchulzApproximationBounds`).
- Normalized numerical approximation certificates (`SchulzApproximationCertificate`).
- Costed square-root and inverse algorithms for general rational input (`RationalSpectralCost`).
- Total costs from finite rational input (`RationalSpectralCostBounds`).
- Numerical certificates polynomial in the actual rational input encoding (`RationalSpectralCertificate`).
-/

section DyadicErrorBudget

/-!
## A guard-bit budget for accumulating rounding errors

With one error of size `2^(-p)` per step and amplification at most
`2^(2B+4)`, the forward error after `k` steps is bounded by
`2^((2B+5)k-p)`. The resulting precision budget is polynomial in `B`,
the number of iterations, and the requested output precision.
-/

namespace GeometricGaussianLHL

theorem dyadic_error_budget_le_one {p L k : ℕ} (h : L * k ≤ p) :
    (2 : ℝ) ^ (L * k) / (2 : ℝ) ^ p ≤ 1 := by
  apply (div_le_one (by positivity)).mpr
  exact pow_le_pow_right₀ (by norm_num) h

theorem dyadic_error_budget_step (p B k : ℕ) :
    (2 : ℝ) ^ (2 * B + 4) * ((2 : ℝ) ^ ((2 * B + 5) * k) / (2 : ℝ) ^ p) +
      1 / (2 : ℝ) ^ p ≤ (2 : ℝ) ^ ((2 * B + 5) * (k + 1)) / (2 : ℝ) ^ p := by
  rw [← mul_div_assoc, ← add_div]
  apply (div_le_div_iff_of_pos_right (by positivity)).mpr
  rw [show (2 * B + 5) * (k + 1) = (2 * B + 5) * k + (2 * B + 5) by ring,
    pow_add (2 : ℝ) ((2 * B + 5) * k) (2 * B + 5)]
  have hα : 1 ≤ (2 : ℝ) ^ (2 * B + 4) := one_le_pow₀ (by norm_num)
  have hβ : 1 ≤ (2 : ℝ) ^ ((2 * B + 5) * k) := one_le_pow₀ (by norm_num)
  have hfactor : (2 : ℝ) ^ (2 * B + 5) = (2 : ℝ) ^ (2 * B + 4) * 2 := by
    rw [show 2 * B + 5 = (2 * B + 4) + 1 by omega, pow_succ]
  rw [hfactor]
  nlinarith

theorem dyadic_error_budget_exact (t L k : ℕ) :
    (2 : ℝ) ^ (L * k) / (2 : ℝ) ^ (t + L * k) = 1 / (2 : ℝ) ^ t := by
  rw [pow_add]
  field_simp

end GeometricGaussianLHL

end DyadicErrorBudget

section SchulzScalar

/-!
## Scalar residual of the multiplication-only inverse-square-root iteration

Starting at `z = 1`, iterate `z ↦ z (3 - a z²) / 2`. For `0 ≤ a ≤ 1`,
the residual `1 - a z²` remains in `[0,1]` and is at most squared at each
step. Multiplication by `a` gives a square-root approximation. The generic
iteration is executable on rational inputs; these real estimates will be
used for the eigenvalues of a positive matrix.
-/

namespace GeometricGaussianLHL

def schulzInvSqrtStep {R : Type*} [Field R] (a z : R) : R := z * (3 - a * z ^ 2) / 2

def schulzInvSqrtIterate {R : Type*} [Field R] (a : R) : ℕ → R
  | 0 => 1
  | k + 1 => schulzInvSqrtStep a (schulzInvSqrtIterate a k)

theorem schulz_residual_step (a z : ℝ) :
    1 - a * (schulzInvSqrtStep a z) ^ 2 =
      (1 - a * z ^ 2) ^ 2 * (3 + (1 - a * z ^ 2)) / 4 := by
  unfold schulzInvSqrtStep
  ring

theorem schulz_step_nonneg {a z : ℝ} (hz : 0 ≤ z) (h : a * z ^ 2 ≤ 1) :
    0 ≤ schulzInvSqrtStep a z := by
  unfold schulzInvSqrtStep
  exact div_nonneg (mul_nonneg hz (by linarith)) (by norm_num)

theorem schulz_residual_bounds {e : ℝ} (he : 0 ≤ e) (he1 : e ≤ 1) :
    0 ≤ e ^ 2 * (3 + e) / 4 ∧ e ^ 2 * (3 + e) / 4 ≤ e ^ 2 := by
  constructor
  · positivity
  · have h := mul_le_mul_of_nonneg_left he1 (sq_nonneg e)
    nlinarith

theorem schulz_iterate_invariants {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (k : ℕ) :
    0 ≤ schulzInvSqrtIterate a k ∧
      0 ≤ 1 - a * (schulzInvSqrtIterate a k) ^ 2 ∧
      1 - a * (schulzInvSqrtIterate a k) ^ 2 ≤ 1 := by
  induction k with
  | zero =>
    simp only [schulzInvSqrtIterate, one_pow, mul_one]
    exact ⟨zero_le_one, sub_nonneg.mpr ha1, by linarith⟩
  | succ k ih =>
    have hb := schulz_residual_bounds ih.2.1 ih.2.2
    have hs : (1 - a * (schulzInvSqrtIterate a k) ^ 2) ^ 2 ≤ 1 := by
      nlinarith [sq_nonneg (1 - a * (schulzInvSqrtIterate a k) ^ 2)]
    refine ⟨schulz_step_nonneg ih.1 (by linarith [ih.2.1]), ?_, ?_⟩
    · simpa only [schulzInvSqrtIterate, schulz_residual_step] using hb.1
    · simpa only [schulzInvSqrtIterate, schulz_residual_step] using hb.2.trans hs

theorem schulz_residual_power_bound {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (k : ℕ) :
    1 - a * (schulzInvSqrtIterate a k) ^ 2 ≤ (1 - a) ^ (2 ^ k) := by
  induction k with
  | zero => simp [schulzInvSqrtIterate]
  | succ k ih =>
    have hi := schulz_iterate_invariants ha ha1 k
    calc
      _ = (1 - a * (schulzInvSqrtIterate a k) ^ 2) ^ 2 *
          (3 + (1 - a * (schulzInvSqrtIterate a k) ^ 2)) / 4 := schulz_residual_step _ _
      _ ≤ (1 - a * (schulzInvSqrtIterate a k) ^ 2) ^ 2 :=
        (schulz_residual_bounds hi.2.1 hi.2.2).2
      _ ≤ ((1 - a) ^ (2 ^ k)) ^ 2 := pow_le_pow_left₀ hi.2.1 ih 2
      _ = (1 - a) ^ (2 ^ (k + 1)) := by rw [← pow_mul, pow_succ]

theorem schulz_sqrt_error_le_residual {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (k : ℕ) :
    |a * schulzInvSqrtIterate a k - Real.sqrt a| ≤
      1 - a * (schulzInvSqrtIterate a k) ^ 2 := by
  let z := schulzInvSqrtIterate a k
  let e := 1 - a * z ^ 2
  have hi := schulz_iterate_invariants ha ha1 k
  have hz : 0 ≤ z := hi.1
  have he : 0 ≤ e := hi.2.1
  have he1 : e ≤ 1 := hi.2.2
  have hy : 0 ≤ a * z := mul_nonneg ha hz
  have hsq : (a * z) ^ 2 = a * (1 - e) := by dsimp only [e]; ring
  have hsqrt := Real.sq_sqrt ha
  have hsqrt0 := Real.sqrt_nonneg a
  have hsqrt1 : Real.sqrt a ≤ 1 := by simpa using Real.sqrt_le_sqrt ha1
  have hyupper : a * z ≤ Real.sqrt a := by
    apply (sq_le_sq₀ hy hsqrt0).mp
    rw [hsq, hsqrt]
    nlinarith [mul_nonneg ha he]
  have hylower : Real.sqrt a * (1 - e) ≤ a * z := by
    apply (sq_le_sq₀ (mul_nonneg hsqrt0 (by linarith)) hy).mp
    rw [mul_pow, hsqrt, hsq]
    apply mul_le_mul_of_nonneg_left _ ha
    nlinarith
  change |a * z - Real.sqrt a| ≤ e
  rw [abs_of_nonpos (sub_nonpos.mpr hyupper)]
  have h := mul_le_mul_of_nonneg_right hsqrt1 he
  nlinarith

end GeometricGaussianLHL

end SchulzScalar

section SchulzMatrixIteration

/-!
## An executable matrix square-root iteration

The mathematical iteration commutes with algebra homomorphisms and acts
entrywise on diagonal matrices. `materializeMatrix` constructs row vectors
inside a function-valued matrix, but compilation can repeat that construction
at each entry query. The `StoredSchulz` section supplies a data-valued recursion
for efficient evaluation of the rounded specification.

The current iteration uses exact rational arithmetic. A polynomial bit-time
claim additionally requires bounded-precision iteration and a cost proof.
-/

set_option backward.isDefEq.respectTransparency false

namespace GeometricGaussianLHL

def materializeMatrix {R : Type*} {r m : ℕ} (A : Matrix (Fin r) (Fin m) R) :
    Matrix (Fin r) (Fin m) R :=
  let rows := Vector.ofFn (fun i => Vector.ofFn (A i))
  fun i j => (rows.get i).get j

theorem materializeMatrix_eq {R : Type*} {r m : ℕ} (A : Matrix (Fin r) (Fin m) R) :
    materializeMatrix A = A := by
  ext i j
  simp [materializeMatrix, Vector.get]

def schulzInvSqrtMatrixStep {R : Type*} [Field R] {n : ℕ}
    (A Z : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R :=
  materializeMatrix ((1 / 2 : R) • (Z * (3 - A * Z ^ 2)))

def schulzInvSqrtMatrixIterate {R : Type*} [Field R] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R) : ℕ → Matrix (Fin n) (Fin n) R
  | 0 => 1
  | k + 1 => schulzInvSqrtMatrixStep A (schulzInvSqrtMatrixIterate A k)

theorem schulzInvSqrtMatrixStep_formula {R : Type*} [Field R] {n : ℕ}
    (A Z : Matrix (Fin n) (Fin n) R) :
    schulzInvSqrtMatrixStep A Z = (1 / 2 : R) • (Z * (3 - A * Z ^ 2)) :=
  materializeMatrix_eq _

theorem schulzInvSqrtMatrixIterate_algHom {R : Type*} [Field R] {n m : ℕ}
    (f : Matrix (Fin n) (Fin n) R →ₐ[R] Matrix (Fin m) (Fin m) R)
    (A : Matrix (Fin n) (Fin n) R) (k : ℕ) :
    f (schulzInvSqrtMatrixIterate A k) = schulzInvSqrtMatrixIterate (f A) k := by
  induction k with
  | zero => simp [schulzInvSqrtMatrixIterate]
  | succ k ih =>
    simp only [schulzInvSqrtMatrixIterate, schulzInvSqrtMatrixStep_formula,
      map_smul, map_mul, map_sub, map_ofNat, map_pow, ih]

theorem schulzInvSqrtMatrixIterate_diagonal {R : Type*} [Field R] {n : ℕ}
    (v : Fin n → R) (k : ℕ) :
    schulzInvSqrtMatrixIterate (Matrix.diagonal v) k =
      Matrix.diagonal (fun i => schulzInvSqrtIterate (v i) k) := by
  induction k with
  | zero => simp [schulzInvSqrtMatrixIterate, schulzInvSqrtIterate]
  | succ k ih =>
    rw [schulzInvSqrtMatrixIterate, schulzInvSqrtMatrixStep_formula, ih,
      Matrix.diagonal_pow, Matrix.diagonal_mul_diagonal]
    rw [show (3 : Matrix (Fin n) (Fin n) R) = Matrix.diagonal (fun _ => (3 : R)) from
      (Matrix.diagonal_natCast 3).symm]
    rw [Matrix.diagonal_sub, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_smul]
    congr 1
    funext i
    simp only [Pi.smul_apply, Pi.pow_apply, smul_eq_mul, schulzInvSqrtIterate, schulzInvSqrtStep]
    ring

theorem schulzInvSqrtMatrixIterate_rat_cast {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (k : ℕ) :
    (schulzInvSqrtMatrixIterate A k).map (fun q : ℚ => (q : ℝ)) =
      schulzInvSqrtMatrixIterate (A.map (fun q : ℚ => (q : ℝ))) k := by
  induction k with
  | zero => simp [schulzInvSqrtMatrixIterate, Matrix.map_one]
  | succ k ih =>
    simp only [schulzInvSqrtMatrixIterate, schulzInvSqrtMatrixStep_formula]
    have hs (M : Matrix (Fin n) (Fin n) ℚ) :
        ((1 / 2 : ℚ) • M).map (fun q : ℚ => (q : ℝ)) =
          (1 / 2 : ℝ) • M.map (fun q : ℚ => (q : ℝ)) := by
      ext i j
      simp
    rw [hs]
    congr 1
    change (Rat.castHom ℝ).mapMatrix _ = _
    simp only [map_mul, map_sub, map_ofNat, map_pow]
    change (schulzInvSqrtMatrixIterate A k).map (fun q : ℚ => (q : ℝ)) *
      (3 - A.map (fun q : ℚ => (q : ℝ)) *
        ((schulzInvSqrtMatrixIterate A k).map (fun q : ℚ => (q : ℝ))) ^ 2) = _
    rw [ih]

end GeometricGaussianLHL

end SchulzMatrixIteration

section SchulzScalarPrecision

/-!
## Explicit precision for the scalar square-root iteration

If `2^(-B) ≤ a ≤ 1`, then `t+B` iterations suffice for absolute square-root
error at most `2^(-t)`. This conservative budget is linear in precision and
the lower-bound exponent. The proof uses a finite Bernoulli estimate, with
no logarithmic or asymptotic convergence assumptions. It is an exact-
arithmetic result; controlling intermediate bit lengths is a separate step.
-/

namespace GeometricGaussianLHL

theorem one_sub_pow_mul_linear_le_one {a : ℝ} (ha1 : a ≤ 1) (N : ℕ) :
    (1 - a) ^ N * (1 + (N : ℝ) * a) ≤ 1 := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hf : (1 - a) * (1 + ((N + 1 : ℕ) : ℝ) * a) ≤ 1 + (N : ℝ) * a := by
      push_cast
      have h := mul_nonneg (show 0 ≤ (N : ℝ) + 1 by positivity) (sq_nonneg a)
      nlinarith
    calc
      _ = (1 - a) ^ N * ((1 - a) * (1 + ((N + 1 : ℕ) : ℝ) * a)) := by
        rw [pow_succ]
        ring
      _ ≤ (1 - a) ^ N * (1 + (N : ℝ) * a) :=
        mul_le_mul_of_nonneg_left hf (pow_nonneg (sub_nonneg.mpr ha1) _)
      _ ≤ 1 := ih

theorem one_sub_pow_le_reciprocal {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (N : ℕ) :
    (1 - a) ^ N ≤ 1 / (1 + (N : ℝ) * a) := by
  apply (le_div_iff₀ (by positivity)).mpr
  exact one_sub_pow_mul_linear_le_one ha1 N

theorem schulz_sqrt_prescribed_error (t B : ℕ) {a : ℝ}
    (ha : 1 / (2 : ℝ) ^ B ≤ a) (ha1 : a ≤ 1) :
    |a * schulzInvSqrtIterate a (t + B) - Real.sqrt a| ≤ 1 / (2 : ℝ) ^ t := by
  have ha0 : 0 ≤ a := (by positivity : (0 : ℝ) ≤ 1 / (2 : ℝ) ^ B).trans ha
  have hp := one_sub_pow_le_reciprocal ha0 ha1 (2 ^ (t + B))
  norm_num only [Nat.cast_pow, Nat.cast_ofNat] at hp
  have hN : (2 : ℝ) ^ t ≤ (2 : ℝ) ^ (t + B) * a := by
    calc
      _ = (2 : ℝ) ^ (t + B) * (1 / (2 : ℝ) ^ B) := by rw [pow_add]; field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left ha (by positivity)
  calc
    _ ≤ 1 - a * (schulzInvSqrtIterate a (t + B)) ^ 2 :=
      schulz_sqrt_error_le_residual ha0 ha1 _
    _ ≤ (1 - a) ^ (2 ^ (t + B)) := schulz_residual_power_bound ha0 ha1 _
    _ ≤ 1 / (1 + (2 : ℝ) ^ (t + B) * a) := hp
    _ ≤ 1 / (2 : ℝ) ^ t := one_div_le_one_div_of_le (by positivity) (by linarith)

theorem schulzInvSqrtIterate_rat_cast (a : ℚ) (k : ℕ) :
    ((schulzInvSqrtIterate a k : ℚ) : ℝ) = schulzInvSqrtIterate (a : ℝ) k := by
  induction k with
  | zero => simp [schulzInvSqrtIterate]
  | succ k ih => simp [schulzInvSqrtIterate, schulzInvSqrtStep, ih]

theorem schulz_rational_sqrt_prescribed_error (t B : ℕ) (a : ℚ)
    (ha : 1 / (2 : ℚ) ^ B ≤ a) (ha1 : a ≤ 1) :
    |((a * schulzInvSqrtIterate a (t + B) : ℚ) : ℝ) - Real.sqrt (a : ℝ)| ≤
      1 / (2 : ℝ) ^ t := by
  rw [Rat.cast_mul, schulzInvSqrtIterate_rat_cast]
  apply schulz_sqrt_prescribed_error t B
  · have h := (Rat.cast_le (K := ℝ)).mpr ha
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat] using h
  · exact_mod_cast ha1

end GeometricGaussianLHL

end SchulzScalarPrecision

section SchulzMatrixPerturbation

/-!
## Propagation of one matrix-iteration error

The estimate is valid for arbitrary, possibly noncommuting perturbed
iterates. It is deliberately conservative and controls absolute forward
error on a bounded ball; it makes no floating-point stability claim.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open scoped Matrix.Norms.L2Operator

namespace GeometricGaussianLHL

theorem schulz_polynomial_lipschitz {R : Type*} [SeminormedRing R]
    (A W Z : R) {M : ℝ} (hthree : ‖(3 : R)‖ ≤ (3 : ℝ))
    (hA : ‖A‖ ≤ 1) (hW : ‖W‖ ≤ M) (hZ : ‖Z‖ ≤ M) :
    ‖W * (3 - A * W ^ 2) - Z * (3 - A * Z ^ 2)‖ ≤
      (3 + 3 * M ^ 2) * ‖W - Z‖ := by
  have hfirst := norm_mul_le_of_le (le_refl ‖W - Z‖) hthree
  have h₁ := norm_mul_le_of_le
    (norm_mul_le_of_le (norm_mul_le_of_le (le_refl ‖W - Z‖) hA) hW) hW
  have h₂ := norm_mul_le_of_le
    (norm_mul_le_of_le (norm_mul_le_of_le hZ hA) (le_refl ‖W - Z‖)) hW
  have h₃ := norm_mul_le_of_le
    (norm_mul_le_of_le (norm_mul_le_of_le hZ hA) hZ) (le_refl ‖W - Z‖)
  have hsum := (norm_add_le ((W - Z) * A * W * W + Z * A * (W - Z) * W)
    (Z * A * Z * (W - Z))).trans
      (add_le_add (norm_add_le ((W - Z) * A * W * W) (Z * A * (W - Z) * W)) le_rfl)
  have heq : W * (3 - A * W ^ 2) - Z * (3 - A * Z ^ 2) =
      (W - Z) * 3 -
        (((W - Z) * A * W * W + Z * A * (W - Z) * W) + Z * A * Z * (W - Z)) := by
    noncomm_ring
  rw [heq]
  have hsub := norm_sub_le ((W - Z) * 3)
    (((W - Z) * A * W * W + Z * A * (W - Z) * W) + Z * A * Z * (W - Z))
  nlinarith

theorem schulzMatrix_step_lipschitz {n : ℕ}
    (A W Z : Matrix (Fin n) (Fin n) ℝ) {M : ℝ}
    (hA : ‖A‖ ≤ 1) (hW : ‖W‖ ≤ M) (hZ : ‖Z‖ ≤ M) :
    ‖schulzInvSqrtMatrixStep A W - schulzInvSqrtMatrixStep A Z‖ ≤
      ((3 + 3 * M ^ 2) / 2) * ‖W - Z‖ := by
  have hthree : ‖(3 : Matrix (Fin n) (Fin n) ℝ)‖ ≤ (3 : ℝ) := by
    rw [show (3 : Matrix (Fin n) (Fin n) ℝ) = Matrix.diagonal (fun _ => (3 : ℝ)) from
      (Matrix.diagonal_natCast 3).symm, Matrix.l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg (by norm_num)).mpr
    intro i
    norm_num
  rw [schulzInvSqrtMatrixStep_formula, schulzInvSqrtMatrixStep_formula, ← smul_sub,
    norm_smul]
  norm_num only [Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have h := schulz_polynomial_lipschitz A W Z hthree hA hW hZ
  nlinarith

theorem schulzMatrix_step_dyadic_lipschitz {n : ℕ} (B : ℕ)
    (A W Z : Matrix (Fin n) (Fin n) ℝ)
    (hA : ‖A‖ ≤ 1) (hW : ‖W‖ ≤ (2 : ℝ) ^ B + 1)
    (hZ : ‖Z‖ ≤ (2 : ℝ) ^ B + 1) :
    ‖schulzInvSqrtMatrixStep A W - schulzInvSqrtMatrixStep A Z‖ ≤
      (2 : ℝ) ^ (2 * B + 4) * ‖W - Z‖ := by
  have h1 : 1 ≤ (2 : ℝ) ^ B := one_le_pow₀ (by norm_num)
  have hc : (3 + 3 * ((2 : ℝ) ^ B + 1) ^ 2) / 2 ≤ (2 : ℝ) ^ (2 * B + 4) := by
    rw [pow_add, show 2 * B = B * 2 by omega, pow_mul]
    norm_num
    nlinarith [sq_nonneg ((2 : ℝ) ^ B - 1)]
  exact (schulzMatrix_step_lipschitz A W Z hA hW hZ).trans
    (mul_le_mul_of_nonneg_right hc (norm_nonneg _))

end GeometricGaussianLHL
end

end SchulzMatrixPerturbation

section SchulzInverseScalar

/-!
## Explicit inverse accuracy of the scalar Schulz iteration

Squaring the inverse-square-root iterate approximates the inverse itself.
For `2^(-B) ≤ a ≤ 1`, `t+2B` exact-arithmetic iterations suffice for absolute
inverse error at most `2^(-t)`. The residual estimate is reusable independently
of the square-root error bound. Rounding and arithmetic costs remain separate.
-/

namespace GeometricGaussianLHL

theorem schulz_residual_prescribed_error (t B : ℕ) {a : ℝ}
    (ha : 1 / (2 : ℝ) ^ B ≤ a) (ha1 : a ≤ 1) :
    1 - a * (schulzInvSqrtIterate a (t + B)) ^ 2 ≤ 1 / (2 : ℝ) ^ t := by
  have ha0 : 0 ≤ a := (by positivity : (0 : ℝ) ≤ 1 / (2 : ℝ) ^ B).trans ha
  have hp := one_sub_pow_le_reciprocal ha0 ha1 (2 ^ (t + B))
  norm_num only [Nat.cast_pow, Nat.cast_ofNat] at hp
  have hN : (2 : ℝ) ^ t ≤ (2 : ℝ) ^ (t + B) * a := by
    calc
      _ = (2 : ℝ) ^ (t + B) * (1 / (2 : ℝ) ^ B) := by rw [pow_add]; field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left ha (by positivity)
  calc
    _ ≤ (1 - a) ^ (2 ^ (t + B)) := schulz_residual_power_bound ha0 ha1 _
    _ ≤ 1 / (1 + (2 : ℝ) ^ (t + B) * a) := hp
    _ ≤ 1 / (2 : ℝ) ^ t := one_div_le_one_div_of_le (by positivity) (by linarith)

theorem schulz_inverse_prescribed_error (t B : ℕ) {a : ℝ}
    (ha : 1 / (2 : ℝ) ^ B ≤ a) (ha1 : a ≤ 1) :
    |(schulzInvSqrtIterate a (t + B + B)) ^ 2 - a⁻¹| ≤ 1 / (2 : ℝ) ^ t := by
  have ha0 : 0 < a := (by positivity : (0 : ℝ) < 1 / (2 : ℝ) ^ B).trans_le ha
  let z := schulzInvSqrtIterate a (t + B + B)
  have he : 0 ≤ 1 - a * z ^ 2 := (schulz_iterate_invariants ha0.le ha1 _).2.1
  have hid : a * (z ^ 2 - a⁻¹) = -(1 - a * z ^ 2) := by
    rw [mul_sub, mul_inv_cancel₀ ha0.ne']
    ring
  have habs : a * |z ^ 2 - a⁻¹| = 1 - a * z ^ 2 := by
    calc
      _ = |a| * |z ^ 2 - a⁻¹| := congrArg (fun c => c * |z ^ 2 - a⁻¹|) (abs_of_pos ha0).symm
      _ = |a * (z ^ 2 - a⁻¹)| := (abs_mul _ _).symm
      _ = _ := by rw [hid, abs_neg, abs_of_nonneg he]
  have hr : 1 - a * z ^ 2 ≤ 1 / (2 : ℝ) ^ (t + B) :=
    schulz_residual_prescribed_error (t + B) B ha ha1
  have hscaled : (1 / (2 : ℝ) ^ B) * |z ^ 2 - a⁻¹| ≤
      (1 / (2 : ℝ) ^ B) * (1 / (2 : ℝ) ^ t) := by
    calc
      _ ≤ a * |z ^ 2 - a⁻¹| := mul_le_mul_of_nonneg_right ha (abs_nonneg _)
      _ = 1 - a * z ^ 2 := habs
      _ ≤ 1 / (2 : ℝ) ^ (t + B) := hr
      _ = _ := by rw [pow_add]; field_simp
  exact (mul_le_mul_iff_right₀ (by positivity : (0 : ℝ) < 1 / (2 : ℝ) ^ B)).mp hscaled

theorem schulz_rational_inverse_prescribed_error (t B : ℕ) (a : ℚ)
    (ha : 1 / (2 : ℚ) ^ B ≤ a) (ha1 : a ≤ 1) :
    |(((schulzInvSqrtIterate a (t + B + B)) ^ 2 : ℚ) : ℝ) - (a : ℝ)⁻¹| ≤
      1 / (2 : ℝ) ^ t := by
  rw [Rat.cast_pow, schulzInvSqrtIterate_rat_cast]
  apply schulz_inverse_prescribed_error t B
  · have h := (Rat.cast_le (K := ℝ)).mpr ha
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat] using h
  · exact_mod_cast ha1

end GeometricGaussianLHL

end SchulzInverseScalar

section SchulzMatrixPrecision

/-!
## Accuracy of the actual rational matrix iteration

The spectral theorem transfers the proved scalar residual bound to the
Euclidean operator norm. For a positive matrix with eigenvalues in
`[2^(-B),1]`, `t+B` exact-arithmetic iterations approximate its actual
positive square root to absolute operator error `2^(-t)`.

The last theorem concerns the executable rational iteration after mapping
its output to real matrices. It does not replace bit complexity by an
iteration count: bounded-precision iteration and its cost are still needed.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open scoped MatrixOrder Matrix.Norms.L2Operator

namespace GeometricGaussianLHL

theorem schulzMatrix_spectral_form {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsHermitian) (k : ℕ) :
    schulzInvSqrtMatrixIterate A k =
      Unitary.conjStarAlgAut ℝ _ hA.eigenvectorUnitary
        (Matrix.diagonal (fun i => schulzInvSqrtIterate (hA.eigenvalues i) k)) := by
  let f := Unitary.conjStarAlgAut ℝ _ hA.eigenvectorUnitary
  have hs : A = f (Matrix.diagonal hA.eigenvalues) := hA.spectral_theorem
  calc
    _ = schulzInvSqrtMatrixIterate (f (Matrix.diagonal hA.eigenvalues)) k :=
      congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => schulzInvSqrtMatrixIterate M k) hs
    _ = f (schulzInvSqrtMatrixIterate (Matrix.diagonal hA.eigenvalues) k) :=
      (schulzInvSqrtMatrixIterate_algHom f.toAlgEquiv.toAlgHom _ k).symm
    _ = _ := congrArg f (schulzInvSqrtMatrixIterate_diagonal hA.eigenvalues k)

theorem schulzTarget_spectral_form {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosSemidef) :
    CFC.sqrt A = Unitary.conjStarAlgAut ℝ _ hA.isHermitian.eigenvectorUnitary
      (Matrix.diagonal (fun i => Real.sqrt (hA.isHermitian.eigenvalues i))) := by
  rw [CFC.sqrt_eq_real_sqrt A hA.nonneg, cfcₙ_eq_cfc, hA.isHermitian.cfc_eq]
  rfl

theorem schulzMatrix_sqrt_operator_error {n : ℕ} (t B : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosSemidef)
    (hlo : ∀ i, 1 / (2 : ℝ) ^ B ≤ hA.isHermitian.eigenvalues i)
    (hhi : ∀ i, hA.isHermitian.eigenvalues i ≤ 1) :
    ‖(Matrix.toEuclideanLin (A * schulzInvSqrtMatrixIterate A (t + B))).toContinuousLinearMap -
      (Matrix.toEuclideanLin (CFC.sqrt A)).toContinuousLinearMap‖ ≤ 1 / (2 : ℝ) ^ t := by
  let f := Unitary.conjStarAlgAut ℝ _ hA.isHermitian.eigenvectorUnitary
  have hs : A = f (Matrix.diagonal hA.isHermitian.eigenvalues) := hA.isHermitian.spectral_theorem
  have hn (M : Matrix (Fin n) (Fin n) ℝ) : ‖f M‖ = ‖M‖ := by
    simp only [f, Unitary.conjStarAlgAut_apply, ← Unitary.coe_star, CStarRing.norm_mul_coe_unitary,
      CStarRing.norm_coe_unitary_mul]
  have herr : ‖A * schulzInvSqrtMatrixIterate A (t + B) - CFC.sqrt A‖ ≤ 1 / (2 : ℝ) ^ t := by
    rw [schulzMatrix_spectral_form A hA.isHermitian, schulzTarget_spectral_form A hA]
    change ‖A * f (Matrix.diagonal (fun i => schulzInvSqrtIterate (hA.isHermitian.eigenvalues i) (t + B))) -
      f (Matrix.diagonal (fun i => Real.sqrt (hA.isHermitian.eigenvalues i)))‖ ≤ _
    rw (occs := .pos [1]) [hs]
    rw [← map_mul, ← map_sub, hn, Matrix.diagonal_mul_diagonal, Matrix.diagonal_sub,
      Matrix.l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    simpa only [Real.norm_eq_abs] using schulz_sqrt_prescribed_error t B (hlo i) (hhi i)
  change ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
    (A * schulzInvSqrtMatrixIterate A (t + B) - CFC.sqrt A)‖ ≤ _ at herr
  have hc (M : Matrix (Fin n) (Fin n) ℝ) :
      Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) M =
        (Matrix.toEuclideanLin M).toContinuousLinearMap := by
    ext x i
    rfl
  simpa only [map_sub, hc] using herr

theorem schulzMatrix_rat_sqrt_operator_error {n : ℕ} (t B : ℕ)
    (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : (A.map (fun q : ℚ => (q : ℝ))).PosSemidef)
    (hlo : ∀ i, 1 / (2 : ℝ) ^ B ≤ hA.isHermitian.eigenvalues i)
    (hhi : ∀ i, hA.isHermitian.eigenvalues i ≤ 1) :
    ‖(Matrix.toEuclideanLin ((A * schulzInvSqrtMatrixIterate A (t + B)).map
        (fun q : ℚ => (q : ℝ)))).toContinuousLinearMap -
      (Matrix.toEuclideanLin (CFC.sqrt (A.map (fun q : ℚ => (q : ℝ))))).toContinuousLinearMap‖ ≤
      1 / (2 : ℝ) ^ t := by
  have he : (A * schulzInvSqrtMatrixIterate A (t + B)).map (fun q : ℚ => (q : ℝ)) =
      A.map (fun q : ℚ => (q : ℝ)) *
        schulzInvSqrtMatrixIterate (A.map (fun q : ℚ => (q : ℝ))) (t + B) := by
    change (Rat.castHom ℝ).mapMatrix (A * schulzInvSqrtMatrixIterate A (t + B)) = _
    rw [map_mul]
    change A.map (fun q : ℚ => (q : ℝ)) *
      (schulzInvSqrtMatrixIterate A (t + B)).map (fun q : ℚ => (q : ℝ)) = _
    rw [schulzInvSqrtMatrixIterate_rat_cast]
  rw [he]
  exact schulzMatrix_sqrt_operator_error t B _ hA hlo hhi

end GeometricGaussianLHL
end

end SchulzMatrixPrecision

section IntegerMatrixQuotient

/-!
## Integer matrices with a common denominator

These identities express the rational square-root iteration using integer
matrix arithmetic and division by positive integer denominators. They are
the refinement interface for an integer implementation; no runtime bound
is assumed by the interface.
-/

set_option backward.isDefEq.respectTransparency false

namespace GeometricGaussianLHL

theorem schulz_scaled_step {n : ℕ} (a d : ℚ) (ha : a ≠ 0) (hd : d ≠ 0)
    (X N : Matrix (Fin n) (Fin n) ℚ) :
    (1 / 2 : ℚ) • ((d⁻¹ • N) * (3 - (a⁻¹ • X) * (d⁻¹ • N) ^ 2)) =
      (1 / (2 * a * d ^ 3)) • (N * ((3 * a * d ^ 2) • 1 - X * N ^ 2)) := by
  rw [show (3 : Matrix (Fin n) (Fin n) ℚ) = (3 : ℚ) • 1 by
    ext i j
    by_cases h : i = j <;> simp [Matrix.ofNat_apply, h]]
  simp only [smul_pow, Matrix.smul_mul, Matrix.mul_smul, mul_sub, mul_one]
  match_scalars <;> field_simp

def integerSchulzNumerator {n : ℕ} (a d : ℕ)
    (X N : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℤ :=
  N * ((3 * (a : ℤ) * (d : ℤ) ^ 2) • 1 - X * N ^ 2)

theorem integerSchulzNumerator_cast {n : ℕ} (a d : ℕ)
    (X N : Matrix (Fin n) (Fin n) ℤ) :
    integerMatrixCast (integerSchulzNumerator a d X N) =
      integerMatrixCast N *
        ((3 * (a : ℚ) * (d : ℚ) ^ 2) • 1 - integerMatrixCast X * integerMatrixCast N ^ 2) := by
  unfold integerSchulzNumerator
  have hm (Y Z : Matrix (Fin n) (Fin n) ℤ) :
      integerMatrixCast (Y * Z) = integerMatrixCast Y * integerMatrixCast Z :=
    map_mul _ _ _
  rw [hm]
  congr 1
  change (Int.castRingHom ℚ).mapMatrix _ = _
  rw [map_sub]
  change integerMatrixCast ((3 * (a : ℤ) * (d : ℤ) ^ 2) • 1) - _ = _
  rw [integerMatrixCast_smul]
  simp [integerMatrixCast, map_mul, map_pow]

theorem integerSchulzNumerator_step {n : ℕ} (a d : ℕ)
    (ha : 0 < a) (hd : 0 < d) (X N : Matrix (Fin n) (Fin n) ℤ) :
    schulzInvSqrtMatrixStep (integerMatrixQuotient a X) (integerMatrixQuotient d N) =
      integerMatrixQuotient (2 * a * d ^ 3) (integerSchulzNumerator a d X N) := by
  rw [schulzInvSqrtMatrixStep_formula]
  simp only [integerMatrixQuotient]
  rw [schulz_scaled_step (a : ℚ) (d : ℚ) (by positivity) (by positivity),
    integerSchulzNumerator_cast]
  simp [one_div]

theorem dyadicNumerator_int_quotient (q a : ℕ) (z : ℤ) :
    dyadicNumerator q ((z : ℚ) / a) =
      (z * (2 : ℤ) ^ q) / (a : ℤ) := by
  unfold dyadicNumerator
  rw [show (z : ℚ) / a * 2 ^ q = ((z * (2 : ℤ) ^ q : ℤ) : ℚ) / a by push_cast; ring]
  exact Rat.floor_intCast_div_natCast _ _

theorem integerMatrixQuotient_mul {n : ℕ} (a d : ℕ)
    (X N : Matrix (Fin n) (Fin n) ℤ) :
    integerMatrixQuotient a X * integerMatrixQuotient d N =
      integerMatrixQuotient (a * d) (X * N) := by
  simp [integerMatrixQuotient, integerMatrixCast, smul_smul, map_mul, mul_comm]

theorem integerMatrixQuotient_identity {n : ℕ} (d : ℕ) (hd : 0 < d) :
    integerMatrixQuotient d ((d : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ)) = 1 := by
  rw [integerMatrixQuotient, integerMatrixCast_smul]
  simp [integerMatrixCast, smul_smul, Nat.ne_of_gt hd]

theorem integerMatrixQuotient_round {n : ℕ} (q a : ℕ)
    (X : Matrix (Fin n) (Fin n) ℤ) :
    integerMatrixQuotient (2 ^ q) (X.map (fun z => (z * (2 : ℤ) ^ q) / (a : ℤ))) =
      dyadicRoundMatrix q (integerMatrixQuotient a X) := by
  ext i j
  rw [integerMatrixQuotient_apply]
  simp only [Matrix.map_apply, Nat.cast_pow, Nat.cast_ofNat, dyadicRoundMatrix,
    dyadicRoundRat, integerMatrixQuotient_apply, dyadicNumerator_int_quotient]

theorem dyadicNumerator_schulz_denominator (q a : ℕ) (z : ℤ) :
    dyadicNumerator q ((z : ℚ) / (2 * a * (2 ^ q) ^ 3 : ℕ)) =
      z / (2 * a * (2 ^ q) ^ 2 : ℕ) := by
  rw [dyadicNumerator_int_quotient]
  push_cast
  rw [show (2 : ℤ) * a * (2 ^ q) ^ 3 = (2 * a * (2 ^ q) ^ 2) * 2 ^ q by ring]
  exact Int.mul_ediv_mul_of_pos_left _ _ (by positivity)

end GeometricGaussianLHL

end IntegerMatrixQuotient

section RoundedSchulz

/-!
## Executable iteration with rounding after every step

The parameter `p` is the operator-precision budget. Each matrix entry is
rounded to `p+n` fractional binary places. This function-valued specification
is identified with a data-valued implementation in the `StoredSchulz` section.
The lemmas below identify rational operations with their real interpretation
and bound the local rounding error.
-/

set_option backward.isDefEq.respectTransparency false

open scoped Matrix.Norms.L2Operator

namespace GeometricGaussianLHL

def roundedSchulzMatrixStep {n : ℕ} (p : ℕ)
    (A Z : Matrix (Fin n) (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ :=
  materializeMatrix (dyadicRoundMatrix (p + n) (schulzInvSqrtMatrixStep A Z))

def roundedSchulzMatrixIterate {n : ℕ} (p : ℕ)
    (A : Matrix (Fin n) (Fin n) ℚ) : ℕ → Matrix (Fin n) (Fin n) ℚ
  | 0 => 1
  | k + 1 => roundedSchulzMatrixStep p A (roundedSchulzMatrixIterate p A k)

theorem euclideanMatrix_norm_sub_CLM {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) :
    ‖A - B‖ = ‖(Matrix.toEuclideanLin A).toContinuousLinearMap -
      (Matrix.toEuclideanLin B).toContinuousLinearMap‖ := by
  rw [Matrix.l2_opNorm_def, map_sub]
  rfl

theorem schulzMatrixStep_rat_cast {n : ℕ} (A Z : Matrix (Fin n) (Fin n) ℚ) :
    (schulzInvSqrtMatrixStep A Z).map (fun q : ℚ => (q : ℝ)) =
      schulzInvSqrtMatrixStep (A.map (fun q : ℚ => (q : ℝ)))
        (Z.map (fun q : ℚ => (q : ℝ))) := by
  simp only [schulzInvSqrtMatrixStep_formula]
  have hs (M : Matrix (Fin n) (Fin n) ℚ) :
      ((1 / 2 : ℚ) • M).map (fun q : ℚ => (q : ℝ)) =
        (1 / 2 : ℝ) • M.map (fun q : ℚ => (q : ℝ)) := by
    ext i j
    simp
  rw [hs]
  congr 1
  change (Rat.castHom ℝ).mapMatrix _ = _
  simp only [map_mul, map_sub, map_ofNat, map_pow]
  rfl

theorem roundedSchulzMatrixStep_error {n : ℕ} (p : ℕ)
    (A Z : Matrix (Fin n) (Fin n) ℚ) :
    ‖(roundedSchulzMatrixStep p A Z).map (fun q : ℚ => (q : ℝ)) -
      schulzInvSqrtMatrixStep (A.map (fun q : ℚ => (q : ℝ)))
        (Z.map (fun q : ℚ => (q : ℝ)))‖ ≤ 1 / (2 : ℝ) ^ p := by
  rw [← schulzMatrixStep_rat_cast, roundedSchulzMatrixStep, materializeMatrix_eq,
    norm_sub_rev, euclideanMatrix_norm_sub_CLM]
  exact dyadicRoundMatrix_prescribed_error p _

end GeometricGaussianLHL

end RoundedSchulz

section SchulzInverseMatrix

/-!
## Matrix inverse accuracy of the squared Schulz iterate

The spectral theorem transfers the scalar inverse error to the Euclidean
operator norm. This targets the actual nonsingular matrix inverse and uses
`t+2B` exact-arithmetic iterations on spectrum `[2^(-B),1]`. The rational
cast theorem concerns the actual rational iteration, without a runtime claim.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open scoped MatrixOrder Matrix.Norms.L2Operator

namespace GeometricGaussianLHL

theorem schulzInverseTarget_spectral_form {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosDef) :
    A⁻¹ = Unitary.conjStarAlgAut ℝ _ hA.isHermitian.eigenvectorUnitary
      (Matrix.diagonal (fun i => (hA.isHermitian.eigenvalues i)⁻¹)) := by
  apply Matrix.inv_eq_right_inv
  rw (occs := .pos [1]) [hA.isHermitian.spectral_theorem]
  rw [← map_mul, Matrix.diagonal_mul_diagonal]
  have hdiag : Matrix.diagonal (fun i => hA.isHermitian.eigenvalues i *
      (hA.isHermitian.eigenvalues i)⁻¹) = (1 : Matrix (Fin n) (Fin n) ℝ) := by
    simp [mul_inv_cancel₀ (hA.eigenvalues_pos _).ne']
  change Unitary.conjStarAlgAut ℝ _ hA.isHermitian.eigenvectorUnitary
    (Matrix.diagonal (fun i => hA.isHermitian.eigenvalues i *
      (hA.isHermitian.eigenvalues i)⁻¹)) = 1
  rw [hdiag, map_one]

theorem schulzMatrix_inverse_operator_error {n : ℕ} (t B : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosSemidef)
    (hlo : ∀ i, 1 / (2 : ℝ) ^ B ≤ hA.isHermitian.eigenvalues i)
    (hhi : ∀ i, hA.isHermitian.eigenvalues i ≤ 1) :
    ‖(schulzInvSqrtMatrixIterate A (t + B + B)) ^ 2 - A⁻¹‖ ≤
      1 / (2 : ℝ) ^ t := by
  have hpd : A.PosDef := hA.isHermitian.posDef_iff_eigenvalues_pos.mpr fun i =>
    (by positivity : (0 : ℝ) < 1 / (2 : ℝ) ^ B).trans_le (hlo i)
  rw [schulzMatrix_spectral_form A hA.isHermitian, schulzInverseTarget_spectral_form A hpd,
    ← map_pow, ← map_sub, unitaryConj_matrix_norm, Matrix.diagonal_pow,
    Matrix.diagonal_sub, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  simpa only [Real.norm_eq_abs, Pi.pow_apply] using
    schulz_inverse_prescribed_error t B (hlo i) (hhi i)

theorem schulzMatrix_rat_inverse_operator_error {n : ℕ} (t B : ℕ)
    (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : (A.map (fun q : ℚ => (q : ℝ))).PosSemidef)
    (hlo : ∀ i, 1 / (2 : ℝ) ^ B ≤ hA.isHermitian.eigenvalues i)
    (hhi : ∀ i, hA.isHermitian.eigenvalues i ≤ 1) :
    ‖((schulzInvSqrtMatrixIterate A (t + B + B)) ^ 2).map (fun q : ℚ => (q : ℝ)) -
      (A.map (fun q : ℚ => (q : ℝ)))⁻¹‖ ≤ 1 / (2 : ℝ) ^ t := by
  change ‖(Rat.castHom ℝ).mapMatrix ((schulzInvSqrtMatrixIterate A (t + B + B)) ^ 2) -
    (A.map (fun q : ℚ => (q : ℝ)))⁻¹‖ ≤ _
  rw [map_pow]
  change ‖((schulzInvSqrtMatrixIterate A (t + B + B)).map (fun q : ℚ => (q : ℝ))) ^ 2 -
    (A.map (fun q : ℚ => (q : ℝ)))⁻¹‖ ≤ _
  rw [schulzInvSqrtMatrixIterate_rat_cast]
  exact schulzMatrix_inverse_operator_error t B _ hA hlo hhi

end GeometricGaussianLHL
end

end SchulzInverseMatrix

section SchulzMatrixBounds

/-!
## Uniform bounds for the exact square-root iteration

These estimates hold in the Euclidean operator norm. The inverse-square-root
iterates have norm at most `2^B` when the input spectrum lies in `[2^(-B),1]`.
This bound will control the propagation of rounding errors.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open scoped MatrixOrder Matrix.Norms.L2Operator

namespace GeometricGaussianLHL

theorem schulz_scalar_iterate_le (B k : ℕ) {a : ℝ}
    (hlo : 1 / (2 : ℝ) ^ B ≤ a) (hhi : a ≤ 1) :
    |schulzInvSqrtIterate a k| ≤ (2 : ℝ) ^ B := by
  have hp : 0 < (2 : ℝ) ^ B := by positivity
  have h1 : 1 ≤ (2 : ℝ) ^ B := one_le_pow₀ (by norm_num)
  have ha : 0 ≤ a := (by positivity : 0 ≤ 1 / (2 : ℝ) ^ B).trans hlo
  obtain ⟨hz, he, _⟩ := schulz_iterate_invariants ha hhi k
  rw [abs_of_nonneg hz]
  have hsq : (schulzInvSqrtIterate a k) ^ 2 ≤ (2 : ℝ) ^ B := by
    have hmul := mul_le_mul_of_nonneg_right hlo (sq_nonneg (schulzInvSqrtIterate a k))
    have hdiv : (schulzInvSqrtIterate a k) ^ 2 / (2 : ℝ) ^ B ≤ 1 := by
      simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul, mul_one] using
        hmul.trans (by linarith : a * (schulzInvSqrtIterate a k) ^ 2 ≤ 1)
    exact (div_le_one hp).mp hdiv
  nlinarith [sq_nonneg ((2 : ℝ) ^ B - 1)]

theorem schulzMatrix_iterate_norm_le {n : ℕ} (B k : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosSemidef)
    (hlo : ∀ i, 1 / (2 : ℝ) ^ B ≤ hA.isHermitian.eigenvalues i)
    (hhi : ∀ i, hA.isHermitian.eigenvalues i ≤ 1) :
    ‖schulzInvSqrtMatrixIterate A k‖ ≤ (2 : ℝ) ^ B := by
  rw [schulzMatrix_spectral_form A hA.isHermitian, unitaryConj_matrix_norm,
    Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  exact schulz_scalar_iterate_le B k (hlo i) (hhi i)

end GeometricGaussianLHL
end

end SchulzMatrixBounds

section IntegerArithmeticBounds

/-!
## Magnitude bounds for integer matrix arithmetic

Partial dot-product sums satisfy the same conservative bound as full sums.
The cubic Schulz numerator has polynomial binary length whenever the input
entries, state entries, and common denominators have bounded binary length.
These bounds concern the actual integer expressions before division.
-/

namespace GeometricGaussianLHL

theorem integerSchulz_inner_bound {n : ℕ} (a d U V : ℕ)
    (X N : Matrix (Fin n) (Fin n) ℤ)
    (ha : a ≤ 2 ^ U) (hd : d ≤ 2 ^ V)
    (hX : ∀ i j, (X i j).natAbs ≤ 2 ^ U)
    (hN : ∀ i j, (N i j).natAbs ≤ 2 ^ V) (i j : Fin n) :
    (((3 * (a : ℤ) * (d : ℤ) ^ 2) • (1 : Matrix (Fin n) (Fin n) ℤ) -
      X * N ^ 2) i j).natAbs ≤ (3 + n * n) * 2 ^ (U + 2 * V) := by
  have hc : (3 * (a : ℤ) * (d : ℤ) ^ 2).natAbs ≤ 3 * 2 ^ (U + 2 * V) := by
    simp only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
    change 3 * a * d ^ 2 ≤ _
    calc
      _ ≤ 3 * 2 ^ U * (2 ^ V) ^ 2 :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 3 ha) (Nat.pow_le_pow_left hd 2)
      _ = _ := by rw [Nat.mul_comm 2 V, pow_add, pow_mul]; ring
  have hNN (i j : Fin n) : ((N ^ 2) i j).natAbs ≤ n * (2 ^ V * 2 ^ V) := by
    rw [pow_two]
    exact integerMatrix_product_bound N N _ _ hN hN i j
  have hXN := integerMatrix_product_bound X (N ^ 2) _ _ hX hNN i j
  have hsub := (Int.natAbs_sub_le
    (((3 * (a : ℤ) * (d : ℤ) ^ 2) • (1 : Matrix (Fin n) (Fin n) ℤ)) i j)
    ((X * N ^ 2) i j)).trans
      (Nat.add_le_add ((integerMatrix_scalar_identity_bound _ i j).trans hc) hXN)
  refine hsub.trans_eq ?_
  simp only [Nat.mul_comm 2 V, pow_add, pow_mul]
  ring

theorem integerSchulzNumerator_bound {n : ℕ} (a d U V : ℕ)
    (X N : Matrix (Fin n) (Fin n) ℤ)
    (ha : a ≤ 2 ^ U) (hd : d ≤ 2 ^ V)
    (hX : ∀ i j, (X i j).natAbs ≤ 2 ^ U)
    (hN : ∀ i j, (N i j).natAbs ≤ 2 ^ V) (i j : Fin n) :
    (integerSchulzNumerator a d X N i j).natAbs ≤
      n * (3 + n * n) * 2 ^ (U + 3 * V) := by
  have h := integerMatrix_product_bound N
    ((3 * (a : ℤ) * (d : ℤ) ^ 2) • 1 - X * N ^ 2) _ _ hN
    (integerSchulz_inner_bound a d U V X N ha hd hX hN) i j
  refine h.trans_eq ?_
  simp only [Nat.mul_comm 2 V, Nat.mul_comm 3 V, pow_add, pow_mul]
  ring

theorem integerSchulz_dimension_factor (n : ℕ) :
    n * (3 + n * n) ≤ 2 ^ (3 * n + 2) := by
  have hn := (Nat.lt_two_pow_self (n := n)).le
  have hn2 := Nat.mul_le_mul hn hn
  have hp : 1 ≤ (2 ^ n) ^ 2 := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hb : 3 + n * n ≤ 4 * (2 ^ n) ^ 2 := by nlinarith
  calc
    _ ≤ 2 ^ n * (4 * (2 ^ n) ^ 2) := Nat.mul_le_mul hn hb
    _ = _ := by rw [Nat.mul_comm 3 n, pow_add, pow_mul]; ring

theorem integerSchulzNumerator_pow_bound {n : ℕ} (a d U V : ℕ)
    (X N : Matrix (Fin n) (Fin n) ℤ)
    (ha : a ≤ 2 ^ U) (hd : d ≤ 2 ^ V)
    (hX : ∀ i j, (X i j).natAbs ≤ 2 ^ U)
    (hN : ∀ i j, (N i j).natAbs ≤ 2 ^ V) (i j : Fin n) :
    (integerSchulzNumerator a d X N i j).natAbs ≤ 2 ^ (U + 3 * V + 3 * n + 2) := by
  calc
    _ ≤ n * (3 + n * n) * 2 ^ (U + 3 * V) :=
      integerSchulzNumerator_bound a d U V X N ha hd hX hN i j
    _ ≤ 2 ^ (3 * n + 2) * 2 ^ (U + 3 * V) :=
      Nat.mul_le_mul_right _ (integerSchulz_dimension_factor n)
    _ = _ := by rw [← pow_add]; congr 1; omega

theorem integerSchulzNumerator_size {n : ℕ} (a d U V : ℕ)
    (X N : Matrix (Fin n) (Fin n) ℤ)
    (ha : a ≤ 2 ^ U) (hd : d ≤ 2 ^ V)
    (hX : ∀ i j, (X i j).natAbs ≤ 2 ^ U)
    (hN : ∀ i j, (N i j).natAbs ≤ 2 ^ V) (i j : Fin n) :
    (integerSchulzNumerator a d X N i j).natAbs.size ≤ U + 3 * V + 3 * n + 3 := by
  apply Nat.size_le.mpr
  have h := integerSchulzNumerator_pow_bound a d U V X N ha hd hX hN i j
  have hp : 0 < 2 ^ (U + 3 * V + 3 * n + 2) := by positivity
  calc
    _ ≤ 2 ^ (U + 3 * V + 3 * n + 2) := h
    _ < 2 ^ (U + 3 * V + 3 * n + 2) * 2 := by omega
    _ = _ := by rw [← pow_succ]

end GeometricGaussianLHL

end IntegerArithmeticBounds

section RoundedSchulzPrecision

/-!
## Forward error of the bounded-precision rational iteration

The error is measured against the exact matrix iterate. Choosing
`p = s + (2B+5)k` keeps the accumulated operator error below `2^(-s)`.
All rounding is performed by the executable rational algorithm.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open scoped MatrixOrder Matrix.Norms.L2Operator

namespace GeometricGaussianLHL

theorem roundedSchulz_forward_error {n : ℕ} (p B : ℕ)
    (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : (A.map (fun q : ℚ => (q : ℝ))).PosSemidef)
    (hlo : ∀ i, 1 / (2 : ℝ) ^ B ≤ hA.isHermitian.eigenvalues i)
    (hhi : ∀ i, hA.isHermitian.eigenvalues i ≤ 1) (k : ℕ) :
    (2 * B + 5) * k ≤ p →
    ‖(roundedSchulzMatrixIterate p A k).map (fun q : ℚ => (q : ℝ)) -
      schulzInvSqrtMatrixIterate (A.map (fun q : ℚ => (q : ℝ))) k‖ ≤
      (2 : ℝ) ^ ((2 * B + 5) * k) / (2 : ℝ) ^ p := by
  induction k with
  | zero =>
    intro _hp
    change ‖(Rat.castHom ℝ).mapMatrix (1 : Matrix (Fin n) (Fin n) ℚ) - 1‖ ≤ _
    rw [map_one, sub_self, norm_zero]
    positivity
  | succ k ih =>
    intro hp
    have hk : (2 * B + 5) * k ≤ p :=
      (Nat.mul_le_mul_left (2 * B + 5) (Nat.le_succ k)).trans hp
    have he := ih hk
    have he1 := he.trans (dyadic_error_budget_le_one hk)
    let Ar := A.map (fun q : ℚ => (q : ℝ))
    let W := (roundedSchulzMatrixIterate p A k).map (fun q : ℚ => (q : ℝ))
    let Z := schulzInvSqrtMatrixIterate Ar k
    have hZ : ‖Z‖ ≤ (2 : ℝ) ^ B := schulzMatrix_iterate_norm_le B k Ar hA hlo hhi
    have hW : ‖W‖ ≤ (2 : ℝ) ^ B + 1 := by
      have ht : ‖W‖ ≤ ‖W - Z‖ + ‖Z‖ := by
        calc
          ‖W‖ = ‖(W - Z) + Z‖ := by rw [sub_add_cancel]
          _ ≤ _ := norm_add_le _ _
      linarith
    have hZ' : ‖Z‖ ≤ (2 : ℝ) ^ B + 1 := by linarith
    have hstep := schulzMatrix_step_dyadic_lipschitz B Ar W Z
      (schulzMatrix_input_norm_le Ar hA hhi) hW hZ'
    have hlocal := roundedSchulzMatrixStep_error p A (roundedSchulzMatrixIterate p A k)
    change ‖(roundedSchulzMatrixStep p A (roundedSchulzMatrixIterate p A k)).map
      (fun q : ℚ => (q : ℝ)) - schulzInvSqrtMatrixStep Ar Z‖ ≤ _
    calc
      _ = ‖((roundedSchulzMatrixStep p A (roundedSchulzMatrixIterate p A k)).map
          (fun q : ℚ => (q : ℝ)) - schulzInvSqrtMatrixStep Ar W) +
          (schulzInvSqrtMatrixStep Ar W - schulzInvSqrtMatrixStep Ar Z)‖ := by
        congr 1
        abel
      _ ≤ _ := norm_add_le _ _
      _ ≤ 1 / (2 : ℝ) ^ p + (2 : ℝ) ^ (2 * B + 4) *
          ((2 : ℝ) ^ ((2 * B + 5) * k) / (2 : ℝ) ^ p) := by
        exact add_le_add hlocal (hstep.trans (mul_le_mul_of_nonneg_left he (by positivity)))
      _ ≤ _ := by simpa only [add_comm] using dyadic_error_budget_step p B k

theorem roundedSchulz_prescribed_forward_error {n : ℕ} (s B k : ℕ)
    (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : (A.map (fun q : ℚ => (q : ℝ))).PosSemidef)
    (hlo : ∀ i, 1 / (2 : ℝ) ^ B ≤ hA.isHermitian.eigenvalues i)
    (hhi : ∀ i, hA.isHermitian.eigenvalues i ≤ 1) :
    ‖(roundedSchulzMatrixIterate (s + (2 * B + 5) * k) A k).map (fun q : ℚ => (q : ℝ)) -
      schulzInvSqrtMatrixIterate (A.map (fun q : ℚ => (q : ℝ))) k‖ ≤ 1 / (2 : ℝ) ^ s := by
  have h := roundedSchulz_forward_error (s + (2 * B + 5) * k) B A hA hlo hhi k (by omega)
  simpa only [dyadic_error_budget_exact] using h

end GeometricGaussianLHL
end

end RoundedSchulzPrecision

section SchulzScheduleCost

/-!
## Computing the Schulz precision schedule

The seven natural arithmetic operations used to choose the iteration count
and dyadic precisions are charged at their operand bit lengths. This is the
same declared arithmetic convention used for the integer matrix operations.
-/

namespace GeometricGaussianLHL

structure SchulzSchedule where
  iterations : ℕ
  precision : ℕ
  storedBits : ℕ
  outputBits : ℕ

def schulzSchedule (n s B : ℕ) : SchulzSchedule :=
  let k := s + B
  let p := s + (2 * B + 5) * k
  ⟨k, p, p + n, s + n⟩

def costedSchulzSchedule (n s B : ℕ) : Costed SchulzSchedule :=
  let k := costedNatAdd s B
  let twiceB := costedNatMul 2 B
  let factor := costedNatAdd twiceB.value 5
  let product := costedNatMul factor.value k.value
  let p := costedNatAdd s product.value
  let q := costedNatAdd p.value n
  let r := costedNatAdd s n
  ⟨⟨k.value, p.value, q.value, r.value⟩,
    k.steps + twiceB.steps + factor.steps + product.steps + p.steps + q.steps + r.steps⟩

theorem costedSchulzSchedule_value (n s B : ℕ) :
    (costedSchulzSchedule n s B).value = schulzSchedule n s B := rfl

def schulzScheduleMagnitude (n s B : ℕ) : ℕ := n + s + B + 5 + (2 * B + 5) * (s + B)
def schulzScheduleBudget (n s B : ℕ) : ℕ := 7 * (2 * schulzScheduleMagnitude n s B + 1) ^ 2

theorem costedSchulzSchedule_steps_le (n s B : ℕ) :
    (costedSchulzSchedule n s B).steps ≤ schulzScheduleBudget n s B := by
  let H := schulzScheduleMagnitude n s B
  have hn : n ≤ H := by dsimp [H, schulzScheduleMagnitude]; omega
  have hs : s ≤ H := by dsimp [H, schulzScheduleMagnitude]; omega
  have hB : B ≤ H := by dsimp [H, schulzScheduleMagnitude]; omega
  have h2 : 2 ≤ H := by dsimp [H, schulzScheduleMagnitude]; omega
  have h5 : 5 ≤ H := by dsimp [H, schulzScheduleMagnitude]; omega
  have h2B : 2 * B ≤ H := by dsimp [H, schulzScheduleMagnitude]; nlinarith
  have hf : 2 * B + 5 ≤ H := by dsimp [H, schulzScheduleMagnitude]; nlinarith
  have hk : s + B ≤ H := by dsimp [H, schulzScheduleMagnitude]; omega
  have hprod : (2 * B + 5) * (s + B) ≤ H := by dsimp [H, schulzScheduleMagnitude]; omega
  have hp : s + (2 * B + 5) * (s + B) ≤ H := by dsimp [H, schulzScheduleMagnitude]; omega
  have h₁ := costedNatAdd_steps_le s B H hs hB
  have h₂ := costedNatMul_steps_le 2 B H h2 hB
  have h₃ := costedNatAdd_steps_le (2 * B) 5 H h2B h5
  have h₄ := costedNatMul_steps_le (2 * B + 5) (s + B) H hf hk
  have h₅ := costedNatAdd_steps_le s ((2 * B + 5) * (s + B)) H hs hprod
  have h₆ := costedNatAdd_steps_le (s + (2 * B + 5) * (s + B)) n H hp hn
  have h₇ := costedNatAdd_steps_le s n H hs hn
  change _ ≤ 7 * (2 * H + 1) ^ 2
  dsimp only [costedSchulzSchedule, costedNatAdd, costedNatMul] at *
  omega

theorem polyBound_schulzScheduleMagnitude {n s B : ℕ → ℕ}
    (hn : PolynomialCostBound n) (hs : PolynomialCostBound s) (hB : PolynomialCostBound B) :
    PolynomialCostBound (fun x => schulzScheduleMagnitude (n x) (s x) (B x)) :=
  ((((hn.add hs).add hB).add (PolynomialCostBound.const 5)).add
    ((((PolynomialCostBound.const 2).mul hB).add (PolynomialCostBound.const 5)).mul (hs.add hB)))

theorem polyBound_schulzScheduleBudget {n s B : ℕ → ℕ}
    (hn : PolynomialCostBound n) (hs : PolynomialCostBound s) (hB : PolynomialCostBound B) :
    PolynomialCostBound (fun x => schulzScheduleBudget (n x) (s x) (B x)) :=
  (PolynomialCostBound.const 7).mul ((((PolynomialCostBound.const 2).mul
    (polyBound_schulzScheduleMagnitude hn hs hB)).add (PolynomialCostBound.const 1)).pow 2)

end GeometricGaussianLHL

end SchulzScheduleCost

section RoundedSchulzInverse

/-!
## Rounded inverse approximation

This numerical specification reuses the rounded inverse-square-root iteration.
Its stored integer refinement and bit bounds are proved in the corresponding
integer modules. Accumulated arithmetic costs remain separate.
-/

set_option backward.isDefEq.respectTransparency false

open scoped MatrixOrder Matrix.Norms.L2Operator

namespace GeometricGaussianLHL

theorem schulz_square_lipschitz {R : Type*} [SeminormedRing R]
    (W Z : R) {M : ℝ} (hW : ‖W‖ ≤ M) (hZ : ‖Z‖ ≤ M) :
    ‖W ^ 2 - Z ^ 2‖ ≤ (2 * M) * ‖W - Z‖ := by
  have he : W ^ 2 - Z ^ 2 = (W - Z) * W + Z * (W - Z) := by noncomm_ring
  rw [he]
  have h₁ := norm_mul_le_of_le (le_refl ‖W - Z‖) hW
  have h₂ := norm_mul_le_of_le hZ (le_refl ‖W - Z‖)
  have hsum := norm_add_le ((W - Z) * W) (Z * (W - Z))
  nlinarith

theorem schulz_square_dyadic_lipschitz {R : Type*} [SeminormedRing R]
    (B : ℕ) (W Z : R) (hW : ‖W‖ ≤ (2 : ℝ) ^ B + 1)
    (hZ : ‖Z‖ ≤ (2 : ℝ) ^ B + 1) :
    ‖W ^ 2 - Z ^ 2‖ ≤ (2 : ℝ) ^ (B + 2) * ‖W - Z‖ := by
  have h1 : 1 ≤ (2 : ℝ) ^ B := one_le_pow₀ (by norm_num)
  have hc : 2 * ((2 : ℝ) ^ B + 1) ≤ (2 : ℝ) ^ (B + 2) := by
    rw [pow_add]
    norm_num
    linarith
  exact (schulz_square_lipschitz W Z hW hZ).trans
    (mul_le_mul_of_nonneg_right hc (norm_nonneg _))

def roundedSchulzInverse {n : ℕ} (t B : ℕ) (A : Matrix (Fin n) (Fin n) ℚ) :
    Matrix (Fin n) (Fin n) ℚ :=
  let k := t + B + 4 + B
  let p := t + B + 4 + (2 * B + 5) * k
  let Z := roundedSchulzMatrixIterate p A k
  materializeMatrix (dyadicRoundMatrix (t + B + 4 + n) (Z ^ 2))

theorem roundedSchulzInverse_matrix_error {n : ℕ} (t B : ℕ)
    (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : (A.map (fun q : ℚ => (q : ℝ))).PosSemidef)
    (hlo : ∀ i, 1 / (2 : ℝ) ^ B ≤ hA.isHermitian.eigenvalues i)
    (hhi : ∀ i, hA.isHermitian.eigenvalues i ≤ 1) :
    ‖(roundedSchulzInverse t B A).map (fun q : ℚ => (q : ℝ)) -
      (A.map (fun q : ℚ => (q : ℝ)))⁻¹‖ ≤ 1 / (2 : ℝ) ^ t := by
  let k := t + B + 4 + B
  let s := t + B + 4
  let p := s + (2 * B + 5) * k
  let Ar := A.map (fun q : ℚ => (q : ℝ))
  let W := (roundedSchulzMatrixIterate p A k).map (fun q : ℚ => (q : ℝ))
  let Z := schulzInvSqrtMatrixIterate Ar k
  let P := (roundedSchulzMatrixIterate p A k) ^ 2
  have hf : ‖W - Z‖ ≤ 1 / (2 : ℝ) ^ s :=
    roundedSchulz_prescribed_forward_error s B k A hA hlo hhi
  have hdyadic {u v : ℕ} (huv : u ≤ v) :
      1 / (2 : ℝ) ^ v ≤ 1 / (2 : ℝ) ^ u :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) huv)
  have hsmall : 1 / (2 : ℝ) ^ s ≤ 1 := by
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1)
      (one_le_pow₀ (by norm_num) : (1 : ℝ) ≤ 2 ^ s)
  have hZ : ‖Z‖ ≤ (2 : ℝ) ^ B := schulzMatrix_iterate_norm_le B k Ar hA hlo hhi
  have hW : ‖W‖ ≤ (2 : ℝ) ^ B + 1 := by
    have htriangle : ‖W‖ ≤ ‖W - Z‖ + ‖Z‖ := by
      calc
        _ = ‖(W - Z) + Z‖ := by rw [sub_add_cancel]
        _ ≤ _ := norm_add_le _ _
    linarith [hf.trans hsmall]
  have hPmap : P.map (fun q : ℚ => (q : ℝ)) = W ^ 2 :=
    map_pow (Rat.castHom ℝ).mapMatrix _ _
  have hproduct : ‖P.map (fun q : ℚ => (q : ℝ)) - Z ^ 2‖ ≤ 1 / (2 : ℝ) ^ (t + 2) := by
    rw [hPmap]
    have hb := (schulz_square_dyadic_lipschitz B W Z hW (by linarith : ‖Z‖ ≤ (2 : ℝ) ^ B + 1)).trans
      (mul_le_mul_of_nonneg_left hf (by positivity))
    have he : (2 : ℝ) ^ (B + 2) * (1 / (2 : ℝ) ^ s) = 1 / (2 : ℝ) ^ (t + 2) := by
      dsimp only [s]
      rw [show t + B + 4 = (B + 2) + (t + 2) by omega, pow_add]
      field_simp
      simp [pow_add, mul_assoc]
    exact hb.trans_eq he
  have hexact0 : ‖Z ^ 2 - Ar⁻¹‖ ≤ 1 / (2 : ℝ) ^ (t + 4) := by
    have hk : k = t + 4 + B + B := by dsimp only [k]; omega
    dsimp only [Z]
    rw [hk]
    exact schulzMatrix_inverse_operator_error (t + 4) B Ar hA hlo hhi
  have hexact := hexact0.trans (hdyadic (by omega : t + 2 ≤ t + 4))
  have hround0 : ‖(roundedSchulzInverse t B A).map (fun q : ℚ => (q : ℝ)) -
      P.map (fun q : ℚ => (q : ℝ))‖ ≤ 1 / (2 : ℝ) ^ s := by
    rw [roundedSchulzInverse, materializeMatrix_eq, norm_sub_rev, euclideanMatrix_norm_sub_CLM]
    exact dyadicRoundMatrix_prescribed_error s P
  have hround := hround0.trans (hdyadic (by dsimp only [s]; omega : t + 2 ≤ s))
  have h₁ := norm_sub_le_norm_sub_add_norm_sub
    ((roundedSchulzInverse t B A).map (fun q : ℚ => (q : ℝ)))
    (P.map (fun q : ℚ => (q : ℝ))) Ar⁻¹
  have h₂ := norm_sub_le_norm_sub_add_norm_sub (P.map (fun q : ℚ => (q : ℝ))) (Z ^ 2) Ar⁻¹
  have hbudget : 3 * (1 / (2 : ℝ) ^ (t + 2)) ≤ 1 / (2 : ℝ) ^ t := by
    rw [pow_add]
    norm_num
    have hp : 0 < (2 : ℝ) ^ t := by positivity
    field_simp
    norm_num
  linarith

theorem roundedSchulzInverse_operator_error {n : ℕ} (t B : ℕ)
    (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : (A.map (fun q : ℚ => (q : ℝ))).PosSemidef)
    (hlo : ∀ i, 1 / (2 : ℝ) ^ B ≤ hA.isHermitian.eigenvalues i)
    (hhi : ∀ i, hA.isHermitian.eigenvalues i ≤ 1) :
    ‖(Matrix.toEuclideanLin ((roundedSchulzInverse t B A).map
        (fun q : ℚ => (q : ℝ)))).toContinuousLinearMap -
      (Matrix.toEuclideanLin ((A.map (fun q : ℚ => (q : ℝ)))⁻¹)).toContinuousLinearMap‖ ≤
      1 / (2 : ℝ) ^ t := by
  rw [← euclideanMatrix_norm_sub_CLM]
  exact roundedSchulzInverse_matrix_error t B A hA hlo hhi

end GeometricGaussianLHL

end RoundedSchulzInverse

section RoundedSchulzSquareRoot

/-!
## An executable rational square-root approximation

For a normalized positive matrix with spectrum in `[2^(-B),1]`, this
algorithm returns a dyadic matrix within `2^(-t)` of its actual positive
square root in Euclidean operator norm. There are `t+B+2` iterations,
with `t+2+(2B+5)(t+B+2)+n` fractional bits per stored intermediate entry.
These accuracy and precision bounds do not yet assert a runtime bound.
-/

set_option backward.isDefEq.respectTransparency false

open scoped MatrixOrder Matrix.Norms.L2Operator

namespace GeometricGaussianLHL

def roundedSchulzSqrt {n : ℕ} (t B : ℕ) (A : Matrix (Fin n) (Fin n) ℚ) :
    Matrix (Fin n) (Fin n) ℚ :=
  let k := t + 2 + B
  let p := t + 2 + (2 * B + 5) * k
  materializeMatrix (dyadicRoundMatrix (t + 2 + n) (A * roundedSchulzMatrixIterate p A k))

theorem rationalMatrix_map_mul {n : ℕ} (A Z : Matrix (Fin n) (Fin n) ℚ) :
    (A * Z).map (fun q : ℚ => (q : ℝ)) =
      A.map (fun q : ℚ => (q : ℝ)) * Z.map (fun q : ℚ => (q : ℝ)) := by
  exact map_mul (Rat.castHom ℝ).mapMatrix A Z

theorem roundedSchulzSqrt_operator_error {n : ℕ} (t B : ℕ)
    (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : (A.map (fun q : ℚ => (q : ℝ))).PosSemidef)
    (hlo : ∀ i, 1 / (2 : ℝ) ^ B ≤ hA.isHermitian.eigenvalues i)
    (hhi : ∀ i, hA.isHermitian.eigenvalues i ≤ 1) :
    ‖(Matrix.toEuclideanLin ((roundedSchulzSqrt t B A).map
        (fun q : ℚ => (q : ℝ)))).toContinuousLinearMap -
      (Matrix.toEuclideanLin (CFC.sqrt (A.map (fun q : ℚ => (q : ℝ))))).toContinuousLinearMap‖ ≤
      1 / (2 : ℝ) ^ t := by
  let k := t + 2 + B
  let p := t + 2 + (2 * B + 5) * k
  let Ar := A.map (fun q : ℚ => (q : ℝ))
  let P := A * roundedSchulzMatrixIterate p A k
  let E := Ar * schulzInvSqrtMatrixIterate Ar k
  have hf := roundedSchulz_prescribed_forward_error (t + 2) B k A hA hlo hhi
  have hproduct : ‖P.map (fun q : ℚ => (q : ℝ)) - E‖ ≤ 1 / (2 : ℝ) ^ (t + 2) := by
    dsimp only [P, E]
    rw [rationalMatrix_map_mul, ← mul_sub]
    exact (norm_mul_le_of_le (schulzMatrix_input_norm_le Ar hA hhi) hf).trans_eq (one_mul _)
  have hexact : ‖E - CFC.sqrt Ar‖ ≤ 1 / (2 : ℝ) ^ (t + 2) := by
    rw [euclideanMatrix_norm_sub_CLM]
    exact schulzMatrix_sqrt_operator_error (t + 2) B Ar hA hlo hhi
  have hround : ‖(roundedSchulzSqrt t B A).map (fun q : ℚ => (q : ℝ)) -
      P.map (fun q : ℚ => (q : ℝ))‖ ≤ 1 / (2 : ℝ) ^ (t + 2) := by
    rw [roundedSchulzSqrt, materializeMatrix_eq, norm_sub_rev, euclideanMatrix_norm_sub_CLM]
    exact dyadicRoundMatrix_prescribed_error (t + 2) P
  rw [← euclideanMatrix_norm_sub_CLM]
  have h₁ := norm_sub_le_norm_sub_add_norm_sub
    ((roundedSchulzSqrt t B A).map (fun q : ℚ => (q : ℝ)))
    (P.map (fun q : ℚ => (q : ℝ))) (CFC.sqrt Ar)
  have h₂ := norm_sub_le_norm_sub_add_norm_sub (P.map (fun q : ℚ => (q : ℝ))) E (CFC.sqrt Ar)
  have hbudget : 3 * (1 / (2 : ℝ) ^ (t + 2)) ≤ 1 / (2 : ℝ) ^ t := by
    rw [pow_add]
    norm_num
    have hp : 0 < (2 : ℝ) ^ t := by positivity
    field_simp
    norm_num
  linarith

end GeometricGaussianLHL

end RoundedSchulzSquareRoot

section SymmetricSchulzInverse

/-!
## Symmetric inverse approximation and stability of positive definiteness

Averaging a rational matrix with its transpose restores symmetry without
increasing its Euclidean operator error against a symmetric target. A spectral
lower bound larger than this error guarantees positive definiteness. These
are numerical refinement statements, not new machine-execution claims.
-/

open scoped MatrixOrder Matrix.Norms.L2Operator

namespace GeometricGaussianLHL

theorem matrix_symmetrize_error {n : ℕ} (R S : Matrix (Fin n) (Fin n) ℝ)
    (hS : S.IsHermitian) :
    ‖(1 / 2 : ℝ) • (R + R.transpose) - S‖ ≤ ‖R - S‖ := by
  have hst : S.transpose = S := Matrix.isHermitian_iff_isSymm.mp hS
  have he : (1 / 2 : ℝ) • (R + R.transpose) - S =
      (1 / 2 : ℝ) • ((R - S) + (R - S).transpose) := by
    rw [Matrix.transpose_sub, hst]
    module
  rw [he, norm_smul]
  have hn : ‖(R - S).transpose‖ = ‖R - S‖ := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.l2_opNorm_conjTranspose (R - S)
  have hh := norm_add_le (R - S) (R - S).transpose
  rw [hn] at hh
  norm_num only [Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  linarith

theorem matrix_posDef_of_operator_error {n : ℕ} (R S : Matrix (Fin n) (Fin n) ℝ)
    (hR : R.IsHermitian) (hS : S.IsHermitian) {δ ε : ℝ}
    (hgap : δ • (1 : Matrix (Fin n) (Fin n) ℝ) ≤ S)
    (herr : ‖R - S‖ ≤ ε) (hsmall : ε < δ) : R.PosDef := by
  classical
  rcases isEmpty_or_nonempty (Fin n) with hn | hn
  · have := hn
    apply Matrix.PosDef.of_dotProduct_mulVec_pos hR
    intro x hx
    exact (hx (Subsingleton.elim _ _)).elim
  · have := hn
    have he : (-ε) • (1 : Matrix (Fin n) (Fin n) ℝ) ≤ R - S := by
      rw [← Algebra.algebraMap_eq_smul_one]
      apply algebraMap_le_of_le_spectrum (ha := hR.sub hS)
      intro x hx
      have hn : |x| ≤ ‖R - S‖ := by
        simpa only [Real.norm_eq_abs] using spectrum.norm_le_norm_of_mem hx
      linarith [neg_abs_le x]
    have hlo : (δ - ε) • (1 : Matrix (Fin n) (Fin n) ℝ) ≤ R := by
      calc
        (δ - ε) • (1 : Matrix (Fin n) (Fin n) ℝ) =
            δ • 1 + (-ε) • 1 := by module
        _ ≤ S + (R - S) := add_le_add hgap he
        _ = R := by abel
    have hp : ((δ - ε) • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef :=
      Matrix.PosDef.smul Matrix.PosDef.one (sub_pos.mpr hsmall)
    have h := hp.add_posSemidef (Matrix.le_iff.mp hlo)
    convert h using 1
    abel

def symmetricSchulzInverse {n : ℕ} (t B : ℕ) (A : Matrix (Fin n) (Fin n) ℚ) :
    Matrix (Fin n) (Fin n) ℚ :=
  let R := roundedSchulzInverse t B A
  (1 / 2 : ℚ) • (R + R.transpose)

theorem symmetricSchulzInverse_real_formula {n : ℕ} (t B : ℕ)
    (A : Matrix (Fin n) (Fin n) ℚ) :
    (symmetricSchulzInverse t B A).map (fun q : ℚ => (q : ℝ)) =
      (1 / 2 : ℝ) • (((roundedSchulzInverse t B A).map (fun q : ℚ => (q : ℝ))) +
        ((roundedSchulzInverse t B A).map (fun q : ℚ => (q : ℝ))).transpose) := by
  ext i j
  simp [symmetricSchulzInverse, Matrix.map_apply, Matrix.transpose_apply,
    Matrix.smul_apply, Matrix.add_apply, mul_add]

theorem symmetricSchulzInverse_isHermitian {n : ℕ} (t B : ℕ)
    (A : Matrix (Fin n) (Fin n) ℚ) :
    ((symmetricSchulzInverse t B A).map (fun q : ℚ => (q : ℝ))).IsHermitian := by
  rw [symmetricSchulzInverse_real_formula]
  apply Matrix.IsHermitian.ext
  intro i j
  simp [Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply, add_comm]

theorem symmetricSchulzInverse_matrix_error {n : ℕ} (t B : ℕ)
    (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : (A.map (fun q : ℚ => (q : ℝ))).PosSemidef)
    (hlo : ∀ i, 1 / (2 : ℝ) ^ B ≤ hA.isHermitian.eigenvalues i)
    (hhi : ∀ i, hA.isHermitian.eigenvalues i ≤ 1) :
    ‖(symmetricSchulzInverse t B A).map (fun q : ℚ => (q : ℝ)) -
      (A.map (fun q : ℚ => (q : ℝ)))⁻¹‖ ≤ 1 / (2 : ℝ) ^ t := by
  rw [symmetricSchulzInverse_real_formula]
  exact (matrix_symmetrize_error _ _ hA.inv.isHermitian).trans
    (roundedSchulzInverse_matrix_error t B A hA hlo hhi)

theorem normalizedInverse_one_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosDef) (hhi : ∀ i, hA.isHermitian.eigenvalues i ≤ 1) :
    (1 : Matrix (Fin n) (Fin n) ℝ) ≤ A⁻¹ := by
  let U := hA.isHermitian.eigenvectorUnitary
  have hD : (Matrix.diagonal (fun i => (hA.isHermitian.eigenvalues i)⁻¹) -
      (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef := by
    rw [← Matrix.diagonal_one, Matrix.diagonal_sub]
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro i
    exact sub_nonneg.mpr (by simpa only [one_div] using one_le_one_div (hA.eigenvalues_pos i) (hhi i))
  have he : A⁻¹ - 1 = Unitary.conjStarAlgAut ℝ _ U
      (Matrix.diagonal (fun i => (hA.isHermitian.eigenvalues i)⁻¹) - 1) := by
    rw [map_sub, map_one, schulzInverseTarget_spectral_form A hA]
  rw [Matrix.le_iff, he]
  exact hD.mul_mul_conjTranspose_same (U : Matrix (Fin n) (Fin n) ℝ)

theorem symmetricSchulzInverse_posDef {n : ℕ} (t B : ℕ) (ht : 0 < t)
    (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : (A.map (fun q : ℚ => (q : ℝ))).PosSemidef)
    (hlo : ∀ i, 1 / (2 : ℝ) ^ B ≤ hA.isHermitian.eigenvalues i)
    (hhi : ∀ i, hA.isHermitian.eigenvalues i ≤ 1) :
    ((symmetricSchulzInverse t B A).map (fun q : ℚ => (q : ℝ))).PosDef := by
  have hpd : (A.map (fun q : ℚ => (q : ℝ))).PosDef :=
    hA.isHermitian.posDef_iff_eigenvalues_pos.mpr fun i =>
      (by positivity : (0 : ℝ) < 1 / (2 : ℝ) ^ B).trans_le (hlo i)
  apply matrix_posDef_of_operator_error _ _ (symmetricSchulzInverse_isHermitian t B A)
    hA.inv.isHermitian (δ := 1) (ε := 1 / (2 : ℝ) ^ t)
  · simpa only [one_smul] using normalizedInverse_one_le _ hpd hhi
  · exact symmetricSchulzInverse_matrix_error t B A hA hlo hhi
  · exact (div_lt_one (by positivity)).mpr (one_lt_pow₀ (by norm_num) (by omega))

theorem symmetricSchulzInverse_operator_error {n : ℕ} (t B : ℕ)
    (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : (A.map (fun q : ℚ => (q : ℝ))).PosSemidef)
    (hlo : ∀ i, 1 / (2 : ℝ) ^ B ≤ hA.isHermitian.eigenvalues i)
    (hhi : ∀ i, hA.isHermitian.eigenvalues i ≤ 1) :
    ‖(Matrix.toEuclideanLin ((symmetricSchulzInverse t B A).map
        (fun q : ℚ => (q : ℝ)))).toContinuousLinearMap -
      (Matrix.toEuclideanLin ((A.map (fun q : ℚ => (q : ℝ)))⁻¹)).toContinuousLinearMap‖ ≤
      1 / (2 : ℝ) ^ t := by
  rw [← euclideanMatrix_norm_sub_CLM]
  exact symmetricSchulzInverse_matrix_error t B A hA hlo hhi

end GeometricGaussianLHL

end SymmetricSchulzInverse

section StoredSchulz

/-!
## Stored-data implementation of the certified square-root algorithm

Lean matrices are functions. A function returning a materialized matrix
can be compiled with the entry indices as additional arguments, rebuilding
the data at each query. Here the recursion returns vectors of row vectors,
so a predecessor is computed as data before the next step evaluates entries.
The proofs identify the returned data with the certified matrix specification.
-/

set_option backward.isDefEq.respectTransparency false

open scoped MatrixOrder Matrix.Norms.L2Operator

namespace GeometricGaussianLHL

def storedRoundedSchulzIterate {n : ℕ} (p : ℕ)
    (A : Matrix (Fin n) (Fin n) ℚ) : ℕ → RationalMatrixData n
  | 0 => rationalMatrixData 1
  | k + 1 =>
    let Z := storedRoundedSchulzIterate p A k
    rationalMatrixData (dyadicRoundMatrix (p + n)
      ((1 / 2 : ℚ) • (rationalMatrixOfData Z * (3 - A * (rationalMatrixOfData Z) ^ 2))))

theorem storedRoundedSchulzIterate_eq {n : ℕ} (p : ℕ)
    (A : Matrix (Fin n) (Fin n) ℚ) (k : ℕ) :
    rationalMatrixOfData (storedRoundedSchulzIterate p A k) =
      roundedSchulzMatrixIterate p A k := by
  induction k with
  | zero => exact rationalMatrixOfData_data 1
  | succ k ih =>
    simp only [storedRoundedSchulzIterate, rationalMatrixOfData_data, ih,
      roundedSchulzMatrixIterate, roundedSchulzMatrixStep, materializeMatrix_eq,
      schulzInvSqrtMatrixStep_formula]

def storedSchulzSqrt {n : ℕ} (t B : ℕ) (A : Matrix (Fin n) (Fin n) ℚ) : RationalMatrixData n :=
  let k := t + 2 + B
  let p := t + 2 + (2 * B + 5) * k
  let Z := storedRoundedSchulzIterate p A k
  rationalMatrixData (dyadicRoundMatrix (t + 2 + n) (A * rationalMatrixOfData Z))

theorem storedSchulzSqrt_eq {n : ℕ} (t B : ℕ) (A : Matrix (Fin n) (Fin n) ℚ) :
    rationalMatrixOfData (storedSchulzSqrt t B A) = roundedSchulzSqrt t B A := by
  simp only [storedSchulzSqrt, rationalMatrixOfData_data, storedRoundedSchulzIterate_eq,
    roundedSchulzSqrt, materializeMatrix_eq]

theorem storedSchulzSqrt_operator_error {n : ℕ} (t B : ℕ)
    (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : (A.map (fun q : ℚ => (q : ℝ))).PosSemidef)
    (hlo : ∀ i, 1 / (2 : ℝ) ^ B ≤ hA.isHermitian.eigenvalues i)
    (hhi : ∀ i, hA.isHermitian.eigenvalues i ≤ 1) :
    ‖(Matrix.toEuclideanLin ((rationalMatrixOfData (storedSchulzSqrt t B A)).map
        (fun q : ℚ => (q : ℝ)))).toContinuousLinearMap -
      (Matrix.toEuclideanLin (CFC.sqrt (A.map (fun q : ℚ => (q : ℝ))))).toContinuousLinearMap‖ ≤
      1 / (2 : ℝ) ^ t := by
  rw [storedSchulzSqrt_eq]
  exact roundedSchulzSqrt_operator_error t B A hA hlo hhi

end GeometricGaussianLHL

end StoredSchulz

section RationalSpectralApproximation

/-!
## Rational square-root and inverse approximations for general positive inputs

Normalization and conditioning are computed from the rational input. Rescaling
then approximates the actual positive square root or inverse, without an
external spectral promise. The inverse output is symmetric and positive
definite. These are executable numerical specifications; the preprocessing
and postprocessing still need their arithmetic cost analysis.
-/

open scoped MatrixOrder Matrix.Norms.L2Operator

namespace GeometricGaussianLHL

theorem normalizedRationalMatrix_sqrt_rescale {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : (A.map (fun q : ℚ => (q : ℝ))).PosDef) :
    (2 : ℝ) ^ rationalMatrixScaleExponent A •
        CFC.sqrt ((normalizedRationalMatrix A).map (fun q : ℚ => (q : ℝ))) =
      CFC.sqrt (A.map (fun q : ℚ => (q : ℝ))) := by
  have hN := normalizedRationalMatrix_posDef A hA
  apply Eq.symm
  apply CFC.sqrt_unique ?_ (smul_nonneg (by positivity) (CFC.sqrt_nonneg _))
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    CFC.sqrt_mul_sqrt_self _ hN.posSemidef.nonneg,
    normalizedRationalMatrix_real_formula, smul_smul]
  have hs : (2 : ℝ) ^ rationalMatrixScaleExponent A *
      (2 : ℝ) ^ rationalMatrixScaleExponent A *
        (1 / (2 : ℝ) ^ rationalMatrixNormalizationExponent A) = 1 := by
    rw [rationalMatrixNormalizationExponent, two_mul, pow_add]
    field_simp
  rw [hs, one_smul]

theorem normalizedRationalMatrix_inverse_rescale {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : (A.map (fun q : ℚ => (q : ℝ))).PosDef) :
    (1 / (2 : ℝ) ^ rationalMatrixNormalizationExponent A) •
        ((normalizedRationalMatrix A).map (fun q : ℚ => (q : ℝ)))⁻¹ =
      (A.map (fun q : ℚ => (q : ℝ)))⁻¹ := by
  have hN := normalizedRationalMatrix_posDef A hA
  apply Eq.symm
  apply Matrix.inv_eq_right_inv
  rw [Matrix.mul_smul, ← Matrix.smul_mul, ← normalizedRationalMatrix_real_formula]
  exact Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hN.det_pos.ne')

def rationalSqrtApprox {n : ℕ} (t : ℕ) (A : Matrix (Fin n) (Fin n) ℚ) :
    Matrix (Fin n) (Fin n) ℚ :=
  materializeMatrix ((2 : ℚ) ^ rationalMatrixScaleExponent A •
    roundedSchulzSqrt (t + rationalMatrixScaleExponent A)
      (rationalMatrixConditionExponent A) (normalizedRationalMatrix A))

def rationalInverseApprox {n : ℕ} (t : ℕ) (A : Matrix (Fin n) (Fin n) ℚ) :
    Matrix (Fin n) (Fin n) ℚ :=
  materializeMatrix ((1 / (2 : ℚ) ^ rationalMatrixNormalizationExponent A) •
    symmetricSchulzInverse (t + 1) (rationalMatrixConditionExponent A) (normalizedRationalMatrix A))

theorem rationalSqrtApprox_real_formula {n : ℕ} (t : ℕ)
    (A : Matrix (Fin n) (Fin n) ℚ) :
    (rationalSqrtApprox t A).map (fun q : ℚ => (q : ℝ)) =
      (2 : ℝ) ^ rationalMatrixScaleExponent A •
        (roundedSchulzSqrt (t + rationalMatrixScaleExponent A)
          (rationalMatrixConditionExponent A) (normalizedRationalMatrix A)).map
            (fun q : ℚ => (q : ℝ)) := by
  rw [rationalSqrtApprox, materializeMatrix_eq]
  ext i j
  simp [Matrix.map_apply, Matrix.smul_apply]

theorem rationalInverseApprox_real_formula {n : ℕ} (t : ℕ)
    (A : Matrix (Fin n) (Fin n) ℚ) :
    (rationalInverseApprox t A).map (fun q : ℚ => (q : ℝ)) =
      (1 / (2 : ℝ) ^ rationalMatrixNormalizationExponent A) •
        (symmetricSchulzInverse (t + 1) (rationalMatrixConditionExponent A)
          (normalizedRationalMatrix A)).map (fun q : ℚ => (q : ℝ)) := by
  rw [rationalInverseApprox, materializeMatrix_eq]
  ext i j
  simp [Matrix.map_apply, Matrix.smul_apply]

theorem rationalSqrtApprox_matrix_error {n : ℕ} (t : ℕ)
    (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : (A.map (fun q : ℚ => (q : ℝ))).PosDef) :
    ‖(rationalSqrtApprox t A).map (fun q : ℚ => (q : ℝ)) -
      CFC.sqrt (A.map (fun q : ℚ => (q : ℝ)))‖ ≤ 1 / (2 : ℝ) ^ t := by
  have hN := normalizedRationalMatrix_posDef A hA
  obtain ⟨hlo, hhi⟩ := normalizedRationalMatrix_spectral_bounds A hA
  have he := roundedSchulzSqrt_operator_error (t + rationalMatrixScaleExponent A)
    (rationalMatrixConditionExponent A) (normalizedRationalMatrix A) hN.posSemidef hlo hhi
  rw [← euclideanMatrix_norm_sub_CLM] at he
  rw [rationalSqrtApprox_real_formula, ← normalizedRationalMatrix_sqrt_rescale A hA,
    ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ rationalMatrixScaleExponent A)]
  calc
    _ ≤ (2 : ℝ) ^ rationalMatrixScaleExponent A *
        (1 / (2 : ℝ) ^ (t + rationalMatrixScaleExponent A)) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ = _ := by rw [pow_add]; field_simp

theorem rationalInverseApprox_matrix_error {n : ℕ} (t : ℕ)
    (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : (A.map (fun q : ℚ => (q : ℝ))).PosDef) :
    ‖(rationalInverseApprox t A).map (fun q : ℚ => (q : ℝ)) -
      (A.map (fun q : ℚ => (q : ℝ)))⁻¹‖ ≤ 1 / (2 : ℝ) ^ t := by
  have hN := normalizedRationalMatrix_posDef A hA
  obtain ⟨hlo, hhi⟩ := normalizedRationalMatrix_spectral_bounds A hA
  have he := symmetricSchulzInverse_matrix_error (t + 1)
    (rationalMatrixConditionExponent A) (normalizedRationalMatrix A) hN.posSemidef hlo hhi
  rw [rationalInverseApprox_real_formula, ← normalizedRationalMatrix_inverse_rescale A hA,
    ← smul_sub, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 : ℝ) ^ rationalMatrixNormalizationExponent A)]
  have hs : 1 / (2 : ℝ) ^ rationalMatrixNormalizationExponent A ≤ 1 := by
    exact (div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num))
  calc
    _ ≤ (1 / (2 : ℝ) ^ rationalMatrixNormalizationExponent A) * (1 / (2 : ℝ) ^ (t + 1)) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ ≤ 1 * (1 / (2 : ℝ) ^ (t + 1)) := mul_le_mul_of_nonneg_right hs (by positivity)
    _ ≤ _ := by
      simp only [one_mul]
      exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) (by omega))

theorem rationalInverseApprox_posDef {n : ℕ} (t : ℕ)
    (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : (A.map (fun q : ℚ => (q : ℝ))).PosDef) :
    ((rationalInverseApprox t A).map (fun q : ℚ => (q : ℝ))).PosDef := by
  rw [rationalInverseApprox_real_formula]
  have hN := normalizedRationalMatrix_posDef A hA
  obtain ⟨hlo, hhi⟩ := normalizedRationalMatrix_spectral_bounds A hA
  exact (symmetricSchulzInverse_posDef (t + 1) _ (by omega) _ hN.posSemidef hlo hhi).smul
    (by positivity)

theorem rationalSqrtApprox_operator_error {n : ℕ} (t : ℕ)
    (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : (A.map (fun q : ℚ => (q : ℝ))).PosDef) :
    ‖(Matrix.toEuclideanLin ((rationalSqrtApprox t A).map
        (fun q : ℚ => (q : ℝ)))).toContinuousLinearMap -
      (Matrix.toEuclideanLin (CFC.sqrt (A.map (fun q : ℚ => (q : ℝ))))).toContinuousLinearMap‖ ≤
      1 / (2 : ℝ) ^ t := by
  rw [← euclideanMatrix_norm_sub_CLM]
  exact rationalSqrtApprox_matrix_error t A hA

theorem rationalInverseApprox_operator_error {n : ℕ} (t : ℕ)
    (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : (A.map (fun q : ℚ => (q : ℝ))).PosDef) :
    ‖(Matrix.toEuclideanLin ((rationalInverseApprox t A).map
        (fun q : ℚ => (q : ℝ)))).toContinuousLinearMap -
      (Matrix.toEuclideanLin ((A.map (fun q : ℚ => (q : ℝ)))⁻¹)).toContinuousLinearMap‖ ≤
      1 / (2 : ℝ) ^ t := by
  rw [← euclideanMatrix_norm_sub_CLM]
  exact rationalInverseApprox_matrix_error t A hA


theorem normalizedInverse_norm_le {n : ℕ} (B : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (hlo : ∀ i, 1 / (2 : ℝ) ^ B ≤ hA.isHermitian.eigenvalues i) :
    ‖A⁻¹‖ ≤ (2 : ℝ) ^ B := by
  rw [schulzInverseTarget_spectral_form A hA, unitaryConj_matrix_norm, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hA.eigenvalues_pos i)), ← one_div]
  apply (div_le_iff₀ (hA.eigenvalues_pos i)).mpr
  simpa only [mul_comm] using (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ B)).mp (hlo i)

theorem rationalInverseTarget_norm_le {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : (A.map (fun q : ℚ => (q : ℝ))).PosDef) :
    ‖(A.map (fun q : ℚ => (q : ℝ)))⁻¹‖ ≤ (2 : ℝ) ^ rationalMatrixConditionExponent A := by
  have hN := normalizedRationalMatrix_posDef A hA
  obtain ⟨hlo, _⟩ := normalizedRationalMatrix_spectral_bounds A hA
  rw [← normalizedRationalMatrix_inverse_rescale A hA, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 : ℝ) ^ rationalMatrixNormalizationExponent A)]
  have hs : 1 / (2 : ℝ) ^ rationalMatrixNormalizationExponent A ≤ 1 :=
    (div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num))
  calc
    _ ≤ 1 * ‖((normalizedRationalMatrix A).map (fun q : ℚ => (q : ℝ)))⁻¹‖ :=
      mul_le_mul_of_nonneg_right hs (norm_nonneg _)
    _ ≤ _ := by
      simpa only [one_mul] using normalizedInverse_norm_le _ _ hN hlo

theorem rationalInverseApprox_norm_le {n : ℕ} (t : ℕ)
    (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : (A.map (fun q : ℚ => (q : ℝ))).PosDef) :
    ‖(rationalInverseApprox t A).map (fun q : ℚ => (q : ℝ))‖ ≤
      (2 : ℝ) ^ (rationalMatrixConditionExponent A + 1) := by
  have he := rationalInverseApprox_matrix_error t A hA
  have ht := rationalInverseTarget_norm_le A hA
  have hb : 1 / (2 : ℝ) ^ t ≤ 1 := (div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num))
  have hn := norm_le_norm_sub_add ((rationalInverseApprox t A).map (fun q : ℚ => (q : ℝ)))
    ((A.map (fun q : ℚ => (q : ℝ)))⁻¹)
  have h1 : 1 ≤ (2 : ℝ) ^ rationalMatrixConditionExponent A := one_le_pow₀ (by norm_num)
  rw [pow_succ]
  linarith

end GeometricGaussianLHL

end RationalSpectralApproximation

section SchulzOutputSize

/-!
## Encoded length of the actual square-root output

On the normalized positive domain, the returned matrix has norm at most two.
Its final dyadic precision bounds the actual reduced numerator and denominator
of every entry. The result below includes the dimension header and all
self-delimiting rational encodings, not just a count of arithmetic values.
-/

set_option backward.isDefEq.respectTransparency false

open scoped MatrixOrder Matrix.Norms.L2Operator

namespace GeometricGaussianLHL

theorem schulzTarget_norm_le_one {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosSemidef) (hhi : ∀ i, hA.isHermitian.eigenvalues i ≤ 1) :
    ‖CFC.sqrt A‖ ≤ 1 := by
  rw [schulzTarget_spectral_form A hA, unitaryConj_matrix_norm, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro i
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact Real.sqrt_le_one.mpr (hhi i)

theorem roundedSchulzSqrt_norm_le_two {n : ℕ} (t B : ℕ)
    (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : (A.map (fun q : ℚ => (q : ℝ))).PosSemidef)
    (hlo : ∀ i, 1 / (2 : ℝ) ^ B ≤ hA.isHermitian.eigenvalues i)
    (hhi : ∀ i, hA.isHermitian.eigenvalues i ≤ 1) :
    ‖(roundedSchulzSqrt t B A).map (fun q : ℚ => (q : ℝ))‖ ≤ 2 := by
  have he := roundedSchulzSqrt_operator_error t B A hA hlo hhi
  rw [← euclideanMatrix_norm_sub_CLM] at he
  have hz := schulzTarget_norm_le_one _ hA hhi
  have ht := norm_le_norm_sub_add
    ((roundedSchulzSqrt t B A).map (fun q : ℚ => (q : ℝ)))
    (CFC.sqrt (A.map (fun q : ℚ => (q : ℝ))))
  have hp : 1 / (2 : ℝ) ^ t ≤ 1 :=
    (div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num))
  linarith

theorem roundedSchulzSqrt_grid {n : ℕ} (t B : ℕ)
    (A : Matrix (Fin n) (Fin n) ℚ) (i j : Fin n) :
    dyadicRoundRat (t + 2 + n) (roundedSchulzSqrt t B A i j) =
      roundedSchulzSqrt t B A i j := by
  simp only [roundedSchulzSqrt, materializeMatrix_eq, dyadicRoundMatrix, dyadicRoundRat_idempotent]

theorem storedSchulzSqrt_magnitude_bits {n : ℕ} (t B : ℕ)
    (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : (A.map (fun q : ℚ => (q : ℝ))).PosSemidef)
    (hlo : ∀ i, 1 / (2 : ℝ) ^ B ≤ hA.isHermitian.eigenvalues i)
    (hhi : ∀ i, hA.isHermitian.eigenvalues i ≤ 1) :
    rationalMatrixMagnitudeBits (rationalMatrixOfData (storedSchulzSqrt t B A)) ≤
      n * n * (2 * (t + 2 + n) + 4) := by
  rw [storedSchulzSqrt_eq]
  unfold rationalMatrixMagnitudeBits
  calc
    _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, (2 * (t + 2 + n) + 4) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      have hx : |roundedSchulzSqrt t B A i j| ≤ (2 : ℚ) ^ 1 := by
        apply rationalMatrix_entry_bound _ 1 _ i j
        simpa using roundedSchulzSqrt_norm_le_two t B A hA hlo hhi
      have h := dyadic_fixed_rational_bits (t + 2 + n) 1
        (roundedSchulzSqrt t B A i j) (roundedSchulzSqrt_grid t B A i j) hx
      omega
    _ = _ := by simp [Nat.mul_assoc]

theorem storedSchulzSqrt_encoded_length {n : ℕ} (t B : ℕ)
    (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : (A.map (fun q : ℚ => (q : ℝ))).PosSemidef)
    (hlo : ∀ i, 1 / (2 : ℝ) ^ B ≤ hA.isHermitian.eigenvalues i)
    (hhi : ∀ i, hA.isHermitian.eigenvalues i ≤ 1) :
    (encodeRationalMatrixData (storedSchulzSqrt t B A)).length ≤
      2 * n + 1 + n * n * (4 * (t + 2 + n) + 9) := by
  rw [encodeRationalMatrixData_length]
  have h := storedSchulzSqrt_magnitude_bits t B A hA hlo hhi
  have hn : n.size ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self
  nlinarith

end GeometricGaussianLHL

end SchulzOutputSize

section SchulzStateSize

/-!
## Binary magnitude bounds for every stored iterate

The spectral assumptions imply a uniform magnitude bound on the actual
rounded states. Every state lies on the chosen dyadic grid, including the
initial identity. Consequently both reduced numerator and denominator have
explicit polynomial binary-size bounds throughout the computation.
-/

set_option backward.isDefEq.respectTransparency false

open scoped MatrixOrder Matrix.Norms.L2Operator

namespace GeometricGaussianLHL

theorem roundedSchulz_state_norm {n : ℕ} (p B k : ℕ)
    (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : (A.map (fun q : ℚ => (q : ℝ))).PosSemidef)
    (hlo : ∀ i, 1 / (2 : ℝ) ^ B ≤ hA.isHermitian.eigenvalues i)
    (hhi : ∀ i, hA.isHermitian.eigenvalues i ≤ 1)
    (hp : (2 * B + 5) * k ≤ p) :
    ‖(roundedSchulzMatrixIterate p A k).map (fun q : ℚ => (q : ℝ))‖ ≤ (2 : ℝ) ^ B + 1 := by
  have he := (roundedSchulz_forward_error p B A hA hlo hhi k hp).trans
    (dyadic_error_budget_le_one hp)
  have hz := schulzMatrix_iterate_norm_le B k _ hA hlo hhi
  have ht := norm_le_norm_sub_add
    ((roundedSchulzMatrixIterate p A k).map (fun q : ℚ => (q : ℝ)))
    (schulzInvSqrtMatrixIterate (A.map (fun q : ℚ => (q : ℝ))) k)
  linarith

theorem roundedSchulz_state_entry {n : ℕ} (p B k : ℕ)
    (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : (A.map (fun q : ℚ => (q : ℝ))).PosSemidef)
    (hlo : ∀ i, 1 / (2 : ℝ) ^ B ≤ hA.isHermitian.eigenvalues i)
    (hhi : ∀ i, hA.isHermitian.eigenvalues i ≤ 1)
    (hp : (2 * B + 5) * k ≤ p) (i j : Fin n) :
    |roundedSchulzMatrixIterate p A k i j| ≤ (2 : ℚ) ^ (B + 1) := by
  apply rationalMatrix_entry_bound _ (B + 1) _ i j
  have hn := roundedSchulz_state_norm p B k A hA hlo hhi hp
  have h1 : 1 ≤ (2 : ℝ) ^ B := one_le_pow₀ (by norm_num)
  rw [pow_succ]
  linarith

theorem roundedSchulz_state_grid {n : ℕ} (p k : ℕ)
    (A : Matrix (Fin n) (Fin n) ℚ) (i j : Fin n) :
    dyadicRoundRat (p + n) (roundedSchulzMatrixIterate p A k i j) =
      roundedSchulzMatrixIterate p A k i j := by
  cases k with
  | zero =>
    change dyadicRoundRat (p + n) (if i = j then (1 : ℚ) else 0) =
      (if i = j then (1 : ℚ) else 0)
    by_cases hij : i = j
    · simp only [ite_eq_left hij]
      exact dyadicRoundRat_int_fixed (p + n) 1
    · simp only [ite_eq_right hij]
      exact dyadicRoundRat_int_fixed (p + n) 0
  | succ k =>
    simp only [roundedSchulzMatrixIterate, roundedSchulzMatrixStep, materializeMatrix_eq,
      dyadicRoundMatrix, dyadicRoundRat_idempotent]

theorem roundedSchulz_state_bits {n : ℕ} (p B k : ℕ)
    (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : (A.map (fun q : ℚ => (q : ℝ))).PosSemidef)
    (hlo : ∀ i, 1 / (2 : ℝ) ^ B ≤ hA.isHermitian.eigenvalues i)
    (hhi : ∀ i, hA.isHermitian.eigenvalues i ≤ 1)
    (hp : (2 * B + 5) * k ≤ p) :
    rationalMatrixMagnitudeBits (roundedSchulzMatrixIterate p A k) ≤
      n * n * (B + 2 * (p + n) + 4) := by
  unfold rationalMatrixMagnitudeBits
  calc
    _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, (B + 2 * (p + n) + 4) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      have h := dyadic_fixed_rational_bits (p + n) (B + 1)
        (roundedSchulzMatrixIterate p A k i j) (roundedSchulz_state_grid p k A i j)
        (roundedSchulz_state_entry p B k A hA hlo hhi hp i j)
      omega
    _ = _ := by simp [Nat.mul_assoc]

theorem storedSchulz_state_bits {n : ℕ} (s B K k : ℕ)
    (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : (A.map (fun q : ℚ => (q : ℝ))).PosSemidef)
    (hlo : ∀ i, 1 / (2 : ℝ) ^ B ≤ hA.isHermitian.eigenvalues i)
    (hhi : ∀ i, hA.isHermitian.eigenvalues i ≤ 1) (hk : k ≤ K) :
    rationalMatrixMagnitudeBits (rationalMatrixOfData
      (storedRoundedSchulzIterate (s + (2 * B + 5) * K) A k)) ≤
      n * n * (B + 2 * (s + (2 * B + 5) * K + n) + 4) := by
  rw [storedRoundedSchulzIterate_eq]
  apply roundedSchulz_state_bits _ B k A hA hlo hhi
  exact (Nat.mul_le_mul_left (2 * B + 5) hk).trans (Nat.le_add_left _ _)

end GeometricGaussianLHL

end SchulzStateSize

section StoredSchulzInverse

/-!
## Stored-data inverse approximation

The vector output refines the rational inverse approximation and inherits its
operator error. Accumulated arithmetic costs remain separate.
-/

set_option backward.isDefEq.respectTransparency false

open scoped MatrixOrder Matrix.Norms.L2Operator

namespace GeometricGaussianLHL

def storedSchulzInverse {n : ℕ} (t B : ℕ) (A : Matrix (Fin n) (Fin n) ℚ) : RationalMatrixData n :=
  let k := t + B + 4 + B
  let p := t + B + 4 + (2 * B + 5) * k
  let Z := storedRoundedSchulzIterate p A k
  rationalMatrixData (dyadicRoundMatrix (t + B + 4 + n) ((rationalMatrixOfData Z) ^ 2))

theorem storedSchulzInverse_eq {n : ℕ} (t B : ℕ) (A : Matrix (Fin n) (Fin n) ℚ) :
    rationalMatrixOfData (storedSchulzInverse t B A) = roundedSchulzInverse t B A := by
  simp only [storedSchulzInverse, rationalMatrixOfData_data, storedRoundedSchulzIterate_eq,
    roundedSchulzInverse, materializeMatrix_eq]

theorem storedSchulzInverse_operator_error {n : ℕ} (t B : ℕ)
    (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : (A.map (fun q : ℚ => (q : ℝ))).PosSemidef)
    (hlo : ∀ i, 1 / (2 : ℝ) ^ B ≤ hA.isHermitian.eigenvalues i)
    (hhi : ∀ i, hA.isHermitian.eigenvalues i ≤ 1) :
    ‖(Matrix.toEuclideanLin ((rationalMatrixOfData (storedSchulzInverse t B A)).map
        (fun q : ℚ => (q : ℝ)))).toContinuousLinearMap -
      (Matrix.toEuclideanLin ((A.map (fun q : ℚ => (q : ℝ)))⁻¹)).toContinuousLinearMap‖ ≤
      1 / (2 : ℝ) ^ t := by
  rw [storedSchulzInverse_eq]
  exact roundedSchulzInverse_operator_error t B A hA hlo hhi

end GeometricGaussianLHL

end StoredSchulzInverse

section IntegerSchulz

/-!
## The square-root iteration using stored integer numerators

Each intermediate matrix is an array of integer numerators with a common
dyadic denominator. Matrix multiplication, subtraction and Euclidean integer
division implement the previously certified rational iteration exactly.
The recursion returns stored data, and the final conversion to rationals
happens only after the integer iteration is complete.
-/

set_option backward.isDefEq.respectTransparency false

open scoped MatrixOrder Matrix.Norms.L2Operator

namespace GeometricGaussianLHL

def integerRoundedSchulzStep {n : ℕ} (q a : ℕ)
    (X N : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℤ :=
  (integerSchulzNumerator a (2 ^ q) X N).map
    (fun z => z / (2 * a * (2 ^ q) ^ 2 : ℕ))

theorem integerRoundedSchulzStep_refines {n : ℕ} (q a : ℕ) (ha : 0 < a)
    (X N : Matrix (Fin n) (Fin n) ℤ) :
    integerMatrixQuotient (2 ^ q) (integerRoundedSchulzStep q a X N) =
      dyadicRoundMatrix q (schulzInvSqrtMatrixStep
        (integerMatrixQuotient a X) (integerMatrixQuotient (2 ^ q) N)) := by
  rw [integerSchulzNumerator_step a (2 ^ q) ha (by positivity)]
  ext i j
  rw [integerMatrixQuotient_apply]
  simp only [integerRoundedSchulzStep, Matrix.map_apply, Nat.cast_pow, Nat.cast_ofNat,
    dyadicRoundMatrix, dyadicRoundRat, integerMatrixQuotient_apply,
    dyadicNumerator_schulz_denominator]

def storedIntegerSchulzIterate {n : ℕ} (q a : ℕ)
    (X : Matrix (Fin n) (Fin n) ℤ) : ℕ → IntegerMatrixData n
  | 0 => integerMatrixData ((2 ^ q : ℤ) • 1)
  | k + 1 =>
    let N := storedIntegerSchulzIterate q a X k
    integerMatrixData (integerRoundedSchulzStep q a X (integerMatrixOfData N))

theorem storedIntegerSchulzIterate_refines {n : ℕ} (p a k : ℕ) (ha : 0 < a)
    (X : Matrix (Fin n) (Fin n) ℤ) :
    integerMatrixQuotient (2 ^ (p + n))
        (integerMatrixOfData (storedIntegerSchulzIterate (p + n) a X k)) =
      roundedSchulzMatrixIterate p (integerMatrixQuotient a X) k := by
  induction k with
  | zero =>
    simp only [storedIntegerSchulzIterate, integerMatrixOfData_data,
      roundedSchulzMatrixIterate]
    convert integerMatrixQuotient_identity (n := n) (2 ^ (p + n)) (by positivity) using 1
    norm_cast
  | succ k ih =>
    simp only [storedIntegerSchulzIterate, integerMatrixOfData_data,
      integerRoundedSchulzStep_refines _ _ ha, ih,
      roundedSchulzMatrixIterate, roundedSchulzMatrixStep, materializeMatrix_eq]

def storedIntegerSchulzSqrt {n : ℕ} (t B a : ℕ)
    (X : Matrix (Fin n) (Fin n) ℤ) : IntegerMatrixData n :=
  let k := t + 2 + B
  let p := t + 2 + (2 * B + 5) * k
  let q := p + n
  let r := t + 2 + n
  let N := storedIntegerSchulzIterate q a X k
  integerMatrixData ((X * integerMatrixOfData N).map
    (fun z => (z * (2 : ℤ) ^ r) / (a * 2 ^ q : ℕ)))

def integerSchulzSqrtRational {n : ℕ} (t B a : ℕ)
    (X : Matrix (Fin n) (Fin n) ℤ) : RationalMatrixData n :=
  rationalMatrixData (integerMatrixQuotient (2 ^ (t + 2 + n))
    (integerMatrixOfData (storedIntegerSchulzSqrt t B a X)))

theorem integerSchulzSqrtRational_refines {n : ℕ} (t B a : ℕ) (ha : 0 < a)
    (X : Matrix (Fin n) (Fin n) ℤ) :
    rationalMatrixOfData (integerSchulzSqrtRational t B a X) =
      roundedSchulzSqrt t B (integerMatrixQuotient a X) := by
  simp only [integerSchulzSqrtRational, rationalMatrixOfData_data,
    storedIntegerSchulzSqrt, integerMatrixOfData_data]
  rw [integerMatrixQuotient_round, ← integerMatrixQuotient_mul,
    storedIntegerSchulzIterate_refines _ _ _ ha]
  simp only [roundedSchulzSqrt, materializeMatrix_eq]

theorem integerSchulzSqrtRational_eq {n : ℕ} (t B a : ℕ) (ha : 0 < a)
    (X : Matrix (Fin n) (Fin n) ℤ) :
    integerSchulzSqrtRational t B a X = storedSchulzSqrt t B (integerMatrixQuotient a X) := by
  have heq := (integerSchulzSqrtRational_refines t B a ha X).trans
    (storedSchulzSqrt_eq t B (integerMatrixQuotient a X)).symm
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  exact congrFun (congrFun heq ⟨i, hi⟩) ⟨j, hj⟩

theorem integerSchulzSqrtRational_operator_error {n : ℕ} (t B a : ℕ) (ha : 0 < a)
    (X : Matrix (Fin n) (Fin n) ℤ)
    (hX : ((integerMatrixQuotient a X).map (fun q : ℚ => (q : ℝ))).PosSemidef)
    (hlo : ∀ i, 1 / (2 : ℝ) ^ B ≤ hX.isHermitian.eigenvalues i)
    (hhi : ∀ i, hX.isHermitian.eigenvalues i ≤ 1) :
    ‖(Matrix.toEuclideanLin ((rationalMatrixOfData (integerSchulzSqrtRational t B a X)).map
        (fun q : ℚ => (q : ℝ)))).toContinuousLinearMap -
      (Matrix.toEuclideanLin (CFC.sqrt ((integerMatrixQuotient a X).map
        (fun q : ℚ => (q : ℝ))))).toContinuousLinearMap‖ ≤ 1 / (2 : ℝ) ^ t := by
  rw [integerSchulzSqrtRational_eq t B a ha X]
  exact storedSchulzSqrt_operator_error t B (integerMatrixQuotient a X) hX hlo hhi

theorem integerSchulzSqrtRational_encoded_length {n : ℕ} (t B a : ℕ) (ha : 0 < a)
    (X : Matrix (Fin n) (Fin n) ℤ)
    (hX : ((integerMatrixQuotient a X).map (fun q : ℚ => (q : ℝ))).PosSemidef)
    (hlo : ∀ i, 1 / (2 : ℝ) ^ B ≤ hX.isHermitian.eigenvalues i)
    (hhi : ∀ i, hX.isHermitian.eigenvalues i ≤ 1) :
    (encodeRationalMatrixData (integerSchulzSqrtRational t B a X)).length ≤
      2 * n + 1 + n * n * (4 * (t + 2 + n) + 9) := by
  rw [integerSchulzSqrtRational_eq t B a ha X]
  exact storedSchulzSqrt_encoded_length t B (integerMatrixQuotient a X) hX hlo hhi

end GeometricGaussianLHL

end IntegerSchulz

section StoredSchulzEncoding

/-!
## Encoded lengths of stored Schulz states
-/

set_option backward.isDefEq.respectTransparency false

open scoped MatrixOrder Matrix.Norms.L2Operator

namespace GeometricGaussianLHL

theorem storedSchulz_state_encoded_length {n : ℕ} (s B K k : ℕ)
    (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : (A.map (fun q : ℚ => (q : ℝ))).PosSemidef)
    (hlo : ∀ i, 1 / (2 : ℝ) ^ B ≤ hA.isHermitian.eigenvalues i)
    (hhi : ∀ i, hA.isHermitian.eigenvalues i ≤ 1) (hk : k ≤ K) :
    (encodeRationalMatrixData (storedRoundedSchulzIterate (s + (2 * B + 5) * K) A k)).length ≤
      2 * n + 1 + 2 * (n * n * (B + 2 * (s + (2 * B + 5) * K + n) + 4)) + n * n := by
  rw [encodeRationalMatrixData_length]
  have h := storedSchulz_state_bits s B K k A hA hlo hhi hk
  have hn : n.size ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self
  omega

end GeometricGaussianLHL

end StoredSchulzEncoding

section IntegerSchulzCost

/-!
## Arithmetic costs of the stored integer Schulz step

The cubic numerator is evaluated through three stored matrix products. Scalar
construction, matrix construction, subtraction and entrywise integer division
are charged explicitly. The cost bounds use the actual intermediate integers.
-/

namespace GeometricGaussianLHL

def costedIntegerScalarMatrix (n : ℕ) (c : ℤ) : Costed (IntegerMatrixData n) :=
  costedIntegerMatrixOfFn fun i j => Costed.charge (c.natAbs.size + n.size + 1) (if i = j then c else 0)

theorem costedIntegerScalarMatrix_value (n : ℕ) (c : ℤ) :
    integerMatrixOfData (costedIntegerScalarMatrix n c).value = c • 1 := by
  rw [costedIntegerScalarMatrix, costedIntegerMatrixOfFn_value]
  ext i j
  by_cases h : i = j <;> simp [Costed.charge, h]

theorem costedIntegerScalarMatrix_steps_le (n : ℕ) (c : ℤ) (L : ℕ)
    (hc : c.natAbs.size ≤ L) :
    (costedIntegerScalarMatrix n c).steps ≤ integerMatrixTraversalBudget n (L + n + 1) := by
  apply costedIntegerMatrixOfFn_steps_le
  intro i j
  have hn : n.size ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self
  dsimp [Costed.charge]
  omega

theorem costedIntegerScalarMatrix_data (n : ℕ) (c : ℤ) :
    (costedIntegerScalarMatrix n c).value = integerMatrixData (c • 1) := by
  rw [← integerMatrixData_ofData (costedIntegerScalarMatrix n c).value, costedIntegerScalarMatrix_value]

def costedIntegerSchulzScale (k : ℤ) (a d : ℕ) : Costed ℤ :=
  (costedIntMul (d : ℤ) d).bind fun dd =>
    (costedIntMul k a).bind fun ka => costedIntMul ka dd

@[simp] theorem costedIntegerSchulzScale_value (k : ℤ) (a d : ℕ) :
    (costedIntegerSchulzScale k a d).value = k * a * (d : ℤ) ^ 2 := by
  simp [costedIntegerSchulzScale, costedIntMul, pow_two]

theorem costedIntegerSchulzScale_size (k : ℤ) (a d L : ℕ)
    (hk : k.natAbs.size ≤ 2) (ha : a.size ≤ L) (hd : d.size ≤ L) :
    (costedIntegerSchulzScale k a d).value.natAbs.size ≤ 3 * L + 5 := by
  have ha' : (a : ℤ).natAbs.size ≤ L := ha
  have hd' : (d : ℤ).natAbs.size ≤ L := hd
  have hka := integer_mul_size_le k a 2 L hk ha'
  have hdd := integer_mul_size_le d d L L hd' hd'
  have h := integer_mul_size_le (k * a) ((d : ℤ) * d) (2 + L + 1) (L + L + 1) hka hdd
  simpa [pow_two, show 2 + L + 1 + (L + L + 1) + 1 = 3 * L + 5 by omega] using h

private theorem intMul_steps_le (a b : ℤ) (L : ℕ)
    (ha : a.natAbs.size ≤ L) (hb : b.natAbs.size ≤ L) :
    (costedIntMul a b).steps ≤ (2 * L + 1) ^ 2 :=
  Nat.pow_le_pow_left (by unfold integerOperandBits; omega) 2

theorem costedIntegerSchulzScale_steps_le (k : ℤ) (a d L : ℕ)
    (hk : k.natAbs.size ≤ 2) (ha : a.size ≤ L) (hd : d.size ≤ L) :
    (costedIntegerSchulzScale k a d).steps ≤ 3 * (2 * (3 * L + 5) + 1) ^ 2 := by
  have hka := integer_mul_size_le k a 2 L hk ha
  have hdd := integer_mul_size_le d d L L hd hd
  have h₁ := intMul_steps_le d d (3 * L + 5) (by simpa using hd.trans (by omega)) (by simpa using hd.trans (by omega))
  have h₂ := intMul_steps_le k a (3 * L + 5) (hk.trans (by omega)) (by simpa using ha.trans (by omega))
  have h₃ := intMul_steps_le (k * a) ((d : ℤ) * d) (3 * L + 5) (hka.trans (by omega)) (hdd.trans (by omega))
  simp only [costedIntegerSchulzScale, Costed.bind_steps, costedIntMul] at *
  omega

def costedIntegerSchulzDiagonal (n a d : ℕ) : Costed (IntegerMatrixData n) :=
  (costedIntegerSchulzScale 3 a d).bind (costedIntegerScalarMatrix n)

theorem costedIntegerSchulzDiagonal_data (n a d : ℕ) :
    (costedIntegerSchulzDiagonal n a d).value = integerMatrixData ((3 * (a : ℤ) * (d : ℤ) ^ 2) • 1) := by
  simp only [costedIntegerSchulzDiagonal, Costed.bind_value, costedIntegerScalarMatrix_data,
    costedIntegerSchulzScale_value]

def costedIntegerSchulzSquareProduct {n : ℕ} (X N : IntegerMatrixData n) : Costed (IntegerMatrixData n) :=
  (costedIntegerMatrixMul N N).bind (costedIntegerMatrixMul X)

theorem costedIntegerSchulzSquareProduct_data {n : ℕ} (X N : IntegerMatrixData n) :
    (costedIntegerSchulzSquareProduct X N).value = integerMatrixData (integerMatrixOfData X * integerMatrixOfData N ^ 2) := by
  simp only [costedIntegerSchulzSquareProduct, Costed.bind_value, costedIntegerMatrixMul_data,
    integerMatrixOfData_data, pow_two]

def costedIntegerSchulzInner {n : ℕ} (a d : ℕ) (X N : IntegerMatrixData n) : Costed (IntegerMatrixData n) :=
  (costedIntegerSchulzDiagonal n a d).bind fun S =>
    (costedIntegerSchulzSquareProduct X N).bind (costedIntegerMatrixSub S)

theorem costedIntegerSchulzInner_data {n : ℕ} (a d : ℕ) (X N : IntegerMatrixData n) :
    (costedIntegerSchulzInner a d X N).value = integerMatrixData
      ((3 * (a : ℤ) * (d : ℤ) ^ 2) • 1 - integerMatrixOfData X * integerMatrixOfData N ^ 2) := by
  rw [costedIntegerSchulzInner, Costed.bind_value, costedIntegerSchulzDiagonal_data,
    Costed.bind_value, costedIntegerSchulzSquareProduct_data,
    costedIntegerMatrixSub_data, integerMatrixOfData_data, integerMatrixOfData_data]

def costedIntegerSchulzNumerator {n : ℕ} (a d : ℕ) (X N : IntegerMatrixData n) : Costed (IntegerMatrixData n) :=
  (costedIntegerSchulzInner a d X N).bind (costedIntegerMatrixMul N)

theorem costedIntegerSchulzNumerator_value {n : ℕ} (a d : ℕ) (X N : IntegerMatrixData n) :
    integerMatrixOfData (costedIntegerSchulzNumerator a d X N).value =
      integerSchulzNumerator a d (integerMatrixOfData X) (integerMatrixOfData N) := by
  rw [costedIntegerSchulzNumerator, Costed.bind_value, costedIntegerSchulzInner_data,
    costedIntegerMatrixMul_value, integerMatrixOfData_data]
  rfl

theorem costedIntegerSchulzNumerator_data {n : ℕ} (a d : ℕ) (X N : IntegerMatrixData n) :
    (costedIntegerSchulzNumerator a d X N).value =
      integerMatrixData (integerSchulzNumerator a d (integerMatrixOfData X) (integerMatrixOfData N)) := by
  rw [← integerMatrixData_ofData (costedIntegerSchulzNumerator a d X N).value, costedIntegerSchulzNumerator_value]

def integerSchulzOperandBudget (n L : ℕ) : ℕ := 8 * (n + L + 1)

def integerSchulzNumeratorBudget (n L : ℕ) : ℕ :=
  let M := integerSchulzOperandBudget n L
  3 * (2 * M + 1) ^ 2 + integerMatrixTraversalBudget n (M + n + 1) +
    3 * integerMatrixMulBudget n M + integerMatrixTraversalBudget n (2 * M + 1)

theorem costedIntegerSchulzNumerator_steps_le {n : ℕ} (a d L : ℕ) (X N : IntegerMatrixData n)
    (ha : a.size ≤ L) (hd : d.size ≤ L)
    (hX : ∀ i j, (integerMatrixOfData X i j).natAbs.size ≤ L)
    (hN : ∀ i j, (integerMatrixOfData N i j).natAbs.size ≤ L) :
    (costedIntegerSchulzNumerator a d X N).steps ≤ integerSchulzNumeratorBudget n L := by
  let M := integerSchulzOperandBudget n L
  let C := costedIntegerSchulzScale 3 a d
  let S := costedIntegerScalarMatrix n C.value
  let NN := costedIntegerMatrixMul N N
  let XNN := costedIntegerMatrixMul X NN.value
  let D := costedIntegerMatrixSub S.value XNN.value
  have hLM : L ≤ M := by dsimp [M, integerSchulzOperandBudget]; omega
  have hM : 3 * n + 4 * L + 7 ≤ M := by dsimp [M, integerSchulzOperandBudget]; omega
  have hc : C.value.natAbs.size ≤ 3 * L + 5 := costedIntegerSchulzScale_size 3 a d L (by decide) ha hd
  have hS (i j) : (integerMatrixOfData S.value i j).natAbs.size ≤ 3 * L + 5 := by
    rw [costedIntegerScalarMatrix_value]
    exact (Nat.size_le_size (integerMatrix_scalar_identity_bound C.value i j)).trans hc
  have hNN := costedIntegerMatrixMul_size_le N N L hN hN
  have hXNN := costedIntegerMatrixMul_size_le X NN.value (n + 2 * L + 1)
    (fun i j => (hX i j).trans (by omega)) hNN
  have hD (i j) : (integerMatrixOfData D.value i j).natAbs.size ≤ 3 * n + 4 * L + 7 := by
    rw [costedIntegerMatrixSub_value]
    exact integer_sub_size_le _ _ (3 * n + 4 * L + 5)
      ((hS i j).trans (by omega)) ((hXNN i j).trans (by omega))
  have hCs : C.steps ≤ 3 * (2 * M + 1) ^ 2 :=
    (costedIntegerSchulzScale_steps_le 3 a d L (by decide) ha hd).trans
      (Nat.mul_le_mul_left 3 (Nat.pow_le_pow_left (by omega) 2))
  have hSs := costedIntegerScalarMatrix_steps_le n C.value M (hc.trans (by omega))
  have hNNs := costedIntegerMatrixMul_steps_le N N M (fun i j => (hN i j).trans hLM) (fun i j => (hN i j).trans hLM)
  have hXNNs := costedIntegerMatrixMul_steps_le X NN.value M (fun i j => (hX i j).trans hLM)
    (fun i j => (hNN i j).trans (by omega))
  have hDs := costedIntegerMatrixSub_steps_le S.value XNN.value M
    (fun i j => (hS i j).trans (by omega)) (fun i j => (hXNN i j).trans (by omega))
  have hTs := costedIntegerMatrixMul_steps_le N D.value M (fun i j => (hN i j).trans hLM)
    (fun i j => (hD i j).trans hM)
  change S.steps ≤ _ at hSs
  change NN.steps ≤ _ at hNNs
  change XNN.steps ≤ _ at hXNNs
  change D.steps ≤ _ at hDs
  change ((C.steps + S.steps) + ((NN.steps + XNN.steps) + D.steps)) + (costedIntegerMatrixMul N D.value).steps ≤ _
  change _ ≤ 3 * (2 * M + 1) ^ 2 + integerMatrixTraversalBudget n (M + n + 1) +
    3 * integerMatrixMulBudget n M + integerMatrixTraversalBudget n (2 * M + 1)
  omega

def costedIntegerSchulzStep {n : ℕ} (q a : ℕ) (X N : IntegerMatrixData n) : Costed (IntegerMatrixData n) :=
  (Costed.charge (q + 1) (2 ^ q : ℕ)).bind fun d =>
    (costedIntegerSchulzNumerator a d X N).bind fun P =>
      (costedIntegerSchulzScale 2 a d).bind fun v =>
        costedIntegerMatrixOfFn fun i j => costedIntDiv (integerMatrixOfData P i j) v

theorem costedIntegerSchulzStep_value {n : ℕ} (q a : ℕ) (X N : IntegerMatrixData n) :
    integerMatrixOfData (costedIntegerSchulzStep q a X N).value =
      integerRoundedSchulzStep q a (integerMatrixOfData X) (integerMatrixOfData N) := by
  rw [costedIntegerSchulzStep, Costed.bind_value]
  dsimp only [Costed.charge]
  rw [Costed.bind_value, costedIntegerSchulzNumerator_data, Costed.bind_value,
    costedIntegerSchulzScale_value, costedIntegerMatrixOfFn_value]
  simp only [integerMatrixOfData_data]
  ext i j
  simp [costedIntDiv, integerRoundedSchulzStep]

def integerSchulzStepBudget (n L : ℕ) : ℕ :=
  let M := integerSchulzOperandBudget n L
  L + integerSchulzNumeratorBudget n L + 3 * (2 * M + 1) ^ 2 +
    integerMatrixTraversalBudget n ((2 * M + 1) ^ 2)

theorem costedIntegerSchulzStep_steps_le {n : ℕ} (q a L : ℕ) (X N : IntegerMatrixData n)
    (hq : q + 1 ≤ L) (ha : a.size ≤ L)
    (hX : ∀ i j, (integerMatrixOfData X i j).natAbs.size ≤ L)
    (hN : ∀ i j, (integerMatrixOfData N i j).natAbs.size ≤ L) :
    (costedIntegerSchulzStep q a X N).steps ≤ integerSchulzStepBudget n L := by
  let M := integerSchulzOperandBudget n L
  let P := costedIntegerSchulzNumerator a (2 ^ q) X N
  let V := costedIntegerSchulzScale 2 a (2 ^ q)
  have hd : (2 ^ q).size ≤ L := by simpa only [Nat.size_pow] using hq
  have hM : 4 * L + 3 * n + 5 ≤ M := by dsimp [M, integerSchulzOperandBudget]; omega
  have hP (i j) : (integerMatrixOfData P.value i j).natAbs.size ≤ M := by
    rw [costedIntegerSchulzNumerator_value]
    have h := integerSchulzNumerator_size a (2 ^ q) L L (integerMatrixOfData X) (integerMatrixOfData N)
      (Nat.size_le.mp ha).le (Nat.size_le.mp hd).le
      (fun i j => (Nat.size_le.mp (hX i j)).le) (fun i j => (Nat.size_le.mp (hN i j)).le) i j
    omega
  have hV : V.value.natAbs.size ≤ M :=
    (costedIntegerSchulzScale_size 2 a (2 ^ q) L (by decide) ha hd).trans (by omega)
  have hPs := costedIntegerSchulzNumerator_steps_le a (2 ^ q) L X N ha hd hX hN
  have hVs : V.steps ≤ 3 * (2 * M + 1) ^ 2 :=
    (costedIntegerSchulzScale_steps_le 2 a (2 ^ q) L (by decide) ha hd).trans
      (Nat.mul_le_mul_left 3 (Nat.pow_le_pow_left (by omega) 2))
  have hDs := costedIntegerMatrixOfFn_steps_le
    (fun i j => costedIntDiv (integerMatrixOfData P.value i j) V.value) ((2 * M + 1) ^ 2)
    (by intro i j; apply Nat.pow_le_pow_left; unfold integerOperandBits; have h := hP i j; omega)
  change P.steps ≤ _ at hPs
  change q + 1 + (P.steps + (V.steps +
    (costedIntegerMatrixOfFn (fun i j => costedIntDiv (integerMatrixOfData P.value i j) V.value)).steps)) ≤ _
  change _ ≤ L + integerSchulzNumeratorBudget n L + 3 * (2 * M + 1) ^ 2 +
    integerMatrixTraversalBudget n ((2 * M + 1) ^ 2)
  omega

end GeometricGaussianLHL

end IntegerSchulzCost

section IntegerSchulzInverse

/-!
## Stored integer inverse approximation

The integer operations implement the rational inverse formula exactly.
Arithmetic cost bounds are handled independently of this accuracy refinement.
-/

set_option backward.isDefEq.respectTransparency false

open scoped MatrixOrder Matrix.Norms.L2Operator

namespace GeometricGaussianLHL

def storedIntegerSchulzInverse {n : ℕ} (t B a : ℕ)
    (X : Matrix (Fin n) (Fin n) ℤ) : IntegerMatrixData n :=
  let k := t + B + 4 + B
  let p := t + B + 4 + (2 * B + 5) * k
  let q := p + n
  let r := t + B + 4 + n
  let N := storedIntegerSchulzIterate q a X k
  integerMatrixData ((integerMatrixOfData N * integerMatrixOfData N).map (fun z => (z * (2 : ℤ) ^ r) / (2 ^ q * 2 ^ q : ℕ)))

def integerSchulzInverseRational {n : ℕ} (t B a : ℕ)
    (X : Matrix (Fin n) (Fin n) ℤ) : RationalMatrixData n :=
  rationalMatrixData (integerMatrixQuotient (2 ^ (t + B + 4 + n))
    (integerMatrixOfData (storedIntegerSchulzInverse t B a X)))

theorem integerSchulzInverseRational_refines {n : ℕ} (t B a : ℕ) (ha : 0 < a)
    (X : Matrix (Fin n) (Fin n) ℤ) :
    rationalMatrixOfData (integerSchulzInverseRational t B a X) =
      roundedSchulzInverse t B (integerMatrixQuotient a X) := by
  simp only [integerSchulzInverseRational, rationalMatrixOfData_data,
    storedIntegerSchulzInverse, integerMatrixOfData_data]
  rw [integerMatrixQuotient_round, ← integerMatrixQuotient_mul,
    storedIntegerSchulzIterate_refines _ _ _ ha]
  simp only [roundedSchulzInverse, materializeMatrix_eq, pow_two]

theorem integerSchulzInverseRational_eq {n : ℕ} (t B a : ℕ) (ha : 0 < a)
    (X : Matrix (Fin n) (Fin n) ℤ) :
    integerSchulzInverseRational t B a X = storedSchulzInverse t B (integerMatrixQuotient a X) := by
  have heq := (integerSchulzInverseRational_refines t B a ha X).trans
    (storedSchulzInverse_eq t B (integerMatrixQuotient a X)).symm
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  exact congrFun (congrFun heq ⟨i, hi⟩) ⟨j, hj⟩

theorem integerSchulzInverseRational_operator_error {n : ℕ} (t B a : ℕ) (ha : 0 < a)
    (X : Matrix (Fin n) (Fin n) ℤ)
    (hX : ((integerMatrixQuotient a X).map (fun q : ℚ => (q : ℝ))).PosSemidef)
    (hlo : ∀ i, 1 / (2 : ℝ) ^ B ≤ hX.isHermitian.eigenvalues i)
    (hhi : ∀ i, hX.isHermitian.eigenvalues i ≤ 1) :
    ‖(Matrix.toEuclideanLin ((rationalMatrixOfData (integerSchulzInverseRational t B a X)).map
        (fun q : ℚ => (q : ℝ)))).toContinuousLinearMap -
      (Matrix.toEuclideanLin (((integerMatrixQuotient a X).map
        (fun q : ℚ => (q : ℝ)))⁻¹)).toContinuousLinearMap‖ ≤ 1 / (2 : ℝ) ^ t := by
  rw [integerSchulzInverseRational_eq t B a ha X]
  exact storedSchulzInverse_operator_error t B (integerMatrixQuotient a X) hX hlo hhi

end GeometricGaussianLHL

end IntegerSchulzInverse

section IntegerSchulzSize

/-!
## Integer sizes throughout the stored iteration

The analytic forward-error bound controls the actual integer states. The
common-denominator conversion bounds the input integers. Together they give
explicit binary-length bounds for the cubic numerators before division,
the divisors, and scaled matrix products used for the final output.
-/

set_option backward.isDefEq.respectTransparency false

open scoped MatrixOrder Matrix.Norms.L2Operator

namespace GeometricGaussianLHL

theorem integerMatrixQuotient_dyadic_bound {n : ℕ} (q B : ℕ)
    (N : Matrix (Fin n) (Fin n) ℤ) (i j : Fin n)
    (h : |integerMatrixQuotient (2 ^ q) N i j| ≤ (2 : ℚ) ^ B) :
    (N i j).natAbs ≤ 2 ^ (B + q) := by
  rw [integerMatrixQuotient_apply, abs_div] at h
  have hd : (0 : ℚ) < (2 ^ q : ℕ) := by positivity
  rw [abs_of_pos hd] at h
  have hm := (div_le_iff₀ hd).mp h
  have he : ((N i j).natAbs : ℚ) = |(N i j : ℚ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  rw [← he] at hm
  have hm' : ((N i j).natAbs : ℚ) ≤ (2 : ℚ) ^ (B + q) := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat, pow_add] using hm
  exact_mod_cast hm'

theorem storedIntegerSchulz_state_bound {n : ℕ} (p B k : ℕ)
    (A : Matrix (Fin n) (Fin n) ℚ) (a : ℕ) (X : Matrix (Fin n) (Fin n) ℤ)
    (ha : 0 < a) (hrep : integerMatrixQuotient a X = A)
    (hA : (A.map (fun q : ℚ => (q : ℝ))).PosSemidef)
    (hlo : ∀ i, 1 / (2 : ℝ) ^ B ≤ hA.isHermitian.eigenvalues i)
    (hhi : ∀ i, hA.isHermitian.eigenvalues i ≤ 1)
    (hp : (2 * B + 5) * k ≤ p) (i j : Fin n) :
    (integerMatrixOfData (storedIntegerSchulzIterate (p + n)
      a X k) i j).natAbs ≤
      2 ^ (B + 1 + (p + n)) := by
  have heq := storedIntegerSchulzIterate_refines p a k
    ha X
  rw [hrep] at heq
  have he := roundedSchulz_state_entry p B k A hA hlo hhi hp i j
  rw [← heq] at he
  exact integerMatrixQuotient_dyadic_bound (p + n) (B + 1) _ i j he

theorem storedIntegerSchulz_common_state_bound {n : ℕ} (p B k : ℕ)
    (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : (A.map (fun q : ℚ => (q : ℝ))).PosSemidef)
    (hlo : ∀ i, 1 / (2 : ℝ) ^ B ≤ hA.isHermitian.eigenvalues i)
    (hhi : ∀ i, hA.isHermitian.eigenvalues i ≤ 1)
    (hp : (2 * B + 5) * k ≤ p) (i j : Fin n) :
    (integerMatrixOfData (storedIntegerSchulzIterate (p + n)
      (rationalMatrixCommonDenominator A) (rationalMatrixCommonNumerators A) k) i j).natAbs ≤
      2 ^ (B + 1 + (p + n)) := by
  exact storedIntegerSchulz_state_bound p B k A (rationalMatrixCommonDenominator A)
    (rationalMatrixCommonNumerators A) (rationalMatrixCommonDenominator_pos A)
    (rationalMatrix_common_reconstruct A) hA hlo hhi hp i j

theorem storedIntegerSchulz_state_size {n : ℕ} (p B k : ℕ)
    (A : Matrix (Fin n) (Fin n) ℚ) (a : ℕ) (X : Matrix (Fin n) (Fin n) ℤ)
    (ha : 0 < a) (hrep : integerMatrixQuotient a X = A)
    (hA : (A.map (fun q : ℚ => (q : ℝ))).PosSemidef)
    (hlo : ∀ i, 1 / (2 : ℝ) ^ B ≤ hA.isHermitian.eigenvalues i)
    (hhi : ∀ i, hA.isHermitian.eigenvalues i ≤ 1)
    (hp : (2 * B + 5) * k ≤ p) (i j : Fin n) :
    (integerMatrixOfData (storedIntegerSchulzIterate (p + n)
      a X k) i j).natAbs.size ≤
      B + p + n + 2 := by
  apply Nat.size_le.mpr
  have h := storedIntegerSchulz_state_bound p B k A a X ha hrep hA hlo hhi hp i j
  have hp2 : 0 < 2 ^ (B + 1 + (p + n)) := by positivity
  calc
    _ ≤ 2 ^ (B + 1 + (p + n)) := h
    _ < 2 ^ (B + 1 + (p + n)) * 2 := by omega
    _ = _ := by rw [← pow_succ]; congr 1; omega

theorem storedIntegerSchulz_common_state_size {n : ℕ} (p B k : ℕ)
    (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : (A.map (fun q : ℚ => (q : ℝ))).PosSemidef)
    (hlo : ∀ i, 1 / (2 : ℝ) ^ B ≤ hA.isHermitian.eigenvalues i)
    (hhi : ∀ i, hA.isHermitian.eigenvalues i ≤ 1)
    (hp : (2 * B + 5) * k ≤ p) (i j : Fin n) :
    (integerMatrixOfData (storedIntegerSchulzIterate (p + n)
      (rationalMatrixCommonDenominator A) (rationalMatrixCommonNumerators A) k) i j).natAbs.size ≤
      B + p + n + 2 := by
  exact storedIntegerSchulz_state_size p B k A (rationalMatrixCommonDenominator A)
    (rationalMatrixCommonNumerators A) (rationalMatrixCommonDenominator_pos A)
    (rationalMatrix_common_reconstruct A) hA hlo hhi hp i j

theorem storedIntegerSchulz_common_numerator_size {n : ℕ} (p B k : ℕ)
    (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : (A.map (fun q : ℚ => (q : ℝ))).PosSemidef)
    (hlo : ∀ i, 1 / (2 : ℝ) ^ B ≤ hA.isHermitian.eigenvalues i)
    (hhi : ∀ i, hA.isHermitian.eigenvalues i ≤ 1)
    (hp : (2 * B + 5) * k ≤ p) (i j : Fin n) :
    (integerSchulzNumerator (rationalMatrixCommonDenominator A) (2 ^ (p + n))
      (rationalMatrixCommonNumerators A)
      (integerMatrixOfData (storedIntegerSchulzIterate (p + n)
        (rationalMatrixCommonDenominator A) (rationalMatrixCommonNumerators A) k)) i j).natAbs.size ≤
      2 * rationalMatrixMagnitudeBits A + 3 * (B + 1 + (p + n)) + 3 * n + 3 := by
  apply integerSchulzNumerator_size
  · exact (rationalMatrixCommonDenominator_le_pow A).trans
      (Nat.pow_le_pow_right (by omega) (by omega))
  · exact Nat.pow_le_pow_right (by omega) (by omega)
  · exact rationalMatrixCommonNumerators_natAbs A
  · exact storedIntegerSchulz_common_state_bound p B k A hA hlo hhi hp

theorem integerSchulz_divisor_size (q a U : ℕ) (ha : a ≤ 2 ^ U) :
    (2 * a * (2 ^ q) ^ 2).size ≤ U + 2 * q + 2 := by
  have h : 2 * a * (2 ^ q) ^ 2 ≤ 2 ^ (U + 2 * q + 1) := by
    calc
      _ ≤ 2 * 2 ^ U * (2 ^ q) ^ 2 :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 ha)
      _ = _ := by simp only [Nat.mul_comm 2 q, pow_add, pow_mul]; ring
  apply Nat.size_le.mpr
  have hp : 0 < 2 ^ (U + 2 * q + 1) := by positivity
  calc
    _ ≤ 2 ^ (U + 2 * q + 1) := h
    _ < 2 ^ (U + 2 * q + 1) * 2 := by omega
    _ = _ := by rw [← pow_succ]

end GeometricGaussianLHL

end IntegerSchulzSize

section RationalMatrixDenominator

/-!
## Converting arbitrary rational matrices to integer input data

The product of the input denominators is a positive common denominator.
The resulting integer numerators reconstruct the original rational matrix
exactly. Both the denominator and these numerators have polynomial binary
length in the actual reduced rational input size.
-/

set_option backward.isDefEq.respectTransparency false

namespace GeometricGaussianLHL

def storedIntegerSqrtFromRational {n : ℕ} (t B : ℕ)
    (A : Matrix (Fin n) (Fin n) ℚ) : RationalMatrixData n :=
  let a := rationalMatrixCommonDenominator A
  let X := integerMatrixData (fun i j => (A i j).num * (a / (A i j).den : ℕ))
  integerSchulzSqrtRational t B a (integerMatrixOfData X)

theorem storedIntegerSqrtFromRational_eq {n : ℕ} (t B : ℕ)
    (A : Matrix (Fin n) (Fin n) ℚ) :
    storedIntegerSqrtFromRational t B A = storedSchulzSqrt t B A := by
  rw [storedIntegerSqrtFromRational, integerMatrixOfData_data]
  change integerSchulzSqrtRational t B (rationalMatrixCommonDenominator A)
    (rationalMatrixCommonNumerators A) = _
  rw [
    integerSchulzSqrtRational_eq _ _ _ (rationalMatrixCommonDenominator_pos A),
    rationalMatrix_common_reconstruct]

end GeometricGaussianLHL

end RationalMatrixDenominator

section StoredSchulzCost

/-!
## Total costs along the actual stored Schulz trajectory

The computed predecessor is passed as stored data to each step. Analytic
rounding invariants bound its integer bit lengths uniformly, which bounds the
accumulated arithmetic costs of the entire iteration. The spectral budget is
an explicit parameter at this stage; input normalization derives it from the
finite rational input in the outer numerical algorithm.
-/

set_option backward.isDefEq.respectTransparency false
open scoped MatrixOrder Matrix.Norms.L2Operator
namespace GeometricGaussianLHL

def costedStoredSchulzIterate {n : ℕ} (q a : ℕ) (X : IntegerMatrixData n) : ℕ → Costed (IntegerMatrixData n)
  | 0 => (Costed.charge (q + 1) (2 ^ q : ℤ)).bind (costedIntegerScalarMatrix n)
  | k + 1 => (costedStoredSchulzIterate q a X k).bind (costedIntegerSchulzStep q a X)

theorem costedStoredSchulzIterate_value {n : ℕ} (q a k : ℕ) (X : IntegerMatrixData n) :
    integerMatrixOfData (costedStoredSchulzIterate q a X k).value =
      integerMatrixOfData (storedIntegerSchulzIterate q a (integerMatrixOfData X) k) := by
  induction k with
  | zero => simp only [costedStoredSchulzIterate, Costed.bind_value, Costed.charge,
      costedIntegerScalarMatrix_value, storedIntegerSchulzIterate, integerMatrixOfData_data]
  | succ k ih => simp only [costedStoredSchulzIterate, Costed.bind_value,
      costedIntegerSchulzStep_value, storedIntegerSchulzIterate, integerMatrixOfData_data, ih]

def integerSchulzInitialBudget (n q : ℕ) : ℕ := q + 1 + integerMatrixTraversalBudget n (q + n + 2)

theorem costedStoredSchulzIterate_initial_steps {n : ℕ} (q a : ℕ) (X : IntegerMatrixData n) :
    (costedStoredSchulzIterate q a X 0).steps ≤ integerSchulzInitialBudget n q := by
  have hc : ((2 : ℤ) ^ q).natAbs.size ≤ q + 1 := by simp [Int.natAbs_pow, Nat.size_pow]
  simpa [costedStoredSchulzIterate, Costed.charge, integerSchulzInitialBudget, Nat.add_assoc,
    Nat.add_left_comm, Nat.add_comm] using
    Nat.add_le_add_left (costedIntegerScalarMatrix_steps_le n ((2 : ℤ) ^ q) (q + 1) hc) (q + 1)

def integerSchulzIterationBudget (n U B p k : ℕ) : ℕ :=
  integerSchulzInitialBudget n (p + n) + k * integerSchulzStepBudget n (U + B + p + n + 2)

theorem costedStoredSchulzIterate_steps_le {n : ℕ} (p B k a U : ℕ) (X : IntegerMatrixData n)
    (ha : 0 < a) (has : a.size ≤ U)
    (hXs : ∀ i j, (integerMatrixOfData X i j).natAbs.size ≤ U)
    (hA : ((integerMatrixQuotient a (integerMatrixOfData X)).map (fun q : ℚ => (q : ℝ))).PosSemidef)
    (hlo : ∀ i, 1 / (2 : ℝ) ^ B ≤ hA.isHermitian.eigenvalues i)
    (hhi : ∀ i, hA.isHermitian.eigenvalues i ≤ 1)
    (hp : (2 * B + 5) * k ≤ p) :
    (costedStoredSchulzIterate (p + n) a X k).steps ≤ integerSchulzIterationBudget n U B p k := by
  induction k with
  | zero => simpa [integerSchulzIterationBudget] using costedStoredSchulzIterate_initial_steps (p + n) a X
  | succ k ih =>
    have hpk : (2 * B + 5) * k ≤ p := by nlinarith
    have hprev := ih hpk
    have hN (i j) :
        (integerMatrixOfData (costedStoredSchulzIterate (p + n) a X k).value i j).natAbs.size ≤
          U + B + p + n + 2 := by
      rw [costedStoredSchulzIterate_value]
      exact (storedIntegerSchulz_state_size p B k _ a (integerMatrixOfData X) ha rfl hA hlo hhi hpk i j).trans
        (by omega)
    have hstep := costedIntegerSchulzStep_steps_le (p + n) a (U + B + p + n + 2) X
      (costedStoredSchulzIterate (p + n) a X k).value (by omega) (has.trans (by omega))
      (fun i j => (hXs i j).trans (by omega)) hN
    simp only [costedStoredSchulzIterate, Costed.bind_steps]
    apply (Nat.add_le_add hprev hstep).trans_eq
    unfold integerSchulzIterationBudget
    ring

theorem polyBound_integerDotStepBudget {n L : ℕ → ℕ}
    (hn : PolynomialCostBound n) (hL : PolynomialCostBound L) :
    PolynomialCostBound (fun x => integerDotStepBudget (n x) (L x)) :=
  ((((((PolynomialCostBound.const 2).mul hL).add (PolynomialCostBound.const 1)).pow 2).add hn).add
    ((PolynomialCostBound.const 4).mul hL)).add (PolynomialCostBound.const 4)

theorem polyBound_integerMatrixTraversalBudget {n B : ℕ → ℕ}
    (hn : PolynomialCostBound n) (hB : PolynomialCostBound B) :
    PolynomialCostBound (fun x => integerMatrixTraversalBudget (n x) (B x)) :=
  (hn.mul ((hn.mul (hB.add (PolynomialCostBound.const 3))).add (PolynomialCostBound.const 4))).add
    (PolynomialCostBound.const 1)

theorem polyBound_integerMatrixMulBudget {n L : ℕ → ℕ}
    (hn : PolynomialCostBound n) (hL : PolynomialCostBound L) :
    PolynomialCostBound (fun x => integerMatrixMulBudget (n x) (L x)) :=
  polyBound_integerMatrixTraversalBudget hn ((hn.add (PolynomialCostBound.const 1)).add
    ((hn.mul (polyBound_integerDotStepBudget hn hL)).add (PolynomialCostBound.const 1)))

theorem polyBound_integerSchulzOperandBudget {n L : ℕ → ℕ}
    (hn : PolynomialCostBound n) (hL : PolynomialCostBound L) :
    PolynomialCostBound (fun x => integerSchulzOperandBudget (n x) (L x)) :=
  (PolynomialCostBound.const 8).mul ((hn.add hL).add (PolynomialCostBound.const 1))

theorem polyBound_integerSchulzNumeratorBudget {n L : ℕ → ℕ}
    (hn : PolynomialCostBound n) (hL : PolynomialCostBound L) :
    PolynomialCostBound (fun x => integerSchulzNumeratorBudget (n x) (L x)) := by
  have hM := polyBound_integerSchulzOperandBudget hn hL
  have hS := ((PolynomialCostBound.const 2).mul hM).add (PolynomialCostBound.const 1)
  exact ((((PolynomialCostBound.const 3).mul (hS.pow 2)).add
    (polyBound_integerMatrixTraversalBudget hn ((hM.add hn).add (PolynomialCostBound.const 1)))).add
      ((PolynomialCostBound.const 3).mul (polyBound_integerMatrixMulBudget hn hM))).add
        (polyBound_integerMatrixTraversalBudget hn hS)

theorem polyBound_integerSchulzStepBudget {n L : ℕ → ℕ}
    (hn : PolynomialCostBound n) (hL : PolynomialCostBound L) :
    PolynomialCostBound (fun x => integerSchulzStepBudget (n x) (L x)) := by
  have hM := polyBound_integerSchulzOperandBudget hn hL
  have hS := (((PolynomialCostBound.const 2).mul hM).add (PolynomialCostBound.const 1)).pow 2
  exact (((hL.add (polyBound_integerSchulzNumeratorBudget hn hL)).add
    ((PolynomialCostBound.const 3).mul hS)).add (polyBound_integerMatrixTraversalBudget hn hS))

theorem polyBound_integerSchulzInitialBudget {n q : ℕ → ℕ}
    (hn : PolynomialCostBound n) (hq : PolynomialCostBound q) :
    PolynomialCostBound (fun x => integerSchulzInitialBudget (n x) (q x)) :=
  (hq.add (PolynomialCostBound.const 1)).add
    (polyBound_integerMatrixTraversalBudget hn ((hq.add hn).add (PolynomialCostBound.const 2)))

theorem polyBound_integerSchulzIterationBudget {n U B p k : ℕ → ℕ}
    (hn : PolynomialCostBound n) (hU : PolynomialCostBound U) (hB : PolynomialCostBound B)
    (hp : PolynomialCostBound p) (hk : PolynomialCostBound k) :
    PolynomialCostBound (fun x => integerSchulzIterationBudget (n x) (U x) (B x) (p x) (k x)) :=
  (polyBound_integerSchulzInitialBudget hn (hp.add hn)).add (hk.mul
    (polyBound_integerSchulzStepBudget hn ((((hU.add hB).add hp).add hn).add (PolynomialCostBound.const 2))))

theorem integerSchulzIterationBudget_mono {n n' U U' B B' p p' k k' : ℕ}
    (hn : n ≤ n') (hU : U ≤ U') (hB : B ≤ B') (hp : p ≤ p') (hk : k ≤ k') :
    integerSchulzIterationBudget n U B p k ≤ integerSchulzIterationBudget n' U' B' p' k' := by
  unfold integerSchulzIterationBudget integerSchulzInitialBudget integerSchulzStepBudget
    integerSchulzNumeratorBudget integerSchulzOperandBudget integerMatrixMulBudget
    integerMatrixTraversalBudget integerDotStepBudget
  dsimp only
  gcongr

/-- Uniform polynomial bound on the charged trajectory, including initialization. -/
theorem storedSchulzIteration_polynomial_cost : ∃ C e : ℕ,
    ∀ (n p B k a U : ℕ) (X : IntegerMatrixData n), 0 < a → a.size ≤ U →
      (∀ i j, (integerMatrixOfData X i j).natAbs.size ≤ U) →
      ∀ hA : ((integerMatrixQuotient a (integerMatrixOfData X)).map (fun q : ℚ => (q : ℝ))).PosSemidef,
      (∀ i, 1 / (2 : ℝ) ^ B ≤ hA.isHermitian.eigenvalues i) →
      (∀ i, hA.isHermitian.eigenvalues i ≤ 1) → (2 * B + 5) * k ≤ p →
      (costedStoredSchulzIterate (p + n) a X k).steps ≤ C * (n + U + B + p + k + 1) ^ e := by
  obtain ⟨C, e, hCe⟩ := (polyBound_integerSchulzIterationBudget PolynomialCostBound.id PolynomialCostBound.id
    PolynomialCostBound.id PolynomialCostBound.id PolynomialCostBound.id).exists_mul_pow_bound
  refine ⟨C, e, fun n p B k a U X ha has hXs hA hlo hhi hp => ?_⟩
  exact (costedStoredSchulzIterate_steps_le p B k a U X ha has hXs hA hlo hhi hp).trans
    ((integerSchulzIterationBudget_mono (by omega) (by omega) (by omega) (by omega) (by omega)).trans
      (hCe (n + U + B + p + k)))

end GeometricGaussianLHL

end StoredSchulzCost

section EncodedIntegerSquareRoot

/-!
## A binary input/output interface for the integer square-root algorithm

The input codec supplies the dimension and rational entries. The algorithm
returns an encoded dyadic matrix and preserves the unused input suffix.
On the normalized spectral domain, this exact computation satisfies the
operator-error and output-length bounds. Runtime remains a separate claim.
-/

set_option backward.isDefEq.respectTransparency false

open scoped MatrixOrder Matrix.Norms.L2Operator

namespace GeometricGaussianLHL

def encodedIntegerSchulzSqrt (t B : ℕ) (bs : List Bool) : Option (List Bool × List Bool) := do
  let (⟨_n, D⟩, tail) ← decodeRationalMatrixDataPrefix bs
  let E := storedIntegerSqrtFromRational t B (rationalMatrixOfData D)
  return (encodeRationalMatrixData E, tail)

theorem encodedIntegerSchulzSqrt_apply {n : ℕ} (t B : ℕ)
    (D : RationalMatrixData n) (tail : List Bool) :
    encodedIntegerSchulzSqrt t B (encodeRationalMatrixData D ++ tail) =
      some (encodeRationalMatrixData (storedSchulzSqrt t B (rationalMatrixOfData D)), tail) := by
  simp [encodedIntegerSchulzSqrt, decodeRationalMatrixData_append,
    storedIntegerSqrtFromRational_eq]

theorem encodedIntegerSchulzSqrt_certificate {n : ℕ} (t B : ℕ)
    (D : RationalMatrixData n) (tail outputTail : List Bool)
    (hD : ((rationalMatrixOfData D).map (fun q : ℚ => (q : ℝ))).PosSemidef)
    (hlo : ∀ i, 1 / (2 : ℝ) ^ B ≤ hD.isHermitian.eigenvalues i)
    (hhi : ∀ i, hD.isHermitian.eigenvalues i ≤ 1) :
    ∃ E : RationalMatrixData n,
      encodedIntegerSchulzSqrt t B (encodeRationalMatrixData D ++ tail) =
        some (encodeRationalMatrixData E, tail) ∧
      decodeRationalMatrixDataPrefix (encodeRationalMatrixData E ++ outputTail) =
        some (⟨n, E⟩, outputTail) ∧
      ‖(Matrix.toEuclideanLin ((rationalMatrixOfData E).map
          (fun q : ℚ => (q : ℝ)))).toContinuousLinearMap -
        (Matrix.toEuclideanLin (CFC.sqrt ((rationalMatrixOfData D).map
          (fun q : ℚ => (q : ℝ))))).toContinuousLinearMap‖ ≤ 1 / (2 : ℝ) ^ t ∧
      (encodeRationalMatrixData E).length ≤ 2 * n + 1 + n * n * (4 * (t + 2 + n) + 9) := by
  refine ⟨storedSchulzSqrt t B (rationalMatrixOfData D),
    encodedIntegerSchulzSqrt_apply t B D tail,
    decodeRationalMatrixData_append _ outputTail, ?_, ?_⟩
  · exact storedSchulzSqrt_operator_error t B (rationalMatrixOfData D) hD hlo hhi
  · exact storedSchulzSqrt_encoded_length t B (rationalMatrixOfData D) hD hlo hhi

end GeometricGaussianLHL

end EncodedIntegerSquareRoot

section SchulzApproximationCost

/-!
## Costs of complete normalized square-root and inverse approximation

The computed schedule, stored integer iteration, final product and rounding,
and rational serialization are composed into one execution. The Boolean
selects one of two fixed algorithms; it is not an extra oracle or input model.
Input normalization and composition with shaping are separate obligations.
-/

set_option backward.isDefEq.respectTransparency false
open scoped MatrixOrder Matrix.Norms.L2Operator
namespace GeometricGaussianLHL

theorem costedStoredSchulzIterate_data {n : ℕ} (q a k : ℕ) (X : IntegerMatrixData n) :
    (costedStoredSchulzIterate q a X k).value =
      storedIntegerSchulzIterate q a (integerMatrixOfData X) k := by
  rw [← integerMatrixData_ofData (costedStoredSchulzIterate q a X k).value,
    costedStoredSchulzIterate_value, integerMatrixData_ofData]

theorem costedRationalQuotient_data {n : ℕ} (a : ℕ) (X : IntegerMatrixData n) :
    (costedRationalQuotient a X).value =
      rationalMatrixData (integerMatrixQuotient a (integerMatrixOfData X)) := by
  have he := (costedRationalQuotient_value a X).trans
    (rationalMatrixOfData_data (integerMatrixQuotient a (integerMatrixOfData X))).symm
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  exact congrFun (congrFun he ⟨i, hi⟩) ⟨j, hj⟩

def costedSchulzProduct {n : ℕ} (inverse : Bool) (q r a : ℕ)
    (X N : IntegerMatrixData n) : Costed (IntegerMatrixData n) :=
  (Costed.charge (q + 1) (2 ^ q : ℤ)).bind fun d =>
    costedIntegerProductRound r (if inverse then d else (a : ℤ)) d (if inverse then N else X) N

theorem costedSchulzProduct_data {n : ℕ} (inverse : Bool) (q r a : ℕ)
    (X N : IntegerMatrixData n) :
    (costedSchulzProduct inverse q r a X N).value =
      integerMatrixData (((if inverse then integerMatrixOfData N else integerMatrixOfData X) *
        integerMatrixOfData N).map (fun z => z * (2 : ℤ) ^ r /
          ((if inverse then (2 : ℤ) ^ q else (a : ℤ)) * 2 ^ q))) := by
  rw [costedSchulzProduct, Costed.bind_value]
  dsimp only [Costed.charge]
  rw [costedIntegerProductRound_data]
  cases inverse <;> rfl

def costedDyadicQuotient {n : ℕ} (r : ℕ) (Z : IntegerMatrixData n) : Costed (RationalMatrixData n) :=
  (Costed.charge (r + 1) (2 ^ r : ℕ)).bind (fun d => costedRationalQuotient d Z)

theorem costedDyadicQuotient_data {n : ℕ} (r : ℕ) (Z : IntegerMatrixData n) :
    (costedDyadicQuotient r Z).value = rationalMatrixData (integerMatrixQuotient (2 ^ r) (integerMatrixOfData Z)) := by
  rw [costedDyadicQuotient, Costed.bind_value]
  exact costedRationalQuotient_data _ Z

def costedSchulzOutput {n : ℕ} (inverse : Bool) (q r a : ℕ)
    (X N : IntegerMatrixData n) : Costed (RationalMatrixData n) :=
  (costedSchulzProduct inverse q r a X N).bind (costedDyadicQuotient r)

theorem costedSchulzOutput_data {n : ℕ} (inverse : Bool) (q r a : ℕ)
    (X N : IntegerMatrixData n) :
    (costedSchulzOutput inverse q r a X N).value =
      rationalMatrixData (integerMatrixQuotient (2 ^ r)
        (((if inverse then integerMatrixOfData N else integerMatrixOfData X) *
          integerMatrixOfData N).map (fun z => z * (2 : ℤ) ^ r /
            ((if inverse then (2 : ℤ) ^ q else (a : ℤ)) * 2 ^ q)))) := by
  rw [costedSchulzOutput, Costed.bind_value, costedSchulzProduct_data,
    costedDyadicQuotient_data, integerMatrixOfData_data]

def costedSchulzApproximation {n : ℕ} (inverse : Bool) (s B a : ℕ)
    (X : IntegerMatrixData n) : Costed (RationalMatrixData n) :=
  (costedSchulzSchedule n s B).bind fun P =>
    (costedStoredSchulzIterate P.storedBits a X P.iterations).bind
      (costedSchulzOutput inverse P.storedBits P.outputBits a X)

theorem costedSchulzApproximation_value {n : ℕ} (inverse : Bool) (s B a : ℕ)
    (X : IntegerMatrixData n) :
    (costedSchulzApproximation inverse s B a X).value =
      let P := schulzSchedule n s B
      let N := storedIntegerSchulzIterate P.storedBits a (integerMatrixOfData X) P.iterations
      rationalMatrixData (integerMatrixQuotient (2 ^ P.outputBits)
        (((if inverse then integerMatrixOfData N else integerMatrixOfData X) *
          integerMatrixOfData N).map (fun z => z * (2 : ℤ) ^ P.outputBits /
            ((if inverse then (2 : ℤ) ^ P.storedBits else (a : ℤ)) * 2 ^ P.storedBits)))) := by
  rw [costedSchulzApproximation, Costed.bind_value, costedSchulzSchedule_value,
    Costed.bind_value, costedStoredSchulzIterate_data, costedSchulzOutput_data]

def costedIntegerSchulzSqrt {n : ℕ} (t B a : ℕ) (X : IntegerMatrixData n) : Costed (RationalMatrixData n) :=
  (costedNatAdd t 2).bind (fun s => costedSchulzApproximation false s B a X)

def costedIntegerSchulzInverse {n : ℕ} (t B a : ℕ) (X : IntegerMatrixData n) : Costed (RationalMatrixData n) :=
  (costedNatAdd t B).bind fun u => (costedNatAdd u 4).bind
    (fun s => costedSchulzApproximation true s B a X)

theorem costedIntegerSchulzSqrt_value {n : ℕ} (t B a : ℕ) (X : IntegerMatrixData n) :
    (costedIntegerSchulzSqrt t B a X).value = integerSchulzSqrtRational t B a (integerMatrixOfData X) := by
  rw [costedIntegerSchulzSqrt, Costed.bind_value]
  dsimp only [costedNatAdd]
  rw [costedSchulzApproximation_value]
  simp only [schulzSchedule, Bool.false_eq_true, ite_false, integerSchulzSqrtRational,
    storedIntegerSchulzSqrt, integerMatrixOfData_data, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]

theorem costedIntegerSchulzInverse_value {n : ℕ} (t B a : ℕ) (X : IntegerMatrixData n) :
    (costedIntegerSchulzInverse t B a X).value = integerSchulzInverseRational t B a (integerMatrixOfData X) := by
  rw [costedIntegerSchulzInverse, Costed.bind_value]
  dsimp only [costedNatAdd]
  rw [Costed.bind_value]
  dsimp only [costedNatAdd]
  rw [costedSchulzApproximation_value]
  simp only [schulzSchedule, ite_eq_left, integerSchulzInverseRational, storedIntegerSchulzInverse,
    integerMatrixOfData_data, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]

end GeometricGaussianLHL

end SchulzApproximationCost

section SchulzApproximationBounds

/-!
## Polynomial costs of normalized numerical approximation

All operand-size bounds come from the supplied integer input and the proved
spectral invariant of the computed iteration. No execution-cost bound is an
input hypothesis. The conditioning exponent remains explicit until the outer
rational normalization is composed with these algorithms.
-/

set_option backward.isDefEq.respectTransparency false
open scoped MatrixOrder Matrix.Norms.L2Operator
namespace GeometricGaussianLHL

theorem costedSchulzProduct_steps_le {n : ℕ} (inverse : Bool) (q r a L : ℕ)
    (X N : IntegerMatrixData n) (hq : q + 1 ≤ L) (hr : r + 1 ≤ L) (ha : a.size ≤ L)
    (hX : ∀ i j, (integerMatrixOfData X i j).natAbs.size ≤ L)
    (hN : ∀ i j, (integerMatrixOfData N i j).natAbs.size ≤ L) :
    (costedSchulzProduct inverse q r a X N).steps ≤ L + integerProductRoundBudget n L := by
  have hd : ((2 : ℤ) ^ q).natAbs.size ≤ L := by simpa [Int.natAbs_pow, Nat.size_pow] using hq
  change q + 1 + (costedIntegerProductRound r _ _ _ N).steps ≤ _
  apply Nat.add_le_add hq
  apply costedIntegerProductRound_steps_le _ _ _ _ _ L hr
  · cases inverse with
    | false => exact ha
    | true => exact hd
  · exact hd
  · cases inverse <;> assumption
  · exact hN

theorem costedSchulzProduct_size {n : ℕ} (inverse : Bool) (q r a L : ℕ)
    (X N : IntegerMatrixData n)
    (hX : ∀ i j, (integerMatrixOfData X i j).natAbs.size ≤ L)
    (hN : ∀ i j, (integerMatrixOfData N i j).natAbs.size ≤ L) (i j : Fin n) :
    (integerMatrixOfData (costedSchulzProduct inverse q r a X N).value i j).natAbs.size ≤ n + 2 * L + r + 1 := by
  rw [costedSchulzProduct, Costed.bind_value]
  dsimp only [Costed.charge]
  cases inverse with
  | false => exact costedIntegerProductRound_size r (a : ℤ) (2 ^ q) X N L hX hN i j
  | true => exact costedIntegerProductRound_size r (2 ^ q) (2 ^ q) N N L hN hN i j

def schulzOutputBudget (n L : ℕ) : ℕ :=
  L + integerProductRoundBudget n L + L + rationalQuotientCostBudget n (n + 3 * L + 1)

theorem costedSchulzOutput_steps_le {n : ℕ} (inverse : Bool) (q r a L : ℕ)
    (X N : IntegerMatrixData n) (hq : q + 1 ≤ L) (hr : r + 1 ≤ L) (ha : a.size ≤ L)
    (hX : ∀ i j, (integerMatrixOfData X i j).natAbs.size ≤ L)
    (hN : ∀ i j, (integerMatrixOfData N i j).natAbs.size ≤ L) :
    (costedSchulzOutput inverse q r a X N).steps ≤ schulzOutputBudget n L := by
  let Z := costedSchulzProduct inverse q r a X N
  have hZ : ∀ i j, (integerMatrixOfData Z.value i j).natAbs.size ≤ n + 3 * L + 1 :=
    fun i j => (costedSchulzProduct_size inverse q r a L X N hX hN i j).trans (by omega)
  have hden : (2 ^ r : ℕ).size ≤ n + 3 * L + 1 := by simpa [Nat.size_pow] using (show r + 1 ≤ n + 3 * L + 1 by omega)
  have hconv := costedRationalQuotient_steps_le (2 ^ r) Z.value (n + 3 * L + 1) (by positivity) hden hZ
  have hprod := costedSchulzProduct_steps_le inverse q r a L X N hq hr ha hX hN
  change Z.steps ≤ _ at hprod
  change Z.steps + (r + 1 + (costedRationalQuotient (2 ^ r) Z.value).steps) ≤ _
  unfold schulzOutputBudget
  omega

def schulzApproximationBudget (n U s B : ℕ) : ℕ :=
  let p := s + (2 * B + 5) * (s + B)
  schulzScheduleBudget n s B + integerSchulzIterationBudget n U B p (s + B) +
    schulzOutputBudget n (U + B + p + n + 2)

theorem costedSchulzApproximation_steps_le {n : ℕ} (inverse : Bool) (s B a U : ℕ)
    (X : IntegerMatrixData n) (ha : 0 < a) (has : a.size ≤ U)
    (hXs : ∀ i j, (integerMatrixOfData X i j).natAbs.size ≤ U)
    (hA : ((integerMatrixQuotient a (integerMatrixOfData X)).map (fun q : ℚ => (q : ℝ))).PosSemidef)
    (hlo : ∀ i, 1 / (2 : ℝ) ^ B ≤ hA.isHermitian.eigenvalues i)
    (hhi : ∀ i, hA.isHermitian.eigenvalues i ≤ 1) :
    (costedSchulzApproximation inverse s B a X).steps ≤ schulzApproximationBudget n U s B := by
  let p := s + (2 * B + 5) * (s + B)
  let N := costedStoredSchulzIterate (p + n) a X (s + B)
  let L := U + B + p + n + 2
  have hp : (2 * B + 5) * (s + B) ≤ p := by dsimp [p]; omega
  have hs : s ≤ p := by dsimp [p]; omega
  have hNs : ∀ i j, (integerMatrixOfData N.value i j).natAbs.size ≤ L := by
    intro i j
    rw [costedStoredSchulzIterate_value]
    exact (storedIntegerSchulz_state_size p B (s + B) _ a (integerMatrixOfData X) ha rfl
      hA hlo hhi hp i j).trans (by dsimp [L]; omega)
  have hNi := costedStoredSchulzIterate_steps_le p B (s + B) a U X ha has hXs hA hlo hhi hp
  change N.steps ≤ _ at hNi
  have hOut := costedSchulzOutput_steps_le inverse (p + n) (s + n) a L X N.value
    (by dsimp [L]; omega) (by dsimp [L]; omega) (has.trans (by dsimp [L]; omega))
    (fun i j => (hXs i j).trans (by dsimp [L]; omega)) hNs
  have hP := costedSchulzSchedule_steps_le n s B
  rw [costedSchulzApproximation, Costed.bind_steps, costedSchulzSchedule_value]
  change (costedSchulzSchedule n s B).steps +
    (N.steps + (costedSchulzOutput inverse (p + n) (s + n) a X N.value).steps) ≤ _
  change _ ≤ schulzScheduleBudget n s B + integerSchulzIterationBudget n U B p (s + B) + schulzOutputBudget n L
  omega

theorem polyBound_integerScaleDivideBudget {n L : ℕ → ℕ}
    (hn : PolynomialCostBound n) (hL : PolynomialCostBound L) :
    PolynomialCostBound (fun x => integerScaleDivideBudget (n x) (L x)) :=
  polyBound_integerMatrixTraversalBudget hn
    (((((PolynomialCostBound.const 2).mul hL).add (PolynomialCostBound.const 1)).pow 2).add
      ((((PolynomialCostBound.const 3).mul hL).add (PolynomialCostBound.const 2)).pow 2))

theorem polyBound_integerProductRoundBudget {n L : ℕ → ℕ}
    (hn : PolynomialCostBound n) (hL : PolynomialCostBound L) :
    PolynomialCostBound (fun x => integerProductRoundBudget (n x) (L x)) :=
  ((hL.add ((((PolynomialCostBound.const 2).mul hL).add (PolynomialCostBound.const 1)).pow 2)).add
    (polyBound_integerMatrixMulBudget hn hL)).add
      (polyBound_integerScaleDivideBudget hn ((hn.add ((PolynomialCostBound.const 2).mul hL)).add (PolynomialCostBound.const 1)))

theorem polyBound_rationalQuotientOutputBudget {n L : ℕ → ℕ}
    (hn : PolynomialCostBound n) (hL : PolynomialCostBound L) :
    PolynomialCostBound (fun x => rationalQuotientOutputBudget (n x) (L x)) :=
  (((PolynomialCostBound.const 2).mul hn).add (PolynomialCostBound.const 1)).add
    ((hn.mul hn).mul (((PolynomialCostBound.const 4).mul hL).add (PolynomialCostBound.const 3)))

theorem polyBound_rationalQuotientCostBudget {n L : ℕ → ℕ}
    (hn : PolynomialCostBound n) (hL : PolynomialCostBound L) :
    PolynomialCostBound (fun x => rationalQuotientCostBudget (n x) (L x)) :=
  ((hL.add (PolynomialCostBound.const 1)).add
    (polyBound_integerMatrixTraversalBudget hn ((hL.add (PolynomialCostBound.const 1)).add
      ((((PolynomialCostBound.const 2).mul hL).add (PolynomialCostBound.const 5)).pow 3)))).add
    (polyBound_rationalQuotientOutputBudget hn hL)

theorem polyBound_schulzOutputBudget {n L : ℕ → ℕ}
    (hn : PolynomialCostBound n) (hL : PolynomialCostBound L) :
    PolynomialCostBound (fun x => schulzOutputBudget (n x) (L x)) :=
  (((hL.add (polyBound_integerProductRoundBudget hn hL)).add hL).add
    (polyBound_rationalQuotientCostBudget hn ((hn.add ((PolynomialCostBound.const 3).mul hL)).add (PolynomialCostBound.const 1))))

theorem polyBound_schulzApproximationBudget {n U s B : ℕ → ℕ}
    (hn : PolynomialCostBound n) (hU : PolynomialCostBound U)
    (hs : PolynomialCostBound s) (hB : PolynomialCostBound B) :
    PolynomialCostBound (fun x => schulzApproximationBudget (n x) (U x) (s x) (B x)) := by
  have hp := hs.add ((((PolynomialCostBound.const 2).mul hB).add (PolynomialCostBound.const 5)).mul (hs.add hB))
  exact ((polyBound_schulzScheduleBudget hn hs hB).add
    (polyBound_integerSchulzIterationBudget hn hU hB hp (hs.add hB))).add
      (polyBound_schulzOutputBudget hn ((((hU.add hB).add hp).add hn).add (PolynomialCostBound.const 2)))

theorem schulzApproximationBudget_mono {n n' U U' s s' B B' : ℕ}
    (hn : n ≤ n') (hU : U ≤ U') (hs : s ≤ s') (hB : B ≤ B') :
    schulzApproximationBudget n U s B ≤ schulzApproximationBudget n' U' s' B' := by
  unfold schulzApproximationBudget schulzScheduleBudget schulzScheduleMagnitude schulzOutputBudget
    integerSchulzIterationBudget integerSchulzInitialBudget integerSchulzStepBudget
    integerSchulzNumeratorBudget integerSchulzOperandBudget integerProductRoundBudget integerScaleDivideBudget
    rationalQuotientCostBudget rationalQuotientOutputBudget integerMatrixMulBudget
    integerMatrixTraversalBudget integerDotStepBudget
  dsimp only
  gcongr

end GeometricGaussianLHL

end SchulzApproximationBounds

section SchulzApproximationCertificate

/-!
## Normalized numerical approximation certificates

Both executions include precision setup and rational-output serialization.
Their outputs agree exactly with the previously proved square-root and inverse
approximations. Costs are uniformly polynomial in dimension, input integer bit
bound, conditioning exponent, and requested output precision.
-/

set_option backward.isDefEq.respectTransparency false
open scoped MatrixOrder Matrix.Norms.L2Operator
namespace GeometricGaussianLHL

def integerSchulzApproximationBudget (n U t B : ℕ) : ℕ :=
  2 * (2 * (t + B + 4) + 1) ^ 2 + schulzApproximationBudget n U (t + B + 4) B

theorem costedIntegerSchulz_steps_le {n : ℕ} (inverse : Bool) (t B a U : ℕ)
    (X : IntegerMatrixData n) (ha : 0 < a) (has : a.size ≤ U)
    (hXs : ∀ i j, (integerMatrixOfData X i j).natAbs.size ≤ U)
    (hA : ((integerMatrixQuotient a (integerMatrixOfData X)).map (fun q : ℚ => (q : ℝ))).PosSemidef)
    (hlo : ∀ i, 1 / (2 : ℝ) ^ B ≤ hA.isHermitian.eigenvalues i)
    (hhi : ∀ i, hA.isHermitian.eigenvalues i ≤ 1) :
    (if inverse then costedIntegerSchulzInverse t B a X else costedIntegerSchulzSqrt t B a X).steps ≤
      integerSchulzApproximationBudget n U t B := by
  cases inverse with
  | false =>
    have hsetup := costedNatAdd_steps_le t 2 (t + B + 4) (by omega) (by omega)
    have hrun := (costedSchulzApproximation_steps_le false (t + 2) B a U X ha has hXs hA hlo hhi).trans
      (schulzApproximationBudget_mono le_rfl le_rfl (show t + 2 ≤ t + B + 4 by omega) le_rfl)
    change (costedNatAdd t 2).steps + (costedSchulzApproximation false (t + 2) B a X).steps ≤ _
    unfold integerSchulzApproximationBudget
    omega
  | true =>
    have hsetup₁ := costedNatAdd_steps_le t B (t + B + 4) (by omega) (by omega)
    have hsetup₂ := costedNatAdd_steps_le (t + B) 4 (t + B + 4) (by omega) (by omega)
    have hrun := costedSchulzApproximation_steps_le true (t + B + 4) B a U X ha has hXs hA hlo hhi
    change (costedNatAdd t B).steps + ((costedNatAdd (t + B) 4).steps +
      (costedSchulzApproximation true (t + B + 4) B a X).steps) ≤ _
    unfold integerSchulzApproximationBudget
    omega

theorem polyBound_integerSchulzApproximationBudget {n U t B : ℕ → ℕ}
    (hn : PolynomialCostBound n) (hU : PolynomialCostBound U)
    (ht : PolynomialCostBound t) (hB : PolynomialCostBound B) :
    PolynomialCostBound (fun x => integerSchulzApproximationBudget (n x) (U x) (t x) (B x)) := by
  have hs := (ht.add hB).add (PolynomialCostBound.const 4)
  exact ((PolynomialCostBound.const 2).mul
    ((((PolynomialCostBound.const 2).mul hs).add (PolynomialCostBound.const 1)).pow 2)).add
      (polyBound_schulzApproximationBudget hn hU hs hB)

theorem integerSchulzApproximationBudget_mono {n n' U U' t t' B B' : ℕ}
    (hn : n ≤ n') (hU : U ≤ U') (ht : t ≤ t') (hB : B ≤ B') :
    integerSchulzApproximationBudget n U t B ≤ integerSchulzApproximationBudget n' U' t' B' := by
  apply Nat.add_le_add
  · gcongr
  · exact schulzApproximationBudget_mono hn hU (by omega) hB

/-- Both fixed algorithms have uniform polynomial cost, including output conversion. -/
theorem normalizedSchulz_polynomial_cost : ∃ C e : ℕ,
    ∀ (inverse : Bool) (n t B a U : ℕ) (X : IntegerMatrixData n), 0 < a → a.size ≤ U →
      (∀ i j, (integerMatrixOfData X i j).natAbs.size ≤ U) →
      ∀ hA : ((integerMatrixQuotient a (integerMatrixOfData X)).map (fun q : ℚ => (q : ℝ))).PosSemidef,
      (∀ i, 1 / (2 : ℝ) ^ B ≤ hA.isHermitian.eigenvalues i) →
      (∀ i, hA.isHermitian.eigenvalues i ≤ 1) →
      (if inverse then costedIntegerSchulzInverse t B a X else costedIntegerSchulzSqrt t B a X).steps ≤
        C * (n + U + t + B + 1) ^ e := by
  obtain ⟨C, e, hCe⟩ := (polyBound_integerSchulzApproximationBudget PolynomialCostBound.id
    PolynomialCostBound.id PolynomialCostBound.id PolynomialCostBound.id).exists_mul_pow_bound
  refine ⟨C, e, fun inverse n t B a U X ha has hXs hA hlo hhi => ?_⟩
  exact (costedIntegerSchulz_steps_le inverse t B a U X ha has hXs hA hlo hhi).trans
    ((integerSchulzApproximationBudget_mono (by omega) (by omega) (by omega) (by omega)).trans
      (hCe (n + U + t + B)))

theorem costedIntegerSchulzSqrt_operator_error {n : ℕ} (t B a : ℕ) (ha : 0 < a)
    (X : IntegerMatrixData n)
    (hA : ((integerMatrixQuotient a (integerMatrixOfData X)).map (fun q : ℚ => (q : ℝ))).PosSemidef)
    (hlo : ∀ i, 1 / (2 : ℝ) ^ B ≤ hA.isHermitian.eigenvalues i)
    (hhi : ∀ i, hA.isHermitian.eigenvalues i ≤ 1) :
    ‖(Matrix.toEuclideanLin ((rationalMatrixOfData (costedIntegerSchulzSqrt t B a X).value).map
        (fun q : ℚ => (q : ℝ)))).toContinuousLinearMap -
      (Matrix.toEuclideanLin (CFC.sqrt ((integerMatrixQuotient a (integerMatrixOfData X)).map
        (fun q : ℚ => (q : ℝ))))).toContinuousLinearMap‖ ≤ 1 / (2 : ℝ) ^ t := by
  rw [costedIntegerSchulzSqrt_value]
  exact integerSchulzSqrtRational_operator_error t B a ha (integerMatrixOfData X) hA hlo hhi

theorem costedIntegerSchulzInverse_operator_error {n : ℕ} (t B a : ℕ) (ha : 0 < a)
    (X : IntegerMatrixData n)
    (hA : ((integerMatrixQuotient a (integerMatrixOfData X)).map (fun q : ℚ => (q : ℝ))).PosSemidef)
    (hlo : ∀ i, 1 / (2 : ℝ) ^ B ≤ hA.isHermitian.eigenvalues i)
    (hhi : ∀ i, hA.isHermitian.eigenvalues i ≤ 1) :
    ‖(Matrix.toEuclideanLin ((rationalMatrixOfData (costedIntegerSchulzInverse t B a X).value).map
        (fun q : ℚ => (q : ℝ)))).toContinuousLinearMap -
      (Matrix.toEuclideanLin (((integerMatrixQuotient a (integerMatrixOfData X)).map
        (fun q : ℚ => (q : ℝ)))⁻¹)).toContinuousLinearMap‖ ≤ 1 / (2 : ℝ) ^ t := by
  rw [costedIntegerSchulzInverse_value]
  exact integerSchulzInverseRational_operator_error t B a ha (integerMatrixOfData X) hA hlo hhi

theorem costedRationalQuotient_length_le_steps {n : ℕ} (a : ℕ) (X : IntegerMatrixData n) :
    (encodeRationalMatrixData (costedRationalQuotient a X).value).length ≤ (costedRationalQuotient a X).steps := by
  let D := costedRationalMatrixOfFn (fun i j => costedIntegerToRational a (integerMatrixOfData X i j))
  change (encodeRationalMatrixData D.value).length ≤ a.size + 1 + (D.steps + (encodeRationalMatrixData D.value).length)
  omega

theorem costedDyadicQuotient_length_le_steps {n : ℕ} (r : ℕ) (X : IntegerMatrixData n) :
    (encodeRationalMatrixData (costedDyadicQuotient r X).value).length ≤ (costedDyadicQuotient r X).steps :=
  (costedRationalQuotient_length_le_steps (2 ^ r) X).trans (Nat.le_add_left _ _)

theorem costedSchulzOutput_length_le_steps {n : ℕ} (inverse : Bool) (q r a : ℕ) (X N : IntegerMatrixData n) :
    (encodeRationalMatrixData (costedSchulzOutput inverse q r a X N).value).length ≤
      (costedSchulzOutput inverse q r a X N).steps :=
  (costedDyadicQuotient_length_le_steps r (costedSchulzProduct inverse q r a X N).value).trans (Nat.le_add_left _ _)

theorem costedSchulzApproximation_length_le_steps {n : ℕ} (inverse : Bool) (s B a : ℕ) (X : IntegerMatrixData n) :
    (encodeRationalMatrixData (costedSchulzApproximation inverse s B a X).value).length ≤
      (costedSchulzApproximation inverse s B a X).steps := by
  let P := (costedSchulzSchedule n s B).value
  exact (costedSchulzOutput_length_le_steps inverse P.storedBits P.outputBits a X
    (costedStoredSchulzIterate P.storedBits a X P.iterations).value).trans
      ((Nat.le_add_left _ _).trans (Nat.le_add_left _ _))

theorem costedIntegerSchulz_length_le_steps {n : ℕ} (inverse : Bool) (t B a : ℕ) (X : IntegerMatrixData n) :
    let run := if inverse then costedIntegerSchulzInverse t B a X else costedIntegerSchulzSqrt t B a X
    (encodeRationalMatrixData run.value).length ≤ run.steps := by
  cases inverse with
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    rw [costedIntegerSchulzSqrt, Costed.bind_value, Costed.bind_steps]
    dsimp only [costedNatAdd]
    exact (costedSchulzApproximation_length_le_steps false (t + 2) B a X).trans (Nat.le_add_left _ _)
  | true =>
    simp only [ite_true]
    rw [costedIntegerSchulzInverse, Costed.bind_value, Costed.bind_steps]
    dsimp only [costedNatAdd]
    rw [Costed.bind_value, Costed.bind_steps]
    dsimp only [costedNatAdd]
    exact (costedSchulzApproximation_length_le_steps true (t + B + 4) B a X).trans
      ((Nat.le_add_left _ _).trans (Nat.le_add_left _ _))

/-- Cost, output length, decoding, and numerical accuracy describe the same execution. -/
theorem normalizedSchulz_approximation_certificate : ∃ C e : ℕ,
    ∀ (inverse : Bool) (n t B a U : ℕ) (X : IntegerMatrixData n), 0 < a → a.size ≤ U →
      (∀ i j, (integerMatrixOfData X i j).natAbs.size ≤ U) →
      ∀ hA : ((integerMatrixQuotient a (integerMatrixOfData X)).map (fun q : ℚ => (q : ℝ))).PosSemidef,
      (∀ i, 1 / (2 : ℝ) ^ B ≤ hA.isHermitian.eigenvalues i) →
      (∀ i, hA.isHermitian.eigenvalues i ≤ 1) →
      let A := (integerMatrixQuotient a (integerMatrixOfData X)).map (fun q : ℚ => (q : ℝ))
      let run := if inverse then costedIntegerSchulzInverse t B a X else costedIntegerSchulzSqrt t B a X
      run.steps ≤ C * (n + U + t + B + 1) ^ e ∧
      (encodeRationalMatrixData run.value).length ≤ C * (n + U + t + B + 1) ^ e ∧
      decodeRationalMatrixDataPrefix (encodeRationalMatrixData run.value) = some (⟨n, run.value⟩, []) ∧
      ‖(Matrix.toEuclideanLin ((rationalMatrixOfData run.value).map (fun q : ℚ => (q : ℝ)))).toContinuousLinearMap -
        (Matrix.toEuclideanLin (if inverse then A⁻¹ else CFC.sqrt A)).toContinuousLinearMap‖ ≤ 1 / (2 : ℝ) ^ t := by
  obtain ⟨C, e, hCe⟩ := normalizedSchulz_polynomial_cost
  refine ⟨C, e, fun inverse n t B a U X ha has hXs hA hlo hhi => ?_⟩
  have hc := hCe inverse n t B a U X ha has hXs hA hlo hhi
  refine ⟨hc, (costedIntegerSchulz_length_le_steps inverse t B a X).trans hc, ?_, ?_⟩
  · simpa only [List.append_nil] using decodeRationalMatrixData_append
      (if inverse then costedIntegerSchulzInverse t B a X else costedIntegerSchulzSqrt t B a X).value []
  · cases inverse with
    | false => exact costedIntegerSchulzSqrt_operator_error t B a ha X hA hlo hhi
    | true => exact costedIntegerSchulzInverse_operator_error t B a ha X hA hlo hhi

end GeometricGaussianLHL

end SchulzApproximationCertificate

section RationalSpectralCost

/-!
## Costed square-root and inverse algorithms for general rational input

Normalization, numerical approximation, symmetry restoration and rescaling
are one computation on stored data. The output equals the existing rational
specification, including the averaging needed for positive inverse outputs.
-/

set_option backward.isDefEq.respectTransparency false
open scoped MatrixOrder Matrix.Norms.L2Operator
namespace GeometricGaussianLHL

theorem costedIntegerSchulzSqrt_spec_data {n : ℕ} (t B a : ℕ) (ha : 0 < a) (X : IntegerMatrixData n) :
    (costedIntegerSchulzSqrt t B a X).value =
      rationalMatrixData (roundedSchulzSqrt t B (integerMatrixQuotient a (integerMatrixOfData X))) := by
  rw [← rationalMatrixData_ofData (costedIntegerSchulzSqrt t B a X).value,
    costedIntegerSchulzSqrt_value, integerSchulzSqrtRational_refines t B a ha]

theorem costedIntegerSchulzInverse_spec_data {n : ℕ} (t B a : ℕ) (ha : 0 < a) (X : IntegerMatrixData n) :
    (costedIntegerSchulzInverse t B a X).value =
      rationalMatrixData (roundedSchulzInverse t B (integerMatrixQuotient a (integerMatrixOfData X))) := by
  rw [← rationalMatrixData_ofData (costedIntegerSchulzInverse t B a X).value,
    costedIntegerSchulzInverse_value, integerSchulzInverseRational_refines t B a ha]

def costedRationalSpectralCore {n : ℕ} (inverse : Bool) (t : ℕ) (P : RationalNormalizedInput n) : Costed (RationalMatrixData n) :=
  if inverse then (costedNatAdd t 1).bind (fun u => costedIntegerSchulzInverse u P.conditionExponent P.denominator P.numerators)
  else (costedNatAdd t P.scaleExponent).bind (fun u => costedIntegerSchulzSqrt u P.conditionExponent P.denominator P.numerators)

theorem costedRationalSpectralCore_data {n : ℕ} (inverse : Bool) (t : ℕ) (P : RationalNormalizedInput n)
    (ha : 0 < P.denominator) :
    (costedRationalSpectralCore inverse t P).value = rationalMatrixData
      (if inverse then roundedSchulzInverse (t + 1) P.conditionExponent (integerMatrixQuotient P.denominator (integerMatrixOfData P.numerators))
      else roundedSchulzSqrt (t + P.scaleExponent) P.conditionExponent (integerMatrixQuotient P.denominator (integerMatrixOfData P.numerators))) := by
  cases inverse with
  | false =>
    rw [costedRationalSpectralCore, ite_eq_right (by decide), Costed.bind_value]
    dsimp only [costedNatAdd]
    rw [costedIntegerSchulzSqrt_spec_data _ _ _ ha, ite_eq_right (by decide)]
  | true =>
    rw [costedRationalSpectralCore, ite_eq_left rfl, Costed.bind_value]
    dsimp only [costedNatAdd]
    rw [costedIntegerSchulzInverse_spec_data _ _ _ ha, ite_eq_left rfl]

def costedRationalSpectralFinish {n : ℕ} (inverse : Bool) (s : ℕ) (D : RationalMatrixData n) : Costed (RationalMatrixData n) :=
  if inverse then (costedRationalSymmetrize D).bind fun R =>
    (costedNatMul 2 s).bind fun e => costedRationalDyadicOutput true e R
  else costedRationalDyadicOutput false s D

theorem costedRationalSpectralFinish_data {n : ℕ} (inverse : Bool) (s : ℕ) (D : RationalMatrixData n) :
    (costedRationalSpectralFinish inverse s D).value = rationalMatrixData
      (if inverse then (1 / (2 : ℚ) ^ (2 * s)) • ((1 / 2 : ℚ) •
        (rationalMatrixOfData D + (rationalMatrixOfData D).transpose))
      else (2 : ℚ) ^ s • rationalMatrixOfData D) := by
  cases inverse with
  | false => simpa only [costedRationalSpectralFinish, Bool.false_eq_true, ite_false] using costedRationalDyadicOutput_data false s D
  | true =>
    simp only [costedRationalSpectralFinish, ite_true]
    rw [Costed.bind_value, costedRationalSymmetrize_data, Costed.bind_value]
    dsimp only [costedNatMul]
    rw [costedRationalDyadicOutput_data, rationalMatrixOfData_data]
    rfl

def costedRationalSpectralApprox {n : ℕ} (inverse : Bool) (t : ℕ) (D : RationalMatrixData n) : Costed (RationalMatrixData n) :=
  (costedRationalNormalization D).bind fun P =>
    (costedRationalSpectralCore inverse t P).bind (costedRationalSpectralFinish inverse P.scaleExponent)

theorem costedRationalSpectralApprox_data {n : ℕ} (inverse : Bool) (t : ℕ) (D : RationalMatrixData n) :
    (costedRationalSpectralApprox inverse t D).value = rationalMatrixData
      (if inverse then rationalInverseApprox t (rationalMatrixOfData D) else rationalSqrtApprox t (rationalMatrixOfData D)) := by
  rw [costedRationalSpectralApprox, Costed.bind_value, costedRationalNormalization_value,
    Costed.bind_value, costedRationalSpectralCore_data inverse t _ (rationalNormalizedInput_denominator_pos D),
    costedRationalSpectralFinish_data, rationalMatrixOfData_data, rationalNormalizedInput_reconstruct]
  cases inverse <;> simp [rationalNormalizedInput, rationalInverseApprox, rationalSqrtApprox,
    symmetricSchulzInverse, materializeMatrix_eq, rationalMatrixNormalizationExponent]

theorem costedRationalSpectralApprox_operator_error {n : ℕ} (inverse : Bool) (t : ℕ) (D : RationalMatrixData n)
    (hD : ((rationalMatrixOfData D).map (fun q : ℚ => (q : ℝ))).PosDef) :
    let A := (rationalMatrixOfData D).map (fun q : ℚ => (q : ℝ))
    ‖(Matrix.toEuclideanLin ((rationalMatrixOfData (costedRationalSpectralApprox inverse t D).value).map
        (fun q : ℚ => (q : ℝ)))).toContinuousLinearMap -
      (Matrix.toEuclideanLin (if inverse then A⁻¹ else CFC.sqrt A)).toContinuousLinearMap‖ ≤ 1 / (2 : ℝ) ^ t := by
  rw [costedRationalSpectralApprox_data, rationalMatrixOfData_data]
  cases inverse with
  | false => exact rationalSqrtApprox_operator_error t (rationalMatrixOfData D) hD
  | true => exact rationalInverseApprox_operator_error t (rationalMatrixOfData D) hD

theorem costedRationalSpectralInverse_posDef {n : ℕ} (t : ℕ) (D : RationalMatrixData n)
    (hD : ((rationalMatrixOfData D).map (fun q : ℚ => (q : ℝ))).PosDef) :
    ((rationalMatrixOfData (costedRationalSpectralApprox true t D).value).map (fun q : ℚ => (q : ℝ))).PosDef := by
  rw [costedRationalSpectralApprox_data, rationalMatrixOfData_data]
  exact rationalInverseApprox_posDef t (rationalMatrixOfData D) hD

theorem costedRationalSpectralCore_length_le_steps {n : ℕ} (inverse : Bool) (t : ℕ) (P : RationalNormalizedInput n) :
    (encodeRationalMatrixData (costedRationalSpectralCore inverse t P).value).length ≤ (costedRationalSpectralCore inverse t P).steps := by
  cases inverse with
  | false =>
    rw [costedRationalSpectralCore, ite_eq_right (by decide), Costed.bind_value, Costed.bind_steps]
    dsimp only [costedNatAdd]
    have h := costedIntegerSchulz_length_le_steps false (t + P.scaleExponent) P.conditionExponent P.denominator P.numerators
    dsimp only at h
    rw [ite_eq_right (by decide)] at h
    exact h.trans (Nat.le_add_left _ _)
  | true =>
    rw [costedRationalSpectralCore, ite_eq_left rfl, Costed.bind_value, Costed.bind_steps]
    dsimp only [costedNatAdd]
    have h := costedIntegerSchulz_length_le_steps true (t + 1) P.conditionExponent P.denominator P.numerators
    dsimp only at h
    rw [ite_eq_left rfl] at h
    exact h.trans (Nat.le_add_left _ _)

theorem costedRationalSpectralFinish_length_le_steps {n : ℕ} (inverse : Bool) (s : ℕ) (D : RationalMatrixData n) :
    (encodeRationalMatrixData (costedRationalSpectralFinish inverse s D).value).length ≤ (costedRationalSpectralFinish inverse s D).steps := by
  cases inverse with
  | false => simpa only [costedRationalSpectralFinish, Bool.false_eq_true, ite_false] using costedRationalDyadicOutput_length_le_steps false s D
  | true =>
    simp only [costedRationalSpectralFinish, ite_true, Costed.bind_value, Costed.bind_steps]
    exact (costedRationalDyadicOutput_length_le_steps true (2 * s) (costedRationalSymmetrize D).value).trans
      ((Nat.le_add_left _ _).trans (Nat.le_add_left _ _))

theorem costedRationalSpectralApprox_length_le_steps {n : ℕ} (inverse : Bool) (t : ℕ) (D : RationalMatrixData n) :
    (encodeRationalMatrixData (costedRationalSpectralApprox inverse t D).value).length ≤ (costedRationalSpectralApprox inverse t D).steps := by
  rw [costedRationalSpectralApprox, Costed.bind_value, Costed.bind_steps, Costed.bind_value, Costed.bind_steps]
  exact (costedRationalSpectralFinish_length_le_steps inverse (costedRationalNormalization D).value.scaleExponent
    (costedRationalSpectralCore inverse t (costedRationalNormalization D).value).value).trans
      ((Nat.le_add_left _ _).trans (Nat.le_add_left _ _))

end GeometricGaussianLHL

end RationalSpectralCost

section RationalSpectralCostBounds

/-!
## Total costs from finite rational input

The normalized spectral hypotheses are derived from positive definiteness and
the actual input encoding. The bounds include preparation, numerical execution,
symmetry restoration and final output serialization.
-/

set_option backward.isDefEq.respectTransparency false
open scoped MatrixOrder Matrix.Norms.L2Operator
namespace GeometricGaussianLHL

def rationalSpectralCoreBudget (n U t B s : ℕ) : ℕ :=
  (2 * (t + s + 2) + 1) ^ 2 + integerSchulzApproximationBudget n U (t + s + 1) B

theorem costedRationalSpectralCore_steps_le {n : ℕ} (inverse : Bool) (t U : ℕ) (P : RationalNormalizedInput n)
    (ha : 0 < P.denominator) (has : P.denominator.size ≤ U)
    (hXs : ∀ i j, (integerMatrixOfData P.numerators i j).natAbs.size ≤ U)
    (hA : ((integerMatrixQuotient P.denominator (integerMatrixOfData P.numerators)).map (fun q : ℚ => (q : ℝ))).PosSemidef)
    (hlo : ∀ i, 1 / (2 : ℝ) ^ P.conditionExponent ≤ hA.isHermitian.eigenvalues i)
    (hhi : ∀ i, hA.isHermitian.eigenvalues i ≤ 1) :
    (costedRationalSpectralCore inverse t P).steps ≤ rationalSpectralCoreBudget n U t P.conditionExponent P.scaleExponent := by
  cases inverse with
  | false =>
    have hsetup := costedNatAdd_steps_le t P.scaleExponent (t + P.scaleExponent + 2) (by omega) (by omega)
    have hrun := costedIntegerSchulz_steps_le false (t + P.scaleExponent) P.conditionExponent P.denominator U P.numerators ha has hXs hA hlo hhi
    simp only [Bool.false_eq_true, ite_false] at hrun
    have hb := integerSchulzApproximationBudget_mono (n := n) (U := U) (B := P.conditionExponent) le_rfl le_rfl
      (show t + P.scaleExponent ≤ t + P.scaleExponent + 1 by omega) le_rfl
    simp only [costedRationalSpectralCore, Bool.false_eq_true, ite_false, Costed.bind_steps]
    dsimp only [costedNatAdd]
    dsimp only [costedNatAdd] at hsetup
    unfold rationalSpectralCoreBudget
    omega
  | true =>
    have hsetup := costedNatAdd_steps_le t 1 (t + P.scaleExponent + 2) (by omega) (by omega)
    have hrun := costedIntegerSchulz_steps_le true (t + 1) P.conditionExponent P.denominator U P.numerators ha has hXs hA hlo hhi
    simp only [ite_true] at hrun
    have hb := integerSchulzApproximationBudget_mono (n := n) (U := U) (B := P.conditionExponent) le_rfl le_rfl
      (show t + 1 ≤ t + P.scaleExponent + 1 by omega) le_rfl
    simp only [costedRationalSpectralCore, ite_true, Costed.bind_steps]
    dsimp only [costedNatAdd]
    dsimp only [costedNatAdd] at hsetup
    unfold rationalSpectralCoreBudget
    omega

theorem rationalDyadicOutputBudget_mono {n n' e e' L L' : ℕ}
    (hn : n ≤ n') (he : e ≤ e') (hL : L ≤ L') :
    rationalDyadicOutputBudget n e L ≤ rationalDyadicOutputBudget n' e' L' := by
  unfold rationalDyadicOutputBudget rationalDyadicScalarBudget integerMatrixTraversalBudget rationalMatrixEncodingBudget
  dsimp only
  gcongr

def rationalSpectralFinishBudget (n s L : ℕ) : ℕ :=
  rationalSymmetrizeBudget n L + (2 * (s + 2) + 1) ^ 2 + rationalDyadicOutputBudget n (2 * s) (15 * L + 17)

theorem costedRationalSpectralFinish_steps_le {n : ℕ} (inverse : Bool) (s L : ℕ) (D : RationalMatrixData n)
    (hD : ∀ i j, rationalMagnitudeBits (rationalMatrixOfData D i j) ≤ L) :
    (costedRationalSpectralFinish inverse s D).steps ≤ rationalSpectralFinishBudget n s L := by
  cases inverse with
  | false =>
    have h := (costedRationalDyadicOutput_steps_le false s L D hD).trans
      (rationalDyadicOutputBudget_mono le_rfl (show s ≤ 2 * s by omega) (show L ≤ 15 * L + 17 by omega))
    simp only [costedRationalSpectralFinish, Bool.false_eq_true, ite_false]
    unfold rationalSpectralFinishBudget
    omega
  | true =>
    have hsym := costedRationalSymmetrize_steps_le D L hD
    have hscale := costedNatMul_steps_le 2 s (s + 2) (by omega) (by omega)
    have hout := costedRationalDyadicOutput_steps_le true (2 * s) (15 * L + 17) (costedRationalSymmetrize D).value
      (costedRationalSymmetrize_size D L hD)
    simp only [costedRationalSpectralFinish, ite_true, Costed.bind_steps]
    dsimp only [costedNatMul]
    dsimp only [costedNatMul] at hscale
    unfold rationalSpectralFinishBudget
    omega

def rationalSpectralBudget (n S t : ℕ) : ℕ :=
  let s := n + 2 * S
  let E := 2 * s
  let B := n * (S + E)
  let U := 2 * S + E + 3
  let M := rationalSpectralCoreBudget n U t B s
  rationalNormalizationBudget n S + M + rationalSpectralFinishBudget n s M

theorem costedRationalSpectralApprox_steps_le {n : ℕ} (inverse : Bool) (t : ℕ) (D : RationalMatrixData n)
    (hD : ((rationalMatrixOfData D).map (fun q : ℚ => (q : ℝ))).PosDef) :
    (costedRationalSpectralApprox inverse t D).steps ≤ rationalSpectralBudget n (rationalMatrixMagnitudeBits (rationalMatrixOfData D)) t := by
  let A := rationalMatrixOfData D
  let P := rationalNormalizedInput D
  let S := rationalMatrixMagnitudeBits A
  let U := 2 * S + rationalMatrixNormalizationExponent A + 3
  let M := rationalSpectralCoreBudget n U t P.conditionExponent P.scaleExponent
  have hA : ((integerMatrixQuotient P.denominator (integerMatrixOfData P.numerators)).map (fun q : ℚ => (q : ℝ))).PosSemidef := by
    rw [rationalNormalizedInput_reconstruct]
    exact (normalizedRationalMatrix_posDef A hD).posSemidef
  have hspec := normalizedRationalMatrix_spectral_bounds A hD
  have hlo : ∀ i, 1 / (2 : ℝ) ^ P.conditionExponent ≤ hA.isHermitian.eigenvalues i := by
    rw [show P.conditionExponent = rationalMatrixConditionExponent A from rfl]
    simpa only [P, A, rationalNormalizedInput_reconstruct] using hspec.1
  have hhi : ∀ i, hA.isHermitian.eigenvalues i ≤ 1 := by
    simpa only [P, rationalNormalizedInput_reconstruct] using hspec.2
  have hsizes := rationalNormalizedInput_sizes D
  have hcore := costedRationalSpectralCore_steps_le inverse t U P (rationalNormalizedInput_denominator_pos D)
    hsizes.1 hsizes.2 hA hlo hhi
  change (costedRationalSpectralCore inverse t P).steps ≤ M at hcore
  have hlength := (costedRationalSpectralCore_length_le_steps inverse t P).trans hcore
  have hout := costedRationalSpectralFinish_steps_le inverse P.scaleExponent M (costedRationalSpectralCore inverse t P).value
    (fun i j => (rationalMatrixEntryBits_le_encoded _ i j).trans hlength)
  have hprep := costedRationalNormalization_steps_le D
  rw [costedRationalSpectralApprox, Costed.bind_steps, costedRationalNormalization_value, Costed.bind_steps]
  change (costedRationalNormalization D).steps + ((costedRationalSpectralCore inverse t P).steps +
    (costedRationalSpectralFinish inverse P.scaleExponent (costedRationalSpectralCore inverse t P).value).steps) ≤ _
  change _ ≤ rationalNormalizationBudget n S + M + rationalSpectralFinishBudget n P.scaleExponent M
  change (costedRationalNormalization D).steps ≤ rationalNormalizationBudget n S at hprep
  omega

end GeometricGaussianLHL

end RationalSpectralCostBounds

section RationalSpectralCertificate

/-!
## Numerical certificates polynomial in the actual rational input encoding

Positive definiteness is the only validity condition. Integer sizes,
conditioning, working precisions and output lengths are all derived. The
polynomial constants are uniform across dimensions and both fixed algorithms.
-/

open scoped MatrixOrder Matrix.Norms.L2Operator
namespace GeometricGaussianLHL

theorem polyBound_natProductBudget {m S : ℕ → ℕ} (hm : PolynomialCostBound m) (hS : PolynomialCostBound S) :
    PolynomialCostBound (fun x => natProductBudget (m x) (S x)) :=
  (hm.mul (((((PolynomialCostBound.const 2).mul hS).add (PolynomialCostBound.const 2)).pow 2).add (PolynomialCostBound.const 1))).add (PolynomialCostBound.const 1)

theorem polyBound_rationalDenominatorBudget {n S : ℕ → ℕ} (hn : PolynomialCostBound n) (hS : PolynomialCostBound S) :
    PolynomialCostBound (fun x => rationalDenominatorBudget (n x) (S x)) :=
  ((((PolynomialCostBound.const 2).mul hn).mul hn).add (PolynomialCostBound.const 1)).add (polyBound_natProductBudget (hn.mul hn) hS)

theorem polyBound_rationalNumeratorBudget {n L : ℕ → ℕ} (hn : PolynomialCostBound n) (hL : PolynomialCostBound L) :
    PolynomialCostBound (fun x => rationalNumeratorBudget (n x) (L x)) :=
  polyBound_integerMatrixTraversalBudget hn ((((PolynomialCostBound.const 2).mul
    ((((PolynomialCostBound.const 2).mul hL).add (PolynomialCostBound.const 1)).pow 2)).add hL).add (PolynomialCostBound.const 1))

theorem polyBound_rationalIntegerInputBudget {n S : ℕ → ℕ} (hn : PolynomialCostBound n) (hS : PolynomialCostBound S) :
    PolynomialCostBound (fun x => rationalIntegerInputBudget (n x) (S x)) :=
  (polyBound_rationalDenominatorBudget hn hS).add (polyBound_rationalNumeratorBudget hn (hS.add (PolynomialCostBound.const 1)))

theorem polyBound_natSumBudget {m S : ℕ → ℕ} (hm : PolynomialCostBound m) (hS : PolynomialCostBound S) :
    PolynomialCostBound (fun x => natSumBudget (m x) (S x)) :=
  (hm.mul (((PolynomialCostBound.const 2).mul hS).add (PolynomialCostBound.const 2))).add (PolynomialCostBound.const 1)

theorem polyBound_rationalMagnitudeBudget {n S : ℕ → ℕ} (hn : PolynomialCostBound n) (hS : PolynomialCostBound S) :
    PolynomialCostBound (fun x => rationalMagnitudeBudget (n x) (S x)) :=
  (((PolynomialCostBound.const 4).mul (((((PolynomialCostBound.const 2).mul hn).add (PolynomialCostBound.const 1)).add
    ((PolynomialCostBound.const 2).mul hS)).add (hn.mul hn))).add (PolynomialCostBound.const 1)).add (polyBound_natSumBudget (hn.mul hn) hS)

theorem polyBound_rationalNormalizationScheduleBudget {n S : ℕ → ℕ} (hn : PolynomialCostBound n) (hS : PolynomialCostBound S) :
    PolynomialCostBound (fun x => rationalNormalizationScheduleBudget (n x) (S x)) :=
  (PolynomialCostBound.const 5).mul ((((PolynomialCostBound.const 10).mul ((hn.add hS).add (PolynomialCostBound.const 1))).add (PolynomialCostBound.const 1)).pow 2)

theorem polyBound_normalizeIntegerDenominatorBudget {L E : ℕ → ℕ} (hL : PolynomialCostBound L) (hE : PolynomialCostBound E) :
    PolynomialCostBound (fun x => normalizeIntegerDenominatorBudget (L x) (E x)) :=
  (hE.add (PolynomialCostBound.const 1)).add (((hL.add hE).add (PolynomialCostBound.const 2)).pow 2)

theorem polyBound_rationalNormalizationBudget {n S : ℕ → ℕ} (hn : PolynomialCostBound n) (hS : PolynomialCostBound S) :
    PolynomialCostBound (fun x => rationalNormalizationBudget (n x) (S x)) :=
  (((polyBound_rationalMagnitudeBudget hn hS).add (polyBound_rationalNormalizationScheduleBudget hn hS)).add
    (polyBound_rationalIntegerInputBudget hn hS)).add (polyBound_normalizeIntegerDenominatorBudget
      (hS.add (PolynomialCostBound.const 1)) ((PolynomialCostBound.const 2).mul (hn.add ((PolynomialCostBound.const 2).mul hS))))

theorem polyBound_rationalMatrixEncodingBudget {n L : ℕ → ℕ} (hn : PolynomialCostBound n) (hL : PolynomialCostBound L) :
    PolynomialCostBound (fun x => rationalMatrixEncodingBudget (n x) (L x)) :=
  (((PolynomialCostBound.const 2).mul hn).add (PolynomialCostBound.const 1)).add
    ((hn.mul hn).mul (((PolynomialCostBound.const 2).mul hL).add (PolynomialCostBound.const 1)))

theorem polyBound_rationalDyadicScalarBudget {e : ℕ → ℕ} (he : PolynomialCostBound e) :
    PolynomialCostBound (fun x => rationalDyadicScalarBudget (e x)) :=
  (((PolynomialCostBound.const 2).mul he).add (PolynomialCostBound.const 3)).add ((he.add (PolynomialCostBound.const 7)).pow 3)

theorem polyBound_rationalDyadicOutputBudget {n e L : ℕ → ℕ}
    (hn : PolynomialCostBound n) (he : PolynomialCostBound e) (hL : PolynomialCostBound L) :
    PolynomialCostBound (fun x => rationalDyadicOutputBudget (n x) (e x) (L x)) := by
  have hH := (hL.add ((PolynomialCostBound.const 2).mul he)).add (PolynomialCostBound.const 3)
  exact ((polyBound_rationalDyadicScalarBudget he).add (polyBound_integerMatrixTraversalBudget hn
    ((((PolynomialCostBound.const 2).mul hH).add (PolynomialCostBound.const 1)).pow 3))).add
      (polyBound_rationalMatrixEncodingBudget hn (((PolynomialCostBound.const 6).mul hH).add (PolynomialCostBound.const 3)))

theorem polyBound_rationalSymmetrizeBudget {n L : ℕ → ℕ} (hn : PolynomialCostBound n) (hL : PolynomialCostBound L) :
    PolynomialCostBound (fun x => rationalSymmetrizeBudget (n x) (L x)) :=
  polyBound_integerMatrixTraversalBudget hn
    (((((PolynomialCostBound.const 2).mul hL).add (PolynomialCostBound.const 1)).pow 3).add
      ((((PolynomialCostBound.const 5).mul hL).add (PolynomialCostBound.const 9)).pow 3))

theorem polyBound_rationalSpectralCoreBudget {n U t B s : ℕ → ℕ}
    (hn : PolynomialCostBound n) (hU : PolynomialCostBound U) (ht : PolynomialCostBound t)
    (hB : PolynomialCostBound B) (hs : PolynomialCostBound s) :
    PolynomialCostBound (fun x => rationalSpectralCoreBudget (n x) (U x) (t x) (B x) (s x)) :=
  ((((PolynomialCostBound.const 2).mul ((ht.add hs).add (PolynomialCostBound.const 2))).add (PolynomialCostBound.const 1)).pow 2).add
    (polyBound_integerSchulzApproximationBudget hn hU ((ht.add hs).add (PolynomialCostBound.const 1)) hB)

theorem polyBound_rationalSpectralFinishBudget {n s L : ℕ → ℕ}
    (hn : PolynomialCostBound n) (hs : PolynomialCostBound s) (hL : PolynomialCostBound L) :
    PolynomialCostBound (fun x => rationalSpectralFinishBudget (n x) (s x) (L x)) :=
  ((polyBound_rationalSymmetrizeBudget hn hL).add
    ((((PolynomialCostBound.const 2).mul (hs.add (PolynomialCostBound.const 2))).add (PolynomialCostBound.const 1)).pow 2)).add
      (polyBound_rationalDyadicOutputBudget hn ((PolynomialCostBound.const 2).mul hs)
        (((PolynomialCostBound.const 15).mul hL).add (PolynomialCostBound.const 17)))

theorem polyBound_rationalSpectralBudget {n S t : ℕ → ℕ}
    (hn : PolynomialCostBound n) (hS : PolynomialCostBound S) (ht : PolynomialCostBound t) :
    PolynomialCostBound (fun x => rationalSpectralBudget (n x) (S x) (t x)) := by
  have hs := hn.add ((PolynomialCostBound.const 2).mul hS)
  have hE := (PolynomialCostBound.const 2).mul hs
  have hB := hn.mul (hS.add hE)
  have hU := (((PolynomialCostBound.const 2).mul hS).add hE).add (PolynomialCostBound.const 3)
  have hM := polyBound_rationalSpectralCoreBudget hn hU ht hB hs
  exact ((polyBound_rationalNormalizationBudget hn hS).add hM).add (polyBound_rationalSpectralFinishBudget hn hs hM)

theorem rationalNormalizationBudget_mono {n n' S S' : ℕ} (hn : n ≤ n') (hS : S ≤ S') :
    rationalNormalizationBudget n S ≤ rationalNormalizationBudget n' S' := by
  unfold rationalNormalizationBudget rationalMagnitudeBudget natSumBudget rationalNormalizationScheduleBudget
    rationalIntegerInputBudget rationalDenominatorBudget natProductBudget rationalNumeratorBudget
    integerMatrixTraversalBudget normalizeIntegerDenominatorBudget
  gcongr

theorem rationalSpectralCoreBudget_mono {n n' U U' t t' B B' s s' : ℕ}
    (hn : n ≤ n') (hU : U ≤ U') (ht : t ≤ t') (hB : B ≤ B') (hs : s ≤ s') :
    rationalSpectralCoreBudget n U t B s ≤ rationalSpectralCoreBudget n' U' t' B' s' := by
  apply Nat.add_le_add
  · gcongr
  · exact integerSchulzApproximationBudget_mono hn hU (by omega) hB

theorem rationalSpectralFinishBudget_mono {n n' s s' L L' : ℕ}
    (hn : n ≤ n') (hs : s ≤ s') (hL : L ≤ L') :
    rationalSpectralFinishBudget n s L ≤ rationalSpectralFinishBudget n' s' L' := by
  apply Nat.add_le_add
  · unfold rationalSymmetrizeBudget integerMatrixTraversalBudget
    gcongr
  · exact rationalDyadicOutputBudget_mono hn (by omega) (by omega)

theorem rationalSpectralBudget_mono {n n' S S' t t' : ℕ}
    (hn : n ≤ n') (hS : S ≤ S') (ht : t ≤ t') :
    rationalSpectralBudget n S t ≤ rationalSpectralBudget n' S' t' := by
  have hs : n + 2 * S ≤ n' + 2 * S' := by omega
  have hU : 2 * S + 2 * (n + 2 * S) + 3 ≤ 2 * S' + 2 * (n' + 2 * S') + 3 := by omega
  have hB : n * (S + 2 * (n + 2 * S)) ≤ n' * (S' + 2 * (n' + 2 * S')) := by gcongr
  have hM := rationalSpectralCoreBudget_mono hn hU ht hB hs
  exact Nat.add_le_add (Nat.add_le_add (rationalNormalizationBudget_mono hn hS) hM)
    (rationalSpectralFinishBudget_mono hn hs hM)

/-- The bound uses the actual input encoding and requested precision, uniformly in dimension. -/
theorem rationalSpectralApprox_polynomial_cost : ∃ C e : ℕ,
    ∀ (inverse : Bool) (n t : ℕ) (D : RationalMatrixData n),
      ((rationalMatrixOfData D).map (fun q : ℚ => (q : ℝ))).PosDef →
      (costedRationalSpectralApprox inverse t D).steps ≤ C * ((encodeRationalMatrixData D).length + t + 1) ^ e := by
  obtain ⟨C, e, hCe⟩ := (polyBound_rationalSpectralBudget PolynomialCostBound.id PolynomialCostBound.id PolynomialCostBound.id).exists_mul_pow_bound
  refine ⟨C, e, fun inverse n t D hD => ?_⟩
  have hlen := encodeRationalMatrixData_length D
  have hn : n ≤ (encodeRationalMatrixData D).length := by have := Nat.le_mul_self n; omega
  have hS : rationalMatrixMagnitudeBits (rationalMatrixOfData D) ≤ (encodeRationalMatrixData D).length := by omega
  exact (costedRationalSpectralApprox_steps_le inverse t D hD).trans
    ((rationalSpectralBudget_mono (by omega) (by omega) (show t ≤ (encodeRationalMatrixData D).length + t by omega)).trans
      (hCe ((encodeRationalMatrixData D).length + t)))

theorem rationalSpectralApprox_polynomialTime (n : ℕ) (inverse : Bool) :
    Costed.PolynomialTime (fun D t => costedRationalSpectralApprox inverse t (D : RationalMatrixData n))
      (fun D => ((rationalMatrixOfData D).map (fun q : ℚ => (q : ℝ))).PosDef)
      (fun D => (encodeRationalMatrixData D).length) := by
  obtain ⟨C, e, hCe⟩ := rationalSpectralApprox_polynomial_cost
  exact ⟨C, e, fun D hD t => hCe inverse n t D hD⟩

theorem rationalSpectral_approximation_certificate : ∃ C e : ℕ,
    ∀ (inverse : Bool) (n t : ℕ) (D : RationalMatrixData n),
      ((rationalMatrixOfData D).map (fun q : ℚ => (q : ℝ))).PosDef →
      let A := (rationalMatrixOfData D).map (fun q : ℚ => (q : ℝ))
      let run := costedRationalSpectralApprox inverse t D
      run.steps ≤ C * ((encodeRationalMatrixData D).length + t + 1) ^ e ∧
      (encodeRationalMatrixData run.value).length ≤ C * ((encodeRationalMatrixData D).length + t + 1) ^ e ∧
      decodeRationalMatrixDataPrefix (encodeRationalMatrixData run.value) = some (⟨n, run.value⟩, []) ∧
      ‖(Matrix.toEuclideanLin ((rationalMatrixOfData run.value).map (fun q : ℚ => (q : ℝ)))).toContinuousLinearMap -
        (Matrix.toEuclideanLin (if inverse then A⁻¹ else CFC.sqrt A)).toContinuousLinearMap‖ ≤ 1 / (2 : ℝ) ^ t := by
  obtain ⟨C, e, hCe⟩ := rationalSpectralApprox_polynomial_cost
  refine ⟨C, e, fun inverse n t D hD => ?_⟩
  have hc := hCe inverse n t D hD
  refine ⟨hc, (costedRationalSpectralApprox_length_le_steps inverse t D).trans hc, ?_,
    costedRationalSpectralApprox_operator_error inverse t D hD⟩
  simpa only [List.append_nil] using decodeRationalMatrixData_append (costedRationalSpectralApprox inverse t D).value []

end GeometricGaussianLHL

end RationalSpectralCertificate
