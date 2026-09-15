import GeometricGaussianLHL.Foundations
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Rat.Lemmas
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Module

/-!
# Finite encodings and dyadic storage

This module collects the following proof sections, in dependency order.
- Stored rational matrix representation (`RationalMatrixData`).
- Prefix encodings for stored vectors (`VectorPrefix`).
- Integer matrices with a common denominator (`IntegerQuotientData`).
- Stored integer matrix representation (`IntegerMatrixData`).
- Executable dyadic rounding and its error (`DyadicRounding`).
- Entry bounds from the Euclidean operator norm (`MatrixEntryBound`).
- From entry errors to Euclidean operator errors (`MatrixEntryError`).
- Binary size of rational values on a dyadic grid (`DyadicRationalSize`).
- Executable matrix rounding with an operator-norm guarantee (`MatrixDyadicRounding`).
- Self-delimiting binary encodings of integers and rationals (`BinaryPrefix`).
- Binary magnitude of rational matrix entries (`MatrixMagnitudeBits`).
- Binary size of rounded matrix numerators (`DyadicStorage`).
- Magnitude bounds for arbitrary successfully decoded prefixes (`BinaryPrefixSize`).
- Raw rational pairs retained by the matrix-input program (`RawRationalPrefix`).
- An actual binary codec for stored rational matrices (`MatrixBinaryEncoding`).
- Clearing rational matrix denominators (`RationalDenominatorData`).
- Exact quotients and space consumed by the rational matrix encoding (`CommonNumeratorEncoding`).
- Row-major entry lists for the actual rational matrix codec (`MatrixInputEncoding`).
- Casting common-denominator representations to real matrices (`RationalDenominatorCast`).
- Entry magnitude from encoded input size (`RationalMagnitudeBound`).
- Width magnitude from encoded input size (`RationalWidthMagnitude`).
-/

section RationalMatrixData

/-!
## Stored rational matrix representation
-/

set_option backward.isDefEq.respectTransparency false

open scoped MatrixOrder Matrix.Norms.L2Operator

namespace GeometricGaussianLHL

abbrev RationalMatrixData (n : ℕ) := Vector (Vector ℚ n) n

def rationalMatrixData {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) : RationalMatrixData n :=
  Vector.ofFn (fun i => Vector.ofFn (A i))

def rationalMatrixOfData {n : ℕ} (D : RationalMatrixData n) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j => (D.get i).get j

theorem rationalMatrixOfData_data {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) :
    rationalMatrixOfData (rationalMatrixData A) = A := by
  ext i j
  simp [rationalMatrixOfData, rationalMatrixData, Vector.get]

end GeometricGaussianLHL

end RationalMatrixData

section VectorPrefix

/-!
## Prefix encodings for stored vectors

The encoder concatenates the component words. The decoder knows the vector
length and reconstructs the array by pushing decoded entries. A separate
length guard can reject oversized dimensions before this recursion is used.
-/

set_option backward.isDefEq.respectTransparency false

namespace GeometricGaussianLHL

def encodeVectorBits {α : Type*} {n : ℕ} (enc : α → List Bool) (v : Vector α n) : List Bool :=
  v.toList.flatMap enc

def decodeVectorPrefix {α : Type*} (dec : List Bool → Option (α × List Bool)) :
    (n : ℕ) → List Bool → Option (Vector α n × List Bool)
  | 0, bs => some (#v[], bs)
  | n + 1, bs => do
    let (v, rest) ← decodeVectorPrefix dec n bs
    let (x, tail) ← dec rest
    return (v.push x, tail)

theorem decodeVectorBits_append {α : Type*} (enc : α → List Bool)
    (dec : List Bool → Option (α × List Bool))
    (hdec : ∀ x tail, dec (enc x ++ tail) = some (x, tail))
    {n : ℕ} (v : Vector α n) (tail : List Bool) :
    decodeVectorPrefix dec n (encodeVectorBits enc v ++ tail) = some (v, tail) := by
  induction n generalizing tail with
  | zero =>
    have hv : v = #v[] := Vector.eq_empty
    subst v
    rfl
  | succ n ih =>
    rw [← Vector.push_pop_back v]
    rw [encodeVectorBits, Vector.toList_push, List.flatMap_append]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]
    rw [decodeVectorPrefix]
    change ((decodeVectorPrefix dec n
      (encodeVectorBits enc v.pop ++ (enc v.back ++ tail))).bind
      (fun q => (dec q.2).bind (fun r => some (q.1.push r.1, r.2)))) = _
    rw [ih v.pop (enc v.back ++ tail)]
    simp only [Option.bind_some, hdec]

theorem encodeVectorBits_length {α : Type*} {n : ℕ}
    (enc : α → List Bool) (v : Vector α n) :
    (encodeVectorBits enc v).length = (v.toList.map (fun x => (enc x).length)).sum := by
  simp [encodeVectorBits, List.length_flatMap]

theorem encodeVectorBits_length_le {α : Type*} {n b : ℕ}
    (enc : α → List Bool) (v : Vector α n) (h : ∀ x ∈ v.toList, (enc x).length ≤ b) :
    (encodeVectorBits enc v).length ≤ n * b := by
  rw [encodeVectorBits_length]
  have hl : ∀ l : List α, (∀ x ∈ l, (enc x).length ≤ b) →
      (l.map (fun x => (enc x).length)).sum ≤ l.length * b := by
    intro l
    induction l with
    | nil => simp
    | cons x l ih =>
      intro hh
      have hx := hh x (by simp)
      have ht := ih (fun y hy => hh y (by simp [hy]))
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      nlinarith
  simpa using hl v.toList h

end GeometricGaussianLHL

end VectorPrefix

section IntegerQuotientData

/-!
## Integer matrices with a common denominator
-/

set_option backward.isDefEq.respectTransparency false

namespace GeometricGaussianLHL

def integerMatrixCast {n : ℕ} (X : Matrix (Fin n) (Fin n) ℤ) :
    Matrix (Fin n) (Fin n) ℚ := (Int.castRingHom ℚ).mapMatrix X

def integerMatrixQuotient {n : ℕ} (a : ℕ) (X : Matrix (Fin n) (Fin n) ℤ) :
    Matrix (Fin n) (Fin n) ℚ := (a : ℚ)⁻¹ • integerMatrixCast X

theorem integerMatrixQuotient_apply {n : ℕ} (a : ℕ)
    (X : Matrix (Fin n) (Fin n) ℤ) (i j : Fin n) :
    integerMatrixQuotient a X i j = (X i j : ℚ) / a := by
  simp [integerMatrixQuotient, integerMatrixCast, div_eq_mul_inv, mul_comm]

theorem integerMatrixCast_smul {n : ℕ} (c : ℤ)
    (X : Matrix (Fin n) (Fin n) ℤ) :
    integerMatrixCast (c • X) = (c : ℚ) • integerMatrixCast X := by
  ext i j
  change ((c • X i j : ℤ) : ℚ) = (c : ℚ) • (X i j : ℚ)
  simp only [smul_eq_mul, Int.cast_mul]

end GeometricGaussianLHL

end IntegerQuotientData

section IntegerMatrixData

/-!
## Stored integer matrix representation
-/

set_option backward.isDefEq.respectTransparency false

open scoped MatrixOrder Matrix.Norms.L2Operator

namespace GeometricGaussianLHL

abbrev IntegerMatrixData (n : ℕ) := Vector (Vector ℤ n) n

def integerMatrixData {n : ℕ} (X : Matrix (Fin n) (Fin n) ℤ) : IntegerMatrixData n :=
  Vector.ofFn (fun i => Vector.ofFn (X i))

def integerMatrixOfData {n : ℕ} (D : IntegerMatrixData n) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j => (D.get i).get j

theorem integerMatrixOfData_data {n : ℕ} (X : Matrix (Fin n) (Fin n) ℤ) :
    integerMatrixOfData (integerMatrixData X) = X := by
  ext i j
  simp [integerMatrixOfData, integerMatrixData, Vector.get]

end GeometricGaussianLHL

end IntegerMatrixData

section DyadicRounding

/-!
## Executable dyadic rounding and its error

Rational intermediate values are rounded down to an integer divided by
`2^t`. The implementation uses rational arithmetic and integer floor, so
it is executable. The error theorems are independent of an input encoding;
they do not assert a polynomial bound on bit operations.
-/

namespace GeometricGaussianLHL

def dyadicNumerator (t : ℕ) (x : ℚ) : ℤ := ⌊x * (2 : ℚ) ^ t⌋

def dyadicRoundRat (t : ℕ) (x : ℚ) : ℚ :=
  (dyadicNumerator t x : ℚ) / (2 : ℚ) ^ t

theorem dyadicRoundRat_le (t : ℕ) (x : ℚ) : dyadicRoundRat t x ≤ x := by
  unfold dyadicRoundRat dyadicNumerator
  exact (div_le_iff₀ (by positivity)).mpr (Int.floor_le _)

theorem dyadicRoundRat_error_nonneg (t : ℕ) (x : ℚ) :
    0 ≤ x - dyadicRoundRat t x := sub_nonneg.mpr (dyadicRoundRat_le t x)

theorem dyadicRoundRat_error_lt (t : ℕ) (x : ℚ) :
    x - dyadicRoundRat t x < 1 / (2 : ℚ) ^ t := by
  have h := Int.lt_floor_add_one (x * (2 : ℚ) ^ t)
  rw [sub_lt_iff_lt_add, dyadicRoundRat, ← add_div, lt_div_iff₀ (by positivity)]
  simpa only [dyadicNumerator, add_comm] using h

theorem dyadicRoundRat_abs_error_lt (t : ℕ) (x : ℚ) :
    |x - dyadicRoundRat t x| < 1 / (2 : ℚ) ^ t := by
  rw [abs_of_nonneg (dyadicRoundRat_error_nonneg t x)]
  exact dyadicRoundRat_error_lt t x

theorem dyadicRoundRat_real_error_lt (t : ℕ) (x : ℚ) :
    |(x : ℝ) - (dyadicRoundRat t x : ℝ)| < 1 / (2 : ℝ) ^ t := by
  have h := (Rat.cast_lt (K := ℝ)).mpr (dyadicRoundRat_abs_error_lt t x)
  simpa only [Rat.cast_abs, Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_pow,
    Rat.cast_ofNat] using h

theorem dyadicRoundRat_grid (t : ℕ) (x : ℚ) :
    dyadicRoundRat t x * (2 : ℚ) ^ t = dyadicNumerator t x := by
  unfold dyadicRoundRat
  exact div_mul_cancel₀ _ (by positivity)

theorem dyadicRoundRat_fixed (t : ℕ) (z : ℤ) :
    dyadicRoundRat t ((z : ℚ) / (2 : ℚ) ^ t) = (z : ℚ) / (2 : ℚ) ^ t := by
  simp [dyadicRoundRat, dyadicNumerator, div_mul_cancel₀ _ (show (2 : ℚ) ^ t ≠ 0 by positivity)]

theorem dyadicRoundRat_idempotent (t : ℕ) (x : ℚ) :
    dyadicRoundRat t (dyadicRoundRat t x) = dyadicRoundRat t x := by
  exact dyadicRoundRat_fixed t (dyadicNumerator t x)

theorem dyadicNumerator_abs_le (t : ℕ) (x : ℚ) :
    |(dyadicNumerator t x : ℚ)| ≤ |x| * (2 : ℚ) ^ t + 1 := by
  have habs : |x * (2 : ℚ) ^ t - dyadicNumerator t x| < 1 := by
    have h := dyadicRoundRat_abs_error_lt t x
    have hm := (mul_lt_mul_iff_left₀ (show 0 < (2 : ℚ) ^ t by positivity)).mpr h
    rw [← abs_of_pos (show 0 < (2 : ℚ) ^ t by positivity), ← abs_mul] at hm
    simpa [mul_sub, mul_div_cancel₀, dyadicRoundRat, mul_comm] using hm
  calc
    |(dyadicNumerator t x : ℚ)| = |x * (2 : ℚ) ^ t -
        (x * (2 : ℚ) ^ t - dyadicNumerator t x)| := by ring_nf
    _ ≤ |x * (2 : ℚ) ^ t| + |x * (2 : ℚ) ^ t - dyadicNumerator t x| := abs_sub _ _
    _ ≤ |x| * (2 : ℚ) ^ t + 1 := by
      rw [abs_mul, abs_of_pos (show 0 < (2 : ℚ) ^ t by positivity)]
      exact add_le_add_right habs.le _

end GeometricGaussianLHL

end DyadicRounding

section MatrixEntryBound

/-!
## Entry bounds from the Euclidean operator norm

Applying the matrix to a coordinate unit vector bounds each of its entries
by its operator norm. This supplies binary magnitude bounds for stored
numerical iterates from the proved spectral estimates.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open scoped Matrix.Norms.L2Operator

namespace GeometricGaussianLHL

theorem euclideanMatrix_entry_le_norm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (i j : Fin n) : |A i j| ≤ ‖A‖ := by
  let T := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A
  let v : Euclidean n := PiLp.single 2 j (1 : ℝ)
  have he : (T v) i = A i j := by
    change (T (WithLp.toLp 2 (Pi.single j (1 : ℝ)))) i = A i j
    simp [T, Matrix.mulVec, dotProduct]
  calc
    |A i j| = ‖(T v) i‖ := by rw [he, Real.norm_eq_abs]
    _ ≤ ‖T v‖ := PiLp.norm_apply_le _ _
    _ ≤ ‖T‖ * ‖v‖ := T.le_opNorm v
    _ = ‖A‖ := by simp [v, T, Matrix.l2_opNorm_toEuclideanCLM]

theorem rationalMatrix_entry_bound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ)
    (B : ℕ) (hA : ‖A.map (fun q : ℚ => (q : ℝ))‖ ≤ (2 : ℝ) ^ B)
    (i j : Fin n) : |A i j| ≤ (2 : ℚ) ^ B := by
  have h := (euclideanMatrix_entry_le_norm (A.map (fun q : ℚ => (q : ℝ))) i j).trans hA
  apply (Rat.cast_le (K := ℝ)).mp
  simpa only [Rat.cast_abs, Rat.cast_pow, Rat.cast_ofNat, Matrix.map_apply] using h

end GeometricGaussianLHL
end

end MatrixEntryBound

section MatrixEntryError

/-!
## From entry errors to Euclidean operator errors

For an `n` by `n` matrix, an absolute entry bound `b` gives Euclidean
operator norm at most `n b`. The proof uses row inner products and
Cauchy–Schwarz in the actual Euclidean metric.
-/

noncomputable section

namespace GeometricGaussianLHL

theorem euclideanMatrix_row_norm_sq_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    {b : ℝ} (hA : ∀ i j, |A i j| ≤ b) (i : Fin n) :
    ‖(WithLp.toLp 2 (fun j => A i j) : Euclidean n)‖ ^ 2 ≤ (n : ℝ) * b ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  calc
    _ ≤ ∑ _j : Fin n, b ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      simpa only [Real.norm_eq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hA i j) 2
    _ = _ := by simp

theorem euclideanMatrix_norm_apply_le_entries {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    {b : ℝ} (hb : 0 ≤ b) (hA : ∀ i j, |A i j| ≤ b) (x : Euclidean n) :
    ‖Matrix.toEuclideanLin A x‖ ≤ (n : ℝ) * b * ‖x‖ := by
  have hrow (i : Fin n) :
      (Matrix.toEuclideanLin A x i) ^ 2 ≤ (n : ℝ) * b ^ 2 * ‖x‖ ^ 2 := by
    let v : Euclidean n := WithLp.toLp 2 (fun j => A i j)
    have he : Matrix.toEuclideanLin A x i = inner ℝ v x := by
      simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, PiLp.inner_apply,
        RCLike.inner_apply, v, mul_comm]
    rw [he]
    have hc := pow_le_pow_left₀ (abs_nonneg (inner ℝ v x)) (abs_real_inner_le_norm v x) 2
    rw [sq_abs, mul_pow] at hc
    exact hc.trans (mul_le_mul_of_nonneg_right (euclideanMatrix_row_norm_sq_le A hA i)
      (sq_nonneg ‖x‖))
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [EuclideanSpace.real_norm_sq_eq]
  calc
    _ ≤ ∑ _i : Fin n, (n : ℝ) * b ^ 2 * ‖x‖ ^ 2 :=
      Finset.sum_le_sum (fun i _ => hrow i)
    _ = ((n : ℝ) * b * ‖x‖) ^ 2 := by simp; ring

theorem euclideanMatrix_opNorm_le_entries {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    {b : ℝ} (hb : 0 ≤ b) (hA : ∀ i j, |A i j| ≤ b) :
    ‖(Matrix.toEuclideanLin A).toContinuousLinearMap‖ ≤ (n : ℝ) * b :=
  ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (Nat.cast_nonneg _) hb)
    (euclideanMatrix_norm_apply_le_entries A hb hA)

theorem euclideanMatrix_opNorm_sub_le_entries {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℝ) {b : ℝ} (hb : 0 ≤ b)
    (hAB : ∀ i j, |A i j - B i j| ≤ b) :
    ‖(Matrix.toEuclideanLin A).toContinuousLinearMap -
      (Matrix.toEuclideanLin B).toContinuousLinearMap‖ ≤ (n : ℝ) * b := by
  have h := euclideanMatrix_opNorm_le_entries (A - B) hb hAB
  simpa only [map_sub] using h

end GeometricGaussianLHL
end

end MatrixEntryError

section DyadicRationalSize

/-!
## Binary size of rational values on a dyadic grid

These bounds concern the actual reduced numerator and denominator of a
rational value. A fixed point of rounding at precision `p` has denominator
dividing `2^p`; an absolute value bound then controls its numerator too.
-/

namespace GeometricGaussianLHL

theorem dyadicRoundRat_int_fixed (p : ℕ) (z : ℤ) :
    dyadicRoundRat p (z : ℚ) = z := by
  have h := dyadicRoundRat_fixed p (z * (2 : ℤ) ^ p)
  simpa only [Int.cast_mul, Int.cast_pow, Int.cast_ofNat,
    mul_div_cancel_right₀ _ (by positivity : (2 : ℚ) ^ p ≠ 0)] using h

theorem dyadic_fixed_den_dvd (p : ℕ) (x : ℚ) (hx : dyadicRoundRat p x = x) :
    x.den ∣ 2 ^ p := by
  have he : dyadicRoundRat p x = Rat.divInt (dyadicNumerator p x) ((2 : ℤ) ^ p) := by
    simp only [dyadicRoundRat, Rat.divInt_eq_div, Int.cast_pow, Int.cast_ofNat]
  have hd := Rat.den_dvd (dyadicNumerator p x) ((2 : ℤ) ^ p)
  rw [← he, hx] at hd
  exact_mod_cast hd

theorem dyadic_fixed_den_le (p : ℕ) (x : ℚ) (hx : dyadicRoundRat p x = x) :
    x.den ≤ 2 ^ p := Nat.le_of_dvd (by positivity) (dyadic_fixed_den_dvd p x hx)

theorem dyadic_fixed_den_size (p : ℕ) (x : ℚ) (hx : dyadicRoundRat p x = x) :
    x.den.size ≤ p + 1 := by
  apply Nat.size_le.mpr
  have h := dyadic_fixed_den_le p x hx
  rw [pow_succ]
  have hp : 0 < 2 ^ p := by positivity
  omega

theorem dyadic_fixed_num_natAbs_le (p B : ℕ) (x : ℚ)
    (hgrid : dyadicRoundRat p x = x) (hx : |x| ≤ (2 : ℚ) ^ B) :
    x.num.natAbs ≤ 2 ^ (B + p) := by
  have hd : (x.den : ℚ) ≤ (2 : ℚ) ^ p := by
    exact_mod_cast dyadic_fixed_den_le p x hgrid
  have hdpos : (0 : ℚ) < x.den := by exact_mod_cast x.den_pos
  have he : (x.num : ℚ) = x * (x.den : ℚ) := by
    exact ((eq_div_iff (ne_of_gt hdpos)).mp x.num_div_den.symm).symm
  have hn : (x.num.natAbs : ℚ) ≤ (2 : ℚ) ^ (B + p) := by
    calc
      _ = |(x.num : ℚ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
      _ = |x| * (x.den : ℚ) := by rw [he, abs_mul, abs_of_pos hdpos]
      _ ≤ (2 : ℚ) ^ B * (2 : ℚ) ^ p := mul_le_mul hx hd hdpos.le (by positivity)
      _ = _ := by rw [pow_add]
  exact_mod_cast hn

theorem dyadic_fixed_num_size (p B : ℕ) (x : ℚ)
    (hgrid : dyadicRoundRat p x = x) (hx : |x| ≤ (2 : ℚ) ^ B) :
    x.num.natAbs.size ≤ B + p + 1 := by
  apply Nat.size_le.mpr
  have h := dyadic_fixed_num_natAbs_le p B x hgrid hx
  rw [pow_succ]
  have hp : 0 < 2 ^ (B + p) := by positivity
  omega

def rationalMagnitudeBits (x : ℚ) : ℕ := x.num.natAbs.size + 1 + x.den.size

theorem dyadic_fixed_rational_bits (p B : ℕ) (x : ℚ)
    (hgrid : dyadicRoundRat p x = x) (hx : |x| ≤ (2 : ℚ) ^ B) :
    rationalMagnitudeBits x ≤ B + 2 * p + 3 := by
  have hn := dyadic_fixed_num_size p B x hgrid hx
  have hd := dyadic_fixed_den_size p x hgrid
  unfold rationalMagnitudeBits
  omega

end GeometricGaussianLHL

end DyadicRationalSize

section MatrixDyadicRounding

/-!
## Executable matrix rounding with an operator-norm guarantee

Rounding every entry to `t+n` fractional binary places gives absolute
Euclidean operator error at most `2^(-t)` for an `n` by `n` rational matrix.
The integer numerators and their common denominator are explicit. These
results control rounding of rational intermediate matrices, not the cost
of computing the paper's real shaping matrix.
-/

namespace GeometricGaussianLHL

def dyadicMatrixNumerators {r m : ℕ} (t : ℕ) (A : Matrix (Fin r) (Fin m) ℚ) :
    Matrix (Fin r) (Fin m) ℤ := fun i j => dyadicNumerator t (A i j)

def dyadicRoundMatrix {r m : ℕ} (t : ℕ) (A : Matrix (Fin r) (Fin m) ℚ) :
    Matrix (Fin r) (Fin m) ℚ := fun i j => dyadicRoundRat t (A i j)

theorem dyadicRoundMatrix_apply {r m : ℕ} (t : ℕ)
    (A : Matrix (Fin r) (Fin m) ℚ) (i : Fin r) (j : Fin m) :
    dyadicRoundMatrix t A i j = (dyadicMatrixNumerators t A i j : ℚ) / (2 : ℚ) ^ t := rfl

theorem dyadicRoundMatrix_transpose {r m : ℕ} (t : ℕ)
    (A : Matrix (Fin r) (Fin m) ℚ) :
    (dyadicRoundMatrix t A).transpose = dyadicRoundMatrix t A.transpose := rfl

theorem dyadicRoundMatrix_symmetric {n : ℕ} (t : ℕ)
    (A : Matrix (Fin n) (Fin n) ℚ) (hA : A.transpose = A) :
    (dyadicRoundMatrix t A).transpose = dyadicRoundMatrix t A := by
  rw [dyadicRoundMatrix_transpose, hA]

theorem dyadicRoundMatrix_idempotent {r m : ℕ} (t : ℕ)
    (A : Matrix (Fin r) (Fin m) ℚ) :
    dyadicRoundMatrix t (dyadicRoundMatrix t A) = dyadicRoundMatrix t A := by
  ext i j
  exact dyadicRoundRat_idempotent t (A i j)

theorem dyadicRoundMatrix_entry_error {r m : ℕ} (t : ℕ)
    (A : Matrix (Fin r) (Fin m) ℚ) (i : Fin r) (j : Fin m) :
    |(A i j : ℝ) - (dyadicRoundMatrix t A i j : ℝ)| < 1 / (2 : ℝ) ^ t :=
  dyadicRoundRat_real_error_lt t (A i j)

theorem dyadicRoundMatrix_operator_error {n : ℕ} (t : ℕ)
    (A : Matrix (Fin n) (Fin n) ℚ) :
    ‖(Matrix.toEuclideanLin (A.map (fun q : ℚ => (q : ℝ)))).toContinuousLinearMap -
      (Matrix.toEuclideanLin ((dyadicRoundMatrix t A).map (fun q : ℚ => (q : ℝ)))).toContinuousLinearMap‖ ≤
      (n : ℝ) * (1 / (2 : ℝ) ^ t) := by
  apply euclideanMatrix_opNorm_sub_le_entries _ _ (by positivity)
  intro i j
  exact (dyadicRoundMatrix_entry_error t A i j).le

theorem dimension_guard_precision (n t : ℕ) :
    (n : ℝ) * (1 / (2 : ℝ) ^ (t + n)) ≤ 1 / (2 : ℝ) ^ t := by
  have hn : (n : ℝ) ≤ (2 : ℝ) ^ n := by
    exact_mod_cast (Nat.lt_two_pow_self (n := n)).le
  calc
    _ ≤ (2 : ℝ) ^ n * (1 / (2 : ℝ) ^ (t + n)) :=
      mul_le_mul_of_nonneg_right hn (by positivity)
    _ = _ := by rw [pow_add]; field_simp

theorem dyadicRoundMatrix_prescribed_error {n : ℕ} (t : ℕ)
    (A : Matrix (Fin n) (Fin n) ℚ) :
    ‖(Matrix.toEuclideanLin (A.map (fun q : ℚ => (q : ℝ)))).toContinuousLinearMap -
      (Matrix.toEuclideanLin ((dyadicRoundMatrix (t + n) A).map (fun q : ℚ => (q : ℝ)))).toContinuousLinearMap‖ ≤
      1 / (2 : ℝ) ^ t :=
  (dyadicRoundMatrix_operator_error (t + n) A).trans (dimension_guard_precision n t)

end GeometricGaussianLHL

end MatrixDyadicRounding

section BinaryPrefix

/-!
## Self-delimiting binary encodings of integers and rationals

Each magnitude bit is preceded by `true`, and `false` terminates the word.
An integer has an additional sign bit. A rational stores its reduced
numerator and denominator. Decoding consumes exactly one encoded value and
returns the untouched suffix; the length bounds count actual Boolean lists.
-/

namespace GeometricGaussianLHL

def binaryWordValue : List Bool → ℕ
  | [] => 0
  | b :: bs => Nat.bit b (binaryWordValue bs)

theorem binaryWordValue_bits (n : ℕ) : binaryWordValue n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => simp [binaryWordValue]
  | bit b n h ih => simp [Nat.bits_append_bit n b h, binaryWordValue, ih]

def encodeBitWord (bs : List Bool) : List Bool :=
  bs.flatMap (fun b => [true, b]) ++ [false]

def decodeNatPrefix : List Bool → Option (ℕ × List Bool)
  | false :: rest => some (0, rest)
  | true :: b :: rest => do
    let (n, tail) ← decodeNatPrefix rest
    return (Nat.bit b n, tail)
  | _ => none

theorem decodeBitWord_append (bs tail : List Bool) :
    decodeNatPrefix (encodeBitWord bs ++ tail) = some (binaryWordValue bs, tail) := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    change ((decodeNatPrefix (encodeBitWord bs ++ tail)).bind
      (fun p => some (Nat.bit b p.1, p.2))) = _
    rw [ih]
    rfl

theorem encodeBitWord_length (bs : List Bool) :
    (encodeBitWord bs).length = 2 * bs.length + 1 := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [encodeBitWord, List.flatMap_cons, List.length_append, List.length_cons,
      List.length_nil] at ih ⊢
    omega

def encodeNatBits (n : ℕ) : List Bool := encodeBitWord n.bits

theorem decodeNatBits_append (n : ℕ) (tail : List Bool) :
    decodeNatPrefix (encodeNatBits n ++ tail) = some (n, tail) := by
  rw [encodeNatBits, decodeBitWord_append, binaryWordValue_bits]

theorem encodeNatBits_length (n : ℕ) : (encodeNatBits n).length = 2 * n.size + 1 := by
  rw [encodeNatBits, encodeBitWord_length, Nat.size_eq_bits_len]

def encodeIntBits : ℤ → List Bool
  | .ofNat n => false :: encodeNatBits n
  | .negSucc n => true :: encodeNatBits (n + 1)

def decodeIntPrefix : List Bool → Option (ℤ × List Bool)
  | sign :: rest => do
    let (n, tail) ← decodeNatPrefix rest
    return (if sign then -(n : ℤ) else (n : ℤ), tail)
  | [] => none

theorem decodeIntBits_append (z : ℤ) (tail : List Bool) :
    decodeIntPrefix (encodeIntBits z ++ tail) = some (z, tail) := by
  cases z <;> simp only [encodeIntBits, List.cons_append, decodeIntPrefix, decodeNatBits_append] <;> rfl

theorem encodeIntBits_length (z : ℤ) :
    (encodeIntBits z).length = 2 * z.natAbs.size + 2 := by
  cases z <;> simp [encodeIntBits, encodeNatBits_length]

def encodeRatBits (x : ℚ) : List Bool := encodeIntBits x.num ++ encodeNatBits x.den

def decodeRatPrefix (bs : List Bool) : Option (ℚ × List Bool) := do
  let (num, rest) ← decodeIntPrefix bs
  let (den, tail) ← decodeNatPrefix rest
  if den = 0 then none else return (Rat.divInt num (den : ℤ), tail)

theorem decodeRatBits_append (x : ℚ) (tail : List Bool) :
    decodeRatPrefix (encodeRatBits x ++ tail) = some (x, tail) := by
  simp [encodeRatBits, decodeRatPrefix, List.append_assoc, decodeIntBits_append,
    decodeNatBits_append, x.den_ne_zero]

theorem encodeRatBits_length (x : ℚ) :
    (encodeRatBits x).length = 2 * rationalMagnitudeBits x + 1 := by
  simp only [encodeRatBits, List.length_append, encodeIntBits_length, encodeNatBits_length,
    rationalMagnitudeBits]
  omega

theorem encodeRatBits_injective : Function.Injective encodeRatBits := by
  intro x y h
  have hd := congrArg (fun bs => decodeRatPrefix (bs ++ [])) h
  simpa only [decodeRatBits_append, Option.some.injEq, Prod.mk.injEq, and_true] using hd

end GeometricGaussianLHL

end BinaryPrefix

section MatrixMagnitudeBits

/-!
## Binary magnitude of rational matrix entries
-/

set_option backward.isDefEq.respectTransparency false

open scoped MatrixOrder Matrix.Norms.L2Operator

namespace GeometricGaussianLHL

def rationalMatrixMagnitudeBits {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) : ℕ :=
  ∑ i, ∑ j, rationalMagnitudeBits (A i j)

end GeometricGaussianLHL

end MatrixMagnitudeBits

section DyadicStorage

/-!
## Binary size of rounded matrix numerators

The bounds count one sign bit and the ordinary binary magnitude of each
integer numerator. The common exponent and matrix dimensions are separate
metadata. This certifies the size of the rounded data, not execution time.
-/

namespace GeometricGaussianLHL

theorem dyadicNumerator_natAbs_le (t B : ℕ) (x : ℚ) (hx : |x| ≤ (2 : ℚ) ^ B) :
    (dyadicNumerator t x).natAbs ≤ 2 ^ (B + t) + 1 := by
  have h : |(dyadicNumerator t x : ℚ)| ≤ (2 : ℚ) ^ (B + t) + 1 := by
    calc
      _ ≤ |x| * (2 : ℚ) ^ t + 1 := dyadicNumerator_abs_le t x
      _ ≤ (2 : ℚ) ^ B * (2 : ℚ) ^ t + 1 := by gcongr
      _ = _ := by rw [pow_add]
  have he : (((dyadicNumerator t x).natAbs : ℕ) : ℚ) = |(dyadicNumerator t x : ℚ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  rw [← he] at h
  exact_mod_cast h

theorem dyadicNumerator_size_le (t B : ℕ) (x : ℚ) (hx : |x| ≤ (2 : ℚ) ^ B) :
    (dyadicNumerator t x).natAbs.size ≤ B + t + 2 := by
  apply Nat.size_le.mpr
  calc
    _ ≤ 2 ^ (B + t) + 1 := dyadicNumerator_natAbs_le t B x hx
    _ < 2 ^ (B + t + 2) := by
      rw [pow_add (2 : ℕ) (B + t) 2]
      have h : 0 < 2 ^ (B + t) := by positivity
      norm_num
      omega

theorem dyadicNumerator_signed_bits_le (t B : ℕ) (x : ℚ) (hx : |x| ≤ (2 : ℚ) ^ B) :
    (dyadicNumerator t x).natAbs.bits.length + 1 ≤ B + t + 3 := by
  rw [Nat.size_eq_bits_len]
  have h := dyadicNumerator_size_le t B x hx
  omega

def dyadicMatrixNumeratorBits {r m : ℕ} (t : ℕ) (A : Matrix (Fin r) (Fin m) ℚ) : ℕ :=
  ∑ i, ∑ j, ((dyadicMatrixNumerators t A i j).natAbs.size + 1)

theorem dyadicMatrixNumeratorBits_le {r m : ℕ} (t B : ℕ)
    (A : Matrix (Fin r) (Fin m) ℚ) (hA : ∀ i j, |A i j| ≤ (2 : ℚ) ^ B) :
    dyadicMatrixNumeratorBits t A ≤ r * m * (B + t + 3) := by
  unfold dyadicMatrixNumeratorBits
  calc
    _ ≤ ∑ _i : Fin r, ∑ _j : Fin m, (B + t + 3) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      have h := dyadicNumerator_size_le t B (A i j) (hA i j)
      change (dyadicNumerator t (A i j)).natAbs.size + 1 ≤ _
      omega
    _ = _ := by simp [Nat.mul_assoc]

end GeometricGaussianLHL

end DyadicStorage

section BinaryPrefixSize

/-!
## Magnitude bounds for arbitrary successfully decoded prefixes

Leading zeroes and negative zero are permitted. The bounds depend on the
consumed input length, without assuming that the encoding is canonical.
-/

namespace GeometricGaussianLHL

theorem decodeNatPrefix_size (bits : List Bool) (n : ℕ) (tail : List Bool)
    (h : decodeNatPrefix bits = some (n, tail)) : 2 * n.size + 1 + tail.length ≤ bits.length := by
  induction bits using List.twoStepInduction generalizing n tail with
  | nil => simp [decodeNatPrefix] at h
  | singleton b =>
    cases b with
    | false =>
      simp only [decodeNatPrefix, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      decide
    | true => simp [decodeNatPrefix] at h
  | cons_cons b c bits ih _ =>
    cases b with
    | false =>
      simp only [decodeNatPrefix, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      simp
      omega
    | true =>
      cases hd : decodeNatPrefix bits with
      | none => simp [decodeNatPrefix, hd] at h
      | some value =>
        rcases value with ⟨m, rest⟩
        have he : some (Nat.bit c m, rest) = some (n, tail) := by simpa [decodeNatPrefix, hd] using h
        rcases Prod.mk.inj (Option.some.inj he) with ⟨hm, ht⟩
        have hl := ih m rest hd
        have hs : (Nat.bit c m).size ≤ m.size + 1 := by
          by_cases hz : Nat.bit c m = 0
          · simp [hz]
          · rw [Nat.size_bit hz]
        rw [hm] at hs
        rw [ht] at hl
        simp only [List.length_cons]
        omega

theorem decodeIntPrefix_size (bits : List Bool) (z : ℤ) (tail : List Bool)
    (h : decodeIntPrefix bits = some (z, tail)) :
    2 * z.natAbs.size + 2 + tail.length ≤ bits.length := by
  cases bits with
  | nil => simp [decodeIntPrefix] at h
  | cons b bits =>
    cases hd : decodeNatPrefix bits with
    | none => simp [decodeIntPrefix, hd] at h
    | some value =>
      rcases value with ⟨n, rest⟩
      have he : some (if b then -(n : ℤ) else (n : ℤ), rest) = some (z, tail) := by
        simpa [decodeIntPrefix, hd] using h
      rcases Prod.mk.inj (Option.some.inj he) with ⟨hz, ht⟩
      have hl := decodeNatPrefix_size bits n rest hd
      have hmag : z.natAbs = n := by rw [← hz]; cases b <;> simp
      rw [ht] at hl
      simp only [hmag, List.length_cons]
      omega

end GeometricGaussianLHL

end BinaryPrefixSize

section RawRationalPrefix

/-!
## Raw rational pairs retained by the matrix-input program

Unlike the value codec, this specification retains the parsed numerator and
denominator before rational reduction. It rejects exactly the same scalar
inputs. Lists are read in source order with a fixed number of entries.
-/

namespace GeometricGaussianLHL

def decodeRawRatPrefix (bits : List Bool) : Option ((ℤ × ℕ) × List Bool) := do
  let (z, rest) ← decodeIntPrefix bits
  let (d, tail) ← decodeNatPrefix rest
  if d = 0 then none else return ((z, d), tail)

def decodeRawRatList : ℕ → List Bool → Option (List (ℤ × ℕ) × List Bool)
  | 0, bits => some ([], bits)
  | k + 1, bits => do
    let (pair, rest) ← decodeRawRatPrefix bits
    let (pairs, tail) ← decodeRawRatList k rest
    return (pair :: pairs, tail)

def rawDenominatorProduct (pairs : List (ℤ × ℕ)) : ℕ := (pairs.map Prod.snd).prod

theorem decodeRawRatPrefix_value (bits : List Bool) :
    decodeRatPrefix bits = (decodeRawRatPrefix bits).map
      (fun p => (Rat.divInt p.1.1 (p.1.2 : ℤ), p.2)) := by
  cases hi : decodeIntPrefix bits with
  | none => simp [decodeRatPrefix, decodeRawRatPrefix, hi]
  | some value =>
    rcases value with ⟨z, rest⟩
    cases hn : decodeNatPrefix rest with
    | none => simp [decodeRatPrefix, decodeRawRatPrefix, hi, hn]
    | some value =>
      rcases value with ⟨d, tail⟩
      by_cases hd : d = 0 <;> simp [decodeRatPrefix, decodeRawRatPrefix, hi, hn, hd]

theorem decodeRawRatPrefix_none (bits : List Bool) :
    decodeRawRatPrefix bits = none ↔ decodeRatPrefix bits = none := by
  rw [decodeRawRatPrefix_value]
  simp

theorem decodeRawRatPrefix_of_parses (bits rest tail : List Bool) (z : ℤ) (d : ℕ)
    (hi : decodeIntPrefix bits = some (z, rest)) (hn : decodeNatPrefix rest = some (d, tail))
    (hd : d ≠ 0) : decodeRawRatPrefix bits = some ((z, d), tail) := by
  simp [decodeRawRatPrefix, hi, hn, hd]

theorem decodeRawRatPrefix_encoded (q : ℚ) (tail : List Bool) :
    decodeRawRatPrefix (encodeRatBits q ++ tail) = some ((q.num, q.den), tail) := by
  simp [decodeRawRatPrefix, encodeRatBits, List.append_assoc,
    decodeIntBits_append, decodeNatBits_append, q.den_ne_zero]

theorem decodeRawRatList_length (k : ℕ) (bits : List Bool) (pairs : List (ℤ × ℕ)) (tail : List Bool)
    (h : decodeRawRatList k bits = some (pairs, tail)) : pairs.length = k := by
  induction k generalizing bits pairs tail with
  | zero => simp only [decodeRawRatList, Option.some.injEq, Prod.mk.injEq] at h; simp [← h.1]
  | succ k ih =>
    cases hd : decodeRawRatPrefix bits with
    | none => simp [decodeRawRatList, hd] at h
    | some value =>
      rcases value with ⟨pair, rest⟩
      cases ht : decodeRawRatList k rest with
      | none => simp [decodeRawRatList, hd, ht] at h
      | some value =>
        rcases value with ⟨ps, bs⟩
        have he : pair :: ps = pairs ∧ bs = tail := by simpa [decodeRawRatList, hd, ht] using h
        have hl := ih rest ps bs ht
        rw [← he.1, List.length_cons, hl]

theorem decodeRawRatList_encoded (qs : List ℚ) (tail : List Bool) :
    decodeRawRatList qs.length (qs.flatMap encodeRatBits ++ tail) =
      some (qs.map (fun q => (q.num, q.den)), tail) := by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
    simp only [List.length_cons, List.flatMap_cons, List.append_assoc, decodeRawRatList,
      decodeRawRatPrefix_encoded, List.map_cons]
    change (decodeRawRatList qs.length (qs.flatMap encodeRatBits ++ tail)).bind
      (fun p => some ((q.num, q.den) :: p.1, p.2)) = _
    rw [ih]
    rfl

theorem rawDenominatorProduct_nil : rawDenominatorProduct [] = 1 := rfl

theorem rawDenominatorProduct_cons (z : ℤ) (d : ℕ) (pairs : List (ℤ × ℕ)) :
    rawDenominatorProduct ((z, d) :: pairs) = d * rawDenominatorProduct pairs := rfl

end GeometricGaussianLHL

end RawRationalPrefix

section MatrixBinaryEncoding

/-!
## An actual binary codec for stored rational matrices

The dimension is followed by row-major rational entries. The public decoder
checks the dimension against the remaining word length before allocating or
recursing through vectors. Decoding an encoded matrix preserves every suffix.
-/

set_option backward.isDefEq.respectTransparency false

open scoped MatrixOrder Matrix.Norms.L2Operator

namespace GeometricGaussianLHL

theorem encodeVectorBits_length_sum {α : Type*} {n : ℕ}
    (enc : α → List Bool) (v : Vector α n) :
    (encodeVectorBits enc v).length = ∑ i : Fin n, (enc (v.get i)).length := by
  rw [encodeVectorBits_length]
  have hv : v.toList = List.ofFn (fun i => v.get i) := by
    rw [← Vector.toList_ofFn]
    congr 1
    ext i
    simp [Vector.get]
  rw [hv, List.map_ofFn, List.sum_ofFn]
  rfl

def encodeRationalMatrixData {n : ℕ} (D : RationalMatrixData n) : List Bool :=
  encodeNatBits n ++ encodeVectorBits (encodeVectorBits encodeRatBits) D

theorem encodeRationalMatrix_payload_length {n : ℕ} (D : RationalMatrixData n) :
    (encodeVectorBits (encodeVectorBits encodeRatBits) D).length =
      2 * rationalMatrixMagnitudeBits (rationalMatrixOfData D) + n * n := by
  simp only [encodeVectorBits_length_sum, encodeRatBits_length,
    rationalMatrixMagnitudeBits, rationalMatrixOfData]
  simp [Finset.sum_add_distrib, Finset.mul_sum]

theorem encodeRationalMatrixData_length {n : ℕ} (D : RationalMatrixData n) :
    (encodeRationalMatrixData D).length =
      2 * n.size + 1 + 2 * rationalMatrixMagnitudeBits (rationalMatrixOfData D) + n * n := by
  rw [encodeRationalMatrixData, List.length_append, encodeNatBits_length,
    encodeRationalMatrix_payload_length]
  omega

def decodeRationalMatrixDataPrefix (bs : List Bool) :
    Option ((Σ n : ℕ, RationalMatrixData n) × List Bool) := do
  let (n, rest) ← decodeNatPrefix bs
  if n ≤ rest.length then
    let (D, tail) ← decodeVectorPrefix (decodeVectorPrefix decodeRatPrefix n) n rest
    return (⟨n, D⟩, tail)
  else none

theorem decodeRationalMatrixData_append {n : ℕ} (D : RationalMatrixData n) (tail : List Bool) :
    decodeRationalMatrixDataPrefix (encodeRationalMatrixData D ++ tail) =
      some (⟨n, D⟩, tail) := by
  have hg : n ≤ (encodeVectorBits (encodeVectorBits encodeRatBits) D ++ tail).length := by
    rw [List.length_append, encodeRationalMatrix_payload_length]
    have hn : n ≤ n * n := Nat.le_mul_self n
    omega
  have hrow (v : Vector ℚ n) (bs : List Bool) :
      decodeVectorPrefix decodeRatPrefix n (encodeVectorBits encodeRatBits v ++ bs) =
        some (v, bs) := decodeVectorBits_append _ _ decodeRatBits_append v bs
  have hmatrix := decodeVectorBits_append (encodeVectorBits encodeRatBits)
    (decodeVectorPrefix decodeRatPrefix n) hrow D tail
  simp [decodeRationalMatrixDataPrefix, encodeRationalMatrixData, List.append_assoc,
    decodeNatBits_append, hmatrix]
  simpa only [List.length_append] using hg

theorem encodeRationalMatrixData_injective {n : ℕ} :
    Function.Injective (encodeRationalMatrixData (n := n)) := by
  intro D E h
  have hd := congrArg (fun bs => decodeRationalMatrixDataPrefix (bs ++ [])) h
  rw [decodeRationalMatrixData_append, decodeRationalMatrixData_append] at hd
  have hp := congrArg (fun q => q.1) (Option.some.inj hd)
  exact eq_of_heq (Sigma.mk.inj hp).2

end GeometricGaussianLHL

end MatrixBinaryEncoding

section RationalDenominatorData

/-!
## Clearing rational matrix denominators
-/

set_option backward.isDefEq.respectTransparency false

namespace GeometricGaussianLHL

def rationalMatrixCommonDenominator {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) : ℕ :=
  ∏ i : Fin n, ∏ j : Fin n, (A i j).den

theorem rationalMatrixCommonDenominator_pos {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) :
    0 < rationalMatrixCommonDenominator A := by
  apply Finset.prod_pos
  intro i _
  apply Finset.prod_pos
  intro j _
  exact (A i j).den_pos

theorem rationalMatrix_den_dvd_common {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ)
    (i j : Fin n) : (A i j).den ∣ rationalMatrixCommonDenominator A := by
  exact dvd_trans (Finset.dvd_prod_of_mem (fun k => (A i k).den) (Finset.mem_univ j))
    (Finset.dvd_prod_of_mem (fun k => ∏ l, (A k l).den) (Finset.mem_univ i))

def rationalMatrixCommonNumerators {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) :
    Matrix (Fin n) (Fin n) ℤ := fun i j =>
  (A i j).num * (rationalMatrixCommonDenominator A / (A i j).den : ℕ)

theorem rationalMatrix_common_reconstruct {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) :
    integerMatrixQuotient (rationalMatrixCommonDenominator A)
      (rationalMatrixCommonNumerators A) = A := by
  have ha : (rationalMatrixCommonDenominator A : ℚ) ≠ 0 := by
    exact_mod_cast (rationalMatrixCommonDenominator_pos A).ne'
  ext i j
  rw [integerMatrixQuotient_apply]
  simp only [rationalMatrixCommonNumerators, Int.cast_mul, Int.cast_natCast,
    Nat.cast_div_charZero (rationalMatrix_den_dvd_common A i j)]
  rw [mul_div_left_comm, mul_div_cancel_left₀ _ ha]
  exact (A i j).num_div_den

theorem rationalMatrix_entry_bits_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ)
    (i j : Fin n) : rationalMagnitudeBits (A i j) ≤ rationalMatrixMagnitudeBits A := by
  exact (Finset.single_le_sum (fun k _ => Nat.zero_le (rationalMagnitudeBits (A i k)))
    (Finset.mem_univ j)).trans
    (Finset.single_le_sum (fun k _ => Nat.zero_le (∑ l, rationalMagnitudeBits (A k l)))
      (Finset.mem_univ i))

theorem rationalMatrixCommonDenominator_le_pow {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    rationalMatrixCommonDenominator A ≤ 2 ^ rationalMatrixMagnitudeBits A := by
  unfold rationalMatrixCommonDenominator rationalMatrixMagnitudeBits
  rw [← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_le_prod'
  intro i _
  rw [← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_le_prod'
  intro j _
  exact (Nat.lt_size_self (A i j).den).le.trans
    (Nat.pow_le_pow_right (by omega) (by unfold rationalMagnitudeBits; omega))

theorem rationalMatrixCommonDenominator_size {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    (rationalMatrixCommonDenominator A).size ≤ rationalMatrixMagnitudeBits A + 1 := by
  apply Nat.size_le.mpr
  have h := rationalMatrixCommonDenominator_le_pow A
  rw [pow_succ]
  have hp : 0 < 2 ^ rationalMatrixMagnitudeBits A := by positivity
  omega

theorem rationalMatrixCommonNumerators_natAbs {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (i j : Fin n) :
    (rationalMatrixCommonNumerators A i j).natAbs ≤
      2 ^ (2 * rationalMatrixMagnitudeBits A) := by
  have hnum : (A i j).num.natAbs ≤ 2 ^ rationalMatrixMagnitudeBits A := by
    have hb := rationalMatrix_entry_bits_le A i j
    unfold rationalMagnitudeBits at hb
    exact (Nat.lt_size_self _).le.trans (Nat.pow_le_pow_right (by omega) (by omega))
  have hden : rationalMatrixCommonDenominator A / (A i j).den ≤
      2 ^ rationalMatrixMagnitudeBits A :=
    (Nat.div_le_self _ _).trans (rationalMatrixCommonDenominator_le_pow A)
  simp only [rationalMatrixCommonNumerators, Int.natAbs_mul, Int.natAbs_natCast]
  convert Nat.mul_le_mul hnum hden using 1
  rw [← pow_add]
  congr 1
  omega

theorem rationalMatrixCommonNumerators_size {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (i j : Fin n) :
    (rationalMatrixCommonNumerators A i j).natAbs.size ≤
      2 * rationalMatrixMagnitudeBits A + 1 := by
  apply Nat.size_le.mpr
  have h := rationalMatrixCommonNumerators_natAbs A i j
  rw [pow_succ]
  have hp : 0 < 2 ^ (2 * rationalMatrixMagnitudeBits A) := by positivity
  omega

end GeometricGaussianLHL

end RationalDenominatorData

section CommonNumeratorEncoding

/-!
## Exact quotients and space consumed by the rational matrix encoding

The common denominator is divisible by each reduced input denominator, so
the signed quotient equals the paper's integer numerator. The
consumed matrix prefix has enough space for two words per output entry.
-/

namespace GeometricGaussianLHL

theorem rationalMatrixCommonNumerators_eq_ediv {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ)
    (i j : Fin n) :
    ((A i j).num * (rationalMatrixCommonDenominator A : ℤ)) / ((A i j).den : ℤ) =
      rationalMatrixCommonNumerators A i j := by
  have hd : ((A i j).den : ℤ) ∣ (rationalMatrixCommonDenominator A : ℤ) := by
    exact_mod_cast rationalMatrix_den_dvd_common A i j
  rw [Int.mul_ediv_assoc _ hd]
  simp only [rationalMatrixCommonNumerators, Int.natCast_ediv]

theorem rationalMatrixMagnitudeBits_entries {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) :
    n * n ≤ rationalMatrixMagnitudeBits A := by
  have h : (∑ _i : Fin n, ∑ _j : Fin n, 1) ≤ rationalMatrixMagnitudeBits A := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    dsimp [rationalMagnitudeBits]
    omega
  simpa using h

theorem encodeRationalMatrixData_two_words {n : ℕ} (D : RationalMatrixData n) :
    2 * (n * n) ≤ (encodeRationalMatrixData D).length := by
  have h := rationalMatrixMagnitudeBits_entries (rationalMatrixOfData D)
  rw [encodeRationalMatrixData_length]
  omega

theorem commonNumeratorOutput_before_tail (base : ℕ) {n : ℕ} (D : RationalMatrixData n)
    (hb : 64 ≤ base) : 64 + 2 * (n * n) ≤ base + (encodeRationalMatrixData D).length := by
  have h := encodeRationalMatrixData_two_words D
  omega

end GeometricGaussianLHL

end CommonNumeratorEncoding

section MatrixInputEncoding

/-!
## Row-major entry lists for the actual rational matrix codec

These equalities connect the input loop's raw pairs and denominator product
to the existing matrix representation and common-denominator definitions.
-/

namespace GeometricGaussianLHL

def matrixInputEntryList {n : ℕ} (D : RationalMatrixData n) : List ℚ :=
  D.toList.flatMap (fun row => row.toList)

theorem matrixInput_vector_toList {α : Type*} {n : ℕ} (v : Vector α n) :
    v.toList = List.ofFn (fun i => v.get i) := by
  rw [← Vector.toList_ofFn]
  congr 1
  ext i
  simp [Vector.get]

theorem matrixInputEntryList_length {n : ℕ} (D : RationalMatrixData n) :
    (matrixInputEntryList D).length = n * n := by
  simp [matrixInputEntryList, List.length_flatMap]

theorem matrixInputEntryList_encode {n : ℕ} (D : RationalMatrixData n) :
    (matrixInputEntryList D).flatMap encodeRatBits =
      encodeVectorBits (encodeVectorBits encodeRatBits) D := by
  simp only [matrixInputEntryList, List.flatMap_assoc]
  rfl

theorem matrixInput_prod_flatMap {α : Type*} (xs : List α) (f : α → List ℕ) :
    (xs.flatMap f).prod = (xs.map (fun x => (f x).prod)).prod := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons, List.prod_append, List.map_cons, List.prod_cons, ih]

theorem matrixInputEntryList_product {n : ℕ} (D : RationalMatrixData n) :
    rawDenominatorProduct ((matrixInputEntryList D).map (fun q => (q.num, q.den))) =
      rationalMatrixCommonDenominator (rationalMatrixOfData D) := by
  simp [rawDenominatorProduct, matrixInputEntryList, matrixInput_vector_toList,
    List.map_flatMap, matrixInput_prod_flatMap, List.map_ofFn, List.prod_ofFn, Function.comp_def,
    rationalMatrixCommonDenominator, rationalMatrixOfData]

theorem decodeRawRatList_matrix {n : ℕ} (D : RationalMatrixData n) (tail : List Bool) :
    decodeRawRatList (n * n) (encodeVectorBits (encodeVectorBits encodeRatBits) D ++ tail) =
      some ((matrixInputEntryList D).map (fun q => (q.num, q.den)), tail) := by
  simpa only [matrixInputEntryList_length, matrixInputEntryList_encode] using
    decodeRawRatList_encoded (matrixInputEntryList D) tail

theorem matrixInputEntryList_ofFn {n : ℕ} (D : RationalMatrixData n) :
    matrixInputEntryList D = List.ofFn (fun k : Fin (n * n) =>
      rationalMatrixOfData D (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2) := by
  have hindex (i j : Fin n) (h : i.val * n + j.val < n * n) :
      (⟨i.val * n + j.val, h⟩ : Fin (n * n)) = finProdFinEquiv (i, j) := by
    ext
    simp [finProdFinEquiv, Nat.mul_comm, Nat.add_comm]
  rw [List.ofFn_mul]
  simp_rw [hindex, Equiv.symm_apply_apply]
  simp [matrixInputEntryList, matrixInput_vector_toList, List.flatMap_def, List.map_ofFn,
    rationalMatrixOfData, Function.comp_def]

theorem matrixInputEntryList_get {n : ℕ} (D : RationalMatrixData n) (i j : Fin n) :
    (matrixInputEntryList D)[(finProdFinEquiv (i, j)).val]'(by
      rw [matrixInputEntryList_length]; exact (finProdFinEquiv (i, j)).isLt) = rationalMatrixOfData D i j := by
  simp only [matrixInputEntryList_ofFn, List.getElem_ofFn]
  change rationalMatrixOfData D (finProdFinEquiv.symm (finProdFinEquiv (i, j))).1
    (finProdFinEquiv.symm (finProdFinEquiv (i, j))).2 = _
  simp only [Equiv.symm_apply_apply]

end GeometricGaussianLHL

end MatrixInputEncoding

section RationalDenominatorCast

/-!
## Casting common-denominator representations to real matrices
-/

open scoped MatrixOrder Matrix.Norms.L2Operator

namespace GeometricGaussianLHL

theorem rationalMatrix_real_common_denominator {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    A.map (fun q : ℚ => (q : ℝ)) =
      (rationalMatrixCommonDenominator A : ℝ)⁻¹ •
        (rationalMatrixCommonNumerators A).map (fun z : ℤ => (z : ℝ)) := by
  calc
    _ = (integerMatrixQuotient (rationalMatrixCommonDenominator A)
        (rationalMatrixCommonNumerators A)).map (fun q : ℚ => (q : ℝ)) :=
      congrArg (fun M => M.map (fun q : ℚ => (q : ℝ))) (rationalMatrix_common_reconstruct A).symm
    _ = _ := by
      ext i j
      simp [integerMatrixQuotient, integerMatrixCast, Matrix.map_apply, Matrix.smul_apply]

theorem rationalMatrix_real_det_common_denominator {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    (A.map (fun q : ℚ => (q : ℝ))).det =
      ((rationalMatrixCommonNumerators A).det : ℝ) /
        (rationalMatrixCommonDenominator A : ℝ) ^ n := by
  rw [rationalMatrix_real_common_denominator, Matrix.det_smul, ← Int.cast_det]
  simp only [Fintype.card_fin, inv_pow, div_eq_mul_inv, mul_comm]

end GeometricGaussianLHL

end RationalDenominatorCast

section RationalMagnitudeBound

/-!
## Entry magnitude from encoded input size
-/

open scoped MatrixOrder Matrix.Norms.L2Operator

namespace GeometricGaussianLHL

theorem rationalMatrix_real_entry_le_input_pow {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (i j : Fin n) :
    |((A i j : ℚ) : ℝ)| ≤ (2 : ℝ) ^ (2 * rationalMatrixMagnitudeBits A) := by
  have ha : (1 : ℝ) ≤ (rationalMatrixCommonDenominator A : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt (rationalMatrixCommonDenominator_pos A))
  have hN : |((rationalMatrixCommonNumerators A i j : ℤ) : ℝ)| ≤
      (2 : ℝ) ^ (2 * rationalMatrixMagnitudeBits A) := by
    have h : ((rationalMatrixCommonNumerators A i j).natAbs : ℝ) ≤
        (2 : ℝ) ^ (2 * rationalMatrixMagnitudeBits A) := by
      exact_mod_cast rationalMatrixCommonNumerators_natAbs A i j
    simpa only [Nat.cast_natAbs, Int.cast_abs] using h
  have he := congrFun (congrFun (rationalMatrix_real_common_denominator A) i) j
  calc
    |((A i j : ℚ) : ℝ)| = |((rationalMatrixCommonNumerators A i j : ℤ) : ℝ)| /
        (rationalMatrixCommonDenominator A : ℝ) := by
      rw [show ((A i j : ℚ) : ℝ) = _ from he]
      simp [Matrix.smul_apply, Matrix.map_apply, abs_mul, abs_inv, div_eq_mul_inv,
        mul_comm]
    _ ≤ (2 : ℝ) ^ (2 * rationalMatrixMagnitudeBits A) /
        (rationalMatrixCommonDenominator A : ℝ) :=
      div_le_div_of_nonneg_right hN (by positivity)
    _ ≤ _ := div_le_self (by positivity) ha

end GeometricGaussianLHL

end RationalMagnitudeBound

section RationalWidthMagnitude

/-!
## Width magnitude from encoded input size
-/

open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator

namespace GeometricGaussianLHL

theorem rationalWidth_abs_le_input_pow (w : ℚ) :
    |(w : ℝ)| ≤ (2 : ℝ) ^ (2 * rationalMagnitudeBits w) := by
  have h := rationalMatrix_real_entry_le_input_pow (fun _ _ : Fin 1 => w) 0 0
  simpa [rationalMatrixMagnitudeBits] using h

end GeometricGaussianLHL

end RationalWidthMagnitude
