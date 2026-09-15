import GeometricGaussianLHL.ArithmeticCost
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Localization.Rat
import Mathlib.RingTheory.Polynomial.Tower

/-!
# Finite algebraic inputs and interval refinement

This module collects the following proof sections, in dependency order.
- Finite algebraic input and rational interval refinement (`AlgebraicInput`).
- Bit growth of rational interval refinement (`AlgebraicInputSize`).
- Finite coefficient lists represent integer polynomials (`AlgebraicPolynomialEncoding`).
- Charged algebraic input refinement (`CostedAlgebraicInput`).
- Every real algebraic number has a valid finite encoding (`AlgebraicEncodingExistence`).
- Bit-sensitive cost of rational Horner evaluation (`RationalHornerCost`).
- Polynomial cost of rational bisection from a finite algebraic encoding (`AlgebraicInputCost`).
-/

section AlgebraicInput

/-!
## Finite algebraic input and rational interval refinement

An input is an integer coefficient list and two rational endpoints. Its
validity predicate identifies one real root in that interval with the
endpoint signs needed for bisection. The algorithm uses rational arithmetic
only; neither a real-number oracle nor the validity proof is executed.

This is the input-preparation algorithm and its accuracy proof.
`AlgebraicInputSize`, `RationalHornerCost` and `AlgebraicInputCost` provide
bit-growth and polynomial-cost proofs in the declared arithmetic cost model.
-/

namespace GeometricGaussianLHL

/-- Coefficients are ordered from constant term upwards. -/
def integerPolynomialHorner {R : Type*} [Ring R] (coefficients : List ℤ) (x : R) : R :=
  coefficients.foldr (fun (a : ℤ) (y : R) => (a : R) + x * y) 0

@[simp] theorem integerPolynomialHorner_nil {R : Type*} [Ring R] (x : R) :
    integerPolynomialHorner [] x = 0 := rfl

@[simp] theorem integerPolynomialHorner_cons {R : Type*} [Ring R]
    (a : ℤ) (coefficients : List ℤ) (x : R) :
    integerPolynomialHorner (a :: coefficients) x = (a : R) + x * integerPolynomialHorner coefficients x := rfl

theorem integerPolynomialHorner_rat_cast (coefficients : List ℤ) (x : ℚ) :
    ((integerPolynomialHorner coefficients x : ℚ) : ℝ) = integerPolynomialHorner coefficients (x : ℝ) := by
  induction coefficients with
  | nil => simp
  | cons a coefficients ih => simp only [integerPolynomialHorner_cons, Rat.cast_add, Rat.cast_mul, Rat.cast_intCast, ih]

theorem integerPolynomialHorner_continuous (coefficients : List ℤ) :
    Continuous (fun x : ℝ => integerPolynomialHorner coefficients x) := by
  induction coefficients with
  | nil => exact continuous_const
  | cons a coefficients ih => exact continuous_const.add (continuous_id.mul ih)

structure AlgebraicRealInput where
  coefficients : List ℤ
  lower : ℚ
  upper : ℚ
  deriving DecidableEq, Repr

namespace AlgebraicRealInput

/-- Semantic validity of finite data. This makes no computational promise. -/
structure ValidFor (I : AlgebraicRealInput) (x : ℝ) : Prop where
  nonzero : ∃ a ∈ I.coefficients, a ≠ 0
  lower_le : (I.lower : ℝ) ≤ x
  le_upper : x ≤ (I.upper : ℝ)
  root : integerPolynomialHorner I.coefficients x = 0
  lower_sign : integerPolynomialHorner I.coefficients (I.lower : ℝ) ≤ 0
  upper_sign : 0 ≤ integerPolynomialHorner I.coefficients (I.upper : ℝ)
  unique : ∀ y : ℝ, (I.lower : ℝ) ≤ y → y ≤ (I.upper : ℝ) →
    integerPolynomialHorner I.coefficients y = 0 → y = x

def midpoint (I : AlgebraicRealInput) : ℚ := (I.lower + I.upper) / 2

def bisect (I : AlgebraicRealInput) : AlgebraicRealInput :=
  if integerPolynomialHorner I.coefficients I.midpoint < 0 then
    { I with lower := I.midpoint }
  else
    { I with upper := I.midpoint }

def refine : ℕ → AlgebraicRealInput → AlgebraicRealInput
  | 0, I => I
  | n + 1, I => (AlgebraicRealInput.refine n I).bisect

theorem ValidFor.root_le_of_nonneg {I : AlgebraicRealInput} {x : ℝ}
    (hI : I.ValidFor x) {y : ℝ} (hl : (I.lower : ℝ) ≤ y) (hu : y ≤ (I.upper : ℝ))
    (hy : 0 ≤ integerPolynomialHorner I.coefficients y) : x ≤ y := by
  obtain ⟨z, hz, hzero⟩ := intermediate_value_Icc hl
    (integerPolynomialHorner_continuous I.coefficients).continuousOn ⟨hI.lower_sign, hy⟩
  have he := hI.unique z hz.1 (hz.2.trans hu) hzero
  exact he ▸ hz.2

theorem ValidFor.le_root_of_nonpos {I : AlgebraicRealInput} {x : ℝ}
    (hI : I.ValidFor x) {y : ℝ} (hl : (I.lower : ℝ) ≤ y) (hu : y ≤ (I.upper : ℝ))
    (hy : integerPolynomialHorner I.coefficients y ≤ 0) : y ≤ x := by
  obtain ⟨z, hz, hzero⟩ := intermediate_value_Icc hu
    (integerPolynomialHorner_continuous I.coefficients).continuousOn ⟨hy, hI.upper_sign⟩
  have he := hI.unique z (hl.trans hz.1) hz.2 hzero
  exact he ▸ hz.1

theorem ValidFor.bisect {I : AlgebraicRealInput} {x : ℝ} (hI : I.ValidFor x) :
    I.bisect.ValidFor x := by
  have hlu := hI.lower_le.trans hI.le_upper
  have hm : (I.midpoint : ℝ) = ((I.lower : ℝ) + (I.upper : ℝ)) / 2 := by
    simp [midpoint]
  have hl : (I.lower : ℝ) ≤ (I.midpoint : ℝ) := by rw [hm]; linarith
  have hu : (I.midpoint : ℝ) ≤ (I.upper : ℝ) := by rw [hm]; linarith
  unfold AlgebraicRealInput.bisect
  split_ifs with h
  · have hs : integerPolynomialHorner I.coefficients (I.midpoint : ℝ) ≤ 0 := by
      rw [← integerPolynomialHorner_rat_cast]
      exact_mod_cast h.le
    exact ⟨hI.nonzero, hI.le_root_of_nonpos hl hu hs, hI.le_upper, hI.root, hs, hI.upper_sign,
      fun y hy hy' hz => hI.unique y (hl.trans hy) hy' hz⟩
  · have hs : 0 ≤ integerPolynomialHorner I.coefficients (I.midpoint : ℝ) := by
      rw [← integerPolynomialHorner_rat_cast]
      exact_mod_cast le_of_not_gt h
    exact ⟨hI.nonzero, hI.lower_le, hI.root_le_of_nonneg hl hu hs, hI.root, hI.lower_sign, hs,
      fun y hy hy' hz => hI.unique y hy (hy'.trans hu) hz⟩

theorem ValidFor.refine {I : AlgebraicRealInput} {x : ℝ} (hI : I.ValidFor x) (n : ℕ) :
    (AlgebraicRealInput.refine n I).ValidFor x := by
  induction n with
  | zero => exact hI
  | succ n ih => exact ih.bisect

theorem bisect_width (I : AlgebraicRealInput) :
    I.bisect.upper - I.bisect.lower = (I.upper - I.lower) / 2 := by
  unfold bisect
  split_ifs <;> simp only [midpoint] <;> ring

theorem refine_width (I : AlgebraicRealInput) (n : ℕ) :
    (AlgebraicRealInput.refine n I).upper - (AlgebraicRealInput.refine n I).lower = (I.upper - I.lower) / (2 : ℚ) ^ n := by
  induction n with
  | zero => simp [refine]
  | succ n ih => rw [refine, bisect_width, ih, div_div, pow_succ]

theorem ValidFor.refine_error {I : AlgebraicRealInput} {x : ℝ} (hI : I.ValidFor x) (n : ℕ) :
    |((AlgebraicRealInput.refine n I).lower : ℝ) - x| ≤ ((I.upper : ℝ) - (I.lower : ℝ)) / (2 : ℝ) ^ n ∧
      |((AlgebraicRealInput.refine n I).upper : ℝ) - x| ≤ ((I.upper : ℝ) - (I.lower : ℝ)) / (2 : ℝ) ^ n := by
  have hn := hI.refine n
  have hw : ((AlgebraicRealInput.refine n I).upper : ℝ) - ((AlgebraicRealInput.refine n I).lower : ℝ) =
      ((I.upper : ℝ) - (I.lower : ℝ)) / (2 : ℝ) ^ n := by
    exact_mod_cast refine_width I n
  rw [← hw, abs_of_nonpos (sub_nonpos.mpr hn.lower_le),
    abs_of_nonneg (sub_nonneg.mpr hn.le_upper)]
  constructor <;> linarith [hn.lower_le, hn.le_upper]

/-- Overhead determined entirely by the two rational endpoint encodings. -/
def spanBits (I : AlgebraicRealInput) : ℕ :=
  2 * (rationalMagnitudeBits I.lower + rationalMagnitudeBits I.upper) + 1

theorem width_le_pow_spanBits (I : AlgebraicRealInput) :
    (I.upper : ℝ) - (I.lower : ℝ) ≤ (2 : ℝ) ^ I.spanBits := by
  have hl := rationalWidth_abs_le_input_pow I.lower
  have hu := rationalWidth_abs_le_input_pow I.upper
  have hl' : (2 : ℝ) ^ (2 * rationalMagnitudeBits I.lower) ≤
      (2 : ℝ) ^ (2 * (rationalMagnitudeBits I.lower + rationalMagnitudeBits I.upper)) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hu' : (2 : ℝ) ^ (2 * rationalMagnitudeBits I.upper) ≤
      (2 : ℝ) ^ (2 * (rationalMagnitudeBits I.lower + rationalMagnitudeBits I.upper)) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  dsimp only [spanBits]
  rw [pow_succ]
  linarith [le_abs_self (I.upper : ℝ), neg_le_abs (I.lower : ℝ)]

/-- The upper endpoint also preserves positivity for positive represented widths. -/
def approx (I : AlgebraicRealInput) (t : ℕ) : ℚ := (AlgebraicRealInput.refine (t + I.spanBits) I).upper

theorem ValidFor.approx_error {I : AlgebraicRealInput} {x : ℝ} (hI : I.ValidFor x) (t : ℕ) :
    |(I.approx t : ℝ) - x| ≤ 1 / (2 : ℝ) ^ t := by
  apply (hI.refine_error (t + I.spanBits)).2.trans
  calc
    _ ≤ (2 : ℝ) ^ I.spanBits / (2 : ℝ) ^ (t + I.spanBits) :=
      div_le_div_of_nonneg_right I.width_le_pow_spanBits (by positivity)
    _ = _ := by rw [pow_add]; field_simp

theorem ValidFor.le_approx {I : AlgebraicRealInput} {x : ℝ} (hI : I.ValidFor x) (t : ℕ) :
    x ≤ (I.approx t : ℝ) := (hI.refine (t + I.spanBits)).le_upper

theorem ValidFor.approx_pos {I : AlgebraicRealInput} {x : ℝ} (hI : I.ValidFor x)
    (hx : 0 < x) (t : ℕ) : 0 < I.approx t := by
  exact_mod_cast hx.trans_le (hI.le_approx t)

end AlgebraicRealInput
end GeometricGaussianLHL

end AlgebraicInput

section AlgebraicInputSize

/-!
## Bit growth of rational interval refinement

All endpoints after `n` bisections have denominator dividing the original
common denominator times `2^n`. Their magnitudes stay within the original
endpoint bound. Thus reduced numerator/denominator lengths grow linearly,
without multiplying the two current denominators at every iteration.
-/
namespace GeometricGaussianLHL

theorem rational_den_le_pow_bits (x : ℚ) : x.den ≤ 2 ^ rationalMagnitudeBits x := by
  apply (Nat.size_le.mp (show x.den.size ≤ rationalMagnitudeBits x by
    unfold rationalMagnitudeBits; omega)).le

theorem rational_abs_le_pow_bits (x : ℚ) : |x| ≤ (2 : ℚ) ^ rationalMagnitudeBits x := by
  have hn : x.num.natAbs ≤ 2 ^ rationalMagnitudeBits x :=
    (Nat.size_le.mp (show x.num.natAbs.size ≤ rationalMagnitudeBits x by
      unfold rationalMagnitudeBits; omega)).le
  have hd : (1 : ℚ) ≤ x.den := by exact_mod_cast x.den_pos
  have hdpos : (0 : ℚ) < x.den := by exact_mod_cast x.den_pos
  calc
    |x| = |(x.num : ℚ) / x.den| := congrArg abs x.num_div_den.symm
    _ = |(x.num : ℚ)| / x.den := by rw [abs_div, abs_of_pos hdpos]
    _ ≤ |(x.num : ℚ)| := div_le_self (abs_nonneg _) hd
    _ ≤ _ := by simpa only [Nat.cast_natAbs, Int.cast_abs, Nat.cast_pow, Nat.cast_ofNat]
                  using (show (x.num.natAbs : ℚ) ≤ (2 : ℚ) ^ rationalMagnitudeBits x by exact_mod_cast hn)

theorem rational_bits_le_of_den_abs (x : ℚ) (D H : ℕ)
    (hd : x.den ≤ 2 ^ D) (hx : |x| ≤ (2 : ℚ) ^ H) :
    rationalMagnitudeBits x ≤ H + 2 * D + 3 := by
  have hdpos : (0 : ℚ) < x.den := by exact_mod_cast x.den_pos
  have he : (x.num : ℚ) = x * (x.den : ℚ) := by
    exact ((eq_div_iff (by positivity : (x.den : ℚ) ≠ 0)).mp x.num_div_den.symm).symm
  have hn : x.num.natAbs ≤ 2 ^ (H + D) := by
    have h : (x.num.natAbs : ℚ) ≤ (2 : ℚ) ^ (H + D) := by
      calc
        _ = |(x.num : ℚ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
        _ = |x| * (x.den : ℚ) := by rw [he, abs_mul, abs_of_pos hdpos]
        _ ≤ (2 : ℚ) ^ H * (2 : ℚ) ^ D :=
          mul_le_mul hx (by exact_mod_cast hd) (by positivity) (by positivity)
        _ = _ := by rw [pow_add]
    exact_mod_cast h
  have hns : x.num.natAbs.size ≤ H + D + 1 :=
    Nat.size_le.mpr (hn.trans_lt (Nat.pow_lt_pow_right (by omega) (by omega)))
  have hds : x.den.size ≤ D + 1 :=
    Nat.size_le.mpr (hd.trans_lt (Nat.pow_lt_pow_right (by omega) (by omega)))
  unfold rationalMagnitudeBits
  omega

theorem rational_add_den_dvd_common (x y : ℚ) {D : ℕ}
    (hx : x.den ∣ D) (hy : y.den ∣ D) : (x + y).den ∣ D :=
  (Rat.add_den_dvd_lcm x y).trans (Nat.lcm_dvd hx hy)

theorem rational_half_den_dvd (x : ℚ) : (x / 2).den ∣ x.den * 2 := by
  have h := Rat.mul_den_dvd x (1 / 2)
  norm_num at h
  simpa only [div_eq_mul_inv, one_mul] using h

namespace AlgebraicRealInput

def endpointBits (I : AlgebraicRealInput) : ℕ :=
  rationalMagnitudeBits I.lower + rationalMagnitudeBits I.upper

def commonDenominator (I : AlgebraicRealInput) : ℕ := I.lower.den * I.upper.den

theorem commonDenominator_pos (I : AlgebraicRealInput) : 0 < I.commonDenominator :=
  Nat.mul_pos I.lower.den_pos I.upper.den_pos

theorem commonDenominator_le (I : AlgebraicRealInput) :
    I.commonDenominator ≤ 2 ^ I.endpointBits := by
  simpa only [commonDenominator, endpointBits, pow_add] using
    Nat.mul_le_mul (rational_den_le_pow_bits I.lower) (rational_den_le_pow_bits I.upper)

theorem midpoint_den_dvd (I : AlgebraicRealInput) {D : ℕ}
    (hl : I.lower.den ∣ D) (hu : I.upper.den ∣ D) : I.midpoint.den ∣ D * 2 :=
  (rational_half_den_dvd _).trans (Nat.mul_dvd_mul (rational_add_den_dvd_common _ _ hl hu) (dvd_refl 2))

theorem bisect_den_dvd (I : AlgebraicRealInput) {D : ℕ}
    (hl : I.lower.den ∣ D) (hu : I.upper.den ∣ D) :
    I.bisect.lower.den ∣ D * 2 ∧ I.bisect.upper.den ∣ D * 2 := by
  have hm := I.midpoint_den_dvd hl hu
  have hl' := hl.trans (Nat.dvd_mul_right D 2)
  have hu' := hu.trans (Nat.dvd_mul_right D 2)
  unfold bisect
  split_ifs <;> exact ⟨by assumption, by assumption⟩

theorem refine_den_dvd (I : AlgebraicRealInput) (n : ℕ) :
    (refine n I).lower.den ∣ I.commonDenominator * 2 ^ n ∧
    (refine n I).upper.den ∣ I.commonDenominator * 2 ^ n := by
  induction n with
  | zero => simp only [refine, pow_zero, mul_one, commonDenominator]
            exact ⟨Nat.dvd_mul_right _ _, Nat.dvd_mul_left _ _⟩
  | succ n ih => simpa only [refine, pow_succ, Nat.mul_assoc] using
      (refine n I).bisect_den_dvd ih.1 ih.2

theorem midpoint_abs_le (I : AlgebraicRealInput) {H : ℚ}
    (hl : |I.lower| ≤ H) (hu : |I.upper| ≤ H) : |I.midpoint| ≤ H := by
  rw [midpoint, abs_div, abs_of_pos (by norm_num : (0 : ℚ) < 2)]
  exact (div_le_iff₀ (by norm_num)).mpr (by linarith [abs_add_le I.lower I.upper])

theorem bisect_abs_le (I : AlgebraicRealInput) {H : ℚ}
    (hl : |I.lower| ≤ H) (hu : |I.upper| ≤ H) :
    |I.bisect.lower| ≤ H ∧ |I.bisect.upper| ≤ H := by
  have hm := I.midpoint_abs_le hl hu
  unfold bisect
  split_ifs <;> exact ⟨by assumption, by assumption⟩

theorem refine_abs_le (I : AlgebraicRealInput) (n : ℕ) :
    |(refine n I).lower| ≤ (2 : ℚ) ^ I.endpointBits ∧
    |(refine n I).upper| ≤ (2 : ℚ) ^ I.endpointBits := by
  induction n with
  | zero =>
    constructor
    · exact (rational_abs_le_pow_bits I.lower).trans
        (pow_le_pow_right₀ (by norm_num) (by unfold endpointBits; omega))
    · exact (rational_abs_le_pow_bits I.upper).trans
        (pow_le_pow_right₀ (by norm_num) (by unfold endpointBits; omega))
  | succ n ih => exact (refine n I).bisect_abs_le ih.1 ih.2

theorem refine_den_le (I : AlgebraicRealInput) (n : ℕ) :
    (refine n I).lower.den ≤ 2 ^ (I.endpointBits + n) ∧
    (refine n I).upper.den ≤ 2 ^ (I.endpointBits + n) := by
  have hpos : 0 < I.commonDenominator * 2 ^ n := Nat.mul_pos I.commonDenominator_pos (by positivity)
  have hbound : I.commonDenominator * 2 ^ n ≤ 2 ^ (I.endpointBits + n) := by
    rw [pow_add]
    exact Nat.mul_le_mul_right _ I.commonDenominator_le
  exact ⟨(Nat.le_of_dvd hpos (I.refine_den_dvd n).1).trans hbound,
    (Nat.le_of_dvd hpos (I.refine_den_dvd n).2).trans hbound⟩

theorem refine_bits (I : AlgebraicRealInput) (n : ℕ) :
    rationalMagnitudeBits (refine n I).lower ≤ 3 * I.endpointBits + 2 * n + 3 ∧
    rationalMagnitudeBits (refine n I).upper ≤ 3 * I.endpointBits + 2 * n + 3 := by
  have hl := rational_bits_le_of_den_abs _ _ _ (I.refine_den_le n).1 (I.refine_abs_le n).1
  have hu := rational_bits_le_of_den_abs _ _ _ (I.refine_den_le n).2 (I.refine_abs_le n).2
  constructor <;> omega

@[simp] theorem refine_coefficients (I : AlgebraicRealInput) (n : ℕ) :
    (refine n I).coefficients = I.coefficients := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change ((refine n I).bisect).coefficients = I.coefficients
    unfold bisect
    split_ifs <;> exact ih

end AlgebraicRealInput
end GeometricGaussianLHL

end AlgebraicInputSize

section AlgebraicPolynomialEncoding

/-!
## Finite coefficient lists represent integer polynomials

The bisection evaluator uses coefficients in increasing degree order. These
lemmas identify its finite list evaluation with Mathlib polynomial evaluation.
-/
namespace GeometricGaussianLHL

open Polynomial

theorem integerPolynomialHorner_ofFn {R : Type*} [CommRing R] (n : ℕ)
    (a : Fin n → ℤ) (x : R) :
    integerPolynomialHorner (List.ofFn a) x = ∑ i, (a i : R) * x ^ i.val := by
  induction n with
  | zero => simp [List.ofFn_zero]
  | succ n ih =>
    rw [List.ofFn_succ, integerPolynomialHorner_cons, ih, Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

def integerPolynomialCoefficients (p : Polynomial ℤ) : List ℤ :=
  List.ofFn (fun i : Fin (p.natDegree + 1) => p.coeff i.val)

theorem integerPolynomialCoefficients_eval (p : Polynomial ℤ) {R : Type*} [CommRing R] (x : R) :
    integerPolynomialHorner (integerPolynomialCoefficients p) x = aeval x p := by
  rw [integerPolynomialCoefficients, integerPolynomialHorner_ofFn, Polynomial.aeval_def,
    Polynomial.eval₂_eq_sum_range]
  exact Fin.sum_univ_eq_sum_range (fun k => (p.coeff k : R) * x ^ k) (p.natDegree + 1)

theorem integerPolynomialCoefficients_nonzero {p : Polynomial ℤ} (hp : p ≠ 0) :
    ∃ a ∈ integerPolynomialCoefficients p, a ≠ 0 := by
  refine ⟨p.leadingCoeff, ?_, Polynomial.leadingCoeff_ne_zero.mpr hp⟩
  apply List.mem_ofFn.mpr
  exact ⟨⟨p.natDegree, Nat.lt_succ_self _⟩, rfl⟩

end GeometricGaussianLHL

end AlgebraicPolynomialEncoding

section CostedAlgebraicInput

/-!
## Charged algebraic input refinement
-/
namespace GeometricGaussianLHL

def costedRatHorner : List ℤ → ℚ → Costed ℚ
  | [], _ => Costed.pure 0
  | a :: coefficients, x =>
    (costedRatHorner coefficients x).bind fun y =>
      (costedRatMul x y).bind fun xy =>
        (Costed.charge (a.natAbs.size + 1) (a : ℚ)).bind fun aq => costedRatAdd aq xy

@[simp] theorem costedRatHorner_value (coefficients : List ℤ) (x : ℚ) :
    (costedRatHorner coefficients x).value = integerPolynomialHorner coefficients x := by
  induction coefficients with
  | nil => rfl
  | cons a coefficients ih =>
    simp only [costedRatHorner, Costed.bind_value, costedRatMul, Costed.charge, costedRatAdd,
      integerPolynomialHorner_cons, ih]

def costedAlgebraicBisect (I : AlgebraicRealInput) : Costed AlgebraicRealInput :=
  (costedRatAdd I.lower I.upper).bind fun s =>
    (costedRatDiv s 2).bind fun mid =>
      (costedRatHorner I.coefficients mid).bind fun y =>
        Costed.charge (rationalMagnitudeBits y + 1)
          (if y < 0 then { I with lower := mid } else { I with upper := mid })

@[simp] theorem costedAlgebraicBisect_value (I : AlgebraicRealInput) :
    (costedAlgebraicBisect I).value = I.bisect := by
  simp only [costedAlgebraicBisect, Costed.bind_value, costedRatAdd, costedRatDiv,
    costedRatHorner_value, Costed.charge, AlgebraicRealInput.bisect, AlgebraicRealInput.midpoint]
  rfl

def costedAlgebraicRefine : ℕ → AlgebraicRealInput → Costed AlgebraicRealInput
  | 0, I => Costed.pure I
  | n + 1, I => (costedAlgebraicRefine n I).bind costedAlgebraicBisect

@[simp] theorem costedAlgebraicRefine_value (n : ℕ) (I : AlgebraicRealInput) :
    (costedAlgebraicRefine n I).value = AlgebraicRealInput.refine n I := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [costedAlgebraicRefine, Costed.bind_value,
      costedAlgebraicBisect_value, ih, AlgebraicRealInput.refine]

/-- The recurrence accumulates charges at the states actually produced. -/
theorem costedAlgebraicRefine_steps (n : ℕ) (I : AlgebraicRealInput) :
    (costedAlgebraicRefine (n + 1) I).steps = (costedAlgebraicRefine n I).steps +
      (costedAlgebraicBisect (AlgebraicRealInput.refine n I)).steps := by
  simp only [costedAlgebraicRefine, Costed.bind_steps, costedAlgebraicRefine_value]

theorem costedAlgebraicRefine_error (n : ℕ) (I : AlgebraicRealInput) {x : ℝ}
    (hI : I.ValidFor x) :
    |(((costedAlgebraicRefine (n + I.spanBits) I).value.upper : ℚ) : ℝ) - x| ≤
      1 / (2 : ℝ) ^ n := by
  simpa only [costedAlgebraicRefine_value, AlgebraicRealInput.approx] using hI.approx_error n

end GeometricGaussianLHL

end CostedAlgebraicInput

section AlgebraicEncodingExistence

/-!
## Every real algebraic number has a valid finite encoding

A separable minimal polynomial gives a simple root. Clearing denominators and
choosing its sign give an integer polynomial with positive derivative at that
root. Rational endpoints in a neighborhood of positive derivative provide the
oriented isolating interval required by the actual bisection algorithm.
-/
open Polynomial Set
open scoped Topology
namespace GeometricGaussianLHL

theorem exists_integerPolynomial_positive_simple_root {x : ℝ} (hx : IsAlgebraic ℚ x) :
    ∃ p : Polynomial ℤ, p ≠ 0 ∧ aeval x p = 0 ∧ 0 < aeval x p.derivative := by
  let q := minpoly ℚ x
  have hq : aeval x q = 0 := minpoly.aeval ℚ x
  have hqd : aeval x q.derivative ≠ 0 := (minpoly.irreducible hx.isIntegral).separable.aeval_derivative_ne_zero hq
  let p := IsLocalization.integerNormalization (nonZeroDivisors ℤ) q
  obtain ⟨c, hc, hmap⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) q
  change p.map (algebraMap ℤ ℚ) = c • q at hmap
  have hc0 : (c : ℝ) ≠ 0 := Int.cast_ne_zero.mpr (mem_nonZeroDivisors_iff_ne_zero.mp hc)
  have hp : aeval x p = 0 := by
    rw [← Polynomial.aeval_map_algebraMap ℚ x p, hmap, map_zsmul, hq, smul_zero]
  have hdmap : p.derivative.map (algebraMap ℤ ℚ) = c • q.derivative := by
    simpa only [Polynomial.derivative_map, Polynomial.derivative_smul] using congrArg Polynomial.derivative hmap
  have hpd : aeval x p.derivative ≠ 0 := by
    rw [← Polynomial.aeval_map_algebraMap ℚ x p.derivative, hdmap, map_zsmul, zsmul_eq_mul]
    exact mul_ne_zero hc0 hqd
  have hp0 : p ≠ 0 := by
    intro he
    simp [he] at hpd
  rcases lt_or_gt_of_ne hpd with hn | hn
  · refine ⟨-p, neg_ne_zero.mpr hp0, ?_, ?_⟩
    · simp [hp]
    · simpa only [Polynomial.derivative_neg, map_neg, neg_pos] using hn
  · exact ⟨p, hp0, hp, hn⟩

theorem integerPolynomial_rational_isolating_interval (p : Polynomial ℤ) (x : ℝ)
    (hx : aeval x p = 0) (hd : 0 < aeval x p.derivative) :
    ∃ l u : ℚ, (l : ℝ) < x ∧ x < (u : ℝ) ∧
      aeval (l : ℝ) p ≤ 0 ∧ 0 ≤ aeval (u : ℝ) p ∧
      ∀ y : ℝ, (l : ℝ) ≤ y → y ≤ (u : ℝ) → aeval y p = 0 → y = x := by
  have ho : IsOpen {y : ℝ | 0 < aeval y p.derivative} :=
    isOpen_lt continuous_const p.derivative.continuous_aeval
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp ho x hd
  obtain ⟨l, hl, hlx⟩ := exists_rat_btwn (show x - ε < x by linarith)
  obtain ⟨u, hxu, hu⟩ := exists_rat_btwn (show x < x + ε by linarith)
  have hlu : (l : ℝ) ≤ u := hlx.le.trans hxu.le
  have hxI : x ∈ Icc (l : ℝ) u := ⟨hlx.le, hxu.le⟩
  have hpos (y : ℝ) (hy : y ∈ Icc (l : ℝ) u) : 0 < aeval y p.derivative := by
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hy.1, hy.2]
  have hm : StrictMonoOn (fun y : ℝ => aeval y p) (Icc (l : ℝ) u) :=
    strictMonoOn_of_deriv_pos (convex_Icc _ _) p.continuous_aeval.continuousOn (by
      intro y hy
      rw [p.deriv_aeval]
      exact hpos y (interior_subset hy))
  refine ⟨l, u, hlx, hxu, ?_, ?_, ?_⟩
  · have h := hm (left_mem_Icc.mpr hlu) hxI hlx
    simpa only [hx] using h.le
  · have h := hm hxI (right_mem_Icc.mpr hlu) hxu
    simpa only [hx] using h.le
  · intro y hly hyu hy
    exact hm.injOn ⟨hly, hyu⟩ hxI (hy.trans hx.symm)

theorem AlgebraicRealInput.exists_valid {x : ℝ} (hx : IsAlgebraic ℚ x) :
    ∃ I : AlgebraicRealInput, I.ValidFor x := by
  obtain ⟨p, hp, hx, hd⟩ := exists_integerPolynomial_positive_simple_root hx
  obtain ⟨l, u, hl, hu, hls, hus, hunique⟩ := integerPolynomial_rational_isolating_interval p x hx hd
  refine ⟨⟨integerPolynomialCoefficients p, l, u⟩, ?_⟩
  exact {
    nonzero := integerPolynomialCoefficients_nonzero hp
    lower_le := hl.le
    le_upper := hu.le
    root := by simpa only [integerPolynomialCoefficients_eval] using hx
    lower_sign := by simpa only [integerPolynomialCoefficients_eval] using hls
    upper_sign := by simpa only [integerPolynomialCoefficients_eval] using hus
    unique := by
      intro y hly hyu hy
      exact hunique y hly hyu (by simpa only [integerPolynomialCoefficients_eval] using hy) }

end GeometricGaussianLHL

end AlgebraicEncodingExistence

section RationalHornerCost

/-!
## Bit-sensitive cost of rational Horner evaluation

Denominators divide a power of the input denominator, while absolute values
have a degree-linear exponent. These facts bound the actual reduced rational
operands at every multiplication and addition in the instrumented algorithm.
-/
namespace GeometricGaussianLHL

theorem intCast_abs_le_pow_size_bound (a : ℤ) (C : ℕ) (ha : a.natAbs.size ≤ C) :
    |(a : ℚ)| ≤ (2 : ℚ) ^ C := by
  have h : a.natAbs ≤ 2 ^ C := (Nat.size_le.mp ha).le
  have h' : (a.natAbs : ℚ) ≤ (2 : ℚ) ^ C := by exact_mod_cast h
  simpa only [Nat.cast_natAbs, Int.cast_abs] using h'

theorem intCast_rational_bits (a : ℤ) : rationalMagnitudeBits (a : ℚ) = a.natAbs.size + 2 := by
  simp [rationalMagnitudeBits]

theorem integerPolynomialHorner_den_dvd (coefficients : List ℤ) (x : ℚ) :
    (integerPolynomialHorner coefficients x).den ∣ x.den ^ coefficients.length := by
  induction coefficients with
  | nil => simp
  | cons a coefficients ih =>
    rw [integerPolynomialHorner_cons, Rat.intCast_add_den]
    simpa only [List.length_cons, pow_succ, Nat.mul_comm] using
      (Rat.mul_den_dvd x (integerPolynomialHorner coefficients x)).trans
        (Nat.mul_dvd_mul (dvd_refl x.den) ih)

theorem integerPolynomialHorner_abs_le (coefficients : List ℤ) (x : ℚ) (C L : ℕ)
    (hc : ∀ a ∈ coefficients, a.natAbs.size ≤ C) (hx : |x| ≤ (2 : ℚ) ^ L) :
    |integerPolynomialHorner coefficients x| ≤ (2 : ℚ) ^ (coefficients.length * (C + L + 1)) := by
  induction coefficients with
  | nil => simp
  | cons a coefficients ih =>
    have ha := intCast_abs_le_pow_size_bound a C (hc a (by simp))
    have hy := ih (fun b hb => hc b (by simp [hb]))
    have hprod : |x * integerPolynomialHorner coefficients x| ≤
        (2 : ℚ) ^ (L + coefficients.length * (C + L + 1)) := by
      rw [abs_mul, pow_add]
      exact mul_le_mul hx hy (abs_nonneg _) (by positivity)
    let e := C + L + coefficients.length * (C + L + 1)
    have h₁ : (2 : ℚ) ^ C ≤ 2 ^ e := pow_le_pow_right₀ (by norm_num) (by dsimp [e]; omega)
    have h₂ : (2 : ℚ) ^ (L + coefficients.length * (C + L + 1)) ≤ 2 ^ e :=
      pow_le_pow_right₀ (by norm_num) (by dsimp [e]; omega)
    rw [integerPolynomialHorner_cons]
    calc
      _ ≤ |(a : ℚ)| + |x * integerPolynomialHorner coefficients x| := abs_add_le _ _
      _ ≤ (2 : ℚ) ^ e + 2 ^ e := add_le_add (ha.trans h₁) (hprod.trans h₂)
      _ = _ := by
        rw [show (a :: coefficients).length * (C + L + 1) = e + 1 by
          dsimp [e]; ring, pow_succ]
        ring

theorem integerPolynomialHorner_den_le (coefficients : List ℤ) (x : ℚ) (L : ℕ)
    (hx : x.den ≤ 2 ^ L) :
    (integerPolynomialHorner coefficients x).den ≤ 2 ^ (L * coefficients.length) := by
  apply (Nat.le_of_dvd (by positivity) (integerPolynomialHorner_den_dvd coefficients x)).trans
  simpa only [pow_mul] using Nat.pow_le_pow_left hx coefficients.length

theorem integerPolynomialHorner_bits (coefficients : List ℤ) (x : ℚ) (C L : ℕ)
    (hc : ∀ a ∈ coefficients, a.natAbs.size ≤ C) (hx : rationalMagnitudeBits x ≤ L) :
    rationalMagnitudeBits (integerPolynomialHorner coefficients x) ≤
      coefficients.length * (C + 3 * L + 1) + 3 := by
  have hd : x.den ≤ 2 ^ L := (rational_den_le_pow_bits x).trans
    (Nat.pow_le_pow_right (by omega) hx)
  have ha : |x| ≤ (2 : ℚ) ^ L := (rational_abs_le_pow_bits x).trans
    (pow_le_pow_right₀ (by norm_num) hx)
  have h := rational_bits_le_of_den_abs _ _ _
    (integerPolynomialHorner_den_le coefficients x L hd)
    (integerPolynomialHorner_abs_le coefficients x C L hc ha)
  convert h using 1; ring

theorem integerPolynomialHorner_product_bits (coefficients : List ℤ) (x : ℚ) (C L : ℕ)
    (hc : ∀ a ∈ coefficients, a.natAbs.size ≤ C) (hx : rationalMagnitudeBits x ≤ L) :
    rationalMagnitudeBits (x * integerPolynomialHorner coefficients x) ≤
      (coefficients.length + 1) * (C + 3 * L + 1) + 3 := by
  have hd : x.den ≤ 2 ^ L := (rational_den_le_pow_bits x).trans
    (Nat.pow_le_pow_right (by omega) hx)
  have ha : |x| ≤ (2 : ℚ) ^ L := (rational_abs_le_pow_bits x).trans
    (pow_le_pow_right₀ (by norm_num) hx)
  have hyden := integerPolynomialHorner_den_le coefficients x L hd
  have hyd : (x * integerPolynomialHorner coefficients x).den ≤
      2 ^ (L + L * coefficients.length) := by
    apply (Nat.le_of_dvd (Nat.mul_pos x.den_pos (Rat.den_pos _)) (Rat.mul_den_dvd _ _)).trans
    simpa only [pow_add] using Nat.mul_le_mul hd hyden
  have hya : |x * integerPolynomialHorner coefficients x| ≤
      (2 : ℚ) ^ (L + coefficients.length * (C + L + 1)) := by
    rw [abs_mul, pow_add]
    exact mul_le_mul ha (integerPolynomialHorner_abs_le coefficients x C L hc ha)
      (abs_nonneg _) (by positivity)
  have h := rational_bits_le_of_den_abs _ _ _ hyd hya
  apply h.trans
  nlinarith

/-- Uniform operand bound for a Horner evaluation of the given length. -/
def hornerOperandBudget (n C L : ℕ) : ℕ := (n + 1) * (C + 3 * L + 3)

def hornerStepBudget (n C L : ℕ) : ℕ :=
  2 * (2 * hornerOperandBudget n C L + 1) ^ 3 + hornerOperandBudget n C L

theorem costedRatHorner_steps_le (coefficients : List ℤ) (x : ℚ) (C L : ℕ)
    (hc : ∀ a ∈ coefficients, a.natAbs.size ≤ C) (hx : rationalMagnitudeBits x ≤ L) :
    (costedRatHorner coefficients x).steps ≤ coefficients.length * hornerStepBudget coefficients.length C L := by
  induction coefficients with
  | nil => simp [costedRatHorner, Costed.pure]
  | cons a coefficients ih =>
    have hcs : ∀ b ∈ coefficients, b.natAbs.size ≤ C := fun b hb => hc b (by simp [hb])
    have ha : a.natAbs.size ≤ C := hc a (by simp)
    let J := hornerOperandBudget (coefficients.length + 1) C L
    have hJ : C + 3 * L + 3 ≤ J := by dsimp [J, hornerOperandBudget]; nlinarith
    have hxJ : rationalMagnitudeBits x ≤ J := hx.trans (by omega)
    have hyJ : rationalMagnitudeBits (integerPolynomialHorner coefficients x) ≤ J := by
      apply (integerPolynomialHorner_bits coefficients x C L hcs hx).trans
      dsimp [J, hornerOperandBudget]
      nlinarith
    have hxyJ : rationalMagnitudeBits (x * integerPolynomialHorner coefficients x) ≤ J := by
      apply (integerPolynomialHorner_product_bits coefficients x C L hcs hx).trans
      dsimp [J, hornerOperandBudget]
      nlinarith
    have haJ : rationalMagnitudeBits (a : ℚ) ≤ J := by rw [intCast_rational_bits]; omega
    have hmul := rationalArithmeticCost_le _ _ hxJ hyJ
    have hadd := rationalArithmeticCost_le _ _ haJ hxyJ
    have hmono : hornerStepBudget coefficients.length C L ≤
        hornerStepBudget (coefficients.length + 1) C L := by
      unfold hornerStepBudget hornerOperandBudget
      gcongr <;> omega
    have hprev := (ih hcs).trans (Nat.mul_le_mul_left coefficients.length hmono)
    simp only [costedRatHorner, Costed.bind_steps, costedRatMul,
      Costed.charge, costedRatAdd, costedRatHorner_value, List.length_cons]
    change (costedRatHorner coefficients x).steps +
      (rationalArithmeticCost x (integerPolynomialHorner coefficients x) +
        (a.natAbs.size + 1 + rationalArithmeticCost (a : ℚ) (x * integerPolynomialHorner coefficients x))) ≤ _
    have hcast : a.natAbs.size + 1 ≤ J := by omega
    apply (Nat.add_le_add hprev (Nat.add_le_add hmul (Nat.add_le_add hcast hadd))).trans_eq
    dsimp only [hornerStepBudget, J]
    ring

end GeometricGaussianLHL

end RationalHornerCost

section AlgebraicInputCost

/-!
## Polynomial cost of rational bisection from a finite algebraic encoding

The algorithm charges rational Horner arithmetic at each actual midpoint.
The common-denominator invariant bounds endpoint sizes throughout the loop.
Input scanning, precision setup and rational output serialization are charged
separately in the same declared arithmetic cost model.
-/
namespace GeometricGaussianLHL

theorem rational_add_bits_le (x y : ℚ) (L : ℕ)
    (hx : rationalMagnitudeBits x ≤ L) (hy : rationalMagnitudeBits y ≤ L) :
    rationalMagnitudeBits (x + y) ≤ 5 * L + 4 := by
  have hxden : x.den ≤ 2 ^ L := (rational_den_le_pow_bits x).trans (Nat.pow_le_pow_right (by omega) hx)
  have hyden : y.den ≤ 2 ^ L := (rational_den_le_pow_bits y).trans (Nat.pow_le_pow_right (by omega) hy)
  have hden : (x + y).den ≤ 2 ^ (2 * L) := by
    apply (Nat.le_of_dvd (Nat.mul_pos x.den_pos y.den_pos) (Rat.add_den_dvd x y)).trans
    simpa only [two_mul, pow_add] using Nat.mul_le_mul hxden hyden
  have hxabs := (rational_abs_le_pow_bits x).trans (pow_le_pow_right₀ (by norm_num) hx)
  have hyabs := (rational_abs_le_pow_bits y).trans (pow_le_pow_right₀ (by norm_num) hy)
  have habs : |x + y| ≤ (2 : ℚ) ^ (L + 1) := by
    rw [pow_succ]
    linarith [abs_add_le x y]
  have h := rational_bits_le_of_den_abs _ _ _ hden habs
  omega

theorem rational_half_bits_le (x : ℚ) (L : ℕ) (hx : rationalMagnitudeBits x ≤ L) :
    rationalMagnitudeBits (x / 2) ≤ 3 * L + 5 := by
  have hd : x.den ≤ 2 ^ L := (rational_den_le_pow_bits x).trans (Nat.pow_le_pow_right (by omega) hx)
  have hden : (x / 2).den ≤ 2 ^ (L + 1) := by
    apply (Nat.le_of_dvd (by positivity) (rational_half_den_dvd x)).trans
    simpa only [pow_succ] using Nat.mul_le_mul_right 2 hd
  have habs : |x / 2| ≤ (2 : ℚ) ^ L := by
    rw [abs_div]
    norm_num
    exact (div_le_self (abs_nonneg x) (by norm_num)).trans
      ((rational_abs_le_pow_bits x).trans (pow_le_pow_right₀ (by norm_num) hx))
  have h := rational_bits_le_of_den_abs _ _ _ hden habs
  omega

/-- One interval update, including evaluation and sign comparison. -/
def algebraicBisectBudget (d C L : ℕ) : ℕ :=
  (2 * L + 1) ^ 3 + (5 * L + 9) ^ 3 +
    d * hornerStepBudget d C (15 * L + 17) + hornerOperandBudget d C (15 * L + 17) + 1

theorem algebraicBisectBudget_mono {d e C D L M : ℕ}
    (hd : d ≤ e) (hC : C ≤ D) (hL : L ≤ M) :
    algebraicBisectBudget d C L ≤ algebraicBisectBudget e D M := by
  unfold algebraicBisectBudget hornerStepBudget hornerOperandBudget
  gcongr

theorem costedAlgebraicBisect_steps_le (I : AlgebraicRealInput) (C L : ℕ)
    (hc : ∀ a ∈ I.coefficients, a.natAbs.size ≤ C)
    (hl : rationalMagnitudeBits I.lower ≤ L) (hu : rationalMagnitudeBits I.upper ≤ L) :
    (costedAlgebraicBisect I).steps ≤ algebraicBisectBudget I.coefficients.length C L := by
  have hs := rational_add_bits_le I.lower I.upper L hl hu
  have hm : rationalMagnitudeBits I.midpoint ≤ 15 * L + 17 := by
    have h := rational_half_bits_le (I.lower + I.upper) (5 * L + 4) hs
    change rationalMagnitudeBits ((I.lower + I.upper) / 2) ≤ _
    omega
  have hsum := rationalArithmeticCost_le _ _ hl hu
  have htwo : rationalMagnitudeBits (2 : ℚ) = 4 := by decide
  have hdiv : rationalArithmeticCost (I.lower + I.upper) 2 ≤ (5 * L + 9) ^ 3 := by
    unfold rationalArithmeticCost
    rw [htwo]
    exact Nat.pow_le_pow_left (by omega) 3
  have hhorner := costedRatHorner_steps_le I.coefficients I.midpoint C (15 * L + 17) hc hm
  have hval := integerPolynomialHorner_bits I.coefficients I.midpoint C (15 * L + 17) hc hm
  have hcompare : rationalMagnitudeBits (integerPolynomialHorner I.coefficients I.midpoint) ≤
      hornerOperandBudget I.coefficients.length C (15 * L + 17) := by
    apply hval.trans
    unfold hornerOperandBudget
    nlinarith
  simp only [costedAlgebraicBisect, Costed.bind_steps, costedRatAdd, costedRatDiv,
    costedRatHorner_value, Costed.charge]
  change rationalArithmeticCost I.lower I.upper +
    (rationalArithmeticCost (I.lower + I.upper) 2 +
      ((costedRatHorner I.coefficients I.midpoint).steps +
        (rationalMagnitudeBits (integerPolynomialHorner I.coefficients I.midpoint) + 1))) ≤ _
  unfold algebraicBisectBudget
  omega

theorem costedAlgebraicRefine_steps_le (I : AlgebraicRealInput) (C n : ℕ)
    (hc : ∀ a ∈ I.coefficients, a.natAbs.size ≤ C) :
    (costedAlgebraicRefine n I).steps ≤
      n * algebraicBisectBudget I.coefficients.length C (3 * I.endpointBits + 2 * n + 3) := by
  induction n with
  | zero => simp [costedAlgebraicRefine, Costed.pure]
  | succ n ih =>
    have hL : 3 * I.endpointBits + 2 * n + 3 ≤ 3 * I.endpointBits + 2 * (n + 1) + 3 := by omega
    have hmono := algebraicBisectBudget_mono (le_refl I.coefficients.length) (le_refl C) hL
    have hprev := ih.trans (Nat.mul_le_mul_left n hmono)
    have hcs : ∀ a ∈ (AlgebraicRealInput.refine n I).coefficients, a.natAbs.size ≤ C := by
      simpa only [AlgebraicRealInput.refine_coefficients] using hc
    have hstep := costedAlgebraicBisect_steps_le (AlgebraicRealInput.refine n I) C
      (3 * I.endpointBits + 2 * (n + 1) + 3) hcs
      ((I.refine_bits n).1.trans hL) ((I.refine_bits n).2.trans hL)
    rw [AlgebraicRealInput.refine_coefficients] at hstep
    rw [costedAlgebraicRefine_steps, Nat.succ_mul]
    exact Nat.add_le_add hprev hstep

namespace AlgebraicRealInput

def coefficientBits : List ℤ → ℕ
  | [] => 0
  | a :: coefficients => a.natAbs.size + 1 + coefficientBits coefficients

def inputSize (I : AlgebraicRealInput) : ℕ := I.endpointBits + coefficientBits I.coefficients + 1

/-- Uses the existing self-delimiting integer and rational encodings. -/
def encode (I : AlgebraicRealInput) : List Bool :=
  encodeNatBits I.coefficients.length ++ I.coefficients.flatMap encodeIntBits ++
    encodeRatBits I.lower ++ encodeRatBits I.upper

theorem coefficientBits_length_le (coefficients : List ℤ) : coefficients.length ≤ coefficientBits coefficients := by
  induction coefficients with
  | nil => rfl
  | cons a coefficients ih => simp only [List.length_cons, coefficientBits]; omega

theorem coefficientBits_entry (coefficients : List ℤ) (a : ℤ) (ha : a ∈ coefficients) :
    a.natAbs.size ≤ coefficientBits coefficients := by
  induction coefficients with
  | nil => simp at ha
  | cons b coefficients ih =>
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · simp only [coefficientBits]; omega
    · have h := ih ha
      simp only [coefficientBits]; omega

theorem encodeCoefficients_length (coefficients : List ℤ) :
    (coefficients.flatMap encodeIntBits).length = 2 * coefficientBits coefficients := by
  induction coefficients with
  | nil => rfl
  | cons a coefficients ih =>
    simp only [List.flatMap_cons, List.length_append, encodeIntBits_length, ih, coefficientBits]
    omega

theorem encode_length (I : AlgebraicRealInput) :
    I.encode.length = 2 * I.inputSize + 2 * I.coefficients.length.size + 1 := by
  simp only [encode, List.length_append, encodeNatBits_length, encodeRatBits_length,
    encodeCoefficients_length, inputSize, endpointBits]
  omega

theorem inputSize_le_encode_length (I : AlgebraicRealInput) : I.inputSize ≤ I.encode.length := by
  rw [I.encode_length]
  omega

theorem coefficients_length_le (I : AlgebraicRealInput) : I.coefficients.length ≤ I.inputSize :=
  (coefficientBits_length_le _).trans (by unfold inputSize; omega)

theorem coefficient_size_le (I : AlgebraicRealInput) (a : ℤ) (ha : a ∈ I.coefficients) :
    a.natAbs.size ≤ I.inputSize := (coefficientBits_entry _ a ha).trans (by unfold inputSize; omega)

theorem endpointBits_le (I : AlgebraicRealInput) : I.endpointBits ≤ I.inputSize := by
  unfold inputSize
  omega

end AlgebraicRealInput

/-- Linear input scan and precision setup; serialized output is charged by
its actual bit length. The loop costs are the accumulated arithmetic costs. -/
def costedAlgebraicApprox (I : AlgebraicRealInput) (t : ℕ) : Costed ℚ :=
  (Costed.charge (10 * (I.encode.length + t.size + 1)) (t + I.spanBits)).bind fun n =>
    (costedAlgebraicRefine n I).bind fun J => Costed.charge (encodeRatBits J.upper).length J.upper

@[simp] theorem costedAlgebraicApprox_value (I : AlgebraicRealInput) (t : ℕ) :
    (costedAlgebraicApprox I t).value = I.approx t := by
  simp only [costedAlgebraicApprox, Costed.bind_value, Costed.charge,
    costedAlgebraicRefine_value, AlgebraicRealInput.approx]

def algebraicPreparationBudget (N : ℕ) : ℕ :=
  2 * (N + 1) * algebraicBisectBudget (N + 1) (N + 1) (7 * (N + 1) + 3) + 24 * (N + 1) + 7

theorem costedAlgebraicApprox_steps_le (I : AlgebraicRealInput) (t : ℕ) :
    (costedAlgebraicApprox I t).steps ≤ algebraicPreparationBudget (I.encode.length + t) := by
  let N := I.encode.length + t + 1
  have hI : I.inputSize ≤ N := I.inputSize_le_encode_length.trans (by dsimp [N]; omega)
  have hE : I.endpointBits ≤ N := I.endpointBits_le.trans hI
  have hn : t + I.spanBits ≤ 2 * N := by
    change t + (2 * I.endpointBits + 1) ≤ 2 * N
    have hE' := I.endpointBits_le.trans I.inputSize_le_encode_length
    dsimp [N]
    omega
  have hd : I.coefficients.length ≤ N := I.coefficients_length_le.trans hI
  have hL : 3 * I.endpointBits + 2 * (t + I.spanBits) + 3 ≤ 7 * N + 3 := by omega
  have hloop := costedAlgebraicRefine_steps_le I I.inputSize (t + I.spanBits) I.coefficient_size_le
  have hloop' : (costedAlgebraicRefine (t + I.spanBits) I).steps ≤
      2 * N * algebraicBisectBudget N N (7 * N + 3) :=
    hloop.trans (Nat.mul_le_mul hn (algebraicBisectBudget_mono hd hI hL))
  have hout : (encodeRatBits (AlgebraicRealInput.refine (t + I.spanBits) I).upper).length ≤ 14 * N + 7 := by
    rw [encodeRatBits_length]
    have h := (I.refine_bits (t + I.spanBits)).2.trans hL
    omega
  have hts : t.size ≤ t := Nat.size_le.mpr Nat.lt_two_pow_self
  have hheader : 10 * (I.encode.length + t.size + 1) ≤ 10 * N := by dsimp [N]; omega
  simp only [costedAlgebraicApprox, Costed.bind_steps, Costed.charge, costedAlgebraicRefine_value]
  change 10 * (I.encode.length + t.size + 1) +
    ((costedAlgebraicRefine (t + I.spanBits) I).steps +
      (encodeRatBits (AlgebraicRealInput.refine (t + I.spanBits) I).upper).length) ≤ _
  unfold algebraicPreparationBudget
  dsimp only [N] at hloop' hout hheader
  omega

theorem polyBound_hornerOperandBudget {n C L : ℕ → ℕ}
    (hn : PolynomialCostBound n) (hC : PolynomialCostBound C) (hL : PolynomialCostBound L) :
    PolynomialCostBound (fun x => hornerOperandBudget (n x) (C x) (L x)) :=
  (hn.add (PolynomialCostBound.const 1)).mul
    ((hC.add ((PolynomialCostBound.const 3).mul hL)).add (PolynomialCostBound.const 3))

theorem polyBound_hornerStepBudget {n C L : ℕ → ℕ}
    (hn : PolynomialCostBound n) (hC : PolynomialCostBound C) (hL : PolynomialCostBound L) :
    PolynomialCostBound (fun x => hornerStepBudget (n x) (C x) (L x)) := by
  have h := polyBound_hornerOperandBudget hn hC hL
  exact ((PolynomialCostBound.const 2).mul
    ((((PolynomialCostBound.const 2).mul h).add (PolynomialCostBound.const 1)).pow 3)).add h

theorem polyBound_algebraicBisectBudget {d C L : ℕ → ℕ}
    (hd : PolynomialCostBound d) (hC : PolynomialCostBound C) (hL : PolynomialCostBound L) :
    PolynomialCostBound (fun x => algebraicBisectBudget (d x) (C x) (L x)) := by
  have hmid := ((PolynomialCostBound.const 15).mul hL).add (PolynomialCostBound.const 17)
  exact (((((((PolynomialCostBound.const 2).mul hL).add (PolynomialCostBound.const 1)).pow 3).add
    ((((PolynomialCostBound.const 5).mul hL).add (PolynomialCostBound.const 9)).pow 3)).add
      (hd.mul (polyBound_hornerStepBudget hd hC hmid))).add
        (polyBound_hornerOperandBudget hd hC hmid)).add (PolynomialCostBound.const 1)

theorem polyBound_algebraicPreparationBudget : PolynomialCostBound algebraicPreparationBudget := by
  have hN := PolynomialCostBound.id.add (PolynomialCostBound.const 1)
  have hL := ((PolynomialCostBound.const 7).mul hN).add (PolynomialCostBound.const 3)
  exact (((((PolynomialCostBound.const 2).mul hN).mul
    (polyBound_algebraicBisectBudget hN hN hL)).add
      ((PolynomialCostBound.const 24).mul hN)).add (PolynomialCostBound.const 7))

/-- Uniform polynomial time for every finite input, even invalid root data.
Semantic validity is needed for accuracy, not for termination or cost. -/
theorem costedAlgebraicApprox_polynomialTime :
    Costed.PolynomialTime costedAlgebraicApprox (fun _ => True) (fun I => I.encode.length) := by
  obtain ⟨C, k, h⟩ := polyBound_algebraicPreparationBudget.exists_mul_pow_bound
  exact ⟨C, k, fun I _ t => (costedAlgebraicApprox_steps_le I t).trans (h (I.encode.length + t))⟩

theorem costedAlgebraicApprox_accuracy (I : AlgebraicRealInput) {x : ℝ}
    (hI : I.ValidFor x) (t : ℕ) :
    |((costedAlgebraicApprox I t).value : ℝ) - x| ≤ 1 / (2 : ℝ) ^ t ∧
      x ≤ ((costedAlgebraicApprox I t).value : ℝ) := by
  rw [costedAlgebraicApprox_value]
  exact ⟨hI.approx_error t, hI.le_approx t⟩


theorem costedAlgebraicApprox_output_length (I : AlgebraicRealInput) (t : ℕ) :
    (encodeRatBits (costedAlgebraicApprox I t).value).length ≤ 14 * I.encode.length + 4 * t + 11 := by
  rw [costedAlgebraicApprox_value, encodeRatBits_length]
  have h := (I.refine_bits (t + I.spanBits)).2
  have hE := I.endpointBits_le.trans I.inputSize_le_encode_length
  change rationalMagnitudeBits (I.approx t) ≤ 3 * I.endpointBits + 2 * (t + I.spanBits) + 3 at h
  change rationalMagnitudeBits (I.approx t) ≤ 3 * I.endpointBits + 2 * (t + (2 * I.endpointBits + 1)) + 3 at h
  omega

/-- Accuracy, positive upper rounding, encoded output and polynomial cost all
refer to the same execution, with constants uniform over every input. -/
theorem algebraicInput_polynomial_approximation_certificate :
    ∃ C k : ℕ, ∀ (I : AlgebraicRealInput) (x : ℝ), I.ValidFor x → ∀ t : ℕ,
      let run := costedAlgebraicApprox I t
      run.steps ≤ C * (I.encode.length + t + 1) ^ k ∧
        |(run.value : ℝ) - x| ≤ 1 / (2 : ℝ) ^ t ∧ x ≤ (run.value : ℝ) ∧
        (encodeRatBits run.value).length ≤ 14 * I.encode.length + 4 * t + 11 ∧
        decodeRatPrefix (encodeRatBits run.value) = some (run.value, []) ∧
        (0 < x → 0 < run.value) := by
  obtain ⟨C, k, hcost⟩ := costedAlgebraicApprox_polynomialTime
  refine ⟨C, k, fun I x hI t => ?_⟩
  have h := costedAlgebraicApprox_accuracy I hI t
  refine ⟨hcost I trivial t, h.1, h.2, costedAlgebraicApprox_output_length I t, ?_, ?_⟩
  · simpa only [List.append_nil] using decodeRatBits_append (costedAlgebraicApprox I t).value []
  · intro hx
    rw [costedAlgebraicApprox_value]
    exact hI.approx_pos hx t

end GeometricGaussianLHL

end AlgebraicInputCost
