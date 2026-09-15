import GeometricGaussianLHL.Encoding
import Mathlib.Algebra.Polynomial.Degree.Support
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Topology.Order.IntermediateValue

/-!
# Arithmetic executions and polynomial cost bounds

This module collects the following proof sections, in dependency order.
- PolynomialCost (`PolynomialCost`).
- Algorithms with explicit arithmetic costs (`ArithmeticCost`).
- Charged natural addition and multiplication (`NaturalArithmetic`).
- Primitive natural arithmetic cost bounds (`NaturalArithmeticBounds`).
-/

section PolynomialCost

/-! # Pointwise polynomial bounds for natural-valued costs

A Mathlib polynomial bounds the cost at every input length. These elementary
closure facts are independent of any computational machine model.
-/
namespace GeometricGaussianLHL

def PolynomialCostBound (f : ℕ → ℕ) : Prop :=
  ∃ p : Polynomial ℕ, ∀ n, f n ≤ p.eval n

namespace PolynomialCostBound

theorem const (c : ℕ) : PolynomialCostBound (fun _ => c) := by
  refine ⟨Polynomial.C c, ?_⟩
  intro n
  simp

theorem add {f g : ℕ → ℕ} (hf : PolynomialCostBound f) (hg : PolynomialCostBound g) :
    PolynomialCostBound (fun n => f n + g n) := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  refine ⟨p + q, fun n => ?_⟩
  simpa using Nat.add_le_add (hp n) (hq n)

theorem mul {f g : ℕ → ℕ} (hf : PolynomialCostBound f) (hg : PolynomialCostBound g) :
    PolynomialCostBound (fun n => f n * g n) := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  refine ⟨p * q, fun n => ?_⟩
  simpa using Nat.mul_le_mul (hp n) (hq n)

theorem pow {f : ℕ → ℕ} (hf : PolynomialCostBound f) (k : ℕ) :
    PolynomialCostBound (fun n => f n ^ k) := by
  obtain ⟨p, hp⟩ := hf
  refine ⟨p ^ k, fun n => ?_⟩
  simpa using Nat.pow_le_pow_left (hp n) k


theorem id : PolynomialCostBound (fun n => n) := by
  refine ⟨Polynomial.X, ?_⟩
  intro n
  simp

theorem mono {f g : ℕ → ℕ} (hg : PolynomialCostBound g) (h : ∀ n, f n ≤ g n) :
    PolynomialCostBound f := by
  obtain ⟨p, hp⟩ := hg
  exact ⟨p, fun n => (h n).trans (hp n)⟩

/-- Extract constants uniform over the entire input-size domain. -/
theorem exists_mul_pow_bound {f : ℕ → ℕ} (hf : PolynomialCostBound f) :
    ∃ C k : ℕ, ∀ n, f n ≤ C * (n + 1) ^ k := by
  obtain ⟨p, hp⟩ := hf
  refine ⟨∑ i ∈ p.support, p.coeff i, p.natDegree, fun n => ?_⟩
  apply (hp n).trans
  rw [Polynomial.eval_eq_sum, Polynomial.sum, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  apply Nat.mul_le_mul_left
  exact (Nat.pow_le_pow_left (Nat.le_succ n) i).trans
    (Nat.pow_le_pow_right (Nat.succ_pos n) (Polynomial.le_natDegree_of_mem_supp i hi))

end PolynomialCostBound
end GeometricGaussianLHL

end PolynomialCost

section ArithmeticCost

/-!
## Algorithms with explicit arithmetic costs

Following the reference certificate's output-and-cost convention, an execution
contains a computed value and a natural cost. Composition adds costs. Integer
addition is charged linearly in operand bit length; multiplication and division
quadratically. Rational arithmetic includes a cubic charge for normalization.
These are the declared primitive costs, not claims about Lean's evaluator or a
compiled machine. A polynomial result must bound these actual accumulated costs.
-/
namespace GeometricGaussianLHL

structure Costed (α : Type*) where
  value : α
  steps : ℕ
  deriving Repr

namespace Costed

def pure (a : α) : Costed α := ⟨a, 0⟩

def bind (x : Costed α) (f : α → Costed β) : Costed β :=
  let y := f x.value
  ⟨y.value, x.steps + y.steps⟩

def charge (cost : ℕ) (a : α) : Costed α := ⟨a, cost⟩

@[simp] theorem bind_value (x : Costed α) (f : α → Costed β) :
    (x.bind f).value = (f x.value).value := rfl

@[simp] theorem bind_steps (x : Costed α) (f : α → Costed β) :
    (x.bind f).steps = x.steps + (f x.value).steps := rfl

theorem bind_steps_le (x : Costed α) (f : α → Costed β) {a b : ℕ}
    (hx : x.steps ≤ a) (hf : (f x.value).steps ≤ b) : (x.bind f).steps ≤ a + b :=
  Nat.add_le_add hx hf

/-- Bit count `t` is charged by its value, as an output-accuracy budget. -/
def PolynomialTime (run : α → ℕ → Costed β) (valid : α → Prop) (inputBits : α → ℕ) : Prop :=
  ∃ C k : ℕ, ∀ a, valid a → ∀ t, (run a t).steps ≤ C * (inputBits a + t + 1) ^ k

end Costed

def integerOperandBits (a b : ℤ) : ℕ := a.natAbs.size + b.natAbs.size + 1

def costedIntAdd (a b : ℤ) : Costed ℤ := ⟨a + b, integerOperandBits a b⟩
def costedIntMul (a b : ℤ) : Costed ℤ := ⟨a * b, (integerOperandBits a b) ^ 2⟩
def costedIntDiv (a b : ℤ) : Costed ℤ := ⟨a / b, (integerOperandBits a b) ^ 2⟩

def rationalArithmeticCost (a b : ℚ) : ℕ :=
  (rationalMagnitudeBits a + rationalMagnitudeBits b + 1) ^ 3

def costedRatAdd (a b : ℚ) : Costed ℚ := ⟨a + b, rationalArithmeticCost a b⟩
def costedRatMul (a b : ℚ) : Costed ℚ := ⟨a * b, rationalArithmeticCost a b⟩
def costedRatDiv (a b : ℚ) : Costed ℚ := ⟨a / b, rationalArithmeticCost a b⟩

theorem rationalArithmeticCost_le (a b : ℚ) {L : ℕ}
    (ha : rationalMagnitudeBits a ≤ L) (hb : rationalMagnitudeBits b ≤ L) :
    rationalArithmeticCost a b ≤ (2 * L + 1) ^ 3 :=
  Nat.pow_le_pow_left (by omega) 3

theorem polyBound_rationalArithmeticCost {a b : ℕ → ℚ}
    (ha : PolynomialCostBound (fun n => rationalMagnitudeBits (a n)))
    (hb : PolynomialCostBound (fun n => rationalMagnitudeBits (b n))) :
    PolynomialCostBound (fun n => rationalArithmeticCost (a n) (b n)) :=
  ((ha.add hb).add (PolynomialCostBound.const 1)).pow 3

end GeometricGaussianLHL

end ArithmeticCost

section NaturalArithmetic

/-!
## Charged natural addition and multiplication
-/

namespace GeometricGaussianLHL

def costedNatAdd (a b : ℕ) : Costed ℕ := ⟨a + b, a.size + b.size + 1⟩
def costedNatMul (a b : ℕ) : Costed ℕ := ⟨a * b, (a.size + b.size + 1) ^ 2⟩

end GeometricGaussianLHL

end NaturalArithmetic

section NaturalArithmeticBounds

/-!
## Primitive natural arithmetic cost bounds
-/

namespace GeometricGaussianLHL

theorem costedNatAdd_steps_le (a b L : ℕ) (ha : a ≤ L) (hb : b ≤ L) :
    (costedNatAdd a b).steps ≤ (2 * L + 1) ^ 2 := by
  have ha' : a.size ≤ L := (Nat.size_le.mpr (Nat.lt_two_pow_self (n := a))).trans ha
  have hb' : b.size ≤ L := (Nat.size_le.mpr (Nat.lt_two_pow_self (n := b))).trans hb
  change a.size + b.size + 1 ≤ _
  nlinarith

theorem costedNatMul_steps_le (a b L : ℕ) (ha : a ≤ L) (hb : b ≤ L) :
    (costedNatMul a b).steps ≤ (2 * L + 1) ^ 2 := by
  have ha' : a.size ≤ L := (Nat.size_le.mpr (Nat.lt_two_pow_self (n := a))).trans ha
  have hb' : b.size ≤ L := (Nat.size_le.mpr (Nat.lt_two_pow_self (n := b))).trans hb
  exact Nat.pow_le_pow_left (by omega) 2

end GeometricGaussianLHL

end NaturalArithmeticBounds
