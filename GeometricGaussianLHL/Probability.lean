import GeometricGaussianLHL.Foundations
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Discrete probability and total variation

This module collects the following proof sections, in dependency order.
- Total variation and symmetric relative entropy (`DiscreteVariation`).
- Moments of sums of independent discrete variables (`IndependentMoments`).
- Discrete Gaussian probability distributions (`DiscreteGaussian`).
- Character tests for total variation (`CharacterVariation`).
- Total variation from uniformly flat reweighting (`FlatReweighting`).
- Event probabilities and total variation (`VariationEvents`).
- Escape probabilities from second moments (`DiscreteMomentEscape`).
- Total variation from a common truncation set (`TruncatedVariation`).
- Joint laws with a common marginal (`JointVariation`).
- Stability of normalized weights on a common truncation set (`ReweightedVariation`).
- Separate exceptional-event budgets (`JointEventBudgets`).
-/

section DiscreteVariation

/-!
## Total variation and symmetric relative entropy

For positive discrete probability masses, total variation is bounded by one half the square root of
the symmetric relative entropy. For integer translates of a centred Gaussian, the two relative
entropies are equal; this gives precisely the shift constant in the elementary Gaussian estimates
lemma.
-/

noncomputable section

namespace GeometricGaussianLHL

theorem quadratic_le_log_ratio_of_le {p q : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hqp : q ≤ p) :
    2 * (p - q) ^ 2 ≤ (p + q) * ((p - q) * Real.log (p / q)) := by
  have hl := Real.le_log_one_add_of_nonneg (div_nonneg (sub_nonneg.mpr hqp) hq.le)
  have h₁ : 1 + (p - q) / q = p / q := by field_simp; ring
  have h₂ : 2 * ((p - q) / q) / ((p - q) / q + 2) = 2 * (p - q) / (p + q) := by
    have hd : (p - q) / q + 2 = (p + q) / q := by field_simp; ring
    rw [hd]
    field_simp
  rw [h₁, h₂] at hl
  have hm := mul_le_mul_of_nonneg_left ((div_le_iff₀ (add_pos hp hq)).mp hl)
    (sub_nonneg.mpr hqp)
  nlinarith only [hm]

theorem quadratic_le_log_ratio {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    2 * (p - q) ^ 2 ≤ (p + q) * ((p - q) * Real.log (p / q)) := by
  rcases le_total q p with h | h
  · exact quadratic_le_log_ratio_of_le hp hq h
  · have hh := quadratic_le_log_ratio_of_le hq hp h
    rw [Real.log_div hp.ne' hq.ne', Real.log_div hq.ne' hp.ne'] at *
    nlinarith only [hh]

theorem sub_mul_log_ratio_nonneg {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    0 ≤ (p - q) * Real.log (p / q) := by
  have hh := quadratic_le_log_ratio hp hq
  have hsum := add_pos hp hq
  nlinarith [sq_nonneg (p - q)]

def discreteTotalVariation {α : Type*} (p q : PMF α) : ℝ :=
  (∑' x, |(p x).toReal - (q x).toReal|) / 2

theorem pmf_summable_toReal {α : Type*} (p : PMF α) :
    Summable (fun x => (p x).toReal) := ENNReal.summable_toReal p.tsum_coe_ne_top

@[simp] theorem pmf_tsum_toReal {α : Type*} (p : PMF α) :
    (∑' x, (p x).toReal) = 1 := by
  rw [← ENNReal.tsum_toReal_eq (fun x => p.apply_ne_top x), p.tsum_coe,
    ENNReal.toReal_one]

theorem pmf_summable_abs_sub {α : Type*} (p q : PMF α) :
    Summable (fun x => |(p x).toReal - (q x).toReal|) := by
  simpa only [Real.norm_eq_abs] using ((pmf_summable_toReal p).sub (pmf_summable_toReal q)).norm

/-- The symmetric entropy bound, proved directly by a scalar logarithmic
inequality and finite Cauchy–Schwarz, followed by the convergent infinite sum. -/
theorem discreteTotalVariation_le_sqrt_symmetricEntropy {α : Type*} (p q : PMF α)
    (hp : ∀ x, 0 < (p x).toReal) (hq : ∀ x, 0 < (q x).toReal)
    (hJ : Summable (fun x => ((p x).toReal - (q x).toReal) *
      Real.log ((p x).toReal / (q x).toReal))) :
    discreteTotalVariation p q ≤ Real.sqrt (∑' x,
      ((p x).toReal - (q x).toReal) * Real.log ((p x).toReal / (q x).toReal)) / 2 := by
  let J : α → ℝ := fun x => ((p x).toReal - (q x).toReal) *
    Real.log ((p x).toReal / (q x).toReal)
  have hJ0 : ∀ x, 0 ≤ J x := fun x => sub_mul_log_ratio_nonneg (hp x) (hq x)
  have hb : ∀ s : Finset α, (∑ x ∈ s, |(p x).toReal - (q x).toReal|) ≤
      Real.sqrt (∑' x, J x) := by
    intro s
    have hCS := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
      (r := fun x => |(p x).toReal - (q x).toReal|)
      (f := fun x => J x / 2) (g := fun x => (p x).toReal + (q x).toReal)
      (fun x _ => div_nonneg (hJ0 x) (by norm_num))
      (fun x _ => add_nonneg (hp x).le (hq x).le)
      (fun x _ => by
        rw [sq_abs]
        have hh := quadratic_le_log_ratio (hp x) (hq x)
        change _ ≤ J x / 2 * ((p x).toReal + (q x).toReal)
        dsimp [J]
        nlinarith only [hh])
    have hfst : (∑ x ∈ s, J x / 2) ≤ (∑' x, J x) / 2 := by
      simpa only [tsum_div_const] using (hJ.div_const 2).sum_le_tsum s
        (fun x _ => div_nonneg (hJ0 x) (by norm_num))
    have hsnd : (∑ x ∈ s, ((p x).toReal + (q x).toReal)) ≤ 2 := by
      have hh := ((pmf_summable_toReal p).add (pmf_summable_toReal q)).sum_le_tsum s
        (fun x _ => add_nonneg (hp x).le (hq x).le)
      simpa only [Summable.tsum_add (pmf_summable_toReal p) (pmf_summable_toReal q),
        pmf_tsum_toReal, one_add_one_eq_two] using hh
    have hprod := mul_le_mul hfst hsnd
      (Finset.sum_nonneg (fun x _ => add_nonneg (hp x).le (hq x).le))
      (div_nonneg (tsum_nonneg hJ0) (by norm_num : (0 : ℝ) ≤ 2))
    apply Real.le_sqrt_of_sq_le
    nlinarith only [hCS, hprod]
  unfold discreteTotalVariation
  exact div_le_div_of_nonneg_right
    ((pmf_summable_abs_sub p q).tsum_le_of_sum_le hb) (by norm_num)

end GeometricGaussianLHL
end

end DiscreteVariation

section IndependentMoments

/-!
## Moments of sums of independent discrete variables

All exchanges below are between absolutely convergent real series.
The binomial formula uses the literal product of the two PMF masses.
-/

noncomputable section

namespace GeometricGaussianLHL

theorem summable_pmf_product_monomial {α β : Type*} (p : PMF α) (q : PMF β)
    (f : α → ℝ) (g : β → ℝ) (j k : ℕ)
    (hf : Summable (fun x => (p x).toReal * f x ^ j))
    (hg : Summable (fun y => (q y).toReal * g y ^ k)) :
    Summable (fun z : α × β => (p z.1).toReal * (q z.2).toReal *
      (f z.1 ^ j * g z.2 ^ k)) :=
  (summable_mul_of_summable_norm hf.norm hg.norm).congr (fun _ => by ring)

theorem tsum_pmf_product_monomial {α β : Type*} (p : PMF α) (q : PMF β)
    (f : α → ℝ) (g : β → ℝ) (j k : ℕ)
    (hf : Summable (fun x => (p x).toReal * f x ^ j))
    (hg : Summable (fun y => (q y).toReal * g y ^ k)) :
    (∑' z : α × β, (p z.1).toReal * (q z.2).toReal * (f z.1 ^ j * g z.2 ^ k)) =
      (∑' x, (p x).toReal * f x ^ j) * (∑' y, (q y).toReal * g y ^ k) := by
  rw [tsum_mul_tsum_of_summable_norm hf.norm hg.norm]
  apply tsum_congr
  intro z
  ring

theorem summable_pmf_product_add_pow {α β : Type*} (p : PMF α) (q : PMF β)
    (f : α → ℝ) (g : β → ℝ)
    (hf : ∀ k : ℕ, Summable (fun x => (p x).toReal * f x ^ k))
    (hg : ∀ k : ℕ, Summable (fun y => (q y).toReal * g y ^ k)) (k : ℕ) :
    Summable (fun z : α × β => (p z.1).toReal * (q z.2).toReal * (f z.1 + g z.2) ^ k) := by
  have h := summable_sum (s := Finset.range (k + 1)) (fun j _ =>
    (summable_pmf_product_monomial p q f g j (k - j) (hf j) (hg (k - j))).mul_right
      (k.choose j : ℝ))
  apply h.congr
  intro z
  rw [add_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem tsum_pmf_product_add_pow {α β : Type*} (p : PMF α) (q : PMF β)
    (f : α → ℝ) (g : β → ℝ)
    (hf : ∀ k : ℕ, Summable (fun x => (p x).toReal * f x ^ k))
    (hg : ∀ k : ℕ, Summable (fun y => (q y).toReal * g y ^ k)) (k : ℕ) :
    (∑' z : α × β, (p z.1).toReal * (q z.2).toReal * (f z.1 + g z.2) ^ k) =
      ∑ j ∈ Finset.range (k + 1),
        (∑' x, (p x).toReal * f x ^ j) * (∑' y, (q y).toReal * g y ^ (k - j)) *
          (k.choose j : ℝ) := by
  simp_rw [add_pow, Finset.mul_sum]
  have hterm : ∀ (z : α × β) j, (p z.1).toReal * (q z.2).toReal *
      (f z.1 ^ j * g z.2 ^ (k - j) * (k.choose j : ℝ)) =
        ((p z.1).toReal * (q z.2).toReal * (f z.1 ^ j * g z.2 ^ (k - j))) *
          (k.choose j : ℝ) := fun _ _ => by ring
  simp_rw [hterm]
  rw [Summable.tsum_finsetSum (fun j _ =>
    (summable_pmf_product_monomial p q f g j (k - j) (hf j) (hg (k - j))).mul_right
      (k.choose j : ℝ))]
  apply Finset.sum_congr rfl
  intro j _
  rw [tsum_mul_right, tsum_pmf_product_monomial p q f g j (k - j) (hf j) (hg (k - j))]

end GeometricGaussianLHL
end

end IndependentMoments

section DiscreteGaussian

/-!
## Discrete Gaussian probability distributions

Actual normalized probability masses on the integers, and finite independent
products. The one-dimensional convergence argument bounds the Gaussian by
a geometric series. It follows the elementary argument also used in the
reference certificate's `Probability.lean`.
-/

open scoped ENNReal

noncomputable section

namespace GeometricGaussianLHL

theorem summable_integer_gaussian {a : ℝ} (ha : 0 < a) :
    Summable (fun z : ℤ => Real.exp (-a * (z : ℝ) ^ 2)) := by
  have hnat : Summable (fun n : ℕ => Real.exp (-a * (n : ℝ) ^ 2)) :=
    Real.summable_exp_nat_mul_of_ge (c := -a) (neg_lt_zero.mpr ha)
      (f := fun n : ℕ => (n : ℝ) ^ 2) (fun n => by
        cases n with
        | zero => norm_num
        | succ n =>
          push_cast
          nlinarith [sq_nonneg (n : ℝ), Nat.cast_nonneg (α := ℝ) n])
  apply Summable.of_nat_of_neg
  · simpa only [Int.cast_natCast] using hnat
  · simpa only [Int.cast_neg, Int.cast_natCast, neg_sq] using hnat

def integerGaussianWeight (s : ℝ) (z : ℤ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-(Real.pi / s ^ 2) * (z : ℝ) ^ 2))

theorem integerGaussianWeight_sum_ne_zero (s : ℝ) :
    (∑' z, integerGaussianWeight s z) ≠ 0 := by
  have h := ENNReal.le_tsum (f := integerGaussianWeight s) 0
  simp only [integerGaussianWeight, Int.cast_zero, zero_pow (by omega : 2 ≠ 0),
    mul_zero, Real.exp_zero, ENNReal.ofReal_one] at h
  exact ne_of_gt (lt_of_lt_of_le zero_lt_one h)

theorem integerGaussianWeight_sum_ne_top {s : ℝ} (hs : 0 < s) :
    (∑' z, integerGaussianWeight s z) ≠ ⊤ :=
  (summable_integer_gaussian (div_pos Real.pi_pos (sq_pos_of_pos hs))).tsum_ofReal_ne_top

def integerGaussian (s : ℝ) (hs : 0 < s) : PMF ℤ :=
  PMF.normalize (integerGaussianWeight s) (integerGaussianWeight_sum_ne_zero s)
    (integerGaussianWeight_sum_ne_top hs)

theorem integerGaussian_apply (s : ℝ) (hs : 0 < s) (z : ℤ) :
    integerGaussian s hs z = integerGaussianWeight s z /
      (∑' k, integerGaussianWeight s k) := by
  simp [integerGaussian, PMF.normalize_apply, div_eq_mul_inv]

theorem integerGaussian_symmetric (s : ℝ) (hs : 0 < s) (z : ℤ) :
    integerGaussian s hs (-z) = integerGaussian s hs z := by
  simp [integerGaussian_apply, integerGaussianWeight]

/-- Tonelli's product identity on finitely many discrete coordinates.
-/
theorem tsum_finite_product {α : Type*} : ∀ (n : ℕ) (f : Fin n → α → ℝ≥0∞),
    (∑' z : Fin n → α, ∏ i, f i (z i)) = ∏ i, ∑' x, f i x := by
  intro n
  induction n with
  | zero => intro f; simp
  | succ n ih =>
    intro f
    let e := Fin.consEquiv (fun _ : Fin (n + 1) => α)
    calc
      (∑' z : Fin (n + 1) → α, ∏ i, f i (z i)) =
          ∑' p : α × (Fin n → α), ∏ i, f i (e p i) := (e.tsum_eq _).symm
      _ = ∑' a, ∑' z : Fin n → α, f 0 a * ∏ i, f i.succ (z i) := by
        rw [ENNReal.tsum_prod' (f := fun p : α × (Fin n → α) => ∏ i, f i (e p i))]
        simp [e, Fin.consEquiv, Fin.prod_univ_succ]
      _ = (∑' a, f 0 a) * (∑' z : Fin n → α, ∏ i, f i.succ (z i)) := by
        simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]
      _ = (∑' a, f 0 a) * ∏ i : Fin n, ∑' x, f i.succ x := by rw [ih]
      _ = ∏ i : Fin (n + 1), ∑' x, f i x := by rw [Fin.prod_univ_succ]

/-- A finite independent product specified by its exact mass function. -/
def independentProduct {α : Type*} {n : ℕ} (p : Fin n → PMF α) : PMF (Fin n → α) :=
  ⟨fun z => ∏ i, p i (z i), by
    apply ENNReal.summable.hasSum_iff.mpr
    rw [tsum_finite_product]
    simp⟩

@[simp] theorem independentProduct_apply {α : Type*} {n : ℕ}
    (p : Fin n → PMF α) (z : Fin n → α) : independentProduct p z = ∏ i, p i (z i) := rfl

def productIntegerGaussian (n : ℕ) (s : ℝ) (hs : 0 < s) : PMF (Coeff n) :=
  independentProduct (fun _ => integerGaussian s hs)

/-- Independent coefficient columns. In the power-of-two setting the
number-field identification will use width `s / sqrt d`. -/
def coefficientColumnLaw (R m : ℕ) (s : ℝ) (hs : 0 < s) : PMF (Fin m → Coeff R) :=
  independentProduct (fun _ => productIntegerGaussian R s hs)

end GeometricGaussianLHL
end

end DiscreteGaussian

section CharacterVariation

/-!
## Character tests for total variation

Bounded complex tests give lower bounds for the actual half-sum distance.
The expectation under a mapped PMF is proved by convergent fiberwise sums.
-/
noncomputable section
namespace GeometricGaussianLHL

def pmfComplexExpectation {α : Type*} (p : PMF α) (f : α → ℂ) : ℂ :=
  ∑' a, ((p a).toReal : ℂ) * f a

theorem pmfComplexExpectation_summable {α : Type*} (p : PMF α) (f : α → ℂ)
    (hf : ∀ a, ‖f a‖ ≤ 1) : Summable (fun a => ((p a).toReal : ℂ) * f a) := by
  apply (pmf_summable_toReal p).of_norm_bounded
  intro a
  rw [norm_mul, Complex.norm_of_nonneg ENNReal.toReal_nonneg]
  exact (mul_le_mul_of_nonneg_left (hf a) ENNReal.toReal_nonneg).trans_eq (mul_one _)

theorem pmfComplexExpectation_map {α β : Type*} (p : PMF α) (g : α → β)
    (f : β → ℂ) (hf : ∀ b, ‖f b‖ ≤ 1) :
    pmfComplexExpectation (p.map g) f = pmfComplexExpectation p (f ∘ g) := by
  classical
  have hm (b : β) : ((p.map g) b).toReal = ∑' a : g ⁻¹' {b}, (p a).toReal := by
    rw [PMF.map_apply, ENNReal.tsum_toReal_eq]
    · rw [tsum_subtype (g ⁻¹' {b}) (fun a => (p a).toReal)]
      apply tsum_congr
      intro a
      by_cases ha : b = g a <;> simp [ha, eq_comm, Set.indicator]
    · intro a
      split_ifs <;> simp [p.apply_ne_top]
  have hs := (pmfComplexExpectation_summable p (f ∘ g) (fun a => hf (g a))).hasSum.tsum_fiberwise g
  unfold pmfComplexExpectation
  rw [← hs.tsum_eq]
  apply tsum_congr
  intro b
  rw [hm, Complex.ofReal_tsum, ← tsum_mul_right]
  apply tsum_congr
  intro a
  have ha : g a = b := a.property
  simp only [Function.comp_apply, ha]

theorem pmfComplexExpectation_sub_norm_le {α : Type*} [Fintype α] (p q : PMF α)
    (f : α → ℂ) (hf : ∀ a, ‖f a‖ ≤ 1) :
    ‖pmfComplexExpectation p f - pmfComplexExpectation q f‖ ≤ 2 * discreteTotalVariation p q := by
  classical
  simp only [pmfComplexExpectation, tsum_fintype, ← Finset.sum_sub_distrib, ← sub_mul,
    ← Complex.ofReal_sub]
  calc
    _ ≤ ∑ a, ‖(((p a).toReal - (q a).toReal : ℝ) : ℂ) * f a‖ := norm_sum_le _ _
    _ ≤ ∑ a, |(p a).toReal - (q a).toReal| := by
      apply Finset.sum_le_sum
      intro a _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_left (hf a) (abs_nonneg _)).trans_eq (mul_one _)
    _ = 2 * discreteTotalVariation p q := by
      simp only [discreteTotalVariation, tsum_fintype]
      ring

theorem zmod_stdAddChar_norm (q : ℕ) [NeZero q] (a : ZMod q) :
    ‖ZMod.stdAddChar a‖ = 1 := by rw [ZMod.stdAddChar_apply, Circle.norm_coe]

theorem uniform_zmod_character_zero (q : ℕ) [NeZero q] [Nontrivial (ZMod q)] :
    pmfComplexExpectation (PMF.uniformOfFintype (ZMod q)) ZMod.stdAddChar = 0 := by
  have hne : (ZMod.stdAddChar : AddChar (ZMod q) ℂ) ≠ 1 := by
    intro h
    have he : ZMod.stdAddChar (1 : ZMod q) = ZMod.stdAddChar (0 : ZMod q) := by simp [h]
    exact one_ne_zero (ZMod.injective_stdAddChar he)
  simp only [pmfComplexExpectation, tsum_fintype, PMF.uniformOfFintype_apply,
    ← Finset.mul_sum, AddChar.sum_eq_zero_of_ne_one hne, mul_zero]

end GeometricGaussianLHL
end

end CharacterVariation

section FlatReweighting

/-!
## Total variation from uniformly flat reweighting

A common multiplicative factor in the point masses is determined by
normalization. Uniform relative errors of size `ε` around that factor give
the exact `ε / (1 - ε)` statistical-distance budget used in pushforward.
The geometric estimate for the fiber weights is a separate obligation.
-/

noncomputable section

namespace GeometricGaussianLHL

theorem discreteTotalVariation_le_of_abs_le_mul {α : Type*} (p q : PMF α) {C : ℝ}
    (h : ∀ x, |(p x).toReal - (q x).toReal| ≤ C * (q x).toReal) :
    discreteTotalVariation p q ≤ C / 2 := by
  have hb := (pmf_summable_abs_sub p q).tsum_le_tsum h
    ((pmf_summable_toReal q).mul_left C)
  rw [tsum_mul_left, pmf_tsum_toReal, mul_one] at hb
  exact div_le_div_of_nonneg_right hb (by norm_num)

theorem discreteTotalVariation_le_of_uniform_ratios {α : Type*} (p q : PMF α)
    {R : ℝ} (hR : 1 ≤ R)
    (h : ∀ x, (p x).toReal ≤ R * (q x).toReal ∧ (q x).toReal ≤ R * (p x).toReal) :
    discreteTotalVariation p q ≤ (R - 1) / 2 := by
  apply discreteTotalVariation_le_of_abs_le_mul
  intro x
  obtain ⟨hpq, hqp⟩ := h x
  rcases le_total (p x).toReal (q x).toReal with hle | hle
  · rw [abs_of_nonpos (sub_nonpos.mpr hle)]
    have hm := mul_le_mul_of_nonneg_left hle (sub_nonneg.mpr hR)
    nlinarith only [hm, hqp]
  · rw [abs_of_nonneg (sub_nonneg.mpr hle)]
    linarith

/-- A uniform comparison before normalization suffices: the normalizing
factor `c` need not be supplied with its own upper or lower bound.
-/
theorem discreteTotalVariation_le_of_flat_reweight {α : Type*} (p q : PMF α)
    {ε c : ℝ} (hε : 0 ≤ ε) (hε1 : ε < 1)
    (h : ∀ x, (1 - ε) * c * (q x).toReal ≤ (p x).toReal ∧
      (p x).toReal ≤ (1 + ε) * c * (q x).toReal) :
    discreteTotalVariation p q ≤ ε / (1 - ε) := by
  have ha : 0 < 1 - ε := by linarith
  have hcl : 1 ≤ (1 + ε) * c := by
    have hb := (pmf_summable_toReal p).tsum_le_tsum (fun x => (h x).2)
      ((pmf_summable_toReal q).mul_left ((1 + ε) * c))
    simpa only [tsum_mul_left, pmf_tsum_toReal, mul_one] using hb
  have hcu : (1 - ε) * c ≤ 1 := by
    have hb := ((pmf_summable_toReal q).mul_left ((1 - ε) * c)).tsum_le_tsum
      (fun x => (h x).1) (pmf_summable_toReal p)
    simpa only [tsum_mul_left, pmf_tsum_toReal, mul_one] using hb
  have hR : 1 ≤ (1 + ε) / (1 - ε) := (le_div_iff₀ ha).mpr (by linarith)
  have hr (x : α) :
      (p x).toReal ≤ ((1 + ε) / (1 - ε)) * (q x).toReal ∧
      (q x).toReal ≤ ((1 + ε) / (1 - ε)) * (p x).toReal := by
    have hq0 : 0 ≤ (q x).toReal := ENNReal.toReal_nonneg
    obtain ⟨hp, hq⟩ := h x
    constructor
    · rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ ha).mpr
      have h₁ := mul_le_mul_of_nonneg_left hq ha.le
      have h₂ := mul_le_mul_of_nonneg_right hcu (mul_nonneg (by linarith : 0 ≤ 1 + ε) hq0)
      nlinarith only [h₁, h₂]
    · rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ ha).mpr
      have h₁ := mul_le_mul_of_nonneg_left hp (by linarith : 0 ≤ 1 + ε)
      have h₂ := mul_le_mul_of_nonneg_right hcl (mul_nonneg ha.le hq0)
      nlinarith only [h₁, h₂]
  calc
    discreteTotalVariation p q ≤ (((1 + ε) / (1 - ε)) - 1) / 2 :=
      discreteTotalVariation_le_of_uniform_ratios p q hR hr
    _ = ε / (1 - ε) := by field_simp; ring

end GeometricGaussianLHL
end

end FlatReweighting

section VariationEvents

/-!
## Event probabilities and total variation

The half-sum definition of total variation controls the difference of the
actual PMF measures on every event. This provides the probability interface
for the Gaussian translation estimate.
-/

noncomputable section

open MeasureTheory

namespace GeometricGaussianLHL

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]

theorem pmf_measureReal_eq_tsum (p : PMF α) (A : Set α) :
    p.toMeasure.real A = ∑' x, A.indicator (fun x => (p x).toReal) x := by
  classical
  rw [Measure.real, p.toMeasure_apply_eq_tsum, ENNReal.tsum_toReal_eq]
  · apply tsum_congr
    intro x
    by_cases hx : x ∈ A <;> simp [Set.indicator, hx]
  · intro x
    by_cases hx : x ∈ A <;> simp [Set.indicator, hx, p.apply_ne_top]

theorem pmf_event_sub_le_totalVariation (p q : PMF α) (A : Set α) :
    p.toMeasure.real A - q.toMeasure.real A ≤ discreteTotalVariation p q := by
  classical
  let d : α → ℝ := fun x => (p x).toReal - (q x).toReal
  have hd : Summable d := (pmf_summable_toReal p).sub (pmf_summable_toReal q)
  have ha : Summable (fun x => |d x|) := by simpa only [Real.norm_eq_abs] using hd.norm
  have hz : (∑' x, d x) = 0 := by
    dsimp [d]
    rw [Summable.tsum_sub (pmf_summable_toReal p) (pmf_summable_toReal q)]
    simp
  have he : p.toMeasure.real A - q.toMeasure.real A = ∑' x, A.indicator d x := by
    rw [pmf_measureReal_eq_tsum, pmf_measureReal_eq_tsum,
      ← Summable.tsum_sub ((pmf_summable_toReal p).indicator A)
        ((pmf_summable_toReal q).indicator A)]
    apply tsum_congr
    intro x
    by_cases hx : x ∈ A <;> simp [Set.indicator, hx, d]
  rw [he]
  have hb : (∑' x, A.indicator d x) ≤ ∑' x, (d x + |d x|) / 2 := by
    apply (hd.indicator A).tsum_le_tsum _ ((hd.add ha).div_const 2)
    intro x
    by_cases hx : x ∈ A
    · rw [Set.indicator_of_mem hx]
      linarith [le_abs_self (d x)]
    · rw [Set.indicator_of_notMem hx]
      linarith [neg_le_abs (d x)]
  rw [tsum_div_const, Summable.tsum_add hd ha, hz, zero_add] at hb
  exact hb

theorem pmf_map_measureReal (p : PMF α) (f : α → α) (A : Set α) :
    (p.map f).toMeasure.real A = p.toMeasure.real (f ⁻¹' A) := by
  simp only [Measure.real, PMF.toMeasure_apply_eq_toOuterMeasure,
    PMF.toOuterMeasure_map_apply]

end GeometricGaussianLHL
end

end VariationEvents

section DiscreteMomentEscape

/-!
## Escape probabilities from second moments

A direct discrete Paley–Zygmund argument. Finite weighted Cauchy–Schwarz
and convergent real series give an event bound for the actual PMF measure.
No normal-approximation result is assumed.
-/

noncomputable section

open MeasureTheory

namespace GeometricGaussianLHL

/-- Cauchy–Schwarz for the contribution of a nonnegative random variable
on an arbitrary event. Both moment series are required to converge.
-/
theorem pmf_event_moment_sq_le {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (p : PMF α) (f : α → ℝ) (A : Set α)
    (hf : ∀ x, 0 ≤ f x)
    (hs : Summable (fun x => (p x).toReal * f x))
    (hs₂ : Summable (fun x => (p x).toReal * (f x) ^ 2)) :
    (∑' x, A.indicator (fun x => (p x).toReal * f x) x) ^ 2 ≤
      (∑' x, (p x).toReal * (f x) ^ 2) * p.toMeasure.real A := by
  classical
  let W := ∑' x, (p x).toReal * (f x) ^ 2
  have hW : 0 ≤ W := tsum_nonneg (fun _ => by positivity)
  have hP : 0 ≤ p.toMeasure.real A := measureReal_nonneg
  have hb : ∀ s : Finset α,
      (∑ x ∈ s, A.indicator (fun x => (p x).toReal * f x) x) ≤
        Real.sqrt (W * p.toMeasure.real A) := by
    intro s
    have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
      (r := A.indicator (fun x => (p x).toReal * f x))
      (f := fun x => (p x).toReal * (f x) ^ 2)
      (g := A.indicator (fun x => (p x).toReal))
      (fun _ _ => by positivity)
      (fun x _ => Set.indicator_nonneg (fun _ _ => ENNReal.toReal_nonneg) x)
      (fun x _ => by
        by_cases hx : x ∈ A
        · simp only [Set.indicator_of_mem hx]; ring_nf; exact le_rfl
        · simp only [Set.indicator_of_notMem hx, zero_pow (by decide : 2 ≠ 0), mul_zero, le_refl])
    have hw := hs₂.sum_le_tsum s (fun _ _ => by positivity)
    have hp := ((pmf_summable_toReal p).indicator A).sum_le_tsum s
      (fun x _ => Set.indicator_nonneg (fun _ _ => ENNReal.toReal_nonneg) x)
    rw [← pmf_measureReal_eq_tsum] at hp
    have hm := mul_le_mul hw hp
      (Finset.sum_nonneg (fun x _ => Set.indicator_nonneg
        (fun _ _ => ENNReal.toReal_nonneg) x)) hW
    exact Real.le_sqrt_of_sq_le (hcs.trans hm)
  have hle := (hs.indicator A).tsum_le_of_sum_le hb
  have hnonneg : 0 ≤ ∑' x, A.indicator (fun x => (p x).toReal * f x) x :=
    tsum_nonneg (fun x => Set.indicator_nonneg (fun x _ =>
      mul_nonneg ENNReal.toReal_nonneg (hf x)) x)
  have hsq := sq_le_sq₀ hnonneg (Real.sqrt_nonneg _) |>.mpr hle
  rwa [Real.sq_sqrt (mul_nonneg hW hP)] at hsq

/-- The discrete second-moment lower bound, with an arbitrary nonnegative
threshold below the mean. The event uses a strict inequality. -/
theorem pmf_paley_zygmund {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (p : PMF α) (f : α → ℝ)
    (hf : ∀ x, 0 ≤ f x)
    (hs : Summable (fun x => (p x).toReal * f x))
    (hs₂ : Summable (fun x => (p x).toReal * (f x) ^ 2))
    {a : ℝ} (ha : 0 ≤ a) (hmean : a ≤ ∑' x, (p x).toReal * f x) :
    ((∑' x, (p x).toReal * f x) - a) ^ 2 ≤
      (∑' x, (p x).toReal * (f x) ^ 2) * p.toMeasure.real {x | a < f x} := by
  classical
  let A : Set α := {x | a < f x}
  have he := hs.tsum_le_tsum
    (g := fun x => (p x).toReal * a + A.indicator (fun x => (p x).toReal * f x) x)
    (fun x => by
      by_cases hx : x ∈ A
      · rw [Set.indicator_of_mem hx]; exact le_add_of_nonneg_left (by positivity)
      · rw [Set.indicator_of_notMem hx, add_zero]
        exact mul_le_mul_of_nonneg_left (le_of_not_gt hx) ENNReal.toReal_nonneg)
    (((pmf_summable_toReal p).mul_right a).add (hs.indicator A))
  rw [Summable.tsum_add ((pmf_summable_toReal p).mul_right a) (hs.indicator A),
    tsum_mul_right, pmf_tsum_toReal, one_mul] at he
  have hi : 0 ≤ ∑' x, A.indicator (fun x => (p x).toReal * f x) x :=
    tsum_nonneg (fun x => Set.indicator_nonneg
      (fun x _ => mul_nonneg ENNReal.toReal_nonneg (hf x)) x)
  have hsq := (sq_le_sq₀ (sub_nonneg.mpr hmean) hi).mpr (sub_le_iff_le_add.mpr (by linarith))
  exact hsq.trans (pmf_event_moment_sq_le p f A hf hs hs₂)

/-- A fourth moment at most five times the variance squared forces at least
`1/20` of the probability beyond half the second moment. -/
theorem pmf_square_escape_of_fourth_moment {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (p : PMF α) (S : α → ℝ) {V : ℝ}
    (hV : 0 < V)
    (hs₂ : Summable (fun x => (p x).toReal * (S x) ^ 2))
    (hs₄ : Summable (fun x => (p x).toReal * (S x) ^ 4))
    (hsecond : (∑' x, (p x).toReal * (S x) ^ 2) = V)
    (hfourth : (∑' x, (p x).toReal * (S x) ^ 4) ≤ 5 * V ^ 2) :
    (1 / 20 : ℝ) ≤ p.toMeasure.real {x | V / 2 < (S x) ^ 2} := by
  have h := pmf_paley_zygmund p (fun x => (S x) ^ 2) (fun x => sq_nonneg _)
    hs₂ (by simpa only [← pow_mul] using hs₄) (a := V / 2) (by positivity)
    (by rw [hsecond]; linarith)
  simp only [← pow_mul, hsecond] at h
  have hp := measureReal_nonneg (μ := p.toMeasure) (s := {x | V / 2 < (S x) ^ 2})
  have hm := mul_le_mul_of_nonneg_right hfourth hp
  have hVs : 0 < V ^ 2 := sq_pos_of_pos hV
  nlinarith

end GeometricGaussianLHL
end

end DiscreteMomentEscape

section TruncatedVariation

/-!
## Total variation from a common truncation set

Uniform relative bounds on a set of high probability control total
variation. The omitted tails are measured under both actual PMFs.
-/

noncomputable section

open MeasureTheory

namespace GeometricGaussianLHL

theorem discreteTotalVariation_nonneg {α : Type*} (p q : PMF α) :
    0 ≤ discreteTotalVariation p q := by
  unfold discreteTotalVariation
  positivity

theorem discreteTotalVariation_le_one {α : Type*} (p q : PMF α) :
    discreteTotalVariation p q ≤ 1 := by
  have h := (pmf_summable_abs_sub p q).tsum_le_tsum
    (fun x => abs_le.mpr ⟨by nlinarith [(show 0 ≤ (p x).toReal from ENNReal.toReal_nonneg), (show 0 ≤ (q x).toReal from ENNReal.toReal_nonneg)],
      by nlinarith [(show 0 ≤ (p x).toReal from ENNReal.toReal_nonneg), (show 0 ≤ (q x).toReal from ENNReal.toReal_nonneg)]⟩)
    ((pmf_summable_toReal p).add (pmf_summable_toReal q))
  rw [Summable.tsum_add (pmf_summable_toReal p) (pmf_summable_toReal q),
    pmf_tsum_toReal, pmf_tsum_toReal] at h
  unfold discreteTotalVariation
  linarith

theorem abs_sub_le_relative_sum {u v R : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hR : 1 ≤ R) (huv : u ≤ R * v) (hvu : v ≤ R * u) :
    |u - v| ≤ (R - 1) * (u + v) := by
  apply abs_le.mpr
  constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr hR) hu, mul_nonneg (sub_nonneg.mpr hR) hv]

theorem discreteTotalVariation_le_of_relative_on {α : Type*}
    [MeasurableSpace α] [MeasurableSingletonClass α] (p q : PMF α) (E : Set α)
    {ξ R : ℝ} (hR : 1 ≤ R)
    (hp : p.toMeasure.real Eᶜ ≤ ξ) (hq : q.toMeasure.real Eᶜ ≤ ξ)
    (hratio : ∀ x ∈ E, (p x).toReal ≤ R * (q x).toReal ∧ (q x).toReal ≤ R * (p x).toReal) :
    discreteTotalVariation p q ≤ ξ + (R - 1) := by
  classical
  have hs := (pmf_summable_toReal p).add (pmf_summable_toReal q)
  have hpc := (pmf_summable_toReal p).indicator Eᶜ
  have hqc := (pmf_summable_toReal q).indicator Eᶜ
  have hbound (x : α) : |(p x).toReal - (q x).toReal| ≤
      (R - 1) * ((p x).toReal + (q x).toReal) +
        Eᶜ.indicator (fun y => (p y).toReal) x + Eᶜ.indicator (fun y => (q y).toReal) x := by
    by_cases hx : x ∈ E
    · simp only [Set.indicator_of_notMem (show x ∉ Eᶜ from fun h => h hx), add_zero]
      exact abs_sub_le_relative_sum ENNReal.toReal_nonneg ENNReal.toReal_nonneg hR
        (hratio x hx).1 (hratio x hx).2
    · simp only [Set.indicator_of_mem (show x ∈ Eᶜ from hx)]
      have ha : |(p x).toReal - (q x).toReal| ≤ (p x).toReal + (q x).toReal :=
        abs_le.mpr ⟨by nlinarith [(show 0 ≤ (p x).toReal from ENNReal.toReal_nonneg)], by nlinarith [(show 0 ≤ (q x).toReal from ENNReal.toReal_nonneg)]⟩
      have hb := mul_nonneg (sub_nonneg.mpr hR)
        (add_nonneg ((show 0 ≤ (p x).toReal from ENNReal.toReal_nonneg)) ((show 0 ≤ (q x).toReal from ENNReal.toReal_nonneg)))
      linarith
  have h := (pmf_summable_abs_sub p q).tsum_le_tsum hbound (((hs.mul_left (R - 1)).add hpc).add hqc)
  rw [Summable.tsum_add ((hs.mul_left (R - 1)).add hpc) hqc,
    Summable.tsum_add (hs.mul_left (R - 1)) hpc, tsum_mul_left,
    Summable.tsum_add (pmf_summable_toReal p) (pmf_summable_toReal q),
    pmf_tsum_toReal, pmf_tsum_toReal, ← pmf_measureReal_eq_tsum, ← pmf_measureReal_eq_tsum] at h
  unfold discreteTotalVariation
  linarith

end GeometricGaussianLHL
end

end TruncatedVariation

section JointVariation

/-!
## Joint laws with a common marginal

Sampling a marginal and then a conditional PMF gives an actual joint PMF.
Its total variation is exactly the marginal average of the conditional
distances. A good-event bound therefore pays the bad-event probability
once, irrespective of the size of the conditional output.
-/

noncomputable section

namespace GeometricGaussianLHL

def jointPMF {α β : Type*} (p : PMF α) (q : α → PMF β) : PMF (α × β) :=
  p.bind (fun a => (q a).map (fun b => (a, b)))

theorem jointPMF_apply {α β : Type*} (p : PMF α) (q : α → PMF β) (a : α) (b : β) :
    jointPMF p q (a, b) = p a * q a b := by
  classical
  simp only [jointPMF, PMF.bind_apply, PMF.map_apply, Prod.mk.injEq]
  have h (x : α) : (∑' y : β, if a = x ∧ b = y then q x y else 0) =
      if a = x then q x b else 0 := by
    by_cases hx : a = x <;> simp [hx]
  simp_rw [h, mul_ite, mul_zero]
  simp

theorem discreteTotalVariation_joint {α β : Type*} (p : PMF α) (q r : α → PMF β) :
    discreteTotalVariation (jointPMF p q) (jointPMF p r) =
      ∑' a, (p a).toReal * discreteTotalVariation (q a) (r a) := by
  have hs := pmf_summable_abs_sub (jointPMF p q) (jointPMF p r)
  calc
    discreteTotalVariation (jointPMF p q) (jointPMF p r) =
        (∑' a, (p a).toReal * (∑' b, |(q a b).toReal - (r a b).toReal|)) / 2 := by
      unfold discreteTotalVariation
      rw [hs.tsum_prod]
      simp_rw [jointPMF_apply, ENNReal.toReal_mul, ← mul_sub, abs_mul,
        abs_of_nonneg ENNReal.toReal_nonneg, tsum_mul_left]
    _ = ∑' a, (p a).toReal * discreteTotalVariation (q a) (r a) := by
      rw [← tsum_div_const]
      simp only [discreteTotalVariation, mul_div_assoc]

theorem summable_weighted_totalVariation {α β : Type*} (p : PMF α) (q r : α → PMF β) :
    Summable (fun a => (p a).toReal * discreteTotalVariation (q a) (r a)) := by
  apply (pmf_summable_toReal p).of_nonneg_of_le
  · intro a
    exact mul_nonneg ENNReal.toReal_nonneg (discreteTotalVariation_nonneg _ _)
  · intro a
    exact mul_le_of_le_one_right ENNReal.toReal_nonneg (discreteTotalVariation_le_one _ _)

theorem discreteTotalVariation_joint_le_uniform {α β : Type*}
    (p : PMF α) (q r : α → PMF β) {ε : ℝ}
    (h : ∀ a, discreteTotalVariation (q a) (r a) ≤ ε) :
    discreteTotalVariation (jointPMF p q) (jointPMF p r) ≤ ε := by
  rw [discreteTotalVariation_joint]
  have hs := (summable_weighted_totalVariation p q r).tsum_le_tsum
    (fun a => mul_le_mul_of_nonneg_left (h a) ENNReal.toReal_nonneg)
    ((pmf_summable_toReal p).mul_right ε)
  simpa only [tsum_mul_right, pmf_tsum_toReal, one_mul] using hs

theorem discreteTotalVariation_joint_le_good_event {α β : Type*}
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (p : PMF α) (q r : α → PMF β) (G : Set α) {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ a ∈ G, discreteTotalVariation (q a) (r a) ≤ ε) :
    discreteTotalVariation (jointPMF p q) (jointPMF p r) ≤ p.toMeasure.real Gᶜ + ε := by
  classical
  have hb (a : α) : (p a).toReal * discreteTotalVariation (q a) (r a) ≤
      (p a).toReal * ε + Gᶜ.indicator (fun a => (p a).toReal) a := by
    by_cases ha : a ∈ G
    · rw [Set.indicator_of_notMem (show a ∉ Gᶜ from fun hc => hc ha), add_zero]
      exact mul_le_mul_of_nonneg_left (h a ha) ENNReal.toReal_nonneg
    · rw [Set.indicator_of_mem (show a ∈ Gᶜ from ha)]
      exact (mul_le_of_le_one_right ENNReal.toReal_nonneg (discreteTotalVariation_le_one _ _)).trans
        (le_add_of_nonneg_left (mul_nonneg ENNReal.toReal_nonneg hε))
  rw [discreteTotalVariation_joint]
  have hs := (summable_weighted_totalVariation p q r).tsum_le_tsum hb
    (((pmf_summable_toReal p).mul_right ε).add ((pmf_summable_toReal p).indicator Gᶜ))
  rw [Summable.tsum_add ((pmf_summable_toReal p).mul_right ε)
    ((pmf_summable_toReal p).indicator Gᶜ), tsum_mul_right, pmf_tsum_toReal, one_mul,
    ← pmf_measureReal_eq_tsum] at hs
  exact hs.trans_eq (add_comm _ _)

/-- The discrete outer-measure formulation requires no measurable-space
structure on the marginal type.
-/
theorem discreteTotalVariation_joint_le_of_event_mass {α β : Type*}
    (p : PMF α) (q r : α → PMF β) (G : Set α) {δ ε : ℝ}
    (hprob : ENNReal.ofReal (1 - δ) ≤ p.toOuterMeasure G) (hε : 0 ≤ ε)
    (h : ∀ a ∈ G, discreteTotalVariation (q a) (r a) ≤ ε) :
    discreteTotalVariation (jointPMF p q) (jointPMF p r) ≤ δ + ε := by
  let : MeasurableSpace α := ⊤
  have hG : MeasurableSet G := trivial
  have hm : 1 - δ ≤ p.toMeasure.real G := by
    rw [← PMF.toMeasure_apply_eq_toOuterMeasure_apply p hG] at hprob
    exact (ENNReal.ofReal_le_iff_le_toReal (MeasureTheory.measure_ne_top _ _)).mp hprob
  have hc : p.toMeasure.real Gᶜ ≤ δ := by
    rw [MeasureTheory.measureReal_compl hG, MeasureTheory.probReal_univ]
    linarith
  exact (discreteTotalVariation_joint_le_good_event p q r G hε h).trans (add_le_add hc le_rfl)

end GeometricGaussianLHL
end

end JointVariation

section ReweightedVariation

/-!
## Stability of normalized weights on a common truncation set

A single unknown normalization factor is controlled by the probabilities
of the truncation set. Exponential comparisons of the unnormalized weights
then give a linear total-variation bound, including when the error is large.
-/

noncomputable section

open MeasureTheory

namespace GeometricGaussianLHL

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]

theorem pmf_measureReal_add_compl (p : PMF α) (E : Set α) :
    p.toMeasure.real E + p.toMeasure.real Eᶜ = 1 := by
  classical
  rw [pmf_measureReal_eq_tsum, pmf_measureReal_eq_tsum,
    ← Summable.tsum_add ((pmf_summable_toReal p).indicator E) ((pmf_summable_toReal p).indicator Eᶜ)]
  calc
    _ = ∑' x, (p x).toReal := by
      apply tsum_congr
      intro x
      by_cases hx : x ∈ E <;> simp [Set.indicator, hx]
    _ = 1 := pmf_tsum_toReal p

theorem pmf_scaled_event_le (p q : PMF α) (E : Set α) (a b : ℝ)
    (h : ∀ x ∈ E, a * (p x).toReal ≤ b * (q x).toReal) :
    a * p.toMeasure.real E ≤ b * q.toMeasure.real E := by
  classical
  rw [pmf_measureReal_eq_tsum, pmf_measureReal_eq_tsum, ← tsum_mul_left, ← tsum_mul_left]
  apply (((pmf_summable_toReal p).indicator E).mul_left a).tsum_le_tsum _
    (((pmf_summable_toReal q).indicator E).mul_left b)
  intro x
  by_cases hx : x ∈ E
  · simpa only [Set.indicator_of_mem hx] using h x hx
  · simp only [Set.indicator_of_notMem hx, mul_zero, le_refl]

theorem discreteTotalVariation_reweight_bound (p q : PMF α) (E : Set α)
    {ξ a c : ℝ} (hξ : 0 ≤ ξ) (hξ1 : ξ < 1) (ha : 0 ≤ a) (hc : 0 < c)
    (hp : p.toMeasure.real Eᶜ ≤ ξ) (hq : q.toMeasure.real Eᶜ ≤ ξ)
    (hweight : ∀ x ∈ E,
      (p x).toReal ≤ Real.exp a * c * (q x).toReal ∧
      c * (q x).toReal ≤ Real.exp a * (p x).toReal) :
    discreteTotalVariation p q ≤ ξ + (Real.exp (2 * a) / (1 - ξ) - 1) := by
  let z := Real.exp a
  have hz : 0 < z := Real.exp_pos a
  have hz1 : 1 ≤ z := Real.one_le_exp_iff.mpr ha
  have hk : 0 < 1 - ξ := by linarith
  have hpE := pmf_measureReal_add_compl p E
  have hqE := pmf_measureReal_add_compl q E
  have hp0 : 0 ≤ p.toMeasure.real Eᶜ := ENNReal.toReal_nonneg
  have hq0 : 0 ≤ q.toMeasure.real Eᶜ := ENNReal.toReal_nonneg
  have hp1 : p.toMeasure.real E ≤ 1 := by linarith
  have hq1 : q.toMeasure.real E ≤ 1 := by linarith
  have hpmin : 1 - ξ ≤ p.toMeasure.real E := by linarith
  have hqmin : 1 - ξ ≤ q.toMeasure.real E := by linarith
  have hl : p.toMeasure.real E ≤ (z * c) * q.toMeasure.real E := by
    simpa only [one_mul] using pmf_scaled_event_le p q E 1 (z * c)
      (fun x hx => by simpa only [one_mul] using (hweight x hx).1)
  have hu := pmf_scaled_event_le q p E c z (fun x hx => (hweight x hx).2)
  have hclow : 1 - ξ ≤ z * c := hpmin.trans (hl.trans (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hq1 (mul_pos hz hc).le))
  have hcup : c * (1 - ξ) ≤ z :=
    (mul_le_mul_of_nonneg_left hqmin hc.le).trans (hu.trans (by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hp1 hz.le))
  have hR : 1 ≤ z ^ 2 / (1 - ξ) := (le_div_iff₀ hk).mpr (by nlinarith)
  have hratio (x : α) (hx : x ∈ E) :
      (p x).toReal ≤ (z ^ 2 / (1 - ξ)) * (q x).toReal ∧
      (q x).toReal ≤ (z ^ 2 / (1 - ξ)) * (p x).toReal := by
    have hq0x : 0 ≤ (q x).toReal := ENNReal.toReal_nonneg
    obtain ⟨h₁, h₂⟩ := hweight x hx
    change (p x).toReal ≤ z * c * (q x).toReal at h₁
    change c * (q x).toReal ≤ z * (p x).toReal at h₂
    constructor
    · rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hk).mpr
      have h₃ := mul_le_mul_of_nonneg_left h₁ hk.le
      have h₄ := mul_le_mul_of_nonneg_right hcup (mul_nonneg hz.le hq0x)
      nlinarith only [h₃, h₄]
    · rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hk).mpr
      have h₃ := mul_le_mul_of_nonneg_right hclow hq0x
      have h₄ := mul_le_mul_of_nonneg_left h₂ hz.le
      nlinarith only [h₃, h₄]
  have h := discreteTotalVariation_le_of_relative_on p q E hR hp hq hratio
  have he : z ^ 2 = Real.exp (2 * a) := by
    dsimp [z]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rwa [he] at h

theorem exp_le_one_add_two_mul {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    Real.exp t ≤ 1 + 2 * t := by
  have h := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (1 : ℝ))
    (show 0 ≤ 1 - t by linarith) ht (show (1 - t) + t = 1 by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, mul_one, Real.exp_zero] at h
  have h' := mul_le_mul_of_nonneg_left Real.exp_one_lt_three.le ht
  nlinarith

theorem discreteTotalVariation_le_of_reweight_on (p q : PMF α) (E : Set α)
    {ξ a c : ℝ} (hξ : 0 ≤ ξ) (hξhalf : ξ ≤ 1 / 2) (ha : 0 ≤ a) (hc : 0 < c)
    (hp : p.toMeasure.real Eᶜ ≤ ξ) (hq : q.toMeasure.real Eᶜ ≤ ξ)
    (hweight : ∀ x ∈ E,
      (p x).toReal ≤ Real.exp a * c * (q x).toReal ∧
      c * (q x).toReal ≤ Real.exp a * (p x).toReal) :
    discreteTotalVariation p q ≤ 3 * ξ + 8 * a := by
  by_cases ha1 : a ≤ 1 / 2
  · have h := discreteTotalVariation_reweight_bound p q E hξ (by linarith) ha hc hp hq hweight
    have he := exp_le_one_add_two_mul (show 0 ≤ 2 * a by linarith) (show 2 * a ≤ 1 by linarith)
    have hk : 0 < 1 - ξ := by linarith
    have hr : Real.exp (2 * a) / (1 - ξ) ≤ 1 + 2 * ξ + 8 * a := by
      apply (div_le_iff₀ hk).mpr
      nlinarith [mul_nonneg hξ (show 0 ≤ 1 - 2 * ξ by linarith),
        mul_nonneg ha (show 0 ≤ 1 - 2 * ξ by linarith)]
    linarith
  · have h := discreteTotalVariation_le_one p q
    linarith

end GeometricGaussianLHL
end

end ReweightedVariation

section JointEventBudgets

/-!
## Separate exceptional-event budgets

Two good events need not be independent. Their intersection pays the sum of their failure
probabilities. This is the probability-accounting step required for the spectral variant of the
spherical-output corollary.
-/

noncomputable section

open MeasureTheory

namespace GeometricGaussianLHL

theorem pmf_intersection_event_mass {α : Type*} (p : PMF α) (G H : Set α)
    {δG δH : ℝ} (hG : ENNReal.ofReal (1 - δG) ≤ p.toOuterMeasure G)
    (hH : ENNReal.ofReal (1 - δH) ≤ p.toOuterMeasure H) :
    ENNReal.ofReal (1 - (δG + δH)) ≤ p.toOuterMeasure (G ∩ H) := by
  let : MeasurableSpace α := ⊤
  have hm (A : Set α) {δ : ℝ} (hA : ENNReal.ofReal (1 - δ) ≤ p.toOuterMeasure A) :
      1 - δ ≤ p.toMeasure.real A := by
    rw [← PMF.toMeasure_apply_eq_toOuterMeasure_apply p (show MeasurableSet A from trivial)] at hA
    exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mp hA
  have hbG := hm G hG
  have hbH := hm H hH
  have hu := measureReal_union_le (μ := p.toMeasure) Gᶜ Hᶜ
  rw [← Set.compl_inter, probReal_compl_eq_one_sub (show MeasurableSet (G ∩ H) from trivial),
    probReal_compl_eq_one_sub (show MeasurableSet G from trivial),
    probReal_compl_eq_one_sub (show MeasurableSet H from trivial)] at hu
  rw [← PMF.toMeasure_apply_eq_toOuterMeasure_apply p
    (show MeasurableSet (G ∩ H) from trivial)]
  apply ENNReal.ofReal_le_of_le_toReal
  change 1 - (δG + δH) ≤ p.toMeasure.real (G ∩ H)
  linarith

theorem discreteTotalVariation_joint_le_two_events {α β : Type*}
    (p : PMF α) (q r : α → PMF β) (G H : Set α) {δG δH ε : ℝ}
    (hG : ENNReal.ofReal (1 - δG) ≤ p.toOuterMeasure G)
    (hH : ENNReal.ofReal (1 - δH) ≤ p.toOuterMeasure H) (hε : 0 ≤ ε)
    (h : ∀ a ∈ G ∩ H, discreteTotalVariation (q a) (r a) ≤ ε) :
    discreteTotalVariation (jointPMF p q) (jointPMF p r) ≤ δG + δH + ε :=
  discreteTotalVariation_joint_le_of_event_mass p q r (G ∩ H)
    (pmf_intersection_event_mass p G H hG hH) hε h

end GeometricGaussianLHL
end

end JointEventBudgets
