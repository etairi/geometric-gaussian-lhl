import «SIS-to-kSIS».GameBounds
import GeometricGaussianLHL.MatrixApproximation
import GeometricGaussianLHL.CanonicalShaping
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Finite weighted rejection sampling

The executable sampler reads uniform binary words, evaluates only each proposed
weight, and stops after a finite trial budget. Its law, declared arithmetic cost,
and truncation error are proved. A fixed-precision exponential evaluator has
proved accuracy, operand-size bounds, and polynomial arithmetic cost. A binary
approximation of pi has the same guarantees. These compose into Gaussian weight
evaluation for finite rational centers and squared widths. A finite binary-word
sampler has proved acceptance, rejection error, and polynomial cost. Partition
and tail bounds transfer its law to the full scalar Gaussian. The security-budget
wrapper has dyadic accuracy and polynomial arithmetic and output-size bounds.
Independent scalar samples produce stored coefficient columns with total dyadic
error. The initial-matrix sampler computes the exact rational coefficient
variance and has proved arithmetic and output-size bounds.
-/


open GeometricGaussianLHL
namespace SISToKSIS
variable {α γ : Type*}

/-- Read independent trial seeds until a trial accepts, or return the supplied
fallback after the fixed budget is exhausted. -/
def rejectionEval (trial : γ → Option α) (fallback : α) :
    (fuel : ℕ) → (Fin fuel → γ) → α
  | 0, _ => fallback
  | fuel + 1, tape => match trial (tape 0) with
    | none => rejectionEval trial fallback fuel (fun i => tape i.succ)
    | some a => a

/-- The same finite algorithm with declared seed, trial, and loop costs.
The loop charge overestimates the counter's bit cost by its remaining value. -/
def rejectionRun (trial : γ → Costed (Option α)) (coinBits : ℕ) (fallback : α) :
    (fuel : ℕ) → (Fin fuel → γ) → Costed α
  | 0, _ => Costed.pure fallback
  | fuel + 1, tape =>
    let first := trial (tape 0)
    let rest := match first.value with
      | none => rejectionRun trial coinBits fallback fuel (fun i => tape i.succ)
      | some a => Costed.pure a
    ⟨rest.value, coinBits + fuel + 1 + first.steps + rest.steps⟩

theorem rejectionRun_value (trial : γ → Costed (Option α)) (coinBits : ℕ)
    (fallback : α) (fuel : ℕ) (tape : Fin fuel → γ) :
    (rejectionRun trial coinBits fallback fuel tape).value =
      rejectionEval (fun seed => (trial seed).value) fallback fuel tape := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    simp only [rejectionRun, rejectionEval]
    cases h : (trial (tape 0)).value with
    | none => exact ih _
    | some a => rfl

theorem rejectionRun_steps_le (trial : γ → Costed (Option α)) (coinBits : ℕ)
    (fallback : α) {C : ℕ} (hC : ∀ seed, (trial seed).steps ≤ C)
    (fuel : ℕ) (tape : Fin fuel → γ) :
    (rejectionRun trial coinBits fallback fuel tape).steps ≤
      fuel * (coinBits + C + fuel + 1) := by
  induction fuel with
  | zero => simp [rejectionRun, Costed.pure]
  | succ fuel ih =>
    have hfirst := hC (tape 0)
    simp only [rejectionRun]
    cases h : (trial (tape 0)).value with
    | none =>
      have hr := ih (fun i => tape i.succ)
      nlinarith
    | some a =>
      simp only [Costed.pure]
      nlinarith

noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Probability semantics of the bounded trial loop. -/
def rejectionLaw (trial : PMF (Option α)) (fallback : α) : ℕ → PMF α
  | 0 => PMF.pure fallback
  | fuel + 1 => trial.bind (fun result => match result with
    | none => rejectionLaw trial fallback fuel
    | some a => PMF.pure a)

/-- The semantics agrees with the actual finite tape algorithm. -/
theorem rejectionEval_law (coin : PMF γ) (trial : γ → Option α)
    (fallback : α) (fuel : ℕ) :
    (independentProduct (fun _ : Fin fuel => coin)).map
        (rejectionEval trial fallback fuel) =
      rejectionLaw (coin.map trial) fallback fuel := by
  induction fuel with
  | zero => exact PMF.map_const _ _
  | succ fuel ih =>
    rw [← independentProduct_cons, PMF.map_comp]
    simp only [jointPMF, PMF.map_bind, PMF.map_comp, Function.comp_def,
      rejectionLaw, PMF.bind_map]
    congr 1
    funext seed
    cases h : trial seed with
    | none => simpa [rejectionEval, Fin.consEquiv, h] using ih
    | some a =>
      simp only [rejectionEval, Fin.consEquiv, Equiv.coe_fn_mk, Fin.cons_zero, h]
      exact PMF.map_const _ _

theorem rejectionLaw_succ_apply [Fintype α] (trial : PMF (Option α))
    (fallback : α) (fuel : ℕ) (a : α) :
    rejectionLaw trial fallback (fuel + 1) a =
      trial (some a) + trial none * rejectionLaw trial fallback fuel a := by
  classical
  simp [rejectionLaw, PMF.bind_apply, tsum_fintype, Fintype.sum_option, PMF.pure_apply,
    mul_ite, add_comm]

/-- Exact mixture after a finite number of trials. The accuracy conclusion
below charges only the event that every trial rejects. -/
theorem rejectionLaw_toReal [Fintype α] (trial : PMF (Option α))
    (fallback : α) (target : PMF α)
    (htarget : ∀ a, (trial (some a)).toReal = (1 - (trial none).toReal) * (target a).toReal)
    (fuel : ℕ) (a : α) :
    (rejectionLaw trial fallback fuel a).toReal =
      (1 - (trial none).toReal ^ fuel) * (target a).toReal +
        (trial none).toReal ^ fuel * (PMF.pure fallback a).toReal := by
  induction fuel with
  | zero => simp [rejectionLaw]
  | succ fuel ih =>
    rw [rejectionLaw_succ_apply, ENNReal.toReal_add (trial.apply_ne_top _)
      (ENNReal.mul_ne_top (trial.apply_ne_top _) ((rejectionLaw trial fallback fuel).apply_ne_top _)),
      ENNReal.toReal_mul, htarget, ih, pow_succ]
    ring

theorem rejectionLaw_error [Fintype α] (trial : PMF (Option α))
    (fallback : α) (target : PMF α)
    (htarget : ∀ a, (trial (some a)).toReal = (1 - (trial none).toReal) * (target a).toReal)
    (fuel : ℕ) :
    discreteTotalVariation (rejectionLaw trial fallback fuel) target ≤ (trial none).toReal ^ fuel := by
  have he : discreteTotalVariation (rejectionLaw trial fallback fuel) target =
      (trial none).toReal ^ fuel * discreteTotalVariation (PMF.pure fallback) target := by
    unfold discreteTotalVariation
    simp_rw [rejectionLaw_toReal trial fallback target htarget fuel]
    have hpoint (a : α) :
        |(1 - (trial none).toReal ^ fuel) * (target a).toReal +
          (trial none).toReal ^ fuel * (PMF.pure fallback a).toReal - (target a).toReal| =
        (trial none).toReal ^ fuel * |(PMF.pure fallback a).toReal - (target a).toReal| := by
      rw [show (1 - (trial none).toReal ^ fuel) * (target a).toReal +
        (trial none).toReal ^ fuel * (PMF.pure fallback a).toReal - (target a).toReal =
        (trial none).toReal ^ fuel * ((PMF.pure fallback a).toReal - (target a).toReal) by ring,
        abs_mul, abs_of_nonneg (by positivity : 0 ≤ (trial none).toReal ^ fuel)]
    simp_rw [hpoint]
    rw [tsum_mul_left, mul_div_assoc]
  rw [he]
  exact mul_le_of_le_one_right (by positivity) (discreteTotalVariation_le_one _ _)

end
end SISToKSIS

open GeometricGaussianLHL
open scoped ENNReal
namespace SISToKSIS

/-- One integer-threshold acceptance test. No table of all weights is evaluated. -/
def weightedTrial {N D : ℕ} (weight : Fin N → ℕ) (seed : Fin N × Fin D) : Option (Fin N) :=
  if seed.2.val < weight seed.1 then some seed.1 else none

def weightedTrialRun {N D : ℕ} (weight : Fin N → Costed ℕ)
    (seed : Fin N × Fin D) : Costed (Option (Fin N)) :=
  let w := weight seed.1
  ⟨if seed.2.val < w.value then some seed.1 else none,
    w.steps + seed.2.val.size + w.value.size + 1⟩

@[simp] theorem weightedTrialRun_value {N D : ℕ} (weight : Fin N → Costed ℕ)
    (seed : Fin N × Fin D) :
    (weightedTrialRun weight seed).value = weightedTrial (fun i => (weight i).value) seed := rfl

theorem weightedTrialRun_steps_le {N bits C : ℕ} (weight : Fin N → Costed ℕ)
    (hcost : ∀ i, (weight i).steps ≤ C) (hweight : ∀ i, (weight i).value ≤ 2 ^ bits)
    (seed : Fin N × Fin (2 ^ bits)) :
    (weightedTrialRun weight seed).steps ≤ C + 2 * bits + 2 := by
  have hseed : seed.2.val.size ≤ bits := Nat.size_le.mpr seed.2.isLt
  have hw : (weight seed.1).value.size ≤ bits + 1 := by
    apply Nat.size_le.mpr
    exact (hweight seed.1).trans_lt (by
      rw [pow_succ]
      have : 0 < 2 ^ bits := by positivity
      omega)
  have hc := hcost seed.1
  change (weight seed.1).steps + seed.2.val.size + (weight seed.1).value.size + 1 ≤ _
  omega

noncomputable section
set_option backward.isDefEq.respectTransparency false

def weightedTrialLaw {N D : ℕ} [NeZero N] [NeZero D] (weight : Fin N → ℕ) :
    PMF (Option (Fin N)) :=
  (jointPMF (PMF.uniformOfFintype (Fin N))
    (fun _ => PMF.uniformOfFintype (Fin D))).map (weightedTrial weight)

theorem weightedTrialLaw_some {N D : ℕ} [NeZero N] [NeZero D]
    (weight : Fin N → ℕ) (hweight : ∀ i, weight i ≤ D) (i : Fin N) :
    weightedTrialLaw (D := D) weight (some i) =
      (weight i : ℝ≥0∞) * ((N : ℝ≥0∞)⁻¹ * (D : ℝ≥0∞)⁻¹) := by
  classical
  letI : DecidableEq (Option (Fin N)) := Classical.decEq _
  rw [weightedTrialLaw, PMF.map_apply, tsum_fintype, Fintype.sum_prod_type]
  have he (j : Fin N) :
      (∑ c : Fin D, if some i = weightedTrial weight (j, c) then
        jointPMF (PMF.uniformOfFintype (Fin N))
          (fun _ => PMF.uniformOfFintype (Fin D)) (j, c) else 0) =
      if i = j then (weight j : ℝ≥0∞) * ((N : ℝ≥0∞)⁻¹ * (D : ℝ≥0∞)⁻¹) else 0 := by
    by_cases hij : i = j
    · subst j
      simp only [jointPMF_apply, PMF.uniformOfFintype_apply, Fintype.card_fin]
      have hpoint (c : Fin D) :
          (if some i = weightedTrial weight (i, c) then
            (N : ℝ≥0∞)⁻¹ * (D : ℝ≥0∞)⁻¹ else 0) =
          if c.val < weight i then (N : ℝ≥0∞)⁻¹ * (D : ℝ≥0∞)⁻¹ else 0 := by
        by_cases hc : c.val < weight i <;> simp [weightedTrial, hc]
      simp_rw [hpoint]
      rw [← Finset.sum_filter]
      simp [Fin.card_filter_val_lt, Nat.min_eq_right (hweight i)]
    · simp only [ite_eq_right hij]
      apply Finset.sum_eq_zero
      intro c _
      by_cases hc : c.val < weight j <;> simp [weightedTrial, hc, hij]
  calc
    _ = ∑ j : Fin N, if i = j then
        (weight j : ℝ≥0∞) * ((N : ℝ≥0∞)⁻¹ * (D : ℝ≥0∞)⁻¹) else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      exact he j
    _ = _ := by simp

def finiteWeightLaw {N : ℕ} (weight : Fin N → ℕ) (hweight : 0 < ∑ i, weight i) :
    PMF (Fin N) :=
  PMF.ofFintype (fun i => (weight i : ℝ≥0∞) / (∑ j, weight j : ℕ)) (by
    simp only [div_eq_mul_inv, ← Finset.sum_mul, ← Nat.cast_sum]
    rw [← div_eq_mul_inv]
    exact ENNReal.div_self (by exact_mod_cast hweight.ne') (by simp))

@[simp] theorem finiteWeightLaw_apply {N : ℕ} (weight : Fin N → ℕ)
    (hweight : 0 < ∑ i, weight i) (i : Fin N) :
    finiteWeightLaw weight hweight i = (weight i : ℝ≥0∞) / (∑ j, weight j : ℕ) := rfl

theorem weightedTrialLaw_some_toReal {N D : ℕ} [NeZero N] [NeZero D]
    (weight : Fin N → ℕ) (hweight : ∀ i, weight i ≤ D) (i : Fin N) :
    (weightedTrialLaw (D := D) weight (some i)).toReal =
      (weight i : ℝ) / ((N : ℝ) * D) := by
  rw [weightedTrialLaw_some weight hweight, ENNReal.toReal_mul, ENNReal.toReal_mul]
  simp [div_eq_mul_inv, mul_inv_rev, mul_comm]

theorem weightedTrialLaw_reject_toReal {N D : ℕ} [NeZero N] [NeZero D]
    (weight : Fin N → ℕ) (hweight : ∀ i, weight i ≤ D) :
    (weightedTrialLaw (D := D) weight none).toReal =
      1 - (∑ i, weight i : ℕ) / ((N : ℝ) * D) := by
  have hs := pmf_tsum_toReal (weightedTrialLaw (D := D) weight)
  rw [tsum_fintype, Fintype.sum_option] at hs
  simp_rw [weightedTrialLaw_some_toReal weight hweight] at hs
  rw [← Finset.sum_div, ← Nat.cast_sum] at hs
  linarith

theorem weightedTrialLaw_target {N D : ℕ} [NeZero N] [NeZero D]
    (weight : Fin N → ℕ) (hweight : ∀ i, weight i ≤ D)
    (hpos : 0 < ∑ i, weight i) (i : Fin N) :
    (weightedTrialLaw (D := D) weight (some i)).toReal =
      (1 - (weightedTrialLaw (D := D) weight none).toReal) *
        (finiteWeightLaw weight hpos i).toReal := by
  rw [weightedTrialLaw_some_toReal weight hweight, weightedTrialLaw_reject_toReal weight hweight,
    finiteWeightLaw_apply, ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast]
  have hw : ((∑ j, weight j : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
  field_simp
  ring

end
end SISToKSIS

noncomputable section
open GeometricGaussianLHL
namespace SISToKSIS

/-- A block of `L` trials reduces failure by at least a factor of two whenever
its expected acceptance count is at least one. -/
theorem rejection_failure_dyadic {p : ℝ} (hp : 0 ≤ p) (hpone : p ≤ 1)
    {L : ℕ} (hL : 1 ≤ (L : ℝ) * p) (t : ℕ) :
    (1 - p) ^ (L * t) ≤ (1 / 2 : ℝ) ^ t := by
  rw [pow_mul]
  apply pow_le_pow_left₀ (pow_nonneg (sub_nonneg.mpr hpone) L)
  have h := one_sub_pow_le_reciprocal hp hpone L
  exact h.trans ((one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2)
    (by linarith : (2 : ℝ) ≤ 1 + (L : ℝ) * p)))

end SISToKSIS
end

open GeometricGaussianLHL
namespace SISToKSIS

/-- A bounded weighted sampler from pairs of uniform binary words. -/
def dyadicRejectionRun {proposalBits acceptanceBits : ℕ}
    (weight : Fin (2 ^ proposalBits) → Costed ℕ) (fallback : Fin (2 ^ proposalBits))
    (fuel : ℕ) (tape : Fin fuel → Fin (2 ^ proposalBits) × Fin (2 ^ acceptanceBits)) :
    Costed (Fin (2 ^ proposalBits)) :=
  rejectionRun (weightedTrialRun weight) (proposalBits + acceptanceBits) fallback fuel tape

theorem dyadicRejectionRun_steps_le {proposalBits acceptanceBits C : ℕ}
    (weight : Fin (2 ^ proposalBits) → Costed ℕ) (fallback : Fin (2 ^ proposalBits))
    (hcost : ∀ i, (weight i).steps ≤ C)
    (hweight : ∀ i, (weight i).value ≤ 2 ^ acceptanceBits)
    (fuel : ℕ) (tape : Fin fuel → Fin (2 ^ proposalBits) × Fin (2 ^ acceptanceBits)) :
    (dyadicRejectionRun weight fallback fuel tape).steps ≤
      fuel * (proposalBits + 3 * acceptanceBits + C + fuel + 3) := by
  have h := rejectionRun_steps_le (weightedTrialRun weight)
    (proposalBits + acceptanceBits) fallback
    (weightedTrialRun_steps_le weight hcost hweight) fuel tape
  unfold dyadicRejectionRun
  convert h using 1
  ring

noncomputable section
set_option backward.isDefEq.respectTransparency false

def dyadicRejectionLaw {proposalBits acceptanceBits : ℕ}
    (weight : Fin (2 ^ proposalBits) → Costed ℕ) (fallback : Fin (2 ^ proposalBits))
    (fuel : ℕ) : PMF (Fin (2 ^ proposalBits)) :=
  (independentProduct (fun _ : Fin fuel =>
    jointPMF (PMF.uniformOfFintype (Fin (2 ^ proposalBits)))
      (fun _ => PMF.uniformOfFintype (Fin (2 ^ acceptanceBits))))).map
    (fun tape => (dyadicRejectionRun weight fallback fuel tape).value)

theorem dyadicRejectionLaw_eq {proposalBits acceptanceBits : ℕ}
    (weight : Fin (2 ^ proposalBits) → Costed ℕ) (fallback : Fin (2 ^ proposalBits))
    (fuel : ℕ) :
    dyadicRejectionLaw (acceptanceBits := acceptanceBits) weight fallback fuel =
      rejectionLaw (weightedTrialLaw (D := 2 ^ acceptanceBits) (fun i => (weight i).value))
        fallback fuel := by
  unfold dyadicRejectionLaw dyadicRejectionRun
  simp_rw [rejectionRun_value, weightedTrialRun_value]
  exact rejectionEval_law _ _ _ _

/-- Exact truncation error relative to the normalized integer weights. -/
theorem dyadicRejectionLaw_error {proposalBits acceptanceBits : ℕ}
    (weight : Fin (2 ^ proposalBits) → Costed ℕ) (fallback : Fin (2 ^ proposalBits))
    (hweight : ∀ i, (weight i).value ≤ 2 ^ acceptanceBits)
    (hpos : 0 < ∑ i, (weight i).value) (fuel : ℕ) :
    discreteTotalVariation (dyadicRejectionLaw (acceptanceBits := acceptanceBits) weight fallback fuel)
      (finiteWeightLaw (fun i => (weight i).value) hpos) ≤
      (1 - ((∑ i, (weight i).value : ℕ) : ℝ) /
        ((2 ^ proposalBits : ℝ) * 2 ^ acceptanceBits)) ^ fuel := by
  rw [dyadicRejectionLaw_eq]
  have h := rejectionLaw_error (weightedTrialLaw (D := 2 ^ acceptanceBits)
    (fun i => (weight i).value)) fallback (finiteWeightLaw _ hpos)
    (weightedTrialLaw_target _ hweight hpos) fuel
  simpa only [weightedTrialLaw_reject_toReal _ hweight, Nat.cast_pow, Nat.cast_ofNat] using h

/-- Polynomially many trials suffice when the reciprocal acceptance bound
`L` is polynomial. The loop uses exactly the displayed finite trial budget. -/
theorem dyadicRejectionLaw_error_of_budget {proposalBits acceptanceBits L : ℕ}
    (weight : Fin (2 ^ proposalBits) → Costed ℕ) (fallback : Fin (2 ^ proposalBits))
    (hweight : ∀ i, (weight i).value ≤ 2 ^ acceptanceBits)
    (hpos : 0 < ∑ i, (weight i).value)
    (haccept : 2 ^ proposalBits * 2 ^ acceptanceBits ≤ L * ∑ i, (weight i).value)
    (t : ℕ) :
    discreteTotalVariation
      (dyadicRejectionLaw (acceptanceBits := acceptanceBits) weight fallback (L * t))
      (finiteWeightLaw (fun i => (weight i).value) hpos) ≤ (1 / 2 : ℝ) ^ t := by
  let p : ℝ := ((∑ i, (weight i).value : ℕ) : ℝ) /
    ((2 ^ proposalBits : ℝ) * 2 ^ acceptanceBits)
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have hpone : p ≤ 1 := by
    have h := weightedTrialLaw_reject_toReal (D := 2 ^ acceptanceBits)
      (fun i => (weight i).value) hweight
    have hn := ENNReal.toReal_nonneg (a := weightedTrialLaw (D := 2 ^ acceptanceBits)
      (fun i => (weight i).value) none)
    simp only [Nat.cast_pow, Nat.cast_ofNat] at h
    dsimp [p]
    linarith
  have hL : 1 ≤ (L : ℝ) * p := by
    dsimp [p]
    rw [← mul_div_assoc]
    apply (one_le_div (by positivity : (0 : ℝ) < 2 ^ proposalBits * 2 ^ acceptanceBits)).mpr
    exact_mod_cast haccept
  exact (dyadicRejectionLaw_error weight fallback hweight hpos (L * t)).trans
    (rejection_failure_dyadic hp hpone hL t)

end
end SISToKSIS

open GeometricGaussianLHL
namespace SISToKSIS

/-- One rounded square with the dyadic denominator kept fixed. -/
def dyadicSquareRun (precision u : ℕ) : Costed ℕ :=
  (Costed.charge (precision + 1) (2 ^ precision)).bind (fun D =>
    (costedNatMul u u).bind (fun v => costedNatDiv v D))

@[simp] theorem dyadicSquareRun_value (precision u : ℕ) :
    (dyadicSquareRun precision u).value = u * u / 2 ^ precision := rfl

/-- Every square is rounded before the next iteration. -/
def dyadicSquareIterate (precision u : ℕ) : ℕ → Costed ℕ
  | 0 => Costed.pure u
  | r + 1 => (dyadicSquareIterate precision u r).bind (fun v =>
    let step := dyadicSquareRun precision v
    ⟨step.value, step.steps + r + 1⟩)

theorem nat_size_le_dyadic_bound {u p : ℕ} (hu : u ≤ 2 ^ p) : u.size ≤ p + 1 := by
  apply Nat.size_le.mpr
  apply hu.trans_lt
  rw [pow_succ]
  have : 0 < 2 ^ p := by positivity
  omega

theorem dyadicSquareRun_bound {p u : ℕ} (hu : u ≤ 2 ^ p) :
    (dyadicSquareRun p u).value ≤ 2 ^ p := by
  have h : u * u / 2 ^ p ≤ (2 ^ p) * (2 ^ p) / 2 ^ p :=
    Nat.div_le_div_right (Nat.mul_self_le_mul_self hu)
  simpa only [dyadicSquareRun_value, Nat.mul_div_cancel_left _ (by positivity : 0 < 2 ^ p)] using h

theorem dyadicSquareRun_steps_le {p u : ℕ} (hu : u ≤ 2 ^ p) :
    (dyadicSquareRun p u).steps ≤ 3 * (3 * p + 3) ^ 2 := by
  have hsize := nat_size_le_dyadic_bound hu
  have hden := nat_size_le_dyadic_bound (Nat.le_refl (2 ^ p))
  have hprod : u * u ≤ 2 ^ (2 * p) := by
    simpa only [two_mul, pow_add] using Nat.mul_self_le_mul_self hu
  have hprodsize := nat_size_le_dyadic_bound hprod
  change p + 1 + ((u.size + u.size + 1) ^ 2 + ((u * u).size + (2 ^ p).size + 1) ^ 2) ≤ _
  have h₁ := Nat.pow_le_pow_left (by omega : u.size + u.size + 1 ≤ 3 * p + 3) 2
  have h₂ := Nat.pow_le_pow_left
    (by omega : (u * u).size + (2 ^ p).size + 1 ≤ 3 * p + 3) 2
  nlinarith

theorem dyadicSquareIterate_bound {p u : ℕ} (hu : u ≤ 2 ^ p) (r : ℕ) :
    (dyadicSquareIterate p u r).value ≤ 2 ^ p := by
  induction r with
  | zero => exact hu
  | succ r ih => exact dyadicSquareRun_bound ih

theorem dyadicSquareIterate_size {p u : ℕ} (hu : u ≤ 2 ^ p) (r : ℕ) :
    (dyadicSquareIterate p u r).value.size ≤ p + 1 :=
  nat_size_le_dyadic_bound (dyadicSquareIterate_bound hu r)

theorem dyadicSquareIterate_steps_le {p u : ℕ} (hu : u ≤ 2 ^ p) (r : ℕ) :
    (dyadicSquareIterate p u r).steps ≤ r * (3 * (3 * p + 3) ^ 2 + r + 1) := by
  induction r with
  | zero => simp [dyadicSquareIterate, Costed.pure]
  | succ r ih =>
    have hs := dyadicSquareRun_steps_le (dyadicSquareIterate_bound hu r)
    change (dyadicSquareIterate p u r).steps +
      ((dyadicSquareRun p (dyadicSquareIterate p u r).value).steps + r + 1) ≤ _
    nlinarith

noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The only rounding error introduced by one integer division. -/
theorem natural_division_error (a D : ℕ) (hD : 0 < D) :
    |((a / D : ℕ) : ℝ) - (a : ℝ) / D| ≤ 1 := by
  have hrem : ((a % D : ℕ) : ℝ) < D := by exact_mod_cast Nat.mod_lt a hD
  have he : ((a % D : ℕ) : ℝ) + (D : ℝ) * (a / D : ℕ) = a := by
    exact_mod_cast Nat.mod_add_div a D
  have hrem0 : (0 : ℝ) ≤ (a % D : ℕ) := by positivity
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hid : ((a / D : ℕ) : ℝ) - (a : ℝ) / D = -((a % D : ℕ) : ℝ) / D := by
    apply (eq_div_iff hDR.ne').mpr
    rw [sub_mul, div_mul_cancel₀ _ hDR.ne']
    nlinarith
  rw [hid, abs_div, abs_neg, abs_of_nonneg hrem0, abs_of_pos hDR]
  exact (div_le_one hDR).mpr hrem.le

theorem dyadicSquareRun_error (p u : ℕ) :
    |((dyadicSquareRun p u).value : ℝ) / (2 : ℝ) ^ p -
      ((u : ℝ) / (2 : ℝ) ^ p) ^ 2| ≤ 1 / (2 : ℝ) ^ p := by
  have h := natural_division_error (u * u) (2 ^ p) (by positivity)
  have he : ((dyadicSquareRun p u).value : ℝ) / (2 : ℝ) ^ p -
      ((u : ℝ) / (2 : ℝ) ^ p) ^ 2 =
      (((u * u / 2 ^ p : ℕ) : ℝ) - (u * u : ℕ) / (2 ^ p : ℕ)) / (2 : ℝ) ^ p := by
    simp only [dyadicSquareRun_value, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    field_simp
  rw [he, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ p)]
  exact div_le_div_of_nonneg_right h (by positivity)

/-- Squaring is uniformly Lipschitz on the interval used by the sampler. -/
theorem abs_square_sub_le_two_mul {a b : ℝ}
    (ha : 0 ≤ a) (haone : a ≤ 1) (hb : 0 ≤ b) (hbone : b ≤ 1) :
    |a ^ 2 - b ^ 2| ≤ 2 * |a - b| := by
  rw [sq_sub_sq, abs_mul, abs_of_nonneg (add_nonneg ha hb)]
  nlinarith [abs_nonneg (a - b)]

/-- The total error of the actual rounded integer iteration. -/
theorem dyadicSquareIterate_error {p u : ℕ} (hu : u ≤ 2 ^ p)
    {b ε : ℝ} (hb : 0 ≤ b) (hbone : b ≤ 1)
    (hstart : |(u : ℝ) / (2 : ℝ) ^ p - b| ≤ ε) (r : ℕ) :
    |((dyadicSquareIterate p u r).value : ℝ) / (2 : ℝ) ^ p - b ^ (2 ^ r)| ≤
      (2 : ℝ) ^ r * ε + ((2 : ℝ) ^ r - 1) / (2 : ℝ) ^ p := by
  induction r with
  | zero => simpa [dyadicSquareIterate, Costed.pure] using hstart
  | succ r ih =>
    let a : ℝ := ((dyadicSquareIterate p u r).value : ℝ) / (2 : ℝ) ^ p
    have ha : 0 ≤ a := by dsimp [a]; positivity
    have haone : a ≤ 1 := by
      apply (div_le_one (by positivity : (0 : ℝ) < 2 ^ p)).mpr
      exact_mod_cast dyadicSquareIterate_bound hu r
    have hbone' : b ^ (2 ^ r) ≤ 1 := pow_le_one₀ hb hbone
    have hsq := abs_square_sub_le_two_mul ha haone (pow_nonneg hb _) hbone'
    have hr := dyadicSquareRun_error p (dyadicSquareIterate p u r).value
    have ht := abs_sub_le
      (((dyadicSquareRun p (dyadicSquareIterate p u r).value).value : ℝ) / (2 : ℝ) ^ p)
      (a ^ 2) ((b ^ (2 ^ r)) ^ 2)
    change |((dyadicSquareRun p (dyadicSquareIterate p u r).value).value : ℝ) /
      (2 : ℝ) ^ p - b ^ (2 ^ (r + 1))| ≤ _
    rw [pow_succ (2 : ℕ), pow_mul, pow_succ (2 : ℝ)]
    dsimp only [a] at hsq ht
    calc
      _ ≤ 1 / (2 : ℝ) ^ p + 2 * ((2 : ℝ) ^ r * ε + ((2 : ℝ) ^ r - 1) / (2 : ℝ) ^ p) :=
        ht.trans (add_le_add hr (hsq.trans (mul_le_mul_of_nonneg_left ih (by norm_num))))
      _ = _ := by ring

end
end SISToKSIS

open GeometricGaussianLHL
namespace SISToKSIS

/-- A natural rational input is represented by numerator `n` and positive
denominator `m`. The seed approximates `1 - (n/m)/2^r`. -/
def exponentialSeedRun (p r n m : ℕ) : Costed ℕ :=
  (Costed.charge (p + r + 2) (2 ^ p, 2 ^ r)).bind (fun scales =>
    (costedNatMul m scales.2).bind (fun M =>
      (Costed.charge (M.size + n.size + 1) (M - n)).bind (fun delta =>
        (costedNatMul scales.1 delta).bind (fun a => costedNatDiv a M))))

@[simp] theorem exponentialSeedRun_value (p r n m : ℕ) :
    (exponentialSeedRun p r n m).value = 2 ^ p * (m * 2 ^ r - n) / (m * 2 ^ r) := rfl

theorem exponentialSeedRun_bound (p r n m : ℕ) (hm : 0 < m) :
    (exponentialSeedRun p r n m).value ≤ 2 ^ p := by
  have hM : 0 < m * 2 ^ r := by positivity
  have h := Nat.div_le_div_right (c := m * 2 ^ r) (Nat.mul_le_mul_left (2 ^ p) (Nat.sub_le (m * 2 ^ r) n))
  simpa only [exponentialSeedRun_value, Nat.mul_div_cancel _ hM] using h

theorem natural_mul_size_le (a b : ℕ) : (a * b).size ≤ a.size + b.size + 1 := by
  simpa only [Int.natAbs_mul, Int.natAbs_natCast] using
    integer_mul_size_le (a : ℤ) (b : ℤ) a.size b.size le_rfl le_rfl

/-- Every operand in the seed computation has a polynomial bit bound. -/
theorem exponentialSeedRun_operand_sizes (p r n m : ℕ) :
    (m * 2 ^ r).size ≤ n.size + m.size + p + r + 4 ∧
    (m * 2 ^ r - n).size ≤ n.size + m.size + p + r + 4 ∧
    (2 ^ p * (m * 2 ^ r - n)).size ≤ n.size + m.size + p + r + 4 := by
  have hM := natural_mul_size_le m (2 ^ r)
  have hdelta := Nat.size_le_size (Nat.sub_le (m * 2 ^ r) n)
  have ha := natural_mul_size_le (2 ^ p) (m * 2 ^ r - n)
  simp only [Nat.size_pow] at hM ha
  omega

theorem exponentialSeedRun_steps_le (p r n m : ℕ) :
    (exponentialSeedRun p r n m).steps ≤
      5 * (2 * (n.size + m.size + p + r + 4) + 1) ^ 2 := by
  let E := n.size + m.size + p + r + 4
  let M := m * 2 ^ r
  obtain ⟨hM, hdelta, ha⟩ := exponentialSeedRun_operand_sizes p r n m
  have hpowP : (2 ^ p).size ≤ E := by simp only [Nat.size_pow]; dsimp [E]; omega
  have hpowR : (2 ^ r).size ≤ E := by simp only [Nat.size_pow]; dsimp [E]; omega
  have hm : m.size ≤ E := by dsimp [E]; omega
  have hn : n.size ≤ E := by dsimp [E]; omega
  have h₁ := Nat.pow_le_pow_left (by omega : m.size + (2 ^ r).size + 1 ≤ 2 * E + 1) 2
  have h₂ := Nat.pow_le_pow_left
    (by omega : (2 ^ p).size + (m * 2 ^ r - n).size + 1 ≤ 2 * E + 1) 2
  have h₃ := Nat.pow_le_pow_left
    (by omega : (2 ^ p * (m * 2 ^ r - n)).size + (m * 2 ^ r).size + 1 ≤ 2 * E + 1) 2
  have hlin : 2 * E + 1 ≤ (2 * E + 1) ^ 2 := by nlinarith
  have h₄ : (m * 2 ^ r).size + n.size + 1 ≤ (2 * E + 1) ^ 2 := by omega
  have h₅ : p + r + 2 ≤ (2 * E + 1) ^ 2 := by dsimp [E] at *; omega
  change p + r + 2 + ((m.size + (2 ^ r).size + 1) ^ 2 +
    ((M.size + n.size + 1) + (( (2 ^ p).size + (M - n).size + 1) ^ 2 +
      ((2 ^ p * (M - n)).size + M.size + 1) ^ 2))) ≤ _
  dsimp only [M, E] at *
  omega

noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem exponentialSeedRun_error (p r n m : ℕ) (hm : 0 < m) (hn : n ≤ m * 2 ^ r) :
    |((exponentialSeedRun p r n m).value : ℝ) / (2 : ℝ) ^ p -
      (1 - (n : ℝ) / m / (2 : ℝ) ^ r)| ≤ 1 / (2 : ℝ) ^ p := by
  have hM : 0 < m * 2 ^ r := by positivity
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have he : 1 - (n : ℝ) / m / (2 : ℝ) ^ r =
      ((2 ^ p * (m * 2 ^ r - n) : ℕ) : ℝ) / (m * 2 ^ r : ℕ) / (2 : ℝ) ^ p := by
    simp only [Nat.cast_mul, Nat.cast_sub hn, Nat.cast_pow, Nat.cast_ofNat]
    field_simp
  rw [he, ← sub_div, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ p)]
  exact div_le_div_of_nonneg_right
    (natural_division_error (2 ^ p * (m * 2 ^ r - n)) (m * 2 ^ r) hM) (by positivity)

end
end SISToKSIS

open GeometricGaussianLHL
namespace SISToKSIS

def exponentialRounds (t : ℕ) : ℕ := 4 * (t + 1)
def exponentialPrecision (t : ℕ) : ℕ := exponentialRounds t + t + 4

/-- Compute an integer acceptance weight for `exp(-n/m)`, with a denominator
specified by `exponentialPrecision`. All arithmetic uses finite integers. -/
def exponentialWeightRun (n m t : ℕ) : Costed ℕ :=
  (Costed.charge (20 * (t + 5) ^ 2) (exponentialRounds t, exponentialPrecision t)).bind
    (fun scales => (costedNatMul (t + 1) m).bind (fun bound =>
      (Costed.charge (bound.size + n.size + 1) (decide (bound ≤ n))).bind (fun tail =>
        if tail then Costed.pure 0 else
          (exponentialSeedRun scales.2 scales.1 n m).bind
            (fun seed => dyadicSquareIterate scales.2 seed scales.1))))

@[simp] theorem exponentialWeightRun_value (n m t : ℕ) :
    (exponentialWeightRun n m t).value =
      if (t + 1) * m ≤ n then 0 else
        (dyadicSquareIterate (exponentialPrecision t)
          (exponentialSeedRun (exponentialPrecision t) (exponentialRounds t) n m).value
          (exponentialRounds t)).value := by
  by_cases htail : (t + 1) * m ≤ n <;>
    simp [exponentialWeightRun, Costed.charge, costedNatMul, Costed.pure, htail]

theorem exponentialWeightRun_bound (n m t : ℕ) (hm : 0 < m) :
    (exponentialWeightRun n m t).value ≤ 2 ^ exponentialPrecision t := by
  rw [exponentialWeightRun_value]
  split_ifs
  · exact Nat.zero_le _
  · exact dyadicSquareIterate_bound (exponentialSeedRun_bound _ _ _ _ hm) _

theorem exponentialWeightRun_size (n m t : ℕ) (hm : 0 < m) :
    (exponentialWeightRun n m t).value.size ≤ exponentialPrecision t + 1 :=
  nat_size_le_dyadic_bound (exponentialWeightRun_bound n m t hm)

noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The rational seed and rounded iteration approximate the actual exponential. -/
theorem exponential_iteration_error (p r n m : ℕ) (hm : 0 < m) (hn : n ≤ m * 2 ^ r) :
    |((dyadicSquareIterate p (exponentialSeedRun p r n m).value r).value : ℝ) /
        (2 : ℝ) ^ p - Real.exp (-(n : ℝ) / m)| ≤
      ((n : ℝ) / m) ^ 2 / (2 : ℝ) ^ r + 2 * (2 : ℝ) ^ r / (2 : ℝ) ^ p := by
  let x : ℝ := (n : ℝ) / m
  let y : ℝ := x / (2 : ℝ) ^ r
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hy : 0 ≤ y := by dsimp [y]; positivity
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hyone : y ≤ 1 := by
    apply (div_le_one (by positivity : (0 : ℝ) < 2 ^ r)).mpr
    apply (div_le_iff₀ hmR).mpr
    have hnR : (n : ℝ) ≤ (m : ℝ) * (2 : ℝ) ^ r := by exact_mod_cast hn
    nlinarith
  have hexp : |(1 - y) - Real.exp (-y)| ≤ y ^ 2 := by
    have h := Real.norm_exp_sub_one_sub_id_le (x := -y) (by
      simpa only [Real.norm_eq_abs, abs_neg, abs_of_nonneg hy] using hyone)
    rw [show 1 - y - Real.exp (-y) = -(Real.exp (-y) - 1 - -y) by ring, abs_neg]
    simpa only [Real.norm_eq_abs, abs_neg, abs_of_nonneg hy] using h
  have hseed := exponentialSeedRun_error p r n m hm hn
  have hstart : |((exponentialSeedRun p r n m).value : ℝ) / (2 : ℝ) ^ p -
      Real.exp (-y)| ≤ 1 / (2 : ℝ) ^ p + y ^ 2 :=
    (abs_sub_le _ (1 - y) _).trans (add_le_add hseed hexp)
  have hi := dyadicSquareIterate_error (exponentialSeedRun_bound p r n m hm)
    (Real.exp_nonneg (-y)) ((Real.exp_le_one_iff).mpr (by linarith)) hstart r
  have hpow : Real.exp (-y) ^ (2 ^ r) = Real.exp (-x) := by
    rw [← Real.exp_nat_mul]
    congr 1
    dsimp [y]
    push_cast
    field_simp
  rw [hpow] at hi
  rw [neg_div]
  change |((dyadicSquareIterate p (exponentialSeedRun p r n m).value r).value : ℝ) /
    (2 : ℝ) ^ p - Real.exp (-x)| ≤ x ^ 2 / (2 : ℝ) ^ r + 2 * (2 : ℝ) ^ r / (2 : ℝ) ^ p
  apply hi.trans
  dsimp only [y]
  have he : (2 : ℝ) ^ r * (1 / (2 : ℝ) ^ p + (x / (2 : ℝ) ^ r) ^ 2) +
      ((2 : ℝ) ^ r - 1) / (2 : ℝ) ^ p =
      x ^ 2 / (2 : ℝ) ^ r + (2 * (2 : ℝ) ^ r - 1) / (2 : ℝ) ^ p := by
    field_simp
    ring
  rw [he]
  gcongr
  linarith

/-- The concrete iteration and precision budgets achieve the requested error. -/
theorem exponential_precision_error (t : ℕ) {x : ℝ} (hx : 0 ≤ x) (hxt : x ≤ t + 1) :
    x ^ 2 / (2 : ℝ) ^ exponentialRounds t +
      2 * (2 : ℝ) ^ exponentialRounds t / (2 : ℝ) ^ exponentialPrecision t ≤
      1 / (2 : ℝ) ^ t := by
  have htwo : ((t : ℝ) + 1) ≤ (2 : ℝ) ^ t := by
    exact_mod_cast (show t + 1 ≤ 2 ^ t from Nat.lt_two_pow_self)
  have hxpow : x ^ 2 ≤ ((2 : ℝ) ^ t) ^ 2 :=
    (sq_le_sq₀ hx (by positivity)).mpr (hxt.trans htwo)
  have h₁ : x ^ 2 / (2 : ℝ) ^ exponentialRounds t ≤ 1 / (2 : ℝ) ^ (t + 1) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    rw [one_mul]
    calc
      _ ≤ ((2 : ℝ) ^ t) ^ 2 * (2 : ℝ) ^ (t + 1) :=
        mul_le_mul_of_nonneg_right hxpow (by positivity)
      _ = (2 : ℝ) ^ (3 * t + 1) := by
        rw [← pow_mul, ← pow_add]
        congr 1
        omega
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by unfold exponentialRounds; omega)
  have h₂ : 2 * (2 : ℝ) ^ exponentialRounds t / (2 : ℝ) ^ exponentialPrecision t ≤
      1 / (2 : ℝ) ^ (t + 1) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    rw [one_mul, ← pow_succ', ← pow_add]
    exact pow_le_pow_right₀ (by norm_num) (by unfold exponentialPrecision; omega)
  calc
    _ ≤ 1 / (2 : ℝ) ^ (t + 1) + 1 / (2 : ℝ) ^ (t + 1) := add_le_add h₁ h₂
    _ = _ := by rw [pow_succ]; field_simp; ring

theorem exponential_tail_cutoff (t : ℕ) {x : ℝ} (hx : t + 1 ≤ x) :
    Real.exp (-x) ≤ 1 / (2 : ℝ) ^ t := by
  have he : Real.exp (-x) ≤ Real.exp (-(t : ℝ)) := Real.exp_le_exp.mpr (by linarith)
  calc
    _ ≤ _ := he
    _ = Real.exp (-1) ^ t := by rw [← Real.exp_nat_mul]; congr 1; ring
    _ ≤ (1 / 2 : ℝ) ^ t := pow_le_pow_left₀ (Real.exp_nonneg _) Real.exp_neg_one_lt_half.le _
    _ = _ := by simp

/-- Certified finite evaluation of each exponential acceptance weight. -/
theorem exponentialWeightRun_error (n m t : ℕ) (hm : 0 < m) :
    |((exponentialWeightRun n m t).value : ℝ) / (2 : ℝ) ^ exponentialPrecision t -
      Real.exp (-(n : ℝ) / m)| ≤ 1 / (2 : ℝ) ^ t := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  rw [exponentialWeightRun_value]
  split_ifs with htail
  · simpa only [Nat.cast_zero, zero_div, zero_sub, abs_neg, abs_of_pos (Real.exp_pos _), neg_div]
      using exponential_tail_cutoff t ((le_div_iff₀ hmR).mpr (by exact_mod_cast htail))
  · have hxt : (n : ℝ) / m ≤ t + 1 := by
      apply (div_le_iff₀ hmR).mpr
      exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge htail))
    have htn : t + 1 ≤ 2 ^ exponentialRounds t :=
      (show t + 1 ≤ 2 ^ t from Nat.lt_two_pow_self).trans
        (Nat.pow_le_pow_right (by decide : 0 < 2) (by unfold exponentialRounds; omega))
    have hn : n ≤ m * 2 ^ exponentialRounds t := by
      have h := Nat.mul_le_mul_left m htn
      nlinarith [Nat.le_of_lt (Nat.lt_of_not_ge htail)]
    exact (exponential_iteration_error _ _ n m hm hn).trans
      (exponential_precision_error t (by positivity) hxt)

end
end SISToKSIS

open GeometricGaussianLHL
namespace SISToKSIS

theorem exponentialWeightRun_steps_le (n m t : ℕ) (hm : 0 < m) :
    (exponentialWeightRun n m t).steps ≤ 20000 * (n.size + m.size + t + 1) ^ 3 := by
  let B := n.size + m.size + t + 1
  let p := exponentialPrecision t
  let r := exponentialRounds t
  have hB : 1 ≤ B := by dsimp [B]; omega
  have ht : t + 1 ≤ B := by dsimp [B]; omega
  have hnb : n.size ≤ B := by dsimp [B]; omega
  have hmb : m.size ≤ B := by dsimp [B]; omega
  have hr : r ≤ 4 * B := by dsimp [r, exponentialRounds]; omega
  have hp : p ≤ 8 * B := by dsimp [p, exponentialPrecision, exponentialRounds]; omega
  have hE : n.size + m.size + p + r + 4 ≤ 16 * B := by
    dsimp [p, r, exponentialPrecision, exponentialRounds, B]
    omega
  have htsize : (t + 1).size ≤ t + 1 := Nat.size_le.mpr Nat.lt_two_pow_self
  have hboundsize := natural_mul_size_le (t + 1) m
  have hcut : ((t + 1) * m).size ≤ 3 * B := by omega
  have hcmp : ((t + 1) * m).size + n.size + 1 ≤ 5 * B := by omega
  have hsetup := Nat.mul_le_mul_left 20
    (Nat.pow_le_pow_left (by omega : t + 5 ≤ 5 * B) 2)
  have hcutcost := Nat.pow_le_pow_left
    (by omega : (t + 1).size + m.size + 1 ≤ 3 * B) 2
  have hseed : (exponentialSeedRun p r n m).steps ≤ 5 * (33 * B) ^ 2 := by
    apply (exponentialSeedRun_steps_le p r n m).trans
    exact Nat.mul_le_mul_left 5 (Nat.pow_le_pow_left (by omega) 2)
  have hpow := Nat.pow_le_pow_left (by omega : 3 * p + 3 ≤ 27 * B) 2
  have hiter : (dyadicSquareIterate p (exponentialSeedRun p r n m).value r).steps ≤
      4 * B * (3 * (27 * B) ^ 2 + 5 * B) := by
    apply (dyadicSquareIterate_steps_le (exponentialSeedRun_bound p r n m hm) r).trans
    exact Nat.mul_le_mul hr (by omega)
  have hrun : (exponentialWeightRun n m t).steps ≤
      20 * (t + 5) ^ 2 + ((t + 1).size + m.size + 1) ^ 2 +
      (((t + 1) * m).size + n.size + 1) + (exponentialSeedRun p r n m).steps +
      (dyadicSquareIterate p (exponentialSeedRun p r n m).value r).steps := by
    by_cases htail : (t + 1) * m ≤ n
    · simp [exponentialWeightRun, Costed.charge, costedNatMul, Costed.pure, htail]
      omega
    · simp [exponentialWeightRun, Costed.charge, costedNatMul, Costed.pure, htail, p, r]
      omega
  have hB₂ : B ^ 2 ≤ B ^ 3 := Nat.pow_le_pow_right hB (by decide)
  have hB₁ : B ≤ B ^ 3 := by
    simpa only [pow_one] using Nat.pow_le_pow_right hB (show 1 ≤ 3 by decide)
  calc
    _ ≤ 20 * (5 * B) ^ 2 + (3 * B) ^ 2 + 5 * B + 5 * (33 * B) ^ 2 +
        4 * B * (3 * (27 * B) ^ 2 + 5 * B) := by omega
    _ = 8748 * B ^ 3 + 5974 * B ^ 2 + 5 * B := by ring
    _ ≤ 20000 * B ^ 3 := by nlinarith

/-- The evaluator follows the existing finite arithmetic-cost convention. -/
theorem exponentialWeightRun_polynomial :
    Costed.PolynomialTime
      (fun input : ℕ × ℕ => fun t => exponentialWeightRun input.1 input.2 t)
      (fun input => 0 < input.2) (fun input => input.1.size + input.2.size) := by
  refine ⟨20000, 3, ?_⟩
  intro input hvalid t
  exact exponentialWeightRun_steps_le input.1 input.2 t hvalid

end SISToKSIS

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GeometricGaussianLHL
namespace SISToKSIS

/-- Normalization removes an unknown common scale at the cost of at most
one full unnormalized L1 error. -/
theorem finite_scaled_mass_error {α : Type*} [Fintype α] (p q : PMF α)
    {c ε : ℝ} (h : ∀ a, |c * (p a).toReal - (q a).toReal| ≤ ε) :
    discreteTotalVariation p q ≤ (Fintype.card α : ℝ) * ε := by
  have hp : ∑ a, (p a).toReal = 1 := by simpa only [tsum_fintype] using pmf_tsum_toReal p
  have hq : ∑ a, (q a).toReal = 1 := by simpa only [tsum_fintype] using pmf_tsum_toReal q
  have hsum : ∑ a, |c * (p a).toReal - (q a).toReal| ≤ (Fintype.card α : ℝ) * ε := by
    simpa using Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ) => h a)
  have hscale : |c - 1| ≤ (Fintype.card α : ℝ) * ε := by
    have ha := (Finset.abs_sum_le_sum_abs (s := Finset.univ)
      (f := fun a => c * (p a).toReal - (q a).toReal)).trans hsum
    simpa only [Finset.sum_sub_distrib, ← Finset.mul_sum, hp, hq, mul_one] using ha
  have hpoint (a : α) : |(p a).toReal - (q a).toReal| ≤
      |1 - c| * (p a).toReal + |c * (p a).toReal - (q a).toReal| := by
    have ht := abs_sub_le (p a).toReal (c * (p a).toReal) (q a).toReal
    have he : |(p a).toReal - c * (p a).toReal| = |1 - c| * (p a).toReal := by
      rw [show (p a).toReal - c * (p a).toReal = (1 - c) * (p a).toReal by ring,
        abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
    rwa [he] at ht
  have hnorm := Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ) => hpoint a)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, hp, mul_one, abs_sub_comm 1 c] at hnorm
  unfold discreteTotalVariation
  rw [tsum_fintype]
  linarith

/-- Absolute errors of integer weights are divided by the ideal partition
mass, without requiring a relative error at every tail point. -/
theorem finiteWeightLaw_error {N : ℕ} (weight : Fin N → ℕ)
    (hweight : 0 < ∑ i, weight i) (target : PMF (Fin N))
    {D Z ε : ℝ} (hD : 0 < D) (hZ : 0 < Z)
    (h : ∀ i, |(weight i : ℝ) / D - Z * (target i).toReal| ≤ ε) :
    discreteTotalVariation (finiteWeightLaw weight hweight) target ≤ (N : ℝ) * ε / Z := by
  let c : ℝ := ((∑ i, weight i : ℕ) : ℝ) / D / Z
  have hW : (((∑ i, weight i : ℕ) : ℝ)) ≠ 0 := by exact_mod_cast hweight.ne'
  have hpoint (i : Fin N) :
      |c * (finiteWeightLaw weight hweight i).toReal - (target i).toReal| ≤ ε / Z := by
    have he : c * (finiteWeightLaw weight hweight i).toReal - (target i).toReal =
        ((weight i : ℝ) / D - Z * (target i).toReal) / Z := by
      simp only [finiteWeightLaw_apply, ENNReal.toReal_div, ENNReal.toReal_natCast]
      dsimp [c]
      field_simp
    rw [he, abs_div, abs_of_pos hZ]
    exact div_le_div_of_nonneg_right (h i) hZ.le
  simpa only [Fintype.card_fin, mul_div_assoc] using finite_scaled_mass_error _ target hpoint

/-- The computed exponential weights inherit a normalized distribution bound. -/
theorem exponentialWeightLaw_error {N : ℕ} (n m : Fin N → ℕ) (hm : ∀ i, 0 < m i)
    (t : ℕ) (hpos : 0 < ∑ i, (exponentialWeightRun (n i) (m i) t).value)
    (target : PMF (Fin N)) {Z : ℝ} (hZ : 0 < Z)
    (htarget : ∀ i, (target i).toReal = Real.exp (-(n i : ℝ) / m i) / Z) :
    discreteTotalVariation (finiteWeightLaw (fun i => (exponentialWeightRun (n i) (m i) t).value) hpos)
      target ≤ (N : ℝ) / ((2 : ℝ) ^ t * Z) := by
  have hpoint (i : Fin N) :
      |((exponentialWeightRun (n i) (m i) t).value : ℝ) /
        (2 : ℝ) ^ exponentialPrecision t - Z * (target i).toReal| ≤ 1 / (2 : ℝ) ^ t := by
    rw [htarget, mul_div_cancel₀ _ hZ.ne']
    exact exponentialWeightRun_error _ _ t (hm i)
  have h := finiteWeightLaw_error _ hpos target (by positivity) hZ hpoint
  convert h using 1
  field_simp

end SISToKSIS
end

open GeometricGaussianLHL
namespace SISToKSIS
set_option backward.isDefEq.respectTransparency false

noncomputable def arctanSeriesPartial (x : ℝ) (N : ℕ) : ℝ :=
  ∑ j ∈ Finset.range N, (-1) ^ j * x ^ (2 * j + 1) / (2 * j + 1 : ℕ)

theorem arctan_series_term_bound {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1 / 2)
    (j : ℕ) :
    ‖(-1 : ℝ) ^ j * x ^ (2 * j + 1) / (2 * j + 1 : ℕ)‖ ≤
      (1 / 2 : ℝ) ^ (j + 1) := by
  have hd : (1 : ℝ) ≤ (2 * j + 1 : ℕ) := by exact_mod_cast (show 1 ≤ 2 * j + 1 by omega)
  rw [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hx _), Real.norm_eq_abs,
    abs_of_nonneg (Nat.cast_nonneg _)]
  calc
    x ^ (2 * j + 1) / (2 * j + 1 : ℕ) ≤ x ^ (2 * j + 1) :=
      div_le_self (pow_nonneg hx _) hd
    _ ≤ (1 / 2 : ℝ) ^ (2 * j + 1) := pow_le_pow_left₀ hx hx' _
    _ ≤ (1 / 2 : ℝ) ^ (j + 1) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)

theorem arctanSeriesPartial_error {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1 / 2)
    (N : ℕ) : |Real.arctan x - arctanSeriesPartial x N| ≤ (1 / 2 : ℝ) ^ N := by
  have hs := Real.hasSum_arctan (x := x) (by rw [Real.norm_eq_abs, abs_of_nonneg hx]; linarith)
  have ht := (hasSum_nat_add_iff' N).mpr hs
  have hg : HasSum (fun j : ℕ => (1 / 2 : ℝ) ^ (j + N + 1)) ((1 / 2 : ℝ) ^ N) := by
    have hg := (hasSum_geometric_of_abs_lt_one (r := (1 / 2 : ℝ)) (by norm_num)).mul_right
      ((1 / 2 : ℝ) ^ (N + 1))
    have hv : ((1 - (1 / 2 : ℝ))⁻¹ * (1 / 2) ^ (N + 1)) = (1 / 2 : ℝ) ^ N := by
      norm_num [pow_succ]
      ring
    rw [← hv]
    simpa only [pow_add, pow_one, mul_assoc] using hg
  exact ht.norm_le_of_bounded hg (fun j => arctan_series_term_bound hx hx' (j + N))

noncomputable def piSeriesPartial (N : ℕ) : ℝ :=
  4 * (arctanSeriesPartial (1 / 2) N + arctanSeriesPartial (1 / 3) N)

theorem piSeriesPartial_error (t : ℕ) :
    |piSeriesPartial (t + 3) - Real.pi| ≤ 1 / (2 : ℝ) ^ t := by
  have h2 := arctanSeriesPartial_error (x := (1 / 2 : ℝ)) (by norm_num) (by norm_num) (t + 3)
  have h3 := arctanSeriesPartial_error (x := (1 / 3 : ℝ)) (by norm_num) (by norm_num) (t + 3)
  have hi : Real.pi = 4 * (Real.arctan (1 / 2) + Real.arctan (1 / 3)) := by
    have h := Real.arctan_inv_2_add_arctan_inv_3
    norm_num [one_div] at *
    linarith
  have he : (8 : ℝ) * (1 / 2) ^ (t + 3) = 1 / (2 : ℝ) ^ t := by
    simp [pow_add]
    ring
  rw [piSeriesPartial, hi]
  calc
    _ = 4 * |(arctanSeriesPartial (1 / 2) (t + 3) - Real.arctan (1 / 2)) +
        (arctanSeriesPartial (1 / 3) (t + 3) - Real.arctan (1 / 3))| := by
      rw [← abs_of_nonneg (show (0 : ℝ) ≤ 4 by norm_num), ← abs_mul]
      congr 1
      ring
    _ ≤ 4 * (|arctanSeriesPartial (1 / 2) (t + 3) - Real.arctan (1 / 2)| +
        |arctanSeriesPartial (1 / 3) (t + 3) - Real.arctan (1 / 3)|) :=
      mul_le_mul_of_nonneg_left (abs_add_le _ _) (by norm_num)
    _ ≤ 8 * (1 / 2 : ℝ) ^ (t + 3) := by
      rw [abs_sub_comm] at h2 h3
      linarith
    _ = _ := he

end SISToKSIS

open GeometricGaussianLHL
namespace SISToKSIS
set_option backward.isDefEq.respectTransparency false

/-- Repeated multiplication, including construction of the finite factor list. -/
def smallNaturalPowerRun (q e : ℕ) : Costed ℕ :=
  (Costed.charge (e * (q.size + e + 1) + 1) (List.replicate e q)).bind costedNatProduct

@[simp] theorem smallNaturalPowerRun_value (q e : ℕ) :
    (smallNaturalPowerRun q e).value = q ^ e := by
  simp [smallNaturalPowerRun, Costed.charge]

theorem smallNaturalPowerRun_size (q e : ℕ) : (q ^ e).size ≤ e * q.size + 1 := by
  simpa using nat_list_product_size (List.replicate e q)

theorem smallNaturalPowerRun_steps_le {q : ℕ} (hq : q.size ≤ 3) (e : ℕ) :
    (smallNaturalPowerRun q e).steps ≤ 100 * (e + 1) ^ 3 := by
  have h := costedNatProduct_steps_le (List.replicate e q) (3 * e) (by simp; nlinarith)
  simp only [List.length_replicate, natProductBudget] at h
  simp only [smallNaturalPowerRun, Costed.bind_steps, Costed.charge]
  have hqe : e * q.size ≤ 3 * e := by nlinarith
  nlinarith

def arctanIntegerTerm (D q j : ℕ) : ℤ :=
  let u : ℕ := D / ((2 * j + 1) * q ^ (2 * j + 1))
  if Even j then (u : ℤ) else -(u : ℤ)

def arctanIntegerSum (D q N : ℕ) : ℤ :=
  ∑ j ∈ Finset.range N, arctanIntegerTerm D q j

theorem arctanIntegerTerm_eq (D q j : ℕ) :
    arctanIntegerTerm D q j = (-1 : ℤ) ^ j *
      (D / ((2 * j + 1) * q ^ (2 * j + 1)) : ℕ) := by
  simp [arctanIntegerTerm, neg_one_pow_eq_ite, ite_mul]

theorem arctanIntegerTerm_abs (D q j : ℕ) : (arctanIntegerTerm D q j).natAbs ≤ D := by
  unfold arctanIntegerTerm
  split_ifs <;> simpa only [Int.natAbs_neg, Int.natAbs_natCast] using
    (Nat.div_le_self D ((2 * j + 1) * q ^ (2 * j + 1)))

theorem arctanIntegerSum_abs (D q N : ℕ) : (arctanIntegerSum D q N).natAbs ≤ N * D := by
  induction N with
  | zero => simp [arctanIntegerSum]
  | succ N ih =>
    rw [arctanIntegerSum, Finset.sum_range_succ]
    exact (Int.natAbs_add_le _ _).trans (by
      have ht := arctanIntegerTerm_abs D q N
      change (arctanIntegerSum D q N).natAbs + (arctanIntegerTerm D q N).natAbs ≤ _
      nlinarith)

/-- Evaluate one rounded arctangent term using integer arithmetic. -/
def arctanTermRun (D q j : ℕ) : Costed ℤ :=
  (Costed.charge (10 * (j + 1)) (2 * j + 1)).bind fun e =>
  (smallNaturalPowerRun q e).bind fun p =>
  (costedNatMul e p).bind fun den =>
  (costedNatDiv D den).bind fun u =>
  Costed.charge (3 * (u.size + j.size + 1))
    (if Even j then (u : ℤ) else -(u : ℤ))

@[simp] theorem arctanTermRun_value (D q j : ℕ) :
    (arctanTermRun D q j).value = arctanIntegerTerm D q j := by
  simp [arctanTermRun, arctanIntegerTerm, Costed.charge, costedNatMul, costedNatDiv]

def arctanSumRun (D q : ℕ) : ℕ → Costed ℤ
  | 0 => Costed.pure 0
  | N + 1 => (arctanSumRun D q N).bind fun s =>
      (arctanTermRun D q N).bind fun u =>
      (costedIntAdd s u).bind fun v => Costed.charge (N + 1) v

@[simp] theorem arctanSumRun_value (D q N : ℕ) :
    (arctanSumRun D q N).value = arctanIntegerSum D q N := by
  induction N with
  | zero => simp [arctanSumRun, arctanIntegerSum, Costed.pure]
  | succ N ih =>
    simp [arctanSumRun, ih, arctanIntegerSum, Finset.sum_range_succ,
      costedIntAdd, Costed.charge]

def piApproximationPrecision (t : ℕ) : ℕ := 2 * t + 10

def piApproximationNumerator (t : ℕ) : ℕ :=
  let D : ℕ := 2 ^ piApproximationPrecision t
  (max (3 * (D : ℤ)) (min (4 * (D : ℤ))
    (4 * (arctanIntegerSum D 2 (t + 4) + arctanIntegerSum D 3 (t + 4))))).toNat

end SISToKSIS
namespace SISToKSIS
set_option backward.isDefEq.respectTransparency false

theorem arctanIntegerTerm_error {D q : ℕ} (hD : 0 < D) (hq : 0 < q) (j : ℕ) :
    |(arctanIntegerTerm D q j : ℝ) / D -
      (-1 : ℝ) ^ j * (1 / q : ℝ) ^ (2 * j + 1) / (2 * j + 1 : ℕ)| ≤ 1 / (D : ℝ) := by
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have heR : (2 * j + 1 : ℕ) ≠ 0 := by omega
  have hden : 0 < (2 * j + 1) * q ^ (2 * j + 1) := by positivity
  have hh := div_le_div_of_nonneg_right
    (natural_division_error D ((2 * j + 1) * q ^ (2 * j + 1)) hden) hDR.le
  have he : (arctanIntegerTerm D q j : ℝ) / D -
      (-1 : ℝ) ^ j * (1 / q : ℝ) ^ (2 * j + 1) / (2 * j + 1 : ℕ) =
      (-1 : ℝ) ^ j *
        (((D / ((2 * j + 1) * q ^ (2 * j + 1)) : ℕ) : ℝ) -
          (D : ℝ) / ((2 * j + 1) * q ^ (2 * j + 1) : ℕ)) / D := by
    simp only [arctanIntegerTerm_eq, Int.cast_mul, Int.cast_pow, Int.cast_neg,
      Int.cast_one, Int.cast_natCast, Nat.cast_mul, Nat.cast_pow, div_pow, one_pow]
    field_simp
  rw [he, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_pos hDR]
  exact hh

theorem arctanIntegerSum_error {D q : ℕ} (hD : 0 < D) (hq : 0 < q) (N : ℕ) :
    |(arctanIntegerSum D q N : ℝ) / D - arctanSeriesPartial (1 / q) N| ≤
      (N : ℝ) / D := by
  simp only [arctanIntegerSum, Int.cast_sum, Finset.sum_div, arctanSeriesPartial,
    ← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  have h := Finset.sum_le_sum (fun j (_ : j ∈ Finset.range N) => arctanIntegerTerm_error hD hq j)
  simpa [div_eq_mul_inv] using h

theorem pi_rounding_budget (t : ℕ) :
    8 * (t + 4 : ℝ) / (2 : ℝ) ^ piApproximationPrecision t ≤ 1 / (2 : ℝ) ^ (t + 1) := by
  have ht : (t : ℝ) + 4 ≤ 4 * (2 : ℝ) ^ t := by
    induction t with
    | zero => norm_num
    | succ t ih =>
      have hp : (1 : ℝ) ≤ 2 ^ t := one_le_pow₀ (by norm_num)
      push_cast
      rw [pow_succ]
      nlinarith
  have he : (2 : ℝ) ^ piApproximationPrecision t = 1024 * ((2 : ℝ) ^ t) ^ 2 := by
    rw [piApproximationPrecision, show 2 * t + 10 = t * 2 + 10 by omega,
      pow_add, pow_mul]
    norm_num
    ring
  rw [he]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  rw [pow_succ]
  nlinarith [sq_nonneg ((2 : ℝ) ^ t)]

theorem pi_raw_error (t : ℕ) :
    |(4 * (arctanIntegerSum (2 ^ piApproximationPrecision t) 2 (t + 4) +
        arctanIntegerSum (2 ^ piApproximationPrecision t) 3 (t + 4)) : ℝ) /
        (2 : ℝ) ^ piApproximationPrecision t - Real.pi| ≤ 1 / (2 : ℝ) ^ t := by
  let D : ℕ := 2 ^ piApproximationPrecision t
  have h2 := arctanIntegerSum_error (D := D) (q := 2) (by dsimp [D]; positivity) (by omega) (t + 4)
  have h3 := arctanIntegerSum_error (D := D) (q := 3) (by dsimp [D]; positivity) (by omega) (t + 4)
  have hround : |(4 * (arctanIntegerSum D 2 (t + 4) + arctanIntegerSum D 3 (t + 4)) : ℝ) /
      D - piSeriesPartial (t + 4)| ≤ 8 * (t + 4 : ℝ) / D := by
    have he : (4 * (arctanIntegerSum D 2 (t + 4) + arctanIntegerSum D 3 (t + 4)) : ℝ) /
      D - piSeriesPartial (t + 4) =
      4 * (((arctanIntegerSum D 2 (t + 4) : ℝ) / D - arctanSeriesPartial (1 / 2) (t + 4)) +
      ((arctanIntegerSum D 3 (t + 4) : ℝ) / D - arctanSeriesPartial (1 / 3) (t + 4))) := by
      unfold piSeriesPartial
      ring
    rw [he, abs_mul, abs_of_pos (show (0 : ℝ) < 4 by norm_num)]
    have h := abs_add_le
      ((arctanIntegerSum D 2 (t + 4) : ℝ) / D - arctanSeriesPartial (1 / 2) (t + 4))
      ((arctanIntegerSum D 3 (t + 4) : ℝ) / D - arctanSeriesPartial (1 / 3) (t + 4))
    push_cast at h2 h3
    norm_num only [Nat.cast_ofNat] at h2 h3
    rw [mul_div_assoc]
    linarith
  have htail := piSeriesPartial_error (t + 1)
  have hbudget := pi_rounding_budget t
  have htri := abs_sub_le
    ((4 * (arctanIntegerSum D 2 (t + 4) + arctanIntegerSum D 3 (t + 4)) : ℝ) / D)
    (piSeriesPartial (t + 4)) Real.pi
  have he : (1 : ℝ) / 2 ^ (t + 1) + 1 / 2 ^ (t + 1) = 1 / 2 ^ t := by
    rw [pow_succ]
    field_simp
    norm_num
  dsimp only [D] at *
  norm_num only [Nat.cast_pow, Nat.cast_ofNat] at *
  convert (htri.trans (add_le_add (hround.trans hbudget) htail)).trans_eq he using 1

theorem abs_clamp_sub_le {a b y : ℝ} (ha : a ≤ y) (hb : y ≤ b) (x : ℝ) :
    |max a (min b x) - y| ≤ |x - y| := by
  have hmin := abs_min_sub_min_le_max b x b y
  have hmax := abs_max_sub_max_le_max a (min b x) a y
  simp only [min_eq_right hb, sub_self, abs_zero, max_eq_right (abs_nonneg (x - y))] at hmin
  simp only [max_eq_right ha, sub_self, abs_zero, max_eq_right (abs_nonneg (min b x - y))] at hmax
  exact hmax.trans hmin

theorem piApproximationNumerator_bounds (t : ℕ) :
    3 * 2 ^ piApproximationPrecision t ≤ piApproximationNumerator t ∧
      piApproximationNumerator t ≤ 4 * 2 ^ piApproximationPrecision t := by
  let D : ℕ := 2 ^ piApproximationPrecision t
  let z := 4 * (arctanIntegerSum D 2 (t + 4) + arctanIntegerSum D 3 (t + 4))
  have h0 : (0 : ℤ) ≤ max (3 * (D : ℤ)) (min (4 * (D : ℤ)) z) :=
    (by positivity : (0 : ℤ) ≤ 3 * D).trans (le_max_left _ _)
  have hlo := le_max_left (3 * (D : ℤ)) (min (4 * (D : ℤ)) z)
  have hhi : max (3 * (D : ℤ)) (min (4 * (D : ℤ)) z) ≤ 4 * D :=
    max_le (by omega) (min_le_left _ _)
  constructor
  · exact_mod_cast (show (3 * D : ℤ) ≤ (piApproximationNumerator t : ℤ) by
      simpa only [piApproximationNumerator, D, z, Int.toNat_of_nonneg h0] using hlo)
  · exact_mod_cast (show (piApproximationNumerator t : ℤ) ≤ (4 * D : ℤ) by
      simpa only [piApproximationNumerator, D, z, Int.toNat_of_nonneg h0] using hhi)

theorem piApproximationNumerator_error (t : ℕ) :
    |(piApproximationNumerator t : ℝ) / (2 : ℝ) ^ piApproximationPrecision t - Real.pi| ≤
      1 / (2 : ℝ) ^ t := by
  let D : ℕ := 2 ^ piApproximationPrecision t
  let z : ℤ := 4 * (arctanIntegerSum D 2 (t + 4) + arctanIntegerSum D 3 (t + 4))
  have hD : (0 : ℝ) < D := by dsimp [D]; positivity
  have h0 : (0 : ℤ) ≤ max (3 * (D : ℤ)) (min (4 * (D : ℤ)) z) :=
    (by positivity : (0 : ℤ) ≤ 3 * D).trans (le_max_left _ _)
  have hv : (piApproximationNumerator t : ℝ) =
      max (3 * (D : ℝ)) (min (4 * (D : ℝ)) (z : ℝ)) := by
    have hh := Int.toNat_of_nonneg h0
    change (((max (3 * (D : ℤ)) (min (4 * (D : ℤ)) z)).toNat : ℝ)) = _
    exact_mod_cast hh
  have he : (piApproximationNumerator t : ℝ) / (D : ℝ) =
      max 3 (min 4 ((z : ℝ) / D)) := by
    rw [hv, ← max_div_div_right hD.le, ← min_div_div_right hD.le]
    simp only [mul_div_cancel_right₀ _ hD.ne']
  have hh := (abs_clamp_sub_le Real.pi_gt_three.le Real.pi_lt_four.le ((z : ℝ) / D)).trans
    (by simpa [z, D] using pi_raw_error t)
  rw [← he] at hh
  simpa only [D, Nat.cast_pow, Nat.cast_ofNat, one_div] using hh

end SISToKSIS
open GeometricGaussianLHL
namespace SISToKSIS
set_option backward.isDefEq.respectTransparency false

theorem arctanTermRun_steps_le {D q j B : ℕ}
    (hD : D.size ≤ B) (hq : q.size ≤ 3) (hj : j ≤ B) :
    (arctanTermRun D q j).steps ≤ 2000 * (B + 1) ^ 3 := by
  let e := 2 * j + 1
  let M := B + 1
  have hM : 1 ≤ M := by dsimp [M]; omega
  have he : e + 1 ≤ 2 * M := by dsimp [e, M]; omega
  have hes : e.size ≤ 2 * M := (show e.size ≤ e from Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega)
  have hp : (q ^ e).size ≤ 6 * M := by
    apply (smallNaturalPowerRun_size q e).trans
    nlinarith
  have hden : (e * q ^ e).size ≤ 9 * M := by
    apply (natural_mul_size_le e (q ^ e)).trans
    omega
  have hu : (D / (e * q ^ e)).size ≤ B :=
    (Nat.size_le_size (Nat.div_le_self _ _)).trans hD
  have hjS : j.size ≤ M := (show j.size ≤ j from Nat.size_le.mpr Nat.lt_two_pow_self).trans (by dsimp [M]; omega)
  have hpow : (smallNaturalPowerRun q e).steps ≤ 800 * M ^ 3 := by
    apply (smallNaturalPowerRun_steps_le hq e).trans
    have hh := Nat.mul_le_mul_left 100 (Nat.pow_le_pow_left he 3)
    nlinarith
  have hm := Nat.pow_le_pow_left (show e.size + (q ^ e).size + 1 ≤ 9 * M by omega) 2
  have hd := Nat.pow_le_pow_left
    (show D.size + (e * q ^ e).size + 1 ≤ 11 * M by dsimp [M] at *; omega) 2
  have hlinear : M ≤ M ^ 3 := by
    simpa only [pow_one] using Nat.pow_le_pow_right hM (show 1 ≤ 3 by omega)
  have hsquare : M ^ 2 ≤ M ^ 3 := Nat.pow_le_pow_right hM (by omega)
  simp only [arctanTermRun, Costed.bind_steps, Costed.charge, smallNaturalPowerRun_value,
    costedNatMul, costedNatDiv]
  change 10 * (j + 1) + ((smallNaturalPowerRun q e).steps +
    ((e.size + (q ^ e).size + 1) ^ 2 + ((D.size + (e * q ^ e).size + 1) ^ 2 +
    3 * ((D / (e * q ^ e)).size + j.size + 1)))) ≤ _
  dsimp only [M] at *
  nlinarith

theorem arctanSumRun_steps_le {D q B : ℕ} (hD : D.size ≤ B) (hq : q.size ≤ 3)
    (N : ℕ) (hN : N ≤ B) :
    (arctanSumRun D q N).steps ≤ 2100 * N * (B + 1) ^ 3 := by
  induction N with
  | zero => simp [arctanSumRun, Costed.pure]
  | succ N ih =>
    have hn : N ≤ B := by omega
    have hi := ih hn
    have ht := arctanTermRun_steps_le hD hq hn
    have hss : (arctanIntegerSum D q N).natAbs.size ≤ 2 * (B + 1) := by
      apply (Nat.size_le_size (arctanIntegerSum_abs D q N)).trans
      apply (natural_mul_size_le N D).trans
      have : N.size ≤ N := Nat.size_le.mpr Nat.lt_two_pow_self
      omega
    have hts : (arctanIntegerTerm D q N).natAbs.size ≤ B :=
      (Nat.size_le_size (arctanIntegerTerm_abs D q N)).trans hD
    have hlinear : B + 1 ≤ (B + 1) ^ 3 := by
      simpa only [pow_one] using Nat.pow_le_pow_right (show 1 ≤ B + 1 by omega)
        (show 1 ≤ 3 by omega)
    simp only [arctanSumRun, Costed.bind_steps, arctanSumRun_value, arctanTermRun_value,
      costedIntAdd, integerOperandBits, Costed.charge]
    nlinarith

/-- Binary approximation of pi, clamped to the interval [3,4]. -/
def piApproximationRun (t : ℕ) : Costed ℕ :=
  (Costed.charge (10 * (t + 5)) (piApproximationPrecision t)).bind fun p =>
  (Costed.charge (p + 1) (2 ^ p)).bind fun D =>
  (arctanSumRun D 2 (t + 4)).bind fun a =>
  (arctanSumRun D 3 (t + 4)).bind fun b =>
  (costedIntAdd a b).bind fun s =>
  (costedIntMul 4 s).bind fun z =>
  (costedNatMul 3 D).bind fun lo =>
  (costedNatMul 4 D).bind fun hi =>
  Costed.charge (10 * (z.natAbs.size + lo.size + hi.size + 1))
    (max (lo : ℤ) (min (hi : ℤ) z)).toNat

@[simp] theorem piApproximationRun_value (t : ℕ) :
    (piApproximationRun t).value = piApproximationNumerator t := by
  simp [piApproximationRun, piApproximationNumerator, Costed.charge, costedIntAdd,
    costedIntMul, costedNatMul]

theorem piApproximationRun_bounds (t : ℕ) :
    3 * 2 ^ piApproximationPrecision t ≤ (piApproximationRun t).value ∧
      (piApproximationRun t).value ≤ 4 * 2 ^ piApproximationPrecision t := by
  simpa only [piApproximationRun_value] using piApproximationNumerator_bounds t

theorem piApproximationRun_error (t : ℕ) :
    |((piApproximationRun t).value : ℝ) / (2 : ℝ) ^ piApproximationPrecision t - Real.pi| ≤
      1 / (2 : ℝ) ^ t := by
  simpa only [piApproximationRun_value] using piApproximationNumerator_error t

theorem piApproximationRun_size (t : ℕ) :
    (piApproximationRun t).value.size ≤ piApproximationPrecision t + 3 := by
  have h := (piApproximationRun_bounds t).2
  have he : 4 * 2 ^ piApproximationPrecision t = 2 ^ (piApproximationPrecision t + 2) := by
    rw [pow_add]
    ring
  rw [he] at h
  exact nat_size_le_dyadic_bound h

theorem piApproximationRun_steps_le (t : ℕ) :
    (piApproximationRun t).steps ≤ 40000000 * (t + 1) ^ 4 := by
  let T := t + 1
  let p := piApproximationPrecision t
  let D : ℕ := 2 ^ p
  let N := t + 4
  let a := arctanIntegerSum D 2 N
  let b := arctanIntegerSum D 3 N
  let s := a + b
  let z := 4 * s
  have hT : 1 ≤ T := by dsimp [T]; omega
  have hD : D.size = 2 * t + 11 := by simp [D, p, piApproximationPrecision, Nat.size_pow]
  have hDB : D.size ≤ 11 * T := by dsimp [T]; omega
  have hN : N ≤ 4 * T := by dsimp [N, T]; omega
  have hNB : N ≤ 2 * t + 11 := by dsimp [N]; omega
  have hNS : N.size ≤ N := Nat.size_le.mpr Nat.lt_two_pow_self
  have hab (q : ℕ) : (arctanIntegerSum D q N).natAbs.size ≤ 16 * T := by
    have h := (Nat.size_le_size (arctanIntegerSum_abs D q N)).trans (natural_mul_size_le N D)
    dsimp only [T, N] at *
    omega
  have ha : a.natAbs.size ≤ 16 * T := hab 2
  have hb : b.natAbs.size ≤ 16 * T := hab 3
  have hs : s.natAbs.size ≤ 18 * T := by
    have h := integer_sub_size_le a (-b) (16 * T) ha (by simpa using hb)
    simp only [sub_neg_eq_add] at h
    dsimp only [s]
    omega
  have hz : z.natAbs.size ≤ 22 * T := by
    have h := integer_mul_size_le 4 s 3 (18 * T) (by decide) hs
    dsimp only [z]
    omega
  have hlo : (3 * D).size ≤ 14 * T := by
    have h := natural_mul_size_le 3 D
    change (3 * D).size ≤ 2 + D.size + 1 at h
    omega
  have hhi : (4 * D).size ≤ 15 * T := by
    have h := natural_mul_size_le 4 D
    change (4 * D).size ≤ 3 + D.size + 1 at h
    omega
  have hsum (q : ℕ) (hq : q.size ≤ 3) :
      (arctanSumRun D q N).steps ≤ 14515200 * T ^ 4 := by
    have h := arctanSumRun_steps_le (D := D) (B := 2 * t + 11) (by omega) hq N hNB
    have hp : (2 * t + 11 + 1) ^ 3 ≤ (12 * T) ^ 3 :=
      Nat.pow_le_pow_left (by dsimp [T]; omega) 3
    have hm := Nat.mul_le_mul (Nat.mul_le_mul_left 2100 hN) hp
    apply h.trans
    nlinarith
  have h2 := hsum 2 (by decide)
  have h3 := hsum 3 (by decide)
  have hzCost := Nat.pow_le_pow_left (show 3 + s.natAbs.size + 1 ≤ 22 * T by omega) 2
  have hloCost := Nat.pow_le_pow_left (show 2 + D.size + 1 ≤ 14 * T by omega) 2
  have hhiCost := Nat.pow_le_pow_left (show 3 + D.size + 1 ≤ 15 * T by omega) 2
  have htotal : (piApproximationRun t).steps =
      10 * (t + 5) + (p + 1 + ((arctanSumRun D 2 N).steps +
      ((arctanSumRun D 3 N).steps + ((a.natAbs.size + b.natAbs.size + 1) +
      ((3 + s.natAbs.size + 1) ^ 2 + ((2 + D.size + 1) ^ 2 +
      ((3 + D.size + 1) ^ 2 + 10 * (z.natAbs.size + (3 * D).size + (4 * D).size + 1)))))))) := by
    simp only [piApproximationRun, Costed.bind_steps, Costed.charge,
      arctanSumRun_value, costedIntAdd, costedIntMul, costedNatMul, integerOperandBits]
    rfl
  have hlin : T ≤ T ^ 4 := by
    simpa only [pow_one] using Nat.pow_le_pow_right hT (show 1 ≤ 4 by omega)
  have hsquare : T ^ 2 ≤ T ^ 4 := Nat.pow_le_pow_right hT (by omega)
  rw [htotal]
  change _ ≤ 40000000 * T ^ 4
  have hp : p + 1 ≤ 11 * T := by dsimp [p, piApproximationPrecision, T]; omega
  have ht5 : t + 5 ≤ 5 * T := by dsimp [T]; omega
  nlinarith

theorem piApproximationRun_polynomial :
    Costed.PolynomialTime (fun _ : Unit => piApproximationRun) (fun _ => True) (fun _ => 0) := by
  refine ⟨40000000, 4, ?_⟩
  intro input hvalid t
  simpa only [zero_add] using piApproximationRun_steps_le t

end SISToKSIS

open GeometricGaussianLHL
namespace SISToKSIS
set_option backward.isDefEq.respectTransparency false

/-- Precision used for pi includes the bit length of the radial argument. -/
def gaussianPiPrecision (n t : ℕ) : ℕ := t + n.size + 1

/-- Compute a finite acceptance weight for `exp(-pi*n/m)`. -/
def gaussianRadialWeightRun (n m t : ℕ) : Costed ℕ :=
  let r := gaussianPiPrecision n t
  let P := piApproximationRun r
  let p := piApproximationPrecision r
  let a := costedNatMul P.value n
  let b := costedNatMul (2 ^ p) m
  let result := exponentialWeightRun a.value b.value (t + 1)
  ⟨result.value, 10 * (n.size + t + 2) + (P.steps + (p + 1 + (a.steps + (b.steps + result.steps))))⟩

@[simp] theorem gaussianRadialWeightRun_value (n m t : ℕ) :
    (gaussianRadialWeightRun n m t).value =
      (exponentialWeightRun ((piApproximationRun (gaussianPiPrecision n t)).value * n)
        (2 ^ piApproximationPrecision (gaussianPiPrecision n t) * m) (t + 1)).value := rfl

theorem gaussianRadialWeightRun_bound (n m t : ℕ) (hm : 0 < m) :
    (gaussianRadialWeightRun n m t).value ≤ 2 ^ exponentialPrecision (t + 1) := by
  rw [gaussianRadialWeightRun_value]
  exact exponentialWeightRun_bound _ _ _ (by positivity)

theorem gaussianRadialWeightRun_size (n m t : ℕ) (hm : 0 < m) :
    (gaussianRadialWeightRun n m t).value.size ≤ exponentialPrecision (t + 1) + 1 :=
  nat_size_le_dyadic_bound (gaussianRadialWeightRun_bound n m t hm)

theorem exp_neg_sub_exp_neg_le {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    |Real.exp (-a) - Real.exp (-b)| ≤ b - a := by
  have hprod : Real.exp (-a) * Real.exp (a - b) = Real.exp (-b) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have he : Real.exp (-a) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hd : Real.exp (a - b) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have h := mul_le_mul_of_nonneg_right he (sub_nonneg.mpr hd)
  have hlin := Real.add_one_le_exp (a - b)
  rw [abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr (by linarith)))]
  nlinarith

theorem exp_neg_lipschitz {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |Real.exp (-a) - Real.exp (-b)| ≤ |a - b| := by
  rcases le_total a b with hab | hba
  · simpa only [abs_of_nonpos (sub_nonpos.mpr hab), neg_sub] using exp_neg_sub_exp_neg_le ha hab
  · rw [abs_sub_comm (Real.exp (-a)), abs_sub_comm a b]
    simpa only [abs_of_nonpos (sub_nonpos.mpr hba), neg_sub] using exp_neg_sub_exp_neg_le hb hba

theorem gaussian_pi_argument_error (n m t : ℕ) (hm : 0 < m) :
    |((piApproximationRun (gaussianPiPrecision n t)).value : ℝ) * n /
        ((2 : ℝ) ^ piApproximationPrecision (gaussianPiPrecision n t) * m) -
        Real.pi * n / m| ≤ 1 / (2 : ℝ) ^ (t + 1) := by
  let r := gaussianPiPrecision n t
  let P := (piApproximationRun r).value
  let D := (2 : ℝ) ^ piApproximationPrecision r
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hn : (n : ℝ) ≤ (2 : ℝ) ^ n.size := by exact_mod_cast (Nat.lt_size_self n).le
  have hratio : (0 : ℝ) ≤ (n : ℝ) / m := by positivity
  have hratio' : (n : ℝ) / m ≤ (2 : ℝ) ^ n.size :=
    (div_le_self (Nat.cast_nonneg _) hmR).trans hn
  have he : (P : ℝ) * n / (D * m) - Real.pi * n / m =
      ((P : ℝ) / D - Real.pi) * ((n : ℝ) / m) := by ring
  change |(P : ℝ) * n / (D * m) - Real.pi * n / m| ≤ _
  rw [he, abs_mul, abs_of_nonneg hratio]
  have h := mul_le_mul (piApproximationRun_error r) hratio' hratio (by positivity)
  have hv : 1 / (2 : ℝ) ^ r * (2 : ℝ) ^ n.size = 1 / (2 : ℝ) ^ (t + 1) := by
    dsimp [r, gaussianPiPrecision]
    rw [show t + n.size + 1 = (t + 1) + n.size by omega, pow_add]
    field_simp
  exact h.trans_eq hv

theorem gaussianRadialWeightRun_error (n m t : ℕ) (hm : 0 < m) :
    |((gaussianRadialWeightRun n m t).value : ℝ) / (2 : ℝ) ^ exponentialPrecision (t + 1) -
      Real.exp (-Real.pi * n / m)| ≤ 1 / (2 : ℝ) ^ t := by
  let r := gaussianPiPrecision n t
  let P := (piApproximationRun r).value
  let D : ℕ := 2 ^ piApproximationPrecision r
  have hden : 0 < D * m := by dsimp [D]; positivity
  have he := exponentialWeightRun_error (P * n) (D * m) (t + 1) hden
  have hpi := gaussian_pi_argument_error n m t hm
  have hlip := exp_neg_lipschitz
    (a := (P : ℝ) * n / ((D : ℝ) * m)) (b := Real.pi * n / m) (by positivity) (by positivity)
  have ht := abs_sub_le
    (((exponentialWeightRun (P * n) (D * m) (t + 1)).value : ℝ) /
      (2 : ℝ) ^ exponentialPrecision (t + 1))
    (Real.exp (-((P : ℝ) * n / ((D : ℝ) * m)))) (Real.exp (-(Real.pi * n / m)))
  rw [gaussianRadialWeightRun_value]
  change |((exponentialWeightRun (P * n) (D * m) (t + 1)).value : ℝ) /
    (2 : ℝ) ^ exponentialPrecision (t + 1) - Real.exp (-Real.pi * n / m)| ≤ _
  have hnorm : -Real.pi * (n : ℝ) / m = -(Real.pi * n / m) := by ring
  rw [hnorm]
  have hsum : 1 / (2 : ℝ) ^ (t + 1) + 1 / (2 : ℝ) ^ (t + 1) = 1 / (2 : ℝ) ^ t := by
    rw [pow_succ]
    field_simp
    norm_num
  norm_num only [Nat.cast_mul] at he
  rw [show -((P : ℝ) * n) / ((D : ℝ) * m) = -((P : ℝ) * n / ((D : ℝ) * m)) by ring] at he
  have hpi' : |(P : ℝ) * n / ((D : ℝ) * m) - Real.pi * n / m| ≤ 1 / (2 : ℝ) ^ (t + 1) := by
    simpa only [P, D, Nat.cast_pow, Nat.cast_ofNat] using hpi
  exact (ht.trans (add_le_add he (hlip.trans hpi'))).trans_eq hsum

end SISToKSIS
open GeometricGaussianLHL
namespace SISToKSIS
set_option backward.isDefEq.respectTransparency false

theorem gaussianRadialWeightRun_steps_le (n m t : ℕ) (hm : 0 < m) :
    (gaussianRadialWeightRun n m t).steps ≤ 2000000000 * (n.size + m.size + t + 1) ^ 4 := by
  let B := n.size + m.size + t + 1
  let r := gaussianPiPrecision n t
  let p := piApproximationPrecision r
  let P := (piApproximationRun r).value
  let D : ℕ := 2 ^ p
  have hB : 1 ≤ B := by dsimp [B]; omega
  have hr : r ≤ B := by dsimp [r, gaussianPiPrecision, B]; omega
  have hn : n.size ≤ B := by dsimp [B]; omega
  have hmS : m.size ≤ B := by dsimp [B]; omega
  have ht : t + 1 ≤ B := by dsimp [B]; omega
  have hp : p ≤ 12 * B := by dsimp [p, piApproximationPrecision]; omega
  have hP : P.size ≤ 15 * B := by
    have h := piApproximationRun_size r
    dsimp only [P, p] at *
    omega
  have hD : D.size ≤ 13 * B := by
    dsimp only [D]
    rw [Nat.size_pow]
    omega
  have ha : (P * n).size ≤ 17 * B := (natural_mul_size_le P n).trans (by omega)
  have hb : (D * m).size ≤ 15 * B := (natural_mul_size_le D m).trans (by omega)
  have hpi : (piApproximationRun r).steps ≤ 640000000 * B ^ 4 := by
    apply (piApproximationRun_steps_le r).trans
    have h := Nat.mul_le_mul_left 40000000
      (Nat.pow_le_pow_left (show r + 1 ≤ 2 * B by omega) 4)
    nlinarith
  have hexp : (exponentialWeightRun (P * n) (D * m) (t + 1)).steps ≤ 857500000 * B ^ 3 := by
    have h := exponentialWeightRun_steps_le (P * n) (D * m) (t + 1) (by dsimp [D]; positivity)
    apply h.trans
    have hp := Nat.mul_le_mul_left 20000 (Nat.pow_le_pow_left
      (show (P * n).size + (D * m).size + (t + 1) + 1 ≤ 35 * B by omega) 3)
    nlinarith
  have hmul1 := Nat.pow_le_pow_left (show P.size + n.size + 1 ≤ 17 * B by omega) 2
  have hmul2 := Nat.pow_le_pow_left (show D.size + m.size + 1 ≤ 15 * B by omega) 2
  have htotal : (gaussianRadialWeightRun n m t).steps =
      10 * (n.size + t + 2) + ((piApproximationRun r).steps + (p + 1 +
      ((P.size + n.size + 1) ^ 2 + ((D.size + m.size + 1) ^ 2 +
      (exponentialWeightRun (P * n) (D * m) (t + 1)).steps)))) := rfl
  have hlin : B ≤ B ^ 4 := by
    simpa only [pow_one] using Nat.pow_le_pow_right hB (show 1 ≤ 4 by omega)
  have hsquare : B ^ 2 ≤ B ^ 4 := Nat.pow_le_pow_right hB (by omega)
  have hcube : B ^ 3 ≤ B ^ 4 := Nat.pow_le_pow_right hB (by omega)
  rw [htotal]
  change _ ≤ 2000000000 * B ^ 4
  have hsetup : n.size + t + 2 ≤ 2 * B := by dsimp [B]; omega
  nlinarith

theorem gaussianRadialWeightRun_polynomial :
    Costed.PolynomialTime
      (fun input : ℕ × ℕ => fun t => gaussianRadialWeightRun input.1 input.2 t)
      (fun input => 0 < input.2) (fun input => input.1.size + input.2.size) := by
  refine ⟨2000000000, 4, ?_⟩
  intro input hvalid t
  exact gaussianRadialWeightRun_steps_le input.1 input.2 t hvalid

theorem gaussianRadialWeightLaw_error {N : ℕ} (n m : Fin N → ℕ) (hm : ∀ i, 0 < m i)
    (t : ℕ) (hpos : 0 < ∑ i, (gaussianRadialWeightRun (n i) (m i) t).value)
    (target : PMF (Fin N)) {Z : ℝ} (hZ : 0 < Z)
    (htarget : ∀ i, (target i).toReal = Real.exp (-Real.pi * (n i : ℝ) / m i) / Z) :
    discreteTotalVariation (finiteWeightLaw (fun i => (gaussianRadialWeightRun (n i) (m i) t).value) hpos)
      target ≤ (N : ℝ) / ((2 : ℝ) ^ t * Z) := by
  have hpoint (i : Fin N) :
      |((gaussianRadialWeightRun (n i) (m i) t).value : ℝ) /
        (2 : ℝ) ^ exponentialPrecision (t + 1) - Z * (target i).toReal| ≤ 1 / (2 : ℝ) ^ t := by
    rw [htarget, mul_div_cancel₀ _ hZ.ne']
    exact gaussianRadialWeightRun_error _ _ t (hm i)
  have h := finiteWeightLaw_error _ hpos target (by positivity) hZ hpoint
  convert h using 1
  field_simp

/-- Points within one Gaussian width retain a fixed positive fraction of the
acceptance denominator, after numerical rounding. -/
theorem gaussianRadialWeightRun_lower (n m t : ℕ) (hm : 0 < m) (hn : n ≤ m) (ht : 6 ≤ t) :
    2 ^ exponentialPrecision (t + 1) ≤ 64 * (gaussianRadialWeightRun n m t).value := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hratio : (n : ℝ) / m ≤ 1 := (div_le_one hmR).mpr (by exact_mod_cast hn)
  have harg : -Real.pi ≤ -Real.pi * (n : ℝ) / m := by
    have h := mul_le_mul_of_nonneg_left hratio Real.pi_pos.le
    calc
      -Real.pi ≤ -(Real.pi * ((n : ℝ) / m)) := neg_le_neg (by simpa using h)
      _ = _ := by ring
  have hpi : (1 / 32 : ℝ) ≤ Real.exp (-Real.pi) := by
    rw [Real.exp_neg, ← one_div]
    apply one_div_le_one_div_of_le (Real.exp_pos _)
    linarith [exp_pi_lt_233_div_ten]
  have hexp := hpi.trans (Real.exp_le_exp.mpr harg)
  have hprecision : 1 / (2 : ℝ) ^ t ≤ 1 / 64 := by
    have hpow := pow_le_pow_right₀ (show (1 : ℝ) ≤ 2 by norm_num) ht
    apply one_div_le_one_div_of_le (by norm_num)
    norm_num at hpow
    exact hpow
  have herror := (abs_le.mp (gaussianRadialWeightRun_error n m t hm)).1
  have hlower : (1 / 64 : ℝ) ≤ ((gaussianRadialWeightRun n m t).value : ℝ) /
      (2 : ℝ) ^ exponentialPrecision (t + 1) := by linarith
  have hprod := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ exponentialPrecision (t + 1))).mp hlower
  have hr : (2 : ℝ) ^ exponentialPrecision (t + 1) ≤ 64 * (gaussianRadialWeightRun n m t).value := by
    linarith
  exact_mod_cast hr

theorem gaussianRadialWeightRun_pos (n m t : ℕ) (hm : 0 < m) (hn : n ≤ m) (ht : 6 ≤ t) :
    0 < (gaussianRadialWeightRun n m t).value := by
  have h := gaussianRadialWeightRun_lower n m t hm hn ht
  have hp : 0 < 2 ^ exponentialPrecision (t + 1) := by positivity
  nlinarith

end SISToKSIS
open GeometricGaussianLHL
namespace SISToKSIS
set_option backward.isDefEq.respectTransparency false

/-- Finite rational center and squared width for a scalar Gaussian. -/
structure ScalarGaussianData where
  centerNum : ℤ
  centerDen : ℕ
  widthSqNum : ℕ
  widthSqDen : ℕ
  deriving DecidableEq

def ScalarGaussianData.Valid (data : ScalarGaussianData) : Prop :=
  0 < data.centerDen ∧ 0 < data.widthSqNum ∧ 0 < data.widthSqDen

def ScalarGaussianData.bits (data : ScalarGaussianData) : ℕ :=
  data.centerNum.natAbs.size + data.centerDen.size + data.widthSqNum.size + data.widthSqDen.size + 1

noncomputable def ScalarGaussianData.center (data : ScalarGaussianData) : ℝ :=
  (data.centerNum : ℝ) / data.centerDen

noncomputable def ScalarGaussianData.widthSq (data : ScalarGaussianData) : ℝ :=
  (data.widthSqNum : ℝ) / data.widthSqDen

def ScalarGaussianData.ofRationals (center widthSq : ℚ) : ScalarGaussianData :=
  ⟨center.num, center.den, widthSq.num.natAbs, widthSq.den⟩

theorem ScalarGaussianData.ofRationals_valid (center widthSq : ℚ) (hwidth : 0 < widthSq) :
    (ofRationals center widthSq).Valid := by
  refine ⟨center.den_pos, ?_, widthSq.den_pos⟩
  have hnum := Rat.num_pos.mpr hwidth
  change 0 < widthSq.num.natAbs
  exact Int.natAbs_pos.mpr hnum.ne'

theorem ScalarGaussianData.ofRationals_center (c v : ℚ) :
    (ofRationals c v).center = (c : ℝ) := by
  exact (Rat.cast_def c).symm

theorem ScalarGaussianData.ofRationals_widthSq (c v : ℚ) (hv : 0 < v) :
    (ofRationals c v).widthSq = (v : ℝ) := by
  have hnum : (0 : ℝ) ≤ v.num := by exact_mod_cast (Rat.num_pos.mpr hv).le
  simp only [ScalarGaussianData.widthSq, ofRationals, Nat.cast_natAbs,
    Int.cast_abs, abs_of_nonneg hnum, Rat.cast_def]

theorem ScalarGaussianData.ofRationals_bits (c v : ℚ) :
    (ofRationals c v).bits ≤ rationalMagnitudeBits c + rationalMagnitudeBits v := by
  dsimp [bits, ofRationals, rationalMagnitudeBits]
  omega

theorem ScalarGaussianData.widthSq_pos (data : ScalarGaussianData) (hdata : data.Valid) :
    0 < data.widthSq := by
  exact div_pos (by exact_mod_cast hdata.2.1) (by exact_mod_cast hdata.2.2)

def scalarRadiusNumerator (data : ScalarGaussianData) (z : ℤ) : ℕ :=
  (z * data.centerDen - data.centerNum).natAbs ^ 2 * data.widthSqDen

def scalarRadiusDenominator (data : ScalarGaussianData) : ℕ :=
  data.centerDen ^ 2 * data.widthSqNum

/-- Exact integer evaluation of the rational squared radius. -/
def scalarRadiusRun (data : ScalarGaussianData) (z : ℤ) : Costed (ℕ × ℕ) :=
  (Costed.charge (data.centerDen.size + 1) (data.centerDen : ℤ)).bind fun a =>
  (costedIntMul z a).bind fun p =>
  (costedIntSub p data.centerNum).bind fun h =>
  (Costed.charge (h.natAbs.size + 1) h.natAbs).bind fun u =>
  (costedNatMul u u).bind fun u2 =>
  (costedNatMul u2 data.widthSqDen).bind fun n =>
  (costedNatMul data.centerDen data.centerDen).bind fun a2 =>
  (costedNatMul a2 data.widthSqNum).bind fun m =>
  Costed.charge 1 (n, m)

@[simp] theorem scalarRadiusRun_value (data : ScalarGaussianData) (z : ℤ) :
    (scalarRadiusRun data z).value = (scalarRadiusNumerator data z, scalarRadiusDenominator data) := by
  simp only [scalarRadiusRun, Costed.bind_value, Costed.charge, costedIntMul, costedIntSub,
    costedNatMul, scalarRadiusNumerator, scalarRadiusDenominator, pow_two]

theorem scalarRadiusDenominator_pos (data : ScalarGaussianData) (hdata : data.Valid) :
    0 < scalarRadiusDenominator data := by
  have h := hdata.1
  have h' := hdata.2.1
  dsimp [scalarRadiusDenominator]
  positivity

theorem scalarRadiusRun_correct (data : ScalarGaussianData) (hdata : data.Valid) (z : ℤ) :
    ((scalarRadiusRun data z).value.1 : ℝ) / (scalarRadiusRun data z).value.2 =
      ((z : ℝ) - data.center) ^ 2 / data.widthSq := by
  have ha : (data.centerDen : ℝ) ≠ 0 := by exact_mod_cast hdata.1.ne'
  have hn : (data.widthSqNum : ℝ) ≠ 0 := by exact_mod_cast hdata.2.1.ne'
  have hd : (data.widthSqDen : ℝ) ≠ 0 := by exact_mod_cast hdata.2.2.ne'
  simp only [scalarRadiusRun_value, scalarRadiusNumerator, scalarRadiusDenominator,
    Nat.cast_mul, Nat.cast_pow, Nat.cast_natAbs, Int.cast_abs, sq_abs, ScalarGaussianData.center,
    ScalarGaussianData.widthSq, Int.cast_sub, Int.cast_mul, Int.cast_natCast]
  field_simp

def scalarGaussianWeightRun (data : ScalarGaussianData) (z : ℤ) (t : ℕ) : Costed ℕ :=
  (scalarRadiusRun data z).bind fun radius => gaussianRadialWeightRun radius.1 radius.2 t

@[simp] theorem scalarGaussianWeightRun_value (data : ScalarGaussianData) (z : ℤ) (t : ℕ) :
    (scalarGaussianWeightRun data z t).value =
      (gaussianRadialWeightRun (scalarRadiusNumerator data z) (scalarRadiusDenominator data) t).value := by
  simp only [scalarGaussianWeightRun, Costed.bind_value, scalarRadiusRun_value]

theorem scalarGaussianWeightRun_bound (data : ScalarGaussianData) (hdata : data.Valid) (z : ℤ) (t : ℕ) :
    (scalarGaussianWeightRun data z t).value ≤ 2 ^ exponentialPrecision (t + 1) := by
  rw [scalarGaussianWeightRun_value]
  exact gaussianRadialWeightRun_bound _ _ t (scalarRadiusDenominator_pos data hdata)

theorem scalarGaussianWeightRun_size (data : ScalarGaussianData) (hdata : data.Valid) (z : ℤ) (t : ℕ) :
    (scalarGaussianWeightRun data z t).value.size ≤ exponentialPrecision (t + 1) + 1 :=
  nat_size_le_dyadic_bound (scalarGaussianWeightRun_bound data hdata z t)

theorem scalarGaussianWeightRun_error (data : ScalarGaussianData) (hdata : data.Valid) (z : ℤ) (t : ℕ) :
    |((scalarGaussianWeightRun data z t).value : ℝ) / (2 : ℝ) ^ exponentialPrecision (t + 1) -
      Real.exp (-Real.pi * ((z : ℝ) - data.center) ^ 2 / data.widthSq)| ≤ 1 / (2 : ℝ) ^ t := by
  have h := gaussianRadialWeightRun_error (scalarRadiusNumerator data z)
    (scalarRadiusDenominator data) t (scalarRadiusDenominator_pos data hdata)
  have he := scalarRadiusRun_correct data hdata z
  simp only [scalarRadiusRun_value] at he
  rw [mul_div_assoc, he, ← mul_div_assoc] at h
  simpa only [scalarGaussianWeightRun_value] using h

theorem scalarGaussianWeightRun_lower (data : ScalarGaussianData) (hdata : data.Valid)
    (z : ℤ) (t : ℕ) (ht : 6 ≤ t) (hz : ((z : ℝ) - data.center) ^ 2 ≤ data.widthSq) :
    2 ^ exponentialPrecision (t + 1) ≤ 64 * (scalarGaussianWeightRun data z t).value := by
  have hden := scalarRadiusDenominator_pos data hdata
  have hratio : (scalarRadiusNumerator data z : ℝ) / scalarRadiusDenominator data ≤ 1 := by
    have he := scalarRadiusRun_correct data hdata z
    simp only [scalarRadiusRun_value] at he
    rw [he]
    exact (div_le_one (data.widthSq_pos hdata)).mpr hz
  have hn : scalarRadiusNumerator data z ≤ scalarRadiusDenominator data := by
    exact_mod_cast (div_le_one (by exact_mod_cast hden)).mp hratio
  simpa only [scalarGaussianWeightRun_value] using
    gaussianRadialWeightRun_lower _ _ t hden hn ht

end SISToKSIS
open GeometricGaussianLHL
namespace SISToKSIS
set_option backward.isDefEq.respectTransparency false

theorem scalarRadius_operand_sizes (data : ScalarGaussianData) (z : ℤ) :
    let B := data.bits + z.natAbs.size + 1
    (z * data.centerDen).natAbs.size ≤ B ∧
    (z * data.centerDen - data.centerNum).natAbs.size ≤ 3 * B ∧
    ((z * data.centerDen - data.centerNum).natAbs ^ 2).size ≤ 7 * B ∧
    (scalarRadiusNumerator data z).size ≤ 9 * B ∧
    (data.centerDen ^ 2).size ≤ 3 * B ∧
    (scalarRadiusDenominator data).size ≤ 5 * B := by
  let B := data.bits + z.natAbs.size + 1
  have hB : 1 ≤ B := by dsimp [B]; omega
  have ha : data.centerDen.size ≤ B := by dsimp [B, ScalarGaussianData.bits]; omega
  have hc : data.centerNum.natAbs.size ≤ B := by dsimp [B, ScalarGaussianData.bits]; omega
  have hnum : data.widthSqNum.size ≤ B := by dsimp [B, ScalarGaussianData.bits]; omega
  have hden : data.widthSqDen.size ≤ B := by dsimp [B, ScalarGaussianData.bits]; omega
  have hp : (z * data.centerDen).natAbs.size ≤ B := by
    have h := integer_mul_size_le z data.centerDen z.natAbs.size data.centerDen.size
      le_rfl (by simp)
    apply h.trans
    dsimp [B, ScalarGaussianData.bits]
    omega
  have hh : (z * data.centerDen - data.centerNum).natAbs.size ≤ 3 * B := by
    apply (integer_sub_size_le _ _ B hp hc).trans
    omega
  have hu2 : ((z * data.centerDen - data.centerNum).natAbs ^ 2).size ≤ 7 * B := by
    rw [pow_two]
    exact (natural_mul_size_le _ _).trans (by omega)
  have hn : (scalarRadiusNumerator data z).size ≤ 9 * B := by
    exact (natural_mul_size_le _ _).trans (by omega)
  have ha2 : (data.centerDen ^ 2).size ≤ 3 * B := by
    rw [pow_two]
    exact (natural_mul_size_le _ _).trans (by omega)
  have hm : (scalarRadiusDenominator data).size ≤ 5 * B := by
    exact (natural_mul_size_le _ _).trans (by omega)
  exact ⟨hp, hh, hu2, hn, ha2, hm⟩

theorem scalarRadiusRun_steps_le (data : ScalarGaussianData) (z : ℤ) :
    (scalarRadiusRun data z).steps ≤ 200 * (data.bits + z.natAbs.size + 1) ^ 2 := by
  let B := data.bits + z.natAbs.size + 1
  let a := data.centerDen
  let p := z * (a : ℤ)
  let h := p - data.centerNum
  have hB : 1 ≤ B := by dsimp [B]; omega
  have ha : a.size ≤ B := by dsimp [a, B, ScalarGaussianData.bits]; omega
  have hc : data.centerNum.natAbs.size ≤ B := by dsimp [B, ScalarGaussianData.bits]; omega
  have hnum : data.widthSqNum.size ≤ B := by dsimp [B, ScalarGaussianData.bits]; omega
  have hden : data.widthSqDen.size ≤ B := by dsimp [B, ScalarGaussianData.bits]; omega
  obtain ⟨hp, hh, hu2, hn, ha2, hm⟩ := scalarRadius_operand_sizes data z
  change p.natAbs.size ≤ B at hp
  change h.natAbs.size ≤ 3 * B at hh
  change (h.natAbs ^ 2).size ≤ 7 * B at hu2
  change (a ^ 2).size ≤ 3 * B at ha2
  have hmul := Nat.pow_le_pow_left (show z.natAbs.size + a.size + 1 ≤ B by
    dsimp [a, B, ScalarGaussianData.bits]; omega) 2
  have hu2Cost := Nat.pow_le_pow_left (show h.natAbs.size + h.natAbs.size + 1 ≤ 7 * B by omega) 2
  have hnCost := Nat.pow_le_pow_left (show (h.natAbs ^ 2).size + data.widthSqDen.size + 1 ≤ 9 * B by omega) 2
  have ha2Cost := Nat.pow_le_pow_left (show a.size + a.size + 1 ≤ 3 * B by omega) 2
  have hmCost := Nat.pow_le_pow_left (show (a ^ 2).size + data.widthSqNum.size + 1 ≤ 5 * B by omega) 2
  have htotal : (scalarRadiusRun data z).steps =
      a.size + 1 + ((z.natAbs.size + a.size + 1) ^ 2 +
      ((p.natAbs.size + data.centerNum.natAbs.size + 1) + (h.natAbs.size + 1 +
      ((h.natAbs.size + h.natAbs.size + 1) ^ 2 +
      (((h.natAbs ^ 2).size + data.widthSqDen.size + 1) ^ 2 +
      ((a.size + a.size + 1) ^ 2 + (((a ^ 2).size + data.widthSqNum.size + 1) ^ 2 + 1))))))) := by
    simp only [scalarRadiusRun, Costed.bind_steps, Costed.charge, costedIntMul, costedIntSub,
      costedNatMul, integerOperandBits, Int.natAbs_natCast, pow_two]
    rfl
  have hlin : B ≤ B ^ 2 := by nlinarith
  rw [htotal]
  change _ ≤ 200 * B ^ 2
  nlinarith

theorem scalarGaussianWeightRun_steps_le (data : ScalarGaussianData) (hdata : data.Valid)
    (z : ℤ) (t : ℕ) :
    (scalarGaussianWeightRun data z t).steps ≤ 102000000000000 *
      (data.bits + z.natAbs.size + t + 1) ^ 4 := by
  let B := data.bits + z.natAbs.size + 1
  let T := data.bits + z.natAbs.size + t + 1
  have hT : 1 ≤ T := by dsimp [T]; omega
  have hBT : B ≤ T := by dsimp [B, T]; omega
  obtain ⟨_, _, _, hn, _, hm⟩ := scalarRadius_operand_sizes data z
  change (scalarRadiusNumerator data z).size ≤ 9 * B at hn
  change (scalarRadiusDenominator data).size ≤ 5 * B at hm
  have hinput : (scalarRadiusNumerator data z).size +
      (scalarRadiusDenominator data).size + t + 1 ≤ 15 * T := by
    dsimp only [B, T] at *
    omega
  have hgauss := gaussianRadialWeightRun_steps_le (scalarRadiusNumerator data z)
    (scalarRadiusDenominator data) t (scalarRadiusDenominator_pos data hdata)
  have hcost : (gaussianRadialWeightRun (scalarRadiusNumerator data z)
      (scalarRadiusDenominator data) t).steps ≤ 101250000000000 * T ^ 4 := by
    apply hgauss.trans
    have h := Nat.mul_le_mul_left 2000000000 (Nat.pow_le_pow_left hinput 4)
    nlinarith
  have hradius := scalarRadiusRun_steps_le data z
  have hb2 := Nat.pow_le_pow_left hBT 2
  have ht2 : T ^ 2 ≤ T ^ 4 := Nat.pow_le_pow_right hT (by omega)
  simp only [scalarGaussianWeightRun, Costed.bind_steps, scalarRadiusRun_value]
  change _ ≤ 102000000000000 * T ^ 4
  change (scalarRadiusRun data z).steps ≤ 200 * B ^ 2 at hradius
  nlinarith

theorem scalarGaussianWeightRun_polynomial :
    Costed.PolynomialTime
      (fun input : ScalarGaussianData × ℤ => scalarGaussianWeightRun input.1 input.2)
      (fun input => input.1.Valid) (fun input => input.1.bits + input.2.natAbs.size) := by
  refine ⟨102000000000000, 4, ?_⟩
  intro input hvalid t
  exact scalarGaussianWeightRun_steps_le input.1 hvalid input.2 t

end SISToKSIS

open GeometricGaussianLHL
namespace SISToKSIS
set_option backward.isDefEq.respectTransparency false

/-- A power-of-two square-root cover, selected from bit lengths alone. -/
def dyadicSqrtBits (u v : ℕ) : ℕ := (u.size - v.size + 2) / 2

/-- Count input bits, compute the exponent, and materialize its binary word. -/
def dyadicSqrtRun (u v : ℕ) : Costed (ℕ × ℕ) :=
  let b := dyadicSqrtBits u v
  ⟨(b, 2 ^ b), 10 * (u.size + v.size + 1) ^ 2 + b + 1⟩

@[simp] theorem dyadicSqrtRun_value (u v : ℕ) :
    (dyadicSqrtRun u v).value = (dyadicSqrtBits u v, 2 ^ dyadicSqrtBits u v) := rfl

theorem dyadicSqrtBits_le (u v : ℕ) : dyadicSqrtBits u v ≤ u.size + 1 := by
  unfold dyadicSqrtBits
  omega

theorem dyadicSqrt_bounds {u v : ℕ} (hv : 0 < v) (huv : v ≤ u) :
    u ≤ (2 ^ dyadicSqrtBits u v) ^ 2 * v ∧
      (2 ^ dyadicSqrtBits u v) ^ 2 * v ≤ 16 * u := by
  have hu : 0 < u := hv.trans_le huv
  have hvsize : 0 < v.size := Nat.size_pos.mpr hv
  have husize : 0 < u.size := Nat.size_pos.mpr hu
  have hs : v.size ≤ u.size := Nat.size_le_size huv
  have hvlo : 2 ^ (v.size - 1) ≤ v := Nat.lt_size.mp (by omega)
  have hulo : 2 ^ (u.size - 1) ≤ u := Nat.lt_size.mp (by omega)
  have hbitslo : u.size ≤ 2 * dyadicSqrtBits u v + (v.size - 1) := by
    unfold dyadicSqrtBits
    omega
  have hbitshi : 2 * dyadicSqrtBits u v + v.size ≤ (u.size - 1) + 4 := by
    unfold dyadicSqrtBits
    omega
  constructor
  · calc
      u ≤ 2 ^ u.size := (Nat.lt_size_self u).le
      _ ≤ 2 ^ (2 * dyadicSqrtBits u v + (v.size - 1)) := Nat.pow_le_pow_right (by omega) hbitslo
      _ = (2 ^ dyadicSqrtBits u v) ^ 2 * 2 ^ (v.size - 1) := by rw [pow_add, pow_mul']
      _ ≤ _ := Nat.mul_le_mul_left _ hvlo
  · calc
      _ ≤ (2 ^ dyadicSqrtBits u v) ^ 2 * 2 ^ v.size :=
        Nat.mul_le_mul_left _ (Nat.lt_size_self v).le
      _ = 2 ^ (2 * dyadicSqrtBits u v + v.size) := by rw [pow_add, pow_mul']
      _ ≤ 2 ^ ((u.size - 1) + 4) := Nat.pow_le_pow_right (by omega) hbitshi
      _ = 16 * 2 ^ (u.size - 1) := by rw [pow_add]; ring
      _ ≤ 16 * u := Nat.mul_le_mul_left _ hulo

theorem dyadicSqrt_real_bounds {u v : ℕ} (hv : 0 < v) (huv : v ≤ u) :
    Real.sqrt ((u : ℝ) / v) ≤ (2 : ℝ) ^ dyadicSqrtBits u v ∧
      (2 : ℝ) ^ dyadicSqrtBits u v ≤ 4 * Real.sqrt ((u : ℝ) / v) := by
  have h := dyadicSqrt_bounds hv huv
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  have hl : (u : ℝ) / v ≤ ((2 : ℝ) ^ dyadicSqrtBits u v) ^ 2 :=
    (div_le_iff₀ hvR).mpr (by exact_mod_cast h.1)
  have hh : ((2 : ℝ) ^ dyadicSqrtBits u v) ^ 2 ≤ 16 * ((u : ℝ) / v) := by
    rw [← mul_div_assoc]
    exact (le_div_iff₀ hvR).mpr (by exact_mod_cast h.2)
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ (u : ℝ) / v by positivity)
  have hs0 := Real.sqrt_nonneg ((u : ℝ) / v)
  have hr : (0 : ℝ) ≤ 2 ^ dyadicSqrtBits u v := by positivity
  constructor <;> nlinarith

theorem dyadicSqrtRun_size (u v : ℕ) :
    (dyadicSqrtRun u v).value.2.size ≤ u.size + 2 := by
  simp only [dyadicSqrtRun_value, Nat.size_pow]
  have h := dyadicSqrtBits_le u v
  omega

theorem dyadicSqrtRun_steps_le (u v : ℕ) :
    (dyadicSqrtRun u v).steps ≤ 12 * (u.size + v.size + 1) ^ 2 := by
  have h := dyadicSqrtBits_le u v
  have hlin : u.size + v.size + 1 ≤ (u.size + v.size + 1) ^ 2 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (show 1 ≤ u.size + v.size + 1 by omega)
      (show 1 ≤ 2 by omega)
  simp only [dyadicSqrtRun]
  nlinarith

end SISToKSIS
open GeometricGaussianLHL
namespace SISToKSIS
set_option backward.isDefEq.respectTransparency false

def gaussianRadiusBits (data : ScalarGaussianData) (T : ℕ) : ℕ :=
  dyadicSqrtBits (T * T * data.widthSqNum) data.widthSqDen

/-- Choose a binary proposal radius covering `T` Gaussian widths. -/
def gaussianRadiusRun (data : ScalarGaussianData) (T : ℕ) : Costed (ℕ × ℕ) :=
  (costedNatMul T T).bind fun T2 =>
  (costedNatMul T2 data.widthSqNum).bind fun u => dyadicSqrtRun u data.widthSqDen

@[simp] theorem gaussianRadiusRun_value (data : ScalarGaussianData) (T : ℕ) :
    (gaussianRadiusRun data T).value = (gaussianRadiusBits data T, 2 ^ gaussianRadiusBits data T) := by
  simp only [gaussianRadiusRun, Costed.bind_value, costedNatMul, dyadicSqrtRun_value,
    gaussianRadiusBits, pow_two]

theorem gaussianRadius_bounds (data : ScalarGaussianData) (hdata : data.Valid)
    {T : ℕ} (hT : 0 < T) (hwidth : 1 ≤ data.widthSq) :
    (T : ℝ) * Real.sqrt data.widthSq ≤ (2 : ℝ) ^ gaussianRadiusBits data T ∧
      (2 : ℝ) ^ gaussianRadiusBits data T ≤ 4 * T * Real.sqrt data.widthSq := by
  have hvR : (0 : ℝ) < data.widthSqDen := by exact_mod_cast hdata.2.2
  have hvu : data.widthSqDen ≤ data.widthSqNum := by
    exact_mod_cast (one_le_div hvR).mp hwidth
  have hscaled : data.widthSqDen ≤ T ^ 2 * data.widthSqNum := by
    have hT2 : 1 ≤ T ^ 2 := one_le_pow₀ hT
    nlinarith
  have h := dyadicSqrt_real_bounds hdata.2.2 hscaled
  have he : Real.sqrt (((T ^ 2 * data.widthSqNum : ℕ) : ℝ) / data.widthSqDen) =
      (T : ℝ) * Real.sqrt data.widthSq := by
    rw [Nat.cast_mul, Nat.cast_pow, mul_div_assoc, Real.sqrt_mul (sq_nonneg _),
      Real.sqrt_sq_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
    rfl
  rw [he] at h
  constructor
  · simpa only [gaussianRadiusBits, pow_two] using h.1
  · simpa only [gaussianRadiusBits, pow_two, mul_assoc] using h.2

theorem gaussianRadiusBits_le (data : ScalarGaussianData) (T : ℕ) :
    gaussianRadiusBits data T ≤ 3 * (data.bits + T + 1) := by
  have hT : T.size ≤ T := Nat.size_le.mpr Nat.lt_two_pow_self
  have hnum : data.widthSqNum.size ≤ data.bits := by dsimp [ScalarGaussianData.bits]; omega
  have hsquare : (T ^ 2).size ≤ 2 * T.size + 1 := by
    simpa only [pow_two, two_mul] using natural_mul_size_le T T
  have hmul := natural_mul_size_le (T ^ 2) data.widthSqNum
  have h := dyadicSqrtBits_le (T ^ 2 * data.widthSqNum) data.widthSqDen
  have h' : gaussianRadiusBits data T ≤ (T ^ 2 * data.widthSqNum).size + 1 := by
    simpa only [gaussianRadiusBits, pow_two] using h
  omega

theorem gaussianRadiusRun_steps_le (data : ScalarGaussianData) (T : ℕ) :
    (gaussianRadiusRun data T).steps ≤ 1000 * (data.bits + T + 1) ^ 2 := by
  let B := data.bits + T + 1
  have hB : 1 ≤ B := by dsimp [B]; omega
  have hT : T.size ≤ T := Nat.size_le.mpr Nat.lt_two_pow_self
  have hnum : data.widthSqNum.size ≤ data.bits := by dsimp [ScalarGaussianData.bits]; omega
  have hden : data.widthSqDen.size ≤ data.bits := by dsimp [ScalarGaussianData.bits]; omega
  have hsquare : (T ^ 2).size ≤ 2 * T.size + 1 := by
    simpa only [pow_two, two_mul] using natural_mul_size_le T T
  have hu : (T ^ 2 * data.widthSqNum).size ≤ 3 * B := by
    apply (natural_mul_size_le _ _).trans
    dsimp [B]
    omega
  have hbits : (T ^ 2 * data.widthSqNum).size + data.widthSqDen.size + 1 ≤ 5 * B := by
    dsimp [B] at *
    omega
  have hd := dyadicSqrtRun_steps_le (T ^ 2 * data.widthSqNum) data.widthSqDen
  have hd' : (dyadicSqrtRun (T ^ 2 * data.widthSqNum) data.widthSqDen).steps ≤ 300 * B ^ 2 := by
    apply hd.trans
    have h := Nat.mul_le_mul_left 12 (Nat.pow_le_pow_left hbits 2)
    nlinarith
  have hmul1 := Nat.pow_le_pow_left (show T.size + T.size + 1 ≤ 3 * B by dsimp [B]; omega) 2
  have hmul2 := Nat.pow_le_pow_left
    (show (T ^ 2).size + data.widthSqNum.size + 1 ≤ 4 * B by dsimp [B]; omega) 2
  simp only [gaussianRadiusRun, Costed.bind_steps, costedNatMul]
  rw [← pow_two T]
  change (T.size + T.size + 1) ^ 2 + (((T ^ 2).size + data.widthSqNum.size + 1) ^ 2 +
    (dyadicSqrtRun (T ^ 2 * data.widthSqNum) data.widthSqDen).steps) ≤ 1000 * B ^ 2
  nlinarith

end SISToKSIS
open GeometricGaussianLHL
namespace SISToKSIS
set_option backward.isDefEq.respectTransparency false

def scalarCenterFloor (data : ScalarGaussianData) : ℤ := data.centerNum / data.centerDen

def scalarCenterFloorRun (data : ScalarGaussianData) : Costed ℤ :=
  (Costed.charge (data.centerDen.size + 1) (data.centerDen : ℤ)).bind fun d =>
    costedIntDiv data.centerNum d

@[simp] theorem scalarCenterFloorRun_value (data : ScalarGaussianData) :
    (scalarCenterFloorRun data).value = scalarCenterFloor data := rfl

theorem scalarCenterFloor_eq (data : ScalarGaussianData) :
    scalarCenterFloor data = ⌊data.center⌋ := by
  rw [ScalarGaussianData.center, Int.floor_div_natCast, Int.floor_intCast]
  rfl

theorem scalarCenterFloor_size (data : ScalarGaussianData) :
    (scalarCenterFloor data).natAbs.size ≤ data.centerNum.natAbs.size :=
  Nat.size_le_size (Int.natAbs_ediv_le_natAbs _ _)

theorem scalarCenterFloorRun_steps_le (data : ScalarGaussianData) :
    (scalarCenterFloorRun data).steps ≤ 2 * (data.bits + 1) ^ 2 := by
  have h : data.centerNum.natAbs.size + data.centerDen.size + 1 ≤ data.bits + 1 := by
    dsimp [ScalarGaussianData.bits]
    omega
  have hden : data.centerDen.size + 1 ≤ data.bits + 1 := by dsimp [ScalarGaussianData.bits]; omega
  have hp := Nat.pow_le_pow_left h 2
  have hlin : data.bits + 1 ≤ (data.bits + 1) ^ 2 := by nlinarith
  simp only [scalarCenterFloorRun, Costed.bind_steps, Costed.charge, costedIntDiv,
    integerOperandBits, Int.natAbs_natCast]
  omega

/-- Decode a uniform binary word as an integer in the centered proposal interval. -/
def gaussianProposalPoint (data : ScalarGaussianData) (b : ℕ) (i : Fin (2 ^ (b + 1))) : ℤ :=
  scalarCenterFloor data - (2 ^ b : ℕ) + i.val

theorem gaussianProposalPoint_injective (data : ScalarGaussianData) (b : ℕ) :
    Function.Injective (gaussianProposalPoint data b) := by
  intro i j h
  apply Fin.ext
  unfold gaussianProposalPoint at h
  omega

theorem gaussianProposalPoint_mem (data : ScalarGaussianData) (b : ℕ) (i : Fin (2 ^ (b + 1))) :
    scalarCenterFloor data - (2 ^ b : ℕ) ≤ gaussianProposalPoint data b i ∧
      gaussianProposalPoint data b i < scalarCenterFloor data + (2 ^ b : ℕ) := by
  have hi := i.isLt
  have hi' : i.val < 2 ^ b * 2 := by simpa only [pow_succ] using hi
  have hiI : (i.val : ℤ) < ((2 ^ b : ℕ) : ℤ) + ((2 ^ b : ℕ) : ℤ) := by
    exact_mod_cast (show i.val < 2 ^ b + 2 ^ b by omega)
  unfold gaussianProposalPoint
  constructor
  · exact le_add_of_nonneg_right (Nat.cast_nonneg _)
  · calc
      _ < scalarCenterFloor data - ((2 ^ b : ℕ) : ℤ) +
          (((2 ^ b : ℕ) : ℤ) + ((2 ^ b : ℕ) : ℤ)) := by omega
      _ = _ := by ring

theorem gaussianProposalPoint_surjective (data : ScalarGaussianData) (b : ℕ) (z : ℤ)
    (hzlo : scalarCenterFloor data - (2 ^ b : ℕ) ≤ z)
    (hzhi : z < scalarCenterFloor data + (2 ^ b : ℕ)) :
    ∃ i : Fin (2 ^ (b + 1)), gaussianProposalPoint data b i = z := by
  let j : ℤ := z - scalarCenterFloor data + (2 ^ b : ℕ)
  have hj : 0 ≤ j := by dsimp [j]; push_cast at *; omega
  have hjlt : j < (2 ^ (b + 1) : ℕ) := by
    rw [pow_succ]
    push_cast
    dsimp [j]
    push_cast at *
    omega
  refine ⟨⟨j.toNat, ?_⟩, ?_⟩
  · have hcast : (j.toNat : ℤ) = j := Int.toNat_of_nonneg hj
    omega
  · simp only [gaussianProposalPoint, Int.toNat_of_nonneg hj]
    dsimp [j]
    omega

/-- All points within `R-1` of the real center occur in the binary proposal. -/
theorem gaussianProposalPoint_covers (data : ScalarGaussianData) (b : ℕ) (z : ℤ)
    (hz : |(z : ℝ) - data.center| ≤ (2 : ℝ) ^ b - 1) :
    ∃ i : Fin (2 ^ (b + 1)), gaussianProposalPoint data b i = z := by
  have hfloor : (scalarCenterFloor data : ℝ) ≤ data.center := by
    rw [scalarCenterFloor_eq]
    exact Int.floor_le _
  have hfloor' : data.center < (scalarCenterFloor data : ℝ) + 1 := by
    rw [scalarCenterFloor_eq]
    exact Int.lt_floor_add_one _
  obtain ⟨hzlo, hzhi⟩ := abs_le.mp hz
  apply gaussianProposalPoint_surjective
  · have h : (scalarCenterFloor data : ℝ) - (2 : ℝ) ^ b ≤ z := by linarith
    exact_mod_cast h
  · have h : (z : ℝ) < (scalarCenterFloor data : ℝ) + (2 : ℝ) ^ b := by linarith
    exact_mod_cast h

end SISToKSIS
open GeometricGaussianLHL
namespace SISToKSIS
set_option backward.isDefEq.respectTransparency false

def gaussianInnerIndex {b F : ℕ} (hF : F ≤ 2 ^ b) : Fin F ↪ Fin (2 ^ (b + 1)) where
  toFun j := ⟨2 ^ b + j.val, by have hj := j.isLt; rw [pow_succ]; omega⟩
  inj' := by intro i j h; apply Fin.ext; have h' := congrArg Fin.val h; dsimp at h'; omega

theorem gaussianProposalPoint_inner (data : ScalarGaussianData) {b F : ℕ}
    (hF : F ≤ 2 ^ b) (j : Fin F) :
    gaussianProposalPoint data b (gaussianInnerIndex hF j) = scalarCenterFloor data + j.val := by
  simp only [gaussianProposalPoint, gaussianInnerIndex, Function.Embedding.coeFn_mk, Nat.cast_add]
  ring

theorem gaussianInnerPoint_bound (data : ScalarGaussianData) {b F : ℕ}
    (hF : F ≤ 2 ^ b) {σ : ℝ} (hσ : 1 ≤ σ) (hFσ : (F : ℝ) ≤ σ) (j : Fin F) :
    |(gaussianProposalPoint data b (gaussianInnerIndex hF j) : ℝ) - data.center| ≤ σ := by
  have hfloor : (scalarCenterFloor data : ℝ) ≤ data.center := by
    rw [scalarCenterFloor_eq]
    exact Int.floor_le _
  have hfloor' : data.center < (scalarCenterFloor data : ℝ) + 1 := by
    rw [scalarCenterFloor_eq]
    exact Int.lt_floor_add_one _
  have hj : (j.val : ℝ) ≤ F := by exact_mod_cast j.isLt.le
  have hj0 : (0 : ℝ) ≤ j.val := by positivity
  rw [gaussianProposalPoint_inner, Int.cast_add, Int.cast_natCast]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The computed interval contains enough points with substantial weight.
The reciprocal acceptance bound depends on the tail budget, not the width. -/
theorem gaussianProposal_acceptance (data : ScalarGaussianData) (hdata : data.Valid)
    {T t : ℕ} (hT : 0 < T) (ht : 6 ≤ t) (hwidth : 1 ≤ data.widthSq) :
    2 ^ (gaussianRadiusBits data T + 1) * 2 ^ exponentialPrecision (t + 1) ≤
      (1024 * T) * ∑ i : Fin (2 ^ (gaussianRadiusBits data T + 1)),
        (scalarGaussianWeightRun data (gaussianProposalPoint data (gaussianRadiusBits data T) i) t).value := by
  classical
  let b := gaussianRadiusBits data T
  let σ := Real.sqrt data.widthSq
  let F := Nat.floor σ
  let D := 2 ^ exponentialPrecision (t + 1)
  let w : Fin (2 ^ (b + 1)) → ℕ := fun i =>
    (scalarGaussianWeightRun data (gaussianProposalPoint data b i) t).value
  have hσ : 1 ≤ σ := Real.one_le_sqrt.mpr hwidth
  have hσ0 : 0 ≤ σ := le_trans (by norm_num) hσ
  have hFpos : 1 ≤ F := by
    exact (Nat.le_floor_iff hσ0).mpr (by simpa using hσ)
  have hFσ : (F : ℝ) ≤ σ := Nat.floor_le hσ0
  have hσF : σ ≤ 2 * (F : ℝ) := by
    have h := Nat.lt_floor_add_one σ
    have hF1 : (1 : ℝ) ≤ F := by exact_mod_cast hFpos
    change σ < (F : ℝ) + 1 at h
    linarith
  have hradius := gaussianRadius_bounds data hdata hT hwidth
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hσR : σ ≤ (2 : ℝ) ^ b := by
    have hmul := le_mul_of_one_le_left hσ0 hT1
    exact hmul.trans hradius.1
  have hFR : F ≤ 2 ^ b := by exact_mod_cast hFσ.trans hσR
  let e : Fin F ↪ Fin (2 ^ (b + 1)) := gaussianInnerIndex hFR
  have hpoint (j : Fin F) : D ≤ 64 * w (e j) := by
    apply scalarGaussianWeightRun_lower data hdata _ t ht
    have ha := gaussianInnerPoint_bound data hFR hσ hFσ j
    have hs := Real.sq_sqrt (data.widthSq_pos hdata).le
    have hsq := (sq_le_sq₀ (abs_nonneg _) hσ0).mpr ha
    simpa only [sq_abs, σ, hs] using hsq
  have hsum : F * D ≤ 64 * ∑ j : Fin F, w (e j) := by
    have h := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hpoint j)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_id, ← Finset.mul_sum] using h
  have hsub : ∑ j : Fin F, w (e j) ≤ ∑ i, w i := by
    rw [← Finset.sum_map]
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  have hN : 2 ^ (b + 1) ≤ 16 * T * F := by
    have hR : (2 : ℝ) ^ b ≤ 8 * T * (F : ℝ) := by
      have hmul := mul_le_mul_of_nonneg_left hσF (show (0 : ℝ) ≤ 4 * T by positivity)
      nlinarith [hradius.2]
    have hN' : (2 : ℝ) ^ (b + 1) ≤ 16 * T * (F : ℝ) := by rw [pow_succ]; nlinarith
    exact_mod_cast hN'
  change 2 ^ (b + 1) * D ≤ (1024 * T) * ∑ i, w i
  have ha := Nat.mul_le_mul_right D hN
  have hb := Nat.mul_le_mul_left (16 * T) (hsum.trans (Nat.mul_le_mul_left 64 hsub))
  nlinarith

theorem gaussianProposal_weight_sum_pos (data : ScalarGaussianData) (hdata : data.Valid)
    {T t : ℕ} (hT : 0 < T) (ht : 6 ≤ t) (hwidth : 1 ≤ data.widthSq) :
    0 < ∑ i : Fin (2 ^ (gaussianRadiusBits data T + 1)),
      (scalarGaussianWeightRun data (gaussianProposalPoint data (gaussianRadiusBits data T) i) t).value := by
  have h := gaussianProposal_acceptance data hdata hT ht hwidth
  have hp : 0 < 2 ^ (gaussianRadiusBits data T + 1) * 2 ^ exponentialPrecision (t + 1) := by positivity
  nlinarith

end SISToKSIS
open GeometricGaussianLHL
namespace SISToKSIS
set_option backward.isDefEq.respectTransparency false

/-- Decode one proposal word with the arithmetic costs of centering and casts. -/
def gaussianProposalPointRun (data : ScalarGaussianData) (b : ℕ) (i : Fin (2 ^ (b + 1))) : Costed ℤ :=
  let center := scalarCenterFloorRun data
  let lo := costedIntSub center.value (2 ^ b : ℕ)
  let result := costedIntAdd lo.value i.val
  ⟨result.value, center.steps + (2 * (b + 2) + (i.val.size + 1 + (lo.steps + result.steps)))⟩

@[simp] theorem gaussianProposalPointRun_value (data : ScalarGaussianData) (b : ℕ)
    (i : Fin (2 ^ (b + 1))) : (gaussianProposalPointRun data b i).value = gaussianProposalPoint data b i := rfl

theorem gaussianProposalPoint_size (data : ScalarGaussianData) (b : ℕ) (i : Fin (2 ^ (b + 1))) :
    (gaussianProposalPoint data b i).natAbs.size ≤ data.bits + b + 5 := by
  have hc : (scalarCenterFloor data).natAbs.size ≤ data.bits :=
    (scalarCenterFloor_size data).trans (by dsimp [ScalarGaussianData.bits]; omega)
  have hR : ((2 ^ b : ℕ) : ℤ).natAbs.size = b + 1 := by simp [Nat.size_pow]
  have hi : i.val.size ≤ b + 1 := Nat.size_le.mpr i.isLt
  have hlo := integer_sub_size_le (scalarCenterFloor data) ((2 ^ b : ℕ) : ℤ)
    (data.bits + b + 1) (by omega) (by omega)
  have hpoint := integer_sub_size_le (scalarCenterFloor data - (2 ^ b : ℕ)) (-(i.val : ℤ))
    (data.bits + b + 3) (by omega) (by simpa using hi.trans (by omega))
  simpa only [sub_neg_eq_add, gaussianProposalPoint] using hpoint

theorem gaussianProposalPointRun_steps_le (data : ScalarGaussianData) (b : ℕ)
    (i : Fin (2 ^ (b + 1))) :
    (gaussianProposalPointRun data b i).steps ≤ 20 * (data.bits + b + 1) ^ 2 := by
  let B := data.bits + b + 1
  have hB : 1 ≤ B := by dsimp [B]; omega
  have hc : (scalarCenterFloor data).natAbs.size ≤ data.bits :=
    (scalarCenterFloor_size data).trans (by dsimp [ScalarGaussianData.bits]; omega)
  have hR : ((2 ^ b : ℕ) : ℤ).natAbs.size = b + 1 := by simp [Nat.size_pow]
  have hi : i.val.size ≤ b + 1 := Nat.size_le.mpr i.isLt
  have hlo := integer_sub_size_le (scalarCenterFloor data) ((2 ^ b : ℕ) : ℤ)
    B (by dsimp [B]; omega) (by
      simpa only [Int.natAbs_pow, Int.natAbs_natCast, Nat.size_pow] using
        (show b + 1 ≤ B by dsimp [B]; omega))
  have hcenter := scalarCenterFloorRun_steps_le data
  have hcenter' : (scalarCenterFloorRun data).steps ≤ 2 * B ^ 2 := by
    apply hcenter.trans
    exact Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left (by dsimp [B]; omega) 2)
  have hlin : B ≤ B ^ 2 := by nlinarith
  simp only [gaussianProposalPointRun, costedIntSub, costedIntAdd, integerOperandBits,
    scalarCenterFloorRun_value, Int.natAbs_natCast, Nat.size_pow]
  dsimp only [B] at *
  nlinarith

def gaussianProposalWeightRun (data : ScalarGaussianData) (b t : ℕ)
    (i : Fin (2 ^ (b + 1))) : Costed ℕ :=
  let point := gaussianProposalPointRun data b i
  let weight := scalarGaussianWeightRun data point.value t
  ⟨weight.value, point.steps + weight.steps⟩

@[simp] theorem gaussianProposalWeightRun_value (data : ScalarGaussianData) (b t : ℕ)
    (i : Fin (2 ^ (b + 1))) :
    (gaussianProposalWeightRun data b t i).value =
      (scalarGaussianWeightRun data (gaussianProposalPoint data b i) t).value := rfl

def gaussianProposalWeightBudget (data : ScalarGaussianData) (b t : ℕ) : ℕ :=
  20 * (data.bits + b + 1) ^ 2 + 102000000000000 * (2 * data.bits + b + t + 6) ^ 4

theorem gaussianProposalWeightRun_steps_le (data : ScalarGaussianData) (hdata : data.Valid)
    (b t : ℕ) (i : Fin (2 ^ (b + 1))) :
    (gaussianProposalWeightRun data b t i).steps ≤ gaussianProposalWeightBudget data b t := by
  have hpoint := gaussianProposalPointRun_steps_le data b i
  have hweight := scalarGaussianWeightRun_steps_le data hdata (gaussianProposalPoint data b i) t
  have hsize := gaussianProposalPoint_size data b i
  have hpow := Nat.mul_le_mul_left 102000000000000 (Nat.pow_le_pow_left
    (show data.bits + (gaussianProposalPoint data b i).natAbs.size + t + 1 ≤
      2 * data.bits + b + t + 6 by omega) 4)
  change (gaussianProposalPointRun data b i).steps +
    (scalarGaussianWeightRun data (gaussianProposalPoint data b i) t).steps ≤ _
  exact Nat.add_le_add hpoint (hweight.trans hpow)

end SISToKSIS

open GeometricGaussianLHL
namespace SISToKSIS
set_option backward.isDefEq.respectTransparency false

def gaussianFallbackIndex (b : ℕ) : Fin (2 ^ (b + 1)) :=
  ⟨2 ^ b, by
    rw [pow_succ]
    have h : 0 < 2 ^ b := by positivity
    omega⟩

abbrev ScalarGaussianTape (data : ScalarGaussianData) (T t q : ℕ) :=
  Fin (1024 * T * q) → Fin (2 ^ (gaussianRadiusBits data T + 1)) ×
    Fin (2 ^ exponentialPrecision (t + 1))

/-- Finite rejection sampler for the rounded Gaussian weights on the computed
proposal interval. Its distance to the full Gaussian also requires a tail bound. -/
def boundedScalarGaussianRun (data : ScalarGaussianData) (T t q : ℕ)
    (tape : ScalarGaussianTape data T t q) : Costed ℤ :=
  let radius := gaussianRadiusRun data T
  let b := radius.value.1
  let sample := dyadicRejectionRun (gaussianProposalWeightRun data b t)
    (gaussianFallbackIndex b) (1024 * T * q) tape
  let point := gaussianProposalPointRun data b sample.value
  ⟨point.value, radius.steps + sample.steps + point.steps⟩

@[simp] theorem boundedScalarGaussianRun_value (data : ScalarGaussianData) (T t q : ℕ)
    (tape : ScalarGaussianTape data T t q) :
    (boundedScalarGaussianRun data T t q tape).value =
      gaussianProposalPoint data (gaussianRadiusBits data T)
        (dyadicRejectionRun (gaussianProposalWeightRun data (gaussianRadiusBits data T) t)
          (gaussianFallbackIndex (gaussianRadiusBits data T)) (1024 * T * q) tape).value := rfl

theorem boundedScalarGaussianRun_steps_le (data : ScalarGaussianData) (hdata : data.Valid)
    (T t q : ℕ) (tape : ScalarGaussianTape data T t q) :
    (boundedScalarGaussianRun data T t q tape).steps ≤
      1000 * (data.bits + T + 1) ^ 2 +
      (1024 * T * q) * ((gaussianRadiusBits data T + 1) +
        3 * exponentialPrecision (t + 1) + gaussianProposalWeightBudget data (gaussianRadiusBits data T) t +
        (1024 * T * q) + 3) + 20 * (data.bits + gaussianRadiusBits data T + 1) ^ 2 := by
  have hradius := gaussianRadiusRun_steps_le data T
  have hsampler := dyadicRejectionRun_steps_le
    (weight := gaussianProposalWeightRun data (gaussianRadiusBits data T) t)
    (fallback := gaussianFallbackIndex (gaussianRadiusBits data T))
    (hweight := fun i => by
      simpa only [gaussianProposalWeightRun_value] using
        scalarGaussianWeightRun_bound data hdata (gaussianProposalPoint data (gaussianRadiusBits data T) i) t)
    (hcost := gaussianProposalWeightRun_steps_le data hdata (gaussianRadiusBits data T) t)
    (fuel := 1024 * T * q) tape
  have hpoint := gaussianProposalPointRun_steps_le data (gaussianRadiusBits data T)
    (dyadicRejectionRun (gaussianProposalWeightRun data (gaussianRadiusBits data T) t)
      (gaussianFallbackIndex (gaussianRadiusBits data T)) (1024 * T * q) tape).value
  exact Nat.add_le_add (Nat.add_le_add hradius hsampler) hpoint

noncomputable section

def boundedScalarGaussianLaw (data : ScalarGaussianData) (T t q : ℕ) : PMF ℤ :=
  (independentProduct (fun _ : Fin (1024 * T * q) =>
    jointPMF (PMF.uniformOfFintype (Fin (2 ^ (gaussianRadiusBits data T + 1))))
      (fun _ => PMF.uniformOfFintype (Fin (2 ^ exponentialPrecision (t + 1)))))).map
    (fun tape => (boundedScalarGaussianRun data T t q tape).value)

theorem boundedScalarGaussianLaw_eq (data : ScalarGaussianData) (T t q : ℕ) :
    boundedScalarGaussianLaw data T t q =
      (dyadicRejectionLaw (acceptanceBits := exponentialPrecision (t + 1))
        (gaussianProposalWeightRun data (gaussianRadiusBits data T) t)
        (gaussianFallbackIndex (gaussianRadiusBits data T)) (1024 * T * q)).map
        (gaussianProposalPoint data (gaussianRadiusBits data T)) := by
  simp only [boundedScalarGaussianLaw, dyadicRejectionLaw, PMF.map_comp, Function.comp_def,
    boundedScalarGaussianRun_value]

theorem boundedScalarGaussianLaw_error (data : ScalarGaussianData) (hdata : data.Valid)
    {T t : ℕ} (hT : 0 < T) (ht : 6 ≤ t) (hwidth : 1 ≤ data.widthSq) (q : ℕ) :
    discreteTotalVariation (boundedScalarGaussianLaw data T t q)
      ((finiteWeightLaw (fun i =>
        (scalarGaussianWeightRun data (gaussianProposalPoint data (gaussianRadiusBits data T) i) t).value)
        (gaussianProposal_weight_sum_pos data hdata hT ht hwidth)).map
        (gaussianProposalPoint data (gaussianRadiusBits data T))) ≤ (1 / 2 : ℝ) ^ q := by
  have h := dyadicRejectionLaw_error_of_budget
    (acceptanceBits := exponentialPrecision (t + 1)) (L := 1024 * T)
    (gaussianProposalWeightRun data (gaussianRadiusBits data T) t)
    (gaussianFallbackIndex (gaussianRadiusBits data T))
    (fun i => by simpa only [gaussianProposalWeightRun_value] using
      scalarGaussianWeightRun_bound data hdata (gaussianProposalPoint data (gaussianRadiusBits data T) i) t)
    (by simpa only [gaussianProposalWeightRun_value] using gaussianProposal_weight_sum_pos data hdata hT ht hwidth)
    (by simpa only [gaussianProposalWeightRun_value] using gaussianProposal_acceptance data hdata hT ht hwidth) q
  rw [boundedScalarGaussianLaw_eq]
  simpa only [gaussianProposalWeightRun_value] using (discreteTotalVariation_map_le _ _ _).trans h

end
end SISToKSIS
open GeometricGaussianLHL
namespace SISToKSIS
set_option backward.isDefEq.respectTransparency false

/-- Uniform finite-tape cost: the security and truncation budgets are charged
by their values, and all field data by their integer bit lengths. -/
theorem boundedScalarGaussianRun_polynomial_bound (data : ScalarGaussianData) (hdata : data.Valid)
    (T t q : ℕ) (tape : ScalarGaussianTape data T t q) :
    (boundedScalarGaussianRun data T t q tape).steps ≤ 5000000000000000000000 *
      (data.bits + T + t + q + 1) ^ 6 := by
  let B := data.bits + T + t + q + 1
  let b := gaussianRadiusBits data T
  let F := 1024 * T * q
  let C := gaussianProposalWeightBudget data b t
  have hB : 1 ≤ B := by dsimp [B]; omega
  have hd : data.bits ≤ B := by dsimp [B]; omega
  have hT : T ≤ B := by dsimp [B]; omega
  have ht : t ≤ B := by dsimp [B]; omega
  have hq : q ≤ B := by dsimp [B]; omega
  have hb : b ≤ 3 * B := by
    have h := gaussianRadiusBits_le data T
    dsimp only [b, B]
    omega
  have hRinput : data.bits + T + 1 ≤ B := by dsimp [B]; omega
  have hF : F ≤ 1024 * B ^ 2 := by
    have h := Nat.mul_le_mul hT hq
    dsimp [F]
    nlinarith
  have hPinput : data.bits + b + 1 ≤ 5 * B := by omega
  have hWinput : 2 * data.bits + b + t + 6 ≤ 12 * B := by omega
  have hPpow := Nat.pow_le_pow_left hPinput 2
  have hWpow := Nat.pow_le_pow_left hWinput 4
  have hB14 : B ≤ B ^ 4 := by
    simpa only [pow_one] using Nat.pow_le_pow_right hB (show 1 ≤ 4 by omega)
  have hB24 : B ^ 2 ≤ B ^ 4 := Nat.pow_le_pow_right hB (by omega)
  have hC : C ≤ 3000000000000000000 * B ^ 4 := by
    dsimp [C, gaussianProposalWeightBudget]
    nlinarith
  have hacc : exponentialPrecision (t + 1) ≤ 18 * B := by
    unfold exponentialPrecision exponentialRounds
    omega
  have hinner : b + 1 + 3 * exponentialPrecision (t + 1) + C + F + 3 ≤
      4000000000000000000 * B ^ 4 := by nlinarith
  have hloop : F * (b + 1 + 3 * exponentialPrecision (t + 1) + C + F + 3) ≤
      4096000000000000000000 * B ^ 6 := by
    have h := Nat.mul_le_mul hF hinner
    nlinarith
  have hrun := boundedScalarGaussianRun_steps_le data hdata T t q tape
  have hRpow := Nat.pow_le_pow_left hRinput 2
  have hB26 : B ^ 2 ≤ B ^ 6 := Nat.pow_le_pow_right hB (by omega)
  change (boundedScalarGaussianRun data T t q tape).steps ≤
    1000 * (data.bits + T + 1) ^ 2 +
    F * (b + 1 + 3 * exponentialPrecision (t + 1) + C + F + 3) +
    20 * (data.bits + b + 1) ^ 2 at hrun
  change _ ≤ 5000000000000000000000 * B ^ 6
  nlinarith

end SISToKSIS

open GeometricGaussianLHL
namespace SISToKSIS
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem scaled_mass_totalVariation_le {α : Type*} (p q : PMF α) (c : ℝ) :
    discreteTotalVariation p q ≤ ∑' a, |c * (p a).toReal - (q a).toReal| := by
  have hd := ((pmf_summable_toReal p).mul_left c).sub (pmf_summable_toReal q)
  have ha : Summable (fun a => |c * (p a).toReal - (q a).toReal|) := by
    simpa only [Real.norm_eq_abs] using hd.norm
  have hscale : |c - 1| ≤ ∑' a, |c * (p a).toReal - (q a).toReal| := by
    have h := norm_tsum_le_tsum_norm hd.norm
    rw [Summable.tsum_sub ((pmf_summable_toReal p).mul_left c) (pmf_summable_toReal q)] at h
    simpa only [tsum_mul_left, pmf_tsum_toReal, mul_one, Real.norm_eq_abs] using h
  have hpoint (a : α) : |(p a).toReal - (q a).toReal| ≤
      |1 - c| * (p a).toReal + |c * (p a).toReal - (q a).toReal| := by
    have h := abs_sub_le (p a).toReal (c * (p a).toReal) (q a).toReal
    have he : |(p a).toReal - c * (p a).toReal| = |1 - c| * (p a).toReal := by
      rw [show (p a).toReal - c * (p a).toReal = (1 - c) * (p a).toReal by ring,
        abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
    rwa [he] at h
  have hsum := (pmf_summable_abs_sub p q).tsum_le_tsum hpoint
    (((pmf_summable_toReal p).mul_left |1 - c|).add ha)
  rw [Summable.tsum_add ((pmf_summable_toReal p).mul_left |1 - c|) ha,
    tsum_mul_left, pmf_tsum_toReal, mul_one, abs_sub_comm 1 c] at hsum
  unfold discreteTotalVariation
  linarith

/-- Normalized finite weights may be compared directly with an infinite target
law. The error separates into pointwise rounding and omitted target mass. -/
theorem finiteWeightLaw_map_error {α : Type*} [DecidableEq α] {N : ℕ}
    (f : Fin N → α) (hf : Function.Injective f) (weight : Fin N → ℕ)
    (hpos : 0 < ∑ i, weight i) (target : PMF α) {D Z ε : ℝ}
    (hD : 0 < D) (hZ : 0 < Z)
    (hpoint : ∀ i, |(weight i : ℝ) / D - Z * (target (f i)).toReal| ≤ ε) :
    discreteTotalVariation ((finiteWeightLaw weight hpos).map f) target ≤
      (N : ℝ) * ε / Z + ∑' a : {a // a ∉ Finset.univ.image f}, (target a).toReal := by
  classical
  let p := (finiteWeightLaw weight hpos).map f
  let c : ℝ := ((∑ i, weight i : ℕ) : ℝ) / D / Z
  let S := Finset.univ.image f
  have hW : (((∑ i, weight i : ℕ) : ℝ)) ≠ 0 := by exact_mod_cast hpos.ne'
  have hmap (i : Fin N) : p (f i) = finiteWeightLaw weight hpos i := by
    simp [p, PMF.map_apply, tsum_fintype, hf.eq_iff]
  have hout (a : α) (ha : a ∉ S) : p a = 0 := by
    simp only [p, PMF.map_apply, tsum_fintype]
    apply Finset.sum_eq_zero
    intro i hi
    apply ite_eq_right
    intro he
    exact ha (Finset.mem_image.mpr ⟨i, hi, he.symm⟩)
  have hscaled (i : Fin N) : |c * (p (f i)).toReal - (target (f i)).toReal| ≤ ε / Z := by
    have he : c * (p (f i)).toReal - (target (f i)).toReal =
        ((weight i : ℝ) / D - Z * (target (f i)).toReal) / Z := by
      rw [hmap]
      simp only [finiteWeightLaw_apply, ENNReal.toReal_div, ENNReal.toReal_natCast]
      dsimp [c]
      field_simp
    rw [he, abs_div, abs_of_pos hZ]
    exact div_le_div_of_nonneg_right (hpoint i) hZ.le
  have hsum : ∑ a ∈ S, |c * (p a).toReal - (target a).toReal| ≤ (N : ℝ) * ε / Z := by
    rw [Finset.sum_image (fun i _ j _ h => hf h)]
    have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hscaled i)
    simpa [mul_div_assoc] using h
  have ha : Summable (fun a => |c * (p a).toReal - (target a).toReal|) := by
    simpa only [Real.norm_eq_abs] using
      (((pmf_summable_toReal p).mul_left c).sub (pmf_summable_toReal target)).norm
  apply (scaled_mass_totalVariation_le p target c).trans
  rw [← ha.sum_add_tsum_subtype_compl S]
  apply add_le_add hsum
  apply le_of_eq
  apply tsum_congr
  intro a
  simp only [hout a a.property, ENNReal.toReal_zero, mul_zero, zero_sub, abs_neg,
    abs_of_nonneg ENNReal.toReal_nonneg]

end
end SISToKSIS

open GeometricGaussianLHL
namespace SISToKSIS
noncomputable section
set_option backward.isDefEq.respectTransparency false

def scalarIdealWeight (c v : ℝ) (z : ℤ) : ℝ := Real.exp (-Real.pi * ((z : ℝ) - c) ^ 2 / v)

def scalarGaussianPartition (c v : ℝ) : ℝ := ∑' z : ℤ, scalarIdealWeight c v z

theorem scalarIdealWeight_pos (c v : ℝ) (z : ℤ) : 0 < scalarIdealWeight c v z := Real.exp_pos _

theorem scalarIdealWeight_summable (c : ℝ) {v : ℝ} (hv : 0 < v) :
    Summable (scalarIdealWeight c v) := by
  have h := summable_shifted_integer_gaussian (div_pos Real.pi_pos hv) c
  convert h using 1
  funext z
  unfold scalarIdealWeight
  congr 1
  ring

theorem scalarGaussianPartition_pos (c : ℝ) {v : ℝ} (hv : 0 < v) :
    0 < scalarGaussianPartition c v :=
  (scalarIdealWeight_pos c v 0).trans_le
    ((scalarIdealWeight_summable c hv).le_tsum 0 (fun _ _ => (scalarIdealWeight_pos c v _).le))

theorem scalarIdealWeight_ofReal_sum (c : ℝ) {v : ℝ} (hv : 0 < v) :
    (∑' z : ℤ, ENNReal.ofReal (scalarIdealWeight c v z)) =
      ENNReal.ofReal (scalarGaussianPartition c v) :=
  (ENNReal.ofReal_tsum_of_nonneg (fun z => (scalarIdealWeight_pos c v z).le)
    (scalarIdealWeight_summable c hv)).symm

def scalarGaussianLaw (c v : ℝ) (hv : 0 < v) : PMF ℤ :=
  PMF.normalize (fun z => ENNReal.ofReal (scalarIdealWeight c v z))
    (by rw [scalarIdealWeight_ofReal_sum c hv]; exact ne_of_gt (ENNReal.ofReal_pos.mpr (scalarGaussianPartition_pos c hv)))
    (by rw [scalarIdealWeight_ofReal_sum c hv]; exact ENNReal.ofReal_ne_top)

theorem scalarGaussianLaw_toReal (c v : ℝ) (hv : 0 < v) (z : ℤ) :
    (scalarGaussianLaw c v hv z).toReal = scalarIdealWeight c v z / scalarGaussianPartition c v := by
  simp only [scalarGaussianLaw, PMF.normalize_apply, scalarIdealWeight_ofReal_sum c hv,
    ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (scalarIdealWeight_pos c v z).le,
    ENNReal.toReal_ofReal (scalarGaussianPartition_pos c hv).le, div_eq_mul_inv]

theorem scalarIdealWeight_near_center (c : ℝ) {v : ℝ} (hv : 0 < v) (z : ℤ)
    (hz : ((z : ℝ) - c) ^ 2 ≤ v) : (1 / 32 : ℝ) ≤ scalarIdealWeight c v z := by
  have hratio : ((z : ℝ) - c) ^ 2 / v ≤ 1 := (div_le_one hv).mpr hz
  have harg : -Real.pi ≤ -Real.pi * ((z : ℝ) - c) ^ 2 / v := by
    have h := mul_le_mul_of_nonneg_left hratio Real.pi_pos.le
    calc
      -Real.pi ≤ -(Real.pi * (((z : ℝ) - c) ^ 2 / v)) := neg_le_neg (by simpa using h)
      _ = _ := by ring
  have hpi : (1 / 32 : ℝ) ≤ Real.exp (-Real.pi) := by
    rw [Real.exp_neg, ← one_div]
    apply one_div_le_one_div_of_le (Real.exp_pos _)
    linarith [exp_pi_lt_233_div_ten]
  exact hpi.trans (Real.exp_le_exp.mpr harg)

theorem scalarGaussianPartition_lower (c : ℝ) {v : ℝ} (hv : 1 ≤ v) :
    Real.sqrt v / 64 ≤ scalarGaussianPartition c v := by
  classical
  let σ := Real.sqrt v
  let F := Nat.floor σ
  let f : Fin F → ℤ := fun j => ⌊c⌋ + j.val
  have hv0 : 0 < v := lt_of_lt_of_le (by norm_num) hv
  have hσ : 1 ≤ σ := Real.one_le_sqrt.mpr hv
  have hσ0 : 0 ≤ σ := le_trans (by norm_num) hσ
  have hFpos : 1 ≤ F := (Nat.le_floor_iff hσ0).mpr (by simpa using hσ)
  have hFσ : (F : ℝ) ≤ σ := Nat.floor_le hσ0
  have hσF : σ ≤ 2 * (F : ℝ) := by
    have h := Nat.lt_floor_add_one σ
    have hF1 : (1 : ℝ) ≤ F := by exact_mod_cast hFpos
    change σ < (F : ℝ) + 1 at h
    linarith
  have hf : Function.Injective f := by
    intro i j h
    apply Fin.ext
    dsimp [f] at h
    omega
  have hpoint (j : Fin F) : (1 / 32 : ℝ) ≤ scalarIdealWeight c v (f j) := by
    apply scalarIdealWeight_near_center c hv0
    have hfloor := Int.floor_le c
    have hfloor' := Int.lt_floor_add_one c
    have hj : (j.val : ℝ) ≤ F := by exact_mod_cast j.isLt.le
    have hj0 : (0 : ℝ) ≤ j.val := by positivity
    have habs : |(f j : ℝ) - c| ≤ σ := by
      dsimp [f]
      push_cast
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    have hs := (sq_le_sq₀ (abs_nonneg _) hσ0).mpr habs
    simpa only [sq_abs, σ, Real.sq_sqrt hv0.le] using hs
  have hsum : (F : ℝ) / 32 ≤ ∑ j : Fin F, scalarIdealWeight c v (f j) := by
    have h := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hpoint j)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one_div] using h
  have hpartial : ∑ j : Fin F, scalarIdealWeight c v (f j) ≤ scalarGaussianPartition c v := by
    rw [← Finset.sum_image (fun i _ j _ h => hf h)]
    exact (scalarIdealWeight_summable c hv0).sum_le_tsum _ (fun _ _ => (scalarIdealWeight_pos c v _).le)
  change σ / 64 ≤ _
  linarith


theorem scalarGaussianPartition_eq_periodic (c : ℝ) {v : ℝ} (hv : 0 < v) :
    scalarGaussianPartition c v = periodicGaussian (1 / Real.sqrt v) c := by
  unfold scalarGaussianPartition scalarIdealWeight periodicGaussian
  apply tsum_congr
  intro z
  congr 1
  rw [div_pow, Real.sq_sqrt hv.le]
  ring

theorem scalarGaussianPartition_upper (c : ℝ) {v : ℝ} (hv : 1 ≤ v) :
    scalarGaussianPartition c v ≤ 2 * Real.sqrt v := by
  have hv0 : 0 < v := lt_of_lt_of_le (by norm_num) hv
  have hs := Real.sqrt_pos.mpr hv0
  have hzero : periodicGaussian (1 / Real.sqrt v) 0 = integerGaussianPartition (Real.sqrt v) := by
    unfold periodicGaussian integerGaussianPartition integerTheta
    apply tsum_congr
    intro z
    congr 1
    ring
  rw [scalarGaussianPartition_eq_periodic c hv0]
  apply (periodicGaussian_le_zero (one_div_pos.mpr hs) c).trans
  rw [hzero, integerGaussianPartition_poisson hs]
  have htheta := integerTheta_antitone Real.pi_pos
    (show Real.pi ≤ Real.pi * (Real.sqrt v) ^ 2 by
      rw [Real.sq_sqrt hv0.le]
      nlinarith [Real.pi_pos])
  have hbound : integerTheta (Real.pi * (Real.sqrt v) ^ 2) ≤ 2 := by
    linarith [integerTheta_pi_upper]
  nlinarith

theorem scalarGaussianPartition_double_upper (c : ℝ) {v : ℝ} (hv : 1 ≤ v) :
    scalarGaussianPartition c (2 * v) ≤ 4 * Real.sqrt v := by
  have hv0 : 0 ≤ v := by linarith
  apply (scalarGaussianPartition_upper c (show 1 ≤ 2 * v by linarith)).trans
  have hs : Real.sqrt (2 * v) ≤ 2 * Real.sqrt v := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · nlinarith [Real.sq_sqrt hv0]
  linarith

/-- The finite proposal omits only points beyond `T-1` Gaussian widths. -/
theorem gaussianProposalPoint_outside (data : ScalarGaussianData) (hdata : data.Valid)
    {T : ℕ} (hT : 0 < T) (hwidth : 1 ≤ data.widthSq)
    (z : ℤ) (hz : z ∉ Finset.univ.image (gaussianProposalPoint data (gaussianRadiusBits data T))) :
    ((T : ℝ) - 1) * Real.sqrt data.widthSq ≤ |(z : ℝ) - data.center| := by
  have hradius := (gaussianRadius_bounds data hdata hT hwidth).1
  have hσ : 1 ≤ Real.sqrt data.widthSq := Real.one_le_sqrt.mpr hwidth
  have hout : (2 : ℝ) ^ gaussianRadiusBits data T - 1 < |(z : ℝ) - data.center| := by
    apply lt_of_not_ge
    intro h
    obtain ⟨i, hi⟩ := gaussianProposalPoint_covers data (gaussianRadiusBits data T) z h
    exact hz (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩)
  nlinarith

theorem scalarIdealWeight_tail {c v a : ℝ} (hv : 0 < v) (ha : 0 ≤ a)
    (z : ℤ) (hz : a * Real.sqrt v ≤ |(z : ℝ) - c|) :
    scalarIdealWeight c v z ≤ Real.exp (-Real.pi * a ^ 2 / 2) * scalarIdealWeight c (2 * v) z := by
  have hs : a ^ 2 * v ≤ ((z : ℝ) - c) ^ 2 := by
    have h := (sq_le_sq₀ (mul_nonneg ha (Real.sqrt_nonneg v)) (abs_nonneg _)).mpr hz
    simpa only [mul_pow, Real.sq_sqrt hv.le, sq_abs] using h
  unfold scalarIdealWeight
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hratio : a ^ 2 ≤ ((z : ℝ) - c) ^ 2 / v := (le_div_iff₀ hv).mpr hs
  have hscaled := mul_le_mul_of_nonneg_left hratio Real.pi_pos.le
  linear_combination hscaled / 2


end
end SISToKSIS

open GeometricGaussianLHL
namespace SISToKSIS
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem scalarGaussianLaw_proposal_tail (data : ScalarGaussianData) (hdata : data.Valid)
    {T : ℕ} (hT : 0 < T) (hwidth : 1 ≤ data.widthSq) :
    (∑' z : {z // z ∉ Finset.univ.image (gaussianProposalPoint data (gaussianRadiusBits data T))},
      (scalarGaussianLaw data.center data.widthSq (data.widthSq_pos hdata) z).toReal) ≤
      256 * Real.exp (-Real.pi * ((T : ℝ) - 1) ^ 2 / 2) := by
  let S := Finset.univ.image (gaussianProposalPoint data (gaussianRadiusBits data T))
  let Z := scalarGaussianPartition data.center data.widthSq
  let E := Real.exp (-Real.pi * ((T : ℝ) - 1) ^ 2 / 2)
  have hv := data.widthSq_pos hdata
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hZ : 0 < Z := scalarGaussianPartition_pos _ hv
  have hρ := scalarIdealWeight_summable data.center hv
  have hρ2 := scalarIdealWeight_summable data.center (show 0 < 2 * data.widthSq by positivity)
  have hpoint (z : {z // z ∉ S}) : scalarIdealWeight data.center data.widthSq z ≤
      E * scalarIdealWeight data.center (2 * data.widthSq) z :=
    scalarIdealWeight_tail hv (by linarith) z
      (gaussianProposalPoint_outside data hdata hT hwidth z z.property)
  have hsum := (hρ.subtype (fun z => z ∉ S)).tsum_le_tsum hpoint
    ((hρ2.subtype (fun z => z ∉ S)).mul_left E)
  rw [tsum_mul_left] at hsum
  have hsub : (∑' z : {z // z ∉ S}, scalarIdealWeight data.center (2 * data.widthSq) z) ≤
      scalarGaussianPartition data.center (2 * data.widthSq) :=
    hρ2.tsum_subtype_le _ _ (fun z => (scalarIdealWeight_pos _ _ z).le)
  have hmass : (∑' z : {z // z ∉ S}, scalarIdealWeight data.center data.widthSq z) ≤
      E * (4 * Real.sqrt data.widthSq) :=
    hsum.trans (mul_le_mul_of_nonneg_left
      (hsub.trans (scalarGaussianPartition_double_upper data.center hwidth)) (Real.exp_pos _).le)
  have hlower := scalarGaussianPartition_lower data.center hwidth
  have hscale : E * (4 * Real.sqrt data.widthSq) ≤ 256 * E * Z := by
    have h := mul_le_mul_of_nonneg_left hlower (Real.exp_pos (-Real.pi * ((T : ℝ) - 1) ^ 2 / 2)).le
    dsimp only [Z, E] at *
    nlinarith
  change (∑' z : {z // z ∉ S}, _) ≤ 256 * E
  simp only [scalarGaussianLaw_toReal]
  rw [tsum_div_const]
  exact (div_le_iff₀ hZ).mpr (hmass.trans hscale)

/-- Error of the actual finite sampler against the full scalar Gaussian. -/
theorem boundedScalarGaussianLaw_full_error (data : ScalarGaussianData) (hdata : data.Valid)
    {T t : ℕ} (hT : 0 < T) (ht : 6 ≤ t) (hwidth : 1 ≤ data.widthSq) (q : ℕ) :
    discreteTotalVariation (boundedScalarGaussianLaw data T t q)
      (scalarGaussianLaw data.center data.widthSq (data.widthSq_pos hdata)) ≤
      (1 / 2 : ℝ) ^ q + 512 * T / (2 : ℝ) ^ t +
        256 * Real.exp (-Real.pi * ((T : ℝ) - 1) ^ 2 / 2) := by
  let f := gaussianProposalPoint data (gaussianRadiusBits data T)
  let w := fun i => (scalarGaussianWeightRun data (f i) t).value
  have hw := gaussianProposal_weight_sum_pos data hdata hT ht hwidth
  let p := (finiteWeightLaw w hw).map f
  let target := scalarGaussianLaw data.center data.widthSq (data.widthSq_pos hdata)
  let Z := scalarGaussianPartition data.center data.widthSq
  have hZ : 0 < Z := scalarGaussianPartition_pos _ (data.widthSq_pos hdata)
  have hn := finiteWeightLaw_map_error f (gaussianProposalPoint_injective data _) w hw target
    (D := (2 : ℝ) ^ exponentialPrecision (t + 1)) (Z := Z) (ε := 1 / (2 : ℝ) ^ t)
    (by positivity) hZ (fun i => by
      dsimp only [target]
      rw [scalarGaussianLaw_toReal, mul_div_cancel₀ _ hZ.ne']
      exact scalarGaussianWeightRun_error data hdata (f i) t)
  have hradius := (gaussianRadius_bounds data hdata hT hwidth).2
  have hlower := scalarGaussianPartition_lower data.center hwidth
  have hratio : ((2 ^ (gaussianRadiusBits data T + 1) : ℕ) : ℝ) *
      (1 / (2 : ℝ) ^ t) / Z ≤ 512 * T / (2 : ℝ) ^ t := by
    apply (div_le_iff₀ hZ).mpr
    have hcount : (2 : ℝ) ^ (gaussianRadiusBits data T + 1) ≤ 512 * T * Z := by
      rw [pow_succ]
      have h := mul_le_mul_of_nonneg_left hlower (show 0 ≤ 512 * (T : ℝ) by positivity)
      dsimp only [Z] at *
      nlinarith
    have h := div_le_div_of_nonneg_right hcount (show 0 ≤ (2 : ℝ) ^ t by positivity)
    push_cast
    convert h using 1 <;> ring
  have htail := scalarGaussianLaw_proposal_tail data hdata hT hwidth
  have hnorm : discreteTotalVariation p target ≤ 512 * T / (2 : ℝ) ^ t +
      256 * Real.exp (-Real.pi * ((T : ℝ) - 1) ^ 2 / 2) :=
    hn.trans (add_le_add hratio htail)
  have h := discreteTotalVariation_triangle (boundedScalarGaussianLaw data T t q) p target
  have hreject := boundedScalarGaussianLaw_error data hdata hT ht hwidth q
  exact h.trans (by linarith)

end
end SISToKSIS

open GeometricGaussianLHL
namespace SISToKSIS
set_option backward.isDefEq.respectTransparency false

/-- Finite independent binary words for security budget `s`. -/
abbrev ScalarGaussianSecurityTape (data : ScalarGaussianData) (s : ℕ) :=
  ScalarGaussianTape data (s + 12) (2 * s + 24) (s + 2)

/-- A finite scalar Gaussian sampler with an explicit dyadic accuracy budget. -/
def scalarGaussianRun (data : ScalarGaussianData) (s : ℕ)
    (tape : ScalarGaussianSecurityTape data s) : Costed ℤ :=
  let radiusBudget := costedNatAdd s 12
  let twice := costedNatMul 2 s
  let precision := costedNatAdd twice.value 24
  let rejectionBudget := costedNatAdd s 2
  let sample := boundedScalarGaussianRun data radiusBudget.value precision.value rejectionBudget.value tape
  ⟨sample.value, radiusBudget.steps + twice.steps + precision.steps + rejectionBudget.steps + sample.steps⟩

@[simp] theorem scalarGaussianRun_value (data : ScalarGaussianData) (s : ℕ)
    (tape : ScalarGaussianSecurityTape data s) :
    (scalarGaussianRun data s tape).value =
      (boundedScalarGaussianRun data (s + 12) (2 * s + 24) (s + 2) tape).value := by
  simp only [scalarGaussianRun, costedNatAdd, costedNatMul]

noncomputable section

def scalarGaussianRunLaw (data : ScalarGaussianData) (s : ℕ) : PMF ℤ :=
  boundedScalarGaussianLaw data (s + 12) (2 * s + 24) (s + 2)

theorem exp_neg_nat_le_dyadic (n : ℕ) : Real.exp (-(n : ℝ)) ≤ (1 / 2 : ℝ) ^ n := by
  have h : Real.exp (-1) ≤ (1 / 2 : ℝ) := by
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (by norm_num) Real.exp_one_gt_two.le
  simpa only [← Real.exp_nat_mul, mul_neg_one] using pow_le_pow_left₀ (Real.exp_pos _).le h n

theorem scalarGaussian_security_tail (s : ℕ) :
    256 * Real.exp (-Real.pi * (((s + 12 : ℕ) : ℝ) - 1) ^ 2 / 2) ≤
      (1 / 2 : ℝ) ^ (s + 3) := by
  have ha : (1 : ℝ) ≤ (s + 11 : ℕ) := by exact_mod_cast (show 1 ≤ s + 11 by omega)
  have hs : ((s + 11 : ℕ) : ℝ) ≤ (((s + 11 : ℕ) : ℝ)) ^ 2 := by nlinarith
  have hpi := mul_le_mul_of_nonneg_right Real.two_le_pi (sq_nonneg (((s + 11 : ℕ) : ℝ)))
  have harg : -Real.pi * (((s + 12 : ℕ) : ℝ) - 1) ^ 2 / 2 ≤ -((s + 11 : ℕ) : ℝ) := by
    have he : ((s + 12 : ℕ) : ℝ) - 1 = (s + 11 : ℕ) := by push_cast; ring
    rw [he]
    nlinarith
  have h := mul_le_mul_of_nonneg_left
    ((Real.exp_le_exp.mpr harg).trans (exp_neg_nat_le_dyadic (s + 11))) (show (0 : ℝ) ≤ 256 by norm_num)
  calc
    _ ≤ 256 * (1 / 2 : ℝ) ^ (s + 11) := h
    _ = (1 / 2 : ℝ) ^ (s + 3) := by rw [pow_add, pow_add]; ring

theorem scalarGaussian_security_rounding (s : ℕ) :
    512 * ((s + 12 : ℕ) : ℝ) / (2 : ℝ) ^ (2 * s + 24) ≤ (1 / 2 : ℝ) ^ (s + 3) := by
  have hT : ((s + 12 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (s + 12) := by
    exact_mod_cast (Nat.lt_two_pow_self (n := s + 12)).le
  apply (div_le_iff₀ (show (0 : ℝ) < 2 ^ (2 * s + 24) by positivity)).mpr
  have h := mul_le_mul_of_nonneg_left hT (show (0 : ℝ) ≤ 512 by norm_num)
  calc
    _ ≤ 512 * (2 : ℝ) ^ (s + 12) := h
    _ = (1 / 2 : ℝ) ^ (s + 3) * (2 : ℝ) ^ (2 * s + 24) := by
      rw [show 2 * s + 24 = (s + 3) + (s + 21) by omega,
        pow_add (2 : ℝ) (s + 3) (s + 21), one_div_pow, one_div,
        ← mul_assoc, inv_mul_cancel₀ (by positivity : (2 : ℝ) ^ (s + 3) ≠ 0), one_mul]
      rw [pow_add, pow_add]
      ring

/-- Accuracy against the full infinite Gaussian law, including finite rejection,
integer weight rounding, normalization, and all omitted tails. -/
theorem scalarGaussianRunLaw_error (data : ScalarGaussianData) (hdata : data.Valid)
    (hwidth : 1 ≤ data.widthSq) (s : ℕ) :
    discreteTotalVariation (scalarGaussianRunLaw data s)
      (scalarGaussianLaw data.center data.widthSq (data.widthSq_pos hdata)) ≤ (1 / 2 : ℝ) ^ s := by
  have h := boundedScalarGaussianLaw_full_error data hdata
    (T := s + 12) (t := 2 * s + 24) (by omega) (by omega) hwidth (s + 2)
  have hround := scalarGaussian_security_rounding s
  have htail := scalarGaussian_security_tail s
  have hsum : (1 / 2 : ℝ) ^ (s + 2) + (1 / 2 : ℝ) ^ (s + 3) +
      (1 / 2 : ℝ) ^ (s + 3) ≤ (1 / 2 : ℝ) ^ s := by
    rw [pow_add, pow_add]
    have hp : 0 ≤ (1 / 2 : ℝ) ^ s := by positivity
    nlinarith
  exact h.trans (by linarith)

end

/-- Arithmetic cost includes all random-word reads and all finite numerical
approximations. It is polynomial in encoded input size and security budget. -/
theorem scalarGaussianRun_polynomial_bound (data : ScalarGaussianData) (hdata : data.Valid)
    (s : ℕ) (tape : ScalarGaussianSecurityTape data s) :
    (scalarGaussianRun data s tape).steps ≤ 20000000000000000000000000000000 *
      (data.bits + s + 1) ^ 6 := by
  let B := data.bits + s + 1
  have hB : 1 ≤ B := by dsimp [B]; omega
  have h := boundedScalarGaussianRun_polynomial_bound data hdata (s + 12) (2 * s + 24) (s + 2) tape
  have hinput : data.bits + (s + 12) + (2 * s + 24) + (s + 2) + 1 ≤ 39 * B := by
    dsimp [B]
    omega
  have hp := Nat.pow_le_pow_left hinput 6
  have hs : s.size ≤ s := Nat.size_le.mpr Nat.lt_two_pow_self
  have hs2 : (2 * s).size ≤ 2 * s := Nat.size_le.mpr Nat.lt_two_pow_self
  have hsp := Nat.pow_le_pow_left (show 2 + s.size + 1 ≤ s + 3 by omega) 2
  have hsetup : (s.size + 4 + 1) + (2 + s.size + 1) ^ 2 +
      ((2 * s).size + 5 + 1) + (s.size + 2 + 1) ≤ 32 * (s + 1) ^ 2 := by nlinarith
  have hsetup' := hsetup.trans
    (Nat.mul_le_mul_left 32 (Nat.pow_le_pow_left (show s + 1 ≤ B by dsimp [B]; omega) 2))
  have hB26 : B ^ 2 ≤ B ^ 6 := Nat.pow_le_pow_right hB (by omega)
  change (s.size + 4 + 1) + (2 + s.size + 1) ^ 2 +
    ((2 * s).size + 5 + 1) + (s.size + 2 + 1) +
    (boundedScalarGaussianRun data (s + 12) (2 * s + 24) (s + 2) tape).steps ≤
      20000000000000000000000000000000 * B ^ 6
  nlinarith


/-- Every tape produces an integer of polynomial encoded length. -/
theorem scalarGaussianRun_output_size (data : ScalarGaussianData) (s : ℕ)
    (tape : ScalarGaussianSecurityTape data s) :
    (scalarGaussianRun data s tape).value.natAbs.size ≤ 44 * (data.bits + s + 1) := by
  rw [scalarGaussianRun_value, boundedScalarGaussianRun_value]
  have h := gaussianProposalPoint_size data (gaussianRadiusBits data (s + 12))
    (dyadicRejectionRun (gaussianProposalWeightRun data (gaussianRadiusBits data (s + 12)) (2 * s + 24))
      (gaussianFallbackIndex (gaussianRadiusBits data (s + 12))) (1024 * (s + 12) * (s + 2)) tape).value
  have hb := gaussianRadiusBits_le data (s + 12)
  omega

end SISToKSIS

open GeometricGaussianLHL
namespace SISToKSIS
set_option backward.isDefEq.respectTransparency false

abbrev GaussianColumnData (R m : ℕ) := Vector (Vector ℤ R) m

def gaussianColumnsOfData {R m : ℕ} (D : GaussianColumnData R m) : Fin m → Coeff R :=
  fun j i => (D.get j).get i

abbrev GaussianColumnTape (data : ScalarGaussianData) (R m s : ℕ) :=
  Fin m → Fin R → ScalarGaussianSecurityTape data (s + R * m)

/-- Store independently sampled integer coefficients, with a security budget
that absorbs the number of scalar coordinates. -/
def gaussianColumnsRun (data : ScalarGaussianData) (R m s : ℕ)
    (tape : GaussianColumnTape data R m s) : Costed (GaussianColumnData R m) :=
  let count := costedNatMul R m
  let precision := costedNatAdd s count.value
  let columns := costedVectorOfFn fun j : Fin m =>
    costedVectorOfFn fun i : Fin R => scalarGaussianRun data precision.value (tape j i)
  ⟨columns.value, count.steps + precision.steps + columns.steps⟩

theorem gaussianColumnsRun_value (data : ScalarGaussianData) (R m s : ℕ)
    (tape : GaussianColumnTape data R m s) :
    gaussianColumnsOfData (gaussianColumnsRun data R m s tape).value =
      fun j i => (scalarGaussianRun data (s + R * m) (tape j i)).value := by
  funext j i
  simp [gaussianColumnsRun, costedNatMul, costedNatAdd, costedVectorOfFn_value,
    gaussianColumnsOfData, Vector.get]

theorem gaussianColumnsRun_steps_le (data : ScalarGaussianData) (hdata : data.Valid) (R m s : ℕ)
    (tape : GaussianColumnTape data R m s) :
    (gaussianColumnsRun data R m s tape).steps ≤
      (R.size + m.size + 1) ^ 2 + (s.size + (R * m).size + 1) +
        m * (R * (20000000000000000000000000000000 * (data.bits + (s + R * m) + 1) ^ 6 + 3) + 4) + 1 := by
  have hinner (j : Fin m) := costedVectorOfFn_steps_le
    (fun i : Fin R => scalarGaussianRun data (s + R * m) (tape j i))
    (20000000000000000000000000000000 * (data.bits + (s + R * m) + 1) ^ 6)
    (fun i => scalarGaussianRun_polynomial_bound data hdata _ (tape j i))
  have houter := costedVectorOfFn_steps_le
    (fun j : Fin m => costedVectorOfFn fun i : Fin R => scalarGaussianRun data (s + R * m) (tape j i)) _ hinner
  change (R.size + m.size + 1) ^ 2 + (s.size + (R * m).size + 1) +
    (costedVectorOfFn fun j : Fin m => costedVectorOfFn fun i : Fin R =>
      scalarGaussianRun data (s + R * m) (tape j i)).steps ≤ _
  norm_num only [Nat.add_assoc] at houter ⊢
  omega

theorem gaussianColumnsRun_output_size (data : ScalarGaussianData) (R m s : ℕ)
    (tape : GaussianColumnTape data R m s) (j : Fin m) (i : Fin R) :
    (gaussianColumnsOfData (gaussianColumnsRun data R m s tape).value j i).natAbs.size ≤
      44 * (data.bits + s + R * m + 1) := by
  rw [gaussianColumnsRun_value]
  simpa only [Nat.add_assoc] using scalarGaussianRun_output_size data (s + R * m) (tape j i)

noncomputable section

/-- Independent finite binary words used by the executable scalar sampler. -/
def scalarGaussianSecurityTapeLaw (data : ScalarGaussianData) (s : ℕ) :
    PMF (ScalarGaussianSecurityTape data s) :=
  independentProduct (fun _ : Fin (1024 * (s + 12) * (s + 2)) =>
    jointPMF (PMF.uniformOfFintype (Fin (2 ^ (gaussianRadiusBits data (s + 12) + 1))))
      (fun _ => PMF.uniformOfFintype (Fin (2 ^ exponentialPrecision (2 * s + 24 + 1)))))

theorem scalarGaussianRun_law (data : ScalarGaussianData) (s : ℕ) :
    (scalarGaussianSecurityTapeLaw data s).map (fun tape => (scalarGaussianRun data s tape).value) =
      scalarGaussianRunLaw data s := by
  simp only [scalarGaussianRun_value]
  rfl

def gaussianColumnTapeLaw (data : ScalarGaussianData) (R m s : ℕ) :
    PMF (GaussianColumnTape data R m s) :=
  independentProduct (fun _ : Fin m => independentProduct (fun _ : Fin R =>
    scalarGaussianSecurityTapeLaw data (s + R * m)))

def gaussianColumnsRunLaw (data : ScalarGaussianData) (R m s : ℕ) : PMF (Fin m → Coeff R) :=
  (gaussianColumnTapeLaw data R m s).map
    (fun tape => gaussianColumnsOfData (gaussianColumnsRun data R m s tape).value)

theorem gaussianColumnsRun_law (data : ScalarGaussianData) (R m s : ℕ) :
    gaussianColumnsRunLaw data R m s =
      independentProduct (fun _ : Fin m => independentProduct (fun _ : Fin R =>
        scalarGaussianRunLaw data (s + R * m))) := by
  have hinner := independentProduct_map
    (fun _ : Fin R => scalarGaussianSecurityTapeLaw data (s + R * m))
    (fun _ tape => (scalarGaussianRun data (s + R * m) tape).value)
  simp only [scalarGaussianRun_law] at hinner
  have houter := independentProduct_map
    (fun _ : Fin m => independentProduct (fun _ : Fin R => scalarGaussianSecurityTapeLaw data (s + R * m)))
    (fun _ row => fun i => (scalarGaussianRun data (s + R * m) (row i)).value)
  simpa only [gaussianColumnsRunLaw, gaussianColumnTapeLaw, gaussianColumnsRun_value, hinner] using houter

/-- Product approximation uses the actual finite-tape law and charges every
coordinate's error. The security choice removes the dimension factor. -/
theorem gaussianColumnsRunLaw_error (data : ScalarGaussianData) (hdata : data.Valid)
    (hwidth : 1 ≤ data.widthSq) (R m s : ℕ) :
    discreteTotalVariation (gaussianColumnsRunLaw data R m s)
      (independentProduct (fun _ : Fin m => independentProduct (fun _ : Fin R =>
        scalarGaussianLaw data.center data.widthSq (data.widthSq_pos hdata)))) ≤ (1 / 2 : ℝ) ^ s := by
  rw [gaussianColumnsRun_law]
  have hinner := discreteTotalVariation_independentProduct_le_uniform
    (fun _ : Fin R => scalarGaussianRunLaw data (s + R * m))
    (fun _ : Fin R => scalarGaussianLaw data.center data.widthSq (data.widthSq_pos hdata))
    (fun _ => scalarGaussianRunLaw_error data hdata hwidth (s + R * m))
  have houter := discreteTotalVariation_independentProduct_le_uniform
    (fun _ : Fin m => independentProduct (fun _ : Fin R => scalarGaussianRunLaw data (s + R * m)))
    (fun _ : Fin m => independentProduct (fun _ : Fin R =>
      scalarGaussianLaw data.center data.widthSq (data.widthSq_pos hdata))) (fun _ => hinner)
  apply houter.trans
  have hcount : ((R * m : ℕ) : ℝ) ≤ (2 : ℝ) ^ (R * m) := by
    exact_mod_cast (Nat.lt_two_pow_self (n := R * m)).le
  have hratio : ((R * m : ℕ) : ℝ) * (1 / 2 : ℝ) ^ (R * m) ≤ 1 := by
    rw [one_div_pow, mul_one_div]
    exact (div_le_one (by positivity)).mpr hcount
  have h := mul_le_mul_of_nonneg_left hratio (show (0 : ℝ) ≤ (1 / 2 : ℝ) ^ s by positivity)
  rw [pow_add]
  push_cast at h
  nlinarith

theorem scalarGaussianLaw_zero_eq_integerGaussian {σ : ℝ} (hσ : 0 < σ) :
    scalarGaussianLaw 0 (σ ^ 2) (sq_pos_of_pos hσ) = integerGaussian σ hσ := by
  have hweight (z : ℤ) : scalarIdealWeight 0 (σ ^ 2) z =
      Real.exp (-(Real.pi / σ ^ 2) * (z : ℝ) ^ 2) := by
    unfold scalarIdealWeight
    congr 1
    ring
  have hZ : scalarGaussianPartition 0 (σ ^ 2) = integerGaussianPartition σ := by
    unfold scalarGaussianPartition integerGaussianPartition integerTheta
    exact tsum_congr hweight
  ext z
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [scalarGaussianLaw_toReal, integerGaussian_toReal, hZ, hweight]

theorem gaussianColumnsRunLaw_integer_error (data : ScalarGaussianData) (hdata : data.Valid)
    {σ : ℝ} (hσ : 1 ≤ σ) (hcenter : data.center = 0) (hvariance : data.widthSq = σ ^ 2)
    (R m s : ℕ) :
    discreteTotalVariation (gaussianColumnsRunLaw data R m s)
      (coefficientColumnLaw R m σ (lt_of_lt_of_le zero_lt_one hσ)) ≤ (1 / 2 : ℝ) ^ s := by
  have hwidth : 1 ≤ data.widthSq := by rw [hvariance]; nlinarith
  have he : scalarGaussianLaw data.center data.widthSq (data.widthSq_pos hdata) =
      integerGaussian σ (lt_of_lt_of_le zero_lt_one hσ) := by
    simp only [hcenter, hvariance]
    exact scalarGaussianLaw_zero_eq_integerGaussian (lt_of_lt_of_le zero_lt_one hσ)
  simpa only [he, coefficientColumnLaw, productIntegerGaussian] using
    gaussianColumnsRunLaw_error data hdata hwidth R m s

end
end SISToKSIS

open GeometricGaussianLHL
namespace SISToKSIS
set_option backward.isDefEq.respectTransparency false

/-- Coefficient variance for canonical width `a/b` and diagonal Gram value `d`. -/
def initialGaussianData (a b d : ℕ) : ScalarGaussianData :=
  ⟨0, 1, a * a, b * b * d⟩

def initialGaussianDataRun (a b d : ℕ) : Costed ScalarGaussianData :=
  let numerator := costedNatMul a a
  let denominatorSquare := costedNatMul b b
  let denominator := costedNatMul denominatorSquare.value d
  ⟨⟨0, 1, numerator.value, denominator.value⟩,
    numerator.steps + denominatorSquare.steps + denominator.steps + 4⟩

@[simp] theorem initialGaussianDataRun_value (a b d : ℕ) :
    (initialGaussianDataRun a b d).value = initialGaussianData a b d := rfl

theorem initialGaussianData_valid {a b d : ℕ} (ha : 0 < a) (hb : 0 < b) (hd : 0 < d) :
    (initialGaussianData a b d).Valid := by
  unfold ScalarGaussianData.Valid initialGaussianData
  exact ⟨by norm_num, Nat.mul_pos ha ha, Nat.mul_pos (Nat.mul_pos hb hb) hd⟩

@[simp] theorem initialGaussianData_center (a b d : ℕ) : (initialGaussianData a b d).center = 0 := by
  simp [ScalarGaussianData.center, initialGaussianData]

theorem initialGaussianData_widthSq (a b d : ℕ) :
    (initialGaussianData a b d).widthSq = ((a : ℝ) / b / Real.sqrt d) ^ 2 := by
  simp only [ScalarGaussianData.widthSq, initialGaussianData, Nat.cast_mul, div_pow,
    Real.sq_sqrt (Nat.cast_nonneg d)]
  ring

theorem initialGaussianData_bits (a b d : ℕ) :
    (initialGaussianData a b d).bits ≤ 2 * a.size + 2 * b.size + d.size + 5 := by
  have hn := natural_mul_size_le a a
  have hb := natural_mul_size_le b b
  have hd := natural_mul_size_le (b * b) d
  have hzero : (0 : ℕ).size = 0 := by decide
  have hone : (1 : ℕ).size = 1 := by decide
  simp only [ScalarGaussianData.bits, initialGaussianData, Int.natAbs_zero, hzero, hone]
  omega

theorem initialGaussianDataRun_steps_le (a b d : ℕ) :
    (initialGaussianDataRun a b d).steps ≤ 24 * (a.size + b.size + d.size + 1) ^ 2 := by
  let B := a.size + b.size + d.size + 1
  have hB : 1 ≤ B := by dsimp [B]; omega
  have hn : a.size + a.size + 1 ≤ 2 * B := by dsimp [B]; omega
  have hb : b.size + b.size + 1 ≤ 2 * B := by dsimp [B]; omega
  have hden := natural_mul_size_le b b
  have hd : (b * b).size + d.size + 1 ≤ 3 * B := by dsimp [B]; omega
  have hnp := Nat.pow_le_pow_left hn 2
  have hbp := Nat.pow_le_pow_left hb 2
  have hdp := Nat.pow_le_pow_left hd 2
  change (a.size + a.size + 1) ^ 2 + (b.size + b.size + 1) ^ 2 +
    ((b * b).size + d.size + 1) ^ 2 + 4 ≤ 24 * B ^ 2
  nlinarith

abbrev InitialGaussianTape (a b d r m s : ℕ) :=
  GaussianColumnTape (initialGaussianData a b d) (r * d) m s

/-- Initial matrix sampling returns stored integer coordinates in the integral
basis. The field-valued matrix is its mathematical interpretation. -/
def initialGaussianRun (a b d r m s : ℕ) (tape : InitialGaussianTape a b d r m s) :
    Costed (GaussianColumnData (r * d) m) :=
  let data := initialGaussianDataRun a b d
  let dimension := costedNatMul r d
  let columns := gaussianColumnsRun data.value dimension.value m s tape
  ⟨columns.value, data.steps + dimension.steps + columns.steps⟩

@[simp] theorem initialGaussianRun_value (a b d r m s : ℕ) (tape : InitialGaussianTape a b d r m s) :
    (initialGaussianRun a b d r m s tape).value =
      (gaussianColumnsRun (initialGaussianData a b d) (r * d) m s tape).value := by
  simp only [initialGaussianRun, initialGaussianDataRun_value, costedNatMul]

theorem initialGaussianRun_steps_le {a b d : ℕ} (ha : 0 < a) (hb : 0 < b) (hd : 0 < d)
    (r m s : ℕ) (tape : InitialGaussianTape a b d r m s) :
    (initialGaussianRun a b d r m s tape).steps ≤
      24 * (a.size + b.size + d.size + 1) ^ 2 + (r.size + d.size + 1) ^ 2 +
      ((r * d).size + m.size + 1) ^ 2 + (s.size + (r * d * m).size + 1) +
      m * (r * d * (20000000000000000000000000000000 *
        ((initialGaussianData a b d).bits + (s + r * d * m) + 1) ^ 6 + 3) + 4) + 1 := by
  have hw := initialGaussianDataRun_steps_le a b d
  have hc := gaussianColumnsRun_steps_le (initialGaussianData a b d)
    (initialGaussianData_valid ha hb hd) (r * d) m s tape
  change (initialGaussianDataRun a b d).steps + (r.size + d.size + 1) ^ 2 +
    (gaussianColumnsRun (initialGaussianData a b d) (r * d) m s tape).steps ≤ _
  omega

end SISToKSIS

open GeometricGaussianLHL
namespace SISToKSIS
set_option backward.isDefEq.respectTransparency false

/-- Encoded width/dimension sizes, sampled coordinate count, and stored columns. -/
def initialGaussianSamplingSize (a b d r m : ℕ) : ℕ :=
  a.size + b.size + d.size + r.size + m.size + r * d * m + m

/-- All scalar samplers, stored vector traversals, width preparation, and
security-budget arithmetic are included in the declared cost. -/
theorem initialGaussianRun_polynomial_bound {a b d : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hd : 0 < d) (r m s : ℕ)
    (tape : InitialGaussianTape a b d r m s) :
    (initialGaussianRun a b d r m s tape).steps ≤
      10 ^ 37 * (initialGaussianSamplingSize a b d r m + s + 1) ^ 7 := by
  let B := initialGaussianSamplingSize a b d r m + s + 1
  let X := (initialGaussianData a b d).bits + (s + r * d * m) + 1
  have hB : 1 ≤ B := by dsimp [B]; omega
  have hs : s ≤ B := by dsimp [B]; omega
  have hm : m ≤ B := by dsimp [B, initialGaussianSamplingSize]; omega
  have hN : r * d * m ≤ B := by dsimp [B, initialGaussianSamplingSize]; omega
  have hwidth : a.size + b.size + d.size + 1 ≤ B := by dsimp [B, initialGaussianSamplingSize]; omega
  have hdimension : r.size + d.size + 1 ≤ B := by dsimp [B, initialGaussianSamplingSize]; omega
  have hmBits : m.size ≤ B := by dsimp [B, initialGaussianSamplingSize]; omega
  have hRBits : (r * d).size ≤ B := (natural_mul_size_le r d).trans hdimension
  have hcount : (r * d).size + m.size + 1 ≤ 3 * B := by omega
  have hsBits : s.size ≤ s := Nat.size_le.mpr Nat.lt_two_pow_self
  have hNBits : (r * d * m).size ≤ r * d * m := Nat.size_le.mpr Nat.lt_two_pow_self
  have hlinear : s.size + (r * d * m).size + 1 ≤ 3 * B := by omega
  have hdata := initialGaussianData_bits a b d
  have hdata' : (initialGaussianData a b d).bits ≤ 5 * B := by
    dsimp [B, initialGaussianSamplingSize]
    omega
  have hX : X ≤ 8 * B := by dsimp [X]; omega
  have hXp := Nat.pow_le_pow_left hX 6
  have hmain := Nat.mul_le_mul hN (Nat.mul_le_mul_left 20000000000000000000000000000000 hXp)
  have hwp := Nat.pow_le_pow_left hwidth 2
  have hdp := Nat.pow_le_pow_left hdimension 2
  have hcp := Nat.pow_le_pow_left hcount 2
  have hB27 : B ^ 2 ≤ B ^ 7 := Nat.pow_le_pow_right hB (by omega)
  have hB17 : B ≤ B ^ 7 := by simpa only [pow_one] using Nat.pow_le_pow_right hB (show 1 ≤ 7 by omega)
  have hrun := initialGaussianRun_steps_le ha hb hd r m s tape
  change (initialGaussianRun a b d r m s tape).steps ≤
    24 * (a.size + b.size + d.size + 1) ^ 2 + (r.size + d.size + 1) ^ 2 +
    ((r * d).size + m.size + 1) ^ 2 + (s.size + (r * d * m).size + 1) +
    m * (r * d * (20000000000000000000000000000000 * X ^ 6 + 3) + 4) + 1 at hrun
  change _ ≤ 10 ^ 37 * B ^ 7
  nlinarith

theorem initialGaussianRun_output_size (a b d r m s : ℕ)
    (tape : InitialGaussianTape a b d r m s) (j : Fin m) (i : Fin (r * d)) :
    (gaussianColumnsOfData (initialGaussianRun a b d r m s tape).value j i).natAbs.size ≤
      352 * (initialGaussianSamplingSize a b d r m + s + 1) := by
  rw [initialGaussianRun_value]
  have h := gaussianColumnsRun_output_size (initialGaussianData a b d) (r * d) m s tape j i
  have hbits := initialGaussianData_bits a b d
  unfold initialGaussianSamplingSize
  omega

end SISToKSIS

open Module NumberField GeometricGaussianLHL
namespace SISToKSIS
noncomputable section
set_option backward.isDefEq.respectTransparency false

def initialGaussianRunLaw (a b d r m s : ℕ) : PMF (Fin m → Coeff (r * d)) :=
  (gaussianColumnTapeLaw (initialGaussianData a b d) (r * d) m s).map
    (fun tape => gaussianColumnsOfData (initialGaussianRun a b d r m s tape).value)

theorem initialGaussianRun_law (a b d r m s : ℕ) :
    initialGaussianRunLaw a b d r m s =
      gaussianColumnsRunLaw (initialGaussianData a b d) (r * d) m s := by
  simp only [initialGaussianRunLaw, initialGaussianRun_value]
  rfl

theorem initialGaussianRunLaw_error {a b d : ℕ} (ha : 0 < a) (hb : 0 < b) (hd : 0 < d)
    (hwidth : Real.sqrt d ≤ (a : ℝ) / b) (r m s : ℕ) :
    discreteTotalVariation (initialGaussianRunLaw a b d r m s)
      (coefficientColumnLaw (r * d) m ((a : ℝ) / b / Real.sqrt d)
        (div_pos (div_pos (Nat.cast_pos.mpr ha) (Nat.cast_pos.mpr hb))
          (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hd)))) ≤ (1 / 2 : ℝ) ^ s := by
  rw [initialGaussianRun_law]
  exact gaussianColumnsRunLaw_integer_error (initialGaussianData a b d)
    (initialGaussianData_valid ha hb hd)
    ((one_le_div (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hd))).mpr hwidth)
    (initialGaussianData_center a b d) (initialGaussianData_widthSq a b d) (r * d) m s

end
end SISToKSIS
