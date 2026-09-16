import GeometricGaussianLHL.GaussianPushforward

/-!
# Randomized adversaries and explicit game losses

Adversaries are probability kernels. Statistical distance therefore controls
their success probabilities, including their internal randomness. A separate
bad-event lemma accounts for the extraction norm bound.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open GeometricGaussianLHL MeasureTheory

namespace SISToKSIS

theorem totalVariation_joint_same_adversary {α β : Type*}
    (p q : PMF α) (adversary : α → PMF β) :
    discreteTotalVariation (jointPMF p adversary) (jointPMF q adversary) =
      discreteTotalVariation p q := by
  have hs := pmf_summable_abs_sub (jointPMF p adversary) (jointPMF q adversary)
  unfold discreteTotalVariation
  rw [hs.tsum_prod]
  simp_rw [jointPMF_apply, ENNReal.toReal_mul, ← sub_mul, abs_mul,
    abs_of_nonneg ENNReal.toReal_nonneg, tsum_mul_left, pmf_tsum_toReal, mul_one]

def successProbability {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (p : PMF α) (adversary : α → PMF β) (wins : α → β → Prop) : ℝ :=
  (jointPMF p adversary).toMeasure.real {z | wins z.1 z.2}

theorem pmfMap_measureReal {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (p : PMF α) (f : α → β) (E : Set β) :
    (p.map f).toMeasure.real E = p.toMeasure.real (f ⁻¹' E) := by
  simp only [Measure.real, PMF.toMeasure_apply_eq_toOuterMeasure,
    PMF.toOuterMeasure_map_apply]

theorem jointPMF_map_second {α β γ : Type*} (p : PMF α) (q : α → PMF β)
    (f : α → β → γ) :
    jointPMF p (fun a => (q a).map (f a)) =
      (jointPMF p q).map (fun z => (z.1, f z.1 z.2)) := by
  simp only [jointPMF, PMF.map_bind, PMF.map_comp, Function.comp_def]

theorem jointPMF_map_input {α β γ : Type*} (p : PMF α) (f : α → β)
    (adversary : β → PMF γ) :
    jointPMF (p.map f) adversary =
      (jointPMF p (fun a => adversary (f a))).map (fun z => (f z.1, z.2)) := by
  simp only [jointPMF, PMF.bind_map, PMF.map_bind, PMF.map_comp, Function.comp_def]

/-- Deterministically encoding the public input is equivalent to composing the adversary. -/
theorem successProbability_map {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    [MeasurableSingletonClass γ] (p : PMF α) (f : α → β)
    (adversary : β → PMF γ) (wins : β → γ → Prop) :
    successProbability (p.map f) adversary wins =
      successProbability p (fun a => adversary (f a)) (fun a z => wins (f a) z) := by
  unfold successProbability
  rw [jointPMF_map_input, pmfMap_measureReal]
  rfl

theorem successProbability_eq_average {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (p : PMF α) (adversary : α → PMF β) (wins : α → β → Prop) :
    successProbability p adversary wins =
      ∑' a, (p a).toReal * (adversary a).toMeasure.real {z | wins a z} := by
  classical
  unfold successProbability
  rw [pmf_measureReal_eq_tsum,
    ((pmf_summable_toReal (jointPMF p adversary)).indicator {z | wins z.1 z.2}).tsum_prod]
  apply tsum_congr
  intro a
  rw [pmf_measureReal_eq_tsum, ← tsum_mul_left]
  apply tsum_congr
  intro b
  by_cases h : wins a b <;> simp [Set.indicator, h, jointPMF_apply, ENNReal.toReal_mul]

/-- Weighted Cauchy–Schwarz for the finite public-matrix distribution. -/
theorem finite_average_square_le {α : Type*} [Fintype α] (p : PMF α) (f : α → ℝ) :
    (∑ a, (p a).toReal * f a) ^ 2 ≤ ∑ a, (p a).toReal * f a ^ 2 := by
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (r := fun a => (p a).toReal * f a) (f := fun a => (p a).toReal)
    (g := fun a => (p a).toReal * f a ^ 2)
    (fun _ _ => ENNReal.toReal_nonneg) (fun _ _ => by positivity)
    (fun _ _ => by ring_nf; exact le_rfl)
  have hp : ∑ a, (p a).toReal = 1 := by simpa only [tsum_fintype] using pmf_tsum_toReal p
  simpa only [hp, one_mul] using h

theorem finite_average_squared_transfer {α : Type*} [Fintype α]
    (p : PMF α) (f g : α → ℝ) {C : ℝ} (hC : 0 < C)
    (h : ∀ a, f a ^ 2 / C ≤ g a) :
    (∑ a, (p a).toReal * f a) ^ 2 / C ≤ ∑ a, (p a).toReal * g a := by
  calc
    _ ≤ (∑ a, (p a).toReal * f a ^ 2) / C :=
      div_le_div_of_nonneg_right (finite_average_square_le p f) hC.le
    _ = ∑ a, (p a).toReal * (f a ^ 2 / C) := by simp only [Finset.sum_div, mul_div_assoc]
    _ ≤ _ := Finset.sum_le_sum (fun a _ =>
      mul_le_mul_of_nonneg_left (h a) ENNReal.toReal_nonneg)

/-- A conditional failure bound charges the exceptional input event only once. -/
theorem joint_bad_probability {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (p : PMF α) (q : α → PMF β) (G : Set α) (E : Set (α × β))
    {δG δE : ℝ} (hG : p.toMeasure.real Gᶜ ≤ δG) (hδE : 0 ≤ δE)
    (hE : ∀ a ∈ G, (q a).toMeasure.real {b | (a, b) ∈ E} ≤ δE) :
    (jointPMF p q).toMeasure.real E ≤ δG + δE := by
  classical
  have hone (a : α) : (q a).toMeasure.real {b | (a, b) ∈ E} ≤ 1 := by
    simpa using measureReal_mono (μ := (q a).toMeasure) (Set.subset_univ {b | (a, b) ∈ E})
  have hs : Summable (fun a => (p a).toReal * (q a).toMeasure.real {b | (a, b) ∈ E}) := by
    apply (pmf_summable_toReal p).of_nonneg_of_le
    · intro a; exact mul_nonneg ENNReal.toReal_nonneg measureReal_nonneg
    · intro a; exact mul_le_of_le_one_right ENNReal.toReal_nonneg (hone a)
  have hb (a : α) : (p a).toReal * (q a).toMeasure.real {b | (a, b) ∈ E} ≤
      (p a).toReal * δE + Gᶜ.indicator (fun x => (p x).toReal) a := by
    by_cases ha : a ∈ G
    · rw [Set.indicator_of_notMem (show a ∉ Gᶜ from fun hc => hc ha), add_zero]
      exact mul_le_mul_of_nonneg_left (hE a ha) ENNReal.toReal_nonneg
    · rw [Set.indicator_of_mem (show a ∈ Gᶜ from ha)]
      exact (mul_le_of_le_one_right ENNReal.toReal_nonneg (hone a)).trans
        (le_add_of_nonneg_left (mul_nonneg ENNReal.toReal_nonneg hδE))
  have ht := hs.tsum_le_tsum hb
    (((pmf_summable_toReal p).mul_right δE).add ((pmf_summable_toReal p).indicator Gᶜ))
  rw [Summable.tsum_add ((pmf_summable_toReal p).mul_right δE)
    ((pmf_summable_toReal p).indicator Gᶜ), tsum_mul_right, pmf_tsum_toReal, one_mul,
    ← pmf_measureReal_eq_tsum] at ht
  have he := successProbability_eq_average p q (fun a b => (a, b) ∈ E)
  change (jointPMF p q).toMeasure.real E = _ at he
  rw [he]
  linarith

theorem joint_bad_outer_probability {α β : Type*}
    (p : PMF α) (q : α → PMF β) (G : Set α) (E : Set (α × β))
    {δG δE : ℝ} (hG : ENNReal.ofReal (1 - δG) ≤ p.toOuterMeasure G)
    (hδE : 0 ≤ δE)
    (hE : ∀ a ∈ G, (q a).toOuterMeasure {b | (a, b) ∈ E} ≤ ENNReal.ofReal δE) :
    (jointPMF p q).toOuterMeasure E ≤ ENNReal.ofReal (δG + δE) := by
  let : MeasurableSpace α := ⊤
  let : MeasurableSpace β := ⊤
  have hmG : 1 - δG ≤ p.toMeasure.real G := by
    rw [← PMF.toMeasure_apply_eq_toOuterMeasure_apply p (show MeasurableSet G from trivial)] at hG
    exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mp hG
  have hcG : p.toMeasure.real Gᶜ ≤ δG := by
    rw [measureReal_compl (show MeasurableSet G from trivial), probReal_univ]
    linarith
  have hmE (a : α) (ha : a ∈ G) : (q a).toMeasure.real {b | (a, b) ∈ E} ≤ δE := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hE a ha)
    rw [Measure.real, PMF.toMeasure_apply_eq_toOuterMeasure]
    simpa only [ENNReal.toReal_ofReal hδE] using h
  have h := joint_bad_probability p q G E hcG hδE hmE
  rw [← PMF.toMeasure_apply_eq_toOuterMeasure (jointPMF p q)]
  rw [← ENNReal.ofReal_toReal (measure_ne_top (jointPMF p q).toMeasure E)]
  exact ENNReal.ofReal_le_ofReal h

theorem pmf_outer_failure_transfer {α : Type*} (p q : PMF α) (E : Set α)
    {δ ε : ℝ} (hδ : 0 ≤ δ) (hq : q.toOuterMeasure E ≤ ENNReal.ofReal δ)
    (hpq : discreteTotalVariation p q ≤ ε) :
    p.toOuterMeasure E ≤ ENNReal.ofReal (δ + ε) := by
  let : MeasurableSpace α := ⊤
  have hqR : q.toMeasure.real E ≤ δ := by
    rw [Measure.real, PMF.toMeasure_apply_eq_toOuterMeasure]
    simpa only [ENNReal.toReal_ofReal hδ] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hq
  have hdiff := (pmf_event_sub_le_totalVariation p q E).trans hpq
  rw [← PMF.toMeasure_apply_eq_toOuterMeasure p]
  rw [← ENNReal.ofReal_toReal (measure_ne_top p.toMeasure E)]
  apply ENNReal.ofReal_le_ofReal
  change p.toMeasure.real E ≤ δ + ε
  linarith

/-- Statistical closeness transfers success for every randomized adversary. -/
theorem successProbability_sub_le {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (p q : PMF α) (adversary : α → PMF β) (wins : α → β → Prop)
    {ε : ℝ} (h : discreteTotalVariation p q ≤ ε) :
    successProbability p adversary wins - successProbability q adversary wins ≤ ε := by
  have he := pmf_event_sub_le_totalVariation (jointPMF p adversary)
    (jointPMF q adversary) {z | wins z.1 z.2}
  rw [totalVariation_joint_same_adversary] at he
  exact he.trans h

/-- An exact solution implication outside a bad event loses at most that event's mass. -/
theorem success_outside_bad_event {α : Type*}
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (p : PMF α) (target source bad : Set α)
    (h : ∀ x ∈ target, x ∉ bad → x ∈ source) :
    p.toMeasure.real target - p.toMeasure.real bad ≤ p.toMeasure.real source := by
  classical
  have hp (x : α) : target.indicator (fun y => (p y).toReal) x ≤
      source.indicator (fun y => (p y).toReal) x +
      bad.indicator (fun y => (p y).toReal) x := by
    by_cases ht : x ∈ target
    · by_cases hb : x ∈ bad
      · simp only [Set.indicator_of_mem ht, Set.indicator_of_mem hb]
        exact le_add_of_nonneg_left (Set.indicator_nonneg
          (fun _ _ => ENNReal.toReal_nonneg) x)
      · simp only [Set.indicator_of_mem ht, Set.indicator_of_notMem hb,
          Set.indicator_of_mem (h x ht hb), add_zero, le_refl]
    · simp only [Set.indicator_of_notMem ht]
      exact add_nonneg (Set.indicator_nonneg (fun _ _ => ENNReal.toReal_nonneg) x)
        (Set.indicator_nonneg (fun _ _ => ENNReal.toReal_nonneg) x)
  have hs := ((pmf_summable_toReal p).indicator target).tsum_le_tsum hp
    (((pmf_summable_toReal p).indicator source).add
      ((pmf_summable_toReal p).indicator bad))
  rw [Summable.tsum_add ((pmf_summable_toReal p).indicator source)
    ((pmf_summable_toReal p).indicator bad), ← pmf_measureReal_eq_tsum,
    ← pmf_measureReal_eq_tsum, ← pmf_measureReal_eq_tsum] at hs
  linarith

/-- Quantitative assembly of the change-of-measure, simulation, and norm losses. -/
theorem squared_advantage_transfer {real shifted simulated source C εsim εnorm : ℝ}
    (hshift : real ^ 2 / C ≤ shifted)
    (hsim : shifted - simulated ≤ εsim)
    (hextract : simulated - εnorm ≤ source) :
    real ^ 2 / C - (εsim + εnorm) ≤ source := by
  linarith

end SISToKSIS
