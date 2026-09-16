import «SIS-to-kSIS».GaussianChangeOfMeasure
import «SIS-to-kSIS».GameBounds

/-!
# Change of measure with randomized adversaries

The likelihood-ratio argument permits zero-probability outputs. Giving the
same randomized adversary either input law preserves the second moment.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open GeometricGaussianLHL MeasureTheory

namespace SISToKSIS

theorem event_sq_le_renyiTwo_of_support {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (p q : PMF α)
    (habs : ∀ x, (q x).toReal = 0 → (p x).toReal = 0)
    (hs : Summable (fun x => (p x).toReal ^ 2 / (q x).toReal)) (E : Set α) :
    p.toMeasure.real E ^ 2 ≤ renyiTwo p q * q.toMeasure.real E := by
  let f := fun x => (p x).toReal / (q x).toReal
  have hfirst : (fun x => (q x).toReal * f x) = (fun x => (p x).toReal) := by
    funext x
    dsimp [f]
    by_cases hx : (q x).toReal = 0
    · simp [hx, habs x hx]
    · field_simp
  have hsecond : (fun x => (q x).toReal * f x ^ 2) =
      (fun x => (p x).toReal ^ 2 / (q x).toReal) := by
    funext x
    dsimp [f]
    by_cases hx : (q x).toReal = 0
    · simp [hx]
    · field_simp
  have h := pmf_event_moment_sq_le q f E
    (fun _ => div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
    (hfirst ▸ pmf_summable_toReal p) (hsecond ▸ hs)
  rw [hfirst, hsecond, ← pmf_measureReal_eq_tsum] at h
  exact h

theorem event_lower_bound_of_renyiTwo_support {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (p q : PMF α)
    (habs : ∀ x, (q x).toReal = 0 → (p x).toReal = 0)
    (hs : Summable (fun x => (p x).toReal ^ 2 / (q x).toReal))
    {C : ℝ} (hC : 0 < C) (hbound : renyiTwo p q ≤ C) (E : Set α) :
    p.toMeasure.real E ^ 2 / C ≤ q.toMeasure.real E := by
  apply (div_le_iff₀ hC).mpr
  have h := (event_sq_le_renyiTwo_of_support p q habs hs E).trans
    (mul_le_mul_of_nonneg_right hbound measureReal_nonneg)
  simpa only [mul_comm] using h

theorem jointPMF_ratio_same_adversary {α β : Type*}
    (p q : PMF α) (adversary : α → PMF β) (z : α × β) :
    (jointPMF p adversary z).toReal ^ 2 / (jointPMF q adversary z).toReal =
      ((p z.1).toReal ^ 2 / (q z.1).toReal) * (adversary z.1 z.2).toReal := by
  rcases z with ⟨a, b⟩
  simp only [jointPMF_apply, ENNReal.toReal_mul]
  by_cases ha : (adversary a b).toReal = 0
  · simp [ha]
  by_cases hq : (q a).toReal = 0
  · simp [hq]
  field_simp

theorem renyiTwo_joint_same_adversary_summable {α β : Type*}
    (p q : PMF α) (adversary : α → PMF β)
    (hs : Summable (fun x => (p x).toReal ^ 2 / (q x).toReal)) :
    Summable (fun z => (jointPMF p adversary z).toReal ^ 2 /
      (jointPMF q adversary z).toReal) := by
  simp_rw [jointPMF_ratio_same_adversary]
  apply (summable_prod_of_nonneg (fun _ => by positivity)).mpr
  constructor
  · intro a
    exact (pmf_summable_toReal (adversary a)).mul_left
      ((p a).toReal ^ 2 / (q a).toReal)
  · simpa only [tsum_mul_left, pmf_tsum_toReal, mul_one] using hs

theorem renyiTwo_joint_same_adversary {α β : Type*}
    (p q : PMF α) (adversary : α → PMF β)
    (hs : Summable (fun x => (p x).toReal ^ 2 / (q x).toReal)) :
    renyiTwo (jointPMF p adversary) (jointPMF q adversary) = renyiTwo p q := by
  unfold renyiTwo
  rw [(renyiTwo_joint_same_adversary_summable p q adversary hs).tsum_prod]
  simp_rw [jointPMF_ratio_same_adversary, tsum_mul_left, pmf_tsum_toReal, mul_one]

theorem jointPMF_support_same_adversary {α β : Type*}
    (p q : PMF α) (adversary : α → PMF β)
    (habs : ∀ x, (q x).toReal = 0 → (p x).toReal = 0) :
    ∀ z, (jointPMF q adversary z).toReal = 0 →
      (jointPMF p adversary z).toReal = 0 := by
  rintro ⟨a, b⟩ h
  simp only [jointPMF_apply, ENNReal.toReal_mul, mul_eq_zero] at h ⊢
  exact h.imp (habs a) id

/-- A change-of-measure bound for every randomized adversary and win predicate. -/
theorem successProbability_lower_bound_of_renyiTwo {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (p q : PMF α) (adversary : α → PMF β) (wins : α → β → Prop)
    (habs : ∀ x, (q x).toReal = 0 → (p x).toReal = 0)
    (hs : Summable (fun x => (p x).toReal ^ 2 / (q x).toReal))
    {C : ℝ} (hC : 0 < C) (hbound : renyiTwo p q ≤ C) :
    successProbability p adversary wins ^ 2 / C ≤
      successProbability q adversary wins := by
  apply event_lower_bound_of_renyiTwo_support _ _
    (jointPMF_support_same_adversary p q adversary habs)
    (renyiTwo_joint_same_adversary_summable p q adversary hs) hC
  rwa [renyiTwo_joint_same_adversary p q adversary hs]

end SISToKSIS
