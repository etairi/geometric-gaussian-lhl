import «SIS-to-kSIS».GameBounds

/-!
# Conditioning and reverse sampling

Both sampling orders are actual conditional PMFs. Their density comparison
reduces to the two fiber probabilities; modular regularity must bound those
probabilities and the exceptional event in the application.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open GeometricGaussianLHL MeasureTheory
open scoped Classical

namespace SISToKSIS

/-- One-sided relative mass control on a high-probability event is sufficient. -/
theorem totalVariation_le_of_lower_on {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (p q : PMF α) (E : Set α) {ε : ℝ}
    (hε : 0 ≤ ε) (h : ∀ x ∈ E, (1 - ε) * (p x).toReal ≤ (q x).toReal) :
    discreteTotalVariation p q ≤ p.toMeasure.real Eᶜ + ε := by
  classical
  have hp := pmf_summable_toReal p
  have hq := pmf_summable_toReal q
  have hc := hp.indicator Eᶜ
  have hb (x : α) : |(p x).toReal - (q x).toReal| ≤
      ((q x).toReal - (p x).toReal) + 2 * ε * (p x).toReal +
        2 * Eᶜ.indicator (fun y => (p y).toReal) x := by
    have hp0 : 0 ≤ (p x).toReal := ENNReal.toReal_nonneg
    have hq0 : 0 ≤ (q x).toReal := ENNReal.toReal_nonneg
    have hεp := mul_nonneg hε hp0
    by_cases hx : x ∈ E
    · simp only [Set.indicator_of_notMem (show x ∉ Eᶜ from fun hh => hh hx), mul_zero, add_zero]
      have hr := h x hx
      apply abs_le.mpr
      constructor <;> nlinarith
    · simp only [Set.indicator_of_mem (show x ∈ Eᶜ from hx)]
      apply abs_le.mpr
      constructor <;> nlinarith
  have ht := (pmf_summable_abs_sub p q).tsum_le_tsum hb
    (((hq.sub hp).add (hp.mul_left (2 * ε))).add (hc.mul_left 2))
  rw [Summable.tsum_add ((hq.sub hp).add (hp.mul_left (2 * ε))) (hc.mul_left 2),
    Summable.tsum_add (hq.sub hp) (hp.mul_left (2 * ε)), Summable.tsum_sub hq hp,
    tsum_mul_left, tsum_mul_left, pmf_tsum_toReal, pmf_tsum_toReal,
    ← pmf_measureReal_eq_tsum] at ht
  unfold discreteTotalVariation
  linarith

theorem filteredPMF_toReal {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (p : PMF α) (E : Set α)
    (hp : ∃ x ∈ E, x ∈ p.support) (x : α) :
    (p.filter E hp x).toReal = E.indicator (fun y => (p y).toReal) x /
      p.toMeasure.real E := by
  classical
  rw [PMF.filter_apply, ENNReal.toReal_mul, ENNReal.toReal_inv,
    Measure.real, PMF.toMeasure_apply_eq_tsum]
  by_cases hx : x ∈ E <;> simp [Set.indicator, hx, div_eq_mul_inv]

theorem pmf_map_injective_apply {α β : Type*} (p : PMF α) (f : α → β)
    (hf : Function.Injective f) (x : α) : p.map f (f x) = p x := by
  rw [PMF.map_apply]
  simp only [hf.eq_iff, tsum_ite_eq']

theorem pmf_map_zero_of_not_range {α β : Type*} (p : PMF α) (f : α → β) (y : β)
    (hy : ∀ x, f x ≠ y) : p.map f y = 0 := by
  rw [PMF.map_apply]
  exact ENNReal.tsum_eq_zero.mpr (fun x => ite_eq_right (Ne.symm (hy x)))

/-- A proportional density on an event uniquely determines the conditional PMF. -/
theorem filteredPMF_eq_of_indicator {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (p q : PMF α) (E : Set α)
    (hp : ∃ x ∈ E, x ∈ p.support) {c : ℝ} (hc : 0 < c)
    (h : ∀ x, E.indicator (fun y => (p y).toReal) x = c * (q x).toReal) :
    p.filter E hp = q := by
  have hm : p.toMeasure.real E = c := by
    rw [pmf_measureReal_eq_tsum]
    simp_rw [h]
    rw [tsum_mul_left, pmf_tsum_toReal, mul_one]
  apply PMF.ext
  intro x
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (q.apply_ne_top x)).mp
  rw [filteredPMF_toReal, h, hm]
  field_simp

/-- A bijection onto an event realizes exact uniform conditioning. -/
theorem uniform_filter_equiv {α β : Type*} [Fintype α] [Fintype β]
    [Nonempty α] [Nonempty β] (E : Set β) (e : α ≃ E)
    (hE : ∃ y ∈ E, y ∈ (PMF.uniformOfFintype β).support) :
    (PMF.uniformOfFintype α).map (fun a => (e a).val) =
      (PMF.uniformOfFintype β).filter E hE := by
  let : MeasurableSpace β := ⊤
  have hα : (0 : ℝ) < Fintype.card α := Nat.cast_pos.mpr Fintype.card_pos
  have hβ : (0 : ℝ) < Fintype.card β := Nat.cast_pos.mpr Fintype.card_pos
  have hi : Function.Injective (fun a => (e a).val) :=
    Subtype.val_injective.comp e.injective
  apply (filteredPMF_eq_of_indicator (PMF.uniformOfFintype β)
    ((PMF.uniformOfFintype α).map (fun a => (e a).val)) E hE
    (div_pos hα hβ) ?_).symm
  intro y
  by_cases hy : y ∈ E
  · obtain ⟨a, ha⟩ := e.surjective ⟨y, hy⟩
    have he : (e a).val = y := congrArg Subtype.val ha
    rw [Set.indicator_of_mem hy, ← he, pmf_map_injective_apply _ _ hi]
    simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast]
    field_simp
  · have hz : ∀ a, (e a).val ≠ y := fun a he => hy (he ▸ (e a).property)
    rw [Set.indicator_of_notMem hy, pmf_map_zero_of_not_range _ _ _ hz,
      ENNReal.toReal_zero, mul_zero]

variable {α β : Type*}

def forwardSampling (p : PMF α) (q : PMF β) (C : α → β → Prop)
    (hq : ∀ a, ∃ b, C a b ∧ b ∈ q.support) : PMF (α × β) :=
  jointPMF p (fun a => q.filter {b | C a b} (hq a))

def reverseSampling (p : PMF α) (q : PMF β) (C : α → β → Prop)
    (hp : ∀ b, ∃ a, C a b ∧ a ∈ p.support) : PMF (α × β) :=
  (jointPMF q (fun b => p.filter {a | C a b} (hp b))).map (Equiv.prodComm β α)

variable [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β]

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
theorem forwardSampling_toReal (p : PMF α) (q : PMF β) (C : α → β → Prop)
    (hq : ∀ a, ∃ b, C a b ∧ b ∈ q.support) (a : α) (b : β) :
    (forwardSampling p q C hq (a, b)).toReal =
      (if C a b then (p a).toReal * (q b).toReal else 0) /
        q.toMeasure.real {b | C a b} := by
  classical
  rw [forwardSampling, jointPMF_apply, ENNReal.toReal_mul, filteredPMF_toReal]
  by_cases h : C a b <;> simp [Set.indicator, h, mul_div_assoc]

omit [MeasurableSpace β] [MeasurableSingletonClass β] in
theorem reverseSampling_toReal (p : PMF α) (q : PMF β) (C : α → β → Prop)
    (hp : ∀ b, ∃ a, C a b ∧ a ∈ p.support) (a : α) (b : β) :
    (reverseSampling p q C hp (a, b)).toReal =
      (if C a b then (p a).toReal * (q b).toReal else 0) /
        p.toMeasure.real {a | C a b} := by
  classical
  have he : (a, b) = Equiv.prodComm β α (b, a) := rfl
  unfold reverseSampling
  rw [he, pmf_map_equiv_apply, jointPMF_apply, ENNReal.toReal_mul, filteredPMF_toReal]
  by_cases h : C a b <;> simp [Set.indicator, h, mul_div_assoc, mul_comm] <;> ring

/-- A quantitative reverse-sampling theorem with its analytical premises exposed. -/
theorem reverseSampling_distance (p : PMF α) (q : PMF β) (C : α → β → Prop)
    (hp : ∀ b, ∃ a, C a b ∧ a ∈ p.support)
    (hq : ∀ a, ∃ b, C a b ∧ b ∈ q.support)
    (G : Set (α × β)) {ε δ : ℝ} (hε : 0 ≤ ε)
    (hbad : (forwardSampling p q C hq).toMeasure.real Gᶜ ≤ δ)
    (hden : ∀ z ∈ G, C z.1 z.2 →
      0 < q.toMeasure.real {b | C z.1 b} ∧
      0 < p.toMeasure.real {a | C a z.2} ∧
      (1 - ε) * p.toMeasure.real {a | C a z.2} ≤ q.toMeasure.real {b | C z.1 b}) :
    discreteTotalVariation (forwardSampling p q C hq) (reverseSampling p q C hp) ≤ δ + ε := by
  apply (totalVariation_le_of_lower_on _ _ G hε ?_).trans (add_le_add hbad le_rfl)
  rintro ⟨a, b⟩ hz
  rw [forwardSampling_toReal, reverseSampling_toReal]
  by_cases hC : C a b
  · simp only [ite_eq_left hC]
    obtain ⟨hF, hR, hden⟩ := hden (a, b) hz hC
    have hn : 0 ≤ (p a).toReal * (q b).toReal := mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    apply (le_div_iff₀ hR).mpr
    rw [mul_assoc, div_mul_eq_mul_div, ← mul_div_assoc]
    apply (div_le_iff₀ hF).mpr
    nlinarith [mul_le_mul_of_nonneg_left hden hn]
  · simp only [ite_eq_right hC, zero_div, mul_zero, le_refl]

end SISToKSIS
