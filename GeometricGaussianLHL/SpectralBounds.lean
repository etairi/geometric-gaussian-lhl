import GeometricGaussianLHL.PolynomialWidth

/-!
# Random-matrix spectral bounds

This module collects the following proof sections, in dependency order.
- The exact bilinear quarter-net bound (`BilinearNets`).
- Absolute column budget for the lower spectral net (`LowerSpectralParameters`).
- Finite inverse-integer nets of the unit sphere (`InverseSphereNets`).
- From finite lower-energy bounds to a uniform lower norm (`LowerSpectralNet`).
- Column and error budgets for the spectral spherical corollaries (`SpectralSphericalParameters`).
- Finite quarter-nets of the unit sphere (`SphereNets`).
- Constants in the spectral natural-scale lower bound (`NaturalSpectralParameters`).
- The canonical space as a real form of the complex embedding space (`CanonicalRealForm`).
- Canonical operator norm from sampled ring-column bounds (`CanonicalMatrixNorm`).
- Bilinear moments of projected complex columns (`ComplexColumnMoment`).
- Spectral tails from actual bilinear exponential moments (`OperatorGaussianTail`).
- Coefficients of a complex embedding linear form (`EmbeddingLinearCoefficients`).
- Canonical matrix bounds from all complex embeddings (`CanonicalEmbeddingMatrix`).
- Field-independent upper singular-value probability (`NumberFieldSpectralUpper`).
- Actual power-of-two Gaussian escape at every embedding (`PowerTwoEmbeddingEscape`).
- The explicit simplified spectral constant (`SpectralThreshold`).
- Fixed-vector lower energy for actual power-of-two Gaussian matrices (`PowerTwoEmbeddingEnergy`).
- The complete upper spectral estimates (`NumberFieldSpectralCertificate`).
- Simultaneous upper bounds at every complex embedding (`UniformEmbeddingUpper`).
- Complex adjoint energy of the actual embedding matrix (`ComplexEmbeddingAdjoint`).
- The canonical adjoint evaluated at every complex embedding (`CanonicalAdjoint`).
- Uniform lower spectral failure on the upper-bounded event (`PowerTwoLowerSpectralEvent`).
- Lower spectral bounds transported to the canonical real operator (`CanonicalSpectralLower`).
- Simultaneous two-sided complex-block spectral probability (`PowerTwoComplexSpectral`).
- The spectral natural scale of the canonical kernel (`PowerTwoNaturalScale`).
- The complete power-of-two singular-value probability bound (`PowerTwoSpectralCertificate`).
-/

section BilinearNets

/-!
## The exact bilinear quarter-net bound

Approximating a unit vector costs a factor `4/3`. Applying the estimate
on the output and input spheres gives the paper's `16/9` operator bound.
No independence or probability assumptions enter these geometric lemmas.
-/

noncomputable section

open scoped InnerProductSpace

namespace GeometricGaussianLHL

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem norm_le_of_quarter_net_inner (s : Finset F)
    (hcover : ∀ x : F, ‖x‖ = 1 → ∃ u ∈ s, ‖x - u‖ ≤ (1 / 4 : ℝ))
    {z : F} {a : ℝ} (ha : 0 ≤ a) (hinner : ∀ u ∈ s, |⟪u, z⟫_ℝ| ≤ a) :
    ‖z‖ ≤ (4 / 3) * a := by
  by_cases hz : z = 0
  · simp only [hz, norm_zero]
    positivity
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  let x : F := ‖z‖⁻¹ • z
  have hx : ‖x‖ = 1 := by simp [x, norm_smul, inv_mul_cancel₀ hn.ne']
  obtain ⟨u, hu, hdist⟩ := hcover x hx
  have hxz : ⟪x, z⟫_ℝ = ‖z‖ := by
    dsimp only [x]
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
    field_simp
  have hsplit : ⟪x, z⟫_ℝ = ⟪x - u, z⟫_ℝ + ⟪u, z⟫_ℝ := by
    rw [inner_sub_left]
    ring
  have hbound : ‖z‖ ≤ (1 / 4) * ‖z‖ + a := by
    calc
      ‖z‖ = |⟪x, z⟫_ℝ| := by rw [hxz, abs_of_nonneg hn.le]
      _ ≤ |⟪x - u, z⟫_ℝ| + |⟪u, z⟫_ℝ| := by rw [hsplit]; exact abs_add_le _ _
      _ ≤ ‖x - u‖ * ‖z‖ + a := add_le_add (abs_real_inner_le_norm _ _) (hinner u hu)
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right hdist hn.le) le_rfl
  linarith

theorem opNorm_le_of_quarter_net (A : E →L[ℝ] F) (s : Finset E)
    (hcover : ∀ x : E, ‖x‖ = 1 → ∃ v ∈ s, ‖x - v‖ ≤ (1 / 4 : ℝ))
    {a : ℝ} (ha : 0 ≤ a) (hA : ∀ v ∈ s, ‖A v‖ ≤ a) : ‖A‖ ≤ (4 / 3) * a := by
  have hn : ‖A‖ ≤ ‖A‖ / 4 + a := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
    intro x hx
    obtain ⟨v, hv, hdist⟩ := hcover x hx
    calc
      ‖A x‖ = ‖A (x - v) + A v‖ := by rw [map_sub, sub_add_cancel]
      _ ≤ ‖A (x - v)‖ + ‖A v‖ := norm_add_le _ _
      _ ≤ ‖A‖ * ‖x - v‖ + a := add_le_add (A.le_opNorm _) (hA v hv)
      _ ≤ ‖A‖ * (1 / 4) + a := add_le_add (mul_le_mul_of_nonneg_left hdist (norm_nonneg A)) le_rfl
      _ = _ := by ring
  linarith

theorem opNorm_le_bilinear_quarter_nets (A : E →L[ℝ] F) (s : Finset E) (t : Finset F)
    (hs : ∀ x : E, ‖x‖ = 1 → ∃ v ∈ s, ‖x - v‖ ≤ (1 / 4 : ℝ))
    (ht : ∀ y : F, ‖y‖ = 1 → ∃ u ∈ t, ‖y - u‖ ≤ (1 / 4 : ℝ))
    {a : ℝ} (ha : 0 ≤ a) (hA : ∀ u ∈ t, ∀ v ∈ s, |⟪u, A v⟫_ℝ| ≤ a) :
    ‖A‖ ≤ (16 / 9) * a := by
  have h := opNorm_le_of_quarter_net A s hs (mul_nonneg (by norm_num) ha)
    (fun v hv => norm_le_of_quarter_net_inner t ht ha (fun u hu => hA u hu v hv))
  linarith

theorem opNorm_exceeds_imp_quarter_net_pair (A : E →L[ℝ] F) (s : Finset E) (t : Finset F)
    (hs : ∀ x : E, ‖x‖ = 1 → ∃ v ∈ s, ‖x - v‖ ≤ (1 / 4 : ℝ))
    (ht : ∀ y : F, ‖y‖ = 1 → ∃ u ∈ t, ‖y - u‖ ≤ (1 / 4 : ℝ))
    {a : ℝ} (ha : 0 ≤ a) (hA : (16 / 9) * a < ‖A‖) :
    ∃ u ∈ t, ∃ v ∈ s, a < |⟪u, A v⟫_ℝ| := by
  by_contra hn
  have hbound : ∀ u ∈ t, ∀ v ∈ s, |⟪u, A v⟫_ℝ| ≤ a := by
    simpa only [not_exists, not_and, not_lt] using hn
  exact (not_lt_of_ge (opNorm_le_bilinear_quarter_nets A s t hs ht ha hbound)) hA

end GeometricGaussianLHL
end

end BilinearNets

section LowerSpectralParameters

/-!
## Absolute column budget for the lower spectral net

The explicit constant absorbs the fine-net cardinality and the embedding
union bound. It also supplies both elementary conditions for the upper
spectral bound with half of the total failure budget.
-/

noncomputable section

namespace GeometricGaussianLHL

def lowerSpectralColumnConstant : ℝ := 8240 * (2 * Real.log 16385 + 2)

theorem lowerSpectralColumnConstant_ge_two : 2 ≤ lowerSpectralColumnConstant := by
  have h := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 16385)
  dsimp [lowerSpectralColumnConstant]
  linarith

theorem lowerSpectral_columns_upper_conditions {r m d : ℕ} {δ : ℝ} (hd : 0 < d)
    (hδ : 0 < δ) (hδone : δ < 1)
    (hcols : lowerSpectralColumnConstant * ((r : ℝ) + Real.log (2 * d / δ)) ≤ m) :
    r ≤ m ∧ Real.log (4 * d / δ) ≤ m := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hL : Real.log 2 ≤ Real.log (2 * d / δ) := by
    apply Real.log_le_log (by norm_num)
    apply (le_div_iff₀ hδ).mpr
    linarith
  have hL0 : 0 ≤ Real.log (2 * d / δ) := (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)).trans hL
  have hb := (mul_le_mul_of_nonneg_right lowerSpectralColumnConstant_ge_two
    (add_nonneg (Nat.cast_nonneg r) hL0)).trans hcols
  constructor
  · exact_mod_cast (show (r : ℝ) ≤ m by linarith [Nat.cast_nonneg (α := ℝ) r])
  · have he : Real.log (4 * d / δ) = Real.log 2 + Real.log (2 * d / δ) := by
      rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity : 2 * (d : ℝ) / δ ≠ 0)]
      congr 1
      ring
    rw [he]
    linarith [Nat.cast_nonneg (α := ℝ) r]

theorem lowerSpectral_net_failure_budget {r m d : ℕ} {δ : ℝ} (hd : 0 < d)
    (hδ : 0 < δ) (hδone : δ < 1)
    (hcols : lowerSpectralColumnConstant * ((r : ℝ) + Real.log (2 * d / δ)) ≤ m) :
    (d : ℝ) * (16385 : ℝ) ^ (2 * r) * Real.exp (-(m : ℝ) / 8240) ≤ δ / 2 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  let L := Real.log (2 * d / δ)
  have hL : 0 ≤ L := by
    apply Real.log_nonneg
    apply (le_div_iff₀ hδ).mpr
    linarith
  have hlog : 0 ≤ Real.log 16385 := Real.log_nonneg (by norm_num)
  have hb : 8240 * (2 * (r : ℝ) * Real.log 16385 + L) ≤ m := by
    apply le_trans _ hcols
    change 8240 * (2 * (r : ℝ) * Real.log 16385 + L) ≤ lowerSpectralColumnConstant * ((r : ℝ) + L)
    dsimp [lowerSpectralColumnConstant]
    nlinarith [mul_nonneg hlog hL, Nat.cast_nonneg (α := ℝ) r]
  have hpow : (16385 : ℝ) ^ (2 * r) = Real.exp (((2 * r : ℕ) : ℝ) * Real.log 16385) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 16385)]
  rw [hpow, mul_assoc, ← Real.exp_add]
  calc
    _ ≤ (d : ℝ) * Real.exp (-L) := by
      apply mul_le_mul_of_nonneg_left _ hdR.le
      apply Real.exp_le_exp.mpr
      push_cast
      linarith
    _ = δ / 2 := by
      dsimp [L]
      rw [Real.exp_neg, Real.exp_log (by positivity : 0 < 2 * (d : ℝ) / δ)]
      field_simp

end GeometricGaussianLHL
end

end LowerSpectralParameters

section InverseSphereNets

/-
The packing-volume proof is adapted from Mathlib's
Besicovitch.card_le_of_separated, copyright (c) 2021 Sébastien Gouëzel.
Released under Apache 2.0 license as described in LICENSE.
-/

/-!
## Finite inverse-integer nets of the unit sphere

Disjoint balls of radius `1/(2q)` prove the `(2q+1)^n` packing bound.
A maximal finite packing gives a net of radius `1/q`. The parameter can
serve both the upper spectral argument and the finer lower spectral net.
-/

noncomputable section

open MeasureTheory Metric Set Module
open scoped ENNReal Function

namespace GeometricGaussianLHL

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem card_le_of_inverse_separated {q : ℕ} (hq : 0 < q) (s : Finset E) (hs : ∀ c ∈ s, ‖c‖ ≤ 1)
    (hsep : ∀ c ∈ s, ∀ d ∈ s, c ≠ d → (1 / (q : ℝ)) ≤ ‖c - d‖) :
    s.card ≤ (2 * q + 1) ^ finrank ℝ E := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  borelize E
  let μ : Measure E := Measure.addHaar
  let δ : ℝ := 1 / (2 * (q : ℝ))
  let ρ : ℝ := (2 * (q : ℝ) + 1) / (2 * (q : ℝ))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  set A := ⋃ c ∈ s, ball (c : E) δ with hA
  have hdisj : Set.Pairwise (s : Set E) (Disjoint on fun c => ball (c : E) δ) := by
    intro c hc d hd hcd
    apply ball_disjoint_ball
    rw [dist_eq_norm]
    convert hsep c hc d hd hcd using 1
    dsimp [δ]
    field_simp
    ring
  have hsub : A ⊆ ball (0 : E) ρ := by
    refine iUnion₂_subset fun x hx => ?_
    apply ball_subset_ball'
    calc
      δ + dist x 0 ≤ δ + 1 := by rw [dist_zero_right]; exact add_le_add le_rfl (hs x hx)
      _ = ρ := by dsimp [δ, ρ]; field_simp; ring
  have hvolume : (s.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ finrank ℝ E) * μ (ball 0 1) ≤
      ENNReal.ofReal (ρ ^ finrank ℝ E) * μ (ball 0 1) := by
    calc
      _ = μ A := by
        rw [hA, measure_biUnion_finset hdisj fun c _ => measurableSet_ball]
        simp only [μ.addHaar_ball_of_pos _ hδ, Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ ≤ μ (ball (0 : E) ρ) := measure_mono hsub
      _ = _ := by rw [μ.addHaar_ball_of_pos _ hρ]
  have hcancel : (s.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ finrank ℝ E) ≤
      ENNReal.ofReal (ρ ^ finrank ℝ E) :=
    (ENNReal.mul_le_mul_iff_left (measure_ball_pos _ _ zero_lt_one).ne' measure_ball_lt_top.ne).mp hvolume
  have hcard : (s.card : ℝ) ≤ ((2 * q + 1 : ℕ) : ℝ) ^ finrank ℝ E := by
    have hh := ENNReal.toReal_le_of_le_ofReal (pow_nonneg hρ.le _) hcancel
    simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ENNReal.toReal_ofReal (pow_nonneg hδ.le _)] at hh
    have hρeq : ρ = ((2 * q + 1 : ℕ) : ℝ) * δ := by
      dsimp [ρ, δ]
      push_cast
      ring
    rw [hρeq, mul_pow] at hh
    exact (mul_le_mul_iff_left₀ (pow_pos hδ _)).mp hh
  exact_mod_cast hcard

/-- A finite sphere net, including the empty sphere in dimension zero.
-/
theorem exists_inverse_sphere_net (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (q : ℕ) (hq : 0 < q) :
    ∃ s : Finset E, (∀ y ∈ s, ‖y‖ = 1) ∧ s.card ≤ (2 * q + 1) ^ finrank ℝ E ∧
      ∀ x : E, ‖x‖ = 1 → ∃ y ∈ s, ‖x - y‖ ≤ (1 / (q : ℝ)) := by
  classical
  let P : Finset E → Prop := fun s => (∀ y ∈ s, ‖y‖ = 1) ∧
    ∀ y ∈ s, ∀ z ∈ s, y ≠ z → (1 / (q : ℝ)) ≤ ‖y - z‖
  let N : Set ℕ := {n | ∃ s : Finset E, s.card = n ∧ P s}
  have hN : N.Nonempty := ⟨0, ∅, by simp, by simp [P]⟩
  have hbounded : BddAbove N := by
    refine ⟨(2 * q + 1) ^ finrank ℝ E, ?_⟩
    rintro n ⟨s, rfl, hs⟩
    exact card_le_of_inverse_separated hq s (fun y hy => (hs.1 y hy).le) hs.2
  obtain ⟨s, hsmax, hs⟩ := Nat.sSup_mem hN hbounded
  refine ⟨s, hs.1, card_le_of_inverse_separated hq s (fun y hy => (hs.1 y hy).le) hs.2, ?_⟩
  intro x hx
  by_contra hn
  have hfar : ∀ y ∈ s, (1 / (q : ℝ)) < ‖x - y‖ := by
    simpa only [not_exists, not_and, not_le] using hn
  have hxnot : x ∉ s := by
    intro hmem
    have hh := hfar x hmem
    simp at hh
    linarith
  have hinsert : P (insert x s) := by
    constructor
    · intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact hx
      · exact hs.1 y hy
    · intro y hy z hz hyz
      rcases Finset.mem_insert.mp hy with hyx | hys
      · subst y
        rcases Finset.mem_insert.mp hz with hzx | hzs
        · exact False.elim (hyz hzx.symm)
        · exact (hfar z hzs).le
      · rcases Finset.mem_insert.mp hz with hzx | hzs
        · subst z
          simpa only [norm_sub_rev] using (hfar y hys).le
        · exact hs.2 y hys z hzs hyz
  have hle := le_csSup hbounded (show (insert x s).card ∈ N from ⟨insert x s, rfl, hinsert⟩)
  rw [Finset.card_insert_of_notMem hxnot, hsmax] at hle
  omega

end GeometricGaussianLHL
end

end InverseSphereNets

section LowerSpectralNet

/-!
## From finite lower-energy bounds to a uniform lower norm

The finer net has radius `1/8192`. An operator bound `4B` and lower
squared norm `B²/527360` on this net imply lower norm `B/2048` everywhere
on the unit sphere. These conservative rational constants are absolute.
-/

noncomputable section

namespace GeometricGaussianLHL

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem lower_norm_of_net (A : E →L[ℝ] F) (T : Finset E) {ε a U : ℝ}
    (hU : 0 ≤ U) (hA : ‖A‖ ≤ U)
    (hnet : ∀ x : E, ‖x‖ = 1 → ∃ v ∈ T, ‖x - v‖ ≤ ε)
    (hlower : ∀ v ∈ T, a ≤ ‖A v‖) (x : E) (hx : ‖x‖ = 1) :
    a - U * ε ≤ ‖A x‖ := by
  obtain ⟨v, hv, hd⟩ := hnet x hx
  have hdist : ‖A (v - x)‖ ≤ U * ε := by
    calc
      _ ≤ ‖A‖ * ‖v - x‖ := A.le_opNorm _
      _ ≤ U * ‖v - x‖ := mul_le_mul_of_nonneg_right hA (norm_nonneg _)
      _ ≤ U * ε := mul_le_mul_of_nonneg_left (by simpa only [norm_sub_rev] using hd) hU
  have htriangle : ‖A v‖ ≤ ‖A x‖ + ‖A (v - x)‖ := by
    calc
      _ = ‖A (x + (v - x))‖ := by congr 2; abel
      _ = ‖A x + A (v - x)‖ := by rw [map_add]
      _ ≤ _ := norm_add_le _ _
  have hl := hlower v hv
  linarith

theorem lower_norm_of_fine_energy_net (A : E →L[ℝ] F) (T : Finset E) {B : ℝ}
    (hB : 0 ≤ B) (hA : ‖A‖ ≤ 4 * B)
    (hnet : ∀ x : E, ‖x‖ = 1 → ∃ v ∈ T, ‖x - v‖ ≤ (1 / 8192 : ℝ))
    (hlower : ∀ v ∈ T, B ^ 2 / 527360 < ‖A v‖ ^ 2) :
    ∀ x : E, ‖x‖ = 1 → B / 2048 ≤ ‖A x‖ := by
  have hn : ∀ v ∈ T, B / 1024 ≤ ‖A v‖ := by
    intro v hv
    apply (sq_le_sq₀ (by positivity) (norm_nonneg _)).mp
    have hh := hlower v hv
    nlinarith [sq_nonneg B]
  intro x hx
  have h := lower_norm_of_net A T
    (by positivity : 0 ≤ 4 * B) hA hnet hn x hx
  linarith

theorem lower_norm_failure_imp_fine_net_point (A : E →L[ℝ] F) (T : Finset E) {B : ℝ}
    (hB : 0 ≤ B) (hA : ‖A‖ ≤ 4 * B)
    (hnet : ∀ x : E, ‖x‖ = 1 → ∃ v ∈ T, ‖x - v‖ ≤ (1 / 8192 : ℝ))
    (hbad : ∃ x : E, ‖x‖ = 1 ∧ ‖A x‖ < B / 2048) :
    ∃ v ∈ T, ‖A v‖ ^ 2 ≤ B ^ 2 / 527360 := by
  by_contra hn
  have he : ∀ v ∈ T, B ^ 2 / 527360 < ‖A v‖ ^ 2 := by
    simpa only [not_exists, not_and, not_le] using hn
  obtain ⟨x, hx, hfail⟩ := hbad
  exact (not_lt_of_ge (lower_norm_of_fine_energy_net A T hB hA hnet he x hx)) hfail

end GeometricGaussianLHL
end

end LowerSpectralNet

section SpectralSphericalParameters

/-!
## Column and error budgets for the spectral spherical corollaries

The paper's spectral column condition implies the simpler upper-bound
condition. Paying one additional failure probability `δ` still leaves the
single-output error strictly below `2^(-ell)` at both finite widths.
-/

noncomputable section

namespace GeometricGaussianLHL

theorem spectral_columns_log_condition {r m d : ℕ} {δ : ℝ} (hd : 0 < d)
    (hδ : 0 < δ) (hδone : δ < 1)
    (hcols : lowerSpectralColumnConstant * ((r : ℝ) + Real.log (2 * d / δ)) ≤ m) :
    Real.log (2 * d / δ) ≤ m := by
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  apply le_trans _ (lowerSpectral_columns_upper_conditions hd hδ hδone hcols).2
  apply Real.log_le_log (by positivity)
  apply div_le_div_of_nonneg_right _ hδ.le
  nlinarith

theorem polynomial_spectral_joint_error_lt {ell : ℝ} (hell : 1 ≤ ell) :
    4 * realSecurityError (ell + 4) +
      2 * realSecurityError (ell + 4) / (1 - 2 * realSecurityError (ell + 4)) <
        realSecurityError ell := by
  have h := jointErrorBound_one_lt (realSecurityError_pos (ell + 4))
    (real_polynomial_failureBudget_le hell)
  simp only [jointErrorBound, Nat.cast_one, mul_one] at h
  rw [realSecurityError_add] at h ⊢
  norm_num at h ⊢
  linarith [realSecurityError_pos ell]

theorem constant_spectral_joint_error_lt {ell : ℝ} (hell : 1 ≤ ell) :
    4 * realSecurityError (ell + 6) +
      2 * realSecurityError (ell + 6) / (1 - 2 * realSecurityError (ell + 6)) <
        realSecurityError ell := by
  have h := jointErrorBound_one_lt (realSecurityError_pos (ell + 6))
    ((real_constant_failureBudget_le hell).trans (by norm_num))
  simp only [jointErrorBound, Nat.cast_one, mul_one] at h
  rw [realSecurityError_add] at h ⊢
  norm_num at h ⊢
  linarith [realSecurityError_pos ell]

/-- A numerical error no larger than the geometric budget also fits in the
spectral single-output security budget.
-/
theorem polynomial_computed_spectral_error_lt {ell τ : ℝ} (hell : 1 ≤ ell)
    (hτ : τ ≤ realSecurityError (ell + 4)) :
    4 * realSecurityError (ell + 4) + (τ +
      2 * realSecurityError (ell + 4) / (1 - 2 * realSecurityError (ell + 4))) <
        realSecurityError ell := by
  have h := jointErrorBound_one_lt (realSecurityError_pos (ell + 4))
    (real_polynomial_failureBudget_le hell)
  simp only [jointErrorBound, Nat.cast_one, mul_one] at h
  rw [realSecurityError_add] at h hτ ⊢
  norm_num at h hτ ⊢
  linarith [realSecurityError_pos ell]

theorem constant_computed_spectral_error_lt {ell τ : ℝ} (hell : 1 ≤ ell)
    (hτ : τ ≤ realSecurityError (ell + 6)) :
    4 * realSecurityError (ell + 6) + (τ +
      2 * realSecurityError (ell + 6) / (1 - 2 * realSecurityError (ell + 6))) <
        realSecurityError ell := by
  have h := jointErrorBound_one_lt (realSecurityError_pos (ell + 6))
    ((real_constant_failureBudget_le hell).trans (by norm_num))
  simp only [jointErrorBound, Nat.cast_one, mul_one] at h
  rw [realSecurityError_add] at h hτ ⊢
  norm_num at h hτ ⊢
  linarith [realSecurityError_pos ell]

end GeometricGaussianLHL
end

end SpectralSphericalParameters

section SphereNets

/-!
## Finite quarter-nets of the unit sphere

The general inverse-integer packing argument, specialized to `q = 4` , gives the literal `9^n` net
size in the upper spectral lemmas.
-/

noncomputable section

open Module

namespace GeometricGaussianLHL

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem card_le_nine_pow_of_quarter_separated (s : Finset E) (hs : ∀ c ∈ s, ‖c‖ ≤ 1)
    (hsep : ∀ c ∈ s, ∀ d ∈ s, c ≠ d → (1 / 4 : ℝ) ≤ ‖c - d‖) :
    s.card ≤ 9 ^ finrank ℝ E := by
  simpa using card_le_of_inverse_separated (by decide : 0 < (4 : ℕ)) s hs hsep

theorem exists_quarter_sphere_net (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] :
    ∃ s : Finset E, (∀ y ∈ s, ‖y‖ = 1) ∧ s.card ≤ 9 ^ finrank ℝ E ∧
      ∀ x : E, ‖x‖ = 1 → ∃ y ∈ s, ‖x - y‖ ≤ (1 / 4 : ℝ) := by
  simpa using exists_inverse_sphere_net E 4 (by decide)

end GeometricGaussianLHL
end

end SphereNets

section NaturalSpectralParameters

/-!
## Constants in the spectral natural-scale lower bound

The spectral column condition bounds `r/(m-r)` by one. Thus the absolute
lower singular-value factor can be retained as an absolute factor after
raising to that exponent. At error `2^(-N)`, the logarithmic rank factor
is exactly `sqrt(log 2)`.
-/

noncomputable section

namespace GeometricGaussianLHL

def naturalSpectralConstant : ℝ := (7 / 10 : ℝ) * Real.sqrt (Real.log 2) / 2048

theorem naturalSpectralConstant_pos : 0 < naturalSpectralConstant := by
  unfold naturalSpectralConstant
  positivity

theorem spectral_columns_twice_rows {r m d : ℕ} {δ : ℝ} (hd : 0 < d)
    (hδ : 0 < δ) (hδone : δ < 1)
    (hcols : lowerSpectralColumnConstant * ((r : ℝ) + Real.log (2 * d / δ)) ≤ m) :
    2 * r ≤ m := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hL : 0 ≤ Real.log (2 * d / δ) := by
    apply Real.log_nonneg
    apply (le_div_iff₀ hδ).mpr
    linarith
  have hb := (mul_le_mul_of_nonneg_right lowerSpectralColumnConstant_ge_two
    (add_nonneg (Nat.cast_nonneg r) hL)).trans hcols
  exact_mod_cast (show 2 * (r : ℝ) ≤ m by linarith)

theorem spectral_natural_exponent_le_one {r m : ℕ} (hrows : 2 * r ≤ m) (hmr : r < m) :
    (r : ℝ) / ((m - r : ℕ) : ℝ) ≤ 1 := by
  have hn : (0 : ℝ) < (m - r : ℕ) := Nat.cast_pos.mpr (Nat.sub_pos_of_lt hmr)
  apply (div_le_iff₀ hn).mpr
  norm_cast
  omega

theorem spectral_lower_factor_rpow {A q : ℝ} (hA : 0 ≤ A) (hq : q ≤ 1) :
    A ^ q / 2048 ≤ (A / 2048) ^ q := by
  have hden : (2048 : ℝ) ^ q ≤ 2048 := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2048) hq
  rw [Real.div_rpow hA (by norm_num)]
  exact div_le_div_of_nonneg_left (Real.rpow_nonneg hA _)
    (Real.rpow_pos_of_pos (by norm_num) q) hden

theorem natural_security_error_parameters {N : ℕ} (hN : 0 < N) :
    0 < realSecurityError N ∧ realSecurityError N < 1 ∧
      Real.sqrt (Real.log (1 / realSecurityError N) / (N : ℝ)) = Real.sqrt (Real.log 2) := by
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  refine ⟨realSecurityError_pos _, ?_, ?_⟩
  · have h := realSecurityError_antitone (show (1 : ℝ) ≤ N by exact_mod_cast hN)
    norm_num [realSecurityError] at h ⊢
    linarith
  · rw [log_inv_realSecurityError]
    congr 1
    field_simp

end GeometricGaussianLHL
end

end NaturalSpectralParameters

section CanonicalRealForm

/-!
## The canonical space as a real form of the complex embedding space

A vector belongs to the canonical real space exactly when its Hermitian
pairings with all embedded integers are real. This characterization uses
the complex embedding basis and real orthogonal projection, and includes
real places as well as nonreal conjugate pairs.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Module NumberField
open scoped InnerProductSpace ComplexConjugate

namespace GeometricGaussianLHL

variable (K : Type*) [Field K] [NumberField K]

local instance realFormEmbeddingsFintype : Fintype (K →+* ℂ) := inferInstance
local instance realFormAmbientInner : InnerProductSpace ℝ (CanonicalAmbient K) := inferInstance

theorem canonicalAmbient_real_inner (x y : CanonicalAmbient K) :
    inner ℝ x y = (inner ℂ x y).re := by
  simp only [PiLp.inner_apply, Complex.re_sum]
  rfl

theorem canonicalInteger_inner_im (x y : 𝓞 K) :
    (inner ℂ (canonicalIntegerVector K x) (canonicalIntegerVector K y)).im = 0 := by
  have h := congrArg Complex.im (canonical_pair_sum_real K x y)
  simp only [Complex.ofReal_im] at h
  exact h.symm

theorem canonicalSpace_inner_im {x y : CanonicalAmbient K}
    (hx : x ∈ canonicalSpace K) (hy : y ∈ canonicalSpace K) :
    (inner ℂ x y).im = 0 := by
  change x ∈ Submodule.span ℝ (Set.range (canonicalIntegerVector K)) at hx
  change y ∈ Submodule.span ℝ (Set.range (canonicalIntegerVector K)) at hy
  induction hx, hy using Submodule.span_induction₂ with
  | mem_mem x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact canonicalInteger_inner_im K a b
  | zero_left y hy => simp
  | zero_right x hx => simp
  | add_left x y z hx hy hz hxz hyz => simp [inner_add_left, hxz, hyz]
  | add_right x y z hx hy hz hxy hxz => simp [inner_add_right, hxy, hxz]
  | smul_left c x y hx hy hxy =>
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_real_left]
    simp [hxy]
  | smul_right c x y hx hy hxy =>
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_real_right]
    simp [hxy]

theorem canonicalInteger_inner_separates {z : CanonicalAmbient K}
    (hz : ∀ a : 𝓞 K, inner ℂ (canonicalIntegerVector K a) z = 0) : z = 0 := by
  let C := (NumberField.canonicalEmbedding.latticeBasis K).map
    (WithLp.linearEquiv 2 ℂ ((K →+* ℂ) → ℂ)).symm
  have hC (i) : C i = canonicalIntegerVector K (NumberField.RingOfIntegers.basis K i) := by
    simp only [C, Basis.map_apply, NumberField.canonicalEmbedding.latticeBasis_apply,
      NumberField.integralBasis_apply]
    rfl
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  conv_lhs => lhs; rw [← C.sum_repr z]
  simp only [sum_inner, inner_smul_left, hC, hz, mul_zero, Finset.sum_const_zero]

theorem canonicalSpace_mem_iff_real_pairings (y : CanonicalAmbient K) :
    y ∈ canonicalSpace K ↔ ∀ a : 𝓞 K,
      (inner ℂ (canonicalIntegerVector K a) y).im = 0 := by
  constructor
  · intro hy a
    exact canonicalSpace_inner_im K (Submodule.subset_span ⟨a, rfl⟩) hy
  · intro hy
    let P := (canonicalSpace K).starProjection y
    have hP : P ∈ canonicalSpace K := Submodule.starProjection_apply_mem _ _
    have hz : y - P = 0 := by
      apply canonicalInteger_inner_separates K
      intro a
      have ha : canonicalIntegerVector K a ∈ canonicalSpace K :=
        Submodule.subset_span ⟨a, rfl⟩
      apply Complex.ext
      · have hr := Submodule.starProjection_inner_eq_zero (K := canonicalSpace K)
          y (canonicalIntegerVector K a) ha
        rw [real_inner_comm, canonicalAmbient_real_inner K] at hr
        exact hr
      · simp only [inner_sub_right, Complex.sub_im, hy a,
          canonicalSpace_inner_im K ha hP, sub_self, Complex.zero_im]
    exact (sub_eq_zero.mp hz).symm ▸ hP

end GeometricGaussianLHL
end

end CanonicalRealForm

section CanonicalMatrixNorm

/-!
## Canonical operator norm from sampled ring-column bounds

The actual canonical matrix is an isometric conjugate of the canonical
operator. The basis condition number and the multiplication constant turn
sampled coefficient-column bounds into the deterministic width used by
the spherical leftover hash lemma.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Module NumberField

namespace GeometricGaussianLHL

variable (K : Type*) [Field K] [NumberField K] {d r m : ℕ}

local instance normEmbeddingsFintype : Fintype (K →+* ℂ) := inferInstance
local instance normAmbientInner : InnerProductSpace ℝ (CanonicalAmbient K) := inferInstance
local instance normSpaceInner : InnerProductSpace ℝ (canonicalSpace K) := inferInstance
local instance normPowerInner (n : ℕ) : InnerProductSpace ℝ (CanonicalPower K n) := inferInstance

theorem canonicalEuclideanMatrix_norm (b : Basis (Fin d) ℤ (𝓞 K))
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) :
    ‖(canonicalEuclideanMatrix K b X).toContinuousLinearMap‖ =
      ‖(canonicalMatrixMap K b X).toContinuousLinearMap‖ := by
  have he : (canonicalEuclideanMatrix K b X).toContinuousLinearMap =
      (canonicalOrthonormalCoordinates K b r : CanonicalPower K r →L[ℝ] Euclidean (r * d)).comp
        ((canonicalMatrixMap K b X).toContinuousLinearMap.comp
          (canonicalOrthonormalCoordinates K b m).symm.toContinuousLinearEquiv.toContinuousLinearMap) := by
    ext x : 1
    rfl
  rw [he, ContinuousLinearMap.opNorm_linearIsometryEquiv_comp,
    ContinuousLinearMap.opNorm_comp_linearIsometryEquiv]

theorem canonicalEuclideanMatrix_norm_le_coefficient (b : Basis (Fin d) ℤ (𝓞 K))
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) :
    ‖(canonicalEuclideanMatrix K b X).toContinuousLinearMap‖ ≤
      basisKappa K b * ‖(realCoefficientMap (ringCoefficientMatrix b X)).toContinuousLinearMap‖ := by
  rw [canonicalEuclideanMatrix_norm]
  change ‖(powerCanonicalEquiv K b r).toContinuousLinearMap.comp
    ((realCoefficientMap (ringCoefficientMatrix b X)).toContinuousLinearMap.comp
      (powerCanonicalEquiv K b m).symm.toContinuousLinearMap)‖ ≤ _
  calc
    _ ≤ ‖(powerCanonicalEquiv K b r).toContinuousLinearMap‖ *
        (‖(realCoefficientMap (ringCoefficientMatrix b X)).toContinuousLinearMap‖ *
          ‖(powerCanonicalEquiv K b m).symm.toContinuousLinearMap‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ basisAlpha K b * (‖(realCoefficientMap (ringCoefficientMatrix b X)).toContinuousLinearMap‖ *
        basisBeta K b) := by
      gcongr
      · exact (basisAlpha_pos K b).le
      · exact powerCanonicalEquiv_norm_le K b r
      · exact powerCanonicalEquiv_symm_norm_le K b m
    _ = _ := by unfold basisKappa; ring

theorem ringCoefficientMatrix_columns_le (b : Basis (Fin d) ℤ (𝓞 K))
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) {U : ℝ}
    (hcols : ∀ j, ‖integerEmbedding (r * d) (ringPowerCoordinates b r (fun k => X k j))‖ ≤ U) :
    ∀ l, ‖realColumn (ringCoefficientMatrix b X) l‖ ≤ basisMu K b * U := by
  rw [ringCoefficientMatrix_eq_block]
  exact blockCoefficientMatrix_column_norm _ _ (basisMu_nonneg K b)
    (basisPowerMultiplication_norm_le_mu K b r) hcols

theorem canonicalEuclideanMatrix_norm_le_columns (b : Basis (Fin d) ℤ (𝓞 K))
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) {U : ℝ} (hU : 0 ≤ U)
    (hcols : ∀ j, ‖integerEmbedding (r * d) (ringPowerCoordinates b r (fun k => X k j))‖ ≤ U) :
    ‖(canonicalEuclideanMatrix K b X).toContinuousLinearMap‖ ≤
      basisKappa K b * (basisMu K b * U) * Real.sqrt (m * d) := by
  have hκ : 0 ≤ basisKappa K b := (by norm_num : (0 : ℝ) ≤ 1).trans (basisKappa_ge_one K b)
  have h := (canonicalEuclideanMatrix_norm_le_coefficient K b X).trans
    (mul_le_mul_of_nonneg_left (coefficient_opNorm_le_columns (ringCoefficientMatrix b X)
      (mul_nonneg (basisMu_nonneg K b) hU) (ringCoefficientMatrix_columns_le K b X hcols)) hκ)
  simpa only [Nat.cast_mul, mul_assoc] using h

end GeometricGaussianLHL
end

end CanonicalMatrixNorm

section ComplexColumnMoment

/-!
## Bilinear moments of projected complex columns

A real linear contraction from the Gaussian's ambient space to complex
column space pulls back the bilinear test vectors by its real adjoint.
Their total squared norm is at most one for unit input and output vectors.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open scoped ENNReal InnerProductSpace

namespace GeometricGaussianLHL

variable {E α : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {r m : ℕ}

theorem complexEuclidean_real_inner_eq (u v : EuclideanSpace ℂ (Fin r)) :
    ⟪u, v⟫_ℝ = (⟪u, v⟫_ℂ).re := by
  simp only [PiLp.inner_apply, Complex.re_sum]
  rfl

def projectedColumnOperator (P : E →L[ℝ] EuclideanSpace ℂ (Fin r)) (X : α → E)
    (z : Fin m → α) : EuclideanSpace ℂ (Fin m) →L[ℝ] EuclideanSpace ℂ (Fin r) :=
  ((Matrix.toEuclideanLin (fun i j => P (X (z j)) i)).toContinuousLinearMap).restrictScalars ℝ

omit [CompleteSpace E] in
theorem projectedColumnOperator_apply (P : E →L[ℝ] EuclideanSpace ℂ (Fin r)) (X : α → E)
    (z : Fin m → α) (v : EuclideanSpace ℂ (Fin m)) :
    projectedColumnOperator P X z v = ∑ j, v j • P (X (z j)) := by
  ext i
  simp [projectedColumnOperator, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, mul_comm]

theorem projectedColumnOperator_inner (P : E →L[ℝ] EuclideanSpace ℂ (Fin r)) (X : α → E)
    (z : Fin m → α) (u : EuclideanSpace ℂ (Fin r)) (v : EuclideanSpace ℂ (Fin m)) :
    ⟪u, projectedColumnOperator P X z v⟫_ℝ =
      ∑ j, ⟪P.adjoint (star (v j) • u), X (z j)⟫_ℝ := by
  rw [projectedColumnOperator_apply, inner_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [ContinuousLinearMap.adjoint_inner_left, complexEuclidean_real_inner_eq,
    complexEuclidean_real_inner_eq, inner_smul_right, inner_smul_left]
  simp only [starRingEnd_apply, star_star]

theorem projectedColumnOperator_coefficient_energy (P : E →L[ℝ] EuclideanSpace ℂ (Fin r))
    (hP : ‖P‖ ≤ 1) (u : EuclideanSpace ℂ (Fin r)) (hu : ‖u‖ = 1)
    (v : EuclideanSpace ℂ (Fin m)) (hv : ‖v‖ = 1) :
    (∑ j, ‖P.adjoint (star (v j) • u)‖ ^ 2) ≤ 1 := by
  have hnorm (j : Fin m) : ‖P.adjoint (star (v j) • u)‖ ≤ ‖star (v j) • u‖ := by
    calc
      _ ≤ ‖P.adjoint‖ * ‖star (v j) • u‖ := P.adjoint.le_opNorm _
      _ ≤ 1 * ‖star (v j) • u‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        simpa only [ContinuousLinearMap.adjoint.norm_map] using hP
      _ = _ := one_mul _
  calc
    _ ≤ ∑ j, ‖star (v j) • u‖ ^ 2 := Finset.sum_le_sum
      (fun j _ => (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (hnorm j))
    _ = 1 := by
      simp only [norm_smul, norm_star, hu, mul_one, ← EuclideanSpace.norm_sq_eq, hv, one_pow]

theorem projectedColumnOperator_mgf (p : Fin m → PMF α) (X : α → E) (b : ℝ)
    (hmgf : ∀ j, ∀ h : E, (∑' z, p j z * ENNReal.ofReal (Real.exp (⟪h, X z⟫_ℝ))) ≤
      ENNReal.ofReal (Real.exp (b ^ 2 * ‖h‖ ^ 2 / (4 * Real.pi))))
    (P : E →L[ℝ] EuclideanSpace ℂ (Fin r)) (hP : ‖P‖ ≤ 1)
    (u : EuclideanSpace ℂ (Fin r)) (hu : ‖u‖ = 1)
    (v : EuclideanSpace ℂ (Fin m)) (hv : ‖v‖ = 1) (θ : ℝ) :
    (∑' z : Fin m → α, independentProduct p z *
      ENNReal.ofReal (Real.exp (θ * ⟪u, projectedColumnOperator P X z v⟫_ℝ))) ≤
        ENNReal.ofReal (Real.exp (b ^ 2 * θ ^ 2 / (4 * Real.pi))) := by
  simp_rw [projectedColumnOperator_inner]
  exact independentProduct_linear_mgf_unit p X b hmgf
    (fun j => P.adjoint (star (v j) • u))
    (projectedColumnOperator_coefficient_energy P hP u hu v hv) θ

end GeometricGaussianLHL
end

end ComplexColumnMoment

section OperatorGaussianTail

/-!
## Spectral tails from actual bilinear exponential moments

The finite quarter-nets and scalar Chernoff estimate give the exact
`16/9` factor and `9^(p+q)` union bound. The input is an actual PMF and
actual exponential sums. Applications must prove its moment hypothesis
for their sampling law; no spectral theorem is assumed here.
-/

noncomputable section

open MeasureTheory Module
open scoped ENNReal InnerProductSpace

namespace GeometricGaussianLHL

variable {E F α : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace α] [MeasurableSingletonClass α]

theorem pmf_operatorNorm_gaussian_tail (p : PMF α) (A : α → E →L[ℝ] F)
    {b a : ℝ} (hb : 0 < b) (ha : 0 < a)
    (hmgf : ∀ u : F, ‖u‖ = 1 → ∀ v : E, ‖v‖ = 1 → ∀ θ : ℝ,
      (∑' x, p x * ENNReal.ofReal (Real.exp (θ * ⟪u, A x v⟫_ℝ))) ≤
        ENNReal.ofReal (Real.exp (b ^ 2 * θ ^ 2 / (4 * Real.pi)))) :
    p.toMeasure {x | (16 / 9) * a < ‖A x‖} ≤
      ENNReal.ofReal (2 * (9 : ℝ) ^ (finrank ℝ E + finrank ℝ F) *
        Real.exp (-Real.pi * a ^ 2 / b ^ 2)) := by
  classical
  obtain ⟨s, hsunit, hscard, hs⟩ := exists_quarter_sphere_net E
  obtain ⟨t, htunit, htcard, ht⟩ := exists_quarter_sphere_net F
  let B := 2 * Real.exp (-Real.pi * a ^ 2 / b ^ 2)
  let events := fun (u : F) (v : E) => {x : α | a < |⟪u, A x v⟫_ℝ|}
  have hsub : {x | (16 / 9) * a < ‖A x‖} ⊆ ⋃ u ∈ t, ⋃ v ∈ s, events u v := by
    intro x hx
    obtain ⟨u, hu, v, hv, he⟩ := opNorm_exceeds_imp_quarter_net_pair (A x) s t hs ht ha.le hx
    exact Set.mem_iUnion.mpr ⟨u, Set.mem_iUnion.mpr ⟨hu, Set.mem_iUnion.mpr ⟨v, Set.mem_iUnion.mpr ⟨hv, he⟩⟩⟩⟩
  have hevent : ∀ u ∈ t, ∀ v ∈ s, p.toMeasure (events u v) ≤ ENNReal.ofReal B := by
    intro u hu v hv
    exact pmf_gaussian_abs_tail p (fun x => ⟪u, A x v⟫_ℝ) (sq_pos_of_pos hb) ha
      (hmgf u (htunit u hu) v (hsunit v hv))
  calc
    _ ≤ p.toMeasure (⋃ u ∈ t, ⋃ v ∈ s, events u v) := measure_mono hsub
    _ ≤ ∑ u ∈ t, ∑ v ∈ s, p.toMeasure (events u v) :=
      (measure_biUnion_finset_le t _).trans
        (Finset.sum_le_sum (fun u _ => measure_biUnion_finset_le s _))
    _ ≤ ∑ u ∈ t, ∑ v ∈ s, ENNReal.ofReal B :=
      Finset.sum_le_sum (fun u hu => Finset.sum_le_sum (fun v hv => hevent u hu v hv))
    _ = ENNReal.ofReal ((t.card : ℝ) * s.card * B) := by
      simp only [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
        ENNReal.ofReal_natCast, mul_assoc]
    _ ≤ ENNReal.ofReal (((9 : ℝ) ^ finrank ℝ F) * (9 ^ finrank ℝ E) * B) := by
      apply ENNReal.ofReal_le_ofReal
      have hcard : (t.card : ℝ) * s.card ≤ (9 : ℝ) ^ finrank ℝ F * (9 ^ finrank ℝ E) := by
        exact_mod_cast Nat.mul_le_mul htcard hscard
      exact mul_le_mul_of_nonneg_right hcard (by dsimp [B]; positivity)
    _ = _ := by congr 1; dsimp [B]; rw [pow_add]; ring

def operatorGaussianThreshold (N : ℕ) (b δ : ℝ) : ℝ :=
  (16 / 9) * b * Real.sqrt (((N : ℝ) * Real.log 9 + Real.log (2 / δ)) / Real.pi)

theorem pmf_operatorNorm_gaussian_failure (p : PMF α) (A : α → E →L[ℝ] F)
    {b δ : ℝ} (hb : 0 < b) (hδ : 0 < δ) (hδone : δ < 1)
    (hmgf : ∀ u : F, ‖u‖ = 1 → ∀ v : E, ‖v‖ = 1 → ∀ θ : ℝ,
      (∑' x, p x * ENNReal.ofReal (Real.exp (θ * ⟪u, A x v⟫_ℝ))) ≤
        ENNReal.ofReal (Real.exp (b ^ 2 * θ ^ 2 / (4 * Real.pi)))) :
    p.toMeasure {x | operatorGaussianThreshold (finrank ℝ E + finrank ℝ F) b δ < ‖A x‖} ≤
      ENNReal.ofReal δ := by
  let N := finrank ℝ E + finrank ℝ F
  let H := (N : ℝ) * Real.log 9 + Real.log (2 / δ)
  have hH : 0 < H := by
    have hlog : 0 < Real.log (2 / δ) := Real.log_pos ((lt_div_iff₀ hδ).mpr (by linarith))
    have hn : 0 ≤ (N : ℝ) * Real.log 9 := mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num))
    dsimp [H]
    linarith
  let a := b * Real.sqrt (H / Real.pi)
  have ha : 0 < a := by dsimp [a]; positivity
  have h := pmf_operatorNorm_gaussian_tail p A hb ha hmgf
  have ht : operatorGaussianThreshold N b δ = (16 / 9) * a := by
    dsimp [operatorGaussianThreshold, a, H]
    ring
  rw [ht]
  apply h.trans_eq
  have he : -Real.pi * a ^ 2 / b ^ 2 = -H := by
    dsimp [a]
    rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ H / Real.pi)]
    field_simp
  rw [he]
  have hpow : (9 : ℝ) ^ N = Real.exp ((N : ℝ) * Real.log 9) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 9)]
  change ENNReal.ofReal (2 * (9 : ℝ) ^ N * Real.exp (-H)) = _
  rw [hpow, mul_assoc, ← Real.exp_add]
  have hh : (N : ℝ) * Real.log 9 + -H = -Real.log (2 / δ) := by dsimp [H]; ring
  rw [hh, Real.exp_neg, Real.exp_log (by positivity : 0 < 2 / δ)]
  congr 1
  field_simp

end GeometricGaussianLHL
end

end OperatorGaussianTail

section EmbeddingLinearCoefficients

/-!
## Coefficients of a complex embedding linear form

For a unit output vector and a modulus-one integral basis, the squared
complex coefficient energy is exactly the field degree. The identity uses
the actual integral-basis coordinate map, not an abstract Gaussian vector.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Module NumberField
open scoped InnerProductSpace

namespace GeometricGaussianLHL

variable (K : Type*) [Field K] [NumberField K] {d r : ℕ}

def embeddingLinearCoefficients (b : Basis (Fin d) ℤ (𝓞 K)) (τ : K →+* ℂ)
    (u : EuclideanSpace ℂ (Fin r)) : Fin (r * d) → ℂ :=
  fun l => star (u (finProdFinEquiv.symm l).1) *
    τ (algebraMap (𝓞 K) K (b (finProdFinEquiv.symm l).2))

omit [NumberField K] in
theorem embeddingLinearCoefficients_energy (b : Basis (Fin d) ℤ (𝓞 K)) (τ : K →+* ℂ)
    (hb : ∀ i, ‖τ (algebraMap (𝓞 K) K (b i))‖ = 1) (u : EuclideanSpace ℂ (Fin r)) :
    (∑ l, ‖embeddingLinearCoefficients K b τ u l‖ ^ 2) = (d : ℝ) * ‖u‖ ^ 2 := by
  rw [← finProdFinEquiv.sum_comp (fun l => ‖embeddingLinearCoefficients K b τ u l‖ ^ 2)]
  simp only [embeddingLinearCoefficients, Equiv.symm_apply_apply, norm_mul, norm_star, hb, mul_one,
    Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← Finset.mul_sum, ← EuclideanSpace.norm_sq_eq]

theorem ringVector_embedding_expansion (b : Basis (Fin d) ℤ (𝓞 K)) (τ : K →+* ℂ)
    (x : Fin r → 𝓞 K) (j : Fin r) :
    τ (algebraMap (𝓞 K) K (x j)) = ∑ i, (ringPowerCoordinates b r x (finProdFinEquiv (j, i)) : ℂ) *
      τ (algebraMap (𝓞 K) K (b i)) := by
  have h := congrArg (fun y : 𝓞 K => τ (algebraMap (𝓞 K) K y)) (b.sum_equivFun (x j))
  simpa only [map_sum, map_zsmul, zsmul_eq_mul, map_mul, map_intCast, ringPowerCoordinates_apply] using h.symm

theorem embeddingLinearCoefficients_linearForm (b : Basis (Fin d) ℤ (𝓞 K)) (τ : K →+* ℂ)
    (u : EuclideanSpace ℂ (Fin r)) (x : Fin r → 𝓞 K) :
    ⟪u, canonicalEuclideanProjection K b r τ (canonicalEuclideanEmbedding K b r x)⟫_ℂ =
      integerComplexLinearForm (embeddingLinearCoefficients K b τ u) (ringPowerCoordinates b r x) := by
  rw [integerComplexLinearForm,
    ← finProdFinEquiv.sum_comp (fun l => embeddingLinearCoefficients K b τ u l *
      (ringPowerCoordinates b r x l : ℂ))]
  simp only [embeddingLinearCoefficients, Equiv.symm_apply_apply, Fintype.sum_prod_type,
    PiLp.inner_apply, RCLike.inner_apply, canonicalEuclideanProjection_integer]
  apply Finset.sum_congr rfl
  intro j _
  rw [ringVector_embedding_expansion K b τ x j, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  simp only [starRingEnd_apply]
  ring

end GeometricGaussianLHL
end

end EmbeddingLinearCoefficients

section CanonicalEmbeddingMatrix

/-!
## Canonical matrix bounds from all complex embeddings

The real canonical matrix commutes with evaluation at every embedding.
Summing the squared block bounds gives a canonical operator-norm bound,
without constructing separate real-place and complex-pair coordinates.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Module NumberField

namespace GeometricGaussianLHL

variable (K : Type*) [Field K] [NumberField K] {d r m : ℕ}

local instance matrixEmbeddingsFintype : Fintype (K →+* ℂ) := inferInstance
local instance matrixAmbientInner : InnerProductSpace ℝ (CanonicalAmbient K) := inferInstance
local instance matrixSpaceInner : InnerProductSpace ℝ (canonicalSpace K) := inferInstance
local instance matrixPowerInner (n : ℕ) : InnerProductSpace ℝ (CanonicalPower K n) := inferInstance

def complexEmbeddingMatrix (τ : K →+* ℂ) (X : Matrix (Fin r) (Fin m) (𝓞 K)) :
    EuclideanSpace ℂ (Fin m) →ₗ[ℝ] EuclideanSpace ℂ (Fin r) :=
  (Matrix.toEuclideanLin (fun i j => τ (algebraMap (𝓞 K) K (X i j)))).restrictScalars ℝ

omit [NumberField K] in
theorem complexEmbeddingMatrix_apply (τ : K →+* ℂ) (X : Matrix (Fin r) (Fin m) (𝓞 K))
    (v : EuclideanSpace ℂ (Fin m)) (i : Fin r) :
    complexEmbeddingMatrix K τ X v i = ∑ j, τ (algebraMap (𝓞 K) K (X i j)) * v j := rfl

theorem canonicalEmbeddingProjection_matrix (b : Basis (Fin d) ℤ (𝓞 K))
    (τ : K →+* ℂ) (X : Matrix (Fin r) (Fin m) (𝓞 K)) (Y : CanonicalPower K m) :
    canonicalEmbeddingProjection K r τ (canonicalMatrixMap K b X Y) =
      complexEmbeddingMatrix K τ X (canonicalEmbeddingProjection K m τ Y) := by
  have h : (canonicalEmbeddingProjection K r τ).comp (canonicalMatrixMap K b X) =
      (complexEmbeddingMatrix K τ X).comp (canonicalEmbeddingProjection K m τ) := by
    apply LinearMap.ext_on (canonicalLattice_span K b m)
    rintro _ ⟨x, rfl⟩
    change canonicalEmbeddingProjection K r τ (canonicalMatrixMap K b X (canonicalPowerEmbedding K m x)) = _
    rw [canonicalMatrixMap_integer]
    ext i
    change τ (algebraMap (𝓞 K) K (∑ j, X i j * x j)) =
      ∑ j, τ (algebraMap (𝓞 K) K (X i j)) * τ (algebraMap (𝓞 K) K (x j))
    simp only [map_sum, map_mul]
  exact LinearMap.congr_fun h Y

theorem canonicalMatrixMap_norm_le_embeddings (b : Basis (Fin d) ℤ (𝓞 K))
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) {U : ℝ} (hU : 0 ≤ U)
    (hX : ∀ τ : K →+* ℂ, ‖(complexEmbeddingMatrix K τ X).toContinuousLinearMap‖ ≤ U) :
    ‖(canonicalMatrixMap K b X).toContinuousLinearMap‖ ≤ U := by
  apply ContinuousLinearMap.opNorm_le_bound _ hU
  intro Y
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hU (norm_nonneg _))).mp
  change ‖canonicalMatrixMap K b X Y‖ ^ 2 ≤ (U * ‖Y‖) ^ 2
  rw [canonicalPower_norm_sq_sum_embeddings K r, mul_pow,
    canonicalPower_norm_sq_sum_embeddings K m, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro τ _
  rw [canonicalEmbeddingProjection_matrix]
  have hn : ‖complexEmbeddingMatrix K τ X (canonicalEmbeddingProjection K m τ Y)‖ ≤
      U * ‖canonicalEmbeddingProjection K m τ Y‖ := by
    exact ((complexEmbeddingMatrix K τ X).toContinuousLinearMap.le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hX τ) (norm_nonneg _))
  simpa only [mul_pow] using (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg hU (norm_nonneg _))).mpr hn

theorem canonicalEuclideanMatrix_norm_le_embeddings (b : Basis (Fin d) ℤ (𝓞 K))
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) {U : ℝ} (hU : 0 ≤ U)
    (hX : ∀ τ : K →+* ℂ, ‖(complexEmbeddingMatrix K τ X).toContinuousLinearMap‖ ≤ U) :
    ‖(canonicalEuclideanMatrix K b X).toContinuousLinearMap‖ ≤ U := by
  rw [canonicalEuclideanMatrix_norm]
  exact canonicalMatrixMap_norm_le_embeddings K b X hU hX

end GeometricGaussianLHL
end

end CanonicalEmbeddingMatrix

section NumberFieldSpectralUpper

/-!
## Field-independent upper singular-value probability

The actual independent ellipsoidal ring-Gaussian columns satisfy the
bilinear moment hypothesis at every complex embedding. A union bound over
all `d` embeddings and the canonical norm identity give the printed
spectral threshold, uniformly for real places and degree one.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Module NumberField MeasureTheory
open scoped ENNReal InnerProductSpace

namespace GeometricGaussianLHL

variable (K : Type*) [Field K] [NumberField K] {d r m : ℕ}

theorem complexEuclidean_real_finrank (n : ℕ) :
    finrank ℝ (EuclideanSpace ℂ (Fin n)) = 2 * n := by
  rw [finrank_real_of_complex, finrank_euclideanSpace_fin]

def numberFieldSpectralThreshold (r m d : ℕ) (B δ : ℝ) : ℝ :=
  (16 / 9) * B * Real.sqrt (((2 * (r + m) : ℕ) : ℝ) * Real.log 9 / Real.pi +
    Real.log (2 * d / δ) / Real.pi)

theorem numberFieldSpectralThreshold_eq (r m d : ℕ) (B δ : ℝ) :
    numberFieldSpectralThreshold r m d B δ = operatorGaussianThreshold (2 * (r + m)) B (δ / d) := by
  unfold numberFieldSpectralThreshold operatorGaussianThreshold
  rw [add_div]
  congr 3
  field_simp

theorem numberFieldSpectralThreshold_nonneg (r m d : ℕ) {B δ : ℝ} (hB : 0 ≤ B) :
    0 ≤ numberFieldSpectralThreshold r m d B δ := by
  unfold numberFieldSpectralThreshold
  positivity

theorem complexEmbeddingMatrix_eq_projected (b : Basis (Fin d) ℤ (𝓞 K)) (τ : K →+* ℂ)
    (Z : Fin m → Fin r → 𝓞 K) :
    (complexEmbeddingMatrix K τ (Matrix.transpose Z)).toContinuousLinearMap =
      projectedColumnOperator (canonicalEuclideanProjection K b r τ) (canonicalEuclideanEmbedding K b r) Z := by
  ext v i
  change (∑ j, τ (algebraMap (𝓞 K) K (Z j i)) * v j) =
    ∑ j, canonicalEuclideanProjection K b r τ (canonicalEuclideanEmbedding K b r (Z j)) i * v j
  simp only [canonicalEuclideanProjection_integer]

theorem independentRingColumns_embedding_failure (b : Basis (Fin d) ℤ (𝓞 K))
    (S : Fin m → Euclidean (r * d) ≃L[ℝ] Euclidean (r * d))
    {B δ : ℝ} (hB : 0 < B) (hS : ∀ j, ‖(S j).toContinuousLinearMap‖ ≤ B)
    (hδ : 0 < δ) (hδone : δ < 1) (τ : K →+* ℂ) :
    (independentProduct (fun j => numberFieldEllipsoidalGaussian K b r (S j) 0)).toOuterMeasure
      {Z | operatorGaussianThreshold (2 * (r + m)) B δ <
        ‖(complexEmbeddingMatrix K τ (Matrix.transpose Z)).toContinuousLinearMap‖} ≤ ENNReal.ofReal δ := by
  let : MeasurableSpace (Fin m → Fin r → 𝓞 K) := ⊤
  rw [← PMF.toMeasure_apply_eq_toOuterMeasure_apply _
    (show MeasurableSet {Z : Fin m → Fin r → 𝓞 K | operatorGaussianThreshold (2 * (r + m)) B δ <
      ‖(complexEmbeddingMatrix K τ (Matrix.transpose Z)).toContinuousLinearMap‖} from trivial)]
  have hdim : finrank ℝ (EuclideanSpace ℂ (Fin m)) + finrank ℝ (EuclideanSpace ℂ (Fin r)) =
      2 * (r + m) := by simp only [complexEuclidean_real_finrank]; omega
  have h := pmf_operatorNorm_gaussian_failure
    (independentProduct (fun j => numberFieldEllipsoidalGaussian K b r (S j) 0))
    (projectedColumnOperator (canonicalEuclideanProjection K b r τ) (canonicalEuclideanEmbedding K b r))
    hB hδ hδone (projectedColumnOperator_mgf _ _ B
      (fun j h => numberFieldEllipsoidalGaussian_exp_moment_opNorm K b r (S j) hB.le (hS j) h)
      _ (canonicalEuclideanProjection_opNorm_le K b r τ))
  simpa only [hdim, ← complexEmbeddingMatrix_eq_projected] using h

theorem numberField_ellipsoidal_spectral_failure (b : Basis (Fin d) ℤ (𝓞 K))
    (S : Fin m → Euclidean (r * d) ≃L[ℝ] Euclidean (r * d))
    {B δ : ℝ} (hB : 0 < B) (hS : ∀ j, ‖(S j).toContinuousLinearMap‖ ≤ B)
    (hδ : 0 < δ) (hδone : δ < 1) :
    (independentMatrixColumns (fun j => numberFieldEllipsoidalGaussian K b r (S j) 0)).toOuterMeasure
      {X | numberFieldSpectralThreshold r m d B δ <
        ‖(canonicalEuclideanMatrix K b X).toContinuousLinearMap‖} ≤ ENNReal.ofReal δ := by
  classical
  let p := independentProduct (fun j => numberFieldEllipsoidalGaussian K b r (S j) 0)
  have hd : 0 < d := integralBasis_dimension_pos K b
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hsmall : δ / d < 1 := (div_lt_one hdR).mpr (hδone.trans_le (by exact_mod_cast hd))
  have hcard : Fintype.card (K →+* ℂ) = d := by
    rw [NumberField.Embeddings.card, ← NumberField.RingOfIntegers.rank]
    simpa only [Fintype.card_fin] using finrank_eq_card_basis b
  let U := numberFieldSpectralThreshold r m d B δ
  have hU : 0 ≤ U := numberFieldSpectralThreshold_nonneg r m d hB.le
  have hsub : {Z : Fin m → Fin r → 𝓞 K | U < ‖(canonicalEuclideanMatrix K b (Matrix.transpose Z)).toContinuousLinearMap‖} ⊆
      ⋃ τ : K →+* ℂ, {Z | U < ‖(complexEmbeddingMatrix K τ (Matrix.transpose Z)).toContinuousLinearMap‖} := by
    intro Z hZ
    by_contra hn
    have hblocks : ∀ τ : K →+* ℂ, ‖(complexEmbeddingMatrix K τ (Matrix.transpose Z)).toContinuousLinearMap‖ ≤ U := by
      simpa only [Set.mem_iUnion, Set.mem_setOf_eq, not_exists, not_lt] using hn
    exact (not_lt_of_ge (canonicalEuclideanMatrix_norm_le_embeddings K b (Matrix.transpose Z) hU hblocks)) hZ
  rw [independentMatrixColumns, PMF.toOuterMeasure_map_apply]
  change p.toOuterMeasure {Z | U < ‖(canonicalEuclideanMatrix K b (Matrix.transpose Z)).toContinuousLinearMap‖} ≤ _
  apply (p.toOuterMeasure.mono hsub).trans
  apply (measure_iUnion_le (μ := p.toOuterMeasure) _).trans
  rw [tsum_fintype]
  calc
    _ ≤ ∑ _ : K →+* ℂ, ENNReal.ofReal (δ / d) := by
      apply Finset.sum_le_sum
      intro τ _
      dsimp only [U]
      rw [numberFieldSpectralThreshold_eq r m d B δ]
      exact independentRingColumns_embedding_failure K b S hB hS (div_pos hδ hdR) hsmall τ
    _ = ENNReal.ofReal δ := by
      simp only [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg d)]
      congr 1
      field_simp

end GeometricGaussianLHL
end

end NumberFieldSpectralUpper

section PowerTwoEmbeddingEscape

/-!
## Actual power-of-two Gaussian escape at every embedding

The coefficient energy is the degree, and the coefficient width is
`s/sqrt(d)`. The factors cancel, giving a uniform probability of at least
`1/2060` beyond squared magnitude `s²/64`, including degree one.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Module NumberField MeasureTheory
open scoped ENNReal InnerProductSpace

namespace GeometricGaussianLHL

variable (K : Type*) [Field K] [NumberField K] {k r : ℕ}
  [IsCyclotomicExtension {2 ^ (k + 1)} ℚ K] {ζ : K}

theorem powerTwo_embedding_square_escape (hζ : IsPrimitiveRoot ζ (2 ^ (k + 1)))
    {s : ℝ} (hs : 0 < s) (hσ : 1 ≤ s / Real.sqrt (2 ^ (k + 1)).totient)
    (τ : K →+* ℂ) (u : EuclideanSpace ℂ (Fin r)) (hu : ‖u‖ = 1) :
    ENNReal.ofReal (1 / 2060) ≤
      (numberFieldGaussian K (cyclotomicIntegralBasis K hζ) r s hs.ne').toOuterMeasure
        {x | s ^ 2 / 64 < ‖⟪u, canonicalEuclideanProjection K (cyclotomicIntegralBasis K hζ) r τ
          (canonicalEuclideanEmbedding K (cyclotomicIntegralBasis K hζ) r x)⟫_ℂ‖ ^ 2} := by
  let d := (2 ^ (k + 1)).totient
  let b := cyclotomicIntegralBasis K hζ
  let a := embeddingLinearCoefficients K b τ u
  have hd : (0 : ℝ) < d := by
    exact_mod_cast integralBasis_dimension_pos K b
  have henergy : (∑ i, ‖a i‖ ^ 2) = d := by
    simpa only [hu, one_pow, mul_one] using embeddingLinearCoefficients_energy K b τ
      (fun i => cyclotomicIntegralBasis_embedding_norm K hζ i τ) u
  have he : (s / Real.sqrt d) ^ 2 * (∑ i, ‖a i‖ ^ 2) / 64 = s ^ 2 / 64 := by
    rw [henergy, div_pow, Real.sq_sqrt hd.le]
    field_simp
  have hprob := productGaussian_complex_square_escape a hσ (by rw [henergy]; exact hd)
  change (1 / 2060 : ℝ) ≤
    (productIntegerGaussian (r * d) (s / Real.sqrt d) (by positivity)).toMeasure.real
      {z | (s / Real.sqrt d) ^ 2 * (∑ i, ‖a i‖ ^ 2) / 64 < ‖integerComplexLinearForm a z‖ ^ 2} at hprob
  rw [he] at hprob
  have hprobE : ENNReal.ofReal (1 / 2060) ≤
      (productIntegerGaussian (r * d) (s / Real.sqrt d) (by positivity)).toOuterMeasure
        {z | s ^ 2 / 64 < ‖integerComplexLinearForm a z‖ ^ 2} := by
    rw [← PMF.toMeasure_apply_eq_toOuterMeasure]
    apply ENNReal.ofReal_le_of_le_toReal
    exact hprob
  rw [← powerTwoGaussian_product K hζ r hs, PMF.toOuterMeasure_map_apply] at hprobE
  simpa only [Set.preimage_setOf_eq, embeddingLinearCoefficients_linearForm] using hprobE

end GeometricGaussianLHL
end

end PowerTwoEmbeddingEscape

section SpectralThreshold

/-!
## The explicit simplified spectral constant

A rational exponential estimate proves `log 9 < 3`; this already suffices
for the paper's conservative factor `4`. Both rectangular orientations use
the same largest-dimension bound.
-/

noncomputable section

namespace GeometricGaussianLHL

theorem log_nine_lt_three : Real.log 9 < 3 := by
  have he : (7 / 4 : ℝ) ≤ Real.exp (3 / 4) := by
    linarith [Real.add_one_le_exp (3 / 4 : ℝ)]
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 4) he 4
  rw [← Real.exp_nat_mul] at hp
  norm_num at hp
  exact (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 9)).mpr (by linarith)

theorem numberFieldSpectralThreshold_le_four {r m d : ℕ} {B δ M : ℝ}
    (hB : 0 ≤ B) (hM : 0 ≤ M) (hr : (r : ℝ) ≤ M) (hm : (m : ℝ) ≤ M)
    (hlog : Real.log (2 * d / δ) ≤ M) :
    numberFieldSpectralThreshold r m d B δ ≤ 4 * B * Real.sqrt M := by
  have hn : 0 ≤ ((2 * (r + m) : ℕ) : ℝ) := Nat.cast_nonneg _
  have hnum : ((2 * (r + m) : ℕ) : ℝ) * Real.log 9 + Real.log (2 * d / δ) ≤ 13 * M := by
    have he := mul_le_mul_of_nonneg_left log_nine_lt_three.le hn
    push_cast at he ⊢
    linarith
  have harg : ((2 * (r + m) : ℕ) : ℝ) * Real.log 9 / Real.pi +
      Real.log (2 * d / δ) / Real.pi ≤ (9 / 4 : ℝ) ^ 2 * M := by
    rw [← add_div, div_le_iff₀ Real.pi_pos]
    have hp := mul_le_mul_of_nonneg_right Real.pi_gt_three.le hM
    nlinarith
  have hsqrt : Real.sqrt (((2 * (r + m) : ℕ) : ℝ) * Real.log 9 / Real.pi +
      Real.log (2 * d / δ) / Real.pi) ≤ (9 / 4) * Real.sqrt M := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity, ?_⟩
    rw [mul_pow, Real.sq_sqrt hM]
    exact harg
  apply (mul_le_mul_of_nonneg_left hsqrt (by positivity : 0 ≤ (16 / 9 : ℝ) * B)).trans_eq
  ring

end GeometricGaussianLHL
end

end SpectralThreshold

section PowerTwoEmbeddingEnergy

/-!
## Fixed-vector lower energy for actual power-of-two Gaussian matrices

Independent escape events give an exponentially small lower tail for the
sum of squared complex column inner products. The statement is uniform
in the chosen embedding and unit vector, with explicit absolute constants.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Module NumberField MeasureTheory
open scoped ENNReal InnerProductSpace

namespace GeometricGaussianLHL

variable (K : Type*) [Field K] [NumberField K] {d r m : ℕ}

def embeddingMatrixEnergy (b : Basis (Fin d) ℤ (𝓞 K)) (τ : K →+* ℂ)
    (u : EuclideanSpace ℂ (Fin r)) (X : Matrix (Fin r) (Fin m) (𝓞 K)) : ℝ :=
  ∑ j, ‖⟪u, canonicalEuclideanProjection K b r τ
    (canonicalEuclideanEmbedding K b r (fun i => X i j))⟫_ℂ‖ ^ 2

variable {k : ℕ} [IsCyclotomicExtension {2 ^ (k + 1)} ℚ K] {ζ : K}

theorem powerTwo_embedding_energy_failure (hζ : IsPrimitiveRoot ζ (2 ^ (k + 1)))
    {s : ℝ} (hs : 0 < s) (hσ : 1 ≤ s / Real.sqrt (2 ^ (k + 1)).totient)
    (τ : K →+* ℂ) (u : EuclideanSpace ℂ (Fin r)) (hu : ‖u‖ = 1) :
    (numberFieldMatrixLaw K (cyclotomicIntegralBasis K hζ) r m s hs.ne').toOuterMeasure
      {X | embeddingMatrixEnergy K (cyclotomicIntegralBasis K hζ) τ u X ≤ s ^ 2 * m / 527360} ≤
        ENNReal.ofReal (Real.exp (-(m : ℝ) / 8240)) := by
  let : MeasurableSpace (Fin r → 𝓞 K) := ⊤
  let b := cyclotomicIntegralBasis K hζ
  let p := numberFieldGaussian K b r s hs.ne'
  let f := fun x : Fin r → 𝓞 K =>
    ‖⟪u, canonicalEuclideanProjection K b r τ (canonicalEuclideanEmbedding K b r x)⟫_ℂ‖ ^ 2
  have hp : (1 / 2060 : ℝ) ≤ p.toMeasure.real {x | s ^ 2 / 64 < f x} := by
    have h := powerTwo_embedding_square_escape K hζ hs hσ τ u hu
    change ENNReal.ofReal (1 / 2060) ≤ p.toOuterMeasure {x | s ^ 2 / 64 < f x} at h
    rw [← PMF.toMeasure_apply_eq_toOuterMeasure] at h
    exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mp h
  have h := independentNonnegativeSum_lower_tail (fun _ : Fin m => p) (fun _ => f)
    (fun _ x => sq_nonneg _) (by positivity : 0 < s ^ 2 / 64) (fun _ => hp)
  have ht : (s ^ 2 / 64) * ((1 / 2060 : ℝ) * m / 4) = s ^ 2 * m / 527360 := by ring
  have he : -(1 / 2060 : ℝ) * m / 4 = -(m : ℝ) / 8240 := by ring
  rw [ht, he, PMF.toMeasure_apply_eq_toOuterMeasure] at h
  rw [numberFieldMatrixLaw, PMF.toOuterMeasure_map_apply]
  exact h

end GeometricGaussianLHL
end

end PowerTwoEmbeddingEnergy

section NumberFieldSpectralCertificate

/-!
## The complete upper spectral estimates

These statements use the actual normalized ring-Gaussian matrix laws and
the canonical Euclidean matrix. Both the displayed logarithmic threshold
and the simplified factor `4` have failure probability at most `δ`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Module NumberField MeasureTheory

namespace GeometricGaussianLHL

theorem pmf_norm_good_mass_of_failure {α : Type*} (p : PMF α)
    (f : α → ℝ) {U δ : ℝ} (hδ : 0 ≤ δ)
    (hbad : p.toOuterMeasure {x | U < f x} ≤ ENNReal.ofReal δ) :
    ENNReal.ofReal (1 - δ) ≤ p.toOuterMeasure {x | f x ≤ U} := by
  let : MeasurableSpace α := ⊤
  rw [← PMF.toMeasure_apply_eq_toOuterMeasure_apply p
    (show MeasurableSet {x | f x ≤ U} from trivial)]
  apply ENNReal.ofReal_le_of_le_toReal
  have hb : p.toMeasure {x | U < f x} ≤ ENNReal.ofReal δ := by
    rw [PMF.toMeasure_apply_eq_toOuterMeasure_apply p
      (show MeasurableSet {x | U < f x} from trivial)]
    exact hbad
  have hc := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  rw [ENNReal.toReal_ofReal hδ] at hc
  have he := probReal_compl_eq_one_sub (μ := p.toMeasure)
    (show MeasurableSet {x | f x ≤ U} from trivial)
  have hset : {x | f x ≤ U}ᶜ = {x | U < f x} := by ext x; simp
  rw [hset] at he
  change p.toMeasure.real {x | U < f x} ≤ δ at hc
  change 1 - δ ≤ p.toMeasure.real {x | f x ≤ U}
  linarith

variable (K : Type*) [Field K] [NumberField K] {d r m : ℕ}

theorem numberField_spherical_spectral_failure (b : Basis (Fin d) ℤ (𝓞 K))
    {s δ : ℝ} (hs : 0 < s) (hδ : 0 < δ) (hδone : δ < 1) :
    (numberFieldMatrixLaw K b r m s hs.ne').toOuterMeasure
      {X | numberFieldSpectralThreshold r m d s δ <
        ‖(canonicalEuclideanMatrix K b X).toContinuousLinearMap‖} ≤ ENNReal.ofReal δ := by
  have hS : ‖(euclideanScalarShape (r * d) s hs.ne').toContinuousLinearMap‖ ≤ s := by
    rw [euclideanScalarShape_toCLM, norm_smul, Real.norm_eq_abs, abs_of_pos hs]
    exact mul_le_of_le_one_right hs.le ContinuousLinearMap.norm_id_le
  have h := numberField_ellipsoidal_spectral_failure K b
    (fun _ : Fin m => euclideanScalarShape (r * d) s hs.ne') hs (fun _ => hS) hδ hδone
  simpa only [numberFieldScalarShape_gaussian_zero, independentMatrixColumns, numberFieldMatrixLaw] using h

theorem numberField_spherical_spectral_upper (b : Basis (Fin d) ℤ (𝓞 K))
    {s δ : ℝ} (hs : 0 < s) (hδ : 0 < δ) (hδone : δ < 1) :
    ENNReal.ofReal (1 - δ) ≤ (numberFieldMatrixLaw K b r m s hs.ne').toOuterMeasure
      {X | ‖(canonicalEuclideanMatrix K b X).toContinuousLinearMap‖ ≤
        numberFieldSpectralThreshold r m d s δ} :=
  pmf_norm_good_mass_of_failure _ _ hδ.le (numberField_spherical_spectral_failure K b hs hδ hδone)

theorem numberField_spherical_spectral_four (b : Basis (Fin d) ℤ (𝓞 K))
    {s δ : ℝ} (hs : 0 < s) (hδ : 0 < δ) (hδone : δ < 1)
    (hmr : r ≤ m) (hmlog : Real.log (2 * d / δ) ≤ m) :
    ENNReal.ofReal (1 - δ) ≤ (numberFieldMatrixLaw K b r m s hs.ne').toOuterMeasure
      {X | ‖(canonicalEuclideanMatrix K b X).toContinuousLinearMap‖ ≤ 4 * s * Real.sqrt m} := by
  apply (numberField_spherical_spectral_upper K b hs hδ hδone).trans
  apply OuterMeasure.mono
  intro X hX
  exact hX.trans (numberFieldSpectralThreshold_le_four hs.le (Nat.cast_nonneg m)
    (by exact_mod_cast hmr) le_rfl hmlog)

theorem numberField_ellipsoidal_spectral_upper (b : Basis (Fin d) ℤ (𝓞 K)) (hr : 0 < r)
    (S : Euclidean (r * d) ≃L[ℝ] Euclidean (r * d))
    {δ : ℝ} (hδ : 0 < δ) (hδone : δ < 1) :
    ENNReal.ofReal (1 - δ) ≤
      (independentMatrixColumns (fun _ : Fin m => numberFieldEllipsoidalGaussian K b r S 0)).toOuterMeasure
        {X | ‖(canonicalEuclideanMatrix K b X).toContinuousLinearMap‖ ≤
          numberFieldSpectralThreshold r m d ‖S.toContinuousLinearMap‖ δ} := by
  let : Nonempty (Fin (r * d)) := ⟨⟨0, Nat.mul_pos hr (integralBasis_dimension_pos K b)⟩⟩
  exact pmf_norm_good_mass_of_failure _ _ hδ.le
    (numberField_ellipsoidal_spectral_failure K b (fun _ => S) S.norm_pos (fun _ => le_rfl) hδ hδone)

theorem numberField_ellipsoidal_spectral_four (b : Basis (Fin d) ℤ (𝓞 K)) (hr : 0 < r)
    (S : Euclidean (r * d) ≃L[ℝ] Euclidean (r * d))
    {δ : ℝ} (hδ : 0 < δ) (hδone : δ < 1) (hcols : (m : ℝ) + Real.log (2 * d / δ) ≤ r) :
    ENNReal.ofReal (1 - δ) ≤
      (independentMatrixColumns (fun _ : Fin m => numberFieldEllipsoidalGaussian K b r S 0)).toOuterMeasure
        {X | ‖(canonicalEuclideanMatrix K b X).toContinuousLinearMap‖ ≤
          4 * ‖S.toContinuousLinearMap‖ * Real.sqrt r} := by
  have hd : (1 : ℝ) ≤ d := by exact_mod_cast integralBasis_dimension_pos K b
  have hlog0 : 0 ≤ Real.log (2 * d / δ) := by
    apply Real.log_nonneg
    apply (le_div_iff₀ hδ).mpr
    linarith
  have hm : (m : ℝ) ≤ r := by linarith
  have hlog : Real.log (2 * d / δ) ≤ r := by linarith [Nat.cast_nonneg (α := ℝ) m]
  apply (numberField_ellipsoidal_spectral_upper K b hr S hδ hδone).trans
  apply OuterMeasure.mono
  intro X hX
  exact hX.trans (numberFieldSpectralThreshold_le_four (norm_nonneg _) (Nat.cast_nonneg r)
    le_rfl hm hlog)

end GeometricGaussianLHL
end

end NumberFieldSpectralCertificate

section UniformEmbeddingUpper

/-!
## Simultaneous upper bounds at every complex embedding

The net-and-moment estimate controls all embedding matrices on a common
actual sampling event. This stronger event is used to pass lower bounds
from a fine sphere net to every unit vector.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Module NumberField MeasureTheory
open scoped ENNReal

namespace GeometricGaussianLHL

variable (K : Type*) [Field K] [NumberField K] {d r m : ℕ}

theorem numberField_ellipsoidal_embedding_union_failure (b : Basis (Fin d) ℤ (𝓞 K))
    (S : Fin m → Euclidean (r * d) ≃L[ℝ] Euclidean (r * d))
    {B δ : ℝ} (hB : 0 < B) (hS : ∀ j, ‖(S j).toContinuousLinearMap‖ ≤ B)
    (hδ : 0 < δ) (hδone : δ < 1) :
    (independentMatrixColumns (fun j => numberFieldEllipsoidalGaussian K b r (S j) 0)).toOuterMeasure
      {X | ∃ τ : K →+* ℂ, numberFieldSpectralThreshold r m d B δ <
        ‖(complexEmbeddingMatrix K τ X).toContinuousLinearMap‖} ≤ ENNReal.ofReal δ := by
  classical
  let p := independentMatrixColumns (fun j => numberFieldEllipsoidalGaussian K b r (S j) 0)
  let U := numberFieldSpectralThreshold r m d B δ
  have hd : 0 < d := integralBasis_dimension_pos K b
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hsmall : δ / d < 1 := (div_lt_one hdR).mpr (hδone.trans_le (by exact_mod_cast hd))
  have hcard : Fintype.card (K →+* ℂ) = d := by
    rw [NumberField.Embeddings.card, ← NumberField.RingOfIntegers.rank]
    simpa only [Fintype.card_fin] using finrank_eq_card_basis b
  have hevent (τ : K →+* ℂ) : p.toOuterMeasure {X | U < ‖(complexEmbeddingMatrix K τ X).toContinuousLinearMap‖} ≤
      ENNReal.ofReal (δ / d) := by
    dsimp only [p, U]
    rw [independentMatrixColumns, PMF.toOuterMeasure_map_apply, numberFieldSpectralThreshold_eq]
    exact independentRingColumns_embedding_failure K b S hB hS (div_pos hδ hdR) hsmall τ
  change p.toOuterMeasure {X | ∃ τ : K →+* ℂ, U < ‖(complexEmbeddingMatrix K τ X).toContinuousLinearMap‖} ≤ _
  rw [show {X | ∃ τ : K →+* ℂ, U < ‖(complexEmbeddingMatrix K τ X).toContinuousLinearMap‖} =
    ⋃ τ : K →+* ℂ, {X | U < ‖(complexEmbeddingMatrix K τ X).toContinuousLinearMap‖} by ext X; simp]
  apply (measure_iUnion_le (μ := p.toOuterMeasure) _).trans
  rw [tsum_fintype]
  apply (Finset.sum_le_sum (fun τ _ => hevent τ)).trans_eq
  simp only [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg d)]
  congr 1
  field_simp

theorem numberField_spherical_embedding_union_failure (b : Basis (Fin d) ℤ (𝓞 K))
    {s δ : ℝ} (hs : 0 < s) (hδ : 0 < δ) (hδone : δ < 1) :
    (numberFieldMatrixLaw K b r m s hs.ne').toOuterMeasure
      {X | ∃ τ : K →+* ℂ, numberFieldSpectralThreshold r m d s δ <
        ‖(complexEmbeddingMatrix K τ X).toContinuousLinearMap‖} ≤ ENNReal.ofReal δ := by
  have hS : ‖(euclideanScalarShape (r * d) s hs.ne').toContinuousLinearMap‖ ≤ s := by
    rw [euclideanScalarShape_toCLM, norm_smul, Real.norm_eq_abs, abs_of_pos hs]
    exact mul_le_of_le_one_right hs.le ContinuousLinearMap.norm_id_le
  have h := numberField_ellipsoidal_embedding_union_failure K b
    (fun _ : Fin m => euclideanScalarShape (r * d) s hs.ne') hs (fun _ => hS) hδ hδone
  simpa only [numberFieldScalarShape_gaussian_zero, independentMatrixColumns, numberFieldMatrixLaw] using h

theorem numberField_spherical_embedding_four_failure (b : Basis (Fin d) ℤ (𝓞 K))
    {s δ : ℝ} (hs : 0 < s) (hδ : 0 < δ) (hδone : δ < 1)
    (hmr : r ≤ m) (hlog : Real.log (2 * d / δ) ≤ m) :
    (numberFieldMatrixLaw K b r m s hs.ne').toOuterMeasure
      {X | ∃ τ : K →+* ℂ, 4 * s * Real.sqrt m <
        ‖(complexEmbeddingMatrix K τ X).toContinuousLinearMap‖} ≤ ENNReal.ofReal δ := by
  apply le_trans ((numberFieldMatrixLaw K b r m s hs.ne').toOuterMeasure.mono ?_)
    (numberField_spherical_embedding_union_failure K b hs hδ hδone)
  rintro X ⟨τ, hτ⟩
  exact ⟨τ, (numberFieldSpectralThreshold_le_four hs.le (Nat.cast_nonneg m)
    (by exact_mod_cast hmr) le_rfl hlog).trans_lt hτ⟩

end GeometricGaussianLHL
end

end UniformEmbeddingUpper

section ComplexEmbeddingAdjoint

/-!
## Complex adjoint energy of the actual embedding matrix

The complex adjoint has the same operator norm as the real restriction
used in the upper estimate. Its squared norm on a test vector is exactly
the sum of squared column inner products used in the lower-tail estimate.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Module NumberField
open scoped InnerProductSpace

namespace GeometricGaussianLHL

variable (K : Type*) [Field K] [NumberField K] {d r m : ℕ}

def complexEmbeddingOperator (τ : K →+* ℂ) (X : Matrix (Fin r) (Fin m) (𝓞 K)) :
    EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin r) :=
  (Matrix.toEuclideanLin (fun i j => τ (algebraMap (𝓞 K) K (X i j)))).toContinuousLinearMap

omit [NumberField K] in
theorem complexEmbeddingOperator_restrict (τ : K →+* ℂ) (X : Matrix (Fin r) (Fin m) (𝓞 K)) :
    (complexEmbeddingOperator K τ X).restrictScalars ℝ =
      (complexEmbeddingMatrix K τ X).toContinuousLinearMap := rfl

omit [NumberField K] in
theorem complexEmbeddingOperator_adjoint_norm (τ : K →+* ℂ) (X : Matrix (Fin r) (Fin m) (𝓞 K)) :
    ‖(complexEmbeddingOperator K τ X).adjoint.restrictScalars ℝ‖ =
      ‖(complexEmbeddingMatrix K τ X).toContinuousLinearMap‖ := by
  rw [ContinuousLinearMap.norm_restrictScalars, ContinuousLinearMap.adjoint.norm_map,
    ← complexEmbeddingOperator_restrict, ContinuousLinearMap.norm_restrictScalars]

theorem complexEmbeddingOperator_column (b : Basis (Fin d) ℤ (𝓞 K)) (τ : K →+* ℂ)
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) (j : Fin m) :
    complexEmbeddingOperator K τ X (EuclideanSpace.single j 1) =
      canonicalEuclideanProjection K b r τ (canonicalEuclideanEmbedding K b r (fun i => X i j)) := by
  classical
  ext i
  rw [canonicalEuclideanProjection_integer]
  change (∑ l, τ (algebraMap (𝓞 K) K (X i l)) * (EuclideanSpace.single j (1 : ℂ)) l) = _
  simp [EuclideanSpace.single, PiLp.single_apply]

theorem embeddingMatrixEnergy_eq_adjoint_norm_sq (b : Basis (Fin d) ℤ (𝓞 K))
    (τ : K →+* ℂ) (u : EuclideanSpace ℂ (Fin r)) (X : Matrix (Fin r) (Fin m) (𝓞 K)) :
    embeddingMatrixEnergy K b τ u X = ‖(complexEmbeddingOperator K τ X).adjoint u‖ ^ 2 := by
  rw [embeddingMatrixEnergy, EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro j _
  have h := congrArg norm (ContinuousLinearMap.adjoint_inner_left (complexEmbeddingOperator K τ X)
    (EuclideanSpace.single j 1) u)
  rw [complexEmbeddingOperator_column K b τ X j] at h
  simp only [EuclideanSpace.inner_single_right, one_mul, starRingEnd_apply, norm_star] at h
  rw [h]

end GeometricGaussianLHL
end

end ComplexEmbeddingAdjoint

section CanonicalAdjoint

/-!
## The canonical adjoint evaluated at every complex embedding

Conjugate multiplication preserves the canonical real form. Consequently
the adjoint of the canonical real matrix evaluates to the complex adjoint
of each embedding matrix, with exactly the paper's all-embeddings norm.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Module NumberField
open scoped InnerProductSpace

namespace GeometricGaussianLHL

variable (K : Type*) [Field K] [NumberField K] {d r m : ℕ}

local instance adjointEmbeddingsFintype : Fintype (K →+* ℂ) := inferInstance
local instance adjointAmbientInner : InnerProductSpace ℝ (CanonicalAmbient K) := inferInstance
local instance adjointSpaceInner : InnerProductSpace ℝ (canonicalSpace K) := inferInstance
local instance adjointPowerInner (n : ℕ) : InnerProductSpace ℝ (CanonicalPower K n) := inferInstance

def canonicalConjugateProduct (a : 𝓞 K) (y : CanonicalAmbient K) : CanonicalAmbient K :=
  WithLp.toLp 2 (fun τ => star (τ (algebraMap (𝓞 K) K a)) * y τ)

theorem canonicalConjugateProduct_pairing (a x : 𝓞 K) (y : CanonicalAmbient K) :
    inner ℂ (canonicalIntegerVector K x) (canonicalConjugateProduct K a y) =
      inner ℂ (canonicalIntegerVector K (a * x)) y := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, canonicalIntegerVector_apply,
    canonicalConjugateProduct, map_mul, starRingEnd_apply]
  apply Finset.sum_congr rfl
  intro τ _
  ring

theorem canonicalConjugateProduct_mem (a : 𝓞 K) (y : canonicalSpace K) :
    canonicalConjugateProduct K a y ∈ canonicalSpace K := by
  rw [canonicalSpace_mem_iff_real_pairings]
  intro x
  rw [canonicalConjugateProduct_pairing]
  exact canonicalSpace_inner_im K (Submodule.subset_span ⟨a * x, rfl⟩) y.property

def canonicalAdjointCandidate (X : Matrix (Fin r) (Fin m) (𝓞 K))
    (Y : CanonicalPower K r) : CanonicalPower K m :=
  WithLp.toLp 2 (fun j => ∑ i, (⟨canonicalConjugateProduct K (X i j) (Y i),
    canonicalConjugateProduct_mem K (X i j) (Y i)⟩ : canonicalSpace K))

theorem canonicalAdjointCandidate_apply (X : Matrix (Fin r) (Fin m) (𝓞 K))
    (Y : CanonicalPower K r) (j : Fin m) (τ : K →+* ℂ) :
    (canonicalAdjointCandidate K X Y j : CanonicalAmbient K) τ =
      ∑ i, star (τ (algebraMap (𝓞 K) K (X i j))) * (Y i : CanonicalAmbient K) τ := by
  simp [canonicalAdjointCandidate, canonicalConjugateProduct]

omit [NumberField K] in
theorem complexEmbeddingOperator_adjoint_apply (τ : K →+* ℂ)
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) (u : EuclideanSpace ℂ (Fin r)) (j : Fin m) :
    (complexEmbeddingOperator K τ X).adjoint u j =
      ∑ i, star (τ (algebraMap (𝓞 K) K (X i j))) * u i := by
  have h := ContinuousLinearMap.adjoint_inner_right (complexEmbeddingOperator K τ X)
    (EuclideanSpace.single j 1) u
  simp only [EuclideanSpace.inner_single_left, map_one, one_mul] at h
  rw [h]
  simp only [PiLp.inner_apply, RCLike.inner_apply']
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  change star (∑ l, τ (algebraMap (𝓞 K) K (X i l)) * (EuclideanSpace.single j (1 : ℂ)) l) = _
  simp [EuclideanSpace.single, PiLp.single_apply]

theorem canonicalAdjointCandidate_projection (τ : K →+* ℂ)
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) (Y : CanonicalPower K r) :
    canonicalEmbeddingProjection K m τ (canonicalAdjointCandidate K X Y) =
      (complexEmbeddingOperator K τ X).adjoint (canonicalEmbeddingProjection K r τ Y) := by
  ext j
  rw [canonicalEmbeddingProjection_apply, canonicalAdjointCandidate_apply,
    complexEmbeddingOperator_adjoint_apply]
  rfl

theorem canonicalPower_inner_sum_embeddings (n : ℕ) (Y Z : CanonicalPower K n) :
    inner ℝ Y Z = ∑ τ : K →+* ℂ,
      (inner ℂ (canonicalEmbeddingProjection K n τ Y) (canonicalEmbeddingProjection K n τ Z)).re := by
  simp only [PiLp.inner_apply, Complex.re_sum]
  change (∑ j, ∑ τ, (inner ℂ ((Y j : CanonicalAmbient K) τ)
    ((Z j : CanonicalAmbient K) τ)).re) = _
  exact Finset.sum_comm

theorem canonicalMatrixMap_adjoint_eq (b : Basis (Fin d) ℤ (𝓞 K))
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) (Y : CanonicalPower K r) :
    (canonicalMatrixMap K b X).toContinuousLinearMap.adjoint Y = canonicalAdjointCandidate K X Y := by
  apply ext_inner_left ℝ
  intro Z
  rw [ContinuousLinearMap.adjoint_inner_right, canonicalPower_inner_sum_embeddings,
    canonicalPower_inner_sum_embeddings]
  apply Finset.sum_congr rfl
  intro τ _
  rw [canonicalAdjointCandidate_projection, ContinuousLinearMap.adjoint_inner_right]
  rw [LinearMap.coe_toContinuousLinearMap', canonicalEmbeddingProjection_matrix]
  rfl

theorem canonicalMatrixMap_adjoint_projection (b : Basis (Fin d) ℤ (𝓞 K))
    (τ : K →+* ℂ) (X : Matrix (Fin r) (Fin m) (𝓞 K)) (Y : CanonicalPower K r) :
    canonicalEmbeddingProjection K m τ ((canonicalMatrixMap K b X).toContinuousLinearMap.adjoint Y) =
      (complexEmbeddingOperator K τ X).adjoint (canonicalEmbeddingProjection K r τ Y) := by
  rw [canonicalMatrixMap_adjoint_eq, canonicalAdjointCandidate_projection]

end GeometricGaussianLHL
end

end CanonicalAdjoint

section PowerTwoLowerSpectralEvent

/-!
## Uniform lower spectral failure on the upper-bounded event

A real `1/8192`-net of the complex output sphere has at most
`16385^(2r)` points. The actual fixed-vector energy tail and a union over
all embeddings control failure of the uniform complex adjoint lower bound.
No conditional independence between the spectral events is assumed.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Module NumberField MeasureTheory
open scoped ENNReal

namespace GeometricGaussianLHL

variable (K : Type*) [Field K] [NumberField K] {r m : ℕ}

def complexSpectralUpperBound (B : ℝ) (X : Matrix (Fin r) (Fin m) (𝓞 K)) : Prop :=
  ∀ τ : K →+* ℂ, ‖(complexEmbeddingMatrix K τ X).toContinuousLinearMap‖ ≤ 4 * B

def complexSpectralLowerFailure (B : ℝ) (X : Matrix (Fin r) (Fin m) (𝓞 K)) : Prop :=
  ∃ τ : K →+* ℂ, ∃ u : EuclideanSpace ℂ (Fin r), ‖u‖ = 1 ∧
    ‖(complexEmbeddingOperator K τ X).adjoint u‖ < B / 2048

variable {k : ℕ} [IsCyclotomicExtension {2 ^ (k + 1)} ℚ K] {ζ : K}

theorem powerTwo_lower_spectral_failure_on_upper (hζ : IsPrimitiveRoot ζ (2 ^ (k + 1)))
    {s : ℝ} (hs : 0 < s) (hσ : 1 ≤ s / Real.sqrt (2 ^ (k + 1)).totient) :
    (numberFieldMatrixLaw K (cyclotomicIntegralBasis K hζ) r m s hs.ne').toOuterMeasure
      {X | complexSpectralUpperBound K (s * Real.sqrt m) X ∧
        complexSpectralLowerFailure K (s * Real.sqrt m) X} ≤
      ENNReal.ofReal (((2 ^ (k + 1)).totient : ℝ) * (16385 : ℝ) ^ (2 * r) *
        Real.exp (-(m : ℝ) / 8240)) := by
  classical
  let b := cyclotomicIntegralBasis K hζ
  let d := (2 ^ (k + 1)).totient
  let p := numberFieldMatrixLaw K b r m s hs.ne'
  let B := s * Real.sqrt m
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hBsq : B ^ 2 = s ^ 2 * m := by
    dsimp [B]
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg m)]
  obtain ⟨T, hTunit, hTcard, hTnet⟩ := exists_inverse_sphere_net (EuclideanSpace ℂ (Fin r)) 8192 (by decide)
  have hTcard' : T.card ≤ 16385 ^ (2 * r) := by
    simpa only [complexEuclidean_real_finrank] using hTcard
  let E := fun (τ : K →+* ℂ) (u : EuclideanSpace ℂ (Fin r)) =>
    {X : Matrix (Fin r) (Fin m) (𝓞 K) | embeddingMatrixEnergy K b τ u X ≤ s ^ 2 * m / 527360}
  have hsub : {X | complexSpectralUpperBound K B X ∧ complexSpectralLowerFailure K B X} ⊆
      ⋃ τ : K →+* ℂ, ⋃ u ∈ T, E τ u := by
    rintro X ⟨hupper, τ, u, hu, hl⟩
    have hnorm : ‖(complexEmbeddingOperator K τ X).adjoint.restrictScalars ℝ‖ ≤ 4 * B := by
      rw [complexEmbeddingOperator_adjoint_norm]
      exact hupper τ
    obtain ⟨v, hv, he⟩ := lower_norm_failure_imp_fine_net_point
      ((complexEmbeddingOperator K τ X).adjoint.restrictScalars ℝ) T hB hnorm hTnet ⟨u, hu, hl⟩
    have hev : X ∈ E τ v := by
      change embeddingMatrixEnergy K b τ v X ≤ s ^ 2 * m / 527360
      rw [embeddingMatrixEnergy_eq_adjoint_norm_sq]
      simpa only [ContinuousLinearMap.coe_restrictScalars', hBsq] using he
    exact Set.mem_iUnion.mpr ⟨τ, Set.mem_iUnion.mpr ⟨v, Set.mem_iUnion.mpr ⟨hv, hev⟩⟩⟩
  have hcard : Fintype.card (K →+* ℂ) = d := by
    rw [NumberField.Embeddings.card, ← NumberField.RingOfIntegers.rank]
    simpa only [Fintype.card_fin] using finrank_eq_card_basis b
  change p.toOuterMeasure {X | complexSpectralUpperBound K B X ∧ complexSpectralLowerFailure K B X} ≤ _
  calc
    _ ≤ p.toOuterMeasure (⋃ τ : K →+* ℂ, ⋃ u ∈ T, E τ u) := p.toOuterMeasure.mono hsub
    _ ≤ ∑ τ : K →+* ℂ, ∑ u ∈ T, p.toOuterMeasure (E τ u) := by
      apply (measure_iUnion_le (μ := p.toOuterMeasure) _).trans
      rw [tsum_fintype]
      exact Finset.sum_le_sum (fun τ _ => measure_biUnion_finset_le T _)
    _ ≤ ∑ _ : K →+* ℂ, ∑ _ ∈ T, ENNReal.ofReal (Real.exp (-(m : ℝ) / 8240)) := by
      apply Finset.sum_le_sum
      intro τ _
      apply Finset.sum_le_sum
      intro u hu
      exact powerTwo_embedding_energy_failure K hζ hs hσ τ u (hTunit u hu)
    _ = ENNReal.ofReal ((d : ℝ) * T.card * Real.exp (-(m : ℝ) / 8240)) := by
      simp only [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul,
        ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast, mul_assoc]
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      have hc : (T.card : ℝ) ≤ (16385 : ℝ) ^ (2 * r) := by exact_mod_cast hTcard'
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg d)) (Real.exp_pos _).le

end GeometricGaussianLHL
end

end PowerTwoLowerSpectralEvent

section CanonicalSpectralLower

/-!
## Lower spectral bounds transported to the canonical real operator

Uniform complex-adjoint bounds transfer by summing squared norms over
all embeddings. Orthonormal canonical coordinates then preserve the bound
and identify it with the smallest transverse stretch of the real matrix.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Module NumberField
open scoped InnerProductSpace

namespace GeometricGaussianLHL

theorem linear_lower_norm_of_unit {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (A : E →L[ℝ] F) {c : ℝ}
    (h : ∀ x, ‖x‖ = 1 → c ≤ ‖A x‖) (x : E) : c * ‖x‖ ≤ ‖A x‖ := by
  by_cases hx : x = 0
  · simp [hx]
  have hp : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hu : ‖‖x‖⁻¹ • x‖ = 1 := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hp.le), inv_mul_cancel₀ hp.ne']
  have hb := h (‖x‖⁻¹ • x) hu
  rw [map_smul, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hp.le)] at hb
  calc
    c * ‖x‖ ≤ (‖x‖⁻¹ * ‖A x‖) * ‖x‖ := mul_le_mul_of_nonneg_right hb hp.le
    _ = ‖A x‖ := by field_simp

variable (K : Type*) [Field K] [NumberField K] {d r m : ℕ}

local instance spectralLowerEmbeddingsFintype : Fintype (K →+* ℂ) := inferInstance
local instance spectralLowerAmbientInner : InnerProductSpace ℝ (CanonicalAmbient K) := inferInstance
local instance spectralLowerSpaceInner : InnerProductSpace ℝ (canonicalSpace K) := inferInstance
local instance spectralLowerPowerInner (n : ℕ) : InnerProductSpace ℝ (CanonicalPower K n) := inferInstance

theorem canonicalMatrixMap_adjoint_lower (b : Basis (Fin d) ℤ (𝓞 K))
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) {c : ℝ} (hc : 0 ≤ c)
    (hX : ∀ τ : K →+* ℂ, ∀ u : EuclideanSpace ℂ (Fin r), ‖u‖ = 1 →
      c ≤ ‖(complexEmbeddingOperator K τ X).adjoint u‖) (Y : CanonicalPower K r) :
    c * ‖Y‖ ≤ ‖(canonicalMatrixMap K b X).toContinuousLinearMap.adjoint Y‖ := by
  apply (sq_le_sq₀ (mul_nonneg hc (norm_nonneg _)) (norm_nonneg _)).mp
  rw [mul_pow, canonicalPower_norm_sq_sum_embeddings K r,
    canonicalPower_norm_sq_sum_embeddings K m, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro τ _
  rw [canonicalMatrixMap_adjoint_projection]
  have h := linear_lower_norm_of_unit ((complexEmbeddingOperator K τ X).adjoint.restrictScalars ℝ)
    (hX τ) (canonicalEmbeddingProjection K r τ Y)
  simpa only [mul_pow, ContinuousLinearMap.coe_restrictScalars'] using (sq_le_sq₀ (mul_nonneg hc (norm_nonneg _)) (norm_nonneg _)).mpr h

theorem canonicalEuclideanMatrix_adjoint_apply (b : Basis (Fin d) ℤ (𝓞 K))
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) (y : Euclidean (r * d)) :
    (canonicalEuclideanMatrix K b X).adjoint y =
      canonicalOrthonormalCoordinates K b m
        ((canonicalMatrixMap K b X).toContinuousLinearMap.adjoint
          ((canonicalOrthonormalCoordinates K b r).symm y)) := by
  apply ext_inner_left ℝ
  intro x
  rw [LinearMap.adjoint_inner_right]
  change inner ℝ (canonicalOrthonormalCoordinates K b r
    (canonicalMatrixMap K b X ((canonicalOrthonormalCoordinates K b m).symm x))) y = _
  rw [← (canonicalOrthonormalCoordinates K b r).apply_symm_apply y]
  rw [LinearIsometryEquiv.inner_map_map]
  conv_rhs => lhs; rw [← (canonicalOrthonormalCoordinates K b m).apply_symm_apply x]
  rw [LinearIsometryEquiv.inner_map_map, ContinuousLinearMap.adjoint_inner_right]
  simp only [LinearMap.coe_toContinuousLinearMap', LinearIsometryEquiv.symm_apply_apply]

theorem canonicalEuclideanMatrix_adjoint_lower (b : Basis (Fin d) ℤ (𝓞 K))
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) {c : ℝ} (hc : 0 ≤ c)
    (hX : ∀ τ : K →+* ℂ, ∀ u : EuclideanSpace ℂ (Fin r), ‖u‖ = 1 →
      c ≤ ‖(complexEmbeddingOperator K τ X).adjoint u‖) (y : Euclidean (r * d)) :
    c * ‖y‖ ≤ ‖(canonicalEuclideanMatrix K b X).adjoint y‖ := by
  rw [canonicalEuclideanMatrix_adjoint_apply, LinearIsometryEquiv.norm_map]
  have h := canonicalMatrixMap_adjoint_lower K b X hc hX
    ((canonicalOrthonormalCoordinates K b r).symm y)
  simpa only [LinearIsometryEquiv.norm_map] using h

end GeometricGaussianLHL
end

end CanonicalSpectralLower

section PowerTwoComplexSpectral

/-!
## Simultaneous two-sided complex-block spectral probability

Both exceptional probabilities are charged to the actual matrix PMF.
The column constant is absolute; the lower constant is `1/2048` and the
upper constant is `4`. Transfer of the complex adjoints to the canonical
real adjoint remains a separate geometric obligation.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Module NumberField MeasureTheory
open scoped ENNReal

namespace GeometricGaussianLHL

theorem pmf_good_mass_of_outer_compl_bound {α : Type*} (p : PMF α) (G : Set α)
    {δ : ℝ} (hδ : 0 ≤ δ) (hbad : p.toOuterMeasure Gᶜ ≤ ENNReal.ofReal δ) :
    ENNReal.ofReal (1 - δ) ≤ p.toOuterMeasure G := by
  let : MeasurableSpace α := ⊤
  rw [← PMF.toMeasure_apply_eq_toOuterMeasure p G]
  apply ENNReal.ofReal_le_of_le_toReal
  rw [← PMF.toMeasure_apply_eq_toOuterMeasure p Gᶜ] at hbad
  have hc := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbad
  rw [ENNReal.toReal_ofReal hδ] at hc
  have he := probReal_compl_eq_one_sub (μ := p.toMeasure) (show MeasurableSet G from trivial)
  change p.toMeasure.real Gᶜ ≤ δ at hc
  change 1 - δ ≤ p.toMeasure.real G
  linarith

variable (K : Type*) [Field K] [NumberField K] {k r m : ℕ}
  [IsCyclotomicExtension {2 ^ (k + 1)} ℚ K] {ζ : K}

theorem powerTwo_complex_spectral_event (hζ : IsPrimitiveRoot ζ (2 ^ (k + 1)))
    {s δ : ℝ} (hs : 0 < s) (hσ : 1 ≤ s / Real.sqrt (2 ^ (k + 1)).totient)
    (hδ : 0 < δ) (hδone : δ < 1)
    (hcols : lowerSpectralColumnConstant * ((r : ℝ) + Real.log (2 * (2 ^ (k + 1)).totient / δ)) ≤ m) :
    ENNReal.ofReal (1 - δ) ≤
      (numberFieldMatrixLaw K (cyclotomicIntegralBasis K hζ) r m s hs.ne').toOuterMeasure
        {X | complexSpectralUpperBound K (s * Real.sqrt m) X ∧
          ∀ τ : K →+* ℂ, ∀ u : EuclideanSpace ℂ (Fin r), ‖u‖ = 1 →
            s * Real.sqrt m / 2048 ≤ ‖(complexEmbeddingOperator K τ X).adjoint u‖} := by
  let b := cyclotomicIntegralBasis K hζ
  let d := (2 ^ (k + 1)).totient
  let p := numberFieldMatrixLaw K b r m s hs.ne'
  let B := s * Real.sqrt m
  let G := {X : Matrix (Fin r) (Fin m) (𝓞 K) | complexSpectralUpperBound K B X ∧
    ∀ τ : K →+* ℂ, ∀ u : EuclideanSpace ℂ (Fin r), ‖u‖ = 1 →
      B / 2048 ≤ ‖(complexEmbeddingOperator K τ X).adjoint u‖}
  have hd : 0 < d := integralBasis_dimension_pos K b
  have hcond := lowerSpectral_columns_upper_conditions hd hδ hδone hcols
  have hupper : p.toOuterMeasure {X | ¬complexSpectralUpperBound K B X} ≤ ENNReal.ofReal (δ / 2) := by
    have hlog : Real.log (2 * (d : ℝ) / (δ / 2)) ≤ m := by
      have he : 2 * (d : ℝ) / (δ / 2) = 4 * d / δ := by ring
      rw [he]
      exact hcond.2
    have h := numberField_spherical_embedding_four_failure K b hs (by positivity : 0 < δ / 2)
      (by linarith : δ / 2 < 1) hcond.1 hlog
    simpa only [complexSpectralUpperBound, not_forall, not_le, B, mul_assoc] using h
  have hlower : p.toOuterMeasure {X | complexSpectralUpperBound K B X ∧
      complexSpectralLowerFailure K B X} ≤ ENNReal.ofReal (δ / 2) := by
    exact (powerTwo_lower_spectral_failure_on_upper K hζ hs hσ).trans
      (ENNReal.ofReal_le_ofReal (lowerSpectral_net_failure_budget hd hδ hδone hcols))
  change ENNReal.ofReal (1 - δ) ≤ p.toOuterMeasure G
  apply pmf_good_mass_of_outer_compl_bound p G hδ.le
  have hsub : Gᶜ ⊆ {X | ¬complexSpectralUpperBound K B X} ∪
      {X | complexSpectralUpperBound K B X ∧ complexSpectralLowerFailure K B X} := by
    intro X hX
    by_cases hu : complexSpectralUpperBound K B X
    · right
      refine ⟨hu, ?_⟩
      by_contra hn
      apply hX
      refine ⟨hu, ?_⟩
      intro τ u hunit
      by_contra hf
      exact hn ⟨τ, u, hunit, lt_of_not_ge hf⟩
    · exact Or.inl hu
  apply (p.toOuterMeasure.mono hsub).trans
  apply (measure_union_le (μ := p.toOuterMeasure) _ _).trans
  apply (add_le_add hupper hlower).trans_eq
  rw [← ENNReal.ofReal_add (by positivity : 0 ≤ δ / 2) (by positivity : 0 ≤ δ / 2)]
  congr 1
  ring

end GeometricGaussianLHL
end

end PowerTwoComplexSpectral

section PowerTwoNaturalScale

/-!
## The spectral natural scale of the canonical kernel

The actual spectral event bounds the smoothing parameter from below on
the integer-surjectivity event, as stipulated in the paper. Real full row
rank is not substituted for integer surjectivity. The necessary kernel-rank
restriction is explicit, and the constant is absolute.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Module NumberField MeasureTheory

namespace GeometricGaussianLHL

variable (K : Type*) [Field K] [NumberField K] {k r m : ℕ}
  [IsCyclotomicExtension {2 ^ (k + 1)} ℚ K] {ζ : K}

local instance naturalSpectralEmbeddingsFintype : Fintype (K →+* ℂ) := inferInstance
local instance naturalSpectralAmbientInner : InnerProductSpace ℝ (CanonicalAmbient K) := inferInstance
local instance naturalSpectralSpaceInner : InnerProductSpace ℝ (canonicalSpace K) := inferInstance
local instance naturalSpectralPowerInner (n : ℕ) : InnerProductSpace ℝ (CanonicalPower K n) := inferInstance

theorem powerTwo_kernel_natural_lower_of_embeddings (hζ : IsPrimitiveRoot ζ (2 ^ (k + 1)))
    (hr : 0 < r) (hrows : 2 * r ≤ m)
    (hN : 2 ≤ (2 ^ (k + 1)).totient * (m - r))
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) (hX : Function.Surjective X.mulVec)
    {A : ℝ} (hA : 0 < A)
    (hl : ∀ τ : K →+* ℂ, ∀ u : EuclideanSpace ℂ (Fin r), ‖u‖ = 1 →
      A / 2048 ≤ ‖(complexEmbeddingOperator K τ X).adjoint u‖) :
    naturalSpectralConstant * Real.sqrt (2 ^ (k + 1)).totient *
      A ^ ((r : ℝ) / ((m - r : ℕ) : ℝ)) ≤
        smoothingParameter (canonicalKernel K X)
          (realSecurityError (((2 ^ (k + 1)).totient * (m - r) : ℕ))) := by
  let b := cyclotomicIntegralBasis K hζ
  let d := (2 ^ (k + 1)).totient
  let q := (r : ℝ) / ((m - r : ℕ) : ℝ)
  have hd := integralBasis_dimension_pos K b
  have hmr : r < m := by omega
  let : Nonempty (Fin (r * d)) := ⟨⟨0, Nat.mul_pos hr hd⟩⟩
  let : Nontrivial (CanonicalPower K r) :=
    (canonicalOrthonormalCoordinates K b r).symm.injective.nontrivial
  have hc : 0 < A / 2048 := by positivity
  let f := canonicalMatrixMap K b X
  have hf := canonicalMatrixMap_surjective K b X hX
  have hlow : ∀ Y, (A / 2048) * ‖Y‖ ≤ ‖f.adjoint Y‖ := by
    intro Y
    have h := canonicalMatrixMap_adjoint_lower K b X hc.le hl Y
    simpa only [f, LinearMap.adjoint_eq_toCLM_adjoint, ContinuousLinearMap.coe_coe] using h
  have hmin := minimumStretch_of_adjoint_lower f hf hc hlow
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hqone : q ≤ 1 := spectral_natural_exponent_le_one hrows hmr
  have he := natural_security_error_parameters
    (show 0 < d * (m - r) from Nat.mul_pos hd (Nat.sub_pos_of_lt hmr))
  have hg := canonicalKernel_natural_smoothing_lower K b X hX hN he.1 he.2.1
  rw [he.2.2, powerTwo_rootDiscr K hζ] at hg
  have hpow := (spectral_lower_factor_rpow hA.le hqone).trans (Real.rpow_le_rpow hc.le hmin hq)
  calc
    naturalSpectralConstant * Real.sqrt d * A ^ q =
        (7 / 10 : ℝ) * Real.sqrt (Real.log 2) * Real.sqrt d * (A ^ q / 2048) := by
      unfold naturalSpectralConstant
      ring
    _ ≤ (7 / 10 : ℝ) * Real.sqrt (Real.log 2) * Real.sqrt d *
        kernelMinimumStretch f hf ^ q :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ ≤ _ := hg

/-- With probability at least `1-δ`, the natural-scale estimate holds
whenever the sampled matrix is surjective over the ring of integers.
-/
theorem powerTwo_kernel_natural_spectral_event (hζ : IsPrimitiveRoot ζ (2 ^ (k + 1)))
    (hr : 0 < r) (hN : 2 ≤ (2 ^ (k + 1)).totient * (m - r))
    {s δ : ℝ} (hs : 0 < s) (hσ : 1 ≤ s / Real.sqrt (2 ^ (k + 1)).totient)
    (hδ : 0 < δ) (hδone : δ < 1)
    (hcols : lowerSpectralColumnConstant *
      ((r : ℝ) + Real.log (2 * (2 ^ (k + 1)).totient / δ)) ≤ m) :
    ENNReal.ofReal (1 - δ) ≤
      (numberFieldMatrixLaw K (cyclotomicIntegralBasis K hζ) r m s hs.ne').toOuterMeasure
        {X | Function.Surjective X.mulVec →
          naturalSpectralConstant * Real.sqrt (2 ^ (k + 1)).totient *
            (s * Real.sqrt m) ^ ((r : ℝ) / ((m - r : ℕ) : ℝ)) ≤
              smoothingParameter (canonicalKernel K X)
                (realSecurityError (((2 ^ (k + 1)).totient * (m - r) : ℕ)))} := by
  have hd := integralBasis_dimension_pos K (cyclotomicIntegralBasis K hζ)
  have hrows := spectral_columns_twice_rows hd hδ hδone hcols
  have hm : (0 : ℝ) < m := Nat.cast_pos.mpr (by omega)
  have hA : 0 < s * Real.sqrt m := by positivity
  apply (powerTwo_complex_spectral_event K hζ hs hσ hδ hδone hcols).trans
  apply OuterMeasure.mono
  rintro X ⟨_, hl⟩ hX
  exact powerTwo_kernel_natural_lower_of_embeddings K hζ hr hrows hN X hX hA hl

end GeometricGaussianLHL
end

end PowerTwoNaturalScale

section PowerTwoSpectralCertificate

/-!
## The complete power-of-two singular-value probability bound

For the actual spherical ring-Gaussian matrix law, the canonical real
operator is surjective and its smallest transverse stretch and operator
norm lie between `s sqrt(m) / 2048` and `4 s sqrt(m)`, with probability
at least `1 - δ`. The column constant is the explicit absolute constant
`8240 * (2 * log 16385 + 2)`. Positive row dimension makes both singular
extrema meaningful. The proof includes the degree-one cyclotomic field.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Module NumberField
open scoped ENNReal

namespace GeometricGaussianLHL

variable (K : Type*) [Field K] [NumberField K] {k r m : ℕ}
  [IsCyclotomicExtension {2 ^ (k + 1)} ℚ K] {ζ : K}

theorem powerTwo_canonical_spectral_event (hζ : IsPrimitiveRoot ζ (2 ^ (k + 1)))
    (hr : 0 < r) {s δ : ℝ} (hs : 0 < s)
    (hσ : 1 ≤ s / Real.sqrt (2 ^ (k + 1)).totient) (hδ : 0 < δ) (hδone : δ < 1)
    (hcols : lowerSpectralColumnConstant *
      ((r : ℝ) + Real.log (2 * (2 ^ (k + 1)).totient / δ)) ≤ m) :
    ENNReal.ofReal (1 - δ) ≤
      (numberFieldMatrixLaw K (cyclotomicIntegralBasis K hζ) r m s hs.ne').toOuterMeasure
        {X | ∃ hX : Function.Surjective (canonicalEuclideanMatrix K (cyclotomicIntegralBasis K hζ) X),
          s * Real.sqrt m / 2048 ≤
            kernelMinimumStretch (canonicalEuclideanMatrix K (cyclotomicIntegralBasis K hζ) X) hX ∧
          kernelMinimumStretch (canonicalEuclideanMatrix K (cyclotomicIntegralBasis K hζ) X) hX ≤
            ‖(canonicalEuclideanMatrix K (cyclotomicIntegralBasis K hζ) X).toContinuousLinearMap‖ ∧
          ‖(canonicalEuclideanMatrix K (cyclotomicIntegralBasis K hζ) X).toContinuousLinearMap‖ ≤
            4 * s * Real.sqrt m} := by
  let b := cyclotomicIntegralBasis K hζ
  let d := (2 ^ (k + 1)).totient
  have hd : 0 < d := integralBasis_dimension_pos K b
  let : Nonempty (Fin (r * d)) := ⟨⟨0, Nat.mul_pos hr hd⟩⟩
  have hrm : (r : ℝ) ≤ m := by
    exact_mod_cast (lowerSpectral_columns_upper_conditions hd hδ hδone hcols).1
  have hm : (0 : ℝ) < m := lt_of_lt_of_le (Nat.cast_pos.mpr hr) hrm
  have hc : 0 < s * Real.sqrt m / 2048 := by positivity
  apply (powerTwo_complex_spectral_event K hζ hs hσ hδ hδone hcols).trans
  apply MeasureTheory.OuterMeasure.mono
  rintro X ⟨hu, hl⟩
  let f := canonicalEuclideanMatrix K b X
  have hlow : ∀ y, (s * Real.sqrt m / 2048) * ‖y‖ ≤ ‖f.adjoint y‖ :=
    canonicalEuclideanMatrix_adjoint_lower K b X hc.le hl
  have hsurj : Function.Surjective f := surjective_of_adjoint_lower f hc hlow
  refine ⟨hsurj, minimumStretch_of_adjoint_lower f hsurj hc hlow,
    kernelMinimumStretch_le_opNorm f hsurj, ?_⟩
  have hupper := canonicalEuclideanMatrix_norm_le_embeddings K b X
    (show 0 ≤ 4 * (s * Real.sqrt m) by positivity) hu
  simpa only [mul_assoc] using hupper

end GeometricGaussianLHL
end

end PowerTwoSpectralCertificate
