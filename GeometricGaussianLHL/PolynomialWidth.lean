import GeometricGaussianLHL.GaussianPushforward
import GeometricGaussianLHL.SmoothingBounds
import GeometricGaussianLHL.ThetaIntegral

/-!
# Polynomial-width smoothing theorems

This module collects the following proof sections, in dependency order.
- Elementary growth bounds for the polynomial-width family (`PolynomialGrowth`).
- A rank potential for sequential column exposure (`RankPotential`).
- Scalar budgets in the finite polynomial-width theorem (`MatrixParameters`).
- Expected theta remainders (`RemainderExpectation`).
- Expected block-matrix integrands (`BlockExpectation`).
- Rank failure for actual independent columns (`RankFailure`).
- Parameters and elementary budgets at constant width (`ConstantWidthParameters`).
- Scalar bounds for the growing-rank family (`PolynomialBudget`).
- The remainder exceptional event for Gaussian block matrices (`BlockRemainder`).
- Numerical constants in the pinned smoothing corollary (`PinnedNumerics`).
- An explicit threshold for the polynomial-width family (`PolynomialFamily`).
- The finite polynomial-width matrix certificate (`PolynomialMatrix`).
- Polynomial-width certificate under a change of metric (`PolynomialCertificate`).
- The finite polynomial-width theorem over number fields (`NumberFieldPolynomial`).
- The pinned dual coefficient minimum (`DualMinimumPinned`).
- Polynomial width and growing rank over a fixed number field (`NumberFieldAsymptotic`).
- The finite power-of-two smoothing corollary (`PowerTwoPolynomial`).
- Two-sided smoothing in the polynomial-width family (`PolynomialPinned`).
-/

section PolynomialGrowth

/-!
## Elementary growth bounds for the polynomial-width family

These estimates keep the paper's natural ceilings and real accuracy
parameter. Explicit square-root bounds for logarithms suffice to make
the logarithmic column height linear in the real rank.
-/

noncomputable section

namespace GeometricGaussianLHL

def polynomialFamilyRows (d : ℕ) (ell : ℝ) : ℕ := ⌈ell / d⌉₊

def polynomialFamilyColumns (c x : ℝ) : ℕ := ⌈c * x * Real.log (2 * x)⌉₊

theorem polynomialFamily_rank_bounds {d : ℕ} (hd : 0 < d) {ell : ℝ} (hell : 0 ≤ ell) :
    ell ≤ ((polynomialFamilyRows d ell * d : ℕ) : ℝ) ∧
      ((polynomialFamilyRows d ell * d : ℕ) : ℝ) < ell + d := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hlo := mul_le_mul_of_nonneg_right (Nat.le_ceil (ell / (d : ℝ))) hd'.le
  have hhi := mul_lt_mul_of_pos_right (Nat.ceil_lt_add_one (div_nonneg hell hd'.le)) hd'
  constructor
  · simpa only [polynomialFamilyRows, Nat.cast_mul, div_mul_cancel₀ ell hd'.ne'] using hlo
  · simpa only [polynomialFamilyRows, Nat.cast_mul, add_mul,
      div_mul_cancel₀ ell hd'.ne', one_mul] using hhi

theorem log_two_mul_le_self {x : ℝ} (hx : 1 ≤ x) : Real.log (2 * x) ≤ x := by
  have hx0 : 0 < x := by linarith
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hx0.ne']
  linarith [Real.log_le_sub_one_of_pos hx0,
    Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]

theorem log_le_two_sqrt {x : ℝ} (hx : 0 ≤ x) : Real.log x ≤ 2 * Real.sqrt x := by
  have h := Real.log_le_rpow_div hx (by norm_num : (0 : ℝ) < 1 / 2)
  rw [← Real.sqrt_eq_rpow] at h
  linarith

theorem polynomialFamilyColumns_lower (c x : ℝ) :
    c * x * Real.log (2 * x) ≤ (polynomialFamilyColumns c x : ℝ) := Nat.le_ceil _

theorem polynomialFamilyColumns_pos {c x : ℝ} (hc : 0 < c) (hx : 1 ≤ x) :
    0 < polynomialFamilyColumns c x := by
  apply Nat.ceil_pos.mpr
  exact mul_pos (mul_pos hc (by linarith)) (Real.log_pos (by linarith))

theorem polynomialFamilyColumns_upper {c x : ℝ} (hc : 0 ≤ c) (hx : 1 ≤ x) :
    (polynomialFamilyColumns c x : ℝ) ≤ (c + 1) * x ^ 2 := by
  have hx0 : 0 < x := by linarith
  have hl : 0 ≤ Real.log (2 * x) := Real.log_nonneg (by linarith)
  have hceil := Nat.ceil_lt_add_one (mul_nonneg (mul_nonneg hc hx0.le) hl)
  have hlog := mul_le_mul_of_nonneg_left (log_two_mul_le_self hx) (mul_nonneg hc hx0.le)
  change (polynomialFamilyColumns c x : ℝ) < c * x * Real.log (2 * x) + 1 at hceil
  nlinarith [sq_nonneg (x - 1)]

theorem polynomialFamilyColumns_log_le {c x : ℝ} (hc : 0 < c) (hx : 25 ≤ x)
    (hconstant : Real.log (2 * (c + 1)) ^ 2 ≤ x) :
    Real.log (2 * (polynomialFamilyColumns c x : ℝ)) ≤ x := by
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hm : (0 : ℝ) < polynomialFamilyColumns c x := by
    exact_mod_cast polynomialFamilyColumns_pos hc hx1
  have hlog := Real.log_le_log (by positivity : 0 < 2 * (polynomialFamilyColumns c x : ℝ))
    (mul_le_mul_of_nonneg_left (polynomialFamilyColumns_upper hc.le hx1) (by norm_num : (0 : ℝ) ≤ 2))
  rw [show 2 * ((c + 1) * x ^ 2) = (2 * (c + 1)) * x ^ 2 by ring,
    Real.log_mul (by positivity : 2 * (c + 1) ≠ 0) (by positivity : x ^ 2 ≠ 0),
    Real.log_pow] at hlog
  norm_num at hlog
  have hs : Real.log (2 * (c + 1)) ≤ Real.sqrt x := by
    apply le_of_sq_le_sq _ (Real.sqrt_nonneg _)
    rwa [Real.sq_sqrt hx0.le]
  have hs5 : 5 ≤ Real.sqrt x := by
    have h := Real.sqrt_le_sqrt hx
    norm_num at h
    exact h
  nlinarith [log_le_two_sqrt hx0.le, Real.sq_sqrt hx0.le,
    mul_nonneg (Real.sqrt_nonneg x) (sub_nonneg.mpr hs5)]

theorem log_inv_realSecurityError (ell : ℝ) :
    Real.log (1 / realSecurityError ell) = ell * Real.log 2 := by
  simp only [realSecurityError, one_div, inv_inv]
  rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2)]

theorem log_two_mul_div_realSecurityError {m : ℕ} (hm : 0 < m) (ell : ℝ) :
    Real.log (2 * m / realSecurityError (ell + 4)) =
      Real.log (2 * m) + (ell + 4) * Real.log 2 := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  rw [div_eq_mul_inv, Real.log_mul (by positivity : (2 : ℝ) * m ≠ 0)
    (inv_ne_zero (realSecurityError_pos _).ne'), ← one_div, log_inv_realSecurityError]

end GeometricGaussianLHL
end

end PolynomialGrowth

section RankPotential

/-!
## A rank potential for sequential column exposure

The potential is zero at full rank and `3^(-rank)` otherwise. A new column
lying in any fixed proper subspace with probability at most one quarter
reduces its expected value by a factor of at least two. This will prove
the rank-failure estimate without selecting a random spanning subset.
-/

noncomputable section

open MeasureTheory

namespace GeometricGaussianLHL

def rankPotential {R : ℕ} (V : Submodule ℝ (Euclidean R)) : ℝ :=
  if V = ⊤ then 0 else (1 / 3 : ℝ) ^ Module.finrank ℝ V

theorem rankPotential_nonneg {R : ℕ} (V : Submodule ℝ (Euclidean R)) : 0 ≤ rankPotential V := by
  unfold rankPotential
  split_ifs <;> positivity

theorem rankPotential_le_one {R : ℕ} (V : Submodule ℝ (Euclidean R)) : rankPotential V ≤ 1 := by
  unfold rankPotential
  split_ifs
  · norm_num
  · exact pow_le_one₀ (by norm_num) (by norm_num)

theorem rankPotential_insert_mem {R : ℕ} (V : Submodule ℝ (Euclidean R))
    {x : Euclidean R} (hx : x ∈ V) : rankPotential (V ⊔ Submodule.span ℝ {x}) = rankPotential V := by
  rw [sup_eq_left.mpr ((Submodule.span_singleton_le_iff_mem x V).mpr hx)]

theorem rankPotential_insert_notMem {R : ℕ} (V : Submodule ℝ (Euclidean R))
    {x : Euclidean R} (hx : x ∉ V) :
    rankPotential (V ⊔ Submodule.span ℝ {x}) ≤ (1 / 3) * rankPotential V := by
  have hV : V ≠ ⊤ := by
    intro h
    apply hx
    rw [h]
    trivial
  by_cases hnew : V ⊔ Submodule.span ℝ {x} = ⊤
  · simp only [rankPotential, ite_eq_left hnew, ite_eq_right hV]
    positivity
  · rw [rankPotential, ite_eq_right hnew, rankPotential, ite_eq_right hV,
      Submodule.finrank_sup_span_singleton hx, pow_succ]
    exact le_of_eq (mul_comm _ _)

theorem rankPotential_insert_le {R : ℕ} (V : Submodule ℝ (Euclidean R)) (x : Euclidean R) :
    rankPotential (V ⊔ Submodule.span ℝ {x}) ≤ rankPotential V := by
  by_cases hx : x ∈ V
  · exact (rankPotential_insert_mem V hx).le
  · have h := rankPotential_insert_notMem V hx
    linarith [rankPotential_nonneg V]

theorem rankPotential_one_step {R : ℕ} (p : PMF (Coeff R))
    (hanti : ∀ V : Submodule ℝ (Euclidean R), V ≠ ⊤ →
      p.toMeasure.real {x : Coeff R | integerEmbedding R x ∈ V} ≤ 1 / 4)
    (V : Submodule ℝ (Euclidean R)) :
    (∑' x : Coeff R, (p x).toReal * rankPotential (V ⊔ Submodule.span ℝ {integerEmbedding R x})) ≤
      (1 / 2) * rankPotential V := by
  classical
  by_cases hV : V = ⊤
  · simp [hV, rankPotential]
  · let A : Set (Coeff R) := {x | integerEmbedding R x ∈ V}ᶜ
    have hprob : (3 / 4 : ℝ) ≤ p.toMeasure.real A := by
      rw [show A = {x : Coeff R | integerEmbedding R x ∈ V}ᶜ from rfl,
        measureReal_compl (Set.to_countable _).measurableSet, probReal_univ]
      linarith [hanti V hV]
    have he := pmf_expectation_bound_of_event p
      (fun x => rankPotential (V ⊔ Submodule.span ℝ {integerEmbedding R x})) A
      (fun x => rankPotential_nonneg _) (fun x => rankPotential_insert_le V _)
      (fun x hx => rankPotential_insert_notMem V hx)
    have hp := mul_le_mul_of_nonneg_left hprob (rankPotential_nonneg V)
    nlinarith

theorem rankPotential_one_step_ennreal {R : ℕ} (p : PMF (Coeff R))
    (hanti : ∀ V : Submodule ℝ (Euclidean R), V ≠ ⊤ →
      p.toMeasure.real {x : Coeff R | integerEmbedding R x ∈ V} ≤ 1 / 4)
    (V : Submodule ℝ (Euclidean R)) :
    (∑' x : Coeff R, p x * ENNReal.ofReal
      (rankPotential (V ⊔ Submodule.span ℝ {integerEmbedding R x}))) ≤
        ENNReal.ofReal ((1 / 2) * rankPotential V) := by
  apply pmf_ennreal_expectation_le_of_bounded _ _
    (fun x => rankPotential_nonneg _) (fun x => rankPotential_insert_le V _)
  exact rankPotential_one_step p hanti V

end GeometricGaussianLHL
end

end RankPotential

section MatrixParameters

/-!
## Scalar budgets in the finite polynomial-width theorem

The determinant scale is at least three, and the paper's logarithmic
height makes the near-origin Gaussian tail fit its error budget.
-/

noncomputable section

namespace GeometricGaussianLHL

def polynomialMatrixScale (R M : ℕ) (s₀ κ μ H : ℝ) : ℝ :=
  polynomialThetaWidth κ μ H * (μ * polynomialColumnThreshold s₀ κ H) * Real.sqrt ((M : ℝ) / R)

theorem polynomialColumnThreshold_ge_lower {s₀ κ H : ℝ} (hs₀ : 0 ≤ s₀)
    (hκ : 1 ≤ κ) (hH : 1 ≤ H) : s₀ ≤ polynomialColumnThreshold s₀ κ H := by
  have hsqrt : (1 : ℝ) ≤ Real.sqrt H := by simpa using Real.sqrt_le_sqrt hH
  have hκ0 : 0 ≤ κ := by linarith
  have h₁ := mul_le_mul_of_nonneg_right hκ hs₀
  have h₂ := mul_le_mul_of_nonneg_left hsqrt (mul_nonneg hκ0 hs₀)
  dsimp [polynomialColumnThreshold]
  nlinarith

theorem polynomialMatrixScale_lower {R M : ℕ} (hR : 1 ≤ R) (hM : 1 ≤ M)
    {s₀ κ μ H : ℝ} (hκ : 1 ≤ κ) (hμ : 1 ≤ μ) (hH : (R : ℝ) ≤ H)
    (hs₀ : 8 * Real.sqrt R ≤ s₀) :
    1 ≤ μ * polynomialColumnThreshold s₀ κ H ∧ 3 ≤ polynomialMatrixScale R M s₀ κ μ H := by
  obtain ⟨hspos, hUpos, ht, _⟩ := polynomialWidth_parameters hR hκ hμ hH hs₀
  have hRreal : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hMreal : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hsqrtR : (1 : ℝ) ≤ Real.sqrt R := by simpa using Real.sqrt_le_sqrt hRreal
  have hsqrtM : (1 : ℝ) ≤ Real.sqrt M := by simpa using Real.sqrt_le_sqrt hMreal
  have hU := polynomialColumnThreshold_ge_lower hspos.le hκ (hRreal.trans hH)
  have hμU : polynomialColumnThreshold s₀ κ H ≤ μ * polynomialColumnThreshold s₀ κ H := by
    nlinarith [mul_le_mul_of_nonneg_right hμ hUpos.le]
  have hB : 8 * Real.sqrt R ≤ μ * polynomialColumnThreshold s₀ κ H := hs₀.trans (hU.trans hμU)
  have hprod : Real.sqrt R * Real.sqrt ((M : ℝ) / R) = Real.sqrt M := by
    rw [← Real.sqrt_mul (show (0 : ℝ) ≤ R by positivity)]
    congr 1
    field_simp
  have hscale : 8 ≤ (μ * polynomialColumnThreshold s₀ κ H) * Real.sqrt ((M : ℝ) / R) := by
    have h := mul_le_mul_of_nonneg_right hB (Real.sqrt_nonneg ((M : ℝ) / R))
    rw [mul_assoc, hprod] at h
    linarith
  refine ⟨by nlinarith, ?_⟩
  dsimp [polynomialMatrixScale]
  nlinarith [mul_le_mul_of_nonneg_left hscale (show 0 ≤ polynomialThetaWidth κ μ H by linarith)]

theorem polynomialThetaWidth_sq_ge {κ μ H : ℝ} (hκ : 1 ≤ κ) (hμ : 1 ≤ μ) (hH : 0 ≤ H) :
    4096 * H ≤ polynomialThetaWidth κ μ H ^ 2 := by
  have hkm : 1 ≤ κ * μ := by
    nlinarith [mul_nonneg (show 0 ≤ κ - 1 by linarith) (show 0 ≤ μ - 1 by linarith)]
  have ht : 64 * Real.sqrt H ≤ polynomialThetaWidth κ μ H := by
    dsimp [polynomialThetaWidth]
    nlinarith [mul_le_mul_of_nonneg_right hkm (Real.sqrt_nonneg H)]
  nlinarith [Real.sq_sqrt hH, Real.sqrt_nonneg H]

theorem logarithmic_height_near_budget {R M m : ℕ} (hR : 1 ≤ R) (hm : 1 ≤ m)
    (hM : 0 < M) (hMR : M ≤ R * m) {δ H : ℝ} (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
    (hheight : H = (R : ℝ) + Real.log (2 * m / δ)) : Real.log (6 * M / δ) ≤ 2 * H := by
  have hRreal : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hmreal : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hMreal : (0 : ℝ) < M := by exact_mod_cast hM
  have hMRreal : (M : ℝ) ≤ R * m := by exact_mod_cast hMR
  have harg : 6 * M / δ ≤ (2 * m / δ) * (3 * R) := by
    have h := div_le_div_of_nonneg_right (show 6 * (M : ℝ) ≤ 6 * (R * m) by linarith) hδ.le
    calc
      _ ≤ 6 * ((R : ℝ) * m) / δ := h
      _ = _ := by ring
  have hlog := Real.log_le_log (show 0 < 6 * (M : ℝ) / δ by positivity) harg
  rw [Real.log_mul (by positivity : (2 * (m : ℝ) / δ) ≠ 0) (by positivity : (3 * (R : ℝ)) ≠ 0),
    Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) (by positivity : (R : ℝ) ≠ 0)] at hlog
  have hlogR : Real.log R ≤ (R : ℝ) := Real.log_le_self (by positivity)
  have hthree : (3 : ℝ) ≤ 2 * m / δ := (le_div_iff₀ hδ).mpr (by linarith)
  have hlogthree := Real.log_le_log (by norm_num : (0 : ℝ) < 3) hthree
  rw [hheight]
  linarith

/-- The near-origin exponential correction is at most half the failure budget.
-/
theorem polynomialWidth_mainTerm_small {R M m : ℕ} {ell : ℝ} (hR : 1 ≤ R) (hm : 1 ≤ m) (hell : 1 ≤ ell)
    (hM : 0 < M) (hMR : M ≤ R * m) {κ μ : ℝ} (hκ : 1 ≤ κ) (hμ : 1 ≤ μ) :
    3 * (M : ℝ) * Real.exp (-Real.pi * polynomialThetaWidth κ μ (polynomialColumnHeight R m ell) ^ 2 / 2) ≤
      realSecurityError (ell + 4) / 2 := by
  have hδhalf : realSecurityError (ell + 4) ≤ 1 / 2 := by
    exact (real_polynomial_failureBudget_le hell).trans (by norm_num)
  have hlog := logarithmic_height_near_budget hR hm hM hMR (realSecurityError_pos _) hδhalf rfl
  have hH : 0 ≤ polynomialColumnHeight R m ell :=
    (show (0 : ℝ) ≤ R by positivity).trans (polynomialColumnHeight_ge_rank hm hell)
  have ht := polynomialThetaWidth_sq_ge hκ hμ hH
  apply mainTerm_small_of_log_bound hM (realSecurityError_pos _)
  have hpi := mul_le_mul_of_nonneg_right Real.two_le_pi
    (sq_nonneg (polynomialThetaWidth κ μ (polynomialColumnHeight R m ell)))
  change Real.log (6 * (M : ℝ) / realSecurityError (ell + 4)) ≤ 2 * polynomialColumnHeight R m ell at hlog
  nlinarith

end GeometricGaussianLHL
end

end MatrixParameters

section RemainderExpectation

/-!
## Expected theta remainders

The actual finite torus integral is converted to a nonnegative integral.
Tonelli exchanges the discrete matrix expectation and integration. A
column-norm event supplies the determinant bound before its indicator is
dropped. No probabilistic remainder estimate is assumed in this conversion.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace GeometricGaussianLHL

theorem centeredUnitCube_measurable (R : ℕ) : MeasurableSet (centeredUnitCube R) := by
  change MeasurableSet {y : Euclidean R | ∀ i, |y i| ≤ (1 / 2 : ℝ)}
  simp only [Set.setOf_forall]
  apply MeasurableSet.iInter
  intro i
  exact measurableSet_le (show Measurable (fun y : Euclidean R => |y i|) by fun_prop) measurable_const

theorem thetaRemainder_nonneg {R M : ℕ} (A : Matrix (Fin R) (Fin M) ℤ) (B : ℝ)
    {t : ℝ} (ht : 0 < t) : 0 ≤ thetaRemainder A B t := by
  unfold thetaRemainder
  apply mul_nonneg
  · unfold gramDet
    positivity
  · exact integral_nonneg (thetaIntegrand_nonneg A ht)

theorem ofReal_thetaRemainder {R M : ℕ} (A : Matrix (Fin R) (Fin M) ℤ) (B : ℝ)
    {t : ℝ} (ht : 0 < t) :
    ENNReal.ofReal (thetaRemainder A B t) = ENNReal.ofReal (t ^ R * gramDet A) *
      ∫⁻ y in centeredUnitCube R \ nearOriginBall R B, ENNReal.ofReal (thetaIntegrand A t y) := by
  have hn : 0 ≤ t ^ R * gramDet A := by unfold gramDet; positivity
  have hi := (thetaIntegrand_integrableOn_cube A ht).mono_set
    (Set.sdiff_subset : centeredUnitCube R \ nearOriginBall R B ⊆ centeredUnitCube R)
  rw [thetaRemainder, ENNReal.ofReal_mul hn,
    ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall (thetaIntegrand_nonneg A ht))]

theorem expected_thetaRemainder_bound {α : Type*} [Countable α] {R M : ℕ}
    (hR : 0 < R) (p : PMF α) (A : α → Matrix (Fin R) (Fin M) ℤ) (G : Set α)
    {B t : ℝ} (hB : 0 ≤ B) (ht : 0 < t) (C : ℝ≥0∞)
    (hcol : ∀ x ∈ G, ∀ j, ‖realColumn (A x) j‖ ≤ B)
    (hcontract : ∀ y ∈ centeredUnitCube R \ nearOriginBall R B,
      (∑' x, p x * ENNReal.ofReal (thetaIntegrand (A x) t y)) ≤ C) :
    (∑' x, p x * G.indicator (fun x => ENNReal.ofReal (thetaRemainder (A x) B t)) x) ≤
      ENNReal.ofReal ((t * B * Real.sqrt ((M : ℝ) / R)) ^ R) * C := by
  classical
  let K : ℝ≥0∞ := ENNReal.ofReal ((t * B * Real.sqrt ((M : ℝ) / R)) ^ R)
  let D : Set (Euclidean R) := centeredUnitCube R \ nearOriginBall R B
  let f : α → Euclidean R → ℝ≥0∞ := fun x y => ENNReal.ofReal (thetaIntegrand (A x) t y)
  have hD : MeasurableSet D := (centeredUnitCube_measurable R).diff (nearOriginBall_measurable R B)
  have hs (x : α) : G.indicator (fun x => ENNReal.ofReal (thetaRemainder (A x) B t)) x ≤
      K * ∫⁻ y in D, f x y := by
    by_cases hx : x ∈ G
    · rw [Set.indicator_of_mem hx, ofReal_thetaRemainder (A x) B ht]
      exact mul_le_mul_left (ENNReal.ofReal_le_ofReal
        (normalized_gramDet_le_column_bound hR (A x) hB ht.le (hcol x hx))) _
    · simp only [Set.indicator_of_notMem hx]
      exact zero_le
  have hmeas (x : α) : AEMeasurable (fun y => p x * f x y) (volume.restrict D) := by
    exact (measurable_const.mul (thetaIntegrand_measurable (A x) t).ennreal_ofReal).aemeasurable
  have hint : (∫⁻ y in D, ∑' x, p x * f x y) ≤ C := by
    calc
      _ ≤ ∫⁻ _y in D, C := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem hD] with y hy
        exact hcontract y hy
      _ = C * volume D := by simp only [lintegral_const, Measure.restrict_apply_univ]
      _ ≤ C * volume (centeredUnitCube R) := mul_le_mul_right (measure_mono Set.sdiff_subset) C
      _ = C := by rw [centeredUnitCube_volume, mul_one]
  calc
    _ ≤ ∑' x, p x * (K * ∫⁻ y in D, f x y) :=
      ENNReal.tsum_le_tsum (fun x => mul_le_mul_right (hs x) (p x))
    _ = K * ∑' x, p x * ∫⁻ y in D, f x y := by
      rw [← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro x
      ring
    _ = K * ∫⁻ y in D, ∑' x, p x * f x y := by
      rw [lintegral_tsum hmeas]
      congr 1
      apply tsum_congr
      intro x
      rw [lintegral_const_mul' _ _ (p.apply_ne_top x)]
    _ ≤ K * C := mul_le_mul_right hint K

end GeometricGaussianLHL
end

end RemainderExpectation

section BlockExpectation

/-!
## Expected block-matrix integrands

The factorization of the actual integer block matrix and the independent ellipsoidal column law turn
the one-column expectation lemma into exponential decay across columns.
-/

noncomputable section

open scoped BigOperators ENNReal

namespace GeometricGaussianLHL

theorem polynomialWidth_operatorColumn_expectation {R d m : ℕ} {ell : ℝ}
    (hR : 1 ≤ R) (hm : 1 ≤ m) (hell : 1 ≤ ell) (hdR : d ≤ R)
    (S : Euclidean R ≃L[ℝ] Euclidean R) {s₀ κ μ : ℝ}
    (hκ : 1 ≤ κ) (hμ : 1 ≤ μ) (hs₀ : 8 * Real.sqrt R ≤ s₀)
    (hlower : ‖S.symm.toContinuousLinearMap‖ ≤ 1 / s₀)
    (T : Fin d → Euclidean R →ₗ[ℝ] Euclidean R) (i : Fin d) (hidentity : T i = LinearMap.id)
    (y : Euclidean R) (hcube : y ∈ centeredUnitCube R)
    (hfar : 1 / (4 * μ * polynomialColumnThreshold s₀ κ (polynomialColumnHeight R m ell)) < ‖y‖) :
    (∑' x : Coeff R, ellipsoidalGaussian S 0 x * ENNReal.ofReal
      (operatorColumnFactor T (polynomialThetaWidth κ μ (polynomialColumnHeight R m ell)) y x)) ≤
        ENNReal.ofReal (7 / 8) := by
  have htpos : 0 < polynomialThetaWidth κ μ (polynomialColumnHeight R m ell) := by
    have h := (polynomialWidth_parameters hR hκ hμ (polynomialColumnHeight_ge_rank (ell := ell) hm hell) hs₀).2.2.1
    linarith
  apply pmf_ennreal_expectation_le_of_bounded _ _
    (operatorColumnFactor_nonneg T htpos y) (operatorColumnFactor_le T htpos y)
  exact polynomialWidth_one_operator_column hR hm hell hdR S hκ hμ hs₀ hlower T i hidentity y hcube hfar

/-- The expected theta integrand of the actual integer matrix decays as `(7/8)^m`. -/
theorem polynomialWidth_block_expectation {R d m : ℕ} {ell : ℝ}
    (hR : 1 ≤ R) (hm : 1 ≤ m) (hell : 1 ≤ ell) (hdR : d ≤ R)
    (S : Euclidean R ≃L[ℝ] Euclidean R) {s₀ κ μ : ℝ}
    (hκ : 1 ≤ κ) (hμ : 1 ≤ μ) (hs₀ : 8 * Real.sqrt R ≤ s₀)
    (hlower : ‖S.symm.toContinuousLinearMap‖ ≤ 1 / s₀)
    (T : Fin d → Matrix (Fin R) (Fin R) ℤ) (i : Fin d) (hidentity : T i = 1)
    (y : Euclidean R) (hcube : y ∈ centeredUnitCube R)
    (hfar : 1 / (4 * μ * polynomialColumnThreshold s₀ κ (polynomialColumnHeight R m ell)) < ‖y‖) :
    (∑' X : Fin m → Coeff R, ellipsoidalColumnLaw m S X * ENNReal.ofReal
      (thetaIntegrand (blockCoefficientMatrix T X)
        (polynomialThetaWidth κ μ (polynomialColumnHeight R m ell)) y)) ≤
        ENNReal.ofReal ((7 / 8 : ℝ) ^ m) := by
  let t := polynomialThetaWidth κ μ (polynomialColumnHeight R m ell)
  let F := operatorColumnFactor (fun k => realCoefficientMap (T k)) t y
  have htpos : 0 < t := by
    have h := (polynomialWidth_parameters hR hκ hμ (polynomialColumnHeight_ge_rank (ell := ell) hm hell) hs₀).2.2.1
    change 8 ≤ t at h
    linarith
  have hF : ∀ x, 0 ≤ F x := operatorColumnFactor_nonneg _ htpos y
  have hsingle : (∑' x, ellipsoidalGaussian S 0 x * ENNReal.ofReal (F x)) ≤ ENNReal.ofReal (7 / 8) :=
    polynomialWidth_operatorColumn_expectation hR hm hell hdR S hκ hμ hs₀ hlower
      (fun k => realCoefficientMap (T k)) i (by rw [hidentity, realCoefficientMap_one]) y hcube hfar
  have heq (X : Fin m → Coeff R) :
      ENNReal.ofReal (thetaIntegrand (blockCoefficientMatrix T X) t y) = ∏ j, ENNReal.ofReal (F (X j)) := by
    rw [thetaIntegrand_block_factorization]
    exact ENNReal.ofReal_prod_of_nonneg (fun j _ => hF (X j))
  change (∑' X, independentProduct (fun _ : Fin m => ellipsoidalGaussian S 0) X *
    ENNReal.ofReal (thetaIntegrand (blockCoefficientMatrix T X) t y)) ≤ _
  simp_rw [heq]
  have h := independentProduct_expectation_le (fun _ : Fin m => ellipsoidalGaussian S 0)
    (fun _ x => ENNReal.ofReal (F x)) (fun _ => ENNReal.ofReal (7 / 8)) (fun _ => hsingle)
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 7 / 8)] using h

end GeometricGaussianLHL
end

end BlockExpectation

section RankFailure

/-!
## Rank failure for actual independent columns

Sequential exposure contracts the rank potential by one half per column.
Its positive lower bound on every proper subspace then gives an exponential
failure bound. This replaces the paper's spanning-subset union argument.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace GeometricGaussianLHL

def sampledSpan {R m : ℕ} (V : Submodule ℝ (Euclidean R)) (X : Fin m → Coeff R) :
    Submodule ℝ (Euclidean R) := V ⊔ Submodule.span ℝ (Set.range (fun j => integerEmbedding R (X j)))

theorem sampledSpan_cons {R m : ℕ} (V : Submodule ℝ (Euclidean R))
    (x : Coeff R) (X : Fin m → Coeff R) :
    sampledSpan V (Fin.cons x X) = sampledSpan (V ⊔ Submodule.span ℝ {integerEmbedding R x}) X := by
  have heq : (fun j : Fin (m + 1) => integerEmbedding R ((Fin.cons x X : Fin (m + 1) → Coeff R) j)) =
      (Fin.cons (integerEmbedding R x) (fun j => integerEmbedding R (X j)) : Fin (m + 1) → Euclidean R) := by
    funext j
    refine Fin.cases rfl (fun _ => rfl) j
  simp only [sampledSpan, heq, Fin.range_cons, Submodule.span_insert, sup_assoc]

theorem rankPotential_independent_expectation {R : ℕ} (p : PMF (Coeff R))
    (hanti : ∀ V : Submodule ℝ (Euclidean R), V ≠ ⊤ →
      p.toMeasure.real {x : Coeff R | integerEmbedding R x ∈ V} ≤ 1 / 4) :
    ∀ (m : ℕ) (V : Submodule ℝ (Euclidean R)),
      (∑' X : Fin m → Coeff R, independentProduct (fun _ => p) X *
        ENNReal.ofReal (rankPotential (sampledSpan V X))) ≤
          ENNReal.ofReal ((1 / 2 : ℝ) ^ m * rankPotential V) := by
  intro m
  induction m with
  | zero =>
    intro V
    simp [sampledSpan, independentProduct_apply]
  | succ m ih =>
    intro V
    let e := Fin.consEquiv (fun _ : Fin (m + 1) => Coeff R)
    let next : Coeff R → Submodule ℝ (Euclidean R) := fun x => V ⊔ Submodule.span ℝ {integerEmbedding R x}
    calc
      _ = ∑' x : Coeff R, p x * (∑' X : Fin m → Coeff R,
          independentProduct (fun _ => p) X * ENNReal.ofReal (rankPotential (sampledSpan (next x) X))) := by
        rw [← e.tsum_eq]
        rw [ENNReal.tsum_prod']
        change (∑' x : Coeff R, ∑' X : Fin m → Coeff R,
          independentProduct (fun _ => p) (Fin.cons x X) *
            ENNReal.ofReal (rankPotential (sampledSpan V (Fin.cons x X)))) = _
        simp only [independentProduct_apply, Fin.prod_univ_succ,
          Fin.cons_zero, Fin.cons_succ, sampledSpan_cons, mul_assoc, ENNReal.tsum_mul_left, next]
      _ ≤ ∑' x : Coeff R, p x * ENNReal.ofReal ((1 / 2 : ℝ) ^ m * rankPotential (next x)) := by
        apply ENNReal.tsum_le_tsum
        intro x
        exact mul_le_mul_right (ih (next x)) (p x)
      _ = ENNReal.ofReal ((1 / 2 : ℝ) ^ m) *
          (∑' x : Coeff R, p x * ENNReal.ofReal (rankPotential (next x))) := by
        simp_rw [ENNReal.ofReal_mul (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) m)]
        rw [← ENNReal.tsum_mul_left]
        apply tsum_congr
        intro x
        ring
      _ ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ m) * ENNReal.ofReal ((1 / 2) * rankPotential V) := by
        exact mul_le_mul_right (rankPotential_one_step_ennreal p hanti V) _
      _ = _ := by
        rw [← ENNReal.ofReal_mul (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) m), pow_succ]
        congr 1
        ring

theorem rankPotential_ge_on_proper {R : ℕ} (V : Submodule ℝ (Euclidean R)) (hV : V ≠ ⊤) :
    (1 / 3 : ℝ) ^ R ≤ rankPotential V := by
  rw [rankPotential, ite_eq_right hV]
  have hdim : Module.finrank ℝ V ≤ R := by simpa using Submodule.finrank_le V
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hdim

/-- An exponential full-rank estimate for the actual product distribution.
-/
theorem independent_columns_rank_failure {R : ℕ} (p : PMF (Coeff R))
    (hanti : ∀ V : Submodule ℝ (Euclidean R), V ≠ ⊤ →
      p.toMeasure.real {x : Coeff R | integerEmbedding R x ∈ V} ≤ 1 / 4) (m : ℕ) :
    (independentProduct (fun _ : Fin m => p)).toMeasure
      {X | sampledSpan ⊥ X ≠ ⊤} ≤ ENNReal.ofReal ((3 : ℝ) ^ R * (1 / 2 : ℝ) ^ m) := by
  classical
  let P := independentProduct (fun _ : Fin m => p)
  let A : Set (Fin m → Coeff R) := {X | sampledSpan ⊥ X ≠ ⊤}
  have hweighted : ENNReal.ofReal ((1 / 3 : ℝ) ^ R) * P.toMeasure A ≤
      ∑' X, P X * ENNReal.ofReal (rankPotential (sampledSpan ⊥ X)) := by
    rw [PMF.toMeasure_apply_eq_tsum, ← ENNReal.tsum_mul_left]
    apply ENNReal.tsum_le_tsum
    intro X
    by_cases hX : X ∈ A
    · rw [Set.indicator_of_mem hX]
      have h := ENNReal.ofReal_le_ofReal (rankPotential_ge_on_proper (sampledSpan ⊥ X) hX)
      calc
        _ = P X * ENNReal.ofReal ((1 / 3 : ℝ) ^ R) := mul_comm _ _
        _ ≤ _ := mul_le_mul_right h (P X)
    · simp only [Set.indicator_of_notMem hX, mul_zero]
      exact zero_le
  have he : (∑' X, P X * ENNReal.ofReal (rankPotential (sampledSpan ⊥ X))) ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ m) := by
    apply (rankPotential_independent_expectation p hanti m ⊥).trans
    apply ENNReal.ofReal_le_ofReal
    have h := mul_le_mul_of_nonneg_left (rankPotential_le_one (⊥ : Submodule ℝ (Euclidean R)))
      (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) m)
    simpa only [mul_one] using h
  have hcancel : ENNReal.ofReal ((3 : ℝ) ^ R) * ENNReal.ofReal ((1 / 3 : ℝ) ^ R) = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity), ← mul_pow]
    norm_num
  calc
    P.toMeasure A = ENNReal.ofReal ((3 : ℝ) ^ R) * (ENNReal.ofReal ((1 / 3 : ℝ) ^ R) * P.toMeasure A) := by
      rw [← mul_assoc, hcancel, one_mul]
    _ ≤ ENNReal.ofReal ((3 : ℝ) ^ R) * ENNReal.ofReal ((1 / 2 : ℝ) ^ m) :=
      mul_le_mul_right (hweighted.trans he) _
    _ = _ := (ENNReal.ofReal_mul (by positivity)).symm

theorem ellipsoidalColumnLaw_rank_failure {R m : ℕ} (hR : 1 ≤ R)
    (S : Euclidean R ≃L[ℝ] Euclidean R) {s₀ : ℝ} (hs₀ : 8 * Real.sqrt R ≤ s₀)
    (hlower : ‖S.symm.toContinuousLinearMap‖ ≤ 1 / s₀) :
    (ellipsoidalColumnLaw m S).toMeasure {X | sampledSpan ⊥ X ≠ ⊤} ≤
      ENNReal.ofReal ((3 : ℝ) ^ R * (1 / 2 : ℝ) ^ m) := by
  have hRreal : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hsqrtR : (1 : ℝ) ≤ Real.sqrt R := by simpa using Real.sqrt_le_sqrt hRreal
  have hspos : 0 < s₀ := by linarith
  apply independent_columns_rank_failure
  intro V hV
  have hb := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (ellipsoidalGaussian_subspace_bound S hspos hlower V hV)
  rw [ENNReal.toReal_ofReal (show 0 ≤ 2 / s₀ by positivity)] at hb
  change (ellipsoidalGaussian S 0).toMeasure.real {x : Coeff R | integerEmbedding R x ∈ V} ≤ _ at hb
  apply hb.trans
  apply (div_le_iff₀ hspos).mpr
  linarith

theorem rank_failure_budget_of_column_condition {R m : ℕ} {W δ : ℝ}
    (hW : 3 ≤ W) (hδ : 0 < δ)
    (hbudget : (R : ℝ) * Real.log W + 2 * Real.log (1 / δ) ≤ (m : ℝ) * Real.log (8 / 7)) :
    (3 : ℝ) ^ R * (1 / 2 : ℝ) ^ m ≤ δ ^ 2 := by
  have hwlog := Real.log_le_log (by norm_num : (0 : ℝ) < 3) hW
  have hclog := Real.log_le_log (by norm_num : (0 : ℝ) < 8 / 7) (by norm_num : (8 / 7 : ℝ) ≤ 2)
  have h₁ := mul_le_mul_of_nonneg_left hwlog (show (0 : ℝ) ≤ R by positivity)
  have h₂ := mul_le_mul_of_nonneg_left hclog (show (0 : ℝ) ≤ m by positivity)
  have hb : (R : ℝ) * Real.log 3 + 2 * Real.log (1 / δ) ≤ (m : ℝ) * Real.log 2 := by
    linarith
  apply remainder_le_of_column_condition (by norm_num : (0 : ℝ) < 3)
    (by norm_num : (0 : ℝ) < 1 / 2) hδ
  convert hb using 1
  norm_num

theorem polynomialWidth_rank_failure {R m : ℕ} (hR : 1 ≤ R)
    (S : Euclidean R ≃L[ℝ] Euclidean R) {s₀ W δ : ℝ} (hs₀ : 8 * Real.sqrt R ≤ s₀)
    (hlower : ‖S.symm.toContinuousLinearMap‖ ≤ 1 / s₀) (hW : 3 ≤ W) (hδ : 0 < δ)
    (hbudget : (R : ℝ) * Real.log W + 2 * Real.log (1 / δ) ≤ (m : ℝ) * Real.log (8 / 7)) :
    (ellipsoidalColumnLaw m S).toMeasure {X | sampledSpan ⊥ X ≠ ⊤} ≤ ENNReal.ofReal (δ ^ 2) :=
  (ellipsoidalColumnLaw_rank_failure hR S hs₀ hlower).trans
    (ENNReal.ofReal_le_ofReal (rank_failure_budget_of_column_condition hW hδ hbudget))

end GeometricGaussianLHL
end

end RankFailure

section ConstantWidthParameters

/-!
## Parameters and elementary budgets at constant width

The height, scalar width, column threshold and determinant scale are the literal parameters used in
the constant-width smoothing theorem. The error parameter is allowed to be any positive real at most
`1/32` .
-/

noncomputable section

namespace GeometricGaussianLHL

def constantThetaWidth (H : ℝ) : ℝ := 640 * Real.sqrt H

def constantColumnThreshold (s H : ℝ) : ℝ := s * Real.sqrt H

def constantMatrixScale (R M : ℕ) (s H : ℝ) : ℝ :=
  constantThetaWidth H * constantColumnThreshold s H * Real.sqrt ((M : ℝ) / R)

def constantColumnHeight (R m : ℕ) (δ : ℝ) : ℝ := (R : ℝ) + Real.log (2 * m / δ)

theorem constantColumnHeight_ge_rank {R m : ℕ} (hm : 1 ≤ m) {δ : ℝ}
    (hδ : 0 < δ) (hδone : δ ≤ 1) : (R : ℝ) ≤ constantColumnHeight R m δ :=
  logarithmicColumnHeight_ge_rank hm hδ hδone

theorem constantWidth_parameters {R M : ℕ} (hR : 1 ≤ R) (hM : 1 ≤ M)
    {s H : ℝ} (hs : 1 ≤ s) (hH : (R : ℝ) ≤ H) :
    1 ≤ constantColumnThreshold s H ∧ 8 ≤ constantThetaWidth H ∧
      3 ≤ constantMatrixScale R M s H := by
  have hRreal : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hMreal : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hRp : (0 : ℝ) < R := by linarith
  have hrootR : 1 ≤ Real.sqrt R := (Real.le_sqrt (by norm_num) hRp.le).mpr (by simpa using hRreal)
  have hrootH := hrootR.trans (Real.sqrt_le_sqrt hH)
  have hrootM : 1 ≤ Real.sqrt M := (Real.le_sqrt (by norm_num) (by positivity)).mpr (by simpa using hMreal)
  have hU : Real.sqrt R ≤ constantColumnThreshold s H := by
    have h := mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg H)
    dsimp [constantColumnThreshold]
    nlinarith [Real.sqrt_le_sqrt hH]
  have hprod : Real.sqrt R * Real.sqrt ((M : ℝ) / R) = Real.sqrt M := by
    rw [← Real.sqrt_mul hRp.le]
    congr 1
    field_simp
  have hscale : 1 ≤ constantColumnThreshold s H * Real.sqrt ((M : ℝ) / R) := by
    have h := mul_le_mul_of_nonneg_right hU (Real.sqrt_nonneg ((M : ℝ) / R))
    rw [hprod] at h
    linarith
  have ht : 8 ≤ constantThetaWidth H := by dsimp [constantThetaWidth]; linarith
  refine ⟨hrootR.trans hU, ht, ?_⟩
  dsimp [constantMatrixScale]
  have h := mul_le_mul_of_nonneg_left hscale (by linarith : 0 ≤ constantThetaWidth H)
  nlinarith

theorem constantWidth_mainTerm_small {R M m : ℕ} (hR : 1 ≤ R) (hm : 1 ≤ m)
    (hM : 0 < M) (hMR : M ≤ R * m) {δ : ℝ} (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) :
    3 * (M : ℝ) * Real.exp (-Real.pi * constantThetaWidth (constantColumnHeight R m δ) ^ 2 / 2) ≤ δ / 2 := by
  have hlog := logarithmic_height_near_budget hR hm hM hMR hδ hδhalf (H := constantColumnHeight R m δ) rfl
  have hH : 0 ≤ constantColumnHeight R m δ := (show (0 : ℝ) ≤ R by positivity).trans
    (constantColumnHeight_ge_rank hm hδ (by linarith))
  have ht : constantThetaWidth (constantColumnHeight R m δ) ^ 2 =
      409600 * constantColumnHeight R m δ := by
    simp only [constantThetaWidth, mul_pow, Real.sq_sqrt hH]
    ring
  apply mainTerm_small_of_log_bound hM hδ
  rw [ht]
  have hp := mul_le_mul_of_nonneg_right Real.two_le_pi hH
  nlinarith

end GeometricGaussianLHL
end

end ConstantWidthParameters

section PolynomialBudget

/-!
## Scalar bounds for the growing-rank family

The column coefficient is chosen with a fixed positive margin. Coarse
polynomial estimates for the determinant scale suffice for its logarithmic
budget; all constants are independent of the accuracy parameter.
-/

noncomputable section

namespace GeometricGaussianLHL

def polynomialFamilyColumnCoefficient (p : ℝ) : ℝ := (p + 5) / Real.log (8 / 7)

theorem log_eight_sevenths_pos : 0 < Real.log (8 / 7 : ℝ) := Real.log_pos (by norm_num)

theorem polynomialFamilyColumnCoefficient_pos {p : ℝ} (hp : 1 / 2 ≤ p) :
    0 < polynomialFamilyColumnCoefficient p :=
  div_pos (by linarith) log_eight_sevenths_pos

theorem polynomialFamilyColumnCoefficient_mul (p : ℝ) :
    polynomialFamilyColumnCoefficient p * Real.log (8 / 7) = p + 5 :=
  div_mul_cancel₀ _ log_eight_sevenths_pos.ne'

theorem polynomialFamilyColumns_gt {p x : ℝ} (hp : 1 / 2 ≤ p) (hx : 1 ≤ x) :
    x < (polynomialFamilyColumns (polynomialFamilyColumnCoefficient p) x : ℝ) := by
  have hc := polynomialFamilyColumnCoefficient_pos hp
  have hq : Real.log (8 / 7 : ℝ) ≤ Real.log (2 * x) :=
    Real.log_le_log (by norm_num) (by linarith)
  have h := mul_le_mul_of_nonneg_left hq (mul_nonneg hc.le (by linarith : 0 ≤ x))
  have he : polynomialFamilyColumnCoefficient p * x * Real.log (8 / 7) = (p + 5) * x := by
    rw [mul_right_comm, polynomialFamilyColumnCoefficient_mul]
  rw [he] at h
  have hlarge : x < (p + 5) * x := by nlinarith [mul_nonneg (by linarith : 0 ≤ p) (by linarith : 0 ≤ x)]
  exact hlarge.trans_le (h.trans (polynomialFamilyColumns_lower _ _))

theorem polynomialFamily_height_le {R m : ℕ} {ell : ℝ} (hm : 0 < m)
    (hell : 4 ≤ ell) (hellR : ell ≤ R) (hlog : Real.log (2 * m) ≤ (R : ℝ)) :
    polynomialColumnHeight R m ell ≤ 4 * R := by
  rw [polynomialColumnHeight, log_two_mul_div_realSecurityError hm]
  have htwo : Real.log (2 : ℝ) ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have h := mul_le_mul_of_nonneg_left htwo (show 0 ≤ ell + 4 by linarith)
  nlinarith

theorem polynomialFamily_sqrt_ratio_le {r d m : ℕ} (hr : 0 < r) (hd : 0 < d)
    {c : ℝ} (hc : 0 < c) (hm : (m : ℝ) ≤ (c + 1) * ((r * d : ℕ) : ℝ) ^ 2) :
    Real.sqrt ((m : ℝ) / r) ≤ (c + 1) * d * ((r * d : ℕ) : ℝ) := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hR : (1 : ℝ) ≤ (r * d : ℕ) := by exact_mod_cast Nat.mul_pos hr hd
  have he : (c + 1) * ((r * d : ℕ) : ℝ) ^ 2 / r =
      (c + 1) * d * ((r * d : ℕ) : ℝ) := by
    push_cast
    field_simp
  have hratio := div_le_div_of_nonneg_right hm hr'.le
  rw [he] at hratio
  have ha : 1 ≤ (c + 1) * d := by nlinarith
  have hax : 1 ≤ (c + 1) * d * ((r * d : ℕ) : ℝ) := by nlinarith
  exact (Real.sqrt_le_sqrt hratio).trans (Real.sqrt_le_self_iff.mpr (Or.inr hax))

theorem polynomialFamily_scale_le {r d m : ℕ} (hr : 0 < r) (hd : 0 < d)
    {c A p H : ℝ} (hc : 0 < c) (hA : 0 ≤ A)
    (hHupper : H ≤ 4 * ((r * d : ℕ) : ℝ))
    (hm : (m : ℝ) ≤ (c + 1) * ((r * d : ℕ) : ℝ) ^ 2) :
    A * ((r * d : ℕ) : ℝ) ^ p * H * Real.sqrt ((m : ℝ) / r) ≤
      (4 * A * (c + 1) * d) * ((r * d : ℕ) : ℝ) ^ (p + 2) := by
  have hR : (0 : ℝ) < (r * d : ℕ) := by exact_mod_cast Nat.mul_pos hr hd
  have h₁ := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hHupper (mul_nonneg hA (Real.rpow_nonneg hR.le p)))
    (Real.sqrt_nonneg ((m : ℝ) / r))
  have h₂ := mul_le_mul_of_nonneg_left (polynomialFamily_sqrt_ratio_le hr hd hc hm)
    (show 0 ≤ A * ((r * d : ℕ) : ℝ) ^ p * (4 * ((r * d : ℕ) : ℝ)) by positivity)
  apply (h₁.trans h₂).trans_eq
  rw [Real.rpow_add hR, Real.rpow_two]
  ring

theorem polynomialFamily_matrix_scale_eq {r d m : ℕ} (hr : 0 < r) (hd : 0 < d)
    {α κ μ p H : ℝ} (hα : α ≠ 0) (hH : 0 ≤ H) :
    polynomialMatrixScale (r * d) (m * d) ((8 * α * ((r * d : ℕ) : ℝ) ^ p) / α) κ μ H =
      (512 * κ ^ 2 * μ ^ 2) * ((r * d : ℕ) : ℝ) ^ p * H * Real.sqrt ((m : ℝ) / r) := by
  have hr' : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hr.ne'
  have hd' : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  have hratio : ((m * d : ℕ) : ℝ) / ((r * d : ℕ) : ℝ) = (m : ℝ) / r := by
    push_cast
    field_simp
  have hs : (8 * α * ((r * d : ℕ) : ℝ) ^ p) / α = 8 * ((r * d : ℕ) : ℝ) ^ p := by
    field_simp
  rw [polynomialMatrixScale, polynomialThetaWidth, polynomialColumnThreshold, hs, hratio]
  calc
    _ = (512 * κ ^ 2 * μ ^ 2) * ((r * d : ℕ) : ℝ) ^ p * (Real.sqrt H ^ 2) *
        Real.sqrt ((m : ℝ) / r) := by ring
    _ = _ := by rw [Real.sq_sqrt hH]

theorem polynomialFamily_log_budget {p x ell W C : ℝ} (hp : 1 / 2 ≤ p)
    (hx : 16 ≤ x) (hellx : ell ≤ x)
    (hW : 0 < W) (hC : 0 < C) (hCx : C ≤ x) (hscale : W ≤ C * x ^ (p + 2)) :
    x * Real.log W + 2 * Real.log (1 / realSecurityError (ell + 4)) ≤
      (polynomialFamilyColumns (polynomialFamilyColumnCoefficient p) x : ℝ) * Real.log (8 / 7) := by
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hlogC := Real.log_le_log hC hCx
  have hlogW := Real.log_le_log hW hscale
  rw [Real.log_mul hC.ne' (Real.rpow_pos_of_pos hx0 _).ne', Real.log_rpow hx0] at hlogW
  have hW' : Real.log W ≤ (p + 3) * Real.log x := by linarith
  have hlogx : 4 * Real.log 2 ≤ Real.log x := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 16) hx
    have he : Real.log (16 : ℝ) = 4 * Real.log 2 := by
      rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.log_pow]
      norm_num
    rwa [he] at h
  have he := mul_le_mul_of_nonneg_left hlogx hx0.le
  have hδ : 2 * Real.log (1 / realSecurityError (ell + 4)) ≤ x * Real.log x := by
    rw [log_inv_realSecurityError]
    have h := mul_le_mul_of_nonneg_right (show 2 * (ell + 4) ≤ 4 * x by linarith)
      (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))
    nlinarith
  have h₁ := mul_le_mul_of_nonneg_left hW' hx0.le
  have h₂ := mul_le_mul_of_nonneg_right
    (polynomialFamilyColumns_lower (polynomialFamilyColumnCoefficient p) x) log_eight_sevenths_pos.le
  have hc := polynomialFamilyColumnCoefficient_mul p
  have hc' : polynomialFamilyColumnCoefficient p * x * Real.log (2 * x) * Real.log (8 / 7) =
      (p + 5) * x * Real.log (2 * x) := by rw [mul_right_comm _ _ (Real.log (8 / 7)),
        mul_right_comm _ x (Real.log (8 / 7)), hc]
  rw [hc'] at h₂
  have hlog : Real.log x ≤ Real.log (2 * x) := Real.log_le_log hx0 (by linarith)
  have h₃ := mul_le_mul_of_nonneg_left hlog (show 0 ≤ (p + 5) * x by positivity)
  have hnonneg := mul_nonneg hx0.le (Real.log_nonneg hx1)
  nlinarith

end GeometricGaussianLHL
end

end PolynomialBudget

section BlockRemainder

/-!
## The remainder exceptional event for Gaussian block matrices

The actual block-matrix expectation is integrated over the far region,
then the logarithmic column condition and Markov's inequality give the
paper's exceptional-event probability.
-/

noncomputable section

open scoped ENNReal

namespace GeometricGaussianLHL

theorem polynomialWidth_remainder_expectation {R d m : ℕ} {ell : ℝ}
    (hR : 1 ≤ R) (hm : 1 ≤ m) (hell : 1 ≤ ell) (hdR : d ≤ R)
    (S : Euclidean R ≃L[ℝ] Euclidean R) {s₀ κ μ : ℝ}
    (hκ : 1 ≤ κ) (hμ : 1 ≤ μ) (hs₀ : 8 * Real.sqrt R ≤ s₀)
    (hlower : ‖S.symm.toContinuousLinearMap‖ ≤ 1 / s₀)
    (T : Fin d → Matrix (Fin R) (Fin R) ℤ) (i : Fin d) (hidentity : T i = 1)
    (hT : ∀ k, ∀ x : Euclidean R, ‖realCoefficientMap (T k) x‖ ≤ μ * ‖x‖) :
    let H := polynomialColumnHeight R m ell
    let t := polynomialThetaWidth κ μ H
    let U := polynomialColumnThreshold s₀ κ H
    (∑' X : Fin m → Coeff R, ellipsoidalColumnLaw m S X *
      (columnNormEvent U).indicator
        (fun X => ENNReal.ofReal (thetaRemainder (blockCoefficientMatrix T X) (μ * U) t)) X) ≤
      ENNReal.ofReal (polynomialMatrixScale R (m * d) s₀ κ μ H ^ R * (7 / 8 : ℝ) ^ m) := by
  dsimp only
  let H := polynomialColumnHeight R m ell
  let t := polynomialThetaWidth κ μ H
  let U := polynomialColumnThreshold s₀ κ H
  let W := polynomialMatrixScale R (m * d) s₀ κ μ H
  obtain ⟨_, hU, ht, _⟩ := polynomialWidth_parameters hR hκ hμ
    (polynomialColumnHeight_ge_rank (ell := ell) hm hell) hs₀
  have htpos : 0 < t := by change 8 ≤ t at ht; linarith
  have hμ0 : 0 ≤ μ := by linarith
  have hB : 0 ≤ μ * U := mul_nonneg hμ0 hU.le
  have hcols : ∀ X ∈ (columnNormEvent U : Set (Fin m → Coeff R)),
      ∀ j, ‖realColumn (blockCoefficientMatrix T X) j‖ ≤ μ * U := by
    intro X hX
    exact blockCoefficientMatrix_column_norm T X hμ0 hT hX
  have hcontract : ∀ y ∈ centeredUnitCube R \ nearOriginBall R (μ * U),
      (∑' X : Fin m → Coeff R, ellipsoidalColumnLaw m S X *
        ENNReal.ofReal (thetaIntegrand (blockCoefficientMatrix T X) t y)) ≤
          ENNReal.ofReal ((7 / 8 : ℝ) ^ m) := by
    intro y hy
    have hfar : 1 / (4 * μ * U) < ‖y‖ := by
      have hh : 1 / (4 * (μ * U)) < ‖y‖ := lt_of_not_ge hy.2
      simpa only [mul_assoc] using hh
    exact polynomialWidth_block_expectation hR hm hell hdR S hκ hμ hs₀ hlower T i hidentity y hy.1 hfar
  have h := expected_thetaRemainder_bound (by omega) (ellipsoidalColumnLaw m S)
    (blockCoefficientMatrix T) (columnNormEvent U) hB htpos (ENNReal.ofReal ((7 / 8 : ℝ) ^ m)) hcols hcontract
  change _ ≤ ENNReal.ofReal (W ^ R) * ENNReal.ofReal ((7 / 8 : ℝ) ^ m) at h
  rw [← ENNReal.ofReal_mul (show 0 ≤ W ^ R by dsimp [W, polynomialMatrixScale]; positivity)] at h
  exact h

theorem polynomialWidth_remainder_failure {R d m : ℕ} {ell : ℝ}
    (hR : 1 ≤ R) (hm : 1 ≤ m) (hell : 1 ≤ ell) (hdR : d ≤ R)
    (S : Euclidean R ≃L[ℝ] Euclidean R) {s₀ κ μ : ℝ}
    (hκ : 1 ≤ κ) (hμ : 1 ≤ μ) (hs₀ : 8 * Real.sqrt R ≤ s₀)
    (hlower : ‖S.symm.toContinuousLinearMap‖ ≤ 1 / s₀)
    (T : Fin d → Matrix (Fin R) (Fin R) ℤ) (i : Fin d) (hidentity : T i = 1)
    (hT : ∀ k, ∀ x : Euclidean R, ‖realCoefficientMap (T k) x‖ ≤ μ * ‖x‖)
    (hbudget : (R : ℝ) * Real.log (polynomialMatrixScale R (m * d) s₀ κ μ (polynomialColumnHeight R m ell)) +
      2 * Real.log (1 / realSecurityError (ell + 4)) ≤ (m : ℝ) * Real.log (8 / 7)) :
    let H := polynomialColumnHeight R m ell
    let t := polynomialThetaWidth κ μ H
    let U := polynomialColumnThreshold s₀ κ H
    (ellipsoidalColumnLaw m S).toMeasure ((columnNormEvent U) ∩
      {X | realSecurityError (ell + 4) < thetaRemainder (blockCoefficientMatrix T X) (μ * U) t}) ≤
        ENNReal.ofReal (realSecurityError (ell + 4)) := by
  dsimp only
  have hd : 1 ≤ d := by have hi := i.isLt; omega
  have hM : 1 ≤ m * d := by nlinarith
  have hW := (polynomialMatrixScale_lower hR hM hκ hμ
    (polynomialColumnHeight_ge_rank (ell := ell) hm hell) hs₀).2
  have hnumeric := polynomial_remainder_le (show 0 < polynomialMatrixScale R (m * d) s₀ κ μ
    (polynomialColumnHeight R m ell) by linarith) (realSecurityError_pos _) hbudget
  apply pmf_markov_indicator_square _ _ _ (realSecurityError_pos _)
  exact (polynomialWidth_remainder_expectation hR hm hell hdR S hκ hμ hs₀ hlower T i hidentity hT).trans
    (ENNReal.ofReal_le_ofReal hnumeric)

end GeometricGaussianLHL
end

end BlockRemainder

section PinnedNumerics

/-!
## Numerical constants in the pinned smoothing corollary

The column budget and logarithmic-size hypothesis imply `ell ≥ 28` ; this threshold does not need to
be added to the smoothing-parameter pinning corollary. The remaining estimates prove the literal
`2.7` , `225` , and `2250` bounds using rational bounds on `log 2` and `π` .
-/

noncomputable section

namespace GeometricGaussianLHL

theorem pinned_column_condition_accuracy_ge {m : ℕ} {R W ell c q : ℝ}
    (hR : 0 ≤ R) (hW : 1 ≤ W) (hell : 1 ≤ ell) (hc : 4 ≤ c)
    (hq : Real.log q ≤ 1 / 7)
    (hbudget : R * Real.log W + 2 * Real.log (1 / realSecurityError (ell + c)) ≤
      (m : ℝ) * Real.log q) (hsize : Real.log (2 * m) ≤ ell / 10) : 28 ≤ ell := by
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hterm : 0 ≤ R * Real.log W := mul_nonneg hR (Real.log_nonneg hW)
  have hL : (5 : ℝ) ≤ 2 * Real.log (1 / realSecurityError (ell + c)) := by
    rw [log_inv_realSecurityError]
    nlinarith [mul_nonneg (show 0 ≤ ell + c - 5 by linarith) (show 0 ≤ Real.log 2 by linarith)]
  have hm : 16 ≤ m := by
    by_contra hn
    have hn' : (m : ℝ) ≤ 15 := by exact_mod_cast (show m ≤ 15 by omega)
    have hmul := mul_le_mul_of_nonneg_left hq (show (0 : ℝ) ≤ m by positivity)
    linarith
  have hlog : Real.log (32 : ℝ) ≤ Real.log (2 * m) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast (show 32 ≤ 2 * m by omega))
  have h32 : (14 / 5 : ℝ) ≤ Real.log 32 := by
    rw [show (32 : ℝ) = 2 ^ (5 : ℕ) by norm_num, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith [Real.log_two_gt_d9]
  linarith

theorem pinned_security_height_le {R m : ℕ} {ell c : ℝ} (hm : 1 ≤ m)
    (hell : 28 ≤ ell) (hc6 : c ≤ 6) (hR : (R : ℝ) = ell)
    (hsize : Real.log (2 * m) ≤ ell / 10) :
    constantColumnHeight R m (realSecurityError (ell + c)) ≤ (27 / 10) * ell := by
  have hmreal : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hlog : Real.log (2 * m / realSecurityError (ell + c)) =
      Real.log (2 * m) + (ell + c) * Real.log 2 := by
    rw [div_eq_mul_inv, Real.log_mul (by positivity : (2 : ℝ) * m ≠ 0)
      (inv_ne_zero (realSecurityError_pos _).ne'), ← one_div, log_inv_realSecurityError]
  have hmul : (ell + c) * Real.log 2 ≤ (ell + 6) * (7 / 10) :=
    mul_le_mul (by linarith) (by linarith [Real.log_two_lt_d9])
      (Real.log_nonneg (by norm_num)) (by linarith)
  rw [constantColumnHeight, hlog, hR]
  linarith

theorem powerTwoScale_ge_one {d r m : ℕ} (hd : 0 < d) (hr : 1 ≤ r) (hmr : r ≤ m)
    {s H c : ℝ} (hs : Real.sqrt d ≤ s) (hH : 1 ≤ H) (hc : 1 ≤ c) :
    1 ≤ c * (s / Real.sqrt d) * H * Real.sqrt ((m : ℝ) / r) := by
  have hdreal : (0 : ℝ) < d := by exact_mod_cast hd
  have hrreal : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hσ : 1 ≤ s / Real.sqrt d := (le_div_iff₀ (Real.sqrt_pos.mpr hdreal)).mpr (by simpa using hs)
  have hratio : (1 : ℝ) ≤ (m : ℝ) / r := (le_div_iff₀ hrreal).mpr (by simpa only [one_mul] using (show (r : ℝ) ≤ m by exact_mod_cast hmr))
  have hsqrt : (1 : ℝ) ≤ Real.sqrt ((m : ℝ) / r) := by simpa using Real.sqrt_le_sqrt hratio
  have h₁ : 1 ≤ c * (s / Real.sqrt d) := one_le_mul_of_one_le_of_one_le hc hσ
  have h₂ : 1 ≤ c * (s / Real.sqrt d) * H := one_le_mul_of_one_le_of_one_le h₁ hH
  exact one_le_mul_of_one_le_of_one_le h₂ hsqrt

def powerTwoSecurityLowerBound (d : ℕ) (ell : ℝ) : ℝ :=
  Real.sqrt d * Real.sqrt (Real.log ((2 : ℝ) ^ (ell + 1)) / Real.pi)

def pinnedRatioConstant (c : ℝ) : ℝ := c * Real.sqrt ((27 / 10) * Real.pi / Real.log 2)

theorem powerTwoSecurityLowerBound_pos {d : ℕ} (hd : 0 < d) {ell : ℝ} (hell : 0 ≤ ell) :
    0 < powerTwoSecurityLowerBound d ell := by
  have hdreal : (0 : ℝ) < d := by exact_mod_cast hd
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  unfold powerTwoSecurityLowerBound
  rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2)]
  positivity

theorem powerTwoPinned_ratio_bound {d : ℕ} (hd : 0 < d) {ell H c : ℝ}
    (hell : 0 ≤ ell) (hH : 0 ≤ H) (hc : 0 ≤ c) (hheight : H ≤ (27 / 10) * ell) :
    c * Real.sqrt (d * H) / powerTwoSecurityLowerBound d ell ≤ pinnedRatioConstant c := by
  have hdreal : (0 : ℝ) < d := by exact_mod_cast hd
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have he : 0 < ell + 1 := by linarith
  have hratio : Real.sqrt (d * H) / powerTwoSecurityLowerBound d ell =
      Real.sqrt (H * Real.pi / ((ell + 1) * Real.log 2)) := by
    unfold powerTwoSecurityLowerBound
    rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2), ← Real.sqrt_mul hdreal.le,
      ← Real.sqrt_div (mul_nonneg hdreal.le hH)]
    congr 1
    field_simp
  rw [mul_div_assoc, hratio]
  apply mul_le_mul_of_nonneg_left _ hc
  apply Real.sqrt_le_sqrt
  calc
    _ = (H / (ell + 1)) * (Real.pi / Real.log 2) := by field_simp
    _ ≤ (27 / 10) * (Real.pi / Real.log 2) :=
      mul_le_mul_of_nonneg_right ((div_le_iff₀ he).mpr (by linarith)) (by positivity)
    _ = _ := by ring

theorem pinnedRatioConstant_polynomial_lt : pinnedRatioConstant 64 < 225 := by
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hq : (27 / 10 : ℝ) * Real.pi / Real.log 2 < (225 / 64) ^ 2 := by
    apply (div_lt_iff₀ hlog).mpr
    nlinarith [Real.pi_lt_d4, Real.log_two_gt_d9]
  have hroot := (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 225 / 64)).mpr hq
  unfold pinnedRatioConstant
  linarith

theorem pinnedRatioConstant_constant_lt : pinnedRatioConstant 640 < 2250 := by
  have h := pinnedRatioConstant_polynomial_lt
  unfold pinnedRatioConstant at *
  linarith

theorem smoothingParameter_antitone_error_of_exists
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {L : Submodule ℤ E} {ε ε' : ℝ} (hexists : ∃ t, SmoothAt L ε t) (hε : ε ≤ ε') :
    smoothingParameter L ε' ≤ smoothingParameter L ε := by
  apply csInf_le_csInf (show BddBelow {t : ℝ | SmoothAt L ε' t} from ⟨0, fun _ ht => ht.1.le⟩)
    hexists
  intro t ht
  exact SmoothAt.mono_error ht hε

end GeometricGaussianLHL
end

end PinnedNumerics

section PolynomialFamily

/-!
## An explicit threshold for the polynomial-width family

Above this fixed threshold, the real accuracy parameter gives the paper's
ceiling-defined row and column counts, the required coefficient width,
the complete finite-theorem column budget, and a square-root smoothing
scale. The threshold depends only on the fixed field constants and `p`.
-/

noncomputable section

set_option maxHeartbeats 800000

namespace GeometricGaussianLHL

def polynomialFamilyThreshold (d : ℕ) (κ μ p : ℝ) : ℝ :=
  let c := polynomialFamilyColumnCoefficient p
  max (d : ℝ) (max 25 (max (Real.log (2 * (c + 1)) ^ 2)
    (4 * (512 * κ ^ 2 * μ ^ 2) * (c + 1) * d)))

theorem polynomialFamily_parameters {d : ℕ} (hd : 0 < d)
    {α κ μ p ell : ℝ} (hα : 0 < α) (hκ : 1 ≤ κ) (hμ : 1 ≤ μ) (hp : 1 / 2 ≤ p)
    (hell : polynomialFamilyThreshold d κ μ p ≤ ell) :
    let r := polynomialFamilyRows d ell
    let R := r * d
    let m := polynomialFamilyColumns (polynomialFamilyColumnCoefficient p) R
    let s := 8 * α * (R : ℝ) ^ p
    let H := polynomialColumnHeight R m ell
    1 ≤ ell ∧ 1 ≤ r ∧ r < m ∧ 0 < s ∧
      8 * Real.sqrt R ≤ s / α ∧
      (R : ℝ) * Real.log (polynomialMatrixScale R (m * d) (s / α) κ μ H) +
          2 * Real.log (1 / realSecurityError (ell + 4)) ≤ (m : ℝ) * Real.log (8 / 7) ∧
      α * polynomialThetaWidth κ μ H ≤ (64 * α * κ * μ * Real.sqrt 8) * Real.sqrt ell := by
  let c := polynomialFamilyColumnCoefficient p
  let A := 512 * κ ^ 2 * μ ^ 2
  let C := 4 * A * (c + 1) * d
  have hc : 0 < c := polynomialFamilyColumnCoefficient_pos hp
  have hA : 0 < A := by dsimp [A]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  change max (d : ℝ) (max 25 (max (Real.log (2 * (c + 1)) ^ 2) C)) ≤ ell at hell
  rcases (max_le_iff.mp hell) with ⟨hdell, hrest⟩
  rcases (max_le_iff.mp hrest) with ⟨h25, hrest⟩
  rcases (max_le_iff.mp hrest) with ⟨hlogc, hCell⟩
  let r := polynomialFamilyRows d ell
  let R := r * d
  let m := polynomialFamilyColumns c R
  let s := 8 * α * (R : ℝ) ^ p
  let H := polynomialColumnHeight R m ell
  change 1 ≤ ell ∧ 1 ≤ r ∧ r < m ∧ 0 < s ∧ _
  have hell1 : 1 ≤ ell := by linarith
  have hr : 0 < r := by
    apply Nat.ceil_pos.mpr
    exact div_pos (by linarith) (by exact_mod_cast hd)
  have hRbounds := polynomialFamily_rank_bounds hd (show 0 ≤ ell by linarith)
  change ell ≤ (R : ℝ) ∧ (R : ℝ) < ell + d at hRbounds
  have hR1 : (1 : ℝ) ≤ R := hell1.trans hRbounds.1
  have hRpos : (0 : ℝ) < R := by linarith
  have hRtwo : (R : ℝ) ≤ 2 * ell := by linarith [hRbounds.2]
  have hrR : r ≤ R := by dsimp [R]; nlinarith
  have hRm : R < m := by
    have h := polynomialFamilyColumns_gt hp hR1
    exact_mod_cast h
  have hmr : r < m := hrR.trans_lt hRm
  have hm : 0 < m := hr.trans hmr
  have hs : 0 < s := by dsimp [s]; positivity
  have hsdiv : s / α = 8 * (R : ℝ) ^ p := by dsimp [s]; field_simp
  have hwidth : 8 * Real.sqrt R ≤ s / α := by
    have h := Real.rpow_le_rpow_of_exponent_le hR1 hp
    rw [← Real.sqrt_eq_rpow] at h
    rw [hsdiv]
    linarith
  have hlog : Real.log (2 * (m : ℝ)) ≤ R := polynomialFamilyColumns_log_le hc
    (h25.trans hRbounds.1) (hlogc.trans hRbounds.1)
  have hHupper : H ≤ 4 * R := polynomialFamily_height_le hm (by linarith) hRbounds.1 hlog
  have hHlower : (R : ℝ) ≤ H := polynomialColumnHeight_ge_rank hm hell1
  have hHpos : 0 < H := hRpos.trans_le hHlower
  have hmupper : (m : ℝ) ≤ (c + 1) * (R : ℝ) ^ 2 := polynomialFamilyColumns_upper hc.le hR1
  have hWeq : polynomialMatrixScale R (m * d) (s / α) κ μ H =
      A * (R : ℝ) ^ p * H * Real.sqrt ((m : ℝ) / r) :=
    polynomialFamily_matrix_scale_eq hr hd hα.ne' hHpos.le
  have hWpos : 0 < polynomialMatrixScale R (m * d) (s / α) κ μ H := by
    rw [hWeq]
    positivity
  have hWupper : polynomialMatrixScale R (m * d) (s / α) κ μ H ≤ C * (R : ℝ) ^ (p + 2) := by
    rw [hWeq]
    exact polynomialFamily_scale_le hr hd hc hA.le hHupper hmupper
  have hbudget := polynomialFamily_log_budget hp (show 16 ≤ (R : ℝ) by linarith [hRbounds.1])
    hRbounds.1 hWpos hC (hCell.trans hRbounds.1) hWupper
  have hH8 : H ≤ 8 * ell := by linarith
  have hroot := Real.sqrt_le_sqrt hH8
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 8)] at hroot
  have ht := mul_le_mul_of_nonneg_left hroot (show 0 ≤ 64 * α * κ * μ by positivity)
  refine ⟨hell1, hr, hmr, hs, hwidth, hbudget, ?_⟩
  change α * (64 * κ * μ * Real.sqrt H) ≤ (64 * α * κ * μ * Real.sqrt 8) * Real.sqrt ell
  calc
    _ = 64 * α * κ * μ * Real.sqrt H := by ring
    _ ≤ 64 * α * κ * μ * (Real.sqrt 8 * Real.sqrt ell) := ht
    _ = _ := by ring

end GeometricGaussianLHL
end

end PolynomialFamily

section PolynomialMatrix

/-!
## The finite polynomial-width matrix certificate

This is the coefficient-matrix form of the finite geometric smoothing theorem. It samples the actual
independent ellipsoidal Gaussian PMF, builds the integer block matrix, and proves integer
surjectivity, intrinsic-dual smoothing, and column bounds outside the stated failure budget. All
analytic and probabilistic estimates are proved dependencies. The number-field coordinate
identification is a separate remaining part of the complete paper certificate.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace GeometricGaussianLHL

def coefficientGoodEvent {R d m : ℕ} (T : Fin d → Matrix (Fin R) (Fin R) ℤ)
    (U t δ : ℝ) : Set (Fin m → Coeff R) :=
  {X | Function.Surjective (coefficientMap (blockCoefficientMatrix T X)) ∧
    SmoothAt (euclideanKernel (blockCoefficientMatrix T X)) (2 * δ) t ∧ X ∈ columnNormEvent U}

/-- The coefficient version of the finite geometric smoothing theorem, with the paper's failure
budget. -/
theorem polynomial_matrix_failure {R d m : ℕ} {ell : ℝ}
    (hR : 1 ≤ R) (hm : 1 ≤ m) (hell : 1 ≤ ell) (hdR : d ≤ R)
    (S : Euclidean R ≃L[ℝ] Euclidean R) {s₀ κ μ : ℝ}
    (hκ : 1 ≤ κ) (hμ : 1 ≤ μ) (hs₀ : 8 * Real.sqrt R ≤ s₀)
    (hlower : ‖S.symm.toContinuousLinearMap‖ ≤ 1 / s₀)
    (hupper : ‖S.toContinuousLinearMap‖ ≤ κ * s₀)
    (T : Fin d → Matrix (Fin R) (Fin R) ℤ) (i : Fin d) (hidentity : T i = 1)
    (hT : ∀ k, ∀ x : Euclidean R, ‖realCoefficientMap (T k) x‖ ≤ μ * ‖x‖)
    (hbudget : (R : ℝ) * Real.log (polynomialMatrixScale R (m * d) s₀ κ μ (polynomialColumnHeight R m ell)) +
      2 * Real.log (1 / realSecurityError (ell + 4)) ≤ (m : ℝ) * Real.log (8 / 7)) :
    let H := polynomialColumnHeight R m ell
    let t := polynomialThetaWidth κ μ H
    let U := polynomialColumnThreshold s₀ κ H
    (ellipsoidalColumnLaw m S).toMeasure (coefficientGoodEvent T U t (realSecurityError (ell + 4)))ᶜ ≤
      ENNReal.ofReal (3 * realSecurityError (ell + 4)) := by
  dsimp only
  let H := polynomialColumnHeight R m ell
  let t := polynomialThetaWidth κ μ H
  let U := polynomialColumnThreshold s₀ κ H
  let δ := realSecurityError (ell + 4)
  let W := polynomialMatrixScale R (m * d) s₀ κ μ H
  let P := ellipsoidalColumnLaw m S
  let G : Set (Fin m → Coeff R) := columnNormEvent U
  let F : Set (Fin m → Coeff R) := {X | sampledSpan ⊥ X ≠ ⊤}
  let E : Set (Fin m → Coeff R) := {X | δ < thetaRemainder (blockCoefficientMatrix T X) (μ * U) t}
  have hd : 1 ≤ d := by have hi := i.isLt; omega
  have hM : 1 ≤ m * d := by nlinarith
  have hMR : m * d ≤ R * m := by simpa [Nat.mul_comm] using Nat.mul_le_mul_left m hdR
  have hδpos : 0 < δ := realSecurityError_pos _
  have hδsmall : δ ≤ 1 / 32 := real_polynomial_failureBudget_le hell
  have hparams := polynomialWidth_parameters hR hκ hμ
    (polynomialColumnHeight_ge_rank (ell := ell) hm hell) hs₀
  have hspos : 0 < s₀ := hparams.1
  have ht : 1 ≤ t := by have hh := hparams.2.2.1; change 8 ≤ t at hh; linarith
  have hμ0 : 0 ≤ μ := by linarith
  have hB : 1 ≤ μ * U := (polynomialMatrixScale_lower hR hM hκ hμ
    (polynomialColumnHeight_ge_rank (ell := ell) hm hell) hs₀).1
  have hW : 3 ≤ W := (polynomialMatrixScale_lower hR hM hκ hμ
    (polynomialColumnHeight_ge_rank (ell := ell) hm hell) hs₀).2
  have hmain : 3 * (m * d : ℕ) * Real.exp (-Real.pi * t ^ 2 / 2) ≤ δ / 2 :=
    polynomialWidth_mainTerm_small hR hm hell (by omega) hMR hκ hμ
  have hgood : ∀ X, X ∈ G → X ∉ F → X ∉ E → X ∈ coefficientGoodEvent T U t δ := by
    intro X hG hF hE
    have hspan : Submodule.span ℝ (Set.range (fun j => integerEmbedding R (X j))) = ⊤ := by
      have hspan : sampledSpan ⊥ X = ⊤ := by simpa only [F, Set.mem_setOf_eq, not_not] using hF
      simpa only [sampledSpan, bot_sup_eq] using hspan
    have hfull := blockCoefficientMatrix_fullRank_of_span T X i hidentity hspan
    have hcol := blockCoefficientMatrix_column_norm T X hμ0 hT hG
    have hrem : thetaRemainder (blockCoefficientMatrix T X) (μ * U) t ≤ δ := le_of_not_gt hE
    have h := surjective_and_smoothAt_of_remainder_bound (blockCoefficientMatrix T X) hfull hB ht hcol
      hδpos.le (by linarith) hmain hrem
    exact ⟨h.1, h.2, hG⟩
  have hbad : (coefficientGoodEvent T U t δ)ᶜ ⊆ (Gᶜ ∪ F) ∪ (G ∩ E) := by
    intro X hX
    by_cases hG : X ∈ G
    · by_cases hF : X ∈ F
      · exact Or.inl (Or.inr hF)
      · by_cases hE : X ∈ E
        · exact Or.inr ⟨hG, hE⟩
        · exact False.elim (hX (hgood X hG hF hE))
    · exact Or.inl (Or.inl hG)
  have hnorm : P.toMeasure Gᶜ ≤ ENNReal.ofReal (δ / 2) := by
    exact polynomialWidth_columnNorm_failure hR hm hell S
      (mul_pos (by linarith) hspos) hupper
  have hrank : P.toMeasure F ≤ ENNReal.ofReal (δ ^ 2) :=
    polynomialWidth_rank_failure hR S hs₀ hlower hW hδpos hbudget
  have hrem : P.toMeasure (G ∩ E) ≤ ENNReal.ofReal δ :=
    polynomialWidth_remainder_failure hR hm hell hdR S hκ hμ hs₀ hlower T i hidentity hT hbudget
  change P.toMeasure (coefficientGoodEvent T U t δ)ᶜ ≤ _
  calc
    _ ≤ P.toMeasure ((Gᶜ ∪ F) ∪ (G ∩ E)) := measure_mono hbad
    _ ≤ (P.toMeasure Gᶜ + P.toMeasure F) + P.toMeasure (G ∩ E) :=
      (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    _ ≤ (ENNReal.ofReal (δ / 2) + ENNReal.ofReal (δ ^ 2)) + ENNReal.ofReal δ := by gcongr
    _ = ENNReal.ofReal (δ / 2 + δ ^ 2 + δ) := by
      rw [ENNReal.ofReal_add (by positivity) hδpos.le,
        ENNReal.ofReal_add (by positivity) (sq_nonneg δ)]
    _ ≤ ENNReal.ofReal (3 * δ) := by
      apply ENNReal.ofReal_le_ofReal
      nlinarith [mul_nonneg hδpos.le (show 0 ≤ 1 - δ by linarith)]

theorem pmf_good_probability_of_compl_bound {α : Type*} [Countable α]
    [MeasurableSpace α] [MeasurableSingletonClass α] (p : PMF α) (A : Set α)
    {ε : ℝ} (hε : 0 ≤ ε) (hbad : p.toMeasure Aᶜ ≤ ENNReal.ofReal ε) :
    ENNReal.ofReal (1 - ε) ≤ p.toMeasure A := by
  have hc := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbad
  rw [ENNReal.toReal_ofReal hε] at hc
  have he := measureReal_add_measureReal_compl (μ := p.toMeasure) (Set.to_countable A).measurableSet
  rw [probReal_univ] at he
  apply (ENNReal.ofReal_le_iff_le_toReal (by finiteness)).mpr
  change p.toMeasure.real Aᶜ ≤ ε at hc
  change 1 - ε ≤ p.toMeasure.real A
  linarith

/-- On the same event, every positive error parameter has the extended
smoothing estimate. -/
theorem coefficientGoodEvent_smoothing {R d m : ℕ}
    (T : Fin d → Matrix (Fin R) (Fin R) ℤ) {U t δ : ℝ} (hδ : 0 < δ) (hδsmall : 2 * δ < 1)
    (X : Fin m → Coeff R) (hX : X ∈ coefficientGoodEvent T U t δ) :
    ∀ ε : ℝ, 0 < ε →
      smoothingParameter (euclideanKernel (blockCoefficientMatrix T X)) ε ≤
        t * Real.sqrt (errorExponent (2 * δ) ε) := by
  intro ε hε
  exact smoothingParameter_le_of_smoothAt (hX.2.1.error_extension (by positivity) hδsmall hε)

end GeometricGaussianLHL
end

end PolynomialMatrix

section PolynomialCertificate

/-!
## Polynomial-width certificate under a change of metric

The same event supplies integer surjectivity, the actual intrinsic-dual mass
bound, column norms, and smoothing in any prescribed linear image metric.
The sampling law is the independent ellipsoidal Gaussian law. The actual
number-field identification is supplied in the `NumberFieldPolynomial` section.
-/

noncomputable section

open scoped ENNReal

namespace GeometricGaussianLHL

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

theorem coefficientGoodEvent_metric_bounds {R d m : ℕ}
    (T : Fin d → Matrix (Fin R) (Fin R) ℤ) {U t δ α : ℝ}
    (hδ : 0 < δ) (hδsmall : 2 * δ < 1)
    (C : Euclidean (m * d) →L[ℝ] F) (hC : ‖C‖ ≤ α)
    (X : Fin m → Coeff R) (hX : X ∈ coefficientGoodEvent T U t δ) :
    smoothingParameter (latticeImage C (euclideanKernel (blockCoefficientMatrix T X))) (2 * δ) ≤ α * t ∧
      ∀ ε : ℝ, 0 < ε →
        smoothingParameter (latticeImage C (euclideanKernel (blockCoefficientMatrix T X))) ε ≤
          (α * t) * Real.sqrt (errorExponent (2 * δ) ε) := by
  let L := euclideanKernel (blockCoefficientMatrix T X)
  let : DiscreteTopology L := integerEmbedding_map_discreteTopology
    (coefficientKernel (blockCoefficientMatrix T X))
  have ht : 0 < t := hX.2.1.1
  constructor
  · calc
      _ ≤ ‖C‖ * smoothingParameter L (2 * δ) :=
        smoothingParameter_metric_change_of_discrete C L (by positivity)
      _ ≤ ‖C‖ * t := mul_le_mul_of_nonneg_left
        (smoothingParameter_le_of_smoothAt hX.2.1) (norm_nonneg C)
      _ ≤ α * t := mul_le_mul_of_nonneg_right hC ht.le
  · intro ε hε
    calc
      _ ≤ ‖C‖ * smoothingParameter L ε := smoothingParameter_metric_change_of_discrete C L hε
      _ ≤ ‖C‖ * (t * Real.sqrt (errorExponent (2 * δ) ε)) :=
        mul_le_mul_of_nonneg_left (coefficientGoodEvent_smoothing T hδ hδsmall X hX ε hε)
          (norm_nonneg C)
      _ ≤ α * (t * Real.sqrt (errorExponent (2 * δ) ε)) :=
        mul_le_mul_of_nonneg_right hC (mul_nonneg ht.le (Real.sqrt_nonneg _))
      _ = _ := (mul_assoc _ _ _).symm

/-- The finite geometric smoothing theorem in coefficient coordinates, including the common event,
metric transport, and simultaneous bounds for every positive error.
-/
theorem polynomial_matrix_certificate {R d m : ℕ} {ell : ℝ}
    (hR : 1 ≤ R) (hm : 1 ≤ m) (hell : 1 ≤ ell) (hdR : d ≤ R)
    (S : Euclidean R ≃L[ℝ] Euclidean R) {s₀ κ μ α : ℝ}
    (hκ : 1 ≤ κ) (hμ : 1 ≤ μ) (hs₀ : 8 * Real.sqrt R ≤ s₀)
    (hlower : ‖S.symm.toContinuousLinearMap‖ ≤ 1 / s₀)
    (hupper : ‖S.toContinuousLinearMap‖ ≤ κ * s₀)
    (T : Fin d → Matrix (Fin R) (Fin R) ℤ) (i : Fin d) (hidentity : T i = 1)
    (hT : ∀ k, ∀ x : Euclidean R, ‖realCoefficientMap (T k) x‖ ≤ μ * ‖x‖)
    (C : Euclidean (m * d) →L[ℝ] F) (hC : ‖C‖ ≤ α)
    (hbudget : (R : ℝ) * Real.log (polynomialMatrixScale R (m * d) s₀ κ μ (polynomialColumnHeight R m ell)) +
      2 * Real.log (1 / realSecurityError (ell + 4)) ≤ (m : ℝ) * Real.log (8 / 7)) :
    let H := polynomialColumnHeight R m ell
    let t := polynomialThetaWidth κ μ H
    let U := polynomialColumnThreshold s₀ κ H
    let δ := realSecurityError (ell + 4)
    ∃ G : Set (Fin m → Coeff R),
      ENNReal.ofReal (1 - 3 * δ) ≤ (ellipsoidalColumnLaw m S).toMeasure G ∧
      ∀ X ∈ G,
        Function.Surjective (coefficientMap (blockCoefficientMatrix T X)) ∧
        nonzeroDualMass (euclideanKernel (blockCoefficientMatrix T X)) t ≤ ENNReal.ofReal (2 * δ) ∧
        smoothingParameter (latticeImage C (euclideanKernel (blockCoefficientMatrix T X))) (2 * δ) ≤ α * t ∧
        (∀ j, ‖integerEmbedding R (X j)‖ ≤ U) ∧
        ∀ ε : ℝ, 0 < ε →
          smoothingParameter (latticeImage C (euclideanKernel (blockCoefficientMatrix T X))) ε ≤
            (α * t) * Real.sqrt (errorExponent (2 * δ) ε) := by
  dsimp only
  let H := polynomialColumnHeight R m ell
  let t := polynomialThetaWidth κ μ H
  let U := polynomialColumnThreshold s₀ κ H
  let δ := realSecurityError (ell + 4)
  have hδ : 0 < δ := realSecurityError_pos _
  have hδsmall : 2 * δ < 1 := by
    have h := real_polynomial_failureBudget_le hell
    change δ ≤ 1 / 32 at h
    linarith
  refine ⟨coefficientGoodEvent T U t δ, ?_, ?_⟩
  · exact pmf_good_probability_of_compl_bound _ _ (by positivity)
      (polynomial_matrix_failure hR hm hell hdR S hκ hμ hs₀ hlower hupper T i hidentity hT hbudget)
  · intro X hX
    have hmetric := coefficientGoodEvent_metric_bounds T hδ hδsmall C hC X hX
    exact ⟨hX.1, hX.2.1.2, hmetric.1, hX.2.2, hmetric.2⟩

end GeometricGaussianLHL
end

end PolynomialCertificate

section NumberFieldPolynomial

/-!
## The finite polynomial-width theorem over number fields

The finite geometric smoothing theorem for the actual ring-Gaussian matrix distribution,
integral-basis constants, coefficient kernel, and canonical t₂ kernel lattice. All three probability
estimates are supplied by proved dependencies. PMF outer measure expresses event probability on the
discrete sample space without imposing an auxiliary measurable-space structure on the abstract
number field.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Module NumberField MeasureTheory
open scoped ENNReal

namespace GeometricGaussianLHL

variable (K : Type*) [Field K] [NumberField K] {d r m : ℕ}

local instance polynomialEmbeddingsFintype : Fintype (K →+* ℂ) := inferInstance
local instance polynomialAmbientInner : InnerProductSpace ℝ (CanonicalAmbient K) := inferInstance
local instance polynomialSpaceInner : InnerProductSpace ℝ (canonicalSpace K) := inferInstance
local instance polynomialPowerInner (n : ℕ) : InnerProductSpace ℝ (CanonicalPower K n) := inferInstance

theorem numberField_polynomial_column_threshold (b : Basis (Fin d) ℤ (𝓞 K)) (s H : ℝ) :
    polynomialColumnThreshold (s / basisAlpha K b) (basisKappa K b) H =
      s * basisBeta K b * Real.sqrt H := by
  have hα := (basisAlpha_pos K b).ne'
  unfold polynomialColumnThreshold basisKappa
  field_simp

def numberFieldPolynomialScale (b : Basis (Fin d) ℤ (𝓞 K)) (r m : ℕ) (s ell : ℝ) : ℝ :=
  let H := polynomialColumnHeight (r * d) m ell
  polynomialThetaWidth (basisKappa K b) (basisMu K b) H * basisMu K b *
    (s * basisBeta K b * Real.sqrt H) * Real.sqrt (((m * d : ℕ) : ℝ) / (r * d))

theorem numberFieldPolynomialScale_eq (b : Basis (Fin d) ℤ (𝓞 K)) (r m : ℕ) (s ell : ℝ) :
    polynomialMatrixScale (r * d) (m * d) (s / basisAlpha K b) (basisKappa K b) (basisMu K b)
      (polynomialColumnHeight (r * d) m ell) = numberFieldPolynomialScale K b r m s ell := by
  unfold polynomialMatrixScale numberFieldPolynomialScale
  rw [numberField_polynomial_column_threshold]
  push_cast
  ring

set_option maxHeartbeats 800000 in
/-- The finite geometric smoothing theorem, including its common event for
all positive smoothing errors, for every real accuracy parameter `ell ≥ 1`. -/
theorem numberField_polynomial_certificate (b : Basis (Fin d) ℤ (𝓞 K))
    (i : Fin d) (hidentity : b i = 1) (hr : 1 ≤ r) (hmr : r < m)
    {ell s : ℝ} (hell : 1 ≤ ell) (hs : 0 < s)
    (hwidth : 8 * Real.sqrt (r * d) ≤ s / basisAlpha K b)
    (hbudget : ((r * d : ℕ) : ℝ) * Real.log (numberFieldPolynomialScale K b r m s ell) +
      2 * Real.log (1 / realSecurityError (ell + 4)) ≤ (m : ℝ) * Real.log (8 / 7)) :
    let H := polynomialColumnHeight (r * d) m ell
    let t := polynomialThetaWidth (basisKappa K b) (basisMu K b) H
    let U := s * basisBeta K b * Real.sqrt H
    let δ := realSecurityError (ell + 4)
    ∃ G : Set (Matrix (Fin r) (Fin m) (𝓞 K)),
      ENNReal.ofReal (1 - 3 * δ) ≤ (numberFieldMatrixLaw K b r m s hs.ne').toOuterMeasure G ∧
      ∀ X ∈ G,
        Function.Surjective X.mulVec ∧
        nonzeroDualMass (euclideanKernel (ringCoefficientMatrix b X)) t ≤ ENNReal.ofReal (2 * δ) ∧
        smoothingParameter (canonicalKernel K X) (2 * δ) ≤ basisAlpha K b * t ∧
        (∀ j, ‖integerEmbedding (r * d) (ringPowerCoordinates b r (fun k => X k j))‖ ≤ U) ∧
        ∀ ε : ℝ, 0 < ε → smoothingParameter (canonicalKernel K X) ε ≤
          (basisAlpha K b * t) * Real.sqrt (errorExponent (2 * δ) ε) := by
  dsimp only
  let H := polynomialColumnHeight (r * d) m ell
  let t := polynomialThetaWidth (basisKappa K b) (basisMu K b) H
  let δ := realSecurityError (ell + 4)
  let S := numberFieldGaussianShape K b r s hs.ne'
  let T := fun k : Fin d => ringPowerMultiplicationMatrix b r (b k)
  let E := matrixColumnCoordinates K b r m
  have hd : 1 ≤ d := integralBasis_dimension_pos K b
  have hR : 1 ≤ r * d := by nlinarith
  have hm : 1 ≤ m := by omega
  have hdR : d ≤ r * d := by nlinarith
  have hα := basisAlpha_pos K b
  have hκ := basisKappa_ge_one K b
  have hμ := basisMu_ge_one K b i hidentity
  have hlower : ‖S.symm.toContinuousLinearMap‖ ≤ 1 / (s / basisAlpha K b) := by
    have h := numberFieldGaussianShape_symm_norm_le K b r hs
    have he : basisAlpha K b / s = 1 / (s / basisAlpha K b) := by field_simp
    exact h.trans_eq he
  have hupper : ‖S.toContinuousLinearMap‖ ≤ basisKappa K b * (s / basisAlpha K b) := by
    have h := numberFieldGaussianShape_norm_le K b r hs
    have he : s * basisBeta K b = basisKappa K b * (s / basisAlpha K b) := by
      unfold basisKappa
      field_simp
    exact h.trans_eq he
  have hTidentity : T i = 1 := by simp only [T, hidentity, ringPowerMultiplicationMatrix_one]
  have hT : ∀ k, ∀ x : Euclidean (r * d), ‖realCoefficientMap (T k) x‖ ≤ basisMu K b * ‖x‖ :=
    basisPowerMultiplication_norm_le_mu K b r
  have hbudget' : ((r * d : ℕ) : ℝ) * Real.log
      (polynomialMatrixScale (r * d) (m * d) (s / basisAlpha K b) (basisKappa K b) (basisMu K b) H) +
      2 * Real.log (1 / δ) ≤ (m : ℝ) * Real.log (8 / 7) := by
    simpa only [H, δ, numberFieldPolynomialScale_eq] using hbudget
  obtain ⟨Gc, hprob, hgood⟩ := polynomial_matrix_certificate (F := CanonicalPower K m) hR hm hell hdR S hκ hμ
    (by simpa only [Nat.cast_mul] using hwidth)
    hlower hupper T i hTidentity hT (powerCanonicalEquiv K b m).toContinuousLinearMap
    (powerCanonicalEquiv_norm_le K b m) hbudget'
  refine ⟨E ⁻¹' Gc, ?_, ?_⟩
  · rw [PMF.toMeasure_apply_eq_toOuterMeasure_apply _ (Set.to_countable Gc).measurableSet] at hprob
    rw [← numberFieldMatrixLaw_coordinate_law K b r m s hs.ne', PMF.toOuterMeasure_map_apply] at hprob
    exact hprob
  · intro X hX
    obtain ⟨himage, hmass, hsmooth, hcols, hall⟩ := hgood (E X) hX
    have hblock : blockCoefficientMatrix T (E X) = ringCoefficientMatrix b X :=
      (ringCoefficientMatrix_eq_block b X).symm
    rw [hblock] at himage hmass hsmooth hall
    rw [← canonicalKernel_eq_image K b X] at hsmooth hall
    refine ⟨(ringCoefficientMatrix_surjective_iff b X).mp himage, hmass, hsmooth, ?_, hall⟩
    simpa only [E, matrixColumnCoordinates_apply, numberField_polynomial_column_threshold] using hcols

end GeometricGaussianLHL
end

end NumberFieldPolynomial

section DualMinimumPinned

/-!
## The pinned dual coefficient minimum

On the same geometric event, the first dual minimum lies between
`1 / (224 κ μ)` and `1`. The numerical constant is checked directly, and the
upper bound comes from the projected standard basis vector.
-/
noncomputable section
open Module NumberField
namespace GeometricGaussianLHL

theorem coefficientDual_firstMinimum_bounds {R M : ℕ} (A : Matrix (Fin R) (Fin M) ℤ)
    (hRM : R < M) {ε t : ℝ} (hε : 0 < ε) (ht : SmoothAt (euclideanKernel A) ε t) :
    Real.sqrt (Real.log (2 / ε) / Real.pi) / t ≤ firstMinimum (latticeDual (euclideanKernel A)) ∧
      firstMinimum (latticeDual (euclideanKernel A)) ≤ 1 := by
  let : DiscreteTopology (euclideanKernel A) := integerEmbedding_map_discreteTopology _
  obtain ⟨v, hv, hv0, hvnorm⟩ := exists_short_coefficientKernel_dual A hRM
  have hD : latticeDual (euclideanKernel A) ≠ ⊥ := by
    intro h
    exact hv0 (by simpa [h] using hv)
  have hL : euclideanKernel A ≠ ⊥ := by
    intro h
    have hs := euclideanKernel_span_ne_bot A hRM
    exact hs (by simp [h])
  have hp := firstMinimum_pos (latticeDual (euclideanKernel A)) hD
  have hlo := (smoothingParameter_lower_firstMinimum (euclideanKernel A) hL hε).trans
    (smoothingParameter_le_of_smoothAt ht)
  refine ⟨(div_le_iff₀ ht.1).mpr ?_, (firstMinimum_le_norm _ hv hv0).trans hvnorm⟩
  have h := (div_le_iff₀ hp).mp hlo
  simpa only [mul_comm] using h

theorem polynomialDualMinimum_numerical_lower {κ μ H L ell : ℝ}
    (hκ : 0 < κ) (hμ : 0 < μ) (hH : 0 < H) (hell : 0 ≤ ell)
    (hheight : H ≤ (27 / 10) * ell) (hlog : ell * Real.log 2 ≤ L) :
    1 / (224 * κ * μ) ≤ Real.sqrt (L / Real.pi) / (64 * κ * μ * Real.sqrt H) := by
  have hnum : (2 / 7 : ℝ) ^ 2 * (27 / 10) * Real.pi ≤ Real.log 2 := by
    nlinarith [Real.pi_lt_d4, Real.log_two_gt_d9]
  have hsquare : (2 / 7 : ℝ) ^ 2 * H ≤ L / Real.pi := by
    apply (le_div_iff₀ Real.pi_pos).mpr
    calc
      _ ≤ ((2 / 7 : ℝ) ^ 2 * (27 / 10) * Real.pi) * ell := by
        nlinarith [mul_le_mul_of_nonneg_left hheight (show 0 ≤ (2 / 7 : ℝ) ^ 2 * Real.pi by positivity)]
      _ ≤ Real.log 2 * ell := mul_le_mul_of_nonneg_right hnum hell
      _ ≤ L := by simpa only [mul_comm] using hlog
  have hroot := Real.sqrt_le_sqrt hsquare
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by norm_num)] at hroot
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hmul := mul_le_mul_of_nonneg_left hroot (show 0 ≤ 224 * κ * μ by positivity)
  convert hmul using 1 <;> ring

theorem coefficientDual_firstMinimum_pinned {R M : ℕ} (A : Matrix (Fin R) (Fin M) ℤ)
    (hRM : R < M) {κ μ H ell : ℝ} (hκ : 0 < κ) (hμ : 0 < μ) (hH : 0 < H)
    (hell : 0 ≤ ell) (hheight : H ≤ (27 / 10) * ell)
    (hmass : nonzeroDualMass (euclideanKernel A) (64 * κ * μ * Real.sqrt H) ≤
      ENNReal.ofReal (2 * realSecurityError (ell + 4))) :
    1 / (224 * κ * μ) ≤ firstMinimum (latticeDual (euclideanKernel A)) ∧
      firstMinimum (latticeDual (euclideanKernel A)) ≤ 1 := by
  have hδ := realSecurityError_pos (ell + 4)
  have hb := coefficientDual_firstMinimum_bounds A hRM (by positivity : 0 < 2 * realSecurityError (ell + 4))
    (show SmoothAt (euclideanKernel A) (2 * realSecurityError (ell + 4)) (64 * κ * μ * Real.sqrt H) from
      ⟨by positivity, hmass⟩)
  have hlog : Real.log (2 / (2 * realSecurityError (ell + 4))) = (ell + 4) * Real.log 2 := by
    rw [show (2 : ℝ) / (2 * realSecurityError (ell + 4)) = 1 / realSecurityError (ell + 4) by field_simp,
      log_inv_realSecurityError]
  refine ⟨(polynomialDualMinimum_numerical_lower hκ hμ hH hell hheight ?_).trans hb.1, hb.2⟩
  rw [hlog]
  nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]

theorem numberField_polynomial_dual_minimum_pinned (K : Type*) [Field K] [NumberField K]
    {d r m : ℕ} (b : Basis (Fin d) ℤ (𝓞 K)) (i : Fin d) (hidentity : b i = 1)
    (hr : 1 ≤ r) (hmr : r < m) {ell s : ℝ} (hell : 28 ≤ ell) (hs : 0 < s)
    (hwidth : 8 * Real.sqrt (r * d) ≤ s / basisAlpha K b)
    (hbudget : ((r * d : ℕ) : ℝ) * Real.log (numberFieldPolynomialScale K b r m s ell) +
      2 * Real.log (1 / realSecurityError (ell + 4)) ≤ (m : ℝ) * Real.log (8 / 7))
    (hR : ((r * d : ℕ) : ℝ) = ell) (hsize : Real.log (2 * m) ≤ ell / 10) :
    ∃ G : Set (Matrix (Fin r) (Fin m) (𝓞 K)),
      ENNReal.ofReal (1 - 3 * realSecurityError (ell + 4)) ≤ (numberFieldMatrixLaw K b r m s hs.ne').toOuterMeasure G ∧
      ∀ X ∈ G,
        1 / (224 * basisKappa K b * basisMu K b) ≤ firstMinimum (latticeDual (euclideanKernel (ringCoefficientMatrix b X))) ∧
        firstMinimum (latticeDual (euclideanKernel (ringCoefficientMatrix b X))) ≤ 1 := by
  have hd := integralBasis_dimension_pos K b
  have hm : 1 ≤ m := by omega
  have hheight : polynomialColumnHeight (r * d) m ell ≤ (27 / 10) * ell :=
    pinned_security_height_le hm hell (by norm_num : (4 : ℝ) ≤ 6) hR hsize
  have hH : 0 < polynomialColumnHeight (r * d) m ell :=
    lt_of_lt_of_le (by exact_mod_cast Nat.mul_pos hr hd) (polynomialColumnHeight_ge_rank hm (by linarith))
  obtain ⟨G, hprob, hgood⟩ := numberField_polynomial_certificate K b i hidentity hr hmr (by linarith) hs hwidth hbudget
  refine ⟨G, hprob, fun X hX => ?_⟩
  exact coefficientDual_firstMinimum_pinned (ringCoefficientMatrix b X) (Nat.mul_lt_mul_of_pos_right hmr hd)
    (lt_of_lt_of_le (by norm_num) (basisKappa_ge_one K b))
    (lt_of_lt_of_le (by norm_num) (basisMu_ge_one K b i hidentity)) hH (by linarith) hheight (hgood X hX).2.1

end GeometricGaussianLHL
end

end DualMinimumPinned

section NumberFieldAsymptotic

/-!
## Polynomial width and growing rank over a fixed number field

The fixed-field polynomial-width theorem for the actual number-field Gaussian matrix law and
canonical kernel. The explicit constants and threshold are independent of the real accuracy
parameter. Surjectivity and both smoothing bounds hold on the same event supplied by the
already-proved finite theorem.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Module NumberField MeasureTheory
open scoped ENNReal

namespace GeometricGaussianLHL

theorem errorExponent_eq_one_of_le {ε₀ ε : ℝ} (h₀ : 0 < ε₀) (h₁ : ε₀ < 1)
    (hle : ε₀ ≤ ε) : errorExponent ε₀ ε = 1 := by
  have hε : 0 < ε := h₀.trans_le hle
  have hlog : 0 < Real.log (1 / ε₀) := Real.log_pos ((lt_div_iff₀ h₀).mpr (by simpa))
  unfold errorExponent
  apply max_eq_left
  apply (div_le_iff₀ hlog).mpr
  rw [one_mul]
  exact Real.log_le_log (by positivity) (one_div_le_one_div_of_le h₀ hle)

theorem polynomial_errorExponent_eq_one {ell : ℝ} (hell : 1 ≤ ell) :
    errorExponent (2 * realSecurityError (ell + 4)) (realSecurityError ell) = 1 := by
  have hδ := real_polynomial_failureBudget_le hell
  have hδpos := realSecurityError_pos (ell + 4)
  have hpos := realSecurityError_pos ell
  apply errorExponent_eq_one_of_le (by positivity) (by linarith)
  rw [realSecurityError_add]
  norm_num
  linarith

variable (K : Type*) [Field K] [NumberField K] {d : ℕ}

local instance asymptoticEmbeddingsFintype : Fintype (K →+* ℂ) := inferInstance
local instance asymptoticAmbientInner : InnerProductSpace ℝ (CanonicalAmbient K) := inferInstance
local instance asymptoticSpaceInner : InnerProductSpace ℝ (canonicalSpace K) := inferInstance
local instance asymptoticPowerInner (n : ℕ) : InnerProductSpace ℝ (CanonicalPower K n) := inferInstance

/-- The fixed-field polynomial-width theorem, including the larger-error assertion, for every fixed
integral basis containing `1` as in the paper's global setup. -/
theorem numberField_polynomial_asymptotic (b : Basis (Fin d) ℤ (𝓞 K))
    (i : Fin d) (hidentity : b i = 1) {p : ℝ} (hp : 1 / 2 ≤ p) :
    ∃ cX cm C ell₀ : ℝ, 0 < cX ∧ 0 < cm ∧ 0 < C ∧
      ∀ ell : ℝ, ell₀ ≤ ell →
        let r := polynomialFamilyRows d ell
        let R := r * d
        let s := cX * (R : ℝ) ^ p
        let m := polynomialFamilyColumns cm R
        let δ := realSecurityError (ell + 4)
        r < m ∧ ∃ hs : 0 < s, ∃ G : Set (Matrix (Fin r) (Fin m) (𝓞 K)),
          ENNReal.ofReal (1 - 3 * δ) ≤ (numberFieldMatrixLaw K b r m s hs.ne').toOuterMeasure G ∧
          ∀ X ∈ G,
            Function.Surjective X.mulVec ∧
            smoothingParameter (canonicalKernel K X) (2 * δ) ≤ C * Real.sqrt ell ∧
            smoothingParameter (canonicalKernel K X) (realSecurityError ell) ≤ C * Real.sqrt ell := by
  let α := basisAlpha K b
  let κ := basisKappa K b
  let μ := basisMu K b
  have hα : 0 < α := basisAlpha_pos K b
  have hκ : 1 ≤ κ := basisKappa_ge_one K b
  have hμ : 1 ≤ μ := basisMu_ge_one K b i hidentity
  refine ⟨8 * α, polynomialFamilyColumnCoefficient p, 64 * α * κ * μ * Real.sqrt 8,
    polynomialFamilyThreshold d κ μ p, by positivity, polynomialFamilyColumnCoefficient_pos hp,
    by positivity, ?_⟩
  intro ell hell
  let r := polynomialFamilyRows d ell
  let R := r * d
  let m := polynomialFamilyColumns (polynomialFamilyColumnCoefficient p) R
  let s := 8 * α * (R : ℝ) ^ p
  obtain ⟨hell1, hr, hmr, hs, hwidth, hbudget, ht⟩ :=
    polynomialFamily_parameters (integralBasis_dimension_pos K b) hα hκ hμ hp hell
  have hb : ((r * d : ℕ) : ℝ) * Real.log (numberFieldPolynomialScale K b r m s ell) +
      2 * Real.log (1 / realSecurityError (ell + 4)) ≤ (m : ℝ) * Real.log (8 / 7) := by
    rw [← numberFieldPolynomialScale_eq]
    exact hbudget
  obtain ⟨G, hprob, hgood⟩ := numberField_polynomial_certificate K b i hidentity hr hmr hell1 hs
    (by simpa only [Nat.cast_mul] using hwidth) hb
  refine ⟨hmr, hs, G, hprob, ?_⟩
  intro X hX
  obtain ⟨himage, _, hsmooth, _, hall⟩ := hgood X hX
  have hlarge := hall (realSecurityError ell) (realSecurityError_pos ell)
  rw [polynomial_errorExponent_eq_one hell1, Real.sqrt_one, mul_one] at hlarge
  exact ⟨himage, hsmooth.trans ht, hlarge.trans ht⟩

end GeometricGaussianLHL
end

end NumberFieldAsymptotic

section PowerTwoPolynomial

/-!
## The finite power-of-two smoothing corollary

The power-of-two geometric smoothing corollary follows from the actual number-field theorem after
substituting the proved power-basis constants. The scale and width conditions are simplified to the
formulas printed in the paper.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Module NumberField
open scoped ENNReal

namespace GeometricGaussianLHL

def powerTwoPolynomialScale (d r m : ℕ) (s ell : ℝ) : ℝ :=
  64 * s * polynomialColumnHeight (r * d) m ell / Real.sqrt d * Real.sqrt ((m : ℝ) / r)

variable (K : Type*) [Field K] [NumberField K] {k : ℕ}
  [IsCyclotomicExtension {2 ^ (k + 1)} ℚ K] {ζ : K}

local instance powerTwoPolynomialEmbeddingsFintype : Fintype (K →+* ℂ) := inferInstance
local instance powerTwoPolynomialAmbientInner : InnerProductSpace ℝ (CanonicalAmbient K) := inferInstance
local instance powerTwoPolynomialSpaceInner : InnerProductSpace ℝ (canonicalSpace K) := inferInstance
local instance powerTwoPolynomialPowerInner (n : ℕ) : InnerProductSpace ℝ (CanonicalPower K n) := inferInstance

theorem numberFieldPolynomialScale_powerTwo (hζ : IsPrimitiveRoot ζ (2 ^ (k + 1)))
    {r m : ℕ} (hm : 1 ≤ m) (s : ℝ) {ell : ℝ} (hell : 1 ≤ ell) :
    numberFieldPolynomialScale K (cyclotomicIntegralBasis K hζ) r m s ell =
      powerTwoPolynomialScale (2 ^ (k + 1)).totient r m s ell := by
  let d := (2 ^ (k + 1)).totient
  let H := polynomialColumnHeight (r * d) m ell
  have hd : (d : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (pow_pos (by norm_num : 0 < (2 : ℕ)) (k + 1))).ne'
  have hH : 0 ≤ H := (show (0 : ℝ) ≤ r * d by positivity).trans (by
    exact_mod_cast polynomialColumnHeight_ge_rank hm hell (R := r * d))
  obtain ⟨hα, hβ, hκ, hμ⟩ := powerTwoBasis_constants K hζ
  unfold numberFieldPolynomialScale powerTwoPolynomialScale
  rw [hβ, hκ, hμ]
  unfold polynomialThetaWidth
  change 64 * 1 * 1 * Real.sqrt H * 1 * (s * (1 / Real.sqrt d) * Real.sqrt H) *
    Real.sqrt (((m * d : ℕ) : ℝ) / ((r : ℝ) * d)) =
      64 * s * H / Real.sqrt d * Real.sqrt ((m : ℝ) / r)
  rw [Nat.cast_mul, mul_div_mul_right _ _ hd]
  calc
    _ = 64 * s * (Real.sqrt H) ^ 2 / Real.sqrt d * Real.sqrt ((m : ℝ) / r) := by ring
    _ = _ := by rw [Real.sq_sqrt hH]

set_option maxHeartbeats 800000 in
/-- The power-of-two geometric smoothing corollary for every real accuracy parameter allowed by the
paper. -/
theorem powerTwo_polynomial_certificate (hζ : IsPrimitiveRoot ζ (2 ^ (k + 1)))
    {r m : ℕ} (hr : 1 ≤ r) (hmr : r < m) {ell s : ℝ} (hell : 1 ≤ ell) (hs : 0 < s)
    (hwidth : 8 * Real.sqrt ((2 ^ (k + 1)).totient * (r * (2 ^ (k + 1)).totient)) ≤ s)
    (hbudget : ((r * (2 ^ (k + 1)).totient : ℕ) : ℝ) *
      Real.log (powerTwoPolynomialScale (2 ^ (k + 1)).totient r m s ell) +
      2 * Real.log (1 / realSecurityError (ell + 4)) ≤ (m : ℝ) * Real.log (8 / 7)) :
    ∃ G : Set (Matrix (Fin r) (Fin m) (𝓞 K)),
      ENNReal.ofReal (1 - 3 * realSecurityError (ell + 4)) ≤
        (numberFieldMatrixLaw K (cyclotomicIntegralBasis K hζ) r m s hs.ne').toOuterMeasure G ∧
      ∀ X ∈ G, Function.Surjective X.mulVec ∧
        smoothingParameter (canonicalKernel K X) (2 * realSecurityError (ell + 4)) ≤
          64 * Real.sqrt ((2 ^ (k + 1)).totient *
            polynomialColumnHeight (r * (2 ^ (k + 1)).totient) m ell) := by
  let b := cyclotomicIntegralBasis K hζ
  let d := (2 ^ (k + 1)).totient
  have hm : 1 ≤ m := by omega
  have hd : (0 : ℝ) < d := by exact_mod_cast Nat.totient_pos.mpr (pow_pos (by norm_num : 0 < (2 : ℕ)) _)
  have hsqrt : 0 < Real.sqrt d := Real.sqrt_pos.mpr hd
  obtain ⟨hα, hβ, hκ, hμ⟩ := powerTwoBasis_constants K hζ
  have hw : 8 * Real.sqrt (r * d) ≤ s / basisAlpha K b := by
    rw [hα]
    apply (le_div_iff₀ hsqrt).mpr
    calc
      _ = 8 * Real.sqrt (d * (r * d)) := by
        rw [mul_assoc, ← Real.sqrt_mul (show (0 : ℝ) ≤ r * d by positivity)]
        congr 2
        ring
      _ ≤ s := hwidth
  have hb : ((r * d : ℕ) : ℝ) * Real.log (numberFieldPolynomialScale K b r m s ell) +
      2 * Real.log (1 / realSecurityError (ell + 4)) ≤ (m : ℝ) * Real.log (8 / 7) := by
    simpa only [b, d, numberFieldPolynomialScale_powerTwo K hζ hm s hell] using hbudget
  obtain ⟨G, hprob, hgood⟩ := numberField_polynomial_certificate K b 0
    (cyclotomicIntegralBasis_one K hζ 0 rfl) hr hmr hell hs hw hb
  refine ⟨G, hprob, ?_⟩
  intro X hX
  obtain ⟨hsurj, _, hη, _, _⟩ := hgood X hX
  refine ⟨hsurj, ?_⟩
  rw [hα, hκ, hμ, polynomialThetaWidth] at hη
  calc
    _ ≤ Real.sqrt d * (64 * 1 * 1 * Real.sqrt (polynomialColumnHeight (r * d) m ell)) := hη
    _ = _ := by rw [Real.sqrt_mul hd.le]; ring

end GeometricGaussianLHL
end

end PowerTwoPolynomial

section PolynomialPinned

/-!
## Two-sided smoothing in the polynomial-width family

The first part of the smoothing-parameter pinning corollary: the same Gaussian-matrix event gives
integer surjectivity, the exact projected-dual lower bound, and fixed positive multiples of
`sqrt ell` on both sides. The numerical ratios for the constant-width theorem remain separate
obligations.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Module NumberField MeasureTheory
open scoped ENNReal

namespace GeometricGaussianLHL

theorem two_div_realSecurityError (ell : ℝ) :
    2 / realSecurityError ell = (2 : ℝ) ^ (ell + 1) := by
  rw [realSecurityError, div_inv_eq_mul, Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
  ring

theorem security_smoothing_lower_scale (ell : ℝ) :
    Real.sqrt (Real.log 2 / Real.pi) * Real.sqrt ell ≤
      Real.sqrt (Real.log ((2 : ℝ) ^ (ell + 1)) / Real.pi) := by
  have hl : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  rw [← Real.sqrt_mul (div_nonneg hl Real.pi_pos.le), Real.log_rpow (by norm_num : (0 : ℝ) < 2)]
  apply Real.sqrt_le_sqrt
  calc
    _ = (ell * Real.log 2) / Real.pi := by ring
    _ ≤ ((ell + 1) * Real.log 2) / Real.pi :=
      div_le_div_of_nonneg_right (by nlinarith) Real.pi_pos.le

variable (K : Type*) [Field K] [NumberField K] {d r m : ℕ}

local instance pinnedEmbeddingsFintype : Fintype (K →+* ℂ) := inferInstance
local instance pinnedAmbientInner : InnerProductSpace ℝ (CanonicalAmbient K) := inferInstance
local instance pinnedSpaceInner : InnerProductSpace ℝ (canonicalSpace K) := inferInstance
local instance pinnedPowerInner (n : ℕ) : InnerProductSpace ℝ (CanonicalPower K n) := inferInstance

theorem canonicalKernel_security_smoothing_lower (b : Basis (Fin d) ℤ (𝓞 K))
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) (hmr : r < m) (ell : ℝ) :
    Real.sqrt (Real.log ((2 : ℝ) ^ (ell + 1)) / Real.pi) / basisBeta K b ≤
      smoothingParameter (canonicalKernel K X) (realSecurityError ell) := by
  have h := (canonicalKernel_projected_dual K b X hmr).2
    (realSecurityError ell) (realSecurityError_pos ell)
  rwa [two_div_realSecurityError] at h

theorem canonicalKernel_security_scale_lower (b : Basis (Fin d) ℤ (𝓞 K))
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) (hmr : r < m) (ell : ℝ) :
    (Real.sqrt (Real.log 2 / Real.pi) / basisBeta K b) * Real.sqrt ell ≤
      smoothingParameter (canonicalKernel K X) (realSecurityError ell) := by
  have h := div_le_div_of_nonneg_right (security_smoothing_lower_scale ell) (basisBeta_pos K b).le
  rw [div_mul_eq_mul_div]
  exact h.trans (canonicalKernel_security_smoothing_lower K b X hmr ell)

/-- The polynomial-width part of the smoothing-parameter pinning corollary, with explicit positive
lower and upper constants witnessing the asserted square-root order. -/
theorem numberField_polynomial_pinned (b : Basis (Fin d) ℤ (𝓞 K))
    (i : Fin d) (hidentity : b i = 1) {p : ℝ} (hp : 1 / 2 ≤ p) :
    ∃ cX cm c C ell₀ : ℝ, 0 < cX ∧ 0 < cm ∧ 0 < c ∧ 0 < C ∧
      ∀ ell : ℝ, ell₀ ≤ ell →
        let r := polynomialFamilyRows d ell
        let R := r * d
        let s := cX * (R : ℝ) ^ p
        let m := polynomialFamilyColumns cm R
        let δ := realSecurityError (ell + 4)
        r < m ∧ ∃ hs : 0 < s, ∃ G : Set (Matrix (Fin r) (Fin m) (𝓞 K)),
          ENNReal.ofReal (1 - 3 * δ) ≤ (numberFieldMatrixLaw K b r m s hs.ne').toOuterMeasure G ∧
          ∀ X ∈ G,
            Function.Surjective X.mulVec ∧
            Real.sqrt (Real.log ((2 : ℝ) ^ (ell + 1)) / Real.pi) / basisBeta K b ≤
              smoothingParameter (canonicalKernel K X) (realSecurityError ell) ∧
            c * Real.sqrt ell ≤ smoothingParameter (canonicalKernel K X) (realSecurityError ell) ∧
            smoothingParameter (canonicalKernel K X) (realSecurityError ell) ≤ C * Real.sqrt ell := by
  obtain ⟨cX, cm, C, ell₀, hcX, hcm, hC, hfamily⟩ := numberField_polynomial_asymptotic K b i hidentity hp
  have hβ := basisBeta_pos K b
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  refine ⟨cX, cm, Real.sqrt (Real.log 2 / Real.pi) / basisBeta K b, C, ell₀,
    hcX, hcm, by positivity, hC, ?_⟩
  intro ell hell
  obtain ⟨hmr, hs, G, hprob, hgood⟩ := hfamily ell hell
  refine ⟨hmr, hs, G, hprob, ?_⟩
  intro X hX
  obtain ⟨himage, _, hupper⟩ := hgood X hX
  exact ⟨himage, canonicalKernel_security_smoothing_lower K b X hmr ell,
    canonicalKernel_security_scale_lower K b X hmr ell, hupper⟩

end GeometricGaussianLHL
end

end PolynomialPinned
