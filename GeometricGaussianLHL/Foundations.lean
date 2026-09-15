import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.BilinearForm.DualLattice
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Projection
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Coefficient kernels, duality, and basic parameters

This module collects the following proof sections, in dependency order.
- Coefficient kernels and image indices (`Foundations`).
- Intrinsic duals and Gaussian mass (`GaussianMass`).
- Minimum stretch of an invertible Gaussian shape (`ShapeMinimumStretch`).
- Finite error budgets (`Parameters`).
- A kernel basis together with lifted quotient vectors (`KernelSplit`).
- Euclidean block coordinates and repeated linear maps (`EuclideanBlocks`).
- Finite rounding with bounded overshoot (`FiniteRounding`).
- Integral-basis coordinates for ring matrices (`RingCoordinates`).
- Extracting surjectivity from a theta bound (`IndexExtraction`).
- Projected ambient dual vectors (`ProjectedDual`).
- The two-vector smoothing lower bound (`SmoothingLower`).
- The intrinsic dual of an integer kernel (`KernelDual`).
- Metric change in the intrinsic span (`MetricChange`).
- Integer and real kernels (`RealKernel`).
- Full row rank and finite image index (`ImageRank`).
- Factoring out the integer image (`IntegerFactorization`).
-/

section Foundations

/-!
## Coefficient kernels and image indices

The integer matrix in Section 2.2 is represented by its actual linear map.
In particular, real full row rank and integer surjectivity are different
properties. The image index is the cardinality of the quotient group, with
Mathlib's convention that an infinite index is zero.
-/

noncomputable section

namespace GeometricGaussianLHL

abbrev Euclidean (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev Coeff (n : ℕ) := Fin n → ℤ

noncomputable def coefficientMap {R M : ℕ} (A : Matrix (Fin R) (Fin M) ℤ) :
    Coeff M →ₗ[ℤ] Coeff R := Matrix.toLin' A

def coefficientKernel {R M : ℕ} (A : Matrix (Fin R) (Fin M) ℤ) :
    Submodule ℤ (Coeff M) := (coefficientMap A).ker

def coefficientImage {R M : ℕ} (A : Matrix (Fin R) (Fin M) ℤ) :
    AddSubgroup (Coeff R) := (coefficientMap A).range.toAddSubgroup

noncomputable def imageIndex {R M : ℕ} (A : Matrix (Fin R) (Fin M) ℤ) : ℕ :=
  (coefficientImage A).index

@[simp] theorem mem_coefficientKernel {R M : ℕ}
    (A : Matrix (Fin R) (Fin M) ℤ) (z : Coeff M) :
    z ∈ coefficientKernel A ↔ A.mulVec z = 0 := Iff.rfl

@[simp] theorem mem_coefficientImage {R M : ℕ}
    (A : Matrix (Fin R) (Fin M) ℤ) (z : Coeff R) :
    z ∈ coefficientImage A ↔ ∃ v, A.mulVec v = z := Iff.rfl

/-- The integer kernel is saturated: a nonzero integer multiple can belong
to it only when the original vector belongs to it. -/
theorem coefficientKernel_saturated {R M : ℕ}
    (A : Matrix (Fin R) (Fin M) ℤ) {a : ℤ} (ha : a ≠ 0) {z : Coeff M}
    (hz : a • z ∈ coefficientKernel A) : z ∈ coefficientKernel A := by
  change coefficientMap A z = 0
  change coefficientMap A (a • z) = 0 at hz
  rw [map_smul] at hz
  exact (smul_eq_zero.mp hz).resolve_left ha

/-- Image index one is precisely surjectivity over the integers. -/
theorem imageIndex_eq_one_iff {R M : ℕ} (A : Matrix (Fin R) (Fin M) ℤ) :
    imageIndex A = 1 ↔ Function.Surjective (coefficientMap A) := by
  rw [imageIndex, AddSubgroup.index_eq_one]
  constructor
  · intro h z
    have hz : z ∈ coefficientImage A := by rw [h]; trivial
    exact hz
  · intro h
    ext z
    simp only [AddSubgroup.mem_top, iff_true]
    exact h z

theorem imageIndex_pos {R M : ℕ} (A : Matrix (Fin R) (Fin M) ℤ)
    [Finite ((Coeff R) ⧸ coefficientImage A)] : 0 < imageIndex A :=
  Nat.pos_of_ne_zero AddSubgroup.index_ne_zero_of_finite

/-- More integer columns than rows force a nonzero integer kernel vector,
without any rank or surjectivity hypothesis. -/
theorem coefficientKernel_ne_bot {R M : ℕ} (A : Matrix (Fin R) (Fin M) ℤ)
    (hRM : R < M) : coefficientKernel A ≠ ⊥ := by
  intro h
  have hinj : Function.Injective (coefficientMap A) := LinearMap.ker_eq_bot.mp h
  have hdim := LinearMap.finrank_le_finrank_of_injective hinj
  simp only [Coeff, Module.finrank_pi, Fintype.card_fin] at hdim
  omega

/-- Integer coefficient vectors in the Euclidean metric. -/
def integerEmbedding (M : ℕ) : Coeff M →ₗ[ℤ] Euclidean M where
  toFun z := WithLp.toLp 2 (fun i => (z i : ℝ))
  map_add' x y := by ext i; simp
  map_smul' a z := by ext i; simp

@[simp] theorem integerEmbedding_apply (M : ℕ) (z : Coeff M) (i : Fin M) :
    integerEmbedding M z i = (z i : ℝ) := rfl

theorem integerEmbedding_injective (M : ℕ) : Function.Injective (integerEmbedding M) := by
  intro x y h
  ext i
  have hi := congrArg (fun v : Euclidean M => v i) h
  change (x i : ℝ) = (y i : ℝ) at hi
  exact_mod_cast hi

def euclideanKernel {R M : ℕ} (A : Matrix (Fin R) (Fin M) ℤ) :
    Submodule ℤ (Euclidean M) := (coefficientKernel A).map (integerEmbedding M)

theorem euclideanKernel_span_ne_bot {R M : ℕ} (A : Matrix (Fin R) (Fin M) ℤ)
    (hRM : R < M) : Submodule.span ℝ (euclideanKernel A : Set (Euclidean M)) ≠ ⊥ := by
  intro hspan
  apply coefficientKernel_ne_bot A hRM
  apply eq_bot_iff.mpr
  intro z hz
  have he : integerEmbedding M z ∈ euclideanKernel A := ⟨z, hz, rfl⟩
  have hs := Submodule.subset_span (R := ℝ) he
  rw [hspan] at hs
  have hz0 : integerEmbedding M z = integerEmbedding M 0 := by simpa using hs
  exact integerEmbedding_injective M hz0

end GeometricGaussianLHL
end

end Foundations

section GaussianMass

/-!
## Intrinsic duals and Gaussian mass

The dual is intersected with the real span of the lattice. This matters for
kernel lattices, which usually do not have full ambient rank. Gaussian sums
take values in `ℝ≥0∞`, so a divergent series cannot silently become zero.
The parameter `t` is the smoothing parameter: the weight is `ρ_{1/t}`.
-/

open scoped ENNReal NNReal

noncomputable section

namespace GeometricGaussianLHL

variable {E : Type*} [NormedAddCommGroup E]

section Dual

variable [InnerProductSpace ℝ E]

def latticeDual (L : Submodule ℤ E) : Submodule ℤ E :=
  (Submodule.span ℝ (L : Set E)).restrictScalars ℤ ⊓
    LinearMap.BilinForm.dualSubmodule (innerₗ E) L

theorem mem_latticeDual {L : Submodule ℤ E} {v : E} :
    v ∈ latticeDual L ↔ v ∈ Submodule.span ℝ (L : Set E) ∧
      ∀ z ∈ L, ∃ k : ℤ, (k : ℝ) = inner ℝ v z := by
  simp [latticeDual, LinearMap.BilinForm.mem_dualSubmodule, Submodule.mem_one]

end Dual

noncomputable def gaussianWeight (t : ℝ) (v : E) : ℝ :=
  Real.exp (-Real.pi * t ^ 2 * ‖v‖ ^ 2)

@[simp] theorem gaussianWeight_zero (t : ℝ) : gaussianWeight t (0 : E) = 1 := by
  simp [gaussianWeight]

theorem gaussianWeight_pos (t : ℝ) (v : E) : 0 < gaussianWeight t v :=
  Real.exp_pos _

@[simp] theorem gaussianWeight_neg (t : ℝ) (v : E) :
    gaussianWeight t (-v) = gaussianWeight t v := by simp [gaussianWeight]

theorem gaussianWeight_le_one (t : ℝ) (v : E) : gaussianWeight t v ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  have := Real.pi_pos
  nlinarith [sq_nonneg t, sq_nonneg ‖v‖, mul_nonneg (sq_nonneg t) (sq_nonneg ‖v‖)]

theorem gaussianWeight_antitone {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (v : E) :
    gaussianWeight t v ≤ gaussianWeight s v := by
  apply Real.exp_le_exp.mpr
  have hsq : s ^ 2 ≤ t ^ 2 := by nlinarith
  have h := mul_le_mul_of_nonneg_left hsq (mul_nonneg Real.pi_pos.le (sq_nonneg ‖v‖))
  nlinarith

/-- Scaling the smoothing parameter raises every Gaussian weight to a real
power, as in equation (43). -/
theorem gaussianWeight_mul_sqrt (t q : ℝ) (hq : 0 ≤ q) (v : E) :
    gaussianWeight (t * Real.sqrt q) v = (gaussianWeight t v) ^ q := by
  rw [gaussianWeight, gaussianWeight, Real.rpow_def_of_pos (Real.exp_pos _),
    Real.log_exp, mul_pow, Real.sq_sqrt hq]
  congr 1
  ring

noncomputable def gaussianMass (t : ℝ) (S : Set E) : ℝ≥0∞ :=
  ∑' v : S, ENNReal.ofReal (gaussianWeight t (v : E))

variable [InnerProductSpace ℝ E]

noncomputable def dualMass (L : Submodule ℤ E) (t : ℝ) : ℝ≥0∞ :=
  gaussianMass t (latticeDual L : Set E)

open scoped Classical in
noncomputable def nonzeroDualMass (L : Submodule ℤ E) (t : ℝ) : ℝ≥0∞ :=
  ∑' v : latticeDual L, if v = 0 then 0 else ENNReal.ofReal (gaussianWeight t (v : E))

theorem dualMass_eq_one_add (L : Submodule ℤ E) (t : ℝ) :
    dualMass L t = 1 + nonzeroDualMass L t := by
  classical
  change (∑' v : latticeDual L, ENNReal.ofReal (gaussianWeight t (v : E))) = _
  rw [ENNReal.tsum_eq_add_tsum_ite
    (f := fun v : latticeDual L => ENNReal.ofReal (gaussianWeight t (v : E))) 0]
  simp only [Submodule.coe_zero, gaussianWeight_zero, ENNReal.ofReal_one]
  congr 1
  unfold nonzeroDualMass
  apply tsum_congr
  intro v
  by_cases hv : v = 0 <;> simp [hv]

theorem one_le_dualMass (L : Submodule ℤ E) (t : ℝ) : 1 ≤ dualMass L t := by
  rw [dualMass_eq_one_add]
  exact le_add_right le_rfl

theorem nonzeroDualMass_antitone (L : Submodule ℤ E) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) : nonzeroDualMass L t ≤ nonzeroDualMass L s := by
  classical
  apply ENNReal.tsum_le_tsum
  intro v
  split_ifs
  · rfl
  · exact ENNReal.ofReal_le_ofReal (gaussianWeight_antitone hs hst v)

def SmoothAt (L : Submodule ℤ E) (ε t : ℝ) : Prop :=
  0 < t ∧ nonzeroDualMass L t ≤ ENNReal.ofReal ε

noncomputable def smoothingParameter (L : Submodule ℤ E) (ε : ℝ) : ℝ :=
  sInf {t : ℝ | SmoothAt L ε t}

theorem SmoothAt.mono_parameter {L : Submodule ℤ E} {ε s t : ℝ}
    (h : SmoothAt L ε s) (hst : s ≤ t) : SmoothAt L ε t :=
  ⟨h.1.trans_le hst, (nonzeroDualMass_antitone L h.1.le hst).trans h.2⟩

theorem SmoothAt.mono_error {L : Submodule ℤ E} {ε ε' t : ℝ}
    (h : SmoothAt L ε t) (hε : ε ≤ ε') : SmoothAt L ε' t :=
  ⟨h.1, h.2.trans (ENNReal.ofReal_le_ofReal hε)⟩

theorem smoothingParameter_le_of_smoothAt {L : Submodule ℤ E} {ε t : ℝ}
    (h : SmoothAt L ε t) : smoothingParameter L ε ≤ t := by
  apply csInf_le (show BddBelow {u : ℝ | SmoothAt L ε u} from ?_) h
  exact ⟨0, fun _ hu => hu.1.le⟩

/-- The power-of-a-sum inequality for a nonnegative series, including infinite
series. This is the analytic core of the common-event error extension. -/
theorem tsum_rpow_le_rpow_tsum {ι : Type*} (f : ι → ℝ≥0∞) {q : ℝ} (hq : 1 ≤ q) :
    (∑' i, f i ^ q) ≤ (∑' i, f i) ^ q := by
  have hq' : 0 ≤ q - 1 := by linarith
  have hp (x : ℝ≥0∞) : x ^ q = x * x ^ (q - 1) := by
    conv_lhs => rw [show q = 1 + (q - 1) by ring]
    rw [ENNReal.rpow_add_of_nonneg 1 (q - 1) (by norm_num) hq', ENNReal.rpow_one]
  calc
    (∑' i, f i ^ q) = ∑' i, f i * f i ^ (q - 1) := by simp_rw [hp]
    _ ≤ ∑' i, f i * (∑' j, f j) ^ (q - 1) := by
      apply ENNReal.tsum_le_tsum
      intro i
      exact mul_le_mul_right (ENNReal.rpow_le_rpow (ENNReal.le_tsum i) hq') _
    _ = (∑' i, f i) * (∑' i, f i) ^ (q - 1) := ENNReal.tsum_mul_right
    _ = (∑' i, f i) ^ q := (hp _).symm

end GeometricGaussianLHL
end

end GaussianMass

section ShapeMinimumStretch

/-!
## Minimum stretch of an invertible Gaussian shape

The reciprocal inverse operator norm is the best uniform lower stretch
in positive dimension. This identifies the inverse-norm width condition
in Gaussian pushforward with the paper's smallest singular value.
-/

noncomputable section

namespace GeometricGaussianLHL

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def shapeMinimumStretch (S : E ≃L[ℝ] E) : ℝ := ‖S.symm.toContinuousLinearMap‖⁻¹

theorem shapeMinimumStretch_nonneg (S : E ≃L[ℝ] E) : 0 ≤ shapeMinimumStretch S :=
  inv_nonneg.mpr (norm_nonneg _)

theorem shapeMinimumStretch_mul_norm_le (S : E ≃L[ℝ] E) (x : E) :
    shapeMinimumStretch S * ‖x‖ ≤ ‖S x‖ := by
  have h := S.symm.toContinuousLinearMap.le_opNorm (S x)
  change ‖S.symm (S x)‖ ≤ ‖S.symm.toContinuousLinearMap‖ * ‖S x‖ at h
  rw [S.symm_apply_apply] at h
  by_cases hz : ‖S.symm.toContinuousLinearMap‖ = 0
  · simp only [shapeMinimumStretch, hz, inv_zero, zero_mul, norm_nonneg]
  · have hp : 0 < ‖S.symm.toContinuousLinearMap‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    change ‖S.symm.toContinuousLinearMap‖⁻¹ * ‖x‖ ≤ ‖S x‖
    rw [← div_eq_inv_mul]
    exact (div_le_iff₀ hp).mpr (by simpa only [mul_comm] using h)

theorem shapeMinimumStretch_pos [Nontrivial E] (S : E ≃L[ℝ] E) :
    0 < shapeMinimumStretch S := inv_pos.mpr S.symm.norm_pos

/-- The positive lower-stretch constants are exactly those below the minimum stretch. -/
theorem le_shapeMinimumStretch_iff [Nontrivial E] (S : E ≃L[ℝ] E) {c : ℝ} (hc : 0 < c) :
    c ≤ shapeMinimumStretch S ↔ ∀ x : E, c * ‖x‖ ≤ ‖S x‖ := by
  constructor
  · intro h x
    exact (mul_le_mul_of_nonneg_right h (norm_nonneg x)).trans (shapeMinimumStretch_mul_norm_le S x)
  · intro h
    have hp : 0 < ‖S.symm.toContinuousLinearMap‖ := S.symm.norm_pos
    have hb : ‖S.symm.toContinuousLinearMap‖ ≤ c⁻¹ := by
      apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hc.le)
      intro y
      change ‖S.symm y‖ ≤ c⁻¹ * ‖y‖
      have hy := h (S.symm y)
      rw [S.apply_symm_apply] at hy
      rw [← div_eq_inv_mul]
      exact (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hy)
    change c ≤ ‖S.symm.toContinuousLinearMap‖⁻¹
    rw [← one_div]
    apply (le_div_iff₀ hp).mpr
    have hb' := mul_le_mul_of_nonneg_right hb hc.le
    simpa only [inv_mul_cancel₀ hc.ne', mul_comm] using hb'

end GeometricGaussianLHL
end

end ShapeMinimumStretch

section Parameters

/-!
## Finite error budgets

The exact constants in the LHL error calculation. This module does not
assume that any probabilistic estimate has already been proved.
-/

noncomputable section

namespace GeometricGaussianLHL

def securityError (ell : ℕ) : ℝ := ((2 : ℝ) ^ ell)⁻¹

theorem securityError_pos (ell : ℕ) : 0 < securityError ell := by
  unfold securityError
  positivity

theorem securityError_add (ell k : ℕ) :
    securityError (ell + k) = securityError ell / 2 ^ k := by
  simp [securityError, pow_add, div_eq_mul_inv, mul_comm]

theorem securityError_antitone {ell μ : ℕ} (h : ell ≤ μ) :
    securityError μ ≤ securityError ell := by
  unfold securityError
  gcongr
  norm_num

theorem polynomial_failureBudget_le {ell : ℕ} (hell : 1 ≤ ell) :
    securityError (ell + 4) ≤ 1 / 32 := by
  calc
    securityError (ell + 4) ≤ securityError 5 := securityError_antitone (by omega)
    _ = 1 / 32 := by norm_num [securityError]

theorem constant_failureBudget_le {ell : ℕ} (hell : 1 ≤ ell) :
    securityError (ell + 6) ≤ 1 / 128 := by
  calc
    securityError (ell + 6) ≤ securityError 7 := securityError_antitone (by omega)
    _ = 1 / 128 := by norm_num [securityError]

/-- The paper's accuracy parameter is real. The natural-parameter definition
above is retained for its existing arithmetic corollaries. -/
def realSecurityError (ell : ℝ) : ℝ := ((2 : ℝ) ^ ell)⁻¹

theorem realSecurityError_pos (ell : ℝ) : 0 < realSecurityError ell := by
  unfold realSecurityError
  positivity

theorem realSecurityError_eq_rpow_neg (ell : ℝ) :
    realSecurityError ell = (2 : ℝ) ^ (-ell) := by
  simp [realSecurityError, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]

@[simp] theorem realSecurityError_natCast (ell : ℕ) :
    realSecurityError (ell : ℝ) = securityError ell := by
  simp [realSecurityError, securityError]

theorem realSecurityError_antitone {ell μ : ℝ} (h : ell ≤ μ) :
    realSecurityError μ ≤ realSecurityError ell := by
  unfold realSecurityError
  gcongr
  norm_num

theorem realSecurityError_add (ell k : ℝ) :
    realSecurityError (ell + k) = realSecurityError ell / (2 : ℝ) ^ k := by
  simp only [realSecurityError, Real.rpow_add (by norm_num : (0 : ℝ) < 2),
    mul_inv_rev, div_eq_mul_inv]
  ring

theorem real_polynomial_failureBudget_le {ell : ℝ} (hell : 1 ≤ ell) :
    realSecurityError (ell + 4) ≤ 1 / 32 := by
  calc
    realSecurityError (ell + 4) ≤ realSecurityError 5 :=
      realSecurityError_antitone (by linarith)
    _ = 1 / 32 := by norm_num [realSecurityError]

theorem real_constant_failureBudget_le {ell : ℝ} (hell : 1 ≤ ell) :
    realSecurityError (ell + 6) ≤ 1 / 128 := by
  calc
    realSecurityError (ell + 6) ≤ realSecurityError 7 :=
      realSecurityError_antitone (by linarith)
    _ = 1 / 128 := by norm_num [realSecurityError]

def jointErrorBound (δ : ℝ) (J : ℕ) : ℝ :=
  3 * δ + (2 * J * δ) / (1 - 2 * δ)

theorem jointErrorBound_one_lt {δ : ℝ} (hδ : 0 < δ) (hu : δ ≤ 1 / 32) :
    jointErrorBound δ 1 < (26 / 5) * δ := by
  have hden : 0 < 1 - 2 * δ := by linarith
  have hfrac : 2 * δ / (1 - 2 * δ) ≤ (32 / 15) * δ := by
    apply (div_le_iff₀ hden).mpr
    nlinarith [mul_nonneg hδ.le (sub_nonneg.mpr hu)]
  simp only [jointErrorBound, Nat.cast_one, mul_one]
  linarith

/-- The numerical inequality in Corollary 5.1 at polynomial width. -/
theorem polynomial_jointError_lt {ell : ℕ} (hell : 1 ≤ ell) :
    jointErrorBound (securityError (ell + 4)) 1 < securityError ell := by
  have h := jointErrorBound_one_lt (securityError_pos (ell + 4))
    (polynomial_failureBudget_le hell)
  rw [securityError_add] at h ⊢
  norm_num at h ⊢
  linarith [securityError_pos ell]

/-- The numerical inequality in Corollary 5.1 at constant width. -/
theorem constant_jointError_lt {ell : ℕ} (hell : 1 ≤ ell) :
    jointErrorBound (securityError (ell + 6)) 1 < securityError ell := by
  have hu : securityError (ell + 6) ≤ 1 / 32 :=
    (constant_failureBudget_le hell).trans (by norm_num)
  have h := jointErrorBound_one_lt (securityError_pos (ell + 6)) hu
  rw [securityError_add] at h ⊢
  norm_num at h ⊢
  linarith [securityError_pos ell]

/-- The polynomial-width joint error budget for every real accuracy parameter. -/
theorem real_polynomial_jointError_lt {ell : ℝ} (hell : 1 ≤ ell) :
    jointErrorBound (realSecurityError (ell + 4)) 1 < realSecurityError ell := by
  have h := jointErrorBound_one_lt (realSecurityError_pos (ell + 4))
    (real_polynomial_failureBudget_le hell)
  rw [realSecurityError_add] at h ⊢
  norm_num at h ⊢
  linarith [realSecurityError_pos ell]

/-- The constant-width joint error budget for every real accuracy parameter. -/
theorem real_constant_jointError_lt {ell : ℝ} (hell : 1 ≤ ell) :
    jointErrorBound (realSecurityError (ell + 6)) 1 < realSecurityError ell := by
  have hu : realSecurityError (ell + 6) ≤ 1 / 32 :=
    (real_constant_failureBudget_le hell).trans (by norm_num)
  have h := jointErrorBound_one_lt (realSecurityError_pos (ell + 6)) hu
  rw [realSecurityError_add] at h ⊢
  norm_num at h ⊢
  linarith [realSecurityError_pos ell]

/-- The logarithmic column condition is exactly the needed exponential
remainder bound. Both finite geometric theorems use this implication. -/
theorem remainder_le_of_column_condition {W c δ : ℝ} {R m : ℕ}
    (hW : 0 < W) (hc : 0 < c) (hδ : 0 < δ)
    (hbudget : (R : ℝ) * Real.log W + 2 * Real.log (1 / δ) ≤
      (m : ℝ) * Real.log (1 / c)) : W ^ R * c ^ m ≤ δ ^ 2 := by
  apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
  rw [Real.log_mul (pow_pos hW R).ne' (pow_pos hc m).ne', Real.log_pow,
    Real.log_pow, Real.log_pow]
  rw [Real.log_div one_ne_zero hδ.ne', Real.log_div one_ne_zero hc.ne',
    Real.log_one, zero_sub, zero_sub] at hbudget
  norm_num only [Nat.cast_ofNat]
  nlinarith

theorem polynomial_remainder_le {W δ : ℝ} {R m : ℕ}
    (hW : 0 < W) (hδ : 0 < δ)
    (hbudget : (R : ℝ) * Real.log W + 2 * Real.log (1 / δ) ≤
      (m : ℝ) * Real.log (8 / 7)) : W ^ R * (7 / 8 : ℝ) ^ m ≤ δ ^ 2 := by
  apply remainder_le_of_column_condition hW (by norm_num) hδ
  convert hbudget using 1
  norm_num

theorem constant_remainder_le {W δ : ℝ} {R m : ℕ}
    (hW : 0 < W) (hδ : 0 < δ)
    (hbudget : (R : ℝ) * Real.log W + 2 * Real.log (1 / δ) ≤
      (m : ℝ) * Real.log (50 / 49)) : W ^ R * (49 / 50 : ℝ) ^ m ≤ δ ^ 2 := by
  apply remainder_le_of_column_condition hW (by norm_num) hδ
  convert hbudget using 1
  norm_num

end GeometricGaussianLHL
end

end Parameters

section KernelSplit

/-!
## A kernel basis together with lifted quotient vectors

A specified linear right inverse splits a surjection over the coefficient
ring itself. In particular, integer lifts and an integer kernel basis form
an integer basis of the domain, as required by the covolume argument.
-/

noncomputable section

open Module

namespace GeometricGaussianLHL

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

def kernelSplitEquiv (f : M →ₗ[R] N) (g : N →ₗ[R] M) (hfg : f.comp g = LinearMap.id) :
    (f.ker × N) ≃ₗ[R] M :=
  { f.ker.subtype.coprod g with
    invFun := fun x => (⟨x - g (f x), by
      change f (x - g (f x)) = 0
      have h := LinearMap.congr_fun hfg (f x)
      simpa only [map_sub, LinearMap.comp_apply, LinearMap.id_apply] using sub_eq_zero.mpr h.symm⟩, f x)
    left_inv := by
      rintro ⟨x, y⟩
      have hy : f (g y) = y := LinearMap.congr_fun hfg y
      apply Prod.ext
      · apply Subtype.ext
        change (x : M) + g y - g (f ((x : M) + g y)) = (x : M)
        rw [map_add, show f (x : M) = 0 from x.property, zero_add, hy, add_sub_cancel_right]
      · change f ((x : M) + g y) = y
        rw [map_add, show f (x : M) = 0 from x.property, zero_add, hy]
    right_inv := by
      intro x
      exact sub_add_cancel x (g (f x)) }

@[simp] theorem kernelSplitEquiv_apply (f : M →ₗ[R] N) (g : N →ₗ[R] M)
    (hfg : f.comp g = LinearMap.id) (x : f.ker) (y : N) :
    kernelSplitEquiv f g hfg (x, y) = (x : M) + g y := rfl

def kernelLiftBasis {ι κ : Type*} (f : M →ₗ[R] N) (g : N →ₗ[R] M)
    (hfg : f.comp g = LinearMap.id) (b : Basis ι R f.ker) (c : Basis κ R N) :
    Basis (ι ⊕ κ) R M := (b.prod c).map (kernelSplitEquiv f g hfg)

@[simp] theorem kernelLiftBasis_inl {ι κ : Type*} (f : M →ₗ[R] N) (g : N →ₗ[R] M)
    (hfg : f.comp g = LinearMap.id) (b : Basis ι R f.ker) (c : Basis κ R N) (i : ι) :
    kernelLiftBasis f g hfg b c (Sum.inl i) = b i := by
  simp [kernelLiftBasis, Basis.prod_apply]

@[simp] theorem kernelLiftBasis_inr {ι κ : Type*} (f : M →ₗ[R] N) (g : N →ₗ[R] M)
    (hfg : f.comp g = LinearMap.id) (b : Basis ι R f.ker) (c : Basis κ R N) (j : κ) :
    kernelLiftBasis f g hfg b c (Sum.inr j) = g (c j) := by
  simp [kernelLiftBasis, Basis.prod_apply]

end GeometricGaussianLHL
end

end KernelSplit

section EuclideanBlocks

/-!
## Euclidean block coordinates and repeated linear maps

Flattening the pair (block, coordinate) preserves the Euclidean norm.
Applying the same linear map to each block has the same operator-norm
upper bound. These constructions keep the canonical metric explicit when
passing from one ring coordinate to a vector of ring coordinates.
-/

noncomputable section

namespace GeometricGaussianLHL

def euclideanBlocks (n d : ℕ) :
    Euclidean (n * d) ≃ₗᵢ[ℝ] PiLp 2 (fun _ : Fin n => Euclidean d) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
    (finProdFinEquiv.symm.trans (Equiv.sigmaEquivProd (Fin n) (Fin d)).symm)).trans
    (LinearIsometryEquiv.piLpCurry ℝ 2 (fun (_ : Fin n) (_ : Fin d) => ℝ))

@[simp] theorem euclideanBlocks_apply (n d : ℕ) (x : Euclidean (n * d))
    (j : Fin n) (k : Fin d) :
    euclideanBlocks n d x j k = x (finProdFinEquiv (j, k)) := rfl

theorem euclideanBlocks_integer {O : Type*} [CommRing O] {d n : ℕ}
    (c : (Fin n → O) → Coeff (n * d)) (c₀ : O → Coeff d)
    (hc : ∀ x j k, c x (finProdFinEquiv (j, k)) = c₀ (x j) k) (x : Fin n → O) :
    euclideanBlocks n d (integerEmbedding (n * d) (c x)) =
      WithLp.toLp 2 (fun j => integerEmbedding d (c₀ (x j))) := by
  ext j k
  simp only [euclideanBlocks_apply, integerEmbedding_apply, hc]

section Repeated

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

def repeatedContinuousEquiv (e : E ≃L[ℝ] F) (n : ℕ) :
    PiLp 2 (fun _ : Fin n => E) ≃L[ℝ] PiLp 2 (fun _ : Fin n => F) :=
  ((WithLp.linearEquiv 2 ℝ (Fin n → E)).trans
    ((LinearEquiv.piCongrRight (fun _ => e.toLinearEquiv)).trans
      (WithLp.linearEquiv 2 ℝ (Fin n → F)).symm)).toContinuousLinearEquiv

omit [FiniteDimensional ℝ F] in
@[simp] theorem repeatedContinuousEquiv_apply (e : E ≃L[ℝ] F) (n : ℕ)
    (x : PiLp 2 (fun _ : Fin n => E)) (j : Fin n) :
    repeatedContinuousEquiv e n x j = e (x j) := rfl

@[simp] theorem repeatedContinuousEquiv_symm (e : E ≃L[ℝ] F) (n : ℕ) :
    (repeatedContinuousEquiv e n).symm = repeatedContinuousEquiv e.symm n := by
  ext x j
  rfl

omit [FiniteDimensional ℝ F] in
theorem repeatedContinuousEquiv_norm_apply_le (e : E ≃L[ℝ] F) (n : ℕ)
    (x : PiLp 2 (fun _ : Fin n => E)) :
    ‖repeatedContinuousEquiv e n x‖ ≤ ‖e.toContinuousLinearMap‖ * ‖x‖ := by
  have hs : ‖repeatedContinuousEquiv e n x‖ ^ 2 ≤ (‖e.toContinuousLinearMap‖ * ‖x‖) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, mul_pow, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    rw [repeatedContinuousEquiv_apply, ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (e.toContinuousLinearMap.le_opNorm (x j)) 2
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp hs

omit [FiniteDimensional ℝ F] in
theorem repeatedContinuousEquiv_norm_le (e : E ≃L[ℝ] F) (n : ℕ) :
    ‖(repeatedContinuousEquiv e n).toContinuousLinearMap‖ ≤ ‖e.toContinuousLinearMap‖ := by
  exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (repeatedContinuousEquiv_norm_apply_le e n)

end Repeated

end GeometricGaussianLHL
end

end EuclideanBlocks

section FiniteRounding

/-!
## Finite rounding with bounded overshoot

The displacement construction in Lemma 4.4 first rounds toward zero and
then increments a subset of coordinates. The subset sum crosses its target
by less than one weight; each resulting coordinate stays within one of
the unrounded real vector.
-/

noncomputable section

open scoped BigOperators

namespace GeometricGaussianLHL

theorem exists_subset_sum_crossing {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w : ι → ℝ) {B d : ℝ} (hB : 0 < B) (hd : 0 ≤ d)
    (hw : ∀ i ∈ s, w i < B) (hs : d ≤ ∑ i ∈ s, w i) :
    ∃ t ⊆ s, d ≤ ∑ i ∈ t, w i ∧ ∑ i ∈ t, w i < d + B := by
  induction s using Finset.induction_on generalizing d with
  | empty =>
    refine ⟨∅, Finset.Subset.refl _, ?_, ?_⟩
    · simpa using hs
    · simpa using (show 0 < d + B by linarith)
  | @insert i s hi ih =>
    by_cases hdi : d ≤ w i
    · refine ⟨{i}, by simp, ?_, ?_⟩
      · simpa using hdi
      · have hiB := hw i (Finset.mem_insert_self i s)
        simpa using (show w i < d + B by linarith)
    · have hds : d - w i ≤ ∑ j ∈ s, w j := by
        rw [Finset.sum_insert hi] at hs
        linarith
      obtain ⟨t, hts, htlo, hthi⟩ := ih (by linarith : 0 ≤ d - w i)
        (fun j hj => hw j (Finset.mem_insert_of_mem hj)) hds
      have hit : i ∉ t := fun hit => hi (hts hit)
      refine ⟨insert i t, Finset.insert_subset_insert i hts, ?_, ?_⟩
      · rw [Finset.sum_insert hit]
        linarith
      · rw [Finset.sum_insert hit]
        linarith

/-- Apply the sign of a real coordinate to an integer magnitude. -/
def orientedInteger (y : ℝ) (n : ℤ) : ℤ := if y < 0 then -n else n

theorem mul_orientedInteger (y : ℝ) (n : ℤ) :
    y * (orientedInteger y n : ℝ) = |y| * (n : ℝ) := by
  by_cases hy : y < 0
  · simp [orientedInteger, hy, abs_of_neg hy]
  · simp [orientedInteger, hy, abs_of_nonneg (le_of_not_gt hy)]

theorem orientedInteger_error (y c : ℝ) (n : ℤ) :
    |(orientedInteger y n : ℝ) - c * y| = |(n : ℝ) - c * (|y|)| := by
  by_cases hy : y < 0
  · simp only [orientedInteger, ite_eq_left hy, Int.cast_neg, abs_of_neg hy]
    rw [show -(n : ℝ) - c * y = -((n : ℝ) - c * -y) by ring, abs_neg]
  · simp [orientedInteger, hy, abs_of_nonneg (le_of_not_gt hy)]

theorem oriented_floor_error_le_one (y c : ℝ) (b : Bool) :
    |(orientedInteger y (⌊c * |y|⌋ + if b then 1 else 0) : ℝ) - c * y| ≤ 1 := by
  rw [orientedInteger_error]
  have hlo := Int.floor_le (c * |y|)
  have hhi := Int.lt_floor_add_one (c * |y|)
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, Int.add_zero,
    Int.cast_add, Int.cast_one] <;> apply abs_le.mpr <;> constructor <;> linarith

theorem integer_rounding_norm_error {R : ℕ} (y : Euclidean R) (c : ℝ) (v : Coeff R)
    (hv : ∀ i, |(v i : ℝ) - c * y i| ≤ 1) :
    ‖integerEmbedding R v - c • y‖ ≤ Real.sqrt R := by
  have hsq : ‖integerEmbedding R v - c • y‖ ^ 2 ≤ (R : ℝ) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      _ ≤ ∑ _i : Fin R, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, integerEmbedding_apply]
        have ha := abs_le.mp (hv i)
        nlinarith [sq_nonneg ((v i : ℝ) - c * y i - 1),
          sq_nonneg ((v i : ℝ) - c * y i + 1)]
      _ = (R : ℝ) := by simp
  nlinarith [Real.sq_sqrt (show 0 ≤ (R : ℝ) by positivity), Real.sqrt_nonneg (R : ℝ),
    norm_nonneg (integerEmbedding R v - c • y)]

end GeometricGaussianLHL
end

end FiniteRounding

section RingCoordinates

/-!
## Integral-basis coordinates for ring matrices

An actual finite integral basis gives linear coordinate equivalences on
powers of the ring. Conjugating a ring matrix by these equivalences gives
its integer coefficient matrix. The kernel identity and surjectivity
equivalence are proved directly, before any Gaussian or metric arguments.
-/

noncomputable section

open Module

namespace GeometricGaussianLHL

variable {O : Type*} [CommRing O] {d r m : ℕ}

/-- Coordinates ordered by the pair (ring coordinate, basis coordinate). -/
def ringPowerCoordinates (b : Basis (Fin d) ℤ O) (n : ℕ) :
    (Fin n → O) ≃ₗ[ℤ] Coeff (n * d) where
  toFun x l := b.equivFun (x (finProdFinEquiv.symm l).1) (finProdFinEquiv.symm l).2
  invFun z j := b.equivFun.symm (fun k => z (finProdFinEquiv (j, k)))
  left_inv x := by
    funext j
    apply b.equivFun.injective
    ext k
    simp only [LinearEquiv.apply_symm_apply, Equiv.symm_apply_apply]
  right_inv z := by
    funext l
    simp only [LinearEquiv.apply_symm_apply, Prod.mk.eta, Equiv.apply_symm_apply]
  map_add' x y := by
    funext l
    simp only [Pi.add_apply, map_add]
  map_smul' a x := by
    funext l
    simp only [Pi.smul_apply, map_smul, RingHom.id_apply]

@[simp] theorem ringPowerCoordinates_apply (b : Basis (Fin d) ℤ O)
    (n : ℕ) (x : Fin n → O) (j : Fin n) (k : Fin d) :
    ringPowerCoordinates b n x (finProdFinEquiv (j, k)) = b.equivFun (x j) k := by
  change b.equivFun (x (finProdFinEquiv.symm (finProdFinEquiv (j, k))).1)
    (finProdFinEquiv.symm (finProdFinEquiv (j, k))).2 = _
  rw [Equiv.symm_apply_apply]

@[simp] theorem ringPowerCoordinates_symm_apply (b : Basis (Fin d) ℤ O)
    (n : ℕ) (z : Coeff (n * d)) (j : Fin n) :
    (ringPowerCoordinates b n).symm z j = b.equivFun.symm (fun k => z (finProdFinEquiv (j, k))) := rfl

def ringMatrixMap (X : Matrix (Fin r) (Fin m) O) :
    (Fin m → O) →ₗ[ℤ] (Fin r → O) := (Matrix.toLin' X).restrictScalars ℤ

@[simp] theorem ringMatrixMap_apply (X : Matrix (Fin r) (Fin m) O) (x : Fin m → O) :
    ringMatrixMap X x = X.mulVec x := rfl

def ringCoefficientMatrix (b : Basis (Fin d) ℤ O) (X : Matrix (Fin r) (Fin m) O) :
    Matrix (Fin (r * d)) (Fin (m * d)) ℤ :=
  LinearMap.toMatrix' ((ringPowerCoordinates b r).toLinearMap ∘ₗ ringMatrixMap X ∘ₗ
    (ringPowerCoordinates b m).symm.toLinearMap)

theorem ringCoefficientMatrix_map (b : Basis (Fin d) ℤ O) (X : Matrix (Fin r) (Fin m) O)
    (x : Fin m → O) :
    coefficientMap (ringCoefficientMatrix b X) (ringPowerCoordinates b m x) =
      ringPowerCoordinates b r (X.mulVec x) := by
  simp only [coefficientMap, ringCoefficientMatrix, Matrix.toLin'_toMatrix', LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, ringMatrixMap_apply]

/-- Integer surjectivity of the coefficient matrix is exactly ring-matrix
surjectivity; it is not an extra assumption on the sampled ring matrix. -/
theorem ringCoefficientMatrix_surjective_iff (b : Basis (Fin d) ℤ O)
    (X : Matrix (Fin r) (Fin m) O) :
    Function.Surjective (coefficientMap (ringCoefficientMatrix b X)) ↔ Function.Surjective X.mulVec := by
  constructor
  · intro h y
    obtain ⟨z, hz⟩ := h (ringPowerCoordinates b r y)
    refine ⟨(ringPowerCoordinates b m).symm z, (ringPowerCoordinates b r).injective ?_⟩
    rw [← ringCoefficientMatrix_map, LinearEquiv.apply_symm_apply]
    exact hz
  · intro h z
    obtain ⟨x, hx⟩ := h ((ringPowerCoordinates b r).symm z)
    refine ⟨ringPowerCoordinates b m x, ?_⟩
    rw [ringCoefficientMatrix_map, hx, LinearEquiv.apply_symm_apply]

theorem ringCoefficientMatrix_kernel (b : Basis (Fin d) ℤ O)
    (X : Matrix (Fin r) (Fin m) O) :
    coefficientKernel (ringCoefficientMatrix b X) =
      (ringMatrixMap X).ker.map (ringPowerCoordinates b m).toLinearMap := by
  ext z
  constructor
  · intro hz
    refine ⟨(ringPowerCoordinates b m).symm z, ?_, LinearEquiv.apply_symm_apply _ _⟩
    change X.mulVec ((ringPowerCoordinates b m).symm z) = 0
    apply (ringPowerCoordinates b r).injective
    rw [← ringCoefficientMatrix_map, LinearEquiv.apply_symm_apply, map_zero]
    exact hz
  · rintro ⟨x, hx, rfl⟩
    change coefficientMap (ringCoefficientMatrix b X) (ringPowerCoordinates b m x) = 0
    rw [ringCoefficientMatrix_map]
    change X.mulVec x = 0 at hx
    rw [hx, map_zero]

end GeometricGaussianLHL
end

end RingCoordinates

section IndexExtraction

/-!
## Extracting surjectivity from a theta bound

These are the algebraic deductions after Proposition 4.1. They do not assert
the integral identity or its probabilistic estimate; those are separate proof
obligations. The mass supplied to these lemmas must include the origin.
-/

namespace GeometricGaussianLHL

/-- A positive integer times a mass containing the origin cannot be below two
unless the integer is one. The same estimate bounds the nonzero mass. -/
theorem index_and_mass_of_bound {I : ℕ} {mass ε : ℝ}
    (hI : 0 < I) (hmass : 1 ≤ mass) (hε : ε < 1)
    (hbound : (I : ℝ) * mass ≤ 1 + ε) :
    I = 1 ∧ mass - 1 ≤ ε := by
  have hIreal : (1 : ℝ) ≤ I := by exact_mod_cast hI
  have hIlt : (I : ℝ) < 2 := by nlinarith
  have hIlt' : I < 2 := by exact_mod_cast hIlt
  have hIeq : I = 1 := by omega
  refine ⟨hIeq, ?_⟩
  simpa [hIeq] using (show (I : ℝ) * mass - 1 ≤ ε by linarith)

/-- The previous conclusion applied to the actual image index of an integer
matrix. Finite index is essential because Mathlib assigns index zero to an
infinite quotient. -/
theorem surjective_and_mass_of_index_bound {R M : ℕ}
    (A : Matrix (Fin R) (Fin M) ℤ)
    [Finite ((Coeff R) ⧸ coefficientImage A)]
    {mass ε : ℝ} (hmass : 1 ≤ mass) (hε : ε < 1)
    (hbound : (imageIndex A : ℝ) * mass ≤ 1 + ε) :
    Function.Surjective (coefficientMap A) ∧ mass - 1 ≤ ε := by
  obtain ⟨hI, hm⟩ := index_and_mass_of_bound (imageIndex_pos A) hmass hε hbound
  exact ⟨(imageIndex_eq_one_iff A).mp hI, hm⟩

/-- Assembly of the near-origin contribution and remainder in Theorems 4.6
and 4.9, once both analytic estimates and the identity have been proved. -/
theorem index_and_mass_of_main_and_remainder {I : ℕ} {mass near far δ : ℝ}
    (hI : 0 < I) (hmass : 1 ≤ mass) (hδ : δ < 1 / 2)
    (hidentity : (I : ℝ) * mass = near + far)
    (hnear : near ≤ 1 + δ) (hfar : far ≤ δ) :
    I = 1 ∧ mass - 1 ≤ 2 * δ := by
  apply index_and_mass_of_bound hI hmass (by linarith)
  linarith

/-- The index-extraction step for the actual extended-valued Gaussian mass
of the coefficient kernel. No convergence assumption is hidden in a real
`tsum`: the upper bound itself forces the mass to be finite. -/
theorem surjective_and_smoothAt_of_index_mass_bound {R M : ℕ}
    (A : Matrix (Fin R) (Fin M) ℤ)
    [Finite ((Coeff R) ⧸ coefficientImage A)] {ε t : ℝ}
    (ht : 0 < t) (hε : ε < 1)
    (hbound : (imageIndex A : ENNReal) * dualMass (euclideanKernel A) t ≤
      1 + ENNReal.ofReal ε) :
    Function.Surjective (coefficientMap A) ∧ SmoothAt (euclideanKernel A) ε t := by
  have htwo : 1 + ENNReal.ofReal ε < (2 : ENNReal) := by
    convert ENNReal.add_lt_add_left (by simp : (1 : ENNReal) ≠ ⊤)
      (ENNReal.ofReal_lt_one.mpr hε) using 1
    norm_num
  have hIlt : (imageIndex A : ENNReal) < 2 := by
    calc
      (imageIndex A : ENNReal) = (imageIndex A : ENNReal) * 1 := (mul_one _).symm
      _ ≤ (imageIndex A : ENNReal) * dualMass (euclideanKernel A) t :=
        mul_le_mul_right (one_le_dualMass _ _) _
      _ ≤ 1 + ENNReal.ofReal ε := hbound
      _ < 2 := htwo
  have hInat : imageIndex A < 2 := by exact_mod_cast hIlt
  have hIpos := imageIndex_pos A
  have hI : imageIndex A = 1 := by omega
  refine ⟨(imageIndex_eq_one_iff A).mp hI, ht, ?_⟩
  rw [hI, Nat.cast_one, one_mul, dualMass_eq_one_add] at hbound
  exact (ENNReal.add_le_add_iff_left (by simp : (1 : ENNReal) ≠ ⊤)).mp hbound

end GeometricGaussianLHL

end IndexExtraction

section ProjectedDual

/-!
## Projected ambient dual vectors

The geometric argument of Proposition 4.14. The inclusion proved here needs
no primitivity assumption: primitivity is needed for equality with the whole
projected ambient dual, but not for the short-vector upper bound.
-/

noncomputable section

namespace GeometricGaussianLHL

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Any vector with integral pairings on the lattice projects into its
intrinsic dual. -/
theorem projection_mem_latticeDual (L : Submodule ℤ E) (v : E)
    (hv : ∀ z ∈ L, ∃ k : ℤ, (k : ℝ) = inner ℝ v z) :
    (Submodule.span ℝ (L : Set E)).starProjection v ∈ latticeDual L := by
  rw [mem_latticeDual]
  refine ⟨Submodule.starProjection_apply_mem _ v, ?_⟩
  intro z hz
  obtain ⟨k, hk⟩ := hv z hz
  refine ⟨k, ?_⟩
  rw [Submodule.inner_starProjection_left_eq_right,
    (Submodule.span ℝ (L : Set E)).starProjection_eq_self_iff.mpr
      (Submodule.subset_span hz)]
  exact hk

/-- A nonzero subspace has a nonzero projection of at least one element of
any ambient basis. -/
theorem exists_nonzero_basis_projection {ι : Type*} (b : Module.Basis ι ℝ E)
    (V : Submodule ℝ E) (hV : V ≠ ⊥) :
    ∃ i, V.starProjection (b i) ≠ 0 := by
  by_contra! h
  have hp : V.starProjection.toLinearMap = 0 := b.ext h
  apply hV
  apply eq_bot_iff.mpr
  intro v hv
  have hz := LinearMap.congr_fun hp v
  rw [ContinuousLinearMap.coe_coe,
    V.starProjection_eq_self_iff.mpr hv, LinearMap.zero_apply] at hz
  exact hz

/-- Proposition 4.14's short-vector conclusion, formulated for any bounded
ambient basis with integral pairings on `L`. This specializes to a basis of
the ambient dual lattice, and to the standard basis for coefficient kernels. -/
theorem exists_short_dual_vector {ι : Type*} (L : Submodule ℤ E)
    (b : Module.Basis ι ℝ E) {β : ℝ}
    (hL : Submodule.span ℝ (L : Set E) ≠ ⊥)
    (hb : ∀ i, ‖b i‖ ≤ β)
    (hintegral : ∀ i z, z ∈ L → ∃ k : ℤ, (k : ℝ) = inner ℝ (b i) z) :
    ∃ v : E, v ∈ latticeDual L ∧ v ≠ 0 ∧ ‖v‖ ≤ β := by
  obtain ⟨i, hi⟩ := exists_nonzero_basis_projection b _ hL
  exact ⟨_, projection_mem_latticeDual L (b i) (hintegral i), hi,
    (Submodule.norm_starProjection_apply_le _ (b i)).trans (hb i)⟩

/-- The coefficient-kernel part of Proposition 4.14, for the actual kernel
of every integer matrix with more columns than rows. -/
theorem exists_short_coefficientKernel_dual {R M : ℕ}
    (A : Matrix (Fin R) (Fin M) ℤ) (hRM : R < M) :
    ∃ v : Euclidean M, v ∈ latticeDual (euclideanKernel A) ∧ v ≠ 0 ∧ ‖v‖ ≤ 1 := by
  apply exists_short_dual_vector (euclideanKernel A)
    (EuclideanSpace.basisFun (Fin M) ℝ).toBasis (euclideanKernel_span_ne_bot A hRM)
  · intro i
    exact le_of_eq ((EuclideanSpace.basisFun (Fin M) ℝ).norm_eq_one i)
  · intro i z hz
    obtain ⟨w, hw, rfl⟩ := hz
    refine ⟨w i, ?_⟩
    change (w i : ℝ) = inner ℝ (EuclideanSpace.basisFun (Fin M) ℝ i) (integerEmbedding M w)
    rw [EuclideanSpace.basisFun_inner, integerEmbedding_apply]

end GeometricGaussianLHL
end

end ProjectedDual

section SmoothingLower

/-!
## The two-vector smoothing lower bound

The first inequality of Proposition 3.3 and the analytic step of Proposition
4.14. Passing to the real infimum explicitly requires a nonempty smoothing
set; existence for discrete lattices is a separate analytic obligation.
-/

open scoped ENNReal

noncomputable section

namespace GeometricGaussianLHL

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem two_weights_le_nonzeroDualMass (L : Submodule ℤ E) (t : ℝ)
    (v : latticeDual L) (hv : v ≠ 0) :
    ENNReal.ofReal (2 * gaussianWeight t (v : E)) ≤ nonzeroDualMass L t := by
  classical
  have hneg : v ≠ -v := by
    intro heq
    have hval : (v : E) = -(v : E) := congrArg Subtype.val heq
    have htwo : (2 : ℝ) • (v : E) = 0 := by
      rw [two_smul]
      nth_rw 1 [hval]
      exact neg_add_cancel _
    have hz : (v : E) = 0 := (smul_eq_zero.mp htwo).resolve_left (by norm_num)
    exact hv (Subtype.ext hz)
  have hsum := ENNReal.sum_le_tsum (f := fun w : latticeDual L =>
    if w = 0 then 0 else ENNReal.ofReal (gaussianWeight t (w : E))) {v, -v}
  simp only [Finset.sum_pair hneg, hv, ite_false, neg_ne_zero.mpr hv,
    Submodule.coe_neg, gaussianWeight_neg] at hsum
  rw [← ENNReal.ofReal_add (gaussianWeight_pos t (v : E)).le
    (gaussianWeight_pos t (v : E)).le] at hsum
  simpa only [two_mul, nonzeroDualMass] using hsum

theorem radius_le_of_two_gaussians_le {t β ε : ℝ} (ht : 0 ≤ t) (hβ : 0 < β)
    (hε : 0 < ε) (hbound : 2 * Real.exp (-Real.pi * t ^ 2 * β ^ 2) ≤ ε) :
    Real.sqrt (Real.log (2 / ε) / Real.pi) / β ≤ t := by
  have hpos : 0 < ε / 2 := by positivity
  have hexp : Real.exp (-Real.pi * t ^ 2 * β ^ 2) ≤ ε / 2 := by linarith
  have hlog : -Real.pi * t ^ 2 * β ^ 2 ≤ Real.log (ε / 2) :=
    (Real.le_log_iff_exp_le hpos).mpr hexp
  rw [Real.log_div hε.ne' (by norm_num : (2 : ℝ) ≠ 0)] at hlog
  apply (div_le_iff₀ hβ).mpr
  apply Real.sqrt_le_iff.mpr
  refine ⟨mul_nonneg ht hβ.le, ?_⟩
  apply (div_le_iff₀ Real.pi_pos).mpr
  rw [Real.log_div (by norm_num : (2 : ℝ) ≠ 0) hε.ne']
  nlinarith

theorem SmoothAt.lower_of_dual_vector {L : Submodule ℤ E} {ε t β : ℝ}
    (h : SmoothAt L ε t) (hε : 0 < ε) (hβ : 0 < β)
    (v : latticeDual L) (hv : v ≠ 0) (hnorm : ‖(v : E)‖ ≤ β) :
    Real.sqrt (Real.log (2 / ε) / Real.pi) / β ≤ t := by
  have hmass := (two_weights_le_nonzeroDualMass L t v hv).trans h.2
  have hweight : 2 * gaussianWeight t (v : E) ≤ ε :=
    (ENNReal.ofReal_le_ofReal_iff hε.le).mp hmass
  apply radius_le_of_two_gaussians_le h.1.le hβ hε
  have hsq : ‖(v : E)‖ ^ 2 ≤ β ^ 2 := by nlinarith [norm_nonneg (v : E)]
  have hmul := mul_le_mul_of_nonneg_left hsq (mul_nonneg Real.pi_pos.le (sq_nonneg t))
  have hexp : Real.exp (-Real.pi * t ^ 2 * β ^ 2) ≤ gaussianWeight t (v : E) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  linarith

theorem smoothingParameter_lower_of_dual_vector {L : Submodule ℤ E} {ε β : ℝ}
    (hexists : ∃ t, SmoothAt L ε t) (hε : 0 < ε) (hβ : 0 < β)
    (v : latticeDual L) (hv : v ≠ 0) (hnorm : ‖(v : E)‖ ≤ β) :
    Real.sqrt (Real.log (2 / ε) / Real.pi) / β ≤ smoothingParameter L ε := by
  apply le_csInf hexists
  intro t ht
  exact SmoothAt.lower_of_dual_vector ht hε hβ v hv hnorm

end GeometricGaussianLHL
end

end SmoothingLower

section KernelDual

/-!
## The intrinsic dual of an integer kernel

The kernel is a direct summand of the ambient integer module: the image of
an integer matrix is free over `ℤ`, hence projective. This allows an integer
functional on the kernel to extend to the ambient module and supplies the
reverse inclusion in Lemma 3.2.
-/

noncomputable section

namespace GeometricGaussianLHL

theorem exists_coefficientKernel_retraction {R M : ℕ}
    (A : Matrix (Fin R) (Fin M) ℤ) :
    ∃ p : Coeff M →ₗ[ℤ] coefficientKernel A, ∀ z : coefficientKernel A, p z = z := by
  let f := coefficientMap A
  obtain ⟨g, hg⟩ := f.rangeRestrict.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (by rintro ⟨y, z, rfl⟩; exact ⟨z, rfl⟩))
  let q : Coeff M →ₗ[ℤ] Coeff M := LinearMap.id - g.comp f.rangeRestrict
  have hq : ∀ z, q z ∈ coefficientKernel A := by
    intro z
    change f (z - g (f.rangeRestrict z)) = 0
    rw [map_sub]
    have h := congrArg Subtype.val (LinearMap.congr_fun hg (f.rangeRestrict z))
    change f (g (f.rangeRestrict z)) = f z at h
    rw [h, sub_self]
  refine ⟨q.codRestrict (coefficientKernel A) hq, ?_⟩
  intro z
  apply Subtype.ext
  change (z : Coeff M) - g (f.rangeRestrict z) = z
  have hz : f.rangeRestrict z = 0 := Subtype.ext z.property
  rw [hz, map_zero, sub_zero]

/-- Integer-valued linear functionals on the kernel extend integrally to
the whole coefficient module. -/
theorem coefficientKernel_functional_extends {R M : ℕ}
    (A : Matrix (Fin R) (Fin M) ℤ) (f : coefficientKernel A →ₗ[ℤ] ℤ) :
    ∃ g : Coeff M →ₗ[ℤ] ℤ, ∀ z : coefficientKernel A, g z = f z := by
  obtain ⟨p, hp⟩ := exists_coefficientKernel_retraction A
  exact ⟨f.comp p, fun z => by simp [hp]⟩

def coefficientKernelEmbeddingEquiv {R M : ℕ} (A : Matrix (Fin R) (Fin M) ℤ) :
    coefficientKernel A ≃ₗ[ℤ] euclideanKernel A :=
  Submodule.equivMapOfInjective (integerEmbedding M) (integerEmbedding_injective M)
    (coefficientKernel A)

@[simp] theorem coefficientKernelEmbeddingEquiv_apply {R M : ℕ}
    (A : Matrix (Fin R) (Fin M) ℤ) (z : coefficientKernel A) :
    (coefficientKernelEmbeddingEquiv A z : Euclidean M) = integerEmbedding M z := rfl

/-- Integral pairing with an intrinsic dual vector, as an integer linear map. -/
def dualIntegerFunctional {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (L : Submodule ℤ E) (v : latticeDual L) : L →ₗ[ℤ] ℤ :=
  LinearMap.BilinForm.dualSubmoduleToDual (innerₗ E) L ⟨v, v.property.2⟩

theorem dualIntegerFunctional_spec {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (L : Submodule ℤ E) (v : latticeDual L) (z : L) :
    (dualIntegerFunctional L v z : ℝ) = inner ℝ (v : E) (z : E) :=
  LinearMap.BilinForm.dualSubmoduleParing_spec (innerₗ E) ⟨v, v.property.2⟩ z

theorem integerEmbedding_inner {M : ℕ} (k z : Coeff M) :
    inner ℝ (integerEmbedding M k) (integerEmbedding M z) =
      ((∑ i, k i * z i : ℤ) : ℝ) := by
  simp [PiLp.inner_apply, integerEmbedding_apply, RCLike.inner_apply, mul_comm]

/-- The integer coefficients of an integer linear functional represent it
by the ordinary dot product. -/
theorem integer_functional_eq_dot {M : ℕ} (g : Coeff M →ₗ[ℤ] ℤ) (z : Coeff M) :
    ∑ i, g (Pi.basisFun ℤ (Fin M) i) * z i = g z := by
  calc
    ∑ i, g (Pi.basisFun ℤ (Fin M) i) * z i =
        ∑ i, g (z i • Pi.basisFun ℤ (Fin M) i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [g.map_smul]
      exact mul_comm _ _
    _ = g (∑ i, z i • Pi.basisFun ℤ (Fin M) i) := (map_sum g _ _).symm
    _ = g z := by
      congr 1
      simpa only [Pi.basisFun_repr] using (Pi.basisFun ℤ (Fin M)).sum_repr z

/-- The reverse inclusion in Lemma 3.2. No full-row-rank assumption is
required for the dual of the integer kernel. -/
theorem dual_kernel_vector_is_projection {R M : ℕ}
    (A : Matrix (Fin R) (Fin M) ℤ) (v : latticeDual (euclideanKernel A)) :
    ∃ k : Coeff M,
      (Submodule.span ℝ (euclideanKernel A : Set (Euclidean M))).starProjection
        (integerEmbedding M k) = v := by
  let e := coefficientKernelEmbeddingEquiv A
  let f := (dualIntegerFunctional (euclideanKernel A) v).comp e.toLinearMap
  obtain ⟨g, hg⟩ := coefficientKernel_functional_extends A f
  let k : Coeff M := fun i => g (Pi.basisFun ℤ (Fin M) i)
  have hpair : ∀ z ∈ euclideanKernel A,
      inner ℝ (integerEmbedding M k) z = inner ℝ (v : Euclidean M) z := by
    rintro z ⟨w, hw, rfl⟩
    rw [integerEmbedding_inner, integer_functional_eq_dot]
    have hi := congrArg (fun a : ℤ => (a : ℝ)) (hg ⟨w, hw⟩)
    rw [hi]
    exact dualIntegerFunctional_spec (euclideanKernel A) v (e ⟨w, hw⟩)
  refine ⟨k, Submodule.eq_starProjection_of_mem_of_inner_eq_zero v.property.1 ?_⟩
  have hspan : Submodule.span ℝ (euclideanKernel A : Set (Euclidean M)) ≤
      (innerₗ (Euclidean M) (integerEmbedding M k - (v : Euclidean M))).ker := by
    apply Submodule.span_le.mpr
    intro z hz
    change inner ℝ (integerEmbedding M k - (v : Euclidean M)) z = 0
    rw [inner_sub_left, hpair z hz, sub_self]
  intro z hz
  exact hspan hz

/-- Lemma 3.2's projected-dual identity for the actual Euclidean realization
of the coefficient kernel. -/
theorem mem_dual_kernel_iff_projection {R M : ℕ}
    (A : Matrix (Fin R) (Fin M) ℤ) (v : Euclidean M) :
    v ∈ latticeDual (euclideanKernel A) ↔
      ∃ k : Coeff M,
        (Submodule.span ℝ (euclideanKernel A : Set (Euclidean M))).starProjection
          (integerEmbedding M k) = v := by
  constructor
  · intro hv
    exact dual_kernel_vector_is_projection A ⟨v, hv⟩
  · rintro ⟨k, rfl⟩
    apply projection_mem_latticeDual
    rintro z ⟨w, hw, rfl⟩
    exact ⟨∑ i, k i * w i, (integerEmbedding_inner k w).symm⟩

end GeometricGaussianLHL
end

end KernelDual

section MetricChange

/-!
## Metric change in the intrinsic span

Pulling a dual vector back by an adjoint requires projection into the source
lattice's span. The resulting
map is injective and contracts norms by at most the operator norm of the
original map. Comparing the actual infinite Gaussian sums proves metric
transport at a certified smoothing parameter.
-/

noncomputable section

open scoped ENNReal

namespace GeometricGaussianLHL

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

def latticeImage (T : E →L[ℝ] F) (L : Submodule ℤ E) : Submodule ℤ F :=
  L.map (T.toLinearMap.restrictScalars ℤ)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem latticeImage_apply_mem (T : E →L[ℝ] F) (L : Submodule ℤ E)
    {z : E} (hz : z ∈ L) : T z ∈ latticeImage T L := ⟨z, hz, rfl⟩

omit [FiniteDimensional ℝ E] in
theorem eq_zero_of_span_pairing_zero (L : Submodule ℤ E) {v : E}
    (hv : v ∈ Submodule.span ℝ (L : Set E))
    (hpair : ∀ z ∈ L, inner ℝ v z = 0) : v = 0 := by
  have hspan : Submodule.span ℝ (L : Set E) ≤ (innerₗ E v).ker :=
    Submodule.span_le.mpr hpair
  exact (inner_self_eq_zero (𝕜 := ℝ)).mp (hspan hv)

theorem projected_adjoint_mem_dual (T : E →L[ℝ] F) (L : Submodule ℤ E)
    (y : latticeDual (latticeImage T L)) :
    (Submodule.span ℝ (L : Set E)).starProjection (T.adjoint y) ∈ latticeDual L := by
  apply projection_mem_latticeDual
  intro z hz
  obtain ⟨k, hk⟩ := (mem_latticeDual.mp y.property).2 (T z)
    (latticeImage_apply_mem T L hz)
  exact ⟨k, by rw [ContinuousLinearMap.adjoint_inner_left]; exact hk⟩

/-- The adjoint restricted to the intrinsic spans. -/
def dualPullback (T : E →L[ℝ] F) (L : Submodule ℤ E) :
    latticeDual (latticeImage T L) →ₗ[ℤ] latticeDual L :=
  (((Submodule.span ℝ (L : Set E)).starProjection.toLinearMap.restrictScalars ℤ).comp
    ((T.adjoint.toLinearMap.restrictScalars ℤ).comp
      (latticeDual (latticeImage T L)).subtype)).codRestrict _
        (projected_adjoint_mem_dual T L)

@[simp] theorem dualPullback_coe (T : E →L[ℝ] F) (L : Submodule ℤ E)
    (y : latticeDual (latticeImage T L)) :
    (dualPullback T L y : E) =
      (Submodule.span ℝ (L : Set E)).starProjection (T.adjoint y) := rfl

theorem dualPullback_inner (T : E →L[ℝ] F) (L : Submodule ℤ E)
    (y : latticeDual (latticeImage T L)) {z : E} (hz : z ∈ L) :
    inner ℝ (dualPullback T L y : E) z = inner ℝ (y : F) (T z) := by
  rw [dualPullback_coe, Submodule.inner_starProjection_left_eq_right,
    (Submodule.span ℝ (L : Set E)).starProjection_eq_self_iff.mpr
      (Submodule.subset_span hz), ContinuousLinearMap.adjoint_inner_left]

theorem dualPullback_injective (T : E →L[ℝ] F) (L : Submodule ℤ E) :
    Function.Injective (dualPullback T L) := by
  intro y w h
  apply Subtype.ext
  apply sub_eq_zero.mp
  apply eq_zero_of_span_pairing_zero (latticeImage T L)
    (Submodule.sub_mem _ y.property.1 w.property.1)
  rintro z ⟨x, hx, rfl⟩
  change inner ℝ ((y : F) - (w : F)) (T x) = 0
  rw [inner_sub_left, ← dualPullback_inner T L y hx, ← dualPullback_inner T L w hx, h,
    sub_self]

theorem norm_dualPullback_le (T : E →L[ℝ] F) (L : Submodule ℤ E)
    (y : latticeDual (latticeImage T L)) :
    ‖(dualPullback T L y : E)‖ ≤ ‖T‖ * ‖(y : F)‖ := by
  calc
    ‖(dualPullback T L y : E)‖ ≤ ‖T.adjoint y‖ :=
      Submodule.norm_starProjection_apply_le _ _
    _ ≤ ‖T.adjoint‖ * ‖(y : F)‖ := T.adjoint.le_opNorm _
    _ = ‖T‖ * ‖(y : F)‖ := by rw [LinearIsometryEquiv.norm_map]

/-- Corrected canonical-dual identity. The ambient inverse
adjoint is followed by projection into the image lattice's real span. -/
theorem mem_dual_image_iff_projected_inverse_adjoint (T : E ≃L[ℝ] F)
    (L : Submodule ℤ E) (y : F) :
    y ∈ latticeDual (latticeImage T.toContinuousLinearMap L) ↔
      ∃ v ∈ latticeDual L,
        (Submodule.span ℝ (latticeImage T.toContinuousLinearMap L : Set F)).starProjection
          (T.symm.toContinuousLinearMap.adjoint v) = y := by
  constructor
  · intro hy
    let v := dualPullback T.toContinuousLinearMap L ⟨y, hy⟩
    refine ⟨v, v.property,
      Submodule.eq_starProjection_of_mem_of_inner_eq_zero hy.1 ?_⟩
    have hspan : Submodule.span ℝ (latticeImage T.toContinuousLinearMap L : Set F) ≤
        (innerₗ F (T.symm.toContinuousLinearMap.adjoint v - y)).ker := by
      apply Submodule.span_le.mpr
      rintro w ⟨z, hz, rfl⟩
      change inner ℝ (T.symm.toContinuousLinearMap.adjoint v - y) (T z) = 0
      rw [inner_sub_left, ContinuousLinearMap.adjoint_inner_left]
      change inner ℝ (v : E) (T.symm (T z)) - inner ℝ y (T z) = 0
      rw [T.symm_apply_apply, dualPullback_inner T.toContinuousLinearMap L ⟨y, hy⟩ hz]
      exact sub_self _
    exact fun z hz => hspan hz
  · rintro ⟨v, hv, rfl⟩
    apply projection_mem_latticeDual
    rintro w ⟨z, hz, rfl⟩
    obtain ⟨k, hk⟩ := (mem_latticeDual.mp hv).2 z hz
    refine ⟨k, ?_⟩
    change (k : ℝ) = inner ℝ (T.symm.toContinuousLinearMap.adjoint v) (T z)
    rw [ContinuousLinearMap.adjoint_inner_left]
    simpa only [ContinuousLinearEquiv.coe_coe, T.symm_apply_apply] using hk

theorem gaussianWeight_metric_change (T : E →L[ℝ] F) (L : Submodule ℤ E)
    (t : ℝ) (y : latticeDual (latticeImage T L)) :
    gaussianWeight (‖T‖ * t) (y : F) ≤ gaussianWeight t (dualPullback T L y : E) := by
  apply Real.exp_le_exp.mpr
  have hsq := sq_le_sq₀ (norm_nonneg (dualPullback T L y : E))
    (mul_nonneg (norm_nonneg T) (norm_nonneg (y : F))) |>.mpr
      (norm_dualPullback_le T L y)
  have h := mul_le_mul_of_nonneg_left hsq (mul_nonneg Real.pi_pos.le (sq_nonneg t))
  change -Real.pi * (‖T‖ * t) ^ 2 * ‖(y : F)‖ ^ 2 ≤
    -Real.pi * t ^ 2 * ‖(dualPullback T L y : E)‖ ^ 2
  nlinarith

/-- Termwise comparison after an injective reindexing. No convergence premise
is needed because the sums take values in `ℝ≥0∞`. -/
theorem nonzeroDualMass_metric_change (T : E →L[ℝ] F) (L : Submodule ℤ E) (t : ℝ) :
    nonzeroDualMass (latticeImage T L) (‖T‖ * t) ≤ nonzeroDualMass L t := by
  classical
  let f : latticeDual L → ℝ≥0∞ :=
    fun v => if v = 0 then 0 else ENNReal.ofReal (gaussianWeight t (v : E))
  calc
    nonzeroDualMass (latticeImage T L) (‖T‖ * t) ≤
        ∑' y : latticeDual (latticeImage T L), f (dualPullback T L y) := by
      apply ENNReal.tsum_le_tsum
      intro y
      by_cases hy : y = 0
      · simp [hy, f]
      · have hp : dualPullback T L y ≠ 0 := by
          intro h
          apply hy
          apply dualPullback_injective T L
          simpa only [map_zero] using h
        simp only [hy, hp, ite_false, f]
        exact ENNReal.ofReal_le_ofReal (gaussianWeight_metric_change T L t y)
    _ ≤ ∑' v, f v := ENNReal.tsum_comp_le_tsum_of_injective
      (dualPullback_injective T L) f
    _ = nonzeroDualMass L t := rfl

theorem SmoothAt.metric_change {L : Submodule ℤ E} {ε t : ℝ}
    (h : SmoothAt L ε t) (T : E →L[ℝ] F) (hT : T ≠ 0) :
    SmoothAt (latticeImage T L) ε (‖T‖ * t) :=
  ⟨mul_pos (norm_pos_iff.mpr hT) h.1, (nonzeroDualMass_metric_change T L t).trans h.2⟩

/-- The infimum inequality for any subgroup with a nonempty smoothing set.
The `SmoothingExistence` section of `GaussianAnalysis.lean` discharges that premise for discrete lattices. -/
theorem smoothingParameter_metric_change (T : E →L[ℝ] F) (hT : T ≠ 0)
    (L : Submodule ℤ E) (ε : ℝ) (hex : ∃ t, SmoothAt L ε t) :
    smoothingParameter (latticeImage T L) ε ≤ ‖T‖ * smoothingParameter L ε := by
  have hn : 0 < ‖T‖ := norm_pos_iff.mpr hT
  have hdiv : smoothingParameter (latticeImage T L) ε / ‖T‖ ≤
      smoothingParameter L ε := by
    apply le_csInf hex
    intro t ht
    apply (div_le_iff₀ hn).mpr
    simpa only [mul_comm] using
      smoothingParameter_le_of_smoothAt (SmoothAt.metric_change ht T hT)
  exact (div_le_iff₀ hn).mp hdiv |>.trans_eq (mul_comm _ _)

end GeometricGaussianLHL
end

end MetricChange

section RealKernel

/-!
## Integer and real kernels

Discreteness identifies the integer rank of each coefficient submodule with
the real dimension of its span. Rank-nullity then proves that the real span
of the integer kernel is exactly the kernel of the real coefficient matrix.
This supplies the subspace appearing in Lemma 3.2's projection formula.
-/

noncomputable section

namespace GeometricGaussianLHL

def integerLattice (M : ℕ) : Submodule ℤ (Euclidean M) := (integerEmbedding M).range

theorem integerEmbedding_basis (M : ℕ) (i : Fin M) :
    integerEmbedding M (Pi.basisFun ℤ (Fin M) i) = EuclideanSpace.basisFun (Fin M) ℝ i := by
  classical
  ext j
  simp [Pi.basisFun_apply, EuclideanSpace.basisFun_apply, Pi.single_apply,
    PiLp.single_apply, apply_ite]

theorem integerLattice_eq_basis_span (M : ℕ) :
    integerLattice M = Submodule.span ℤ (Set.range (EuclideanSpace.basisFun (Fin M) ℝ)) := by
  rw [integerLattice, ← Submodule.map_top, ← (Pi.basisFun ℤ (Fin M)).span_eq,
    Submodule.map_span, ← Set.range_comp]
  congr 1
  exact congrArg Set.range (funext (integerEmbedding_basis M))

instance integerLattice_discreteTopology (M : ℕ) : DiscreteTopology (integerLattice M) := by
  rw [integerLattice_eq_basis_span]
  exact inferInstanceAs (DiscreteTopology
    (Submodule.span ℤ (Set.range (EuclideanSpace.basisFun (Fin M) ℝ).toBasis)))

theorem integerLattice_span (M : ℕ) :
    Submodule.span ℝ (integerLattice M : Set (Euclidean M)) = ⊤ := by
  rw [integerLattice_eq_basis_span, Submodule.span_span_of_tower]
  exact (EuclideanSpace.basisFun (Fin M) ℝ).toBasis.span_eq

theorem integerEmbedding_map_discreteTopology {M : ℕ} (p : Submodule ℤ (Coeff M)) :
    DiscreteTopology (p.map (integerEmbedding M)) := by
  let f : p.map (integerEmbedding M) → integerLattice M :=
    fun z => ⟨z, by obtain ⟨x, _, hx⟩ := z.property; exact ⟨x, hx⟩⟩
  apply DiscreteTopology.of_continuous_injective (f := f)
  · exact continuous_subtype_val.subtype_mk _
  · intro x y h
    exact Subtype.ext (congrArg (fun z : integerLattice M => (z : Euclidean M)) h)

theorem integerEmbedding_span_finrank {M : ℕ} (p : Submodule ℤ (Coeff M)) :
    Module.finrank ℝ (Submodule.span ℝ (p.map (integerEmbedding M) : Set (Euclidean M))) =
      Module.finrank ℤ p := by
  have hd := integerEmbedding_map_discreteTopology p
  have h := Real.finrank_eq_int_finrank_of_discrete
    (s := (p.map (integerEmbedding M) : Set (Euclidean M))) (by
      rw [Submodule.span_eq]; exact hd)
  change Module.finrank ℝ (Submodule.span ℝ _) = Module.finrank ℤ (Submodule.span ℤ _) at h
  rw [Submodule.span_eq] at h
  exact h.trans (Submodule.equivMapOfInjective (integerEmbedding M)
    (integerEmbedding_injective M) p).finrank_eq.symm

def realCoefficientMap {R M : ℕ} (A : Matrix (Fin R) (Fin M) ℤ) :
    Euclidean M →ₗ[ℝ] Euclidean R := Matrix.toLpLin 2 2 (A.map Int.cast)

theorem realCoefficientMap_integerEmbedding {R M : ℕ}
    (A : Matrix (Fin R) (Fin M) ℤ) (z : Coeff M) :
    realCoefficientMap A (integerEmbedding M z) = integerEmbedding R (coefficientMap A z) := by
  ext i
  simp [realCoefficientMap, Matrix.toLpLin_apply, coefficientMap,
    Matrix.mulVec, dotProduct, integerEmbedding_apply]

theorem integer_image_real_image {R M : ℕ} (A : Matrix (Fin R) (Fin M) ℤ) :
    (realCoefficientMap A) '' (integerLattice M : Set (Euclidean M)) =
      ((coefficientMap A).range.map (integerEmbedding R) : Set (Euclidean R)) := by
  ext y
  constructor
  · rintro ⟨x, ⟨z, rfl⟩, rfl⟩
    exact ⟨coefficientMap A z, ⟨z, rfl⟩, (realCoefficientMap_integerEmbedding A z).symm⟩
  · rintro ⟨x, ⟨z, rfl⟩, rfl⟩
    exact ⟨integerEmbedding M z, ⟨z, rfl⟩, realCoefficientMap_integerEmbedding A z⟩

theorem realCoefficientMap_range {R M : ℕ} (A : Matrix (Fin R) (Fin M) ℤ) :
    (realCoefficientMap A).range = Submodule.span ℝ
      ((coefficientMap A).range.map (integerEmbedding R) : Set (Euclidean R)) := by
  rw [← integer_image_real_image, Submodule.span_image, integerLattice_span, Submodule.map_top]

/-- The integer kernel spans the full kernel over the reals, including
rank-deficient matrices. -/
theorem euclideanKernel_span_eq_real_ker {R M : ℕ} (A : Matrix (Fin R) (Fin M) ℤ) :
    Submodule.span ℝ (euclideanKernel A : Set (Euclidean M)) = (realCoefficientMap A).ker := by
  have hle : Submodule.span ℝ (euclideanKernel A : Set (Euclidean M)) ≤
      (realCoefficientMap A).ker := by
    apply Submodule.span_le.mpr
    rintro x ⟨z, hz, rfl⟩
    change realCoefficientMap A (integerEmbedding M z) = 0
    rw [realCoefficientMap_integerEmbedding, show coefficientMap A z = 0 from hz, map_zero]
  have hi := (coefficientMap A).ker.finrank_quotient_add_finrank
  rw [(coefficientMap A).quotKerEquivRange.finrank_eq] at hi
  have hr := (realCoefficientMap A).finrank_range_add_finrank_ker
  rw [realCoefficientMap_range, integerEmbedding_span_finrank] at hr
  have hk := integerEmbedding_span_finrank (coefficientKernel A)
  apply Submodule.eq_of_le_of_finrank_eq hle
  simp only [Coeff, Module.finrank_pi, Fintype.card_fin] at hi
  simp only [Euclidean, finrank_euclideanSpace, Fintype.card_fin] at hr
  change Module.finrank ℝ (Submodule.span ℝ (euclideanKernel A : Set (Euclidean M))) = _ at hk
  change Module.finrank ℤ (coefficientMap A).range + Module.finrank ℤ (coefficientKernel A) = M at hi
  have heq : Module.finrank ℤ (coefficientKernel A) =
      Module.finrank ℝ (realCoefficientMap A).ker := by
    exact Nat.add_left_cancel (hi.trans hr.symm)
  exact hk.trans heq

/-- Lemma 3.2, with projection onto the kernel of the actual real matrix. -/
theorem mem_dual_kernel_iff_real_projection {R M : ℕ}
    (A : Matrix (Fin R) (Fin M) ℤ) (v : Euclidean M) :
    v ∈ latticeDual (euclideanKernel A) ↔
      ∃ k : Coeff M, (realCoefficientMap A).ker.starProjection (integerEmbedding M k) = v := by
  rw [mem_dual_kernel_iff_projection, euclideanKernel_span_eq_real_ker]

theorem realCoefficientMap_transpose {R M : ℕ} (A : Matrix (Fin R) (Fin M) ℤ) :
    realCoefficientMap A.transpose = (realCoefficientMap A).adjoint := by
  unfold realCoefficientMap
  rw [show A.transpose.map (Int.cast : ℤ → ℝ) = (A.map (Int.cast : ℤ → ℝ)).conjTranspose by
    ext i j; simp]
  exact Matrix.toEuclideanLin_conjTranspose_eq_adjoint _

theorem realCoefficientMap_ker_orthogonal {R M : ℕ}
    (A : Matrix (Fin R) (Fin M) ℤ) :
    (realCoefficientMap A).kerᗮ = (realCoefficientMap A.transpose).range := by
  rw [LinearMap.orthogonal_ker, realCoefficientMap_transpose]

/-- Both descriptions in Lemma 3.2: an intrinsic dual vector lies in the real
kernel and is an integer vector plus a vector in the transpose's range. -/
theorem mem_dual_kernel_iff_integer_add_transpose {R M : ℕ}
    (A : Matrix (Fin R) (Fin M) ℤ) (v : Euclidean M) :
    v ∈ latticeDual (euclideanKernel A) ↔
      v ∈ (realCoefficientMap A).ker ∧
        ∃ k : Coeff M, ∃ y : Euclidean R,
          v = integerEmbedding M k + realCoefficientMap A.transpose y := by
  constructor
  · intro hv
    obtain ⟨k, hk⟩ := (mem_dual_kernel_iff_real_projection A v).mp hv
    have hdiff : v - integerEmbedding M k ∈ (realCoefficientMap A.transpose).range := by
      rw [← realCoefficientMap_ker_orthogonal]
      have h := Submodule.sub_starProjection_mem_orthogonal
        (K := (realCoefficientMap A).ker) (integerEmbedding M k)
      rw [hk] at h
      simpa only [neg_sub] using (realCoefficientMap A).kerᗮ.neg_mem h
    obtain ⟨y, hy⟩ := hdiff
    refine ⟨euclideanKernel_span_eq_real_ker A ▸ hv.1, k, y, ?_⟩
    rw [hy]
    abel
  · rintro ⟨hv, k, y, hrep⟩
    apply (mem_dual_kernel_iff_real_projection A v).mpr
    refine ⟨k, Submodule.eq_starProjection_of_mem_orthogonal hv ?_⟩
    rw [realCoefficientMap_ker_orthogonal, hrep]
    have h : -(realCoefficientMap A.transpose y) ∈ (realCoefficientMap A.transpose).range :=
      (realCoefficientMap A.transpose).range.neg_mem ⟨y, rfl⟩
    convert h using 1
    abel

end GeometricGaussianLHL
end

end RealKernel

section ImageRank

/-!
## Full row rank and finite image index

Full row rank over the reals is equivalent to finite index of the image over
the integers. It does not imply that this index is one. This removes the
separate finite-quotient hypothesis from the index-extraction step used with
Proposition 4.1.
-/

noncomputable section

namespace GeometricGaussianLHL

theorem finite_coefficientImage_quotient_iff_real_surjective {R M : ℕ}
    (A : Matrix (Fin R) (Fin M) ℤ) :
    Finite ((Coeff R) ⧸ coefficientImage A) ↔ Function.Surjective (realCoefficientMap A) := by
  change Finite ((Coeff R) ⧸ (coefficientMap A).range) ↔ _
  rw [Submodule.finiteQuotient_iff]
  constructor
  · intro h
    apply LinearMap.range_eq_top.mp
    apply Submodule.eq_top_of_finrank_eq
    rw [realCoefficientMap_range, integerEmbedding_span_finrank, h]
    simp [Coeff, Euclidean]
  · intro h
    have hr : Module.finrank ℝ (realCoefficientMap A).range = R := by
      rw [LinearMap.range_eq_top.mpr h]
      simp [Euclidean]
    rw [realCoefficientMap_range, integerEmbedding_span_finrank] at hr
    simpa [Coeff] using hr

theorem imageIndex_pos_of_real_surjective {R M : ℕ}
    (A : Matrix (Fin R) (Fin M) ℤ) (hA : Function.Surjective (realCoefficientMap A)) :
    0 < imageIndex A := by
  let := (finite_coefficientImage_quotient_iff_real_surjective A).mpr hA
  exact imageIndex_pos A

/-- The finite-index assumption is obtained from the same real full-row-rank
hypothesis used in the theta integral. -/
theorem surjective_and_smoothAt_of_full_rank_mass_bound {R M : ℕ}
    (A : Matrix (Fin R) (Fin M) ℤ) (hA : Function.Surjective (realCoefficientMap A))
    {ε t : ℝ} (ht : 0 < t) (hε : ε < 1)
    (hbound : (imageIndex A : ENNReal) * dualMass (euclideanKernel A) t ≤
      1 + ENNReal.ofReal ε) :
    Function.Surjective (coefficientMap A) ∧ SmoothAt (euclideanKernel A) ε t := by
  let := (finite_coefficientImage_quotient_iff_real_surjective A).mpr hA
  exact surjective_and_smoothAt_of_index_mass_bound A ht hε hbound

end GeometricGaussianLHL
end

end ImageRank

section IntegerFactorization

/-!
## Factoring out the integer image

A full-row-rank integer matrix factors as `C B`, where `B` is surjective
over the integers and `C` is a square injective integer matrix. The finite
image index is the absolute determinant of `C`.
-/

noncomputable section

namespace GeometricGaussianLHL

theorem coefficientMap_mul {R N M : ℕ} (C : Matrix (Fin R) (Fin N) ℤ)
    (B : Matrix (Fin N) (Fin M) ℤ) :
    coefficientMap (C * B) = (coefficientMap C).comp (coefficientMap B) := Matrix.toLin'_mul _ _

theorem coefficientImage_mul {R N M : ℕ} (C : Matrix (Fin R) (Fin N) ℤ)
    (B : Matrix (Fin N) (Fin M) ℤ) :
    coefficientImage (C * B) = (coefficientImage B).map (coefficientMap C).toAddMonoidHom := by
  unfold coefficientImage
  rw [coefficientMap_mul, LinearMap.range_comp]
  rfl

theorem coefficientImage_mul_of_surjective {R N M : ℕ} (C : Matrix (Fin R) (Fin N) ℤ)
    (B : Matrix (Fin N) (Fin M) ℤ) (hB : Function.Surjective (coefficientMap B)) :
    coefficientImage (C * B) = coefficientImage C := by
  unfold coefficientImage
  rw [coefficientMap_mul, LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr hB)]

theorem imageIndex_mul_of_surjective {R N M : ℕ} (C : Matrix (Fin R) (Fin N) ℤ)
    (B : Matrix (Fin N) (Fin M) ℤ) (hB : Function.Surjective (coefficientMap B)) :
    imageIndex (C * B) = imageIndex C := by
  rw [imageIndex, coefficientImage_mul_of_surjective C B hB]
  rfl

/-- The index of the range of an injective square integer matrix. -/
theorem imageIndex_square_eq_natAbs_det {R : ℕ} (C : Matrix (Fin R) (Fin R) ℤ)
    (hC : Function.Injective (coefficientMap C)) : imageIndex C = C.det.natAbs := by
  have h := Submodule.natAbs_det_equiv (coefficientMap C).range
    (LinearEquiv.ofInjective (coefficientMap C) hC)
  change (coefficientMap C).det.natAbs = Nat.card (Coeff R ⧸ (coefficientMap C).range) at h
  rw [coefficientMap, LinearMap.det_toLin'] at h
  exact h.symm

/-- A basis of the image gives the factorization without changing its index. -/
theorem exists_integer_image_factorization {R M : ℕ} (A : Matrix (Fin R) (Fin M) ℤ)
    (hA : Function.Surjective (realCoefficientMap A)) :
    ∃ C : Matrix (Fin R) (Fin R) ℤ, ∃ B : Matrix (Fin R) (Fin M) ℤ,
      A = C * B ∧ Function.Surjective (coefficientMap B) ∧ Function.Injective (coefficientMap C) := by
  let f := coefficientMap A
  have hf : Finite (Coeff R ⧸ f.range) :=
    (finite_coefficientImage_quotient_iff_real_surjective A).mpr hA
  have hrank : Module.finrank ℤ f.range = R := by
    have h := (Submodule.finiteQuotient_iff f.range).mp hf
    simpa only [Coeff, Module.finrank_pi, Fintype.card_fin] using h
  let b := Module.finBasisOfFinrankEq ℤ f.range hrank
  let c : Coeff R →ₗ[ℤ] Coeff R := f.range.subtype.comp b.equivFun.symm.toLinearMap
  let d : Coeff M →ₗ[ℤ] Coeff R := b.equivFun.toLinearMap.comp f.rangeRestrict
  have hc : Function.Injective c := Subtype.val_injective.comp b.equivFun.symm.injective
  have hd : Function.Surjective d := b.equivFun.surjective.comp f.surjective_rangeRestrict
  have hcomp : c.comp d = f := by
    apply LinearMap.ext
    intro x
    change (b.equivFun.symm (b.equivFun (f.rangeRestrict x)) : Coeff R) = f x
    rw [b.equivFun.symm_apply_apply]
    rfl
  refine ⟨LinearMap.toMatrix' c, LinearMap.toMatrix' d, ?_, ?_, ?_⟩
  · apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', Matrix.toLin'_toMatrix']
    exact hcomp.symm
  · simpa only [coefficientMap, Matrix.toLin'_toMatrix'] using hd
  · simpa only [coefficientMap, Matrix.toLin'_toMatrix'] using hc

/-- Surjectivity over the integers gives an integer matrix right inverse. -/
theorem exists_integer_right_inverse {R M : ℕ} (B : Matrix (Fin R) (Fin M) ℤ)
    (hB : Function.Surjective (coefficientMap B)) :
    ∃ D : Matrix (Fin M) (Fin R) ℤ, B * D = 1 := by
  obtain ⟨g, hg⟩ := (coefficientMap B).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hB)
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', Matrix.toLin'_one]
  exact hg

theorem coefficientMap_square_injective_iff_det_ne_zero {R : ℕ}
    (C : Matrix (Fin R) (Fin R) ℤ) :
    Function.Injective (coefficientMap C) ↔ C.det ≠ 0 := by
  simpa only [coefficientMap, LinearMap.det_toLin', not_not, LinearMap.ker_eq_bot] using
    (LinearMap.det_eq_zero_iff_ker_ne_bot (f := coefficientMap C)).not.symm

theorem imageIndex_transpose_square {R : ℕ} (C : Matrix (Fin R) (Fin R) ℤ)
    (hC : Function.Injective (coefficientMap C)) : imageIndex C.transpose = imageIndex C := by
  have hCt : Function.Injective (coefficientMap C.transpose) :=
    (coefficientMap_square_injective_iff_det_ne_zero C.transpose).mpr
      (by simpa using (coefficientMap_square_injective_iff_det_ne_zero C).mp hC)
  rw [imageIndex_square_eq_natAbs_det _ hCt, imageIndex_square_eq_natAbs_det _ hC, Matrix.det_transpose]

theorem realCoefficientMap_square_surjective_of_injective {R : ℕ}
    (C : Matrix (Fin R) (Fin R) ℤ) (hC : Function.Injective (coefficientMap C)) :
    Function.Surjective (realCoefficientMap C) := by
  apply (finite_coefficientImage_quotient_iff_real_surjective C).mp
  change Finite (Coeff R ⧸ (coefficientMap C).range)
  apply (Submodule.finiteQuotient_iff _).mpr
  exact (LinearEquiv.ofInjective (coefficientMap C) hC).finrank_eq.symm

theorem realCoefficientMap_surjective_of_integer_surjective {R M : ℕ}
    (B : Matrix (Fin R) (Fin M) ℤ) (hB : Function.Surjective (coefficientMap B)) :
    Function.Surjective (realCoefficientMap B) := by
  apply LinearMap.range_eq_top.mp
  rw [realCoefficientMap_range, LinearMap.range_eq_top.mpr hB, Submodule.map_top]
  exact integerLattice_span R

theorem realCoefficientMap_mul {R N M : ℕ} (C : Matrix (Fin R) (Fin N) ℤ)
    (B : Matrix (Fin N) (Fin M) ℤ) :
    realCoefficientMap (C * B) = (realCoefficientMap C).comp (realCoefficientMap B) := by
  have h : (C * B).map (Int.cast : ℤ → ℝ) =
      C.map (Int.cast : ℤ → ℝ) * B.map (Int.cast : ℤ → ℝ) := by
    ext i j
    simp [Matrix.mul_apply]
  unfold realCoefficientMap
  rw [h, Matrix.toLpLin_mul 2 2 2]

@[simp] theorem realCoefficientMap_one (R : ℕ) :
    realCoefficientMap (1 : Matrix (Fin R) (Fin R) ℤ) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  ext i
  simp [realCoefficientMap]

end GeometricGaussianLHL
end

end IntegerFactorization
