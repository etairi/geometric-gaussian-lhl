import «SIS-to-kSIS».FiniteSampling
import «SIS-to-kSIS».GaussianWidths
import «SIS-to-kSIS».BlockAlgebra

/-!
# Coordinate factorizations and sequential Gaussian sampling laws

The independent ring-coordinate description identifies the spherical matrix law and the
diagonal-width column law used by the reduction games. Sequential Gaussian laws have an exact
product mass, explicit normalizer-bias bounds, and a proved adaptive hybrid bound for the finite
scalar samplers. Stored rational Schur elimination has verified exact covariance factorization and
pivot lower bounds. Its triangular Gaussian target equals the existing ellipsoidal law. Uniform
polynomial bounds control the exact factorization’s intermediate rational sizes, stored output
sizes, and accumulated declared costs. Stored prefix centers have exact values, polynomial costs,
and additive output-size bounds. The stored adaptive run realizes the sequential law. Its
composition with exact rational factorization samples the coefficient ellipsoidal Gaussian within
the supplied error budget, with polynomial costs and output lengths bounded by the original
covariance input. In a scalar-Gram integral basis, the computed rational shape gives an exact
coefficient covariance and a finite number-field sampler. Its error and width margins match the
spectral hint-generator lemma; a bounded rank check, rational shaping, and identity fallback compose
into a stored column sampler with polynomial cost on every encoded input. Supplied basis
multiplication tables prepare the exact coefficient matrices from initial samples. Shared shaping
and finite conditional tapes generate both hint blocks, with polynomial arithmetic costs and output
sizes. Stored ring multiplication, block assembly, and modular reduction then construct the
adversary inputs and cache the exact extraction matrix, with uniform polynomial declared costs.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Module NumberField GeometricGaussianLHL

namespace SISToKSIS

variable (K : Type*) [Field K] [NumberField K] {d n m : ℕ}

local instance factorAmbientInner : InnerProductSpace ℝ (CanonicalAmbient K) := inferInstance
local instance factorSpaceInner : InnerProductSpace ℝ (canonicalSpace K) := inferInstance
local instance factorPowerInner (n : ℕ) : InnerProductSpace ℝ (CanonicalPower K n) := inferInstance

def ringGaussianWeight (s : ℝ) (x : 𝓞 K) : ℝ :=
  gaussianWeight (1 / s) (canonicalIntegerEmbedding K x)

theorem ringGaussianWeight_pos (s : ℝ) (x : 𝓞 K) : 0 < ringGaussianWeight K s x :=
  gaussianWeight_pos _ _

theorem numberFieldGaussianWeight_product (s : ℝ) (x : Fin n → 𝓞 K) :
    numberFieldGaussianWeight K n s x = ∏ i, ringGaussianWeight K s (x i) := by
  simp only [numberFieldGaussianWeight, gaussianWeight, PiLp.norm_sq_eq_of_L2,
    canonicalPowerEmbedding_apply, Finset.mul_sum, Real.exp_sum, ringGaussianWeight]

theorem numberFieldGaussianWeight_one (s : ℝ) (x : 𝓞 K) :
    numberFieldGaussianWeight K 1 s (fun _ => x) = ringGaussianWeight K s x := by
  simp [numberFieldGaussianWeight_product]

theorem summable_ringGaussianWeight (b : Basis (Fin d) ℤ (𝓞 K)) (s : ℝ) (hs : s ≠ 0) :
    Summable (ringGaussianWeight K s) := by
  have h := (summable_numberFieldGaussianWeight K b 1 s hs).comp_injective
    (Equiv.funUnique (Fin 1) (𝓞 K)).symm.injective
  change Summable (fun x : 𝓞 K => numberFieldGaussianWeight K 1 s (fun _ => x)) at h
  exact h.congr (numberFieldGaussianWeight_one K s)

def ringGaussianPartition (s : ℝ) : ℝ := ∑' x, ringGaussianWeight K s x

theorem ringGaussianPartition_pos (b : Basis (Fin d) ℤ (𝓞 K)) (s : ℝ) (hs : s ≠ 0) :
    0 < ringGaussianPartition K s :=
  (gaussianWeight_pos _ _).trans_le
    ((summable_ringGaussianWeight K b s hs).le_tsum 0 (fun _ _ => (gaussianWeight_pos _ _).le))

theorem numberFieldGaussianPartition_product (b : Basis (Fin d) ℤ (𝓞 K))
    (s : ℝ) (hs : s ≠ 0) :
    numberFieldGaussianPartition K n s = ringGaussianPartition K s ^ n := by
  unfold numberFieldGaussianPartition
  simp_rw [numberFieldGaussianWeight_product]
  rw [tsum_finite_product_real (fun _ : Fin n => ringGaussianWeight K s)
    (fun _ _ => (gaussianWeight_pos _ _).le) (fun _ => summable_ringGaussianWeight K b s hs)]
  simp only [ringGaussianPartition, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

def ringGaussian (b : Basis (Fin d) ℤ (𝓞 K)) (s : ℝ) (hs : s ≠ 0) : PMF (𝓞 K) :=
  (numberFieldGaussian K b 1 s hs).map (Equiv.funUnique (Fin 1) (𝓞 K))

theorem ringGaussian_apply (b : Basis (Fin d) ℤ (𝓞 K)) (s : ℝ) (hs : s ≠ 0) (x : 𝓞 K) :
    ringGaussian K b s hs x = ENNReal.ofReal (ringGaussianWeight K s x / ringGaussianPartition K s) := by
  have h := pmf_map_equiv_apply (numberFieldGaussian K b 1 s hs)
    (Equiv.funUnique (Fin 1) (𝓞 K)) (fun _ => x)
  change ringGaussian K b s hs x = _ at h
  rw [h, numberFieldGaussian_apply, numberFieldGaussianWeight_one,
    numberFieldGaussianPartition_product K b s hs, pow_one]

theorem numberFieldGaussian_independent_coordinates (b : Basis (Fin d) ℤ (𝓞 K))
    (s : ℝ) (hs : s ≠ 0) :
    numberFieldGaussian K b n s hs = independentProduct (fun _ : Fin n => ringGaussian K b s hs) := by
  ext x
  simp only [numberFieldGaussian_apply, numberFieldGaussianWeight_product,
    numberFieldGaussianPartition_product K b s hs, independentProduct_apply, ringGaussian_apply]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => div_nonneg (ringGaussianWeight_pos K s (x i)).le
    (ringGaussianPartition_pos K b s hs).le), Finset.prod_div_distrib]
  simp

theorem canonicalDiagonalShape_weight (b : Basis (Fin d) ℤ (𝓞 K))
    (w : Fin n → ℝ) (hw : ∀ i, w i ≠ 0) (x : Fin n → 𝓞 K) :
    gaussianWeight 1 ((canonicalDiagonalShape K b w hw).symm
      (canonicalEuclideanEmbedding K b n x)) = ∏ i, ringGaussianWeight K (w i) (x i) := by
  change gaussianWeight 1 ((canonicalDiagonalShape K b w hw).symm
    (canonicalOrthonormalCoordinates K b n (canonicalPowerEmbedding K n x))) = _
  rw [canonicalDiagonalShape_symm_coordinates]
  simp only [gaussianWeight, LinearIsometryEquiv.norm_map, PiLp.norm_sq_eq_of_L2,
    canonicalDiagonalEquiv_symm_apply, canonicalPowerEmbedding_apply, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs, Finset.mul_sum, Real.exp_sum, ringGaussianWeight,
    one_pow, mul_one, one_div, mul_assoc]

theorem canonicalDiagonalShape_partition (b : Basis (Fin d) ℤ (𝓞 K))
    (w : Fin n → ℝ) (hw : ∀ i, w i ≠ 0) :
    numberFieldEllipsoidPartition K b n (canonicalDiagonalShape K b w hw) =
      ∏ i, ringGaussianPartition K (w i) := by
  unfold numberFieldEllipsoidPartition
  simp_rw [canonicalDiagonalShape_weight]
  exact tsum_finite_product_real _ (fun _ _ => (gaussianWeight_pos _ _).le)
    (fun i => summable_ringGaussianWeight K b (w i) (hw i))

theorem canonicalDiagonalShape_gaussian_zero (b : Basis (Fin d) ℤ (𝓞 K))
    (w : Fin n → ℝ) (hw : ∀ i, w i ≠ 0) :
    numberFieldEllipsoidalGaussian K b n (canonicalDiagonalShape K b w hw) 0 =
      independentProduct (fun i => ringGaussian K b (w i) (hw i)) := by
  ext x
  simp only [numberFieldEllipsoidalGaussian_apply, map_zero, sub_zero,
    canonicalDiagonalShape_weight, canonicalDiagonalShape_partition,
    independentProduct_apply, ringGaussian_apply]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => div_nonneg (ringGaussianWeight_pos K (w i) (x i)).le
    (ringGaussianPartition_pos K b (w i) (hw i)).le), Finset.prod_div_distrib]

theorem canonicalDiagonalShape_gaussian_shift (b : Basis (Fin d) ℤ (𝓞 K))
    (w : Fin n → ℝ) (hw : ∀ i, w i ≠ 0) (c : Fin n → 𝓞 K) :
    numberFieldEllipsoidalGaussian K b n (canonicalDiagonalShape K b w hw) c =
      independentProduct (fun i => (ringGaussian K b (w i) (hw i)).map (Equiv.addRight (c i))) := by
  rw [← numberFieldEllipsoidalGaussian_translate, canonicalDiagonalShape_gaussian_zero]
  exact independentProduct_map _ (fun i => Equiv.addRight (c i))

theorem independentMatrixColumns_apply {α : Type*} (p : Fin m → PMF (Fin n → α))
    (X : Matrix (Fin n) (Fin m) α) :
    independentMatrixColumns p X = ∏ j, p j (fun i => X i j) := by
  let e := Equiv.piComm (fun _ : Fin m => fun _ : Fin n => α)
  change (independentProduct p).map e (e X.transpose) = _
  rw [pmf_map_equiv_apply]
  rfl

theorem numberFieldMatrixLaw_rows (b : Basis (Fin d) ℤ (𝓞 K))
    (s : ℝ) (hs : s ≠ 0) :
    numberFieldMatrixLaw K b n m s hs =
      independentProduct (fun _ : Fin n => numberFieldGaussian K b m s hs) := by
  ext X
  change independentMatrixColumns (fun _ : Fin m => numberFieldGaussian K b n s hs) X = _
  rw [independentMatrixColumns_apply]
  simp only [numberFieldGaussian_independent_coordinates, independentProduct_apply]
  exact Finset.prod_comm

/-- Transpose both row-hint blocks into the columns used in the modular game. -/
def hintBlocksEquiv {α : Type*} (m k : ℕ) :
    (Matrix (Fin k) (Fin m) α × Matrix (Fin k) (Fin k) α) ≃
      Matrix (Fin (m + k)) (Fin k) α where
  toFun z i j := Fin.append (fun a => z.1 j a) (fun b => z.2 j b) i
  invFun Z := (fun j i => Z (Fin.castAdd k i) j, fun i j => Z (Fin.natAdd m j) i)
  left_inv z := by ext <;> simp
  right_inv Z := by
    funext i j
    exact Fin.addCases (fun a => by simp) (fun b => by simp) i

theorem pmf_map_addRight_apply {α : Type*} [AddGroup α] (p : PMF α) (c x : α) :
    p.map (Equiv.addRight c) x = p (x - c) := by
  have h := pmf_map_equiv_apply p (Equiv.addRight c) (x - c)
  change p.map (Equiv.addRight c) ((x - c) + c) = _ at h
  simpa only [sub_add_cancel] using h

/-- The target block distribution is exactly the diagonal-width Gaussian hint
law, with the unit shifts in the final block. -/
theorem paperHint_blocks_law (b : Basis (Fin d) ℤ (𝓞 K)) (m k : ℕ)
    {s₁ s₂ : ℝ} (h₁ : s₁ ≠ 0) (h₂ : s₂ ≠ 0) :
    (jointPMF (numberFieldMatrixLaw K b k m s₁ h₁) (fun _ =>
      independentMatrixColumns (fun j : Fin k =>
        (numberFieldGaussian K b k s₂ h₂).map (Equiv.addRight (matrixIdentityColumn j))))).map
        (hintBlocksEquiv m k) =
      independentMatrixColumns (fun j : Fin k => numberFieldEllipsoidalGaussian K b (m + k)
        (paperHintShape K b m k h₁ h₂) (matrixIdentityColumn (Fin.natAdd m j))) := by
  ext Z
  obtain ⟨⟨X, Y⟩, rfl⟩ := (hintBlocksEquiv (α := 𝓞 K) m k).surjective Z
  have hne (i : Fin m) (j : Fin k) : Fin.castAdd k i ≠ Fin.natAdd m j := by
    intro h
    have he := congrArg Fin.val h
    simp at he
    omega
  rw [pmf_map_equiv_apply, jointPMF_apply, numberFieldMatrixLaw_rows]
  simp only [independentMatrixColumns_apply, paperHintShape, canonicalDiagonalShape_gaussian_shift,
    independentProduct_apply, pmf_map_addRight_apply, numberFieldGaussian_independent_coordinates]
  simp only [Fin.prod_univ_add, Finset.prod_mul_distrib,
    blockWidths, Fin.append_left, Fin.append_right, hintBlocksEquiv, Equiv.coe_fn_mk,
    Pi.sub_apply, matrixIdentityColumn, Matrix.one_apply]
  simp [hne, eq_comm]
  change (∏ i, ∏ j, ringGaussian K b s₁ h₁ (X i j)) *
      (∏ i, ∏ j, ringGaussian K b s₂ h₂ (Y i j - if i = j then 1 else 0)) =
    (∏ i, ∏ j, ringGaussian K b s₁ h₁ (X i j)) *
      (∏ i, ∏ j, ringGaussian K b s₂ h₂ (Y j i - if i = j then 1 else 0))
  congr 1
  rw [Finset.prod_comm]
  simp only [eq_comm]

theorem integerGaussianPartition_le_twice {s : ℝ} (hs : 1 ≤ s) :
    integerGaussianPartition s ≤ 2 * s := by
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
  rw [integerGaussianPartition_poisson hs0]
  have hpi : Real.pi ≤ Real.pi * s ^ 2 := by
    nlinarith [Real.pi_pos, sq_nonneg (s - 1)]
  have htheta : integerTheta (Real.pi * s ^ 2) ≤ 2 :=
    (integerTheta_antitone Real.pi_pos hpi).trans (by linarith [integerTheta_pi_upper])
  nlinarith [mul_le_mul_of_nonneg_left htheta hs0.le]

theorem numberFieldGaussianPartition_of_diagonal (b : Basis (Fin d) ℤ (𝓞 K))
    {c : ℝ} (hc : 0 < c) (hGram : ∀ i j, canonicalGram K b i j = if i = j then c else 0)
    (n : ℕ) {s : ℝ} (hs : 0 < s) :
    numberFieldGaussianPartition K n s = integerGaussianPartition (s / Real.sqrt c) ^ (n * d) := by
  rw [← numberFieldGaussianPartition_eq_ellipsoid K b n s hs.ne']
  unfold ellipsoidPartition
  simp_rw [numberFieldGaussianShape_weight_of_diagonal K b hc hGram n hs,
    gaussianWeight_integer_product]
  let a : ℝ := Real.pi / (s / Real.sqrt c) ^ 2
  have ha : 0 < a := by dsimp [a]; positivity
  have hw (z : ℤ) : Real.exp (-(Real.pi * (1 / (s / Real.sqrt c)) ^ 2) * (z : ℝ) ^ 2) =
      Real.exp (-a * (z : ℝ) ^ 2) := by
    congr 1
    dsimp [a]
    ring
  simp_rw [hw]
  rw [tsum_finite_product_real (fun _ : Fin (n * d) => fun z : ℤ => Real.exp (-a * (z : ℝ) ^ 2))
    (fun _ _ => (Real.exp_pos _).le) (fun _ => summable_integer_gaussian ha)]
  simp only [integerGaussianPartition, integerTheta, a, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

theorem numberFieldGaussianPartition_le_of_diagonal (b : Basis (Fin d) ℤ (𝓞 K))
    {c : ℝ} (hc : 0 < c) (hGram : ∀ i j, canonicalGram K b i j = if i = j then c else 0)
    (n : ℕ) {s : ℝ} (hs : Real.sqrt c ≤ s) :
    numberFieldGaussianPartition K n s ≤ (2 * s / Real.sqrt c) ^ (n * d) := by
  have hs0 : 0 < s := (Real.sqrt_pos.mpr hc).trans_le hs
  rw [numberFieldGaussianPartition_of_diagonal K b hc hGram n hs0]
  have h := integerGaussianPartition_le_twice ((one_le_div (Real.sqrt_pos.mpr hc)).mpr hs)
  simpa only [mul_div_assoc] using pow_le_pow_left₀
    (integerGaussianPartition_pos (div_pos hs0 (Real.sqrt_pos.mpr hc))).le h (n * d)

end SISToKSIS

open GeometricGaussianLHL
namespace SISToKSIS
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Removing the zero Fourier mode bounds every shifted scalar partition by
its nonzero Fourier mass. The Poisson identity is reused from the parent library. -/
theorem periodicGaussian_sub_mean_le {t : ℝ} (ht : 0 < t) (c : ℝ) :
    |periodicGaussian t c - 1 / t| ≤ periodicGaussian t 0 - 1 / t := by
  classical
  let f : ℤ → ℂ := fun z => (gaussianFourierCoefficient t z : ℂ) * fourier z ((-c : ℝ) : UnitAddCircle)
  let g : ℤ → ℂ := fun z => if z = 0 then 0 else f z
  have hzero : f 0 = ((1 / t : ℝ) : ℂ) := by simp [f, gaussianFourierCoefficient]
  have hid : (periodicGaussian t c : ℂ) - ((1 / t : ℝ) : ℂ) = ∑' z, g z := by
    rw [periodicGaussian_fourier ht c,
      (summable_gaussianFourierTerm ht (-c)).tsum_eq_add_tsum_ite 0]
    change f 0 + (∑' z, g z) - ((1 / t : ℝ) : ℂ) = _
    rw [hzero, add_sub_cancel_left]
  have hnorm (z : ℤ) : ‖g z‖ = if z = 0 then 0 else gaussianFourierCoefficient t z := by
    by_cases hz : z = 0
    · simp [g, hz]
    · simp only [g, hz, ite_false, f, norm_gaussianFourierTerm ht]
  have hg : Summable (fun z => ‖g z‖) :=
    (summable_gaussianFourierCoefficient ht).of_nonneg_of_le (fun z => norm_nonneg (g z))
      (fun z => by rw [hnorm]; split_ifs <;> first | exact (gaussianFourierCoefficient_pos ht z).le | exact le_rfl)
  have hsum : (∑' z : ℤ, if z = 0 then 0 else gaussianFourierCoefficient t z) =
      periodicGaussian t 0 - 1 / t := by
    rw [periodicGaussian_zero_eq_fourier_sum ht,
      (summable_gaussianFourierCoefficient ht).tsum_eq_add_tsum_ite 0]
    have hz : gaussianFourierCoefficient t 0 = 1 / t := by simp [gaussianFourierCoefficient]
    rw [hz, add_sub_cancel_left]
  have h := norm_tsum_le_tsum_norm hg
  rw [← hid] at h
  simpa only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, hnorm, hsum] using h

/-- Relative normalizer error, uniformly in the real center. -/
theorem scalarGaussianPartition_relative_flatness (c : ℝ) {v : ℝ} (hv : 1 ≤ v) :
    |scalarGaussianPartition c v / Real.sqrt v - 1| ≤ 3 * Real.exp (-Real.pi * v) := by
  have hv0 : 0 < v := lt_of_lt_of_le zero_lt_one hv
  have hs := Real.sqrt_pos.mpr hv0
  have hσ : 1 ≤ Real.sqrt v := Real.one_le_sqrt.mpr hv
  have hzero : periodicGaussian (1 / Real.sqrt v) 0 =
      Real.sqrt v * periodicGaussian (Real.sqrt v) 0 := by
    have he : periodicGaussian (1 / Real.sqrt v) 0 = integerGaussianPartition (Real.sqrt v) := by
      unfold periodicGaussian integerGaussianPartition integerTheta
      apply tsum_congr
      intro z
      congr 1
      ring
    rw [he, integerGaussianPartition_poisson hs]
    congr 1
    unfold periodicGaussian integerTheta
    apply tsum_congr
    intro z
    congr 1
    ring
  have hflat := periodicGaussian_sub_mean_le (one_div_pos.mpr hs) c
  rw [hzero, one_div_one_div] at hflat
  have htail := periodicGaussian_origin_bound hσ
  rw [Real.sq_sqrt hv0.le] at htail
  have hmass : |scalarGaussianPartition c v - Real.sqrt v| ≤
      Real.sqrt v * (3 * Real.exp (-Real.pi * v)) := by
    rw [scalarGaussianPartition_eq_periodic c hv0]
    apply hflat.trans
    have h := mul_le_mul_of_nonneg_left htail hs.le
    nlinarith
  have he : scalarGaussianPartition c v / Real.sqrt v - 1 =
      (scalarGaussianPartition c v - Real.sqrt v) / Real.sqrt v := by field_simp
  rw [he, abs_div, abs_of_pos hs]
  exact (div_le_iff₀ hs).mpr (by simpa only [mul_comm] using hmass)

theorem scalarGaussianVariance_of_log {N : ℕ} (hN : 2 ≤ N)
    {ε v : ℝ} (hε : 0 < ε) (hεone : ε ≤ 1)
    (hv : 4 * Real.log ((N : ℝ) / ε) ≤ v) : 1 ≤ v := by
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hx : 2 ≤ (N : ℝ) / ε := by
    apply (le_div_iff₀ hε).mpr
    nlinarith
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < (1 / 2))
    rw [one_div, Real.log_inv] at h
    norm_num at h
    linarith
  have hlog := hlog2.trans (Real.log_le_log (by norm_num) hx)
  linarith

/-- A logarithmic squared width gives a per-coordinate normalizer budget.
The dimension condition holds in the SIS reduction, where `dm ≥ 64`. -/
theorem scalarGaussianPartition_flat_of_log (c : ℝ) {N : ℕ} (hN : 2 ≤ N)
    {ε v : ℝ} (hε : 0 < ε) (hεone : ε ≤ 1)
    (hv : 4 * Real.log ((N : ℝ) / ε) ≤ v) :
    |scalarGaussianPartition c v / Real.sqrt v - 1| ≤ ε / (8 * N) := by
  let x := (N : ℝ) / ε
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hx : 2 ≤ x := by
    dsimp [x]
    apply (le_div_iff₀ hε).mpr
    nlinarith
  have hx0 : 0 < x := by linarith
  have hvone : 1 ≤ v := scalarGaussianVariance_of_log hN hε hεone hv
  have hpow : 24 * x ≤ x ^ 8 := by
    have h := pow_le_pow_left₀ (show (0 : ℝ) ≤ 2 by norm_num) hx 7
    norm_num at h
    have hh := mul_le_mul_of_nonneg_right h hx0.le
    rw [pow_succ]
    nlinarith
  have hlogbound : Real.log (24 * x) ≤ Real.pi * v := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < 24 * x) hpow
    rw [Real.log_pow] at h
    norm_num at h
    have hpi := mul_le_mul_of_nonneg_right Real.two_le_pi (show 0 ≤ v by linarith)
    change 4 * Real.log x ≤ v at hv
    nlinarith
  have hexp : Real.exp (-Real.pi * v) ≤ 1 / (24 * x) := by
    calc
      _ ≤ Real.exp (-Real.log (24 * x)) := Real.exp_le_exp.mpr (by linarith)
      _ = _ := by rw [Real.exp_neg, Real.exp_log (by positivity), one_div]
  apply (scalarGaussianPartition_relative_flatness c hvone).trans
  have h := mul_le_mul_of_nonneg_left hexp (show (0 : ℝ) ≤ 3 by norm_num)
  convert h using 1
  dsimp [x]
  field_simp
  ring

end
end SISToKSIS

open GeometricGaussianLHL
namespace SISToKSIS
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Uniform factor errors accumulate linearly while their total budget is small. -/
theorem product_near_one {N : ℕ} (r : Fin N → ℝ) {δ : ℝ}
    (hδ : 0 ≤ δ) (hδone : δ ≤ 1) (hsmall : (N : ℝ) * δ ≤ 1)
    (hr : ∀ i, |r i - 1| ≤ δ) : |(∏ i, r i) - 1| ≤ 2 * N * δ := by
  have hlo (i : Fin N) : 1 - δ ≤ r i := by have h := (abs_le.mp (hr i)).1; linarith
  have hhi (i : Fin N) : r i ≤ 1 + δ := by have h := (abs_le.mp (hr i)).2; linarith
  have hr0 (i : Fin N) : 0 ≤ r i := (by linarith : 0 ≤ 1 - δ).trans (hlo i)
  have hprodlo : (1 - δ) ^ N ≤ ∏ i, r i := by
    have h := Finset.prod_le_prod (fun _ (_ : _ ∈ (Finset.univ : Finset (Fin N))) =>
      (show 0 ≤ 1 - δ by linarith)) (fun i _ => hlo i)
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using h
  have hprodhi : (∏ i, r i) ≤ (1 + δ) ^ N := by
    have h := Finset.prod_le_prod (fun i (_ : i ∈ Finset.univ) => hr0 i) (fun i _ => hhi i)
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using h
  have hbernoulli := one_add_mul_le_pow (a := -δ) (by linarith : -2 ≤ -δ) N
  have hexp : (1 + δ) ^ N ≤ Real.exp ((N : ℝ) * δ) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp δ]) N
  have hupper := hprodhi.trans (hexp.trans (exp_le_one_add_two_mul (by positivity) hsmall))
  have hnonneg : (0 : ℝ) ≤ N * δ := by positivity
  apply abs_le.mpr
  constructor
  · have he : (1 + -δ) ^ N = (1 - δ) ^ N := by ring
    rw [he] at hbernoulli
    nlinarith
  · nlinarith

theorem scalarGaussian_normalizer_product {N : ℕ} (hN : 2 ≤ N)
    (c v : Fin N → ℝ) {ε : ℝ} (hε : 0 < ε) (hεone : ε ≤ 1)
    (hv : ∀ i, 4 * Real.log ((N : ℝ) / ε) ≤ v i) :
    |(∏ i, scalarGaussianPartition (c i) (v i) / Real.sqrt (v i)) - 1| ≤ ε / 4 := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hN)
  have he : (N : ℝ) * (ε / (8 * N)) = ε / 8 := by field_simp
  have hδ : ε / (8 * N) ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have h := product_near_one (fun i => scalarGaussianPartition (c i) (v i) / Real.sqrt (v i))
    (by positivity : 0 ≤ ε / (8 * N)) hδ (by rw [he]; linarith)
    (fun i => scalarGaussianPartition_flat_of_log (c i) hN hε hεone (hv i))
  apply h.trans
  nlinarith [he]

/-- Compare a normalized target with a law built using point-dependent
normalizers, without assuming that those normalizers are independent. -/
theorem totalVariation_le_of_normalizer_product {α : Type*} {N : ℕ}
    (p q : PMF α) (r : α → Fin N → ℝ) (scale : ℝ) {δ : ℝ}
    (hδ : 0 ≤ δ) (hδone : δ ≤ 1) (hsmall : (N : ℝ) * δ ≤ 1)
    (hr : ∀ z i, |r z i - 1| ≤ δ)
    (hweight : ∀ z, scale * (q z).toReal = (p z).toReal * ∏ i, r z i) :
    discreteTotalVariation p q ≤ 2 * N * δ := by
  have hpoint (z : α) : |scale * (q z).toReal - (p z).toReal| ≤
      (2 * N * δ) * (p z).toReal := by
    rw [hweight, ← mul_sub_one, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
    have h := mul_le_mul_of_nonneg_left (product_near_one (r z) hδ hδone hsmall (hr z))
      (show 0 ≤ (p z).toReal from ENNReal.toReal_nonneg)
    simpa only [mul_comm] using h
  have hs : Summable (fun z => |scale * (q z).toReal - (p z).toReal|) := by
    simpa only [Real.norm_eq_abs] using
      (((pmf_summable_toReal q).mul_left scale).sub (pmf_summable_toReal p)).norm
  have hsum := hs.tsum_le_tsum hpoint ((pmf_summable_toReal p).mul_left (2 * N * δ))
  rw [tsum_mul_left, pmf_tsum_toReal, mul_one] at hsum
  rw [discreteTotalVariation_symm]
  exact (scaled_mass_totalVariation_le q p scale).trans hsum

end
end SISToKSIS

open GeometricGaussianLHL
namespace SISToKSIS
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The previously sampled coordinates of a full tuple. -/
def prefixRestrict {α : Type*} {N : ℕ} (z : Fin N → α) (i : Fin N) : Fin i.val → α :=
  fun j => z ⟨j.val, lt_trans j.isLt i.isLt⟩

@[simp] theorem prefixRestrict_cons_zero {α : Type*} {N : ℕ} (a : α) (z : Fin N → α) :
    prefixRestrict (Fin.cons a z) 0 = Fin.elim0 := by
  funext j
  exact Fin.elim0 j

@[simp] theorem prefixRestrict_cons_succ {α : Type*} {N : ℕ}
    (a : α) (z : Fin N → α) (i : Fin N) :
    prefixRestrict (Fin.cons a z) i.succ = Fin.cons a (prefixRestrict z i) := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp [prefixRestrict]
  · change (Fin.cons a z : Fin (N + 1) → α) (Fin.succ ⟨j.val, lt_trans j.isLt i.isLt⟩) = _
    simp only [Fin.cons_succ]
    rfl

def prefixPMF {α : Type*} : (N : ℕ) →
    (∀ i : Fin N, (Fin i.val → α) → PMF α) → PMF (Fin N → α)
  | 0, _ => PMF.pure Fin.elim0
  | N + 1, kernel =>
    (jointPMF (kernel 0 Fin.elim0) (fun a =>
      prefixPMF N (fun i z => kernel i.succ (Fin.cons a z)))).map
      (Fin.consEquiv (fun _ : Fin (N + 1) => α))

/-- Sequential kernels have their exact product mass even when each kernel
and its normalizer depend on all earlier outputs. -/
theorem prefixPMF_apply {α : Type*} (N : ℕ)
    (kernel : ∀ i : Fin N, (Fin i.val → α) → PMF α) (z : Fin N → α) :
    prefixPMF N kernel z = ∏ i, kernel i (prefixRestrict z i) (z i) := by
  induction N with
  | zero =>
    simp [prefixPMF]
    funext i
    exact Fin.elim0 i
  | succ N ih =>
    obtain ⟨⟨a, z⟩, rfl⟩ := (Fin.consEquiv (fun _ : Fin (N + 1) => α)).surjective z
    rw [prefixPMF, pmf_map_equiv_apply, jointPMF_apply, ih]
    simp only [Fin.prod_univ_succ, Fin.consEquiv, Equiv.coe_fn_mk, Fin.cons_zero, Fin.cons_succ,
      prefixRestrict_cons_zero, prefixRestrict_cons_succ]

/-- Adaptive hybrid bound for kernels evaluated at the same prefix. -/
theorem prefixPMF_error {α : Type*} (N : ℕ)
    (p q : ∀ i : Fin N, (Fin i.val → α) → PMF α) (ε : Fin N → ℝ)
    (h : ∀ i z, discreteTotalVariation (p i z) (q i z) ≤ ε i) :
    discreteTotalVariation (prefixPMF N p) (prefixPMF N q) ≤ ∑ i, ε i := by
  induction N with
  | zero => simp [prefixPMF, discreteTotalVariation]
  | succ N ih =>
    rw [prefixPMF, prefixPMF, discreteTotalVariation_map_equiv, Fin.sum_univ_succ]
    let pTail := fun a => prefixPMF N (fun i z => p i.succ (Fin.cons a z))
    let qTail := fun a => prefixPMF N (fun i z => q i.succ (Fin.cons a z))
    have htail (a : α) : discreteTotalVariation (pTail a) (qTail a) ≤ ∑ i : Fin N, ε i.succ :=
      ih (fun i z => p i.succ (Fin.cons a z)) (fun i z => q i.succ (Fin.cons a z))
        (fun i => ε i.succ) (fun i z => h i.succ (Fin.cons a z))
    have hfirst := totalVariation_joint_same_adversary (p 0 Fin.elim0) (q 0 Fin.elim0) pTail
    have hsecond := discreteTotalVariation_joint_le_uniform (q 0 Fin.elim0) pTail qTail htail
    have htriangle := discreteTotalVariation_triangle (jointPMF (p 0 Fin.elim0) pTail)
      (jointPMF (q 0 Fin.elim0) pTail) (jointPMF (q 0 Fin.elim0) qTail)
    rw [hfirst] at htriangle
    exact htriangle.trans (add_le_add (h 0 Fin.elim0) hsecond)

end
end SISToKSIS

open GeometricGaussianLHL
namespace SISToKSIS
noncomputable section
set_option backward.isDefEq.respectTransparency false

abbrev GaussianPrefixCenters (N : ℕ) := ∀ i : Fin N, Coeff i.val → ℝ

def sequentialGaussianLaw {N : ℕ} (c : GaussianPrefixCenters N) (v : Fin N → ℝ)
    (hv : ∀ i, 0 < v i) : PMF (Coeff N) :=
  prefixPMF N (fun i z => scalarGaussianLaw (c i z) (v i) (hv i))

/-- Unnormalized product of Gaussian weights with prefix-dependent centers.
Identifying this target with an ellipsoidal Gaussian weight requires a
separate identity for the triangular matrix factorization. -/
def triangularGaussianWeight {N : ℕ} (c : GaussianPrefixCenters N) (v : Fin N → ℝ)
    (z : Coeff N) : ℝ := ∏ i, scalarIdealWeight (c i (prefixRestrict z i)) (v i) (z i)

def triangularGaussianNormalizers {N : ℕ} (c : GaussianPrefixCenters N) (v : Fin N → ℝ)
    (z : Coeff N) : ℝ := ∏ i, scalarGaussianPartition (c i (prefixRestrict z i)) (v i)

theorem triangularGaussianWeight_pos {N : ℕ} (c : GaussianPrefixCenters N)
    (v : Fin N → ℝ) (z : Coeff N) : 0 < triangularGaussianWeight c v z :=
  Finset.prod_pos (fun i _ => scalarIdealWeight_pos (c i (prefixRestrict z i)) (v i) (z i))

theorem triangularGaussianNormalizers_pos {N : ℕ} (c : GaussianPrefixCenters N)
    (v : Fin N → ℝ) (hv : ∀ i, 0 < v i) (z : Coeff N) :
    0 < triangularGaussianNormalizers c v z :=
  Finset.prod_pos (fun i _ => scalarGaussianPartition_pos _ (hv i))

theorem triangularGaussianWeight_sequential_mass {N : ℕ} (c : GaussianPrefixCenters N)
    (v : Fin N → ℝ) (hv : ∀ i, 0 < v i) (z : Coeff N) :
    triangularGaussianWeight c v z =
      triangularGaussianNormalizers c v z * (sequentialGaussianLaw c v hv z).toReal := by
  have hZ := (triangularGaussianNormalizers_pos c v hv z).ne'
  simp only [sequentialGaussianLaw, prefixPMF_apply, ENNReal.toReal_prod,
    scalarGaussianLaw_toReal, Finset.prod_div_distrib]
  change triangularGaussianWeight c v z =
    triangularGaussianNormalizers c v z *
      (triangularGaussianWeight c v z / triangularGaussianNormalizers c v z)
  field_simp

theorem scalarGaussianPartition_le_zero (c : ℝ) {v : ℝ} (hv : 0 < v) :
    scalarGaussianPartition c v ≤ scalarGaussianPartition 0 v := by
  rw [scalarGaussianPartition_eq_periodic c hv, scalarGaussianPartition_eq_periodic 0 hv]
  exact periodicGaussian_le_zero (one_div_pos.mpr (Real.sqrt_pos.mpr hv)) c

theorem triangularGaussianWeight_summable {N : ℕ} (c : GaussianPrefixCenters N)
    (v : Fin N → ℝ) (hv : ∀ i, 0 < v i) : Summable (triangularGaussianWeight c v) := by
  let C := ∏ i, scalarGaussianPartition 0 (v i)
  have hZ (z : Coeff N) : triangularGaussianNormalizers c v z ≤ C :=
    Finset.prod_le_prod (fun i _ => (scalarGaussianPartition_pos _ (hv i)).le)
      (fun i _ => scalarGaussianPartition_le_zero _ (hv i))
  apply ((pmf_summable_toReal (sequentialGaussianLaw c v hv)).mul_left C).of_nonneg_of_le
    (fun z => (triangularGaussianWeight_pos c v z).le)
  intro z
  rw [triangularGaussianWeight_sequential_mass c v hv z]
  exact mul_le_mul_of_nonneg_right (hZ z) ENNReal.toReal_nonneg

def triangularGaussianPartition {N : ℕ} (c : GaussianPrefixCenters N) (v : Fin N → ℝ) : ℝ :=
  ∑' z : Coeff N, triangularGaussianWeight c v z

theorem triangularGaussianPartition_pos {N : ℕ} (c : GaussianPrefixCenters N)
    (v : Fin N → ℝ) (hv : ∀ i, 0 < v i) : 0 < triangularGaussianPartition c v :=
  (triangularGaussianWeight_pos c v 0).trans_le
    ((triangularGaussianWeight_summable c v hv).le_tsum 0
      (fun z _ => (triangularGaussianWeight_pos c v z).le))

def triangularGaussianLaw {N : ℕ} (c : GaussianPrefixCenters N) (v : Fin N → ℝ)
    (hv : ∀ i, 0 < v i) : PMF (Coeff N) :=
  PMF.normalize (fun z => ENNReal.ofReal (triangularGaussianWeight c v z))
    (by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun z => (triangularGaussianWeight_pos c v z).le)
        (triangularGaussianWeight_summable c v hv)]
      exact ne_of_gt (ENNReal.ofReal_pos.mpr (triangularGaussianPartition_pos c v hv)))
    (triangularGaussianWeight_summable c v hv).tsum_ofReal_ne_top

theorem triangularGaussianLaw_toReal {N : ℕ} (c : GaussianPrefixCenters N) (v : Fin N → ℝ)
    (hv : ∀ i, 0 < v i) (z : Coeff N) :
    (triangularGaussianLaw c v hv z).toReal = triangularGaussianWeight c v z / triangularGaussianPartition c v := by
  simp only [triangularGaussianLaw, PMF.normalize_apply]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun z => (triangularGaussianWeight_pos c v z).le)
    (triangularGaussianWeight_summable c v hv)]
  change (ENNReal.ofReal (triangularGaussianWeight c v z) *
    (ENNReal.ofReal (triangularGaussianPartition c v))⁻¹).toReal = _
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (triangularGaussianWeight_pos c v z).le,
    ENNReal.toReal_ofReal (triangularGaussianPartition_pos c v hv).le, div_eq_mul_inv]

theorem triangularGaussianLaw_density {N : ℕ} (c : GaussianPrefixCenters N) (v : Fin N → ℝ)
    (hv : ∀ i, 0 < v i) (z : Coeff N) :
    (triangularGaussianPartition c v / (∏ i, Real.sqrt (v i))) *
      (triangularGaussianLaw c v hv z).toReal =
      (sequentialGaussianLaw c v hv z).toReal *
        ∏ i, scalarGaussianPartition (c i (prefixRestrict z i)) (v i) / Real.sqrt (v i) := by
  have hV : (∏ i, Real.sqrt (v i)) ≠ 0 :=
    (Finset.prod_pos (fun i _ => Real.sqrt_pos.mpr (hv i))).ne'
  have hZ := (triangularGaussianPartition_pos c v hv).ne'
  rw [triangularGaussianLaw_toReal, Finset.prod_div_distrib]
  change _ = (sequentialGaussianLaw c v hv z).toReal *
    (triangularGaussianNormalizers c v z / ∏ i, Real.sqrt (v i))
  rw [triangularGaussianWeight_sequential_mass c v hv z]
  field_simp

/-- Sequential ideal scalar Gaussians approximate the fully normalized
triangular target; the cumulative normalizer bias is explicitly charged. -/
theorem sequentialGaussianLaw_error {N : ℕ} (hN : 2 ≤ N)
    (c : GaussianPrefixCenters N) (v : Fin N → ℝ) (hv : ∀ i, 0 < v i)
    {ε : ℝ} (hε : 0 < ε) (hεone : ε ≤ 1)
    (hlog : ∀ i, 4 * Real.log ((N : ℝ) / ε) ≤ v i) :
    discreteTotalVariation (sequentialGaussianLaw c v hv) (triangularGaussianLaw c v hv) ≤ ε / 4 := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hN)
  have he : (N : ℝ) * (ε / (8 * N)) = ε / 8 := by field_simp
  have hδ : ε / (8 * N) ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have h := totalVariation_le_of_normalizer_product (sequentialGaussianLaw c v hv)
    (triangularGaussianLaw c v hv)
    (fun z i => scalarGaussianPartition (c i (prefixRestrict z i)) (v i) / Real.sqrt (v i))
    (triangularGaussianPartition c v / (∏ i, Real.sqrt (v i)))
    (by positivity : 0 ≤ ε / (8 * N)) hδ (by rw [he]; linarith)
    (fun z i => scalarGaussianPartition_flat_of_log _ hN hε hεone (hlog i))
    (triangularGaussianLaw_density c v hv)
  apply h.trans
  nlinarith [he]

end
end SISToKSIS

open GeometricGaussianLHL
namespace SISToKSIS
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Adaptive composition of the verified finite scalar laws. The stored
triangular sampler below implements these prefix-dependent kernels. -/
def finiteSequentialGaussianLaw {N : ℕ}
    (data : ∀ i : Fin N, Coeff i.val → ScalarGaussianData) (s : ℕ) : PMF (Coeff N) :=
  prefixPMF N (fun i z => scalarGaussianRunLaw (data i z) (s + N))

theorem finiteSequentialGaussianLaw_scalar_error {N : ℕ}
    (data : ∀ i : Fin N, Coeff i.val → ScalarGaussianData)
    (hdata : ∀ i z, (data i z).Valid) (c : GaussianPrefixCenters N) (v : Fin N → ℝ)
    (hv : ∀ i, 0 < v i) (hwidth : ∀ i, 1 ≤ v i)
    (hcenter : ∀ i z, (data i z).center = c i z)
    (hvariance : ∀ i z, (data i z).widthSq = v i) (s : ℕ) :
    discreteTotalVariation (finiteSequentialGaussianLaw data s)
      (sequentialGaussianLaw c v hv) ≤ (1 / 2 : ℝ) ^ s := by
  have hpoint (i : Fin N) (z : Coeff i.val) :
      discreteTotalVariation (scalarGaussianRunLaw (data i z) (s + N))
        (scalarGaussianLaw (c i z) (v i) (hv i)) ≤ (1 / 2 : ℝ) ^ (s + N) := by
    have hw : 1 ≤ (data i z).widthSq := by rw [hvariance]; exact hwidth i
    simpa only [hcenter, hvariance] using scalarGaussianRunLaw_error (data i z) (hdata i z) hw (s + N)
  have h := prefixPMF_error N
    (fun i z => scalarGaussianRunLaw (data i z) (s + N))
    (fun i z => scalarGaussianLaw (c i z) (v i) (hv i))
    (fun _ => (1 / 2 : ℝ) ^ (s + N)) hpoint
  change discreteTotalVariation (finiteSequentialGaussianLaw data s) (sequentialGaussianLaw c v hv) ≤ _ at h
  apply h.trans
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, pow_add]
  have hcount : (N : ℝ) ≤ (2 : ℝ) ^ N := by exact_mod_cast (Nat.lt_two_pow_self (n := N)).le
  have hratio : (N : ℝ) * (1 / 2 : ℝ) ^ N ≤ 1 := by
    rw [one_div_pow, mul_one_div]
    exact (div_le_one (by positivity)).mpr hcount
  have hp := mul_le_mul_of_nonneg_left hratio (show (0 : ℝ) ≤ (1 / 2 : ℝ) ^ s by positivity)
  nlinarith

/-- The finite scalar errors and the sequential normalizer bias together fit
half of the supplied column budget. Matrix factorization and prefix evaluation
are separate obligations, not assumptions hidden in this probability bound. -/
theorem finiteSequentialGaussianLaw_error {N : ℕ} (hN : 2 ≤ N)
    (data : ∀ i : Fin N, Coeff i.val → ScalarGaussianData)
    (hdata : ∀ i z, (data i z).Valid) (c : GaussianPrefixCenters N) (v : Fin N → ℝ)
    (hv : ∀ i, 0 < v i) (hcenter : ∀ i z, (data i z).center = c i z)
    (hvariance : ∀ i z, (data i z).widthSq = v i)
    {ε : ℝ} (hε : 0 < ε) (hεone : ε ≤ 1)
    (hlog : ∀ i, 4 * Real.log ((N : ℝ) / ε) ≤ v i)
    (s : ℕ) (hbudget : (1 / 2 : ℝ) ^ s ≤ ε / 4) :
    discreteTotalVariation (finiteSequentialGaussianLaw data s) (triangularGaussianLaw c v hv) ≤ ε / 2 := by
  have hscalar := finiteSequentialGaussianLaw_scalar_error data hdata c v hv
    (fun i => scalarGaussianVariance_of_log hN hε hεone (hlog i)) hcenter hvariance s
  have hnormalizer := sequentialGaussianLaw_error hN c v hv hε hεone hlog
  have h := discreteTotalVariation_triangle (finiteSequentialGaussianLaw data s)
    (sequentialGaussianLaw c v hv) (triangularGaussianLaw c v hv)
  linarith

/-- An explicit integer precision prescription for a dyadic column budget. -/
theorem finiteSequentialGaussianLaw_error_dyadic {N : ℕ} (hN : 2 ≤ N)
    (data : ∀ i : Fin N, Coeff i.val → ScalarGaussianData)
    (hdata : ∀ i z, (data i z).Valid) (c : GaussianPrefixCenters N) (v : Fin N → ℝ)
    (hv : ∀ i, 0 < v i) (hcenter : ∀ i z, (data i z).center = c i z)
    (hvariance : ∀ i z, (data i z).widthSq = v i) (s : ℕ)
    (hlog : ∀ i, 4 * Real.log ((N : ℝ) / (1 / 2 : ℝ) ^ s) ≤ v i) :
    discreteTotalVariation (finiteSequentialGaussianLaw data (s + 2))
      (triangularGaussianLaw c v hv) ≤ (1 / 2 : ℝ) ^ (s + 1) := by
  have hεone : (1 / 2 : ℝ) ^ s ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hbudget : (1 / 2 : ℝ) ^ (s + 2) ≤ (1 / 2 : ℝ) ^ s / 4 := by
    rw [pow_add]
    norm_num
    exact le_of_eq (by ring)
  have h := finiteSequentialGaussianLaw_error hN data hdata c v hv hcenter hvariance
    (by positivity : (0 : ℝ) < (1 / 2 : ℝ) ^ s) hεone hlog (s + 2) hbudget
  apply h.trans
  rw [pow_succ]
  exact le_of_eq (by ring)

end
end SISToKSIS

end

open GeometricGaussianLHL Matrix
namespace SISToKSIS
set_option backward.isDefEq.respectTransparency false

section Field
variable {F : Type*} [Field F] {N : ℕ}

/-- Remove the first row and column by a scalar Schur complement. -/
def gaussianSchurTail (A : Matrix (Fin (N + 1)) (Fin (N + 1)) F) :
    Matrix (Fin N) (Fin N) F :=
  fun i j => A i.succ j.succ - A i.succ 0 * A 0 j.succ / A 0 0

/-- Lift a tail row to a row orthogonal to the first covariance coordinate. -/
def gaussianSchurRow (A : Matrix (Fin (N + 1)) (Fin (N + 1)) F)
    (x : Fin N → F) : Fin (N + 1) → F :=
  Fin.cons (-(∑ i, x i * A i.succ 0) / A 0 0) x

@[simp] theorem gaussianSchurRow_zero (A : Matrix (Fin (N + 1)) (Fin (N + 1)) F)
    (x : Fin N → F) : gaussianSchurRow A x 0 = -(∑ i, x i * A i.succ 0) / A 0 0 := rfl

@[simp] theorem gaussianSchurRow_succ (A : Matrix (Fin (N + 1)) (Fin (N + 1)) F)
    (x : Fin N → F) (i : Fin N) : gaussianSchurRow A x i.succ = x i := by
  simp [gaussianSchurRow]

theorem gaussianSchurRow_vecMul_zero (A : Matrix (Fin (N + 1)) (Fin (N + 1)) F)
    (ha : A 0 0 ≠ 0) (x : Fin N → F) : (gaussianSchurRow A x ᵥ* A) 0 = 0 := by
  simp only [vecMul, dotProduct, Fin.sum_univ_succ, gaussianSchurRow_zero,
    gaussianSchurRow_succ]
  field_simp
  ring

theorem gaussianSchurRow_vecMul_succ (A : Matrix (Fin (N + 1)) (Fin (N + 1)) F)
    (x : Fin N → F) (j : Fin N) :
    (gaussianSchurRow A x ᵥ* A) j.succ = (x ᵥ* gaussianSchurTail A) j := by
  simp only [vecMul, dotProduct, Fin.sum_univ_succ, gaussianSchurRow_zero,
    gaussianSchurRow_succ, gaussianSchurTail, mul_sub, Finset.sum_sub_distrib]
  have hs : (∑ i, x i * (A i.succ 0 * A 0 j.succ / A 0 0)) =
      (∑ i, x i * A i.succ 0) * A 0 j.succ / A 0 0 := by
    simp only [div_eq_mul_inv, ← mul_assoc, Finset.sum_mul]
  rw [hs]
  ring

theorem gaussianSchurRow_mulVec_zero (A : Matrix (Fin (N + 1)) (Fin (N + 1)) F)
    (hA : ∀ i j, A i j = A j i) (ha : A 0 0 ≠ 0) (x : Fin N → F) :
    (A *ᵥ gaussianSchurRow A x) 0 = 0 := by
  calc
    _ = (gaussianSchurRow A x ᵥ* A) 0 := by
      simp only [mulVec, vecMul, dotProduct]
      apply Finset.sum_congr rfl
      intro j _
      rw [hA 0 j, mul_comm]
    _ = 0 := gaussianSchurRow_vecMul_zero A ha x

theorem gaussianSchurRow_bilinear (A : Matrix (Fin (N + 1)) (Fin (N + 1)) F)
    (ha : A 0 0 ≠ 0) (x y : Fin N → F) :
    gaussianSchurRow A x ⬝ᵥ (A *ᵥ gaussianSchurRow A y) = x ⬝ᵥ (gaussianSchurTail A *ᵥ y) := by
  rw [dotProduct_mulVec, dotProduct_mulVec]
  simp only [dotProduct, Fin.sum_univ_succ, gaussianSchurRow_vecMul_zero A ha,
    gaussianSchurRow_succ, gaussianSchurRow_vecMul_succ, zero_mul, zero_add]

theorem gaussianSchurTail_symmetric (A : Matrix (Fin (N + 1)) (Fin (N + 1)) F)
    (hA : ∀ i j, A i j = A j i) :
    ∀ i j, gaussianSchurTail A i j = gaussianSchurTail A j i := by
  intro i j
  simp only [gaussianSchurTail, hA i.succ j.succ, hA 0 j.succ, hA 0 i.succ]
  ring

/-- Extend the tail elimination matrix, retaining a unit first diagonal entry. -/
def gaussianSchurLift (A : Matrix (Fin (N + 1)) (Fin (N + 1)) F)
    (U : Matrix (Fin N) (Fin N) F) : Matrix (Fin (N + 1)) (Fin (N + 1)) F :=
  Fin.cons (Fin.cons 1 (fun _ => 0)) (fun i => gaussianSchurRow A (U i))

@[simp] theorem gaussianSchurLift_zero (A : Matrix (Fin (N + 1)) (Fin (N + 1)) F)
    (U : Matrix (Fin N) (Fin N) F) : gaussianSchurLift A U 0 = Fin.cons 1 (fun _ => 0) := rfl

@[simp] theorem gaussianSchurLift_succ (A : Matrix (Fin (N + 1)) (Fin (N + 1)) F)
    (U : Matrix (Fin N) (Fin N) F) (i : Fin N) :
    gaussianSchurLift A U i.succ = gaussianSchurRow A (U i) := by simp [gaussianSchurLift]

theorem gaussianSchurLift_congruence (A : Matrix (Fin (N + 1)) (Fin (N + 1)) F)
    (hA : ∀ i j, A i j = A j i) (ha : A 0 0 ≠ 0)
    (U : Matrix (Fin N) (Fin N) F) (v : Fin N → F)
    (hU : U * gaussianSchurTail A * U.transpose = diagonal v) :
    gaussianSchurLift A U * A * (gaussianSchurLift A U).transpose = diagonal (Fin.cons (A 0 0) v) := by
  have entry (i j : Fin (N + 1)) :
      (gaussianSchurLift A U * A * (gaussianSchurLift A U).transpose) i j =
        gaussianSchurLift A U i ⬝ᵥ (A *ᵥ gaussianSchurLift A U j) := by
    simp only [mul_apply, transpose_apply, dotProduct, mulVec, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    ring
  ext i j
  rw [entry]
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
  · simp [dotProduct, mulVec, Fin.sum_univ_succ]
  · simp only [gaussianSchurLift_zero, gaussianSchurLift_succ, dotProduct,
      Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, one_mul, zero_mul,
      Finset.sum_const_zero, add_zero]
    rw [gaussianSchurRow_mulVec_zero A hA ha,
      diagonal_apply_ne _ (Fin.succ_ne_zero j).symm]
  · rw [gaussianSchurLift_succ, gaussianSchurLift_zero, dotProduct_mulVec]
    simp [dotProduct, Fin.sum_univ_succ, gaussianSchurRow_vecMul_zero A ha]
  · rw [gaussianSchurLift_succ, gaussianSchurLift_succ, gaussianSchurRow_bilinear A ha]
    have he := congrFun (congrFun hU i) j
    rw [dotProduct_mulVec]
    simpa only [mul_apply, transpose_apply, vecMul, dotProduct,
      diagonal_apply, Fin.succ_inj, Fin.cons_succ] using he

/-- Exact algebraic recursion. The finite implementation below stores every
Schur tail before continuing, so the recursive call is executed once. -/
def gaussianSchurFactor : (N : ℕ) → Matrix (Fin N) (Fin N) F →
    Matrix (Fin N) (Fin N) F × (Fin N → F)
  | 0, _ => (1, fun i => Fin.elim0 i)
  | N + 1, A =>
    let tail := gaussianSchurFactor N (gaussianSchurTail A)
    (gaussianSchurLift A tail.1, Fin.cons (A 0 0) tail.2)

theorem gaussianSchurFactor_unitLower (N : ℕ) (A : Matrix (Fin N) (Fin N) F) :
    (∀ i, (gaussianSchurFactor N A).1 i i = 1) ∧
      ∀ i j, i < j → (gaussianSchurFactor N A).1 i j = 0 := by
  induction N with
  | zero => exact ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  | succ N ih =>
    obtain ⟨hdiag, htri⟩ := ih (gaussianSchurTail A)
    constructor
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · simpa only [gaussianSchurFactor, gaussianSchurLift_succ, gaussianSchurRow_succ] using hdiag j
    · intro i j
      refine Fin.cases ?_ (fun i => ?_) i
      · refine Fin.cases ?_ (fun j => ?_) j
        · intro hij; exact (lt_irrefl _ hij).elim
        · intro _; rfl
      · refine Fin.cases ?_ (fun j => ?_) j
        · intro hij; exact (not_lt_of_ge (Fin.zero_le _) hij).elim
        · intro hij; exact htri i j (Fin.succ_lt_succ_iff.mp hij)

end Field

theorem gaussianSchurTail_posDef {N : ℕ}
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (hA : A.PosDef) :
    (gaussianSchurTail A).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · apply Matrix.IsHermitian.ext
    intro i j
    exact gaussianSchurTail_symmetric A (fun i j => (hA.isHermitian.apply j i)) j i
  · intro x hx
    have hrow : gaussianSchurRow A x ≠ 0 := by
      intro h
      apply hx
      funext i
      simpa only [gaussianSchurRow_succ, Pi.zero_apply] using congrFun h i.succ
    have h := hA.dotProduct_mulVec_pos hrow
    simpa only [star_trivial, gaussianSchurRow_bilinear A hA.diag_pos.ne'] using h

theorem gaussianSchurFactor_correct (N : ℕ) (A : Matrix (Fin N) (Fin N) ℝ)
    (hA : A.PosDef) :
    (gaussianSchurFactor N A).1 * A * (gaussianSchurFactor N A).1.transpose =
      diagonal (gaussianSchurFactor N A).2 ∧
      ∀ i, 0 < (gaussianSchurFactor N A).2 i := by
  induction N with
  | zero => exact ⟨by ext i; exact Fin.elim0 i, fun i => Fin.elim0 i⟩
  | succ N ih =>
    obtain ⟨hcong, hpos⟩ := ih (gaussianSchurTail A) (gaussianSchurTail_posDef A hA)
    refine ⟨gaussianSchurLift_congruence A (fun i j => hA.isHermitian.apply j i)
      hA.diag_pos.ne' _ _ hcong, ?_⟩
    intro i
    exact Fin.cases hA.diag_pos hpos i

end SISToKSIS

open GeometricGaussianLHL Matrix
namespace SISToKSIS
set_option backward.isDefEq.respectTransparency false

/-- Stored rational elimination rows and scalar covariance pivots. -/
structure GaussianSchurData (N : ℕ) where
  rows : RationalMatrixData N
  pivots : Vector ℚ N
  deriving Repr

/-- Every Schur entry is computed once and stored before the next recursion. -/
def gaussianSchurTailRun {N : ℕ} (A : RationalMatrixData (N + 1)) :
    Costed (RationalMatrixData N) :=
  costedRationalRectOfFn fun i j =>
    let C := rationalMatrixOfData A
    let product := costedRatMul (C i.succ 0) (C 0 j.succ)
    let quotient := costedRatDiv product.value (C 0 0)
    let difference := costedRatSub (C i.succ j.succ) quotient.value
    ⟨difference.value, product.steps + quotient.steps + difference.steps + 4⟩

theorem gaussianSchurTailRun_value {N : ℕ} (A : RationalMatrixData (N + 1)) :
    rationalMatrixOfData (gaussianSchurTailRun A).value =
      gaussianSchurTail (rationalMatrixOfData A) := by
  rw [gaussianSchurTailRun, costedRationalRectOfFn_data]
  change rationalMatrixOfData (rationalMatrixData _) = _
  rw [rationalMatrixOfData_data]
  rfl

/-- Reconstruct the first elimination column by charged rational dot products. -/
def gaussianSchurLiftRun {N : ℕ} (A : RationalMatrixData (N + 1))
    (U : RationalMatrixData N) : Costed (RationalMatrixData (N + 1)) :=
  costedRationalRectOfFn fun i j =>
    Fin.cases (Costed.charge 1 (Fin.cases 1 (fun _ => 0) j))
      (fun i => Fin.cases
        (let pairs := List.ofFn fun l => (rationalMatrixOfData U i l,
          rationalMatrixOfData A l.succ 0)
         let dot := costedRationalDot pairs
         let quotient := costedRatDiv (-dot.value) (rationalMatrixOfData A 0 0)
         ⟨quotient.value, N + 1 + dot.steps + rationalMagnitudeBits dot.value + 1 + quotient.steps⟩)
        (fun j => let q := rationalMatrixOfData U i j
          Costed.charge (rationalMagnitudeBits q + 1) q) j) i

theorem gaussianSchurLiftRun_value {N : ℕ} (A : RationalMatrixData (N + 1))
    (U : RationalMatrixData N) :
    rationalMatrixOfData (gaussianSchurLiftRun A U).value =
      gaussianSchurLift (rationalMatrixOfData A) (rationalMatrixOfData U) := by
  rw [gaussianSchurLiftRun, costedRationalRectOfFn_data]
  change rationalMatrixOfData (rationalMatrixData _) = _
  rw [rationalMatrixOfData_data]
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
  · rfl
  · rfl
  · simp [gaussianSchurLift, gaussianSchurRow, costedRatDiv, rationalListDot, List.sum_ofFn]
  · rfl

/-- Exact rational covariance elimination. The recursive result, stored tail,
and stored reconstruction are each evaluated once. -/
def gaussianSchurRun : (N : ℕ) → RationalMatrixData N → Costed (GaussianSchurData N)
  | 0, _ => ⟨⟨Vector.ofFn (fun i => Fin.elim0 i), Vector.ofFn (fun i => Fin.elim0 i)⟩, 3⟩
  | N + 1, A =>
    let tail := gaussianSchurTailRun A
    let rest := gaussianSchurRun N tail.value
    let rows := gaussianSchurLiftRun A rest.value.rows
    let pivots := costedVectorOfFn fun i : Fin (N + 1) =>
      let q := Fin.cases (rationalMatrixOfData A 0 0) (fun j => rest.value.pivots.get j) i
      Costed.charge (rationalMagnitudeBits q + 1) q
    ⟨⟨rows.value, pivots.value⟩, tail.steps + rest.steps + rows.steps + pivots.steps + 3⟩

theorem gaussianSchurRun_value (N : ℕ) (A : RationalMatrixData N) :
    (rationalMatrixOfData (gaussianSchurRun N A).value.rows,
      fun i => (gaussianSchurRun N A).value.pivots.get i) =
      gaussianSchurFactor N (rationalMatrixOfData A) := by
  induction N with
  | zero =>
    apply Prod.ext <;> funext i <;> exact Fin.elim0 i
  | succ N ih =>
    have h := ih (gaussianSchurTailRun A).value
    rw [gaussianSchurTailRun_value] at h
    apply Prod.ext
    · change rationalMatrixOfData (gaussianSchurLiftRun A
        (gaussianSchurRun N (gaussianSchurTailRun A).value).value.rows).value = _
      rw [gaussianSchurLiftRun_value]
      exact congrArg (gaussianSchurLift (rationalMatrixOfData A)) (congrArg Prod.fst h)
    · funext i
      simp only [gaussianSchurRun, costedVectorOfFn_value, Costed.charge,
        gaussianSchurFactor]
      simp only [Vector.get, Vector.toArray_ofFn, Array.getElem_ofFn, Fin.val_cast]
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · exact congrFun (congrArg Prod.snd h) j

end SISToKSIS

open GeometricGaussianLHL Matrix
namespace SISToKSIS
set_option backward.isDefEq.respectTransparency false

section Map
variable {F G : Type*} [Field F] [Field G] (f : F →+* G) {N : ℕ}

theorem gaussianSchurTail_map (A : Matrix (Fin (N + 1)) (Fin (N + 1)) F) :
    gaussianSchurTail (A.map f) = (gaussianSchurTail A).map f := by
  ext i j
  simp [gaussianSchurTail]

theorem gaussianSchurRow_map (A : Matrix (Fin (N + 1)) (Fin (N + 1)) F)
    (x : Fin N → F) : gaussianSchurRow (A.map f) (fun i => f (x i)) =
      fun i => f (gaussianSchurRow A x i) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [gaussianSchurRow]
  · simp

theorem gaussianSchurLift_map (A : Matrix (Fin (N + 1)) (Fin (N + 1)) F)
    (U : Matrix (Fin N) (Fin N) F) : gaussianSchurLift (A.map f) (U.map f) =
      (gaussianSchurLift A U).map f := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i
  · refine Fin.cases ?_ (fun j => ?_) j <;> simp
  · rw [gaussianSchurLift_succ]
    have he : (U.map f) i = fun j => f (U i j) := by funext j; rfl
    rw [he, gaussianSchurRow_map]
    rfl

theorem gaussianSchurFactor_map (N : ℕ) (A : Matrix (Fin N) (Fin N) F) :
    gaussianSchurFactor N (A.map f) =
      ((gaussianSchurFactor N A).1.map f, fun i => f ((gaussianSchurFactor N A).2 i)) := by
  induction N with
  | zero => exact Prod.ext (by ext i; exact Fin.elim0 i) (by funext i; exact Fin.elim0 i)
  | succ N ih =>
    simp only [gaussianSchurFactor, gaussianSchurTail_map, ih, gaussianSchurLift_map]
    apply Prod.ext
    · rfl
    · funext i
      exact Fin.cases rfl (fun _ => rfl) i

theorem gaussianSchurFactor_det (N : ℕ) (A : Matrix (Fin N) (Fin N) F) :
    (gaussianSchurFactor N A).1.det = 1 := by
  obtain ⟨hd, ht⟩ := gaussianSchurFactor_unitLower N A
  rw [Matrix.det_of_isLowerTriangular _ (fun _ _ h => ht _ _ h)]
  simp [hd]

end Map

/-- A lower covariance bound survives every pivot without dimension loss,
because each elimination row retains a unit diagonal entry. -/
theorem gaussianSchurFactor_width_lower (N : ℕ) (A : Matrix (Fin N) (Fin N) ℝ)
    (hA : A.PosDef) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hlower : ∀ x : Fin N → ℝ, ρ * (∑ j, x j ^ 2) ≤ x ⬝ᵥ (A *ᵥ x)) (i : Fin N) :
    ρ ≤ (gaussianSchurFactor N A).2 i := by
  let U := (gaussianSchurFactor N A).1
  have hdiag : U i i = 1 := (gaussianSchurFactor_unitLower N A).1 i
  have hnorm : 1 ≤ ∑ j, U i j ^ 2 := by
    have h := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin N))) =>
      sq_nonneg (U i j)) (Finset.mem_univ i)
    simpa only [hdiag, one_pow] using h
  have hentry := congrFun (congrFun (gaussianSchurFactor_correct N A hA).1 i) i
  change (U * A * U.transpose) i i = _ at hentry
  have he : U i ⬝ᵥ (A *ᵥ U i) = (gaussianSchurFactor N A).2 i := by
    rw [dotProduct_mulVec]
    simpa only [mul_apply, transpose_apply, vecMul, dotProduct, diagonal_apply_eq] using hentry
  calc
    ρ ≤ ρ * (∑ j, U i j ^ 2) := le_mul_of_one_le_right hρ hnorm
    _ ≤ U i ⬝ᵥ (A *ᵥ U i) := hlower (U i)
    _ = _ := he

/-- The stored rational algorithm inherits the real positive-definite
factorization through the exact rational-to-real embedding. -/
theorem gaussianSchurRun_correct (N : ℕ) (A : RationalMatrixData N)
    (hA : ((rationalMatrixOfData A).map (fun q : ℚ => (q : ℝ))).PosDef) :
    let U := (rationalMatrixOfData (gaussianSchurRun N A).value.rows).map (fun q : ℚ => (q : ℝ))
    let v := fun i => ((gaussianSchurRun N A).value.pivots.get i : ℝ)
    U * (rationalMatrixOfData A).map (fun q : ℚ => (q : ℝ)) * U.transpose = diagonal v ∧
      (∀ i, 0 < v i) ∧ (∀ i, U i i = 1) ∧ (∀ i j, i < j → U i j = 0) := by
  have hrun := gaussianSchurRun_value N A
  have hmap := gaussianSchurFactor_map (Rat.castHom ℝ) N (rationalMatrixOfData A)
  change gaussianSchurFactor N ((rationalMatrixOfData A).map (fun q : ℚ => (q : ℝ))) =
    ((gaussianSchurFactor N (rationalMatrixOfData A)).1.map (fun q : ℚ => (q : ℝ)),
      fun i => ((gaussianSchurFactor N (rationalMatrixOfData A)).2 i : ℝ)) at hmap
  have he : gaussianSchurFactor N ((rationalMatrixOfData A).map (fun q : ℚ => (q : ℝ))) =
      ((rationalMatrixOfData (gaussianSchurRun N A).value.rows).map (fun q : ℚ => (q : ℝ)),
        fun i => ((gaussianSchurRun N A).value.pivots.get i : ℝ)) := by
    rw [hmap, ← hrun]
  have hc := gaussianSchurFactor_correct N _ hA
  have hu := gaussianSchurFactor_unitLower N ((rationalMatrixOfData A).map (fun q : ℚ => (q : ℝ)))
  rw [he] at hc hu
  exact ⟨hc.1, hc.2, hu.1, hu.2⟩

end SISToKSIS

open GeometricGaussianLHL Matrix
namespace SISToKSIS
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The adaptive center is determined by the already sampled coordinates. -/
def gaussianSchurCenters {N : ℕ} (U : Matrix (Fin N) (Fin N) ℝ) : GaussianPrefixCenters N :=
  fun i z => -(∑ j : Fin i.val, U i ⟨j.val, lt_trans j.isLt i.isLt⟩ * (z j : ℝ))

theorem unitLower_mulVec {N : ℕ} (U : Matrix (Fin N) (Fin N) ℝ)
    (hd : ∀ i, U i i = 1) (ht : ∀ i j, i < j → U i j = 0)
    (x : Fin N → ℝ) (i : Fin N) :
    (U *ᵥ x) i = x i + ∑ j : Fin i.val,
      U i ⟨j.val, lt_trans j.isLt i.isLt⟩ * x ⟨j.val, lt_trans j.isLt i.isLt⟩ := by
  classical
  have hp : (∑ j : Fin i.val, U i ⟨j.val, lt_trans j.isLt i.isLt⟩ *
      x ⟨j.val, lt_trans j.isLt i.isLt⟩) =
      ∑ j ∈ Finset.univ.filter (fun j : Fin N => j < i), U i j * x j := by
    apply Finset.sum_bij (fun j _ => (⟨j.val, lt_trans j.isLt i.isLt⟩ : Fin N))
    · intro j _
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, j.isLt⟩
    · intro j _ l _ h
      exact Fin.ext (congrArg (fun j : Fin N => j.val) h)
    · intro j hj
      exact ⟨⟨j.val, (Finset.mem_filter.mp hj).2⟩, Finset.mem_univ _, rfl⟩
    · intro j _
      rfl
  have hrest : (∑ j ∈ Finset.univ.filter (fun j : Fin N => ¬j < i), U i j * x j) = x i := by
    rw [Finset.sum_eq_single i]
    · simp [hd]
    · intro j hj hji
      have hij : i < j := lt_of_le_of_ne (not_lt.mp (Finset.mem_filter.mp hj).2) hji.symm
      rw [ht i j hij, zero_mul]
    · simp
  rw [hp, ← hrest]
  simpa only [mulVec, dotProduct, add_comm] using
    (Finset.sum_filter_add_sum_filter_not (s := Finset.univ) (p := fun j : Fin N => j < i)
      (f := fun j => U i j * x j)).symm

theorem gaussianSchurCenters_residual {N : ℕ} (U : Matrix (Fin N) (Fin N) ℝ)
    (hd : ∀ i, U i i = 1) (ht : ∀ i j, i < j → U i j = 0)
    (z : Coeff N) (i : Fin N) :
    (z i : ℝ) - gaussianSchurCenters U i (prefixRestrict z i) =
      (U *ᵥ (fun j => (z j : ℝ))) i := by
  rw [unitLower_mulVec U hd ht]
  simp [gaussianSchurCenters, prefixRestrict]

/-- Normalize a covariance factor to an orthogonal matrix. This is a proof
identity; square roots are not used by the rational sampling program. -/
theorem covariance_factor_energy {N : ℕ} (B : Matrix (Fin N) (Fin N) ℝ)
    (v : Fin N → ℝ) (hv : ∀ i, 0 < v i) (hB : B * B.transpose = diagonal v)
    (x : Fin N → ℝ) : (∑ i, (B *ᵥ x) i ^ 2 / v i) = ∑ i, x i ^ 2 := by
  let R := diagonal (fun i => 1 / Real.sqrt (v i))
  let W := R * B
  have hscalar (i : Fin N) : (1 / Real.sqrt (v i)) * v i * (1 / Real.sqrt (v i)) = 1 := by
    have hs := (Real.sqrt_pos.mpr (hv i)).ne'
    field_simp
    exact (Real.sq_sqrt (hv i).le).symm
  have hdiag : R * diagonal v * R = 1 := by
    dsimp [R]
    rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
    simp only [hscalar, diagonal_one]
  have hW : W * W.transpose = 1 := by
    change (R * B) * (R * B).transpose = _
    rw [transpose_mul]
    have hR : R.transpose = R := diagonal_transpose _
    rw [hR]
    calc
      R * B * (B.transpose * R) = R * (B * B.transpose) * R := by simp only [mul_assoc]
      _ = 1 := by rw [hB, hdiag]
  have hWt : W.transpose * W = 1 := mul_eq_one_comm.mp hW
  have hn : (W *ᵥ x) ⬝ᵥ (W *ᵥ x) = x ⬝ᵥ x := by
    calc
      _ = x ⬝ᵥ (W.transpose *ᵥ (W *ᵥ x)) := by
        rw [dotProduct_mulVec x, vecMul_transpose]
      _ = x ⬝ᵥ x := by rw [mulVec_mulVec, hWt, one_mulVec]
  change (∑ i, (B *ᵥ x) i ^ 2 / v i) = _
  calc
    _ = (W *ᵥ x) ⬝ᵥ (W *ᵥ x) := by
      simp only [W, ← mulVec_mulVec, R, dotProduct, mulVec_diagonal]
      apply Finset.sum_congr rfl
      intro i _
      field_simp [(hv i).ne', (Real.sqrt_pos.mpr (hv i)).ne']
      rw [Real.sq_sqrt (hv i).le]
    _ = _ := by simpa only [dotProduct, sq] using hn

theorem schur_weight_of_covariance {N : ℕ} (U S : Matrix (Fin N) (Fin N) ℝ)
    (v : Fin N → ℝ) (hv : ∀ i, 0 < v i)
    (hd : ∀ i, U i i = 1) (ht : ∀ i j, i < j → U i j = 0)
    (hcov : U * (S * S.transpose) * U.transpose = diagonal v)
    (z : Coeff N) (x : Fin N → ℝ) (hx : S *ᵥ x = fun i => (z i : ℝ)) :
    triangularGaussianWeight (gaussianSchurCenters U) v z =
      gaussianWeight 1 (WithLp.toLp 2 x : Euclidean N) := by
  have hUS : (U * S) * (U * S).transpose = diagonal v := by
    rw [transpose_mul]
    simpa only [mul_assoc] using hcov
  have he := covariance_factor_energy (U * S) v hv hUS x
  rw [← mulVec_mulVec, hx] at he
  simp only [triangularGaussianWeight, scalarIdealWeight,
    gaussianSchurCenters_residual U hd ht, ← Real.exp_sum]
  rw [gaussianWeight, one_pow, mul_one, PiLp.norm_sq_eq_of_L2]
  congr 1
  calc
    (∑ i, -Real.pi * (U *ᵥ (fun j => (z j : ℝ))) i ^ 2 / v i) =
        -Real.pi * (∑ i, (U *ᵥ (fun j => (z j : ℝ))) i ^ 2 / v i) := by
      simp only [Finset.mul_sum, mul_div_assoc]
    _ = -Real.pi * (∑ i, x i ^ 2) := by rw [he]
    _ = _ := by simp only [Real.norm_eq_abs, sq_abs]

end
end SISToKSIS

open GeometricGaussianLHL Matrix
namespace SISToKSIS
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem schur_weight_eq_ellipsoid {N : ℕ} (U M : Matrix (Fin N) (Fin N) ℝ)
    (S : Euclidean N ≃L[ℝ] Euclidean N) (hM : Matrix.toEuclideanLin M = S.toLinearMap)
    (v : Fin N → ℝ) (hv : ∀ i, 0 < v i)
    (hd : ∀ i, U i i = 1) (ht : ∀ i j, i < j → U i j = 0)
    (hcov : U * (M * M.transpose) * U.transpose = diagonal v) (z : Coeff N) :
    triangularGaussianWeight (gaussianSchurCenters U) v z = ellipsoidWeight S 0 z := by
  have hx : M *ᵥ WithLp.ofLp (S.symm (integerEmbedding N z)) = fun i => (z i : ℝ) := by
    have he := congrArg (fun f : Euclidean N →ₗ[ℝ] Euclidean N =>
      f (S.symm (integerEmbedding N z))) hM
    have hf := congrArg WithLp.ofLp he
    change M *ᵥ WithLp.ofLp (S.symm (integerEmbedding N z)) =
      WithLp.ofLp (S (S.symm (integerEmbedding N z))) at hf
    rw [S.apply_symm_apply] at hf
    exact hf
  have hw := schur_weight_of_covariance U M v hv hd ht hcov z
    (WithLp.ofLp (S.symm (integerEmbedding N z))) hx
  simpa only [WithLp.toLp_ofLp, ellipsoidWeight, sub_zero] using hw

/-- The triangular target is exactly the existing ellipsoidal Gaussian;
only the previously quantified sequential and scalar errors are incurred. -/
theorem schur_law_eq_ellipsoidalGaussian {N : ℕ} (U M : Matrix (Fin N) (Fin N) ℝ)
    (S : Euclidean N ≃L[ℝ] Euclidean N) (hM : Matrix.toEuclideanLin M = S.toLinearMap)
    (v : Fin N → ℝ) (hv : ∀ i, 0 < v i)
    (hd : ∀ i, U i i = 1) (ht : ∀ i j, i < j → U i j = 0)
    (hcov : U * (M * M.transpose) * U.transpose = diagonal v) :
    triangularGaussianLaw (gaussianSchurCenters U) v hv = ellipsoidalGaussian S 0 := by
  have hw := schur_weight_eq_ellipsoid U M S hM v hv hd ht hcov
  have hp : triangularGaussianPartition (gaussianSchurCenters U) v = ellipsoidPartition S 0 := by
    unfold triangularGaussianPartition ellipsoidPartition
    exact tsum_congr hw
  ext z
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [triangularGaussianLaw_toReal, ellipsoidalGaussian_toReal, hw, hp]

theorem finiteSequentialGaussianLaw_ellipsoid_error {N : ℕ} (hN : 2 ≤ N)
    (U M : Matrix (Fin N) (Fin N) ℝ)
    (S : Euclidean N ≃L[ℝ] Euclidean N) (hM : Matrix.toEuclideanLin M = S.toLinearMap)
    (v : Fin N → ℝ) (hv : ∀ i, 0 < v i)
    (hd : ∀ i, U i i = 1) (ht : ∀ i j, i < j → U i j = 0)
    (hcov : U * (M * M.transpose) * U.transpose = diagonal v)
    (data : ∀ i : Fin N, Coeff i.val → ScalarGaussianData)
    (hdata : ∀ i z, (data i z).Valid)
    (hcenter : ∀ i z, (data i z).center = gaussianSchurCenters U i z)
    (hvariance : ∀ i z, (data i z).widthSq = v i)
    {ε : ℝ} (hε : 0 < ε) (hεone : ε ≤ 1)
    (hlog : ∀ i, 4 * Real.log ((N : ℝ) / ε) ≤ v i)
    (s : ℕ) (hbudget : (1 / 2 : ℝ) ^ s ≤ ε / 4) :
    discreteTotalVariation (finiteSequentialGaussianLaw data s) (ellipsoidalGaussian S 0) ≤ ε / 2 := by
  rw [← schur_law_eq_ellipsoidalGaussian U M S hM v hv hd ht hcov]
  exact finiteSequentialGaussianLaw_error hN data hdata (gaussianSchurCenters U) v hv
    hcenter hvariance hε hεone hlog s hbudget

end
end SISToKSIS


open GeometricGaussianLHL Matrix
namespace SISToKSIS
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem rationalMatrix_bits_le_entries {N L : ℕ} (A : Matrix (Fin N) (Fin N) ℚ)
    (hA : ∀ i j, rationalMagnitudeBits (A i j) ≤ L) :
    rationalMatrixMagnitudeBits A ≤ N * N * L := by
  calc
    _ ≤ ∑ _i : Fin N, ∑ _j : Fin N, L :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hA i j
    _ = _ := by simp; ring

/-- Determinants occur only in the size proof, not in the executable elimination. -/
theorem rationalMatrix_det_common_denominator {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℚ) :
    A.det = ((rationalMatrixCommonNumerators A).det : ℚ) /
      (rationalMatrixCommonDenominator A : ℚ) ^ N := by
  have hm : A = (1 / (rationalMatrixCommonDenominator A : ℚ)) •
      (rationalMatrixCommonNumerators A).map (fun z : ℤ => (z : ℚ)) := by
    ext i j
    have h := congrFun (congrFun (rationalMatrix_common_reconstruct A) i) j
    rw [integerMatrixQuotient_apply] at h
    simpa only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, one_div,
      div_eq_mul_inv, mul_comm, mul_one, one_mul] using h.symm
  calc
    A.det = ((1 / (rationalMatrixCommonDenominator A : ℚ)) •
        (rationalMatrixCommonNumerators A).map (fun z : ℤ => (z : ℚ))).det := congrArg Matrix.det hm
    _ = _ := by
      rw [Matrix.det_smul, ← Int.cast_det]
      simp only [Fintype.card_fin, div_eq_mul_inv, mul_one, inv_pow, mul_comm]

theorem rationalMatrix_det_den_le {N L : ℕ} (A : Matrix (Fin N) (Fin N) ℚ)
    (hA : ∀ i j, rationalMagnitudeBits (A i j) ≤ L) :
    A.det.den ≤ 2 ^ (N * (N * N * L)) := by
  have hd : A.det.den ∣ rationalMatrixCommonDenominator A ^ N := by
    have he : A.det = Rat.divInt (rationalMatrixCommonNumerators A).det
        ((rationalMatrixCommonDenominator A : ℤ) ^ N) := by
      rw [rationalMatrix_det_common_denominator]
      simp only [Rat.divInt_eq_div, Int.cast_pow, Int.cast_natCast]
    have h := Rat.den_dvd (rationalMatrixCommonNumerators A).det
      ((rationalMatrixCommonDenominator A : ℤ) ^ N)
    rw [← he] at h
    exact_mod_cast h
  have hb : rationalMatrixCommonDenominator A ≤ 2 ^ (N * N * L) :=
    (rationalMatrixCommonDenominator_le_pow A).trans
      (Nat.pow_le_pow_right (by decide) (rationalMatrix_bits_le_entries A hA))
  calc
    A.det.den ≤ rationalMatrixCommonDenominator A ^ N :=
      Nat.le_of_dvd (pow_pos (rationalMatrixCommonDenominator_pos A) _) hd
    _ ≤ (2 ^ (N * N * L)) ^ N := Nat.pow_le_pow_left hb _
    _ = _ := by rw [← pow_mul, Nat.mul_comm]

theorem rationalMatrix_det_abs_le {N L : ℕ} (A : Matrix (Fin N) (Fin N) ℚ)
    (hA : ∀ i j, rationalMagnitudeBits (A i j) ≤ L) :
    |A.det| ≤ (2 : ℚ) ^ (N * N + N * L) := by
  have hb (i j : Fin N) : |A i j| ≤ (2 : ℚ) ^ L :=
    (rational_abs_le_pow_bits _).trans (pow_le_pow_right₀ (by norm_num) (hA i j))
  have hfac : N.factorial ≤ 2 ^ (N * N) := by
    calc
      _ ≤ N ^ N := Nat.factorial_le_pow N
      _ ≤ (2 ^ N) ^ N := Nat.pow_le_pow_left (Nat.lt_two_pow_self (n := N)).le N
      _ = _ := by rw [← pow_mul]
  calc
    |A.det| ≤ ∑ σ : Equiv.Perm (Fin N),
        |((Equiv.Perm.sign σ : ℤ) : ℚ) * ∏ i, A (σ i) i| := by
      rw [Matrix.det_apply']
      exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ σ : Equiv.Perm (Fin N), ∏ i, |A (σ i) i| := by
      apply Finset.sum_congr rfl
      intro σ _
      simp only [abs_mul, ← Int.cast_abs, Equiv.Perm.sign_abs, Int.cast_one,
        one_mul, Finset.abs_prod]
    _ ≤ ∑ _σ : Equiv.Perm (Fin N), (2 : ℚ) ^ (N * L) := by
      apply Finset.sum_le_sum
      intro σ _
      calc
        _ ≤ ∏ _i : Fin N, (2 : ℚ) ^ L := Finset.prod_le_prod
          (fun i _ => abs_nonneg _) (fun i _ => hb (σ i) i)
        _ = _ := by simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
            ← pow_mul, Nat.mul_comm]
    _ = (N.factorial : ℚ) * (2 : ℚ) ^ (N * L) := by
      simp [Fintype.card_perm]
    _ ≤ (2 : ℚ) ^ (N * N) * (2 : ℚ) ^ (N * L) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hfac) (by positivity)
    _ = _ := by rw [pow_add]

def rationalDetBitsBudget (N L : ℕ) : ℕ := N * N + N * L + 2 * (N * (N * N * L)) + 3

theorem rationalMatrix_det_bits {N L : ℕ} (A : Matrix (Fin N) (Fin N) ℚ)
    (hA : ∀ i j, rationalMagnitudeBits (A i j) ≤ L) :
    rationalMagnitudeBits A.det ≤ rationalDetBitsBudget N L :=
  rational_bits_le_of_den_abs _ _ _ (rationalMatrix_det_den_le A hA) (rationalMatrix_det_abs_le A hA)

def rationalInverseBitsBudget (N L : ℕ) : ℕ := 6 * rationalDetBitsBudget N (L + 3) + 3

/-- A uniform polynomial size bound for every entry of the mathematical
inverse, including singular inputs. No determinant evaluation is charged. -/
theorem rationalMatrix_inverse_bits {N L : ℕ} (A : Matrix (Fin N) (Fin N) ℚ)
    (hA : ∀ i j, rationalMagnitudeBits (A i j) ≤ L) (i j : Fin N) :
    rationalMagnitudeBits (A⁻¹ i j) ≤ rationalInverseBitsBudget N L := by
  have hA' : ∀ i j, rationalMagnitudeBits (A i j) ≤ L + 3 := fun i j => (hA i j).trans (by omega)
  have hadj : rationalMagnitudeBits (A.adjugate i j) ≤ rationalDetBitsBudget N (L + 3) := by
    rw [Matrix.adjugate_apply]
    apply rationalMatrix_det_bits
    intro a b
    by_cases h : a = j
    · subst a
      simp only [Matrix.updateRow_self, Pi.single_apply]
      split_ifs
      · have h1 : rationalMagnitudeBits (1 : ℚ) = 3 := by decide
        rw [h1]; omega
      · have h0 : rationalMagnitudeBits (0 : ℚ) = 2 := by decide
        rw [h0]; omega
    · simpa only [Matrix.updateRow_apply, h, ↓reduceIte] using hA' a b
  rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv]
  exact rational_mul_bits_le _ _ _
    (by rw [rational_inv_bits]; exact rationalMatrix_det_bits A hA') hadj

theorem rationalInverseBitsBudget_mono {N M L B : ℕ} (hN : N ≤ M) (hL : L ≤ B) :
    rationalInverseBitsBudget N L ≤ rationalInverseBitsBudget M B := by
  unfold rationalInverseBitsBudget rationalDetBitsBudget
  gcongr

theorem rationalPosDef_isUnitDet {N : ℕ} (A : Matrix (Fin N) (Fin N) ℚ)
    (hA : (A.map (fun q : ℚ => (q : ℝ))).PosDef) : IsUnit A.det := by
  apply isUnit_iff_ne_zero.mpr
  intro hz
  have h := hA.det_pos
  rw [← Rat.cast_det, hz] at h
  norm_num at h

/-- One inverse identity controls all recursive Schur tails through
submatrices of the original inverse. -/
theorem gaussianSchurTail_inverse {F : Type*} [Field F] {N : ℕ}
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) F)
    (ha : A 0 0 ≠ 0) (hA : IsUnit A.det) :
    (gaussianSchurTail A)⁻¹ = A⁻¹.submatrix Fin.succ Fin.succ := by
  let E := gaussianSchurLift A 1
  have hzero (i : Fin N) : (E * A) i.succ 0 = 0 := by
    change (gaussianSchurRow A ((1 : Matrix (Fin N) (Fin N) F) i) ᵥ* A) 0 = 0
    exact gaussianSchurRow_vecMul_zero A ha _
  have hsucc (i j : Fin N) : (E * A) i.succ j.succ = gaussianSchurTail A i j := by
    change (gaussianSchurRow A ((1 : Matrix (Fin N) (Fin N) F) i) ᵥ* A) j.succ = _
    rw [gaussianSchurRow_vecMul_succ]
    change ((1 : Matrix (Fin N) (Fin N) F) * gaussianSchurTail A) i j = _
    rw [Matrix.one_mul]
  have hid : E * A * A⁻¹ = E := Matrix.mul_nonsing_inv_cancel_right A E hA
  apply Matrix.inv_eq_right_inv
  ext i j
  have he := congrFun (congrFun hid i.succ) j.succ
  rw [Matrix.mul_apply, Fin.sum_univ_succ, hzero, zero_mul, zero_add] at he
  simpa only [Matrix.mul_apply, Matrix.submatrix_apply, hsucc, E,
    gaussianSchurLift_succ, gaussianSchurRow_succ] using he

end
end SISToKSIS

open GeometricGaussianLHL Matrix
namespace SISToKSIS
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem rationalSchurTail_posDef {N : ℕ} (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℚ)
    (hA : (A.map (fun q : ℚ => (q : ℝ))).PosDef) :
    ((gaussianSchurTail A).map (fun q : ℚ => (q : ℝ))).PosDef := by
  have h := gaussianSchurTail_posDef (A.map (Rat.castHom ℝ)) hA
  rw [gaussianSchurTail_map] at h
  exact h

theorem rationalSchurPivot_ne_zero {N : ℕ} (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℚ)
    (hA : (A.map (fun q : ℚ => (q : ℝ))).PosDef) : A 0 0 ≠ 0 := by
  intro hz
  have h := hA.diag_pos (i := 0)
  simp only [Matrix.map_apply, hz, Rat.cast_zero, lt_self_iff_false] at h

theorem gaussianSchurFactor_mul_upper (N : ℕ) (A : Matrix (Fin N) (Fin N) ℚ)
    (hA : (A.map (fun q : ℚ => (q : ℝ))).PosDef) :
    (∀ i j, j < i → ((gaussianSchurFactor N A).1 * A) i j = 0) ∧
      ∀ i, ((gaussianSchurFactor N A).1 * A) i i = (gaussianSchurFactor N A).2 i := by
  induction N with
  | zero => exact ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  | succ N ih =>
    obtain ⟨hupper, hdiag⟩ := ih (gaussianSchurTail A) (rationalSchurTail_posDef A hA)
    have hzero (i : Fin N) : ((gaussianSchurFactor (N + 1) A).1 * A) i.succ 0 = 0 := by
      exact gaussianSchurRow_vecMul_zero A (rationalSchurPivot_ne_zero A hA) _
    have hsucc (i j : Fin N) : ((gaussianSchurFactor (N + 1) A).1 * A) i.succ j.succ =
        ((gaussianSchurFactor N (gaussianSchurTail A)).1 * gaussianSchurTail A) i j := by
      exact gaussianSchurRow_vecMul_succ A _ j
    constructor
    · intro i j
      refine Fin.cases ?_ (fun i => ?_) i
      · intro h; exact (not_lt_of_ge (Fin.zero_le _) h).elim
      · refine Fin.cases ?_ (fun j => ?_) j
        · intro _; exact hzero i
        · intro h; rw [hsucc]; exact hupper i j (Fin.succ_lt_succ_iff.mp h)
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · simp [gaussianSchurFactor, Matrix.mul_apply, Fin.sum_univ_succ]
      · rw [hsucc, hdiag]
        rfl

def gaussianLeadingIndex {N : ℕ} (i : Fin N) (j : Fin (i.val + 1)) : Fin N :=
  ⟨j.val, lt_of_lt_of_le j.isLt (Nat.succ_le_iff.mpr i.isLt)⟩

theorem gaussianLeadingIndex_injective {N : ℕ} (i : Fin N) :
    Function.Injective (gaussianLeadingIndex i) := by
  intro a b h
  exact Fin.ext (congrArg (fun j : Fin N => j.val) h)

@[simp] theorem gaussianLeadingIndex_last {N : ℕ} (i : Fin N) :
    gaussianLeadingIndex i (Fin.last i.val) = i := by ext; rfl

def gaussianLeadingMatrix {N : ℕ} (A : Matrix (Fin N) (Fin N) ℚ) (i : Fin N) :
    Matrix (Fin (i.val + 1)) (Fin (i.val + 1)) ℚ :=
  A.submatrix (gaussianLeadingIndex i) (gaussianLeadingIndex i)

theorem fin_sum_prefix {F : Type*} [AddCommMonoid F] {N k : ℕ} (hk : k ≤ N)
    (f : Fin N → F) (hf : ∀ i, k ≤ i.val → f i = 0) :
    (∑ i, f i) = ∑ i : Fin k, f ⟨i.val, lt_of_lt_of_le i.isLt hk⟩ := by
  classical
  symm
  apply Finset.sum_bij_ne_zero
    (fun i _ _ => (⟨i.val, lt_of_lt_of_le i.isLt hk⟩ : Fin N))
  · intro _ _ _; exact Finset.mem_univ _
  · intro a _ _ b _ _ h
    exact Fin.ext (congrArg (fun j : Fin N => j.val) h)
  · intro i _ hi
    have hik : i.val < k := by
      by_contra h
      exact hi (hf i (not_lt.mp h))
    exact ⟨⟨i.val, hik⟩, Finset.mem_univ _, hi, rfl⟩
  · intro _ _ _; rfl

/-- Each unit elimination row is a normalized row of a leading principal
inverse. This identity bounds rational sizes without recursive inflation. -/
theorem gaussianSchurFactor_row_inverse (N : ℕ) (A : Matrix (Fin N) (Fin N) ℚ)
    (hA : (A.map (fun q : ℚ => (q : ℝ))).PosDef) (i : Fin N)
    (j : Fin (i.val + 1)) :
    (gaussianSchurFactor N A).1 i (gaussianLeadingIndex i j) =
      (gaussianLeadingMatrix A i)⁻¹ (Fin.last i.val) j /
        (gaussianLeadingMatrix A i)⁻¹ (Fin.last i.val) (Fin.last i.val) := by
  classical
  let U := (gaussianSchurFactor N A).1
  let v := (gaussianSchurFactor N A).2
  let P := gaussianLeadingMatrix A i
  let row := fun j => U i (gaussianLeadingIndex i j)
  have hP : IsUnit P.det := rationalPosDef_isUnitDet P
    (hA.submatrix (gaussianLeadingIndex_injective i))
  obtain ⟨hd, ht⟩ := gaussianSchurFactor_unitLower N A
  obtain ⟨hu, hv⟩ := gaussianSchurFactor_mul_upper N A hA
  have hmul (j : Fin (i.val + 1)) : (row ᵥ* P) j = (U * A) i (gaussianLeadingIndex i j) := by
    symm
    exact fin_sum_prefix (Nat.succ_le_iff.mpr i.isLt)
      (fun l => U i l * A l (gaussianLeadingIndex i j)) (fun l hl => by
        rw [show U i l = 0 from ht i l (show i < l from hl), zero_mul])
  have hr : row ᵥ* P = Pi.single (Fin.last i.val) (v i) := by
    funext j
    rw [hmul]
    by_cases hj : j = Fin.last i.val
    · subst j
      simp only [gaussianLeadingIndex_last, Pi.single_eq_same]
      exact hv i
    · have hji : gaussianLeadingIndex i j < i := by
        have hne : j.val ≠ i.val := fun h => hj (Fin.ext h)
        have hjle : j.val ≤ i.val := Nat.le_of_lt_succ j.isLt
        change j.val < i.val
        exact lt_of_le_of_ne hjle hne
      rw [show (U * A) i (gaussianLeadingIndex i j) = 0 from hu i _ hji]
      simp [hj]
  have hinv : (row ᵥ* P) ᵥ* P⁻¹ = row := by
    rw [vecMul_vecMul, Matrix.mul_nonsing_inv _ hP, vecMul_one]
  rw [hr] at hinv
  have he (j : Fin (i.val + 1)) : row j = v i * P⁻¹ (Fin.last i.val) j := by
    simpa [vecMul, dotProduct, Pi.single_apply] using (congrFun hinv j).symm
  have hone : v i * P⁻¹ (Fin.last i.val) (Fin.last i.val) = 1 := by
    rw [← he]
    exact (congrArg (U i) (gaussianLeadingIndex_last i)).trans (hd i)
  have hn : P⁻¹ (Fin.last i.val) (Fin.last i.val) ≠ 0 := by
    intro h
    rw [h, mul_zero] at hone
    exact zero_ne_one hone
  change row j = P⁻¹ (Fin.last i.val) j / P⁻¹ (Fin.last i.val) (Fin.last i.val)
  apply (eq_div_iff hn).mpr
  rw [he]
  calc
    v i * P⁻¹ (Fin.last i.val) j * P⁻¹ (Fin.last i.val) (Fin.last i.val) =
        (v i * P⁻¹ (Fin.last i.val) (Fin.last i.val)) * P⁻¹ (Fin.last i.val) j := by ring
    _ = _ := by rw [hone, one_mul]

def gaussianSchurRowBitsBudget (N L : ℕ) : ℕ := 6 * rationalInverseBitsBudget N L + 3

theorem gaussianSchurFactor_rows_bits {N L : ℕ} (A : Matrix (Fin N) (Fin N) ℚ)
    (hA : (A.map (fun q : ℚ => (q : ℝ))).PosDef)
    (hbits : ∀ i j, rationalMagnitudeBits (A i j) ≤ L) (i j : Fin N) :
    rationalMagnitudeBits ((gaussianSchurFactor N A).1 i j) ≤ gaussianSchurRowBitsBudget N L := by
  by_cases hij : i < j
  · rw [(gaussianSchurFactor_unitLower N A).2 i j hij]
    have h0 : rationalMagnitudeBits (0 : ℚ) = 2 := by decide
    rw [h0]
    unfold gaussianSchurRowBitsBudget
    omega
  · let t : Fin (i.val + 1) := ⟨j.val, Nat.lt_succ_iff.mpr (not_lt.mp hij)⟩
    have ht : gaussianLeadingIndex i t = j := by ext; rfl
    rw [← ht, gaussianSchurFactor_row_inverse N A hA i t]
    have hi (a b : Fin (i.val + 1)) :
        rationalMagnitudeBits ((gaussianLeadingMatrix A i)⁻¹ a b) ≤ rationalInverseBitsBudget N L :=
      (rationalMatrix_inverse_bits _ (fun a b => hbits _ _) a b).trans
        (rationalInverseBitsBudget_mono (Nat.succ_le_iff.mpr i.isLt) le_rfl)
    exact rational_div_bits_le _ _ _ (hi _ _) (hi _ _)

end
end SISToKSIS

open GeometricGaussianLHL Matrix
namespace SISToKSIS
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem rationalMatrix_bits_of_inverse_submatrix {N M L : ℕ}
    (A : Matrix (Fin M) (Fin M) ℚ) (hA : IsUnit A.det)
    (Q : Matrix (Fin N) (Fin N) ℚ) (hQ : ∀ i j, rationalMagnitudeBits (Q i j) ≤ L)
    (e : Fin M → Fin N) (he : A⁻¹ = Q.submatrix e e) (hM : M ≤ N) (i j : Fin M) :
    rationalMagnitudeBits (A i j) ≤ rationalInverseBitsBudget N L := by
  have h := rationalMatrix_inverse_bits (Q.submatrix e e) (fun i j => hQ (e i) (e j)) i j
  rw [← he, Matrix.nonsing_inv_nonsing_inv A hA] at h
  exact h.trans (rationalInverseBitsBudget_mono hM le_rfl)

theorem gaussianSchurTail_inverse_submatrix {N M : ℕ}
    (A : Matrix (Fin (M + 1)) (Fin (M + 1)) ℚ)
    (hA : (A.map (fun q : ℚ => (q : ℝ))).PosDef)
    (Q : Matrix (Fin N) (Fin N) ℚ) (e : Fin (M + 1) → Fin N)
    (he : A⁻¹ = Q.submatrix e e) :
    (gaussianSchurTail A)⁻¹ = Q.submatrix (fun i => e i.succ) (fun i => e i.succ) := by
  rw [gaussianSchurTail_inverse A (rationalSchurPivot_ne_zero A hA)
    (rationalPosDef_isUnitDet A hA), he, Matrix.submatrix_submatrix]
  rfl

/-- Uniformly bound every pivot in the recursion by keeping the original
inverse fixed. The dimension of each subsequent submatrix only decreases. -/
theorem gaussianSchurFactor_pivots_bits_of_inverse_submatrix {N L : ℕ}
    (Q : Matrix (Fin N) (Fin N) ℚ) (hQ : ∀ i j, rationalMagnitudeBits (Q i j) ≤ L)
    (M : ℕ) (A : Matrix (Fin M) (Fin M) ℚ)
    (hA : (A.map (fun q : ℚ => (q : ℝ))).PosDef)
    (e : Fin M → Fin N) (he : A⁻¹ = Q.submatrix e e) (hM : M ≤ N) (i : Fin M) :
    rationalMagnitudeBits ((gaussianSchurFactor M A).2 i) ≤ rationalInverseBitsBudget N L := by
  induction M with
  | zero => exact Fin.elim0 i
  | succ M ih =>
    refine Fin.cases ?_ (fun i => ?_) i
    · exact rationalMatrix_bits_of_inverse_submatrix A (rationalPosDef_isUnitDet A hA)
        Q hQ e he hM 0 0
    · exact ih (gaussianSchurTail A) (rationalSchurTail_posDef A hA)
        (fun j => e j.succ) (gaussianSchurTail_inverse_submatrix A hA Q e he)
        (by omega) i

theorem gaussianSchurFactor_pivots_bits {N L : ℕ} (A : Matrix (Fin N) (Fin N) ℚ)
    (hA : (A.map (fun q : ℚ => (q : ℝ))).PosDef)
    (hbits : ∀ i j, rationalMagnitudeBits (A i j) ≤ L) (i : Fin N) :
    rationalMagnitudeBits ((gaussianSchurFactor N A).2 i) ≤
      rationalInverseBitsBudget N (rationalInverseBitsBudget N L) :=
  gaussianSchurFactor_pivots_bits_of_inverse_submatrix A⁻¹
    (rationalMatrix_inverse_bits A hbits) N A hA id (by simp) le_rfl i

theorem gaussianSchurRun_output_bits {N L : ℕ} (A : RationalMatrixData N)
    (hA : ((rationalMatrixOfData A).map (fun q : ℚ => (q : ℝ))).PosDef)
    (hbits : ∀ i j, rationalMagnitudeBits (rationalMatrixOfData A i j) ≤ L) :
    (∀ i j, rationalMagnitudeBits (rationalMatrixOfData (gaussianSchurRun N A).value.rows i j) ≤
      gaussianSchurRowBitsBudget N L) ∧
    (∀ i, rationalMagnitudeBits ((gaussianSchurRun N A).value.pivots.get i) ≤
      rationalInverseBitsBudget N (rationalInverseBitsBudget N L)) := by
  have he := gaussianSchurRun_value N A
  constructor
  · intro i j
    have h := congrFun (congrFun (congrArg Prod.fst he) i) j
    change rationalMatrixOfData (gaussianSchurRun N A).value.rows i j =
      (gaussianSchurFactor N (rationalMatrixOfData A)).1 i j at h
    rw [h]
    exact gaussianSchurFactor_rows_bits _ hA hbits i j
  · intro i
    have h := congrFun (congrArg Prod.snd he) i
    change (gaussianSchurRun N A).value.pivots.get i =
      (gaussianSchurFactor N (rationalMatrixOfData A)).2 i at h
    rw [h]
    exact gaussianSchurFactor_pivots_bits _ hA hbits i

end
end SISToKSIS

open GeometricGaussianLHL Matrix
namespace SISToKSIS
set_option backward.isDefEq.respectTransparency false

def gaussianSchurTailCost (N L : ℕ) : ℕ :=
  rationalRectTraversalBudget N N (3 * (2 * (40 * (L + 1)) + 1) ^ 3 + 4)

theorem gaussianSchurTailRun_steps_le {N : ℕ} (A : RationalMatrixData (N + 1)) (L : ℕ)
    (hA : ∀ i j, rationalMagnitudeBits (rationalMatrixOfData A i j) ≤ L) :
    (gaussianSchurTailRun A).steps ≤ gaussianSchurTailCost N L := by
  unfold gaussianSchurTailRun gaussianSchurTailCost
  apply costedRationalRectOfFn_steps_le
  intro i j
  let C := rationalMatrixOfData A
  let K := 40 * (L + 1)
  have hLK : L ≤ K := by dsimp [K]; omega
  have hp : rationalMagnitudeBits (C i.succ 0 * C 0 j.succ) ≤ 6 * L + 3 :=
    rational_mul_bits_le _ _ _ (hA _ _) (hA _ _)
  have hq : rationalMagnitudeBits ((C i.succ 0 * C 0 j.succ) / C 0 0) ≤ K := by
    have h : rationalMagnitudeBits ((C i.succ 0 * C 0 j.succ) / C 0 0) ≤ 6 * (6 * L + 3) + 3 :=
      rational_div_bits_le _ _ (6 * L + 3) hp ((hA 0 0).trans (by omega))
    dsimp [K]
    omega
  have h1 := rationalArithmeticCost_le (C i.succ 0) (C 0 j.succ)
    ((hA _ _).trans hLK) ((hA _ _).trans hLK)
  have h2 := rationalArithmeticCost_le (C i.succ 0 * C 0 j.succ) (C 0 0)
    (hp.trans (by dsimp [K]; omega)) ((hA _ _).trans hLK)
  have h3 := rationalArithmeticCost_le (C i.succ j.succ)
    ((C i.succ 0 * C 0 j.succ) / C 0 0) ((hA _ _).trans hLK) hq
  change rationalArithmeticCost (C i.succ 0) (C 0 j.succ) +
    rationalArithmeticCost (C i.succ 0 * C 0 j.succ) (C 0 0) +
    rationalArithmeticCost (C i.succ j.succ) ((C i.succ 0 * C 0 j.succ) / C 0 0) + 4 ≤
      3 * (2 * K + 1) ^ 3 + 4
  omega

def gaussianSchurLiftCost (N L : ℕ) : ℕ :=
  rationalRectTraversalBudget (N + 1) (N + 1)
    (N + 1 + rationalDotBudget N L + rationalDotOperandBudget N L + 1 +
      (2 * rationalDotOperandBudget N L + 1) ^ 3 + L + 1)

theorem gaussianSchurLiftRun_steps_le {N : ℕ} (A : RationalMatrixData (N + 1))
    (U : RationalMatrixData N) (L : ℕ)
    (hA : ∀ i j, rationalMagnitudeBits (rationalMatrixOfData A i j) ≤ L)
    (hU : ∀ i j, rationalMagnitudeBits (rationalMatrixOfData U i j) ≤ L) :
    (gaussianSchurLiftRun A U).steps ≤ gaussianSchurLiftCost N L := by
  unfold gaussianSchurLiftRun gaussianSchurLiftCost
  apply costedRationalRectOfFn_steps_le
  intro i j
  refine Fin.cases ?_ (fun i => ?_) i
  · change 1 ≤ _
    omega
  · refine Fin.cases ?_ (fun j => ?_) j
    · let pairs := List.ofFn fun l => (rationalMatrixOfData U i l, rationalMatrixOfData A l.succ 0)
      have hp : ∀ x ∈ pairs, rationalMagnitudeBits x.1 ≤ L ∧ rationalMagnitudeBits x.2 ≤ L := by
        intro x hx
        obtain ⟨l, rfl⟩ := List.mem_ofFn.mp hx
        exact ⟨hU i l, hA l.succ 0⟩
      have hlen : pairs.length = N := List.length_ofFn
      have hd := costedRationalDot_steps_le pairs L hp
      have hb := rationalListDot_bits pairs L hp
      rw [hlen] at hd hb
      have hL : L ≤ rationalDotOperandBudget N L := by unfold rationalDotOperandBudget; omega
      have hdiv := rationalArithmeticCost_le (-(costedRationalDot pairs).value)
        (rationalMatrixOfData A 0 0)
        (by rw [rational_neg_bits, costedRationalDot_value]; exact hb) ((hA 0 0).trans hL)
      change N + 1 + (costedRationalDot pairs).steps +
        rationalMagnitudeBits (costedRationalDot pairs).value + 1 +
        rationalArithmeticCost (-(costedRationalDot pairs).value) (rationalMatrixOfData A 0 0) ≤ _
      rw [costedRationalDot_value]
      rw [costedRationalDot_value] at hdiv
      omega
    · change rationalMagnitudeBits (rationalMatrixOfData U i j) + 1 ≤ _
      have h := hU i j
      omega

theorem gaussianSchurTailCost_mono {N M L B : ℕ} (hN : N ≤ M) (hL : L ≤ B) :
    gaussianSchurTailCost N L ≤ gaussianSchurTailCost M B := by
  unfold gaussianSchurTailCost rationalRectTraversalBudget
  gcongr

theorem gaussianSchurLiftCost_mono {N M L B : ℕ} (hN : N ≤ M) (hL : L ≤ B) :
    gaussianSchurLiftCost N L ≤ gaussianSchurLiftCost M B := by
  unfold gaussianSchurLiftCost rationalRectTraversalBudget rationalDotBudget rationalDotOperandBudget
  gcongr

def gaussianSchurStageBits (N L : ℕ) : ℕ :=
  rationalInverseBitsBudget N L + gaussianSchurRowBitsBudget N (rationalInverseBitsBudget N L) + 1

def gaussianSchurStageCost (N L : ℕ) : ℕ :=
  gaussianSchurTailCost N (gaussianSchurStageBits N L) +
    gaussianSchurLiftCost N (gaussianSchurStageBits N L) +
    (N + 1) * (gaussianSchurStageBits N L + 4) + 4

end SISToKSIS

open GeometricGaussianLHL Matrix
namespace SISToKSIS
set_option backward.isDefEq.respectTransparency false

theorem gaussianSchurRun_steps_of_inverse_submatrix {N L : ℕ}
    (Q : Matrix (Fin N) (Fin N) ℚ) (hQ : ∀ i j, rationalMagnitudeBits (Q i j) ≤ L)
    (M : ℕ) (A : RationalMatrixData M)
    (hA : ((rationalMatrixOfData A).map (fun q : ℚ => (q : ℝ))).PosDef)
    (e : Fin M → Fin N) (he : (rationalMatrixOfData A)⁻¹ = Q.submatrix e e) (hM : M ≤ N) :
    (gaussianSchurRun M A).steps ≤ M * gaussianSchurStageCost N L + 3 := by
  induction M with
  | zero => simp [gaussianSchurRun]
  | succ M ih =>
    let C := rationalMatrixOfData A
    let tail := gaussianSchurTailRun A
    let rest := gaussianSchurRun M tail.value
    let B := rationalInverseBitsBudget N L
    let K := gaussianSchurStageBits N L
    have hMK : M ≤ N := by omega
    have hBK : B ≤ K := by dsimp [B, K, gaussianSchurStageBits]; omega
    have hbits : ∀ i j, rationalMagnitudeBits (C i j) ≤ B :=
      rationalMatrix_bits_of_inverse_submatrix C (rationalPosDef_isUnitDet C hA) Q hQ e he hM
    have htval : rationalMatrixOfData tail.value = gaussianSchurTail C := gaussianSchurTailRun_value A
    have htpos : ((rationalMatrixOfData tail.value).map (fun q : ℚ => (q : ℝ))).PosDef := by
      rw [htval]
      exact rationalSchurTail_posDef C hA
    have htinv : (rationalMatrixOfData tail.value)⁻¹ =
        Q.submatrix (fun i => e i.succ) (fun i => e i.succ) := by
      rw [htval]
      exact gaussianSchurTail_inverse_submatrix C hA Q e he
    have htbits : ∀ i j, rationalMagnitudeBits (rationalMatrixOfData tail.value i j) ≤ B :=
      rationalMatrix_bits_of_inverse_submatrix _ (rationalPosDef_isUnitDet _ htpos)
        Q hQ _ htinv hMK
    have hrest := ih tail.value htpos (fun i => e i.succ) htinv hMK
    change rest.steps ≤ M * gaussianSchurStageCost N L + 3 at hrest
    have hrows : ∀ i j, rationalMagnitudeBits (rationalMatrixOfData rest.value.rows i j) ≤ K := by
      intro i j
      have h := (gaussianSchurRun_output_bits tail.value htpos htbits).1 i j
      have hm := rationalInverseBitsBudget_mono (L := B) hMK le_rfl
      apply h.trans
      dsimp [K, gaussianSchurStageBits, gaussianSchurRowBitsBudget, B] at hm ⊢
      omega
    have hpivots : ∀ i, rationalMagnitudeBits (rest.value.pivots.get i) ≤ B := by
      intro i
      have hv := congrFun (congrArg Prod.snd (gaussianSchurRun_value M tail.value)) i
      change rest.value.pivots.get i = (gaussianSchurFactor M (rationalMatrixOfData tail.value)).2 i at hv
      rw [hv]
      exact gaussianSchurFactor_pivots_bits_of_inverse_submatrix Q hQ M _ htpos
        (fun i => e i.succ) htinv hMK i
    have htail : tail.steps ≤ gaussianSchurTailCost N K :=
      (gaussianSchurTailRun_steps_le A K (fun i j => (hbits i j).trans hBK)).trans
        (gaussianSchurTailCost_mono hMK le_rfl)
    have hlift : (gaussianSchurLiftRun A rest.value.rows).steps ≤ gaussianSchurLiftCost N K :=
      (gaussianSchurLiftRun_steps_le A rest.value.rows K
        (fun i j => (hbits i j).trans hBK) hrows).trans
        (gaussianSchurLiftCost_mono hMK le_rfl)
    let f := fun i : Fin (M + 1) =>
      let q := Fin.cases (C 0 0) (fun j => rest.value.pivots.get j) i
      Costed.charge (rationalMagnitudeBits q + 1) q
    have hf (i : Fin (M + 1)) : (f i).steps ≤ K + 1 := by
      refine Fin.cases ?_ (fun i => ?_) i
      · exact Nat.add_le_add_right ((hbits 0 0).trans hBK) 1
      · exact Nat.add_le_add_right ((hpivots i).trans hBK) 1
    have hp : (costedVectorOfFn f).steps ≤ (N + 1) * (K + 4) + 1 := by
      apply (costedVectorOfFn_steps_le f (K + 1) hf).trans
      have hm : M + 1 ≤ N + 1 := by omega
      simpa only [Nat.add_assoc] using Nat.add_le_add_right (Nat.mul_le_mul_right (K + 4) hm) 1
    have hlocal : tail.steps + (gaussianSchurLiftRun A rest.value.rows).steps +
        (costedVectorOfFn f).steps + 3 ≤ gaussianSchurStageCost N L := by
      change _ ≤ gaussianSchurTailCost N K + gaussianSchurLiftCost N K + (N + 1) * (K + 4) + 4
      omega
    change tail.steps + rest.steps + (gaussianSchurLiftRun A rest.value.rows).steps +
      (costedVectorOfFn f).steps + 3 ≤ (M + 1) * gaussianSchurStageCost N L + 3
    rw [Nat.add_mul, one_mul]
    omega

def gaussianSchurRunBudget (N L : ℕ) : ℕ :=
  N * gaussianSchurStageCost N (rationalInverseBitsBudget N L) + 3

theorem gaussianSchurRun_steps_le {N L : ℕ} (A : RationalMatrixData N)
    (hA : ((rationalMatrixOfData A).map (fun q : ℚ => (q : ℝ))).PosDef)
    (hbits : ∀ i j, rationalMagnitudeBits (rationalMatrixOfData A i j) ≤ L) :
    (gaussianSchurRun N A).steps ≤ gaussianSchurRunBudget N L :=
  gaussianSchurRun_steps_of_inverse_submatrix (rationalMatrixOfData A)⁻¹
    (rationalMatrix_inverse_bits _ hbits) N A hA id (by simp) le_rfl

theorem gaussianSchurRunBudget_mono {N M L B : ℕ} (hN : N ≤ M) (hL : L ≤ B) :
    gaussianSchurRunBudget N L ≤ gaussianSchurRunBudget M B := by
  unfold gaussianSchurRunBudget gaussianSchurStageCost gaussianSchurStageBits
    gaussianSchurTailCost gaussianSchurLiftCost rationalRectTraversalBudget
    rationalDotBudget rationalDotOperandBudget gaussianSchurRowBitsBudget
    rationalInverseBitsBudget rationalDetBitsBudget
  gcongr

theorem gaussianSchurRunBudget_polynomial :
    PolynomialCostBound (fun t => gaussianSchurRunBudget t t) := by
  let detP (n l : Polynomial ℕ) := n * n + n * l + 2 * (n * (n * n * l)) + 3
  let invP (n l : Polynomial ℕ) := 6 * detP n (l + 3) + 3
  let rowP (n l : Polynomial ℕ) := 6 * invP n l + 3
  let bitsP (n l : Polynomial ℕ) := invP n l + rowP n (invP n l) + 1
  let dotBitsP (n l : Polynomial ℕ) := 4 * n * l + n + 6 * l + 3
  let dotP (n l : Polynomial ℕ) := n * (2 * (2 * dotBitsP n l + 1) ^ 3 + 1) + 1
  let rectP (n l : Polynomial ℕ) := n * (n * (l + 3) + 4) + 1
  let tailP (n l : Polynomial ℕ) := rectP n (3 * (2 * (40 * (l + 1)) + 1) ^ 3 + 4)
  let liftP (n l : Polynomial ℕ) := rectP (n + 1)
    (n + 1 + dotP n l + dotBitsP n l + 1 + (2 * dotBitsP n l + 1) ^ 3 + l + 1)
  let stageP (n l : Polynomial ℕ) := tailP n (bitsP n l) + liftP n (bitsP n l) +
    (n + 1) * (bitsP n l + 4) + 4
  refine ⟨Polynomial.X * stageP Polynomial.X (invP Polynomial.X Polynomial.X) + 3, ?_⟩
  intro t
  apply le_of_eq
  simp [gaussianSchurRunBudget, gaussianSchurStageCost, gaussianSchurStageBits,
    gaussianSchurTailCost, gaussianSchurLiftCost, rationalRectTraversalBudget,
    rationalDotBudget, rationalDotOperandBudget, gaussianSchurRowBitsBudget,
    rationalInverseBitsBudget, rationalDetBitsBudget,
    stageP, tailP, liftP, rectP, dotP, dotBitsP, bitsP, rowP, invP, detP]

/-- The stored exact factorization has a polynomial declared cost in the
dimension and encoded rational input sizes, uniformly over all SPD inputs. -/
theorem gaussianSchurRun_polynomial : ∃ C k : ℕ, ∀ (N : ℕ) (A : RationalMatrixData N),
    ((rationalMatrixOfData A).map (fun q : ℚ => (q : ℝ))).PosDef →
      (gaussianSchurRun N A).steps ≤
        C * (N + rationalMatrixMagnitudeBits (rationalMatrixOfData A) + 1) ^ k := by
  obtain ⟨C, k, h⟩ := gaussianSchurRunBudget_polynomial.exists_mul_pow_bound
  refine ⟨C, k, fun N A hA => ?_⟩
  exact (gaussianSchurRun_steps_le A hA (rationalMatrix_entry_bits_le _)).trans
    ((gaussianSchurRunBudget_mono (Nat.le_add_right _ _)
      (Nat.le_add_left _ _)).trans (h _))

end SISToKSIS


open GeometricGaussianLHL
namespace SISToKSIS
set_option backward.isDefEq.respectTransparency false

theorem integerListDot_size_separate (xs : List (ℤ × ℤ)) (A B : ℕ)
    (hxs : ∀ x ∈ xs, x.1.natAbs.size ≤ A ∧ x.2.natAbs.size ≤ B) :
    (integerListDot xs).natAbs.size ≤ xs.length + A + B + 1 := by
  have habs : (integerListDot xs).natAbs ≤ xs.length * 2 ^ (A + B) := by
    induction xs with
    | nil => simp [integerListDot]
    | cons x xs ih =>
      have hx := hxs x (List.mem_cons_self ..)
      have ht := ih (fun y hy => hxs y (List.mem_cons_of_mem _ hy))
      have hm : (x.1 * x.2).natAbs ≤ 2 ^ (A + B) := by
        rw [Int.natAbs_mul, pow_add]
        exact Nat.mul_le_mul (Nat.size_le.mp hx.1).le (Nat.size_le.mp hx.2).le
      simpa [integerListDot, Nat.add_mul, Nat.add_comm] using
        (Int.natAbs_add_le (x.1 * x.2) (integerListDot xs)).trans (Nat.add_le_add hm ht)
  apply integer_size_le_of_abs_bound
  calc
    _ ≤ xs.length * 2 ^ (A + B) := habs
    _ ≤ 2 ^ xs.length * 2 ^ (A + B) :=
      Nat.mul_le_mul_right _ (Nat.lt_two_pow_self (n := xs.length)).le
    _ = _ := by rw [← pow_add]; congr 1; omega

/-- Proposal radius size depends on the fixed variance, not the adaptive center. -/
theorem gaussianRadiusBits_width_bound (data : ScalarGaussianData) (T : ℕ) :
    gaussianRadiusBits data T ≤ 2 * T.size + data.widthSqNum.size + 3 := by
  have h := dyadicSqrtBits_le (T * T * data.widthSqNum) data.widthSqDen
  have hmul := natural_mul_size_le T T
  have hmul' := natural_mul_size_le (T * T) data.widthSqNum
  unfold gaussianRadiusBits
  omega

/-- The coefficient of the center's bit length is one, permitting iteration. -/
theorem scalarGaussianRun_output_size_affine (data : ScalarGaussianData) (s : ℕ)
    (tape : ScalarGaussianSecurityTape data s) :
    (scalarGaussianRun data s tape).value.natAbs.size ≤
      data.centerNum.natAbs.size + data.centerDen.size + 2 * data.widthSqNum.size +
        data.widthSqDen.size + 2 * (s + 12).size + 9 := by
  rw [scalarGaussianRun_value, boundedScalarGaussianRun_value]
  have h := gaussianProposalPoint_size data (gaussianRadiusBits data (s + 12))
    (dyadicRejectionRun (gaussianProposalWeightRun data (gaussianRadiusBits data (s + 12)) (2 * s + 24))
      (gaussianFallbackIndex (gaussianRadiusBits data (s + 12))) (1024 * (s + 12) * (s + 2)) tape).value
  have hb := gaussianRadiusBits_width_bound data (s + 12)
  dsimp [ScalarGaussianData.bits] at h
  omega

/-- One stored denominator is shared by every adaptive center. -/
structure GaussianPrefixData (N : ℕ) where
  denominator : ℕ
  rows : IntegerMatrixData N
  pivots : Vector ℚ N
  deriving Repr

def GaussianPrefixData.Valid {N : ℕ} (D : GaussianPrefixData N) : Prop :=
  0 < D.denominator ∧ ∀ i, 0 < D.pivots.get i

def GaussianPrefixData.BitsLe {N : ℕ} (D : GaussianPrefixData N) (L : ℕ) : Prop :=
  D.denominator.size ≤ L ∧
    (∀ i j, (integerMatrixOfData D.rows i j).natAbs.size ≤ L) ∧
    ∀ i, rationalMagnitudeBits (D.pivots.get i) ≤ L

/-- Clear the rational elimination rows once; store the fixed pivots once. -/
def gaussianPrefixPrepareRun {N : ℕ} (D : GaussianSchurData N) : Costed (GaussianPrefixData N) :=
  let rows := costedRationalIntegerInput D.rows
  let pivots := costedVectorOfFn fun i =>
    Costed.charge (rationalMagnitudeBits (D.pivots.get i) + 1) (D.pivots.get i)
  ⟨⟨rows.value.1, rows.value.2, pivots.value⟩, rows.steps + pivots.steps + 3⟩

theorem gaussianPrefixPrepareRun_value {N : ℕ} (D : GaussianSchurData N) :
    (gaussianPrefixPrepareRun D).value =
      ⟨rationalMatrixCommonDenominator (rationalMatrixOfData D.rows),
        integerMatrixData (rationalMatrixCommonNumerators (rationalMatrixOfData D.rows)),
        D.pivots⟩ := by
  simp only [gaussianPrefixPrepareRun, costedRationalIntegerInput_value,
    costedVectorOfFn_value, Costed.charge]
  congr 1
  apply Vector.ext
  intro i hi
  simp [Vector.get]

theorem gaussianPrefixPrepareRun_valid {N : ℕ} (D : GaussianSchurData N)
    (hv : ∀ i, 0 < D.pivots.get i) : (gaussianPrefixPrepareRun D).value.Valid := by
  rw [gaussianPrefixPrepareRun_value]
  exact ⟨rationalMatrixCommonDenominator_pos _, hv⟩

theorem gaussianPrefixPrepareRun_bits {N : ℕ} (D : GaussianSchurData N) (L : ℕ)
    (hv : ∀ i, rationalMagnitudeBits (D.pivots.get i) ≤ L) :
    (gaussianPrefixPrepareRun D).value.BitsLe
      (2 * rationalMatrixMagnitudeBits (rationalMatrixOfData D.rows) + L + 1) := by
  rw [gaussianPrefixPrepareRun_value]
  refine ⟨(rationalMatrixCommonDenominator_size _).trans (by omega), ?_, ?_⟩
  · intro i j
    rw [integerMatrixOfData_data]
    exact (rationalMatrixCommonNumerators_size _ i j).trans (by omega)
  · intro i
    exact (hv i).trans (by omega)

theorem gaussianPrefixPrepareRun_steps_le {N : ℕ} (D : GaussianSchurData N) (L : ℕ)
    (hv : ∀ i, rationalMagnitudeBits (D.pivots.get i) ≤ L) :
    (gaussianPrefixPrepareRun D).steps ≤
      rationalIntegerInputBudget N (rationalMatrixMagnitudeBits (rationalMatrixOfData D.rows)) +
        N * (L + 4) + 4 := by
  have hp := costedVectorOfFn_steps_le
    (fun i => Costed.charge (rationalMagnitudeBits (D.pivots.get i) + 1) (D.pivots.get i))
    (L + 1) (fun i => Nat.add_le_add_right (hv i) 1)
  have hr := costedRationalIntegerInput_steps_le D.rows
  dsimp only [gaussianPrefixPrepareRun]
  norm_num only [Nat.add_assoc] at hp
  omega

def gaussianPrefixScalarData {N : ℕ} (D : GaussianPrefixData N) (i : Fin N)
    (z : Coeff i.val) : ScalarGaussianData :=
  ⟨-(∑ j : Fin i.val, integerMatrixOfData D.rows i ⟨j.val, lt_trans j.isLt i.isLt⟩ * z j),
    D.denominator, (D.pivots.get i).num.natAbs, (D.pivots.get i).den⟩

/-- Compute the center with one integer dot product and the shared denominator. -/
def gaussianPrefixScalarDataRun {N : ℕ} (D : GaussianPrefixData N) (i : Fin N)
    (z : Vector ℤ i.val) : Costed ScalarGaussianData :=
  let pairs := costedVectorOfFn fun j : Fin i.val =>
    let a := integerMatrixOfData D.rows i ⟨j.val, lt_trans j.isLt i.isLt⟩
    Costed.charge (a.natAbs.size + (z.get j).natAbs.size + 3) (a, z.get j)
  let dot := costedIntegerDot pairs.value.toList
  let center := costedIntSub 0 dot.value
  let v := D.pivots.get i
  ⟨⟨center.value, D.denominator, v.num.natAbs, v.den⟩,
    pairs.steps + i.val + 1 + dot.steps + center.steps +
      D.denominator.size + rationalMagnitudeBits v + 4⟩

@[simp] theorem gaussianPrefixScalarDataRun_value {N : ℕ} (D : GaussianPrefixData N)
    (i : Fin N) (z : Vector ℤ i.val) :
    (gaussianPrefixScalarDataRun D i z).value = gaussianPrefixScalarData D i z.get := by
  simp [gaussianPrefixScalarDataRun, gaussianPrefixScalarData, costedVectorOfFn_value,
    Costed.charge, costedIntSub, integerListDot, Vector.toList_ofFn, List.sum_ofFn]

theorem gaussianPrefixScalarData_valid {N : ℕ} (D : GaussianPrefixData N)
    (hD : D.Valid) (i : Fin N) (z : Coeff i.val) : (gaussianPrefixScalarData D i z).Valid := by
  exact ⟨hD.1, Int.natAbs_pos.mpr (Rat.num_pos.mpr (hD.2 i)).ne', (D.pivots.get i).den_pos⟩

theorem gaussianPrefixScalarData_widthSq {N : ℕ} (D : GaussianPrefixData N)
    (hD : D.Valid) (i : Fin N) (z : Coeff i.val) :
    (gaussianPrefixScalarData D i z).widthSq = (D.pivots.get i : ℝ) :=
  ScalarGaussianData.ofRationals_widthSq 0 _ (hD.2 i)

theorem gaussianPrefixScalarData_center {N : ℕ} (D : GaussianSchurData N)
    (i : Fin N) (z : Coeff i.val) :
    (gaussianPrefixScalarData (gaussianPrefixPrepareRun D).value i z).center =
      gaussianSchurCenters ((rationalMatrixOfData D.rows).map (fun q : ℚ => (q : ℝ))) i z := by
  rw [gaussianPrefixPrepareRun_value]
  simp only [gaussianPrefixScalarData, ScalarGaussianData.center,
    integerMatrixOfData_data, gaussianSchurCenters, Matrix.map_apply,
    Int.cast_neg, Int.cast_sum, Int.cast_mul, neg_div, Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  have h := congrFun (congrFun (rationalMatrix_common_reconstruct
    (rationalMatrixOfData D.rows)) i) ⟨j.val, lt_trans j.isLt i.isLt⟩
  rw [integerMatrixQuotient_apply] at h
  have hreal := congrArg (fun q : ℚ => (q : ℝ)) h
  simp only [Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast] at hreal
  rw [← hreal]
  ring

theorem gaussianPrefixScalarData_center_bits {N L P : ℕ} (D : GaussianPrefixData N)
    (hD : D.BitsLe L) (i : Fin N) (z : Coeff i.val)
    (hz : ∀ j, (z j).natAbs.size ≤ P) :
    (gaussianPrefixScalarData D i z).centerNum.natAbs.size ≤ i.val + L + P + 1 := by
  have h := integerListDot_size_separate
    (List.ofFn fun j : Fin i.val =>
      (integerMatrixOfData D.rows i ⟨j.val, lt_trans j.isLt i.isLt⟩, z j)) L P
    (by
      intro x hx
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
      exact ⟨hD.2.1 _ _, hz j⟩)
  simpa [gaussianPrefixScalarData, integerListDot, List.sum_ofFn] using h

theorem gaussianPrefixScalarData_bits {N L P : ℕ} (D : GaussianPrefixData N)
    (hD : D.BitsLe L) (i : Fin N) (z : Coeff i.val)
    (hz : ∀ j, (z j).natAbs.size ≤ P) :
    (gaussianPrefixScalarData D i z).bits ≤ i.val + 3 * L + P + 2 := by
  have hc := gaussianPrefixScalarData_center_bits D hD i z hz
  have hv := hD.2.2 i
  have hd := hD.1
  dsimp [ScalarGaussianData.bits, gaussianPrefixScalarData, rationalMagnitudeBits] at *
  omega

theorem gaussianPrefixScalar_output_bits {N L P : ℕ} (D : GaussianPrefixData N)
    (hD : D.BitsLe L) (i : Fin N) (z : Coeff i.val)
    (hz : ∀ j, (z j).natAbs.size ≤ P) (s : ℕ)
    (tape : ScalarGaussianSecurityTape (gaussianPrefixScalarData D i z) s) :
    (scalarGaussianRun (gaussianPrefixScalarData D i z) s tape).value.natAbs.size ≤
      P + N + 4 * L + 2 * (s + 12).size + 10 := by
  have h := scalarGaussianRun_output_size_affine (gaussianPrefixScalarData D i z) s tape
  have hc := gaussianPrefixScalarData_center_bits D hD i z hz
  have hv := hD.2.2 i
  have hd := hD.1
  dsimp [gaussianPrefixScalarData, rationalMagnitudeBits] at *
  omega


/-- Reads, dot products, negation, and construction of the scalar input. -/
def gaussianPrefixCenterBudget (N L P : ℕ) : ℕ :=
  (N * (L + P + 6) + 1) + N + 1 +
    (N * integerDotStepBudget N (L + P) + 1) +
    (N + L + P + 2) + 2 * L + 4

theorem gaussianPrefixScalarDataRun_steps_le {N L P : ℕ} (D : GaussianPrefixData N)
    (hD : D.BitsLe L) (i : Fin N) (z : Vector ℤ i.val)
    (hz : ∀ j, (z.get j).natAbs.size ≤ P) :
    (gaussianPrefixScalarDataRun D i z).steps ≤ gaussianPrefixCenterBudget N L P := by
  let f := fun j : Fin i.val =>
    let a := integerMatrixOfData D.rows i ⟨j.val, lt_trans j.isLt i.isLt⟩
    Costed.charge (a.natAbs.size + (z.get j).natAbs.size + 3) (a, z.get j)
  let pairs := costedVectorOfFn f
  have hpairs : pairs.steps ≤ N * (L + P + 6) + 1 := by
    have hf : ∀ j, (f j).steps ≤ L + P + 3 := by
      intro j
      have ha := hD.2.1 i ⟨j.val, lt_trans j.isLt i.isLt⟩
      have hzj := hz j
      dsimp [f, Costed.charge]
      omega
    apply (costedVectorOfFn_steps_le f (L + P + 3) hf).trans
    simpa only [Nat.add_assoc] using Nat.add_le_add_right
      (Nat.mul_le_mul_right (L + P + 6) i.isLt.le) 1
  have hpairsValue : pairs.value.toList = List.ofFn (fun j => (f j).value) := by
    simp [pairs, costedVectorOfFn_value, Vector.toList_ofFn]
  have hentries : ∀ x ∈ pairs.value.toList,
      x.1.natAbs.size ≤ L ∧ x.2.natAbs.size ≤ P := by
    rw [hpairsValue]
    intro x hx
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
    exact ⟨hD.2.1 _ _, hz j⟩
  have hdot := costedIntegerDot_steps_le pairs.value.toList (L + P) (by
    intro x hx
    have h := hentries x hx
    exact ⟨h.1.trans (by omega), h.2.trans (by omega)⟩)
  have hdot' : (costedIntegerDot pairs.value.toList).steps ≤
      N * integerDotStepBudget N (L + P) + 1 := by
    apply hdot.trans
    simp only [Vector.length_toList]
    unfold integerDotStepBudget
    gcongr <;> exact i.isLt.le
  have hdotbits := integerListDot_size_separate pairs.value.toList L P hentries
  simp only [Vector.length_toList] at hdotbits
  have hneg : (costedIntSub 0 (costedIntegerDot pairs.value.toList).value).steps ≤
      N + L + P + 2 := by
    simp only [costedIntSub, integerOperandBits, costedIntegerDot_value,
      Int.natAbs_zero, Nat.size_zero, zero_add]
    omega
  have hd := hD.1
  have hv := hD.2.2 i
  change pairs.steps + i.val + 1 + (costedIntegerDot pairs.value.toList).steps +
    (costedIntSub 0 (costedIntegerDot pairs.value.toList).value).steps +
      D.denominator.size + rationalMagnitudeBits (D.pivots.get i) + 4 ≤ _
  unfold gaussianPrefixCenterBudget
  omega

theorem gaussianPrefixCenterBudget_mono {N M L B P Q : ℕ}
    (hN : N ≤ M) (hL : L ≤ B) (hP : P ≤ Q) :
    gaussianPrefixCenterBudget N L P ≤ gaussianPrefixCenterBudget M B Q := by
  unfold gaussianPrefixCenterBudget integerDotStepBudget
  gcongr

/-- Tape lengths depend only on the fixed variance and the precision. -/
abbrev GaussianPrefixTape {N : ℕ} (D : GaussianPrefixData N) (i : Fin N) (s : ℕ) :=
  ScalarGaussianSecurityTape (gaussianPrefixScalarData D i (fun _ => 0)) s

/-- Store a prefix-dependent center, then run the already verified scalar sampler. -/
def gaussianPrefixStepRun {N : ℕ} (D : GaussianPrefixData N) (i : Fin N)
    (z : Vector ℤ i.val) (s : ℕ) (tape : GaussianPrefixTape D i s) : Costed ℤ :=
  let data := gaussianPrefixScalarDataRun D i z
  let sample := scalarGaussianRun data.value s tape
  ⟨sample.value, data.steps + sample.steps + 1⟩

theorem gaussianPrefixScalarDataRun_sample {N : ℕ} (D : GaussianPrefixData N) (i : Fin N)
    (z : Vector ℤ i.val) (s : ℕ) (tape : GaussianPrefixTape D i s) :
    scalarGaussianRun (gaussianPrefixScalarDataRun D i z).value s tape =
      scalarGaussianRun (gaussianPrefixScalarData D i z.get) s tape := by
  change scalarGaussianRun
    ⟨(gaussianPrefixScalarDataRun D i z).value.centerNum,
      D.denominator, (D.pivots.get i).num.natAbs, (D.pivots.get i).den⟩ s tape = _
  rw [congrArg ScalarGaussianData.centerNum (gaussianPrefixScalarDataRun_value D i z)]
  rfl

theorem gaussianPrefixStepRun_value {N : ℕ} (D : GaussianPrefixData N) (i : Fin N)
    (z : Vector ℤ i.val) (s : ℕ) (tape : GaussianPrefixTape D i s) :
    (gaussianPrefixStepRun D i z s tape).value =
      (scalarGaussianRun (gaussianPrefixScalarData D i z.get) s tape).value := by
  simp only [gaussianPrefixStepRun, gaussianPrefixScalarDataRun_sample]

theorem gaussianPrefixStepRun_output_bits {N L P : ℕ} (D : GaussianPrefixData N)
    (hD : D.BitsLe L) (i : Fin N) (z : Vector ℤ i.val)
    (hz : ∀ j, (z.get j).natAbs.size ≤ P) (s : ℕ) (tape : GaussianPrefixTape D i s) :
    (gaussianPrefixStepRun D i z s tape).value.natAbs.size ≤
      P + N + 4 * L + 2 * (s + 12).size + 10 := by
  rw [gaussianPrefixStepRun_value]
  exact gaussianPrefixScalar_output_bits D hD i z.get hz s tape

def gaussianPrefixStepBudget (N L P s : ℕ) : ℕ :=
  gaussianPrefixCenterBudget N L P +
    20000000000000000000000000000000 * (N + 3 * L + P + s + 3) ^ 6 + 1

theorem gaussianPrefixStepRun_steps_le {N L P : ℕ} (D : GaussianPrefixData N)
    (hvalid : D.Valid) (hD : D.BitsLe L) (i : Fin N) (z : Vector ℤ i.val)
    (hz : ∀ j, (z.get j).natAbs.size ≤ P) (s : ℕ) (tape : GaussianPrefixTape D i s) :
    (gaussianPrefixStepRun D i z s tape).steps ≤ gaussianPrefixStepBudget N L P s := by
  have hc := gaussianPrefixScalarDataRun_steps_le D hD i z hz
  have hbits := gaussianPrefixScalarData_bits D hD i z.get hz
  have hs := scalarGaussianRun_polynomial_bound (gaussianPrefixScalarData D i z.get)
    (gaussianPrefixScalarData_valid D hvalid i z.get) s tape
  have hs' : (scalarGaussianRun (gaussianPrefixScalarData D i z.get) s tape).steps ≤
      20000000000000000000000000000000 * (N + 3 * L + P + s + 3) ^ 6 := by
    apply hs.trans
    apply Nat.mul_le_mul_left
    apply Nat.pow_le_pow_left
    omega
  simp only [gaussianPrefixStepRun, gaussianPrefixScalarDataRun_sample]
  unfold gaussianPrefixStepBudget
  omega

theorem gaussianPrefixStepBudget_mono {N M L B P Q s t : ℕ}
    (hN : N ≤ M) (hL : L ≤ B) (hP : P ≤ Q) (hs : s ≤ t) :
    gaussianPrefixStepBudget N L P s ≤ gaussianPrefixStepBudget M B Q t := by
  unfold gaussianPrefixStepBudget gaussianPrefixCenterBudget integerDotStepBudget
  gcongr

theorem gaussianPrefixStepBudget_polynomial :
    PolynomialCostBound (fun t => gaussianPrefixStepBudget t t t t) := by
  let x : Polynomial ℕ := Polynomial.X
  let center := (x * (x + x + 6) + 1) + x + 1 +
    (x * ((2 * (x + x) + 1) ^ 2 + x + 4 * (x + x) + 4) + 1) +
    (x + x + x + 2) + 2 * x + 4
  refine ⟨center + 20000000000000000000000000000000 * (x + 3 * x + x + x + 3) ^ 6 + 1, ?_⟩
  intro t
  apply le_of_eq
  simp [gaussianPrefixStepBudget, gaussianPrefixCenterBudget, integerDotStepBudget, center, x]

noncomputable section

def gaussianPrefixTapeLaw {N : ℕ} (D : GaussianPrefixData N) (i : Fin N) (s : ℕ) :
    PMF (GaussianPrefixTape D i s) :=
  scalarGaussianSecurityTapeLaw (gaussianPrefixScalarData D i (fun _ => 0)) s

/-- The same finite random-word law works for every previously sampled prefix. -/
theorem gaussianPrefixStepRun_law {N : ℕ} (D : GaussianPrefixData N) (i : Fin N)
    (z : Vector ℤ i.val) (s : ℕ) :
    (gaussianPrefixTapeLaw D i s).map (fun tape => (gaussianPrefixStepRun D i z s tape).value) =
      scalarGaussianRunLaw (gaussianPrefixScalarData D i z.get) s := by
  simp only [gaussianPrefixStepRun_value]
  exact scalarGaussianRun_law (gaussianPrefixScalarData D i z.get) s

end

end SISToKSIS


open GeometricGaussianLHL
namespace SISToKSIS
set_option backward.isDefEq.respectTransparency false

/-- Copy a sampled head and the stored tail into a charged integer vector. -/
def integerVectorConsRun {N : ℕ} (a : ℤ) (z : Vector ℤ N) : Costed (Vector ℤ (N + 1)) :=
  costedVectorOfFn fun i : Fin (N + 1) =>
    let v : ℤ := Fin.cons (α := fun _ => ℤ) a z.get i
    Costed.charge (v.natAbs.size + 1) v

@[simp] theorem integerVectorConsRun_value {N : ℕ} (a : ℤ) (z : Vector ℤ N) :
    (integerVectorConsRun a z).value = Vector.ofFn (Fin.cons a z.get) := by
  simp only [integerVectorConsRun, costedVectorOfFn_value, Costed.charge]

@[simp] theorem integerVectorConsRun_get {N : ℕ} (a : ℤ) (z : Vector ℤ N) :
    (integerVectorConsRun a z).value.get = Fin.cons a z.get := by
  rw [integerVectorConsRun_value]
  funext i
  simp [Vector.get]

theorem integerVectorConsRun_steps_le {N B : ℕ} (a : ℤ) (z : Vector ℤ N)
    (ha : a.natAbs.size ≤ B) (hz : ∀ i, (z.get i).natAbs.size ≤ B) :
    (integerVectorConsRun a z).steps ≤ (N + 1) * (B + 4) + 1 := by
  have hf : ∀ i : Fin (N + 1),
      (Costed.charge ((Fin.cons (α := fun _ => ℤ) a z.get i).natAbs.size + 1)
        (Fin.cons (α := fun _ => ℤ) a z.get i)).steps ≤ B + 1 := by
    intro i
    change (Fin.cons (α := fun _ => ℤ) a z.get i).natAbs.size + 1 ≤ B + 1
    apply Nat.add_le_add_right
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using ha
    · simpa using hz j
  have h := costedVectorOfFn_steps_le _ (B + 1) hf
  norm_num only [Nat.add_assoc] at h
  exact h

/-- Mathematical evaluation of adaptive coordinate kernels. -/
def prefixEval {α : Type*} : (N : ℕ) →
    (∀ i : Fin N, (Fin i.val → α) → α) → (Fin N → α)
  | 0, _ => Fin.elim0
  | N + 1, kernel =>
    let a := kernel 0 Fin.elim0
    Fin.cons a (prefixEval N (fun i z => kernel i.succ (Fin.cons a z)))

/-- The implementation stores each draw and charges every prefix/output copy. -/
def prefixVectorRun : (N : ℕ) →
    (∀ i : Fin N, Vector ℤ i.val → Costed ℤ) → Costed (Vector ℤ N)
  | 0, _ => ⟨Vector.ofFn Fin.elim0, 1⟩
  | N + 1, kernel =>
    let first := kernel 0 (Vector.ofFn Fin.elim0)
    let tail := prefixVectorRun N fun i z =>
      let pref := integerVectorConsRun first.value z
      let draw := kernel i.succ pref.value
      ⟨draw.value, pref.steps + draw.steps⟩
    let output := integerVectorConsRun first.value tail.value
    ⟨output.value, first.steps + tail.steps + output.steps + N + 1⟩

theorem prefixVectorRun_value (N : ℕ)
    (kernel : ∀ i : Fin N, Vector ℤ i.val → Costed ℤ) :
    (prefixVectorRun N kernel).value.get =
      prefixEval N (fun i z => (kernel i (Vector.ofFn z)).value) := by
  induction N with
  | zero => funext i; exact Fin.elim0 i
  | succ N ih =>
    rw [prefixVectorRun, integerVectorConsRun_get, ih, prefixEval]
    congr 1
    congr 1
    funext i z
    simp only [integerVectorConsRun_value]
    have hzget : (Vector.ofFn z).get = z := by
      funext j
      simp [Vector.get]
    rw [hzget]

noncomputable section

/-- Independent finite-coordinate seed laws, allowing different seed types. -/
def dependentSeedLaw : (N : ℕ) → (γ : Fin N → Type*) →
    (∀ i, PMF (γ i)) → PMF (∀ i, γ i)
  | 0, _, _ => PMF.pure (fun i => Fin.elim0 i)
  | N + 1, γ, p =>
    (jointPMF (p 0) (fun _ => dependentSeedLaw N (fun i => γ i.succ)
      (fun i => p i.succ))).map (Fin.consEquiv γ)

theorem dependentSeedLaw_apply (N : ℕ) (γ : Fin N → Type*) (p : ∀ i, PMF (γ i))
    (z : ∀ i, γ i) : dependentSeedLaw N γ p z = ∏ i, p i (z i) := by
  induction N with
  | zero =>
    simp [dependentSeedLaw]
    funext i
    exact Fin.elim0 i
  | succ N ih =>
    obtain ⟨⟨a, z⟩, rfl⟩ := (Fin.consEquiv γ).surjective z
    rw [dependentSeedLaw, pmf_map_equiv_apply, jointPMF_apply, ih]
    simp only [Fin.prod_univ_succ, Fin.consEquiv, Equiv.coe_fn_mk, Fin.cons_zero, Fin.cons_succ]

/-- Independent coordinate seeds implement the adaptive joint distribution. -/
theorem prefixEval_law {α : Type*} (N : ℕ) (γ : Fin N → Type*)
    (p : ∀ i, PMF (γ i)) (kernel : ∀ i : Fin N, (Fin i.val → α) → γ i → α) :
    (dependentSeedLaw N γ p).map (fun seeds =>
      prefixEval N (fun i z => kernel i z (seeds i))) =
        prefixPMF N (fun i z => (p i).map (kernel i z)) := by
  induction N with
  | zero => simp only [dependentSeedLaw, prefixEval, prefixPMF, PMF.pure_map]
  | succ N ih =>
    let f := kernel 0 Fin.elim0
    let tail := dependentSeedLaw N (fun i => γ i.succ) (fun i => p i.succ)
    let evalTail := fun (a : α) (seeds : ∀ i : Fin N, γ i.succ) => prefixEval N
      (fun i z => kernel i.succ (Fin.cons a z) (seeds i))
    let lawTail := fun a => prefixPMF N
      (fun i z => (p i.succ).map (kernel i.succ (Fin.cons a z)))
    have ht (a : α) : tail.map (evalTail a) = lawTail a :=
      ih _ _ (fun i z => kernel i.succ (Fin.cons a z))
    rw [dependentSeedLaw, PMF.map_comp, prefixPMF]
    change (jointPMF (p 0) (fun _ => tail)).map
        (fun z => Fin.cons (f z.1) (evalTail (f z.1) z.2)) =
      (jointPMF ((p 0).map f) lawTail).map (Fin.consEquiv (fun _ => α))
    rw [jointPMF_map_input, PMF.map_comp]
    have htail : jointPMF (p 0) (fun a => lawTail (f a)) =
        (jointPMF (p 0) (fun _ => tail)).map
          (fun z => (z.1, evalTail (f z.1) z.2)) := by
      simp_rw [← ht]
      exact jointPMF_map_second _ _ _
    rw [htail, PMF.map_comp]
    rfl

end

def prefixCopyBudget (D K : ℕ) : ℕ := (D + 1) * (D * K + 4) + D + 2

/-- The coordinate offset tracks additive size growth through stored recursion. -/
theorem prefixVectorRun_bounds (N : ℕ)
    (kernel : ∀ i : Fin N, Vector ℤ i.val → Costed ℤ) (D O K C : ℕ)
    (hdim : O + N ≤ D)
    (hkernel : ∀ i z, (∀ j, (z.get j).natAbs.size ≤ (O + i.val) * K) →
      (kernel i z).value.natAbs.size ≤ (O + i.val + 1) * K ∧ (kernel i z).steps ≤ C) :
    (∀ i, ((prefixVectorRun N kernel).value.get i).natAbs.size ≤ (O + i.val + 1) * K) ∧
      (prefixVectorRun N kernel).steps ≤ N * (C + (N + 1) * prefixCopyBudget D K) + 1 := by
  induction N generalizing O C with
  | zero =>
    constructor
    · intro i; exact Fin.elim0 i
    · simp [prefixVectorRun]
  | succ N ih =>
    let P := prefixCopyBudget D K
    let first := kernel 0 (Vector.ofFn Fin.elim0)
    let tailKernel := fun (i : Fin N) (z : Vector ℤ i.val) =>
      let pref := integerVectorConsRun first.value z
      let draw := kernel i.succ pref.value
      (⟨draw.value, pref.steps + draw.steps⟩ : Costed ℤ)
    let tail := prefixVectorRun N tailKernel
    let output := integerVectorConsRun first.value tail.value
    have hfirst := hkernel 0 (Vector.ofFn Fin.elim0) (fun j => Fin.elim0 j)
    change first.value.natAbs.size ≤ (O + 0 + 1) * K ∧ first.steps ≤ C at hfirst
    simp only [Nat.add_zero] at hfirst
    have hfirstD : first.value.natAbs.size ≤ D * K :=
      hfirst.1.trans (Nat.mul_le_mul_right K (by omega))
    have hcopy {M : ℕ} (hM : M ≤ D) (a : ℤ) (z : Vector ℤ M)
        (ha : a.natAbs.size ≤ D * K) (hz : ∀ j, (z.get j).natAbs.size ≤ D * K) :
        (integerVectorConsRun a z).steps ≤ P := by
      apply (integerVectorConsRun_steps_le a z ha hz).trans
      have hm := Nat.mul_le_mul_right (D * K + 4) (Nat.add_le_add_right hM 1)
      dsimp [P, prefixCopyBudget]
      omega
    have htailKernel : ∀ (i : Fin N) (z : Vector ℤ i.val),
        (∀ j, (z.get j).natAbs.size ≤ (O + 1 + i.val) * K) →
        (tailKernel i z).value.natAbs.size ≤ (O + 1 + i.val + 1) * K ∧
          (tailKernel i z).steps ≤ C + P := by
      intro i z hz
      let pref := integerVectorConsRun first.value z
      have hpref : ∀ j, (pref.value.get j).natAbs.size ≤ (O + i.succ.val) * K := by
        rw [integerVectorConsRun_get]
        intro j
        refine Fin.cases ?_ (fun j => ?_) j
        · simp only [Fin.cons_zero, Fin.val_succ]
          exact hfirst.1.trans (Nat.mul_le_mul_right K (by omega))
        · simpa only [Fin.cons_succ, Fin.val_succ, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using hz j
      have hdraw := hkernel i.succ pref.value hpref
      have hcopy' : pref.steps ≤ P := by
        apply hcopy (by omega) first.value z hfirstD
        intro j
        exact (hz j).trans (Nat.mul_le_mul_right K (by omega))
      constructor
      · simpa only [tailKernel, Fin.val_succ, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using hdraw.1
      · change pref.steps + (kernel i.succ pref.value).steps ≤ C + P
        omega
    have htail := ih tailKernel (O + 1) (C + P) (by omega) htailKernel
    change (∀ i, (tail.value.get i).natAbs.size ≤ (O + 1 + i.val + 1) * K) ∧
      tail.steps ≤ N * (C + P + (N + 1) * P) + 1 at htail
    have houtput : output.steps ≤ P := by
      apply hcopy (by omega) first.value tail.value hfirstD
      intro j
      exact (htail.1 j).trans (Nat.mul_le_mul_right K (by omega))
    have hcontrol : N + 1 ≤ P := by
      dsimp [P, prefixCopyBudget]
      omega
    constructor
    · change ∀ i, (output.value.get i).natAbs.size ≤ (O + i.val + 1) * K
      rw [integerVectorConsRun_get]
      intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · simpa using hfirst.1
      · simpa only [Fin.cons_succ, Fin.val_succ, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using htail.1 i
    · change first.steps + tail.steps + output.steps + N + 1 ≤
        (N + 1) * (C + (N + 1 + 1) * P) + 1
      have hn : 0 ≤ N * P := Nat.zero_le _
      nlinarith [hfirst.2, htail.2]

/-- Empty-prefix runs have a uniform linear bound on the output bit lengths. -/
theorem prefixVectorRun_bits (N K : ℕ)
    (kernel : ∀ i : Fin N, Vector ℤ i.val → Costed ℤ)
    (hkernel : ∀ i z, (∀ j, (z.get j).natAbs.size ≤ i.val * K) →
      (kernel i z).value.natAbs.size ≤ (i.val + 1) * K)
    (C : ℕ) (hcost : ∀ i z, (∀ j, (z.get j).natAbs.size ≤ i.val * K) →
      (kernel i z).steps ≤ C) (i : Fin N) :
    ((prefixVectorRun N kernel).value.get i).natAbs.size ≤ N * K := by
  have h := prefixVectorRun_bounds N kernel N 0 K C (by omega)
    (by simpa using fun i z hz => And.intro (hkernel i z hz) (hcost i z hz))
  exact (h.1 i).trans (Nat.mul_le_mul_right K (by omega))

abbrev GaussianAdaptiveTape {N : ℕ} (D : GaussianPrefixData N) (s : ℕ) :=
  ∀ i : Fin N, GaussianPrefixTape D i (s + N)

/-- Sample all coordinates adaptively and store their integer coefficients. -/
def gaussianAdaptiveRun {N : ℕ} (D : GaussianPrefixData N) (s : ℕ)
    (tape : GaussianAdaptiveTape D s) : Costed (Vector ℤ N) :=
  let precision := costedNatAdd s N
  let samples := prefixVectorRun N fun i z => gaussianPrefixStepRun D i z precision.value (tape i)
  ⟨samples.value, precision.steps + samples.steps + 1⟩

theorem gaussianAdaptiveRun_value {N : ℕ} (D : GaussianPrefixData N) (s : ℕ)
    (tape : GaussianAdaptiveTape D s) :
    (gaussianAdaptiveRun D s tape).value.get = prefixEval N (fun i z =>
      (gaussianPrefixStepRun D i (Vector.ofFn z) (s + N) (tape i)).value) := by
  change (prefixVectorRun N (fun i z => gaussianPrefixStepRun D i z (s + N) (tape i))).value.get = _
  exact prefixVectorRun_value _ _

def gaussianAdaptiveGrowth (N L s : ℕ) : ℕ := N + 4 * L + 2 * (s + N + 12) + 10

def gaussianAdaptiveBudget (N L s : ℕ) : ℕ :=
  (s + N + 1) + N * (gaussianPrefixStepBudget N L (N * gaussianAdaptiveGrowth N L s) (s + N) +
    (N + 1) * prefixCopyBudget N (gaussianAdaptiveGrowth N L s)) + 2

/-- Polynomial bounds for every tape, including all adaptive prefix copies. -/
theorem gaussianAdaptiveRun_bounds {N L : ℕ} (D : GaussianPrefixData N)
    (hvalid : D.Valid) (hD : D.BitsLe L) (s : ℕ) (tape : GaussianAdaptiveTape D s) :
    (∀ i, ((gaussianAdaptiveRun D s tape).value.get i).natAbs.size ≤
      N * gaussianAdaptiveGrowth N L s) ∧
    (gaussianAdaptiveRun D s tape).steps ≤ gaussianAdaptiveBudget N L s := by
  let K := gaussianAdaptiveGrowth N L s
  let C := gaussianPrefixStepBudget N L (N * K) (s + N)
  let kernel := fun (i : Fin N) (z : Vector ℤ i.val) =>
    gaussianPrefixStepRun D i z (s + N) (tape i)
  have hkernel : ∀ i z, (∀ j, (z.get j).natAbs.size ≤ (0 + i.val) * K) →
      (kernel i z).value.natAbs.size ≤ (0 + i.val + 1) * K ∧ (kernel i z).steps ≤ C := by
    intro i z hz
    simp only [zero_add] at hz ⊢
    have hbits := gaussianPrefixStepRun_output_bits D hD i z hz (s + N) (tape i)
    have hg : N + 4 * L + 2 * (s + N + 12).size + 10 ≤ K := by
      have hsize : (s + N + 12).size ≤ s + N + 12 := Nat.size_le.mpr Nat.lt_two_pow_self
      dsimp [K, gaussianAdaptiveGrowth]
      omega
    refine ⟨hbits.trans ?_, ?_⟩
    · nlinarith
    · apply gaussianPrefixStepRun_steps_le D hvalid hD i z _ (s + N) (tape i)
      intro j
      exact (hz j).trans (Nat.mul_le_mul_right K i.isLt.le)
  have h := prefixVectorRun_bounds N kernel N 0 K C (by omega) hkernel
  constructor
  · intro i
    change ((prefixVectorRun N kernel).value.get i).natAbs.size ≤ N * K
    exact (h.1 i).trans (Nat.mul_le_mul_right K (by omega))
  · have hs : s.size ≤ s := Nat.size_le.mpr Nat.lt_two_pow_self
    have hN : N.size ≤ N := Nat.size_le.mpr Nat.lt_two_pow_self
    change (s.size + N.size + 1) + (prefixVectorRun N kernel).steps + 1 ≤ _
    change _ ≤ (s + N + 1) + N * (C + (N + 1) * prefixCopyBudget N K) + 2
    omega

theorem gaussianAdaptiveBudget_mono {N M L B s t : ℕ}
    (hN : N ≤ M) (hL : L ≤ B) (hs : s ≤ t) :
    gaussianAdaptiveBudget N L s ≤ gaussianAdaptiveBudget M B t := by
  unfold gaussianAdaptiveBudget gaussianAdaptiveGrowth gaussianPrefixStepBudget
    gaussianPrefixCenterBudget integerDotStepBudget prefixCopyBudget
  gcongr

theorem gaussianAdaptiveBudget_polynomial :
    PolynomialCostBound (fun t => gaussianAdaptiveBudget t t t) := by
  let x : Polynomial ℕ := Polynomial.X
  let growth := x + 4 * x + 2 * (x + x + 12) + 10
  let prev := x * growth
  let center := (x * (x + prev + 6) + 1) + x + 1 +
    (x * ((2 * (x + prev) + 1) ^ 2 + x + 4 * (x + prev) + 4) + 1) +
    (x + x + prev + 2) + 2 * x + 4
  let step := center + 20000000000000000000000000000000 *
    (x + 3 * x + prev + (x + x) + 3) ^ 6 + 1
  let copy := (x + 1) * (x * growth + 4) + x + 2
  refine ⟨(x + x + 1) + x * (step + (x + 1) * copy) + 2, ?_⟩
  intro t
  apply le_of_eq
  simp [gaussianAdaptiveBudget, gaussianAdaptiveGrowth, gaussianPrefixStepBudget,
    gaussianPrefixCenterBudget, integerDotStepBudget, prefixCopyBudget,
    x, growth, prev, center, step, copy]

theorem gaussianAdaptiveRun_polynomial : ∃ C k : ℕ, ∀ (N L : ℕ)
    (D : GaussianPrefixData N), D.Valid → D.BitsLe L → ∀ (s : ℕ) (tape : GaussianAdaptiveTape D s),
      (gaussianAdaptiveRun D s tape).steps ≤ C * (N + L + s + 1) ^ k := by
  obtain ⟨C, k, h⟩ := gaussianAdaptiveBudget_polynomial.exists_mul_pow_bound
  refine ⟨C, k, fun N L D hvalid hD s tape => ?_⟩
  exact (gaussianAdaptiveRun_bounds D hvalid hD s tape).2.trans
    ((gaussianAdaptiveBudget_mono (by omega) (by omega) (by omega)).trans (h (N + L + s)))

noncomputable section

def gaussianAdaptiveTapeLaw {N : ℕ} (D : GaussianPrefixData N) (s : ℕ) :
    PMF (GaussianAdaptiveTape D s) :=
  dependentSeedLaw N (fun i => GaussianPrefixTape D i (s + N))
    (fun i => gaussianPrefixTapeLaw D i (s + N))

def gaussianAdaptiveRunLaw {N : ℕ} (D : GaussianPrefixData N) (s : ℕ) : PMF (Coeff N) :=
  (gaussianAdaptiveTapeLaw D s).map (fun tape => (gaussianAdaptiveRun D s tape).value.get)

theorem gaussianAdaptiveRun_law {N : ℕ} (D : GaussianPrefixData N) (s : ℕ) :
    gaussianAdaptiveRunLaw D s = finiteSequentialGaussianLaw (gaussianPrefixScalarData D) s := by
  unfold gaussianAdaptiveRunLaw gaussianAdaptiveTapeLaw
  simp only [gaussianAdaptiveRun_value]
  rw [prefixEval_law N (fun i => GaussianPrefixTape D i (s + N))
    (fun i => gaussianPrefixTapeLaw D i (s + N))
    (fun i z tape => (gaussianPrefixStepRun D i (Vector.ofFn z) (s + N) tape).value)]
  unfold finiteSequentialGaussianLaw
  refine congrArg (prefixPMF N) (funext fun i => funext fun z => ?_)
  have h := gaussianPrefixStepRun_law D i (Vector.ofFn z) (s + N)
  have hzget : (Vector.ofFn z).get = z := by
    funext j
    simp [Vector.get]
  simpa only [hzget] using h

/-- The stored adaptive program inherits the full triangular target error bound. -/
theorem gaussianAdaptiveRunLaw_error {N : ℕ} (hN : 2 ≤ N)
    (D : GaussianSchurData N) (hv : ∀ i, 0 < D.pivots.get i)
    {ε : ℝ} (hε : 0 < ε) (hεone : ε ≤ 1)
    (hlog : ∀ i, 4 * Real.log ((N : ℝ) / ε) ≤ (D.pivots.get i : ℝ))
    (s : ℕ) (hbudget : (1 / 2 : ℝ) ^ s ≤ ε / 4) :
    discreteTotalVariation (gaussianAdaptiveRunLaw (gaussianPrefixPrepareRun D).value s)
      (triangularGaussianLaw
        (gaussianSchurCenters ((rationalMatrixOfData D.rows).map (fun q : ℚ => (q : ℝ))))
        (fun i => (D.pivots.get i : ℝ)) (fun i => by exact_mod_cast hv i)) ≤ ε / 2 := by
  rw [gaussianAdaptiveRun_law]
  apply finiteSequentialGaussianLaw_error hN _
    (fun i z => gaussianPrefixScalarData_valid _ (gaussianPrefixPrepareRun_valid D hv) i z)
    _ _ _ (gaussianPrefixScalarData_center D) _ hε hεone hlog s hbudget
  intro i z
  rw [gaussianPrefixScalarData_widthSq _ (gaussianPrefixPrepareRun_valid D hv),
    gaussianPrefixPrepareRun_value]

end

theorem GaussianPrefixData.BitsLe.mono {N L B : ℕ} {D : GaussianPrefixData N}
    (hD : D.BitsLe L) (hLB : L ≤ B) : D.BitsLe B :=
  ⟨hD.1.trans hLB, fun i j => (hD.2.1 i j).trans hLB, fun i => (hD.2.2 i).trans hLB⟩

/-- Prepared rational-covariance sampling data, used to specify finite tape types. -/
def gaussianCovarianceData (N : ℕ) (A : RationalMatrixData N) : GaussianPrefixData N :=
  (gaussianPrefixPrepareRun (gaussianSchurRun N A).value).value

/-- Factor once, clear row denominators once, and sample the stored coordinates. -/
def gaussianCovarianceRun (N : ℕ) (A : RationalMatrixData N) (s : ℕ)
    (tape : GaussianAdaptiveTape (gaussianCovarianceData N A) s) : Costed (Vector ℤ N) :=
  let factor := gaussianSchurRun N A
  let prepared := gaussianPrefixPrepareRun factor.value
  let sample := gaussianAdaptiveRun prepared.value s tape
  ⟨sample.value, factor.steps + prepared.steps + sample.steps + 3⟩

theorem gaussianCovarianceRun_value (N : ℕ) (A : RationalMatrixData N) (s : ℕ)
    (tape : GaussianAdaptiveTape (gaussianCovarianceData N A) s) :
    (gaussianCovarianceRun N A s tape).value =
      (gaussianAdaptiveRun (gaussianCovarianceData N A) s tape).value := rfl

theorem gaussianCovarianceData_valid (N : ℕ) (A : RationalMatrixData N)
    (hA : ((rationalMatrixOfData A).map (fun q : ℚ => (q : ℝ))).PosDef) :
    (gaussianCovarianceData N A).Valid := by
  apply gaussianPrefixPrepareRun_valid
  intro i
  have h := (gaussianSchurRun_correct N A hA).2.1 i
  change (0 : ℝ) < ((gaussianSchurRun N A).value.pivots.get i : ℝ) at h
  exact_mod_cast h

def gaussianCovarianceBits (N L : ℕ) : ℕ :=
  2 * (N * N * gaussianSchurRowBitsBudget N L) +
    rationalInverseBitsBudget N (rationalInverseBitsBudget N L) + 1

theorem gaussianCovarianceBits_mono {N M L B : ℕ} (hN : N ≤ M) (hL : L ≤ B) :
    gaussianCovarianceBits N L ≤ gaussianCovarianceBits M B := by
  unfold gaussianCovarianceBits gaussianSchurRowBitsBudget rationalInverseBitsBudget rationalDetBitsBudget
  gcongr

theorem gaussianCovarianceBits_polynomial :
    PolynomialCostBound (fun t => gaussianCovarianceBits t t) := by
  let x : Polynomial ℕ := Polynomial.X
  let detP (n l : Polynomial ℕ) := n * n + n * l + 2 * (n * (n * n * l)) + 3
  let invP (n l : Polynomial ℕ) := 6 * detP n (l + 3) + 3
  refine ⟨2 * (x * x * (6 * invP x x + 3)) + invP x (invP x x) + 1, ?_⟩
  intro t
  apply le_of_eq
  simp [gaussianCovarianceBits, gaussianSchurRowBitsBudget, rationalInverseBitsBudget,
    rationalDetBitsBudget, x, detP, invP]

theorem gaussianCovarianceData_bits {N L : ℕ} (A : RationalMatrixData N)
    (hA : ((rationalMatrixOfData A).map (fun q : ℚ => (q : ℝ))).PosDef)
    (hbits : ∀ i j, rationalMagnitudeBits (rationalMatrixOfData A i j) ≤ L) :
    (gaussianCovarianceData N A).BitsLe (gaussianCovarianceBits N L) := by
  have hout := gaussianSchurRun_output_bits A hA hbits
  have hrows := rationalMatrix_bits_le_entries _ hout.1
  have h := gaussianPrefixPrepareRun_bits (gaussianSchurRun N A).value _ hout.2
  apply h.mono
  unfold gaussianCovarianceBits
  omega

theorem rationalIntegerInputBudget_mono {N M L B : ℕ} (hN : N ≤ M) (hL : L ≤ B) :
    rationalIntegerInputBudget N L ≤ rationalIntegerInputBudget M B := by
  unfold rationalIntegerInputBudget rationalDenominatorBudget rationalNumeratorBudget
    natProductBudget integerMatrixTraversalBudget
  gcongr

theorem rationalIntegerInputBudget_polynomial :
    PolynomialCostBound (fun t => rationalIntegerInputBudget t t) := by
  let x : Polynomial ℕ := Polynomial.X
  refine ⟨(2 * x * x + 1 + (x * x * ((2 * x + 2) ^ 2 + 1) + 1)) +
    (x * (x * ((2 * (2 * (x + 1) + 1) ^ 2 + (x + 1) + 1) + 3) + 4) + 1), ?_⟩
  intro t
  apply le_of_eq
  simp [rationalIntegerInputBudget, rationalDenominatorBudget, rationalNumeratorBudget,
    natProductBudget, integerMatrixTraversalBudget, x]

/-- Monotone polynomial cost bounds compose over a polynomial intermediate size. -/
theorem polynomialCostBound_comp_mono {f g : ℕ → ℕ}
    (hf : PolynomialCostBound f) (hg : PolynomialCostBound g) (hmono : Monotone f) :
    PolynomialCostBound (fun n => f (g n)) := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  refine ⟨p.comp q, fun n => ?_⟩
  simpa only [Polynomial.eval_comp] using (hmono (hq n)).trans (hp (q.eval n))

def gaussianCovarianceDiagonalCost (T : ℕ) : ℕ :=
  gaussianSchurRunBudget T T + rationalIntegerInputBudget T T + T * (T + 4) + 4 +
    gaussianAdaptiveBudget T T T + 3

theorem gaussianCovarianceDiagonalCost_mono : Monotone gaussianCovarianceDiagonalCost := by
  intro a b hab
  unfold gaussianCovarianceDiagonalCost
  gcongr
  · exact gaussianSchurRunBudget_mono hab hab
  · exact rationalIntegerInputBudget_mono hab hab
  · exact gaussianAdaptiveBudget_mono hab hab hab

theorem gaussianCovarianceDiagonalCost_polynomial : PolynomialCostBound gaussianCovarianceDiagonalCost := by
  exact (((((gaussianSchurRunBudget_polynomial.add rationalIntegerInputBudget_polynomial).add
    (PolynomialCostBound.id.mul (PolynomialCostBound.id.add (PolynomialCostBound.const 4)))).add
      (PolynomialCostBound.const 4)).add gaussianAdaptiveBudget_polynomial).add (PolynomialCostBound.const 3))

def gaussianCovarianceBudget (N L s : ℕ) : ℕ :=
  gaussianCovarianceDiagonalCost (N + L + gaussianCovarianceBits N L + s)

theorem gaussianCovarianceBudget_mono {N M L B s t : ℕ}
    (hN : N ≤ M) (hL : L ≤ B) (hs : s ≤ t) :
    gaussianCovarianceBudget N L s ≤ gaussianCovarianceBudget M B t := by
  apply gaussianCovarianceDiagonalCost_mono
  have hb := gaussianCovarianceBits_mono hN hL
  omega

theorem gaussianCovarianceBudget_polynomial :
    PolynomialCostBound (fun t => gaussianCovarianceBudget t t t) :=
  polynomialCostBound_comp_mono gaussianCovarianceDiagonalCost_polynomial
    (((PolynomialCostBound.id.add PolynomialCostBound.id).add gaussianCovarianceBits_polynomial).add
      PolynomialCostBound.id) gaussianCovarianceDiagonalCost_mono

/-- All preparation and adaptive costs are controlled by the original covariance input. -/
theorem gaussianCovarianceRun_steps_le {N L : ℕ} (A : RationalMatrixData N)
    (hA : ((rationalMatrixOfData A).map (fun q : ℚ => (q : ℝ))).PosDef)
    (hbits : ∀ i j, rationalMagnitudeBits (rationalMatrixOfData A i j) ≤ L)
    (s : ℕ) (tape : GaussianAdaptiveTape (gaussianCovarianceData N A) s) :
    (gaussianCovarianceRun N A s tape).steps ≤ gaussianCovarianceBudget N L s := by
  let B := gaussianCovarianceBits N L
  let T := N + L + B + s
  have hNT : N ≤ T := by dsimp [T]; omega
  have hLT : L ≤ T := by dsimp [T]; omega
  have hBT : B ≤ T := by dsimp [T]; omega
  have hsT : s ≤ T := by dsimp [T]; omega
  have hout := gaussianSchurRun_output_bits A hA hbits
  have hrows := rationalMatrix_bits_le_entries _ hout.1
  have hrowsT : rationalMatrixMagnitudeBits (rationalMatrixOfData (gaussianSchurRun N A).value.rows) ≤ T := by
    apply hrows.trans
    dsimp [T, B, gaussianCovarianceBits]
    omega
  have hvT : rationalInverseBitsBudget N (rationalInverseBitsBudget N L) ≤ T := by
    dsimp [T, B, gaussianCovarianceBits]
    omega
  have hfactor := (gaussianSchurRun_steps_le A hA hbits).trans (gaussianSchurRunBudget_mono hNT hLT)
  have hprep := gaussianPrefixPrepareRun_steps_le (gaussianSchurRun N A).value _ hout.2
  have hprep' : (gaussianPrefixPrepareRun (gaussianSchurRun N A).value).steps ≤
      rationalIntegerInputBudget T T + T * (T + 4) + 4 := by
    apply hprep.trans
    have hinput := rationalIntegerInputBudget_mono hNT hrowsT
    have hpiv := Nat.mul_le_mul hNT (Nat.add_le_add_right hvT 4)
    omega
  have hsamp := (gaussianAdaptiveRun_bounds (gaussianCovarianceData N A)
    (gaussianCovarianceData_valid N A hA) (gaussianCovarianceData_bits A hA hbits) s tape).2
  have hsamp' := hsamp.trans (gaussianAdaptiveBudget_mono hNT hBT hsT)
  change (gaussianSchurRun N A).steps + (gaussianPrefixPrepareRun (gaussianSchurRun N A).value).steps +
    (gaussianAdaptiveRun (gaussianCovarianceData N A) s tape).steps + 3 ≤
      gaussianCovarianceDiagonalCost T
  unfold gaussianCovarianceDiagonalCost
  omega

theorem gaussianCovarianceRun_polynomial : ∃ C k : ℕ, ∀ (N : ℕ) (A : RationalMatrixData N),
    ((rationalMatrixOfData A).map (fun q : ℚ => (q : ℝ))).PosDef → ∀ (s : ℕ)
      (tape : GaussianAdaptiveTape (gaussianCovarianceData N A) s),
      (gaussianCovarianceRun N A s tape).steps ≤
        C * (N + rationalMatrixMagnitudeBits (rationalMatrixOfData A) + s + 1) ^ k := by
  obtain ⟨C, k, h⟩ := gaussianCovarianceBudget_polynomial.exists_mul_pow_bound
  refine ⟨C, k, fun N A hA s tape => ?_⟩
  exact (gaussianCovarianceRun_steps_le A hA (rationalMatrix_entry_bits_le _) s tape).trans
    ((gaussianCovarianceBudget_mono (by omega) (by omega) (by omega)).trans
      (h (N + rationalMatrixMagnitudeBits (rationalMatrixOfData A) + s)))

theorem gaussianCovarianceRun_output_bits {N L : ℕ} (A : RationalMatrixData N)
    (hA : ((rationalMatrixOfData A).map (fun q : ℚ => (q : ℝ))).PosDef)
    (hbits : ∀ i j, rationalMagnitudeBits (rationalMatrixOfData A i j) ≤ L)
    (s : ℕ) (tape : GaussianAdaptiveTape (gaussianCovarianceData N A) s) (i : Fin N) :
    ((gaussianCovarianceRun N A s tape).value.get i).natAbs.size ≤
      N * gaussianAdaptiveGrowth N (gaussianCovarianceBits N L) s := by
  rw [gaussianCovarianceRun_value]
  exact (gaussianAdaptiveRun_bounds (gaussianCovarianceData N A)
    (gaussianCovarianceData_valid N A hA) (gaussianCovarianceData_bits A hA hbits) s tape).1 i

open Matrix

theorem gaussianSchurRun_pivots_lower (N : ℕ) (A : RationalMatrixData N)
    (hA : ((rationalMatrixOfData A).map (fun q : ℚ => (q : ℝ))).PosDef)
    {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hlower : ∀ x : Fin N → ℝ, ρ * (∑ j, x j ^ 2) ≤
      x ⬝ᵥ (((rationalMatrixOfData A).map (fun q : ℚ => (q : ℝ))) *ᵥ x)) (i : Fin N) :
    ρ ≤ ((gaussianSchurRun N A).value.pivots.get i : ℝ) := by
  have h := gaussianSchurFactor_width_lower N _ hA hρ hlower i
  have hmap := congrFun (congrArg Prod.snd
    (gaussianSchurFactor_map (Rat.castHom ℝ) N (rationalMatrixOfData A))) i
  change (gaussianSchurFactor N ((rationalMatrixOfData A).map (fun q : ℚ => (q : ℝ)))).2 i =
    ((gaussianSchurFactor N (rationalMatrixOfData A)).2 i : ℝ) at hmap
  have hrun := congrFun (congrArg Prod.snd (gaussianSchurRun_value N A)) i
  change (gaussianSchurRun N A).value.pivots.get i =
    (gaussianSchurFactor N (rationalMatrixOfData A)).2 i at hrun
  rw [hmap, ← hrun] at h
  exact h

noncomputable section

/-- The law of the actual stored covariance sampler under independent finite words. -/
def gaussianCovarianceRunLaw (N : ℕ) (A : RationalMatrixData N) (s : ℕ) : PMF (Coeff N) :=
  (gaussianAdaptiveTapeLaw (gaussianCovarianceData N A) s).map
    (fun tape => (gaussianCovarianceRun N A s tape).value.get)

theorem gaussianCovarianceRun_law (N : ℕ) (A : RationalMatrixData N) (s : ℕ) :
    gaussianCovarianceRunLaw N A s = gaussianAdaptiveRunLaw (gaussianCovarianceData N A) s := by
  simp only [gaussianCovarianceRunLaw, gaussianCovarianceRun_value, gaussianAdaptiveRunLaw]

/-- A supplied covariance lower bound gives the full ellipsoidal sampling budget.
No adaptive-data, sampler-accuracy, or intermediate-bit hypothesis is assumed. -/
theorem gaussianCovarianceRunLaw_error {N : ℕ} (hN : 2 ≤ N) (A : RationalMatrixData N)
    (hA : ((rationalMatrixOfData A).map (fun q : ℚ => (q : ℝ))).PosDef)
    (M : Matrix (Fin N) (Fin N) ℝ) (S : Euclidean N ≃L[ℝ] Euclidean N)
    (hM : Matrix.toEuclideanLin M = S.toLinearMap)
    (hshape : (rationalMatrixOfData A).map (fun q : ℚ => (q : ℝ)) = M * M.transpose)
    {ρ ε : ℝ} (hρ : 0 ≤ ρ)
    (hlower : ∀ x : Fin N → ℝ, ρ * (∑ j, x j ^ 2) ≤
      x ⬝ᵥ (((rationalMatrixOfData A).map (fun q : ℚ => (q : ℝ))) *ᵥ x))
    (hε : 0 < ε) (hεone : ε ≤ 1) (hlog : 4 * Real.log ((N : ℝ) / ε) ≤ ρ)
    (s : ℕ) (hbudget : (1 / 2 : ℝ) ^ s ≤ ε / 4) :
    discreteTotalVariation (gaussianCovarianceRunLaw N A s) (ellipsoidalGaussian S 0) ≤ ε / 2 := by
  let D := (gaussianSchurRun N A).value
  let U := (rationalMatrixOfData D.rows).map (fun q : ℚ => (q : ℝ))
  let v := fun i => (D.pivots.get i : ℝ)
  have hc := gaussianSchurRun_correct N A hA
  change U * (rationalMatrixOfData A).map (fun q : ℚ => (q : ℝ)) * U.transpose = diagonal v ∧
    (∀ i, 0 < v i) ∧ (∀ i, U i i = 1) ∧ (∀ i j, i < j → U i j = 0) at hc
  have hv : ∀ i, 0 < D.pivots.get i := by
    intro i
    have h := hc.2.1 i
    change (0 : ℝ) < (D.pivots.get i : ℝ) at h
    exact_mod_cast h
  have hwidth : ∀ i, 4 * Real.log ((N : ℝ) / ε) ≤ v i :=
    fun i => hlog.trans (gaussianSchurRun_pivots_lower N A hA hρ hlower i)
  have hseq := gaussianAdaptiveRunLaw_error hN D hv hε hεone hwidth s hbudget
  have hcov : U * (M * M.transpose) * U.transpose = diagonal v := by
    rw [← hshape]
    exact hc.1
  have he := schur_law_eq_ellipsoidalGaussian U M S hM v hc.2.1 hc.2.2.1 hc.2.2.2 hcov
  rw [gaussianCovarianceRun_law, ← he]
  exact hseq

theorem gaussianCovarianceRunLaw_error_dyadic {N : ℕ} (hN : 2 ≤ N) (A : RationalMatrixData N)
    (hA : ((rationalMatrixOfData A).map (fun q : ℚ => (q : ℝ))).PosDef)
    (M : Matrix (Fin N) (Fin N) ℝ) (S : Euclidean N ≃L[ℝ] Euclidean N)
    (hM : Matrix.toEuclideanLin M = S.toLinearMap)
    (hshape : (rationalMatrixOfData A).map (fun q : ℚ => (q : ℝ)) = M * M.transpose)
    {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hlower : ∀ x : Fin N → ℝ, ρ * (∑ j, x j ^ 2) ≤
      x ⬝ᵥ (((rationalMatrixOfData A).map (fun q : ℚ => (q : ℝ))) *ᵥ x))
    (s : ℕ) (hlog : 4 * Real.log ((N : ℝ) / (1 / 2 : ℝ) ^ s) ≤ ρ) :
    discreteTotalVariation (gaussianCovarianceRunLaw N A (s + 2)) (ellipsoidalGaussian S 0) ≤
      (1 / 2 : ℝ) ^ (s + 1) := by
  have hεone : (1 / 2 : ℝ) ^ s ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hbudget : (1 / 2 : ℝ) ^ (s + 2) ≤ (1 / 2 : ℝ) ^ s / 4 := by
    rw [pow_add]
    norm_num
    exact le_of_eq (by ring)
  have h := gaussianCovarianceRunLaw_error hN A hA M S hM hshape hρ hlower
    (by positivity : 0 < (1 / 2 : ℝ) ^ s) hεone hlog (s + 2) hbudget
  apply h.trans
  rw [pow_succ]
  exact le_of_eq (by ring)

end

end SISToKSIS


open Module NumberField GeometricGaussianLHL
open scoped MatrixOrder
namespace SISToKSIS
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable (K : Type*) [Field K] [NumberField K] {d : ℕ}
local instance bridgeAmbientInner : InnerProductSpace ℝ (CanonicalAmbient K) := inferInstance
local instance bridgeSpaceInner : InnerProductSpace ℝ (canonicalSpace K) := inferInstance
local instance bridgePowerInner (n : ℕ) : InnerProductSpace ℝ (CanonicalPower K n) := inferInstance

theorem canonicalGramSquareRoot_scalar (b : Basis (Fin d) ℤ (𝓞 K)) {c : ℝ}
    (hc : 0 < c) (hGram : ∀ i j, canonicalGram K b i j = if i = j then c else 0)
    (x : Euclidean d) :
    positiveSquareRootShape (canonicalGram K b) (canonicalGram_posDef K b) x = Real.sqrt c • x := by
  classical
  have hg : canonicalGram K b = c • (1 : Matrix (Fin d) (Fin d) ℝ) := by
    ext i j
    by_cases hij : i = j <;> simp [hGram, hij]
  have hsqrt : CFC.sqrt (canonicalGram K b) = Real.sqrt c • (1 : Matrix (Fin d) (Fin d) ℝ) := by
    apply CFC.sqrt_unique ?_ (smul_nonneg (Real.sqrt_nonneg _) zero_le_one)
    rw [Matrix.smul_mul, Matrix.mul_smul, one_mul, smul_smul, ← pow_two,
      Real.sq_sqrt hc.le, ← hg]
  change Matrix.toEuclideanLin (CFC.sqrt (canonicalGram K b)) x = _
  rw [hsqrt]
  simp

theorem canonicalGramPowerRoot_scalar (b : Basis (Fin d) ℤ (𝓞 K)) {c : ℝ}
    (hc : 0 < c) (hGram : ∀ i j, canonicalGram K b i j = if i = j then c else 0)
    (n : ℕ) (x : Euclidean (n * d)) : canonicalGramPowerRoot K b n x = Real.sqrt c • x := by
  apply (euclideanBlocks n d).injective
  rw [canonicalGramPowerRoot_apply, map_smul]
  ext j : 1
  change positiveSquareRootShape (canonicalGram K b) (canonicalGram_posDef K b)
    (euclideanBlocks n d x j) = Real.sqrt c • (euclideanBlocks n d x j)
  exact canonicalGramSquareRoot_scalar K b hc hGram _

theorem canonicalEuclideanEmbedding_gram_coordinates (b : Basis (Fin d) ℤ (𝓞 K))
    (n : ℕ) (x : Fin n → 𝓞 K) :
    canonicalEuclideanEmbedding K b n x = canonicalGramEuclideanIsometry K b n
      (canonicalGramPowerRoot K b n (integerEmbedding (n * d) (ringPowerCoordinates b n x))) := by
  change canonicalOrthonormalCoordinates K b n (canonicalPowerEmbedding K n x) =
    canonicalOrthonormalCoordinates K b n (canonicalGramPowerIsometry K b n _)
  rw [canonicalGramPowerIsometry_apply, ContinuousLinearEquiv.symm_apply_apply,
    powerCanonicalEquiv_integer]

theorem canonicalEuclideanEmbedding_scalar_gram (b : Basis (Fin d) ℤ (𝓞 K)) {c : ℝ}
    (hc : 0 < c) (hGram : ∀ i j, canonicalGram K b i j = if i = j then c else 0)
    (n : ℕ) (x : Fin n → 𝓞 K) :
    canonicalEuclideanEmbedding K b n x = canonicalGramEuclideanIsometry K b n
      (Real.sqrt c • integerEmbedding (n * d) (ringPowerCoordinates b n x)) := by
  rw [canonicalEuclideanEmbedding_gram_coordinates, canonicalGramPowerRoot_scalar K b hc hGram]

/-- Coefficient shape used only to state the target law; the sampler computes its covariance. -/
def coefficientComputedShape {N : ℕ} (R : Matrix (Fin N) (Fin N) ℝ) (hR : R.PosDef)
    (c : ℝ) (hc : 0 < c) : Euclidean N ≃L[ℝ] Euclidean N :=
  (positiveMatrixShape R hR).trans (euclideanScalarShape N (Real.sqrt c)⁻¹
    (inv_ne_zero (Real.sqrt_pos.mpr hc).ne'))

theorem coefficientComputedShape_symm_apply {N : ℕ} (R : Matrix (Fin N) (Fin N) ℝ)
    (hR : R.PosDef) (c : ℝ) (hc : 0 < c) (x : Euclidean N) :
    (coefficientComputedShape R hR c hc).symm x =
      (positiveMatrixShape R hR).symm (Real.sqrt c • x) := by
  change (positiveMatrixShape R hR).symm ((Real.sqrt c)⁻¹⁻¹ • x) = _
  rw [inv_inv]

/-- The integer-coordinate weights of the computed canonical shape agree exactly. -/
theorem canonicalComputedShape_coefficient_weight (b : Basis (Fin d) ℤ (𝓞 K)) {c : ℝ}
    (hc : 0 < c) (hGram : ∀ i j, canonicalGram K b i j = if i = j then c else 0)
    (n : ℕ) (R : Matrix (Fin (n * d)) (Fin (n * d)) ℝ) (hR : R.PosDef)
    (x : Fin n → 𝓞 K) :
    ellipsoidWeight (coefficientComputedShape R hR c hc) 0 (ringPowerCoordinates b n x) =
      gaussianWeight 1 ((canonicalComputedShape K b R hR).symm (canonicalEuclideanEmbedding K b n x)) := by
  rw [canonicalEuclideanEmbedding_scalar_gram K b hc hGram]
  simp only [ellipsoidWeight, sub_zero, coefficientComputedShape_symm_apply,
    canonicalComputedShape, isometricTransportShape]
  change gaussianWeight 1 ((positiveMatrixShape R hR).symm
      (Real.sqrt c • integerEmbedding (n * d) (ringPowerCoordinates b n x))) =
    gaussianWeight 1 (canonicalGramEuclideanIsometry K b n ((positiveMatrixShape R hR).symm
      ((canonicalGramEuclideanIsometry K b n).symm (canonicalGramEuclideanIsometry K b n
        (Real.sqrt c • integerEmbedding (n * d) (ringPowerCoordinates b n x))))))
  rw [LinearIsometryEquiv.symm_apply_apply]
  simp only [gaussianWeight, LinearIsometryEquiv.norm_map]

theorem canonicalComputedShape_coefficient_partition (b : Basis (Fin d) ℤ (𝓞 K)) {c : ℝ}
    (hc : 0 < c) (hGram : ∀ i j, canonicalGram K b i j = if i = j then c else 0)
    (n : ℕ) (R : Matrix (Fin (n * d)) (Fin (n * d)) ℝ) (hR : R.PosDef) :
    ellipsoidPartition (coefficientComputedShape R hR c hc) 0 =
      numberFieldEllipsoidPartition K b n (canonicalComputedShape K b R hR) := by
  unfold ellipsoidPartition numberFieldEllipsoidPartition
  rw [← (ringPowerCoordinates b n).toEquiv.tsum_eq]
  exact tsum_congr (canonicalComputedShape_coefficient_weight K b hc hGram n R hR)

/-- Transport through the integral basis introduces no additional statistical error. -/
theorem canonicalComputedShape_coefficient_law (b : Basis (Fin d) ℤ (𝓞 K)) {c : ℝ}
    (hc : 0 < c) (hGram : ∀ i j, canonicalGram K b i j = if i = j then c else 0)
    (n : ℕ) (R : Matrix (Fin (n * d)) (Fin (n * d)) ℝ) (hR : R.PosDef) :
    (numberFieldEllipsoidalGaussian K b n (canonicalComputedShape K b R hR) 0).map
      (ringPowerCoordinates b n) = ellipsoidalGaussian (coefficientComputedShape R hR c hc) 0 := by
  ext z
  obtain ⟨x, rfl⟩ := (ringPowerCoordinates b n).surjective z
  have h := pmf_map_equiv_apply
    (numberFieldEllipsoidalGaussian K b n (canonicalComputedShape K b R hR) 0)
    (ringPowerCoordinates b n).toEquiv x
  change ((numberFieldEllipsoidalGaussian K b n (canonicalComputedShape K b R hR) 0).map
      (ringPowerCoordinates b n)) (ringPowerCoordinates b n x) = _ at h
  rw [h, numberFieldEllipsoidalGaussian_apply, ellipsoidalGaussian_apply,
    canonicalComputedShape_coefficient_weight K b hc hGram,
    canonicalComputedShape_coefficient_partition K b hc hGram, map_zero, sub_zero]

theorem coefficientComputedShape_linear {N : ℕ} (R : Matrix (Fin N) (Fin N) ℝ)
    (hR : R.PosDef) (c : ℝ) (hc : 0 < c) :
    Matrix.toEuclideanLin ((Real.sqrt c)⁻¹ • R) =
      (coefficientComputedShape R hR c hc).toLinearMap := by
  ext x : 1
  rw [map_smul]
  rfl

theorem coefficientComputedShape_covariance {N : ℕ} (R : Matrix (Fin N) (Fin N) ℝ)
    (c : ℝ) (hc : 0 < c) :
    ((Real.sqrt c)⁻¹ • R) * ((Real.sqrt c)⁻¹ • R).transpose = c⁻¹ • (R * R.transpose) := by
  rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    ← pow_two, inv_pow, Real.sq_sqrt hc.le]

theorem coefficientCovariance_posDef {N : ℕ} (R : Matrix (Fin N) (Fin N) ℝ)
    (hR : R.PosDef) (c : ℝ) (hc : 0 < c) : (c⁻¹ • (R * R.transpose)).PosDef := by
  have h := Matrix.PosDef.mul_conjTranspose_self R (Matrix.vecMul_injective_of_isUnit hR.isUnit)
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using h.smul (inv_pos.mpr hc)

/-- Compute the coefficient covariance of a shape in a basis with Gram matrix `d I`. -/
def coefficientCovarianceRun (N d : ℕ) (R : RationalMatrixData N) :
    Costed (RationalMatrixData N) :=
  (costedRationalRowGram R).bind fun G =>
    (Costed.charge (d.size + 1) (d : ℚ)).bind fun divisor =>
      (costedRatDiv 1 divisor).bind fun scale => costedRationalRectScale scale G

theorem coefficientCovarianceRun_value (N d : ℕ) (R : RationalMatrixData N) :
    (coefficientCovarianceRun N d R).value =
      rationalRectMatrixData ((d : ℚ)⁻¹ •
        (rationalMatrixOfData R * (rationalMatrixOfData R).transpose)) := by
  change (costedRationalRectScale (1 / (d : ℚ)) (costedRationalRowGram R).value).value = _
  rw [one_div, costedRationalRectScale_data, costedRationalRowGram_data,
    rationalRectMatrixOfData_data]
  rfl

theorem coefficientCovarianceRun_real (N d : ℕ) (R : RationalMatrixData N) :
    (rationalMatrixOfData (coefficientCovarianceRun N d R).value).map (fun q : ℚ => (q : ℝ)) =
      (d : ℝ)⁻¹ • ((rationalMatrixOfData R).map (fun q : ℚ => (q : ℝ)) *
        ((rationalMatrixOfData R).map (fun q : ℚ => (q : ℝ))).transpose) := by
  rw [coefficientCovarianceRun_value]
  change (rationalRectMatrixOfData (rationalRectMatrixData _)).map _ = _
  rw [rationalRectMatrixOfData_data]
  ext i j
  simp [Matrix.mul_apply, Matrix.smul_apply,
    Matrix.transpose_apply, Matrix.map_apply]

theorem coefficientCovarianceRun_posDef (N d : ℕ) (hd : 0 < d) (R : RationalMatrixData N)
    (hR : ((rationalMatrixOfData R).map (fun q : ℚ => (q : ℝ))).PosDef) :
    ((rationalMatrixOfData (coefficientCovarianceRun N d R).value).map
      (fun q : ℚ => (q : ℝ))).PosDef := by
  rw [coefficientCovarianceRun_real]
  exact coefficientCovariance_posDef _ hR _ (by exact_mod_cast hd)

theorem rationalNatCast_bits_le (d : ℕ) : rationalMagnitudeBits (d : ℚ) ≤ d + 2 := by
  have hd : d.size ≤ d := Nat.size_le.mpr Nat.lt_two_pow_self
  simpa using (intCast_rational_bits (d : ℤ)).le.trans (Nat.add_le_add_right hd 2)

def coefficientCovarianceOperandBits (N L d : ℕ) : ℕ := rationalDotOperandBudget N L + d + 3

def coefficientCovarianceBits (N L d : ℕ) : ℕ := 6 * coefficientCovarianceOperandBits N L d + 3

def coefficientCovarianceBudget (N L d : ℕ) : ℕ :=
  rationalRowGramBudget N N L + d + 1 + (2 * (d + 3) + 1) ^ 3 +
    rationalRectTraversalBudget N N ((2 * coefficientCovarianceOperandBits N L d + 1) ^ 3)

theorem coefficientCovarianceRun_bits (N d L : ℕ) (R : RationalMatrixData N)
    (hR : ∀ i j, rationalMagnitudeBits (rationalMatrixOfData R i j) ≤ L) (i j : Fin N) :
    rationalMagnitudeBits (rationalMatrixOfData (coefficientCovarianceRun N d R).value i j) ≤
      coefficientCovarianceBits N L d := by
  have hscale : rationalMagnitudeBits ((d : ℚ)⁻¹) ≤ coefficientCovarianceOperandBits N L d := by
    rw [rational_inv_bits]
    exact (rationalNatCast_bits_le d).trans (by unfold coefficientCovarianceOperandBits; omega)
  have hgram : ∀ i j, rationalMagnitudeBits
      (rationalMatrixOfData (costedRationalRowGram R).value i j) ≤
        coefficientCovarianceOperandBits N L d := fun i j =>
    (costedRationalRowGram_size R L hR i j).trans (by unfold coefficientCovarianceOperandBits; omega)
  change rationalMagnitudeBits (rationalMatrixOfData
    (costedRationalRectScale (1 / (d : ℚ)) (costedRationalRowGram R).value).value i j) ≤ _
  rw [one_div]
  exact costedRationalRectScale_size ((d : ℚ)⁻¹)
    (costedRationalRowGram R).value _ hscale hgram i j

theorem coefficientCovarianceRun_steps_le (N d L : ℕ) (R : RationalMatrixData N)
    (hR : ∀ i j, rationalMagnitudeBits (rationalMatrixOfData R i j) ≤ L) :
    (coefficientCovarianceRun N d R).steps ≤ coefficientCovarianceBudget N L d := by
  have hg := costedRationalRowGram_steps_le R L hR
  have hd : d.size ≤ d := Nat.size_le.mpr Nat.lt_two_pow_self
  have hdiv := rationalArithmeticCost_le (1 : ℚ) (d : ℚ)
    (show rationalMagnitudeBits (1 : ℚ) ≤ d + 3 by norm_num [rationalMagnitudeBits])
    ((rationalNatCast_bits_le d).trans (by omega : d + 2 ≤ d + 3))
  have hscale : rationalMagnitudeBits ((d : ℚ)⁻¹) ≤ coefficientCovarianceOperandBits N L d := by
    rw [rational_inv_bits]
    exact (rationalNatCast_bits_le d).trans (by unfold coefficientCovarianceOperandBits; omega)
  have hgram : ∀ i j, rationalMagnitudeBits
      (rationalMatrixOfData (costedRationalRowGram R).value i j) ≤
        coefficientCovarianceOperandBits N L d := fun i j =>
    (costedRationalRowGram_size R L hR i j).trans (by unfold coefficientCovarianceOperandBits; omega)
  have hs := costedRationalRectScale_steps_le ((d : ℚ)⁻¹) (costedRationalRowGram R).value
    _ hscale hgram
  simp only [coefficientCovarianceRun, Costed.bind_steps, Costed.charge, costedRatDiv,
    one_div] at *
  unfold coefficientCovarianceBudget
  omega

open Matrix

theorem coefficientCovarianceBits_mono {N M L B d e : ℕ}
    (hN : N ≤ M) (hL : L ≤ B) (hd : d ≤ e) :
    coefficientCovarianceBits N L d ≤ coefficientCovarianceBits M B e := by
  unfold coefficientCovarianceBits coefficientCovarianceOperandBits rationalDotOperandBudget
  gcongr

theorem coefficientCovarianceBudget_mono {N M L B d e : ℕ}
    (hN : N ≤ M) (hL : L ≤ B) (hd : d ≤ e) :
    coefficientCovarianceBudget N L d ≤ coefficientCovarianceBudget M B e := by
  unfold coefficientCovarianceBudget coefficientCovarianceOperandBits rationalRowGramBudget
    rationalRectMulBudget rationalRectTraversalBudget rationalDotBudget rationalDotOperandBudget
  gcongr

theorem coefficientCovarianceBits_polynomial :
    PolynomialCostBound (fun t => coefficientCovarianceBits t t t) :=
  ((PolynomialCostBound.const 6).mul
    (((polyBound_rationalDotOperandBudget PolynomialCostBound.id PolynomialCostBound.id).add
      PolynomialCostBound.id).add (PolynomialCostBound.const 3))).add (PolynomialCostBound.const 3)

theorem coefficientCovarianceBudget_polynomial :
    PolynomialCostBound (fun t => coefficientCovarianceBudget t t t) := by
  have hop : PolynomialCostBound (fun t => coefficientCovarianceOperandBits t t t) :=
    ((polyBound_rationalDotOperandBudget PolynomialCostBound.id PolynomialCostBound.id).add
      PolynomialCostBound.id).add (PolynomialCostBound.const 3)
  exact ((((polyBound_rationalRowGramBudget PolynomialCostBound.id PolynomialCostBound.id
    PolynomialCostBound.id).add PolynomialCostBound.id).add (PolynomialCostBound.const 1)).add
      ((((PolynomialCostBound.const 2).mul (PolynomialCostBound.id.add (PolynomialCostBound.const 3))).add
        (PolynomialCostBound.const 1)).pow 3)).add
    (polyBound_rationalRectTraversalBudget PolynomialCostBound.id PolynomialCostBound.id
      ((((PolynomialCostBound.const 2).mul hop).add (PolynomialCostBound.const 1)).pow 3))

/-- Finite tape for the computed shape, determined by its rational covariance. -/
abbrev CoefficientShapeSampleTape (N d : ℕ) (R : RationalMatrixData N) (s : ℕ) :=
  GaussianAdaptiveTape (gaussianCovarianceData N (coefficientCovarianceRun N d R).value) s

/-- Form the stored covariance once and then invoke the finite covariance sampler. -/
def coefficientShapeSampleRun (N d : ℕ) (R : RationalMatrixData N) (s : ℕ)
    (tape : CoefficientShapeSampleTape N d R s) : Costed (Vector ℤ N) :=
  let covariance := coefficientCovarianceRun N d R
  let sample := gaussianCovarianceRun N covariance.value s tape
  ⟨sample.value, covariance.steps + sample.steps + 1⟩

theorem coefficientShapeSampleRun_value (N d : ℕ) (R : RationalMatrixData N) (s : ℕ)
    (tape : CoefficientShapeSampleTape N d R s) :
    (coefficientShapeSampleRun N d R s tape).value =
      (gaussianCovarianceRun N (coefficientCovarianceRun N d R).value s tape).value := rfl

def coefficientShapeSampleDiagonalCost (T : ℕ) : ℕ :=
  coefficientCovarianceBudget T T T + gaussianCovarianceBudget T T T + 1

theorem coefficientShapeSampleDiagonalCost_mono {T U : ℕ} (h : T ≤ U) :
    coefficientShapeSampleDiagonalCost T ≤ coefficientShapeSampleDiagonalCost U :=
  Nat.add_le_add_right (Nat.add_le_add (coefficientCovarianceBudget_mono h h h)
    (gaussianCovarianceBudget_mono h h h)) 1

theorem coefficientShapeSampleDiagonalCost_polynomial : PolynomialCostBound coefficientShapeSampleDiagonalCost :=
  (coefficientCovarianceBudget_polynomial.add gaussianCovarianceBudget_polynomial).add
    (PolynomialCostBound.const 1)

def coefficientShapeSampleBudget (N L d s : ℕ) : ℕ :=
  coefficientShapeSampleDiagonalCost (N + L + d + s + coefficientCovarianceBits N L d)

theorem coefficientShapeSampleBudget_mono {N M L B d e s t : ℕ}
    (hN : N ≤ M) (hL : L ≤ B) (hd : d ≤ e) (hs : s ≤ t) :
    coefficientShapeSampleBudget N L d s ≤ coefficientShapeSampleBudget M B e t := by
  apply coefficientShapeSampleDiagonalCost_mono
  have hb := coefficientCovarianceBits_mono hN hL hd
  omega

theorem coefficientShapeSampleBudget_polynomial :
    PolynomialCostBound (fun t => coefficientShapeSampleBudget t t t t) :=
  polynomialCostBound_comp_mono coefficientShapeSampleDiagonalCost_polynomial
    ((((PolynomialCostBound.id.add PolynomialCostBound.id).add PolynomialCostBound.id).add
      PolynomialCostBound.id).add coefficientCovarianceBits_polynomial)
    (fun _ _ h => coefficientShapeSampleDiagonalCost_mono h)

theorem coefficientShapeSampleRun_steps_le {N L d : ℕ} (hd : 0 < d)
    (R : RationalMatrixData N)
    (hR : ((rationalMatrixOfData R).map (fun q : ℚ => (q : ℝ))).PosDef)
    (hbits : ∀ i j, rationalMagnitudeBits (rationalMatrixOfData R i j) ≤ L)
    (s : ℕ) (tape : CoefficientShapeSampleTape N d R s) :
    (coefficientShapeSampleRun N d R s tape).steps ≤ coefficientShapeSampleBudget N L d s := by
  let T := N + L + d + s + coefficientCovarianceBits N L d
  have hc := (coefficientCovarianceRun_steps_le N d L R hbits).trans
    (coefficientCovarianceBudget_mono (show N ≤ T by dsimp [T]; omega)
      (show L ≤ T by dsimp [T]; omega) (show d ≤ T by dsimp [T]; omega))
  have hs := (gaussianCovarianceRun_steps_le (coefficientCovarianceRun N d R).value
    (coefficientCovarianceRun_posDef N d hd R hR) (coefficientCovarianceRun_bits N d L R hbits) s tape).trans
      (gaussianCovarianceBudget_mono (show N ≤ T by dsimp [T]; omega)
        (show coefficientCovarianceBits N L d ≤ T by dsimp [T]; omega)
        (show s ≤ T by dsimp [T]; omega))
  exact Nat.add_le_add_right (Nat.add_le_add hc hs) 1

theorem coefficientShapeSampleRun_polynomial : ∃ C k : ℕ, ∀ (N d : ℕ), 0 < d →
    ∀ (R : RationalMatrixData N), ((rationalMatrixOfData R).map (fun q : ℚ => (q : ℝ))).PosDef →
      ∀ (s : ℕ) (tape : CoefficientShapeSampleTape N d R s),
        (coefficientShapeSampleRun N d R s tape).steps ≤
          C * (N + rationalMatrixMagnitudeBits (rationalMatrixOfData R) + d + s + 1) ^ k := by
  obtain ⟨C, k, h⟩ := coefficientShapeSampleBudget_polynomial.exists_mul_pow_bound
  refine ⟨C, k, fun N d hd R hR s tape => ?_⟩
  exact (coefficientShapeSampleRun_steps_le hd R hR (rationalMatrix_entry_bits_le _) s tape).trans
    ((coefficientShapeSampleBudget_mono (by omega) (by omega) (by omega) (by omega)).trans
      (h (N + rationalMatrixMagnitudeBits (rationalMatrixOfData R) + d + s)))

theorem coefficientShapeSampleRun_output_bits {N L d : ℕ} (hd : 0 < d)
    (R : RationalMatrixData N)
    (hR : ((rationalMatrixOfData R).map (fun q : ℚ => (q : ℝ))).PosDef)
    (hbits : ∀ i j, rationalMagnitudeBits (rationalMatrixOfData R i j) ≤ L)
    (s : ℕ) (tape : CoefficientShapeSampleTape N d R s) (i : Fin N) :
    ((coefficientShapeSampleRun N d R s tape).value.get i).natAbs.size ≤
      N * gaussianAdaptiveGrowth N (gaussianCovarianceBits N (coefficientCovarianceBits N L d)) s :=
  gaussianCovarianceRun_output_bits (coefficientCovarianceRun N d R).value
    (coefficientCovarianceRun_posDef N d hd R hR) (coefficientCovarianceRun_bits N d L R hbits) s tape i

def coefficientShapeSampleLaw (N d : ℕ) (R : RationalMatrixData N) (s : ℕ) : PMF (Fin N → ℤ) :=
  (gaussianAdaptiveTapeLaw (gaussianCovarianceData N (coefficientCovarianceRun N d R).value) s).map
    (fun tape => (coefficientShapeSampleRun N d R s tape).value.get)

theorem coefficientShapeSampleLaw_eq (N d : ℕ) (R : RationalMatrixData N) (s : ℕ) :
    coefficientShapeSampleLaw N d R s =
      gaussianCovarianceRunLaw N (coefficientCovarianceRun N d R).value s := rfl

/-- Interpret the finite integer output through the already supplied integral basis. -/
def computedNumberFieldSampleLaw (b : Basis (Fin d) ℤ (𝓞 K)) (n : ℕ)
    (R : RationalMatrixData (n * d)) (s : ℕ) : PMF (Fin n → 𝓞 K) :=
  (coefficientShapeSampleLaw (n * d) d R s).map (ringPowerCoordinates b n).symm

theorem computedNumberFieldSampleLaw_error (b : Basis (Fin d) ℤ (𝓞 K))
    (hGram : ∀ i j, canonicalGram K b i j = if i = j then (d : ℝ) else 0)
    (n : ℕ) (hN : 2 ≤ n * d) (R : RationalMatrixData (n * d))
    (hR : ((rationalMatrixOfData R).map (fun q : ℚ => (q : ℝ))).PosDef)
    {ρ ε : ℝ} (hρ : 0 ≤ ρ)
    (hlower : ∀ x : Fin (n * d) → ℝ, ρ * (∑ j, x j ^ 2) ≤
      x ⬝ᵥ (((rationalMatrixOfData (coefficientCovarianceRun (n * d) d R).value).map
        (fun q : ℚ => (q : ℝ))) *ᵥ x))
    (hε : 0 < ε) (hεone : ε ≤ 1) (hlog : 4 * Real.log ((n * d : ℕ) / ε) ≤ ρ)
    (s : ℕ) (hbudget : (1 / 2 : ℝ) ^ s ≤ ε / 4) :
    discreteTotalVariation (computedNumberFieldSampleLaw K b n R s)
      (numberFieldEllipsoidalGaussian K b n
        (canonicalComputedShape K b _ hR) 0) ≤ ε / 2 := by
  have hd : 0 < d := integralBasis_dimension_pos K b
  have hdreal : (0 : ℝ) < d := by exact_mod_cast hd
  let Rreal := (rationalMatrixOfData R).map (fun q : ℚ => (q : ℝ))
  have hcov : (rationalMatrixOfData (coefficientCovarianceRun (n * d) d R).value).map
      (fun q : ℚ => (q : ℝ)) =
      ((Real.sqrt (d : ℝ))⁻¹ • Rreal) * ((Real.sqrt (d : ℝ))⁻¹ • Rreal).transpose := by
    rw [coefficientComputedShape_covariance _ _ hdreal, coefficientCovarianceRun_real]
  have hs := gaussianCovarianceRunLaw_error hN (coefficientCovarianceRun (n * d) d R).value
    (coefficientCovarianceRun_posDef _ _ hd R hR) _ (coefficientComputedShape Rreal hR d hdreal)
    (coefficientComputedShape_linear _ _ _ _) hcov hρ hlower hε hεone hlog s hbudget
  have he := discreteTotalVariation_map_equiv (computedNumberFieldSampleLaw K b n R s)
    (numberFieldEllipsoidalGaussian K b n (canonicalComputedShape K b Rreal hR) 0)
    (ringPowerCoordinates b n).toEquiv
  rw [← he]
  have hmap : (computedNumberFieldSampleLaw K b n R s).map (ringPowerCoordinates b n).toEquiv =
      coefficientShapeSampleLaw (n * d) d R s := by
    rw [computedNumberFieldSampleLaw, PMF.map_comp]
    have hf : (⇑(ringPowerCoordinates b n).toEquiv ∘ ⇑(ringPowerCoordinates b n).symm) = id := by
      funext x
      exact (ringPowerCoordinates b n).apply_symm_apply x
    rw [hf, PMF.map_id]
  rw [hmap]
  have htarget := canonicalComputedShape_coefficient_law K b hdreal hGram n Rreal hR
  change (numberFieldEllipsoidalGaussian K b n (canonicalComputedShape K b Rreal hR) 0).map
    (ringPowerCoordinates b n).toEquiv = _ at htarget
  rw [htarget, coefficientShapeSampleLaw_eq]
  exact hs

open Matrix

theorem coefficientCovariance_energy {N : ℕ} (R : Matrix (Fin N) (Fin N) ℝ)
    (hR : R.PosDef) (c : ℝ) (x : Fin N → ℝ) :
    x ⬝ᵥ ((c⁻¹ • (R * R.transpose)) *ᵥ x) =
      c⁻¹ * ‖positiveMatrixShape R hR (WithLp.toLp 2 x)‖ ^ 2 := by
  have hRt : R.transpose = R := Matrix.isHermitian_iff_isSymm.mp hR.isHermitian
  have he : x ⬝ᵥ ((R * R.transpose) *ᵥ x) = (R *ᵥ x) ⬝ᵥ (R *ᵥ x) := by
    calc
      _ = x ⬝ᵥ (R.transpose *ᵥ (R *ᵥ x)) := by rw [hRt, mulVec_mulVec]
      _ = _ := by rw [dotProduct_mulVec, vecMul_transpose]
  rw [smul_mulVec, dotProduct_smul, he]
  congr 1
  change (R *ᵥ x) ⬝ᵥ (R *ᵥ x) = ‖Matrix.toEuclideanLin R (WithLp.toLp 2 x)‖ ^ 2
  simp only [PiLp.norm_sq_eq_of_L2, Real.norm_eq_abs, sq_abs]
  change (∑ i, (R *ᵥ x) i * (R *ᵥ x) i) = ∑ i, (R *ᵥ x) i ^ 2
  simp only [pow_two]

theorem coefficientCovariance_lower_of_width {N : ℕ} (R : Matrix (Fin N) (Fin N) ℝ)
    (hR : R.PosDef) {c a : ℝ} (hc : 0 < c) (ha : 0 ≤ a)
    (hwidth : ∀ x : Euclidean N, (a * Real.sqrt c) * ‖x‖ ≤ ‖positiveMatrixShape R hR x‖)
    (x : Fin N → ℝ) :
    a ^ 2 * (∑ i, x i ^ 2) ≤ x ⬝ᵥ ((c⁻¹ • (R * R.transpose)) *ᵥ x) := by
  rw [coefficientCovariance_energy]
  have hs := pow_le_pow_left₀
    (show 0 ≤ (a * Real.sqrt c) * ‖(WithLp.toLp 2 x : Euclidean N)‖ by positivity)
    (hwidth (WithLp.toLp 2 x)) 2
  have hn : ‖WithLp.toLp 2 x‖ ^ 2 = ∑ i, x i ^ 2 := by
    simp only [PiLp.norm_sq_eq_of_L2, Real.norm_eq_abs, sq_abs]
  rw [mul_pow, mul_pow, Real.sq_sqrt hc.le, hn] at hs
  rw [← div_eq_inv_mul, le_div_iff₀ hc]
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hs

theorem canonicalComputedShape_width (b : Basis (Fin d) ℤ (𝓞 K)) (n : ℕ)
    (R : Matrix (Fin (n * d)) (Fin (n * d)) ℝ) (hR : R.PosDef)
    {a : ℝ} (hwidth : a ≤ shapeMinimumStretch (canonicalComputedShape K b R hR))
    (x : Euclidean (n * d)) : a * ‖x‖ ≤ ‖positiveMatrixShape R hR x‖ := by
  rw [canonicalComputedShape, isometricTransportShape_minimumStretch] at hwidth
  exact (mul_le_mul_of_nonneg_right hwidth (norm_nonneg x)).trans
    (shapeMinimumStretch_mul_norm_le (positiveMatrixShape R hR) x)

/-- The paper's canonical width `2 r sqrt(d)` gives coefficient covariance at least `4 r² I`. -/
theorem canonicalComputedShape_sampling_margin (b : Basis (Fin d) ℤ (𝓞 K)) (n : ℕ)
    (R : RationalMatrixData (n * d))
    (hR : ((rationalMatrixOfData R).map (fun q : ℚ => (q : ℝ))).PosDef)
    {r : ℝ} (hr : 0 ≤ r)
    (hwidth : 2 * r * Real.sqrt (d : ℝ) ≤
      shapeMinimumStretch (canonicalComputedShape K b _ hR)) (x : Fin (n * d) → ℝ) :
    (4 * r ^ 2) * (∑ i, x i ^ 2) ≤
      x ⬝ᵥ (((rationalMatrixOfData (coefficientCovarianceRun (n * d) d R).value).map
        (fun q : ℚ => (q : ℝ))) *ᵥ x) := by
  rw [coefficientCovarianceRun_real]
  have h := coefficientCovariance_lower_of_width _ hR
    (by exact_mod_cast integralBasis_dimension_pos K b : (0 : ℝ) < d)
    (by positivity : 0 ≤ 2 * r) (canonicalComputedShape_width K b n _ hR hwidth) x
  convert h using 1
  ring

/-- The spectral hint-generator sampling width meets the finite sampler's logarithmic threshold. -/
theorem sampling_radius_log_budget {N : ℕ} (hN : 2 ≤ N) {ε C : ℝ}
    (hε : 0 < ε) (hεone : ε ≤ 1) (hC : 1 ≤ C) :
    4 * Real.log ((N : ℝ) / ε) ≤ 4 * (C * Real.sqrt (Real.log ((N : ℝ) / ε))) ^ 2 := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hl : 0 ≤ Real.log ((N : ℝ) / ε) := Real.log_nonneg ((le_div_iff₀ hε).mpr (by linarith))
  rw [mul_pow, Real.sq_sqrt hl]
  have hc : 1 ≤ C ^ 2 := by nlinarith
  nlinarith [mul_nonneg (sub_nonneg.mpr hc) hl]

/-- Instantiate the finite sampler with the accepted width from the hint-generator lemma. -/
theorem computedNumberFieldSampleLaw_error_of_width (b : Basis (Fin d) ℤ (𝓞 K))
    (hGram : ∀ i j, canonicalGram K b i j = if i = j then (d : ℝ) else 0)
    (n : ℕ) (hN : 2 ≤ n * d) (R : RationalMatrixData (n * d))
    (hR : ((rationalMatrixOfData R).map (fun q : ℚ => (q : ℝ))).PosDef)
    {r ε : ℝ} (hr : 0 ≤ r) (hε : 0 < ε) (hεone : ε ≤ 1)
    (hwidth : 2 * r * Real.sqrt (d : ℝ) ≤ shapeMinimumStretch (canonicalComputedShape K b _ hR))
    (hlog : 4 * Real.log ((n * d : ℕ) / ε) ≤ 4 * r ^ 2)
    (s : ℕ) (hbudget : (1 / 2 : ℝ) ^ s ≤ ε / 4) :
    discreteTotalVariation (computedNumberFieldSampleLaw K b n R s)
      (numberFieldEllipsoidalGaussian K b n (canonicalComputedShape K b _ hR) 0) ≤ ε / 2 :=
  computedNumberFieldSampleLaw_error K b hGram n hN R hR (by positivity)
    (canonicalComputedShape_sampling_margin K b n R hR hr hwidth) hε hεone hlog s hbudget

/-- Combine finite sampling and the existing Gaussian shape-stability theorem. The two half-budgets
are exactly the per-column error of the spectral hint generator. -/
theorem computedNumberFieldSampleLaw_traceAverage_error (b : Basis (Fin d) ℤ (𝓞 K))
    (hGram : ∀ i j, canonicalGram K b i j = if i = j then (d : ℝ) else 0)
    {n k : ℕ} (hN : 2 ≤ n * d) (X : Matrix (Fin k) (Fin n) (𝓞 K))
    (hX : Function.Surjective X.mulVec) (hk : 0 < k) {w : ℝ} (hw : 0 < w)
    (R : RationalMatrixData (n * d))
    (hR : ((rationalMatrixOfData R).map (fun q : ℚ => (q : ℝ))).PosDef)
    {r ε δ : ℝ} (hr : 0 ≤ r) (hε : 0 < ε) (hεone : ε ≤ 1) (hδ : 0 ≤ δ)
    (hwidth : 2 * r * Real.sqrt (d : ℝ) ≤ shapeMinimumStretch (canonicalComputedShape K b _ hR))
    (hlog : 4 * Real.log ((n * d : ℕ) / ε) ≤ 4 * r ^ 2)
    (herr : ‖(canonicalComputedShape K b _ hR).toContinuousLinearMap -
      (canonicalGramShapingShape K b X hX hk w hw).toContinuousLinearMap‖ ≤ δ)
    (hprecision : 3 * (‖(canonicalEuclideanMatrix K b X).toContinuousLinearMap‖ / w * δ) ≤
      gaussianTargetPrecision (n * d) (ε / 2))
    (s : ℕ) (hbudget : (1 / 2 : ℝ) ^ s ≤ ε / 4) :
    discreteTotalVariation (computedNumberFieldSampleLaw K b n R s)
      (numberFieldEllipsoidalGaussian K b n (canonicalGramShapingShape K b X hX hk w hw) 0) ≤ ε := by
  have hs := computedNumberFieldSampleLaw_error_of_width K b hGram n hN R hR
    hr hε hεone hwidth hlog s hbudget
  have hp := numberFieldEllipsoidalGaussian_shape_error K b
    (canonicalGramShapingShape K b X hX hk w hw) (canonicalComputedShape K b _ hR) 0
    hδ (by positivity : 0 < ε / 2) (by linarith : ε / 2 ≤ 1) herr
    (by simpa only [canonicalGramShapingShape_inverse_norm] using hprecision)
  have ht := discreteTotalVariation_triangle (computedNumberFieldSampleLaw K b n R s)
    (numberFieldEllipsoidalGaussian K b n (canonicalComputedShape K b _ hR) 0)
    (numberFieldEllipsoidalGaussian K b n (canonicalGramShapingShape K b X hX hk w hw) 0)
  linarith

/-- Operator approximation preserves the margin needed for accepted samples. -/
theorem shapeMinimumStretch_approximation {N : ℕ} [Nontrivial (Euclidean N)]
    (S T : Euclidean N ≃L[ℝ] Euclidean N) {a δ : ℝ} (ha : 0 < a)
    (herr : ‖T.toContinuousLinearMap - S.toContinuousLinearMap‖ ≤ δ)
    (hmargin : a + δ ≤ shapeMinimumStretch S) : a ≤ shapeMinimumStretch T := by
  apply (le_shapeMinimumStretch_iff T ha).mpr
  intro x
  have he := (T.toContinuousLinearMap - S.toContinuousLinearMap).le_opNorm x
  change ‖T x - S x‖ ≤ ‖T.toContinuousLinearMap - S.toContinuousLinearMap‖ * ‖x‖ at he
  have he' := he.trans (mul_le_mul_of_nonneg_right herr (norm_nonneg x))
  have hS := (mul_le_mul_of_nonneg_right hmargin (norm_nonneg x)).trans
    (shapeMinimumStretch_mul_norm_le S x)
  have ht : ‖S x‖ ≤ ‖T x‖ + ‖T x - S x‖ := by
    exact norm_le_norm_add_norm_sub (T x) (S x)
  nlinarith

/-- The stated `B ≥ 4 r sqrt(d)` window leaves the required factor-two sampling margin. -/
theorem canonicalComputedShape_width_of_paper_window (b : Basis (Fin d) ℤ (𝓞 K))
    {n k : ℕ} (hn : 0 < n) (hk : 0 < k) (X : Matrix (Fin k) (Fin n) (𝓞 K))
    (hX : Function.Surjective X.mulVec) {w r B V δ : ℝ} (hw : 0 < w) (hr : 0 < r)
    (hB : 4 * r * Real.sqrt (d : ℝ) ≤ B) (hwB : B * V ≤ w)
    (hnorm : ‖(canonicalEuclideanMatrix K b X).toContinuousLinearMap‖ ≤ V)
    (R : Matrix (Fin (n * d)) (Fin (n * d)) ℝ) (hR : R.PosDef)
    (herr : ‖(canonicalComputedShape K b R hR).toContinuousLinearMap -
      (canonicalGramShapingShape K b X hX hk w hw).toContinuousLinearMap‖ ≤ δ)
    (hδ : δ ≤ 2 * r * Real.sqrt (d : ℝ)) :
    2 * r * Real.sqrt (d : ℝ) ≤ shapeMinimumStretch (canonicalComputedShape K b R hR) := by
  have hd := integralBasis_dimension_pos K b
  let : NeZero (k * d) := ⟨(Nat.mul_pos hk hd).ne'⟩
  let : NeZero (n * d) := ⟨(Nat.mul_pos hn hd).ne'⟩
  have hdreal : (0 : ℝ) < d := by exact_mod_cast hd
  have hroot : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr hdreal
  have hop := surjective_operator_norm_pos (canonicalEuclideanMatrix K b X).toContinuousLinearMap
    (canonicalEuclideanMatrix_surjective K b X hX)
  have hBzero : 0 ≤ B := (by positivity : 0 ≤ 4 * r * Real.sqrt (d : ℝ)).trans hB
  have hS : 4 * r * Real.sqrt (d : ℝ) ≤
      shapeMinimumStretch (canonicalGramShapingShape K b X hX hk w hw) := by
    rw [canonicalGramShapingShape_minimumStretch]
    exact hB.trans ((le_div_iff₀ hop).mpr ((mul_le_mul_of_nonneg_left hnorm hBzero).trans hwB))
  apply shapeMinimumStretch_approximation _ _ (by positivity) herr
  nlinarith

end
end SISToKSIS


open GeometricGaussianLHL Matrix
namespace SISToKSIS
set_option backward.isDefEq.respectTransparency false

/-- Check every stored rational entry against a supplied bit cap.
The charge covers entry scans, bit-length comparisons and the finite traversal. -/
def rationalMatrixBitsCheck {N : ℕ} (A : RationalMatrixData N) (cap : ℕ) : Costed Bool :=
  ⟨decide (∀ i j, rationalMagnitudeBits (rationalMatrixOfData A i j) ≤ cap),
    N * N * (rationalMatrixMagnitudeBits (rationalMatrixOfData A) + cap + 5) + 1⟩

theorem rationalMatrixBitsCheck_value {N : ℕ} (A : RationalMatrixData N) (cap : ℕ) :
    (rationalMatrixBitsCheck A cap).value = true ↔
      ∀ i j, rationalMagnitudeBits (rationalMatrixOfData A i j) ≤ cap := by
  simp [rationalMatrixBitsCheck]

/-- Exact positivity check, stopping before elimination on an oversized or nonpositive pivot. -/
def boundedSchurPositiveRun (cap : ℕ) : (N : ℕ) → RationalMatrixData N → Costed Bool
  | 0, _ => Costed.charge 1 true
  | N + 1, A =>
    let bounds := rationalMatrixBitsCheck A cap
    if bounds.value then
      let pivot := Costed.charge (rationalMagnitudeBits (rationalMatrixOfData A 0 0) + 2)
        (decide (0 < rationalMatrixOfData A 0 0))
      if pivot.value then
        let tail := gaussianSchurTailRun A
        let rest := boundedSchurPositiveRun cap N tail.value
        ⟨rest.value, bounds.steps + pivot.steps + tail.steps + rest.steps + 3⟩
      else ⟨false, bounds.steps + pivot.steps + 2⟩
    else ⟨false, bounds.steps + 1⟩

theorem boundedSchurPositiveRun_value_succ (cap N : ℕ) (A : RationalMatrixData (N + 1)) :
    (boundedSchurPositiveRun cap (N + 1) A).value =
      if ∀ i j, rationalMagnitudeBits (rationalMatrixOfData A i j) ≤ cap then
        if 0 < rationalMatrixOfData A 0 0 then
          (boundedSchurPositiveRun cap N (gaussianSchurTailRun A).value).value else false
      else false := by
  by_cases hb : ∀ i j, rationalMagnitudeBits (rationalMatrixOfData A i j) ≤ cap <;>
    by_cases hp : 0 < rationalMatrixOfData A 0 0 <;>
      simp [boundedSchurPositiveRun, rationalMatrixBitsCheck, Costed.charge, hb, hp]

theorem boundedSchurPositiveRun_pivots (cap N : ℕ) (A : RationalMatrixData N)
    (h : (boundedSchurPositiveRun cap N A).value = true) :
    ∀ i, 0 < (gaussianSchurFactor N (rationalMatrixOfData A)).2 i := by
  induction N with
  | zero => exact fun i => Fin.elim0 i
  | succ N ih =>
    rw [boundedSchurPositiveRun_value_succ] at h
    split_ifs at h with hbits hp
    · have ht := ih (gaussianSchurTailRun A).value h
      rw [gaussianSchurTailRun_value] at ht
      exact fun i => Fin.cases hp ht i

theorem gaussianSchurFactor_congruence_of_positive (N : ℕ)
    (A : Matrix (Fin N) (Fin N) ℝ) (hA : ∀ i j, A i j = A j i)
    (hp : ∀ i, 0 < (gaussianSchurFactor N A).2 i) :
    (gaussianSchurFactor N A).1 * A * (gaussianSchurFactor N A).1.transpose =
      diagonal (gaussianSchurFactor N A).2 := by
  induction N with
  | zero => ext i; exact Fin.elim0 i
  | succ N ih =>
    exact gaussianSchurLift_congruence A hA (hp 0).ne' _ _
      (ih (gaussianSchurTail A) (gaussianSchurTail_symmetric A hA) (fun i => hp i.succ))

theorem gaussianSchurFactor_posDef_of_positive (N : ℕ)
    (A : Matrix (Fin N) (Fin N) ℝ) (hA : ∀ i j, A i j = A j i)
    (hp : ∀ i, 0 < (gaussianSchurFactor N A).2 i) : A.PosDef := by
  have hu : IsUnit (gaussianSchurFactor N A).1 :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (by rw [gaussianSchurFactor_det]; exact isUnit_one)
  apply hu.posDef_star_right_conjugate_iff.mp
  change ((gaussianSchurFactor N A).1 * A * (gaussianSchurFactor N A).1.conjTranspose).PosDef
  rw [Matrix.conjTranspose_eq_transpose_of_trivial, gaussianSchurFactor_congruence_of_positive N A hA hp]
  exact Matrix.PosDef.diagonal hp

theorem boundedSchurPositiveRun_sound (cap N : ℕ) (A : RationalMatrixData N)
    (hA : ∀ i j, rationalMatrixOfData A i j = rationalMatrixOfData A j i)
    (h : (boundedSchurPositiveRun cap N A).value = true) :
    ((rationalMatrixOfData A).map (fun q : ℚ => (q : ℝ))).PosDef := by
  have hp := boundedSchurPositiveRun_pivots cap N A h
  apply gaussianSchurFactor_posDef_of_positive
  · intro i j
    change (rationalMatrixOfData A i j : ℝ) = (rationalMatrixOfData A j i : ℝ)
    exact_mod_cast hA i j
  · intro i
    have hmap := congrFun (congrArg Prod.snd
      (gaussianSchurFactor_map (Rat.castHom ℝ) N (rationalMatrixOfData A))) i
    change (gaussianSchurFactor N ((rationalMatrixOfData A).map (fun q : ℚ => (q : ℝ)))).2 i =
      ((gaussianSchurFactor N (rationalMatrixOfData A)).2 i : ℝ) at hmap
    rw [hmap]
    exact_mod_cast hp i

theorem boundedSchurPositiveRun_complete_of_inverse_submatrix {N L cap : ℕ}
    (Q : Matrix (Fin N) (Fin N) ℚ) (hQ : ∀ i j, rationalMagnitudeBits (Q i j) ≤ L)
    (hcap : rationalInverseBitsBudget N L ≤ cap)
    (M : ℕ) (A : RationalMatrixData M)
    (hA : ((rationalMatrixOfData A).map (fun q : ℚ => (q : ℝ))).PosDef)
    (e : Fin M → Fin N) (he : (rationalMatrixOfData A)⁻¹ = Q.submatrix e e) (hM : M ≤ N) :
    (boundedSchurPositiveRun cap M A).value = true := by
  induction M with
  | zero => rfl
  | succ M ih =>
    have hb : ∀ i j, rationalMagnitudeBits (rationalMatrixOfData A i j) ≤ cap := fun i j =>
      (rationalMatrix_bits_of_inverse_submatrix _ (rationalPosDef_isUnitDet _ hA)
        Q hQ e he hM i j).trans hcap
    have hp : 0 < rationalMatrixOfData A 0 0 := by
      have hp := hA.diag_pos (i := 0)
      change (0 : ℝ) < (rationalMatrixOfData A 0 0 : ℝ) at hp
      exact_mod_cast hp
    rw [boundedSchurPositiveRun_value_succ, ite_eq_left hb, ite_eq_left hp]
    apply ih (gaussianSchurTailRun A).value
    · rw [gaussianSchurTailRun_value]
      exact rationalSchurTail_posDef _ hA
    · rw [gaussianSchurTailRun_value]
      exact gaussianSchurTail_inverse_submatrix _ hA Q e he
    · omega

def boundedSchurCap (N L : ℕ) : ℕ := rationalInverseBitsBudget N (rationalInverseBitsBudget N L)

theorem boundedSchurPositiveRun_complete {N L : ℕ} (A : RationalMatrixData N)
    (hA : ((rationalMatrixOfData A).map (fun q : ℚ => (q : ℝ))).PosDef)
    (hbits : ∀ i j, rationalMagnitudeBits (rationalMatrixOfData A i j) ≤ L) :
    (boundedSchurPositiveRun (boundedSchurCap N L) N A).value = true :=
  boundedSchurPositiveRun_complete_of_inverse_submatrix (rationalMatrixOfData A)⁻¹
    (rationalMatrix_inverse_bits _ hbits) le_rfl N A hA id (by simp) le_rfl

theorem gaussianSchurTailRun_bits {N L : ℕ} (A : RationalMatrixData (N + 1))
    (hA : ∀ i j, rationalMagnitudeBits (rationalMatrixOfData A i j) ≤ L) (i j : Fin N) :
    rationalMagnitudeBits (rationalMatrixOfData (gaussianSchurTailRun A).value i j) ≤ 200 * (L + 1) := by
  rw [gaussianSchurTailRun_value]
  let C := rationalMatrixOfData A
  have hp := rational_mul_bits_le (C i.succ 0) (C 0 j.succ) L (hA _ _) (hA _ _)
  have hq := rational_div_bits_le (C i.succ 0 * C 0 j.succ) (C 0 0) (6 * L + 3)
    hp ((hA _ _).trans (by omega))
  have hd := rational_sub_bits_le (C i.succ j.succ) ((C i.succ 0 * C 0 j.succ) / C 0 0)
    (6 * (6 * L + 3) + 3) ((hA _ _).trans (by omega)) hq
  exact hd.trans (by omega)

def boundedSchurStageCost (N B cap : ℕ) : ℕ :=
  N * N * (N * N * B + cap + 5) + 1 + (cap + 2) + gaussianSchurTailCost N cap + 3

theorem rationalMatrixBitsCheck_steps {N B cap : ℕ} (A : RationalMatrixData N)
    (hbits : ∀ i j, rationalMagnitudeBits (rationalMatrixOfData A i j) ≤ B) :
    (rationalMatrixBitsCheck A cap).steps ≤ N * N * (N * N * B + cap + 5) + 1 := by
  have h := rationalMatrix_bits_le_entries _ hbits
  change N * N * (rationalMatrixMagnitudeBits (rationalMatrixOfData A) + cap + 5) + 1 ≤ _
  gcongr

/-- The cap enforces a polynomial cost even when the input is singular or indefinite. -/
theorem boundedSchurPositiveRun_steps {D B cap : ℕ} (hB : 200 * (cap + 1) ≤ B)
    (N : ℕ) (A : RationalMatrixData N) (hN : N ≤ D)
    (hbits : ∀ i j, rationalMagnitudeBits (rationalMatrixOfData A i j) ≤ B) :
    (boundedSchurPositiveRun cap N A).steps ≤ N * boundedSchurStageCost D B cap + 1 := by
  induction N with
  | zero => simp [boundedSchurPositiveRun, Costed.charge]
  | succ N ih =>
    have hcheck := (rationalMatrixBitsCheck_steps A hbits).trans (show
      (N + 1) * (N + 1) * ((N + 1) * (N + 1) * B + cap + 5) + 1 ≤
        D * D * (D * D * B + cap + 5) + 1 by gcongr)
    have htailcost := gaussianSchurTailCost_mono (show N ≤ D by omega) (le_refl cap)
    by_cases hb : ∀ i j, rationalMagnitudeBits (rationalMatrixOfData A i j) ≤ cap
    · have hbtrue : (rationalMatrixBitsCheck A cap).value = true := (rationalMatrixBitsCheck_value A cap).mpr hb
      have hpbits := hb 0 0
      have ht := (gaussianSchurTailRun_steps_le A cap hb).trans htailcost
      have htbits := fun i j => (gaussianSchurTailRun_bits A hb i j).trans hB
      have hi := ih (gaussianSchurTailRun A).value (by omega) htbits
      by_cases hp : 0 < rationalMatrixOfData A 0 0
      · simp only [boundedSchurPositiveRun, hbtrue, ↓reduceIte, Costed.charge,
          hp, decide_true]
        unfold boundedSchurStageCost at *
        nlinarith
      · simp only [boundedSchurPositiveRun, hbtrue, ↓reduceIte, Costed.charge,
          hp, decide_false, Bool.false_eq_true]
        unfold boundedSchurStageCost at *
        nlinarith
    · have hbfalse : (rationalMatrixBitsCheck A cap).value = false := by
        simp [rationalMatrixBitsCheck, hb]
      simp only [boundedSchurPositiveRun, hbfalse, Bool.false_eq_true, ↓reduceIte]
      unfold boundedSchurStageCost at *
      nlinarith


theorem boundedSchurCap_mono {N M L B : ℕ} (hN : N ≤ M) (hL : L ≤ B) :
    boundedSchurCap N L ≤ boundedSchurCap M B :=
  rationalInverseBitsBudget_mono hN (rationalInverseBitsBudget_mono hN hL)

theorem boundedSchurCap_polynomial : PolynomialCostBound (fun t => boundedSchurCap t t) := by
  let x : Polynomial ℕ := Polynomial.X
  let detP (n l : Polynomial ℕ) := n * n + n * l + 2 * (n * (n * n * l)) + 3
  let invP (n l : Polynomial ℕ) := 6 * detP n (l + 3) + 3
  refine ⟨invP x (invP x x), ?_⟩
  intro t
  apply le_of_eq
  simp [boundedSchurCap, rationalInverseBitsBudget, rationalDetBitsBudget, x, detP, invP]

def boundedSchurPositiveBudget (N L cap : ℕ) : ℕ :=
  N * boundedSchurStageCost N (L + 200 * (cap + 1)) cap + 1

theorem boundedSchurPositiveBudget_mono {N M L B cap top : ℕ}
    (hN : N ≤ M) (hL : L ≤ B) (hc : cap ≤ top) :
    boundedSchurPositiveBudget N L cap ≤ boundedSchurPositiveBudget M B top := by
  unfold boundedSchurPositiveBudget boundedSchurStageCost gaussianSchurTailCost rationalRectTraversalBudget
  gcongr

theorem boundedSchurPositiveBudget_polynomial :
    PolynomialCostBound (fun t => boundedSchurPositiveBudget t t t) := by
  let x : Polynomial ℕ := Polynomial.X
  let b := x + 200 * (x + 1)
  let tail := x * (x * ((3 * (2 * (40 * (x + 1)) + 1) ^ 3 + 4) + 3) + 4) + 1
  refine ⟨x * (x * x * (x * x * b + x + 5) + 1 + (x + 2) + tail + 3) + 1, ?_⟩
  intro t
  apply le_of_eq
  simp [boundedSchurPositiveBudget, boundedSchurStageCost, gaussianSchurTailCost,
    rationalRectTraversalBudget, x, b, tail]

theorem boundedSchurPositiveRun_budget {N L : ℕ} (A : RationalMatrixData N)
    (hbits : ∀ i j, rationalMagnitudeBits (rationalMatrixOfData A i j) ≤ L) (cap : ℕ) :
    (boundedSchurPositiveRun cap N A).steps ≤ boundedSchurPositiveBudget N L cap :=
  boundedSchurPositiveRun_steps (by omega) N A le_rfl
    (fun i j => (hbits i j).trans (by omega))

theorem boundedSchurPositiveRun_polynomial : ∃ C k : ℕ,
    ∀ (N cap : ℕ) (A : RationalMatrixData N),
      (boundedSchurPositiveRun cap N A).steps ≤
        C * (N + rationalMatrixMagnitudeBits (rationalMatrixOfData A) + cap + 1) ^ k := by
  obtain ⟨C, k, h⟩ := boundedSchurPositiveBudget_polynomial.exists_mul_pow_bound
  refine ⟨C, k, fun N cap A => ?_⟩
  exact (boundedSchurPositiveRun_budget A (rationalMatrix_entry_bits_le _) cap).trans
    ((boundedSchurPositiveBudget_mono (by omega) (by omega) (by omega)).trans
      (h (N + rationalMatrixMagnitudeBits (rationalMatrixOfData A) + cap)))

/-- The complete cap still costs only a polynomial in the original matrix data. -/
theorem boundedSchurPositiveRun_complete_polynomial : ∃ C k : ℕ,
    ∀ (N : ℕ) (A : RationalMatrixData N),
      (boundedSchurPositiveRun (boundedSchurCap N (rationalMatrixMagnitudeBits (rationalMatrixOfData A))) N A).steps ≤
        C * (N + rationalMatrixMagnitudeBits (rationalMatrixOfData A) + 1) ^ k := by
  have hp : PolynomialCostBound (fun t => boundedSchurPositiveBudget t t (boundedSchurCap t t)) := by
    have hf := polynomialCostBound_comp_mono boundedSchurPositiveBudget_polynomial
      ((PolynomialCostBound.id.add PolynomialCostBound.id).add boundedSchurCap_polynomial)
      (fun _ _ h => boundedSchurPositiveBudget_mono h h h)
    exact hf.mono (fun t => boundedSchurPositiveBudget_mono (by omega) (by omega) (by omega))
  obtain ⟨C, k, h⟩ := hp.exists_mul_pow_bound
  refine ⟨C, k, fun N A => ?_⟩
  exact (boundedSchurPositiveRun_budget A (rationalMatrix_entry_bits_le _) _).trans
    ((boundedSchurPositiveBudget_mono (by omega) (by omega)
      (boundedSchurCap_mono (by omega) (by omega))).trans
        (h (N + rationalMatrixMagnitudeBits (rationalMatrixOfData A))))

/-- Evaluate the determinant bit bound by charged natural arithmetic; no determinant is evaluated. -/
def schurDetBitsRun (N L : ℕ) : Costed ℕ :=
  let nn := costedNatMul N N
  let nl := costedNatMul N L
  let nnl := costedNatMul nn.value L
  let nnnl := costedNatMul N nnl.value
  let twice := costedNatMul 2 nnnl.value
  let sum := costedNatAdd nn.value nl.value
  let total := costedNatAdd sum.value twice.value
  let output := costedNatAdd total.value 3
  ⟨output.value, nn.steps + nl.steps + nnl.steps + nnnl.steps + twice.steps + sum.steps + total.steps + output.steps + 8⟩

theorem schurDetBitsRun_value (N L : ℕ) : (schurDetBitsRun N L).value = rationalDetBitsBudget N L := rfl

def schurDetBitsOperand (N L : ℕ) : ℕ := N + L + N * N * L + rationalDetBitsBudget N L + 3
def schurDetBitsCost (N L : ℕ) : ℕ := 8 * (2 * schurDetBitsOperand N L + 1) ^ 2 + 8

theorem schurDetBitsRun_steps (N L : ℕ) : (schurDetBitsRun N L).steps ≤ schurDetBitsCost N L := by
  let T := schurDetBitsOperand N L
  have hm (a b : ℕ) (ha : a ≤ T) (hb : b ≤ T) := costedNatMul_steps_le a b T ha hb
  have ha (a b : ℕ) (ha : a ≤ T) (hb : b ≤ T) := costedNatAdd_steps_le a b T ha hb
  have h1 := hm N N (by dsimp [T, schurDetBitsOperand]; omega) (by dsimp [T, schurDetBitsOperand]; omega)
  have h2 := hm N L (by dsimp [T, schurDetBitsOperand]; omega) (by dsimp [T, schurDetBitsOperand]; omega)
  have h3 := hm (N * N) L (by dsimp [T, schurDetBitsOperand, rationalDetBitsBudget]; omega)
    (by dsimp [T, schurDetBitsOperand]; omega)
  have h4 := hm N (N * N * L) (by dsimp [T, schurDetBitsOperand]; omega)
    (by dsimp [T, schurDetBitsOperand]; omega)
  have h5 := hm 2 (N * (N * N * L)) (by dsimp [T, schurDetBitsOperand]; omega)
    (by dsimp [T, schurDetBitsOperand, rationalDetBitsBudget]; omega)
  have h6 := ha (N * N) (N * L) (by dsimp [T, schurDetBitsOperand, rationalDetBitsBudget]; omega)
    (by dsimp [T, schurDetBitsOperand, rationalDetBitsBudget]; omega)
  have h7 := ha (N * N + N * L) (2 * (N * (N * N * L)))
    (by dsimp [T, schurDetBitsOperand, rationalDetBitsBudget]; omega)
    (by dsimp [T, schurDetBitsOperand, rationalDetBitsBudget]; omega)
  have h8 := ha (N * N + N * L + 2 * (N * (N * N * L))) 3
    (by dsimp [T, schurDetBitsOperand, rationalDetBitsBudget]; omega)
    (by dsimp [T, schurDetBitsOperand]; omega)
  change (costedNatMul N N).steps + (costedNatMul N L).steps + (costedNatMul (N * N) L).steps +
    (costedNatMul N (N * N * L)).steps + (costedNatMul 2 (N * (N * N * L))).steps +
    (costedNatAdd (N * N) (N * L)).steps + (costedNatAdd (N * N + N * L) (2 * (N * (N * N * L)))).steps +
    (costedNatAdd (N * N + N * L + 2 * (N * (N * N * L))) 3).steps + 8 ≤ 8 * (2 * T + 1) ^ 2 + 8
  omega

def schurInverseBitsRun (N L : ℕ) : Costed ℕ :=
  let shifted := costedNatAdd L 3
  let det := schurDetBitsRun N shifted.value
  let scaled := costedNatMul 6 det.value
  let output := costedNatAdd scaled.value 3
  ⟨output.value, shifted.steps + det.steps + scaled.steps + output.steps + 4⟩

theorem schurInverseBitsRun_value (N L : ℕ) :
    (schurInverseBitsRun N L).value = rationalInverseBitsBudget N L := rfl

def schurInverseBitsOperand (N L : ℕ) : ℕ := N + L + 6 * rationalDetBitsBudget N (L + 3) + 6
def schurInverseBitsCost (N L : ℕ) : ℕ :=
  schurDetBitsCost N (L + 3) + 3 * (2 * schurInverseBitsOperand N L + 1) ^ 2 + 4

theorem schurInverseBitsRun_steps (N L : ℕ) :
    (schurInverseBitsRun N L).steps ≤ schurInverseBitsCost N L := by
  let T := schurInverseBitsOperand N L
  have h1 := costedNatAdd_steps_le L 3 T (by dsimp [T, schurInverseBitsOperand]; omega)
    (by dsimp [T, schurInverseBitsOperand]; omega)
  have h2 := schurDetBitsRun_steps N (L + 3)
  have h3 := costedNatMul_steps_le 6 (rationalDetBitsBudget N (L + 3)) T
    (by dsimp [T, schurInverseBitsOperand]; omega) (by dsimp [T, schurInverseBitsOperand]; omega)
  have h4 := costedNatAdd_steps_le (6 * rationalDetBitsBudget N (L + 3)) 3 T
    (by dsimp [T, schurInverseBitsOperand]; omega) (by dsimp [T, schurInverseBitsOperand]; omega)
  change (costedNatAdd L 3).steps + (schurDetBitsRun N (L + 3)).steps +
    (costedNatMul 6 (rationalDetBitsBudget N (L + 3))).steps +
    (costedNatAdd (6 * rationalDetBitsBudget N (L + 3)) 3).steps + 4 ≤
      schurDetBitsCost N (L + 3) + 3 * (2 * T + 1) ^ 2 + 4
  omega

def boundedSchurCapRun (N L : ℕ) : Costed ℕ :=
  (schurInverseBitsRun N L).bind (schurInverseBitsRun N)

theorem boundedSchurCapRun_value (N L : ℕ) : (boundedSchurCapRun N L).value = boundedSchurCap N L := rfl

def boundedSchurCapCost (N L : ℕ) : ℕ :=
  schurInverseBitsCost N L + schurInverseBitsCost N (rationalInverseBitsBudget N L)

theorem boundedSchurCapRun_steps (N L : ℕ) :
    (boundedSchurCapRun N L).steps ≤ boundedSchurCapCost N L :=
  Nat.add_le_add (schurInverseBitsRun_steps N L)
    (schurInverseBitsRun_steps N (rationalInverseBitsBudget N L))

theorem schurDetBitsCost_mono {N M L B : ℕ} (hN : N ≤ M) (hL : L ≤ B) :
    schurDetBitsCost N L ≤ schurDetBitsCost M B := by
  unfold schurDetBitsCost schurDetBitsOperand rationalDetBitsBudget
  gcongr

theorem schurInverseBitsCost_mono {N M L B : ℕ} (hN : N ≤ M) (hL : L ≤ B) :
    schurInverseBitsCost N L ≤ schurInverseBitsCost M B := by
  unfold schurInverseBitsCost schurInverseBitsOperand schurDetBitsCost schurDetBitsOperand rationalDetBitsBudget
  gcongr

theorem boundedSchurCapCost_mono {N M L B : ℕ} (hN : N ≤ M) (hL : L ≤ B) :
    boundedSchurCapCost N L ≤ boundedSchurCapCost M B :=
  Nat.add_le_add (schurInverseBitsCost_mono hN hL)
    (schurInverseBitsCost_mono hN (rationalInverseBitsBudget_mono hN hL))

theorem boundedSchurCapCost_polynomial : PolynomialCostBound (fun t => boundedSchurCapCost t t) := by
  let x : Polynomial ℕ := Polynomial.X
  let detP (n l : Polynomial ℕ) := n * n + n * l + 2 * (n * (n * n * l)) + 3
  let invP (n l : Polynomial ℕ) := 6 * detP n (l + 3) + 3
  let detCost (n l : Polynomial ℕ) := 8 * (2 * (n + l + n * n * l + detP n l + 3) + 1) ^ 2 + 8
  let invCost (n l : Polynomial ℕ) := detCost n (l + 3) +
    3 * (2 * (n + l + 6 * detP n (l + 3) + 6) + 1) ^ 2 + 4
  refine ⟨invCost x x + invCost x (invP x x), ?_⟩
  intro t
  apply le_of_eq
  simp [boundedSchurCapCost, schurInverseBitsCost, schurInverseBitsOperand, schurDetBitsCost,
    schurDetBitsOperand, rationalInverseBitsBudget, rationalDetBitsBudget, x, detP, invP, detCost, invCost]

/-- Scan the stored data, compute the proved sufficient cap, and check positivity. -/
def rationalPositiveCheckRun (N : ℕ) (A : RationalMatrixData N) : Costed Bool :=
  let bits := Costed.charge (N * N * (rationalMatrixMagnitudeBits (rationalMatrixOfData A) + 5) + 1)
    (rationalMatrixMagnitudeBits (rationalMatrixOfData A))
  let cap := boundedSchurCapRun N bits.value
  let checked := boundedSchurPositiveRun cap.value N A
  ⟨checked.value, bits.steps + cap.steps + checked.steps + 3⟩

theorem rationalPositiveCheckRun_value (N : ℕ) (A : RationalMatrixData N) :
    (rationalPositiveCheckRun N A).value =
      (boundedSchurPositiveRun (boundedSchurCap N (rationalMatrixMagnitudeBits (rationalMatrixOfData A))) N A).value := rfl

theorem rationalPositiveCheckRun_sound (N : ℕ) (A : RationalMatrixData N)
    (hA : ∀ i j, rationalMatrixOfData A i j = rationalMatrixOfData A j i)
    (h : (rationalPositiveCheckRun N A).value = true) :
    ((rationalMatrixOfData A).map (fun q : ℚ => (q : ℝ))).PosDef :=
  boundedSchurPositiveRun_sound _ N A hA h

theorem rationalPositiveCheckRun_complete (N : ℕ) (A : RationalMatrixData N)
    (hA : ((rationalMatrixOfData A).map (fun q : ℚ => (q : ℝ))).PosDef) :
    (rationalPositiveCheckRun N A).value = true :=
  boundedSchurPositiveRun_complete A hA (rationalMatrix_entry_bits_le _)

def rationalPositiveCheckBudget (N L : ℕ) : ℕ :=
  N * N * (L + 5) + 1 + boundedSchurCapCost N L +
    boundedSchurPositiveBudget N L (boundedSchurCap N L) + 3

theorem rationalPositiveCheckBudget_mono {N M L B : ℕ} (hN : N ≤ M) (hL : L ≤ B) :
    rationalPositiveCheckBudget N L ≤ rationalPositiveCheckBudget M B := by
  have hcap := boundedSchurCapCost_mono hN hL
  have hcheck := boundedSchurPositiveBudget_mono hN hL (boundedSchurCap_mono hN hL)
  have hb : N * N * (L + 5) ≤ M * M * (B + 5) := by gcongr
  unfold rationalPositiveCheckBudget
  omega

theorem rationalPositiveCheckRun_steps (N : ℕ) (A : RationalMatrixData N) :
    (rationalPositiveCheckRun N A).steps ≤
      rationalPositiveCheckBudget N (rationalMatrixMagnitudeBits (rationalMatrixOfData A)) := by
  have hcap := boundedSchurCapRun_steps N (rationalMatrixMagnitudeBits (rationalMatrixOfData A))
  have hcheck := boundedSchurPositiveRun_budget A (rationalMatrix_entry_bits_le _)
    (boundedSchurCap N (rationalMatrixMagnitudeBits (rationalMatrixOfData A)))
  change N * N * (rationalMatrixMagnitudeBits (rationalMatrixOfData A) + 5) + 1 +
    (boundedSchurCapRun N (rationalMatrixMagnitudeBits (rationalMatrixOfData A))).steps +
    (boundedSchurPositiveRun (boundedSchurCap N (rationalMatrixMagnitudeBits (rationalMatrixOfData A))) N A).steps + 3 ≤ _
  unfold rationalPositiveCheckBudget
  omega

theorem rationalPositiveCheckBudget_polynomial : PolynomialCostBound (fun t => rationalPositiveCheckBudget t t) := by
  have hp : PolynomialCostBound (fun t => boundedSchurPositiveBudget t t (boundedSchurCap t t)) := by
    have hf := polynomialCostBound_comp_mono boundedSchurPositiveBudget_polynomial
      ((PolynomialCostBound.id.add PolynomialCostBound.id).add boundedSchurCap_polynomial)
      (fun _ _ h => boundedSchurPositiveBudget_mono h h h)
    exact hf.mono (fun t => boundedSchurPositiveBudget_mono (by omega) (by omega) (by omega))
  exact (((((PolynomialCostBound.id.mul PolynomialCostBound.id).mul
    (PolynomialCostBound.id.add (PolynomialCostBound.const 5))).add (PolynomialCostBound.const 1)).add
      boundedSchurCapCost_polynomial).add hp).add (PolynomialCostBound.const 3)

theorem rationalPositiveCheckRun_polynomial : ∃ C k : ℕ, ∀ (N : ℕ) (A : RationalMatrixData N),
    (rationalPositiveCheckRun N A).steps ≤
      C * (N + rationalMatrixMagnitudeBits (rationalMatrixOfData A) + 1) ^ k := by
  obtain ⟨C, k, h⟩ := rationalPositiveCheckBudget_polynomial.exists_mul_pow_bound
  refine ⟨C, k, fun N A => ?_⟩
  exact (rationalPositiveCheckRun_steps N A).trans
    ((rationalPositiveCheckBudget_mono (by omega) (by omega)).trans
      (h (N + rationalMatrixMagnitudeBits (rationalMatrixOfData A))))

/-- Full row rank is checked by exact bounded elimination of the rational row Gram matrix. -/
def rationalGramCheckRun {P N : ℕ} (Q : RationalRectData P N) : Costed Bool :=
  (costedRationalRowGram Q).bind (rationalPositiveCheckRun P)

theorem rationalGramCheckRun_iff {P N : ℕ} (Q : RationalRectData P N) :
    (rationalGramCheckRun Q).value = true ↔
      IsUnit (rationalRectMatrixOfData Q * (rationalRectMatrixOfData Q).transpose).det := by
  let G := (costedRationalRowGram Q).value
  have hG : rationalMatrixOfData G =
      rationalRectMatrixOfData Q * (rationalRectMatrixOfData Q).transpose := by
    dsimp only [G]
    rw [costedRationalRowGram_data]
    exact rationalRectMatrixOfData_data _
  constructor
  · intro h
    have hs : ∀ i j, rationalMatrixOfData G i j = rationalMatrixOfData G j i := by
      rw [hG]
      intro i j
      simp only [mul_apply, transpose_apply]
      apply Finset.sum_congr rfl
      intro a _
      ring
    have hp := rationalPositiveCheckRun_sound P G hs h
    rw [hG] at hp
    exact rationalPosDef_isUnitDet _ hp
  · intro h
    apply rationalPositiveCheckRun_complete P G
    rw [hG]
    exact rationalGram_real_posDef _ h

def rationalGramCheckBudget (P N L : ℕ) : ℕ :=
  rationalRowGramBudget P N L + rationalPositiveCheckBudget P (P * P * rationalDotOperandBudget N L)

theorem rationalGramCheckRun_steps {P N L : ℕ} (Q : RationalRectData P N)
    (hQ : ∀ i j, rationalMagnitudeBits (rationalRectMatrixOfData Q i j) ≤ L) :
    (rationalGramCheckRun Q).steps ≤ rationalGramCheckBudget P N L := by
  have hg := costedRationalRowGram_steps_le Q L hQ
  have hs := rationalMatrix_bits_le_entries _ (costedRationalRowGram_size Q L hQ)
  have hc := (rationalPositiveCheckRun_steps P (costedRationalRowGram Q).value).trans
    (rationalPositiveCheckBudget_mono le_rfl hs)
  exact Nat.add_le_add hg hc

theorem rationalGramCheckBudget_mono {P P' N N' L L' : ℕ}
    (hP : P ≤ P') (hN : N ≤ N') (hL : L ≤ L') :
    rationalGramCheckBudget P N L ≤ rationalGramCheckBudget P' N' L' := by
  have hg : rationalRowGramBudget P N L ≤ rationalRowGramBudget P' N' L' := by
    unfold rationalRowGramBudget rationalRectMulBudget rationalRectTraversalBudget rationalDotBudget rationalDotOperandBudget
    gcongr
  have hc := rationalPositiveCheckBudget_mono hP (show
    P * P * rationalDotOperandBudget N L ≤ P' * P' * rationalDotOperandBudget N' L' by
      unfold rationalDotOperandBudget; gcongr)
  exact Nat.add_le_add hg hc

theorem rationalGramCheckBudget_polynomial : PolynomialCostBound (fun t => rationalGramCheckBudget t t t) := by
  have hb : PolynomialCostBound (fun t => t * t * rationalDotOperandBudget t t) :=
    (PolynomialCostBound.id.mul PolynomialCostBound.id).mul
      (polyBound_rationalDotOperandBudget PolynomialCostBound.id PolynomialCostBound.id)
  have hc : PolynomialCostBound (fun t => rationalPositiveCheckBudget t (t * t * rationalDotOperandBudget t t)) := by
    have h := polynomialCostBound_comp_mono rationalPositiveCheckBudget_polynomial
      (PolynomialCostBound.id.add hb) (fun _ _ h => rationalPositiveCheckBudget_mono h h)
    exact h.mono (fun t => rationalPositiveCheckBudget_mono (by omega) (by omega))
  exact (polyBound_rationalRowGramBudget PolynomialCostBound.id PolynomialCostBound.id PolynomialCostBound.id).add hc

/-- Use the parent shaping algorithm on full-rank inputs and an identity fallback otherwise.
The fallback only affects matrices outside the good event of the reduction. -/
def guardedRationalShapeRun {P N : ℕ} (t : ℕ) (Q : RationalRectData P N) (w : ℚ) :
    Costed (RationalMatrixData N) :=
  let check := rationalGramCheckRun Q
  let shape := if check.value then costedRationalShapingApprox t Q w else costedRationalIdentity N
  ⟨shape.value, check.steps + shape.steps + 1⟩

theorem guardedRationalShapeRun_value_of_fullRank {P N : ℕ} (t : ℕ) (Q : RationalRectData P N) (w : ℚ)
    (hQ : IsUnit (rationalRectMatrixOfData Q * (rationalRectMatrixOfData Q).transpose).det) :
    (guardedRationalShapeRun t Q w).value = (costedRationalShapingApprox t Q w).value := by
  simp only [guardedRationalShapeRun, (rationalGramCheckRun_iff Q).mpr hQ, ↓reduceIte]

theorem guardedRationalShapeRun_value_of_rankFailure {P N : ℕ} (t : ℕ) (Q : RationalRectData P N) (w : ℚ)
    (hQ : ¬IsUnit (rationalRectMatrixOfData Q * (rationalRectMatrixOfData Q).transpose).det) :
    (guardedRationalShapeRun t Q w).value = (costedRationalIdentity N).value := by
  have h : (rationalGramCheckRun Q).value = false := Bool.eq_false_iff.mpr (mt (rationalGramCheckRun_iff Q).mp hQ)
  simp only [guardedRationalShapeRun, h, Bool.false_eq_true, ↓reduceIte]

theorem guardedRationalShapeRun_posDef {P N : ℕ} (hP : 0 < P) (t : ℕ)
    (Q : RationalRectData P N) (w : ℚ) (hw : w ≠ 0) :
    ((rationalMatrixOfData (guardedRationalShapeRun t Q w).value).map (fun q : ℚ => (q : ℝ))).PosDef := by
  by_cases hQ : IsUnit (rationalRectMatrixOfData Q * (rationalRectMatrixOfData Q).transpose).det
  · rw [guardedRationalShapeRun_value_of_fullRank t Q w hQ]
    exact costedRationalShapingApprox_posDef t Q w hP hQ hw
  · rw [guardedRationalShapeRun_value_of_rankFailure t Q w hQ, costedRationalIdentity_data]
    change ((rationalRectMatrixOfData (rationalRectMatrixData (1 : Matrix (Fin N) (Fin N) ℚ))).map _).PosDef
    rw [rationalRectMatrixOfData_data]
    have he : (1 : Matrix (Fin N) (Fin N) ℚ).map (fun q : ℚ => (q : ℝ)) = 1 := by
      ext i j
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
    rw [he]
    exact Matrix.PosDef.one

def guardedRationalShapeBudget (P N L t : ℕ) : ℕ :=
  rationalGramCheckBudget P N L + rationalShapingBudget P N L t +
    rationalRectTraversalBudget N N (N + 2) + 1

theorem guardedRationalShapeRun_steps {P N L : ℕ} (hP : 0 < P) (t : ℕ)
    (Q : RationalRectData P N) (w : ℚ) (hw : w ≠ 0)
    (hQ : ∀ i j, rationalMagnitudeBits (rationalRectMatrixOfData Q i j) ≤ L)
    (hwbits : rationalMagnitudeBits w ≤ L) :
    (guardedRationalShapeRun t Q w).steps ≤ guardedRationalShapeBudget P N L t := by
  have hc := rationalGramCheckRun_steps Q hQ
  have hi := costedRationalIdentity_steps_le N
  by_cases hg : (rationalGramCheckRun Q).value = true
  · have hs := costedRationalShapingApprox_steps_le t Q w L hQ hwbits hP
      ((rationalGramCheckRun_iff Q).mp hg) hw
    simp only [guardedRationalShapeRun, hg, ↓reduceIte]
    unfold guardedRationalShapeBudget
    omega
  · have hf : (rationalGramCheckRun Q).value = false := Bool.eq_false_iff.mpr hg
    simp only [guardedRationalShapeRun, hf, Bool.false_eq_true, ↓reduceIte]
    unfold guardedRationalShapeBudget
    omega

theorem guardedRationalShapeRun_bits {P N L : ℕ} (hP : 0 < P) (t : ℕ)
    (Q : RationalRectData P N) (w : ℚ) (hw : w ≠ 0)
    (hQ : ∀ i j, rationalMagnitudeBits (rationalRectMatrixOfData Q i j) ≤ L)
    (hwbits : rationalMagnitudeBits w ≤ L) (i j : Fin N) :
    rationalMagnitudeBits (rationalMatrixOfData (guardedRationalShapeRun t Q w).value i j) ≤
      guardedRationalShapeBudget P N L t + 3 := by
  by_cases hg : IsUnit (rationalRectMatrixOfData Q * (rationalRectMatrixOfData Q).transpose).det
  · rw [guardedRationalShapeRun_value_of_fullRank t Q w hg]
    exact ((rationalMatrixEntryBits_le_encoded _ i j).trans
      ((costedRationalShapingApprox_length_le_steps t Q w).trans
        (costedRationalShapingApprox_steps_le t Q w L hQ hwbits hP hg hw))).trans
      (by unfold guardedRationalShapeBudget; omega)
  · rw [guardedRationalShapeRun_value_of_rankFailure t Q w hg]
    exact (costedRationalIdentity_size N i j).trans (by omega)

theorem guardedRationalShapeBudget_mono {P P' N N' L L' t t' : ℕ}
    (hP : P ≤ P') (hN : N ≤ N') (hL : L ≤ L') (ht : t ≤ t') :
    guardedRationalShapeBudget P N L t ≤ guardedRationalShapeBudget P' N' L' t' := by
  have hc := rationalGramCheckBudget_mono hP hN hL
  have hs := rationalShapingBudget_mono hP hN hL ht
  have hi : rationalRectTraversalBudget N N (N + 2) ≤ rationalRectTraversalBudget N' N' (N' + 2) := by
    unfold rationalRectTraversalBudget
    gcongr
  unfold guardedRationalShapeBudget
  omega

theorem guardedRationalShapeBudget_polynomial :
    PolynomialCostBound (fun t => guardedRationalShapeBudget t t t t) :=
  ((rationalGramCheckBudget_polynomial.add (polyBound_rationalShapingBudget PolynomialCostBound.id
    PolynomialCostBound.id PolynomialCostBound.id PolynomialCostBound.id)).add
      (polyBound_rationalRectTraversalBudget PolynomialCostBound.id PolynomialCostBound.id
        (PolynomialCostBound.id.add (PolynomialCostBound.const 2)))).add (PolynomialCostBound.const 1)

theorem guardedRationalShapeRun_polynomial : ∃ C e : ℕ, ∀ (P N : ℕ), 0 < P →
    ∀ (Q : RationalRectData P N) (w : ℚ), w ≠ 0 → ∀ t : ℕ,
      (guardedRationalShapeRun t Q w).steps ≤
        C * (P + N + rationalRectMagnitudeBits Q + rationalMagnitudeBits w + t + 1) ^ e := by
  obtain ⟨C, e, h⟩ := guardedRationalShapeBudget_polynomial.exists_mul_pow_bound
  refine ⟨C, e, fun P N hP Q w hw t => ?_⟩
  have hb : ∀ i j, rationalMagnitudeBits (rationalRectMatrixOfData Q i j) ≤
      rationalRectMagnitudeBits Q + rationalMagnitudeBits w := fun i j =>
    (rationalRect_entry_bits_le Q i j).trans (by omega)
  exact (guardedRationalShapeRun_steps hP t Q w hw hb (by omega)).trans
    ((guardedRationalShapeBudget_mono (by omega) (by omega) (by omega) (by omega)).trans
      (h (P + N + rationalRectMagnitudeBits Q + rationalMagnitudeBits w + t)))

abbrev GuardedHintColumnTape {P N : ℕ} (d t s : ℕ) (Q : RationalRectData P N) (w : ℚ) :=
  CoefficientShapeSampleTape N d (guardedRationalShapeRun t Q w).value s

/-- Actual finite column generation from stored rational coefficients and width. -/
def guardedHintColumnRun {P N : ℕ} (d t s : ℕ) (Q : RationalRectData P N) (w : ℚ)
    (tape : GuardedHintColumnTape d t s Q w) : Costed (Vector ℤ N) :=
  let shape := guardedRationalShapeRun t Q w
  let sample := coefficientShapeSampleRun N d shape.value s tape
  ⟨sample.value, shape.steps + sample.steps + 1⟩

theorem guardedHintColumnRun_value {P N : ℕ} (d t s : ℕ) (Q : RationalRectData P N) (w : ℚ)
    (tape : GuardedHintColumnTape d t s Q w) :
    (guardedHintColumnRun d t s Q w tape).value =
      (coefficientShapeSampleRun N d (guardedRationalShapeRun t Q w).value s tape).value := rfl

def guardedHintColumnDiagonalCost (T : ℕ) : ℕ :=
  guardedRationalShapeBudget T T T T + coefficientShapeSampleBudget T T T T + 1

theorem guardedHintColumnDiagonalCost_mono {T U : ℕ} (h : T ≤ U) :
    guardedHintColumnDiagonalCost T ≤ guardedHintColumnDiagonalCost U :=
  Nat.add_le_add_right (Nat.add_le_add (guardedRationalShapeBudget_mono h h h h)
    (coefficientShapeSampleBudget_mono h h h h)) 1

theorem guardedHintColumnDiagonalCost_polynomial : PolynomialCostBound guardedHintColumnDiagonalCost :=
  (guardedRationalShapeBudget_polynomial.add coefficientShapeSampleBudget_polynomial).add (PolynomialCostBound.const 1)

def guardedHintColumnBudget (P N L d t s : ℕ) : ℕ :=
  guardedHintColumnDiagonalCost (P + N + L + d + t + s + guardedRationalShapeBudget P N L t + 3)

theorem guardedHintColumnBudget_mono {P P' N N' L L' d d' t t' s s' : ℕ}
    (hP : P ≤ P') (hN : N ≤ N') (hL : L ≤ L') (hd : d ≤ d') (ht : t ≤ t') (hs : s ≤ s') :
    guardedHintColumnBudget P N L d t s ≤ guardedHintColumnBudget P' N' L' d' t' s' := by
  apply guardedHintColumnDiagonalCost_mono
  have hb := guardedRationalShapeBudget_mono hP hN hL ht
  omega

theorem guardedHintColumnBudget_polynomial :
    PolynomialCostBound (fun t => guardedHintColumnBudget t t t t t t) :=
  polynomialCostBound_comp_mono guardedHintColumnDiagonalCost_polynomial
    (((((((PolynomialCostBound.id.add PolynomialCostBound.id).add PolynomialCostBound.id).add
      PolynomialCostBound.id).add PolynomialCostBound.id).add PolynomialCostBound.id).add
        guardedRationalShapeBudget_polynomial).add (PolynomialCostBound.const 3))
    (fun _ _ h => guardedHintColumnDiagonalCost_mono h)

theorem guardedHintColumnRun_steps {P N L : ℕ} (hP : 0 < P) (d t s : ℕ) (hd : 0 < d)
    (Q : RationalRectData P N) (w : ℚ) (hw : w ≠ 0)
    (hQ : ∀ i j, rationalMagnitudeBits (rationalRectMatrixOfData Q i j) ≤ L)
    (hwbits : rationalMagnitudeBits w ≤ L) (tape : GuardedHintColumnTape d t s Q w) :
    (guardedHintColumnRun d t s Q w tape).steps ≤ guardedHintColumnBudget P N L d t s := by
  let T := P + N + L + d + t + s + guardedRationalShapeBudget P N L t + 3
  have hc := (guardedRationalShapeRun_steps hP t Q w hw hQ hwbits).trans
    (guardedRationalShapeBudget_mono (show P ≤ T by dsimp [T]; omega)
      (show N ≤ T by dsimp [T]; omega) (show L ≤ T by dsimp [T]; omega) (show t ≤ T by dsimp [T]; omega))
  have hs := (coefficientShapeSampleRun_steps_le hd (guardedRationalShapeRun t Q w).value
    (guardedRationalShapeRun_posDef hP t Q w hw) (guardedRationalShapeRun_bits hP t Q w hw hQ hwbits) s tape).trans
      (coefficientShapeSampleBudget_mono (show N ≤ T by dsimp [T]; omega)
        (show guardedRationalShapeBudget P N L t + 3 ≤ T by dsimp [T]; omega)
        (show d ≤ T by dsimp [T]; omega) (show s ≤ T by dsimp [T]; omega))
  exact Nat.add_le_add_right (Nat.add_le_add hc hs) 1

theorem guardedHintColumnRun_polynomial : ∃ C e : ℕ, ∀ (P N d : ℕ), 0 < P → 0 < d →
    ∀ (Q : RationalRectData P N) (w : ℚ), w ≠ 0 → ∀ (t s : ℕ) (tape : GuardedHintColumnTape d t s Q w),
      (guardedHintColumnRun d t s Q w tape).steps ≤
        C * (P + N + rationalRectMagnitudeBits Q + rationalMagnitudeBits w + d + t + s + 1) ^ e := by
  obtain ⟨C, e, h⟩ := guardedHintColumnBudget_polynomial.exists_mul_pow_bound
  refine ⟨C, e, fun P N d hP hd Q w hw t s tape => ?_⟩
  have hb : ∀ i j, rationalMagnitudeBits (rationalRectMatrixOfData Q i j) ≤
      rationalRectMagnitudeBits Q + rationalMagnitudeBits w := fun i j =>
    (rationalRect_entry_bits_le Q i j).trans (by omega)
  exact (guardedHintColumnRun_steps hP d t s hd Q w hw hb (by omega) tape).trans
    ((guardedHintColumnBudget_mono (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans
      (h (P + N + rationalRectMagnitudeBits Q + rationalMagnitudeBits w + d + t + s)))

theorem guardedHintColumnRun_output_bits {P N L : ℕ} (hP : 0 < P) (d t s : ℕ) (hd : 0 < d)
    (Q : RationalRectData P N) (w : ℚ) (hw : w ≠ 0)
    (hQ : ∀ i j, rationalMagnitudeBits (rationalRectMatrixOfData Q i j) ≤ L)
    (hwbits : rationalMagnitudeBits w ≤ L) (tape : GuardedHintColumnTape d t s Q w) (i : Fin N) :
    ((guardedHintColumnRun d t s Q w tape).value.get i).natAbs.size ≤
      N * gaussianAdaptiveGrowth N
        (gaussianCovarianceBits N (coefficientCovarianceBits N (guardedRationalShapeBudget P N L t + 3) d)) s :=
  coefficientShapeSampleRun_output_bits hd (guardedRationalShapeRun t Q w).value
    (guardedRationalShapeRun_posDef hP t Q w hw) (guardedRationalShapeRun_bits hP t Q w hw hQ hwbits) s tape i

noncomputable section

def guardedHintColumnLaw {P N : ℕ} (d t s : ℕ) (Q : RationalRectData P N) (w : ℚ) : PMF (Fin N → ℤ) :=
  (gaussianAdaptiveTapeLaw (gaussianCovarianceData N
    (coefficientCovarianceRun N d (guardedRationalShapeRun t Q w).value).value) s).map
      (fun tape => (guardedHintColumnRun d t s Q w tape).value.get)

theorem guardedHintColumnLaw_eq {P N : ℕ} (d t s : ℕ) (Q : RationalRectData P N) (w : ℚ) :
    guardedHintColumnLaw d t s Q w =
      coefficientShapeSampleLaw N d (guardedRationalShapeRun t Q w).value s := rfl

end

end SISToKSIS


open Module GeometricGaussianLHL
namespace SISToKSIS
set_option backward.isDefEq.respectTransparency false

/-- Stored matrices for multiplication by each integral basis vector. -/
abbrev BasisMultiplicationData (d : ℕ) := Vector (IntegerMatrixData d) d

def basisMultiplicationEntry {d : ℕ} (T : BasisMultiplicationData d) (t i j : Fin d) : ℤ :=
  integerMatrixOfData (T.get t) i j

def basisMultiplicationBits {d : ℕ} (T : BasisMultiplicationData d) : ℕ :=
  ∑ t, ∑ i, ∑ j, (basisMultiplicationEntry T t i j).natAbs.size

theorem basisMultiplicationEntry_bits {d : ℕ} (T : BasisMultiplicationData d) (t i j : Fin d) :
    (basisMultiplicationEntry T t i j).natAbs.size ≤ basisMultiplicationBits T := by
  unfold basisMultiplicationBits
  exact (Finset.single_le_sum (fun j _ => Nat.zero_le
    (basisMultiplicationEntry T t i j).natAbs.size) (Finset.mem_univ j)).trans
    ((Finset.single_le_sum (fun i _ => Nat.zero_le
      (∑ j, (basisMultiplicationEntry T t i j).natAbs.size)) (Finset.mem_univ i)).trans
      (Finset.single_le_sum (fun t _ => Nat.zero_le
        (∑ i, ∑ j, (basisMultiplicationEntry T t i j).natAbs.size)) (Finset.mem_univ t)))

def gaussianColumnsBits {R m : ℕ} (D : GaussianColumnData R m) : ℕ :=
  ∑ j, ∑ i, (gaussianColumnsOfData D j i).natAbs.size

theorem gaussianColumns_entry_bits {R m : ℕ} (D : GaussianColumnData R m) (j : Fin m) (i : Fin R) :
    (gaussianColumnsOfData D j i).natAbs.size ≤ gaussianColumnsBits D :=
  (Finset.single_le_sum (fun i _ => Nat.zero_le (gaussianColumnsOfData D j i).natAbs.size)
    (Finset.mem_univ i)).trans (Finset.single_le_sum (fun j _ => Nat.zero_le
      (∑ i, (gaussianColumnsOfData D j i).natAbs.size)) (Finset.mem_univ j))

/-- The exact integer block matrix computed from the stored basis table and columns. -/
def storedRingCoefficientMatrix {d k m : ℕ} (T : BasisMultiplicationData d)
    (D : GaussianColumnData (k * d) m) : Matrix (Fin (k * d)) (Fin (m * d)) ℤ :=
  fun i j => ∑ l, basisMultiplicationEntry T (finProdFinEquiv.symm j).2
    (finProdFinEquiv.symm i).2 l *
      gaussianColumnsOfData D (finProdFinEquiv.symm j).1
        (finProdFinEquiv ((finProdFinEquiv.symm i).1, l))

/-- Copy a pair of integer operands, charging the flattened input index. -/
def storedCoefficientPairRun {d k m : ℕ} (T : BasisMultiplicationData d)
    (D : GaussianColumnData (k * d) m) (row : Fin k) (col : Fin m)
    (t i l : Fin d) : Costed (ℤ × ℤ) :=
  let a := basisMultiplicationEntry T t i l
  let b := gaussianColumnsOfData D col (finProdFinEquiv (row, l))
  ⟨(a, b), (row.val.size + d.size + 1) ^ 2 +
    ((row.val * d).size + l.val.size + 1) + a.natAbs.size + b.natAbs.size + 3⟩

/-- Compute an entry once, including block decoding, operand storage and the rational cast. -/
def storedRingCoefficientEntryRun {d k m : ℕ} (T : BasisMultiplicationData d)
    (D : GaussianColumnData (k * d) m) (i : Fin (k * d)) (j : Fin (m * d)) : Costed ℚ :=
  let row := finProdFinEquiv.symm i
  let col := finProdFinEquiv.symm j
  let pairs := costedVectorOfFn (storedCoefficientPairRun T D row.1 col.1 col.2 row.2)
  let dot := costedIntegerDot pairs.value.toList
  ⟨(dot.value : ℚ), 2 * (i.val.size + d.size + 1) ^ 2 +
    2 * (j.val.size + d.size + 1) ^ 2 + pairs.steps + (d + 1) + dot.steps +
    (dot.value.natAbs.size + 1) + 3⟩

theorem storedRingCoefficientEntryRun_value {d k m : ℕ} (T : BasisMultiplicationData d)
    (D : GaussianColumnData (k * d) m) (i : Fin (k * d)) (j : Fin (m * d)) :
    (storedRingCoefficientEntryRun T D i j).value = (storedRingCoefficientMatrix T D i j : ℚ) := by
  simp [storedRingCoefficientEntryRun, costedVectorOfFn_value, costedIntegerDot_value,
    integerListDot, Vector.toList_ofFn, storedCoefficientPairRun, storedRingCoefficientMatrix,
    List.sum_ofFn]

/-- Finite preparation of the exact rational input to the shaping algorithm. -/
def storedRingCoefficientRun {d k m : ℕ} (T : BasisMultiplicationData d)
    (D : GaussianColumnData (k * d) m) : Costed (RationalRectData (k * d) (m * d)) :=
  costedRationalRectOfFn (storedRingCoefficientEntryRun T D)

theorem storedRingCoefficientRun_value {d k m : ℕ} (T : BasisMultiplicationData d)
    (D : GaussianColumnData (k * d) m) :
    rationalRectMatrixOfData (storedRingCoefficientRun T D).value =
      integerRationalMatrix (storedRingCoefficientMatrix T D) := by
  rw [storedRingCoefficientRun, costedRationalRectOfFn_data, rationalRectMatrixOfData_data]
  ext i j
  exact storedRingCoefficientEntryRun_value T D i j

def storedCoefficientPairBudget (d k L : ℕ) : ℕ :=
  (k + d + 1) ^ 2 + (k * d + d + 1) + 2 * L + 3

theorem storedCoefficientPairRun_steps {d k m L : ℕ} (T : BasisMultiplicationData d)
    (D : GaussianColumnData (k * d) m)
    (hT : ∀ t i j, (basisMultiplicationEntry T t i j).natAbs.size ≤ L)
    (hD : ∀ j i, (gaussianColumnsOfData D j i).natAbs.size ≤ L)
    (row : Fin k) (col : Fin m) (t i l : Fin d) :
    (storedCoefficientPairRun T D row col t i l).steps ≤ storedCoefficientPairBudget d k L := by
  have sz (n : ℕ) : n.size ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self
  have hd := sz d
  have hr := (sz row.val).trans row.isLt.le
  have hl := (sz l.val).trans l.isLt.le
  have hp := (sz (row.val * d)).trans (Nat.mul_le_mul_right d row.isLt.le)
  have hpow := Nat.pow_le_pow_left (show row.val.size + d.size + 1 ≤ k + d + 1 by omega) 2
  have ha := hT t i l
  have hb := hD col (finProdFinEquiv (row, l))
  dsimp only [storedCoefficientPairRun]
  unfold storedCoefficientPairBudget
  omega

def storedRingCoefficientEntryBudget (d k m L : ℕ) : ℕ :=
  2 * (k * d + d + 1) ^ 2 + 2 * (m * d + d + 1) ^ 2 +
    (d * (storedCoefficientPairBudget d k L + 3) + 1) + (d + 1) +
    (d * integerDotStepBudget d L + 1) + (d + 2 * L + 2) + 3

theorem storedRingCoefficientEntryRun_steps {d k m L : ℕ} (T : BasisMultiplicationData d)
    (D : GaussianColumnData (k * d) m)
    (hT : ∀ t i j, (basisMultiplicationEntry T t i j).natAbs.size ≤ L)
    (hD : ∀ j i, (gaussianColumnsOfData D j i).natAbs.size ≤ L)
    (i : Fin (k * d)) (j : Fin (m * d)) :
    (storedRingCoefficientEntryRun T D i j).steps ≤ storedRingCoefficientEntryBudget d k m L := by
  let pairs := costedVectorOfFn (storedCoefficientPairRun T D
    (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm j).1
    (finProdFinEquiv.symm j).2 (finProdFinEquiv.symm i).2)
  have hpairs : ∀ x ∈ pairs.value.toList, x.1.natAbs.size ≤ L ∧ x.2.natAbs.size ≤ L := by
    intro x hx
    simp only [pairs, costedVectorOfFn_value, Vector.toList_ofFn, List.mem_ofFn] at hx
    obtain ⟨l, rfl⟩ := hx
    exact ⟨hT _ _ l, hD _ _⟩
  have hdot := costedIntegerDot_steps_le pairs.value.toList L hpairs
  have hbits := integerListDot_size_le pairs.value.toList L hpairs
  simp only [Vector.length_toList] at hdot hbits
  have hpair := costedVectorOfFn_steps_le _ _
    (storedCoefficientPairRun_steps T D hT hD
      (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm j).1
      (finProdFinEquiv.symm j).2 (finProdFinEquiv.symm i).2)
  change pairs.steps ≤ _ at hpair
  have sz (n : ℕ) : n.size ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self
  have hd := sz d
  have hi := (sz i.val).trans i.isLt.le
  have hj := (sz j.val).trans j.isLt.le
  have hi2 := Nat.pow_le_pow_left (show i.val.size + d.size + 1 ≤ k * d + d + 1 by omega) 2
  have hj2 := Nat.pow_le_pow_left (show j.val.size + d.size + 1 ≤ m * d + d + 1 by omega) 2
  change 2 * (i.val.size + d.size + 1) ^ 2 + 2 * (j.val.size + d.size + 1) ^ 2 +
    pairs.steps + (d + 1) + (costedIntegerDot pairs.value.toList).steps +
    ((costedIntegerDot pairs.value.toList).value.natAbs.size + 1) + 3 ≤ _
  rw [costedIntegerDot_value]
  unfold storedRingCoefficientEntryBudget
  omega

theorem storedRingCoefficientMatrix_bits {d k m L : ℕ} (T : BasisMultiplicationData d)
    (D : GaussianColumnData (k * d) m)
    (hT : ∀ t i j, (basisMultiplicationEntry T t i j).natAbs.size ≤ L)
    (hD : ∀ j i, (gaussianColumnsOfData D j i).natAbs.size ≤ L) (i j) :
    (storedRingCoefficientMatrix T D i j).natAbs.size ≤ d + 2 * L + 1 := by
  have h := integerListDot_size_le (List.ofFn fun l : Fin d =>
    (basisMultiplicationEntry T (finProdFinEquiv.symm j).2 (finProdFinEquiv.symm i).2 l,
      gaussianColumnsOfData D (finProdFinEquiv.symm j).1
        (finProdFinEquiv ((finProdFinEquiv.symm i).1, l)))) L (by
      intro x hx
      obtain ⟨l, rfl⟩ := List.mem_ofFn.mp hx
      exact ⟨hT _ _ _, hD _ _⟩)
  simpa [integerListDot, List.sum_ofFn, storedRingCoefficientMatrix] using h

def storedRingCoefficientBudget (d k m L : ℕ) : ℕ :=
  rationalRectTraversalBudget (k * d) (m * d) (storedRingCoefficientEntryBudget d k m L)

theorem storedRingCoefficientRun_steps {d k m L : ℕ} (T : BasisMultiplicationData d)
    (D : GaussianColumnData (k * d) m)
    (hT : ∀ t i j, (basisMultiplicationEntry T t i j).natAbs.size ≤ L)
    (hD : ∀ j i, (gaussianColumnsOfData D j i).natAbs.size ≤ L) :
    (storedRingCoefficientRun T D).steps ≤ storedRingCoefficientBudget d k m L :=
  costedRationalRectOfFn_steps_le _ _ (storedRingCoefficientEntryRun_steps T D hT hD)

theorem storedRingCoefficientRun_bits {d k m L : ℕ} (T : BasisMultiplicationData d)
    (D : GaussianColumnData (k * d) m)
    (hT : ∀ t i j, (basisMultiplicationEntry T t i j).natAbs.size ≤ L)
    (hD : ∀ j i, (gaussianColumnsOfData D j i).natAbs.size ≤ L) (i j) :
    rationalMagnitudeBits (rationalRectMatrixOfData (storedRingCoefficientRun T D).value i j) ≤
      d + 2 * L + 3 := by
  rw [storedRingCoefficientRun_value]
  exact (intCast_rational_bits _).le.trans
    (Nat.add_le_add_right (storedRingCoefficientMatrix_bits T D hT hD i j) 2)

section Semantics
variable {O : Type*} [CommRing O] {d k m : ℕ}

/-- The supplied finite table represents multiplication in the specified integral basis. -/
def BasisMultiplicationData.Represents (T : BasisMultiplicationData d) (b : Basis (Fin d) ℤ O) : Prop :=
  ∀ t i j, basisMultiplicationEntry T t i j = b.equivFun (b t * b j) i

noncomputable def decodedCoefficientMatrix (b : Basis (Fin d) ℤ O)
    (D : GaussianColumnData (k * d) m) : Matrix (Fin k) (Fin m) O :=
  fun i j => (ringPowerCoordinates b k).symm (gaussianColumnsOfData D j) i

theorem decodedCoefficientMatrix_coordinates (b : Basis (Fin d) ℤ O)
    (D : GaussianColumnData (k * d) m) (i : Fin k) (j : Fin m) (l : Fin d) :
    b.equivFun (decodedCoefficientMatrix b D i j) l =
      gaussianColumnsOfData D j (finProdFinEquiv (i, l)) := by
  change b.equivFun (b.equivFun.symm _) l = _
  rw [LinearEquiv.apply_symm_apply]

theorem BasisMultiplicationData.coordinates_mul (T : BasisMultiplicationData d)
    (b : Basis (Fin d) ℤ O) (hT : T.Represents b) (t i : Fin d) (x : O) :
    ∑ j, basisMultiplicationEntry T t i j * b.equivFun x j = b.equivFun (b t * x) i := by
  conv_rhs => rw [← b.sum_equivFun x]
  simp only [Finset.mul_sum, mul_smul_comm, map_sum, map_smul,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [hT t i j, mul_comm]

theorem storedRingCoefficientMatrix_correct (T : BasisMultiplicationData d)
    (b : Basis (Fin d) ℤ O) (hT : T.Represents b) (D : GaussianColumnData (k * d) m) :
    storedRingCoefficientMatrix T D = ringCoefficientMatrix b (decodedCoefficientMatrix b D) := by
  ext i j
  obtain ⟨⟨row, l⟩, rfl⟩ := finProdFinEquiv.surjective i
  obtain ⟨⟨col, t⟩, rfl⟩ := finProdFinEquiv.surjective j
  have hc := congrFun (ringCoefficientMatrix_column b (decodedCoefficientMatrix b D) col t)
    (finProdFinEquiv (row, l))
  rw [ringPowerCoordinates_apply] at hc
  rw [hc]
  simp only [storedRingCoefficientMatrix, Equiv.symm_apply_apply]
  simpa only [decodedCoefficientMatrix_coordinates] using
    T.coordinates_mul b hT t l (decodedCoefficientMatrix b D row col)

theorem storedRingCoefficientRun_correct (T : BasisMultiplicationData d)
    (b : Basis (Fin d) ℤ O) (hT : T.Represents b) (D : GaussianColumnData (k * d) m) :
    rationalRectMatrixOfData (storedRingCoefficientRun T D).value =
      integerRationalMatrix (ringCoefficientMatrix b (decodedCoefficientMatrix b D)) := by
  rw [storedRingCoefficientRun_value, storedRingCoefficientMatrix_correct T b hT]

end Semantics

theorem storedRingCoefficientBudget_mono {d d' k k' m m' L L' : ℕ}
    (hd : d ≤ d') (hk : k ≤ k') (hm : m ≤ m') (hL : L ≤ L') :
    storedRingCoefficientBudget d k m L ≤ storedRingCoefficientBudget d' k' m' L' := by
  unfold storedRingCoefficientBudget storedRingCoefficientEntryBudget storedCoefficientPairBudget
    rationalRectTraversalBudget integerDotStepBudget
  gcongr

theorem storedRingCoefficientBudget_polynomial :
    PolynomialCostBound (fun t => storedRingCoefficientBudget t t t t) := by
  let x : Polynomial ℕ := Polynomial.X
  let pair := (x + x + 1) ^ 2 + (x * x + x + 1) + 2 * x + 3
  let dot := (2 * x + 1) ^ 2 + x + 4 * x + 4
  let entry := 2 * (x * x + x + 1) ^ 2 + 2 * (x * x + x + 1) ^ 2 +
    (x * (pair + 3) + 1) + (x + 1) + (x * dot + 1) + (x + 2 * x + 2) + 3
  refine ⟨(x * x) * ((x * x) * (entry + 3) + 4) + 1, ?_⟩
  intro t
  apply le_of_eq
  simp [storedRingCoefficientBudget, storedRingCoefficientEntryBudget, storedCoefficientPairBudget,
    rationalRectTraversalBudget, integerDotStepBudget, entry, pair, dot, x]

theorem storedRingCoefficientRun_polynomial : ∃ C e : ℕ, ∀ (d k m : ℕ)
    (T : BasisMultiplicationData d) (D : GaussianColumnData (k * d) m),
    (storedRingCoefficientRun T D).steps ≤
      C * (d + k + m + basisMultiplicationBits T + gaussianColumnsBits D + 1) ^ e := by
  obtain ⟨C, e, h⟩ := storedRingCoefficientBudget_polynomial.exists_mul_pow_bound
  refine ⟨C, e, fun d k m T D => ?_⟩
  have hT : ∀ t i j, (basisMultiplicationEntry T t i j).natAbs.size ≤
      basisMultiplicationBits T + gaussianColumnsBits D := fun t i j =>
    (basisMultiplicationEntry_bits T t i j).trans (by omega)
  have hD : ∀ j i, (gaussianColumnsOfData D j i).natAbs.size ≤
      basisMultiplicationBits T + gaussianColumnsBits D := fun j i =>
    (gaussianColumns_entry_bits D j i).trans (by omega)
  exact (storedRingCoefficientRun_steps T D hT hD).trans
    ((storedRingCoefficientBudget_mono (by omega) (by omega) (by omega) (by omega)).trans
      (h (d + k + m + basisMultiplicationBits T + gaussianColumnsBits D)))

def encodeBasisMultiplicationData {d : ℕ} (T : BasisMultiplicationData d) : List Bool :=
  encodeNatBits d ++ encodeVectorBits (encodeVectorBits (encodeVectorBits encodeIntBits)) T

theorem encodeBasisMultiplicationData_length {d : ℕ} (T : BasisMultiplicationData d) :
    (encodeBasisMultiplicationData T).length =
      2 * d.size + 1 + 2 * basisMultiplicationBits T + 2 * d * d * d := by
  simp only [encodeBasisMultiplicationData, List.length_append, encodeNatBits_length,
    encodeVectorBits_length_sum, encodeIntBits_length, basisMultiplicationBits,
    basisMultiplicationEntry, integerMatrixOfData]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
  ring

theorem basisMultiplicationBits_le_encoded {d : ℕ} (T : BasisMultiplicationData d) :
    basisMultiplicationBits T ≤ (encodeBasisMultiplicationData T).length := by
  rw [encodeBasisMultiplicationData_length]
  omega

theorem gaussianColumnsBits_le_encoded {R m : ℕ} (D : GaussianColumnData R m) :
    gaussianColumnsBits D ≤ (encodeIntegerRectData D).length := by
  rw [encodeIntegerRectData_length]
  change (∑ j, ∑ i, (gaussianColumnsOfData D j i).natAbs.size) ≤
    2 * m.size + 2 * R.size + 2 +
      2 * (∑ j, ∑ i, (gaussianColumnsOfData D j i).natAbs.size) + 2 * (m * R)
  omega

theorem storedRingCoefficientRun_polynomial_encoded : ∃ C e : ℕ, ∀ (d k m : ℕ)
    (T : BasisMultiplicationData d) (D : GaussianColumnData (k * d) m),
    (storedRingCoefficientRun T D).steps ≤
      C * (d + k + m + (encodeBasisMultiplicationData T).length +
        (encodeIntegerRectData D).length + 1) ^ e := by
  obtain ⟨C, e, h⟩ := storedRingCoefficientRun_polynomial
  refine ⟨C, e, fun d k m T D => (h d k m T D).trans ?_⟩
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_left
  have ht := basisMultiplicationBits_le_encoded T
  have hD := gaussianColumnsBits_le_encoded D
  omega

/-- Retain the initial sample while constructing its exact stored multiplication matrix. -/
def initialCoefficientRun {d : ℕ} (T : BasisMultiplicationData d) (a b k m s : ℕ)
    (tape : InitialGaussianTape a b d k m s) :
    Costed (GaussianColumnData (k * d) m × RationalRectData (k * d) (m * d)) :=
  let initial := initialGaussianRun a b d k m s tape
  let coefficients := storedRingCoefficientRun T initial.value
  ⟨(initial.value, coefficients.value), initial.steps + coefficients.steps + 1⟩

theorem initialCoefficientRun_value {d : ℕ} (T : BasisMultiplicationData d) (a b k m s : ℕ)
    (tape : InitialGaussianTape a b d k m s) :
    (initialCoefficientRun T a b k m s tape).value =
      ((initialGaussianRun a b d k m s tape).value,
        (storedRingCoefficientRun T (initialGaussianRun a b d k m s tape).value).value) := rfl

def initialCoefficientBudget (d k m L I s : ℕ) : ℕ :=
  10 ^ 37 * (I + s + 1) ^ 7 +
    storedRingCoefficientBudget d k m (L + 352 * (I + s + 1)) + 1

theorem initialCoefficientRun_steps {a b d L : ℕ} (T : BasisMultiplicationData d)
    (hT : ∀ t i j, (basisMultiplicationEntry T t i j).natAbs.size ≤ L)
    (ha : 0 < a) (hb : 0 < b) (hd : 0 < d) (k m s : ℕ)
    (tape : InitialGaussianTape a b d k m s) :
    (initialCoefficientRun T a b k m s tape).steps ≤
      initialCoefficientBudget d k m L (initialGaussianSamplingSize a b d k m) s := by
  have hi := initialGaussianRun_polynomial_bound ha hb hd k m s tape
  have ht : ∀ t i j, (basisMultiplicationEntry T t i j).natAbs.size ≤
      L + 352 * (initialGaussianSamplingSize a b d k m + s + 1) := fun t i j =>
    (hT t i j).trans (by omega)
  have hc := storedRingCoefficientRun_steps T (initialGaussianRun a b d k m s tape).value ht
    (fun j i => (initialGaussianRun_output_size a b d k m s tape j i).trans (by omega))
  exact Nat.add_le_add_right (Nat.add_le_add hi hc) 1

theorem initialCoefficientRun_bits {d : ℕ} (T : BasisMultiplicationData d) (a b k m s : ℕ)
    (tape : InitialGaussianTape a b d k m s) (i j) :
    rationalMagnitudeBits (rationalRectMatrixOfData (initialCoefficientRun T a b k m s tape).value.2 i j) ≤
      d + 2 * (basisMultiplicationBits T + 352 * (initialGaussianSamplingSize a b d k m + s + 1)) + 3 := by
  exact storedRingCoefficientRun_bits T (initialGaussianRun a b d k m s tape).value
    (fun t i j => (basisMultiplicationEntry_bits T t i j).trans (by omega))
    (fun j i => (initialGaussianRun_output_size a b d k m s tape j i).trans (by omega)) i j

theorem initialCoefficientBudget_mono {d d' k k' m m' L L' I I' s s' : ℕ}
    (hd : d ≤ d') (hk : k ≤ k') (hm : m ≤ m') (hL : L ≤ L') (hI : I ≤ I') (hs : s ≤ s') :
    initialCoefficientBudget d k m L I s ≤ initialCoefficientBudget d' k' m' L' I' s' := by
  unfold initialCoefficientBudget
  apply Nat.add_le_add_right
  apply Nat.add_le_add
  · gcongr
  · apply storedRingCoefficientBudget_mono hd hk hm
    omega

theorem initialCoefficientBudget_polynomial :
    PolynomialCostBound (fun t => initialCoefficientBudget t t t t t t) := by
  have hp : PolynomialCostBound (fun t =>
      storedRingCoefficientBudget t t t (t + 352 * (t + t + 1))) :=
    (polynomialCostBound_comp_mono storedRingCoefficientBudget_polynomial
      (PolynomialCostBound.id.add ((PolynomialCostBound.const 352).mul
        ((PolynomialCostBound.id.add PolynomialCostBound.id).add (PolynomialCostBound.const 1))))
      (fun _ _ h => storedRingCoefficientBudget_mono h h h h)).mono
        (fun t => storedRingCoefficientBudget_mono (by omega) (by omega) (by omega) le_rfl)
  exact (((PolynomialCostBound.const (10 ^ 37)).mul
    (((PolynomialCostBound.id.add PolynomialCostBound.id).add (PolynomialCostBound.const 1)).pow 7)).add hp).add
      (PolynomialCostBound.const 1)

theorem initialCoefficientRun_polynomial : ∃ C e : ℕ, ∀ (d : ℕ) (T : BasisMultiplicationData d)
    (a b : ℕ), 0 < a → 0 < b → 0 < d → ∀ (k m s : ℕ) (tape : InitialGaussianTape a b d k m s),
      (initialCoefficientRun T a b k m s tape).steps ≤
        C * (d + k + m + basisMultiplicationBits T + initialGaussianSamplingSize a b d k m + s + 1) ^ e := by
  obtain ⟨C, e, h⟩ := initialCoefficientBudget_polynomial.exists_mul_pow_bound
  refine ⟨C, e, fun d T a b ha hb hd k m s tape => ?_⟩
  exact (initialCoefficientRun_steps T (basisMultiplicationEntry_bits T) ha hb hd k m s tape).trans
    ((initialCoefficientBudget_mono (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans
      (h (d + k + m + basisMultiplicationBits T + initialGaussianSamplingSize a b d k m + s)))

section StoredCoordinates
variable {O : Type*} [CommRing O] {d k m : ℕ}

/-- Mathematical encoding used to compare the stored computation with the field-valued games. -/
noncomputable def encodedRingMatrix (b : Basis (Fin d) ℤ O)
    (X : Matrix (Fin k) (Fin m) O) : GaussianColumnData (k * d) m :=
  Vector.ofFn (fun j => Vector.ofFn (ringPowerCoordinates b k (fun i => X i j)))

theorem gaussianColumnsOfData_encodedRingMatrix (b : Basis (Fin d) ℤ O)
    (X : Matrix (Fin k) (Fin m) O) :
    gaussianColumnsOfData (encodedRingMatrix b X) =
      fun j => ringPowerCoordinates b k (fun i => X i j) := by
  funext j i
  simp [gaussianColumnsOfData, encodedRingMatrix, Vector.get]

theorem decodedCoefficientMatrix_encodedRingMatrix (b : Basis (Fin d) ℤ O)
    (X : Matrix (Fin k) (Fin m) O) : decodedCoefficientMatrix b (encodedRingMatrix b X) = X := by
  ext i j
  simp only [decodedCoefficientMatrix, gaussianColumnsOfData_encodedRingMatrix,
    LinearEquiv.symm_apply_apply]

theorem gaussianColumnsOfData_injective (R m : ℕ) :
    Function.Injective (@gaussianColumnsOfData R m) := by
  intro D E h
  apply Vector.ext
  intro j hj
  apply Vector.ext
  intro i hi
  exact congrFun (congrFun h ⟨j, hj⟩) ⟨i, hi⟩

theorem encodedRingMatrix_decodedCoefficientMatrix (b : Basis (Fin d) ℤ O)
    (D : GaussianColumnData (k * d) m) : encodedRingMatrix b (decodedCoefficientMatrix b D) = D := by
  apply gaussianColumnsOfData_injective
  rw [gaussianColumnsOfData_encodedRingMatrix]
  funext j i
  change ringPowerCoordinates b k ((ringPowerCoordinates b k).symm (gaussianColumnsOfData D j)) i = _
  rw [LinearEquiv.apply_symm_apply]

/-- The parameter family used by the analytical law is realized by the stored constructor. -/
theorem storedRingCoefficientRun_encoded_correct (T : BasisMultiplicationData d)
    (b : Basis (Fin d) ℤ O) (hT : T.Represents b) (X : Matrix (Fin k) (Fin m) O) :
    rationalRectMatrixOfData (storedRingCoefficientRun T (encodedRingMatrix b X)).value =
      integerRationalMatrix (ringCoefficientMatrix b X) := by
  rw [storedRingCoefficientRun_correct T b hT, decodedCoefficientMatrix_encodedRingMatrix]

theorem initialCoefficientRun_correct (T : BasisMultiplicationData d)
    (basis : Basis (Fin d) ℤ O) (hT : T.Represents basis) (a b k m s : ℕ)
    (tape : InitialGaussianTape a b d k m s) :
    rationalRectMatrixOfData (initialCoefficientRun T a b k m s tape).value.2 =
      integerRationalMatrix (ringCoefficientMatrix basis
        (decodedCoefficientMatrix basis (initialCoefficientRun T a b k m s tape).value.1)) :=
  storedRingCoefficientRun_correct T basis hT (initialGaussianRun a b d k m s tape).value

theorem initialCoefficientRun_family (T : BasisMultiplicationData d)
    (basis : Basis (Fin d) ℤ O) (a b k m s : ℕ)
    (tape : InitialGaussianTape a b d k m s) :
    (initialCoefficientRun T a b k m s tape).value.2 =
      (storedRingCoefficientRun T (encodedRingMatrix basis
        (decodedCoefficientMatrix basis (initialCoefficientRun T a b k m s tape).value.1))).value := by
  rw [encodedRingMatrix_decodedCoefficientMatrix]
  rfl

end StoredCoordinates

structure HintPrecisionSchedule where
  dimension : ℕ
  shapingBits : ℕ
  samplingBits : ℕ
  deriving Repr, DecidableEq

/-- Charged arithmetic for exactly the precision schedule used by the accuracy proof. -/
def hintPrecisionRun (m d p : ℕ) : Costed HintPrecisionSchedule :=
  let N := costedNatMul m d
  let next := costedNatAdd p 1
  let doubled := costedNatMul 2 next.value
  let base := costedNatAdd 0 N.value
  let combined := costedNatAdd base.value doubled.value
  let shaping := costedNatAdd combined.value 18
  let sampling := costedNatAdd p 2
  ⟨⟨N.value, shaping.value, sampling.value⟩,
    N.steps + next.steps + doubled.steps + base.steps + combined.steps + shaping.steps + sampling.steps + 1⟩

theorem hintPrecisionRun_value (m d p : ℕ) :
    (hintPrecisionRun m d p).value = ⟨m * d, gaussianShapeBits (m * d) 0 (p + 1), p + 2⟩ := rfl

def hintPrecisionBudget (m d p : ℕ) : ℕ :=
  7 * (2 * (m * d + 2 * (p + 1) + m + d + p + 25) + 1) ^ 2 + 1

theorem hintPrecisionRun_steps (m d p : ℕ) : (hintPrecisionRun m d p).steps ≤ hintPrecisionBudget m d p := by
  let L := m * d + 2 * (p + 1) + m + d + p + 25
  have hN := costedNatMul_steps_le m d L (by dsimp [L]; omega) (by dsimp [L]; omega)
  have hn := costedNatAdd_steps_le p 1 L (by dsimp [L]; omega) (by dsimp [L]; omega)
  have hd := costedNatMul_steps_le 2 (p + 1) L (by dsimp [L]; omega) (by dsimp [L]; omega)
  have hb := costedNatAdd_steps_le 0 (m * d) L (by omega) (by dsimp [L]; omega)
  have hc := costedNatAdd_steps_le (0 + m * d) (2 * (p + 1)) L (by dsimp [L]; omega) (by dsimp [L]; omega)
  have hh := costedNatAdd_steps_le (0 + m * d + 2 * (p + 1)) 18 L (by dsimp [L]; omega) (by dsimp [L]; omega)
  have hs := costedNatAdd_steps_le p 2 L (by dsimp [L]; omega) (by dsimp [L]; omega)
  change (costedNatMul m d).steps + (costedNatAdd p 1).steps + (costedNatMul 2 (p + 1)).steps +
    (costedNatAdd 0 (m * d)).steps + (costedNatAdd (0 + m * d) (2 * (p + 1))).steps +
    (costedNatAdd (0 + m * d + 2 * (p + 1)) 18).steps + (costedNatAdd p 2).steps + 1 ≤
      7 * (2 * L + 1) ^ 2 + 1
  omega

theorem hintPrecisionBudget_mono {m m' d d' p p' : ℕ}
    (hm : m ≤ m') (hd : d ≤ d') (hp : p ≤ p') :
    hintPrecisionBudget m d p ≤ hintPrecisionBudget m' d' p' := by
  unfold hintPrecisionBudget
  gcongr

theorem hintPrecisionBudget_polynomial : PolynomialCostBound (fun t => hintPrecisionBudget t t t) := by
  let x : Polynomial ℕ := Polynomial.X
  refine ⟨7 * (2 * (x * x + 2 * (x + 1) + x + x + x + 25) + 1) ^ 2 + 1, ?_⟩
  intro t
  apply le_of_eq
  simp [hintPrecisionBudget, x]

abbrev BasisHintColumnsTape {d k m : ℕ} (T : BasisMultiplicationData d)
    (D : GaussianColumnData (k * d) m) (w : ℚ) (p : ℕ) :=
  Fin k → CoefficientShapeSampleTape (m * d) d
    (guardedRationalShapeRun (hintPrecisionRun m d p).value.shapingBits
      (storedRingCoefficientRun T D).value w).value (hintPrecisionRun m d p).value.samplingBits

/-- Prepare the coefficient matrix and shape once, then store all independently sampled columns. -/
def basisHintColumnsRun {d k m : ℕ} (T : BasisMultiplicationData d)
    (D : GaussianColumnData (k * d) m) (w : ℚ) (p : ℕ)
    (tape : BasisHintColumnsTape T D w p) : Costed (GaussianColumnData (m * d) k) :=
  let schedule := hintPrecisionRun m d p
  let coefficients := storedRingCoefficientRun T D
  let shape := guardedRationalShapeRun schedule.value.shapingBits coefficients.value w
  let samples := costedVectorOfFn (fun j : Fin k =>
    coefficientShapeSampleRun (m * d) d shape.value schedule.value.samplingBits (tape j))
  ⟨samples.value, schedule.steps + coefficients.steps + shape.steps + samples.steps + 1⟩

theorem basisHintColumnsRun_coordinates {d k m : ℕ} (T : BasisMultiplicationData d)
    (D : GaussianColumnData (k * d) m) (w : ℚ) (p : ℕ)
    (tape : BasisHintColumnsTape T D w p) :
    gaussianColumnsOfData (basisHintColumnsRun T D w p tape).value =
      fun j => (guardedHintColumnRun d (gaussianShapeBits (m * d) 0 (p + 1)) (p + 2)
        (storedRingCoefficientRun T D).value w (tape j)).value.get := by
  funext j i
  simp [basisHintColumnsRun, gaussianColumnsOfData, costedVectorOfFn_value, Vector.get,
    guardedHintColumnRun, hintPrecisionRun_value]

/-- A common bound for all dimensions, precisions and intermediate shape entry lengths. -/
def basisHintColumnsBase (d k m L p : ℕ) : ℕ :=
  d + k + m + L + p + k * d + m * d + (d + 2 * L + 3) + gaussianShapeBits (m * d) 0 (p + 1)

def basisHintColumnsWork (d k m L p : ℕ) : ℕ :=
  let B := basisHintColumnsBase d k m L p
  B + guardedRationalShapeBudget B B B B + 3

def basisHintColumnsDiagonalCost (x : ℕ) : ℕ :=
  hintPrecisionBudget x x x + storedRingCoefficientBudget x x x x +
    guardedRationalShapeBudget x x x x + x * (coefficientShapeSampleBudget x x x x + 3) + 2

def basisHintColumnsBudget (d k m L p : ℕ) : ℕ :=
  basisHintColumnsDiagonalCost (basisHintColumnsWork d k m L p)

theorem basisHintColumnsBase_mono {d d' k k' m m' L L' p p' : ℕ}
    (hd : d ≤ d') (hk : k ≤ k') (hm : m ≤ m') (hL : L ≤ L') (hp : p ≤ p') :
    basisHintColumnsBase d k m L p ≤ basisHintColumnsBase d' k' m' L' p' := by
  unfold basisHintColumnsBase gaussianShapeBits
  gcongr

theorem basisHintColumnsBase_polynomial : PolynomialCostBound (fun t => basisHintColumnsBase t t t t t) := by
  let x : Polynomial ℕ := Polynomial.X
  refine ⟨x + x + x + x + x + x * x + x * x + (x + 2 * x + 3) +
    (0 + x * x + 2 * (x + 1) + 18), ?_⟩
  intro t
  apply le_of_eq
  simp [basisHintColumnsBase, gaussianShapeBits, x]

theorem basisHintColumnsWork_mono {d d' k k' m m' L L' p p' : ℕ}
    (hd : d ≤ d') (hk : k ≤ k') (hm : m ≤ m') (hL : L ≤ L') (hp : p ≤ p') :
    basisHintColumnsWork d k m L p ≤ basisHintColumnsWork d' k' m' L' p' := by
  have h := basisHintColumnsBase_mono hd hk hm hL hp
  exact Nat.add_le_add_right (Nat.add_le_add h (guardedRationalShapeBudget_mono h h h h)) 3

theorem basisHintColumnsWork_polynomial : PolynomialCostBound (fun t => basisHintColumnsWork t t t t t) :=
  (basisHintColumnsBase_polynomial.add
    (polynomialCostBound_comp_mono guardedRationalShapeBudget_polynomial basisHintColumnsBase_polynomial
      (fun _ _ h => guardedRationalShapeBudget_mono h h h h))).add (PolynomialCostBound.const 3)

theorem basisHintColumnsDiagonalCost_mono {x y : ℕ} (h : x ≤ y) :
    basisHintColumnsDiagonalCost x ≤ basisHintColumnsDiagonalCost y := by
  unfold basisHintColumnsDiagonalCost
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add
    (Nat.add_le_add (hintPrecisionBudget_mono h h h) (storedRingCoefficientBudget_mono h h h h))
    (guardedRationalShapeBudget_mono h h h h))
    (Nat.mul_le_mul h (Nat.add_le_add_right (coefficientShapeSampleBudget_mono h h h h) 3))) 2

theorem basisHintColumnsDiagonalCost_polynomial : PolynomialCostBound basisHintColumnsDiagonalCost :=
  (((hintPrecisionBudget_polynomial.add storedRingCoefficientBudget_polynomial).add
    guardedRationalShapeBudget_polynomial).add (PolynomialCostBound.id.mul
      (coefficientShapeSampleBudget_polynomial.add (PolynomialCostBound.const 3)))).add (PolynomialCostBound.const 2)

theorem basisHintColumnsBudget_mono {d d' k k' m m' L L' p p' : ℕ}
    (hd : d ≤ d') (hk : k ≤ k') (hm : m ≤ m') (hL : L ≤ L') (hp : p ≤ p') :
    basisHintColumnsBudget d k m L p ≤ basisHintColumnsBudget d' k' m' L' p' :=
  basisHintColumnsDiagonalCost_mono (basisHintColumnsWork_mono hd hk hm hL hp)

theorem basisHintColumnsBudget_polynomial : PolynomialCostBound (fun t => basisHintColumnsBudget t t t t t) :=
  polynomialCostBound_comp_mono basisHintColumnsDiagonalCost_polynomial basisHintColumnsWork_polynomial
    (fun _ _ h => basisHintColumnsDiagonalCost_mono h)

theorem basisHintColumnsRun_steps {d k m L : ℕ} (hd : 0 < d) (hk : 0 < k)
    (T : BasisMultiplicationData d) (D : GaussianColumnData (k * d) m)
    (hT : ∀ t i j, (basisMultiplicationEntry T t i j).natAbs.size ≤ L)
    (hD : ∀ j i, (gaussianColumnsOfData D j i).natAbs.size ≤ L)
    (w : ℚ) (hw : w ≠ 0) (hwbits : rationalMagnitudeBits w ≤ L) (p : ℕ)
    (tape : BasisHintColumnsTape T D w p) :
    (basisHintColumnsRun T D w p tape).steps ≤ basisHintColumnsBudget d k m L p := by
  let t := gaussianShapeBits (m * d) 0 (p + 1)
  let Q := (storedRingCoefficientRun T D).value
  let B := basisHintColumnsBase d k m L p
  let W := basisHintColumnsWork d k m L p
  have hB : d ≤ B ∧ k ≤ B ∧ m ≤ B ∧ L ≤ B ∧ p ≤ B ∧ k * d ≤ B ∧ m * d ≤ B ∧
      d + 2 * L + 3 ≤ B ∧ t ≤ B := by dsimp [B, t, basisHintColumnsBase]; omega
  have hBW : B ≤ W := by dsimp [W, basisHintColumnsWork]; omega
  have hQ := storedRingCoefficientRun_bits T D hT hD
  have hw' : rationalMagnitudeBits w ≤ d + 2 * L + 3 := hwbits.trans (by omega)
  have hS := guardedRationalShapeBudget_mono hB.2.2.2.2.2.1 hB.2.2.2.2.2.2.1
    hB.2.2.2.2.2.2.2.1 hB.2.2.2.2.2.2.2.2
  have hSW : guardedRationalShapeBudget (k * d) (m * d) (d + 2 * L + 3) t + 3 ≤ W := by
    change _ ≤ B + guardedRationalShapeBudget B B B B + 3
    omega
  have hdim : d ≤ W ∧ k ≤ W ∧ m ≤ W ∧ L ≤ W ∧ p ≤ W ∧ k * d ≤ W ∧ m * d ≤ W := by
    omega
  have ht : t ≤ W := hB.2.2.2.2.2.2.2.2.trans hBW
  have hs : p + 2 ≤ W := by dsimp [W, basisHintColumnsWork]; omega
  have hLs : d + 2 * L + 3 ≤ W := hB.2.2.2.2.2.2.2.1.trans hBW
  have hc := (storedRingCoefficientRun_steps T D hT hD).trans
    (storedRingCoefficientBudget_mono hdim.1 hdim.2.1 hdim.2.2.1 hdim.2.2.2.1)
  have hp := (hintPrecisionRun_steps m d p).trans
    (hintPrecisionBudget_mono hdim.2.2.1 hdim.1 hdim.2.2.2.2.1)
  have hshape := (guardedRationalShapeRun_steps (Nat.mul_pos hk hd) t Q w hw hQ hw').trans
    (guardedRationalShapeBudget_mono hdim.2.2.2.2.2.1 hdim.2.2.2.2.2.2 hLs ht)
  have hsample (j : Fin k) :
      (coefficientShapeSampleRun (m * d) d (guardedRationalShapeRun t Q w).value (p + 2) (tape j)).steps ≤
        coefficientShapeSampleBudget W W W W :=
    (coefficientShapeSampleRun_steps_le hd _ (guardedRationalShapeRun_posDef (Nat.mul_pos hk hd) t Q w hw)
      (guardedRationalShapeRun_bits (Nat.mul_pos hk hd) t Q w hw hQ hw') (p + 2) (tape j)).trans
        (coefficientShapeSampleBudget_mono hdim.2.2.2.2.2.2 hSW hdim.1 hs)
  have hcols := (costedVectorOfFn_steps_le _ _ hsample).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_right _ hdim.2.1) 1)
  change (hintPrecisionRun m d p).steps + (storedRingCoefficientRun T D).steps +
    (guardedRationalShapeRun t Q w).steps +
    (costedVectorOfFn (fun j => coefficientShapeSampleRun (m * d) d
      (guardedRationalShapeRun t Q w).value (p + 2) (tape j))).steps + 1 ≤ _
  change _ ≤ hintPrecisionBudget W W W + storedRingCoefficientBudget W W W W +
    guardedRationalShapeBudget W W W W + W * (coefficientShapeSampleBudget W W W W + 3) + 2
  omega

theorem basisHintColumnsRun_polynomial : ∃ C e : ℕ, ∀ (d k m : ℕ), 0 < d → 0 < k →
    ∀ (T : BasisMultiplicationData d) (D : GaussianColumnData (k * d) m) (w : ℚ), w ≠ 0 →
    ∀ (p : ℕ) (tape : BasisHintColumnsTape T D w p), (basisHintColumnsRun T D w p tape).steps ≤
      C * (d + k + m + basisMultiplicationBits T + gaussianColumnsBits D + rationalMagnitudeBits w + p + 1) ^ e := by
  obtain ⟨C, e, h⟩ := basisHintColumnsBudget_polynomial.exists_mul_pow_bound
  refine ⟨C, e, fun d k m hd hk T D w hw p tape => ?_⟩
  let L := basisMultiplicationBits T + gaussianColumnsBits D + rationalMagnitudeBits w
  have ht : ∀ t i j, (basisMultiplicationEntry T t i j).natAbs.size ≤ L := fun t i j =>
    (basisMultiplicationEntry_bits T t i j).trans (by dsimp [L]; omega)
  have hD : ∀ j i, (gaussianColumnsOfData D j i).natAbs.size ≤ L := fun j i =>
    (gaussianColumns_entry_bits D j i).trans (by dsimp [L]; omega)
  exact (basisHintColumnsRun_steps hd hk T D ht hD w hw (show rationalMagnitudeBits w ≤ L by dsimp [L]; omega) p tape).trans
    ((basisHintColumnsBudget_mono (by omega) (by omega) (by omega) (by dsimp [L]; omega) (by omega)).trans
      (h (d + k + m + basisMultiplicationBits T + gaussianColumnsBits D + rationalMagnitudeBits w + p)))

theorem basisHintColumnsRun_output_bits {d k m L : ℕ} (hd : 0 < d) (hk : 0 < k)
    (T : BasisMultiplicationData d) (D : GaussianColumnData (k * d) m)
    (hT : ∀ t i j, (basisMultiplicationEntry T t i j).natAbs.size ≤ L)
    (hD : ∀ j i, (gaussianColumnsOfData D j i).natAbs.size ≤ L)
    (w : ℚ) (hw : w ≠ 0) (hwbits : rationalMagnitudeBits w ≤ L) (p : ℕ)
    (tape : BasisHintColumnsTape T D w p) (j : Fin k) (i : Fin (m * d)) :
    (gaussianColumnsOfData (basisHintColumnsRun T D w p tape).value j i).natAbs.size ≤
      (m * d) * gaussianAdaptiveGrowth (m * d)
        (gaussianCovarianceBits (m * d) (coefficientCovarianceBits (m * d)
          (guardedRationalShapeBudget (k * d) (m * d) (d + 2 * L + 3)
            (gaussianShapeBits (m * d) 0 (p + 1)) + 3) d)) (p + 2) := by
  rw [basisHintColumnsRun_coordinates]
  exact guardedHintColumnRun_output_bits (Nat.mul_pos hk hd) d _ _ hd _ w hw
    (storedRingCoefficientRun_bits T D hT hD) (hwbits.trans (by omega)) (tape j) i

noncomputable section

def basisHintColumnsTapeLaw {d k m : ℕ} (T : BasisMultiplicationData d)
    (D : GaussianColumnData (k * d) m) (w : ℚ) (p : ℕ) : PMF (BasisHintColumnsTape T D w p) :=
  independentProduct (fun _ : Fin k => gaussianAdaptiveTapeLaw (gaussianCovarianceData (m * d)
    (coefficientCovarianceRun (m * d) d (guardedRationalShapeRun (hintPrecisionRun m d p).value.shapingBits
      (storedRingCoefficientRun T D).value w).value).value) (hintPrecisionRun m d p).value.samplingBits)

def basisHintColumnsRunLaw {d k m : ℕ} (T : BasisMultiplicationData d)
    (D : GaussianColumnData (k * d) m) (w : ℚ) (p : ℕ) : PMF (Fin k → Coeff (m * d)) :=
  (basisHintColumnsTapeLaw T D w p).map (fun tape => gaussianColumnsOfData (basisHintColumnsRun T D w p tape).value)

theorem basisHintColumnsRun_law {d k m : ℕ} (T : BasisMultiplicationData d)
    (D : GaussianColumnData (k * d) m) (w : ℚ) (p : ℕ) :
    basisHintColumnsRunLaw T D w p = independentProduct (fun _ : Fin k =>
      guardedHintColumnLaw d (gaussianShapeBits (m * d) 0 (p + 1)) (p + 2) (storedRingCoefficientRun T D).value w) := by
  rw [basisHintColumnsRunLaw]
  simp only [basisHintColumnsRun_coordinates, basisHintColumnsTapeLaw, guardedHintColumnLaw, hintPrecisionRun_value]
  let Q := (storedRingCoefficientRun T D).value
  let t := gaussianShapeBits (m * d) 0 (p + 1)
  let data := gaussianCovarianceData (m * d)
    (coefficientCovarianceRun (m * d) d (guardedRationalShapeRun t Q w).value).value
  exact independentProduct_map (fun _ : Fin k => gaussianAdaptiveTapeLaw data (p + 2))
    (fun _ (tape : GaussianAdaptiveTape data (p + 2)) =>
      (guardedHintColumnRun d t (p + 2) Q w tape).value.get)

end

/-- The preimage tapes depend on the stored initial draw through its computed shape. -/
abbrev GaussianHintTape {d : ℕ} (T : BasisMultiplicationData d) (a b k m s : ℕ) (w : ℚ) (p : ℕ) :=
  (initial : InitialGaussianTape a b d k m s) ×
    BasisHintColumnsTape T (initialGaussianRun a b d k m s initial).value w p

/-- Complete finite generation of the two ring-coordinate blocks used by the reduction. -/
def gaussianHintRun {d : ℕ} (T : BasisMultiplicationData d) (a b k m s : ℕ) (w : ℚ) (p : ℕ)
    (tape : GaussianHintTape T a b k m s w p) :
    Costed (GaussianColumnData (k * d) m × GaussianColumnData (m * d) k) :=
  let initial := initialGaussianRun a b d k m s tape.1
  let columns := basisHintColumnsRun T initial.value w p tape.2
  ⟨(initial.value, columns.value), initial.steps + columns.steps + 1⟩

theorem gaussianHintRun_value {d : ℕ} (T : BasisMultiplicationData d) (a b k m s : ℕ) (w : ℚ) (p : ℕ)
    (tape : GaussianHintTape T a b k m s w p) :
    (gaussianHintRun T a b k m s w p tape).value =
      ((initialGaussianRun a b d k m s tape.1).value,
        (basisHintColumnsRun T (initialGaussianRun a b d k m s tape.1).value w p tape.2).value) := rfl

def gaussianHintBudget (d k m L I s p : ℕ) : ℕ :=
  10 ^ 37 * (I + s + 1) ^ 7 + basisHintColumnsBudget d k m (L + 352 * (I + s + 1)) p + 1

theorem gaussianHintRun_steps {a b d L : ℕ} (T : BasisMultiplicationData d)
    (hT : ∀ t i j, (basisMultiplicationEntry T t i j).natAbs.size ≤ L)
    (ha : 0 < a) (hb : 0 < b) (hd : 0 < d) (k m s : ℕ) (hk : 0 < k)
    (w : ℚ) (hw : w ≠ 0) (hwbits : rationalMagnitudeBits w ≤ L) (p : ℕ)
    (tape : GaussianHintTape T a b k m s w p) :
    (gaussianHintRun T a b k m s w p tape).steps ≤
      gaussianHintBudget d k m L (initialGaussianSamplingSize a b d k m) s p := by
  have hi := initialGaussianRun_polynomial_bound ha hb hd k m s tape.1
  have ht : ∀ t i j, (basisMultiplicationEntry T t i j).natAbs.size ≤
      L + 352 * (initialGaussianSamplingSize a b d k m + s + 1) := fun t i j =>
    (hT t i j).trans (by omega)
  have hc := basisHintColumnsRun_steps hd hk T (initialGaussianRun a b d k m s tape.1).value ht
    (fun j i => (initialGaussianRun_output_size a b d k m s tape.1 j i).trans (by omega))
    w hw (hwbits.trans (by omega)) p tape.2
  exact Nat.add_le_add_right (Nat.add_le_add hi hc) 1

theorem gaussianHintBudget_mono {d d' k k' m m' L L' I I' s s' p p' : ℕ}
    (hd : d ≤ d') (hk : k ≤ k') (hm : m ≤ m') (hL : L ≤ L') (hI : I ≤ I') (hs : s ≤ s') (hp : p ≤ p') :
    gaussianHintBudget d k m L I s p ≤ gaussianHintBudget d' k' m' L' I' s' p' := by
  unfold gaussianHintBudget
  apply Nat.add_le_add_right
  apply Nat.add_le_add
  · gcongr
  · apply basisHintColumnsBudget_mono hd hk hm (by omega) hp

theorem gaussianHintBudget_polynomial : PolynomialCostBound (fun t => gaussianHintBudget t t t t t t t) := by
  have hp : PolynomialCostBound (fun t =>
      basisHintColumnsBudget t t t (t + 352 * (t + t + 1)) t) :=
    (polynomialCostBound_comp_mono basisHintColumnsBudget_polynomial
      (PolynomialCostBound.id.add ((PolynomialCostBound.const 352).mul
        ((PolynomialCostBound.id.add PolynomialCostBound.id).add (PolynomialCostBound.const 1))))
      (fun _ _ h => basisHintColumnsBudget_mono h h h h h)).mono
        (fun t => basisHintColumnsBudget_mono (by omega) (by omega) (by omega) le_rfl (by omega))
  exact (((PolynomialCostBound.const (10 ^ 37)).mul
    (((PolynomialCostBound.id.add PolynomialCostBound.id).add (PolynomialCostBound.const 1)).pow 7)).add hp).add
      (PolynomialCostBound.const 1)

theorem gaussianHintRun_polynomial : ∃ C e : ℕ, ∀ (d : ℕ) (T : BasisMultiplicationData d)
    (a b : ℕ), 0 < a → 0 < b → 0 < d → ∀ (k m s : ℕ), 0 < k → ∀ w : ℚ, w ≠ 0 →
    ∀ (p : ℕ) (tape : GaussianHintTape T a b k m s w p), (gaussianHintRun T a b k m s w p tape).steps ≤
      C * (d + k + m + basisMultiplicationBits T + rationalMagnitudeBits w +
        initialGaussianSamplingSize a b d k m + s + p + 1) ^ e := by
  obtain ⟨C, e, h⟩ := gaussianHintBudget_polynomial.exists_mul_pow_bound
  refine ⟨C, e, fun d T a b ha hb hd k m s hk w hw p tape => ?_⟩
  have ht : ∀ t i j, (basisMultiplicationEntry T t i j).natAbs.size ≤
      basisMultiplicationBits T + rationalMagnitudeBits w := fun t i j =>
    (basisMultiplicationEntry_bits T t i j).trans (by omega)
  exact (gaussianHintRun_steps T ht ha hb hd k m s hk w hw (by omega) p tape).trans
    ((gaussianHintBudget_mono (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans
      (h (d + k + m + basisMultiplicationBits T + rationalMagnitudeBits w +
        initialGaussianSamplingSize a b d k m + s + p)))

noncomputable section

/-- Actual independent finite words conditional on the stored initial draw. -/
def gaussianHintTapeLaw {d : ℕ} (T : BasisMultiplicationData d) (a b k m s : ℕ) (w : ℚ) (p : ℕ) :
    PMF (GaussianHintTape T a b k m s w p) :=
  (gaussianColumnTapeLaw (initialGaussianData a b d) (k * d) m s).bind fun initial =>
    (basisHintColumnsTapeLaw T (initialGaussianRun a b d k m s initial).value w p).map (Sigma.mk initial)

def gaussianHintRunLaw {d : ℕ} (T : BasisMultiplicationData d) (a b k m s : ℕ) (w : ℚ) (p : ℕ) :
    PMF (GaussianColumnData (k * d) m × GaussianColumnData (m * d) k) :=
  (gaussianHintTapeLaw T a b k m s w p).map (fun tape => (gaussianHintRun T a b k m s w p tape).value)

/-- The stored initial block is retained jointly with the conditional preimage columns. -/
theorem gaussianHintRunLaw_eq {d : ℕ} (T : BasisMultiplicationData d) (a b k m s : ℕ) (w : ℚ) (p : ℕ) :
    gaussianHintRunLaw T a b k m s w p =
      (gaussianColumnTapeLaw (initialGaussianData a b d) (k * d) m s).bind fun initial =>
        (basisHintColumnsTapeLaw T (initialGaussianRun a b d k m s initial).value w p).map
          (fun columns => ((initialGaussianRun a b d k m s initial).value,
            (basisHintColumnsRun T (initialGaussianRun a b d k m s initial).value w p columns).value)) := by
  simp only [gaussianHintRunLaw, gaussianHintTapeLaw, PMF.map_bind, PMF.map_comp,
    Function.comp_def, gaussianHintRun_value]

end

/-- Coefficient bit bound for a finite sample from a stored rational shape. -/
def coefficientHintOutputSize (N L d s : ℕ) : ℕ :=
  N * gaussianAdaptiveGrowth N (gaussianCovarianceBits N (coefficientCovarianceBits N L d)) s

theorem coefficientHintOutputSize_mono {N N' L L' d d' s s' : ℕ}
    (hN : N ≤ N') (hL : L ≤ L') (hd : d ≤ d') (hs : s ≤ s') :
    coefficientHintOutputSize N L d s ≤ coefficientHintOutputSize N' L' d' s' := by
  have hg := gaussianCovarianceBits_mono hN (coefficientCovarianceBits_mono hN hL hd)
  apply Nat.mul_le_mul hN
  unfold gaussianAdaptiveGrowth
  omega

theorem coefficientHintOutputSize_polynomial :
    PolynomialCostBound (fun t => coefficientHintOutputSize t t t t) := by
  have hc := PolynomialCostBound.id.add coefficientCovarianceBits_polynomial
  have hg : PolynomialCostBound (fun t => gaussianCovarianceBits t (coefficientCovarianceBits t t t)) :=
    (polynomialCostBound_comp_mono gaussianCovarianceBits_polynomial hc
      (fun _ _ h => gaussianCovarianceBits_mono h h)).mono
        (fun t => gaussianCovarianceBits_mono (by omega) (by omega))
  exact PolynomialCostBound.id.mul
    (((PolynomialCostBound.id.add ((PolynomialCostBound.const 4).mul hg)).add
      ((PolynomialCostBound.const 2).mul
        ((PolynomialCostBound.id.add PolynomialCostBound.id).add (PolynomialCostBound.const 12)))).add
          (PolynomialCostBound.const 10))

def basisHintColumnsOutputBudget (d k m L p : ℕ) : ℕ :=
  let W := basisHintColumnsWork d k m L p
  coefficientHintOutputSize W W W W

theorem basisHintColumnsOutputBudget_mono {d d' k k' m m' L L' p p' : ℕ}
    (hd : d ≤ d') (hk : k ≤ k') (hm : m ≤ m') (hL : L ≤ L') (hp : p ≤ p') :
    basisHintColumnsOutputBudget d k m L p ≤ basisHintColumnsOutputBudget d' k' m' L' p' := by
  have h := basisHintColumnsWork_mono hd hk hm hL hp
  exact coefficientHintOutputSize_mono h h h h

theorem basisHintColumnsOutputBudget_polynomial :
    PolynomialCostBound (fun t => basisHintColumnsOutputBudget t t t t t) :=
  polynomialCostBound_comp_mono (f := fun t => coefficientHintOutputSize t t t t)
    (g := fun t => basisHintColumnsWork t t t t t)
    coefficientHintOutputSize_polynomial basisHintColumnsWork_polynomial
    (fun _ _ h => coefficientHintOutputSize_mono h h h h)

theorem basisHintColumnsRun_output_budget {d k m L : ℕ} (hd : 0 < d) (hk : 0 < k)
    (T : BasisMultiplicationData d) (D : GaussianColumnData (k * d) m)
    (hT : ∀ t i j, (basisMultiplicationEntry T t i j).natAbs.size ≤ L)
    (hD : ∀ j i, (gaussianColumnsOfData D j i).natAbs.size ≤ L)
    (w : ℚ) (hw : w ≠ 0) (hwbits : rationalMagnitudeBits w ≤ L) (p : ℕ)
    (tape : BasisHintColumnsTape T D w p) (j : Fin k) (i : Fin (m * d)) :
    (gaussianColumnsOfData (basisHintColumnsRun T D w p tape).value j i).natAbs.size ≤
      basisHintColumnsOutputBudget d k m L p := by
  let t := gaussianShapeBits (m * d) 0 (p + 1)
  let B := basisHintColumnsBase d k m L p
  let W := basisHintColumnsWork d k m L p
  have hP : k * d ≤ B := by dsimp [B, basisHintColumnsBase]; omega
  have hN : m * d ≤ B := by dsimp [B, basisHintColumnsBase]; omega
  have hL : d + 2 * L + 3 ≤ B := by dsimp [B, basisHintColumnsBase]; omega
  have ht : t ≤ B := by dsimp [B, basisHintColumnsBase, t]; omega
  have hS := guardedRationalShapeBudget_mono hP hN hL ht
  have hBW : B ≤ W := by dsimp [W, basisHintColumnsWork]; omega
  have hSW : guardedRationalShapeBudget (k * d) (m * d) (d + 2 * L + 3) t + 3 ≤ W := by
    change _ ≤ B + guardedRationalShapeBudget B B B B + 3
    omega
  have hdW : d ≤ W := (show d ≤ B by dsimp [B, basisHintColumnsBase]; omega).trans hBW
  have hsW : p + 2 ≤ W := by
    have hp : p ≤ B := by dsimp [B, basisHintColumnsBase]; omega
    change p + 2 ≤ B + guardedRationalShapeBudget B B B B + 3
    omega
  exact (basisHintColumnsRun_output_bits hd hk T D hT hD w hw hwbits p tape j i).trans
    (coefficientHintOutputSize_mono (hN.trans hBW) hSW hdW hsW)

theorem basisHintColumnsRun_output_polynomial : ∃ C e : ℕ, ∀ (d k m : ℕ), 0 < d → 0 < k →
    ∀ (T : BasisMultiplicationData d) (D : GaussianColumnData (k * d) m) (w : ℚ), w ≠ 0 →
    ∀ (p : ℕ) (tape : BasisHintColumnsTape T D w p) (j : Fin k) (i : Fin (m * d)),
      (gaussianColumnsOfData (basisHintColumnsRun T D w p tape).value j i).natAbs.size ≤
        C * (d + k + m + basisMultiplicationBits T + gaussianColumnsBits D + rationalMagnitudeBits w + p + 1) ^ e := by
  obtain ⟨C, e, h⟩ := basisHintColumnsOutputBudget_polynomial.exists_mul_pow_bound
  refine ⟨C, e, fun d k m hd hk T D w hw p tape j i => ?_⟩
  let L := basisMultiplicationBits T + gaussianColumnsBits D + rationalMagnitudeBits w
  have ht : ∀ t i j, (basisMultiplicationEntry T t i j).natAbs.size ≤ L := fun t i j =>
    (basisMultiplicationEntry_bits T t i j).trans (by dsimp [L]; omega)
  have hD : ∀ j i, (gaussianColumnsOfData D j i).natAbs.size ≤ L := fun j i =>
    (gaussianColumns_entry_bits D j i).trans (by dsimp [L]; omega)
  exact (basisHintColumnsRun_output_budget hd hk T D ht hD w hw
    (show rationalMagnitudeBits w ≤ L by dsimp [L]; omega) p tape j i).trans
      ((basisHintColumnsOutputBudget_mono (by omega) (by omega) (by omega) (by dsimp [L]; omega) (by omega)).trans
        (h (d + k + m + basisMultiplicationBits T + gaussianColumnsBits D + rationalMagnitudeBits w + p)))

def gaussianHintOutputBudget (d k m L I s p : ℕ) : ℕ :=
  basisHintColumnsOutputBudget d k m (L + 352 * (I + s + 1)) p

theorem gaussianHintRun_output_bits {d L : ℕ} (T : BasisMultiplicationData d)
    (hT : ∀ t i j, (basisMultiplicationEntry T t i j).natAbs.size ≤ L)
    (hd : 0 < d) (a b k m s : ℕ) (hk : 0 < k)
    (w : ℚ) (hw : w ≠ 0) (hwbits : rationalMagnitudeBits w ≤ L) (p : ℕ)
    (tape : GaussianHintTape T a b k m s w p) (j : Fin k) (i : Fin (m * d)) :
    (gaussianColumnsOfData (gaussianHintRun T a b k m s w p tape).value.2 j i).natAbs.size ≤
      gaussianHintOutputBudget d k m L (initialGaussianSamplingSize a b d k m) s p :=
  basisHintColumnsRun_output_budget hd hk T (initialGaussianRun a b d k m s tape.1).value
    (fun t i j => (hT t i j).trans (by omega))
    (fun j i => (initialGaussianRun_output_size a b d k m s tape.1 j i).trans (by omega))
    w hw (hwbits.trans (by omega)) p tape.2 j i

theorem gaussianHintOutputBudget_mono {d d' k k' m m' L L' I I' s s' p p' : ℕ}
    (hd : d ≤ d') (hk : k ≤ k') (hm : m ≤ m') (hL : L ≤ L') (hI : I ≤ I') (hs : s ≤ s') (hp : p ≤ p') :
    gaussianHintOutputBudget d k m L I s p ≤ gaussianHintOutputBudget d' k' m' L' I' s' p' :=
  basisHintColumnsOutputBudget_mono hd hk hm (by omega) hp

theorem gaussianHintOutputBudget_polynomial :
    PolynomialCostBound (fun t => gaussianHintOutputBudget t t t t t t t) :=
  (polynomialCostBound_comp_mono basisHintColumnsOutputBudget_polynomial
    (PolynomialCostBound.id.add ((PolynomialCostBound.const 352).mul
      ((PolynomialCostBound.id.add PolynomialCostBound.id).add (PolynomialCostBound.const 1))))
    (fun _ _ h => basisHintColumnsOutputBudget_mono h h h h h)).mono
      (fun t => basisHintColumnsOutputBudget_mono (by omega) (by omega) (by omega) le_rfl (by omega))

theorem gaussianHintRun_output_polynomial : ∃ C e : ℕ, ∀ (d : ℕ) (T : BasisMultiplicationData d)
    (a b : ℕ), 0 < d → ∀ (k m s : ℕ), 0 < k → ∀ w : ℚ, w ≠ 0 →
    ∀ (p : ℕ) (tape : GaussianHintTape T a b k m s w p) (j : Fin k) (i : Fin (m * d)),
      (gaussianColumnsOfData (gaussianHintRun T a b k m s w p tape).value.2 j i).natAbs.size ≤
        C * (d + k + m + basisMultiplicationBits T + rationalMagnitudeBits w +
          initialGaussianSamplingSize a b d k m + s + p + 1) ^ e := by
  obtain ⟨C, e, h⟩ := gaussianHintOutputBudget_polynomial.exists_mul_pow_bound
  refine ⟨C, e, fun d T a b hd k m s hk w hw p tape j i => ?_⟩
  have ht : ∀ t i j, (basisMultiplicationEntry T t i j).natAbs.size ≤
      basisMultiplicationBits T + rationalMagnitudeBits w := fun t i j =>
    (basisMultiplicationEntry_bits T t i j).trans (by omega)
  exact (gaussianHintRun_output_bits T ht hd a b k m s hk w hw (by omega) p tape j i).trans
    ((gaussianHintOutputBudget_mono (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans
      (h (d + k + m + basisMultiplicationBits T + rationalMagnitudeBits w +
        initialGaussianSamplingSize a b d k m + s + p)))


/-- Store integer columns while accumulating the cost of every entry. -/
def storedColumnsOfFn {R m : ℕ} (f : Fin m → Fin R → Costed ℤ) : Costed (GaussianColumnData R m) :=
  costedVectorOfFn (fun j => costedVectorOfFn (f j))

theorem storedColumnsOfFn_value {R m : ℕ} (f : Fin m → Fin R → Costed ℤ) :
    gaussianColumnsOfData (storedColumnsOfFn f).value = fun j i => (f j i).value := by
  funext j i
  simp [storedColumnsOfFn, costedVectorOfFn_value, gaussianColumnsOfData, Vector.get]

theorem storedColumnsOfFn_steps {R m B : ℕ} (f : Fin m → Fin R → Costed ℤ)
    (hf : ∀ j i, (f j i).steps ≤ B) :
    (storedColumnsOfFn f).steps ≤ rationalRectTraversalBudget m R B :=
  costedVectorOfFn_steps_le _ _ (fun j => costedVectorOfFn_steps_le _ B (hf j))

/-- Apply the stored integer numerators of a rational matrix to integer columns. -/
def storedNumeratorPairRun {R S m : ℕ} (Q : RationalRectData R S)
    (D : GaussianColumnData S m) (j : Fin m) (i : Fin R) (l : Fin S) : Costed (ℤ × ℤ) :=
  let a := (rationalRectMatrixOfData Q i l).num
  let b := gaussianColumnsOfData D j l
  ⟨(a, b), a.natAbs.size + b.natAbs.size + 3⟩

def storedNumeratorApplyEntryRun {R S m : ℕ} (Q : RationalRectData R S)
    (D : GaussianColumnData S m) (j : Fin m) (i : Fin R) : Costed ℤ :=
  let pairs := costedVectorOfFn (storedNumeratorPairRun Q D j i)
  let dot := costedIntegerDot pairs.value.toList
  ⟨dot.value, pairs.steps + (S + 1) + dot.steps + 1⟩

def storedNumeratorApplyRun {R S m : ℕ} (Q : RationalRectData R S)
    (D : GaussianColumnData S m) : Costed (GaussianColumnData R m) :=
  storedColumnsOfFn (storedNumeratorApplyEntryRun Q D)

theorem storedNumeratorApplyRun_value {R S m : ℕ} (Q : RationalRectData R S)
    (D : GaussianColumnData S m) :
    gaussianColumnsOfData (storedNumeratorApplyRun Q D).value =
      fun j i => ∑ l, (rationalRectMatrixOfData Q i l).num * gaussianColumnsOfData D j l := by
  rw [storedNumeratorApplyRun, storedColumnsOfFn_value]
  funext j i
  simp [storedNumeratorApplyEntryRun, costedVectorOfFn_value, costedIntegerDot_value,
    integerListDot, Vector.toList_ofFn, storedNumeratorPairRun, List.sum_ofFn]

def storedNumeratorEntryBudget (S L : ℕ) : ℕ :=
  S * (2 * L + 6) + 1 + (S + 1) + (S * integerDotStepBudget S L + 1) + 1

theorem storedNumeratorApplyEntryRun_bounds {R S m L : ℕ} (Q : RationalRectData R S)
    (D : GaussianColumnData S m)
    (hQ : ∀ i l, (rationalRectMatrixOfData Q i l).num.natAbs.size ≤ L)
    (hD : ∀ j l, (gaussianColumnsOfData D j l).natAbs.size ≤ L) (j : Fin m) (i : Fin R) :
    (storedNumeratorApplyEntryRun Q D j i).steps ≤ storedNumeratorEntryBudget S L ∧
    (storedNumeratorApplyEntryRun Q D j i).value.natAbs.size ≤ S + 2 * L + 1 := by
  let pairs := costedVectorOfFn (storedNumeratorPairRun Q D j i)
  have hpairs : ∀ x ∈ pairs.value.toList, x.1.natAbs.size ≤ L ∧ x.2.natAbs.size ≤ L := by
    intro x hx
    simp only [pairs, costedVectorOfFn_value, Vector.toList_ofFn, List.mem_ofFn] at hx
    obtain ⟨l, rfl⟩ := hx
    exact ⟨hQ i l, hD j l⟩
  have hdot := costedIntegerDot_steps_le pairs.value.toList L hpairs
  have hbits := integerListDot_size_le pairs.value.toList L hpairs
  simp only [Vector.length_toList] at hdot hbits
  have hp : pairs.steps ≤ S * (2 * L + 6) + 1 := by
    apply costedVectorOfFn_steps_le _ (2 * L + 3)
    intro l
    have ha := hQ i l
    have hb := hD j l
    dsimp only [storedNumeratorPairRun]
    omega
  constructor
  · change pairs.steps + (S + 1) + (costedIntegerDot pairs.value.toList).steps + 1 ≤ _
    unfold storedNumeratorEntryBudget
    omega
  · change (costedIntegerDot pairs.value.toList).value.natAbs.size ≤ _
    rwa [costedIntegerDot_value]

/-- Matrix multiplication in the supplied integral basis, on stored coefficients. -/
def storedRingMulRun {d r s t : ℕ} (T : BasisMultiplicationData d)
    (A : GaussianColumnData (r * d) s) (B : GaussianColumnData (s * d) t) :
    Costed (GaussianColumnData (r * d) t) :=
  let Q := storedRingCoefficientRun T A
  let product := storedNumeratorApplyRun Q.value B
  ⟨product.value, Q.steps + product.steps + 1⟩

theorem storedRingMulRun_coordinates {d r s t : ℕ} (T : BasisMultiplicationData d)
    (A : GaussianColumnData (r * d) s) (B : GaussianColumnData (s * d) t) :
    gaussianColumnsOfData (storedRingMulRun T A B).value =
      fun j => (storedRingCoefficientMatrix T A).mulVec (gaussianColumnsOfData B j) := by
  change gaussianColumnsOfData (storedNumeratorApplyRun (storedRingCoefficientRun T A).value B).value = _
  rw [storedNumeratorApplyRun_value, storedRingCoefficientRun_value]
  simp only [integerRationalMatrix]
  rfl

def storedRingMulBudget (d r s t L : ℕ) : ℕ :=
  storedRingCoefficientBudget d r s L +
    rationalRectTraversalBudget t (r * d) (storedNumeratorEntryBudget (s * d) (d + 2 * L + 1)) + 1

def storedRingMulBits (d s L : ℕ) : ℕ := s * d + 2 * (d + 2 * L + 1) + 1

theorem storedRingMulRun_bounds {d r s t L : ℕ} (T : BasisMultiplicationData d)
    (A : GaussianColumnData (r * d) s) (B : GaussianColumnData (s * d) t)
    (hT : ∀ u i l, (basisMultiplicationEntry T u i l).natAbs.size ≤ L)
    (hA : ∀ j i, (gaussianColumnsOfData A j i).natAbs.size ≤ L)
    (hB : ∀ j i, (gaussianColumnsOfData B j i).natAbs.size ≤ L) :
    (storedRingMulRun T A B).steps ≤ storedRingMulBudget d r s t L ∧
    ∀ j i, (gaussianColumnsOfData (storedRingMulRun T A B).value j i).natAbs.size ≤ storedRingMulBits d s L := by
  have hq : ∀ i l, (rationalRectMatrixOfData (storedRingCoefficientRun T A).value i l).num.natAbs.size ≤
      d + 2 * L + 1 := by
    intro i l
    rw [storedRingCoefficientRun_value]
    simpa [integerRationalMatrix] using storedRingCoefficientMatrix_bits T A hT hA i l
  have hb : ∀ j i, (gaussianColumnsOfData B j i).natAbs.size ≤ d + 2 * L + 1 :=
    fun j i => (hB j i).trans (by omega)
  have hentry := storedNumeratorApplyEntryRun_bounds (storedRingCoefficientRun T A).value B hq hb
  constructor
  · have hs := storedColumnsOfFn_steps _ (fun j i => (hentry j i).1)
    exact Nat.add_le_add_right (Nat.add_le_add (storedRingCoefficientRun_steps T A hT hA) hs) 1
  · intro j i
    change (gaussianColumnsOfData (storedNumeratorApplyRun _ _).value j i).natAbs.size ≤ _
    rw [storedNumeratorApplyRun, storedColumnsOfFn_value]
    exact (hentry j i).2

theorem storedRingMulBudget_mono {d d' r r' s s' t t' L L' : ℕ}
    (hd : d ≤ d') (hr : r ≤ r') (hs : s ≤ s') (ht : t ≤ t') (hL : L ≤ L') :
    storedRingMulBudget d r s t L ≤ storedRingMulBudget d' r' s' t' L' := by
  unfold storedRingMulBudget
  apply Nat.add_le_add_right
  apply Nat.add_le_add (storedRingCoefficientBudget_mono hd hr hs hL)
  unfold rationalRectTraversalBudget storedNumeratorEntryBudget integerDotStepBudget
  gcongr

theorem storedRingMulBudget_polynomial : PolynomialCostBound (fun t => storedRingMulBudget t t t t t) := by
  have hpoly : PolynomialCostBound (fun t =>
      rationalRectTraversalBudget t (t * t) (storedNumeratorEntryBudget (t * t) (t + 2 * t + 1))) := by
    let x : Polynomial ℕ := Polynomial.X
    let L := x + 2 * x + 1
    let entry := x * x * (2 * L + 6) + 1 + (x * x + 1) +
      (x * x * ((2 * L + 1) ^ 2 + x * x + 4 * L + 4) + 1) + 1
    refine ⟨x * (x * x * (entry + 3) + 4) + 1, ?_⟩
    intro t
    apply le_of_eq
    simp [rationalRectTraversalBudget, storedNumeratorEntryBudget, integerDotStepBudget, entry, L, x]
  exact (storedRingCoefficientBudget_polynomial.add hpoly).add (PolynomialCostBound.const 1)

theorem storedRingMulRun_polynomial : ∃ C e : ℕ, ∀ (d r s t : ℕ) (T : BasisMultiplicationData d)
    (A : GaussianColumnData (r * d) s) (B : GaussianColumnData (s * d) t),
    (storedRingMulRun T A B).steps ≤
      C * (d + r + s + t + basisMultiplicationBits T + gaussianColumnsBits A + gaussianColumnsBits B + 1) ^ e := by
  obtain ⟨C, e, h⟩ := storedRingMulBudget_polynomial.exists_mul_pow_bound
  refine ⟨C, e, fun d r s t T A B => ?_⟩
  let L := basisMultiplicationBits T + gaussianColumnsBits A + gaussianColumnsBits B
  have ht : ∀ u i l, (basisMultiplicationEntry T u i l).natAbs.size ≤ L := fun u i l =>
    (basisMultiplicationEntry_bits T u i l).trans (by dsimp [L]; omega)
  have ha : ∀ j i, (gaussianColumnsOfData A j i).natAbs.size ≤ L := fun j i =>
    (gaussianColumns_entry_bits A j i).trans (by dsimp [L]; omega)
  have hb : ∀ j i, (gaussianColumnsOfData B j i).natAbs.size ≤ L := fun j i =>
    (gaussianColumns_entry_bits B j i).trans (by dsimp [L]; omega)
  simpa only [L, Nat.add_assoc] using (storedRingMulRun_bounds T A B ht ha hb).1.trans
    ((storedRingMulBudget_mono (d' := d + r + s + t + L) (r' := d + r + s + t + L)
      (s' := d + r + s + t + L) (t' := d + r + s + t + L) (L' := d + r + s + t + L)
      (by omega) (by omega) (by omega) (by omega) (by omega)).trans
      (h (d + r + s + t + L)))

section RingSemantics
variable {O : Type*} [CommRing O] {d r s t : ℕ}

theorem decodedCoefficientMatrix_ext (b : Basis (Fin d) ℤ O)
    (A : GaussianColumnData (r * d) s) (M : Matrix (Fin r) (Fin s) O)
    (h : ∀ j i, gaussianColumnsOfData A j i = ringPowerCoordinates b r (fun l => M l j) i) :
    decodedCoefficientMatrix b A = M := by
  ext i j
  have hc : gaussianColumnsOfData A j = ringPowerCoordinates b r (fun l => M l j) := funext (h j)
  simp only [decodedCoefficientMatrix, hc, LinearEquiv.symm_apply_apply]

theorem storedRingMulRun_correct (T : BasisMultiplicationData d) (b : Basis (Fin d) ℤ O)
    (hT : T.Represents b) (A : GaussianColumnData (r * d) s) (B : GaussianColumnData (s * d) t) :
    decodedCoefficientMatrix b (storedRingMulRun T A B).value =
      decodedCoefficientMatrix b A * decodedCoefficientMatrix b B := by
  apply decodedCoefficientMatrix_ext
  intro j i
  rw [storedRingMulRun_coordinates, storedRingCoefficientMatrix_correct T b hT]
  have hc : gaussianColumnsOfData B j = ringPowerCoordinates b s (fun l => decodedCoefficientMatrix b B l j) := by
    change _ = ringPowerCoordinates b s ((ringPowerCoordinates b s).symm _)
    rw [LinearEquiv.apply_symm_apply]
  dsimp only
  rw [hc]
  exact congrFun (ringCoefficientMatrix_map b (decodedCoefficientMatrix b A)
    (fun l => decodedCoefficientMatrix b B l j)) i

end RingSemantics

/-- A conservative charge for the fixed number of index divisions, products and sums. -/
def storedRingIndexBudget (d r s : ℕ) : ℕ := 10 * (d + r + s + r * d + s * d + 1) ^ 2 + 10

/-- Copy a transposed ring entry without changing its basis-coordinate order. -/
def storedRingTransposeEntryRun {d r s : ℕ} (A : GaussianColumnData (r * d) s)
    (j : Fin r) (i : Fin (s * d)) : Costed ℤ :=
  let row := finProdFinEquiv.symm i
  let x := gaussianColumnsOfData A row.1 (finProdFinEquiv (j, row.2))
  ⟨x, storedRingIndexBudget d r s + x.natAbs.size + 1⟩

def storedRingTransposeRun {d r s : ℕ} (A : GaussianColumnData (r * d) s) :
    Costed (GaussianColumnData (s * d) r) :=
  storedColumnsOfFn (storedRingTransposeEntryRun A)

theorem storedRingTransposeRun_coordinates {d r s : ℕ} (A : GaussianColumnData (r * d) s)
    (j : Fin r) (i : Fin s) (l : Fin d) :
    gaussianColumnsOfData (storedRingTransposeRun A).value j (finProdFinEquiv (i, l)) =
      gaussianColumnsOfData A i (finProdFinEquiv (j, l)) := by
  rw [storedRingTransposeRun, storedColumnsOfFn_value]
  simp [storedRingTransposeEntryRun]

def storedColumnsAddRun {R m : ℕ} (A B : GaussianColumnData R m) : Costed (GaussianColumnData R m) :=
  storedColumnsOfFn (fun j i => costedIntAdd (gaussianColumnsOfData A j i) (gaussianColumnsOfData B j i))

def storedColumnsSubRun {R m : ℕ} (A B : GaussianColumnData R m) : Costed (GaussianColumnData R m) :=
  storedColumnsOfFn (fun j i => costedIntSub (gaussianColumnsOfData A j i) (gaussianColumnsOfData B j i))

def storedColumnsNegRun {R m : ℕ} (A : GaussianColumnData R m) : Costed (GaussianColumnData R m) :=
  storedColumnsOfFn (fun j i =>
    let x := gaussianColumnsOfData A j i
    ⟨-x, x.natAbs.size + 1⟩)

def storedRingIdentityRun {d : ℕ} (one : Vector ℤ d) (r : ℕ) : Costed (GaussianColumnData (r * d) r) :=
  storedColumnsOfFn (fun j i =>
    let row := finProdFinEquiv.symm i
    let x := if row.1 = j then one.get row.2 else 0
    ⟨x, storedRingIndexBudget d r r + x.natAbs.size + 1⟩)

/-- Concatenate ring-matrix columns in the same order as `finSumFinEquiv`. -/
def storedColumnsAppendRun {R m n : ℕ} (A : GaussianColumnData R m) (B : GaussianColumnData R n) :
    Costed (GaussianColumnData R (m + n)) :=
  storedColumnsOfFn (fun j i =>
    let x := Sum.elim (fun a => gaussianColumnsOfData A a i)
      (fun b => gaussianColumnsOfData B b i) (finSumFinEquiv.symm j)
    ⟨x, 10 * (m + n + 1) ^ 2 + x.natAbs.size + 1⟩)

theorem storedColumnsAddRun_coordinates {R m : ℕ} (A B : GaussianColumnData R m) :
    gaussianColumnsOfData (storedColumnsAddRun A B).value = gaussianColumnsOfData A + gaussianColumnsOfData B := by
  rw [storedColumnsAddRun, storedColumnsOfFn_value]
  rfl

theorem storedColumnsSubRun_coordinates {R m : ℕ} (A B : GaussianColumnData R m) :
    gaussianColumnsOfData (storedColumnsSubRun A B).value = gaussianColumnsOfData A - gaussianColumnsOfData B := by
  rw [storedColumnsSubRun, storedColumnsOfFn_value]
  rfl

theorem storedColumnsNegRun_coordinates {R m : ℕ} (A : GaussianColumnData R m) :
    gaussianColumnsOfData (storedColumnsNegRun A).value = -gaussianColumnsOfData A := by
  rw [storedColumnsNegRun, storedColumnsOfFn_value]
  rfl

theorem storedRingIdentityRun_coordinates {d : ℕ} (one : Vector ℤ d) (r : ℕ)
    (j i : Fin r) (l : Fin d) :
    gaussianColumnsOfData (storedRingIdentityRun one r).value j (finProdFinEquiv (i, l)) =
      if i = j then one.get l else 0 := by
  rw [storedRingIdentityRun, storedColumnsOfFn_value]
  simp only [Equiv.symm_apply_apply]

theorem storedColumnsAppendRun_coordinates {R m n : ℕ}
    (A : GaussianColumnData R m) (B : GaussianColumnData R n) (j : Fin (m + n)) (i : Fin R) :
    gaussianColumnsOfData (storedColumnsAppendRun A B).value j i =
      Sum.elim (fun a => gaussianColumnsOfData A a i)
        (fun b => gaussianColumnsOfData B b i) (finSumFinEquiv.symm j) := by
  rw [storedColumnsAppendRun, storedColumnsOfFn_value]

def storedRingTransposeBudget (d r s L : ℕ) : ℕ :=
  rationalRectTraversalBudget r (s * d) (storedRingIndexBudget d r s + L + 1)

theorem storedRingTransposeRun_bounds {d r s L : ℕ} (A : GaussianColumnData (r * d) s)
    (hA : ∀ j i, (gaussianColumnsOfData A j i).natAbs.size ≤ L) :
    (storedRingTransposeRun A).steps ≤ storedRingTransposeBudget d r s L ∧
    ∀ j i, (gaussianColumnsOfData (storedRingTransposeRun A).value j i).natAbs.size ≤ L := by
  constructor
  · apply storedColumnsOfFn_steps
    intro j i
    dsimp only [storedRingTransposeEntryRun]
    exact Nat.add_le_add_right (Nat.add_le_add_left (hA _ _) _) 1
  · intro j i
    obtain ⟨⟨row, l⟩, rfl⟩ := finProdFinEquiv.surjective i
    rw [storedRingTransposeRun_coordinates]
    exact hA _ _

theorem storedColumnsAddRun_bounds {R m L : ℕ} (A B : GaussianColumnData R m)
    (hA : ∀ j i, (gaussianColumnsOfData A j i).natAbs.size ≤ L)
    (hB : ∀ j i, (gaussianColumnsOfData B j i).natAbs.size ≤ L) :
    (storedColumnsAddRun A B).steps ≤ rationalRectTraversalBudget m R (2 * L + 1) ∧
    ∀ j i, (gaussianColumnsOfData (storedColumnsAddRun A B).value j i).natAbs.size ≤ L + 2 := by
  constructor
  · apply storedColumnsOfFn_steps
    intro j i
    have ha := hA j i
    have hb := hB j i
    dsimp only [costedIntAdd, integerOperandBits]
    omega
  · intro j i
    rw [storedColumnsAddRun_coordinates]
    simpa only [Pi.add_apply, sub_neg_eq_add] using
      integer_sub_size_le (gaussianColumnsOfData A j i) (-gaussianColumnsOfData B j i) L
        (hA j i) (by simpa using hB j i)

theorem storedColumnsSubRun_bounds {R m L : ℕ} (A B : GaussianColumnData R m)
    (hA : ∀ j i, (gaussianColumnsOfData A j i).natAbs.size ≤ L)
    (hB : ∀ j i, (gaussianColumnsOfData B j i).natAbs.size ≤ L) :
    (storedColumnsSubRun A B).steps ≤ rationalRectTraversalBudget m R (2 * L + 1) ∧
    ∀ j i, (gaussianColumnsOfData (storedColumnsSubRun A B).value j i).natAbs.size ≤ L + 2 := by
  constructor
  · apply storedColumnsOfFn_steps
    intro j i
    have ha := hA j i
    have hb := hB j i
    dsimp only [costedIntSub, integerOperandBits]
    omega
  · intro j i
    rw [storedColumnsSubRun_coordinates]
    exact integer_sub_size_le _ _ L (hA j i) (hB j i)

theorem storedColumnsNegRun_bounds {R m L : ℕ} (A : GaussianColumnData R m)
    (hA : ∀ j i, (gaussianColumnsOfData A j i).natAbs.size ≤ L) :
    (storedColumnsNegRun A).steps ≤ rationalRectTraversalBudget m R (L + 1) ∧
    ∀ j i, (gaussianColumnsOfData (storedColumnsNegRun A).value j i).natAbs.size ≤ L := by
  constructor
  · apply storedColumnsOfFn_steps
    intro j i
    exact Nat.add_le_add_right (hA j i) 1
  · intro j i
    simpa [storedColumnsNegRun_coordinates] using hA j i

theorem storedRingIdentityRun_bounds {d L : ℕ} (one : Vector ℤ d) (r : ℕ)
    (hOne : ∀ l, (one.get l).natAbs.size ≤ L) :
    (storedRingIdentityRun one r).steps ≤
      rationalRectTraversalBudget r (r * d) (storedRingIndexBudget d r r + L + 1) ∧
    ∀ j i, (gaussianColumnsOfData (storedRingIdentityRun one r).value j i).natAbs.size ≤ L := by
  have hx (j : Fin r) (i : Fin (r * d)) :
      (if (finProdFinEquiv.symm i).1 = j then one.get (finProdFinEquiv.symm i).2 else 0).natAbs.size ≤ L := by
    split_ifs
    · exact hOne _
    · simp
  constructor
  · apply storedColumnsOfFn_steps
    intro j i
    exact Nat.add_le_add_right (Nat.add_le_add_left (hx j i) _) 1
  · intro j i
    rw [storedRingIdentityRun, storedColumnsOfFn_value]
    exact hx j i

theorem storedColumnsAppendRun_bounds {R m n L : ℕ} (A : GaussianColumnData R m) (B : GaussianColumnData R n)
    (hA : ∀ j i, (gaussianColumnsOfData A j i).natAbs.size ≤ L)
    (hB : ∀ j i, (gaussianColumnsOfData B j i).natAbs.size ≤ L) :
    (storedColumnsAppendRun A B).steps ≤ rationalRectTraversalBudget (m + n) R (10 * (m + n + 1) ^ 2 + L + 1) ∧
    ∀ j i, (gaussianColumnsOfData (storedColumnsAppendRun A B).value j i).natAbs.size ≤ L := by
  have hx (j : Fin (m + n)) (i : Fin R) :
      (Sum.elim (fun a => gaussianColumnsOfData A a i)
        (fun b => gaussianColumnsOfData B b i) (finSumFinEquiv.symm j)).natAbs.size ≤ L := by
    cases finSumFinEquiv.symm j with
    | inl a => exact hA a i
    | inr b => exact hB b i
  constructor
  · apply storedColumnsOfFn_steps
    intro j i
    exact Nat.add_le_add_right (Nat.add_le_add_left (hx j i) _) 1
  · intro j i
    rw [storedColumnsAppendRun_coordinates]
    exact hx j i

section RingBlockSemantics
variable {O : Type*} [CommRing O] {d r s t : ℕ}

theorem storedRingTransposeRun_correct (b : Basis (Fin d) ℤ O) (A : GaussianColumnData (r * d) s) :
    decodedCoefficientMatrix b (storedRingTransposeRun A).value = (decodedCoefficientMatrix b A).transpose := by
  ext i j
  apply b.equivFun.injective
  funext l
  rw [decodedCoefficientMatrix_coordinates, storedRingTransposeRun_coordinates]
  exact (decodedCoefficientMatrix_coordinates b A j i l).symm

theorem storedColumnsAddRun_correct (b : Basis (Fin d) ℤ O) (A B : GaussianColumnData (r * d) s) :
    decodedCoefficientMatrix b (storedColumnsAddRun A B).value = decodedCoefficientMatrix b A + decodedCoefficientMatrix b B := by
  ext i j
  apply b.equivFun.injective
  funext l
  simp only [decodedCoefficientMatrix_coordinates, storedColumnsAddRun_coordinates,
    Matrix.add_apply, map_add, Pi.add_apply, decodedCoefficientMatrix_coordinates]

theorem storedColumnsSubRun_correct (b : Basis (Fin d) ℤ O) (A B : GaussianColumnData (r * d) s) :
    decodedCoefficientMatrix b (storedColumnsSubRun A B).value = decodedCoefficientMatrix b A - decodedCoefficientMatrix b B := by
  ext i j
  apply b.equivFun.injective
  funext l
  simp only [decodedCoefficientMatrix_coordinates, storedColumnsSubRun_coordinates,
    Matrix.sub_apply, map_sub, Pi.sub_apply, decodedCoefficientMatrix_coordinates]

theorem storedColumnsNegRun_correct (b : Basis (Fin d) ℤ O) (A : GaussianColumnData (r * d) s) :
    decodedCoefficientMatrix b (storedColumnsNegRun A).value = -decodedCoefficientMatrix b A := by
  ext i j
  apply b.equivFun.injective
  funext l
  simp only [decodedCoefficientMatrix_coordinates, storedColumnsNegRun_coordinates,
    Matrix.neg_apply, map_neg, Pi.neg_apply, decodedCoefficientMatrix_coordinates]

theorem storedRingIdentityRun_correct (b : Basis (Fin d) ℤ O) (one : Vector ℤ d)
    (hOne : ∀ l, one.get l = b.equivFun 1 l) (r : ℕ) :
    decodedCoefficientMatrix b (storedRingIdentityRun one r).value = 1 := by
  ext i j
  apply b.equivFun.injective
  funext l
  rw [decodedCoefficientMatrix_coordinates, storedRingIdentityRun_coordinates]
  change (if i = j then one.get l else 0) = b.equivFun (if i = j then 1 else 0) l
  by_cases h : i = j
  · simp [h, hOne]
  · simp [h]

theorem storedColumnsAppendRun_correct (b : Basis (Fin d) ℤ O)
    (A : GaussianColumnData (r * d) s) (B : GaussianColumnData (r * d) t) :
    decodedCoefficientMatrix b (storedColumnsAppendRun A B).value =
      (Matrix.fromCols (decodedCoefficientMatrix b A) (decodedCoefficientMatrix b B)).submatrix id finSumFinEquiv.symm := by
  ext i j
  apply b.equivFun.injective
  funext l
  rw [decodedCoefficientMatrix_coordinates, storedColumnsAppendRun_coordinates]
  cases h : finSumFinEquiv.symm j with
  | inl a => simpa [Matrix.submatrix, Matrix.fromCols, h] using (decodedCoefficientMatrix_coordinates b A i a l).symm
  | inr c => simpa [Matrix.submatrix, Matrix.fromCols, h] using (decodedCoefficientMatrix_coordinates b B i c l).symm

end RingBlockSemantics

/-- Construct the actual integer hint matrix supplied to the adversary. -/
def storedColumnHintsRun {d k m : ℕ} (T : BasisMultiplicationData d) (one : Vector ℤ d)
    (X : GaussianColumnData (k * d) m) (R : GaussianColumnData (m * d) k) :
    Costed (GaussianColumnData ((m + k) * d) k) :=
  let product := storedRingMulRun T X R
  let identity := storedRingIdentityRun one k
  let lower := storedColumnsAddRun product.value identity.value
  let rows := storedColumnsAppendRun X lower.value
  let columns := storedRingTransposeRun rows.value
  ⟨columns.value, product.steps + identity.steps + lower.steps + rows.steps + columns.steps + 5⟩

/-- Construct `[-I-XᵀRᵀ, Xᵀ]` in the exact coordinate order of the reduction. -/
def storedExtractionMatrixRun {d k m : ℕ} (T : BasisMultiplicationData d) (one : Vector ℤ d)
    (X : GaussianColumnData (k * d) m) (R : GaussianColumnData (m * d) k) :
    Costed (GaussianColumnData (m * d) (m + k)) :=
  let xt := storedRingTransposeRun X
  let rt := storedRingTransposeRun R
  let product := storedRingMulRun T xt.value rt.value
  let identity := storedRingIdentityRun one m
  let negative := storedColumnsNegRun identity.value
  let left := storedColumnsSubRun negative.value product.value
  let result := storedColumnsAppendRun left.value xt.value
  ⟨result.value, xt.steps + rt.steps + product.steps + identity.steps + negative.steps + left.steps + result.steps + 7⟩

def storedColumnHintsBudget (d k m L : ℕ) : ℕ :=
  let V := storedRingMulBits d m L
  storedRingMulBudget d k m k L +
    rationalRectTraversalBudget k (k * d) (storedRingIndexBudget d k k + L + 1) +
    rationalRectTraversalBudget k (k * d) (2 * V + 1) +
    rationalRectTraversalBudget (m + k) (k * d) (10 * (m + k + 1) ^ 2 + (V + 2) + 1) +
    storedRingTransposeBudget d k (m + k) (V + 2) + 5

def storedExtractionMatrixBudget (d k m L : ℕ) : ℕ :=
  let V := storedRingMulBits d k L
  storedRingTransposeBudget d k m L + storedRingTransposeBudget d m k L +
    storedRingMulBudget d m k m L +
    rationalRectTraversalBudget m (m * d) (storedRingIndexBudget d m m + L + 1) +
    rationalRectTraversalBudget m (m * d) (L + 1) +
    rationalRectTraversalBudget m (m * d) (2 * V + 1) +
    rationalRectTraversalBudget (m + k) (m * d) (10 * (m + k + 1) ^ 2 + (V + 2) + 1) + 7

theorem storedColumnHintsRun_bounds {d k m L : ℕ} (T : BasisMultiplicationData d) (one : Vector ℤ d)
    (X : GaussianColumnData (k * d) m) (R : GaussianColumnData (m * d) k)
    (hT : ∀ t i l, (basisMultiplicationEntry T t i l).natAbs.size ≤ L)
    (hOne : ∀ l, (one.get l).natAbs.size ≤ L)
    (hX : ∀ j i, (gaussianColumnsOfData X j i).natAbs.size ≤ L)
    (hR : ∀ j i, (gaussianColumnsOfData R j i).natAbs.size ≤ L) :
    (storedColumnHintsRun T one X R).steps ≤ storedColumnHintsBudget d k m L ∧
    ∀ j i, (gaussianColumnsOfData (storedColumnHintsRun T one X R).value j i).natAbs.size ≤
      storedRingMulBits d m L + 2 := by
  let V := storedRingMulBits d m L
  have hLV : L ≤ V := by dsimp [V, storedRingMulBits]; omega
  have hp := storedRingMulRun_bounds T X R hT hX hR
  have hi := storedRingIdentityRun_bounds one k hOne
  have hl := storedColumnsAddRun_bounds _ _ hp.2 (fun j i => (hi.2 j i).trans hLV)
  have hr := storedColumnsAppendRun_bounds X _
    (fun j i => (hX j i).trans (hLV.trans (by omega))) hl.2
  have hc := storedRingTransposeRun_bounds _ hr.2
  constructor
  · exact Nat.add_le_add_right
      (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hp.1 hi.1) hl.1) hr.1) hc.1) 5
  · exact hc.2

theorem storedExtractionMatrixRun_bounds {d k m L : ℕ} (T : BasisMultiplicationData d) (one : Vector ℤ d)
    (X : GaussianColumnData (k * d) m) (R : GaussianColumnData (m * d) k)
    (hT : ∀ t i l, (basisMultiplicationEntry T t i l).natAbs.size ≤ L)
    (hOne : ∀ l, (one.get l).natAbs.size ≤ L)
    (hX : ∀ j i, (gaussianColumnsOfData X j i).natAbs.size ≤ L)
    (hR : ∀ j i, (gaussianColumnsOfData R j i).natAbs.size ≤ L) :
    (storedExtractionMatrixRun T one X R).steps ≤ storedExtractionMatrixBudget d k m L ∧
    ∀ j i, (gaussianColumnsOfData (storedExtractionMatrixRun T one X R).value j i).natAbs.size ≤
      storedRingMulBits d k L + 2 := by
  let V := storedRingMulBits d k L
  have hLV : L ≤ V := by dsimp [V, storedRingMulBits]; omega
  have hx := storedRingTransposeRun_bounds X hX
  have hr := storedRingTransposeRun_bounds R hR
  have hp := storedRingMulRun_bounds T _ _ hT hx.2 hr.2
  have hi := storedRingIdentityRun_bounds one m hOne
  have hn := storedColumnsNegRun_bounds _ hi.2
  have hl := storedColumnsSubRun_bounds _ _ (fun j i => (hn.2 j i).trans hLV) hp.2
  have ha := storedColumnsAppendRun_bounds _ _ hl.2
    (fun j i => (hx.2 j i).trans (hLV.trans (by omega)))
  constructor
  · exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
      (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hx.1 hr.1) hp.1) hi.1) hn.1) hl.1) ha.1) 7
  · exact ha.2

section ReductionMatrixSemantics
variable {O : Type*} [CommRing O] {d k m : ℕ}

theorem storedColumnHintsRun_correct (T : BasisMultiplicationData d) (b : Basis (Fin d) ℤ O)
    (hT : T.Represents b) (one : Vector ℤ d) (hOne : ∀ l, one.get l = b.equivFun 1 l)
    (X : GaussianColumnData (k * d) m) (R : GaussianColumnData (m * d) k) :
    decodedCoefficientMatrix b (storedColumnHintsRun T one X R).value =
      (columnHints (decodedCoefficientMatrix b X) (decodedCoefficientMatrix b R)).submatrix finSumFinEquiv.symm id := by
  simp only [storedColumnHintsRun, storedRingTransposeRun_correct, storedColumnsAppendRun_correct,
    storedColumnsAddRun_correct, storedRingMulRun_correct T b hT, storedRingIdentityRun_correct b one hOne]
  rfl

theorem storedExtractionMatrixRun_correct (T : BasisMultiplicationData d) (b : Basis (Fin d) ℤ O)
    (hT : T.Represents b) (one : Vector ℤ d) (hOne : ∀ l, one.get l = b.equivFun 1 l)
    (X : GaussianColumnData (k * d) m) (R : GaussianColumnData (m * d) k) :
    decodedCoefficientMatrix b (storedExtractionMatrixRun T one X R).value =
      (extractionMatrix (decodedCoefficientMatrix b X) (decodedCoefficientMatrix b R)).submatrix id finSumFinEquiv.symm := by
  simp only [storedExtractionMatrixRun, storedColumnsAppendRun_correct, storedColumnsSubRun_correct,
    storedColumnsNegRun_correct, storedRingIdentityRun_correct b one hOne,
    storedRingMulRun_correct T b hT, storedRingTransposeRun_correct]
  simp only [extractionMatrix, kernelColumns, Matrix.transpose_fromRows,
    Matrix.transpose_sub, Matrix.transpose_neg, Matrix.transpose_one, Matrix.transpose_mul]

end ReductionMatrixSemantics

theorem storedColumnHintsBudget_mono {d d' k k' m m' L L' : ℕ}
    (hd : d ≤ d') (hk : k ≤ k') (hm : m ≤ m') (hL : L ≤ L') :
    storedColumnHintsBudget d k m L ≤ storedColumnHintsBudget d' k' m' L' := by
  unfold storedColumnHintsBudget storedRingTransposeBudget storedRingMulBits storedRingIndexBudget
    storedRingMulBudget storedRingCoefficientBudget storedRingCoefficientEntryBudget
    storedCoefficientPairBudget rationalRectTraversalBudget storedNumeratorEntryBudget integerDotStepBudget
  dsimp only
  gcongr

theorem storedExtractionMatrixBudget_mono {d d' k k' m m' L L' : ℕ}
    (hd : d ≤ d') (hk : k ≤ k') (hm : m ≤ m') (hL : L ≤ L') :
    storedExtractionMatrixBudget d k m L ≤ storedExtractionMatrixBudget d' k' m' L' := by
  unfold storedExtractionMatrixBudget storedRingTransposeBudget storedRingMulBits storedRingIndexBudget
    storedRingMulBudget storedRingCoefficientBudget storedRingCoefficientEntryBudget
    storedCoefficientPairBudget rationalRectTraversalBudget storedNumeratorEntryBudget integerDotStepBudget
  dsimp only
  gcongr

theorem storedColumnHintsBudget_polynomial : PolynomialCostBound (fun t => storedColumnHintsBudget t t t t) := by
  have hrest : PolynomialCostBound (fun t =>
      rationalRectTraversalBudget t (t * t) (storedRingIndexBudget t t t + t + 1) +
      rationalRectTraversalBudget t (t * t) (2 * storedRingMulBits t t t + 1) +
      rationalRectTraversalBudget (t + t) (t * t) (10 * (t + t + 1) ^ 2 + (storedRingMulBits t t t + 2) + 1) +
      storedRingTransposeBudget t t (t + t) (storedRingMulBits t t t + 2) + 5) := by
    let x : Polynomial ℕ := Polynomial.X
    let I := 10 * (x + x + x + x * x + x * x + 1) ^ 2 + 10
    let J := 10 * (x + x + (x + x) + x * x + (x + x) * x + 1) ^ 2 + 10
    let V := x * x + 2 * (x + 2 * x + 1) + 1
    refine ⟨(x * (x * x * (I + x + 1 + 3) + 4) + 1) +
      (x * (x * x * (2 * V + 1 + 3) + 4) + 1) +
      ((x + x) * (x * x * (10 * (x + x + 1) ^ 2 + (V + 2) + 1 + 3) + 4) + 1) +
      (x * ((x + x) * x * (J + (V + 2) + 1 + 3) + 4) + 1) + 5, ?_⟩
    intro t
    apply le_of_eq
    simp [rationalRectTraversalBudget, storedRingTransposeBudget, storedRingIndexBudget,
      storedRingMulBits, I, J, V, x]
  exact (storedRingMulBudget_polynomial.add hrest).mono (fun t => by
    unfold storedColumnHintsBudget
    dsimp only
    omega)

theorem storedExtractionMatrixBudget_polynomial : PolynomialCostBound (fun t => storedExtractionMatrixBudget t t t t) := by
  have hrest : PolynomialCostBound (fun t =>
      storedRingTransposeBudget t t t t + storedRingTransposeBudget t t t t +
      rationalRectTraversalBudget t (t * t) (storedRingIndexBudget t t t + t + 1) +
      rationalRectTraversalBudget t (t * t) (t + 1) +
      rationalRectTraversalBudget t (t * t) (2 * storedRingMulBits t t t + 1) +
      rationalRectTraversalBudget (t + t) (t * t) (10 * (t + t + 1) ^ 2 + (storedRingMulBits t t t + 2) + 1) + 7) := by
    let x : Polynomial ℕ := Polynomial.X
    let I := 10 * (x + x + x + x * x + x * x + 1) ^ 2 + 10
    let V := x * x + 2 * (x + 2 * x + 1) + 1
    let idCost := x * (x * x * (I + x + 1 + 3) + 4) + 1
    refine ⟨idCost + idCost + idCost + (x * (x * x * (x + 1 + 3) + 4) + 1) +
      (x * (x * x * (2 * V + 1 + 3) + 4) + 1) +
      ((x + x) * (x * x * (10 * (x + x + 1) ^ 2 + (V + 2) + 1 + 3) + 4) + 1) + 7, ?_⟩
    intro t
    apply le_of_eq
    simp [rationalRectTraversalBudget, storedRingTransposeBudget, storedRingIndexBudget,
      storedRingMulBits, idCost, I, V, x]
  exact (storedRingMulBudget_polynomial.add hrest).mono (fun t => by
    unfold storedExtractionMatrixBudget
    dsimp only
    omega)

def storedUnitBits {d : ℕ} (one : Vector ℤ d) : ℕ := ∑ l, (one.get l).natAbs.size

theorem storedUnit_entry_bits {d : ℕ} (one : Vector ℤ d) (l : Fin d) :
    (one.get l).natAbs.size ≤ storedUnitBits one :=
  Finset.single_le_sum (fun i _ => Nat.zero_le (one.get i).natAbs.size) (Finset.mem_univ l)

def storedReductionInputSize {d k m : ℕ} (T : BasisMultiplicationData d) (one : Vector ℤ d)
    (X : GaussianColumnData (k * d) m) (R : GaussianColumnData (m * d) k) : ℕ :=
  d + k + m + basisMultiplicationBits T + storedUnitBits one + gaussianColumnsBits X + gaussianColumnsBits R

theorem storedReductionInputSize_bounds {d k m : ℕ} (T : BasisMultiplicationData d) (one : Vector ℤ d)
    (X : GaussianColumnData (k * d) m) (R : GaussianColumnData (m * d) k) :
    let L := storedReductionInputSize T one X R
    d ≤ L ∧ k ≤ L ∧ m ≤ L ∧
    (∀ t i l, (basisMultiplicationEntry T t i l).natAbs.size ≤ L) ∧
    (∀ l, (one.get l).natAbs.size ≤ L) ∧
    (∀ j i, (gaussianColumnsOfData X j i).natAbs.size ≤ L) ∧
    (∀ j i, (gaussianColumnsOfData R j i).natAbs.size ≤ L) := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold storedReductionInputSize; omega
  · unfold storedReductionInputSize; omega
  · unfold storedReductionInputSize; omega
  · intro t i l
    exact (basisMultiplicationEntry_bits T t i l).trans (by unfold storedReductionInputSize; omega)
  · intro l
    exact (storedUnit_entry_bits one l).trans (by unfold storedReductionInputSize; omega)
  · intro j i
    exact (gaussianColumns_entry_bits X j i).trans (by unfold storedReductionInputSize; omega)
  · intro j i
    exact (gaussianColumns_entry_bits R j i).trans (by unfold storedReductionInputSize; omega)

theorem storedColumnHintsRun_polynomial : ∃ C e : ℕ, ∀ (d k m : ℕ) (T : BasisMultiplicationData d)
    (one : Vector ℤ d) (X : GaussianColumnData (k * d) m) (R : GaussianColumnData (m * d) k),
    (storedColumnHintsRun T one X R).steps ≤ C * (storedReductionInputSize T one X R + 1) ^ e := by
  obtain ⟨C, e, h⟩ := storedColumnHintsBudget_polynomial.exists_mul_pow_bound
  refine ⟨C, e, fun d k m T one X R => ?_⟩
  obtain ⟨hd, hk, hm, ht, ho, hx, hr⟩ := storedReductionInputSize_bounds T one X R
  exact (storedColumnHintsRun_bounds T one X R ht ho hx hr).1.trans
    ((storedColumnHintsBudget_mono hd hk hm le_rfl).trans (h _))

theorem storedExtractionMatrixRun_polynomial : ∃ C e : ℕ, ∀ (d k m : ℕ) (T : BasisMultiplicationData d)
    (one : Vector ℤ d) (X : GaussianColumnData (k * d) m) (R : GaussianColumnData (m * d) k),
    (storedExtractionMatrixRun T one X R).steps ≤ C * (storedReductionInputSize T one X R + 1) ^ e := by
  obtain ⟨C, e, h⟩ := storedExtractionMatrixBudget_polynomial.exists_mul_pow_bound
  refine ⟨C, e, fun d k m T one X R => ?_⟩
  obtain ⟨hd, hk, hm, ht, ho, hx, hr⟩ := storedReductionInputSize_bounds T one X R
  exact (storedExtractionMatrixRun_bounds T one X R ht ho hx hr).1.trans
    ((storedExtractionMatrixBudget_mono hd hk hm le_rfl).trans (h _))

theorem storedColumnHintsRun_output_polynomial {d k m : ℕ} (T : BasisMultiplicationData d)
    (one : Vector ℤ d) (X : GaussianColumnData (k * d) m) (R : GaussianColumnData (m * d) k) (j i) :
    (gaussianColumnsOfData (storedColumnHintsRun T one X R).value j i).natAbs.size ≤
      12 * (storedReductionInputSize T one X R + 1) ^ 2 := by
  obtain ⟨hd, hk, hm, ht, ho, hx, hr⟩ := storedReductionInputSize_bounds T one X R
  apply (storedColumnHintsRun_bounds T one X R ht ho hx hr).2 j i |>.trans
  unfold storedRingMulBits
  have hp := Nat.mul_le_mul hm hd
  nlinarith

theorem storedExtractionMatrixRun_output_polynomial {d k m : ℕ} (T : BasisMultiplicationData d)
    (one : Vector ℤ d) (X : GaussianColumnData (k * d) m) (R : GaussianColumnData (m * d) k) (j i) :
    (gaussianColumnsOfData (storedExtractionMatrixRun T one X R).value j i).natAbs.size ≤
      12 * (storedReductionInputSize T one X R + 1) ^ 2 := by
  obtain ⟨hd, hk, hm, ht, ho, hx, hr⟩ := storedReductionInputSize_bounds T one X R
  apply (storedExtractionMatrixRun_bounds T one X R ht ho hx hr).2 j i |>.trans
  unfold storedRingMulBits
  have hp := Nat.mul_le_mul hk hd
  nlinarith

/-- Reduce every stored integer coefficient to its canonical nonnegative residue. -/
def storedColumnsModRun {R m : ℕ} (q : ℕ) (A : GaussianColumnData R m) : Costed (GaussianColumnData R m) :=
  storedColumnsOfFn (fun j i =>
    let a := gaussianColumnsOfData A j i
    ⟨a % (q : ℤ), (a.natAbs.size + q.size + 1) ^ 2 + 1⟩)

theorem storedColumnsModRun_coordinates {R m : ℕ} (q : ℕ) (A : GaussianColumnData R m) :
    gaussianColumnsOfData (storedColumnsModRun q A).value = fun j i => gaussianColumnsOfData A j i % (q : ℤ) := by
  rw [storedColumnsModRun, storedColumnsOfFn_value]

theorem storedColumnsModRun_steps {R m L : ℕ} (q : ℕ) (A : GaussianColumnData R m)
    (hA : ∀ j i, (gaussianColumnsOfData A j i).natAbs.size ≤ L) :
    (storedColumnsModRun q A).steps ≤ rationalRectTraversalBudget m R ((L + q.size + 1) ^ 2 + 1) := by
  apply storedColumnsOfFn_steps
  intro j i
  dsimp only
  gcongr
  exact hA j i

theorem storedColumnsModRun_range {R m : ℕ} {q : ℕ} (hq : 0 < q) (A : GaussianColumnData R m) (j i) :
    0 ≤ gaussianColumnsOfData (storedColumnsModRun q A).value j i ∧
    gaussianColumnsOfData (storedColumnsModRun q A).value j i < (q : ℤ) := by
  rw [storedColumnsModRun_coordinates]
  exact ⟨Int.emod_nonneg _ (by exact_mod_cast hq.ne'), Int.emod_lt_of_pos _ (by exact_mod_cast hq)⟩

theorem storedColumnsModRun_bits {R m : ℕ} {q : ℕ} (hq : 0 < q) (A : GaussianColumnData R m) (j i) :
    (gaussianColumnsOfData (storedColumnsModRun q A).value j i).natAbs.size ≤ q.size := by
  obtain ⟨hn, hq'⟩ := storedColumnsModRun_range hq A j i
  have ha : (gaussianColumnsOfData (storedColumnsModRun q A).value j i).natAbs ≤ q := by
    exact_mod_cast (show ((gaussianColumnsOfData (storedColumnsModRun q A).value j i).natAbs : ℤ) ≤ (q : ℤ) by
      rw [Int.natCast_natAbs, abs_of_nonneg hn]
      exact hq'.le)
  exact Nat.size_le_size ha

/-- Construct the public input from a supplied integral representative of the SIS challenge. -/
def storedPublicFromExtractionRun {d n m c : ℕ} (T : BasisMultiplicationData d) (q : ℕ)
    (B : GaussianColumnData (n * d) m) (E : GaussianColumnData (m * d) c) :
    Costed (GaussianColumnData (n * d) c) :=
  let product := storedRingMulRun T B E
  let reduced := storedColumnsModRun q product.value
  ⟨reduced.value, product.steps + reduced.steps + 2⟩

def storedPublicBudget (d n m c L Q : ℕ) : ℕ :=
  storedRingMulBudget d n m c L + rationalRectTraversalBudget c (n * d)
    ((storedRingMulBits d m L + Q + 1) ^ 2 + 1) + 2

theorem storedPublicFromExtractionRun_steps {d n m c L : ℕ} (T : BasisMultiplicationData d) (q : ℕ)
    (B : GaussianColumnData (n * d) m) (E : GaussianColumnData (m * d) c)
    (hT : ∀ t i l, (basisMultiplicationEntry T t i l).natAbs.size ≤ L)
    (hB : ∀ j i, (gaussianColumnsOfData B j i).natAbs.size ≤ L)
    (hE : ∀ j i, (gaussianColumnsOfData E j i).natAbs.size ≤ L) :
    (storedPublicFromExtractionRun T q B E).steps ≤ storedPublicBudget d n m c L q.size := by
  have hp := storedRingMulRun_bounds T B E hT hB hE
  exact Nat.add_le_add_right (Nat.add_le_add hp.1 (storedColumnsModRun_steps q _ hp.2)) 2

theorem storedPublicFromExtractionRun_bits {d n m c : ℕ} (T : BasisMultiplicationData d) {q : ℕ}
    (hq : 0 < q) (B : GaussianColumnData (n * d) m) (E : GaussianColumnData (m * d) c) (j i) :
    (gaussianColumnsOfData (storedPublicFromExtractionRun T q B E).value j i).natAbs.size ≤ q.size :=
  storedColumnsModRun_bits hq (storedRingMulRun T B E).value j i

theorem storedPublicBudget_mono {d d' n n' m m' c c' L L' Q Q' : ℕ}
    (hd : d ≤ d') (hn : n ≤ n') (hm : m ≤ m') (hc : c ≤ c') (hL : L ≤ L') (hQ : Q ≤ Q') :
    storedPublicBudget d n m c L Q ≤ storedPublicBudget d' n' m' c' L' Q' := by
  unfold storedPublicBudget
  apply Nat.add_le_add_right
  apply Nat.add_le_add (storedRingMulBudget_mono hd hn hm hc hL)
  unfold rationalRectTraversalBudget storedRingMulBits
  gcongr

theorem storedPublicBudget_polynomial : PolynomialCostBound (fun t => storedPublicBudget t t t t t t) := by
  have hrest : PolynomialCostBound (fun t => rationalRectTraversalBudget t (t * t)
      ((storedRingMulBits t t t + t + 1) ^ 2 + 1) + 2) := by
    let x : Polynomial ℕ := Polynomial.X
    refine ⟨x * (x * x * (((x * x + 2 * (x + 2 * x + 1) + 1 + x + 1) ^ 2 + 1) + 3) + 4) + 1 + 2, ?_⟩
    intro t
    apply le_of_eq
    simp [rationalRectTraversalBudget, storedRingMulBits, x]
  exact (storedRingMulBudget_polynomial.add hrest).mono (fun t => by unfold storedPublicBudget; omega)

theorem storedPublicFromExtractionRun_polynomial : ∃ C e : ℕ, ∀ (d n m c : ℕ)
    (T : BasisMultiplicationData d) (q : ℕ) (B : GaussianColumnData (n * d) m) (E : GaussianColumnData (m * d) c),
    (storedPublicFromExtractionRun T q B E).steps ≤
      C * (d + n + m + c + basisMultiplicationBits T + gaussianColumnsBits B + gaussianColumnsBits E + q.size + 1) ^ e := by
  obtain ⟨C, e, h⟩ := storedPublicBudget_polynomial.exists_mul_pow_bound
  refine ⟨C, e, fun d n m c T q B E => ?_⟩
  let U := d + n + m + c + basisMultiplicationBits T + gaussianColumnsBits B + gaussianColumnsBits E + q.size
  have ht : ∀ t i l, (basisMultiplicationEntry T t i l).natAbs.size ≤ U := fun t i l =>
    (basisMultiplicationEntry_bits T t i l).trans (by dsimp [U]; omega)
  have hb : ∀ j i, (gaussianColumnsOfData B j i).natAbs.size ≤ U := fun j i =>
    (gaussianColumns_entry_bits B j i).trans (by dsimp [U]; omega)
  have he : ∀ j i, (gaussianColumnsOfData E j i).natAbs.size ≤ U := fun j i =>
    (gaussianColumns_entry_bits E j i).trans (by dsimp [U]; omega)
  exact (storedPublicFromExtractionRun_steps T q B E ht hb he).trans
    ((storedPublicBudget_mono (d' := U) (n' := U) (m' := U) (c' := U) (L' := U) (Q' := U)
      (by dsimp [U]; omega) (by dsimp [U]; omega) (by dsimp [U]; omega)
      (by dsimp [U]; omega) le_rfl (by dsimp [U]; omega)).trans (h U))

section ResidueArithmeticSemantics
variable {O F : Type*} [CommRing O] [CommRing F] {d r s : ℕ}

theorem intCast_emod_of_modulus_zero (q : ℕ) (hq : (q : F) = 0) (a : ℤ) :
    ((a % (q : ℤ) : ℤ) : F) = (a : F) := by
  have h := congrArg (fun z : ℤ => (z : F)) (Int.mul_ediv_add_emod a (q : ℤ))
  simpa [hq] using h

/-- Coordinatewise integer remainders preserve the represented element in any quotient killing `q`. -/
theorem storedColumnsModRun_correct (b : Basis (Fin d) ℤ O) (f : O →+* F)
    (q : ℕ) (hq : (q : F) = 0) (A : GaussianColumnData (r * d) s) :
    (decodedCoefficientMatrix b (storedColumnsModRun q A).value).map f = (decodedCoefficientMatrix b A).map f := by
  ext i j
  change f (decodedCoefficientMatrix b (storedColumnsModRun q A).value i j) = f (decodedCoefficientMatrix b A i j)
  conv_lhs => rw [← b.sum_equivFun (decodedCoefficientMatrix b (storedColumnsModRun q A).value i j)]
  conv_rhs => rw [← b.sum_equivFun (decodedCoefficientMatrix b A i j)]
  simp only [map_sum, zsmul_eq_mul, map_mul, map_intCast, decodedCoefficientMatrix_coordinates,
    storedColumnsModRun_coordinates]
  apply Finset.sum_congr rfl
  intro l _
  rw [intCast_emod_of_modulus_zero q hq]

theorem storedPublicFromExtractionRun_correct {n m c : ℕ} (T : BasisMultiplicationData d)
    (b : Basis (Fin d) ℤ O) (hT : T.Represents b) (f : O →+* F) (q : ℕ) (hq : (q : F) = 0)
    (B : GaussianColumnData (n * d) m) (E : GaussianColumnData (m * d) c) :
    (decodedCoefficientMatrix b (storedPublicFromExtractionRun T q B E).value).map f =
      (decodedCoefficientMatrix b B * decodedCoefficientMatrix b E).map f := by
  change (decodedCoefficientMatrix b (storedColumnsModRun q (storedRingMulRun T B E).value).value).map f = _
  rw [storedColumnsModRun_correct b f q hq, storedRingMulRun_correct T b hT]

end ResidueArithmeticSemantics

/-- Canonical stored unit for an integral power basis whose first vector is one. -/
def storedPowerBasisOne (d : ℕ) : Vector ℤ d := Vector.ofFn (fun i => if i.val = 0 then 1 else 0)

theorem storedPowerBasisOne_bits (d : ℕ) (l : Fin d) : (storedPowerBasisOne d |>.get l).natAbs.size ≤ 1 := by
  simp only [storedPowerBasisOne, Vector.get, Vector.toArray_ofFn, Array.getElem_ofFn, Fin.val_cast]
  split_ifs <;> decide

theorem storedPowerBasisOne_correct {O : Type*} [CommRing O] {d : ℕ} (hd : 0 < d)
    (b : Basis (Fin d) ℤ O) (hb : b ⟨0, hd⟩ = 1) (l : Fin d) :
    (storedPowerBasisOne d).get l = b.equivFun 1 l := by
  rw [← hb, Basis.equivFun_self]
  simp [storedPowerBasisOne, Vector.get, Fin.ext_iff, eq_comm]

/-- Prepare the adversary's two inputs and retain the extraction matrix for its answer. -/
def storedReductionPreparationRun {d n k m : ℕ} (T : BasisMultiplicationData d) (one : Vector ℤ d) (q : ℕ)
    (B : GaussianColumnData (n * d) m) (X : GaussianColumnData (k * d) m) (R : GaussianColumnData (m * d) k) :
    Costed (GaussianColumnData ((m + k) * d) k ×
      GaussianColumnData (m * d) (m + k) × GaussianColumnData (n * d) (m + k)) :=
  let H := storedColumnHintsRun T one X R
  let E := storedExtractionMatrixRun T one X R
  let A := storedPublicFromExtractionRun T q B E.value
  ⟨(H.value, E.value, A.value), H.steps + E.steps + A.steps + 3⟩

def storedPreparationBudget (d n k m L Q : ℕ) : ℕ :=
  storedColumnHintsBudget d k m L + storedExtractionMatrixBudget d k m L +
    storedPublicBudget d n m (m + k) (L + (storedRingMulBits d k L + 2)) Q + 3

theorem storedReductionPreparationRun_steps {d n k m L : ℕ} (T : BasisMultiplicationData d) (one : Vector ℤ d)
    (q : ℕ) (B : GaussianColumnData (n * d) m) (X : GaussianColumnData (k * d) m) (R : GaussianColumnData (m * d) k)
    (hT : ∀ t i l, (basisMultiplicationEntry T t i l).natAbs.size ≤ L)
    (hOne : ∀ l, (one.get l).natAbs.size ≤ L)
    (hB : ∀ j i, (gaussianColumnsOfData B j i).natAbs.size ≤ L)
    (hX : ∀ j i, (gaussianColumnsOfData X j i).natAbs.size ≤ L)
    (hR : ∀ j i, (gaussianColumnsOfData R j i).natAbs.size ≤ L) :
    (storedReductionPreparationRun T one q B X R).steps ≤ storedPreparationBudget d n k m L q.size := by
  have hh := storedColumnHintsRun_bounds T one X R hT hOne hX hR
  have he := storedExtractionMatrixRun_bounds T one X R hT hOne hX hR
  have hp := storedPublicFromExtractionRun_steps T q B (storedExtractionMatrixRun T one X R).value
    (L := L + (storedRingMulBits d k L + 2))
    (fun t i l => (hT t i l).trans (by omega))
    (fun j i => (hB j i).trans (by omega))
    (fun j i => (he.2 j i).trans (by omega))
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add hh.1 he.1) hp) 3

theorem storedPreparationBudget_mono {d d' n n' k k' m m' L L' Q Q' : ℕ}
    (hd : d ≤ d') (hn : n ≤ n') (hk : k ≤ k') (hm : m ≤ m') (hL : L ≤ L') (hQ : Q ≤ Q') :
    storedPreparationBudget d n k m L Q ≤ storedPreparationBudget d' n' k' m' L' Q' := by
  unfold storedPreparationBudget
  apply Nat.add_le_add_right
  apply Nat.add_le_add (Nat.add_le_add (storedColumnHintsBudget_mono hd hk hm hL)
    (storedExtractionMatrixBudget_mono hd hk hm hL))
  apply storedPublicBudget_mono hd hn hm (Nat.add_le_add hm hk) _ hQ
  unfold storedRingMulBits
  gcongr

def storedPreparationWork (t : ℕ) : ℕ := 2 * t + storedRingMulBits t t t + 3

theorem storedPreparationWork_polynomial : PolynomialCostBound storedPreparationWork := by
  let x : Polynomial ℕ := Polynomial.X
  refine ⟨2 * x + (x * x + 2 * (x + 2 * x + 1) + 1) + 3, ?_⟩
  intro t
  apply le_of_eq
  simp [storedPreparationWork, storedRingMulBits, x]

theorem storedPreparationBudget_polynomial : PolynomialCostBound (fun t => storedPreparationBudget t t t t t t) := by
  have hp := polynomialCostBound_comp_mono (f := fun t => storedPublicBudget t t t t t t)
    (g := storedPreparationWork) storedPublicBudget_polynomial storedPreparationWork_polynomial
    (fun _ _ h => storedPublicBudget_mono h h h h h h)
  have hp' : PolynomialCostBound (fun t => storedPublicBudget t t t (t + t)
      (t + (storedRingMulBits t t t + 2)) t) := hp.mono (fun t => by
    apply storedPublicBudget_mono <;> unfold storedPreparationWork <;> omega)
  exact (((storedColumnHintsBudget_polynomial.add storedExtractionMatrixBudget_polynomial).add hp').add
    (PolynomialCostBound.const 3))

def storedPreparationInputSize {d n k m : ℕ} (T : BasisMultiplicationData d) (one : Vector ℤ d) (q : ℕ)
    (B : GaussianColumnData (n * d) m) (X : GaussianColumnData (k * d) m) (R : GaussianColumnData (m * d) k) : ℕ :=
  n + q.size + gaussianColumnsBits B + storedReductionInputSize T one X R

theorem storedReductionPreparationRun_polynomial : ∃ C e : ℕ, ∀ (d n k m : ℕ) (T : BasisMultiplicationData d)
    (one : Vector ℤ d) (q : ℕ) (B : GaussianColumnData (n * d) m)
    (X : GaussianColumnData (k * d) m) (R : GaussianColumnData (m * d) k),
    (storedReductionPreparationRun T one q B X R).steps ≤ C * (storedPreparationInputSize T one q B X R + 1) ^ e := by
  obtain ⟨C, e, h⟩ := storedPreparationBudget_polynomial.exists_mul_pow_bound
  refine ⟨C, e, fun d n k m T one q B X R => ?_⟩
  let U := storedPreparationInputSize T one q B X R
  obtain ⟨hd, hk, hm, ht, ho, hx, hr⟩ := storedReductionInputSize_bounds T one X R
  have hU : storedReductionInputSize T one X R ≤ U := by dsimp [U, storedPreparationInputSize]; omega
  have hb : ∀ j i, (gaussianColumnsOfData B j i).natAbs.size ≤ U := fun j i =>
    (gaussianColumns_entry_bits B j i).trans (by dsimp [U, storedPreparationInputSize]; omega)
  exact (storedReductionPreparationRun_steps T one q B X R
    (fun t i l => (ht t i l).trans hU) (fun l => (ho l).trans hU) hb
    (fun j i => (hx j i).trans hU) (fun j i => (hr j i).trans hU)).trans
      ((storedPreparationBudget_mono (d' := U) (n' := U) (k' := U) (m' := U) (L' := U) (Q' := U)
        (hd.trans hU) (by dsimp [U, storedPreparationInputSize]; omega) (hk.trans hU) (hm.trans hU)
        le_rfl (by dsimp [U, storedPreparationInputSize]; omega)).trans (h U))

end SISToKSIS
