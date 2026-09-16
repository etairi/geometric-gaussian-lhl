import «SIS-to-kSIS».OperatorBounds

/-!
# Finite parameter conditions and error budgets

These are the explicit numerical conditions used by the updated reduction.
The final reduction must establish the corresponding distribution estimates;
defining this window is not a proof of those estimates.
-/

noncomputable section

namespace SISToKSIS

def modularExponent (d m n : ℕ) : ℝ := (n : ℝ) / m + 2 / ((d : ℝ) * m)

def modularWidthFloor (d m n q : ℕ) : ℝ :=
  8 * d * Real.sqrt m * (q : ℝ) ^ modularExponent d m n

def independenceWidthFloor (d m n k q : ℕ) (u : ℝ) : ℝ :=
  2 * Real.sqrt d * (u ^ k * (q : ℝ) ^ n) ^ (1 / ((m : ℝ) - k))

/-- The arithmetic window in the updated SIS-to-k-SIS theorem. -/
def ArithmeticWindow (d m n k q g : ℕ) (u s₁ s₂ : ℝ) : Prop :=
  1 ≤ u ∧
  ∀ s ∈ ({s₁, s₂} : Set ℝ),
    max (modularWidthFloor d m n q) (independenceWidthFloor d m n k q u) ≤ s ∧
    s ≤ min ((q : ℝ) ^ (1 / (g : ℝ)) / Real.sqrt m) (u * s₁)

def hintDistributionError (k : ℕ) (pB δsp ε εs : ℝ) : ℝ :=
  pB + δsp + (k : ℝ) * (ε / (1 - ε)) + (k : ℝ) * εs

def hintNormFailure (k : ℕ) (pB δsp δop εs : ℝ) : ℝ :=
  pB + δsp + δop + (k : ℝ) * εs

/-- One explicit absolute constant, using the existing spectral proofs. -/
def normLoss (m : ℕ) (s₂ : ℝ) : ℝ := 32773 * s₂ * Real.sqrt m

theorem normLoss_pos {m : ℕ} (hm : 0 < m) {s₂ : ℝ} (hs₂ : 0 < s₂) :
    0 < normLoss m s₂ := by
  unfold normLoss
  positivity

theorem arithmeticWindow_first_lower {d m n k q g : ℕ} {u s₁ s₂ : ℝ}
    (h : ArithmeticWindow d m n k q g u s₁ s₂) :
    modularWidthFloor d m n q ≤ s₁ ∧ modularWidthFloor d m n q ≤ s₂ := by
  exact ⟨(le_max_left _ _).trans (h.2 s₁ (by simp)).1,
    (le_max_left _ _).trans (h.2 s₂ (by simp)).1⟩

theorem arithmeticWindow_ratio {d m n k q g : ℕ} {u s₁ s₂ : ℝ}
    (h : ArithmeticWindow d m n k q g u s₁ s₂) : s₂ ≤ u * s₁ :=
  (h.2 s₂ (by simp)).2.trans (min_le_right _ _)

theorem modularExponent_nonneg (d m n : ℕ) : 0 ≤ modularExponent d m n := by
  unfold modularExponent
  positivity

theorem modularWidthFloor_lower (d m n : ℕ) {q : ℕ} (hq : 1 ≤ q) :
    8 * d * Real.sqrt m ≤ modularWidthFloor d m n q := by
  have hp : 1 ≤ (q : ℝ) ^ modularExponent d m n :=
    Real.one_le_rpow (by exact_mod_cast hq) (modularExponent_nonneg d m n)
  exact (le_mul_of_one_le_right (by positivity) hp)

/-- The supplied arithmetic window already makes the actual hint shifts have constant loss. -/
theorem arithmeticWindow_shift_width {d m n k q g : ℕ} {u s₁ s₂ : ℝ}
    (hd : 1 ≤ d) (hkm : k ≤ m) (hq : 1 ≤ q)
    (h : ArithmeticWindow d m n k q g u s₁ s₂) : (k : ℝ) * d ≤ s₂ ^ 2 := by
  have hl : 8 * d * Real.sqrt m ≤ s₂ :=
    (modularWidthFloor_lower d m n hq).trans (arithmeticWindow_first_lower h).2
  have hsq := (sq_le_sq₀ (by positivity : 0 ≤ 8 * d * Real.sqrt m)
    ((by positivity : 0 ≤ 8 * d * Real.sqrt m).trans hl)).mpr hl
  have he : (8 * (d : ℝ) * Real.sqrt m) ^ 2 = 64 * (d : ℝ) ^ 2 * m := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
    norm_num
  rw [he] at hsq
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hmR : (k : ℝ) ≤ m := by exact_mod_cast hkm
  have hdd : (d : ℝ) ≤ 64 * (d : ℝ) ^ 2 := by nlinarith
  calc
    (k : ℝ) * d ≤ (m : ℝ) * d := mul_le_mul_of_nonneg_right hmR (by positivity)
    _ = (d : ℝ) * m := mul_comm _ _
    _ ≤ 64 * (d : ℝ) ^ 2 * m := mul_le_mul_of_nonneg_right hdd (by positivity)
    _ ≤ _ := hsq

theorem hintDistributionError_nonneg {k : ℕ} {pB δsp ε εs : ℝ}
    (hB : 0 ≤ pB) (hsp : 0 ≤ δsp) (hε : 0 ≤ ε) (hεone : ε < 1)
    (hs : 0 ≤ εs) : 0 ≤ hintDistributionError k pB δsp ε εs := by
  unfold hintDistributionError
  have : 0 < 1 - ε := sub_pos.mpr hεone
  positivity

theorem hintDistributionError_geometric (k : ℕ) (δ δsp εs : ℝ) :
    hintDistributionError k (3 * δ) δsp (2 * δ) εs =
      3 * δ + δsp + 2 * (k : ℝ) * δ / (1 - 2 * δ) + (k : ℝ) * εs := by
  unfold hintDistributionError
  ring

/-- The supplied spectral bounds give the improved `s₂ sqrt(m)` loss. -/
theorem normLoss_of_spectral {m : ℕ} (hm : 1 ≤ m) {a r s₁ s₂ : ℝ}
    (hr : 0 ≤ r) (hs₁ : 0 < s₁) (hs : s₁ ≤ s₂)
    (hscale : 1 ≤ s₂ * Real.sqrt m)
    (ha_bound : a ≤ 4 * s₁ * Real.sqrt m) (hr_bound : r ≤ 8192 * s₂ / s₁) :
    1 + a * r + a ≤ normLoss m s₂ := by
  apply spectral_extraction_constant hr hs₁ _ hs hscale ha_bound hr_bound
  have hcast : (1 : ℝ) ≤ m := by exact_mod_cast hm
  exact Real.one_le_sqrt.mpr hcast

theorem diagonal_mass_ratio (m k d : ℕ) {x a b Q : ℝ}
    (hx : x ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) :
    (2 * b / x) ^ (k * d) * Q * (x ^ d) ^ (m + k) /
      (a ^ (m * d) * b ^ (k * d)) =
        2 ^ (k * d) * Q * (x / a) ^ (m * d) := by
  rw [pow_add]
  simp only [div_pow, mul_pow, ← pow_mul, Nat.mul_comm d m, Nat.mul_comm d k]
  field_simp

theorem width_power_ratio_le {M K : ℕ} (hKM : K ≤ M) {x a Q : ℝ}
    (hx : 0 < x) (ha : 0 < a) (hscale : 2 * x ≤ a)
    (hQ : Q ≤ (a / (2 * x)) ^ (M - K)) :
    2 ^ K * Q * (x / a) ^ M ≤ (1 / 2 : ℝ) ^ (M - K) := by
  have hr : 2 * x / a ≤ 1 := (div_le_one ha).mpr hscale
  calc
    _ ≤ 2 ^ K * (a / (2 * x)) ^ (M - K) * (x / a) ^ M :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hQ (by positivity)) (by positivity)
    _ = (1 / 2 : ℝ) ^ (M - K) * (2 * x / a) ^ K := by
      nth_rw 2 [← Nat.sub_add_cancel hKM]
      rw [pow_add]
      simp only [div_pow, mul_pow]
      field_simp
      ring
    _ ≤ _ := mul_le_of_le_one_right (by positivity) (pow_le_one₀ (by positivity) hr)

theorem independenceWidthFloor_power (d m n k q : ℕ) (hd : 0 < d) (hkm : k < m)
    (hq : 1 ≤ q) {u s : ℝ} (hu : 1 ≤ u)
    (hs : independenceWidthFloor d m n k q u ≤ s) :
    (q : ℝ) ^ n ≤ (s / (2 * Real.sqrt d)) ^ (m - k) := by
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hp : m - k ≠ 0 := Nat.ne_of_gt (Nat.sub_pos_of_lt hkm)
  have hbase : 0 ≤ u ^ k * (q : ℝ) ^ n := by positivity
  have hl : (u ^ k * (q : ℝ) ^ n) ^ ((m - k : ℕ) : ℝ)⁻¹ ≤
      s / (2 * Real.sqrt d) := by
    apply (le_div_iff₀ (by positivity)).mpr
    have he : ((m - k : ℕ) : ℝ) = (m : ℝ) - k := Nat.cast_sub hkm.le
    simpa only [independenceWidthFloor, he, one_div, mul_comm] using hs
  have hpow := pow_le_pow_left₀ (Real.rpow_nonneg hbase _) hl (m - k)
  rw [Real.rpow_inv_natCast_pow hbase hp] at hpow
  exact (le_mul_of_one_le_left (by positivity : 0 ≤ (q : ℝ) ^ n)
    (one_le_pow₀ hu)).trans hpow

theorem independenceWidthFloor_ge_twice_sqrt (d m n k q : ℕ) (hkm : k < m)
    (hq : 1 ≤ q) {u : ℝ} (hu : 1 ≤ u) :
    2 * Real.sqrt d ≤ independenceWidthFloor d m n k q u := by
  have hbase : 1 ≤ u ^ k * (q : ℝ) ^ n :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hu) (one_le_pow₀ (by exact_mod_cast hq))
  have hp : 0 ≤ 1 / ((m : ℝ) - k) := by
    have hm : (k : ℝ) < m := by exact_mod_cast hkm
    positivity
  exact le_mul_of_one_le_right (by positivity) (Real.one_le_rpow hbase hp)

theorem arithmeticWindow_independence_ratio {d m n k q g : ℕ}
    (hd : 0 < d) (hkm : k < m) (hq : 1 ≤ q) {u s₁ s₂ : ℝ}
    (hw : ArithmeticWindow d m n k q g u s₁ s₂) :
    2 ^ (k * d) * (q : ℝ) ^ (d * n) * (Real.sqrt d / s₁) ^ (m * d) ≤
      (1 / 2 : ℝ) ^ ((m - k) * d) := by
  have hfloor : independenceWidthFloor d m n k q u ≤ s₁ :=
    (le_max_right _ _).trans (hw.2 s₁ (by simp)).1
  have hscale : 2 * Real.sqrt d ≤ s₁ :=
    (independenceWidthFloor_ge_twice_sqrt d m n k q hkm hq hw.1).trans hfloor
  have hx : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hd)
  have ha : 0 < s₁ := (mul_pos (by norm_num) hx).trans_le hscale
  have hQ := pow_le_pow_left₀ (by positivity : 0 ≤ (q : ℝ) ^ n)
    (independenceWidthFloor_power d m n k q hd hkm hq hw.1 hfloor) d
  simp only [← pow_mul, Nat.mul_comm n d] at hQ
  have h := width_power_ratio_le (Nat.mul_le_mul_right d hkm.le) hx ha hscale
    (Q := (q : ℝ) ^ (d * n)) (by simpa only [← Nat.sub_mul] using hQ)
  simpa only [← Nat.sub_mul] using h

theorem residue_tail_gap_pos {d m : ℕ} (hd : 0 < d) (hm : 0 < m) :
    0 < 1 - Real.exp (-((m : ℝ) * d) / 32) := by
  apply sub_pos.mpr
  apply Real.exp_lt_one_iff.mpr
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  exact div_neg_of_neg_of_pos (neg_neg_of_pos (mul_pos hmR hdR)) (by norm_num)

theorem equal_norm_roots {N q d g : ℕ} (hd : 0 < d) (hg : 0 < g)
    (hpow : N ^ g = q ^ d) :
    (N : ℝ) ^ (1 / (d : ℝ)) = (q : ℝ) ^ (1 / (g : ℝ)) := by
  apply (pow_left_inj₀ (Real.rpow_nonneg (Nat.cast_nonneg N) _)
    (Real.rpow_nonneg (Nat.cast_nonneg q) _) (Nat.mul_ne_zero hd.ne' hg.ne')).mp
  rw [pow_mul, one_div, Real.rpow_inv_natCast_pow (Nat.cast_nonneg N) hd.ne']
  rw [Nat.mul_comm d g, pow_mul, one_div,
    Real.rpow_inv_natCast_pow (Nat.cast_nonneg q) hg.ne']
  exact_mod_cast hpow

theorem arithmeticWindow_ideal_ceiling {d m n k q g N : ℕ}
    (hd : 0 < d) (hg : 0 < g) (hm : 0 < m) (hpow : N ^ g = q ^ d)
    {u s₁ s₂ : ℝ} (hw : ArithmeticWindow d m n k q g u s₁ s₂) :
    s₂ * Real.sqrt m ≤ (N : ℝ) ^ (1 / (d : ℝ)) := by
  rw [equal_norm_roots hd hg hpow]
  apply (le_div_iff₀ (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hm))).mp
  exact (hw.2 s₂ (by simp)).2.trans (min_le_left _ _)

end SISToKSIS
