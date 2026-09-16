import «SIS-to-kSIS».CosetAveraging
import «SIS-to-kSIS».ModularReverseSampling
import Mathlib.Algebra.CharP.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Mathlib.NumberTheory.RamificationInertia.Galois

/-!
# Modular regularity from the arithmetic width window

The actual expected dual mass is bounded by a tail correction and a width
term. Ideal norms, finite frequency counts, and the supplied width floor
bound this expectation by `2 * 2^(-d*m)`. Markov's inequality then gives a
smoothing failure at most `2^(-floor(d*m/4))`, also after diagonal whitening.
This discharges the smoothing term in the quantitative reverse-sampling law.
Stored integer matrix operations realize the public input and exact extraction
of this game. Finite residue coordinates correspond to its ideal quotient, with
canonical representatives bounded by the modulus bit length. A finite-word
oracle interface and the complete stored reduction have the exact game law and
uniform polynomial declared costs. Both final geometric parameter regimes are
instantiated for this actual program, including its initial sampling error.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped ENNReal Classical
namespace SISToKSIS

theorem ideal_norm_scaled_ratio {d : ℕ} (hd : 0 < d) {h v q c t : ℝ}
    (hv : 0 < v) (hc : 0 < c) (ht : 0 < t)
    (hprod : h * v = q ^ d) (ℓ : ℕ) :
    (4 * Real.sqrt ℓ / ((t * (q⁻¹ * c⁻¹)) * v ^ (1 / (d : ℝ)))) ^ d =
      (4 * c * Real.sqrt ℓ / t) ^ d * h := by
  have hroot : (v ^ (1 / (d : ℝ))) ^ d = v := by
    rw [one_div, Real.rpow_inv_natCast_pow hv.le hd.ne']
  simp only [div_pow, mul_pow, inv_pow, hroot]
  rw [← hprod]
  field_simp

theorem inv_pow_max_mass_le {h a C : ℝ≥0∞} (hh : h ≠ 0) (hhfin : h ≠ ⊤) (r : ℕ) :
    (h ^ r)⁻¹ * ((max 1 (a * h) * C) ^ r - 1) ≤
      (C ^ r - 1) * (h ^ r)⁻¹ + C ^ r * a ^ r := by
  by_cases hab : a * h ≤ 1
  · rw [max_eq_left hab, one_mul, mul_comm (h ^ r)⁻¹]
    exact le_self_add
  · rw [max_eq_right (le_of_not_ge hab)]
    calc
      _ ≤ (h ^ r)⁻¹ * ((a * h) * C) ^ r := by gcongr; exact tsub_le_self
      _ = C ^ r * a ^ r := by
        rw [mul_pow, mul_pow]
        calc
          _ = C ^ r * a ^ r * ((h ^ r)⁻¹ * h ^ r) := by ac_rfl
          _ = _ := by rw [ENNReal.inv_mul_cancel (pow_ne_zero _ hh) (by finiteness), mul_one]
      _ ≤ _ := le_add_self

theorem sum_inv_pow_max_mass_le {α : Type*} [Fintype α]
    (h : α → ℝ≥0∞) (hh : ∀ x, h x ≠ 0) (hhfin : ∀ x, h x ≠ ⊤)
    (a C H : ℝ≥0∞) (r : ℕ) (hsum : (∑ x, (h x ^ r)⁻¹) ≤ H) :
    (∑ x, (h x ^ r)⁻¹ * ((max 1 (a * h x) * C) ^ r - 1)) ≤
      (C ^ r - 1) * H + Fintype.card α * (C ^ r * a ^ r) := by
  apply (Finset.sum_le_sum (s := Finset.univ) (fun x _ => inv_pow_max_mass_le (hh x) (hhfin x) r)).trans
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact add_le_add (mul_le_mul' le_rfl hsum) le_rfl

end SISToKSIS

noncomputable section
namespace SISToKSIS

theorem modularExponent_power {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    (n : ℕ) {q : ℝ} (hq : 0 ≤ q) :
    (q ^ modularExponent d m n) ^ (d * m) = q ^ (d * n + 2) := by
  have hdR : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  have hmR : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have he : modularExponent d m n * ((d * m : ℕ) : ℝ) = ((d * n + 2 : ℕ) : ℝ) := by
    unfold modularExponent
    push_cast
    field_simp
  calc
    _ = q ^ (modularExponent d m n * ((d * m : ℕ) : ℝ)) := by
      rw [Real.rpow_mul hq, Real.rpow_natCast]
    _ = _ := by rw [he, Real.rpow_natCast]

theorem modularWidthFloor_ratio_le {d m n q : ℕ} (hd : 0 < d) (hm : 0 < m)
    (hq : 1 ≤ q) {t : ℝ} (ht : modularWidthFloor d m n q ≤ t) :
    4 * d * Real.sqrt m / t ≤ (1 / 2 : ℝ) / (q : ℝ) ^ modularExponent d m n := by
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hqR : (0 : ℝ) < q := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq)
  have hpow : 0 < (q : ℝ) ^ modularExponent d m n := Real.rpow_pos_of_pos hqR _
  have hfloor : 0 < modularWidthFloor d m n q := by unfold modularWidthFloor; positivity
  calc
    _ ≤ 4 * d * Real.sqrt m / modularWidthFloor d m n q :=
      div_le_div_of_nonneg_left (by positivity) hfloor ht
    _ = _ := by unfold modularWidthFloor; field_simp; ring

theorem modularWidthFloor_ratio_half {d m n q : ℕ} (hd : 0 < d) (hm : 0 < m)
    (hq : 1 ≤ q) {t : ℝ} (ht : modularWidthFloor d m n q ≤ t) :
    4 * d * Real.sqrt m / t ≤ (1 / 2 : ℝ) := by
  have hqpow : 1 ≤ (q : ℝ) ^ modularExponent d m n :=
    Real.one_le_rpow (by exact_mod_cast hq) (modularExponent_nonneg d m n)
  exact (modularWidthFloor_ratio_le hd hm hq ht).trans
    (div_le_self (by norm_num) hqpow)

theorem modularWidthFloor_power_budget {d m n q r : ℕ} (hd : 0 < d) (hm : 0 < m)
    (hq : 1 ≤ q) (hmr : m ≤ r) {t : ℝ} (ht : modularWidthFloor d m n q ≤ t) :
    (q : ℝ) ^ (d * n) * ((4 * d * Real.sqrt m / t) ^ d) ^ r ≤
      (1 / 2 : ℝ) ^ (d * r) / (q : ℝ) ^ 2 := by
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hqR : (0 : ℝ) < q := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq)
  have hfloor : 0 < modularWidthFloor d m n q := by
    unfold modularWidthFloor
    exact mul_pos (by positivity) (Real.rpow_pos_of_pos hqR _)
  have htpos : 0 < t := hfloor.trans_le ht
  have hrpos : 0 ≤ 4 * (d : ℝ) * Real.sqrt m / t := by positivity
  have hp := pow_le_pow_left₀ hrpos (modularWidthFloor_ratio_le hd hm hq ht) (d * m)
  rw [div_pow (1 / 2 : ℝ) ((q : ℝ) ^ modularExponent d m n) (d * m),
    modularExponent_power hd hm n hqR.le] at hp
  have hbase : (q : ℝ) ^ (d * n + 2) * (4 * d * Real.sqrt m / t) ^ (d * m) ≤
      (1 / 2 : ℝ) ^ (d * m) := by
    exact (mul_comm _ _).trans_le ((le_div_iff₀ (pow_pos hqR _)).mp hp)
  have he : d * r = d * m + d * (r - m) := by
    rw [← Nat.mul_add, Nat.add_comm m, Nat.sub_add_cancel hmr]
  have hextra := pow_le_pow_left₀ hrpos (modularWidthFloor_ratio_half hd hm hq ht) (d * (r - m))
  have htotal : (q : ℝ) ^ (d * n + 2) * (4 * d * Real.sqrt m / t) ^ (d * r) ≤
      (1 / 2 : ℝ) ^ (d * r) := by
    rw [he, pow_add (4 * (d : ℝ) * Real.sqrt m / t) (d * m) (d * (r - m)),
      pow_add (1 / 2 : ℝ) (d * m) (d * (r - m)), ← mul_assoc]
    exact mul_le_mul hbase hextra (by positivity) (by positivity)
  apply (le_div_iff₀ (pow_pos hqR 2)).mpr
  apply le_trans (le_of_eq ?_) htotal
  rw [← pow_mul, pow_add]
  ring

end SISToKSIS

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Module NumberField GeometricGaussianLHL
open scoped ENNReal Classical
namespace SISToKSIS

def gaussianRegularityCorrection (d ℓ : ℕ) : ℝ := 1 + 2 * (2 : ℝ) ^ (-(3 * (d : ℝ) * ℓ))
def gaussianRegularityScale (d ℓ : ℕ) (c t : ℝ) : ℝ := (4 * c * Real.sqrt ℓ / t) ^ d

theorem gaussianRegularityCorrection_ge_one (d ℓ : ℕ) : 1 ≤ gaussianRegularityCorrection d ℓ := by
  have h : 0 ≤ 2 * (2 : ℝ) ^ (-(3 * (d : ℝ) * ℓ)) := by positivity
  unfold gaussianRegularityCorrection
  linarith

variable (K : Type*) [Field K] [NumberField K] {d n : ℕ}

theorem residueDotIdeal_scaled_ratio (b : Basis (Fin d) ℤ (𝓞 K)) (q : ℕ) [NeZero q]
    (s : Fin n → ResidueRing K q) {c t : ℝ} (hc : 0 < c) (ht : 0 < t) (ℓ : ℕ) :
    (4 * Real.sqrt ℓ /
      ((t * ((q : ℝ)⁻¹ * c⁻¹)) * (Ideal.absNorm (residueDotIdeal K q s) : ℝ) ^ (1 / (d : ℝ)))) ^ d =
        gaussianRegularityScale d ℓ c t * Fintype.card (dotImageIdeal s) := by
  have hp := residueDotIdeal_card_mul_norm K b q s
  have hN : (0 : ℝ) < Ideal.absNorm (residueDotIdeal K q s) := by
    apply Nat.cast_pos.mpr
    apply Nat.pos_of_ne_zero
    intro hz
    rw [hz, mul_zero] at hp
    exact pow_ne_zero d (NeZero.ne q) hp.symm
  exact ideal_norm_scaled_ratio (integralBasis_dimension_pos K b) hN hc ht
    (by exact_mod_cast hp) ℓ

theorem cyclotomicModularLattice_expected_mass_budget
    (N : ℕ) [NeZero N] [IsCyclotomicExtension {N} ℚ K]
    (b : Basis (Fin d) ℤ (𝓞 K)) {c : ℝ} (hc : 0 < c)
    (hGram : ∀ i j, canonicalGram K b i j = if i = j then c else 0)
    (q : ℕ) [NeZero q] (r n ℓ : ℕ) (hnr : n ≤ r) (hℓ : 1 ≤ ℓ) {t : ℝ} (ht : 0 < t) :
    (∑ A : Matrix (Fin n) (Fin r) (ResidueRing K q),
      PMF.uniformOfFintype (Matrix (Fin n) (Fin r) (ResidueRing K q)) A *
        nonzeroDualMass (numberFieldModularLattice K b q A) t) ≤
      ((ENNReal.ofReal (gaussianRegularityCorrection d ℓ)) ^ r - 1) *
        Fintype.card (Ideal (ResidueRing K q)) +
      (q : ℝ≥0∞) ^ (d * n) * ((ENNReal.ofReal (gaussianRegularityCorrection d ℓ)) ^ r *
        (ENNReal.ofReal (gaussianRegularityScale d ℓ c t)) ^ r) := by
  apply (cyclotomicModularLattice_expected_nonzeroDualMass_explicit K N b hc hGram q r n ℓ hℓ ht).trans
  simp_rw [residueDotIdeal_scaled_ratio K b q _ hc ht ℓ]
  have ha : 0 ≤ gaussianRegularityScale d ℓ c t := by
    unfold gaussianRegularityScale
    positivity
  have hC0 : 0 ≤ 1 + 2 * (2 : ℝ) ^ (-(3 * (d : ℝ) * ℓ)) := by positivity
  simp only [ENNReal.ofReal_mul' hC0, ENNReal.ofReal_max, ENNReal.ofReal_one]
  simp only [ENNReal.ofReal_mul ha, ENNReal.ofReal_natCast]
  have hsum := sum_inv_pow_max_mass_le
    (fun s : Fin n → ResidueRing K q => (Fintype.card (dotImageIdeal s) : ℝ≥0∞))
    (fun _ => by positivity) (fun _ => by finiteness)
    (ENNReal.ofReal (gaussianRegularityScale d ℓ c t))
    (ENNReal.ofReal (gaussianRegularityCorrection d ℓ))
    (Fintype.card (Ideal (ResidueRing K q))) r (sum_dotImageIdeal_inv_pow_le hnr)
  have hcard : Fintype.card (Fin n → ResidueRing K q) = q ^ (d * n) := by
    rw [Fintype.card_fun, Fintype.card_fin, ← Nat.card_eq_fintype_card,
      residueRing_card K b q, ← pow_mul]
  simpa only [hcard, Nat.cast_pow, gaussianRegularityCorrection] using hsum

theorem cyclotomicModularLattice_expected_mass_split_budget
    (N : ℕ) [NeZero N] [IsCyclotomicExtension {N} ℚ K]
    (b : Basis (Fin d) ℤ (𝓞 K)) {c : ℝ} (hc : 0 < c)
    (hGram : ∀ i j, canonicalGram K b i j = if i = j then c else 0)
    (q : ℕ) [NeZero q] {g : ℕ} (I : Fin g → Ideal (𝓞 K)) [∀ j, (I j).IsMaximal]
    (hI : Function.Injective I) (hfac : Ideal.span ({(q : 𝓞 K)} : Set (𝓞 K)) = ∏ j, I j)
    (r n ℓ : ℕ) (hnr : n ≤ r) (hℓ : 1 ≤ ℓ) {t : ℝ} (ht : 0 < t) :
    (∑ A : Matrix (Fin n) (Fin r) (ResidueRing K q),
      PMF.uniformOfFintype (Matrix (Fin n) (Fin r) (ResidueRing K q)) A *
        nonzeroDualMass (numberFieldModularLattice K b q A) t) ≤
      ENNReal.ofReal ((gaussianRegularityCorrection d ℓ ^ r - 1) * (2 : ℝ) ^ g +
        (q : ℝ) ^ (d * n) * (gaussianRegularityCorrection d ℓ ^ r *
          gaussianRegularityScale d ℓ c t ^ r)) := by
  have h := cyclotomicModularLattice_expected_mass_budget K N b hc hGram q r n ℓ hnr hℓ ht
  have hcard : Fintype.card (Ideal (ResidueRing K q)) = 2 ^ g :=
    quotient_ideal_card_of_factorization _ I hI hfac
  rw [hcard, Nat.cast_pow, Nat.cast_ofNat] at h
  apply h.trans_eq
  have hC := gaussianRegularityCorrection_ge_one d ℓ
  have ha : 0 ≤ gaussianRegularityScale d ℓ c t := by unfold gaussianRegularityScale; positivity
  have hCp : 0 ≤ gaussianRegularityCorrection d ℓ ^ r - 1 := sub_nonneg.mpr (one_le_pow₀ hC)
  rw [ENNReal.ofReal_add (mul_nonneg hCp (by positivity)) (by positivity)]
  rw [ENNReal.ofReal_mul hCp, ENNReal.ofReal_mul (by positivity : 0 ≤ (q : ℝ) ^ (d * n)),
    ENNReal.ofReal_mul (pow_nonneg (le_trans (by norm_num) hC) r)]
  simp only [ENNReal.ofReal_sub _ (by norm_num : (0 : ℝ) ≤ 1),
    ENNReal.ofReal_pow (le_trans (by norm_num) hC), ENNReal.ofReal_pow ha,
    ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_pow (Nat.cast_nonneg q),
    ENNReal.ofReal_one, ENNReal.ofReal_ofNat, ENNReal.ofReal_natCast]

end SISToKSIS

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Module NumberField GeometricGaussianLHL
open scoped Classical
namespace SISToKSIS
variable (K : Type*) [Field K] [NumberField K] {d : ℕ}
local instance regularityResidueField (I : Ideal (𝓞 K)) [I.IsMaximal] : Field ((𝓞 K) ⧸ I) :=
  Ideal.Quotient.field I

omit [NumberField K] in
theorem primeIdeal_quotient_charP {q : ℕ} (hq : q.Prime)
    (I : Ideal (𝓞 K)) [I.IsMaximal] (hqI : (q : 𝓞 K) ∈ I) : CharP ((𝓞 K) ⧸ I) q := by
  apply (CharP.charP_iff_prime_eq_zero hq).mpr
  rw [← map_natCast (Ideal.Quotient.mk I), Ideal.Quotient.eq_zero_iff_mem]
  exact hqI

omit [NumberField K] in
theorem primeIdeal_liesOver_of_mem {q : ℕ} (hq : q.Prime)
    (I : Ideal (𝓞 K)) [I.IsMaximal] (hqI : (q : 𝓞 K) ∈ I) :
    I.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ)) := by
  let : CharP ((𝓞 K) ⧸ I) q := primeIdeal_quotient_charP K hq I hqI
  constructor
  ext z
  change z ∈ Ideal.span ({(q : ℤ)} : Set ℤ) ↔ algebraMap ℤ (𝓞 K) z ∈ I
  rw [Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem]
  change (q : ℤ) ∣ z ↔ (z : (𝓞 K) ⧸ I) = 0
  exact (CharP.intCast_eq_zero_iff ((𝓞 K) ⧸ I) q z).symm

omit [NumberField K] in
theorem modulus_mem_ideal_factor {q g : ℕ} (I : Fin g → Ideal (𝓞 K))
    (hfac : Ideal.span ({(q : 𝓞 K)} : Set (𝓞 K)) = ∏ j, I j) (j : Fin g) :
    (q : 𝓞 K) ∈ I j := by
  have hle : Ideal.span ({(q : 𝓞 K)} : Set (𝓞 K)) ≤ I j := by
    rw [hfac]
    exact Ideal.prod_le_inf.trans (Finset.inf_le (Finset.mem_univ j))
  exact hle (Ideal.subset_span (Set.mem_singleton _))

theorem primeIdeal_norm_eq_of_galois [IsGalois ℚ K] {q : ℕ} (hq : q.Prime)
    (I J : Ideal (𝓞 K)) [I.IsMaximal] [J.IsMaximal]
    (hqI : (q : 𝓞 K) ∈ I) (hqJ : (q : 𝓞 K) ∈ J) : Ideal.absNorm I = Ideal.absNorm J := by
  let : I.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ)) := primeIdeal_liesOver_of_mem K hq I hqI
  let : J.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ)) := primeIdeal_liesOver_of_mem K hq J hqJ
  let : IsGaloisGroup (K ≃ₐ[ℚ] K) ℤ (𝓞 K) :=
    IsGaloisGroup.of_isFractionRing (K ≃ₐ[ℚ] K) ℤ (𝓞 K) ℚ K
  rw [← Ideal.natAbs_pow_inertiaDeg (q : ℤ) I, ← Ideal.natAbs_pow_inertiaDeg (q : ℤ) J,
    Ideal.inertiaDeg_eq_of_isGaloisGroup (Ideal.span ({(q : ℤ)} : Set ℤ)) I J (K ≃ₐ[ℚ] K)]

theorem primeIdeal_factor_norm_power [IsGalois ℚ K] (b : Basis (Fin d) ℤ (𝓞 K))
    {q g : ℕ} (hq : q.Prime) (I : Fin g → Ideal (𝓞 K)) [∀ j, (I j).IsMaximal]
    (hfac : Ideal.span ({(q : 𝓞 K)} : Set (𝓞 K)) = ∏ j, I j) (j : Fin g) :
    Ideal.absNorm (I j) ^ g = q ^ d := by
  have hnorm : (∏ j, Ideal.absNorm (I j)) = q ^ d := by
    rw [← map_prod, ← hfac, Ideal.absNorm_span_natCast, Module.finrank_eq_card_basis b,
      Fintype.card_fin]
  calc
    _ = ∏ _a : Fin g, Ideal.absNorm (I j) := by simp
    _ = ∏ a, Ideal.absNorm (I a) := by
      apply Finset.prod_congr rfl
      intro a _
      exact primeIdeal_norm_eq_of_galois K hq (I j) (I a)
        (modulus_mem_ideal_factor K I hfac j) (modulus_mem_ideal_factor K I hfac a)
    _ = _ := hnorm

theorem primeIdeal_factor_count_pos (b : Basis (Fin d) ℤ (𝓞 K))
    {q g : ℕ} (hq : q.Prime) (I : Fin g → Ideal (𝓞 K))
    (hfac : Ideal.span ({(q : 𝓞 K)} : Set (𝓞 K)) = ∏ j, I j) : 0 < g := by
  have hnorm : (∏ j, Ideal.absNorm (I j)) = q ^ d := by
    rw [← map_prod, ← hfac, Ideal.absNorm_span_natCast, Module.finrank_eq_card_basis b,
      Fintype.card_fin]
  by_contra hg
  have hg0 : g = 0 := by omega
  subst g
  simp only [Finset.univ_eq_empty, Finset.prod_empty] at hnorm
  exact (ne_of_gt (one_lt_pow₀ hq.one_lt (integralBasis_dimension_pos K b).ne')) hnorm.symm


theorem prime_le_residueIdeal_norm {q : ℕ} (hq : q.Prime)
    (I : Ideal (𝓞 K)) [I.IsMaximal] (hqI : (q : 𝓞 K) ∈ I) : q ≤ Ideal.absNorm I := by
  let : NeZero q := ⟨hq.ne_zero⟩
  let : Fintype ((𝓞 K) ⧸ I) := Fintype.ofFinite _
  let : CharP ((𝓞 K) ⧸ I) q := primeIdeal_quotient_charP K hq I hqI
  change q ≤ Nat.card ((𝓞 K) ⧸ I)
  rw [Nat.card_eq_fintype_card]
  have h := Fintype.card_le_of_injective (ZMod.castHom (dvd_refl q) ((𝓞 K) ⧸ I))
    (ZMod.castHom_injective (n := q) (R := (𝓞 K) ⧸ I))
  simpa only [ZMod.card] using h

theorem primeIdeal_factor_count_le_degree (b : Basis (Fin d) ℤ (𝓞 K))
    {q g : ℕ} (hq : q.Prime) (I : Fin g → Ideal (𝓞 K)) [∀ j, (I j).IsMaximal]
    (hfac : Ideal.span ({(q : 𝓞 K)} : Set (𝓞 K)) = ∏ j, I j) : g ≤ d := by
  have hqI (j : Fin g) : (q : 𝓞 K) ∈ I j := modulus_mem_ideal_factor K I hfac j
  have hnorm : (∏ j, Ideal.absNorm (I j)) = q ^ d := by
    rw [← map_prod, ← hfac, Ideal.absNorm_span_natCast, Module.finrank_eq_card_basis b,
      Fintype.card_fin]
  apply (Nat.pow_le_pow_iff_right hq.one_lt).mp
  calc
    q ^ g = ∏ _j : Fin g, q := by simp
    _ ≤ ∏ j, Ideal.absNorm (I j) := by
      gcongr with j
      exact prime_le_residueIdeal_norm K hq (I j) (hqI j)
    _ = _ := hnorm

end SISToKSIS

noncomputable section
namespace SISToKSIS

theorem pow_one_add_mul_one_sub_le_one {x : ℝ} (hx : 0 ≤ x) (r : ℕ) :
    (1 + x) ^ r * (1 - (r : ℝ) * x) ≤ 1 := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ, Nat.cast_succ]
    calc
      _ = (1 + x) ^ r * ((1 - (r : ℝ) * x) - ((r : ℝ) + 1) * x ^ 2) := by ring
      _ ≤ (1 + x) ^ r * (1 - (r : ℝ) * x) :=
        mul_le_mul_of_nonneg_left (sub_le_self _ (by positivity)) (by positivity)
      _ ≤ 1 := ih

theorem pow_one_add_le_linear {x : ℝ} (hx : 0 ≤ x) (r : ℕ)
    (hrx : (r : ℝ) * x ≤ 1 / 2) : (1 + x) ^ r ≤ 1 + 2 * r * x := by
  have hy : 0 ≤ (r : ℝ) * x := mul_nonneg (Nat.cast_nonneg _) hx
  have hden : 0 < 1 - (r : ℝ) * x := by linarith
  calc
    _ ≤ 1 / (1 - (r : ℝ) * x) :=
      (le_div_iff₀ hden).mpr (pow_one_add_mul_one_sub_le_one hx r)
    _ ≤ _ := (div_le_iff₀ hden).mpr (by
      have h := mul_nonneg hy (show 0 ≤ 1 - 2 * ((r : ℝ) * x) by linarith)
      nlinarith)

theorem eight_mul_le_two_pow {D : ℕ} (hD : 6 ≤ D) : 8 * D ≤ 2 ^ D := by
  induction D, hD using Nat.le_induction with
  | base => norm_num
  | succ D hD ih =>
    rw [pow_succ]
    omega

theorem regularity_correction_budget {D g r : ℕ} (hD : 6 ≤ D)
    (hg : g ≤ D) (hr : r ≤ 2 * D) :
    (1 + 2 * (1 / 2 : ℝ) ^ (3 * D)) ^ r ≤ 2 ∧
      ((1 + 2 * (1 / 2 : ℝ) ^ (3 * D)) ^ r - 1) * (2 : ℝ) ^ g ≤ (1 / 2 : ℝ) ^ D := by
  have h8 := eight_mul_le_two_pow hD
  have h8R : 8 * (D : ℝ) ≤ (2 : ℝ) ^ D := by exact_mod_cast h8
  have hrR : (r : ℝ) ≤ 2 * D := by exact_mod_cast hr
  have h4r : 4 * r ≤ 2 ^ (3 * D) := by
    calc
      4 * r ≤ 8 * D := by omega
      _ ≤ 2 ^ D := h8
      _ ≤ _ := pow_le_pow_right' (by omega : (1 : ℕ) ≤ 2) (by omega)
  have hsmall : (r : ℝ) * (2 * (1 / 2 : ℝ) ^ (3 * D)) ≤ 1 / 2 := by
    have h4rR : 4 * (r : ℝ) ≤ (2 : ℝ) ^ (3 * D) := by exact_mod_cast h4r
    calc
      _ = (2 * (r : ℝ)) / (2 : ℝ) ^ (3 * D) := by rw [div_pow, one_pow]; ring
      _ ≤ _ := (div_le_iff₀ (by positivity)).mpr (by linarith)
  have hpow := pow_one_add_le_linear (by positivity : 0 ≤ 2 * (1 / 2 : ℝ) ^ (3 * D)) r hsmall
  have hsub : (1 + 2 * (1 / 2 : ℝ) ^ (3 * D)) ^ r - 1 ≤
      4 * r * (1 / 2 : ℝ) ^ (3 * D) := by nlinarith
  refine ⟨by nlinarith, ?_⟩
  have h2g : (2 : ℝ) ^ g ≤ (2 : ℝ) ^ D := pow_le_pow_right₀ (by norm_num) hg
  calc
    _ ≤ (4 * r * (1 / 2 : ℝ) ^ (3 * D)) * (2 : ℝ) ^ D :=
      mul_le_mul hsub h2g (by positivity) (by positivity)
    _ ≤ (8 * D * (1 / 2 : ℝ) ^ (3 * D)) * (2 : ℝ) ^ D :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (show 4 * (r : ℝ) ≤ 8 * D by linarith) (by positivity))
        (by positivity)
    _ ≤ ((2 : ℝ) ^ D * (1 / 2 : ℝ) ^ (3 * D)) * (2 : ℝ) ^ D := by gcongr
    _ = _ := by
      have he : 3 * D = D + D + D := by omega
      simp only [one_div, inv_pow, he, pow_add]
      field_simp

theorem gaussianRegularityCorrection_eq (d m : ℕ) :
    gaussianRegularityCorrection d m = 1 + 2 * (1 / 2 : ℝ) ^ (3 * (d * m)) := by
  unfold gaussianRegularityCorrection
  have he : 3 * (d : ℝ) * m = ((3 * (d * m) : ℕ) : ℝ) := by push_cast; ring
  rw [he, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast, one_div, inv_pow]

theorem modularRegularity_numerical_budget {d m n q r g : ℕ}
    (hd : 0 < d) (hm : 0 < m) (hD : 6 ≤ d * m) (hq : 2 ≤ q)
    (hg : g ≤ d) (hmr : m ≤ r) (hr : r ≤ 2 * (d * m)) {t : ℝ}
    (ht : modularWidthFloor d m n q ≤ t) :
    (gaussianRegularityCorrection d m ^ r - 1) * (2 : ℝ) ^ g +
      (q : ℝ) ^ (d * n) * (gaussianRegularityCorrection d m ^ r *
        gaussianRegularityScale d m d t ^ r) ≤ 2 * (1 / 2 : ℝ) ^ (d * m) := by
  have hdm : d ≤ d * m := Nat.le_mul_of_pos_right _ hm
  have hcor := regularity_correction_budget hD (hg.trans hdm) hr
  rw [← gaussianRegularityCorrection_eq] at hcor
  have hw := modularWidthFloor_power_budget hd hm (by omega : 1 ≤ q) hmr ht
  change (q : ℝ) ^ (d * n) * gaussianRegularityScale d m d t ^ r ≤ _ at hw
  have htpos : 0 < t := (show 0 < 8 * (d : ℝ) * Real.sqrt m by positivity).trans_le
    ((modularWidthFloor_lower d m n (by omega : 1 ≤ q)).trans ht)
  have hwidth : (q : ℝ) ^ (d * n) * (gaussianRegularityCorrection d m ^ r *
      gaussianRegularityScale d m d t ^ r) ≤ (1 / 2 : ℝ) ^ (d * m) := by
    have hpow : (1 / 2 : ℝ) ^ (d * r) ≤ (1 / 2 : ℝ) ^ (d * m) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.mul_le_mul_left d hmr)
    have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
    calc
      _ = gaussianRegularityCorrection d m ^ r *
          ((q : ℝ) ^ (d * n) * gaussianRegularityScale d m d t ^ r) := by ring
      _ ≤ 2 * ((1 / 2 : ℝ) ^ (d * r) / (q : ℝ) ^ 2) :=
        mul_le_mul hcor.1 hw (by unfold gaussianRegularityScale; positivity) (by norm_num)
      _ ≤ (1 / 2 : ℝ) ^ (d * r) := by
        rw [← mul_div_assoc]
        apply (div_le_iff₀ (by positivity : 0 < (q : ℝ) ^ 2)).mpr
        have hq2 : (2 : ℝ) ≤ (q : ℝ) ^ 2 := by nlinarith
        simpa only [mul_comm] using mul_le_mul_of_nonneg_left hq2
          (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) (d * r))
      _ ≤ _ := hpow
  linarith [hcor.2]

end SISToKSIS

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Module NumberField GeometricGaussianLHL MeasureTheory
open scoped ENNReal Classical
namespace SISToKSIS

def modularRegularityError (d m : ℕ) : ℝ := (1 / 2 : ℝ) ^ (d * m / 4)

theorem modularRegularityError_pos (d m : ℕ) : 0 < modularRegularityError d m := by
  unfold modularRegularityError
  positivity

theorem modularRegularityError_lt_one {d m : ℕ} (hD : 4 ≤ d * m) :
    modularRegularityError d m < 1 := by
  exact pow_lt_one₀ (by norm_num) (by norm_num) (by omega)

theorem modularRegularity_mass_le_error_sq {d m : ℕ} (hD : 2 ≤ d * m) :
    2 * (1 / 2 : ℝ) ^ (d * m) ≤ modularRegularityError d m ^ 2 := by
  have he : d * m = (d * m - 1) + 1 := by omega
  calc
    _ = (1 / 2 : ℝ) ^ (d * m - 1) := by nth_rw 1 [he]; rw [pow_succ]; ring
    _ ≤ (1 / 2 : ℝ) ^ (2 * (d * m / 4)) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    _ = _ := by unfold modularRegularityError; rw [← pow_mul, Nat.mul_comm]

theorem modularRegularityError_le_hint_error {d m k : ℕ} (hd : 0 < d)
    (hkm : 64 * k ≤ m) : modularRegularityError d m ≤ (1 / 2 : ℝ) ^ (2 * k) := by
  have hmD : m ≤ d * m := Nat.le_mul_of_pos_left _ hd
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)

theorem modularRegularityError_le_security_error {d m k security : ℕ}
    (hsecurity : security ≤ d * k) (hkm : 64 * k ≤ m) :
    modularRegularityError d m ≤ (1 / 2 : ℝ) ^ (16 * security) := by
  have hD : 64 * security ≤ d * m := by
    have h := Nat.mul_le_mul_left d hkm
    nlinarith
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)

theorem pmf_whitened_smoothing_failure_le {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] {D : ℕ} (p : PMF α)
    (L : α → Submodule ℤ (Euclidean D)) (T : Euclidean D →L[ℝ] Euclidean D)
    {t ε : ℝ} (ht : 0 ≤ t) (hT : ‖T‖ * t ≤ 1) (hε : 0 < ε)
    (hexpect : (∑' a, p a * nonzeroDualMass (L a) t) ≤ ENNReal.ofReal (ε ^ 2)) :
    p.toMeasure {a | ¬ SmoothAt (latticeImage T (L a)) ε 1} ≤ ENNReal.ofReal ε := by
  have h := pmf_markov_bound p (fun a => nonzeroDualMass (L a) t) hε hexpect
  have he : ENNReal.ofReal (ε ^ 2) / ENNReal.ofReal ε = ENNReal.ofReal ε := by
    rw [← ENNReal.ofReal_div_of_pos hε]
    congr 1
    field_simp
  rw [he] at h
  apply (measure_mono ?_).trans h
  intro a ha
  have hb : ENNReal.ofReal ε < nonzeroDualMass (latticeImage T (L a)) 1 := by
    simpa only [Set.mem_ofPred_eq, SmoothAt, zero_lt_one, true_and, not_le] using ha
  exact hb.trans_le (nonzeroDualMass_image_one_le (L a) T ht hT)

variable (K : Type*) [Field K] [NumberField K] {d : ℕ}
local instance regularityPublicMeasurable (q n r : ℕ) :
    MeasurableSpace (Matrix (Fin n) (Fin r) (ResidueRing K q)) := ⊤

theorem cyclotomicModularLattice_expected_mass_exponential
    (N : ℕ) [NeZero N] [IsCyclotomicExtension {N} ℚ K]
    (b : Basis (Fin d) ℤ (𝓞 K))
    (hGram : ∀ i j, canonicalGram K b i j = if i = j then (d : ℝ) else 0)
    (q : ℕ) [NeZero q] (hq : q.Prime) {g : ℕ}
    (I : Fin g → Ideal (𝓞 K)) [∀ j, (I j).IsMaximal]
    (hI : Function.Injective I) (hfac : Ideal.span ({(q : 𝓞 K)} : Set (𝓞 K)) = ∏ j, I j)
    (m r n : ℕ) (hm : 0 < m) (hD : 6 ≤ d * m) (hnr : n ≤ r)
    (hmr : m ≤ r) (hr : r ≤ 2 * (d * m)) {t : ℝ}
    (ht : modularWidthFloor d m n q ≤ t) :
    (∑ A : Matrix (Fin n) (Fin r) (ResidueRing K q),
      PMF.uniformOfFintype (Matrix (Fin n) (Fin r) (ResidueRing K q)) A *
        nonzeroDualMass (numberFieldModularLattice K b q A) t) ≤
      ENNReal.ofReal (2 * (1 / 2 : ℝ) ^ (d * m)) := by
  have hd := integralBasis_dimension_pos K b
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have htpos : 0 < t := (show 0 < 8 * (d : ℝ) * Real.sqrt m by positivity).trans_le
    ((modularWidthFloor_lower d m n hq.one_lt.le).trans ht)
  have h := cyclotomicModularLattice_expected_mass_split_budget K N b hdR hGram q I hI hfac
    r n m hnr (by omega) htpos
  exact h.trans (ENNReal.ofReal_le_ofReal (modularRegularity_numerical_budget hd hm hD hq.two_le
    (primeIdeal_factor_count_le_degree K b hq I hfac) hmr hr ht))

theorem cyclotomicModularSmoothingFailure_le
    (N : ℕ) [NeZero N] [IsCyclotomicExtension {N} ℚ K]
    (b : Basis (Fin d) ℤ (𝓞 K))
    (hGram : ∀ i j, canonicalGram K b i j = if i = j then (d : ℝ) else 0)
    (q : ℕ) [NeZero q] (hq : q.Prime) {g : ℕ}
    (I : Fin g → Ideal (𝓞 K)) [∀ j, (I j).IsMaximal]
    (hI : Function.Injective I) (hfac : Ideal.span ({(q : 𝓞 K)} : Set (𝓞 K)) = ∏ j, I j)
    (m r n : ℕ) (hm : 0 < m) (hD : 6 ≤ d * m) (hnr : n ≤ r)
    (hmr : m ≤ r) (hr : r ≤ 2 * (d * m))
    (S : Euclidean (r * d) ≃L[ℝ] Euclidean (r * d)) {t : ℝ}
    (ht : modularWidthFloor d m n q ≤ t) (hS : ‖S.symm.toContinuousLinearMap‖ * t ≤ 1) :
    modularSmoothingFailure (n := n) K b q S (modularRegularityError d m) ≤ modularRegularityError d m := by
  have hd := integralBasis_dimension_pos K b
  have htpos : 0 < t := (show 0 < 8 * (d : ℝ) * Real.sqrt m by positivity).trans_le
    ((modularWidthFloor_lower d m n hq.one_lt.le).trans ht)
  have hexpect := cyclotomicModularLattice_expected_mass_exponential K N b hGram q hq I hI hfac
    m r n hm hD hnr hmr hr ht
  have h := pmf_whitened_smoothing_failure_le
    (PMF.uniformOfFintype (Matrix (Fin n) (Fin r) (ResidueRing K q)))
    (numberFieldModularLattice K b q) S.symm.toContinuousLinearMap htpos.le hS
    (modularRegularityError_pos d m) (by
      rw [tsum_fintype]
      exact hexpect.trans (ENNReal.ofReal_le_ofReal (modularRegularity_mass_le_error_sq (by omega))))
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top h).trans_eq
    (ENNReal.toReal_ofReal (modularRegularityError_pos d m).le)

theorem paper_modularSmoothingFailure_le
    (N : ℕ) [NeZero N] [IsCyclotomicExtension {N} ℚ K]
    (b : Basis (Fin d) ℤ (𝓞 K))
    (hGram : ∀ i j, canonicalGram K b i j = if i = j then (d : ℝ) else 0)
    (q : ℕ) [NeZero q] (hq : q.Prime) {g : ℕ}
    (I : Fin g → Ideal (𝓞 K)) [∀ j, (I j).IsMaximal]
    (hI : Function.Injective I) (hfac : Ideal.span ({(q : 𝓞 K)} : Set (𝓞 K)) = ∏ j, I j)
    {m k n : ℕ} (hk : 0 < k) (hkm : 64 * k ≤ m) (hnm : n ≤ m)
    {u s₁ s₂ : ℝ} (h₁ : 0 < s₁) (h₂ : 0 < s₂) (hs : s₁ ≤ s₂)
    (hw : ArithmeticWindow d m n k q g u s₁ s₂) :
    modularSmoothingFailure (n := n) K b q (paperHintShape K b m k h₁.ne' h₂.ne')
      (modularRegularityError d m) ≤ modularRegularityError d m := by
  have hd := integralBasis_dimension_pos K b
  have hm : 0 < m := by omega
  have hmD : m ≤ d * m := Nat.le_mul_of_pos_left _ hd
  apply cyclotomicModularSmoothingFailure_le K N b hGram q hq I hI hfac m (m + k) n hm
    (by omega) (by omega) (by omega) (by omega) _ (arithmeticWindow_first_lower hw).1
  calc
    _ ≤ s₁⁻¹ * s₁ := mul_le_mul_of_nonneg_right (paperHintShape_inverse_norm_le K b m k h₁ h₂ hs) h₁.le
    _ = 1 := inv_mul_cancel₀ h₁.ne'

end SISToKSIS

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Module NumberField GeometricGaussianLHL
namespace SISToKSIS
variable (K : Type*) [Field K] [NumberField K] {d m k n : ℕ}

theorem paper_reverseSampling_explicit
    (N : ℕ) [NeZero N] [IsCyclotomicExtension {N} ℚ K]
    (b : Basis (Fin d) ℤ (𝓞 K))
    (hGram : ∀ i j, canonicalGram K b i j = if i = j then (d : ℝ) else 0)
    (q : ℕ) [NeZero q] (hq : q.Prime) {g : ℕ}
    (I : Fin g → Ideal (𝓞 K)) [∀ j, (I j).IsMaximal]
    (hI : Function.Injective I) (hfac : Ideal.span ({(q : 𝓞 K)} : Set (𝓞 K)) = ∏ j, I j)
    (hg : 0 < g) (hNorm : ∀ j, Ideal.absNorm (I j) ^ g = q ^ d)
    (centers : Fin k → Euclidean ((m + k) * d))
    (hk : 0 < k) (hkm : 64 * k ≤ m) (hnm : n ≤ m)
    {u s₁ s₂ : ℝ} (h₁ : 0 < s₁) (h₂ : 0 < s₂) (hs : s₁ ≤ s₂)
    (hw : ArithmeticWindow d m n k q g u s₁ s₂) :
    discreteTotalVariation
      (modularForwardLaw (n := n) K b q (paperHintShape K b m k h₁.ne' h₂.ne') centers)
      (modularReverseLaw (n := n) K b q (paperHintShape K b m k h₁.ne' h₂.ne') centers) ≤
      modularRegularityError d m +
        (g : ℝ) * k * (1 / 2 : ℝ) ^ ((m - k) * d) /
          ((1 - Real.exp (-((m : ℝ) * d) / 32)) * (1 - modularRegularityError d m)) +
        2 * k * modularRegularityError d m := by
  have hd := integralBasis_dimension_pos K b
  have hmD : m ≤ d * m := Nat.le_mul_of_pos_left _ hd
  have hε := modularRegularityError_pos d m
  have hεone := modularRegularityError_lt_one (d := d) (m := m) (by omega)
  have h := paper_reverseSampling_distance K b hGram q I hI hfac hg hNorm centers
    (by omega) hkm h₁ h₂ hs hw hε.le hεone
  have hS := paper_modularSmoothingFailure_le K N b hGram q hq I hI hfac hk hkm hnm h₁ h₂ hs hw
  linarith


/-- The paper bound with the common prime-ideal norms derived from cyclotomicity. -/
theorem paper_reverseSampling_from_factorization
    (N : ℕ) [NeZero N] [IsCyclotomicExtension {N} ℚ K]
    (b : Basis (Fin d) ℤ (𝓞 K))
    (hGram : ∀ i j, canonicalGram K b i j = if i = j then (d : ℝ) else 0)
    (q : ℕ) [NeZero q] (hq : q.Prime) {g : ℕ}
    (I : Fin g → Ideal (𝓞 K)) [∀ j, (I j).IsMaximal]
    (hI : Function.Injective I) (hfac : Ideal.span ({(q : 𝓞 K)} : Set (𝓞 K)) = ∏ j, I j)
    (centers : Fin k → Euclidean ((m + k) * d))
    (hk : 0 < k) (hkm : 64 * k ≤ m) (hnm : n ≤ m)
    {u s₁ s₂ : ℝ} (h₁ : 0 < s₁) (h₂ : 0 < s₂) (hs : s₁ ≤ s₂)
    (hw : ArithmeticWindow d m n k q g u s₁ s₂) :
    discreteTotalVariation
      (modularForwardLaw (n := n) K b q (paperHintShape K b m k h₁.ne' h₂.ne') centers)
      (modularReverseLaw (n := n) K b q (paperHintShape K b m k h₁.ne' h₂.ne') centers) ≤
      modularRegularityError d m +
        (g : ℝ) * k * (1 / 2 : ℝ) ^ ((m - k) * d) /
          ((1 - Real.exp (-((m : ℝ) * d) / 32)) * (1 - modularRegularityError d m)) +
        2 * k * modularRegularityError d m := by
  let : IsGalois ℚ K := IsCyclotomicExtension.isGalois {N} ℚ K
  exact paper_reverseSampling_explicit K N b hGram q hq I hI hfac
    (primeIdeal_factor_count_pos K b hq I hfac)
    (primeIdeal_factor_norm_power K b hq I hfac) centers hk hkm hnm h₁ h₂ hs hw


end SISToKSIS

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Module NumberField GeometricGaussianLHL
namespace SISToKSIS

/-- The explicit error of reversing the public-matrix and Gaussian-hint
sampling order at the paper's width window. -/
def modularReverseError (d m k g : ℕ) : ℝ :=
  modularRegularityError d m +
    (g : ℝ) * k * (1 / 2 : ℝ) ^ ((m - k) * d) /
      ((1 - Real.exp (-((m : ℝ) * d) / 32)) * (1 - modularRegularityError d m)) +
    2 * k * modularRegularityError d m

variable (K : Type*) [Field K] [NumberField K] {d m k n : ℕ}
local instance simulationPublicMeasurable (q n r : ℕ) :
    MeasurableSpace (Matrix (Fin n) (Fin r) (ResidueRing K q)) := ⊤
local instance simulationHintMeasurable (r k : ℕ) :
    MeasurableSpace (Matrix (Fin r) (Fin k) (𝓞 K)) := ⊤

theorem HintGeneratorBounds.source_forward_distance
    (N : ℕ) [NeZero N] [IsCyclotomicExtension {N} ℚ K]
    (b : Basis (Fin d) ℤ (𝓞 K))
    (hGram : ∀ i j, canonicalGram K b i j = if i = j then (d : ℝ) else 0)
    (q : ℕ) [NeZero q] (hq : q.Prime) {g : ℕ}
    (I : Fin g → Ideal (𝓞 K)) [∀ j, (I j).IsMaximal]
    (hI : Function.Injective I) (hfac : Ideal.span ({(q : 𝓞 K)} : Set (𝓞 K)) = ∏ j, I j)
    (hk : 0 < k) (hkm : 64 * k ≤ m) (hnm : n ≤ m)
    {u s₁ s₂ δlaw δnorm : ℝ} (h₁ : 0 < s₁) (h₂ : 0 < s₂) (hs : s₁ ≤ s₂)
    (hw : ArithmeticWindow d m n k q g u s₁ s₂)
    (sampler : Matrix (Fin k) (Fin m) (𝓞 K) → Fin k → PMF (Fin m → 𝓞 K))
    (hgen : HintGeneratorBounds K b (numberFieldMatrixLaw K b k m s₁ h₁.ne') h₂ sampler δlaw δnorm) :
    discreteTotalVariation
      (sourceSimulationLaw (n := n) K q
        (jointPMF (numberFieldMatrixLaw K b k m s₁ h₁.ne')
          (fun X => independentMatrixColumns (sampler X))))
      (modularForwardLaw (n := n) K b q (paperHintShape K b m k h₁.ne' h₂.ne')
        (paperHintCenters K b m k)) ≤ δlaw + modularReverseError d m k g := by
  have hS := hgen.source_reverse_distance (n := n) K b q h₁.ne' h₂ sampler
  have hR := paper_reverseSampling_from_factorization K N b hGram q hq I hI hfac
    (paperHintCenters K b m k) hk hkm hnm h₁ h₂ hs hw
  have ht := discreteTotalVariation_triangle
    (sourceSimulationLaw (n := n) K q
      (jointPMF (numberFieldMatrixLaw K b k m s₁ h₁.ne')
        (fun X => independentMatrixColumns (sampler X))))
    (modularReverseLaw (n := n) K b q (paperHintShape K b m k h₁.ne' h₂.ne')
      (paperHintCenters K b m k))
    (modularForwardLaw (n := n) K b q (paperHintShape K b m k h₁.ne' h₂.ne')
      (paperHintCenters K b m k))
  rw [discreteTotalVariation_symm (modularReverseLaw _ _ _ _ _)] at ht
  exact ht.trans (add_le_add hS hR)

/-- The centered k-SIS game's squared success transfers to the actual source
simulation. The extraction norm failure and finite implementation remain
separate obligations. -/
theorem paper_simulated_success_lower_bound {β : Type*}
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (N : ℕ) [NeZero N] [IsCyclotomicExtension {N} ℚ K]
    (b : Basis (Fin d) ℤ (𝓞 K))
    (hGram : ∀ i j, canonicalGram K b i j = if i = j then (d : ℝ) else 0)
    (q : ℕ) [NeZero q] (hq : q.Prime) {g : ℕ}
    (I : Fin g → Ideal (𝓞 K)) [∀ j, (I j).IsMaximal]
    (hI : Function.Injective I) (hfac : Ideal.span ({(q : 𝓞 K)} : Set (𝓞 K)) = ∏ j, I j)
    (hk : 0 < k) (hkm : 64 * k ≤ m) (hnm : n ≤ m)
    {u s₁ s₂ δlaw δnorm : ℝ} (h₁ : 0 < s₁) (h₂ : 0 < s₂) (hs : s₁ ≤ s₂)
    (hw : ArithmeticWindow d m n k q g u s₁ s₂)
    (sampler : Matrix (Fin k) (Fin m) (𝓞 K) → Fin k → PMF (Fin m → 𝓞 K))
    (hgen : HintGeneratorBounds K b (numberFieldMatrixLaw K b k m s₁ h₁.ne') h₂ sampler δlaw δnorm)
    (adversary : Matrix (Fin n) (Fin (m + k)) (ResidueRing K q) →
      Matrix (Fin (m + k)) (Fin k) (𝓞 K) → PMF β)
    (wins : Matrix (Fin n) (Fin (m + k)) (ResidueRing K q) →
      Matrix (Fin (m + k)) (Fin k) (𝓞 K) → β → Prop) :
    modularGameSuccess K b q (paperHintShape K b m k h₁.ne' h₂.ne') (fun _ => 0)
        adversary wins ^ 2 / Real.exp (2 * Real.pi) -
      (δlaw + modularReverseError d m k g) ≤
      successProbability
        (sourceSimulationLaw (n := n) K q
          (jointPMF (numberFieldMatrixLaw K b k m s₁ h₁.ne')
            (fun X => independentMatrixColumns (sampler X))))
        (fun z => adversary z.1 z.2) (fun z => wins z.1 z.2) := by
  have hshift := paper_modularGameSuccess_shift_bound K b h₁.ne' h₂.ne'
    (by omega : k ≤ m) hw adversary wins
  have hdist := hgen.source_forward_distance K N b hGram q hq I hI hfac
    hk hkm hnm h₁ h₂ hs hw sampler
  have htransfer := successProbability_sub_le
    (modularForwardLaw (n := n) K b q (paperHintShape K b m k h₁.ne' h₂.ne')
      (paperHintCenters K b m k))
    (sourceSimulationLaw (n := n) K q
      (jointPMF (numberFieldMatrixLaw K b k m s₁ h₁.ne')
        (fun X => independentMatrixColumns (sampler X))))
    (fun z => adversary z.1 z.2) (fun z => wins z.1 z.2)
    ((discreteTotalVariation_symm _ _).trans_le hdist)
  rw [← modularGameSuccess_eq_forward_success] at htransfer
  linarith

end SISToKSIS

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Module NumberField GeometricGaussianLHL MeasureTheory
namespace SISToKSIS
variable (K : Type*) [Field K] [NumberField K] {d m k n : ℕ}

local instance advantageMatrixMeasurable (a b : ℕ) :
    MeasurableSpace (Matrix (Fin a) (Fin b) (𝓞 K)) := ⊤
local instance advantagePublicMeasurable (q a b : ℕ) :
    MeasurableSpace (Matrix (Fin a) (Fin b) (ResidueRing K q)) := ⊤
local instance advantageVectorMeasurable (ι : Type*) : MeasurableSpace (ι → 𝓞 K) := ⊤

/-- The full analytical advantage bound for the actual reduction adversary.
The supplied hint-generator bounds must still be realized by a finite sampler
with the required accuracy and arithmetic cost. -/
theorem paper_SIS_reduction_advantage
    (N : ℕ) [NeZero N] [IsCyclotomicExtension {N} ℚ K]
    (b : Basis (Fin d) ℤ (𝓞 K))
    (hGram : ∀ i j, canonicalGram K b i j = if i = j then (d : ℝ) else 0)
    (q : ℕ) [NeZero q] (hq : q.Prime) {g : ℕ}
    (I : Fin g → Ideal (𝓞 K)) [∀ j, (I j).IsMaximal]
    (hI : Function.Injective I) (hfac : Ideal.span ({(q : 𝓞 K)} : Set (𝓞 K)) = ∏ j, I j)
    (hk : 0 < k) (hkm : 64 * k ≤ m) (hnm : n ≤ m)
    {u s₁ s₂ δlaw δnorm β₀ β₁ : ℝ} (h₁ : 0 < s₁) (h₂ : 0 < s₂) (hs : s₁ ≤ s₂)
    (hw : ArithmeticWindow d m n k q g u s₁ s₂)
    (hβ : normLoss m s₂ * β₁ ≤ β₀) (hδnorm : 0 ≤ δnorm)
    (sampler : Matrix (Fin k) (Fin m) (𝓞 K) → Fin k → PMF (Fin m → 𝓞 K))
    (hgen : HintGeneratorBounds K b (numberFieldMatrixLaw K b k m s₁ h₁.ne') h₂ sampler δlaw δnorm)
    (adversary : Matrix (Fin n) (Fin (m + k)) (ResidueRing K q) →
      Matrix (Fin (m + k)) (Fin k) (𝓞 K) → PMF (Fin m ⊕ Fin k → 𝓞 K)) :
    modularGameSuccess K b q (paperHintShape K b m k h₁.ne' h₂.ne') (fun _ => 0)
        adversary (simulatedKSISWins K q β₁) ^ 2 / Real.exp (2 * Real.pi) -
      (δlaw + modularReverseError d m k g + δnorm) ≤
      successProbability (PMF.uniformOfFintype (Matrix (Fin n) (Fin m) (ResidueRing K q)))
        (reductionAdversary K q
          (jointPMF (numberFieldMatrixLaw K b k m s₁ h₁.ne')
            (fun X => independentMatrixColumns (sampler X))) adversary)
        (IsSISSolution (residueMap K q) (canonicalRingNorm K) β₀) := by
  have hsimulation := paper_simulated_success_lower_bound K N b hGram q hq I hI hfac
    hk hkm hnm h₁ h₂ hs hw sampler hgen adversary (simulatedKSISWins K q β₁)
  have hextraction := reductionAdversary_success_loss K q
    (jointPMF (numberFieldMatrixLaw K b k m s₁ h₁.ne')
      (fun X => independentMatrixColumns (sampler X))) adversary
    (by omega : 0 < m) h₂ hβ hδnorm hgen.norm
  linarith

end SISToKSIS

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Module NumberField GeometricGaussianLHL
namespace SISToKSIS
variable (K : Type*) [Field K] [NumberField K] {m k n : ℕ}
variable {a : ℕ} [IsCyclotomicExtension {2 ^ (a + 1)} ℚ K] {ζ : K}

local instance parameterMatrixMeasurable (a b : ℕ) :
    MeasurableSpace (Matrix (Fin a) (Fin b) (𝓞 K)) := ⊤
local instance parameterPublicMeasurable (q a b : ℕ) :
    MeasurableSpace (Matrix (Fin a) (Fin b) (ResidueRing K q)) := ⊤
local instance parameterVectorMeasurable (ι : Type*) : MeasurableSpace (ι → 𝓞 K) := ⊤

/-- The actual SIS advantage with the polynomial geometric bound instantiated.
Accuracy of the supplied column sampler remains an implementation obligation. -/
theorem powerTwo_polynomial_SIS_reduction_advantage
    (hζ : IsPrimitiveRoot ζ (2 ^ (a + 1)))
    (q : ℕ) [NeZero q] (hq : q.Prime) {g : ℕ}
    (I : Fin g → Ideal (𝓞 K)) [∀ j, (I j).IsMaximal]
    (hI : Function.Injective I) (hfac : Ideal.span ({(q : 𝓞 K)} : Set (𝓞 K)) = ∏ j, I j)
    (hk : 0 < k) (hkm : 64 * k ≤ m) (hnm : n ≤ m)
    {ell u s₁ s₂ δsp δop εs β₀ β₁ : ℝ}
    (hell : 1 ≤ ell) (h₁ : 0 < s₁) (h₂ : 0 < s₂) (hs : s₁ ≤ s₂)
    (hw : ArithmeticWindow (2 ^ (a + 1)).totient m n k q g u s₁ s₂)
    (hbudget : ((k * (2 ^ (a + 1)).totient : ℕ) : ℝ) *
      Real.log (numberFieldPolynomialScale K (cyclotomicIntegralBasis K hζ) k m s₁ ell) +
      2 * Real.log (1 / realSecurityError (ell + 4)) ≤
      (m : ℝ) * Real.log (8 / 7))
    (hδsp : 0 < δsp) (hδspone : δsp < 1)
    (hcols : lowerSpectralColumnConstant *
      ((k : ℝ) + Real.log (2 * (2 ^ (a + 1)).totient / δsp)) ≤ m)
    (hδop : 0 < δop) (hδopone : δop < 1)
    (hlogop : Real.log (2 * (2 ^ (a + 1)).totient / δop) ≤ m) (hεs : 0 ≤ εs)
    (hwidth : numberFieldPolynomialSmoothingBound K (cyclotomicIntegralBasis K hζ) k m ell *
      (4 * s₁ * Real.sqrt m) ≤ s₂)
    (hβ : normLoss m s₂ * β₁ ≤ β₀)
    (sampler : Matrix (Fin k) (Fin m) (𝓞 K) → Fin k → PMF (Fin m → 𝓞 K))
    (haccuracy : SpectralSamplerAccuracy K (cyclotomicIntegralBasis K hζ)
      hk s₁ h₂ sampler εs)
    (adversary : Matrix (Fin n) (Fin (m + k)) (ResidueRing K q) →
      Matrix (Fin (m + k)) (Fin k) (𝓞 K) → PMF (Fin m ⊕ Fin k → 𝓞 K)) :
    modularGameSuccess K (cyclotomicIntegralBasis K hζ) q
        (paperHintShape K (cyclotomicIntegralBasis K hζ) m k h₁.ne' h₂.ne') (fun _ => 0)
        adversary (simulatedKSISWins K q β₁) ^ 2 / Real.exp (2 * Real.pi) -
      (hintDistributionError k (3 * realSecurityError (ell + 4)) δsp
          (2 * realSecurityError (ell + 4)) εs +
        modularReverseError (2 ^ (a + 1)).totient m k g +
        hintNormFailure k (3 * realSecurityError (ell + 4)) δsp δop εs) ≤
      successProbability (PMF.uniformOfFintype (Matrix (Fin n) (Fin m) (ResidueRing K q)))
        (reductionAdversary K q
          (jointPMF (numberFieldMatrixLaw K (cyclotomicIntegralBasis K hζ) k m s₁ h₁.ne')
            (fun X => independentMatrixColumns (sampler X))) adversary)
        (IsSISSolution (residueMap K q) (canonicalRingNorm K) β₀) := by
  have hd := integralBasis_dimension_pos K (cyclotomicIntegralBasis K hζ)
  have hδ : 0 < realSecurityError (ell + 4) := realSecurityError_pos _
  have hwidthX := arithmeticWindow_geometric_input_width hd (by omega : k ≤ m)
    hq.one_le hw
  rw [← (powerTwoBasis_constants K hζ).1] at hwidthX
  have hgen := powerTwo_polynomial_hint_generator_bounds K hζ hk (by omega : k < m)
    hell h₁ hs hwidthX hbudget hδsp hδspone hcols hδop hδopone hlogop hεs hwidth
    sampler haccuracy
  exact paper_SIS_reduction_advantage K (2 ^ (a + 1)) (cyclotomicIntegralBasis K hζ)
    (powerTwoGram_diagonal K hζ) q hq I hI hfac hk hkm hnm h₁ h₂ hs hw hβ
    (by unfold hintNormFailure; positivity) sampler hgen adversary

/-- The actual SIS advantage with the constant geometric bound instantiated.
Accuracy of the supplied column sampler remains an implementation obligation. -/
theorem powerTwo_constant_SIS_reduction_advantage
    (hζ : IsPrimitiveRoot ζ (2 ^ (a + 1)))
    (q : ℕ) [NeZero q] (hq : q.Prime) {g : ℕ}
    (I : Fin g → Ideal (𝓞 K)) [∀ j, (I j).IsMaximal]
    (hI : Function.Injective I) (hfac : Ideal.span ({(q : 𝓞 K)} : Set (𝓞 K)) = ∏ j, I j)
    (hk : 0 < k) (hkm : 64 * k ≤ m) (hnm : n ≤ m)
    {ell u s₁ s₂ δsp δop εs β₀ β₁ : ℝ}
    (hell : 1 ≤ ell) (h₁ : 0 < s₁) (h₂ : 0 < s₂) (hs : s₁ ≤ s₂)
    (hw : ArithmeticWindow (2 ^ (a + 1)).totient m n k q g u s₁ s₂)
    (hbudget : ((k * (2 ^ (a + 1)).totient : ℕ) : ℝ) *
      Real.log (powerTwoConstantScale (2 ^ (a + 1)).totient k m s₁ ell) +
      2 * Real.log (1 / realSecurityError (ell + 6)) ≤
      (m : ℝ) * Real.log (50 / 49))
    (hδsp : 0 < δsp) (hδspone : δsp < 1)
    (hcols : lowerSpectralColumnConstant *
      ((k : ℝ) + Real.log (2 * (2 ^ (a + 1)).totient / δsp)) ≤ m)
    (hδop : 0 < δop) (hδopone : δop < 1)
    (hlogop : Real.log (2 * (2 ^ (a + 1)).totient / δop) ≤ m) (hεs : 0 ≤ εs)
    (hwidth : powerTwoConstantSmoothingBound (2 ^ (a + 1)).totient k m ell *
      (4 * s₁ * Real.sqrt m) ≤ s₂)
    (hβ : normLoss m s₂ * β₁ ≤ β₀)
    (sampler : Matrix (Fin k) (Fin m) (𝓞 K) → Fin k → PMF (Fin m → 𝓞 K))
    (haccuracy : SpectralSamplerAccuracy K (cyclotomicIntegralBasis K hζ)
      hk s₁ h₂ sampler εs)
    (adversary : Matrix (Fin n) (Fin (m + k)) (ResidueRing K q) →
      Matrix (Fin (m + k)) (Fin k) (𝓞 K) → PMF (Fin m ⊕ Fin k → 𝓞 K)) :
    modularGameSuccess K (cyclotomicIntegralBasis K hζ) q
        (paperHintShape K (cyclotomicIntegralBasis K hζ) m k h₁.ne' h₂.ne') (fun _ => 0)
        adversary (simulatedKSISWins K q β₁) ^ 2 / Real.exp (2 * Real.pi) -
      (hintDistributionError k (3 * realSecurityError (ell + 6)) δsp
          (2 * realSecurityError (ell + 6)) εs +
        modularReverseError (2 ^ (a + 1)).totient m k g +
        hintNormFailure k (3 * realSecurityError (ell + 6)) δsp δop εs) ≤
      successProbability (PMF.uniformOfFintype (Matrix (Fin n) (Fin m) (ResidueRing K q)))
        (reductionAdversary K q
          (jointPMF (numberFieldMatrixLaw K (cyclotomicIntegralBasis K hζ) k m s₁ h₁.ne')
            (fun X => independentMatrixColumns (sampler X))) adversary)
        (IsSISSolution (residueMap K q) (canonicalRingNorm K) β₀) := by
  have hd := integralBasis_dimension_pos K (cyclotomicIntegralBasis K hζ)
  have hδ : 0 < realSecurityError (ell + 6) := realSecurityError_pos _
  have hwidthX := arithmeticWindow_constant_input_width hd hk (by omega : k ≤ m)
    hq.one_le hw
  have hgen := powerTwo_constant_hint_generator_bounds K hζ hk (by omega : k < m)
    hell h₁ hs hwidthX hbudget hδsp hδspone hcols hδop hδopone hlogop hεs hwidth
    sampler haccuracy
  exact paper_SIS_reduction_advantage K (2 ^ (a + 1)) (cyclotomicIntegralBasis K hζ)
    (powerTwoGram_diagonal K hζ) q hq I hI hfac hk hkm hnm h₁ h₂ hs hw hβ
    (by unfold hintNormFailure; positivity) sampler hgen adversary

end SISToKSIS

open Module NumberField GeometricGaussianLHL
namespace SISToKSIS
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable (K : Type*) [Field K] [NumberField K] {d m k n : ℕ}

local instance finiteInitialMatrixMeasurable (a b : ℕ) :
    MeasurableSpace (Matrix (Fin a) (Fin b) (𝓞 K)) := ⊤
local instance finiteInitialPublicMeasurable (q a b : ℕ) :
    MeasurableSpace (Matrix (Fin a) (Fin b) (ResidueRing K q)) := ⊤
local instance finiteInitialVectorMeasurable (ι : Type*) : MeasurableSpace (ι → 𝓞 K) := ⊤

/-- The reduction now uses the actual finite initial-matrix sampler. Its error
is charged once, after the complete dependent hint generation and adversary.
The shaped-column accuracy and its implementation remain explicit obligations. -/
theorem paper_SIS_reduction_advantage_finite_initial
    (N : ℕ) [NeZero N] [IsCyclotomicExtension {N} ℚ K]
    (basis : Basis (Fin d) ℤ (𝓞 K))
    (hGram : ∀ i j, canonicalGram K basis i j = if i = j then (d : ℝ) else 0)
    (q : ℕ) [NeZero q] (hq : q.Prime) {g : ℕ}
    (I : Fin g → Ideal (𝓞 K)) [∀ j, (I j).IsMaximal]
    (hI : Function.Injective I) (hfac : Ideal.span ({(q : 𝓞 K)} : Set (𝓞 K)) = ∏ j, I j)
    (hk : 0 < k) (hkm : 64 * k ≤ m) (hnm : n ≤ m)
    {u s₁ s₂ δlaw δnorm β₀ β₁ : ℝ} (h₁ : 0 < s₁) (h₂ : 0 < s₂) (hs : s₁ ≤ s₂)
    (hw : ArithmeticWindow d m n k q g u s₁ s₂)
    (hβ : normLoss m s₂ * β₁ ≤ β₀) (hδnorm : 0 ≤ δnorm)
    (widthNum widthDen precision : ℕ) (hNum : 0 < widthNum) (hDen : 0 < widthDen)
    (hencoding : s₁ = (widthNum : ℝ) / widthDen)
    (sampler : Matrix (Fin k) (Fin m) (𝓞 K) → Fin k → PMF (Fin m → 𝓞 K))
    (hgen : HintGeneratorBounds K basis (numberFieldMatrixLaw K basis k m s₁ h₁.ne') h₂ sampler δlaw δnorm)
    (adversary : Matrix (Fin n) (Fin (m + k)) (ResidueRing K q) →
      Matrix (Fin (m + k)) (Fin k) (𝓞 K) → PMF (Fin m ⊕ Fin k → 𝓞 K)) :
    modularGameSuccess K basis q (paperHintShape K basis m k h₁.ne' h₂.ne') (fun _ => 0)
        adversary (simulatedKSISWins K q β₁) ^ 2 / Real.exp (2 * Real.pi) -
      (δlaw + modularReverseError d m k g + δnorm + (1 / 2 : ℝ) ^ precision) ≤
      successProbability (PMF.uniformOfFintype (Matrix (Fin n) (Fin m) (ResidueRing K q)))
        (reductionAdversary K q
          (jointPMF (finiteInitialMatrixLaw K basis widthNum widthDen k m precision)
            (fun X => independentMatrixColumns (sampler X))) adversary)
        (IsSISSolution (residueMap K q) (canonicalRingNorm K) β₀) := by
  have hwindow : ArithmeticWindow d m n k q g u ((widthNum : ℝ) / widthDen) s₂ := by
    simpa only [hencoding] using hw
  have hinit := finiteInitialMatrixLaw_error_of_window K basis hGram hNum hDen hk
    (by omega : k ≤ m) hq.one_le hwindow precision
  have hinit' : discreteTotalVariation (numberFieldMatrixLaw K basis k m s₁ h₁.ne')
      (finiteInitialMatrixLaw K basis widthNum widthDen k m precision) ≤ (1 / 2 : ℝ) ^ precision := by
    rw [discreteTotalVariation_symm]
    simpa only [hencoding] using hinit
  have htransfer := reductionAdversary_success_initial_error K q
    (numberFieldMatrixLaw K basis k m s₁ h₁.ne')
    (finiteInitialMatrixLaw K basis widthNum widthDen k m precision) sampler adversary β₀ hinit'
  have hanalytic := paper_SIS_reduction_advantage K N basis hGram q hq I hI hfac
    hk hkm hnm h₁ h₂ hs hw hβ hδnorm sampler hgen adversary
  linarith

end
end SISToKSIS


open Module GeometricGaussianLHL
namespace SISToKSIS
set_option backward.isDefEq.respectTransparency false

section StoredGameMatrices
open NumberField
variable (K : Type*) [Field K] {d k m n : ℕ}

/-- The actual finite hint constructor supplies the exact matrix of the existing game. -/
theorem storedColumnHintsRun_game (T : BasisMultiplicationData d) (b : Basis (Fin d) ℤ (𝓞 K))
    (hT : T.Represents b) (one : Vector ℤ d) (hOne : ∀ l, one.get l = b.equivFun 1 l)
    (X : GaussianColumnData (k * d) m) (R : GaussianColumnData (m * d) k) :
    decodedCoefficientMatrix b (storedColumnHintsRun T one X R).value =
      generatedColumnMatrix K (decodedCoefficientMatrix b X, decodedCoefficientMatrix b R) :=
  storedColumnHintsRun_correct T b hT one hOne X R

/-- Supplied integer challenge representatives give exactly the public matrix in the modular game. -/
theorem storedPublicFromExtractionRun_game (T : BasisMultiplicationData d) (b : Basis (Fin d) ℤ (𝓞 K))
    (hT : T.Represents b) (one : Vector ℤ d) (hOne : ∀ l, one.get l = b.equivFun 1 l)
    (q : ℕ) (B : GaussianColumnData (n * d) m)
    (X : GaussianColumnData (k * d) m) (R : GaussianColumnData (m * d) k) :
    (decodedCoefficientMatrix b (storedPublicFromExtractionRun T q B
      (storedExtractionMatrixRun T one X R).value).value).map (residueMap K q) =
      sourcePublicMatrix K q (decodedCoefficientMatrix b X, decodedCoefficientMatrix b R)
        ((decodedCoefficientMatrix b B).map (residueMap K q)) := by
  rw [storedPublicFromExtractionRun_correct T b hT (residueMap K q) q (residueMap_modulus K q),
    storedExtractionMatrixRun_correct T b hT one hOne]
  simp only [Matrix.map_mul]
  ext i j
  simp [sourcePublicMatrix, Matrix.mul_apply, Matrix.submatrix]

/-- Applying the cached extraction matrix to a stored adversary output realizes exact solution extraction. -/
theorem storedRingMulRun_extractedVector (T : BasisMultiplicationData d) (b : Basis (Fin d) ℤ (𝓞 K))
    (hT : T.Represents b) (one : Vector ℤ d) (hOne : ∀ l, one.get l = b.equivFun 1 l)
    (X : GaussianColumnData (k * d) m) (R : GaussianColumnData (m * d) k)
    (V : GaussianColumnData ((m + k) * d) 1) :
    (fun i => decodedCoefficientMatrix b
      (storedRingMulRun T (storedExtractionMatrixRun T one X R).value V).value i 0) =
      extractedVector K (decodedCoefficientMatrix b X, decodedCoefficientMatrix b R)
        (fun i => decodedCoefficientMatrix b V (finSumFinEquiv i) 0) := by
  rw [storedRingMulRun_correct T b hT, storedExtractionMatrixRun_correct T b hT one hOne]
  change ((extractionMatrix (decodedCoefficientMatrix b X) (decodedCoefficientMatrix b R)).submatrix
    id finSumFinEquiv.symm).mulVec (fun i => decodedCoefficientMatrix b V i 0) = _
  rw [Matrix.submatrix_mulVec_equiv]
  rfl

end StoredGameMatrices

section BasisResidueCoordinates
variable {O : Type*} [CommRing O] {d : ℕ}

/-- The principal ideal generated by the integer modulus is coordinatewise divisibility. -/
theorem mem_modulusIdeal_iff_basis_dvd (b : Basis (Fin d) ℤ O) (q : ℕ) (x : O) :
    x ∈ Ideal.span ({(q : O)} : Set O) ↔ ∀ l, (q : ℤ) ∣ b.equivFun x l := by
  rw [Ideal.mem_span_singleton]
  constructor
  · rintro ⟨y, rfl⟩ l
    refine ⟨b.equivFun y l, ?_⟩
    have he : (q : O) * y = (q : ℤ) • y := by simp [zsmul_eq_mul]
    rw [he, map_smul]
    rfl
  · intro hx
    choose c hc using hx
    refine ⟨b.equivFun.symm c, ?_⟩
    apply b.equivFun.injective
    funext l
    have he : (q : O) * b.equivFun.symm c = (q : ℤ) • b.equivFun.symm c := by simp [zsmul_eq_mul]
    rw [he, map_smul, LinearEquiv.apply_symm_apply]
    exact hc l

/-- Equality in the ring quotient is exactly equality of the integral coordinates modulo `q`. -/
theorem basisQuotient_eq_iff_coordinates (b : Basis (Fin d) ℤ O) (q : ℕ) (x y : O) :
    Ideal.Quotient.mk (Ideal.span ({(q : O)} : Set O)) x =
      Ideal.Quotient.mk (Ideal.span ({(q : O)} : Set O)) y ↔
      ∀ l, (b.equivFun x l : ZMod q) = (b.equivFun y l : ZMod q) := by
  rw [Ideal.Quotient.eq, mem_modulusIdeal_iff_basis_dvd b q]
  simp only [map_sub, Pi.sub_apply, ← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, sub_eq_zero]

noncomputable def basisResidueRepresentative (b : Basis (Fin d) ℤ O) (q : ℕ) (z : Fin d → ZMod q) : O :=
  b.equivFun.symm (fun l => ((z l).val : ℤ))

theorem basisResidueRepresentative_coordinates (b : Basis (Fin d) ℤ O) (q : ℕ) (z : Fin d → ZMod q) (l : Fin d) :
    b.equivFun (basisResidueRepresentative b q z) l = ((z l).val : ℤ) := by
  rw [basisResidueRepresentative, LinearEquiv.apply_symm_apply]

noncomputable def basisResidueDecode (b : Basis (Fin d) ℤ O) (q : ℕ) (z : Fin d → ZMod q) :
    O ⧸ Ideal.span ({(q : O)} : Set O) :=
  Ideal.Quotient.mk _ (basisResidueRepresentative b q z)

theorem basisResidueDecode_bijective (b : Basis (Fin d) ℤ O) (q : ℕ) [NeZero q] :
    Function.Bijective (basisResidueDecode b q) := by
  constructor
  · intro z w h
    apply funext
    intro l
    have hc := (basisQuotient_eq_iff_coordinates b q _ _).mp h l
    simpa [basisResidueRepresentative_coordinates] using hc
  · intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    refine ⟨fun l => (b.equivFun x l : ZMod q), ?_⟩
    apply (basisQuotient_eq_iff_coordinates b q _ _).mpr
    intro l
    simp [basisResidueRepresentative_coordinates]

/-- A semantic equivalence for standard finite residue encodings; it is not a runtime quotient oracle. -/
noncomputable def basisResidueEquiv (b : Basis (Fin d) ℤ O) (q : ℕ) [NeZero q] :
    (Fin d → ZMod q) ≃ O ⧸ Ideal.span ({(q : O)} : Set O) :=
  Equiv.ofBijective (basisResidueDecode b q) (basisResidueDecode_bijective b q)

theorem basisResidueRepresentative_short (b : Basis (Fin d) ℤ O) (q : ℕ) [NeZero q]
    (z : Fin d → ZMod q) (l : Fin d) :
    0 ≤ b.equivFun (basisResidueRepresentative b q z) l ∧
    b.equivFun (basisResidueRepresentative b q z) l < (q : ℤ) ∧
    (b.equivFun (basisResidueRepresentative b q z) l).natAbs.size ≤ q.size := by
  rw [basisResidueRepresentative_coordinates]
  refine ⟨by positivity, by exact_mod_cast ZMod.val_lt (z l),
    ?_⟩
  change (z l).val.size ≤ q.size
  exact Nat.size_le_size (ZMod.val_lt (z l)).le

end BasisResidueCoordinates

end SISToKSIS


open Module NumberField GeometricGaussianLHL
namespace SISToKSIS
set_option backward.isDefEq.respectTransparency false

/-- Stored canonical integer representatives of residue coordinates. -/
def CanonicalResidueData (q R m : ℕ) :=
  {D : GaussianColumnData R m // ∀ j i, 0 ≤ gaussianColumnsOfData D j i ∧ gaussianColumnsOfData D j i < (q : ℤ)}

def canonicalResidueOfFn {q R m : ℕ} (f : Fin m → Fin R → Fin q) : CanonicalResidueData q R m :=
  ⟨Vector.ofFn (fun j => Vector.ofFn (fun i => ((f j i).val : ℤ))), by
    intro j i
    simp only [gaussianColumnsOfData, Vector.get, Vector.toArray_ofFn, Array.getElem_ofFn, Fin.val_cast]
    exact ⟨by positivity, by exact_mod_cast (f j i).isLt⟩⟩

theorem canonicalResidueOfFn_coordinates {q R m : ℕ} (f : Fin m → Fin R → Fin q) (j i) :
    gaussianColumnsOfData (canonicalResidueOfFn f).val j i = ((f j i).val : ℤ) := by
  simp [canonicalResidueOfFn, gaussianColumnsOfData, Vector.get]

/-- A finite encoding equivalence; both directions operate on stored integer or bounded-natural data. -/
def canonicalResidueDataEquiv (q R m : ℕ) : CanonicalResidueData q R m ≃ (Fin m → Fin R → Fin q) where
  toFun D j i := ⟨(gaussianColumnsOfData D.val j i).toNat, by
    have h := D.property j i
    omega⟩
  invFun := canonicalResidueOfFn
  left_inv D := by
    apply Subtype.ext
    apply gaussianColumnsOfData_injective
    funext j i
    rw [canonicalResidueOfFn_coordinates]
    exact Int.toNat_of_nonneg (D.property j i).1
  right_inv f := by
    funext j i
    apply Fin.ext
    simp [canonicalResidueOfFn_coordinates]

instance canonicalResidueDataFintype (q R m : ℕ) : Fintype (CanonicalResidueData q R m) :=
  Fintype.ofEquiv (Fin m → Fin R → Fin q) (canonicalResidueDataEquiv q R m).symm

instance canonicalResidueDataNonempty (q R m : ℕ) [NeZero q] : Nonempty (CanonicalResidueData q R m) :=
  ⟨canonicalResidueOfFn (fun _ _ => ⟨0, NeZero.pos q⟩)⟩

theorem canonicalResidueData_bits {q R m : ℕ} (D : CanonicalResidueData q R m) (j i) :
    (gaussianColumnsOfData D.val j i).natAbs.size ≤ q.size := by
  have h := D.property j i
  have ha : (gaussianColumnsOfData D.val j i).natAbs ≤ q := by
    exact_mod_cast (show ((gaussianColumnsOfData D.val j i).natAbs : ℤ) ≤ (q : ℤ) by
      rw [Int.natCast_natAbs, abs_of_nonneg h.1]
      exact h.2.le)
  exact Nat.size_le_size ha

theorem canonicalResidueData_totalBits {q R m : ℕ} (D : CanonicalResidueData q R m) :
    gaussianColumnsBits D.val ≤ m * R * q.size := by
  unfold gaussianColumnsBits
  calc
    _ ≤ ∑ _ : Fin m, ∑ _ : Fin R, q.size := Finset.sum_le_sum (fun j _ =>
      Finset.sum_le_sum (fun i _ => canonicalResidueData_bits D j i))
    _ = _ := by simp; ring

section CanonicalMatrixSemantics
variable {O : Type*} [CommRing O] {d r s : ℕ}

noncomputable def decodedResidueMatrix (b : Basis (Fin d) ℤ O) (q : ℕ)
    (D : CanonicalResidueData q (r * d) s) : Matrix (Fin r) (Fin s) (O ⧸ Ideal.span ({(q : O)} : Set O)) :=
  (decodedCoefficientMatrix b D.val).map (Ideal.Quotient.mk _)

theorem decodedResidueMatrix_injective (b : Basis (Fin d) ℤ O) (q : ℕ) :
    Function.Injective (@decodedResidueMatrix O _ d r s b q) := by
  intro A B h
  apply Subtype.ext
  apply gaussianColumnsOfData_injective
  funext j i
  obtain ⟨⟨row, l⟩, rfl⟩ := finProdFinEquiv.surjective i
  have he := congrFun (congrFun h row) j
  have hc := (basisQuotient_eq_iff_coordinates b q _ _).mp he l
  rw [decodedCoefficientMatrix_coordinates, decodedCoefficientMatrix_coordinates,
    ZMod.intCast_eq_intCast_iff'] at hc
  rw [Int.emod_eq_of_lt (A.property j _).1 (A.property j _).2,
    Int.emod_eq_of_lt (B.property j _).1 (B.property j _).2] at hc
  exact hc

theorem decodedResidueMatrix_surjective (b : Basis (Fin d) ℤ O) (q : ℕ) [NeZero q] :
    Function.Surjective (@decodedResidueMatrix O _ d r s b q) := by
  intro Y
  let Z : Fin r → Fin s → Fin d → ZMod q := fun i j => (basisResidueEquiv b q).symm (Y i j)
  let D : CanonicalResidueData q (r * d) s := canonicalResidueOfFn (fun j i =>
    ⟨(Z (finProdFinEquiv.symm i).1 j (finProdFinEquiv.symm i).2).val, ZMod.val_lt _⟩)
  refine ⟨D, ?_⟩
  ext i j
  have hc : decodedCoefficientMatrix b D.val i j = basisResidueRepresentative b q (Z i j) := by
    apply b.equivFun.injective
    funext l
    rw [decodedCoefficientMatrix_coordinates, basisResidueRepresentative_coordinates]
    simp only [D, canonicalResidueOfFn_coordinates, Equiv.symm_apply_apply]
  change Ideal.Quotient.mk _ (decodedCoefficientMatrix b D.val i j) = _
  rw [hc]
  exact (basisResidueEquiv b q).apply_symm_apply (Y i j)

/-- Canonical stored matrix encodings are in bijection with the exact quotient matrices in the game. -/
noncomputable def canonicalResidueMatrixEquiv (b : Basis (Fin d) ℤ O) (q : ℕ) [NeZero q] :
    CanonicalResidueData q (r * d) s ≃ Matrix (Fin r) (Fin s) (O ⧸ Ideal.span ({(q : O)} : Set O)) :=
  Equiv.ofBijective (decodedResidueMatrix b q)
    ⟨decodedResidueMatrix_injective b q, decodedResidueMatrix_surjective b q⟩

theorem canonicalResidueMatrix_uniform (b : Basis (Fin d) ℤ O) (q : ℕ) [NeZero q]
    [Fintype (O ⧸ Ideal.span ({(q : O)} : Set O))] :
    (PMF.uniformOfFintype (CanonicalResidueData q (r * d) s)).map (decodedResidueMatrix b q) =
      PMF.uniformOfFintype (Matrix (Fin r) (Fin s) (O ⧸ Ideal.span ({(q : O)} : Set O))) :=
  uniform_map_equiv (canonicalResidueMatrixEquiv b q)

theorem canonicalResidueMatrix_reencode (b : Basis (Fin d) ℤ O) (q : ℕ) [NeZero q]
    (D : CanonicalResidueData q (r * d) s) :
    (canonicalResidueMatrixEquiv b q).symm (decodedResidueMatrix b q D) = D :=
  (canonicalResidueMatrixEquiv b q).symm_apply_apply D

end CanonicalMatrixSemantics

/-- A supplied finite-word adversary on canonical public matrices and stored integer hints.
The randomness prescription itself has a declared cost. -/
structure EncodedKSISOracle (q d n M k : ℕ) where
  randomness : CanonicalResidueData q (n * d) M → GaussianColumnData (M * d) k → Costed ℕ
  run : ∀ A H, Fin (2 ^ (randomness A H).value) → Costed (GaussianColumnData (M * d) 1)

abbrev EncodedKSISOracle.Seed {q d n M k : ℕ} (O : EncodedKSISOracle q d n M k)
    (A : CanonicalResidueData q (n * d) M) (H : GaussianColumnData (M * d) k) :=
  Fin (2 ^ (O.randomness A H).value)

/-- Charge the randomness prescription, the random word, and the supplied adversary execution. -/
def EncodedKSISOracle.call {q d n M k : ℕ} (O : EncodedKSISOracle q d n M k)
    (A : CanonicalResidueData q (n * d) M) (H : GaussianColumnData (M * d) k) (seed : O.Seed A H) :
    Costed (GaussianColumnData (M * d) 1) :=
  let random := O.randomness A H
  let answer := O.run A H seed
  ⟨answer.value, random.steps + random.value + answer.steps + 1⟩

def encodedOracleInputSize {q d n M k : ℕ}
    (A : CanonicalResidueData q (n * d) M) (H : GaussianColumnData (M * d) k) : ℕ :=
  d + n + M + k + q.size + gaussianColumnsBits A.val + gaussianColumnsBits H

/-- The supplied oracle's uniform cost/output contract in the declared arithmetic model. -/
def EncodedKSISOracle.PolynomialBound {q d n M k : ℕ} (O : EncodedKSISOracle q d n M k) (C e : ℕ) : Prop :=
  ∀ A H (seed : O.Seed A H), (O.call A H seed).steps + gaussianColumnsBits (O.call A H seed).value ≤
    C * (encodedOracleInputSize A H + 1) ^ e

noncomputable section

def EncodedKSISOracle.seedLaw {q d n M k : ℕ} (O : EncodedKSISOracle q d n M k)
    (A : CanonicalResidueData q (n * d) M) (H : GaussianColumnData (M * d) k) : PMF (O.Seed A H) :=
  PMF.uniformOfFintype _

def EncodedKSISOracle.callLaw {q d n M k : ℕ} (O : EncodedKSISOracle q d n M k)
    (A : CanonicalResidueData q (n * d) M) (H : GaussianColumnData (M * d) k) : PMF (GaussianColumnData (M * d) 1) :=
  (O.seedLaw A H).map (fun seed => (O.call A H seed).value)

end

def canonicalPreparedPublic {d n k m q : ℕ} (T : BasisMultiplicationData d) (one : Vector ℤ d)
    (hq : 0 < q) (B : GaussianColumnData (n * d) m)
    (X : GaussianColumnData (k * d) m) (R : GaussianColumnData (m * d) k) : CanonicalResidueData q (n * d) (m + k) :=
  ⟨(storedReductionPreparationRun T one q B X R).value.2.2, fun j i =>
    storedColumnsModRun_range hq (storedRingMulRun T B (storedExtractionMatrixRun T one X R).value).value j i⟩

abbrev StoredOracleStageSeed {d n k m q : ℕ} (T : BasisMultiplicationData d) (one : Vector ℤ d)
    (hq : 0 < q) (O : EncodedKSISOracle q d n (m + k) k) (B : GaussianColumnData (n * d) m)
    (X : GaussianColumnData (k * d) m) (R : GaussianColumnData (m * d) k) :=
  O.Seed (canonicalPreparedPublic T one hq B X R) (storedColumnHintsRun T one X R).value

/-- Prepare the inputs, invoke the supplied oracle, and apply the cached extraction matrix. -/
def storedOracleStageRun {d n k m q : ℕ} (T : BasisMultiplicationData d) (one : Vector ℤ d)
    (hq : 0 < q) (O : EncodedKSISOracle q d n (m + k) k) (B : GaussianColumnData (n * d) m)
    (X : GaussianColumnData (k * d) m) (R : GaussianColumnData (m * d) k)
    (seed : StoredOracleStageSeed T one hq O B X R) : Costed (GaussianColumnData (m * d) 1) :=
  let prepared := storedReductionPreparationRun T one q B X R
  let A : CanonicalResidueData q (n * d) (m + k) :=
    ⟨prepared.value.2.2, (canonicalPreparedPublic T one hq B X R).property⟩
  let answer := O.call A prepared.value.1 seed
  let result := storedRingMulRun T prepared.value.2.1 answer.value
  ⟨result.value, prepared.steps + answer.steps + result.steps + 3⟩

theorem storedOracleStageRun_value {d n k m q : ℕ} (T : BasisMultiplicationData d) (one : Vector ℤ d)
    (hq : 0 < q) (O : EncodedKSISOracle q d n (m + k) k) (B : GaussianColumnData (n * d) m)
    (X : GaussianColumnData (k * d) m) (R : GaussianColumnData (m * d) k)
    (seed : StoredOracleStageSeed T one hq O B X R) :
    (storedOracleStageRun T one hq O B X R seed).value =
      (storedRingMulRun T (storedExtractionMatrixRun T one X R).value
        (O.call (canonicalPreparedPublic T one hq B X R) (storedColumnHintsRun T one X R).value seed).value).value := rfl

noncomputable section

def storedOracleStageLaw {d n k m q : ℕ} (T : BasisMultiplicationData d) (one : Vector ℤ d)
    (hq : 0 < q) (O : EncodedKSISOracle q d n (m + k) k) (B : GaussianColumnData (n * d) m)
    (X : GaussianColumnData (k * d) m) (R : GaussianColumnData (m * d) k) : PMF (GaussianColumnData (m * d) 1) :=
  (O.seedLaw (canonicalPreparedPublic T one hq B X R) (storedColumnHintsRun T one X R).value).map
    (fun seed => (storedOracleStageRun T one hq O B X R seed).value)

theorem storedOracleStageLaw_eq {d n k m q : ℕ} (T : BasisMultiplicationData d) (one : Vector ℤ d)
    (hq : 0 < q) (O : EncodedKSISOracle q d n (m + k) k) (B : GaussianColumnData (n * d) m)
    (X : GaussianColumnData (k * d) m) (R : GaussianColumnData (m * d) k) :
    storedOracleStageLaw T one hq O B X R =
      (O.callLaw (canonicalPreparedPublic T one hq B X R) (storedColumnHintsRun T one X R).value).map
        (fun V => (storedRingMulRun T (storedExtractionMatrixRun T one X R).value V).value) := by
  simp only [storedOracleStageLaw, EncodedKSISOracle.callLaw, PMF.map_comp,
    Function.comp_def, storedOracleStageRun_value]

end

abbrev EncodedReductionTape {d n k m q : ℕ} (T : BasisMultiplicationData d) (one : Vector ℤ d)
    (hq : 0 < q) (O : EncodedKSISOracle q d n (m + k) k) (B : GaussianColumnData (n * d) m)
    (a b s : ℕ) (w : ℚ) (p : ℕ) :=
  (initial : GaussianHintTape T a b k m s w p) ×
    StoredOracleStageSeed T one hq O B (gaussianHintRun T a b k m s w p initial).value.1
      (gaussianHintRun T a b k m s w p initial).value.2

/-- The complete finite reduction program, from Gaussian words through oracle execution to the SIS answer. -/
def encodedReductionRun {d n k m q : ℕ} (T : BasisMultiplicationData d) (one : Vector ℤ d)
    (hq : 0 < q) (O : EncodedKSISOracle q d n (m + k) k) (B : GaussianColumnData (n * d) m)
    (a b s : ℕ) (w : ℚ) (p : ℕ) (tape : EncodedReductionTape T one hq O B a b s w p) :
    Costed (GaussianColumnData (m * d) 1) :=
  let blocks := gaussianHintRun T a b k m s w p tape.1
  let final := storedOracleStageRun T one hq O B blocks.value.1 blocks.value.2 tape.2
  ⟨final.value, blocks.steps + final.steps + 1⟩

noncomputable section

def encodedReductionTapeLaw {d n k m q : ℕ} (T : BasisMultiplicationData d) (one : Vector ℤ d)
    (hq : 0 < q) (O : EncodedKSISOracle q d n (m + k) k) (B : GaussianColumnData (n * d) m)
    (a b s : ℕ) (w : ℚ) (p : ℕ) : PMF (EncodedReductionTape T one hq O B a b s w p) :=
  (gaussianHintTapeLaw T a b k m s w p).bind fun initial =>
    let blocks := (gaussianHintRun T a b k m s w p initial).value
    (O.seedLaw (canonicalPreparedPublic T one hq B blocks.1 blocks.2)
      (storedColumnHintsRun T one blocks.1 blocks.2).value).map (Sigma.mk initial)

def encodedReductionRunLaw {d n k m q : ℕ} (T : BasisMultiplicationData d) (one : Vector ℤ d)
    (hq : 0 < q) (O : EncodedKSISOracle q d n (m + k) k) (B : GaussianColumnData (n * d) m)
    (a b s : ℕ) (w : ℚ) (p : ℕ) : PMF (GaussianColumnData (m * d) 1) :=
  (encodedReductionTapeLaw T one hq O B a b s w p).map
    (fun tape => (encodedReductionRun T one hq O B a b s w p tape).value)

theorem encodedReductionRunLaw_eq {d n k m q : ℕ} (T : BasisMultiplicationData d) (one : Vector ℤ d)
    (hq : 0 < q) (O : EncodedKSISOracle q d n (m + k) k) (B : GaussianColumnData (n * d) m)
    (a b s : ℕ) (w : ℚ) (p : ℕ) :
    encodedReductionRunLaw T one hq O B a b s w p =
      (gaussianHintRunLaw T a b k m s w p).bind (fun z => storedOracleStageLaw T one hq O B z.1 z.2) := by
  simp only [encodedReductionRunLaw, encodedReductionTapeLaw, PMF.map_bind, PMF.map_comp,
    Function.comp_def, gaussianHintRunLaw, PMF.bind_map, storedOracleStageLaw, encodedReductionRun]

end

noncomputable section
variable (K : Type*) [Field K] {d n k m q : ℕ}

def decodedSISAnswer (b : Basis (Fin d) ℤ (𝓞 K)) (V : GaussianColumnData (m * d) 1) : Fin m → 𝓞 K :=
  fun i => decodedCoefficientMatrix b V i 0

def decodedKSISAnswer (b : Basis (Fin d) ℤ (𝓞 K)) (V : GaussianColumnData ((m + k) * d) 1) : Fin m ⊕ Fin k → 𝓞 K :=
  fun i => decodedCoefficientMatrix b V (finSumFinEquiv i) 0

/-- Mathematical interpretation of the supplied finite adversary, using unique input encodings. -/
def decodedKSISOracle [NeZero q] (b : Basis (Fin d) ℤ (𝓞 K)) (O : EncodedKSISOracle q d n (m + k) k)
    (A : Matrix (Fin n) (Fin (m + k)) (ResidueRing K q)) (H : Matrix (Fin (m + k)) (Fin k) (𝓞 K)) :
    PMF (Fin m ⊕ Fin k → 𝓞 K) :=
  (O.callLaw ((canonicalResidueMatrixEquiv b q).symm A) (encodedRingMatrix b H)).map (decodedKSISAnswer K b)

theorem decodedKSISOracle_on_data [NeZero q] (b : Basis (Fin d) ℤ (𝓞 K)) (O : EncodedKSISOracle q d n (m + k) k)
    (A : CanonicalResidueData q (n * d) (m + k)) (H : GaussianColumnData ((m + k) * d) k) :
    decodedKSISOracle K b O (decodedResidueMatrix b q A) (decodedCoefficientMatrix b H) =
      (O.callLaw A H).map (decodedKSISAnswer K b) := by
  rw [decodedKSISOracle, canonicalResidueMatrix_reencode, encodedRingMatrix_decodedCoefficientMatrix]

theorem storedOracleStageLaw_game [NeZero q] (T : BasisMultiplicationData d) (b : Basis (Fin d) ℤ (𝓞 K))
    (hT : T.Represents b) (one : Vector ℤ d) (hOne : ∀ l, one.get l = b.equivFun 1 l)
    (hq : 0 < q) (O : EncodedKSISOracle q d n (m + k) k) (B : GaussianColumnData (n * d) m)
    (X : GaussianColumnData (k * d) m) (R : GaussianColumnData (m * d) k) :
    (storedOracleStageLaw T one hq O B X R).map (decodedSISAnswer K b) =
      (decodedKSISOracle K b O
        (sourcePublicMatrix K q (decodedCoefficientMatrix b X, decodedCoefficientMatrix b R)
          ((decodedCoefficientMatrix b B).map (residueMap K q)))
        (generatedColumnMatrix K (decodedCoefficientMatrix b X, decodedCoefficientMatrix b R))).map
          (extractedVector K (decodedCoefficientMatrix b X, decodedCoefficientMatrix b R)) := by
  have hA : decodedResidueMatrix b q (canonicalPreparedPublic T one hq B X R) =
      sourcePublicMatrix K q (decodedCoefficientMatrix b X, decodedCoefficientMatrix b R)
        ((decodedCoefficientMatrix b B).map (residueMap K q)) :=
    storedPublicFromExtractionRun_game K T b hT one hOne q B X R
  rw [← hA, ← storedColumnHintsRun_game K T b hT one hOne X R,
    decodedKSISOracle_on_data, storedOracleStageLaw_eq, PMF.map_comp, PMF.map_comp]
  congr 1
  funext V
  exact storedRingMulRun_extractedVector K T b hT one hOne X R V

/-- The full finite program, including the actual oracle call, has exactly the analytical reduction law. -/
theorem encodedReductionRun_field_law [NeZero q] (T : BasisMultiplicationData d) (b : Basis (Fin d) ℤ (𝓞 K))
    (hT : T.Represents b) (one : Vector ℤ d) (hOne : ∀ l, one.get l = b.equivFun 1 l)
    (hq : 0 < q) (O : EncodedKSISOracle q d n (m + k) k) (B : GaussianColumnData (n * d) m)
    (a c s : ℕ) (w : ℚ) (p : ℕ) :
    (encodedReductionRunLaw T one hq O B a c s w p).map (decodedSISAnswer K b) =
      reductionAdversary K q
        (jointPMF (finiteInitialMatrixLaw K b a c k m s)
          (fun X => independentMatrixColumns (basisDataHintSampler K b T w p X)))
        (decodedKSISOracle K b O) ((decodedCoefficientMatrix b B).map (residueMap K q)) := by
  rw [encodedReductionRunLaw_eq, PMF.map_bind, reductionAdversary,
    ← gaussianHintRun_field_law K b T a c k m s w p, PMF.bind_map]
  apply congrArg (fun f => (gaussianHintRunLaw T a c k m s w p).bind f)
  funext z
  exact storedOracleStageLaw_game K T b hT one hOne hq O B z.1 z.2

/-- Uniform finite challenge encodings and the full execution give the exact joint SIS game. -/
theorem encodedReduction_joint_game [NumberField K] [NeZero q] (T : BasisMultiplicationData d)
    (b : Basis (Fin d) ℤ (𝓞 K)) (hT : T.Represents b) (one : Vector ℤ d)
    (hOne : ∀ l, one.get l = b.equivFun 1 l) (hq : 0 < q)
    (O : EncodedKSISOracle q d n (m + k) k) (a c s : ℕ) (w : ℚ) (p : ℕ) :
    (jointPMF (PMF.uniformOfFintype (CanonicalResidueData q (n * d) m))
      (fun B => encodedReductionRunLaw T one hq O B.val a c s w p)).map
        (fun z => (decodedResidueMatrix b q z.1, decodedSISAnswer K b z.2)) =
      jointPMF (PMF.uniformOfFintype (Matrix (Fin n) (Fin m) (ResidueRing K q)))
        (reductionAdversary K q
          (jointPMF (finiteInitialMatrixLaw K b a c k m s)
            (fun X => independentMatrixColumns (basisDataHintSampler K b T w p X))) (decodedKSISOracle K b O)) := by
  rw [← canonicalResidueMatrix_uniform b q, jointPMF_map_input]
  have hkernel : (fun B : CanonicalResidueData q (n * d) m =>
      (encodedReductionRunLaw T one hq O B.val a c s w p).map (decodedSISAnswer K b)) =
      (fun B => reductionAdversary K q
        (jointPMF (finiteInitialMatrixLaw K b a c k m s)
          (fun X => independentMatrixColumns (basisDataHintSampler K b T w p X)))
        (decodedKSISOracle K b O) (decodedResidueMatrix b q B)) := by
    funext B
    exact encodedReductionRun_field_law K T b hT one hOne hq O B.val a c s w p
  rw [← hkernel, jointPMF_map_second, PMF.map_comp]
  rfl

end

theorem gaussianColumnsBits_le {R m L : ℕ} (D : GaussianColumnData R m)
    (hD : ∀ j i, (gaussianColumnsOfData D j i).natAbs.size ≤ L) :
    gaussianColumnsBits D ≤ m * R * L := by
  unfold gaussianColumnsBits
  calc
    _ ≤ ∑ _ : Fin m, ∑ _ : Fin R, L := Finset.sum_le_sum (fun j _ =>
      Finset.sum_le_sum (fun i _ => hD j i))
    _ = _ := by simp; ring

def storedOracleInputBudget (d n k m L Q : ℕ) : ℕ :=
  d + n + (m + k) + k + Q + (m + k) * (n * d) * Q +
    k * ((m + k) * d) * (storedRingMulBits d m L + 2)

theorem storedOracleInputSize_le {d n k m q L : ℕ} (T : BasisMultiplicationData d) (one : Vector ℤ d)
    (hq : 0 < q) (B : GaussianColumnData (n * d) m)
    (X : GaussianColumnData (k * d) m) (R : GaussianColumnData (m * d) k)
    (hT : ∀ t i l, (basisMultiplicationEntry T t i l).natAbs.size ≤ L)
    (hOne : ∀ l, (one.get l).natAbs.size ≤ L)
    (hX : ∀ j i, (gaussianColumnsOfData X j i).natAbs.size ≤ L)
    (hR : ∀ j i, (gaussianColumnsOfData R j i).natAbs.size ≤ L) :
    encodedOracleInputSize (canonicalPreparedPublic T one hq B X R) (storedColumnHintsRun T one X R).value ≤
      storedOracleInputBudget d n k m L q.size := by
  have ha := canonicalResidueData_totalBits (canonicalPreparedPublic T one hq B X R)
  have hh := gaussianColumnsBits_le _ (storedColumnHintsRun_bounds T one X R hT hOne hX hR).2
  unfold encodedOracleInputSize storedOracleInputBudget
  omega

def storedOracleCallBudget (C e d n k m L Q : ℕ) : ℕ :=
  C * (storedOracleInputBudget d n k m L Q + 1) ^ e

def storedOracleStageBudget (C e d n k m L Q : ℕ) : ℕ :=
  storedPreparationBudget d n k m L Q + storedOracleCallBudget C e d n k m L Q +
    storedRingMulBudget d m (m + k) 1
      (L + (storedRingMulBits d k L + 2) + storedOracleCallBudget C e d n k m L Q) + 3

def storedOracleStageOutputBits (C e d n k m L Q : ℕ) : ℕ :=
  storedRingMulBits d (m + k)
    (L + (storedRingMulBits d k L + 2) + storedOracleCallBudget C e d n k m L Q)

theorem storedOracleStageRun_bounds {d n k m q L C e : ℕ} (T : BasisMultiplicationData d) (one : Vector ℤ d)
    (hq : 0 < q) (O : EncodedKSISOracle q d n (m + k) k) (hO : O.PolynomialBound C e)
    (B : GaussianColumnData (n * d) m) (X : GaussianColumnData (k * d) m) (R : GaussianColumnData (m * d) k)
    (hT : ∀ t i l, (basisMultiplicationEntry T t i l).natAbs.size ≤ L)
    (hOne : ∀ l, (one.get l).natAbs.size ≤ L)
    (hB : ∀ j i, (gaussianColumnsOfData B j i).natAbs.size ≤ L)
    (hX : ∀ j i, (gaussianColumnsOfData X j i).natAbs.size ≤ L)
    (hR : ∀ j i, (gaussianColumnsOfData R j i).natAbs.size ≤ L)
    (seed : StoredOracleStageSeed T one hq O B X R) :
    (storedOracleStageRun T one hq O B X R seed).steps ≤ storedOracleStageBudget C e d n k m L q.size ∧
    ∀ j i, (gaussianColumnsOfData (storedOracleStageRun T one hq O B X R seed).value j i).natAbs.size ≤
      storedOracleStageOutputBits C e d n k m L q.size := by
  let answer := O.call (canonicalPreparedPublic T one hq B X R) (storedColumnHintsRun T one X R).value seed
  have hin := storedOracleInputSize_le T one hq B X R hT hOne hX hR
  have ho : answer.steps + gaussianColumnsBits answer.value ≤ storedOracleCallBudget C e d n k m L q.size :=
    (hO _ _ seed).trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_left (Nat.add_le_add_right hin 1) e))
  have he := storedExtractionMatrixRun_bounds T one X R hT hOne hX hR
  have hout : ∀ j i, (gaussianColumnsOfData answer.value j i).natAbs.size ≤ storedOracleCallBudget C e d n k m L q.size :=
    fun j i => (gaussianColumns_entry_bits answer.value j i).trans (by omega)
  let V := L + (storedRingMulBits d k L + 2) + storedOracleCallBudget C e d n k m L q.size
  have hm := storedRingMulRun_bounds T (storedExtractionMatrixRun T one X R).value answer.value
    (L := V) (fun t i l => (hT t i l).trans (by dsimp [V]; omega))
    (fun j i => (he.2 j i).trans (by dsimp [V]; omega))
    (fun j i => (hout j i).trans (by dsimp [V]; omega))
  constructor
  · have hp := storedReductionPreparationRun_steps T one q B X R hT hOne hB hX hR
    exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add hp (show answer.steps ≤ _ by omega)) hm.1) 3
  · exact hm.2

theorem storedOracleInputBudget_mono {d d' n n' k k' m m' L L' Q Q' : ℕ}
    (hd : d ≤ d') (hn : n ≤ n') (hk : k ≤ k') (hm : m ≤ m') (hL : L ≤ L') (hQ : Q ≤ Q') :
    storedOracleInputBudget d n k m L Q ≤ storedOracleInputBudget d' n' k' m' L' Q' := by
  unfold storedOracleInputBudget storedRingMulBits
  gcongr

theorem storedOracleStageBudget_mono (C e : ℕ) {d d' n n' k k' m m' L L' Q Q' : ℕ}
    (hd : d ≤ d') (hn : n ≤ n') (hk : k ≤ k') (hm : m ≤ m') (hL : L ≤ L') (hQ : Q ≤ Q') :
    storedOracleStageBudget C e d n k m L Q ≤ storedOracleStageBudget C e d' n' k' m' L' Q' := by
  have ho : storedOracleCallBudget C e d n k m L Q ≤ storedOracleCallBudget C e d' n' k' m' L' Q' :=
    Nat.mul_le_mul_left C (Nat.pow_le_pow_left (Nat.add_le_add_right (storedOracleInputBudget_mono hd hn hk hm hL hQ) 1) e)
  unfold storedOracleStageBudget
  apply Nat.add_le_add_right
  apply Nat.add_le_add (Nat.add_le_add (storedPreparationBudget_mono hd hn hk hm hL hQ) ho)
  apply storedRingMulBudget_mono hd hm (Nat.add_le_add hm hk) le_rfl
  apply Nat.add_le_add _ ho
  unfold storedRingMulBits
  gcongr

theorem storedOracleStageOutputBits_mono (C e : ℕ) {d d' n n' k k' m m' L L' Q Q' : ℕ}
    (hd : d ≤ d') (hn : n ≤ n') (hk : k ≤ k') (hm : m ≤ m') (hL : L ≤ L') (hQ : Q ≤ Q') :
    storedOracleStageOutputBits C e d n k m L Q ≤ storedOracleStageOutputBits C e d' n' k' m' L' Q' := by
  have ho : storedOracleCallBudget C e d n k m L Q ≤ storedOracleCallBudget C e d' n' k' m' L' Q' :=
    Nat.mul_le_mul_left C (Nat.pow_le_pow_left (Nat.add_le_add_right (storedOracleInputBudget_mono hd hn hk hm hL hQ) 1) e)
  unfold storedOracleStageOutputBits storedRingMulBits
  gcongr

theorem storedOracleInputBudget_polynomial : PolynomialCostBound (fun t => storedOracleInputBudget t t t t t t) := by
  let x : Polynomial ℕ := Polynomial.X
  refine ⟨x + x + (x + x) + x + x + (x + x) * (x * x) * x +
    x * ((x + x) * x) * ((x * x + 2 * (x + 2 * x + 1) + 1) + 2), ?_⟩
  intro t
  apply le_of_eq
  simp [storedOracleInputBudget, storedRingMulBits, x]

theorem storedOracleCallBudget_polynomial (C e : ℕ) : PolynomialCostBound (fun t => storedOracleCallBudget C e t t t t t t) :=
  (PolynomialCostBound.const C).mul ((storedOracleInputBudget_polynomial.add (PolynomialCostBound.const 1)).pow e)

def storedOracleStageWork (C e t : ℕ) : ℕ :=
  2 * t + (storedRingMulBits t t t + 2) + storedOracleCallBudget C e t t t t t t + 1

theorem storedRingMulBits_polynomial : PolynomialCostBound (fun t => storedRingMulBits t t t) := by
  let x : Polynomial ℕ := Polynomial.X
  refine ⟨x * x + 2 * (x + 2 * x + 1) + 1, ?_⟩
  intro t
  apply le_of_eq
  simp [storedRingMulBits, x]

theorem storedOracleStageWork_polynomial (C e : ℕ) : PolynomialCostBound (storedOracleStageWork C e) :=
  (((((PolynomialCostBound.const 2).mul PolynomialCostBound.id).add
    (storedRingMulBits_polynomial.add (PolynomialCostBound.const 2))).add
      (storedOracleCallBudget_polynomial C e)).add (PolynomialCostBound.const 1))

theorem storedOracleStageBudget_polynomial (C e : ℕ) : PolynomialCostBound (fun t => storedOracleStageBudget C e t t t t t t) := by
  have hp := polynomialCostBound_comp_mono (f := fun t => storedRingMulBudget t t t t t)
    (g := storedOracleStageWork C e) storedRingMulBudget_polynomial (storedOracleStageWork_polynomial C e)
    (fun _ _ h => storedRingMulBudget_mono h h h h h)
  have hp' : PolynomialCostBound (fun t => storedRingMulBudget t t (t + t) 1
      (t + (storedRingMulBits t t t + 2) + storedOracleCallBudget C e t t t t t t)) :=
    hp.mono (fun t => by apply storedRingMulBudget_mono <;> unfold storedOracleStageWork <;> omega)
  exact (((storedPreparationBudget_polynomial.add (storedOracleCallBudget_polynomial C e)).add hp').add
    (PolynomialCostBound.const 3))

theorem storedRingMulBits_mono {d d' s s' L L' : ℕ} (hd : d ≤ d') (hs : s ≤ s') (hL : L ≤ L') :
    storedRingMulBits d s L ≤ storedRingMulBits d' s' L' := by
  unfold storedRingMulBits
  gcongr

theorem storedOracleStageOutputBits_polynomial (C e : ℕ) : PolynomialCostBound (fun t => storedOracleStageOutputBits C e t t t t t t) := by
  have hp := polynomialCostBound_comp_mono (f := fun t => storedRingMulBits t t t)
    (g := storedOracleStageWork C e) storedRingMulBits_polynomial (storedOracleStageWork_polynomial C e)
    (fun _ _ h => storedRingMulBits_mono h h h)
  apply hp.mono
  intro t
  unfold storedOracleStageOutputBits
  have ht : t ≤ storedOracleStageWork C e t := by unfold storedOracleStageWork; omega
  have h2t : t + t ≤ storedOracleStageWork C e t := by unfold storedOracleStageWork; omega
  have hL : t + (storedRingMulBits t t t + 2) + storedOracleCallBudget C e t t t t t t ≤ storedOracleStageWork C e t := by
    unfold storedOracleStageWork
    omega
  exact storedRingMulBits_mono ht h2t hL

def encodedReductionInputSize {d n m : ℕ} (T : BasisMultiplicationData d) (one : Vector ℤ d)
    (q k : ℕ) (B : GaussianColumnData (n * d) m) (a b s : ℕ) (w : ℚ) (p : ℕ) : ℕ :=
  d + n + k + m + q.size + basisMultiplicationBits T + storedUnitBits one + gaussianColumnsBits B +
    rationalMagnitudeBits w + initialGaussianSamplingSize a b d k m + s + p

def encodedReductionWork (t : ℕ) : ℕ :=
  t + 352 * (t + t + 1) + gaussianHintOutputBudget t t t t t t t

def encodedReductionCostBudget (C e t : ℕ) : ℕ :=
  gaussianHintBudget t t t t t t t +
    storedOracleStageBudget C e (encodedReductionWork t) (encodedReductionWork t)
      (encodedReductionWork t) (encodedReductionWork t) (encodedReductionWork t) (encodedReductionWork t) + 1

def encodedReductionOutputBudget (C e t : ℕ) : ℕ :=
  storedOracleStageOutputBits C e (encodedReductionWork t) (encodedReductionWork t)
    (encodedReductionWork t) (encodedReductionWork t) (encodedReductionWork t) (encodedReductionWork t)

def encodedReductionTotalBudget (C e t : ℕ) : ℕ :=
  encodedReductionCostBudget C e t + t * t * encodedReductionOutputBudget C e t

theorem encodedReductionWork_polynomial : PolynomialCostBound encodedReductionWork :=
  (PolynomialCostBound.id.add ((PolynomialCostBound.const 352).mul
    ((PolynomialCostBound.id.add PolynomialCostBound.id).add (PolynomialCostBound.const 1)))).add
      gaussianHintOutputBudget_polynomial

theorem encodedReductionCostBudget_polynomial (C e : ℕ) : PolynomialCostBound (encodedReductionCostBudget C e) :=
  (gaussianHintBudget_polynomial.add
    (polynomialCostBound_comp_mono (f := fun t => storedOracleStageBudget C e t t t t t t)
      (g := encodedReductionWork) (storedOracleStageBudget_polynomial C e) encodedReductionWork_polynomial
      (fun _ _ h => storedOracleStageBudget_mono C e h h h h h h))).add (PolynomialCostBound.const 1)

theorem encodedReductionOutputBudget_polynomial (C e : ℕ) : PolynomialCostBound (encodedReductionOutputBudget C e) :=
  polynomialCostBound_comp_mono (f := fun t => storedOracleStageOutputBits C e t t t t t t)
    (g := encodedReductionWork) (storedOracleStageOutputBits_polynomial C e) encodedReductionWork_polynomial
    (fun _ _ h => storedOracleStageOutputBits_mono C e h h h h h h)

theorem encodedReductionTotalBudget_polynomial (C e : ℕ) : PolynomialCostBound (encodedReductionTotalBudget C e) :=
  (encodedReductionCostBudget_polynomial C e).add
    ((PolynomialCostBound.id.mul PolynomialCostBound.id).mul (encodedReductionOutputBudget_polynomial C e))

/-- The complete program has original-input bounds; the only external cost hypothesis is the supplied oracle's contract. -/
theorem encodedReductionRun_bounds {d n k m q C e : ℕ} (T : BasisMultiplicationData d) (one : Vector ℤ d)
    (hq : 0 < q) (O : EncodedKSISOracle q d n (m + k) k) (hO : O.PolynomialBound C e)
    (B : GaussianColumnData (n * d) m) (a b s : ℕ) (ha : 0 < a) (hb : 0 < b) (hd : 0 < d) (hk : 0 < k)
    (w : ℚ) (hw : w ≠ 0) (p : ℕ) (tape : EncodedReductionTape T one hq O B a b s w p) :
    let N := encodedReductionInputSize T one q k B a b s w p
    (encodedReductionRun T one hq O B a b s w p tape).steps ≤ encodedReductionCostBudget C e N ∧
    ∀ j i, (gaussianColumnsOfData (encodedReductionRun T one hq O B a b s w p tape).value j i).natAbs.size ≤
      encodedReductionOutputBudget C e N := by
  let N := encodedReductionInputSize T one q k B a b s w p
  let W := encodedReductionWork N
  have hNW : N ≤ W := by dsimp [W, encodedReductionWork]; omega
  have hdN : d ≤ N := by dsimp [N, encodedReductionInputSize]; omega
  have hnN : n ≤ N := by dsimp [N, encodedReductionInputSize]; omega
  have hkN : k ≤ N := by dsimp [N, encodedReductionInputSize]; omega
  have hmN : m ≤ N := by dsimp [N, encodedReductionInputSize]; omega
  have hqN : q.size ≤ N := by dsimp [N, encodedReductionInputSize]; omega
  have hIN : initialGaussianSamplingSize a b d k m ≤ N := by dsimp [N, encodedReductionInputSize]; omega
  have hsN : s ≤ N := by dsimp [N, encodedReductionInputSize]; omega
  have hpN : p ≤ N := by dsimp [N, encodedReductionInputSize]; omega
  have hwN : rationalMagnitudeBits w ≤ N := by dsimp [N, encodedReductionInputSize]; omega
  have ht : ∀ t i l, (basisMultiplicationEntry T t i l).natAbs.size ≤ N := fun t i l =>
    (basisMultiplicationEntry_bits T t i l).trans (by dsimp [N, encodedReductionInputSize]; omega)
  have ho : ∀ l, (one.get l).natAbs.size ≤ N := fun l =>
    (storedUnit_entry_bits one l).trans (by dsimp [N, encodedReductionInputSize]; omega)
  have hB : ∀ j i, (gaussianColumnsOfData B j i).natAbs.size ≤ N := fun j i =>
    (gaussianColumns_entry_bits B j i).trans (by dsimp [N, encodedReductionInputSize]; omega)
  let blocks := gaussianHintRun T a b k m s w p tape.1
  have hg : blocks.steps ≤ gaussianHintBudget N N N N N N N :=
    (gaussianHintRun_steps T ht ha hb hd k m s hk w hw hwN p tape.1).trans
      (gaussianHintBudget_mono hdN hkN hmN le_rfl hIN hsN hpN)
  have hx : ∀ j i, (gaussianColumnsOfData blocks.value.1 j i).natAbs.size ≤ W := by
    intro j i
    apply (initialGaussianRun_output_size a b d k m s tape.1.1 j i).trans
    have hsize : 352 * (initialGaussianSamplingSize a b d k m + s + 1) ≤ 352 * (N + N + 1) := by gcongr
    dsimp [W, encodedReductionWork]
    omega
  have hr : ∀ j i, (gaussianColumnsOfData blocks.value.2 j i).natAbs.size ≤ W := by
    intro j i
    have h := (gaussianHintRun_output_bits T ht hd a b k m s hk w hw hwN p tape.1 j i).trans
      (gaussianHintOutputBudget_mono hdN hkN hmN le_rfl hIN hsN hpN)
    dsimp [W, encodedReductionWork]
    exact h.trans (by omega)
  have hstage := storedOracleStageRun_bounds T one hq O hO B blocks.value.1 blocks.value.2
    (fun t i l => (ht t i l).trans hNW) (fun l => (ho l).trans hNW)
    (fun j i => (hB j i).trans hNW) hx hr tape.2
  have hcost := hstage.1.trans (storedOracleStageBudget_mono C e (hdN.trans hNW) (hnN.trans hNW)
    (hkN.trans hNW) (hmN.trans hNW) le_rfl (hqN.trans hNW))
  constructor
  · exact Nat.add_le_add_right (Nat.add_le_add hg hcost) 1
  · intro j i
    exact (hstage.2 j i).trans (storedOracleStageOutputBits_mono C e (hdN.trans hNW) (hnN.trans hNW)
      (hkN.trans hNW) (hmN.trans hNW) le_rfl (hqN.trans hNW))

theorem encodedReductionRun_totalBound {d n k m q C e : ℕ} (T : BasisMultiplicationData d) (one : Vector ℤ d)
    (hq : 0 < q) (O : EncodedKSISOracle q d n (m + k) k) (hO : O.PolynomialBound C e)
    (B : GaussianColumnData (n * d) m) (a b s : ℕ) (ha : 0 < a) (hb : 0 < b) (hd : 0 < d) (hk : 0 < k)
    (w : ℚ) (hw : w ≠ 0) (p : ℕ) (tape : EncodedReductionTape T one hq O B a b s w p) :
    (encodedReductionRun T one hq O B a b s w p tape).steps +
      gaussianColumnsBits (encodedReductionRun T one hq O B a b s w p tape).value ≤
      encodedReductionTotalBudget C e (encodedReductionInputSize T one q k B a b s w p) := by
  have h := encodedReductionRun_bounds T one hq O hO B a b s ha hb hd hk w hw p tape
  have hout := gaussianColumnsBits_le _ h.2
  have hdN : d ≤ encodedReductionInputSize T one q k B a b s w p := by unfold encodedReductionInputSize; omega
  have hmN : m ≤ encodedReductionInputSize T one q k B a b s w p := by unfold encodedReductionInputSize; omega
  have hdim := Nat.mul_le_mul hmN hdN
  simp only [one_mul] at hout
  exact Nat.add_le_add h.1 (hout.trans (Nat.mul_le_mul_right _ hdim))

/-- Uniform polynomial declared time and output size for every oracle satisfying its supplied polynomial contract. -/
theorem encodedReductionRun_polynomial (C e : ℕ) : ∃ C' e' : ℕ, ∀ (d n k m q : ℕ)
    (T : BasisMultiplicationData d) (one : Vector ℤ d) (hq : 0 < q)
    (O : EncodedKSISOracle q d n (m + k) k), O.PolynomialBound C e →
    ∀ (B : GaussianColumnData (n * d) m) (a b s : ℕ), 0 < a → 0 < b → 0 < d → 0 < k →
    ∀ (w : ℚ), w ≠ 0 → ∀ (p : ℕ) (tape : EncodedReductionTape T one hq O B a b s w p),
    (encodedReductionRun T one hq O B a b s w p tape).steps +
      gaussianColumnsBits (encodedReductionRun T one hq O B a b s w p tape).value ≤
      C' * (encodedReductionInputSize T one q k B a b s w p + 1) ^ e' := by
  obtain ⟨C', e', h⟩ := (encodedReductionTotalBudget_polynomial C e).exists_mul_pow_bound
  exact ⟨C', e', fun d n k m q T one hq O hO B a b s ha hb hd hk w hw p tape =>
    (encodedReductionRun_totalBound T one hq O hO B a b s ha hb hd hk w hw p tape).trans (h _)⟩

noncomputable section
variable (K : Type*) [Field K] [NumberField K] {d n k m q : ℕ}

local instance encodedDataMeasurable (R M : ℕ) : MeasurableSpace (GaussianColumnData R M) := ⊤
local instance canonicalDataMeasurable (q R M : ℕ) : MeasurableSpace (CanonicalResidueData q R M) := ⊤
local instance encodedPublicMeasurable (q n m : ℕ) : MeasurableSpace (Matrix (Fin n) (Fin m) (ResidueRing K q)) := ⊤
local instance encodedAnswerMeasurable (m : ℕ) : MeasurableSpace (Fin m → 𝓞 K) := ⊤

/-- Actual SIS success of the finite program on a uniformly encoded source challenge. -/
def encodedReductionSuccess [NeZero q] (b : Basis (Fin d) ℤ (𝓞 K)) (T : BasisMultiplicationData d)
    (one : Vector ℤ d) (hq : 0 < q) (O : EncodedKSISOracle q d n (m + k) k)
    (a c s : ℕ) (w : ℚ) (p : ℕ) (β : ℝ) : ℝ :=
  successProbability (PMF.uniformOfFintype (CanonicalResidueData q (n * d) m))
    (fun B => encodedReductionRunLaw T one hq O B.val a c s w p)
    (fun B V => IsSISSolution (residueMap K q) (canonicalRingNorm K) β
      (decodedResidueMatrix b q B) (decodedSISAnswer K b V))

theorem encodedReductionSuccess_eq [NeZero q] (b : Basis (Fin d) ℤ (𝓞 K)) (T : BasisMultiplicationData d)
    (hT : T.Represents b) (one : Vector ℤ d) (hOne : ∀ l, one.get l = b.equivFun 1 l)
    (hq : 0 < q) (O : EncodedKSISOracle q d n (m + k) k) (a c s : ℕ) (w : ℚ) (p : ℕ) (β : ℝ) :
    encodedReductionSuccess K b T one hq O a c s w p β =
      successProbability (PMF.uniformOfFintype (Matrix (Fin n) (Fin m) (ResidueRing K q)))
        (reductionAdversary K q
          (jointPMF (finiteInitialMatrixLaw K b a c k m s)
            (fun X => independentMatrixColumns (basisDataHintSampler K b T w p X))) (decodedKSISOracle K b O))
        (IsSISSolution (residueMap K q) (canonicalRingNorm K) β) := by
  unfold encodedReductionSuccess successProbability
  rw [← encodedReduction_joint_game K T b hT one hOne hq O a c s w p, pmfMap_measureReal]
  rfl

end

/-- The unchanged per-column finite-sampling width floor. -/
noncomputable def samplingWidthFloor (d m : ℕ) (ε C : ℝ) : ℝ :=
  4 * (C * Real.sqrt (Real.log ((m * d : ℕ) / ε))) * Real.sqrt (d : ℝ)

theorem reductionSamplingDimension {d k m : ℕ} (hd : 0 < d) (hk : 0 < k) (hkm : 64 * k ≤ m) :
    2 ≤ m * d := by
  have hm : 2 ≤ m := by omega
  have hmd : m ≤ m * d := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left m (Nat.succ_le_of_lt hd)
  exact hm.trans hmd

theorem widths_of_max {B S A w : ℝ} (hA : 0 ≤ A) (h : max B S * A ≤ w) : B * A ≤ w ∧ S * A ≤ w :=
  ⟨(mul_le_mul_of_nonneg_right (le_max_left B S) hA).trans h,
    (mul_le_mul_of_nonneg_right (le_max_right B S) hA).trans h⟩

noncomputable section
variable (K : Type*) [Field K] [NumberField K] {d k m : ℕ}

/-- The paper's arbitrary smoothing bound may be enlarged to the unchanged sampling floor. -/
theorem basisDataHintSampler_accuracy_of_max (basis : Basis (Fin d) ℤ (𝓞 K))
    (hGram : ∀ i j, canonicalGram K basis i j = if i = j then (d : ℝ) else 0)
    (hN : 2 ≤ m * d) (hk : 0 < k) (T : BasisMultiplicationData d) (hT : T.Represents basis)
    (w : ℚ) (hw : 0 < w) (p : ℕ) {s₁ ε C B : ℝ}
    (hs₁ : 0 ≤ s₁) (hε : 0 < ε) (hεone : ε ≤ 1) (hprec : (1 / 2 : ℝ) ^ p ≤ ε) (hC : 1 ≤ C)
    (hwidth : max B (samplingWidthFloor d m ε C) * (4 * s₁ * Real.sqrt m) ≤ (w : ℝ)) :
    SpectralSamplerAccuracy (m := m) K basis hk s₁ (by exact_mod_cast hw : (0 : ℝ) < w)
      (basisDataHintSampler K basis T w p) ε := by
  have hsamp := (widths_of_max (by positivity : 0 ≤ 4 * s₁ * Real.sqrt m) hwidth).2
  exact basisDataHintSampler_accuracy (k := k) (m := m) K basis hGram hN hk T hT w hw p
    hs₁ hε hεone hprec hC (B := samplingWidthFloor d m ε C) le_rfl hsamp

end

noncomputable section
open Module NumberField GeometricGaussianLHL
variable (K : Type*) [Field K] [NumberField K] {m k n : ℕ}
variable {a : ℕ} [IsCyclotomicExtension {2 ^ (a + 1)} ℚ K] {ζ : K}
local instance finalIntegerMatrixMeasurable (r s : ℕ) : MeasurableSpace (Matrix (Fin r) (Fin s) (𝓞 K)) := ⊤
local instance finalPublicMeasurable (q r s : ℕ) : MeasurableSpace (Matrix (Fin r) (Fin s) (ResidueRing K q)) := ⊤
local instance finalAnswerMeasurable (ι : Type*) : MeasurableSpace (ι → 𝓞 K) := ⊤

/-- The polynomial geometric regime, instantiated by the actual finite reduction and oracle.
No hint-generator, sampler-accuracy, or intermediate-size premise remains. -/
theorem powerTwo_polynomial_encoded_SIS_reduction
    (hζ : IsPrimitiveRoot ζ (2 ^ (a + 1)))
    (T : BasisMultiplicationData (2 ^ (a + 1)).totient) (hT : T.Represents (cyclotomicIntegralBasis K hζ))
    (one : Vector ℤ (2 ^ (a + 1)).totient) (hOne : ∀ l, one.get l = (cyclotomicIntegralBasis K hζ).equivFun 1 l)
    (q : ℕ) [NeZero q] (hq : q.Prime) {g : ℕ}
    (I : Fin g → Ideal (𝓞 K)) [∀ j, (I j).IsMaximal]
    (hI : Function.Injective I) (hfac : Ideal.span ({(q : 𝓞 K)} : Set (𝓞 K)) = ∏ j, I j)
    (hk : 0 < k) (hkm : 64 * k ≤ m) (hnm : n ≤ m)
    {ell u s₁ δsp δop εs β₀ β₁ C : ℝ} (hell : 1 ≤ ell) (h₁ : 0 < s₁)
    (widthNum widthDen initialPrecision : ℕ) (hNum : 0 < widthNum) (hDen : 0 < widthDen)
    (hencoding : s₁ = (widthNum : ℝ) / widthDen)
    (w : ℚ) (hwpos : 0 < w) (p : ℕ) (hs : s₁ ≤ (w : ℝ))
    (hw : ArithmeticWindow (2 ^ (a + 1)).totient m n k q g u s₁ (w : ℝ))
    (hbudget : ((k * (2 ^ (a + 1)).totient : ℕ) : ℝ) * Real.log (numberFieldPolynomialScale K (cyclotomicIntegralBasis K hζ) k m s₁ ell) +
      2 * Real.log (1 / realSecurityError (ell + 4)) ≤ (m : ℝ) * Real.log (8 / 7))
    (hδsp : 0 < δsp) (hδspone : δsp < 1)
    (hcols : lowerSpectralColumnConstant * ((k : ℝ) + Real.log (2 * (2 ^ (a + 1)).totient / δsp)) ≤ m)
    (hδop : 0 < δop) (hδopone : δop < 1) (hlogop : Real.log (2 * (2 ^ (a + 1)).totient / δop) ≤ m)
    (hεs : 0 < εs) (hεsone : εs ≤ 1) (hprec : (1 / 2 : ℝ) ^ p ≤ εs) (hC : 1 ≤ C)
    (hwidth : max (numberFieldPolynomialSmoothingBound K (cyclotomicIntegralBasis K hζ) k m ell) (samplingWidthFloor (2 ^ (a + 1)).totient m εs C) *
      (4 * s₁ * Real.sqrt m) ≤ (w : ℝ))
    (hβ : normLoss m (w : ℝ) * β₁ ≤ β₀)
    (O : EncodedKSISOracle q (2 ^ (a + 1)).totient n (m + k) k) :
    modularGameSuccess K (cyclotomicIntegralBasis K hζ) q
        (paperHintShape K (cyclotomicIntegralBasis K hζ) m k h₁.ne' (by exact_mod_cast hwpos.ne' : (w : ℝ) ≠ 0)) (fun _ => 0)
        (decodedKSISOracle K (cyclotomicIntegralBasis K hζ) O) (simulatedKSISWins K q β₁) ^ 2 / Real.exp (2 * Real.pi) -
      (hintDistributionError k (3 * realSecurityError (ell + 4)) δsp (2 * realSecurityError (ell + 4)) εs +
        modularReverseError (2 ^ (a + 1)).totient m k g +
        hintNormFailure k (3 * realSecurityError (ell + 4)) δsp δop εs + (1 / 2 : ℝ) ^ initialPrecision) ≤
      encodedReductionSuccess K (cyclotomicIntegralBasis K hζ) T one hq.pos O widthNum widthDen initialPrecision w p β₀ := by
  have hd := integralBasis_dimension_pos K (cyclotomicIntegralBasis K hζ)
  have hN := reductionSamplingDimension hd hk hkm
  have hδ := realSecurityError_pos (ell + 4)
  have hscale : 0 ≤ 4 * s₁ * Real.sqrt m := by positivity
  have hgeo := (widths_of_max hscale hwidth).1
  have hacc := basisDataHintSampler_accuracy_of_max (k := k) (m := m) K (cyclotomicIntegralBasis K hζ) (powerTwoGram_diagonal K hζ)
    hN hk T hT w hwpos p h₁.le hεs hεsone hprec hC hwidth
  have hwidthX := arithmeticWindow_geometric_input_width hd (by omega : k ≤ m) hq.one_le hw
  rw [← (powerTwoBasis_constants K hζ).1] at hwidthX
  have hgen := powerTwo_polynomial_hint_generator_bounds K hζ hk (by omega : k < m)
    hell h₁ hs hwidthX hbudget hδsp hδspone hcols hδop hδopone hlogop hεs.le hgeo
    (basisDataHintSampler K (cyclotomicIntegralBasis K hζ) T w p) hacc
  rw [encodedReductionSuccess_eq K (cyclotomicIntegralBasis K hζ) T hT one hOne]
  exact paper_SIS_reduction_advantage_finite_initial K (2 ^ (a + 1)) (cyclotomicIntegralBasis K hζ)
    (powerTwoGram_diagonal K hζ) q hq I hI hfac hk hkm hnm h₁ (by exact_mod_cast hwpos) hs hw hβ
    (by unfold hintNormFailure; positivity) widthNum widthDen initialPrecision hNum hDen hencoding
    (basisDataHintSampler K (cyclotomicIntegralBasis K hζ) T w p) hgen (decodedKSISOracle K (cyclotomicIntegralBasis K hζ) O)

/-- The constant geometric regime, instantiated by the actual finite reduction and oracle.
No hint-generator, sampler-accuracy, or intermediate-size premise remains. -/
theorem powerTwo_constant_encoded_SIS_reduction
    (hζ : IsPrimitiveRoot ζ (2 ^ (a + 1)))
    (T : BasisMultiplicationData (2 ^ (a + 1)).totient) (hT : T.Represents (cyclotomicIntegralBasis K hζ))
    (one : Vector ℤ (2 ^ (a + 1)).totient) (hOne : ∀ l, one.get l = (cyclotomicIntegralBasis K hζ).equivFun 1 l)
    (q : ℕ) [NeZero q] (hq : q.Prime) {g : ℕ}
    (I : Fin g → Ideal (𝓞 K)) [∀ j, (I j).IsMaximal]
    (hI : Function.Injective I) (hfac : Ideal.span ({(q : 𝓞 K)} : Set (𝓞 K)) = ∏ j, I j)
    (hk : 0 < k) (hkm : 64 * k ≤ m) (hnm : n ≤ m)
    {ell u s₁ δsp δop εs β₀ β₁ C : ℝ} (hell : 1 ≤ ell) (h₁ : 0 < s₁)
    (widthNum widthDen initialPrecision : ℕ) (hNum : 0 < widthNum) (hDen : 0 < widthDen)
    (hencoding : s₁ = (widthNum : ℝ) / widthDen)
    (w : ℚ) (hwpos : 0 < w) (p : ℕ) (hs : s₁ ≤ (w : ℝ))
    (hw : ArithmeticWindow (2 ^ (a + 1)).totient m n k q g u s₁ (w : ℝ))
    (hbudget : ((k * (2 ^ (a + 1)).totient : ℕ) : ℝ) * Real.log (powerTwoConstantScale (2 ^ (a + 1)).totient k m s₁ ell) +
      2 * Real.log (1 / realSecurityError (ell + 6)) ≤ (m : ℝ) * Real.log (50 / 49))
    (hδsp : 0 < δsp) (hδspone : δsp < 1)
    (hcols : lowerSpectralColumnConstant * ((k : ℝ) + Real.log (2 * (2 ^ (a + 1)).totient / δsp)) ≤ m)
    (hδop : 0 < δop) (hδopone : δop < 1) (hlogop : Real.log (2 * (2 ^ (a + 1)).totient / δop) ≤ m)
    (hεs : 0 < εs) (hεsone : εs ≤ 1) (hprec : (1 / 2 : ℝ) ^ p ≤ εs) (hC : 1 ≤ C)
    (hwidth : max (powerTwoConstantSmoothingBound (2 ^ (a + 1)).totient k m ell) (samplingWidthFloor (2 ^ (a + 1)).totient m εs C) *
      (4 * s₁ * Real.sqrt m) ≤ (w : ℝ))
    (hβ : normLoss m (w : ℝ) * β₁ ≤ β₀)
    (O : EncodedKSISOracle q (2 ^ (a + 1)).totient n (m + k) k) :
    modularGameSuccess K (cyclotomicIntegralBasis K hζ) q
        (paperHintShape K (cyclotomicIntegralBasis K hζ) m k h₁.ne' (by exact_mod_cast hwpos.ne' : (w : ℝ) ≠ 0)) (fun _ => 0)
        (decodedKSISOracle K (cyclotomicIntegralBasis K hζ) O) (simulatedKSISWins K q β₁) ^ 2 / Real.exp (2 * Real.pi) -
      (hintDistributionError k (3 * realSecurityError (ell + 6)) δsp (2 * realSecurityError (ell + 6)) εs +
        modularReverseError (2 ^ (a + 1)).totient m k g +
        hintNormFailure k (3 * realSecurityError (ell + 6)) δsp δop εs + (1 / 2 : ℝ) ^ initialPrecision) ≤
      encodedReductionSuccess K (cyclotomicIntegralBasis K hζ) T one hq.pos O widthNum widthDen initialPrecision w p β₀ := by
  have hd := integralBasis_dimension_pos K (cyclotomicIntegralBasis K hζ)
  have hN := reductionSamplingDimension hd hk hkm
  have hδ := realSecurityError_pos (ell + 6)
  have hscale : 0 ≤ 4 * s₁ * Real.sqrt m := by positivity
  have hgeo := (widths_of_max hscale hwidth).1
  have hacc := basisDataHintSampler_accuracy_of_max (k := k) (m := m) K (cyclotomicIntegralBasis K hζ) (powerTwoGram_diagonal K hζ)
    hN hk T hT w hwpos p h₁.le hεs hεsone hprec hC hwidth
  have hwidthX := arithmeticWindow_constant_input_width hd hk (by omega : k ≤ m) hq.one_le hw
  have hgen := powerTwo_constant_hint_generator_bounds K hζ hk (by omega : k < m)
    hell h₁ hs hwidthX hbudget hδsp hδspone hcols hδop hδopone hlogop hεs.le hgeo
    (basisDataHintSampler K (cyclotomicIntegralBasis K hζ) T w p) hacc
  rw [encodedReductionSuccess_eq K (cyclotomicIntegralBasis K hζ) T hT one hOne]
  exact paper_SIS_reduction_advantage_finite_initial K (2 ^ (a + 1)) (cyclotomicIntegralBasis K hζ)
    (powerTwoGram_diagonal K hζ) q hq I hI hfac hk hkm hnm h₁ (by exact_mod_cast hwpos) hs hw hβ
    (by unfold hintNormFailure; positivity) widthNum widthDen initialPrecision hNum hDen hencoding
    (basisDataHintSampler K (cyclotomicIntegralBasis K hζ) T w p) hgen (decodedKSISOracle K (cyclotomicIntegralBasis K hζ) O)

end

end SISToKSIS
