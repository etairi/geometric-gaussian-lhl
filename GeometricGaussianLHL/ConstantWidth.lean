import GeometricGaussianLHL.PolynomialWidth

/-!
# Constant-width smoothing theorems

This module collects the following proof sections, in dependency order.
- Unit-coordinate translation of a product Gaussian (`ProductGaussianUnitShift`).
- Constant-width contraction from small coordinates (`GaussianSmallCoordinates`).
- The small-coordinate case with the paper's exact parameters (`ConstantWidthSmallCase`).
- A scalar contraction controls the whole ring block (`ConstantWidthBlock`).
- Gaussian translations and one-coordinate displacements (`GaussianCoordinateShift`).
- Column-norm failure at constant width (`ConstantWidthColumnNorm`).
- Uniform contraction at constant width (`ConstantWidthContraction`).
- Rank failure at constant coefficient width (`GaussianConstantRank`).
- Remainder decay at constant width (`ConstantWidthRemainder`).
- The finite constant-width coefficient certificate (`ConstantWidthMatrix`).
- Constant-width smoothing over power-of-two number fields (`NumberFieldConstantWidth`).
- Uniform column budgets at coefficient width one (`ConstantWidthFamily`).
- The numerical power-of-two pinned smoothing bounds (`PowerTwoPinned`).
- Constant-width asymptotics uniformly in the field degree (`ConstantWidthAsymptotic`).
-/

section ProductGaussianUnitShift

/-!
## Unit-coordinate translation of a product Gaussian

The scalar unit-shift identity is lifted to one coordinate of the actual
product distribution. The same bound holds for either sign of the shift.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace GeometricGaussianLHL

theorem integerGaussian_nat_step (s : ℝ) (hs : 0 < s) (n : ℕ) :
    (integerGaussian s hs ((n : ℤ) + 1)).toReal ≤ (integerGaussian s hs n).toReal := by
  rw [integerGaussian_toReal, integerGaussian_toReal]
  apply div_le_div_of_nonneg_right _ (integerGaussianPartition_pos hs).le
  apply Real.exp_le_exp.mpr
  simp only [Int.cast_add, Int.cast_natCast, Int.cast_one]
  exact mul_le_mul_of_nonpos_left (by nlinarith [Nat.cast_nonneg (α := ℝ) n])
    (neg_nonpos.mpr (div_pos Real.pi_pos (sq_pos_of_pos hs)).le)

theorem integerGaussian_unit_translation (s : ℝ) (hs : 0 < s) :
    discreteTotalVariation (integerGaussian s hs) ((integerGaussian s hs).map (fun z => z + 1)) =
      (integerGaussian s hs 0).toReal :=
  pmf_unimodal_unit_translation _ (integerGaussian_symmetric s hs) (integerGaussian_nat_step s hs)

theorem pmf_integer_translate_variation_neg (p : PMF ℤ) (v : ℤ) :
    discreteTotalVariation p (p.map (fun z => z + -v)) =
      discreteTotalVariation p (p.map (fun z => z + v)) := by
  have happly (w z : ℤ) : (p.map (fun x => x + w)) z = p (z - w) := by
    simpa only [sub_add_cancel] using pmf_map_integer_add_apply p w (z - w)
  unfold discreteTotalVariation
  congr 1
  rw [← (Equiv.addRight v).tsum_eq (fun z => |(p z).toReal - (p.map (fun z => z + v) z).toReal|)]
  simp only [Equiv.coe_addRight, happly, add_sub_cancel_right, sub_neg_eq_add, abs_sub_comm]

theorem integerGaussian_signed_unit_translation {s : ℝ} (hs : 1 ≤ s) (v : ℤ) (hv : |v| = 1) :
    discreteTotalVariation (integerGaussian s (by linarith))
      ((integerGaussian s (by linarith)).map (fun z => z + v)) < (921 / 1000 : ℝ) := by
  have hv' : v = 1 ∨ v = -1 := by
    rcases le_total 0 v with h | h
    · rw [abs_of_nonneg h] at hv
      exact Or.inl hv
    · rw [abs_of_nonpos h] at hv
      exact Or.inr (by omega)
  rcases hv' with rfl | rfl
  · rw [integerGaussian_unit_translation]
    exact integerGaussian_zero_mass_lt hs
  · rw [pmf_integer_translate_variation_neg, integerGaussian_unit_translation]
    exact integerGaussian_zero_mass_lt hs

/-- Translating one coordinate costs at most its scalar total variation.
-/
theorem independentProduct_single_translation_le {n : ℕ} (p : PMF ℤ) (i : Fin n) (v : ℤ) :
    discreteTotalVariation (independentProduct (fun _ : Fin n => p))
      ((independentProduct (fun _ : Fin n => p)).map (fun z => z + Pi.single i v)) ≤
        discreteTotalVariation p (p.map (fun z => z + v)) := by
  classical
  have hmap : (fun z : Fin n → ℤ => z + Pi.single i v) =
      (fun (z : Fin n → ℤ) (j : Fin n) => z j + (Pi.single i v : Fin n → ℤ) j) := rfl
  rw [hmap]
  rw [independentProduct_map (fun _ : Fin n => p)
    (fun (j : Fin n) (z : ℤ) => z + (Pi.single i v : Fin n → ℤ) j)]
  apply (discreteTotalVariation_independentProduct_le _ _).trans
  rw [Finset.sum_eq_single i]
  · simp only [Pi.single_eq_same]
    exact le_rfl
  · intro j _ hji
    simp only [Pi.single_eq_of_ne hji, add_zero]
    change discreteTotalVariation p (p.map id) = 0
    rw [PMF.map_id]
    simp [discreteTotalVariation]
  · simp

theorem productIntegerGaussian_signed_unit_translation {n : ℕ} {s : ℝ} (hs : 1 ≤ s)
    (i : Fin n) (v : ℤ) (hv : |v| = 1) :
    discreteTotalVariation (productIntegerGaussian n s (by linarith))
      ((productIntegerGaussian n s (by linarith)).map (fun z => z + Pi.single i v)) <
        (921 / 1000 : ℝ) :=
  (independentProduct_single_translation_le _ i v).trans_lt
    (integerGaussian_signed_unit_translation hs v hv)

end GeometricGaussianLHL
end

end ProductGaussianUnitShift

section GaussianSmallCoordinates

/-!
## Constant-width contraction from small coordinates

A fourth-moment escape bound and a Chernoff tail replace the normal
approximation in this case. All probabilities and expectations refer to
the actual product Gaussian; the periodic images are controlled through
distance to the integers.
-/

noncomputable section

open MeasureTheory

namespace GeometricGaussianLHL

theorem integerDistance_eq_abs_of_abs_le_half {u : ℝ} (hu : |u| ≤ 1 / 2) :
    integerDistance u = |u| := by
  apply le_antisymm
  · simpa only [integerDistance, Real.dist_eq, sub_zero] using
      (Metric.infDist_le_dist_of_mem (x := u) (show (0 : ℝ) ∈ Set.range (Int.cast : ℤ → ℝ) from ⟨0, by simp⟩))
  · by_contra! h
    obtain ⟨k, hk⟩ := (integerDistance_lt_iff u |u|).mp h
    by_cases hk0 : k = 0
    · simp only [hk0, Int.cast_zero, sub_zero, lt_self_iff_false] at hk
    · have hki : (1 : ℤ) ≤ |k| := Int.one_le_abs hk0
      have hkr : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast hki
      have htri : |(k : ℝ)| ≤ |u - (k : ℝ)| + |u| := by
        simpa only [sub_zero, abs_sub_comm (k : ℝ) u] using abs_sub_le (k : ℝ) u 0
      linarith

theorem periodicGaussian_origin_le_1001 {t : ℝ} (ht : 8 ≤ t) :
    periodicGaussian t 0 ≤ (1001 / 1000 : ℝ) := by
  have hx : 192 ≤ Real.pi * t ^ 2 := by
    have hts : 64 ≤ t ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right Real.pi_gt_three.le (sq_nonneg t)]
  have he := Real.pow_div_factorial_le_exp (Real.pi * t ^ 2) (by positivity) 2
  norm_num only [Nat.factorial, Nat.cast_ofNat] at he
  have he' : 3000 ≤ Real.exp (Real.pi * t ^ 2) := by nlinarith
  have hneg : Real.exp (-Real.pi * t ^ 2) ≤ 1 / 3000 := by
    rw [neg_mul, Real.exp_neg]
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num) he'
  have h := periodicGaussian_origin_bound (by linarith : 1 ≤ t)
  linarith

theorem productGaussian_integer_escape_of_small_coordinates {n : ℕ} (y : Fin n → ℝ)
    {s t : ℝ} (hs : 1 ≤ s) (ht : 0 < t)
    (hQ : 0 < ∑ i, y i ^ 2)
    (hcoord : ∀ i, y i ^ 2 ≤ (∑ j, y j ^ 2) / 400)
    (htail : s ^ 2 * (∑ i, y i ^ 2) ≤ 1 / 6400)
    (hscale : 2 / t ^ 2 < integerGaussianSecondMoment s (by linarith) * ∑ i, y i ^ 2) :
    (49 / 1000 : ℝ) ≤ (productIntegerGaussian n s (by linarith)).toMeasure.real
      {z | 1 / t ≤ integerDistance (integerLinearForm y z)} := by
  let p := productIntegerGaussian n s (by linarith)
  let V := integerGaussianSecondMoment s (by linarith) * ∑ i, y i ^ 2
  let A : Set (Coeff n) := {z | V / 2 < integerLinearForm y z ^ 2}
  let B : Set (Coeff n) := {z | 1 / t ≤ integerDistance (integerLinearForm y z)}
  let C : Set (Coeff n) := {z | (1 / 4 : ℝ) < |integerLinearForm y z|}
  have hA : (1 / 20 : ℝ) ≤ p.toMeasure.real A := productGaussian_square_escape y hs hQ hcoord
  have hC : p.toMeasure.real C < 1 / 1000 := productGaussian_quarter_tail y s (by linarith) htail
  have hsub : A ⊆ B ∪ C := by
    intro z hz
    by_cases hc : z ∈ C
    · exact Or.inr hc
    · left
      have hsmall : |integerLinearForm y z| ≤ 1 / 4 := le_of_not_gt hc
      change 1 / t ≤ integerDistance (integerLinearForm y z)
      rw [integerDistance_eq_abs_of_abs_le_half (by linarith)]
      have ha : V / 2 < integerLinearForm y z ^ 2 := hz
      have hsc : (1 / t) ^ 2 < V / 2 := by
        change 2 / t ^ 2 < V at hscale
        calc
          (1 / t) ^ 2 = (2 / t ^ 2) / 2 := by ring
          _ < V / 2 := div_lt_div_of_pos_right hscale (by norm_num)
      exact (sq_le_sq₀ (by positivity) (abs_nonneg _)).mp
        (by rw [sq_abs]; exact (hsc.trans ha).le)
  have hm := (measureReal_mono (μ := p.toMeasure) hsub).trans (measureReal_union_le B C)
  change (49 / 1000 : ℝ) ≤ p.toMeasure.real B
  linarith

/-- A reusable scalar contraction criterion. A probability saving of
`39/1000` away from the integers suffices for the original `39/40`.
-/
theorem periodicGaussian_expectation_of_escape {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (p : PMF α) (f : α → ℝ) {t : ℝ} (ht : 8 ≤ t)
    (hescape : (39 / 1000 : ℝ) ≤ p.toMeasure.real {x | 1 / t ≤ integerDistance (f x)}) :
    (∑' x, (p x).toReal * periodicGaussian t (f x)) ≤ 39 / 40 := by
  have htpos : 0 < t := by linarith
  have hφ : 1 ≤ periodicGaussian t 0 := periodicGaussian_zero_ge_one htpos
  have he := pmf_expectation_bound_of_event p (fun x => periodicGaussian t (f x))
    {x | 1 / t ≤ integerDistance (f x)}
    (fun _ => (periodicGaussian_pos htpos _).le) (fun _ => periodicGaussian_le_zero htpos _)
    (a := 1 / 8) (fun x hx => by
      have h := (periodicGaussian_off_integer ht hx).le
      nlinarith)
  have hm := mul_le_mul_of_nonneg_left hescape (show 0 ≤ periodicGaussian t 0 by linarith)
  have hbound := periodicGaussian_origin_le_1001 ht
  nlinarith

/-- The scalar `39/40` contraction in the small-coordinate regime. The
three geometric hypotheses are instantiated from the paper's width and
length parameters in the subsequent specialization. -/
theorem productGaussian_small_coordinate_contraction {n : ℕ} (y : Fin n → ℝ)
    {s t : ℝ} (hs : 1 ≤ s) (ht : 8 ≤ t)
    (hQ : 0 < ∑ i, y i ^ 2)
    (hcoord : ∀ i, y i ^ 2 ≤ (∑ j, y j ^ 2) / 400)
    (htail : s ^ 2 * (∑ i, y i ^ 2) ≤ 1 / 6400)
    (hscale : 2 / t ^ 2 < integerGaussianSecondMoment s (by linarith) * ∑ i, y i ^ 2) :
    (∑' z : Coeff n, (productIntegerGaussian n s (by linarith) z).toReal *
      periodicGaussian t (integerLinearForm y z)) ≤ 39 / 40 := by
  apply periodicGaussian_expectation_of_escape _ _ ht
  have hp := productGaussian_integer_escape_of_small_coordinates y hs (by linarith) hQ hcoord htail hscale
  exact (by norm_num : (39 / 1000 : ℝ) ≤ 49 / 1000).trans hp

end GeometricGaussianLHL
end

end GaussianSmallCoordinates

section ConstantWidthSmallCase

/-!
## The small-coordinate case with the paper's exact parameters

For `H ≥ n ≥ 1`, width at least one, and `t = 640 sqrt H`, the paper's
length threshold and coordinate cutoff imply all three quantitative
hypotheses of the fourth-moment contraction proof.
-/

noncomputable section

namespace GeometricGaussianLHL

theorem integerLinearForm_eq_inner {n : ℕ} (y : Euclidean n) (z : Coeff n) :
    integerLinearForm (fun i => y i) z = inner ℝ y (integerEmbedding n z) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [integerLinearForm, dotProduct, Pi.star_apply, star_trivial, integerEmbedding_apply]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

/-- The deterministic estimates needed for the small-coordinate case.
-/
theorem constantWidth_small_coordinate_parameters {n : ℕ} (hn : 1 ≤ n)
    {s H : ℝ} (hs : 1 ≤ s) (hH : (n : ℝ) ≤ H) (y : Euclidean n)
    (hlen : 1 / (4 * s * Real.sqrt H) ≤ ‖y‖)
    (hcoord : ∀ i, |y i| ≤ 8 / (s * (640 * Real.sqrt H))) :
    8 ≤ 640 * Real.sqrt H ∧
    0 < ∑ i, y i ^ 2 ∧
    (∀ i, y i ^ 2 ≤ (∑ j, y j ^ 2) / 400) ∧
    s ^ 2 * (∑ i, y i ^ 2) ≤ 1 / 6400 ∧
    2 / (640 * Real.sqrt H) ^ 2 <
      integerGaussianSecondMoment s (by linarith) * ∑ i, y i ^ 2 := by
  have hsp : 0 < s := by linarith
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hH1 : 1 ≤ H := hn'.trans hH
  have hHp : 0 < H := by linarith
  have hroot : 0 < Real.sqrt H := Real.sqrt_pos.mpr hHp
  have hroot1 : 1 ≤ Real.sqrt H := (Real.le_sqrt (by norm_num) hHp.le).mpr (by simpa using hH1)
  let L := 1 / (4 * s * Real.sqrt H)
  let b := 8 / (s * (640 * Real.sqrt H))
  let Q := ∑ i, y i ^ 2
  have hL : 0 < L := by dsimp [L]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hbL : b = L / 20 := by dsimp [b, L]; ring
  have hQ : L ^ 2 ≤ Q := by
    dsimp [Q]
    rw [← EuclideanSpace.real_norm_sq_eq]
    exact (sq_le_sq₀ hL.le (norm_nonneg y)).mpr hlen
  have hcoord₂ : ∀ i, y i ^ 2 ≤ b ^ 2 := by
    intro i
    have h := (sq_le_sq₀ (abs_nonneg (y i)) hb).mpr (hcoord i)
    simpa only [sq_abs] using h
  have hrel : ∀ i, y i ^ 2 ≤ Q / 400 := by
    intro i
    have hh := hcoord₂ i
    rw [hbL] at hh
    nlinarith
  have hQupper : Q ≤ (n : ℝ) * b ^ 2 := by
    have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hcoord₂ i)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using hh
  have htail : s ^ 2 * Q ≤ 1 / 6400 := by
    have he : s ^ 2 * (H * b ^ 2) = 1 / 6400 := by
      dsimp [b]
      simp only [div_pow, mul_pow, Real.sq_sqrt hHp.le]
      field_simp
      ring
    calc
      _ ≤ s ^ 2 * ((n : ℝ) * b ^ 2) := mul_le_mul_of_nonneg_left hQupper (sq_nonneg s)
      _ ≤ s ^ 2 * (H * b ^ 2) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hH (sq_nonneg b)) (sq_nonneg s)
      _ = _ := he
  have hv := integerGaussianSecondMoment_lower hs
  have hv0 := integerGaussianSecondMoment_nonneg s hsp
  have hlower : 1 / (256 * H) ≤ integerGaussianSecondMoment s hsp * Q := by
    have he : (s ^ 2 / 16) * L ^ 2 = 1 / (256 * H) := by
      dsimp [L]
      simp only [div_pow, mul_pow, Real.sq_sqrt hHp.le]
      field_simp
      ring
    rw [← he]
    exact mul_le_mul hv hQ (sq_nonneg L) hv0
  refine ⟨by linarith, (sq_pos_of_pos hL).trans_le hQ, hrel, htail, ?_⟩
  apply lt_of_lt_of_le _ hlower
  apply (div_lt_div_iff₀ (by positivity : 0 < (640 * Real.sqrt H) ^ 2)
    (by positivity : 0 < 256 * H)).mpr
  rw [mul_pow, Real.sq_sqrt hHp.le]
  nlinarith

/-- The small-coordinate half of the constant-width contraction lemma, for the actual Gaussian and
literal Euclidean inner product, with the original constant `39/40` . -/
theorem constantWidth_small_coordinate_contraction {n : ℕ} (hn : 1 ≤ n)
    {s H : ℝ} (hs : 1 ≤ s) (hH : (n : ℝ) ≤ H) (y : Euclidean n)
    (hlen : 1 / (4 * s * Real.sqrt H) ≤ ‖y‖)
    (hcoord : ∀ i, |y i| ≤ 8 / (s * (640 * Real.sqrt H))) :
    (∑' z : Coeff n, (productIntegerGaussian n s (by linarith) z).toReal *
      periodicGaussian (640 * Real.sqrt H) (inner ℝ y (integerEmbedding n z))) ≤ 39 / 40 := by
  obtain ⟨ht, hQ, hrel, htail, hscale⟩ := constantWidth_small_coordinate_parameters hn hs hH y hlen hcoord
  simpa only [integerLinearForm_eq_inner] using
    productGaussian_small_coordinate_contraction (fun i => y i) hs ht hQ hrel htail hscale

end GeometricGaussianLHL
end

end ConstantWidthSmallCase

section ConstantWidthBlock

/-!
## A scalar contraction controls the whole ring block

Only the witness factor needs a scalar expectation bound. All factors
may depend on the same sample; no independence within the block is used.
-/

noncomputable section

namespace GeometricGaussianLHL

theorem periodicGaussian_origin_pow_tight {t : ℝ} (ht : 8 ≤ t) (d : ℕ)
    (hd : (d : ℝ) * 1000 ≤ t ^ 2) :
    periodicGaussian t 0 ^ d ≤ (1001 / 1000 : ℝ) := by
  have htpos : 0 < t := by linarith
  have hbase : periodicGaussian t 0 ≤ Real.exp (3 * Real.exp (-Real.pi * t ^ 2)) := by
    have hb := periodicGaussian_origin_bound (show 1 ≤ t by linarith)
    linarith [Real.add_one_le_exp (3 * Real.exp (-Real.pi * t ^ 2))]
  have hp : periodicGaussian t 0 ^ d ≤ Real.exp (3 * Real.exp (-Real.pi * t ^ 2)) ^ d := by
    gcongr
    exact (periodicGaussian_pos htpos 0).le
  rw [← Real.exp_nat_mul] at hp
  have harg : (d : ℝ) * (3 * Real.exp (-Real.pi * t ^ 2)) ≤ 1 / 10000 := by
    have hsmall := gaussian_origin_exponent_small (show 64 ≤ t ^ 2 by nlinarith)
    have hm := mul_le_mul_of_nonneg_right hd
      (show 0 ≤ 3 * Real.exp (-Real.pi * t ^ 2) by positivity)
    nlinarith
  have hexp := Real.exp_le_exp.mpr harg
  have hnum := Real.exp_bound_div_one_sub_of_interval (by norm_num : (0 : ℝ) ≤ 1 / 10000)
    (by norm_num : (1 / 10000 : ℝ) < 1)
  norm_num at hnum
  linarith

theorem nonnegative_product_le_witness {d : ℕ} (f : Fin d → ℝ) (i : Fin d) {C : ℝ}
    (hf : ∀ j, 0 ≤ f j) (hC : ∀ j, f j ≤ C) :
    (∏ j, f j) ≤ f i * C ^ (d - 1) := by
  classical
  rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ i)]
  have h := Finset.prod_le_prod (s := Finset.univ.erase i) (fun j _ => hf j) (fun j _ => hC j)
  have hc : (∏ _j ∈ Finset.univ.erase i, C) = C ^ (d - 1) := by
    simp only [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i),
      Finset.card_univ, Fintype.card_fin]
  rw [hc] at h
  exact mul_le_mul_of_nonneg_left h (hf i)

/-- The exact `49/50` block constant from a `39/40` scalar contraction.
-/
theorem periodicGaussian_block_contraction {α : Type*} {d : ℕ} (p : PMF α)
    (g : Fin d → α → ℝ) (i : Fin d) {t : ℝ} (ht : 8 ≤ t)
    (hd : (d : ℝ) * 1000 ≤ t ^ 2)
    (hscalar : (∑' x, (p x).toReal * periodicGaussian t (g i x)) ≤ 39 / 40) :
    (∑' x, (p x).toReal * ∏ j, periodicGaussian t (g j x)) ≤ 49 / 50 := by
  have htpos : 0 < t := by linarith
  let C := periodicGaussian t 0
  have hC : 0 ≤ C := (periodicGaussian_pos htpos 0).le
  have hs := pmf_weighted_summable_of_bounded p (fun x => ∏ j, periodicGaussian t (g j x))
    (fun _ => Finset.prod_nonneg (fun _ _ => (periodicGaussian_pos htpos _).le))
    (C := C ^ d) (fun x => by
      simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
        Finset.prod_le_prod (s := (Finset.univ : Finset (Fin d)))
          (f := fun j => periodicGaussian t (g j x)) (g := fun _ => C)
          (fun _ _ => (periodicGaussian_pos htpos _).le)
          (fun _ _ => periodicGaussian_le_zero htpos _))
  have hsone := pmf_weighted_summable_of_bounded p (fun x => periodicGaussian t (g i x))
    (fun _ => (periodicGaussian_pos htpos _).le) (fun _ => periodicGaussian_le_zero htpos _)
  have he := hs.tsum_le_tsum
    (g := fun x => ((p x).toReal * periodicGaussian t (g i x)) * C ^ (d - 1))
    (fun x => by
      have h := mul_le_mul_of_nonneg_left
        (nonnegative_product_le_witness (fun j => periodicGaussian t (g j x)) i
          (fun _ => (periodicGaussian_pos htpos _).le) (fun _ => periodicGaussian_le_zero htpos _))
        (show 0 ≤ (p x).toReal from ENNReal.toReal_nonneg)
      simpa only [mul_assoc] using h)
    (hsone.mul_right (C ^ (d - 1)))
  rw [tsum_mul_right] at he
  have hpow : C ^ (d - 1) ≤ 1001 / 1000 := by
    apply periodicGaussian_origin_pow_tight ht
    have hn : ((d - 1 : ℕ) : ℝ) ≤ d := by exact_mod_cast Nat.sub_le d 1
    exact (mul_le_mul_of_nonneg_right hn (by norm_num)).trans hd
  have hm := mul_le_mul_of_nonneg_right hscalar (pow_nonneg hC (d - 1))
  have hnum := mul_le_mul_of_nonneg_left hpow (by norm_num : (0 : ℝ) ≤ 39 / 40)
  linarith

/-- The block conclusion of the constant-width contraction lemma in the small-coordinate case. The
witness identity is enough; all other factors may be arbitrarily dependent. -/
theorem constantWidth_small_coordinate_block {n d : ℕ} (hn : 1 ≤ n) (hd : d ≤ n)
    {s H : ℝ} (hs : 1 ≤ s) (hH : (n : ℝ) ≤ H) (y : Euclidean n)
    (hlen : 1 / (4 * s * Real.sqrt H) ≤ ‖y‖)
    (hcoord : ∀ i, |y i| ≤ 8 / (s * (640 * Real.sqrt H)))
    (g : Fin d → Coeff n → ℝ) (i : Fin d)
    (hwitness : ∀ z, g i z = inner ℝ y (integerEmbedding n z)) :
    (∑' z : Coeff n, (productIntegerGaussian n s (by linarith) z).toReal *
      ∏ j, periodicGaussian (640 * Real.sqrt H) (g j z)) ≤ 49 / 50 := by
  have hparams := constantWidth_small_coordinate_parameters hn hs hH y hlen hcoord
  apply periodicGaussian_block_contraction _ g i hparams.1
  · have hn0 : (0 : ℝ) ≤ n := by positivity
    have hH0 := hn0.trans hH
    have hd' : (d : ℝ) ≤ n := by exact_mod_cast hd
    rw [mul_pow, Real.sq_sqrt hH0]
    nlinarith
  · simp_rw [hwitness]
    exact constantWidth_small_coordinate_contraction hn hs hH y hlen hcoord

end GeometricGaussianLHL
end

end ConstantWidthBlock

section GaussianCoordinateShift

/-!
## Gaussian translations and one-coordinate displacements

The scalar shape is identified with the actual product Gaussian. A signed
integer in one coordinate then supplies the displacement used in the
large-coordinate case of the constant-width contraction.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace GeometricGaussianLHL

theorem ellipsoidalGaussian_scalar_eq_product (n : ℕ) (s : ℝ) (hs : 0 < s) :
    ellipsoidalGaussian (euclideanScalarShape n s hs.ne') 0 = productIntegerGaussian n s hs := by
  apply ellipsoidalGaussian_eq_product_of_isotropic_weight _ hs
  intro z
  simp only [ellipsoidWeight, sub_zero, euclideanScalarShape_symm_apply, gaussianWeight,
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, inv_pow, one_pow, one_div]
  congr 1
  ring

theorem productIntegerGaussian_translate_variation {n : ℕ} (s : ℝ) (hs : 0 < s) (v : Coeff n) :
    discreteTotalVariation (productIntegerGaussian n s hs)
      ((productIntegerGaussian n s hs).map (fun z => z + v)) ≤
        Real.sqrt (Real.pi / 2) * (‖integerEmbedding n v‖ / s) := by
  rw [← ellipsoidalGaussian_scalar_eq_product n s hs]
  have h := ellipsoidalGaussian_translate_variation (euclideanScalarShape n s hs.ne') v
  simpa only [euclideanScalarShape_symm_apply, norm_smul, Real.norm_eq_abs,
    abs_inv, abs_of_pos hs, div_eq_mul_inv, mul_comm s⁻¹] using h

theorem integerEmbedding_single_norm {n : ℕ} (i : Fin n) (v : ℤ) :
    ‖integerEmbedding n (Pi.single i v)‖ = |(v : ℝ)| := by
  classical
  apply (sq_eq_sq₀ (norm_nonneg _) (abs_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq, sq_abs]
  simp only [integerEmbedding_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [Pi.single_eq_of_ne hji]
  · simp

theorem integerEmbedding_single_inner {n : ℕ} (y : Euclidean n) (i : Fin n) (v : ℤ) :
    inner ℝ y (integerEmbedding n (Pi.single i v)) = y i * (v : ℝ) := by
  classical
  rw [← integerLinearForm_eq_inner]
  unfold integerLinearForm
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [Pi.single_eq_of_ne hji]
  · simp

theorem orientedInteger_abs (y : ℝ) (v : ℤ) : |orientedInteger y v| = |v| := by
  unfold orientedInteger
  split <;> simp

/-- When the coordinate is below `2/t`, a signed ceiling shift has norm
at most half the Gaussian width and the required slab displacement.
-/
theorem exists_large_coordinate_ceiling_shift {n : ℕ} (y : Euclidean n) (i : Fin n)
    {s t : ℝ} (hs : 0 < s) (ht : 8 ≤ t)
    (hlo : 8 / (s * t) ≤ |y i|) (hhi : |y i| < 2 / t) :
    ∃ v : Coeff n, 2 * (1 / t) ≤ inner ℝ y (integerEmbedding n v) ∧
      inner ℝ y (integerEmbedding n v) ≤ 1 - 2 * (1 / t) ∧
      ‖integerEmbedding n v‖ ≤ s / 2 := by
  have htpos : 0 < t := by linarith
  have ha : 0 < |y i| := (by positivity : 0 < 8 / (s * t)).trans_le hlo
  let k : ℤ := ⌈2 / (t * |y i|)⌉
  let v : Coeff n := Pi.single i (orientedInteger (y i) k)
  have hk0 : 0 ≤ k := le_of_lt (Int.ceil_pos.mpr (by positivity))
  have hklo : 2 / (t * |y i|) ≤ (k : ℝ) := Int.le_ceil _
  have hkhi : (k : ℝ) < 2 / (t * |y i|) + 1 := Int.ceil_lt_add_one _
  have hpair : inner ℝ y (integerEmbedding n v) = |y i| * (k : ℝ) := by
    rw [integerEmbedding_single_inner, mul_orientedInteger]
  have hnorm : ‖integerEmbedding n v‖ = (k : ℝ) := by
    rw [integerEmbedding_single_norm]
    have h := orientedInteger_abs (y i) k
    have hh : |((orientedInteger (y i) k : ℤ) : ℝ)| = |(k : ℝ)| := by exact_mod_cast h
    rw [hh, abs_of_nonneg (by exact_mod_cast hk0)]
  have hproduct : 8 ≤ |y i| * (s * t) := (div_le_iff₀ (mul_pos hs htpos)).mp hlo
  have hsmall : |y i| * t < 2 := (lt_div_iff₀ htpos).mp hhi
  have hs4 : 4 < s := by nlinarith [mul_lt_mul_of_pos_left hsmall hs]
  have hceilbound : 2 / (t * |y i|) ≤ s / 4 := by
    apply (div_le_iff₀ (mul_pos htpos ha)).mpr
    nlinarith only [hproduct]
  refine ⟨v, ?_, ?_, ?_⟩
  · rw [hpair]
    have h := mul_le_mul_of_nonneg_left hklo ha.le
    have he : |y i| * (2 / (t * |y i|)) = 2 * (1 / t) := by field_simp
    rwa [he] at h
  · rw [hpair]
    have h := mul_lt_mul_of_pos_left hkhi ha
    have he : |y i| * (2 / (t * |y i|) + 1) = 2 / t + |y i| := by field_simp
    rw [he] at h
    have htinv : 1 / t ≤ (1 / 8 : ℝ) := one_div_le_one_div_of_le (by norm_num) ht
    have hhi' : |y i| < 2 * (1 / t) := by simpa only [div_eq_mul_inv, one_mul] using hhi
    rw [div_eq_mul_inv] at h
    simp only [one_div] at htinv hhi' ⊢
    nlinarith
  · rw [hnorm]
    linarith

end GeometricGaussianLHL
end

end GaussianCoordinateShift

section ConstantWidthColumnNorm

/-!
## Column-norm failure at constant width
-/

noncomputable section

namespace GeometricGaussianLHL

theorem euclideanScalarShape_norm_le (R : ℕ) {s : ℝ} (hs : 0 < s) :
    ‖(euclideanScalarShape R s hs.ne').toContinuousLinearMap‖ ≤ s := by
  rw [euclideanScalarShape_toCLM, norm_smul, Real.norm_eq_abs, abs_of_pos hs]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := Euclidean R)) hs.le

theorem constantWidth_columnNorm_failure {R m : ℕ} (hR : 1 ≤ R) (hm : 1 ≤ m)
    {s δ : ℝ} (hs : 1 ≤ s) (hδ : 0 < δ) (hδone : δ ≤ 1) :
    (coefficientColumnLaw R m s (by linarith)).toMeasure
      (columnNormEvent (constantColumnThreshold s (constantColumnHeight R m δ)))ᶜ ≤
        ENNReal.ofReal (δ / 2) := by
  have hsp : 0 < s := by linarith
  have hH : 0 < constantColumnHeight R m δ :=
    (show (0 : ℝ) < R by exact_mod_cast (show 0 < R by omega)).trans_le
      (constantColumnHeight_ge_rank hm hδ hδone)
  have h := ellipsoidalColumnLaw_norm_tail (m := m) (euclideanScalarShape R s hsp.ne') hsp hH
    (euclideanScalarShape_norm_le R hsp)
  simp only [ellipsoidalColumnLaw, ellipsoidalGaussian_scalar_eq_product R s hsp] at h
  apply h.trans
  apply ENNReal.ofReal_le_ofReal
  exact logarithmic_gaussian_tail_budget (by omega) hδ hH.le rfl

end GeometricGaussianLHL
end

end ConstantWidthColumnNorm

section ConstantWidthContraction

/-!
## Uniform contraction at constant width

The constant-width contraction lemma for the actual product integer Gaussian. A large coordinate
supplies a disjoint integer translate with controlled total variation; the complementary case uses
the proved fourth-moment argument. A witness identity factor gives the block conclusion without
within-block independence.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace GeometricGaussianLHL

theorem productGaussian_large_coordinate_displacement {n : ℕ} {s t : ℝ}
    (hs : 1 ≤ s) (ht : 8 ≤ t) (y : Euclidean n) (hcube : y ∈ centeredUnitCube n)
    (i : Fin n) (hi : 8 / (s * t) ≤ |y i|) :
    ∃ v : Coeff n, 2 * (1 / t) ≤ inner ℝ y (integerEmbedding n v) ∧
      inner ℝ y (integerEmbedding n v) ≤ 1 - 2 * (1 / t) ∧
      discreteTotalVariation (productIntegerGaussian n s (by linarith))
        ((productIntegerGaussian n s (by linarith)).map (fun z => z + v)) ≤ 921 / 1000 := by
  have hsp : 0 < s := by linarith
  have htpos : 0 < t := by linarith
  by_cases hlarge : 2 / t ≤ |y i|
  · let v : Coeff n := Pi.single i (orientedInteger (y i) 1)
    have hpair : inner ℝ y (integerEmbedding n v) = |y i| := by
      rw [integerEmbedding_single_inner, mul_orientedInteger]
      simp
    refine ⟨v, ?_, ?_, ?_⟩
    · rw [hpair]
      simpa only [div_eq_mul_inv, one_mul] using hlarge
    · rw [hpair]
      have hicube : |y i| ≤ 1 / 2 := hcube i
      have htinv := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 8) ht
      linarith
    · exact (productIntegerGaussian_signed_unit_translation hs i (orientedInteger (y i) 1)
        (by rw [orientedInteger_abs]; norm_num)).le
  · obtain ⟨v, hvlo, hvhi, hvnorm⟩ := exists_large_coordinate_ceiling_shift y i hsp ht hi (lt_of_not_ge hlarge)
    refine ⟨v, hvlo, hvhi, ?_⟩
    have hnorm : ‖integerEmbedding n v‖ / s ≤ 1 / 2 := by
      apply (div_le_iff₀ hsp).mpr
      linarith
    have hsqrt : Real.sqrt (Real.pi / 2) ≤ (3 / 2 : ℝ) :=
      (Real.sqrt_le_iff).mpr ⟨by norm_num, by linarith [Real.pi_le_four]⟩
    have hprod := mul_le_mul hsqrt hnorm (div_nonneg (norm_nonneg _) hsp.le) (by norm_num : (0 : ℝ) ≤ 3 / 2)
    have htv := productIntegerGaussian_translate_variation s hsp v
    linarith

theorem productGaussian_large_coordinate_contraction {n : ℕ} {s t : ℝ}
    (hs : 1 ≤ s) (ht : 8 ≤ t) (y : Euclidean n) (hcube : y ∈ centeredUnitCube n)
    (i : Fin n) (hi : 8 / (s * t) ≤ |y i|) :
    (∑' z : Coeff n, (productIntegerGaussian n s (by linarith) z).toReal *
      periodicGaussian t (inner ℝ y (integerEmbedding n z))) ≤ 39 / 40 := by
  obtain ⟨v, hvlo, hvhi, htv⟩ := productGaussian_large_coordinate_displacement hs ht y hcube i hi
  let p := productIntegerGaussian n s (by linarith)
  have he := pmf_compl_of_disjoint_image p (integerSlab y (1 / t)) (fun z => z + v)
    (add_left_injective v) (integerSlab_disjoint_translate y (1 / t) v hvlo hvhi)
  apply periodicGaussian_expectation_of_escape p _ ht
  have hset : (integerSlab y (1 / t))ᶜ =
      {z | 1 / t ≤ integerDistance (inner ℝ y (integerEmbedding n z))} := by
    ext z
    simp [integerSlab]
  rw [← hset]
  change discreteTotalVariation p (p.map (fun z => z + v)) ≤ 921 / 1000 at htv
  linarith

/-- The constant-width contraction lemma's scalar assertion, with the original constant and
parameters. -/
theorem constantWidth_scalar_contraction {n : ℕ} (hn : 1 ≤ n) {s H : ℝ}
    (hs : 1 ≤ s) (hH : (n : ℝ) ≤ H) (y : Euclidean n) (hcube : y ∈ centeredUnitCube n)
    (hlen : 1 / (4 * s * Real.sqrt H) ≤ ‖y‖) :
    (∑' z : Coeff n, (productIntegerGaussian n s (by linarith) z).toReal *
      periodicGaussian (640 * Real.sqrt H) (inner ℝ y (integerEmbedding n z))) ≤ 39 / 40 := by
  by_cases hsmall : ∀ i, |y i| ≤ 8 / (s * (640 * Real.sqrt H))
  · exact constantWidth_small_coordinate_contraction hn hs hH y hlen hsmall
  · push Not at hsmall
    obtain ⟨i, hi⟩ := hsmall
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hH1 : 1 ≤ H := hn'.trans hH
    have hroot : 1 ≤ Real.sqrt H :=
      (Real.le_sqrt (by norm_num) (by linarith)).mpr (by simpa using hH1)
    exact productGaussian_large_coordinate_contraction hs (by linarith) y hcube i hi.le

/-- The constant-width contraction lemma's block assertion. The identity witness is the only
relation required between factors; no independence within a block is assumed. -/
theorem constantWidth_block_contraction {n d : ℕ} (hn : 1 ≤ n) (hd : d ≤ n) {s H : ℝ}
    (hs : 1 ≤ s) (hH : (n : ℝ) ≤ H) (y : Euclidean n) (hcube : y ∈ centeredUnitCube n)
    (hlen : 1 / (4 * s * Real.sqrt H) ≤ ‖y‖)
    (g : Fin d → Coeff n → ℝ) (i : Fin d)
    (hwitness : ∀ z, g i z = inner ℝ y (integerEmbedding n z)) :
    (∑' z : Coeff n, (productIntegerGaussian n s (by linarith) z).toReal *
      ∏ j, periodicGaussian (640 * Real.sqrt H) (g j z)) ≤ 49 / 50 := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hH1 : 1 ≤ H := hn'.trans hH
  have hroot : 1 ≤ Real.sqrt H :=
    (Real.le_sqrt (by norm_num) (by linarith)).mpr (by simpa using hH1)
  apply periodicGaussian_block_contraction _ g i (by linarith)
  · have hd' : (d : ℝ) ≤ n := by exact_mod_cast hd
    rw [mul_pow, Real.sq_sqrt (by linarith : 0 ≤ H)]
    nlinarith
  · simp_rw [hwitness]
    exact constantWidth_scalar_contraction hn hs hH y hcube hlen

theorem constantWidth_operator_column_contraction {n d : ℕ} (hn : 1 ≤ n) (hd : d ≤ n) {s H : ℝ}
    (hs : 1 ≤ s) (hH : (n : ℝ) ≤ H) (y : Euclidean n) (hcube : y ∈ centeredUnitCube n)
    (hlen : 1 / (4 * s * Real.sqrt H) ≤ ‖y‖)
    (T : Fin d → Euclidean n →ₗ[ℝ] Euclidean n) (i : Fin d) (hidentity : T i = LinearMap.id) :
    (∑' z : Coeff n, (productIntegerGaussian n s (by linarith) z).toReal *
      operatorColumnFactor T (640 * Real.sqrt H) y z) ≤ 49 / 50 := by
  apply constantWidth_block_contraction hn hd hs hH y hcube hlen
    (fun j z => inner ℝ y (T j (integerEmbedding n z))) i
  intro z
  rw [hidentity, LinearMap.id_apply]

/-- Literal integer multiplication matrices, as used in the ring-column construction. In particular
this covers the matrices in the constant-width contraction lemma. -/
theorem constantWidth_coefficient_column_contraction {n d : ℕ} (hn : 1 ≤ n) (hd : d ≤ n) {s H : ℝ}
    (hs : 1 ≤ s) (hH : (n : ℝ) ≤ H) (y : Euclidean n) (hcube : y ∈ centeredUnitCube n)
    (hlen : 1 / (4 * s * Real.sqrt H) ≤ ‖y‖)
    (T : Fin d → Matrix (Fin n) (Fin n) ℤ) (i : Fin d) (hidentity : T i = 1) :
    (∑' z : Coeff n, (productIntegerGaussian n s (by linarith) z).toReal *
      operatorColumnFactor (fun j => realCoefficientMap (T j)) (640 * Real.sqrt H) y z) ≤ 49 / 50 := by
  apply constantWidth_operator_column_contraction hn hd hs hH y hcube hlen _ i
  rw [hidentity, realCoefficientMap_one]

end GeometricGaussianLHL
end

end ConstantWidthContraction

section GaussianConstantRank

/-!
## Rank failure at constant coefficient width

The exact unit-coordinate overlap controls every proper real subspace.
Sequential exposure then contracts the existing rank potential by `19/20`.
The paper's column condition pays for the resulting rank-failure bound.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace GeometricGaussianLHL

theorem productIntegerGaussian_subspace_mass {R : ℕ} {s : ℝ} (hs : 1 ≤ s)
    (V : Submodule ℝ (Euclidean R)) (hV : V ≠ ⊤) :
    (productIntegerGaussian R s (by linarith)).toMeasure.real
      {z : Coeff R | integerEmbedding R z ∈ V} < (921 / 1000 : ℝ) := by
  have hsp : 0 < s := by linarith
  have ho : Vᗮ ≠ ⊥ := fun hz => hV (Submodule.orthogonal_eq_bot_iff.mp hz)
  obtain ⟨h, hh, hn⟩ := Submodule.exists_mem_ne_zero_of_ne_bot ho
  have hi : ∃ i : Fin R, h i ≠ 0 := by
    by_contra! hi
    apply hn
    ext i
    exact hi i
  obtain ⟨i, hi⟩ := hi
  let v : Coeff R := Pi.single i (orientedInteger (h i) 1)
  have hvanish : ∀ x ∈ V, inner ℝ h x = 0 := (V.mem_orthogonal' h).mp hh
  have hpositive : 0 < inner ℝ h (integerEmbedding R v) := by
    rw [integerEmbedding_single_inner, mul_orientedInteger]
    simpa only [Int.cast_one, mul_one] using abs_pos.mpr hi
  have hsubset : {z : Coeff R | integerEmbedding R z ∈ V} ⊆
      {z : Coeff R | inner ℝ h (integerEmbedding R z) = 0} := fun z hz => hvanish _ hz
  exact ((measureReal_mono hsubset).trans (pmf_hyperplane_le_translate_variation
    (productIntegerGaussian R s hsp) h v hpositive)).trans_lt
      (productIntegerGaussian_signed_unit_translation hs i (orientedInteger (h i) 1)
        (by rw [orientedInteger_abs]; norm_num))

theorem constantRankPotential_one_step {R : ℕ} (p : PMF (Coeff R))
    (hanti : ∀ V : Submodule ℝ (Euclidean R), V ≠ ⊤ →
      p.toMeasure.real {x : Coeff R | integerEmbedding R x ∈ V} ≤ 37 / 40)
    (V : Submodule ℝ (Euclidean R)) :
    (∑' x : Coeff R, (p x).toReal * rankPotential (V ⊔ Submodule.span ℝ {integerEmbedding R x})) ≤
      (19 / 20) * rankPotential V := by
  classical
  by_cases hV : V = ⊤
  · simp [hV, rankPotential]
  · let A : Set (Coeff R) := {x | integerEmbedding R x ∈ V}ᶜ
    have hprob : (3 / 40 : ℝ) ≤ p.toMeasure.real A := by
      rw [show A = {x : Coeff R | integerEmbedding R x ∈ V}ᶜ from rfl,
        measureReal_compl (Set.to_countable _).measurableSet, probReal_univ]
      linarith [hanti V hV]
    have he := pmf_expectation_bound_of_event p
      (fun x => rankPotential (V ⊔ Submodule.span ℝ {integerEmbedding R x})) A
      (fun x => rankPotential_nonneg _) (fun x => rankPotential_insert_le V _)
      (fun x hx => rankPotential_insert_notMem V hx)
    have hp := mul_le_mul_of_nonneg_left hprob (rankPotential_nonneg V)
    nlinarith

theorem constantRankPotential_one_step_ennreal {R : ℕ} (p : PMF (Coeff R))
    (hanti : ∀ V : Submodule ℝ (Euclidean R), V ≠ ⊤ →
      p.toMeasure.real {x : Coeff R | integerEmbedding R x ∈ V} ≤ 37 / 40)
    (V : Submodule ℝ (Euclidean R)) :
    (∑' x : Coeff R, p x * ENNReal.ofReal
      (rankPotential (V ⊔ Submodule.span ℝ {integerEmbedding R x}))) ≤
        ENNReal.ofReal ((19 / 20) * rankPotential V) := by
  apply pmf_ennreal_expectation_le_of_bounded _ _
    (fun x => rankPotential_nonneg _) (fun x => rankPotential_insert_le V _)
  exact constantRankPotential_one_step p hanti V

theorem constantRankPotential_independent_expectation {R : ℕ} (p : PMF (Coeff R))
    (hanti : ∀ V : Submodule ℝ (Euclidean R), V ≠ ⊤ →
      p.toMeasure.real {x : Coeff R | integerEmbedding R x ∈ V} ≤ 37 / 40) :
    ∀ (m : ℕ) (V : Submodule ℝ (Euclidean R)),
      (∑' X : Fin m → Coeff R, independentProduct (fun _ => p) X *
        ENNReal.ofReal (rankPotential (sampledSpan V X))) ≤
          ENNReal.ofReal ((19 / 20 : ℝ) ^ m * rankPotential V) := by
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
      _ ≤ ∑' x : Coeff R, p x * ENNReal.ofReal ((19 / 20 : ℝ) ^ m * rankPotential (next x)) := by
        apply ENNReal.tsum_le_tsum
        intro x
        exact mul_le_mul_right (ih (next x)) (p x)
      _ = ENNReal.ofReal ((19 / 20 : ℝ) ^ m) *
          (∑' x : Coeff R, p x * ENNReal.ofReal (rankPotential (next x))) := by
        simp_rw [ENNReal.ofReal_mul (pow_nonneg (by norm_num : (0 : ℝ) ≤ 19 / 20) m)]
        rw [← ENNReal.tsum_mul_left]
        apply tsum_congr
        intro x
        ring
      _ ≤ ENNReal.ofReal ((19 / 20 : ℝ) ^ m) * ENNReal.ofReal ((19 / 20) * rankPotential V) := by
        exact mul_le_mul_right (constantRankPotential_one_step_ennreal p hanti V) _
      _ = _ := by
        rw [← ENNReal.ofReal_mul (pow_nonneg (by norm_num : (0 : ℝ) ≤ 19 / 20) m), pow_succ]
        congr 1
        ring

theorem independent_columns_constant_rank_failure {R : ℕ} (p : PMF (Coeff R))
    (hanti : ∀ V : Submodule ℝ (Euclidean R), V ≠ ⊤ →
      p.toMeasure.real {x : Coeff R | integerEmbedding R x ∈ V} ≤ 37 / 40) (m : ℕ) :
    (independentProduct (fun _ : Fin m => p)).toMeasure
      {X | sampledSpan ⊥ X ≠ ⊤} ≤ ENNReal.ofReal ((3 : ℝ) ^ R * (19 / 20 : ℝ) ^ m) := by
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
      ENNReal.ofReal ((19 / 20 : ℝ) ^ m) := by
    apply (constantRankPotential_independent_expectation p hanti m ⊥).trans
    apply ENNReal.ofReal_le_ofReal
    have h := mul_le_mul_of_nonneg_left (rankPotential_le_one (⊥ : Submodule ℝ (Euclidean R)))
      (pow_nonneg (by norm_num : (0 : ℝ) ≤ 19 / 20) m)
    simpa only [mul_one] using h
  have hcancel : ENNReal.ofReal ((3 : ℝ) ^ R) * ENNReal.ofReal ((1 / 3 : ℝ) ^ R) = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity), ← mul_pow]
    norm_num
  calc
    P.toMeasure A = ENNReal.ofReal ((3 : ℝ) ^ R) * (ENNReal.ofReal ((1 / 3 : ℝ) ^ R) * P.toMeasure A) := by
      rw [← mul_assoc, hcancel, one_mul]
    _ ≤ ENNReal.ofReal ((3 : ℝ) ^ R) * ENNReal.ofReal ((19 / 20 : ℝ) ^ m) :=
      mul_le_mul_right (hweighted.trans he) _
    _ = _ := (ENNReal.ofReal_mul (by positivity)).symm

theorem constantWidth_rank_failure_budget {R m : ℕ} {W δ : ℝ}
    (hW : 3 ≤ W) (hδ : 0 < δ)
    (hbudget : (R : ℝ) * Real.log W + 2 * Real.log (1 / δ) ≤ (m : ℝ) * Real.log (50 / 49)) :
    (3 : ℝ) ^ R * (19 / 20 : ℝ) ^ m ≤ δ ^ 2 := by
  have hwlog := Real.log_le_log (by norm_num : (0 : ℝ) < 3) hW
  have hclog := Real.log_le_log (by norm_num : (0 : ℝ) < 50 / 49) (by norm_num : (50 / 49 : ℝ) ≤ 20 / 19)
  have h₁ := mul_le_mul_of_nonneg_left hwlog (show (0 : ℝ) ≤ R by positivity)
  have h₂ := mul_le_mul_of_nonneg_left hclog (show (0 : ℝ) ≤ m by positivity)
  have hb : (R : ℝ) * Real.log 3 + 2 * Real.log (1 / δ) ≤ (m : ℝ) * Real.log (20 / 19) := by
    linarith
  apply remainder_le_of_column_condition (by norm_num : (0 : ℝ) < 3)
    (by norm_num : (0 : ℝ) < 19 / 20) hδ
  convert hb using 1
  norm_num


theorem productGaussian_columns_rank_failure {R : ℕ} {s : ℝ} (hs : 1 ≤ s) (m : ℕ) :
    (independentProduct (fun _ : Fin m => productIntegerGaussian R s (by linarith))).toMeasure
      {X | sampledSpan ⊥ X ≠ ⊤} ≤ ENNReal.ofReal ((3 : ℝ) ^ R * (19 / 20 : ℝ) ^ m) := by
  apply independent_columns_constant_rank_failure
  intro V hV
  exact (productIntegerGaussian_subspace_mass hs V hV).le.trans (by norm_num)

theorem productGaussian_constantWidth_rank_failure {R m : ℕ} {s W δ : ℝ}
    (hs : 1 ≤ s) (hW : 3 ≤ W) (hδ : 0 < δ)
    (hbudget : (R : ℝ) * Real.log W + 2 * Real.log (1 / δ) ≤ (m : ℝ) * Real.log (50 / 49)) :
    (independentProduct (fun _ : Fin m => productIntegerGaussian R s (by linarith))).toMeasure
      {X | sampledSpan ⊥ X ≠ ⊤} ≤ ENNReal.ofReal (δ ^ 2) :=
  (productGaussian_columns_rank_failure hs m).trans
    (ENNReal.ofReal_le_ofReal (constantWidth_rank_failure_budget hW hδ hbudget))

end GeometricGaussianLHL
end

end GaussianConstantRank

section ConstantWidthRemainder

/-!
## Remainder decay at constant width

The actual independent Gaussian columns factor the theta integrand. The proved `49/50` block
contraction, determinant bound, Tonelli and Markov then give the remainder exceptional-event bound
in the constant-width smoothing theorem.
-/

noncomputable section

open scoped ENNReal

namespace GeometricGaussianLHL

theorem constantWidth_block_expectation {R d m : ℕ} (hR : 1 ≤ R) (hdR : d ≤ R)
    {s H : ℝ} (hs : 1 ≤ s) (hH : (R : ℝ) ≤ H)
    (T : Fin d → Matrix (Fin R) (Fin R) ℤ) (i : Fin d) (hidentity : T i = 1)
    (y : Euclidean R) (hcube : y ∈ centeredUnitCube R)
    (hfar : 1 / (4 * s * Real.sqrt H) ≤ ‖y‖) :
    (∑' X : Fin m → Coeff R, coefficientColumnLaw R m s (by linarith) X *
      ENNReal.ofReal (thetaIntegrand (blockCoefficientMatrix T X) (constantThetaWidth H) y)) ≤
        ENNReal.ofReal ((49 / 50 : ℝ) ^ m) := by
  let t := constantThetaWidth H
  let F := operatorColumnFactor (fun k => realCoefficientMap (T k)) t y
  have htpos : 0 < t := by
    have h := (constantWidth_parameters hR (by norm_num : 1 ≤ (1 : ℕ)) hs hH).2.1
    change 8 ≤ t at h
    linarith
  have hF : ∀ x, 0 ≤ F x := operatorColumnFactor_nonneg _ htpos y
  have hsingle : (∑' x, productIntegerGaussian R s (by linarith) x * ENNReal.ofReal (F x)) ≤
      ENNReal.ofReal (49 / 50) := by
    apply pmf_ennreal_expectation_le_of_bounded _ _ hF (operatorColumnFactor_le _ htpos y)
    exact constantWidth_coefficient_column_contraction hR hdR hs hH y hcube hfar T i hidentity
  have heq (X : Fin m → Coeff R) :
      ENNReal.ofReal (thetaIntegrand (blockCoefficientMatrix T X) t y) = ∏ j, ENNReal.ofReal (F (X j)) := by
    rw [thetaIntegrand_block_factorization]
    exact ENNReal.ofReal_prod_of_nonneg (fun j _ => hF (X j))
  change (∑' X, independentProduct (fun _ : Fin m => productIntegerGaussian R s (by linarith)) X *
    ENNReal.ofReal (thetaIntegrand (blockCoefficientMatrix T X) t y)) ≤ _
  simp_rw [heq]
  have h := independentProduct_expectation_le (fun _ : Fin m => productIntegerGaussian R s (by linarith))
    (fun _ x => ENNReal.ofReal (F x)) (fun _ => ENNReal.ofReal (49 / 50)) (fun _ => hsingle)
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 49 / 50)] using h

theorem constantWidth_remainder_expectation {R d m : ℕ} (hR : 1 ≤ R) (hm : 1 ≤ m) (hdR : d ≤ R)
    {s H : ℝ} (hs : 1 ≤ s) (hH : (R : ℝ) ≤ H)
    (T : Fin d → Matrix (Fin R) (Fin R) ℤ) (i : Fin d) (hidentity : T i = 1)
    (hT : ∀ k, ∀ x : Euclidean R, ‖realCoefficientMap (T k) x‖ ≤ ‖x‖) :
    let t := constantThetaWidth H
    let U := constantColumnThreshold s H
    (∑' X : Fin m → Coeff R, coefficientColumnLaw R m s (by linarith) X *
      (columnNormEvent U).indicator
        (fun X => ENNReal.ofReal (thetaRemainder (blockCoefficientMatrix T X) U t)) X) ≤
      ENNReal.ofReal (constantMatrixScale R (m * d) s H ^ R * (49 / 50 : ℝ) ^ m) := by
  dsimp only
  let t := constantThetaWidth H
  let U := constantColumnThreshold s H
  let W := constantMatrixScale R (m * d) s H
  have hd : 1 ≤ d := by have hi := i.isLt; omega
  have hM : 1 ≤ m * d := by nlinarith
  obtain ⟨hU, ht, hW⟩ := constantWidth_parameters hR hM hs hH
  have htpos : 0 < t := by change 8 ≤ t at ht; linarith
  have hcols : ∀ X ∈ (columnNormEvent U : Set (Fin m → Coeff R)),
      ∀ j, ‖realColumn (blockCoefficientMatrix T X) j‖ ≤ U := by
    intro X hX
    simpa only [one_mul] using blockCoefficientMatrix_column_norm T X (by norm_num : (0 : ℝ) ≤ 1)
      (fun k x => by simpa only [one_mul] using hT k x) hX
  have hcontract : ∀ y ∈ centeredUnitCube R \ nearOriginBall R U,
      (∑' X : Fin m → Coeff R, coefficientColumnLaw R m s (by linarith) X *
        ENNReal.ofReal (thetaIntegrand (blockCoefficientMatrix T X) t y)) ≤
          ENNReal.ofReal ((49 / 50 : ℝ) ^ m) := by
    intro y hy
    have hfar : 1 / (4 * s * Real.sqrt H) ≤ ‖y‖ := by
      have hh : 1 / (4 * U) < ‖y‖ := lt_of_not_ge hy.2
      have hh' : 1 / (4 * s * Real.sqrt H) < ‖y‖ := by
        simpa only [U, constantColumnThreshold, mul_assoc] using hh
      exact hh'.le
    exact constantWidth_block_expectation hR hdR hs hH T i hidentity y hy.1 hfar
  have h := expected_thetaRemainder_bound (by omega) (coefficientColumnLaw R m s (by linarith))
    (blockCoefficientMatrix T) (columnNormEvent U) (by linarith : 0 ≤ U) htpos
    (ENNReal.ofReal ((49 / 50 : ℝ) ^ m)) hcols hcontract
  change _ ≤ ENNReal.ofReal (W ^ R) * ENNReal.ofReal ((49 / 50 : ℝ) ^ m) at h
  rw [← ENNReal.ofReal_mul (show 0 ≤ W ^ R by dsimp [W]; positivity)] at h
  exact h

theorem constantWidth_remainder_failure {R d m : ℕ} (hR : 1 ≤ R) (hm : 1 ≤ m) (hdR : d ≤ R)
    {s H δ : ℝ} (hs : 1 ≤ s) (hH : (R : ℝ) ≤ H) (hδ : 0 < δ)
    (T : Fin d → Matrix (Fin R) (Fin R) ℤ) (i : Fin d) (hidentity : T i = 1)
    (hT : ∀ k, ∀ x : Euclidean R, ‖realCoefficientMap (T k) x‖ ≤ ‖x‖)
    (hbudget : (R : ℝ) * Real.log (constantMatrixScale R (m * d) s H) +
      2 * Real.log (1 / δ) ≤ (m : ℝ) * Real.log (50 / 49)) :
    (coefficientColumnLaw R m s (by linarith)).toMeasure
      ((columnNormEvent (constantColumnThreshold s H)) ∩
        {X | δ < thetaRemainder (blockCoefficientMatrix T X) (constantColumnThreshold s H) (constantThetaWidth H)}) ≤
          ENNReal.ofReal δ := by
  have hd : 1 ≤ d := by have hi := i.isLt; omega
  have hM : 1 ≤ m * d := by nlinarith
  have hW := (constantWidth_parameters hR hM hs hH).2.2
  have hnum := constant_remainder_le (by linarith : 0 < constantMatrixScale R (m * d) s H) hδ hbudget
  apply pmf_markov_indicator_square _ _ _ hδ
  exact (constantWidth_remainder_expectation hR hm hdR hs hH T i hidentity hT).trans
    (ENNReal.ofReal_le_ofReal hnum)

end GeometricGaussianLHL
end

end ConstantWidthRemainder

section ConstantWidthMatrix

/-!
## The finite constant-width coefficient certificate

Actual independent Gaussian columns of scalar width at least one satisfy
integer surjectivity, intrinsic-dual smoothing and column bounds on one
event of probability at least `1 - 3δ`. The identity multiplication block
and contraction hypotheses hold for the power-of-two integral basis.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace GeometricGaussianLHL

theorem constantWidth_matrix_failure {R d m : ℕ} (hR : 1 ≤ R) (hm : 1 ≤ m) (hdR : d ≤ R)
    {s δ : ℝ} (hs : 1 ≤ s) (hδ : 0 < δ) (hδbound : δ ≤ 1 / 32)
    (T : Fin d → Matrix (Fin R) (Fin R) ℤ) (i : Fin d) (hidentity : T i = 1)
    (hT : ∀ k, ∀ x : Euclidean R, ‖realCoefficientMap (T k) x‖ ≤ ‖x‖)
    (hbudget : (R : ℝ) * Real.log (constantMatrixScale R (m * d) s (constantColumnHeight R m δ)) +
      2 * Real.log (1 / δ) ≤ (m : ℝ) * Real.log (50 / 49)) :
    (coefficientColumnLaw R m s (by linarith)).toMeasure
      (coefficientGoodEvent T (constantColumnThreshold s (constantColumnHeight R m δ))
        (constantThetaWidth (constantColumnHeight R m δ)) δ)ᶜ ≤ ENNReal.ofReal (3 * δ) := by
  let H := constantColumnHeight R m δ
  let t := constantThetaWidth H
  let U := constantColumnThreshold s H
  let W := constantMatrixScale R (m * d) s H
  let P := coefficientColumnLaw R m s (by linarith)
  let G : Set (Fin m → Coeff R) := columnNormEvent U
  let F : Set (Fin m → Coeff R) := {X | sampledSpan ⊥ X ≠ ⊤}
  let E : Set (Fin m → Coeff R) := {X | δ < thetaRemainder (blockCoefficientMatrix T X) U t}
  have hd : 1 ≤ d := by have hi := i.isLt; omega
  have hM : 1 ≤ m * d := by nlinarith
  have hMR : m * d ≤ R * m := by simpa [Nat.mul_comm] using Nat.mul_le_mul_left m hdR
  have hδpos : 0 < δ := hδ
  have hδsmall : δ ≤ 1 / 32 := hδbound
  have hH := constantColumnHeight_ge_rank (R := R) hm hδ (by linarith)
  obtain ⟨hU, ht8, hW⟩ := constantWidth_parameters hR hM hs hH
  have ht : 1 ≤ t := by change 8 ≤ t at ht8; linarith
  have hB : 1 ≤ U := hU
  have hmain : 3 * (m * d : ℕ) * Real.exp (-Real.pi * t ^ 2 / 2) ≤ δ / 2 :=
    constantWidth_mainTerm_small hR hm (by omega) hMR hδ (by linarith)
  have hgood : ∀ X, X ∈ G → X ∉ F → X ∉ E → X ∈ coefficientGoodEvent T U t δ := by
    intro X hG hF hE
    have hspan : Submodule.span ℝ (Set.range (fun j => integerEmbedding R (X j))) = ⊤ := by
      have hspan : sampledSpan ⊥ X = ⊤ := by simpa only [F, Set.mem_setOf_eq, not_not] using hF
      simpa only [sampledSpan, bot_sup_eq] using hspan
    have hfull := blockCoefficientMatrix_fullRank_of_span T X i hidentity hspan
    have hcol : ∀ j, ‖realColumn (blockCoefficientMatrix T X) j‖ ≤ U := by
      simpa only [one_mul] using blockCoefficientMatrix_column_norm T X (by norm_num : (0 : ℝ) ≤ 1)
        (fun k x => by simpa only [one_mul] using hT k x) hG
    have hrem : thetaRemainder (blockCoefficientMatrix T X) U t ≤ δ := le_of_not_gt hE
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
  have hnorm : P.toMeasure Gᶜ ≤ ENNReal.ofReal (δ / 2) :=
    constantWidth_columnNorm_failure hR hm hs hδ (by linarith)
  have hrank : P.toMeasure F ≤ ENNReal.ofReal (δ ^ 2) :=
    productGaussian_constantWidth_rank_failure hs hW hδ hbudget
  have hrem : P.toMeasure (G ∩ E) ≤ ENNReal.ofReal δ :=
    constantWidth_remainder_failure hR hm hdR hs hH hδ T i hidentity hT hbudget
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

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- The coefficient form of the constant-width smoothing theorem, with metric transport and a common
exceptional event for all positive errors.
-/
theorem constantWidth_matrix_certificate {R d m : ℕ} (hR : 1 ≤ R) (hm : 1 ≤ m) (hdR : d ≤ R)
    {s δ α : ℝ} (hs : 1 ≤ s) (hδ : 0 < δ) (hδbound : δ ≤ 1 / 32)
    (T : Fin d → Matrix (Fin R) (Fin R) ℤ) (i : Fin d) (hidentity : T i = 1)
    (hT : ∀ k, ∀ x : Euclidean R, ‖realCoefficientMap (T k) x‖ ≤ ‖x‖)
    (C : Euclidean (m * d) →L[ℝ] F) (hC : ‖C‖ ≤ α)
    (hbudget : (R : ℝ) * Real.log (constantMatrixScale R (m * d) s (constantColumnHeight R m δ)) +
      2 * Real.log (1 / δ) ≤ (m : ℝ) * Real.log (50 / 49)) :
    let H := constantColumnHeight R m δ
    let t := constantThetaWidth H
    let U := constantColumnThreshold s H
    ∃ G : Set (Fin m → Coeff R),
      ENNReal.ofReal (1 - 3 * δ) ≤ (coefficientColumnLaw R m s (by linarith)).toMeasure G ∧
      ∀ X ∈ G,
        Function.Surjective (coefficientMap (blockCoefficientMatrix T X)) ∧
        nonzeroDualMass (euclideanKernel (blockCoefficientMatrix T X)) t ≤ ENNReal.ofReal (2 * δ) ∧
        smoothingParameter (latticeImage C (euclideanKernel (blockCoefficientMatrix T X))) (2 * δ) ≤ α * t ∧
        (∀ j, ‖integerEmbedding R (X j)‖ ≤ U) ∧
        ∀ ε : ℝ, 0 < ε →
          smoothingParameter (latticeImage C (euclideanKernel (blockCoefficientMatrix T X))) ε ≤
            (α * t) * Real.sqrt (errorExponent (2 * δ) ε) := by
  dsimp only
  refine ⟨coefficientGoodEvent T (constantColumnThreshold s (constantColumnHeight R m δ))
    (constantThetaWidth (constantColumnHeight R m δ)) δ, ?_, ?_⟩
  · exact pmf_good_probability_of_compl_bound _ _ (by positivity)
      (constantWidth_matrix_failure hR hm hdR hs hδ hδbound T i hidentity hT hbudget)
  · intro X hX
    have hmetric := coefficientGoodEvent_metric_bounds T hδ (by linarith) C hC X hX
    exact ⟨hX.1, hX.2.1.2, hmetric.1, hX.2.2, hmetric.2⟩

end GeometricGaussianLHL
end

end ConstantWidthMatrix

section NumberFieldConstantWidth

/-!
## Constant-width smoothing over power-of-two number fields

The constant-width smoothing theorem for the actual ring-Gaussian matrix distribution and canonical
kernel, with the printed scale and constants. The same argument includes the rational case in the
remark following the theorem.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Module NumberField MeasureTheory
open scoped ENNReal

namespace GeometricGaussianLHL

def powerTwoConstantScale (d r m : ℕ) (s ell : ℝ) : ℝ :=
  640 * (s / Real.sqrt d) * constantColumnHeight (r * d) m (realSecurityError (ell + 6)) *
    Real.sqrt ((m : ℝ) / r)

theorem constantMatrixScale_powerTwo {d r m : ℕ} (hd : 0 < d) (hm : 1 ≤ m)
    {ell : ℝ} (hell : 1 ≤ ell) (s : ℝ) :
    constantMatrixScale (r * d) (m * d) (s / Real.sqrt d)
      (constantColumnHeight (r * d) m (realSecurityError (ell + 6))) =
        powerTwoConstantScale d r m s ell := by
  have hdreal : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hδ := realSecurityError_pos (ell + 6)
  have hH : 0 ≤ constantColumnHeight (r * d) m (realSecurityError (ell + 6)) :=
    (show (0 : ℝ) ≤ (r * d : ℕ) by positivity).trans
      (constantColumnHeight_ge_rank hm hδ (by have h := real_constant_failureBudget_le hell; linarith))
  unfold constantMatrixScale constantThetaWidth constantColumnThreshold powerTwoConstantScale
  rw [Nat.cast_mul, Nat.cast_mul, mul_div_mul_right _ _ hdreal]
  calc
    _ = 640 * (s / Real.sqrt d) *
        (Real.sqrt (constantColumnHeight (r * d) m (realSecurityError (ell + 6)))) ^ 2 *
          Real.sqrt ((m : ℝ) / r) := by ring
    _ = _ := by rw [Real.sq_sqrt hH]

variable (K : Type*) [Field K] [NumberField K] {k : ℕ}
  [IsCyclotomicExtension {2 ^ (k + 1)} ℚ K] {ζ : K}

local instance constantEmbeddingsFintype : Fintype (K →+* ℂ) := inferInstance
local instance constantAmbientInner : InnerProductSpace ℝ (CanonicalAmbient K) := inferInstance
local instance constantSpaceInner : InnerProductSpace ℝ (canonicalSpace K) := inferInstance
local instance constantPowerInner (n : ℕ) : InnerProductSpace ℝ (CanonicalPower K n) := inferInstance

/-- The constant-width smoothing theorem, with the common event for all positive error parameters.
The coefficient dual mass and column bounds are retained for the LHL consequences. -/
theorem numberField_constantWidth_certificate (hζ : IsPrimitiveRoot ζ (2 ^ (k + 1)))
    {r m : ℕ} (hr : 1 ≤ r) (hmr : r < m) {ell s : ℝ} (hell : 1 ≤ ell)
    (hs : 0 < s) (hwidth : Real.sqrt (2 ^ (k + 1)).totient ≤ s)
    (hbudget : ((r * (2 ^ (k + 1)).totient : ℕ) : ℝ) *
      Real.log (powerTwoConstantScale (2 ^ (k + 1)).totient r m s ell) +
      2 * Real.log (1 / realSecurityError (ell + 6)) ≤ (m : ℝ) * Real.log (50 / 49)) :
    let d := (2 ^ (k + 1)).totient
    let b := cyclotomicIntegralBasis K hζ
    let δ := realSecurityError (ell + 6)
    let H := constantColumnHeight (r * d) m δ
    let B := 640 * Real.sqrt (d * H)
    ∃ G : Set (Matrix (Fin r) (Fin m) (𝓞 K)),
      ENNReal.ofReal (1 - 3 * δ) ≤ (numberFieldMatrixLaw K b r m s hs.ne').toOuterMeasure G ∧
      ∀ X ∈ G,
        Function.Surjective X.mulVec ∧
        nonzeroDualMass (euclideanKernel (ringCoefficientMatrix b X)) (constantThetaWidth H) ≤
          ENNReal.ofReal (2 * δ) ∧
        smoothingParameter (canonicalKernel K X) (2 * δ) ≤ B ∧
        (∀ j, ‖integerEmbedding (r * d) (ringPowerCoordinates b r (fun a => X a j))‖ ≤
          constantColumnThreshold (s / Real.sqrt d) H) ∧
        ∀ ε : ℝ, 0 < ε → smoothingParameter (canonicalKernel K X) ε ≤
          B * Real.sqrt (errorExponent (2 * δ) ε) := by
  dsimp only
  let d := (2 ^ (k + 1)).totient
  let b := cyclotomicIntegralBasis K hζ
  let δ := realSecurityError (ell + 6)
  let H := constantColumnHeight (r * d) m δ
  let σ := s / Real.sqrt d
  let T := fun j : Fin d => ringPowerMultiplicationMatrix b r (b j)
  let E := matrixColumnCoordinates K b r m
  have hd : 1 ≤ d := integralBasis_dimension_pos K b
  have hdreal : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hR : 1 ≤ r * d := by nlinarith
  have hm : 1 ≤ m := by omega
  have hdR : d ≤ r * d := by nlinarith
  have hσ : 1 ≤ σ := (le_div_iff₀ (Real.sqrt_pos.mpr hdreal)).mpr (by simpa only [one_mul] using hwidth)
  have hδ : 0 < δ := realSecurityError_pos _
  have hδbound : δ ≤ 1 / 32 := (real_constant_failureBudget_le hell).trans (by norm_num)
  obtain ⟨hα, _, _, hμ⟩ := powerTwoBasis_constants K hζ
  have hTidentity : T 0 = 1 := by
    simp only [T, b, cyclotomicIntegralBasis_one K hζ 0 rfl, ringPowerMultiplicationMatrix_one]
  have hT : ∀ j, ∀ x : Euclidean (r * d), ‖realCoefficientMap (T j) x‖ ≤ ‖x‖ := by
    intro j x
    simpa only [b, hμ, one_mul] using basisPowerMultiplication_norm_le_mu K b r j x
  have hbudget' : ((r * d : ℕ) : ℝ) * Real.log (constantMatrixScale (r * d) (m * d) σ H) +
      2 * Real.log (1 / δ) ≤ (m : ℝ) * Real.log (50 / 49) := by
    simpa only [σ, H, δ, constantMatrixScale_powerTwo (by omega : 0 < d) hm hell s] using hbudget
  have hC : ‖(powerCanonicalEquiv K b m).toContinuousLinearMap‖ ≤ Real.sqrt d := by
    simpa only [b, hα] using powerCanonicalEquiv_norm_le K b m
  obtain ⟨Gc, hprob, hgood⟩ := constantWidth_matrix_certificate (F := CanonicalPower K m)
    hR hm hdR hσ hδ hδbound T 0 hTidentity hT
    (powerCanonicalEquiv K b m).toContinuousLinearMap hC hbudget'
  have hscale : Real.sqrt d * constantThetaWidth H = 640 * Real.sqrt (d * H) := by
    rw [constantThetaWidth, Real.sqrt_mul hdreal.le]
    ring
  refine ⟨E ⁻¹' Gc, ?_, ?_⟩
  · rw [PMF.toMeasure_apply_eq_toOuterMeasure_apply _ (Set.to_countable Gc).measurableSet] at hprob
    rw [← powerTwoMatrix_product K hζ r m hs, PMF.toOuterMeasure_map_apply] at hprob
    exact hprob
  · intro X hX
    obtain ⟨himage, hmass, hsmooth, hcols, hall⟩ := hgood (E X) hX
    have hblock : blockCoefficientMatrix T (E X) = ringCoefficientMatrix b X :=
      (ringCoefficientMatrix_eq_block b X).symm
    rw [hblock] at himage hmass hsmooth hall
    rw [← canonicalKernel_eq_image K b X, hscale] at hsmooth hall
    refine ⟨(ringCoefficientMatrix_surjective_iff b X).mp himage, hmass, hsmooth, ?_, hall⟩
    simpa only [E, matrixColumnCoordinates_apply] using hcols

end GeometricGaussianLHL
end

end NumberFieldConstantWidth

section ConstantWidthFamily

/-!
## Uniform column budgets at coefficient width one

The absolute constants below prove the asymptotic assertion of the constant-width asymptotic
parameter discussion. The threshold is independent of both the degree and the row count. A coarse
quadratic bound for the scale suffices inside its logarithm.
-/
noncomputable section
namespace GeometricGaussianLHL

def constantFamilyColumnCoefficient : ℝ := 5 / Real.log (50 / 49)

def constantFamilyThreshold : ℝ :=
  max 25 (max (Real.log (2 * (constantFamilyColumnCoefficient + 1)) ^ 2)
    (2560 * (constantFamilyColumnCoefficient + 1)))

theorem log_fifty_fortyninths_pos : 0 < Real.log (50 / 49 : ℝ) :=
  Real.log_pos (by norm_num)

theorem constantFamilyColumnCoefficient_pos : 0 < constantFamilyColumnCoefficient :=
  div_pos (by norm_num) log_fifty_fortyninths_pos

theorem constantFamilyColumnCoefficient_mul :
    constantFamilyColumnCoefficient * Real.log (50 / 49) = 5 :=
  div_mul_cancel₀ _ log_fifty_fortyninths_pos.ne'

theorem constantFamilyColumns_gt {x : ℝ} (hx : 1 ≤ x) :
    x < (polynomialFamilyColumns constantFamilyColumnCoefficient x : ℝ) := by
  have hc := constantFamilyColumnCoefficient_pos
  have hq : Real.log (50 / 49 : ℝ) ≤ Real.log (2 * x) :=
    Real.log_le_log (by norm_num) (by linarith)
  have h := mul_le_mul_of_nonneg_left hq (show 0 ≤ constantFamilyColumnCoefficient * x by positivity)
  rw [mul_right_comm _ x, constantFamilyColumnCoefficient_mul] at h
  exact (show x < 5 * x by linarith).trans_le (h.trans (polynomialFamilyColumns_lower _ _))

theorem constantFamily_height_le {R m : ℕ} {ell : ℝ} (hm : 0 < m)
    (hell : 6 ≤ ell) (hellR : ell ≤ R) (hlog : Real.log (2 * m) ≤ (R : ℝ)) :
    constantColumnHeight R m (realSecurityError (ell + 6)) ≤ 4 * R := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  unfold constantColumnHeight
  rw [div_eq_mul_inv, Real.log_mul (by positivity : (2 : ℝ) * m ≠ 0)
    (inv_ne_zero (realSecurityError_pos _).ne'), ← one_div, log_inv_realSecurityError]
  have htwo : Real.log (2 : ℝ) ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have h := mul_le_mul_of_nonneg_left htwo (show 0 ≤ ell + 6 by linarith)
  nlinarith

theorem constantFamily_sqrt_ratio_le {r m : ℕ} (hr : 1 ≤ r) {c x : ℝ}
    (hc : 0 < c) (hx : 0 ≤ x) (hm : (m : ℝ) ≤ (c + 1) * x ^ 2) :
    Real.sqrt ((m : ℝ) / r) ≤ (c + 1) * x := by
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hdiv : (m : ℝ) / r ≤ m := div_le_self (by positivity) hr'
  apply (Real.sqrt_le_iff).mpr
  refine ⟨by positivity, ?_⟩
  have h := mul_le_mul_of_nonneg_right (show c + 1 ≤ (c + 1) ^ 2 by nlinarith) (sq_nonneg x)
  nlinarith [hdiv.trans hm]

theorem constantFamily_log_budget {x ell W C : ℝ} (hx : 16 ≤ x)
    (hellx : ell ≤ x) (hW : 0 < W) (hC : 0 < C) (hCx : C ≤ x)
    (hscale : W ≤ C * x ^ 2) :
    x * Real.log W + 2 * Real.log (1 / realSecurityError (ell + 6)) ≤
      (polynomialFamilyColumns constantFamilyColumnCoefficient x : ℝ) * Real.log (50 / 49) := by
  have hx0 : 0 < x := by linarith
  have hlogC := Real.log_le_log hC hCx
  have hlogW := Real.log_le_log hW hscale
  rw [Real.log_mul hC.ne' (by positivity : x ^ 2 ≠ 0), Real.log_pow] at hlogW
  norm_num at hlogW
  have hW' : Real.log W ≤ 3 * Real.log x := by linarith
  have hlogx : 4 * Real.log 2 ≤ Real.log x := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 16) hx
    have he : Real.log (16 : ℝ) = 4 * Real.log 2 := by
      rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.log_pow]
      norm_num
    rwa [he] at h
  have he := mul_le_mul_of_nonneg_left hlogx hx0.le
  have hδ : 2 * Real.log (1 / realSecurityError (ell + 6)) ≤ x * Real.log x := by
    rw [log_inv_realSecurityError]
    have h := mul_le_mul_of_nonneg_right (show 2 * (ell + 6) ≤ 4 * x by linarith)
      (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))
    nlinarith
  have h₁ := mul_le_mul_of_nonneg_left hW' hx0.le
  have h₂ := mul_le_mul_of_nonneg_right
    (polynomialFamilyColumns_lower constantFamilyColumnCoefficient x) log_fifty_fortyninths_pos.le
  have hc : constantFamilyColumnCoefficient * x * Real.log (2 * x) * Real.log (50 / 49) =
      5 * x * Real.log (2 * x) := by
    rw [mul_right_comm _ _ (Real.log (50 / 49)), mul_right_comm _ x (Real.log (50 / 49)),
      constantFamilyColumnCoefficient_mul]
  rw [hc] at h₂
  have hlog := Real.log_le_log hx0 (show x ≤ 2 * x by linarith)
  have h₃ := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 5 * x by positivity)
  nlinarith [mul_nonneg hx0.le (Real.log_nonneg (show 1 ≤ x by linarith))]

/-- The complete finite budget at width `sqrt d`, with absolute constants. -/
theorem constantFamily_parameters {d r : ℕ} (hd : 0 < d) (hr : 1 ≤ r)
    {ell : ℝ} (hell : constantFamilyThreshold ≤ ell)
    (hRlower : ell ≤ ((r * d : ℕ) : ℝ)) (hRupper : ((r * d : ℕ) : ℝ) ≤ 2 * ell) :
    let m := polynomialFamilyColumns constantFamilyColumnCoefficient ((r * d : ℕ) : ℝ)
    let H := constantColumnHeight (r * d) m (realSecurityError (ell + 6))
    1 ≤ ell ∧ r < m ∧
      ((r * d : ℕ) : ℝ) * Real.log (powerTwoConstantScale d r m (Real.sqrt d) ell) +
        2 * Real.log (1 / realSecurityError (ell + 6)) ≤ (m : ℝ) * Real.log (50 / 49) ∧
      640 * Real.sqrt (d * H) ≤ (640 * Real.sqrt 8) * Real.sqrt (d * ell) := by
  let c := constantFamilyColumnCoefficient
  let R := r * d
  let m := polynomialFamilyColumns c R
  let H := constantColumnHeight R m (realSecurityError (ell + 6))
  let C := 2560 * (c + 1)
  have hc : 0 < c := constantFamilyColumnCoefficient_pos
  have hC : 0 < C := by dsimp [C]; positivity
  change max 25 (max (Real.log (2 * (c + 1)) ^ 2) C) ≤ ell at hell
  obtain ⟨h25, hrest⟩ := max_le_iff.mp hell
  obtain ⟨hlogc, hCell⟩ := max_le_iff.mp hrest
  have hell1 : 1 ≤ ell := by linarith
  have hR1 : (1 : ℝ) ≤ R := hell1.trans hRlower
  have hRpos : (0 : ℝ) < R := by linarith
  have hrR : r ≤ R := by dsimp [R]; nlinarith
  have hRm : R < m := by exact_mod_cast constantFamilyColumns_gt hR1
  have hmr := hrR.trans_lt hRm
  have hm : 0 < m := lt_of_lt_of_le (by omega : 0 < r) hmr.le
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hr' : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hlog : Real.log (2 * (m : ℝ)) ≤ R :=
    polynomialFamilyColumns_log_le hc (h25.trans hRlower) (hlogc.trans hRlower)
  have hHupper : H ≤ 4 * R := constantFamily_height_le hm (by linarith) hRlower hlog
  have hHlower : (R : ℝ) ≤ H := constantColumnHeight_ge_rank hm (realSecurityError_pos _)
    ((real_constant_failureBudget_le hell1).trans (by norm_num))
  have hHpos : 0 < H := hRpos.trans_le hHlower
  have hmupper : (m : ℝ) ≤ (c + 1) * (R : ℝ) ^ 2 := polynomialFamilyColumns_upper hc.le hR1
  have hWeq : powerTwoConstantScale d r m (Real.sqrt d) ell = 640 * H * Real.sqrt ((m : ℝ) / r) := by
    simp only [powerTwoConstantScale, div_self (Real.sqrt_pos.mpr hd').ne', mul_one, H, R]
  have hWpos : 0 < powerTwoConstantScale d r m (Real.sqrt d) ell := by rw [hWeq]; positivity
  have hWupper : powerTwoConstantScale d r m (Real.sqrt d) ell ≤ C * (R : ℝ) ^ 2 := by
    rw [hWeq]
    calc
      _ ≤ 640 * (4 * R) * Real.sqrt ((m : ℝ) / r) := by gcongr
      _ ≤ 640 * (4 * R) * ((c + 1) * R) :=
        mul_le_mul_of_nonneg_left (constantFamily_sqrt_ratio_le hr hc hRpos.le hmupper) (by positivity)
      _ = C * (R : ℝ) ^ 2 := by dsimp [C]; ring
  have hbudget := constantFamily_log_budget (show 16 ≤ (R : ℝ) by linarith)
    hRlower hWpos hC (hCell.trans hRlower) hWupper
  have hH8 : H ≤ 8 * ell := by linarith
  have hroot := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hH8 hd'.le)
  rw [show (d : ℝ) * (8 * ell) = 8 * (d * ell) by ring,
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 8)] at hroot
  refine ⟨hell1, hmr, hbudget, ?_⟩
  nlinarith

end GeometricGaussianLHL
end

end ConstantWidthFamily

section PowerTwoPinned

/-!
## The numerical power-of-two pinned smoothing bounds

The two numerical variants of the smoothing-parameter pinning corollary refer to the actual Gaussian
matrix law and canonical kernel. The upper bound is compared with the projected-dual lower bound at
error `2^(-ell)` . The threshold `ell ≥ 28` is derived from the stated hypotheses, not added as an
assumption.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Module NumberField

namespace GeometricGaussianLHL

variable (K : Type*) [Field K] [NumberField K] {k r m : ℕ}
  [IsCyclotomicExtension {2 ^ (k + 1)} ℚ K] {ζ : K}

local instance pinnedPowerTwoEmbeddingsFintype : Fintype (K →+* ℂ) := inferInstance
local instance pinnedPowerTwoAmbientInner : InnerProductSpace ℝ (CanonicalAmbient K) := inferInstance
local instance pinnedPowerTwoSpaceInner : InnerProductSpace ℝ (canonicalSpace K) := inferInstance
local instance pinnedPowerTwoPowerInner (n : ℕ) : InnerProductSpace ℝ (CanonicalPower K n) := inferInstance

theorem powerTwoKernel_security_bounds (hζ : IsPrimitiveRoot ζ (2 ^ (k + 1)))
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) (hmr : r < m) {ell ε B : ℝ}
    (hε : 0 < ε) (hle : ε ≤ realSecurityError ell)
    (hη : smoothingParameter (canonicalKernel K X) ε ≤ B) :
    powerTwoSecurityLowerBound (2 ^ (k + 1)).totient ell ≤
        smoothingParameter (canonicalKernel K X) (realSecurityError ell) ∧
      smoothingParameter (canonicalKernel K X) (realSecurityError ell) ≤ B := by
  let b := cyclotomicIntegralBasis K hζ
  have hfg := canonicalLattice_subgroup_fg K b (canonicalKernel K X) (canonicalKernel_le_lattice K X)
  have hexists := exists_smoothAt_of_fg (canonicalKernel K X) hfg hε
  have hupper := (smoothingParameter_antitone_error_of_exists hexists hle).trans hη
  have hlower := canonicalKernel_security_smoothing_lower K b X hmr ell
  rw [(powerTwoBasis_constants K hζ).2.1] at hlower
  refine ⟨?_, hupper⟩
  simpa only [powerTwoSecurityLowerBound, one_div, div_inv_eq_mul, mul_comm] using hlower

/-- The polynomial-width numerical ratio in the smoothing-parameter pinning corollary. -/
theorem powerTwo_polynomial_pinned (hζ : IsPrimitiveRoot ζ (2 ^ (k + 1)))
    (hr : 1 ≤ r) (hmr : r < m) {ell s : ℝ} (hell : 1 ≤ ell) (hs : 0 < s)
    (hwidth : 8 * Real.sqrt ((2 ^ (k + 1)).totient * (r * (2 ^ (k + 1)).totient)) ≤ s)
    (hbudget : ((r * (2 ^ (k + 1)).totient : ℕ) : ℝ) *
      Real.log (powerTwoPolynomialScale (2 ^ (k + 1)).totient r m s ell) +
      2 * Real.log (1 / realSecurityError (ell + 4)) ≤ (m : ℝ) * Real.log (8 / 7))
    (hR : ((r * (2 ^ (k + 1)).totient : ℕ) : ℝ) = ell)
    (hsize : Real.log (2 * m) ≤ ell / 10) :
    let d := (2 ^ (k + 1)).totient
    let B := 64 * Real.sqrt (d * polynomialColumnHeight (r * d) m ell)
    let L := powerTwoSecurityLowerBound d ell
    ∃ G : Set (Matrix (Fin r) (Fin m) (𝓞 K)),
      ENNReal.ofReal (1 - 3 * realSecurityError (ell + 4)) ≤
        (numberFieldMatrixLaw K (cyclotomicIntegralBasis K hζ) r m s hs.ne').toOuterMeasure G ∧
      B / L ≤ pinnedRatioConstant 64 ∧ pinnedRatioConstant 64 < 225 ∧
      ∀ X ∈ G, Function.Surjective X.mulVec ∧
        L ≤ smoothingParameter (canonicalKernel K X) (realSecurityError ell) ∧
        smoothingParameter (canonicalKernel K X) (realSecurityError ell) ≤ B := by
  dsimp only
  let d := (2 ^ (k + 1)).totient
  let H := polynomialColumnHeight (r * d) m ell
  have hd : 0 < d := integralBasis_dimension_pos K (cyclotomicIntegralBasis K hζ)
  have hdreal : (0 : ℝ) < d := by exact_mod_cast hd
  have hm : 1 ≤ m := by omega
  have hRone : (1 : ℝ) ≤ (r * d : ℕ) := by exact_mod_cast Nat.mul_pos (by omega : 0 < r) hd
  have hHone : 1 ≤ H := hRone.trans (polynomialColumnHeight_ge_rank hm hell)
  have hsqrt : Real.sqrt d ≤ s := by
    have hprod : (d : ℝ) ≤ d * (r * d) := by
      have hh : (1 : ℝ) ≤ r * d := by simpa only [Nat.cast_mul] using hRone
      nlinarith
    have hroot := Real.sqrt_le_sqrt hprod
    nlinarith [Real.sqrt_nonneg ((d : ℝ) * (r * d))]
  have hW : 1 ≤ powerTwoPolynomialScale d r m s ell := by
    have h := powerTwoScale_ge_one hd hr hmr.le hsqrt hHone (by norm_num : (1 : ℝ) ≤ 64)
    convert h using 1
    dsimp [powerTwoPolynomialScale, H]
    ring
  have hell28 := pinned_column_condition_accuracy_ge (show (0 : ℝ) ≤ (r * d : ℕ) by positivity)
    hW hell (by norm_num : (4 : ℝ) ≤ 4)
    (by have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 8 / 7); linarith)
    hbudget hsize
  have hheight : H ≤ (27 / 10) * ell :=
    pinned_security_height_le (R := r * d) hm hell28 (by norm_num : (4 : ℝ) ≤ 6) hR hsize
  obtain ⟨G, hprob, hgood⟩ := powerTwo_polynomial_certificate K hζ hr hmr hell hs hwidth hbudget
  refine ⟨G, hprob, powerTwoPinned_ratio_bound hd (by linarith) (by linarith : 0 ≤ H)
    (by norm_num : (0 : ℝ) ≤ 64) hheight, pinnedRatioConstant_polynomial_lt, ?_⟩
  intro X hX
  have hε : 2 * realSecurityError (ell + 4) ≤ realSecurityError ell := by
    rw [realSecurityError_add]
    norm_num
    linarith [realSecurityError_pos ell]
  exact ⟨(hgood X hX).1, powerTwoKernel_security_bounds K hζ X hmr
    (mul_pos (by norm_num) (realSecurityError_pos _)) hε (hgood X hX).2⟩

/-- The constant-width numerical ratio in the smoothing-parameter pinning corollary. -/
theorem powerTwo_constantWidth_pinned (hζ : IsPrimitiveRoot ζ (2 ^ (k + 1)))
    (hr : 1 ≤ r) (hmr : r < m) {ell s : ℝ} (hell : 1 ≤ ell) (hs : 0 < s)
    (hwidth : Real.sqrt (2 ^ (k + 1)).totient ≤ s)
    (hbudget : ((r * (2 ^ (k + 1)).totient : ℕ) : ℝ) *
      Real.log (powerTwoConstantScale (2 ^ (k + 1)).totient r m s ell) +
      2 * Real.log (1 / realSecurityError (ell + 6)) ≤ (m : ℝ) * Real.log (50 / 49))
    (hR : ((r * (2 ^ (k + 1)).totient : ℕ) : ℝ) = ell)
    (hsize : Real.log (2 * m) ≤ ell / 10) :
    let d := (2 ^ (k + 1)).totient
    let B := 640 * Real.sqrt (d * constantColumnHeight (r * d) m (realSecurityError (ell + 6)))
    let L := powerTwoSecurityLowerBound d ell
    ∃ G : Set (Matrix (Fin r) (Fin m) (𝓞 K)),
      ENNReal.ofReal (1 - 3 * realSecurityError (ell + 6)) ≤
        (numberFieldMatrixLaw K (cyclotomicIntegralBasis K hζ) r m s hs.ne').toOuterMeasure G ∧
      B / L ≤ pinnedRatioConstant 640 ∧ pinnedRatioConstant 640 < 2250 ∧
      ∀ X ∈ G, Function.Surjective X.mulVec ∧
        L ≤ smoothingParameter (canonicalKernel K X) (realSecurityError ell) ∧
        smoothingParameter (canonicalKernel K X) (realSecurityError ell) ≤ B := by
  dsimp only
  let d := (2 ^ (k + 1)).totient
  let H := constantColumnHeight (r * d) m (realSecurityError (ell + 6))
  have hd : 0 < d := integralBasis_dimension_pos K (cyclotomicIntegralBasis K hζ)
  have hm : 1 ≤ m := by omega
  have hRone : (1 : ℝ) ≤ (r * d : ℕ) := by exact_mod_cast Nat.mul_pos (by omega : 0 < r) hd
  have hHone : 1 ≤ H := hRone.trans (constantColumnHeight_ge_rank hm (realSecurityError_pos _)
    (by have h := real_constant_failureBudget_le hell; linarith))
  have hW : 1 ≤ powerTwoConstantScale d r m s ell :=
    powerTwoScale_ge_one hd hr hmr.le hwidth hHone (by norm_num : (1 : ℝ) ≤ 640)
  have hell28 := pinned_column_condition_accuracy_ge (show (0 : ℝ) ≤ (r * d : ℕ) by positivity)
    hW hell (by norm_num : (4 : ℝ) ≤ 6)
    (by have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 50 / 49); linarith)
    hbudget hsize
  have hheight : H ≤ (27 / 10) * ell :=
    pinned_security_height_le (R := r * d) hm hell28 (by norm_num : (6 : ℝ) ≤ 6) hR hsize
  obtain ⟨G, hprob, hgood⟩ := numberField_constantWidth_certificate K hζ hr hmr hell hs hwidth hbudget
  refine ⟨G, hprob, powerTwoPinned_ratio_bound hd (by linarith) (by linarith : 0 ≤ H)
    (by norm_num : (0 : ℝ) ≤ 640) hheight, pinnedRatioConstant_constant_lt, ?_⟩
  intro X hX
  have hε : 2 * realSecurityError (ell + 6) ≤ realSecurityError ell := by
    rw [realSecurityError_add]
    norm_num
    linarith [realSecurityError_pos ell]
  exact ⟨(hgood X hX).1, powerTwoKernel_security_bounds K hζ X hmr
    (mul_pos (by norm_num) (realSecurityError_pos _)) hε (hgood X hX).2.2.1⟩

end GeometricGaussianLHL
end

end PowerTwoPinned

section ConstantWidthAsymptotic

/-!
## Constant-width asymptotics uniformly in the field degree

The constant-width asymptotic parameter discussion at coefficient width one, for the actual Gaussian
matrix law. The same absolute column coefficient, smoothing constant and threshold work for every
power-of-two cyclotomic field and every row count with `λ ≤ dr ≤ 2λ` .
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Module NumberField
namespace GeometricGaussianLHL

theorem constant_errorExponent_eq_one {ell : ℝ} (hell : 1 ≤ ell) :
    errorExponent (2 * realSecurityError (ell + 6)) (realSecurityError ell) = 1 := by
  have hδ := real_constant_failureBudget_le hell
  have hδpos := realSecurityError_pos (ell + 6)
  have hpos := realSecurityError_pos ell
  apply errorExponent_eq_one_of_le (by positivity) (by linarith)
  rw [realSecurityError_add]
  norm_num
  linarith

/-- The constants and threshold precede all field and dimension quantifiers. -/
theorem numberField_constantWidth_uniform_asymptotic :
    ∃ cm C ell₀ : ℝ, 0 < cm ∧ 0 < C ∧ 0 < ell₀ ∧
      ∀ (K : Type*) [Field K] [NumberField K] (k : ℕ)
        [IsCyclotomicExtension {2 ^ (k + 1)} ℚ K] (ζ : K)
        (hζ : IsPrimitiveRoot ζ (2 ^ (k + 1))) (r : ℕ) (_hr : 1 ≤ r)
        (ell : ℝ), ell₀ ≤ ell →
        let d := (2 ^ (k + 1)).totient
        ell ≤ ((r * d : ℕ) : ℝ) → ((r * d : ℕ) : ℝ) ≤ 2 * ell →
        let b := cyclotomicIntegralBasis K hζ
        let m := polynomialFamilyColumns cm ((r * d : ℕ) : ℝ)
        let δ := realSecurityError (ell + 6)
        r < m ∧ ∃ hs : 0 < Real.sqrt d,
          ∃ G : Set (Matrix (Fin r) (Fin m) (𝓞 K)),
            ENNReal.ofReal (1 - 3 * δ) ≤
              (numberFieldMatrixLaw K b r m (Real.sqrt d) hs.ne').toOuterMeasure G ∧
            ∀ X ∈ G,
              Function.Surjective X.mulVec ∧
              smoothingParameter (canonicalKernel K X) (2 * δ) ≤ C * Real.sqrt (d * ell) ∧
              smoothingParameter (canonicalKernel K X) (realSecurityError ell) ≤ C * Real.sqrt (d * ell) := by
  refine ⟨constantFamilyColumnCoefficient, 640 * Real.sqrt 8, constantFamilyThreshold,
    constantFamilyColumnCoefficient_pos, by positivity, ?_, ?_⟩
  · exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 25) (le_max_left _ _)
  · intro K _ _ k _ ζ hζ r hr ell hell
    dsimp only
    let d := (2 ^ (k + 1)).totient
    let b := cyclotomicIntegralBasis K hζ
    intro hRlower hRupper
    let m := polynomialFamilyColumns constantFamilyColumnCoefficient ((r * d : ℕ) : ℝ)
    have hd : 0 < d := integralBasis_dimension_pos K b
    obtain ⟨hell1, hmr, hbudget, ht⟩ := constantFamily_parameters hd hr hell hRlower hRupper
    have hs : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
    obtain ⟨G, hprob, hgood⟩ := numberField_constantWidth_certificate K hζ hr hmr hell1 hs le_rfl hbudget
    refine ⟨hmr, hs, G, hprob, ?_⟩
    intro X hX
    obtain ⟨himage, _, hsmooth, _, hall⟩ := hgood X hX
    have hlarge := hall (realSecurityError ell) (realSecurityError_pos ell)
    rw [constant_errorExponent_eq_one hell1, Real.sqrt_one, mul_one] at hlarge
    exact ⟨himage, hsmooth.trans ht, hlarge.trans ht⟩

end GeometricGaussianLHL
end

end ConstantWidthAsymptotic
