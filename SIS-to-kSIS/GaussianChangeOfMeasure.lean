import GeometricGaussianLHL.GaussianPoisson

/-!
# Gaussian change of measure for the shifted-hint game

The direction needed by the reduction compares a centered lattice Gaussian to
a shifted one on the same lattice. The partition maximum at the origin gives
a direct second-moment bound without a smoothing assumption.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open GeometricGaussianLHL MeasureTheory

namespace SISToKSIS

def renyiTwo {α : Type*} (p q : PMF α) : ℝ :=
  ∑' x, (p x).toReal ^ 2 / (q x).toReal

theorem renyiTwo_map_equiv {α β : Type*} (p q : PMF α) (e : α ≃ β) :
    renyiTwo (p.map e) (q.map e) = renyiTwo p q := by
  unfold renyiTwo
  rw [← e.tsum_eq]
  simp only [pmf_map_equiv_apply]

theorem summable_finite_product_real {α : Type*} {k : ℕ} (f : Fin k → α → ℝ)
    (hf : ∀ i x, 0 ≤ f i x) (hs : ∀ i, Summable (f i)) :
    Summable (fun z : Fin k → α => ∏ i, f i (z i)) := by
  have hfinite : (∑' z : Fin k → α, ∏ i, ENNReal.ofReal (f i (z i))) ≠ ⊤ := by
    rw [tsum_finite_product k (fun i x => ENNReal.ofReal (f i x))]
    exact ENNReal.prod_ne_top (fun i _ => (hs i).tsum_ofReal_ne_top)
  have h := ENNReal.summable_toReal hfinite
  simp_rw [ENNReal.toReal_prod, ENNReal.toReal_ofReal (hf _ _)] at h
  exact h

theorem tsum_finite_product_real {α : Type*} {k : ℕ} (f : Fin k → α → ℝ)
    (hf : ∀ i x, 0 ≤ f i x) (hs : ∀ i, Summable (f i)) :
    (∑' z : Fin k → α, ∏ i, f i (z i)) = ∏ i, ∑' x, f i x := by
  have h := congrArg ENNReal.toReal (tsum_finite_product k (fun i x => ENNReal.ofReal (f i x)))
  rw [ENNReal.tsum_toReal_eq (fun z => ENNReal.prod_ne_top (fun _ _ => ENNReal.ofReal_ne_top))] at h
  simp_rw [ENNReal.toReal_prod, ENNReal.toReal_ofReal (hf _ _)] at h
  simp_rw [← ENNReal.ofReal_tsum_of_nonneg (hf _) (hs _),
    ENNReal.toReal_ofReal (tsum_nonneg (hf _))] at h
  exact h

theorem renyiTwo_independentProduct {α : Type*} {k : ℕ} (p q : Fin k → PMF α)
    (hs : ∀ i, Summable (fun x => (p i x).toReal ^ 2 / (q i x).toReal)) :
    renyiTwo (independentProduct p) (independentProduct q) = ∏ i, renyiTwo (p i) (q i) := by
  unfold renyiTwo
  simp_rw [independentProduct_apply, ENNReal.toReal_prod, ← Finset.prod_pow,
    ← Finset.prod_div_distrib]
  exact tsum_finite_product_real _ (fun _ _ => div_nonneg (sq_nonneg _) ENNReal.toReal_nonneg) hs

theorem renyiTwo_independentProduct_summable {α : Type*} {k : ℕ} (p q : Fin k → PMF α)
    (hs : ∀ i, Summable (fun x => (p i x).toReal ^ 2 / (q i x).toReal)) :
    Summable (fun z => (independentProduct p z).toReal ^ 2 /
      (independentProduct q z).toReal) := by
  simp_rw [independentProduct_apply, ENNReal.toReal_prod, ← Finset.prod_pow,
    ← Finset.prod_div_distrib]
  exact summable_finite_product_real (fun i x => (p i x).toReal ^ 2 / (q i x).toReal)
    (fun _ _ => div_nonneg (sq_nonneg _) ENNReal.toReal_nonneg) hs

/-- The event form of the order-two change-of-measure inequality. -/
theorem event_sq_le_renyiTwo {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (p q : PMF α)
    (hq : ∀ x, 0 < (q x).toReal)
    (hs : Summable (fun x => (p x).toReal ^ 2 / (q x).toReal)) (E : Set α) :
    p.toMeasure.real E ^ 2 ≤ renyiTwo p q * q.toMeasure.real E := by
  let f := fun x => (p x).toReal / (q x).toReal
  have hfirst : (fun x => (q x).toReal * f x) = (fun x => (p x).toReal) := by
    funext x
    dsimp [f]
    field_simp [(hq x).ne']
  have hsecond : (fun x => (q x).toReal * f x ^ 2) =
      (fun x => (p x).toReal ^ 2 / (q x).toReal) := by
    funext x
    dsimp [f]
    field_simp [(hq x).ne']
  have h := pmf_event_moment_sq_le q f E
    (fun x => div_nonneg ENNReal.toReal_nonneg (hq x).le)
    (hfirst ▸ pmf_summable_toReal p) (hsecond ▸ hs)
  rw [hfirst, hsecond, ← pmf_measureReal_eq_tsum] at h
  exact h

theorem event_lower_bound_of_renyiTwo {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (p q : PMF α)
    (hq : ∀ x, 0 < (q x).toReal)
    (hs : Summable (fun x => (p x).toReal ^ 2 / (q x).toReal))
    {C : ℝ} (hC : 0 < C) (hbound : renyiTwo p q ≤ C) (E : Set α) :
    p.toMeasure.real E ^ 2 / C ≤ q.toMeasure.real E := by
  apply (div_le_iff₀ hC).mpr
  have h := (event_sq_le_renyiTwo p q hq hs E).trans
    (mul_le_mul_of_nonneg_right hbound measureReal_nonneg)
  simpa only [mul_comm] using h

section Gaussian

variable {n : ℕ}

theorem gaussian_ratio_weight (S : Euclidean n ≃L[ℝ] Euclidean n)
    (c : Euclidean n) (z : Coeff n) :
    ellipsoidWeight S 0 z ^ 2 / ellipsoidWeight S c z =
      Real.exp (2 * Real.pi * ‖S.symm c‖ ^ 2) * ellipsoidWeight S (-c) z := by
  simp only [ellipsoidWeight, gaussianWeight, sub_zero, map_sub, map_neg,
    one_pow]
  rw [← Real.exp_nat_mul, ← Real.exp_sub, ← Real.exp_add]
  congr 1
  rw [norm_sub_sq_real, sub_neg_eq_add, norm_add_sq_real]
  ring

theorem gaussian_ratio_density (S : Euclidean n ≃L[ℝ] Euclidean n)
    (c : Euclidean n) (z : Coeff n) :
    (ellipsoidalGaussian S 0 z).toReal ^ 2 / (ellipsoidalGaussian S c z).toReal =
      (Real.exp (2 * Real.pi * ‖S.symm c‖ ^ 2) *
        (ellipsoidPartition S c / ellipsoidPartition S 0 ^ 2)) *
        ellipsoidWeight S (-c) z := by
  rw [ellipsoidalGaussian_toReal, ellipsoidalGaussian_toReal]
  have h := gaussian_ratio_weight S c z
  have hZ := (ellipsoidPartition_pos S 0).ne'
  have hZc := (ellipsoidPartition_pos S c).ne'
  have hw := (ellipsoidWeight_pos S c z).ne'
  field_simp at h ⊢
  nlinarith [h]

theorem gaussian_renyiTwo_summable (S : Euclidean n ≃L[ℝ] Euclidean n)
    (c : Euclidean n) : Summable (fun z : Coeff n =>
      (ellipsoidalGaussian S 0 z).toReal ^ 2 / (ellipsoidalGaussian S c z).toReal) := by
  simp_rw [gaussian_ratio_density]
  exact (summable_ellipsoidWeight S (-c)).mul_left _

theorem gaussian_renyiTwo_eq (S : Euclidean n ≃L[ℝ] Euclidean n)
    (c : Euclidean n) :
    renyiTwo (ellipsoidalGaussian S 0) (ellipsoidalGaussian S c) =
      Real.exp (2 * Real.pi * ‖S.symm c‖ ^ 2) *
        (ellipsoidPartition S c * ellipsoidPartition S (-c) /
          ellipsoidPartition S 0 ^ 2) := by
  unfold renyiTwo
  simp_rw [gaussian_ratio_density]
  rw [tsum_mul_left]
  change _ * ellipsoidPartition S (-c) = _
  ring

/-- A sharper bound in the required direction than the smoothing-based bound. -/
theorem gaussian_renyiTwo_le (S : Euclidean n ≃L[ℝ] Euclidean n)
    (c : Euclidean n) :
    renyiTwo (ellipsoidalGaussian S 0) (ellipsoidalGaussian S c) ≤
      Real.exp (2 * Real.pi * ‖S.symm c‖ ^ 2) := by
  rw [gaussian_renyiTwo_eq]
  apply mul_le_of_le_one_right (Real.exp_pos _).le
  apply (div_le_one (sq_pos_of_pos (ellipsoidPartition_pos S 0))).mpr
  simpa only [pow_two] using mul_le_mul (ellipsoidPartition_le_zero S c)
    (ellipsoidPartition_le_zero S (-c)) (ellipsoidPartition_pos S (-c)).le
    (ellipsoidPartition_pos S 0).le

theorem shifted_gaussian_event_lower_bound (S : Euclidean n ≃L[ℝ] Euclidean n)
    (c : Euclidean n) (E : Set (Coeff n)) :
    (ellipsoidalGaussian S 0).toMeasure.real E ^ 2 /
      Real.exp (2 * Real.pi * ‖S.symm c‖ ^ 2) ≤
        (ellipsoidalGaussian S c).toMeasure.real E :=
  event_lower_bound_of_renyiTwo _ _ (ellipsoidalGaussian_toReal_pos S c)
    (gaussian_renyiTwo_summable S c) (Real.exp_pos _) (gaussian_renyiTwo_le S c) E

end Gaussian

section Lattices

variable {n : ℕ} (L : Submodule ℤ (Euclidean n))
  [DiscreteTopology L] [IsZLattice ℝ L]

/-- A Gaussian supported on `L`, with an arbitrary ambient center. The center
need not belong to `L`, which is essential for the shifted k-SIS game. -/
def shiftedLatticeGaussian (S : Euclidean n ≃L[ℝ] Euclidean n) (c : Euclidean n) : PMF L :=
  (ellipsoidalGaussian (latticeCoefficientShape L S) ((fullLatticeRealEquiv L).symm c)).map
    (fullLatticeCoordinateEquiv L).toEquiv

theorem shiftedLatticeGaussian_coordinates (S : Euclidean n ≃L[ℝ] Euclidean n)
    (c : Euclidean n) (z : Coeff n) :
    shiftedLatticeGaussian L S c (fullLatticeCoordinateEquiv L z) =
      ellipsoidalGaussian (latticeCoefficientShape L S) ((fullLatticeRealEquiv L).symm c) z :=
  pmf_map_equiv_apply _ (fullLatticeCoordinateEquiv L).toEquiv z

theorem shiftedLatticeGaussian_density (S : Euclidean n ≃L[ℝ] Euclidean n)
    (c : Euclidean n) (z : L) :
    (shiftedLatticeGaussian L S c z).toReal =
      latticeShiftedWeight L S c z / latticeShiftedPartition L S c := by
  obtain ⟨v, rfl⟩ := (fullLatticeCoordinateEquiv L).surjective z
  rw [shiftedLatticeGaussian_coordinates, ellipsoidalGaussian_toReal,
    latticeShiftedWeight_coordinates, latticeShiftedPartition_coordinates]

theorem shiftedLatticeGaussian_positive (S : Euclidean n ≃L[ℝ] Euclidean n)
    (c : Euclidean n) (z : L) : 0 < (shiftedLatticeGaussian L S c z).toReal := by
  obtain ⟨v, rfl⟩ := (fullLatticeCoordinateEquiv L).surjective z
  rw [shiftedLatticeGaussian_coordinates]
  exact ellipsoidalGaussian_toReal_pos _ _ _

theorem shiftedLatticeGaussian_renyiTwo_summable
    (S : Euclidean n ≃L[ℝ] Euclidean n) (c : Euclidean n) :
    Summable (fun z : L => (shiftedLatticeGaussian L S 0 z).toReal ^ 2 /
      (shiftedLatticeGaussian L S c z).toReal) := by
  apply (fullLatticeCoordinateEquiv L).toEquiv.summable_iff.mp
  change Summable (fun z : Coeff n =>
    (shiftedLatticeGaussian L S 0 (fullLatticeCoordinateEquiv L z)).toReal ^ 2 /
      (shiftedLatticeGaussian L S c (fullLatticeCoordinateEquiv L z)).toReal)
  simp_rw [shiftedLatticeGaussian_coordinates L S 0,
    shiftedLatticeGaussian_coordinates L S c, map_zero]
  exact gaussian_renyiTwo_summable _ _

/-- The centered-to-shifted bound holds on every full lattice, at every width. -/
theorem shiftedLatticeGaussian_renyiTwo_le
    (S : Euclidean n ≃L[ℝ] Euclidean n) (c : Euclidean n) :
    renyiTwo (shiftedLatticeGaussian L S 0) (shiftedLatticeGaussian L S c) ≤
      Real.exp (2 * Real.pi * ‖S.symm c‖ ^ 2) := by
  unfold shiftedLatticeGaussian
  rw [renyiTwo_map_equiv, map_zero]
  have h := gaussian_renyiTwo_le (latticeCoefficientShape L S)
    ((fullLatticeRealEquiv L).symm c)
  have he : (latticeCoefficientShape L S).symm ((fullLatticeRealEquiv L).symm c) =
      S.symm c := by
    change S.symm (fullLatticeRealEquiv L ((fullLatticeRealEquiv L).symm c)) = S.symm c
    rw [ContinuousLinearEquiv.apply_symm_apply]
  simpa only [he] using h

theorem shifted_lattice_event_lower_bound
    (S : Euclidean n ≃L[ℝ] Euclidean n) (c : Euclidean n) (E : Set L) :
    (shiftedLatticeGaussian L S 0).toMeasure.real E ^ 2 /
      Real.exp (2 * Real.pi * ‖S.symm c‖ ^ 2) ≤
        (shiftedLatticeGaussian L S c).toMeasure.real E :=
  event_lower_bound_of_renyiTwo _ _ (shiftedLatticeGaussian_positive L S c)
    (shiftedLatticeGaussian_renyiTwo_summable L S c) (Real.exp_pos _)
    (shiftedLatticeGaussian_renyiTwo_le L S c) E

end Lattices

end SISToKSIS
