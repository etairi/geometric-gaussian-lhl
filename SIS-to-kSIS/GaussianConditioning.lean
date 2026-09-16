import «SIS-to-kSIS».GaussianChangeOfMeasure
import «SIS-to-kSIS».ReverseSampling

/-!
# Gaussian conditioning on a full sublattice

Conditioning an ambient lattice Gaussian to a full sublattice gives exactly
the Gaussian on that sublattice. The normalizing probability is the ratio of
the actual partition sums, including for centers outside either lattice.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open GeometricGaussianLHL MeasureTheory

namespace SISToKSIS

theorem independentProduct_event_support {α : Type*} {k : ℕ}
    (p : Fin k → PMF α) (E : Fin k → Set α)
    (hp : ∀ j, ∃ x ∈ E j, x ∈ (p j).support) :
    ∃ z ∈ {z : Fin k → α | ∀ j, z j ∈ E j}, z ∈ (independentProduct p).support := by
  classical
  refine ⟨fun j => (hp j).choose, fun j => (hp j).choose_spec.1, ?_⟩
  rw [PMF.mem_support_iff, independentProduct_apply]
  exact Finset.prod_ne_zero_iff.mpr
    (fun j _ => (PMF.mem_support_iff (p j) _).mp (hp j).choose_spec.2)

/-- Coordinatewise conditioning preserves the independence of the columns. -/
theorem independentProduct_filter {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] {k : ℕ} (p : Fin k → PMF α) (E : Fin k → Set α)
    (hp : ∀ j, ∃ x ∈ E j, x ∈ (p j).support) :
    (independentProduct p).filter {z | ∀ j, z j ∈ E j}
      (independentProduct_event_support p E hp) =
        independentProduct (fun j => (p j).filter (E j) (hp j)) := by
  classical
  ext z
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [filteredPMF_toReal]
  simp only [Measure.real, independentProduct_event_all, independentProduct_apply,
    ENNReal.toReal_prod, filteredPMF_toReal, Finset.prod_div_distrib]
  congr 1
  by_cases hz : ∀ j, z j ∈ E j
  · rw [Set.indicator_of_mem (show z ∈ {z | ∀ j, z j ∈ E j} from hz)]
    simp only [Set.indicator_of_mem (hz _), independentProduct_apply, ENNReal.toReal_prod]
  · rw [Set.indicator_of_notMem (show z ∉ {z | ∀ j, z j ∈ E j} from hz)]
    obtain ⟨j, hj⟩ := not_forall.mp hz
    exact (Finset.prod_eq_zero (Finset.mem_univ j) (Set.indicator_of_notMem hj _)).symm

variable {n : ℕ} (L N : Submodule ℤ (Euclidean n))
  [DiscreteTopology L] [IsZLattice ℝ L] [DiscreteTopology N] [IsZLattice ℝ N]

theorem latticeShiftedPartition_pos (S : Euclidean n ≃L[ℝ] Euclidean n)
    (c : Euclidean n) : 0 < latticeShiftedPartition L S c := by
  rw [latticeShiftedPartition_coordinates]
  exact ellipsoidPartition_pos _ _

def sublatticeEvent : Set L := {x | (x : Euclidean n) ∈ N}

omit [DiscreteTopology N] [IsZLattice ℝ N] in
theorem sublatticeEvent_gaussian_support (S : Euclidean n ≃L[ℝ] Euclidean n)
    (c : Euclidean n) :
    ∃ x ∈ sublatticeEvent L N, x ∈ (shiftedLatticeGaussian L S c).support := by
  refine ⟨0, N.zero_mem, ?_⟩
  rw [PMF.mem_support_iff]
  intro hz
  have hpos := shiftedLatticeGaussian_positive L S c 0
  simp only [hz, ENNReal.toReal_zero, lt_self_iff_false] at hpos

theorem sublatticeGaussian_indicator (hNL : N ≤ L)
    (S : Euclidean n ≃L[ℝ] Euclidean n) (c : Euclidean n) (x : L) :
    (sublatticeEvent L N).indicator (fun y => (shiftedLatticeGaussian L S c y).toReal) x =
      (latticeShiftedPartition N S c / latticeShiftedPartition L S c) *
        ((shiftedLatticeGaussian N S c).map (Submodule.inclusion hNL) x).toReal := by
  classical
  by_cases hx : x ∈ sublatticeEvent L N
  · let y : N := ⟨x, hx⟩
    have hy : Submodule.inclusion hNL y = x := rfl
    have hinj : Function.Injective (Submodule.inclusion hNL) := by
      intro u v h
      exact Subtype.ext (congrArg (fun z : L => (z : Euclidean n)) h)
    have hm := congrArg ENNReal.toReal
      (pmf_map_injective_apply (shiftedLatticeGaussian N S c) (Submodule.inclusion hNL) hinj y)
    rw [hy] at hm
    have hw : latticeShiftedWeight N S c y = latticeShiftedWeight L S c x := rfl
    rw [Set.indicator_of_mem hx, hm, shiftedLatticeGaussian_density,
      shiftedLatticeGaussian_density, hw]
    field_simp [(latticeShiftedPartition_pos L S c).ne',
      (latticeShiftedPartition_pos N S c).ne']
  · have hz : (shiftedLatticeGaussian N S c).map (Submodule.inclusion hNL) x = 0 := by
      apply pmf_map_zero_of_not_range
      intro y hy
      apply hx
      have he : (y : Euclidean n) = (x : Euclidean n) := congrArg Subtype.val hy
      change (x : Euclidean n) ∈ N
      exact he ▸ y.2
    simp only [Set.indicator_of_notMem hx, hz, ENNReal.toReal_zero, mul_zero]

theorem sublatticeGaussian_probability (hNL : N ≤ L)
    (S : Euclidean n ≃L[ℝ] Euclidean n) (c : Euclidean n) :
    (shiftedLatticeGaussian L S c).toMeasure.real (sublatticeEvent L N) =
      latticeShiftedPartition N S c / latticeShiftedPartition L S c := by
  rw [pmf_measureReal_eq_tsum]
  simp_rw [sublatticeGaussian_indicator L N hNL S c]
  rw [tsum_mul_left, pmf_tsum_toReal, mul_one]

theorem shiftedLatticeGaussian_condition (hNL : N ≤ L)
    (S : Euclidean n ≃L[ℝ] Euclidean n) (c : Euclidean n) :
    (shiftedLatticeGaussian L S c).filter (sublatticeEvent L N)
      (sublatticeEvent_gaussian_support L N S c) =
        (shiftedLatticeGaussian N S c).map (Submodule.inclusion hNL) :=
  filteredPMF_eq_of_indicator _ _ _ (sublatticeEvent_gaussian_support L N S c)
    (div_pos (latticeShiftedPartition_pos N S c) (latticeShiftedPartition_pos L S c))
    (sublatticeGaussian_indicator L N hNL S c)

/-- All independent Gaussian columns conditioned on the sublattice are exactly
independent sublattice Gaussians with their original ambient centers. -/
theorem shiftedLatticeGaussian_columns_condition {k : ℕ} (hNL : N ≤ L)
    (S : Euclidean n ≃L[ℝ] Euclidean n) (centers : Fin k → Euclidean n) :
    (independentProduct (fun j => shiftedLatticeGaussian L S (centers j))).filter
      {z | ∀ j, z j ∈ sublatticeEvent L N}
      (independentProduct_event_support _ _
        (fun j => sublatticeEvent_gaussian_support L N S (centers j))) =
      (independentProduct (fun j => shiftedLatticeGaussian N S (centers j))).map
        (fun z j => Submodule.inclusion hNL (z j)) := by
  rw [independentProduct_filter _ (fun _ => sublatticeEvent L N)
    (fun j => sublatticeEvent_gaussian_support L N S (centers j))]
  simp_rw [shiftedLatticeGaussian_condition L N hNL]
  exact (independentProduct_map _ (fun _ => Submodule.inclusion hNL)).symm

end SISToKSIS
