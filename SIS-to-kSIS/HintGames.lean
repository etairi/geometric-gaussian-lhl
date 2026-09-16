import «SIS-to-kSIS».AdversaryChangeOfMeasure
import «SIS-to-kSIS».ModularLattices

/-!
# Gaussian hints and the shifted adversary game

Independent hints are sampled on the actual full lattice. The shift centers
are ambient vectors and need not satisfy the modular kernel equation.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open GeometricGaussianLHL MeasureTheory

namespace SISToKSIS

variable {n k : ℕ} (L : Submodule ℤ (Euclidean n))
  [DiscreteTopology L] [IsZLattice ℝ L]

def latticeHintLaw (S : Euclidean n ≃L[ℝ] Euclidean n)
    (centers : Fin k → Euclidean n) : PMF (Fin k → L) :=
  independentProduct (fun j => shiftedLatticeGaussian L S (centers j))

def shiftEnergy (S : Euclidean n ≃L[ℝ] Euclidean n)
    (centers : Fin k → Euclidean n) : ℝ :=
  ∑ j, ‖S.symm (centers j)‖ ^ 2

theorem shiftEnergy_nonneg (S : Euclidean n ≃L[ℝ] Euclidean n)
    (centers : Fin k → Euclidean n) : 0 ≤ shiftEnergy S centers :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem latticeHintLaw_positive (S : Euclidean n ≃L[ℝ] Euclidean n)
    (centers : Fin k → Euclidean n) (z : Fin k → L) :
    0 < (latticeHintLaw L S centers z).toReal := by
  simp only [latticeHintLaw, independentProduct_apply, ENNReal.toReal_prod]
  exact Finset.prod_pos (fun j _ => shiftedLatticeGaussian_positive L S (centers j) (z j))

theorem latticeHintLaw_renyiTwo_summable (S : Euclidean n ≃L[ℝ] Euclidean n)
    (centers : Fin k → Euclidean n) :
    Summable (fun z => (latticeHintLaw L S (fun _ => 0) z).toReal ^ 2 /
      (latticeHintLaw L S centers z).toReal) :=
  renyiTwo_independentProduct_summable _ _
    (fun j => shiftedLatticeGaussian_renyiTwo_summable L S (centers j))

/-- Tensorization charges precisely the sum of the squared normalized shifts. -/
theorem latticeHintLaw_renyiTwo_le (S : Euclidean n ≃L[ℝ] Euclidean n)
    (centers : Fin k → Euclidean n) :
    renyiTwo (latticeHintLaw L S (fun _ => 0)) (latticeHintLaw L S centers) ≤
      Real.exp (2 * Real.pi * shiftEnergy S centers) := by
  unfold latticeHintLaw
  rw [renyiTwo_independentProduct _ _
    (fun j => shiftedLatticeGaussian_renyiTwo_summable L S (centers j))]
  calc
    _ ≤ ∏ j, Real.exp (2 * Real.pi * ‖S.symm (centers j)‖ ^ 2) := by
      apply Finset.prod_le_prod
      · intro j _
        exact tsum_nonneg (fun _ => div_nonneg (sq_nonneg _) ENNReal.toReal_nonneg)
      · intro j _
        exact shiftedLatticeGaussian_renyiTwo_le L S (centers j)
    _ = _ := by rw [← Real.exp_sum]; congr 1; simp [shiftEnergy, Finset.mul_sum]

theorem latticeHintLaw_event_lower_bound (S : Euclidean n ≃L[ℝ] Euclidean n)
    (centers : Fin k → Euclidean n) (E : Set (Fin k → L)) :
    (latticeHintLaw L S (fun _ => 0)).toMeasure.real E ^ 2 /
      Real.exp (2 * Real.pi * shiftEnergy S centers) ≤
        (latticeHintLaw L S centers).toMeasure.real E :=
  event_lower_bound_of_renyiTwo _ _ (latticeHintLaw_positive L S centers)
    (latticeHintLaw_renyiTwo_summable L S centers) (Real.exp_pos _)
    (latticeHintLaw_renyiTwo_le L S centers) E

/-- The shifted-game comparison holds for every randomized adversary. -/
theorem shifted_hint_adversary_bound {β : Type*} [MeasurableSpace β]
    [MeasurableSingletonClass β] (S : Euclidean n ≃L[ℝ] Euclidean n)
    (centers : Fin k → Euclidean n) (adversary : (Fin k → L) → PMF β)
    (wins : (Fin k → L) → β → Prop) :
    successProbability (latticeHintLaw L S (fun _ => 0)) adversary wins ^ 2 /
      Real.exp (2 * Real.pi * shiftEnergy S centers) ≤
        successProbability (latticeHintLaw L S centers) adversary wins :=
  successProbability_lower_bound_of_renyiTwo _ _ adversary wins
    (fun z hz => False.elim ((latticeHintLaw_positive L S centers z).ne' hz))
    (latticeHintLaw_renyiTwo_summable L S centers) (Real.exp_pos _)
    (latticeHintLaw_renyiTwo_le L S centers)

theorem shiftEnergy_le_of_inverse_bound (S : Euclidean n ≃L[ℝ] Euclidean n)
    (centers : Fin k → Euclidean n) {B : ℝ}
    (hB : ∀ j, ‖S.symm (centers j)‖ ^ 2 ≤ B) : shiftEnergy S centers ≤ k * B := by
  simpa [shiftEnergy] using Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hB j)

theorem latticeHintLaw_renyiTwo_le_constant (S : Euclidean n ≃L[ℝ] Euclidean n)
    (centers : Fin k → Euclidean n) (h : shiftEnergy S centers ≤ 1) :
    renyiTwo (latticeHintLaw L S (fun _ => 0)) (latticeHintLaw L S centers) ≤
      Real.exp (2 * Real.pi) := by
  apply (latticeHintLaw_renyiTwo_le L S centers).trans
  apply Real.exp_le_exp.mpr
  simpa using mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ 2 * Real.pi)

theorem shifted_hint_adversary_bound_constant {β : Type*} [MeasurableSpace β]
    [MeasurableSingletonClass β] (S : Euclidean n ≃L[ℝ] Euclidean n)
    (centers : Fin k → Euclidean n) (henergy : shiftEnergy S centers ≤ 1)
    (adversary : (Fin k → L) → PMF β) (wins : (Fin k → L) → β → Prop) :
    successProbability (latticeHintLaw L S (fun _ => 0)) adversary wins ^ 2 /
      Real.exp (2 * Real.pi) ≤
        successProbability (latticeHintLaw L S centers) adversary wins :=
  successProbability_lower_bound_of_renyiTwo _ _ adversary wins
    (fun z hz => False.elim ((latticeHintLaw_positive L S centers z).ne' hz))
    (latticeHintLaw_renyiTwo_summable L S centers) (Real.exp_pos _)
    (latticeHintLaw_renyiTwo_le_constant L S centers henergy)

section NumberFields

open Module NumberField

variable (K : Type*) [Field K] [NumberField K] {d m r : ℕ}

local instance hintGamesMatrixMeasurable (a c : ℕ) : MeasurableSpace (Matrix (Fin a) (Fin c) (𝓞 K)) := ⊤
local instance hintGamesMatrixSingletons (a c : ℕ) : MeasurableSingletonClass (Matrix (Fin a) (Fin c) (𝓞 K)) :=
  inferInstance

def modularHintEncoding (b : Basis (Fin d) ℤ (𝓞 K)) (q : ℕ)
    (A : Matrix (Fin r) (Fin m) (ResidueRing K q))
    (hints : Fin k → numberFieldModularLattice K b q A) :
    Matrix (Fin m) (Fin k) (𝓞 K) :=
  fun i j => ((integralKernelEquiv K b q A).symm (hints j)).1 i

/-- The actual integral Gaussian hints supplied in the modular k-SIS game. -/
def modularHintLaw (b : Basis (Fin d) ℤ (𝓞 K)) (q : ℕ) [NeZero q]
    (A : Matrix (Fin r) (Fin m) (ResidueRing K q))
    (S : Euclidean (m * d) ≃L[ℝ] Euclidean (m * d))
    (centers : Fin k → Euclidean (m * d)) : PMF (Matrix (Fin m) (Fin k) (𝓞 K)) :=
  (latticeHintLaw (numberFieldModularLattice K b q A) S centers).map
    (modularHintEncoding K b q A)

theorem modularHintLaw_supported_on_kernel (b : Basis (Fin d) ℤ (𝓞 K))
    (q : ℕ) [NeZero q] (A : Matrix (Fin r) (Fin m) (ResidueRing K q))
    (S : Euclidean (m * d) ≃L[ℝ] Euclidean (m * d))
    (centers : Fin k → Euclidean (m * d))
    (H : Matrix (Fin m) (Fin k) (𝓞 K))
    (hH : H ∈ (modularHintLaw K b q A S centers).support) (j : Fin k) :
    H.transpose j ∈ modularKernel (residueMap K q) A := by
  obtain ⟨hints, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hH
  exact ((integralKernelEquiv K b q A).symm (hints j)).2

theorem modular_hint_adversary_bound {β : Type*} [MeasurableSpace β]
    [MeasurableSingletonClass β] (b : Basis (Fin d) ℤ (𝓞 K))
    (q : ℕ) [NeZero q] (A : Matrix (Fin r) (Fin m) (ResidueRing K q))
    (S : Euclidean (m * d) ≃L[ℝ] Euclidean (m * d))
    (centers : Fin k → Euclidean (m * d)) (henergy : shiftEnergy S centers ≤ 1)
    (adversary : Matrix (Fin m) (Fin k) (𝓞 K) → PMF β)
    (wins : Matrix (Fin m) (Fin k) (𝓞 K) → β → Prop) :
    successProbability (modularHintLaw K b q A S (fun _ => 0)) adversary wins ^ 2 /
      Real.exp (2 * Real.pi) ≤
        successProbability (modularHintLaw K b q A S centers) adversary wins := by
  simp only [modularHintLaw, successProbability_map]
  exact shifted_hint_adversary_bound_constant (numberFieldModularLattice K b q A)
    S centers henergy _ _

/-- First sample the uniform public matrix, then Gaussian kernel hints and an adversary output. -/
def modularGameSuccess {β : Type*} [MeasurableSpace β]
    (b : Basis (Fin d) ℤ (𝓞 K)) (q : ℕ) [NeZero q]
    (S : Euclidean (m * d) ≃L[ℝ] Euclidean (m * d))
    (centers : Fin k → Euclidean (m * d))
    (adversary : Matrix (Fin r) (Fin m) (ResidueRing K q) →
      Matrix (Fin m) (Fin k) (𝓞 K) → PMF β)
    (wins : Matrix (Fin r) (Fin m) (ResidueRing K q) →
      Matrix (Fin m) (Fin k) (𝓞 K) → β → Prop) : ℝ :=
  ∑ A, (PMF.uniformOfFintype (Matrix (Fin r) (Fin m) (ResidueRing K q)) A).toReal *
    successProbability (modularHintLaw K b q A S centers) (adversary A) (wins A)

/-- The centered-to-shifted comparison includes the random public matrix and adversary coins. -/
theorem modularGameSuccess_shift_bound {β : Type*} [MeasurableSpace β]
    [MeasurableSingletonClass β] (b : Basis (Fin d) ℤ (𝓞 K)) (q : ℕ) [NeZero q]
    (S : Euclidean (m * d) ≃L[ℝ] Euclidean (m * d))
    (centers : Fin k → Euclidean (m * d)) (henergy : shiftEnergy S centers ≤ 1)
    (adversary : Matrix (Fin r) (Fin m) (ResidueRing K q) →
      Matrix (Fin m) (Fin k) (𝓞 K) → PMF β)
    (wins : Matrix (Fin r) (Fin m) (ResidueRing K q) →
      Matrix (Fin m) (Fin k) (𝓞 K) → β → Prop) :
    modularGameSuccess K b q S (fun _ => 0) adversary wins ^ 2 /
      Real.exp (2 * Real.pi) ≤ modularGameSuccess K b q S centers adversary wins :=
  finite_average_squared_transfer _ _ _ (Real.exp_pos _)
    (fun A => modular_hint_adversary_bound K b q A S centers henergy (adversary A) (wins A))

end NumberFields

end SISToKSIS
