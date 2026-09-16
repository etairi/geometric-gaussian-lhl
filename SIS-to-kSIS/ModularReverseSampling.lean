import «SIS-to-kSIS».FiniteResidueGames
import «SIS-to-kSIS».SpectralHints

/-!
# Reverse sampling for the actual modular hint distributions

The forward law conditions ambient Gaussian columns on the modular equations.
The reverse law conditions a uniform public matrix on the same equations.
Flatness and the exact CRT compatibility count control their distance.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open Module NumberField GeometricGaussianLHL MeasureTheory
namespace SISToKSIS

section Lattices
variable {n : ℕ} (L N : Submodule ℤ (Euclidean n))
  [DiscreteTopology L] [IsZLattice ℝ L] [DiscreteTopology N] [IsZLattice ℝ N]

omit [DiscreteTopology L] [IsZLattice ℝ L] in
theorem fullLattice_dual_antitone (hNL : N ≤ L) : latticeDual L ≤ latticeDual N := by
  intro x hx
  rw [mem_latticeDual] at hx ⊢
  refine ⟨?_, fun z hz => hx.2 z (hNL hz)⟩
  rw [IsZLattice.span_top (K := ℝ) (L := N)]
  trivial

theorem fullLattice_smoothAt_mono (hNL : N ≤ L) {ε t : ℝ} (h : SmoothAt N ε t) :
    SmoothAt L ε t := by
  classical
  refine ⟨h.1, le_trans ?_ h.2⟩
  let f := Submodule.inclusion (fullLattice_dual_antitone L N hNL)
  have hf : Function.Injective f := Submodule.inclusion_injective _
  have hzero (x : latticeDual L) : f x = 0 ↔ x = 0 := by
    constructor
    · intro hx; exact hf (hx.trans f.map_zero.symm)
    · rintro rfl; exact f.map_zero
  have hm := ENNReal.tsum_comp_le_tsum_of_injective hf
    (fun x : latticeDual N => if x = 0 then 0 else ENNReal.ofReal (gaussianWeight t (x : Euclidean n)))
  have he : nonzeroDualMass L t = ∑' x : latticeDual L,
      if f x = 0 then 0 else ENNReal.ofReal (gaussianWeight t (f x : Euclidean n)) := by
    unfold nonzeroDualMass
    apply tsum_congr
    intro x
    by_cases hx : x = 0 <;> simp [hzero, hx, f]
  rw [he]
  apply hm.trans_eq
  unfold nonzeroDualMass
  apply tsum_congr
  intro y
  by_cases hy : y = 0 <;> simp [hy]

theorem sublatticeGaussian_probability_lower (hNL : N ≤ L)
    (S : Euclidean n ≃L[ℝ] Euclidean n) (c : Euclidean n)
    {ε Q : ℝ} (hε : 0 ≤ ε) (hεone : ε < 1) (hQ : 0 < Q)
    (hcov : ZLattice.covolume N ≤ Q * ZLattice.covolume L)
    (hsm : SmoothAt (latticeImage S.symm.toContinuousLinearMap N) ε 1) :
    (1 - ε) / (1 + ε) / Q ≤
      (shiftedLatticeGaussian L S c).toMeasure.real (sublatticeEvent L N) := by
  let LW := latticeImage S.symm.toContinuousLinearMap L
  let NW := latticeImage S.symm.toContinuousLinearMap N
  let : DiscreteTopology LW := latticeImage_discrete S.symm L
  let : DiscreteTopology NW := latticeImage_discrete S.symm N
  let : IsZLattice ℝ LW :=
    ⟨latticeImage_equiv_span_top L (IsZLattice.span_top (K := ℝ) (L := L)) S.symm⟩
  let : IsZLattice ℝ NW :=
    ⟨latticeImage_equiv_span_top N (IsZLattice.span_top (K := ℝ) (L := N)) S.symm⟩
  have hw : NW ≤ LW := Submodule.map_mono hNL
  have hsmL := fullLattice_smoothAt_mono LW NW hw hsm
  have hcovW : ZLattice.covolume NW ≤ Q * ZLattice.covolume LW := by
    dsimp only [NW, LW]
    rw [covolume_latticeImage_equiv, covolume_latticeImage_equiv]
    have ht := mul_le_mul_of_nonneg_left hcov S.symm.toLinearMap.normDet_nonneg
    simpa only [mul_left_comm] using ht
  have hcL := ZLattice.covolume_pos LW volume
  have hcN := ZLattice.covolume_pos NW volume
  have hplus : 0 < 1 + ε := by linarith
  have hlower := (latticeShiftedPartition_flat_of_smoothAt N S hε hsm c).1
  have hupper := (latticeShiftedPartition_flat_of_smoothAt L S hε hsmL c).2
  have hsmall : (1 - ε) / (Q * ZLattice.covolume LW) ≤ latticeShiftedPartition N S c :=
    (div_le_div_of_nonneg_left (sub_pos.mpr hεone).le hcN hcovW).trans hlower
  rw [sublatticeGaussian_probability L N hNL]
  calc
    _ = ((1 - ε) / (Q * ZLattice.covolume LW)) /
        ((1 + ε) / ZLattice.covolume LW) := by
      field_simp
    _ ≤ latticeShiftedPartition N S c / ((1 + ε) / ZLattice.covolume LW) :=
      div_le_div_of_nonneg_right hsmall (div_pos hplus hcL).le
    _ ≤ _ := div_le_div_of_nonneg_left (latticeShiftedPartition_pos N S c).le
      (latticeShiftedPartition_pos L S c) hupper

end Lattices

def flatnessRatio (ε : ℝ) : ℝ := (1 - ε) / (1 + ε)

theorem flatnessRatio_pos {ε : ℝ} (hε : 0 ≤ ε) (hεone : ε < 1) :
    0 < flatnessRatio ε := div_pos (sub_pos.mpr hεone) (by linarith)

theorem flatnessRatio_le_one {ε : ℝ} (hε : 0 ≤ ε) : flatnessRatio ε ≤ 1 := by
  apply (div_le_one (by linarith : 0 < 1 + ε)).mpr
  linarith

theorem flatnessRatio_bernoulli {ε : ℝ} (hε : 0 ≤ ε) (hεone : ε < 1) (k : ℕ) :
    1 - 2 * (k : ℝ) * ε ≤ flatnessRatio ε ^ k := by
  have hr := flatnessRatio_pos hε hεone
  have hb := one_add_mul_sub_le_pow (show (-1 : ℝ) ≤ flatnessRatio ε by linarith) k
  have he : flatnessRatio ε - 1 = -(2 * ε / (1 + ε)) := by
    unfold flatnessRatio
    field_simp
    ring
  rw [he] at hb
  have hd : 2 * ε / (1 + ε) ≤ 2 * ε := div_le_self (by positivity) (by linarith)
  have hm := mul_le_mul_of_nonneg_left hd (Nat.cast_nonneg k)
  nlinarith

theorem filter_map_equiv {α β : Type*} (p : PMF α) (e : α ≃ β) (E : Set β)
    (hp : ∃ x ∈ e ⁻¹' E, x ∈ p.support)
    (hq : ∃ y ∈ E, y ∈ (p.map e).support) :
    (p.map e).filter E hq = (p.filter (e ⁻¹' E) hp).map e := by
  classical
  ext y
  obtain ⟨x, rfl⟩ := e.surjective y
  rw [PMF.filter_apply, pmf_map_equiv_apply, PMF.filter_apply]
  have he : (∑' y, E.indicator (p.map e) y) = ∑' x, (e ⁻¹' E).indicator p x := by
    rw [← e.tsum_eq]
    apply tsum_congr
    intro x
    by_cases hx : e x ∈ E <;> simp [Set.indicator, hx]
  rw [he]
  by_cases hx : e x ∈ E <;> simp [Set.indicator, hx]

theorem shiftedLatticeGaussian_eq_centered {n : ℕ} (L : Submodule ℤ (Euclidean n))
    [DiscreteTopology L] [IsZLattice ℝ L]
    (S : Euclidean n ≃L[ℝ] Euclidean n) (c : L) :
    shiftedLatticeGaussian L S (c : Euclidean n) = latticeGaussianCentered L S c := by
  have he : latticeShiftedPartition L S (c : Euclidean n) = latticeGaussianPartition L S :=
    latticeGaussianCentered_partition L S c
  ext x
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [shiftedLatticeGaussian_density, he, latticeGaussianCentered_apply,
    ENNReal.toReal_ofReal (div_nonneg (gaussianWeight_pos _ _).le (latticeGaussianPartition_pos L S).le)]
  rfl

variable (K : Type*) [Field K] [NumberField K] {d m n k : ℕ}

def ambientHintEquiv (b : Basis (Fin d) ℤ (𝓞 K)) :
    (Fin k → canonicalEuclideanLattice K b m) ≃ Matrix (Fin m) (Fin k) (𝓞 K) where
  toFun x i j := (canonicalEuclideanLatticeEquiv K b m).symm (x j) i
  invFun H j := canonicalEuclideanLatticeEquiv K b m (fun i => H i j)
  left_inv x := by funext j; exact (canonicalEuclideanLatticeEquiv K b m).apply_symm_apply _
  right_inv H := by
    funext i j
    exact congrFun ((canonicalEuclideanLatticeEquiv K b m).symm_apply_apply (fun i => H i j)) i

def ambientHintLaw (b : Basis (Fin d) ℤ (𝓞 K))
    (S : Euclidean (m * d) ≃L[ℝ] Euclidean (m * d))
    (centers : Fin k → Euclidean (m * d)) : PMF (Matrix (Fin m) (Fin k) (𝓞 K)) :=
  (latticeHintLaw (canonicalEuclideanLattice K b m) S centers).map (ambientHintEquiv K b)

theorem ambientHintLaw_positive (b : Basis (Fin d) ℤ (𝓞 K))
    (S : Euclidean (m * d) ≃L[ℝ] Euclidean (m * d))
    (centers : Fin k → Euclidean (m * d)) (H : Matrix (Fin m) (Fin k) (𝓞 K)) :
    0 < (ambientHintLaw K b S centers H).toReal := by
  obtain ⟨x, rfl⟩ := (ambientHintEquiv (m := m) (k := k) K b).surjective H
  rw [ambientHintLaw, pmf_map_equiv_apply]
  exact latticeHintLaw_positive _ _ _ _

def compatibleHints (q : ℕ) (A : Matrix (Fin n) (Fin m) (ResidueRing K q))
    (H : Matrix (Fin m) (Fin k) (𝓞 K)) : Prop := A * H.map (residueMap K q) = 0

omit [NumberField K] in
theorem compatibleHints_iff (q : ℕ) (A : Matrix (Fin n) (Fin m) (ResidueRing K q))
    (H : Matrix (Fin m) (Fin k) (𝓞 K)) :
    compatibleHints K q A H ↔ ∀ j, H.transpose j ∈ modularKernel (residueMap K q) A := by
  simp only [compatibleHints, mem_modularKernel]
  constructor
  · intro h j; funext a; exact congrFun (congrFun h a) j
  · intro h; ext a j; exact congrFun (h j) a

theorem compatibleHints_support (b : Basis (Fin d) ℤ (𝓞 K))
    (q : ℕ) (A : Matrix (Fin n) (Fin m) (ResidueRing K q))
    (S : Euclidean (m * d) ≃L[ℝ] Euclidean (m * d))
    (centers : Fin k → Euclidean (m * d)) :
    ∃ H ∈ {H | compatibleHints K q A H}, H ∈ (ambientHintLaw K b S centers).support := by
  refine ⟨0, ?_, ?_⟩
  · simp [compatibleHints]
  · rw [PMF.mem_support_iff]
    intro hz
    have hp := ambientHintLaw_positive K b S centers 0
    simp only [hz, ENNReal.toReal_zero, lt_self_iff_false] at hp

theorem canonicalEmbedding_inverse (b : Basis (Fin d) ℤ (𝓞 K))
    (x : canonicalEuclideanLattice K b m) :
    canonicalEuclideanEmbedding K b m ((canonicalEuclideanLatticeEquiv K b m).symm x) = x := by
  simpa only [canonicalEuclideanLatticeEquiv_apply] using
    congrArg Subtype.val ((canonicalEuclideanLatticeEquiv K b m).apply_symm_apply x)

theorem ambientHintEquiv_preimage_compatible (b : Basis (Fin d) ℤ (𝓞 K))
    (q : ℕ) (A : Matrix (Fin n) (Fin m) (ResidueRing K q)) :
    (ambientHintEquiv (k := k) K b) ⁻¹' {H | compatibleHints K q A H} =
      {z | ∀ j, z j ∈ sublatticeEvent (canonicalEuclideanLattice K b m)
        (numberFieldModularLattice K b q A)} := by
  ext z
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, compatibleHints_iff,
    ← canonicalEmbedding_mem_modularLattice_iff K b q A]
  change (∀ j, canonicalEuclideanEmbedding K b m
    ((canonicalEuclideanLatticeEquiv K b m).symm (z j)) ∈ numberFieldModularLattice K b q A) ↔ _
  simp only [canonicalEmbedding_inverse]
  rfl

theorem ambientHintLaw_condition (b : Basis (Fin d) ℤ (𝓞 K))
    (q : ℕ) [NeZero q] (A : Matrix (Fin n) (Fin m) (ResidueRing K q))
    (S : Euclidean (m * d) ≃L[ℝ] Euclidean (m * d))
    (centers : Fin k → Euclidean (m * d)) :
    (ambientHintLaw K b S centers).filter {H | compatibleHints K q A H}
      (compatibleHints_support K b q A S centers) = modularHintLaw K b q A S centers := by
  let L := canonicalEuclideanLattice K b m
  let N := numberFieldModularLattice K b q A
  have hNL : N ≤ L := congruenceLattice_le _ _
  let E : Set (Matrix (Fin m) (Fin k) (𝓞 K)) := {H | compatibleHints K q A H}
  have he := ambientHintEquiv_preimage_compatible (k := k) K b q A
  have hp : ∃ z ∈ (ambientHintEquiv K b) ⁻¹' E,
      z ∈ (latticeHintLaw L S centers).support := by
    rw [he]
    exact independentProduct_event_support _ _ (fun j => sublatticeEvent_gaussian_support L N S (centers j))
  have hc : (latticeHintLaw L S centers).filter ((ambientHintEquiv K b) ⁻¹' E) hp =
      (latticeHintLaw N S centers).map (fun z j => Submodule.inclusion hNL (z j)) := by
    simpa only [E, he, latticeHintLaw] using shiftedLatticeGaussian_columns_condition L N hNL S centers
  change ((latticeHintLaw L S centers).map (ambientHintEquiv K b)).filter E _ = _
  rw [filter_map_equiv _ _ _ hp, hc, PMF.map_comp]
  have henc (x : N) : (canonicalEuclideanLatticeEquiv K b m).symm (Submodule.inclusion hNL x) =
      ((integralKernelEquiv K b q A).symm x).1 := by
    apply canonicalEuclideanEmbedding_injective K b m
    rw [canonicalEmbedding_inverse]
    exact ((integralKernelEquiv_coe K b q A _).symm.trans
      (congrArg (fun z : N => (z : Euclidean (m * d)))
        ((integralKernelEquiv K b q A).apply_symm_apply x))).symm
  unfold modularHintLaw
  congr 1
  funext z i j
  exact congrFun (henc (z j)) i

theorem ambientHintLaw_integral_centers (b : Basis (Fin d) ℤ (𝓞 K))
    (S : Euclidean (m * d) ≃L[ℝ] Euclidean (m * d))
    (c : Fin k → Fin m → 𝓞 K) :
    ambientHintLaw K b S (fun j => canonicalEuclideanEmbedding K b m (c j)) =
      independentMatrixColumns (fun j => numberFieldEllipsoidalGaussian K b m S (c j)) := by
  unfold ambientHintLaw latticeHintLaw independentMatrixColumns numberFieldEllipsoidalGaussian
  rw [← independentProduct_map, PMF.map_comp]
  have hshift (j : Fin k) : shiftedLatticeGaussian (canonicalEuclideanLattice K b m) S
      (canonicalEuclideanEmbedding K b m (c j)) =
      latticeGaussianCentered (canonicalEuclideanLattice K b m) S (canonicalEuclideanLatticeEquiv K b m (c j)) := by
    simpa only [canonicalEuclideanLatticeEquiv_apply] using
      shiftedLatticeGaussian_eq_centered (canonicalEuclideanLattice K b m) S
        (canonicalEuclideanLatticeEquiv K b m (c j))
  simp_rw [hshift]
  rfl

local instance reverseHintMatrixMeasurable (a c : ℕ) :
    MeasurableSpace (Matrix (Fin a) (Fin c) (𝓞 K)) := ⊤

local instance reversePublicMatrixMeasurable (q a c : ℕ) :
    MeasurableSpace (Matrix (Fin a) (Fin c) (ResidueRing K q)) := ⊤

/-- A lower bound for the actual Gaussian compatibility probability, for every
public matrix whose modular kernel satisfies the stated smoothing condition. -/
theorem ambientHintLaw_compatibility_lower (b : Basis (Fin d) ℤ (𝓞 K))
    (q : ℕ) [NeZero q] (A : Matrix (Fin n) (Fin m) (ResidueRing K q))
    (S : Euclidean (m * d) ≃L[ℝ] Euclidean (m * d))
    (centers : Fin k → Euclidean (m * d)) {ε : ℝ} (hε : 0 ≤ ε) (hεone : ε < 1)
    (hsm : SmoothAt (latticeImage S.symm.toContinuousLinearMap
      (numberFieldModularLattice K b q A)) ε 1) :
    flatnessRatio ε ^ k / (q : ℝ) ^ (d * n * k) ≤
      (ambientHintLaw K b S centers).toMeasure.real {H | compatibleHints K q A H} := by
  let L := canonicalEuclideanLattice K b m
  let N := numberFieldModularLattice K b q A
  have hNL : N ≤ L := congruenceLattice_le _ _
  have hq : (0 : ℝ) < q := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  have hcol (j : Fin k) : flatnessRatio ε / (q : ℝ) ^ (d * n) ≤
      (shiftedLatticeGaussian L S (centers j)).toMeasure.real (sublatticeEvent L N) :=
    sublatticeGaussian_probability_lower L N hNL S (centers j) hε hεone (pow_pos hq _)
      (numberFieldModularLattice_covolume_le K b q A) hsm
  rw [ambientHintLaw, pmfMap_measureReal, ambientHintEquiv_preimage_compatible]
  change flatnessRatio ε ^ k / (q : ℝ) ^ (d * n * k) ≤
    (independentProduct (fun j => shiftedLatticeGaussian L S (centers j))).toMeasure.real
      {z | ∀ j, z j ∈ sublatticeEvent L N}
  rw [Measure.real, independentProduct_event_all, ENNReal.toReal_prod]
  calc
    _ = ∏ _j : Fin k, flatnessRatio ε / (q : ℝ) ^ (d * n) := by
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, div_pow, ← pow_mul]
    _ ≤ _ := Finset.prod_le_prod (fun _ _ => div_nonneg (flatnessRatio_pos hε hεone).le (by positivity))
      (fun j _ => hcol j)

theorem compatiblePublic_support (q : ℕ) [NeZero q]
    (H : Matrix (Fin m) (Fin k) (𝓞 K)) :
    ∃ A : Matrix (Fin n) (Fin m) (ResidueRing K q), compatibleHints K q A H ∧
      A ∈ (PMF.uniformOfFintype (Matrix (Fin n) (Fin m) (ResidueRing K q))).support := by
  refine ⟨0, ?_, PMF.mem_support_uniformOfFintype 0⟩
  simp [compatibleHints]

def modularForwardLaw (b : Basis (Fin d) ℤ (𝓞 K)) (q : ℕ) [NeZero q]
    (S : Euclidean (m * d) ≃L[ℝ] Euclidean (m * d))
    (centers : Fin k → Euclidean (m * d)) :
    PMF (Matrix (Fin n) (Fin m) (ResidueRing K q) × Matrix (Fin m) (Fin k) (𝓞 K)) :=
  jointPMF (PMF.uniformOfFintype _) (fun A => modularHintLaw K b q A S centers)

def modularReverseLaw (b : Basis (Fin d) ℤ (𝓞 K)) (q : ℕ) [NeZero q]
    (S : Euclidean (m * d) ≃L[ℝ] Euclidean (m * d))
    (centers : Fin k → Euclidean (m * d)) :
    PMF (Matrix (Fin n) (Fin m) (ResidueRing K q) × Matrix (Fin m) (Fin k) (𝓞 K)) :=
  reverseSampling (PMF.uniformOfFintype _) (ambientHintLaw K b S centers)
    (compatibleHints K q) (compatiblePublic_support K q)

theorem modularForwardLaw_eq_forwardSampling (b : Basis (Fin d) ℤ (𝓞 K))
    (q : ℕ) [NeZero q] (S : Euclidean (m * d) ≃L[ℝ] Euclidean (m * d))
    (centers : Fin k → Euclidean (m * d)) :
    modularForwardLaw (n := n) K b q S centers =
      forwardSampling (PMF.uniformOfFintype _) (ambientHintLaw K b S centers)
        (compatibleHints K q) (fun A => compatibleHints_support K b q A S centers) := by
  simp only [modularForwardLaw, forwardSampling, ambientHintLaw_condition]

/-- The actual bad-public-matrix probability that the remaining modular
regularity estimate must bound from the supplied width window. -/
def modularSmoothingFailure (b : Basis (Fin d) ℤ (𝓞 K)) (q : ℕ) [NeZero q]
    (S : Euclidean (m * d) ≃L[ℝ] Euclidean (m * d)) (ε : ℝ) : ℝ :=
  (PMF.uniformOfFintype (Matrix (Fin n) (Fin m) (ResidueRing K q))).toMeasure.real
    {A | ¬ SmoothAt (latticeImage S.symm.toContinuousLinearMap
      (numberFieldModularLattice K b q A)) ε 1}

theorem modularSmoothingFailure_nonneg (b : Basis (Fin d) ℤ (𝓞 K)) (q : ℕ) [NeZero q]
    (S : Euclidean (m * d) ≃L[ℝ] Euclidean (m * d)) (ε : ℝ) :
    0 ≤ modularSmoothingFailure (n := n) K b q S ε := measureReal_nonneg

/-- Quantitative reverse sampling for the actual paper distributions. The sole
remaining analytic error is the explicitly measured modular smoothing failure. -/
theorem paper_reverseSampling_distance {g : ℕ} (b : Basis (Fin d) ℤ (𝓞 K))
    (hGram : ∀ i j, canonicalGram K b i j = if i = j then (d : ℝ) else 0)
    (q : ℕ) [NeZero q] (I : Fin g → Ideal (𝓞 K)) [∀ j, (I j).IsMaximal]
    (hI : Function.Injective I)
    (hfac : Ideal.span ({(q : 𝓞 K)} : Set (𝓞 K)) = ∏ j, I j)
    (hg : 0 < g) (hNorm : ∀ j, Ideal.absNorm (I j) ^ g = q ^ d)
    (centers : Fin k → Euclidean ((m + k) * d)) (hm : 0 < m) (hkm : 64 * k ≤ m)
    {u s₁ s₂ ε : ℝ} (h₁ : 0 < s₁) (h₂ : 0 < s₂) (hs : s₁ ≤ s₂)
    (hw : ArithmeticWindow d m n k q g u s₁ s₂) (hε : 0 ≤ ε) (hεone : ε < 1) :
    discreteTotalVariation
      (modularForwardLaw (n := n) K b q (paperHintShape K b m k h₁.ne' h₂.ne') centers)
      (modularReverseLaw (n := n) K b q (paperHintShape K b m k h₁.ne' h₂.ne') centers) ≤
      modularSmoothingFailure (n := n) K b q (paperHintShape K b m k h₁.ne' h₂.ne') ε +
        (g : ℝ) * k * (1 / 2 : ℝ) ^ ((m - k) * d) /
          ((1 - Real.exp (-((m : ℝ) * d) / 32)) * (1 - ε)) + 2 * k * ε := by
  let S := paperHintShape K b m k h₁.ne' h₂.ne'
  let Public := Matrix (Fin n) (Fin (m + k)) (ResidueRing K q)
  let Hints := Matrix (Fin (m + k)) (Fin k) (𝓞 K)
  let p : PMF Public := PMF.uniformOfFintype _
  let w : PMF Hints := ambientHintLaw K b S centers
  let v : Public → PMF Hints := fun A => modularHintLaw K b q A S centers
  let G : Set Public := {A | SmoothAt (latticeImage S.symm.toContinuousLinearMap
    (numberFieldModularLattice K b q A)) ε 1}
  let E : Set (Public × Hints) := {z | z.1 ∈ G ∧ independentHintsAtPrimes K I z.2}
  let δS := modularSmoothingFailure (n := n) K b q S ε
  let δH := (g : ℝ) * k * (1 / 2 : ℝ) ^ ((m - k) * d) /
    ((1 - Real.exp (-((m : ℝ) * d) / 32)) * (1 - ε))
  have hδH : 0 ≤ δH := div_nonneg (by positivity)
    (mul_pos (residue_tail_gap_pos (integralBasis_dimension_pos K b) hm) (sub_pos.mpr hεone)).le
  have hbad : (jointPMF p v).toMeasure.real Eᶜ ≤ δS + δH := by
    apply joint_bad_probability p v G Eᶜ (show p.toMeasure.real Gᶜ ≤ δS from le_rfl) hδH
    intro A hA
    have hh := paper_modularHintLaw_independence K b hGram q A I hg hNorm centers hm hkm
      h₁ h₂ hs hw hε hεone hA
    have hR := ENNReal.toReal_mono ENNReal.ofReal_ne_top hh
    rw [ENNReal.toReal_ofReal hδH] at hR
    have he : {H | (A, H) ∈ Eᶜ} = {H | ¬ independentHintsAtPrimes K I H} := by
      ext H
      simp only [E, Set.mem_compl_iff, Set.mem_ofPred_eq, hA, true_and]
      rfl
    rw [he, Measure.real, PMF.toMeasure_apply_eq_toOuterMeasure]
    exact hR
  have hF : forwardSampling p w (compatibleHints K q)
      (fun A => compatibleHints_support K b q A S centers) = jointPMF p v := by
    unfold forwardSampling
    apply congrArg (jointPMF p)
    funext A
    exact ambientHintLaw_condition K b q A S centers
  have hqpos : (0 : ℝ) < q := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  have hden (z : Public × Hints) (hz : z ∈ E) (_hC : compatibleHints K q z.1 z.2) :
      0 < w.toMeasure.real {H | compatibleHints K q z.1 H} ∧
      0 < p.toMeasure.real {A | compatibleHints K q A z.2} ∧
      (1 - 2 * (k : ℝ) * ε) * p.toMeasure.real {A | compatibleHints K q A z.2} ≤
        w.toMeasure.real {H | compatibleHints K q z.1 H} := by
    have hprob := ambientHintLaw_compatibility_lower K b q z.1 S centers hε hεone hz.1
    have hc := congrArg ENNReal.toReal
      (uniform_prime_hint_compatibility K b q I hI hfac z.2 hz.2
        (0 : Matrix (Fin n) (Fin k) (ResidueRing K q)))
    have hcomp : p.toMeasure.real {A | compatibleHints K q A z.2} =
        1 / (q : ℝ) ^ (d * n * k) := by
      simpa only [Measure.real, PMF.toMeasure_apply_eq_toOuterMeasure, compatibleHints,
        ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_natCast, one_div,
        show d * (k * n) = d * n * k by ring] using hc
    refine ⟨(div_pos (pow_pos (flatnessRatio_pos hε hεone) _) (pow_pos hqpos _)).trans_le hprob,
      ?_, ?_⟩
    · rw [hcomp]
      positivity
    · rw [hcomp, mul_one_div]
      exact (div_le_div_of_nonneg_right (flatnessRatio_bernoulli hε hεone k)
        (pow_pos hqpos _).le).trans hprob
  change discreteTotalVariation (jointPMF p v)
    (reverseSampling p w (compatibleHints K q) (compatiblePublic_support K q)) ≤ δS + δH + 2 * k * ε
  rw [← hF]
  exact reverseSampling_distance p w (compatibleHints K q) (compatiblePublic_support K q)
    (fun A => compatibleHints_support K b q A S centers) E (by positivity)
    (by rw [hF]; exact hbad) hden

end SISToKSIS

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Module NumberField GeometricGaussianLHL
open scoped Classical
namespace SISToKSIS

section MatrixMaps
variable {R Q : Type*} [CommRing R] [CommRing Q] {m k : ℕ}

theorem columnHints_map (f : R →+* Q) (X : Matrix (Fin k) (Fin m) R)
    (Z : Matrix (Fin m) (Fin k) R) :
    (columnHints X Z).map f = columnHints (X.map f) (Z.map f) := by
  simp only [columnHints, rowHints, Matrix.transpose_map, Matrix.fromCols_map,
    Matrix.map_add f (map_add f), Matrix.map_mul (f := f),
    Matrix.map_one f (map_zero f) (map_one f)]

theorem extractionMatrix_map (f : R →+* Q) (X : Matrix (Fin k) (Fin m) R)
    (Z : Matrix (Fin m) (Fin k) R) :
    (extractionMatrix X Z).map f = extractionMatrix (X.map f) (Z.map f) := by
  simp only [extractionMatrix, kernelColumns, Matrix.transpose_map, Matrix.fromRows_map,
    Matrix.map_sub f (map_sub f), Matrix.map_neg f (map_neg f), Matrix.map_mul (f := f),
    Matrix.map_one f (map_zero f) (map_one f)]

end MatrixMaps

variable (K : Type*) [Field K] [NumberField K] {d m k n : ℕ}

def generatedColumnMatrix
    (z : Matrix (Fin k) (Fin m) (𝓞 K) × Matrix (Fin m) (Fin k) (𝓞 K)) :
    Matrix (Fin (m + k)) (Fin k) (𝓞 K) :=
  (columnHints z.1 z.2).submatrix finSumFinEquiv.symm id

def sourcePublicMatrix (q : ℕ)
    (z : Matrix (Fin k) (Fin m) (𝓞 K) × Matrix (Fin m) (Fin k) (𝓞 K))
    (B : Matrix (Fin n) (Fin m) (ResidueRing K q)) :
    Matrix (Fin n) (Fin (m + k)) (ResidueRing K q) :=
  (B * (extractionMatrix z.1 z.2).map (residueMap K q)).submatrix id finSumFinEquiv.symm

theorem sourcePublicMatrix_uniform_conditioned (q : ℕ) [NeZero q]
    (z : Matrix (Fin k) (Fin m) (𝓞 K) × Matrix (Fin m) (Fin k) (𝓞 K)) :
    (PMF.uniformOfFintype (Matrix (Fin n) (Fin m) (ResidueRing K q))).map
      (sourcePublicMatrix K q z) =
      (PMF.uniformOfFintype (Matrix (Fin n) (Fin (m + k)) (ResidueRing K q))).filter
        {A | compatibleHints K q A (generatedColumnMatrix K z)}
        (compatiblePublic_support K q (generatedColumnMatrix K z)) := by
  have he : (generatedColumnMatrix K z).map (residueMap K q) =
      (columnHints (z.1.map (residueMap K q)) (z.2.map (residueMap K q))).submatrix
        finSumFinEquiv.symm id := by
    change ((columnHints z.1 z.2).map (residueMap K q)).submatrix
      finSumFinEquiv.symm id = _
    rw [columnHints_map]
  have hE := compatiblePublic_support (n := n) K q (generatedColumnMatrix K z)
  simp only [compatibleHints, he] at hE
  have h := uniform_publicMatrix_conditioned
    (z.1.map (residueMap K q)) (z.2.map (residueMap K q)) hE
  change (PMF.uniformOfFintype (Matrix (Fin n) (Fin m) (ResidueRing K q))).map
    (fun B => (B * (extractionMatrix z.1 z.2).map (residueMap K q)).submatrix
      id finSumFinEquiv.symm) = _
  rw [extractionMatrix_map]
  simpa only [compatibleHints, he] using h

/-- The actual source game before invoking the adversary. -/
def sourceSimulationLaw (q : ℕ) [NeZero q]
    (p : PMF (Matrix (Fin k) (Fin m) (𝓞 K) × Matrix (Fin m) (Fin k) (𝓞 K))) :
    PMF (Matrix (Fin n) (Fin (m + k)) (ResidueRing K q) ×
      Matrix (Fin (m + k)) (Fin k) (𝓞 K)) :=
  (jointPMF p (fun _ => PMF.uniformOfFintype (Matrix (Fin n) (Fin m) (ResidueRing K q)))).map
    (fun z => (sourcePublicMatrix K q z.1 z.2, generatedColumnMatrix K z.1))

theorem sourceSimulationLaw_eq_reverseSampling (q : ℕ) [NeZero q]
    (p : PMF (Matrix (Fin k) (Fin m) (𝓞 K) × Matrix (Fin m) (Fin k) (𝓞 K))) :
    sourceSimulationLaw (n := n) K q p =
      reverseSampling (PMF.uniformOfFintype _)
        (p.map (generatedColumnMatrix K)) (compatibleHints K q) (compatiblePublic_support K q) := by
  let w := PMF.uniformOfFintype (Matrix (Fin n) (Fin m) (ResidueRing K q))
  let C := fun H : Matrix (Fin (m + k)) (Fin k) (𝓞 K) => (PMF.uniformOfFintype (Matrix (Fin n) (Fin (m + k)) (ResidueRing K q))).filter
    {A | compatibleHints K q A H} (compatiblePublic_support K q H)
  have hC (z) : w.map (sourcePublicMatrix K q z) = C (generatedColumnMatrix K z) :=
    sourcePublicMatrix_uniform_conditioned K q z
  simp only [sourceSimulationLaw, reverseSampling, jointPMF, PMF.map_bind, PMF.bind_map,
    PMF.map_comp, Function.comp_def, Equiv.prodComm_apply]
  apply congrArg (fun f => p.bind f)
  funext z
  have h := congrArg (fun t => t.map (fun A => (A, generatedColumnMatrix K z))) (hC z)
  simpa only [PMF.map_comp, Function.comp_def, Prod.swap_prod_mk, w, C] using h

theorem sourceSimulationLaw_distance_reverse (b : Basis (Fin d) ℤ (𝓞 K))
    (q : ℕ) [NeZero q]
    (p : PMF (Matrix (Fin k) (Fin m) (𝓞 K) × Matrix (Fin m) (Fin k) (𝓞 K)))
    (S : Euclidean ((m + k) * d) ≃L[ℝ] Euclidean ((m + k) * d))
    (centers : Fin k → Euclidean ((m + k) * d)) :
    discreteTotalVariation (sourceSimulationLaw (n := n) K q p)
      (modularReverseLaw (n := n) K b q S centers) =
      discreteTotalVariation (p.map (generatedColumnMatrix K)) (ambientHintLaw K b S centers) := by
  simp only [sourceSimulationLaw_eq_reverseSampling, modularReverseLaw, reverseSampling,
    discreteTotalVariation_map_equiv, totalVariation_joint_same_adversary]

theorem HintGeneratorBounds.source_reverse_distance (b : Basis (Fin d) ℤ (𝓞 K))
    (q : ℕ) [NeZero q] {s₁ s₂ δlaw δnorm : ℝ} (h₁ : s₁ ≠ 0) (hs₂ : 0 < s₂)
    (sampler : Matrix (Fin k) (Fin m) (𝓞 K) → Fin k → PMF (Fin m → 𝓞 K))
    (h : HintGeneratorBounds K b (numberFieldMatrixLaw K b k m s₁ h₁) hs₂ sampler δlaw δnorm) :
    discreteTotalVariation
      (sourceSimulationLaw (n := n) K q
        (jointPMF (numberFieldMatrixLaw K b k m s₁ h₁)
          (fun X => independentMatrixColumns (sampler X))))
      (modularReverseLaw (n := n) K b q (paperHintShape K b m k h₁ hs₂.ne')
        (paperHintCenters K b m k)) ≤ δlaw := by
  rw [sourceSimulationLaw_distance_reverse]
  unfold paperHintCenters canonicalUnitCenter
  rw [ambientHintLaw_integral_centers]
  exact h.generated_column_law K b h₁ hs₂ sampler

end SISToKSIS

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Module NumberField GeometricGaussianLHL MeasureTheory
open scoped Classical
namespace SISToKSIS

/-- Conditioning first on a finite public input gives the same success
probability as the joint public-input game. -/
theorem successProbability_joint_finite_first {α β γ : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β] [MeasurableSingletonClass γ]
    (p : PMF α) (q : α → PMF β) (adversary : α → β → PMF γ)
    (wins : α → β → γ → Prop) :
    successProbability (jointPMF p q) (fun z => adversary z.1 z.2) (fun z => wins z.1 z.2) =
      ∑ a, (p a).toReal * successProbability (q a) (adversary a) (wins a) := by
  have hs : Summable (fun z : α × β => (jointPMF p q z).toReal *
      (adversary z.1 z.2).toMeasure.real {w | wins z.1 z.2 w}) := by
    apply (pmf_summable_toReal (jointPMF p q)).of_nonneg_of_le
    · intro z
      exact mul_nonneg ENNReal.toReal_nonneg measureReal_nonneg
    · intro z
      apply mul_le_of_le_one_right ENNReal.toReal_nonneg
      simp
  rw [successProbability_eq_average, hs.tsum_prod, tsum_fintype]
  apply Finset.sum_congr rfl
  intro a _
  rw [successProbability_eq_average, ← tsum_mul_left]
  apply tsum_congr
  intro b
  rw [jointPMF_apply, ENNReal.toReal_mul, mul_assoc]

variable (K : Type*) [Field K] [NumberField K] {d m k n : ℕ}
local instance assemblyPublicMeasurable (q n r : ℕ) :
    MeasurableSpace (Matrix (Fin n) (Fin r) (ResidueRing K q)) := ⊤
local instance assemblyHintMeasurable (r k : ℕ) :
    MeasurableSpace (Matrix (Fin r) (Fin k) (𝓞 K)) := ⊤

theorem modularGameSuccess_eq_forward_success {β : Type*}
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (b : Basis (Fin d) ℤ (𝓞 K)) (q : ℕ) [NeZero q]
    (S : Euclidean (m * d) ≃L[ℝ] Euclidean (m * d))
    (centers : Fin k → Euclidean (m * d))
    (adversary : Matrix (Fin n) (Fin m) (ResidueRing K q) →
      Matrix (Fin m) (Fin k) (𝓞 K) → PMF β)
    (wins : Matrix (Fin n) (Fin m) (ResidueRing K q) →
      Matrix (Fin m) (Fin k) (𝓞 K) → β → Prop) :
    modularGameSuccess K b q S centers adversary wins =
      successProbability (modularForwardLaw K b q S centers)
        (fun z => adversary z.1 z.2) (fun z => wins z.1 z.2) := by
  exact (successProbability_joint_finite_first _ _ adversary wins).symm

end SISToKSIS

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Module NumberField GeometricGaussianLHL MeasureTheory Matrix
open scoped Classical
namespace SISToKSIS

theorem jointPMF_fst {α β : Type*} (p : PMF α) (q : α → PMF β) :
    (jointPMF p q).map Prod.fst = p := by
  simp only [jointPMF, PMF.map_bind, PMF.map_comp, Function.comp_def]
  change (p.bind fun a => (q a).map (Function.const β a)) = p
  simp

variable (K : Type*) [Field K] [NumberField K] {m k n : ℕ}

/-- The k-SIS predicate in the game's flat public-matrix convention, with the
adversary's output expressed in the equivalent two-block coordinates. -/
def simulatedKSISWins (q : ℕ) (β : ℝ)
    (A : Matrix (Fin n) (Fin (m + k)) (ResidueRing K q))
    (H : Matrix (Fin (m + k)) (Fin k) (𝓞 K)) (v : Fin m ⊕ Fin k → 𝓞 K) : Prop :=
  IsKSISSolution (residueMap K q) (algebraMap (𝓞 K) K) (splitCanonicalNorm K) β
    (A.submatrix id finSumFinEquiv) (H.submatrix finSumFinEquiv id) v

def extractedVector
    (z : Matrix (Fin k) (Fin m) (𝓞 K) × Matrix (Fin m) (Fin k) (𝓞 K))
    (v : Fin m ⊕ Fin k → 𝓞 K) : Fin m → 𝓞 K := extractionMatrix z.1 z.2 *ᵥ v

/-- The reduction's adversary: sample the hint blocks, call the k-SIS adversary
on the transformed input, and apply the exact extraction matrix. -/
def reductionAdversary (q : ℕ)
    (p : PMF (Matrix (Fin k) (Fin m) (𝓞 K) × Matrix (Fin m) (Fin k) (𝓞 K)))
    (adversary : Matrix (Fin n) (Fin (m + k)) (ResidueRing K q) →
      Matrix (Fin (m + k)) (Fin k) (𝓞 K) → PMF (Fin m ⊕ Fin k → 𝓞 K))
    (B : Matrix (Fin n) (Fin m) (ResidueRing K q)) : PMF (Fin m → 𝓞 K) :=
  p.bind (fun z => (adversary (sourcePublicMatrix K q z B) (generatedColumnMatrix K z)).map
    (extractedVector K z))

def extractionCoupledLaw (q : ℕ) [NeZero q]
    (p : PMF (Matrix (Fin k) (Fin m) (𝓞 K) × Matrix (Fin m) (Fin k) (𝓞 K)))
    (adversary : Matrix (Fin n) (Fin (m + k)) (ResidueRing K q) →
      Matrix (Fin (m + k)) (Fin k) (𝓞 K) → PMF (Fin m ⊕ Fin k → 𝓞 K)) :=
  jointPMF (jointPMF p (fun _ => PMF.uniformOfFintype (Matrix (Fin n) (Fin m) (ResidueRing K q))))
    (fun z => adversary (sourcePublicMatrix K q z.1 z.2) (generatedColumnMatrix K z.1))

theorem reductionAdversary_joint_law (q : ℕ) [NeZero q]
    (p : PMF (Matrix (Fin k) (Fin m) (𝓞 K) × Matrix (Fin m) (Fin k) (𝓞 K)))
    (adversary : Matrix (Fin n) (Fin (m + k)) (ResidueRing K q) →
      Matrix (Fin (m + k)) (Fin k) (𝓞 K) → PMF (Fin m ⊕ Fin k → 𝓞 K)) :
    jointPMF (PMF.uniformOfFintype (Matrix (Fin n) (Fin m) (ResidueRing K q)))
      (reductionAdversary K q p adversary) =
      (extractionCoupledLaw K q p adversary).map
        (fun z => (z.1.2, extractedVector K z.1.1 z.2)) := by
  simp only [reductionAdversary, extractionCoupledLaw, jointPMF,
    PMF.map_bind, PMF.bind_bind, PMF.bind_map, PMF.map_comp, Function.comp_def]
  exact PMF.bind_comm _ _ _

theorem simulatedKSISWins_source (q : ℕ) (β : ℝ)
    (z : Matrix (Fin k) (Fin m) (𝓞 K) × Matrix (Fin m) (Fin k) (𝓞 K))
    (B : Matrix (Fin n) (Fin m) (ResidueRing K q)) (v : Fin m ⊕ Fin k → 𝓞 K) :
    simulatedKSISWins K q β (sourcePublicMatrix K q z B) (generatedColumnMatrix K z) v ↔
      IsKSISSolution (residueMap K q) (algebraMap (𝓞 K) K) (splitCanonicalNorm K) β
        (B * (extractionMatrix z.1 z.2).map (residueMap K q)) (columnHints z.1 z.2) v := by
  have hp : (sourcePublicMatrix K q z B).submatrix id finSumFinEquiv =
      B * (extractionMatrix z.1 z.2).map (residueMap K q) := by
    funext i j
    simp [sourcePublicMatrix]
  have hh : (generatedColumnMatrix K z).submatrix finSumFinEquiv id = columnHints z.1 z.2 := by
    funext i j
    simp [generatedColumnMatrix]
  simp only [simulatedKSISWins, hp, hh]

/-- A simultaneous norm bound is sufficient for every adversarial output. -/
theorem extractedVector_solution (q : ℕ)
    (z : Matrix (Fin k) (Fin m) (𝓞 K) × Matrix (Fin m) (Fin k) (𝓞 K))
    (B : Matrix (Fin n) (Fin m) (ResidueRing K q)) (v : Fin m ⊕ Fin k → 𝓞 K)
    {s₂ β₀ β₁ : ℝ} (hm : 0 < m) (hs₂ : 0 < s₂)
    (hβ : normLoss m s₂ * β₁ ≤ β₀)
    (hbound : ∀ v, canonicalRingNorm K (extractedVector K z v) ≤
      normLoss m s₂ * splitCanonicalNorm K v)
    (hv : simulatedKSISWins K q β₁ (sourcePublicMatrix K q z B) (generatedColumnMatrix K z) v) :
    IsSISSolution (residueMap K q) (canonicalRingNorm K) β₀ B (extractedVector K z v) :=
  extract_solution (residueMap K q) (algebraMap (𝓞 K) K)
    (canonicalRingNorm K) (splitCanonicalNorm K) B z.1 z.2
    (normLoss_pos hm hs₂) hβ hbound v ((simulatedKSISWins_source K q β₁ z B v).mp hv)

end SISToKSIS

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Module NumberField GeometricGaussianLHL MeasureTheory
open scoped Classical
namespace SISToKSIS
variable (K : Type*) [Field K] [NumberField K] {m k n : ℕ}

local instance extractionMatrixMeasurable (a b : ℕ) :
    MeasurableSpace (Matrix (Fin a) (Fin b) (𝓞 K)) := ⊤
local instance extractionPublicMeasurable (q a b : ℕ) :
    MeasurableSpace (Matrix (Fin a) (Fin b) (ResidueRing K q)) := ⊤
local instance extractionVectorMeasurable (ι : Type*) : MeasurableSpace (ι → 𝓞 K) := ⊤

theorem extractionCoupledLaw_blocks (q : ℕ) [NeZero q]
    (p : PMF (Matrix (Fin k) (Fin m) (𝓞 K) × Matrix (Fin m) (Fin k) (𝓞 K)))
    (adversary : Matrix (Fin n) (Fin (m + k)) (ResidueRing K q) →
      Matrix (Fin (m + k)) (Fin k) (𝓞 K) → PMF (Fin m ⊕ Fin k → 𝓞 K)) :
    (extractionCoupledLaw K q p adversary).map (fun z => z.1.1) = p := by
  calc
    _ = ((extractionCoupledLaw K q p adversary).map Prod.fst).map Prod.fst := by
      rw [PMF.map_comp]
      rfl
    _ = p := by rw [extractionCoupledLaw, jointPMF_fst, jointPMF_fst]

theorem sourceSimulation_success_coupled (q : ℕ) [NeZero q]
    (p : PMF (Matrix (Fin k) (Fin m) (𝓞 K) × Matrix (Fin m) (Fin k) (𝓞 K)))
    (adversary : Matrix (Fin n) (Fin (m + k)) (ResidueRing K q) →
      Matrix (Fin (m + k)) (Fin k) (𝓞 K) → PMF (Fin m ⊕ Fin k → 𝓞 K)) (β : ℝ) :
    successProbability (sourceSimulationLaw (n := n) K q p)
      (fun z => adversary z.1 z.2) (fun z => simulatedKSISWins K q β z.1 z.2) =
      (extractionCoupledLaw K q p adversary).toMeasure.real
        {z | simulatedKSISWins K q β (sourcePublicMatrix K q z.1.1 z.1.2)
          (generatedColumnMatrix K z.1.1) z.2} := by
  rw [sourceSimulationLaw, successProbability_map]
  rfl

theorem reductionAdversary_success_coupled (q : ℕ) [NeZero q]
    (p : PMF (Matrix (Fin k) (Fin m) (𝓞 K) × Matrix (Fin m) (Fin k) (𝓞 K)))
    (adversary : Matrix (Fin n) (Fin (m + k)) (ResidueRing K q) →
      Matrix (Fin (m + k)) (Fin k) (𝓞 K) → PMF (Fin m ⊕ Fin k → 𝓞 K)) (β : ℝ) :
    successProbability (PMF.uniformOfFintype (Matrix (Fin n) (Fin m) (ResidueRing K q)))
      (reductionAdversary K q p adversary)
      (IsSISSolution (residueMap K q) (canonicalRingNorm K) β) =
      (extractionCoupledLaw K q p adversary).toMeasure.real
        {z | IsSISSolution (residueMap K q) (canonicalRingNorm K) β z.1.2
          (extractedVector K z.1.1 z.2)} := by
  unfold successProbability
  rw [reductionAdversary_joint_law, pmfMap_measureReal]
  rfl

/-- Successful k-SIS outputs give successful SIS outputs outside the simultaneous
norm-failure event. The adversary may depend on both the public matrix and hints. -/
theorem reductionAdversary_success_loss (q : ℕ) [NeZero q]
    (p : PMF (Matrix (Fin k) (Fin m) (𝓞 K) × Matrix (Fin m) (Fin k) (𝓞 K)))
    (adversary : Matrix (Fin n) (Fin (m + k)) (ResidueRing K q) →
      Matrix (Fin (m + k)) (Fin k) (𝓞 K) → PMF (Fin m ⊕ Fin k → 𝓞 K))
    {s₂ β₀ β₁ δnorm : ℝ} (hm : 0 < m) (hs₂ : 0 < s₂)
    (hβ : normLoss m s₂ * β₁ ≤ β₀) (hδnorm : 0 ≤ δnorm)
    (hbad : p.toOuterMeasure {z | ∃ v : Fin m ⊕ Fin k → 𝓞 K,
      normLoss m s₂ * splitCanonicalNorm K v < canonicalRingNorm K (extractedVector K z v)} ≤
        ENNReal.ofReal δnorm) :
    successProbability (sourceSimulationLaw (n := n) K q p)
      (fun z => adversary z.1 z.2) (fun z => simulatedKSISWins K q β₁ z.1 z.2) - δnorm ≤
      successProbability (PMF.uniformOfFintype (Matrix (Fin n) (Fin m) (ResidueRing K q)))
        (reductionAdversary K q p adversary)
        (IsSISSolution (residueMap K q) (canonicalRingNorm K) β₀) := by
  let bad := {z : Matrix (Fin k) (Fin m) (𝓞 K) × Matrix (Fin m) (Fin k) (𝓞 K) |
    ∃ v : Fin m ⊕ Fin k → 𝓞 K,
      normLoss m s₂ * splitCanonicalNorm K v < canonicalRingNorm K (extractedVector K z v)}
  have hb : p.toMeasure.real bad ≤ δnorm := by
    rw [Measure.real, PMF.toMeasure_apply_eq_toOuterMeasure]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hbad).trans_eq
      (ENNReal.toReal_ofReal hδnorm)
  have hmarg : (extractionCoupledLaw K q p adversary).toMeasure.real
      {z | z.1.1 ∈ bad} = p.toMeasure.real bad := by
    have h := pmfMap_measureReal (extractionCoupledLaw K q p adversary) (fun z => z.1.1) bad
    rw [extractionCoupledLaw_blocks] at h
    exact h.symm
  have hsuccess := success_outside_bad_event (extractionCoupledLaw K q p adversary)
    {z | simulatedKSISWins K q β₁ (sourcePublicMatrix K q z.1.1 z.1.2)
      (generatedColumnMatrix K z.1.1) z.2}
    {z | IsSISSolution (residueMap K q) (canonicalRingNorm K) β₀ z.1.2
      (extractedVector K z.1.1 z.2)}
    {z | z.1.1 ∈ bad} (by
      intro z hz hgood
      apply extractedVector_solution K q z.1.1 z.1.2 z.2 hm hs₂ hβ _ hz
      intro v
      exact le_of_not_gt (fun hv => hgood ⟨v, hv⟩))
  rw [hmarg] at hsuccess
  rw [sourceSimulation_success_coupled, reductionAdversary_success_coupled]
  linarith

end SISToKSIS

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Module NumberField GeometricGaussianLHL MeasureTheory
namespace SISToKSIS
variable (K : Type*) [Field K] [NumberField K] {m k n : ℕ}

local instance inputErrorMatrixMeasurable (a b : ℕ) :
    MeasurableSpace (Matrix (Fin a) (Fin b) (𝓞 K)) := ⊤
local instance inputErrorPublicMeasurable (q a b : ℕ) :
    MeasurableSpace (Matrix (Fin a) (Fin b) (ResidueRing K q)) := ⊤
local instance inputErrorVectorMeasurable (ι : Type*) : MeasurableSpace (ι → 𝓞 K) := ⊤

/-- Replacing the law of the sampled blocks charges its distance only once,
including after adaptive adversarial queries and solution extraction. -/
theorem reductionAdversary_success_block_error (q : ℕ) [NeZero q]
    (p p' : PMF (Matrix (Fin k) (Fin m) (𝓞 K) × Matrix (Fin m) (Fin k) (𝓞 K)))
    (adversary : Matrix (Fin n) (Fin (m + k)) (ResidueRing K q) →
      Matrix (Fin (m + k)) (Fin k) (𝓞 K) → PMF (Fin m ⊕ Fin k → 𝓞 K))
    (β : ℝ) {ε : ℝ} (hp : discreteTotalVariation p p' ≤ ε) :
    successProbability (PMF.uniformOfFintype (Matrix (Fin n) (Fin m) (ResidueRing K q)))
        (reductionAdversary K q p adversary)
        (IsSISSolution (residueMap K q) (canonicalRingNorm K) β) -
      successProbability (PMF.uniformOfFintype (Matrix (Fin n) (Fin m) (ResidueRing K q)))
        (reductionAdversary K q p' adversary)
        (IsSISSolution (residueMap K q) (canonicalRingNorm K) β) ≤ ε := by
  rw [reductionAdversary_success_coupled, reductionAdversary_success_coupled]
  have h := pmf_event_sub_le_totalVariation (extractionCoupledLaw K q p adversary)
    (extractionCoupledLaw K q p' adversary)
    {z | IsSISSolution (residueMap K q) (canonicalRingNorm K) β z.1.2
      (extractedVector K z.1.1 z.2)}
  simp only [extractionCoupledLaw, totalVariation_joint_same_adversary] at h
  exact h.trans hp

/-- A finite approximation to the initial Gaussian matrix is charged once,
even though all shaped columns depend on that matrix. -/
theorem reductionAdversary_success_initial_error (q : ℕ) [NeZero q]
    (p p' : PMF (Matrix (Fin k) (Fin m) (𝓞 K)))
    (sampler : Matrix (Fin k) (Fin m) (𝓞 K) → Fin k → PMF (Fin m → 𝓞 K))
    (adversary : Matrix (Fin n) (Fin (m + k)) (ResidueRing K q) →
      Matrix (Fin (m + k)) (Fin k) (𝓞 K) → PMF (Fin m ⊕ Fin k → 𝓞 K))
    (β : ℝ) {ε : ℝ} (hp : discreteTotalVariation p p' ≤ ε) :
    successProbability (PMF.uniformOfFintype (Matrix (Fin n) (Fin m) (ResidueRing K q)))
        (reductionAdversary K q
          (jointPMF p (fun X => independentMatrixColumns (sampler X))) adversary)
        (IsSISSolution (residueMap K q) (canonicalRingNorm K) β) -
      successProbability (PMF.uniformOfFintype (Matrix (Fin n) (Fin m) (ResidueRing K q)))
        (reductionAdversary K q
          (jointPMF p' (fun X => independentMatrixColumns (sampler X))) adversary)
        (IsSISSolution (residueMap K q) (canonicalRingNorm K) β) ≤ ε := by
  exact reductionAdversary_success_block_error K q _ _ adversary β
    (by simpa only [totalVariation_joint_same_adversary] using hp)

end SISToKSIS
