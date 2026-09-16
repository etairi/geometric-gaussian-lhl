import «SIS-to-kSIS».ResidueMass
import «SIS-to-kSIS».HintGames

/-!
# Residue-span probabilities for Gaussian kernel hints

The numerator is bounded on the full prime-residue image lattice. The
denominator is the actual modular-kernel Gaussian partition; smoothing gives
its lower bound uniformly for all ambient shift centers.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Module NumberField GeometricGaussianLHL MeasureTheory

namespace SISToKSIS

def paddedColumns {F : Type*} [Zero F] {m r k : ℕ}
    (v : Fin r → (Fin m → F)) : Matrix (Fin m) (Fin k) F :=
  fun i j => if h : j.val < r then v ⟨j.val, h⟩ i else 0

theorem span_le_paddedColumns_range {F : Type*} [Field F] {m r k : ℕ}
    (v : Fin r → (Fin m → F)) (hr : r ≤ k) :
    Submodule.span F (Set.range v) ≤ LinearMap.range (paddedColumns (k := k) v).mulVecLin := by
  rw [Matrix.range_mulVecLin]
  apply Submodule.span_mono
  rintro _ ⟨j, rfl⟩
  refine ⟨Fin.castLE hr j, ?_⟩
  ext i
  simp [paddedColumns, Matrix.col, j.isLt]

theorem canonical_discr_sqrt_of_diagonal (K : Type*) [Field K] [NumberField K]
    {d : ℕ} (b : Basis (Fin d) ℤ (𝓞 K))
    (hGram : ∀ i j, canonicalGram K b i j = if i = j then (d : ℝ) else 0) :
    Real.sqrt |(NumberField.discr K : ℝ)| = Real.sqrt d ^ d := by
  have hG : canonicalGram K b = Matrix.diagonal (fun _ : Fin d => (d : ℝ)) := by
    ext i j
    rw [hGram, Matrix.diagonal_apply]
  have hdisc : |(NumberField.discr K : ℝ)| = (d : ℝ) ^ d := by
    rw [← canonicalGram_det K b, hG, Matrix.det_diagonal]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (pow_nonneg (Real.sqrt_nonneg _) _)).mp
  rw [Real.sq_sqrt (abs_nonneg _), hdisc, ← pow_mul, Nat.mul_comm d 2,
    pow_mul, Real.sq_sqrt (Nat.cast_nonneg d)]

/-- A fresh independent column is tested only against the other columns.
The span estimate is required for every fixed list, including dependent lists. -/
theorem independentProduct_linearIndependent_failure {α F V : Type*}
    [Field F] [AddCommGroup V] [Module F V] (f : α → V)
    {δ : ℝ} (hδ : 0 ≤ δ) (k : ℕ) :
    ∀ (p : Fin k → PMF α),
      (∀ i (r : ℕ), r < k → ∀ v : Fin r → V,
        (p i).toOuterMeasure {x | f x ∈ Submodule.span F (Set.range v)} ≤ ENNReal.ofReal δ) →
      (independentProduct p).toOuterMeasure {z | ¬ LinearIndependent F (fun i => f (z i))} ≤
        ENNReal.ofReal ((k : ℝ) * δ) := by
  let : MeasurableSpace α := ⊤
  induction k with
  | zero =>
      intro p _
      simp
  | succ k ih =>
      intro p hspan
      let pt : PMF (Fin k → α) := independentProduct (fun i : Fin k => p i.succ)
      let G : Set (Fin k → α) := {z | LinearIndependent F (fun i => f (z i))}
      let E : Set ((Fin k → α) × α) :=
        {z : (Fin k → α) × α | ¬ LinearIndependent F (fun i : Fin (k + 1) => f (Fin.cons (α := fun _ => α) z.2 z.1 i))}
      have ht := ih (fun i => p i.succ) (fun i r hr v => hspan i.succ r (by omega) v)
      have htR : pt.toMeasure.real Gᶜ ≤ (k : ℝ) * δ := by
        rw [Measure.real, PMF.toMeasure_apply_eq_toOuterMeasure]
        exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top ht).trans_eq
          (ENNReal.toReal_ofReal (mul_nonneg (Nat.cast_nonneg k) hδ))
      have hE (z : Fin k → α) (hz : z ∈ G) :
          (p 0).toMeasure.real {x | (z, x) ∈ E} ≤ δ := by
        have he (x : α) : (fun i : Fin (k + 1) => f (Fin.cons (α := fun _ => α) x z i)) =
            Fin.cons (α := fun _ => V) (f x) (fun i => f (z i)) := by
          funext i
          exact Fin.cases rfl (fun _ => rfl) i
        have hs : {x | (z, x) ∈ E} = {x | f x ∈ Submodule.span F (Set.range (fun i => f (z i)))} := by
          ext x
          change (¬ LinearIndependent F (fun i => f (Fin.cons (α := fun _ => α) x z i))) ↔ _
          rw [he, linearIndependent_finCons]
          change (¬ (LinearIndependent F (fun i => f (z i)) ∧ _)) ↔ _
          simp only [show LinearIndependent F (fun i => f (z i)) from hz, true_and, not_not,
            Set.mem_ofPred_eq]
        rw [hs, Measure.real, PMF.toMeasure_apply_eq_toOuterMeasure]
        exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top
          (hspan 0 k (by omega) (fun i => f (z i)))).trans_eq (ENNReal.toReal_ofReal hδ)
      have hj := joint_bad_probability pt (fun _ => p 0) G E htR hδ hE
      have hJ := ENNReal.ofReal_le_ofReal hj
      rw [Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _),
        PMF.toMeasure_apply_eq_toOuterMeasure] at hJ
      rw [← independentProduct_cons p, PMF.toOuterMeasure_map_apply,
        ← jointPMF_const_swap pt (p 0), PMF.toOuterMeasure_map_apply]
      change (jointPMF pt (fun _ => p 0)).toOuterMeasure E ≤ _
      convert hJ using 1
      congr 1
      push_cast
      ring

section Lattices

variable {n : ℕ} (L N : Submodule ℤ (Euclidean n))
  [DiscreteTopology L] [IsZLattice ℝ L] [DiscreteTopology N] [IsZLattice ℝ N]

theorem latticeShiftedPartition_le_centered (S : Euclidean n ≃L[ℝ] Euclidean n)
    (c : Euclidean n) : latticeShiftedPartition N S c ≤ latticeGaussianPartition N S := by
  rw [latticeShiftedPartition_coordinates, latticeGaussianPartition_eq]
  exact ellipsoidPartition_le_zero _ _

/-- The two lattices need not contain one another. -/
theorem shiftedLatticeGaussian_submodule_probability [MeasurableSpace L]
    [MeasurableSingletonClass L] (S : Euclidean n ≃L[ℝ] Euclidean n) (c : Euclidean n) :
    (shiftedLatticeGaussian L S c).toMeasure.real (sublatticeEvent L N) ≤
      latticeGaussianPartition N S / latticeShiftedPartition L S c := by
  let E := sublatticeEvent L N
  let f : E → N := fun x => ⟨x.1, x.2⟩
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : N => (z : Euclidean n)) h
  have hs : Summable (fun x : E => latticeShiftedWeight L S c x) :=
    (summable_latticeShiftedWeight L S c).subtype E
  have hnum : (∑' x : E, latticeShiftedWeight L S c x) ≤ latticeShiftedPartition N S c := by
    apply hs.tsum_le_tsum_of_inj f hf
      (fun y _ => (gaussianWeight_pos 1 (S.symm ((y : Euclidean n) - c))).le)
      (fun x => le_rfl) (summable_latticeShiftedWeight N S c)
  rw [pmf_measureReal_eq_tsum, ← tsum_subtype E (fun x => (shiftedLatticeGaussian L S c x).toReal)]
  simp_rw [shiftedLatticeGaussian_density]
  rw [tsum_div_const]
  exact div_le_div_of_nonneg_right
    (hnum.trans (latticeShiftedPartition_le_centered N S c))
    (latticeShiftedPartition_pos L S c).le

theorem shiftedLatticeGaussian_submodule_probability_of_smoothAt [MeasurableSpace L]
    [MeasurableSingletonClass L] (S : Euclidean n ≃L[ℝ] Euclidean n) (c : Euclidean n)
    {ε : ℝ} (hε : 0 ≤ ε) (hεone : ε < 1)
    (hsm : SmoothAt (latticeImage S.symm.toContinuousLinearMap L) ε 1) :
    (shiftedLatticeGaussian L S c).toMeasure.real (sublatticeEvent L N) ≤
      latticeGaussianPartition N S *
        ZLattice.covolume (latticeImage S.symm.toContinuousLinearMap L) / (1 - ε) := by
  let : DiscreteTopology (latticeImage S.symm.toContinuousLinearMap L) :=
    latticeImage_discrete S.symm L
  let : IsZLattice ℝ (latticeImage S.symm.toContinuousLinearMap L) :=
    ⟨latticeImage_equiv_span_top L (IsZLattice.span_top (K := ℝ) (L := L)) S.symm⟩
  have hc := ZLattice.covolume_pos (latticeImage S.symm.toContinuousLinearMap L) volume
  have hz := (latticeShiftedPartition_flat_of_smoothAt L S hε hsm c).1
  apply (shiftedLatticeGaussian_submodule_probability L N S c).trans
  calc
    _ ≤ latticeGaussianPartition N S /
        ((1 - ε) / ZLattice.covolume (latticeImage S.symm.toContinuousLinearMap L)) :=
      div_le_div_of_nonneg_left (latticeGaussianPartition_pos N S).le
        (div_pos (sub_pos.mpr hεone) hc) hz
    _ = _ := by rw [div_div_eq_mul_div]

end Lattices

section NumberFields

variable (K : Type*) [Field K] [NumberField K] {d m k n : ℕ}

local instance independenceResidueField (I : Ideal (𝓞 K)) [I.IsMaximal] :
    Field ((𝓞 K) ⧸ I) := Ideal.Quotient.field I

/-- A single shifted kernel hint lies in any prescribed `k`-column prime-residue
span with this probability. The modular smoothing hypothesis remains explicit. -/
theorem shifted_kernel_prime_residue_probability (b : Basis (Fin d) ℤ (𝓞 K))
    (q : ℕ) [NeZero q] (A : Matrix (Fin n) (Fin (m + k)) (ResidueRing K q))
    (I : Ideal (𝓞 K)) [I.IsMaximal] (hI : Ideal.absNorm I ≠ 0)
    (U : Matrix (Fin (m + k)) (Fin k) ((𝓞 K) ⧸ I))
    (S : Euclidean ((m + k) * d) ≃L[ℝ] Euclidean ((m + k) * d))
    (c : Euclidean ((m + k) * d)) (hm : 0 < m) (hkm : 64 * k ≤ m)
    {σ ε : ℝ} (hσ : 0 < σ) (hS : ‖S.toContinuousLinearMap‖ ≤ σ)
    (hwidth : σ * Real.sqrt m ≤ (Ideal.absNorm I : ℝ) ^ (1 / (d : ℝ)))
    (hε : 0 ≤ ε) (hεone : ε < 1)
    (hsm : SmoothAt (latticeImage S.symm.toContinuousLinearMap
      (numberFieldModularLattice K b q A)) ε 1) :
    (shiftedLatticeGaussian (numberFieldModularLattice K b q A) S c).toOuterMeasure
      {x | ((integralKernelEquiv K b q A).symm x).1 ∈
        residueColumnEvent (Ideal.Quotient.mk I) U} ≤
      ENNReal.ofReal (numberFieldGaussianPartition K k σ *
        ZLattice.covolume (latticeImage S.symm.toContinuousLinearMap
          (numberFieldModularLattice K b q A)) /
        ((1 - Real.exp (-((m : ℝ) * d) / 32)) * (1 - ε))) := by
  let L := numberFieldModularLattice K b q A
  let N := residueColumnLattice K b (Ideal.Quotient.mk I) U
  have hq : (Ideal.absNorm I : ℤ) ≠ 0 := by exact_mod_cast hI
  have hchar : ((Ideal.absNorm I : ℤ) : (𝓞 K) ⧸ I) = 0 := by
    have h := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.absNorm_mem I)
    simpa only [map_natCast, Int.cast_natCast] using h
  let : IsZLattice ℝ N := residueColumnLattice_full K b (Ideal.Quotient.mk I) U _ hq hchar
  let : MeasurableSpace L := ⊤
  let : DiscreteTopology (latticeImage S.symm.toContinuousLinearMap L) :=
    latticeImage_discrete S.symm L
  let : IsZLattice ℝ (latticeImage S.symm.toContinuousLinearMap L) :=
    ⟨latticeImage_equiv_span_top L (IsZLattice.span_top (K := ℝ) (L := L)) S.symm⟩
  have hmass : latticeGaussianPartition N S ≤
      numberFieldGaussianPartition K k σ / (1 - Real.exp (-((m : ℝ) * d) / 32)) := by
    have h := prime_ideal_residue_mass_of_width K b I hI U S hm hkm hσ hS hwidth
    unfold latticeGaussianPartition
    rw [← (residueColumnLatticeEquiv K b (Ideal.Quotient.mk I) U).tsum_eq]
    exact h
  have h := shiftedLatticeGaussian_submodule_probability_of_smoothAt L N S c hε hεone hsm
  have hc : 0 ≤ ZLattice.covolume (latticeImage S.symm.toContinuousLinearMap L) :=
    (ZLattice.covolume_pos _ volume).le
  have hbound := h.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hmass hc) (sub_nonneg.mpr hεone.le))
  have he : sublatticeEvent L N = {x : L | ((integralKernelEquiv K b q A).symm x).1 ∈
      residueColumnEvent (Ideal.Quotient.mk I) U} := by
    ext x
    constructor
    · rintro ⟨v, hv, hvx⟩
      have hxv : v = ((integralKernelEquiv K b q A).symm x).1 := by
        apply canonicalEuclideanEmbedding_injective K b (m + k)
        rw [hvx]
        exact ((integralKernelEquiv_coe K b q A _).symm.trans
          (congrArg (fun z : L => (z : Euclidean ((m + k) * d)))
            ((integralKernelEquiv K b q A).apply_symm_apply x))).symm
      change ((integralKernelEquiv K b q A).symm x).1 ∈ residueColumnModule (Ideal.Quotient.mk I) U
      rwa [← hxv]
    · intro hx
      refine ⟨((integralKernelEquiv K b q A).symm x).1, hx, ?_⟩
      exact (integralKernelEquiv_coe K b q A _).symm.trans
        (congrArg (fun z : L => (z : Euclidean ((m + k) * d)))
          ((integralKernelEquiv K b q A).apply_symm_apply x))
  rw [he] at hbound
  have hp := ENNReal.ofReal_le_ofReal hbound
  rw [Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _),
    PMF.toMeasure_apply_eq_toOuterMeasure] at hp
  convert hp using 1
  congr 1
  dsimp only [L]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The diagonal determinant discharges the lattice-volume term for the actual
paper hint shape, for every public matrix and every shift center. -/
theorem paper_shifted_kernel_prime_residue_probability (b : Basis (Fin d) ℤ (𝓞 K))
    (q : ℕ) [NeZero q] (A : Matrix (Fin n) (Fin (m + k)) (ResidueRing K q))
    (I : Ideal (𝓞 K)) [I.IsMaximal] (hI : Ideal.absNorm I ≠ 0)
    (U : Matrix (Fin (m + k)) (Fin k) ((𝓞 K) ⧸ I))
    (c : Euclidean ((m + k) * d)) (hm : 0 < m) (hkm : 64 * k ≤ m)
    {s₁ s₂ ε : ℝ} (h₁ : 0 < s₁) (h₂ : 0 < s₂) (hs : s₁ ≤ s₂)
    (hwidth : s₂ * Real.sqrt m ≤ (Ideal.absNorm I : ℝ) ^ (1 / (d : ℝ)))
    (hε : 0 ≤ ε) (hεone : ε < 1)
    (hsm : SmoothAt (latticeImage
      (paperHintShape K b m k h₁.ne' h₂.ne').symm.toContinuousLinearMap
      (numberFieldModularLattice K b q A)) ε 1) :
    (shiftedLatticeGaussian (numberFieldModularLattice K b q A)
      (paperHintShape K b m k h₁.ne' h₂.ne') c).toOuterMeasure
      {x | ((integralKernelEquiv K b q A).symm x).1 ∈
        residueColumnEvent (Ideal.Quotient.mk I) U} ≤
      ENNReal.ofReal (numberFieldGaussianPartition K k s₂ * (q : ℝ) ^ (d * n) *
        Real.sqrt |(NumberField.discr K : ℝ)| ^ (m + k) /
        ((s₁ ^ (m * d) * s₂ ^ (k * d)) *
          (1 - Real.exp (-((m : ℝ) * d) / 32)) * (1 - ε))) := by
  have h := shifted_kernel_prime_residue_probability K b q A I hI U
    (paperHintShape K b m k h₁.ne' h₂.ne') c hm hkm h₂
    (paperHintShape_norm_le K b m k h₁ h₂ hs) hwidth hε hεone hsm
  apply h.trans
  apply ENNReal.ofReal_le_ofReal
  have hd : (0 : ℝ) < d := Nat.cast_pos.mpr (integralBasis_dimension_pos K b)
  have htail : 0 < 1 - Real.exp (-((m : ℝ) * d) / 32) := by
    apply sub_pos.mpr
    apply Real.exp_lt_one_iff.mpr
    have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
    exact div_neg_of_neg_of_pos (neg_neg_of_pos (mul_pos hmR hd)) (by norm_num)
  have hv := paperHint_whitened_covolume_le K b m k n q A h₁ h₂
  have hh := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hv (numberFieldGaussianPartition_pos K b k s₂ h₂.ne').le)
    (mul_pos htail (sub_pos.mpr hεone)).le
  convert hh using 1
  · rfl
  · simp only [div_eq_mul_inv, mul_inv_rev]
    ring

/-- The paper's width window makes the exact diagonal mass ratio exponentially
small. The second width cancels with its block in the volume determinant. -/
theorem paper_gaussian_independence_ratio (b : Basis (Fin d) ℤ (𝓞 K))
    (hGram : ∀ i j, canonicalGram K b i j = if i = j then (d : ℝ) else 0)
    {q g : ℕ} (hq : 1 ≤ q) (hkm : k < m) {u s₁ s₂ : ℝ}
    (h₁ : 0 < s₁) (h₂ : 0 < s₂) (hs : s₁ ≤ s₂)
    (hw : ArithmeticWindow d m n k q g u s₁ s₂) :
    numberFieldGaussianPartition K k s₂ * (q : ℝ) ^ (d * n) *
      Real.sqrt |(NumberField.discr K : ℝ)| ^ (m + k) /
      (s₁ ^ (m * d) * s₂ ^ (k * d)) ≤ (1 / 2 : ℝ) ^ ((m - k) * d) := by
  have hd := integralBasis_dimension_pos K b
  have hx : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hd)
  have hfloor : independenceWidthFloor d m n k q u ≤ s₁ :=
    (le_max_right _ _).trans (hw.2 s₁ (by simp)).1
  have hscale := (independenceWidthFloor_ge_twice_sqrt d m n k q hkm hq hw.1).trans hfloor
  have hpart := numberFieldGaussianPartition_le_of_diagonal K b (Nat.cast_pos.mpr hd)
    hGram k (show Real.sqrt (d : ℝ) ≤ s₂ by linarith)
  calc
    _ ≤ (2 * s₂ / Real.sqrt d) ^ (k * d) * (q : ℝ) ^ (d * n) *
        Real.sqrt |(NumberField.discr K : ℝ)| ^ (m + k) /
        (s₁ ^ (m * d) * s₂ ^ (k * d)) := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpart (by positivity)) (by positivity))
        (mul_pos (pow_pos h₁ _) (pow_pos h₂ _)).le
    _ = 2 ^ (k * d) * (q : ℝ) ^ (d * n) * (Real.sqrt d / s₁) ^ (m * d) := by
      rw [canonical_discr_sqrt_of_diagonal K b hGram]
      exact diagonal_mass_ratio m k d hx.ne' h₁.ne' h₂.ne'
    _ ≤ _ := arithmeticWindow_independence_ratio hd hkm hq hw

/-- A numerical per-span estimate, retaining only the modular smoothing premise
and the actual prime-ideal width ceiling from the reference's factorization. -/
theorem paper_prime_residue_probability_of_window (b : Basis (Fin d) ℤ (𝓞 K))
    (hGram : ∀ i j, canonicalGram K b i j = if i = j then (d : ℝ) else 0)
    (q : ℕ) [NeZero q] (A : Matrix (Fin n) (Fin (m + k)) (ResidueRing K q))
    (I : Ideal (𝓞 K)) [I.IsMaximal] (hI : Ideal.absNorm I ≠ 0)
    (U : Matrix (Fin (m + k)) (Fin k) ((𝓞 K) ⧸ I))
    (c : Euclidean ((m + k) * d)) (hm : 0 < m) (hkm : 64 * k ≤ m)
    {g : ℕ} {u s₁ s₂ ε : ℝ} (h₁ : 0 < s₁) (h₂ : 0 < s₂) (hs : s₁ ≤ s₂)
    (hw : ArithmeticWindow d m n k q g u s₁ s₂)
    (hwidth : s₂ * Real.sqrt m ≤ (Ideal.absNorm I : ℝ) ^ (1 / (d : ℝ)))
    (hε : 0 ≤ ε) (hεone : ε < 1)
    (hsm : SmoothAt (latticeImage
      (paperHintShape K b m k h₁.ne' h₂.ne').symm.toContinuousLinearMap
      (numberFieldModularLattice K b q A)) ε 1) :
    (shiftedLatticeGaussian (numberFieldModularLattice K b q A)
      (paperHintShape K b m k h₁.ne' h₂.ne') c).toOuterMeasure
      {x | ((integralKernelEquiv K b q A).symm x).1 ∈
        residueColumnEvent (Ideal.Quotient.mk I) U} ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ ((m - k) * d) /
        ((1 - Real.exp (-((m : ℝ) * d) / 32)) * (1 - ε))) := by
  have h := paper_shifted_kernel_prime_residue_probability K b q A I hI U c hm hkm
    h₁ h₂ hs hwidth hε hεone hsm
  apply h.trans
  apply ENNReal.ofReal_le_ofReal
  have hratio := paper_gaussian_independence_ratio K b hGram
    (Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)) (by omega : k < m) h₁ h₂ hs hw
  have he :
      numberFieldGaussianPartition K k s₂ * (q : ℝ) ^ (d * n) *
        Real.sqrt |(NumberField.discr K : ℝ)| ^ (m + k) /
        (s₁ ^ (m * d) * s₂ ^ (k * d) * (1 - Real.exp (-((m : ℝ) * d) / 32)) * (1 - ε)) =
      (numberFieldGaussianPartition K k s₂ * (q : ℝ) ^ (d * n) *
        Real.sqrt |(NumberField.discr K : ℝ)| ^ (m + k) / (s₁ ^ (m * d) * s₂ ^ (k * d))) /
        ((1 - Real.exp (-((m : ℝ) * d) / 32)) * (1 - ε)) := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [he]
  exact div_le_div_of_nonneg_right hratio
    (mul_pos (residue_tail_gap_pos (integralBasis_dimension_pos K b) hm) (sub_pos.mpr hεone)).le

def primeIndependentHints (I : Ideal (𝓞 K)) [I.IsMaximal]
    (H : Matrix (Fin (m + k)) (Fin k) (𝓞 K)) : Prop :=
  LinearIndependent ((𝓞 K) ⧸ I) (fun j i => Ideal.Quotient.mk I (H i j))

/-- Independence of the actual shifted Gaussian hints in one residue field. -/
theorem paper_modularHintLaw_prime_independence (b : Basis (Fin d) ℤ (𝓞 K))
    (hGram : ∀ i j, canonicalGram K b i j = if i = j then (d : ℝ) else 0)
    (q : ℕ) [NeZero q] (A : Matrix (Fin n) (Fin (m + k)) (ResidueRing K q))
    (I : Ideal (𝓞 K)) [I.IsMaximal] (hI : Ideal.absNorm I ≠ 0)
    (centers : Fin k → Euclidean ((m + k) * d)) (hm : 0 < m) (hkm : 64 * k ≤ m)
    {g : ℕ} {u s₁ s₂ ε : ℝ} (h₁ : 0 < s₁) (h₂ : 0 < s₂) (hs : s₁ ≤ s₂)
    (hw : ArithmeticWindow d m n k q g u s₁ s₂)
    (hwidth : s₂ * Real.sqrt m ≤ (Ideal.absNorm I : ℝ) ^ (1 / (d : ℝ)))
    (hε : 0 ≤ ε) (hεone : ε < 1)
    (hsm : SmoothAt (latticeImage
      (paperHintShape K b m k h₁.ne' h₂.ne').symm.toContinuousLinearMap
      (numberFieldModularLattice K b q A)) ε 1) :
    (modularHintLaw K b q A (paperHintShape K b m k h₁.ne' h₂.ne') centers).toOuterMeasure
      {H | ¬ primeIndependentHints K I H} ≤
      ENNReal.ofReal ((k : ℝ) * (1 / 2 : ℝ) ^ ((m - k) * d) /
        ((1 - Real.exp (-((m : ℝ) * d) / 32)) * (1 - ε))) := by
  let L := numberFieldModularLattice K b q A
  let S := paperHintShape K b m k h₁.ne' h₂.ne'
  let f : L → (Fin (m + k) → (𝓞 K) ⧸ I) :=
    fun x i => Ideal.Quotient.mk I (((integralKernelEquiv K b q A).symm x).1 i)
  let δ := (1 / 2 : ℝ) ^ ((m - k) * d) /
    ((1 - Real.exp (-((m : ℝ) * d) / 32)) * (1 - ε))
  have hδ : 0 ≤ δ := div_nonneg (by positivity)
    (mul_pos (residue_tail_gap_pos (integralBasis_dimension_pos K b) hm) (sub_pos.mpr hεone)).le
  have hspan (j : Fin k) (r : ℕ) (hr : r < k) (v : Fin r → (Fin (m + k) → (𝓞 K) ⧸ I)) :
      (shiftedLatticeGaussian L S (centers j)).toOuterMeasure
        {x | f x ∈ Submodule.span ((𝓞 K) ⧸ I) (Set.range v)} ≤ ENNReal.ofReal δ := by
    have hh := paper_prime_residue_probability_of_window K b hGram q A I hI
      (paddedColumns (k := k) v) (centers j) hm hkm h₁ h₂ hs hw hwidth hε hεone hsm
    apply (OuterMeasure.mono _ ?_).trans hh
    intro x hx
    exact span_le_paddedColumns_range v hr.le hx
  have h := independentProduct_linearIndependent_failure f hδ k
    (fun j => shiftedLatticeGaussian L S (centers j)) hspan
  rw [modularHintLaw, PMF.toOuterMeasure_map_apply]
  change (independentProduct (fun j => shiftedLatticeGaussian L S (centers j))).toOuterMeasure
    {z | ¬ LinearIndependent ((𝓞 K) ⧸ I) (fun j => f (z j))} ≤ _
  simpa only [δ, mul_div_assoc] using h

variable {g : ℕ}

def independentHintsAtPrimes (I : Fin g → Ideal (𝓞 K)) [∀ j, (I j).IsMaximal]
    (H : Matrix (Fin (m + k)) (Fin k) (𝓞 K)) : Prop :=
  ∀ j, primeIndependentHints K (I j) H

/-- The supplied norm identities convert the numerical width ceiling to every
residue field, and a union bound accounts for the whole family of factors. -/
theorem paper_modularHintLaw_independence (b : Basis (Fin d) ℤ (𝓞 K))
    (hGram : ∀ i j, canonicalGram K b i j = if i = j then (d : ℝ) else 0)
    (q : ℕ) [NeZero q] (A : Matrix (Fin n) (Fin (m + k)) (ResidueRing K q))
    (I : Fin g → Ideal (𝓞 K)) [∀ j, (I j).IsMaximal]
    (hg : 0 < g) (hNorm : ∀ j, Ideal.absNorm (I j) ^ g = q ^ d)
    (centers : Fin k → Euclidean ((m + k) * d)) (hm : 0 < m) (hkm : 64 * k ≤ m)
    {u s₁ s₂ ε : ℝ} (h₁ : 0 < s₁) (h₂ : 0 < s₂) (hs : s₁ ≤ s₂)
    (hw : ArithmeticWindow d m n k q g u s₁ s₂)
    (hε : 0 ≤ ε) (hεone : ε < 1)
    (hsm : SmoothAt (latticeImage
      (paperHintShape K b m k h₁.ne' h₂.ne').symm.toContinuousLinearMap
      (numberFieldModularLattice K b q A)) ε 1) :
    (modularHintLaw K b q A (paperHintShape K b m k h₁.ne' h₂.ne') centers).toOuterMeasure
      {H | ¬ independentHintsAtPrimes K I H} ≤
      ENNReal.ofReal ((g : ℝ) * k * (1 / 2 : ℝ) ^ ((m - k) * d) /
        ((1 - Real.exp (-((m : ℝ) * d) / 32)) * (1 - ε))) := by
  let p := modularHintLaw K b q A (paperHintShape K b m k h₁.ne' h₂.ne') centers
  let δ := (k : ℝ) * (1 / 2 : ℝ) ^ ((m - k) * d) /
    ((1 - Real.exp (-((m : ℝ) * d) / 32)) * (1 - ε))
  have hd := integralBasis_dimension_pos K b
  have hδ : 0 ≤ δ := div_nonneg (by positivity)
    (mul_pos (residue_tail_gap_pos hd hm) (sub_pos.mpr hεone)).le
  have hEach (j : Fin g) : p.toOuterMeasure {H | ¬ primeIndependentHints K (I j) H} ≤
      ENNReal.ofReal δ := by
    have hI : Ideal.absNorm (I j) ≠ 0 := by
      intro hz
      have hzq := hNorm j
      rw [hz, zero_pow hg.ne'] at hzq
      exact pow_ne_zero d (NeZero.ne q) hzq.symm
    exact paper_modularHintLaw_prime_independence K b hGram q A (I j) hI centers hm hkm
      h₁ h₂ hs hw (arithmeticWindow_ideal_ceiling hd hg hm (hNorm j) hw) hε hεone hsm
  have hEvent : {H : Matrix (Fin (m + k)) (Fin k) (𝓞 K) | ¬ independentHintsAtPrimes K I H} =
      ⋃ j : Fin g, {H | ¬ primeIndependentHints K (I j) H} := by
    ext H
    simp only [independentHintsAtPrimes, Set.mem_ofPred_eq, Set.mem_iUnion, not_forall]
  rw [hEvent]
  apply (measure_iUnion_fintype_le p.toOuterMeasure _).trans
  apply (Finset.sum_le_sum (fun j _ => hEach j)).trans
  rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => hδ)]
  apply ENNReal.ofReal_le_ofReal
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, δ]
  exact le_of_eq (by ring)

end NumberFields

end SISToKSIS
