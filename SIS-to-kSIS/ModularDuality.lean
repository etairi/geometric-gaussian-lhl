import «SIS-to-kSIS».ModularLattices
import GeometricGaussianLHL.ShapingGeometry
import Mathlib.NumberTheory.Cyclotomic.Gal

/-!
# Duals of modular kernel lattices

An integral map's congruence kernel has dual equal to the ambient dual plus
its scaled adjoint image. Finite coefficient representatives cover this dual.
Removing the zero vector in every coset gives a mass upper bound even when
rank deficiency makes the coset representatives non-unique.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Module NumberField GeometricGaussianLHL
open scoped Matrix ENNReal Classical
namespace SISToKSIS
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ E] in
theorem fullLattice_dual_eq_bilin (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L] :
    latticeDual L = LinearMap.BilinForm.dualSubmodule (innerₗ E) L := by
  simp [latticeDual, IsZLattice.span_top (K := ℝ) (L := L)]

theorem fullLattice_dual_dual (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L] : latticeDual (latticeDual L) = L := by
  let : DiscreteTopology (latticeDual L) := fullLattice_dual_discrete L
  let : IsZLattice ℝ (latticeDual L) := ⟨fullLattice_dual_span L⟩
  rw [fullLattice_dual_eq_bilin, fullLattice_dual_eq_bilin]
  let b := (Module.finBasis ℤ L).ofZLatticeBasis ℝ L
  have hb : Submodule.span ℤ (Set.range b) = L :=
    (Module.finBasis ℤ L).ofZLatticeBasis_span ℝ
  rw [← hb]
  apply LinearMap.BilinForm.dualSubmodule_dualSubmodule_of_basis
  · constructor
    · intro x hx
      exact inner_self_eq_zero.mp (hx x)
    · intro x hx
      exact inner_self_eq_zero.mp (hx x)
  · exact ⟨fun x y => (real_inner_comm x y).symm⟩

/-- Pull back the scaled output lattice, retaining the integral domain lattice. -/
def modulusPullback (L : Submodule ℤ E) (M : Submodule ℤ F)
    (T : E →L[ℝ] F) (q : ℤ) : Submodule ℤ E :=
  L ⊓ M.comap (((q : ℝ)⁻¹ • T).toLinearMap.restrictScalars ℤ)

/-- The integral dual and the scaled adjoint image generate the congruence dual. -/
def modulusDual (L : Submodule ℤ E) (M : Submodule ℤ F)
    (T : E →L[ℝ] F) (q : ℤ) : Submodule ℤ E :=
  latticeDual L ⊔ latticeImage ((q : ℝ)⁻¹ • T.adjoint) (latticeDual M)

theorem integral_adjoint_mem_dual (L : Submodule ℤ E) (M : Submodule ℤ F)
    [DiscreteTopology L] [IsZLattice ℝ L] (T : E →L[ℝ] F) (hT : ∀ x ∈ L, T x ∈ M)
    {y : F} (hy : y ∈ latticeDual M) : T.adjoint y ∈ latticeDual L := by
  rw [mem_latticeDual]
  refine ⟨by rw [IsZLattice.span_top (K := ℝ) (L := L)]; trivial, ?_⟩
  intro x hx
  rw [ContinuousLinearMap.adjoint_inner_left]
  exact (mem_latticeDual.mp hy).2 _ (hT x hx)

theorem modulusDual_scaled_mem (L : Submodule ℤ E) (M : Submodule ℤ F)
    [DiscreteTopology L] [IsZLattice ℝ L] (T : E →L[ℝ] F) (hT : ∀ x ∈ L, T x ∈ M)
    {q : ℤ} (hq : q ≠ 0) {x : E} (hx : x ∈ modulusDual L M T q) :
    (q : ℝ) • x ∈ latticeDual L := by
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨w, hw, rfl⟩ := hv
  rw [smul_add]
  apply (latticeDual L).add_mem
  · simpa only [Int.cast_smul_eq_zsmul] using (latticeDual L).smul_mem q hu
  · change (q : ℝ) • ((q : ℝ)⁻¹ • T.adjoint w) ∈ latticeDual L
    rw [smul_smul, mul_inv_cancel₀ hqR, one_smul]
    exact integral_adjoint_mem_dual L M T hT hw

theorem modulusDual_discrete (L : Submodule ℤ E) (M : Submodule ℤ F)
    [DiscreteTopology L] [IsZLattice ℝ L]
    (T : E →L[ℝ] F) (hT : ∀ x ∈ L, T x ∈ M) {q : ℤ} (hq : q ≠ 0) :
    DiscreteTopology (modulusDual L M T q) := by
  let : DiscreteTopology (latticeDual L) := fullLattice_dual_discrete L
  let f : modulusDual L M T q → latticeDual L :=
    fun x => ⟨(q : ℝ) • (x : E), modulusDual_scaled_mem L M T hT hq x.2⟩
  apply DiscreteTopology.of_continuous_injective (f := f)
  · exact (continuous_const.smul continuous_subtype_val).subtype_mk _
  · intro x y h
    apply Subtype.ext
    exact (smul_right_injective E (show (q : ℝ) ≠ 0 by exact_mod_cast hq))
      (congrArg Subtype.val h)

theorem modulusDual_span (L : Submodule ℤ E) (M : Submodule ℤ F)
    [DiscreteTopology L] [IsZLattice ℝ L] (T : E →L[ℝ] F) (q : ℤ) :
    Submodule.span ℝ (modulusDual L M T q : Set E) = ⊤ := by
  apply top_unique
  rw [← fullLattice_dual_span L]
  apply Submodule.span_mono
  intro x hx
  exact (show latticeDual L ≤ modulusDual L M T q from le_sup_left) hx

theorem modulusDual_dual (L : Submodule ℤ E) (M : Submodule ℤ F)
    [DiscreteTopology L] [IsZLattice ℝ L] [DiscreteTopology M] [IsZLattice ℝ M]
    (T : E →L[ℝ] F) (q : ℤ) :
    latticeDual (modulusDual L M T q) = modulusPullback L M T q := by
  ext x
  rw [mem_latticeDual]
  constructor
  · intro hx
    refine ⟨?_, ?_⟩
    · change x ∈ L
      rw [← fullLattice_dual_dual L, mem_latticeDual]
      exact ⟨by rw [fullLattice_dual_span L]; trivial,
        fun y hy => hx.2 y ((show latticeDual L ≤ modulusDual L M T q from le_sup_left) hy)⟩
    · change (q : ℝ)⁻¹ • T x ∈ M
      rw [← fullLattice_dual_dual M, mem_latticeDual]
      refine ⟨by rw [fullLattice_dual_span M]; trivial, ?_⟩
      intro y hy
      obtain ⟨z, hz⟩ := hx.2 (((q : ℝ)⁻¹ • T.adjoint) y)
        ((show latticeImage ((q : ℝ)⁻¹ • T.adjoint) (latticeDual M) ≤
          modulusDual L M T q from le_sup_right) ⟨y, hy, rfl⟩)
      refine ⟨z, hz.trans ?_⟩
      simp only [smul_apply, inner_smul_right,
        ContinuousLinearMap.adjoint_inner_right, real_inner_smul_left]
  · rintro ⟨hxL, hxM⟩
    refine ⟨by rw [modulusDual_span L M T q]; trivial, ?_⟩
    intro y hy
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hy
    obtain ⟨w, hw, rfl⟩ := hv
    obtain ⟨a, ha⟩ := (mem_latticeDual.mp hu).2 x hxL
    obtain ⟨c, hc⟩ := (mem_latticeDual.mp hw).2 _ hxM
    refine ⟨a + c, ?_⟩
    change (↑(a + c) : ℝ) = inner ℝ x (u + (q : ℝ)⁻¹ • T.adjoint w)
    rw [Int.cast_add, ha, hc, inner_add_right, inner_smul_right,
      ContinuousLinearMap.adjoint_inner_right]
    change inner ℝ u x + inner ℝ w ((q : ℝ)⁻¹ • T x) = _
    rw [inner_smul_right, real_inner_comm u x, real_inner_comm w (T x)]

theorem modulusPullback_dual (L : Submodule ℤ E) (M : Submodule ℤ F)
    [DiscreteTopology L] [IsZLattice ℝ L] [DiscreteTopology M] [IsZLattice ℝ M]
    (T : E →L[ℝ] F) (hT : ∀ x ∈ L, T x ∈ M) {q : ℤ} (hq : q ≠ 0) :
    latticeDual (modulusPullback L M T q) = modulusDual L M T q := by
  let : DiscreteTopology (modulusDual L M T q) := modulusDual_discrete L M T hT hq
  let : IsZLattice ℝ (modulusDual L M T q) := ⟨modulusDual_span L M T q⟩
  rw [← modulusDual_dual L M T q, fullLattice_dual_dual]

section ResidueRepresentatives
variable {V : Type*} [AddCommGroup V] {r : ℕ}

/-- Coefficient representatives for the quotient of a free integral module by `q`. -/
def latticeResidueRepresentative (b : Basis (Fin r) ℤ V) (q : ℕ)
    (s : Fin r → ZMod q) : V := b.equivFun.symm (fun i => ((s i).val : ℤ))

theorem latticeResidueRepresentative_decomposition (b : Basis (Fin r) ℤ V)
    (q : ℕ) [NeZero q] (v : V) :
    ∃ s : Fin r → ZMod q, ∃ w : V,
      v = latticeResidueRepresentative b q s + (q : ℤ) • w := by
  refine ⟨fun i => (b.equivFun v i : ZMod q),
    b.equivFun.symm (fun i => b.equivFun v i / (q : ℤ)), ?_⟩
  apply b.equivFun.injective
  ext i
  simp only [latticeResidueRepresentative, map_add, map_smul,
    LinearEquiv.apply_symm_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    ZMod.val_intCast]
  exact (Int.emod_add_mul_ediv _ _).symm
end ResidueRepresentatives

theorem modulusDual_finite_cover_representatives
    (L : Submodule ℤ E) (M : Submodule ℤ F)
    [DiscreteTopology L] [IsZLattice ℝ L]
    (T : E →L[ℝ] F) (hT : ∀ x ∈ L, T x ∈ M) (q : ℕ) [NeZero q]
    {ι : Type*} (rep : ι → latticeDual M)
    (hrep : ∀ v : latticeDual M, ∃ s, ∃ w : latticeDual M, v = rep s + (q : ℤ) • w)
    {x : E} (hx : x ∈ modulusDual L M T q) :
    ∃ s, ∃ u : latticeDual L,
      x = (u : E) + (q : ℝ)⁻¹ • T.adjoint (rep s : F) := by
  have hq : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨w, hw, rfl⟩ := hv
  obtain ⟨s, z, hz⟩ := hrep (⟨w, hw⟩ : latticeDual M)
  refine ⟨s, ⟨u + T.adjoint z, (latticeDual L).add_mem hu
    (integral_adjoint_mem_dual L M T hT z.2)⟩, ?_⟩
  have hw' := congrArg (fun v : latticeDual M => (v : F)) hz
  change w = (rep s : F) + (q : ℤ) • (z : F) at hw'
  have hqsmul : (q : ℤ) • (z : F) = (q : ℝ) • (z : F) := by
    simpa only [Int.cast_natCast] using (Int.cast_smul_eq_zsmul ℝ (q : ℤ) (z : F)).symm
  rw [hqsmul] at hw'
  change u + (↑(q : ℤ) : ℝ)⁻¹ • T.adjoint w = _
  rw [hw', map_add, map_smul]
  simp only [Int.cast_natCast, smul_add, smul_smul, inv_mul_cancel₀ hq, one_smul]
  abel


theorem modulusDual_finite_cover (L : Submodule ℤ E) (M : Submodule ℤ F)
    [DiscreteTopology L] [IsZLattice ℝ L]
    (T : E →L[ℝ] F) (hT : ∀ x ∈ L, T x ∈ M) (q : ℕ) [NeZero q]
    {r : ℕ} (b : Basis (Fin r) ℤ (latticeDual M))
    {x : E} (hx : x ∈ modulusDual L M T q) :
    ∃ s : Fin r → ZMod q, ∃ u : latticeDual L,
      x = (u : E) + (q : ℝ)⁻¹ • T.adjoint ((latticeResidueRepresentative b q s : latticeDual M) : F) := by
  exact modulusDual_finite_cover_representatives L M T hT q
    (latticeResidueRepresentative b q) (latticeResidueRepresentative_decomposition b q) hx

/-- Gaussian mass of a translated lattice, with the ambient zero removed. -/
def nonzeroCosetMass (L : Submodule ℤ E) (t : ℝ) (c : E) : ℝ≥0∞ :=
  ∑' u : L, if (u : E) + c = 0 then 0 else ENNReal.ofReal (gaussianWeight t ((u : E) + c))

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem nonzero_mass_le_finite_coset_cover {ι : Type*} [Fintype ι]
    (L D : Submodule ℤ E) (hLD : L ≤ D) (c : ι → E) (hc : ∀ i, c i ∈ D)
    (hcover : ∀ x : D, ∃ i : ι, ∃ u : L, (x : E) = (u : E) + c i) (t : ℝ) :
    (∑' x : D, if x = 0 then 0 else ENNReal.ofReal (gaussianWeight t (x : E))) ≤
      ∑ i, nonzeroCosetMass L t (c i) := by
  classical
  let f : ι × L → D := fun v => ⟨(v.2 : E) + c v.1, D.add_mem (hLD v.2.2) (hc v.1)⟩
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨i, u, h⟩ := hcover x
    exact ⟨(i, u), Subtype.ext h.symm⟩
  have h := ENNReal.tsum_le_tsum_comp_of_surjective hf
    (fun x : D => if x = 0 then 0 else ENNReal.ofReal (gaussianWeight t (x : E)))
  apply h.trans_eq
  rw [ENNReal.tsum_prod', tsum_fintype]
  apply Finset.sum_congr rfl
  intro i _
  unfold nonzeroCosetMass
  apply tsum_congr
  intro u
  have he : f (i, u) = 0 ↔ (u : E) + c i = 0 := Subtype.ext_iff
  simp only [he]
  rfl

theorem modulusPullback_nonzeroDualMass_le
    (L : Submodule ℤ E) (M : Submodule ℤ F)
    [DiscreteTopology L] [IsZLattice ℝ L] [DiscreteTopology M] [IsZLattice ℝ M]
    (T : E →L[ℝ] F) (hT : ∀ x ∈ L, T x ∈ M) (q : ℕ) [NeZero q]
    {r : ℕ} (b : Basis (Fin r) ℤ (latticeDual M)) (t : ℝ) :
    nonzeroDualMass (modulusPullback L M T q) t ≤
      ∑ s : Fin r → ZMod q, nonzeroCosetMass (latticeDual L) t
        ((q : ℝ)⁻¹ • T.adjoint ((latticeResidueRepresentative b q s : latticeDual M) : F)) := by
  classical
  rw [nonzeroDualMass, modulusPullback_dual L M T hT (by exact_mod_cast NeZero.ne q)]
  apply nonzero_mass_le_finite_coset_cover
  · exact le_sup_left
  · intro s
    apply (show latticeImage ((↑(q : ℤ) : ℝ)⁻¹ • T.adjoint) (latticeDual M) ≤
      modulusDual L M T q from le_sup_right)
    refine ⟨((latticeResidueRepresentative b q s : latticeDual M) : F),
      (latticeResidueRepresentative b q s).2, ?_⟩
    simp only [Int.cast_natCast]
    rfl
  · intro x
    exact modulusDual_finite_cover L M T hT q b x.2


/-- A contraction of the whitening map compares its dual mass to a scalar width. -/
theorem nonzeroDualMass_image_one_le (L : Submodule ℤ E) (T : E →L[ℝ] F)
    {t : ℝ} (ht : 0 ≤ t) (hT : ‖T‖ * t ≤ 1) :
    nonzeroDualMass (latticeImage T L) 1 ≤ nonzeroDualMass L t :=
  (nonzeroDualMass_antitone _ (mul_nonneg (norm_nonneg T) ht) hT).trans
    (nonzeroDualMass_metric_change T L t)

section NumberFields
variable (K : Type*) [Field K] [NumberField K] {d m n : ℕ}

omit [NumberField K] in
theorem modularKernel_lift_iff (q : ℕ) (A : Matrix (Fin n) (Fin m) (𝓞 K))
    (v : Fin m → 𝓞 K) :
    v ∈ modularKernel (residueMap K q) (A.map (residueMap K q)) ↔
      ∃ w : Fin n → 𝓞 K, A *ᵥ v = (q : ℤ) • w := by
  classical
  rw [mem_modularKernel]
  have he : A.map (residueMap K q) *ᵥ (residueMap K q ∘ v) =
      residueMap K q ∘ (A *ᵥ v) := by
    funext i
    exact (RingHom.map_mulVec (residueMap K q) A v i).symm
  rw [he]
  constructor
  · intro h
    have hi (i : Fin n) : ∃ w : 𝓞 K, (A *ᵥ v) i = (q : 𝓞 K) * w := by
      have hz : residueMap K q ((A *ᵥ v) i) = 0 := congrFun h i
      exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hz)
    choose w hw using hi
    refine ⟨w, ?_⟩
    funext i
    simpa only [Pi.smul_apply, zsmul_eq_mul, Int.cast_natCast] using hw i
  · rintro ⟨w, hw⟩
    rw [hw]
    ext i
    simp [zsmul_eq_mul, residueMap_modulus]

theorem numberFieldModularLattice_eq_modulusPullback
    (b : Basis (Fin d) ℤ (𝓞 K)) (q : ℕ) [NeZero q]
    (A : Matrix (Fin n) (Fin m) (𝓞 K)) :
    numberFieldModularLattice K b q (A.map (residueMap K q)) =
      modulusPullback (canonicalEuclideanLattice K b m) (canonicalEuclideanLattice K b n)
        (canonicalEuclideanMatrix K b A).toContinuousLinearMap q := by
  have hq : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hsmul (w : Fin n → 𝓞 K) :
      canonicalEuclideanEmbedding K b n ((q : ℤ) • w) =
        (q : ℝ) • canonicalEuclideanEmbedding K b n w := by
    rw [map_smul]
    simpa only [Int.cast_natCast] using
      (Int.cast_smul_eq_zsmul ℝ (q : ℤ) (canonicalEuclideanEmbedding K b n w)).symm
  ext x
  constructor
  · intro hx
    obtain ⟨v, rfl⟩ := congruenceLattice_le _ _ hx
    have hv := (canonicalEmbedding_mem_modularLattice_iff K b q _ v).mp hx
    obtain ⟨w, hw⟩ := (modularKernel_lift_iff K q A v).mp hv
    refine ⟨⟨v, rfl⟩, ?_⟩
    change (↑(q : ℤ) : ℝ)⁻¹ • canonicalEuclideanMatrix K b A
      (canonicalEuclideanEmbedding K b m v) ∈ canonicalEuclideanLattice K b n
    rw [canonicalEuclideanMatrix_integer, hw, hsmul]
    simp only [Int.cast_natCast, smul_smul, inv_mul_cancel₀ hq, one_smul]
    exact ⟨w, rfl⟩
  · rintro ⟨⟨v, rfl⟩, hx⟩
    obtain ⟨w, hw⟩ := hx
    apply (canonicalEmbedding_mem_modularLattice_iff K b q _ v).mpr
    apply (modularKernel_lift_iff K q A v).mpr
    refine ⟨w, canonicalEuclideanEmbedding_injective K b n ?_⟩
    rw [hsmul, ← canonicalEuclideanMatrix_integer]
    change canonicalEuclideanEmbedding K b n w =
      (↑(q : ℤ) : ℝ)⁻¹ • canonicalEuclideanMatrix K b A
        (canonicalEuclideanEmbedding K b m v) at hw
    rw [hw]
    simp [smul_smul, hq]

theorem numberFieldModularLattice_dual_lift
    (b : Basis (Fin d) ℤ (𝓞 K)) (q : ℕ) [NeZero q]
    (A : Matrix (Fin n) (Fin m) (𝓞 K)) :
    latticeDual (numberFieldModularLattice K b q (A.map (residueMap K q))) =
      modulusDual (canonicalEuclideanLattice K b m) (canonicalEuclideanLattice K b n)
        (canonicalEuclideanMatrix K b A).toContinuousLinearMap q := by
  rw [numberFieldModularLattice_eq_modulusPullback]
  apply modulusPullback_dual
  · exact canonicalEuclideanMatrix_lattice K b A
  · exact_mod_cast NeZero.ne q

/-- Integral lifts used to express the finite quotient's Euclidean adjoint. -/
def residueMatrixLift (q : ℕ) (A : Matrix (Fin n) (Fin m) (ResidueRing K q)) :
    Matrix (Fin n) (Fin m) (𝓞 K) :=
  fun i j => (Ideal.Quotient.mk_surjective (A i j)).choose

omit [NumberField K] in
theorem residueMatrixLift_map (q : ℕ) (A : Matrix (Fin n) (Fin m) (ResidueRing K q)) :
    (residueMatrixLift K q A).map (residueMap K q) = A := by
  funext i j
  exact (Ideal.Quotient.mk_surjective (A i j)).choose_spec

/-- The dual formula holds for every public matrix, including matrices of deficient rank. -/
theorem numberFieldModularLattice_dual
    (b : Basis (Fin d) ℤ (𝓞 K)) (q : ℕ) [NeZero q]
    (A : Matrix (Fin n) (Fin m) (ResidueRing K q)) :
    latticeDual (numberFieldModularLattice K b q A) =
      modulusDual (canonicalEuclideanLattice K b m) (canonicalEuclideanLattice K b n)
        (canonicalEuclideanMatrix K b (residueMatrixLift K q A)).toContinuousLinearMap q := by
  have h := numberFieldModularLattice_dual_lift K b q (residueMatrixLift K q A)
  simpa only [residueMatrixLift_map] using h

theorem numberFieldModularLattice_nonzeroDualMass_le
    (b : Basis (Fin d) ℤ (𝓞 K)) (q : ℕ) [NeZero q]
    (A : Matrix (Fin n) (Fin m) (ResidueRing K q))
    {r : ℕ} (c : Basis (Fin r) ℤ (latticeDual (canonicalEuclideanLattice K b n))) (t : ℝ) :
    nonzeroDualMass (numberFieldModularLattice K b q A) t ≤
      ∑ s : Fin r → ZMod q, nonzeroCosetMass (latticeDual (canonicalEuclideanLattice K b m)) t
        ((q : ℝ)⁻¹ • (canonicalEuclideanMatrix K b (residueMatrixLift K q A)).toContinuousLinearMap.adjoint
          ((latticeResidueRepresentative c q s : latticeDual (canonicalEuclideanLattice K b n)) :
            Euclidean (n * d))) := by
  have h := modulusPullback_nonzeroDualMass_le (canonicalEuclideanLattice K b m)
    (canonicalEuclideanLattice K b n)
    (canonicalEuclideanMatrix K b (residueMatrixLift K q A)).toContinuousLinearMap
    (canonicalEuclideanMatrix_lattice K b (residueMatrixLift K q A)) q c t
  rw [← numberFieldModularLattice_eq_modulusPullback, residueMatrixLift_map] at h
  exact h

/-- The output dual has exactly `n*d` integral coordinates. -/
def canonicalEuclideanDualBasis (b : Basis (Fin d) ℤ (𝓞 K)) (n : ℕ) :
    Basis (Fin (n * d)) ℤ (latticeDual (canonicalEuclideanLattice K b n)) := by
  let : DiscreteTopology (latticeDual (canonicalEuclideanLattice K b n)) :=
    fullLattice_dual_discrete _
  let : IsZLattice ℝ (latticeDual (canonicalEuclideanLattice K b n)) :=
    ⟨fullLattice_dual_span _⟩
  exact fullLatticeIntegralBasis _

/-- The finite sum whose uniform-public expectation controls modular smoothing. -/
def modularDualCosetMass (b : Basis (Fin d) ℤ (𝓞 K)) (q : ℕ) [NeZero q]
    (A : Matrix (Fin n) (Fin m) (ResidueRing K q)) (t : ℝ) : ℝ≥0∞ :=
  ∑ s : Fin (n * d) → ZMod q,
    nonzeroCosetMass (latticeDual (canonicalEuclideanLattice K b m)) t
      ((q : ℝ)⁻¹ • (canonicalEuclideanMatrix K b (residueMatrixLift K q A)).toContinuousLinearMap.adjoint
        ((latticeResidueRepresentative (canonicalEuclideanDualBasis K b n) q s :
          latticeDual (canonicalEuclideanLattice K b n)) : Euclidean (n * d)))

theorem nonzeroDualMass_le_modularDualCosetMass
    (b : Basis (Fin d) ℤ (𝓞 K)) (q : ℕ) [NeZero q]
    (A : Matrix (Fin n) (Fin m) (ResidueRing K q)) (t : ℝ) :
    nonzeroDualMass (numberFieldModularLattice K b q A) t ≤ modularDualCosetMass K b q A t :=
  numberFieldModularLattice_nonzeroDualMass_le K b q A (canonicalEuclideanDualBasis K b n) t

theorem whitenedModularLattice_nonzeroDualMass_le
    (b : Basis (Fin d) ℤ (𝓞 K)) (q : ℕ) [NeZero q]
    (A : Matrix (Fin n) (Fin m) (ResidueRing K q))
    (S : Euclidean (m * d) ≃L[ℝ] Euclidean (m * d))
    {t : ℝ} (ht : 0 ≤ t) (hS : ‖S.symm.toContinuousLinearMap‖ * t ≤ 1) :
    nonzeroDualMass (latticeImage S.symm.toContinuousLinearMap
      (numberFieldModularLattice K b q A)) 1 ≤ modularDualCosetMass K b q A t :=
  (nonzeroDualMass_image_one_le _ _ ht hS).trans (nonzeroDualMass_le_modularDualCosetMass K b q A t)

end NumberFields

end SISToKSIS

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Module NumberField GeometricGaussianLHL
namespace SISToKSIS
variable (K : Type*) [Field K] [NumberField K] {d : ℕ}

theorem canonicalEuclideanLattice_scalarGram_image (b : Basis (Fin d) ℤ (𝓞 K))
    {c : ℝ} (hc : 0 < c) (hGram : ∀ i j, canonicalGram K b i j = if i = j then c else 0)
    (r : ℕ) :
    canonicalEuclideanLattice K b r = latticeImage
      ((euclideanScalarShape (r * d) (Real.sqrt c) (Real.sqrt_pos.mpr hc).ne').trans
        (scalarGramEuclideanIsometry K b hc hGram r).toContinuousLinearEquiv).toContinuousLinearMap
      (integerLattice (r * d)) := by
  let T := (euclideanScalarShape (r * d) (Real.sqrt c) (Real.sqrt_pos.mpr hc).ne').trans
    (scalarGramEuclideanIsometry K b hc hGram r).toContinuousLinearEquiv
  have hv (v : Fin r → 𝓞 K) :
      T (integerEmbedding (r * d) (ringPowerCoordinates b r v)) = canonicalEuclideanEmbedding K b r v := by
    change canonicalOrthonormalCoordinates K b r ((Real.sqrt c)⁻¹ •
      powerCanonicalEquiv K b r (Real.sqrt c • integerEmbedding (r * d) (ringPowerCoordinates b r v))) = _
    simp only [map_smul, smul_smul, inv_mul_cancel₀ (Real.sqrt_pos.mpr hc).ne', one_smul,
      powerCanonicalEquiv_integer]
    rfl
  ext x
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨integerEmbedding (r * d) (ringPowerCoordinates b r v), ⟨_, rfl⟩, hv v⟩
  · rintro ⟨y, ⟨z, rfl⟩, rfl⟩
    refine ⟨(ringPowerCoordinates b r).symm z, ?_⟩
    change canonicalEuclideanEmbedding K b r ((ringPowerCoordinates b r).symm z) =
      T (integerEmbedding (r * d) z)
    simpa only [LinearEquiv.apply_symm_apply] using (hv ((ringPowerCoordinates b r).symm z)).symm

theorem canonicalEuclideanLattice_scalarGram_dual (b : Basis (Fin d) ℤ (𝓞 K))
    {c : ℝ} (hc : 0 < c) (hGram : ∀ i j, canonicalGram K b i j = if i = j then c else 0)
    (r : ℕ) :
    latticeDual (canonicalEuclideanLattice K b r) =
      latticeImage (euclideanScalarShape (r * d) c⁻¹ (inv_ne_zero hc.ne')).toContinuousLinearMap
        (canonicalEuclideanLattice K b r) := by
  let e := scalarGramEuclideanIsometry K b hc hGram r
  let T := (euclideanScalarShape (r * d) (Real.sqrt c) (Real.sqrt_pos.mpr hc).ne').trans
    e.toContinuousLinearEquiv
  have hL : canonicalEuclideanLattice K b r = latticeImage T.toContinuousLinearMap (integerLattice (r * d)) :=
    canonicalEuclideanLattice_scalarGram_image K b hc hGram r
  have he : e.toContinuousLinearEquiv.symm.toContinuousLinearMap.adjoint =
      e.toContinuousLinearEquiv.toContinuousLinearMap := by
    exact congrArg ContinuousLinearEquiv.toContinuousLinearMap (inverseAdjointEquiv_isometry e)
  have hsym : T.symm.toContinuousLinearMap =
      ((Real.sqrt c)⁻¹ • ContinuousLinearMap.id ℝ (Euclidean (r * d))).comp
        e.toContinuousLinearEquiv.symm.toContinuousLinearMap := by
    ext x : 1
    rfl
  have hT : (inverseAdjointEquiv T).toContinuousLinearMap = c⁻¹ • T.toContinuousLinearMap := by
    ext x : 1
    change T.symm.toContinuousLinearMap.adjoint x = c⁻¹ • T x
    rw [hsym, ContinuousLinearMap.adjoint_comp, map_smul, ContinuousLinearMap.adjoint_id,
      ContinuousLinearMap.comp_apply, smul_apply, ContinuousLinearMap.id_apply, he]
    change e ((Real.sqrt c)⁻¹ • x) = c⁻¹ • e (Real.sqrt c • x)
    rw [map_smul, map_smul, smul_smul]
    congr 1
    have hs := Real.sq_sqrt hc.le
    field_simp
    nlinarith
  rw [hL, latticeDual_image_equiv _ (integerLattice_span _), integerLattice_dual_eq, hT]
  unfold latticeImage
  rw [← Submodule.map_comp]
  rfl

end SISToKSIS

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Module NumberField GeometricGaussianLHL
open scoped ComplexConjugate ENNReal Classical
namespace SISToKSIS
variable (K : Type*) [Field K] [NumberField K]

def cyclotomicConjugation (N : ℕ) [NeZero N] [IsCyclotomicExtension {N} ℚ K] : K ≃ₐ[ℚ] K :=
  IsCyclotomicExtension.fromZetaAut (IsCyclotomicExtension.zeta_spec N ℚ K).inv
    (Polynomial.cyclotomic.irreducible_rat (NeZero.pos N))

theorem cyclotomicConjugation_zeta (N : ℕ) [NeZero N] [IsCyclotomicExtension {N} ℚ K] :
    cyclotomicConjugation K N (IsCyclotomicExtension.zeta N ℚ K) =
      (IsCyclotomicExtension.zeta N ℚ K)⁻¹ :=
  IsCyclotomicExtension.fromZetaAut_spec _ _

theorem cyclotomicConjugation_embedding (N : ℕ) [NeZero N] [IsCyclotomicExtension {N} ℚ K]
    (τ : K →+* ℂ) (x : K) : τ (cyclotomicConjugation K N x) = conj (τ x) := by
  have he : τ.toRatAlgHom.comp (cyclotomicConjugation K N).toAlgHom =
      ((starRingEnd ℂ).comp τ).toRatAlgHom := by
    apply ((IsCyclotomicExtension.zeta_spec N ℚ K).powerBasis ℚ).algHom_ext
    change τ (cyclotomicConjugation K N (IsCyclotomicExtension.zeta N ℚ K)) =
      conj (τ (IsCyclotomicExtension.zeta N ℚ K))
    rw [cyclotomicConjugation_zeta, map_inv₀]
    exact Complex.inv_eq_conj (cyclotomic_embedding_norm K (IsCyclotomicExtension.zeta_spec N ℚ K) τ)
  exact congrArg (fun f : K →ₐ[ℚ] ℂ => f x) he

def cyclotomicIntegerConjugation (N : ℕ) [NeZero N] [IsCyclotomicExtension {N} ℚ K] :
    𝓞 K ≃+* 𝓞 K :=
  (RingOfIntegers.mapAlgEquiv (cyclotomicConjugation K N)).toRingEquiv

theorem cyclotomicIntegerConjugation_embedding (N : ℕ) [NeZero N]
    [IsCyclotomicExtension {N} ℚ K] (τ : K →+* ℂ) (x : 𝓞 K) :
    τ (cyclotomicIntegerConjugation K N x : K) = conj (τ (x : K)) :=
  cyclotomicConjugation_embedding K N τ x

end SISToKSIS

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Module NumberField GeometricGaussianLHL
open scoped ComplexConjugate ENNReal Classical Matrix
namespace SISToKSIS
variable (K : Type*) [Field K] [NumberField K] {d m n : ℕ}

local instance adjointEmbeddingsFintype : Fintype (K →+* ℂ) := inferInstance
local instance adjointAmbientInner : InnerProductSpace ℝ (CanonicalAmbient K) := inferInstance
local instance adjointSpaceInner : InnerProductSpace ℝ (canonicalSpace K) := inferInstance
local instance adjointPowerInner (r : ℕ) : InnerProductSpace ℝ (CanonicalPower K r) := inferInstance

theorem canonicalIntegerEmbedding_inner_mul (σ : 𝓞 K ≃+* 𝓞 K)
    (hσ : ∀ (τ : K →+* ℂ) (a : 𝓞 K),
      τ (algebraMap (𝓞 K) K (σ a)) = conj (τ (algebraMap (𝓞 K) K a)))
    (a x y : 𝓞 K) :
    inner ℝ (canonicalIntegerEmbedding K (a * x)) (canonicalIntegerEmbedding K y) =
      inner ℝ (canonicalIntegerEmbedding K x) (canonicalIntegerEmbedding K (σ a * y)) := by
  change inner ℝ (canonicalIntegerVector K (a * x)) (canonicalIntegerVector K y) =
    inner ℝ (canonicalIntegerVector K x) (canonicalIntegerVector K (σ a * y))
  rw [PiLp.inner_apply, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro τ _
  change (τ (algebraMap (𝓞 K) K y) * conj (τ (algebraMap (𝓞 K) K (a * x)))).re =
    (τ (algebraMap (𝓞 K) K (σ a * y)) * conj (τ (algebraMap (𝓞 K) K x))).re
  simp only [map_mul, hσ]
  congr 1
  ring

theorem canonicalEuclideanEmbedding_inner_mulVec (b : Basis (Fin d) ℤ (𝓞 K))
    (σ : 𝓞 K ≃+* 𝓞 K)
    (hσ : ∀ (τ : K →+* ℂ) (a : 𝓞 K),
      τ (algebraMap (𝓞 K) K (σ a)) = conj (τ (algebraMap (𝓞 K) K a)))
    (A : Matrix (Fin n) (Fin m) (𝓞 K)) (u : Fin m → 𝓞 K) (v : Fin n → 𝓞 K) :
    inner ℝ (canonicalEuclideanEmbedding K b n (A *ᵥ u)) (canonicalEuclideanEmbedding K b n v) =
      inner ℝ (canonicalEuclideanEmbedding K b m u)
        (canonicalEuclideanEmbedding K b m ((A.map σ).transpose *ᵥ v)) := by
  change inner ℝ (canonicalOrthonormalCoordinates K b n (canonicalPowerEmbedding K n (A *ᵥ u)))
      (canonicalOrthonormalCoordinates K b n (canonicalPowerEmbedding K n v)) =
    inner ℝ (canonicalOrthonormalCoordinates K b m (canonicalPowerEmbedding K m u))
      (canonicalOrthonormalCoordinates K b m (canonicalPowerEmbedding K m ((A.map σ).transpose *ᵥ v)))
  rw [LinearIsometryEquiv.inner_map_map, LinearIsometryEquiv.inner_map_map,
    PiLp.inner_apply, PiLp.inner_apply]
  simp only [canonicalPowerEmbedding_apply, Matrix.mulVec, dotProduct, map_sum,
    sum_inner, inner_sum, Matrix.transpose_apply, Matrix.map_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  exact canonicalIntegerEmbedding_inner_mul K σ hσ _ _ _

theorem canonicalEuclideanMatrix_adjoint_integer (b : Basis (Fin d) ℤ (𝓞 K))
    (σ : 𝓞 K ≃+* 𝓞 K)
    (hσ : ∀ (τ : K →+* ℂ) (a : 𝓞 K),
      τ (algebraMap (𝓞 K) K (σ a)) = conj (τ (algebraMap (𝓞 K) K a)))
    (A : Matrix (Fin n) (Fin m) (𝓞 K)) (v : Fin n → 𝓞 K) :
    (canonicalEuclideanMatrix K b A).toContinuousLinearMap.adjoint
        (canonicalEuclideanEmbedding K b n v) =
      canonicalEuclideanEmbedding K b m ((A.map σ).transpose *ᵥ v) := by
  have he : (innerₗ (Euclidean (m * d))).flip
      ((canonicalEuclideanMatrix K b A).toContinuousLinearMap.adjoint
        (canonicalEuclideanEmbedding K b n v)) =
      (innerₗ (Euclidean (m * d))).flip
        (canonicalEuclideanEmbedding K b m ((A.map σ).transpose *ᵥ v)) := by
    apply LinearMap.ext_on (IsZLattice.span_top (K := ℝ) (L := canonicalEuclideanLattice K b m))
    rintro _ ⟨u, rfl⟩
    change inner ℝ (canonicalEuclideanEmbedding K b m u)
        ((canonicalEuclideanMatrix K b A).toContinuousLinearMap.adjoint
          (canonicalEuclideanEmbedding K b n v)) = _
    rw [ContinuousLinearMap.adjoint_inner_right]
    change inner ℝ (canonicalEuclideanMatrix K b A (canonicalEuclideanEmbedding K b m u))
      (canonicalEuclideanEmbedding K b n v) = _
    rw [canonicalEuclideanMatrix_integer]
    exact canonicalEuclideanEmbedding_inner_mulVec K b σ hσ A u v
  exact ext_inner_left ℝ (fun x => LinearMap.congr_fun he x)

theorem canonicalEuclideanMatrix_adjoint (b : Basis (Fin d) ℤ (𝓞 K))
    (σ : 𝓞 K ≃+* 𝓞 K)
    (hσ : ∀ (τ : K →+* ℂ) (a : 𝓞 K),
      τ (algebraMap (𝓞 K) K (σ a)) = conj (τ (algebraMap (𝓞 K) K a)))
    (A : Matrix (Fin n) (Fin m) (𝓞 K)) :
    (canonicalEuclideanMatrix K b A).toContinuousLinearMap.adjoint =
      (canonicalEuclideanMatrix K b ((A.map σ).transpose)).toContinuousLinearMap := by
  have he : (canonicalEuclideanMatrix K b A).toContinuousLinearMap.adjoint.toLinearMap =
      canonicalEuclideanMatrix K b ((A.map σ).transpose) := by
    apply LinearMap.ext_on (IsZLattice.span_top (K := ℝ) (L := canonicalEuclideanLattice K b n))
    rintro _ ⟨v, rfl⟩
    exact (canonicalEuclideanMatrix_adjoint_integer K b σ hσ A v).trans
      (canonicalEuclideanMatrix_integer K b _ v).symm
  ext x : 1
  exact LinearMap.congr_fun he x

end SISToKSIS

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Module NumberField GeometricGaussianLHL
open scoped ENNReal Classical Matrix ComplexConjugate
namespace SISToKSIS

variable (K : Type*) [Field K] [NumberField K] {d r : ℕ}

def residueVectorLift (q : ℕ) (s : Fin r → ResidueRing K q) : Fin r → 𝓞 K :=
  fun i => (Ideal.Quotient.mk_surjective (s i)).choose

omit [NumberField K] in
@[simp] theorem residueVectorLift_map (q : ℕ) (s : Fin r → ResidueRing K q) (i : Fin r) :
    residueMap K q (residueVectorLift K q s i) = s i :=
  (Ideal.Quotient.mk_surjective (s i)).choose_spec

omit [NumberField K] in
theorem residueVectorLift_decomposition (q : ℕ) (v : Fin r → 𝓞 K) :
    ∃ s : Fin r → ResidueRing K q, ∃ w : Fin r → 𝓞 K,
      v = residueVectorLift K q s + (q : ℤ) • w := by
  let s : Fin r → ResidueRing K q := fun i => residueMap K q (v i)
  have hw (i : Fin r) : ∃ z : 𝓞 K, v i - residueVectorLift K q s i = (q : 𝓞 K) * z := by
    apply Ideal.mem_span_singleton.mp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change residueMap K q (v i - residueVectorLift K q s i) = 0
    rw [map_sub, residueVectorLift_map]
    exact sub_self _
  choose w hw using hw
  refine ⟨s, w, ?_⟩
  funext i
  simp only [Pi.add_apply, zsmul_eq_mul, Int.cast_natCast]
  exact (sub_eq_iff_eq_add.mp (hw i)).trans (add_comm _ _)

def canonicalScalarDualMap (b : Basis (Fin d) ℤ (𝓞 K)) {c : ℝ} (hc : 0 < c)
    (hGram : ∀ i j, canonicalGram K b i j = if i = j then c else 0) (r : ℕ) :
    (Fin r → 𝓞 K) →ₗ[ℤ] latticeDual (canonicalEuclideanLattice K b r) :=
  (((euclideanScalarShape (r * d) c⁻¹ (inv_ne_zero hc.ne')).toLinearMap.restrictScalars ℤ).comp
    (canonicalEuclideanEmbedding K b r)).codRestrict _ (fun v => by
      rw [canonicalEuclideanLattice_scalarGram_dual K b hc hGram]
      exact ⟨canonicalEuclideanEmbedding K b r v, ⟨v, rfl⟩, rfl⟩)

@[simp] theorem canonicalScalarDualMap_apply (b : Basis (Fin d) ℤ (𝓞 K)) {c : ℝ} (hc : 0 < c)
    (hGram : ∀ i j, canonicalGram K b i j = if i = j then c else 0) (r : ℕ)
    (v : Fin r → 𝓞 K) :
    (canonicalScalarDualMap K b hc hGram r v : Euclidean (r * d)) =
      c⁻¹ • canonicalEuclideanEmbedding K b r v := rfl

theorem canonicalScalarDualMap_surjective (b : Basis (Fin d) ℤ (𝓞 K)) {c : ℝ} (hc : 0 < c)
    (hGram : ∀ i j, canonicalGram K b i j = if i = j then c else 0) (r : ℕ) :
    Function.Surjective (canonicalScalarDualMap K b hc hGram r) := by
  intro x
  have hx := (congrArg (fun L : Submodule ℤ (Euclidean (r * d)) => (x : Euclidean (r * d)) ∈ L)
    (canonicalEuclideanLattice_scalarGram_dual K b hc hGram r)).mp x.2
  obtain ⟨y, ⟨v, rfl⟩, hv⟩ := hx
  exact ⟨v, Subtype.ext hv⟩

def canonicalDualResidueRepresentative (b : Basis (Fin d) ℤ (𝓞 K)) {c : ℝ} (hc : 0 < c)
    (hGram : ∀ i j, canonicalGram K b i j = if i = j then c else 0)
    (q r : ℕ) (s : Fin r → ResidueRing K q) : latticeDual (canonicalEuclideanLattice K b r) :=
  canonicalScalarDualMap K b hc hGram r (residueVectorLift K q s)

theorem canonicalDualResidueRepresentative_decomposition
    (b : Basis (Fin d) ℤ (𝓞 K)) {c : ℝ} (hc : 0 < c)
    (hGram : ∀ i j, canonicalGram K b i j = if i = j then c else 0) (q r : ℕ)
    (x : latticeDual (canonicalEuclideanLattice K b r)) :
    ∃ s : Fin r → ResidueRing K q, ∃ w : latticeDual (canonicalEuclideanLattice K b r),
      x = canonicalDualResidueRepresentative K b hc hGram q r s + (q : ℤ) • w := by
  obtain ⟨v, rfl⟩ := canonicalScalarDualMap_surjective K b hc hGram r x
  obtain ⟨s, w, hw⟩ := residueVectorLift_decomposition K q v
  exact ⟨s, canonicalScalarDualMap K b hc hGram r w, by rw [hw, map_add, map_smul]; rfl⟩

theorem numberFieldModularLattice_nonzeroDualMass_le_residueCosets
    (b : Basis (Fin d) ℤ (𝓞 K)) {c : ℝ} (hc : 0 < c)
    (hGram : ∀ i j, canonicalGram K b i j = if i = j then c else 0)
    (q : ℕ) [NeZero q] {m n : ℕ} (A : Matrix (Fin n) (Fin m) (ResidueRing K q)) (t : ℝ) :
    nonzeroDualMass (numberFieldModularLattice K b q A) t ≤
      ∑ s : Fin n → ResidueRing K q,
        nonzeroCosetMass (latticeDual (canonicalEuclideanLattice K b m)) t
          ((q : ℝ)⁻¹ • (canonicalEuclideanMatrix K b (residueMatrixLift K q A)).toContinuousLinearMap.adjoint
            (canonicalDualResidueRepresentative K b hc hGram q n s : Euclidean (n * d))) := by
  rw [nonzeroDualMass, numberFieldModularLattice_dual]
  apply nonzero_mass_le_finite_coset_cover
  · exact le_sup_left
  · intro s
    apply (show latticeImage ((↑(q : ℤ) : ℝ)⁻¹ •
        (canonicalEuclideanMatrix K b (residueMatrixLift K q A)).toContinuousLinearMap.adjoint)
        (latticeDual (canonicalEuclideanLattice K b n)) ≤
        modulusDual (canonicalEuclideanLattice K b m) (canonicalEuclideanLattice K b n)
          (canonicalEuclideanMatrix K b (residueMatrixLift K q A)).toContinuousLinearMap q from le_sup_right)
    refine ⟨_, (canonicalDualResidueRepresentative K b hc hGram q n s).2, ?_⟩
    simp only [Int.cast_natCast]
    rfl
  · intro x
    exact modulusDual_finite_cover_representatives _ _ _
      (canonicalEuclideanMatrix_lattice K b (residueMatrixLift K q A)) q
      (canonicalDualResidueRepresentative K b hc hGram q n)
      (canonicalDualResidueRepresentative_decomposition K b hc hGram q n) x.2

theorem numberFieldModularLattice_nonzeroDualMass_le_conjugateCosets
    (b : Basis (Fin d) ℤ (𝓞 K)) {c : ℝ} (hc : 0 < c)
    (hGram : ∀ i j, canonicalGram K b i j = if i = j then c else 0)
    (σ : 𝓞 K ≃+* 𝓞 K)
    (hσ : ∀ (τ : K →+* ℂ) (a : 𝓞 K),
      τ (algebraMap (𝓞 K) K (σ a)) = conj (τ (algebraMap (𝓞 K) K a)))
    (q : ℕ) [NeZero q] {m n : ℕ} (A : Matrix (Fin n) (Fin m) (ResidueRing K q)) (t : ℝ) :
    nonzeroDualMass (numberFieldModularLattice K b q A) t ≤
      ∑ s : Fin n → ResidueRing K q,
        nonzeroCosetMass
          (latticeImage (euclideanScalarShape (m * d) c⁻¹ (inv_ne_zero hc.ne')).toContinuousLinearMap
            (canonicalEuclideanLattice K b m)) t
          ((q : ℝ)⁻¹ • c⁻¹ • canonicalEuclideanEmbedding K b m
            (((residueMatrixLift K q A).map σ).transpose *ᵥ residueVectorLift K q s)) := by
  apply (numberFieldModularLattice_nonzeroDualMass_le_residueCosets K b hc hGram q A t).trans_eq
  apply Finset.sum_congr rfl
  intro s _
  unfold canonicalDualResidueRepresentative
  rw [canonicalScalarDualMap_apply, map_smul,
    canonicalEuclideanMatrix_adjoint_integer K b σ hσ,
    canonicalEuclideanLattice_scalarGram_dual K b hc hGram]

theorem cyclotomicModularLattice_nonzeroDualMass_le_cosets
    (N : ℕ) [NeZero N] [IsCyclotomicExtension {N} ℚ K]
    (b : Basis (Fin d) ℤ (𝓞 K)) {c : ℝ} (hc : 0 < c)
    (hGram : ∀ i j, canonicalGram K b i j = if i = j then c else 0)
    (q : ℕ) [NeZero q] {m n : ℕ} (A : Matrix (Fin n) (Fin m) (ResidueRing K q)) (t : ℝ) :
    nonzeroDualMass (numberFieldModularLattice K b q A) t ≤
      ∑ s : Fin n → ResidueRing K q,
        nonzeroCosetMass
          (latticeImage (euclideanScalarShape (m * d) c⁻¹ (inv_ne_zero hc.ne')).toContinuousLinearMap
            (canonicalEuclideanLattice K b m)) t
          ((q : ℝ)⁻¹ • c⁻¹ • canonicalEuclideanEmbedding K b m
            (((residueMatrixLift K q A).map (cyclotomicIntegerConjugation K N)).transpose *ᵥ
              residueVectorLift K q s)) :=
  numberFieldModularLattice_nonzeroDualMass_le_conjugateCosets K b hc hGram
    (cyclotomicIntegerConjugation K N) (cyclotomicIntegerConjugation_embedding K N) q A t

end SISToKSIS
