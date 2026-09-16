import GeometricGaussianLHL.GaussianPushforward
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient

/-!
# Modular kernels as full Euclidean lattices

The public matrix acts in a quotient ring, while Gaussian hints live in its
integral kernel. A nonzero integer annihilating the quotient implies that this
kernel is a full lattice, even when the public matrix is not surjective.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Module NumberField GeometricGaussianLHL MeasureTheory
open scoped Matrix

namespace SISToKSIS

section CongruenceLattice

variable {E P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [AddCommGroup P]

def congruenceLattice (L : Submodule ℤ E) (f : L →ₗ[ℤ] P) : Submodule ℤ E :=
  (LinearMap.ker f).map L.subtype

omit [NormedSpace ℝ E] in
theorem congruenceLattice_le (L : Submodule ℤ E) (f : L →ₗ[ℤ] P) :
    congruenceLattice L f ≤ L := by
  rintro x ⟨z, _, rfl⟩
  exact z.2

instance congruenceLattice_discrete (L : Submodule ℤ E) [DiscreteTopology L]
    (f : L →ₗ[ℤ] P) : DiscreteTopology (congruenceLattice L f) := by
  apply DiscreteTopology.of_continuous_injective
    (continuous_inclusion (congruenceLattice_le L f))
  exact Set.inclusion_injective (congruenceLattice_le L f)

theorem congruenceLattice_full (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (f : L →ₗ[ℤ] P) (q : ℤ) (hq : q ≠ 0) (hkill : ∀ z, q • f z = 0) :
    IsZLattice ℝ (congruenceLattice L f) := by
  constructor
  apply top_unique
  rw [← IsZLattice.span_top (K := ℝ) (L := L)]
  apply Submodule.span_le.mpr
  intro x hx
  have hqx : (q : ℝ) • x ∈ Submodule.span ℝ (congruenceLattice L f : Set E) := by
    apply Submodule.subset_span
    refine ⟨q • (⟨x, hx⟩ : L), ?_, ?_⟩
    · change f (q • (⟨x, hx⟩ : L)) = 0
      rw [LinearMap.map_smul]
      exact hkill _
    · simp [Int.cast_smul_eq_zsmul]
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  have hs := (Submodule.span ℝ (congruenceLattice L f : Set E)).smul_mem
    (q : ℝ)⁻¹ hqx
  simpa [smul_smul, hq'] using hs

end CongruenceLattice

section ModularMap

variable {R Q : Type*} [CommRing R] [CommRing Q]
  {ι κ : Type*} [Fintype ι]

def quotientVectorMap (f : R →+* Q) : (ι → R) →ₗ[ℤ] (ι → Q) :=
  LinearMap.pi (fun i => f.toIntAlgHom.toLinearMap.comp (LinearMap.proj i))

omit [Fintype ι] in
@[simp] theorem quotientVectorMap_apply (f : R →+* Q) (v : ι → R) :
    quotientVectorMap f v = f ∘ v := rfl

def modularMap (f : R →+* Q) (A : Matrix κ ι Q) : (ι → R) →ₗ[ℤ] (κ → Q) :=
  (A.mulVecLin.restrictScalars ℤ).comp (quotientVectorMap f)

@[simp] theorem modularMap_apply (f : R →+* Q) (A : Matrix κ ι Q) (v : ι → R) :
    modularMap f A v = A *ᵥ (f ∘ v) := rfl

def modularKernel (f : R →+* Q) (A : Matrix κ ι Q) : Submodule ℤ (ι → R) :=
  LinearMap.ker (modularMap f A)

@[simp] theorem mem_modularKernel (f : R →+* Q) (A : Matrix κ ι Q) (v : ι → R) :
    v ∈ modularKernel f A ↔ A *ᵥ (f ∘ v) = 0 := Iff.rfl

theorem modularMap_annihilated (f : R →+* Q) (A : Matrix κ ι Q)
    (q : ℤ) (hq : (q : Q) = 0) (v : ι → R) : q • modularMap f A v = 0 := by
  ext i
  simp [zsmul_eq_mul, hq]

end ModularMap

section NumberFields

variable (K : Type*) [Field K] [NumberField K] {d m n : ℕ}

abbrev ResidueRing (q : ℕ) := (𝓞 K) ⧸ Ideal.span ({(q : 𝓞 K)} : Set (𝓞 K))

def residueMap (q : ℕ) : 𝓞 K →+* ResidueRing K q :=
  Ideal.Quotient.mk _

omit [NumberField K] in
theorem residueMap_modulus (q : ℕ) : (q : ResidueRing K q) = 0 := by
  change residueMap K q (q : 𝓞 K) = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))

instance residueRing_finite (q : ℕ) [NeZero q] : Finite (ResidueRing K q) := by
  apply Ideal.finiteQuotientOfFreeOfNeBot
  intro h
  have hm : (q : 𝓞 K) ∈ Ideal.span ({(q : 𝓞 K)} : Set (𝓞 K)) :=
    Ideal.subset_span (by simp)
  rw [h] at hm
  exact (Nat.cast_ne_zero.mpr (NeZero.ne q) : (q : 𝓞 K) ≠ 0) hm

instance residueRing_fintype (q : ℕ) [NeZero q] : Fintype (ResidueRing K q) :=
  Fintype.ofFinite _

def numberFieldModularMap (b : Basis (Fin d) ℤ (𝓞 K)) (q : ℕ)
    (A : Matrix (Fin n) (Fin m) (ResidueRing K q)) :
    canonicalEuclideanLattice K b m →ₗ[ℤ] (Fin n → ResidueRing K q) :=
  (modularMap (residueMap K q) A).comp (canonicalEuclideanLatticeEquiv K b m).symm.toLinearMap

def numberFieldModularLattice (b : Basis (Fin d) ℤ (𝓞 K)) (q : ℕ)
    (A : Matrix (Fin n) (Fin m) (ResidueRing K q)) : Submodule ℤ (Euclidean (m * d)) :=
  congruenceLattice (canonicalEuclideanLattice K b m) (numberFieldModularMap K b q A)

instance numberFieldModularLattice_discrete (b : Basis (Fin d) ℤ (𝓞 K)) (q : ℕ)
    (A : Matrix (Fin n) (Fin m) (ResidueRing K q)) :
    DiscreteTopology (numberFieldModularLattice K b q A) :=
  congruenceLattice_discrete _ _

theorem numberFieldModularLattice_full (b : Basis (Fin d) ℤ (𝓞 K)) (q : ℕ)
    (hq : q ≠ 0) (A : Matrix (Fin n) (Fin m) (ResidueRing K q)) :
    IsZLattice ℝ (numberFieldModularLattice K b q A) := by
  apply congruenceLattice_full _ _ (q : ℤ) (by exact_mod_cast hq)
  intro z
  apply modularMap_annihilated
  simpa using residueMap_modulus K q

instance numberFieldModularLattice_isZLattice (b : Basis (Fin d) ℤ (𝓞 K))
    (q : ℕ) [NeZero q] (A : Matrix (Fin n) (Fin m) (ResidueRing K q)) :
    IsZLattice ℝ (numberFieldModularLattice K b q A) :=
  numberFieldModularLattice_full K b q (NeZero.ne q) A

theorem canonicalEmbedding_mem_modularLattice_iff
    (b : Basis (Fin d) ℤ (𝓞 K)) (q : ℕ)
    (A : Matrix (Fin n) (Fin m) (ResidueRing K q)) (v : Fin m → 𝓞 K) :
    canonicalEuclideanEmbedding K b m v ∈ numberFieldModularLattice K b q A ↔
      v ∈ modularKernel (residueMap K q) A := by
  constructor
  · rintro ⟨z, hz, he⟩
    change modularMap (residueMap K q) A v = 0
    have he' : z = canonicalEuclideanLatticeEquiv K b m v := Subtype.ext he
    change numberFieldModularMap K b q A z = 0 at hz
    rw [he'] at hz
    simpa only [numberFieldModularMap, LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] using hz
  · intro hv
    change modularMap (residueMap K q) A v = 0 at hv
    refine ⟨canonicalEuclideanLatticeEquiv K b m v, ?_, rfl⟩
    change numberFieldModularMap K b q A (canonicalEuclideanLatticeEquiv K b m v) = 0
    simpa only [numberFieldModularMap, LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] using hv

/-- The exact identification of integral modular solutions with the Euclidean lattice. -/
def integralKernelEquiv (b : Basis (Fin d) ℤ (𝓞 K)) (q : ℕ)
    (A : Matrix (Fin n) (Fin m) (ResidueRing K q)) :
    modularKernel (residueMap K q) A ≃ₗ[ℤ] numberFieldModularLattice K b q A :=
  LinearEquiv.ofBijective
    { toFun := fun v => ⟨canonicalEuclideanEmbedding K b m v,
        (canonicalEmbedding_mem_modularLattice_iff K b q A v).mpr v.2⟩
      map_add' := by intros; apply Subtype.ext; exact map_add _ _ _
      map_smul' := by intros; apply Subtype.ext; exact map_smul _ _ _ }
    ⟨by
      intro x y h
      apply Subtype.ext
      exact canonicalEuclideanEmbedding_injective K b m (congrArg Subtype.val h), by
      intro z
      obtain ⟨v, hv⟩ := congruenceLattice_le (canonicalEuclideanLattice K b m)
        (numberFieldModularMap K b q A) z.2
      refine ⟨⟨v, (canonicalEmbedding_mem_modularLattice_iff K b q A v).mp ?_⟩,
        Subtype.ext hv⟩
      simpa only [hv] using z.2⟩

@[simp] theorem integralKernelEquiv_coe (b : Basis (Fin d) ℤ (𝓞 K)) (q : ℕ)
    (A : Matrix (Fin n) (Fin m) (ResidueRing K q))
    (v : modularKernel (residueMap K q) A) :
    (integralKernelEquiv K b q A v : Euclidean (m * d)) =
      canonicalEuclideanEmbedding K b m v := rfl

end NumberFields

section
variable {E P : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [AddCommGroup P] (L : Submodule ℤ E) (f : L →ₗ[ℤ] P)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem congruenceLattice_relIndex :
    (congruenceLattice L f).toAddSubgroup.relIndex L.toAddSubgroup =
      Nat.card f.toAddMonoidHom.range := by
  have htop : L.toAddSubgroup = AddSubgroup.map L.subtype.toAddMonoidHom ⊤ := by
    ext x
    constructor
    · intro hx
      exact ⟨⟨x, hx⟩, trivial, rfl⟩
    · rintro ⟨x, _, rfl⟩
      exact x.2
  change (AddSubgroup.map L.subtype.toAddMonoidHom f.toAddMonoidHom.ker).relIndex _ = _
  rw [htop, AddSubgroup.relIndex_map_map_of_injective _ _ L.subtype_injective,
    AddSubgroup.relIndex_top_right, AddSubgroup.index_ker]

theorem congruenceLattice_covolume_le [DiscreteTopology L] [IsZLattice ℝ L]
    [IsZLattice ℝ (congruenceLattice L f)] [Finite P] :
    ZLattice.covolume (congruenceLattice L f) ≤ (Nat.card P : ℝ) * ZLattice.covolume L := by
  apply (div_le_iff₀ (ZLattice.covolume_pos L volume)).mp
  rw [ZLattice.covolume_div_covolume_eq_relIndex' _ _ (congruenceLattice_le L f),
    congruenceLattice_relIndex]
  exact_mod_cast Nat.card_le_card_of_injective (fun x : f.toAddMonoidHom.range => (x : P))
    Subtype.val_injective
end

variable (K : Type*) [Field K] [NumberField K] {d m n : ℕ}

theorem residueRing_card (b : Basis (Fin d) ℤ (𝓞 K)) (q : ℕ) :
    Nat.card (ResidueRing K q) = q ^ d := by
  change Ideal.absNorm (Ideal.span ({(q : 𝓞 K)} : Set (𝓞 K))) = _
  rw [Ideal.absNorm_span_natCast, Module.finrank_eq_card_basis b, Fintype.card_fin]

theorem numberFieldModularLattice_covolume_le (b : Basis (Fin d) ℤ (𝓞 K))
    (q : ℕ) [NeZero q] (A : Matrix (Fin n) (Fin m) (ResidueRing K q)) :
    ZLattice.covolume (numberFieldModularLattice K b q A) ≤
      (q : ℝ) ^ (d * n) * ZLattice.covolume (canonicalEuclideanLattice K b m) := by
  let : IsZLattice ℝ (congruenceLattice (canonicalEuclideanLattice K b m)
      (numberFieldModularMap K b q A)) :=
    numberFieldModularLattice_full K b q (NeZero.ne q) A
  have h := congruenceLattice_covolume_le (canonicalEuclideanLattice K b m)
    (numberFieldModularMap K b q A)
  have hc : Nat.card (Fin n → ResidueRing K q) = q ^ (d * n) := by
    rw [Nat.card_fun, Nat.card_fin, residueRing_card K b q, ← pow_mul]
  rw [hc, Nat.cast_pow] at h
  exact h

local instance volumeEmbeddingsFintype : Fintype (K →+* ℂ) := inferInstance
local instance volumeAmbientInner : InnerProductSpace ℝ (CanonicalAmbient K) := inferInstance
local instance volumeSpaceInner : InnerProductSpace ℝ (canonicalSpace K) := inferInstance
local instance volumePowerInner (r : ℕ) : InnerProductSpace ℝ (CanonicalPower K r) := inferInstance
local instance volumePowerMeasureSpace (r : ℕ) : MeasureSpace (CanonicalPower K r) :=
  measureSpaceOfInnerProductSpace

theorem canonicalEuclideanLattice_covolume (b : Basis (Fin d) ℤ (𝓞 K)) (m : ℕ) :
    ZLattice.covolume (canonicalEuclideanLattice K b m) =
      Real.sqrt |(NumberField.discr K : ℝ)| ^ m := by
  let : DiscreteTopology (canonicalLattice K m) := canonicalLattice_discrete K b m
  let : IsZLattice ℝ (canonicalLattice K m) := ⟨canonicalLattice_span K b m⟩
  rw [canonicalEuclideanLattice_eq_image, covolume_latticeImage_isometry,
    canonicalLattice_covolume K b m]

theorem numberFieldModularLattice_covolume_le_discr (b : Basis (Fin d) ℤ (𝓞 K))
    (q : ℕ) [NeZero q] (A : Matrix (Fin n) (Fin m) (ResidueRing K q)) :
    ZLattice.covolume (numberFieldModularLattice K b q A) ≤
      (q : ℝ) ^ (d * n) * Real.sqrt |(NumberField.discr K : ℝ)| ^ m := by
  simpa only [canonicalEuclideanLattice_covolume K b m] using
    numberFieldModularLattice_covolume_le K b q A

end SISToKSIS
