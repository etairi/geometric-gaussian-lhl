import «SIS-to-kSIS».ModularDuality
import «SIS-to-kSIS».UniformSimulation
import «SIS-to-kSIS».GaussianRegularity
import Mathlib.Data.SetLike.Fintype
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Quotient.Card
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Gaussian coset averages and finite residue images

A finite quotient partitions a lattice into cosets. Removing the ambient zero
from each coset gives an exact nonzero-mass identity. Uniform surjective
additive maps then turn it into the corresponding expectation formula. For a
fixed residue frequency, a uniform matrix has independent uniform dot products
in the ideal it generates. The integral preimage ideal has the required norm.
These cosets partition its scaled lattice, giving the actual modular-kernel
expectation bound. Grouping frequencies by ideals controls the remaining sum.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Module NumberField GeometricGaussianLHL
open scoped ENNReal Classical
namespace SISToKSIS

theorem finite_pmf_expectation_map {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF α) (f : α → β) (w : β → ℝ≥0∞) :
    (∑ x, p x * w (f x)) = ∑ y, (p.map f) y * w y := by
  simp only [PMF.map_apply, tsum_fintype, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp [ite_mul]

theorem uniform_surjective_expectation {G H : Type*} [AddGroup G] [AddGroup H]
    [Fintype G] [Fintype H] (f : G →+ H) (hf : Function.Surjective f)
    (w : H → ℝ≥0∞) :
    (∑ x : G, PMF.uniformOfFintype G x * w (f x)) =
      (Fintype.card H : ℝ≥0∞)⁻¹ * ∑ y : H, w y := by
  rw [finite_pmf_expectation_map, uniform_map_surjective_addHom f hf]
  simp only [PMF.uniformOfFintype_apply, Finset.mul_sum]

variable {E : Type*} [NormedAddCommGroup E]

theorem nonzeroCosetMass_add_mem (L : Submodule ℤ E) (t : ℝ) (c : E)
    {u : E} (hu : u ∈ L) :
    nonzeroCosetMass L t (u + c) = nonzeroCosetMass L t c := by
  let e : L ≃ L := Equiv.addRight ⟨u, hu⟩
  unfold nonzeroCosetMass
  have h := e.tsum_eq (fun x : L =>
    if (x : E) + c = 0 then 0 else ENNReal.ofReal (gaussianWeight t ((x : E) + c)))
  apply Eq.trans _ h
  apply tsum_congr
  intro x
  change (if (x : E) + (u + c) = 0 then 0 else ENNReal.ofReal (gaussianWeight t ((x : E) + (u + c)))) =
    if ((x : E) + u) + c = 0 then 0 else ENNReal.ofReal (gaussianWeight t (((x : E) + u) + c))
  rw [add_assoc]

theorem gaussianMass_eq_one_add_nonzeroCosetMass (L : Submodule ℤ E) (t : ℝ) :
    gaussianMass t (L : Set E) = 1 + nonzeroCosetMass L t 0 := by
  change (∑' x : L, ENNReal.ofReal (gaussianWeight t (x : E))) = _
  rw [ENNReal.tsum_eq_add_tsum_ite
    (f := fun x : L => ENNReal.ofReal (gaussianWeight t (x : E))) 0]
  simp only [Submodule.coe_zero, gaussianWeight_zero, ENNReal.ofReal_one]
  congr 1
  unfold nonzeroCosetMass
  apply tsum_congr
  intro x
  have hx : (x : E) = 0 ↔ x = 0 := by
    change (x : E) = ((0 : L) : E) ↔ x = 0
    exact Subtype.ext_iff.symm
  by_cases h : x = 0 <;> simp [h, hx]

theorem nonzeroCosetMass_eq_mass_sub_one (L : Submodule ℤ E) (t : ℝ) :
    nonzeroCosetMass L t 0 = gaussianMass t (L : Set E) - 1 := by
  rw [gaussianMass_eq_one_add_nonzeroCosetMass]
  simp

theorem nonzeroCosetMass_sum_eq {Q : Type*} [AddGroup Q] [Fintype Q]
    (L D : Submodule ℤ E) (hLD : L ≤ D) (f : D →+ Q)
    (hker : ∀ x : D, f x = 0 ↔ (x : E) ∈ L)
    (c : Q → D) (hc : ∀ s, f (c s) = s) (t : ℝ) :
    (∑ s : Q, nonzeroCosetMass L t (c s : E)) =
      nonzeroCosetMass D t 0 := by
  let g : Q × L → D := fun z => ⟨(z.2 : E) + c z.1, D.add_mem (hLD z.2.2) (c z.1).2⟩
  have hg (z : Q × L) : f (g z) = z.1 := by
    change f ((⟨(z.2 : E), hLD z.2.2⟩ : D) + c z.1) = z.1
    rw [map_add, (hker _).mpr z.2.2, hc, zero_add]
  have hi : Function.Injective g := by
    rintro ⟨s, u⟩ ⟨s', u'⟩ h
    have hs : s = s' := by simpa only [hg] using congrArg f h
    subst s'
    have hu : u = u' := by
      apply Subtype.ext
      exact add_right_cancel (congrArg Subtype.val h)
    subst u'
    rfl
  have hs : Function.Surjective g := by
    intro x
    have hx : ((x - c (f x) : D) : E) ∈ L := by
      apply (hker _).mp
      rw [map_sub, hc, sub_self]
    refine ⟨(f x, ⟨(x : E) - c (f x), hx⟩), ?_⟩
    apply Subtype.ext
    exact sub_add_cancel _ _
  let e := Equiv.ofBijective g ⟨hi, hs⟩
  have he := e.tsum_eq (fun x : D =>
    if (x : E) = 0 then 0 else ENNReal.ofReal (gaussianWeight t (x : E)))
  rw [ENNReal.tsum_prod', tsum_fintype] at he
  convert he using 1
  · apply Finset.sum_congr rfl
    intro s _
    rfl
  · simp only [nonzeroCosetMass, add_zero]

theorem uniform_nonzeroCosetMass_expectation {G Q : Type*} [AddGroup G] [AddGroup Q]
    [Fintype G] [Fintype Q] (L D : Submodule ℤ E) (hLD : L ≤ D)
    (f : D →+ Q) (hker : ∀ x : D, f x = 0 ↔ (x : E) ∈ L)
    (c : Q → D) (hc : ∀ s, f (c s) = s)
    (g : G →+ Q) (hg : Function.Surjective g) (t : ℝ) :
    (∑ x : G, PMF.uniformOfFintype G x * nonzeroCosetMass L t (c (g x) : E)) =
      (Fintype.card Q : ℝ≥0∞)⁻¹ * (gaussianMass t (D : Set E) - 1) := by
  rw [uniform_surjective_expectation g hg (fun s => nonzeroCosetMass L t (c s : E)),
    nonzeroCosetMass_sum_eq L D hLD f hker c hc,
    nonzeroCosetMass_eq_mass_sub_one]

end SISToKSIS

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Module NumberField GeometricGaussianLHL
open scoped ENNReal Classical
namespace SISToKSIS
variable {R : Type*} [CommRing R] {n m : ℕ}

/-- The ideal generated by a fixed residue frequency. -/
def dotImageIdeal (s : Fin n → R) : Ideal R := Ideal.span (Set.range s)

def dotImageMap (s : Fin n → R) : (Fin n → R) →ₗ[R] dotImageIdeal s :=
  (Fintype.linearCombination R s).codRestrict (dotImageIdeal s) (fun v => by
    change Fintype.linearCombination R s v ∈ Submodule.span R (Set.range s)
    rw [← Fintype.range_linearCombination]
    exact LinearMap.mem_range_self _ v)

@[simp] theorem dotImageMap_apply (s v : Fin n → R) :
    (dotImageMap s v : R) = ∑ i, v i * s i :=
  Fintype.linearCombination_apply _ _ _

theorem dotImageMap_surjective (s : Fin n → R) : Function.Surjective (dotImageMap s) := by
  intro x
  have hx : (x : R) ∈ LinearMap.range (Fintype.linearCombination R s) := by
    rw [Fintype.range_linearCombination]
    exact x.2
  obtain ⟨v, hv⟩ := hx
  exact ⟨v, Subtype.ext hv⟩

theorem uniform_dotImage [Fintype R] (s : Fin n → R) :
    (PMF.uniformOfFintype (Fin n → R)).map (dotImageMap s) =
      PMF.uniformOfFintype (dotImageIdeal s) :=
  uniform_map_surjective_addHom (dotImageMap s).toAddMonoidHom (dotImageMap_surjective s)

/-- Each column is mapped to its dot product with the fixed residue frequency. -/
def dotImageColumns (s : Fin n → R) (m : ℕ) :
    Matrix (Fin n) (Fin m) R →+ (Fin m → dotImageIdeal s) where
  toFun A j := dotImageMap s (fun i => A i j)
  map_zero' := by ext j; simp
  map_add' A B := by
    funext j
    exact (dotImageMap s).map_add (fun i => A i j) (fun i => B i j)

@[simp] theorem dotImageColumns_apply (s : Fin n → R) (A : Matrix (Fin n) (Fin m) R)
    (j : Fin m) : (dotImageColumns s m A j : R) = ∑ i, A i j * s i :=
  dotImageMap_apply _ _

theorem dotImageColumns_surjective (s : Fin n → R) (m : ℕ) :
    Function.Surjective (dotImageColumns s m) := by
  intro v
  choose w hw using fun j => dotImageMap_surjective s (v j)
  exact ⟨fun i j => w j i, funext hw⟩

theorem uniform_dotImageColumns [Fintype R] (s : Fin n → R) (m : ℕ) :
    (PMF.uniformOfFintype (Matrix (Fin n) (Fin m) R)).map (dotImageColumns s m) =
      PMF.uniformOfFintype (Fin m → dotImageIdeal s) :=
  uniform_map_surjective_addHom (dotImageColumns s m) (dotImageColumns_surjective s m)

variable (K : Type*) [Field K] [NumberField K]

/-- The actual integral ideal above the image of a residue-frequency dot product. -/
def residueDotIdeal (q : ℕ) (s : Fin n → ResidueRing K q) : Ideal (𝓞 K) :=
  (dotImageIdeal s).comap (residueMap K q)

omit [NumberField K] in
theorem modulus_mem_residueDotIdeal (q : ℕ) (s : Fin n → ResidueRing K q) :
    (q : 𝓞 K) ∈ residueDotIdeal K q s := by
  change residueMap K q (q : 𝓞 K) ∈ dotImageIdeal s
  rw [map_natCast, residueMap_modulus]
  exact (dotImageIdeal s).zero_mem

theorem residueDotIdeal_quotient_card (q : ℕ) (s : Fin n → ResidueRing K q) :
    Nat.card (ResidueRing K q ⧸ dotImageIdeal s) = Ideal.absNorm (residueDotIdeal K q s) := by
  let e : (𝓞 K ⧸ residueDotIdeal K q s) ≃+* (ResidueRing K q ⧸ dotImageIdeal s) :=
    RingEquiv.ofBijective (Ideal.quotientMap (dotImageIdeal s) (residueMap K q) le_rfl)
      ⟨Ideal.quotientMap_injective, Ideal.quotientMap_surjective Ideal.Quotient.mk_surjective⟩
  rw [← Nat.card_congr e.toEquiv]
  rfl

theorem residueDotIdeal_card_mul_norm {d : ℕ} (b : Basis (Fin d) ℤ (𝓞 K))
    (q : ℕ) [NeZero q] (s : Fin n → ResidueRing K q) :
    Fintype.card (dotImageIdeal s) * Ideal.absNorm (residueDotIdeal K q s) = q ^ d := by
  have h := Submodule.card_eq_card_quotient_mul_card (dotImageIdeal s)
  rw [residueDotIdeal_quotient_card, residueRing_card K b q,
    Nat.card_eq_fintype_card] at h
  exact h.symm

end SISToKSIS

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Module NumberField GeometricGaussianLHL
open scoped ENNReal Classical
namespace SISToKSIS
variable (K : Type*) [Field K] [NumberField K] {n m : ℕ}

def residueRingEquiv (q : ℕ) (σ : 𝓞 K ≃+* 𝓞 K) : ResidueRing K q ≃+* ResidueRing K q :=
  Ideal.quotientEquiv _ _ σ (by simp [Ideal.map_span])

omit [NumberField K] in
@[simp] theorem residueRingEquiv_map (q : ℕ) (σ : 𝓞 K ≃+* 𝓞 K) (x : 𝓞 K) :
    residueRingEquiv K q σ (residueMap K q x) = residueMap K q (σ x) := rfl

def residueMatrixEquivMap (q : ℕ) (σ : 𝓞 K ≃+* 𝓞 K) (n m : ℕ) :
    Matrix (Fin n) (Fin m) (ResidueRing K q) →+
      Matrix (Fin n) (Fin m) (ResidueRing K q) :=
  coordinateAddHom (ι := Fin n) (coordinateAddHom (ι := Fin m)
    (residueRingEquiv K q σ).toAddMonoidHom)

omit [NumberField K] in
@[simp] theorem residueMatrixEquivMap_apply (q : ℕ) (σ : 𝓞 K ≃+* 𝓞 K)
    (A : Matrix (Fin n) (Fin m) (ResidueRing K q)) :
    residueMatrixEquivMap K q σ n m A = A.map (residueRingEquiv K q σ) := rfl

omit [NumberField K] in
theorem residueMatrixEquivMap_surjective (q : ℕ) (σ : 𝓞 K ≃+* 𝓞 K) (n m : ℕ) :
    Function.Surjective (residueMatrixEquivMap K q σ n m) :=
  coordinateAddHom_surjective _
    (coordinateAddHom_surjective _ (residueRingEquiv K q σ).surjective)

theorem uniform_automorphism_dotImageColumns (q : ℕ) [NeZero q]
    (σ : 𝓞 K ≃+* 𝓞 K) (s : Fin n → ResidueRing K q) (m : ℕ) :
    (PMF.uniformOfFintype (Matrix (Fin n) (Fin m) (ResidueRing K q))).map
      (fun A => dotImageColumns s m (A.map (residueRingEquiv K q σ))) =
      PMF.uniformOfFintype (Fin m → dotImageIdeal s) := by
  exact uniform_map_surjective_addHom
    ((dotImageColumns s m).comp (residueMatrixEquivMap K q σ n m))
    ((dotImageColumns_surjective s m).comp (residueMatrixEquivMap_surjective K q σ n m))

omit [NumberField K] in
theorem residueMatrixLift_automorphism (q : ℕ) (σ : 𝓞 K ≃+* 𝓞 K)
    (A : Matrix (Fin n) (Fin m) (ResidueRing K q)) :
    ((residueMatrixLift K q A).map σ).map (residueMap K q) =
      A.map (residueRingEquiv K q σ) := by
  funext i j
  change residueMap K q (σ (residueMatrixLift K q A i j)) = _
  rw [← residueRingEquiv_map]
  have h := congrFun (congrFun (residueMatrixLift_map K q A) i) j
  exact congrArg (residueRingEquiv K q σ) h

end SISToKSIS

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Module NumberField GeometricGaussianLHL
open scoped ENNReal Classical Matrix
namespace SISToKSIS
variable (K : Type*) [Field K] [NumberField K] {d r m n : ℕ}

def idealResidueCosetMap (q : ℕ) (J : Ideal (ResidueRing K q)) (r : ℕ)
    (v : (Fin r → J) × (Fin r → 𝓞 K)) : Fin r → J.comap (residueMap K q) :=
  fun i => ⟨residueVectorLift K q (fun j => (v.1 j : ResidueRing K q)) i + (q : 𝓞 K) * v.2 i, by
    change residueMap K q _ ∈ J
    simpa only [map_add, map_mul, map_natCast, residueMap_modulus, zero_mul, add_zero,
      residueVectorLift_map] using (v.1 i).2⟩

omit [NumberField K] in
@[simp] theorem idealResidueCosetMap_residue (q : ℕ) (J : Ideal (ResidueRing K q)) (r : ℕ)
    (v : (Fin r → J) × (Fin r → 𝓞 K)) (i : Fin r) :
    residueMap K q (idealResidueCosetMap K q J r v i : 𝓞 K) = (v.1 i : ResidueRing K q) := by
  simp only [idealResidueCosetMap, map_add, map_mul, map_natCast, residueMap_modulus,
    zero_mul, add_zero, residueVectorLift_map]

def idealResidueCosetEquiv (q : ℕ) [NeZero q] (J : Ideal (ResidueRing K q)) (r : ℕ) :
    ((Fin r → J) × (Fin r → 𝓞 K)) ≃ (Fin r → J.comap (residueMap K q)) :=
  Equiv.ofBijective (idealResidueCosetMap K q J r) ⟨by
    rintro ⟨s, u⟩ ⟨s', u'⟩ h
    have hs : s = s' := by
      funext i
      apply Subtype.ext
      have he := congrArg (fun v : Fin r → J.comap (residueMap K q) =>
        residueMap K q (v i : 𝓞 K)) h
      simpa only [idealResidueCosetMap_residue] using he
    subst s'
    have hu : u = u' := by
      funext i
      have he := congrArg (fun v : Fin r → J.comap (residueMap K q) => (v i : 𝓞 K)) h
      exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr (NeZero.ne q) : (q : 𝓞 K) ≠ 0)
        (add_left_cancel he)
    subst u'
    rfl, by
    intro v
    obtain ⟨s, w, hw⟩ := residueVectorLift_decomposition K q (fun i => (v i : 𝓞 K))
    have hs (i : Fin r) : residueMap K q (v i : 𝓞 K) = s i := by
      have hi := congrFun hw i
      rw [hi]
      change residueMap K q (residueVectorLift K q s i + (q : ℤ) • w i) = s i
      simp only [zsmul_eq_mul, Int.cast_natCast,
        map_add, map_mul, map_natCast, residueMap_modulus, zero_mul, add_zero,
        residueVectorLift_map]
    let y : Fin r → J := fun i => ⟨s i, by rw [← hs i]; exact (v i).2⟩
    refine ⟨(y, w), ?_⟩
    funext i
    apply Subtype.ext
    have hi := congrFun hw i
    change (v i : 𝓞 K) = residueVectorLift K q s i + (q : ℤ) • w i at hi
    simpa only [idealResidueCosetMap, y, zsmul_eq_mul,
      Int.cast_natCast] using hi.symm⟩

@[simp] theorem idealResidueCosetEquiv_apply (q : ℕ) [NeZero q]
    (J : Ideal (ResidueRing K q)) (r : ℕ) (v : (Fin r → J) × (Fin r → 𝓞 K)) (i : Fin r) :
    (idealResidueCosetEquiv K q J r v i : 𝓞 K) =
      residueVectorLift K q (fun j => (v.1 j : ResidueRing K q)) i + (q : 𝓞 K) * v.2 i := rfl

def scalarCanonicalLattice (b : Basis (Fin d) ℤ (𝓞 K)) (r : ℕ) (a : ℝ) (ha : a ≠ 0) :
    Submodule ℤ (Euclidean (r * d)) :=
  latticeImage (euclideanScalarShape (r * d) a ha).toContinuousLinearMap (canonicalEuclideanLattice K b r)

def scalarCanonicalEquiv (b : Basis (Fin d) ℤ (𝓞 K)) (r : ℕ) (a : ℝ) (ha : a ≠ 0) :
    (Fin r → 𝓞 K) ≃ₗ[ℤ] scalarCanonicalLattice K b r a ha :=
  (canonicalEuclideanLatticeEquiv K b r).trans
    (latticeImageEquiv (euclideanScalarShape (r * d) a ha) (canonicalEuclideanLattice K b r))

@[simp] theorem scalarCanonicalEquiv_apply (b : Basis (Fin d) ℤ (𝓞 K)) (r : ℕ)
    (a : ℝ) (ha : a ≠ 0) (v : Fin r → 𝓞 K) :
    (scalarCanonicalEquiv K b r a ha v : Euclidean (r * d)) = a • canonicalEuclideanEmbedding K b r v := rfl

def scalarIdealLattice (b : Basis (Fin d) ℤ (𝓞 K)) (I : Ideal (𝓞 K)) (r : ℕ)
    (a : ℝ) (ha : a ≠ 0) : Submodule ℤ (Euclidean (r * d)) :=
  latticeImage (euclideanScalarShape (r * d) a ha).toContinuousLinearMap (idealEuclideanLattice K b I r)

def scalarIdealEquiv (b : Basis (Fin d) ℤ (𝓞 K)) (I : Ideal (𝓞 K)) (r : ℕ)
    (a : ℝ) (ha : a ≠ 0) : (Fin r → I) ≃ scalarIdealLattice K b I r a ha :=
  (idealEuclideanLatticeEquiv K b I r).trans
    (latticeImageEquiv (euclideanScalarShape (r * d) a ha) (idealEuclideanLattice K b I r)).toEquiv

@[simp] theorem scalarIdealEquiv_apply (b : Basis (Fin d) ℤ (𝓞 K)) (I : Ideal (𝓞 K)) (r : ℕ)
    (a : ℝ) (ha : a ≠ 0) (v : Fin r → I) :
    (scalarIdealEquiv K b I r a ha v : Euclidean (r * d)) =
      a • canonicalEuclideanEmbedding K b r (fun i => (v i : 𝓞 K)) := rfl

theorem scalar_modulus_embedding (b : Basis (Fin d) ℤ (𝓞 K)) (q : ℕ) [NeZero q]
    (a : ℝ) (u v : Fin r → 𝓞 K) :
    (q : ℝ)⁻¹ • a • canonicalEuclideanEmbedding K b r (u + (q : ℤ) • v) =
      a • canonicalEuclideanEmbedding K b r v +
        (q : ℝ)⁻¹ • a • canonicalEuclideanEmbedding K b r u := by
  have hq : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  rw [map_add, map_smul, ← Int.cast_smul_eq_zsmul ℝ (q : ℤ)
    (canonicalEuclideanEmbedding K b r v)]
  simp only [Int.cast_natCast, smul_add, smul_smul]
  have he : (q : ℝ)⁻¹ * (a * q) = a := by field_simp
  rw [he, add_comm]

def scalarIdealCosetEquiv (b : Basis (Fin d) ℤ (𝓞 K)) (q : ℕ) [NeZero q]
    (J : Ideal (ResidueRing K q)) (r : ℕ) (a : ℝ) (ha : a ≠ 0) :
    ((Fin r → J) × scalarCanonicalLattice K b r a ha) ≃
      scalarIdealLattice K b (J.comap (residueMap K q)) r ((q : ℝ)⁻¹ * a)
        (mul_ne_zero (inv_ne_zero (Nat.cast_ne_zero.mpr (NeZero.ne q))) ha) :=
  ((Equiv.prodCongr (Equiv.refl _) (scalarCanonicalEquiv K b r a ha).symm.toEquiv).trans
    (idealResidueCosetEquiv K q J r)).trans
      (scalarIdealEquiv K b (J.comap (residueMap K q)) r ((q : ℝ)⁻¹ * a) _)

@[simp] theorem scalarIdealCosetEquiv_apply (b : Basis (Fin d) ℤ (𝓞 K)) (q : ℕ) [NeZero q]
    (J : Ideal (ResidueRing K q)) (r : ℕ) (a : ℝ) (ha : a ≠ 0)
    (y : Fin r → J) (u : scalarCanonicalLattice K b r a ha) :
    (scalarIdealCosetEquiv K b q J r a ha (y, u) : Euclidean (r * d)) =
      (u : Euclidean (r * d)) + (q : ℝ)⁻¹ • a •
        canonicalEuclideanEmbedding K b r (residueVectorLift K q (fun i => (y i : ResidueRing K q))) := by
  let v := (scalarCanonicalEquiv K b r a ha).symm u
  have hv : a • canonicalEuclideanEmbedding K b r v = (u : Euclidean (r * d)) :=
    congrArg (fun x : scalarCanonicalLattice K b r a ha => (x : Euclidean (r * d)))
      ((scalarCanonicalEquiv K b r a ha).apply_symm_apply u)
  change ((q : ℝ)⁻¹ * a) • canonicalEuclideanEmbedding K b r
    (fun i => residueVectorLift K q (fun j => (y j : ResidueRing K q)) i + (q : 𝓞 K) * v i) = _
  rw [mul_smul]
  have he : (fun i => residueVectorLift K q (fun j => (y j : ResidueRing K q)) i + (q : 𝓞 K) * v i) =
      residueVectorLift K q (fun j => (y j : ResidueRing K q)) + (q : ℤ) • v := by
    funext i
    change _ = residueVectorLift K q (fun j => (y j : ResidueRing K q)) i + (q : ℤ) • v i
    simp only [zsmul_eq_mul, Int.cast_natCast]
  rw [he, scalar_modulus_embedding, hv]

theorem scalarIdealCosetMass_sum (b : Basis (Fin d) ℤ (𝓞 K)) (q : ℕ) [NeZero q]
    (J : Ideal (ResidueRing K q)) (r : ℕ) (a : ℝ) (ha : a ≠ 0) (t : ℝ) :
    (∑ y : Fin r → J, nonzeroCosetMass (scalarCanonicalLattice K b r a ha) t
      ((q : ℝ)⁻¹ • a • canonicalEuclideanEmbedding K b r
        (residueVectorLift K q (fun i => (y i : ResidueRing K q))))) =
      gaussianMass t (scalarIdealLattice K b (J.comap (residueMap K q)) r ((q : ℝ)⁻¹ * a)
        (mul_ne_zero (inv_ne_zero (Nat.cast_ne_zero.mpr (NeZero.ne q))) ha) : Set (Euclidean (r * d))) - 1 := by
  rw [← nonzeroCosetMass_eq_mass_sub_one]
  have h := (scalarIdealCosetEquiv K b q J r a ha).tsum_eq (fun x =>
    if (x : Euclidean (r * d)) = 0 then 0 else ENNReal.ofReal (gaussianWeight t (x : Euclidean (r * d))))
  rw [ENNReal.tsum_prod', tsum_fintype] at h
  apply Eq.trans ?_ (Eq.trans h ?_)
  · apply Finset.sum_congr rfl
    intro y _
    unfold nonzeroCosetMass
    apply tsum_congr
    intro u
    rw [scalarIdealCosetEquiv_apply]
    by_cases hz : (u : Euclidean (r * d)) + (q : ℝ)⁻¹ • a •
        canonicalEuclideanEmbedding K b r (residueVectorLift K q (fun i => (y i : ResidueRing K q))) = 0
    · simp only [hz, ite_true]
    · simp only [hz, ite_false]
  · unfold nonzeroCosetMass
    apply tsum_congr
    intro x
    by_cases hz : (x : Euclidean (r * d)) = 0 <;> simp [hz]

theorem scalarCosetMass_eq_lift (b : Basis (Fin d) ℤ (𝓞 K)) (q : ℕ) [NeZero q]
    (a : ℝ) (ha : a ≠ 0) (t : ℝ) (v : Fin r → 𝓞 K) :
    nonzeroCosetMass (scalarCanonicalLattice K b r a ha) t
      ((q : ℝ)⁻¹ • a • canonicalEuclideanEmbedding K b r v) =
    nonzeroCosetMass (scalarCanonicalLattice K b r a ha) t
      ((q : ℝ)⁻¹ • a • canonicalEuclideanEmbedding K b r
        (residueVectorLift K q (fun i => residueMap K q (v i)))) := by
  obtain ⟨s, w, hw⟩ := residueVectorLift_decomposition K q v
  have hs : (fun i => residueMap K q (v i)) = s := by
    funext i
    rw [congrFun hw i]
    change residueMap K q (residueVectorLift K q s i + (q : ℤ) • w i) = s i
    simp only [zsmul_eq_mul, Int.cast_natCast,
      map_add, map_mul, map_natCast, residueMap_modulus, zero_mul, add_zero,
      residueVectorLift_map]
  rw [hs, hw, scalar_modulus_embedding]
  apply nonzeroCosetMass_add_mem
  exact ⟨canonicalEuclideanEmbedding K b r w, ⟨w, rfl⟩, rfl⟩

def integralDotLift (q : ℕ) (σ : 𝓞 K ≃+* 𝓞 K)
    (A : Matrix (Fin n) (Fin m) (ResidueRing K q)) (s : Fin n → ResidueRing K q) :
    Fin m → 𝓞 K := ((residueMatrixLift K q A).map σ).transpose *ᵥ residueVectorLift K q s

omit [NumberField K] in
theorem integralDotLift_residue (q : ℕ) (σ : 𝓞 K ≃+* 𝓞 K)
    (A : Matrix (Fin n) (Fin m) (ResidueRing K q)) (s : Fin n → ResidueRing K q) (j : Fin m) :
    residueMap K q (integralDotLift K q σ A s j) =
      (dotImageColumns s m (A.map (residueRingEquiv K q σ)) j : ResidueRing K q) := by
  change residueMap K q (∑ i, σ (residueMatrixLift K q A i j) * residueVectorLift K q s i) =
    ∑ i, residueRingEquiv K q σ (A i j) * s i
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hA := congrFun (congrFun (residueMatrixLift_automorphism K q σ A) i) j
  change residueMap K q (σ (residueMatrixLift K q A i j)) = residueRingEquiv K q σ (A i j) at hA
  rw [map_mul, residueVectorLift_map, hA]

theorem uniform_integralDotCosetMass_expectation (b : Basis (Fin d) ℤ (𝓞 K))
    (q : ℕ) [NeZero q] (σ : 𝓞 K ≃+* 𝓞 K) (s : Fin n → ResidueRing K q)
    (m : ℕ) (a : ℝ) (ha : a ≠ 0) (t : ℝ) :
    (∑ A : Matrix (Fin n) (Fin m) (ResidueRing K q),
      PMF.uniformOfFintype (Matrix (Fin n) (Fin m) (ResidueRing K q)) A *
        nonzeroCosetMass (scalarCanonicalLattice K b m a ha) t
          ((q : ℝ)⁻¹ • a • canonicalEuclideanEmbedding K b m (integralDotLift K q σ A s))) =
      ((Fintype.card (dotImageIdeal s) : ℝ≥0∞) ^ m)⁻¹ *
        (gaussianMass t (scalarIdealLattice K b (residueDotIdeal K q s) m ((q : ℝ)⁻¹ * a)
          (mul_ne_zero (inv_ne_zero (Nat.cast_ne_zero.mpr (NeZero.ne q))) ha) : Set (Euclidean (m * d))) - 1) := by
  let w : (Fin m → dotImageIdeal s) → ℝ≥0∞ := fun y =>
    nonzeroCosetMass (scalarCanonicalLattice K b m a ha) t
      ((q : ℝ)⁻¹ • a • canonicalEuclideanEmbedding K b m
        (residueVectorLift K q (fun i => (y i : ResidueRing K q))))
  have hm (A : Matrix (Fin n) (Fin m) (ResidueRing K q)) :
      nonzeroCosetMass (scalarCanonicalLattice K b m a ha) t
        ((q : ℝ)⁻¹ • a • canonicalEuclideanEmbedding K b m (integralDotLift K q σ A s)) =
      w (dotImageColumns s m (A.map (residueRingEquiv K q σ))) := by
    rw [scalarCosetMass_eq_lift]
    have hv : (fun i => residueMap K q (integralDotLift K q σ A s i)) =
        (fun i => (dotImageColumns s m (A.map (residueRingEquiv K q σ)) i : ResidueRing K q)) :=
      funext (integralDotLift_residue K q σ A s)
    rw [hv]
  simp_rw [hm]
  rw [finite_pmf_expectation_map, uniform_automorphism_dotImageColumns]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow,
    ← Finset.mul_sum]
  congr 1
  exact scalarIdealCosetMass_sum K b q (dotImageIdeal s) m a ha t

theorem uniform_integralDotCosetMass_expectation_power (b : Basis (Fin d) ℤ (𝓞 K))
    (q : ℕ) [NeZero q] (σ : 𝓞 K ≃+* 𝓞 K) (s : Fin n → ResidueRing K q)
    (m : ℕ) (a : ℝ) (ha : a ≠ 0) (t : ℝ) :
    (∑ A : Matrix (Fin n) (Fin m) (ResidueRing K q),
      PMF.uniformOfFintype (Matrix (Fin n) (Fin m) (ResidueRing K q)) A *
        nonzeroCosetMass (scalarCanonicalLattice K b m a ha) t
          ((q : ℝ)⁻¹ • a • canonicalEuclideanEmbedding K b m (integralDotLift K q σ A s))) =
      ((Fintype.card (dotImageIdeal s) : ℝ≥0∞) ^ m)⁻¹ *
        (gaussianMass (t * ((q : ℝ)⁻¹ * a))
          (idealEuclideanLattice K b (residueDotIdeal K q s) 1 : Set (Euclidean (1 * d))) ^ m - 1) := by
  rw [uniform_integralDotCosetMass_expectation, scalarIdealLattice, gaussianMass_scalar_image,
    idealGaussianMass_power]

theorem cyclotomicModularLattice_expected_nonzeroDualMass_le
    (N : ℕ) [NeZero N] [IsCyclotomicExtension {N} ℚ K]
    (b : Basis (Fin d) ℤ (𝓞 K)) {c : ℝ} (hc : 0 < c)
    (hGram : ∀ i j, canonicalGram K b i j = if i = j then c else 0)
    (q : ℕ) [NeZero q] (r n : ℕ) (t : ℝ) :
    (∑ A : Matrix (Fin n) (Fin r) (ResidueRing K q),
      PMF.uniformOfFintype (Matrix (Fin n) (Fin r) (ResidueRing K q)) A *
        nonzeroDualMass (numberFieldModularLattice K b q A) t) ≤
      ∑ s : Fin n → ResidueRing K q, ((Fintype.card (dotImageIdeal s) : ℝ≥0∞) ^ r)⁻¹ *
        (gaussianMass (t * ((q : ℝ)⁻¹ * c⁻¹))
          (idealEuclideanLattice K b (residueDotIdeal K q s) 1 : Set (Euclidean (1 * d))) ^ r - 1) := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun A _ =>
    mul_le_mul' (le_refl (PMF.uniformOfFintype (Matrix (Fin n) (Fin r) (ResidueRing K q)) A))
      (cyclotomicModularLattice_nonzeroDualMass_le_cosets K N b hc hGram q A t))
  apply h.trans_eq
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  exact uniform_integralDotCosetMass_expectation_power K b q
    (cyclotomicIntegerConjugation K N) s r c⁻¹ (inv_ne_zero hc.ne') t

theorem cyclotomicModularLattice_expected_nonzeroDualMass_explicit
    (N : ℕ) [NeZero N] [IsCyclotomicExtension {N} ℚ K]
    (b : Basis (Fin d) ℤ (𝓞 K)) {c : ℝ} (hc : 0 < c)
    (hGram : ∀ i j, canonicalGram K b i j = if i = j then c else 0)
    (q : ℕ) [NeZero q] (r n ℓ : ℕ) (hℓ : 1 ≤ ℓ) {t : ℝ} (ht : 0 < t) :
    (∑ A : Matrix (Fin n) (Fin r) (ResidueRing K q),
      PMF.uniformOfFintype (Matrix (Fin n) (Fin r) (ResidueRing K q)) A *
        nonzeroDualMass (numberFieldModularLattice K b q A) t) ≤
      ∑ s : Fin n → ResidueRing K q, ((Fintype.card (dotImageIdeal s) : ℝ≥0∞) ^ r)⁻¹ *
        ((ENNReal.ofReal (max 1 ((4 * Real.sqrt ℓ /
          ((t * ((q : ℝ)⁻¹ * c⁻¹)) * (Ideal.absNorm (residueDotIdeal K q s) : ℝ) ^ (1 / (d : ℝ)))) ^ d) *
          (1 + 2 * (2 : ℝ) ^ (-(3 * (d : ℝ) * ℓ))))) ^ r - 1) := by
  apply (cyclotomicModularLattice_expected_nonzeroDualMass_le K N b hc hGram q r n t).trans
  apply Finset.sum_le_sum
  intro s _
  have hscale : 0 < t * ((q : ℝ)⁻¹ * c⁻¹) := by
    have hq : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
    positivity
  have hI := idealGaussianMass_all_widths K b (residueDotIdeal K q s) q
    (modulus_mem_residueDotIdeal K q s) ℓ hℓ hscale
  exact mul_le_mul' le_rfl (tsub_le_tsub_right (pow_le_pow_left' hI r) 1)

end SISToKSIS

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped ENNReal Classical
namespace SISToKSIS
variable {R : Type*} [CommRing R] [Fintype R] {n r : ℕ}

theorem dotImageIdeal_fiber_card_le (J : Ideal R) :
    Fintype.card {s : Fin n → R // dotImageIdeal s = J} ≤ Fintype.card J ^ n := by
  let f : {s : Fin n → R // dotImageIdeal s = J} → (Fin n → J) := fun s i =>
    ⟨s.1 i, (congrArg (fun J' : Ideal R => s.1 i ∈ J') s.2).mp
      (Ideal.subset_span ⟨i, rfl⟩)⟩
  have hf : Function.Injective f := by
    intro s t h
    apply Subtype.ext
    funext i
    exact congrArg (fun v : Fin n → J => (v i : R)) h
  simpa only [Fintype.card_fun, Fintype.card_fin] using Fintype.card_le_of_injective f hf

theorem sum_dotImageIdeal_inv_pow_le (hnr : n ≤ r) :
    (∑ s : Fin n → R, ((Fintype.card (dotImageIdeal s) : ℝ≥0∞) ^ r)⁻¹) ≤
      Fintype.card (Ideal R) := by
  rw [← Fintype.sum_fiberwise' (fun s : Fin n → R => dotImageIdeal s)
    (fun J : Ideal R => ((Fintype.card J : ℝ≥0∞) ^ r)⁻¹)]
  calc
    _ = ∑ J : Ideal R, (Fintype.card {s : Fin n → R // dotImageIdeal s = J} : ℝ≥0∞) *
        ((Fintype.card J : ℝ≥0∞) ^ r)⁻¹ := by simp
    _ ≤ ∑ _J : Ideal R, (1 : ℝ≥0∞) := by
      apply Finset.sum_le_sum
      intro J _
      have hcard : Fintype.card {s : Fin n → R // dotImageIdeal s = J} ≤ Fintype.card J ^ r :=
        (dotImageIdeal_fiber_card_le J).trans
          (pow_le_pow_right' (Fintype.card_pos_iff.mpr ⟨0⟩) hnr)
      have hcast : (Fintype.card {s : Fin n → R // dotImageIdeal s = J} : ℝ≥0∞) ≤
          (Fintype.card J : ℝ≥0∞) ^ r := by exact_mod_cast hcard
      have hJ : (Fintype.card J : ℝ≥0∞) ^ r ≠ 0 := by positivity
      exact (mul_le_mul' hcast le_rfl).trans_eq (ENNReal.mul_inv_cancel hJ (by finiteness))
    _ = _ := by simp

theorem ideal_card_of_field_product {g : ℕ} {F : Fin g → Type*} [∀ j, Field (F j)]
    (e : R ≃+* ∀ j, F j) : Fintype.card (Ideal R) = 2 ^ g := by
  let f : Ideal R ≃ (Fin g → Fin 2) :=
    e.idealComapOrderIso.symm.toEquiv |>.trans
      (Ideal.piOrderIso.toEquiv.trans (Equiv.piCongrRight (fun j => Ideal.equivFinTwo (F j))))
  exact (Fintype.card_congr f).trans (by simp)

theorem sum_dotImageIdeal_inv_pow_le_of_field_product {g : ℕ}
    {F : Fin g → Type*} [∀ j, Field (F j)] (e : R ≃+* ∀ j, F j) (hnr : n ≤ r) :
    (∑ s : Fin n → R, ((Fintype.card (dotImageIdeal s) : ℝ≥0∞) ^ r)⁻¹) ≤ (2 : ℝ≥0∞) ^ g := by
  have h := sum_dotImageIdeal_inv_pow_le (R := R) hnr
  simpa only [ideal_card_of_field_product e, Nat.cast_pow, Nat.cast_ofNat] using h

section Quotient
variable {S : Type*} [CommRing S] {g : ℕ}
local instance quotientFactorField (I : Ideal S) [I.IsMaximal] : Field (S ⧸ I) :=
  Ideal.Quotient.field I

theorem quotient_ideal_card_of_factorization (J : Ideal S) [Fintype (S ⧸ J)]
    (I : Fin g → Ideal S) [∀ j, (I j).IsMaximal]
    (hI : Function.Injective I) (hfac : J = ∏ j, I j) :
    Fintype.card (Ideal (S ⧸ J)) = 2 ^ g := by
  have hp : Pairwise (fun a b => IsCoprime (I a) (I b)) :=
    fun a b hab => Ideal.isCoprime_of_isMaximal (hI.ne hab)
  have hJI : J = ⨅ j, I j := by
    rw [hfac, Ideal.prod_eq_iInf_of_pairwise_isCoprime]
    · simp
    · intro a _ b _ hab
      exact hp hab
  exact ideal_card_of_field_product
    ((Ideal.quotEquivOfEq hJI).trans (Ideal.quotientInfRingEquivPiQuotient I hp))
end Quotient
end SISToKSIS
