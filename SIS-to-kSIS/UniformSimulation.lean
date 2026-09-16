import «SIS-to-kSIS».BlockAlgebra
import «SIS-to-kSIS».ReverseSampling
import Mathlib.GroupTheory.Index
import Mathlib.Data.Fintype.BigOperators

/-!
# Exact uniform simulation for the generated hints

For each generated hint matrix, composing a uniform source linear map with
extraction is exactly uniform among maps annihilating the hints. This equality
needs no exceptional event, prime modulus, or field structure.
-/

namespace SISToKSIS

section Algebra

variable {R M N P : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P]

theorem hint_extract_decomposition (a : N →ₗ[R] M) (r : M →ₗ[R] N) (v : M × N) :
    hintMap a r (hintCoefficients r v) + extractSection r (extractMap a r v) = v := by
  rw [hint_reconstruction]
  ext <;> simp [extractSection] <;> abel

def AnnihilatingMaps (a : N →ₗ[R] M) (r : M →ₗ[R] N) :=
  {b : M × N →ₗ[R] P // b.comp (hintMap a r) = 0}

instance (a : N →ₗ[R] M) (r : M →ₗ[R] N) :
    Nonempty (AnnihilatingMaps (P := P) a r) := ⟨⟨0, by simp⟩⟩

/-- A constructive bijection from source public matrices to compatible public matrices. -/
def publicMapEquiv (a : N →ₗ[R] M) (r : M →ₗ[R] N) :
    (M →ₗ[R] P) ≃ AnnihilatingMaps (P := P) a r where
  toFun b := ⟨b.comp (extractMap a r), by
    apply LinearMap.ext
    intro c
    simp only [LinearMap.comp_apply, extract_hint, map_zero, LinearMap.zero_apply]⟩
  invFun b := b.1.comp (extractSection r)
  left_inv b := by
    apply LinearMap.ext
    intro v
    simp only [LinearMap.comp_apply, extract_section]
  right_inv b := by
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    have hz : b.1 (hintMap a r (hintCoefficients r v)) = 0 :=
      LinearMap.congr_fun b.2 _
    have hv := congrArg b.1 (hint_extract_decomposition a r v)
    simpa only [map_add, hz, zero_add, LinearMap.comp_apply] using hv

end Algebra

section MatrixSimulation

open Matrix
open scoped Classical
variable {R : Type*} [CommRing R] {m n k : ℕ}

/-- Matrix of the explicit right inverse to extraction. -/
def extractionSectionMatrix (Z : Matrix (Fin m) (Fin k) R) :
    Matrix (Fin m ⊕ Fin k) (Fin m) R := fromRows (-1) (-Zᵀ)

theorem extractionSectionMatrix_apply (Z : Matrix (Fin m) (Fin k) R) (v : Fin m → R) :
    extractionSectionMatrix Z *ᵥ v =
      Sum.elim (extractSection Zᵀ.toLin' v).1 (extractSection Zᵀ.toLin' v).2 := by
  simp [extractionSectionMatrix, extractSection, Matrix.toLin'_apply, Matrix.neg_mulVec, Matrix.one_mulVec]

theorem extraction_mul_section (X : Matrix (Fin k) (Fin m) R)
    (Z : Matrix (Fin m) (Fin k) R) :
    extractionMatrix X Z * extractionSectionMatrix Z = 1 := by
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  rw [← Matrix.mulVec_mulVec, extractionSectionMatrix_apply, extractionMatrix_apply]
  change extractMap Xᵀ.toLin' Zᵀ.toLin' (extractSection Zᵀ.toLin' v) = 1 *ᵥ v
  rw [extract_section, Matrix.one_mulVec]

theorem matrix_hint_extract_decomposition (X : Matrix (Fin k) (Fin m) R)
    (Z : Matrix (Fin m) (Fin k) R) (v : Fin m ⊕ Fin k → R) :
    columnHints X Z *ᵥ hintCoefficients Zᵀ.toLin' (v ∘ Sum.inl, v ∘ Sum.inr) +
      extractionSectionMatrix Z *ᵥ (extractionMatrix X Z *ᵥ v) = v := by
  rw [columnHints_apply, extractionSectionMatrix_apply, extractionMatrix_apply]
  have h := hint_extract_decomposition Xᵀ.toLin' Zᵀ.toLin' (v ∘ Sum.inl, v ∘ Sum.inr)
  funext i
  cases i with
  | inl i => exact congrFun (congrArg Prod.fst h) i
  | inr i => exact congrFun (congrArg Prod.snd h) i

theorem compatible_matrix_reconstruction (X : Matrix (Fin k) (Fin m) R)
    (Z : Matrix (Fin m) (Fin k) R) (A : Matrix (Fin n) (Fin m ⊕ Fin k) R)
    (hA : A * columnHints X Z = 0) :
    (A * extractionSectionMatrix Z) * extractionMatrix X Z = A := by
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  have h := congrArg (fun w => A *ᵥ w) (matrix_hint_extract_decomposition X Z v)
  rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, hA, Matrix.zero_mulVec, zero_add,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec] at h
  exact h

/-- The source matrix maps bijectively onto all public matrices compatible with
these generated hints, over any commutative ring. -/
def publicMatrixEquiv (X : Matrix (Fin k) (Fin m) R)
    (Z : Matrix (Fin m) (Fin k) R) :
    Matrix (Fin n) (Fin m) R ≃
      {A : Matrix (Fin n) (Fin m ⊕ Fin k) R // A * columnHints X Z = 0} where
  toFun B := ⟨B * extractionMatrix X Z, by
    rw [Matrix.mul_assoc, extraction_mul_columnHints, Matrix.mul_zero]⟩
  invFun A := A.1 * extractionSectionMatrix Z
  left_inv B := by
    change (B * extractionMatrix X Z) * extractionSectionMatrix Z = B
    rw [Matrix.mul_assoc, extraction_mul_section, Matrix.mul_one]
  right_inv A := Subtype.ext (compatible_matrix_reconstruction X Z A.1 A.2)

instance generatedCompatibleMatrix_nonempty (X : Matrix (Fin k) (Fin m) R)
    (Z : Matrix (Fin m) (Fin k) R) :
    Nonempty {A : Matrix (Fin n) (Fin m ⊕ Fin k) R // A * columnHints X Z = 0} :=
  ⟨⟨0, Matrix.zero_mul _⟩⟩


end MatrixSimulation

section Probability

noncomputable section

open GeometricGaussianLHL
open scoped ENNReal

theorem uniform_map_equiv {α β : Type*} [Fintype α] [Fintype β]
    [Nonempty α] [Nonempty β] (e : α ≃ β) :
    (PMF.uniformOfFintype α).map e = PMF.uniformOfFintype β := by
  classical
  ext y
  obtain ⟨x, rfl⟩ := e.surjective y
  rw [PMF.map_apply]
  simp only [e.injective.eq_iff, tsum_ite_eq', PMF.uniformOfFintype_apply,
    Fintype.card_congr e]

variable {R M N P : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P]

/-- The final algebraic hybrid in the reverse-sampling argument is an exact equality. -/
theorem uniform_publicMap (a : N →ₗ[R] M) (r : M →ₗ[R] N)
    [Fintype (M →ₗ[R] P)] [Fintype (AnnihilatingMaps (P := P) a r)] :
    (PMF.uniformOfFintype (M →ₗ[R] P)).map (publicMapEquiv a r) =
      PMF.uniformOfFintype (AnnihilatingMaps (P := P) a r) :=
  uniform_map_equiv (publicMapEquiv a r)

theorem uniform_map_surjective_addHom {G H : Type*} [AddGroup G] [AddGroup H]
    [Fintype G] [Fintype H] (f : G →+ H) (hf : Function.Surjective f) :
    (PMF.uniformOfFintype G).map f = PMF.uniformOfFintype H := by
  classical
  let p := (PMF.uniformOfFintype G).map f
  have hp (y : H) : p y =
      ((Finset.univ.filter (fun x => f x = y)).card : ℝ≥0∞) / Fintype.card G := by
    rw [PMF.map_apply, tsum_fintype]
    simp only [PMF.uniformOfFintype_apply]
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv, eq_comm]
  have hc (x y : H) : p x = p y := by
    rw [hp, hp, AddMonoidHom.card_fiber_eq_of_mem_range f (hf x) (hf y)]
  ext y
  rw [PMF.uniformOfFintype_apply]
  apply ENNReal.eq_inv_of_mul_eq_one_left
  have he : (∑ x, p x) = (Fintype.card H : ℝ≥0∞) * p y := by
    calc
      _ = ∑ _x : H, p y := Finset.sum_congr rfl (fun x _ => hc x y)
      _ = _ := by simp
  rw [mul_comm, ← he]
  simpa only [tsum_fintype] using p.tsum_coe

def coordinateAddHom {G H ι : Type*} [AddMonoid G] [AddMonoid H]
    (f : G →+ H) : (ι → G) →+ (ι → H) where
  toFun x i := f (x i)
  map_zero' := by ext i; exact f.map_zero
  map_add' x y := by ext i; exact f.map_add _ _

theorem coordinateAddHom_surjective {G H ι : Type*} [AddMonoid G] [AddMonoid H]
    (f : G →+ H) (hf : Function.Surjective f) :
    Function.Surjective (coordinateAddHom (ι := ι) f) := by
  intro y
  refine ⟨fun i => Classical.choose (hf (y i)), ?_⟩
  funext i
  exact Classical.choose_spec (hf (y i))

section Matrices
variable {R : Type*} [CommRing R] {m n k : ℕ}
open scoped Classical

theorem uniform_publicMatrix [Fintype R] (X : Matrix (Fin k) (Fin m) R)
    (Z : Matrix (Fin m) (Fin k) R) :
    (PMF.uniformOfFintype (Matrix (Fin n) (Fin m) R)).map (publicMatrixEquiv X Z) =
      PMF.uniformOfFintype {A : Matrix (Fin n) (Fin m ⊕ Fin k) R //
        A * columnHints X Z = 0} :=
  uniform_map_equiv (publicMatrixEquiv X Z)


/-- The same source-to-public bijection in the single finite-index format used
by the modular Gaussian games. -/
def publicMatrixFlatEquiv (X : Matrix (Fin k) (Fin m) R)
    (Z : Matrix (Fin m) (Fin k) R) :
    Matrix (Fin n) (Fin m) R ≃
      {A : Matrix (Fin n) (Fin (m + k)) R //
        A * (columnHints X Z).submatrix finSumFinEquiv.symm id = 0} :=
  (publicMatrixEquiv X Z).trans
    ((Matrix.reindex (Equiv.refl (Fin n)) finSumFinEquiv).subtypeEquiv (by
      intro A
      simp only [Matrix.reindex_apply, Equiv.refl_symm, Equiv.coe_refl,
        Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id]))

/-- Exact conditioning for the concrete matrix algorithm. The event always
contains the zero public matrix. -/
theorem uniform_publicMatrix_conditioned [Fintype R]
    (X : Matrix (Fin k) (Fin m) R) (Z : Matrix (Fin m) (Fin k) R)
    (hE : ∃ A : Matrix (Fin n) (Fin (m + k)) R,
      A * (columnHints X Z).submatrix finSumFinEquiv.symm id = 0 ∧
        A ∈ (PMF.uniformOfFintype (Matrix (Fin n) (Fin (m + k)) R)).support) :
    (PMF.uniformOfFintype (Matrix (Fin n) (Fin m) R)).map
      (fun B => (B * extractionMatrix X Z).submatrix id finSumFinEquiv.symm) =
      (PMF.uniformOfFintype (Matrix (Fin n) (Fin (m + k)) R)).filter
        {A | A * (columnHints X Z).submatrix finSumFinEquiv.symm id = 0} hE :=
  uniform_filter_equiv _ (publicMatrixFlatEquiv X Z) hE


def publicHintProduct (H : Matrix (Fin m) (Fin k) R) :
    Matrix (Fin n) (Fin m) R →+ Matrix (Fin n) (Fin k) R where
  toFun A := A * H
  map_zero' := Matrix.zero_mul H
  map_add' A B := Matrix.add_mul A B H

theorem publicHintProduct_surjective (H : Matrix (Fin m) (Fin k) R)
    (L : Matrix (Fin k) (Fin m) R) (hLH : L * H = 1) :
    Function.Surjective (publicHintProduct (n := n) H) := by
  intro V
  refine ⟨V * L, ?_⟩
  change (V * L) * H = V
  rw [Matrix.mul_assoc, hLH, Matrix.mul_one]

theorem uniform_publicHintProduct [Fintype R] (H : Matrix (Fin m) (Fin k) R)
    (L : Matrix (Fin k) (Fin m) R) (hLH : L * H = 1) :
    (PMF.uniformOfFintype (Matrix (Fin n) (Fin m) R)).map (publicHintProduct H) =
      PMF.uniformOfFintype (Matrix (Fin n) (Fin k) R) :=
  uniform_map_surjective_addHom _ (publicHintProduct_surjective H L hLH)

/-- Exact compatibility mass over any finite commutative ring, from an actual
left inverse of the hint matrix. -/
theorem uniform_compatibility_probability [Fintype R]
    (H : Matrix (Fin m) (Fin k) R) (L : Matrix (Fin k) (Fin m) R)
    (hLH : L * H = 1) (V : Matrix (Fin n) (Fin k) R) :
    (PMF.uniformOfFintype (Matrix (Fin n) (Fin m) R)).toOuterMeasure {A | A * H = V} =
      ((Fintype.card R : ℝ≥0∞) ^ (k * n))⁻¹ := by
  have h := congrArg (fun p : PMF (Matrix (Fin n) (Fin k) R) => p.toOuterMeasure {V})
    (uniform_publicHintProduct H L hLH)
  rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_apply_singleton,
    PMF.uniformOfFintype_apply] at h
  have hc : Fintype.card (Matrix (Fin n) (Fin k) R) = Fintype.card R ^ (k * n) := by
    classical
    change Fintype.card (Fin n → Fin k → R) = _
    rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, ← pow_mul]
  change (PMF.uniformOfFintype (Matrix (Fin n) (Fin m) R)).toOuterMeasure
    {A | A * H = V} = (Fintype.card (Matrix (Fin n) (Fin k) R) : ℝ≥0∞)⁻¹ at h
  simpa only [hc, Nat.cast_pow] using h

end Matrices
end

end Probability

end SISToKSIS
