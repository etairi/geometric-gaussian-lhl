import Mathlib.LinearAlgebra.Prod
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Exact algebra of the SIS-to-k-SIS reduction

The reduction's block identities hold over every commutative ring. In particular,
the kernel calculation is exact before reduction modulo the modulus. We use
products for the two coordinate blocks and later identify them with matrices.
-/

namespace SISToKSIS

section Linear

variable {R M N : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- The transpose of the hint matrix `[X₁, X₁ R + I]`, acting on coefficients. -/
def hintMap (a : N →ₗ[R] M) (r : M →ₗ[R] N) : N →ₗ[R] M × N :=
  a.prod (r.comp a + LinearMap.id)

/-- The extraction map `Vᵀ = [-I - X₁ᵀ Rᵀ, X₁ᵀ]`. -/
def extractMap (a : N →ₗ[R] M) (r : M →ₗ[R] N) : M × N →ₗ[R] M :=
  (-LinearMap.id - a.comp r).coprod a

/-- Recovers coefficients of a vector in the hint span. -/
def hintCoefficients (r : M →ₗ[R] N) : M × N →ₗ[R] N :=
  (-r).coprod LinearMap.id

@[simp] theorem hintMap_apply (a : N →ₗ[R] M) (r : M →ₗ[R] N) (c : N) :
    hintMap a r c = (a c, r (a c) + c) := rfl

@[simp] theorem extractMap_apply (a : N →ₗ[R] M) (r : M →ₗ[R] N) (v : M × N) :
    extractMap a r v = -v.1 - a (r v.1) + a v.2 := rfl

@[simp] theorem hintCoefficients_apply (r : M →ₗ[R] N) (v : M × N) :
    hintCoefficients r v = -r v.1 + v.2 := rfl

@[simp] theorem extract_hint (a : N →ₗ[R] M) (r : M →ₗ[R] N) (c : N) :
    extractMap a r (hintMap a r c) = 0 := by
  simp
  abel

@[simp] theorem coefficients_hint (a : N →ₗ[R] M) (r : M →ₗ[R] N) (c : N) :
    hintCoefficients r (hintMap a r c) = c := by
  simp

theorem hintMap_injective (a : N →ₗ[R] M) (r : M →ₗ[R] N) :
    Function.Injective (hintMap a r) :=
  Function.LeftInverse.injective (coefficients_hint a r)

/-- Every vector decomposes into a hint combination and an extracted component. -/
theorem hint_reconstruction (a : N →ₗ[R] M) (r : M →ₗ[R] N) (v : M × N) :
    hintMap a r (hintCoefficients r v) =
      (v.1 + extractMap a r v, v.2 + r (extractMap a r v)) := by
  ext <;> simp <;> abel

theorem extract_eq_zero_iff (a : N →ₗ[R] M) (r : M →ₗ[R] N) (v : M × N) :
    extractMap a r v = 0 ↔ v ∈ LinearMap.range (hintMap a r) := by
  constructor
  · intro h
    refine ⟨hintCoefficients r v, ?_⟩
    simpa [h] using hint_reconstruction a r v
  · rintro ⟨c, rfl⟩
    exact extract_hint a r c

/-- No modular independence hypothesis is needed for exact nonzeroness. -/
theorem extract_ne_zero (a : N →ₗ[R] M) (r : M →ₗ[R] N) (v : M × N)
    (h : v ∉ LinearMap.range (hintMap a r)) : extractMap a r v ≠ 0 := by
  exact fun hz => h ((extract_eq_zero_iff a r v).mp hz)

theorem ker_extractMap (a : N →ₗ[R] M) (r : M →ₗ[R] N) :
    LinearMap.ker (extractMap a r) = LinearMap.range (hintMap a r) := by
  ext v
  exact extract_eq_zero_iff a r v

/-- A concrete right inverse to extraction, valid over the integer ring and its quotients. -/
def extractSection (r : M →ₗ[R] N) : M →ₗ[R] M × N :=
  (-LinearMap.id).prod (-r)

@[simp] theorem extract_section (a : N →ₗ[R] M) (r : M →ₗ[R] N) (x : M) :
    extractMap a r (extractSection r x) = x := by
  simp [extractSection]

theorem extractMap_surjective (a : N →ₗ[R] M) (r : M →ₗ[R] N) :
    Function.Surjective (extractMap a r) :=
  Function.RightInverse.surjective (extract_section a r)

/-- The corrected unimodular coordinate transformation, specified by an explicit inverse. -/
def reductionEquiv (a : N →ₗ[R] M) (r : M →ₗ[R] N) : (M × N) ≃ₗ[R] (M × N) where
  toFun v := (extractMap a r v, hintCoefficients r v)
  invFun v := (a v.2 - v.1, r (a v.2 - v.1) + v.2)
  left_inv v := by ext <;> simp <;> abel
  right_inv v := by ext <;> simp <;> abel
  map_add' u v := Prod.ext (map_add _ _ _) (map_add _ _ _)
  map_smul' c v := Prod.ext (map_smul _ _ _) (map_smul _ _ _)

end Linear

section Matrices

open Matrix

variable {R : Type*} [CommRing R] {m k : ℕ}

/-- The generated row hint matrix. -/
def rowHints (x : Matrix (Fin k) (Fin m) R) (r : Matrix (Fin m) (Fin k) R) :
    Matrix (Fin k) (Fin m ⊕ Fin k) R :=
  fromCols x (x * r + 1)

/-- The last `m` columns of the paper's unimodular matrix. -/
def kernelColumns (x : Matrix (Fin k) (Fin m) R) (r : Matrix (Fin m) (Fin k) R) :
    Matrix (Fin m ⊕ Fin k) (Fin m) R :=
  fromRows (-1 - r * x) x

/-- The public-matrix transformation and solution-extraction matrix. -/
def extractionMatrix (x : Matrix (Fin k) (Fin m) R) (r : Matrix (Fin m) (Fin k) R) :
    Matrix (Fin m) (Fin m ⊕ Fin k) R :=
  (kernelColumns x r)ᵀ

/-- The column hint matrix supplied to the k-SIS adversary. -/
def columnHints (x : Matrix (Fin k) (Fin m) R) (r : Matrix (Fin m) (Fin k) R) :
    Matrix (Fin m ⊕ Fin k) (Fin k) R :=
  (rowHints x r)ᵀ

theorem rowHints_mul_kernelColumns (x : Matrix (Fin k) (Fin m) R)
    (r : Matrix (Fin m) (Fin k) R) : rowHints x r * kernelColumns x r = 0 := by
  simp only [rowHints, kernelColumns, fromCols_mul_fromRows, Matrix.mul_sub,
    Matrix.add_mul, Matrix.mul_neg, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]
  abel

theorem extraction_mul_columnHints (x : Matrix (Fin k) (Fin m) R)
    (r : Matrix (Fin m) (Fin k) R) : extractionMatrix x r * columnHints x r = 0 := by
  rw [extractionMatrix, columnHints, ← transpose_mul, rowHints_mul_kernelColumns,
    transpose_zero]

theorem extractionMatrix_apply (x : Matrix (Fin k) (Fin m) R)
    (r : Matrix (Fin m) (Fin k) R) (v : Fin m ⊕ Fin k → R) :
    extractionMatrix x r *ᵥ v =
      extractMap xᵀ.toLin' rᵀ.toLin' (v ∘ Sum.inl, v ∘ Sum.inr) := by
  simp [extractionMatrix, kernelColumns, transpose_fromRows, transpose_sub,
    transpose_neg, transpose_mul, sub_mulVec, neg_mulVec, Matrix.mulVec_mulVec,
    Matrix.toLin'_apply]

theorem columnHints_apply (x : Matrix (Fin k) (Fin m) R)
    (r : Matrix (Fin m) (Fin k) R) (c : Fin k → R) :
    columnHints x r *ᵥ c =
      Sum.elim (hintMap xᵀ.toLin' rᵀ.toLin' c).1
        (hintMap xᵀ.toLin' rᵀ.toLin' c).2 := by
  simp [columnHints, rowHints, transpose_fromCols, transpose_add, transpose_mul,
    add_mulVec, Matrix.mulVec_mulVec, Matrix.toLin'_apply]

/-- Exact kernel equality, over both the ring of integers and every quotient ring. -/
theorem extraction_eq_zero_iff_columnHints (x : Matrix (Fin k) (Fin m) R)
    (r : Matrix (Fin m) (Fin k) R) (v : Fin m ⊕ Fin k → R) :
    extractionMatrix x r *ᵥ v = 0 ↔ ∃ c, columnHints x r *ᵥ c = v := by
  rw [extractionMatrix_apply, extract_eq_zero_iff]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    rw [columnHints_apply, hc]
    funext i
    cases i <;> rfl
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    rw [columnHints_apply] at hc
    apply Prod.ext
    · exact congrArg (fun f => f ∘ Sum.inl) hc
    · exact congrArg (fun f => f ∘ Sum.inr) hc

theorem extraction_nonzero (x : Matrix (Fin k) (Fin m) R)
    (r : Matrix (Fin m) (Fin k) R) (v : Fin m ⊕ Fin k → R)
    (h : ¬ ∃ c, columnHints x r *ᵥ c = v) : extractionMatrix x r *ᵥ v ≠ 0 := by
  exact fun hz => h ((extraction_eq_zero_iff_columnHints x r v).mp hz)

end Matrices

end SISToKSIS
