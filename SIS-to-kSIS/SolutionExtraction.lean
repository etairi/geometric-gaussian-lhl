import «SIS-to-kSIS».BlockAlgebra
import Mathlib.Analysis.Normed.Module.Basic

/-!
# Exact solution extraction

The public equation is checked in a quotient ring, the returned vector is kept
in the coefficient ring, and exclusion from the hint span is checked in the
field. These three domains are deliberately distinguished.
-/

namespace SISToKSIS

open Matrix

section Equations

variable {R Q K : Type*} [CommRing R] [CommRing Q] [Field K]
  {m k n : ℕ}

/-- The SIS solution predicate with the strict bound used in the SIS definition in ePrint 2025/1852.
-/
def IsSISSolution (modQ : R →+* Q) (norm : (Fin m → R) → ℝ)
    (β : ℝ) (A : Matrix (Fin n) (Fin m) Q) (v : Fin m → R) : Prop :=
  v ≠ 0 ∧ A *ᵥ (modQ ∘ v) = 0 ∧ norm v < β

/-- A k-SIS solution is outside the field-linear span of the supplied hint columns.
-/
def IsKSISSolution (modQ : R →+* Q) (embed : R →+* K)
    (norm : (Fin m ⊕ Fin k → R) → ℝ) (β : ℝ)
    (B : Matrix (Fin n) (Fin m ⊕ Fin k) Q)
    (H : Matrix (Fin m ⊕ Fin k) (Fin k) R) (v : Fin m ⊕ Fin k → R) : Prop :=
  B *ᵥ (modQ ∘ v) = 0 ∧ norm v < β ∧
    embed ∘ v ∉ LinearMap.range (H.map embed).toLin'

theorem map_mulVec_eq (f : R →+* Q) {ι κ : Type*} [Fintype κ]
    (M : Matrix ι κ R) (v : κ → R) :
    f ∘ (M *ᵥ v) = M.map f *ᵥ (f ∘ v) := by
  funext i
  exact RingHom.map_mulVec f M v i

/-- Exclusion from the field span implies exact nonzero extraction in the ring. -/
theorem extraction_nonzero_of_not_field_span (embed : R →+* K)
    (x : Matrix (Fin k) (Fin m) R) (r : Matrix (Fin m) (Fin k) R)
    (v : Fin m ⊕ Fin k → R)
    (h : embed ∘ v ∉ LinearMap.range ((columnHints x r).map embed).toLin') :
    extractionMatrix x r *ᵥ v ≠ 0 := by
  apply extraction_nonzero x r v
  rintro ⟨c, hc⟩
  apply h
  refine ⟨embed ∘ c, ?_⟩
  change (columnHints x r).map embed *ᵥ (embed ∘ c) = embed ∘ v
  rw [← map_mulVec_eq, hc]

/-- The reduction preserves the modular kernel equation exactly. -/
theorem extraction_preserves_equation (modQ : R →+* Q)
    (A : Matrix (Fin n) (Fin m) Q)
    (x : Matrix (Fin k) (Fin m) R) (r : Matrix (Fin m) (Fin k) R)
    (v : Fin m ⊕ Fin k → R)
    (h : (A * (extractionMatrix x r).map modQ) *ᵥ (modQ ∘ v) = 0) :
    A *ᵥ (modQ ∘ (extractionMatrix x r *ᵥ v)) = 0 := by
  rw [map_mulVec_eq, Matrix.mulVec_mulVec]
  exact h

/-- Deterministic correctness, with the quantitative norm estimate stated explicitly. -/
theorem extract_solution (modQ : R →+* Q) (embed : R →+* K)
    (sourceNorm : (Fin m → R) → ℝ) (targetNorm : (Fin m ⊕ Fin k → R) → ℝ)
    (A : Matrix (Fin n) (Fin m) Q)
    (x : Matrix (Fin k) (Fin m) R) (r : Matrix (Fin m) (Fin k) R)
    {C β₀ β₁ : ℝ} (hC : 0 < C) (hβ : C * β₁ ≤ β₀)
    (hbound : ∀ v, sourceNorm (extractionMatrix x r *ᵥ v) ≤ C * targetNorm v)
    (v : Fin m ⊕ Fin k → R)
    (hv : IsKSISSolution modQ embed targetNorm β₁
      (A * (extractionMatrix x r).map modQ) (columnHints x r) v) :
    IsSISSolution modQ sourceNorm β₀ A (extractionMatrix x r *ᵥ v) := by
  refine ⟨extraction_nonzero_of_not_field_span embed x r v hv.2.2,
    extraction_preserves_equation modQ A x r v hv.1, ?_⟩
  exact lt_of_le_of_lt (hbound v) (lt_of_lt_of_le (mul_lt_mul_of_pos_left hv.2.1 hC) hβ)

end Equations

end SISToKSIS
