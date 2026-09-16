import GeometricGaussianLHL.SpectralBounds

/-!
# Operator norm bounds for extraction

The projections may be those of a Euclidean orthogonal sum. Their norms are
charged explicitly, so the proof does not confuse a maximum-column matrix norm
with the operator norm on canonical solution vectors.
-/

namespace SISToKSIS

section Operators

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

def extractionOperator (a : F →L[ℝ] E) (r : E →L[ℝ] F)
    (p : G →L[ℝ] E) (q : G →L[ℝ] F) : G →L[ℝ] E :=
  -p - a.comp (r.comp p) + a.comp q

theorem extractionOperator_norm_le (a : F →L[ℝ] E) (r : E →L[ℝ] F)
    (p : G →L[ℝ] E) (q : G →L[ℝ] F) (hp : ‖p‖ ≤ 1) (hq : ‖q‖ ≤ 1) :
    ‖extractionOperator a r p q‖ ≤ 1 + ‖a‖ * ‖r‖ + ‖a‖ := by
  have hcomp := (a.opNorm_comp_le (r.comp p)).trans
    (mul_le_mul_of_nonneg_left (r.opNorm_comp_le p) (norm_nonneg a))
  have hp' : ‖a‖ * (‖r‖ * ‖p‖) ≤ ‖a‖ * ‖r‖ := by
    nlinarith [norm_nonneg a, norm_nonneg r,
      mul_le_mul_of_nonneg_left hp (mul_nonneg (norm_nonneg a) (norm_nonneg r))]
  have hq' : ‖a.comp q‖ ≤ ‖a‖ :=
    (a.opNorm_comp_le q).trans (by simpa using mul_le_mul_of_nonneg_left hq (norm_nonneg a))
  have htri := (norm_add_le (-p - a.comp (r.comp p)) (a.comp q)).trans
    (add_le_add (norm_sub_le (-p) (a.comp (r.comp p))) le_rfl)
  simp only [norm_neg] at htri
  change ‖-p - a.comp (r.comp p) + a.comp q‖ ≤ _
  linarith [hcomp.trans hp']

/-- Combines the explicit spectral constants already proved by GeometricGaussianLHL. -/
theorem spectral_extraction_constant {a r s₁ s₂ M : ℝ}
    (hr : 0 ≤ r) (hs₁ : 0 < s₁) (hM : 1 ≤ M)
    (hs : s₁ ≤ s₂) (hscale : 1 ≤ s₂ * M)
    (ha_bound : a ≤ 4 * s₁ * M) (hr_bound : r ≤ 8192 * s₂ / s₁) :
    1 + a * r + a ≤ 32773 * s₂ * M := by
  have hp := mul_le_mul ha_bound hr_bound hr (by positivity : 0 ≤ 4 * s₁ * M)
  have hprod : (4 * s₁ * M) * (8192 * s₂ / s₁) = 32768 * s₂ * M := by
    field_simp
    ring
  rw [hprod] at hp
  have hsM := mul_le_mul_of_nonneg_right hs (by linarith : 0 ≤ M)
  linarith

end Operators

end SISToKSIS
