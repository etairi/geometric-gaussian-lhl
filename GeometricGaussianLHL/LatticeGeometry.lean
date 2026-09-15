import GeometricGaussianLHL.NumberFieldGeometry
import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.MeasureTheory.Group.GeometryOfNumbers
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Topology.Order.Compact

/-!
# Intrinsic lattice geometry and covolumes

This module collects the following proof sections, in dependency order.
- An elementary lower bound for Euclidean ball volume (`BallVolumeBound`).
- Intrinsic lattice covolumes (`IntrinsicCovolume`).
- The actual first minimum of a discrete lattice (`LatticeMinimum`).
- Orthogonal decomposition of a basis volume (`OrthogonalGram`).
- A quantitative Minkowski vector bound (`MinkowskiMinimum`).
- The Jacobian transverse to a kernel (`KernelJacobian`).
- Covolume in a surjective sequence of lattices (`LatticeKernelCovolume`).
- Covolume under a linear change of coordinates (`CovolumeTransport`).
- Short dual vectors in linear images of the integer lattice (`ImageDual`).
- The canonical projected-dual lower bound (`CanonicalLower`).
- The operator-norm bound for a kernel Jacobian (`KernelJacobianBound`).
- Covolume of the canonical ring lattice (`CanonicalCovolume`).
- The actual canonical matrix operator and kernel rank (`CanonicalOperator`).
- Covolume of a full lattice and its dual (`DualCovolume`).
- Covolume of the actual canonical kernel (`CanonicalKernelCovolume`).
- Duals in their intrinsic Euclidean span (`IntrinsicDual`).
- The smallest transverse stretch and the kernel Jacobian (`KernelMinimumStretch`).
- Smoothing under isometries and passage to the real span (`IsometricSmoothing`).
- Isometric transport of intrinsic duals in every rank (`IsometricDualTransport`).
- Smoothing under isometric embeddings into larger spaces (`IsometricEmbeddingSmoothing`).
-/

section BallVolumeBound

/-!
## An elementary lower bound for Euclidean ball volume

The Gamma recurrence gives `Γ(N/2+1) ≤ (N/2)^(N/2)` for every integer
dimension `N ≥ 2`. This suffices for the numerical smoothing constant in
Proposition 3.3 without an asymptotic estimate for the Gamma function.
-/

noncomputable section

open Module MeasureTheory

namespace GeometricGaussianLHL

theorem gamma_rpow_step {x : ℝ} (hx : 1 ≤ x)
    (h : Real.Gamma (x + 1) ≤ x ^ x) :
    Real.Gamma ((x + 1) + 1) ≤ (x + 1) ^ (x + 1) := by
  have hx0 : 0 ≤ x := by linarith
  have hx1 : 0 < x + 1 := by linarith
  rw [Real.Gamma_add_one hx1.ne', Real.rpow_add hx1, Real.rpow_one]
  calc
    (x + 1) * Real.Gamma (x + 1) ≤ (x + 1) * x ^ x := mul_le_mul_of_nonneg_left h hx1.le
    _ ≤ (x + 1) * (x + 1) ^ x := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hx0 (by linarith) hx0) hx1.le
    _ = _ := mul_comm _ _

theorem gamma_three_half_upper : Real.Gamma ((3 : ℝ) / 2 + 1) ≤ ((3 : ℝ) / 2) ^ ((3 : ℝ) / 2) := by
  rw [Real.Gamma_add_one (by norm_num : (3 : ℝ) / 2 ≠ 0)]
  calc
    (3 / 2 : ℝ) * Real.Gamma (3 / 2) ≤ (3 / 2 : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left Real.Gamma_three_div_two_lt_one.le (by norm_num)
    _ ≤ ((3 : ℝ) / 2) ^ ((3 : ℝ) / 2) := by
      simpa using Real.rpow_le_rpow_of_exponent_le
        (by norm_num : (1 : ℝ) ≤ 3 / 2) (by norm_num : (1 : ℝ) ≤ 3 / 2)

theorem gamma_half_dimension_le (n : ℕ) (hn : 2 ≤ n) :
    Real.Gamma ((n : ℝ) / 2 + 1) ≤ ((n : ℝ) / 2) ^ ((n : ℝ) / 2) := by
  induction n using Nat.twoStepInduction with
  | zero => omega
  | one => omega
  | more n ih _ =>
    rcases n with _ | n
    · norm_num [Real.Gamma_two]
    rcases n with _ | n
    · simpa using gamma_three_half_upper
    have hn' : 2 ≤ n + 2 := by omega
    have hx : (1 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) / 2 := by
      have : (2 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by exact_mod_cast hn'
      linarith
    have h := gamma_rpow_step hx (ih hn')
    convert h using 1 <;> congr 1 <;> push_cast <;> ring

theorem gamma_half_dimension_le_sqrt_pow (n : ℕ) (hn : 2 ≤ n) :
    Real.Gamma ((n : ℝ) / 2 + 1) ≤ Real.sqrt ((n : ℝ) / 2) ^ n := by
  have h := gamma_half_dimension_le n hn
  rw [Real.rpow_div_two_eq_sqrt _ (by positivity), Real.rpow_natCast] at h
  exact h

theorem unitBall_volume_factor_lower (n : ℕ) (hn : 2 ≤ n) :
    (Real.sqrt Real.pi / Real.sqrt ((n : ℝ) / 2)) ^ n ≤
      Real.sqrt Real.pi ^ n / Real.Gamma ((n : ℝ) / 2 + 1) := by
  rw [div_pow]
  apply div_le_div_of_nonneg_left (by positivity)
    (Real.Gamma_pos_of_pos (by positivity)) (gamma_half_dimension_le_sqrt_pow n hn)

theorem closedBall_volume_lower {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
    (hn : 2 ≤ finrank ℝ E) {r : ℝ} (hr : 0 ≤ r) :
    ENNReal.ofReal ((r * (Real.sqrt Real.pi / Real.sqrt ((finrank ℝ E : ℝ) / 2))) ^ finrank ℝ E) ≤
      volume (Metric.closedBall (0 : E) r) := by
  rw [InnerProductSpace.volume_closedBall, mul_pow, ENNReal.ofReal_mul (pow_nonneg hr _),
    ENNReal.ofReal_pow hr]
  exact mul_le_mul_right (ENNReal.ofReal_le_ofReal (unitBall_volume_factor_lower _ hn)) _

end GeometricGaussianLHL
end

end BallVolumeBound

section IntrinsicCovolume

/-!
## Intrinsic lattice covolumes

The covolume of a lower-rank lattice is measured in its real span with the
inherited inner product. An integral basis computes this volume as the
square root of its actual Gram determinant.
-/

noncomputable section

open Module MeasureTheory

namespace GeometricGaussianLHL

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def intrinsicLattice (L : Submodule ℤ E) :
    Submodule ℤ (Submodule.span ℝ (L : Set E)) :=
  L.comap ((Submodule.span ℝ (L : Set E)).restrictScalars ℤ).subtype

def intrinsicLatticeEquiv (L : Submodule ℤ E) : intrinsicLattice L ≃ₗ[ℤ] L :=
  Submodule.comapSubtypeEquivOfLe (p := L)
    (q := (Submodule.span ℝ (L : Set E)).restrictScalars ℤ) (fun _ hx => Submodule.subset_span hx)

instance intrinsicLattice_discrete (L : Submodule ℤ E) [DiscreteTopology L] :
    DiscreteTopology (intrinsicLattice L) := by
  apply ZLattice.comap_discreteTopology ℝ L
    (Submodule.span ℝ (L : Set E)).subtypeL.continuous Subtype.val_injective

instance intrinsicLattice_isZLattice (L : Submodule ℤ E) [DiscreteTopology L] :
    IsZLattice ℝ (intrinsicLattice L) := ⟨Submodule.span_span_coe_preimage⟩

theorem intrinsicLattice_rank (L : Submodule ℤ E) [DiscreteTopology L] :
    finrank ℤ L = finrank ℝ (Submodule.span ℝ (L : Set E)) := by
  rw [← (intrinsicLatticeEquiv L).finrank_eq]
  exact ZLattice.rank ℝ (intrinsicLattice L)

variable [MeasurableSpace E] [BorelSpace E]

def intrinsicCovolume (L : Submodule ℤ E) : ℝ := ZLattice.covolume (intrinsicLattice L)

theorem intrinsicCovolume_pos (L : Submodule ℤ E) [DiscreteTopology L] :
    0 < intrinsicCovolume L := ZLattice.covolume_pos (intrinsicLattice L) volume

theorem covolume_eq_sqrt_gram {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] (b : Basis ι ℤ L) :
    ZLattice.covolume L = Real.sqrt (Matrix.gram ℝ (fun i => (b i : E))).det := by
  let e : Fin (finrank ℝ E) ≃ ι := Fintype.equivOfCardEq (by
    rw [Fintype.card_fin, ← ZLattice.rank ℝ L, finrank_eq_card_basis b])
  let o : OrthonormalBasis ι ℝ E := (stdOrthonormalBasis ℝ E).reindex e
  have ho : volume.real (ZSpan.fundamentalDomain o.toBasis) = 1 := by
    rw [measureReal_congr (ZSpan.fundamentalDomain_ae_parallelepiped o.toBasis volume)]
    simp only [measureReal_def, OrthonormalBasis.coe_toBasis, o.volume_parallelepiped, ENNReal.toReal_one]
  have hG : (Matrix.gram ℝ (fun i => (b i : E))).det =
      (o.toBasis.det (fun i => (b i : E))) ^ 2 := by
    rw [Matrix.gram_eq_conjTranspose_mul o, Matrix.det_mul, Matrix.det_conjTranspose]
    simp only [star_trivial, pow_two]
    rfl
  rw [ZLattice.covolume_eq_det_mul_measureReal L volume b o.toBasis, ho, mul_one, hG, Real.sqrt_sq_eq_abs]
  rfl

theorem intrinsicCovolume_eq_sqrt_gram {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : Submodule ℤ E) [DiscreteTopology L] (b : Basis ι ℤ L) :
    intrinsicCovolume L = Real.sqrt (Matrix.gram ℝ (fun i => (b i : E))).det := by
  let b' := b.map (intrinsicLatticeEquiv L).symm
  rw [intrinsicCovolume, covolume_eq_sqrt_gram (intrinsicLattice L) b']
  rfl

end GeometricGaussianLHL
end

end IntrinsicCovolume

section LatticeMinimum

/-!
## The actual first minimum of a discrete lattice

The first minimum is the infimum of nonzero lattice-vector norms. For a
nonzero discrete lattice it is positive, attained, and bounds every such
norm from below.
-/

noncomputable section

open Module

namespace GeometricGaussianLHL

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def firstMinimum (L : Submodule ℤ E) : ℝ :=
  sInf {r : ℝ | ∃ v : E, v ∈ L ∧ v ≠ 0 ∧ ‖v‖ = r}

theorem exists_shortest_lattice_vector (L : Submodule ℤ E) [DiscreteTopology L] (hL : L ≠ ⊥) :
    ∃ v : E, v ∈ L ∧ v ≠ 0 ∧ ∀ w : E, w ∈ L → w ≠ 0 → ‖v‖ ≤ ‖w‖ := by
  have hex : ∃ w : E, w ∈ L ∧ w ≠ 0 := by
    by_contra! h
    apply hL
    exact eq_bot_iff.mpr h
  obtain ⟨w, hw, hw0⟩ := hex
  let S : Set E := {v | v ∈ Metric.closedBall 0 ‖w‖ ∩ (L : Set E) ∧ v ≠ 0}
  have hfin : (Metric.closedBall (0 : E) ‖w‖ ∩ (L : Set E)).Finite := by
    change (Metric.closedBall (0 : E) ‖w‖ ∩ L.toAddSubgroup).Finite
    have : DiscreteTopology L.toAddSubgroup := (inferInstance : DiscreteTopology L)
    exact Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete
      Metric.isBounded_closedBall inferInstance
  have hS : S.Finite := hfin.subset (fun _ hx => hx.1)
  have hwS : w ∈ S := ⟨⟨by simp, hw⟩, hw0⟩
  obtain ⟨v, hv, hmin⟩ := hS.isCompact.exists_isMinOn ⟨w, hwS⟩ continuous_norm.continuousOn
  refine ⟨v, hv.1.2, hv.2, ?_⟩
  intro z hz hz0
  by_cases hzw : ‖z‖ ≤ ‖w‖
  · exact hmin ⟨⟨by simpa using hzw, hz⟩, hz0⟩
  · exact (hmin hwS).trans (le_of_not_ge hzw)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem firstMinimum_eq_of_shortest (L : Submodule ℤ E) {v : E}
    (hv : v ∈ L) (hv0 : v ≠ 0)
    (hmin : ∀ w : E, w ∈ L → w ≠ 0 → ‖v‖ ≤ ‖w‖) : firstMinimum L = ‖v‖ := by
  unfold firstMinimum
  apply le_antisymm
  · apply csInf_le
    · exact ⟨0, by rintro _ ⟨w, _, _, rfl⟩; exact norm_nonneg w⟩
    · exact ⟨v, hv, hv0, rfl⟩
  · apply le_csInf
    · exact ⟨‖v‖, v, hv, hv0, rfl⟩
    · rintro _ ⟨w, hw, hw0, rfl⟩
      exact hmin w hw hw0

theorem firstMinimum_attained (L : Submodule ℤ E) [DiscreteTopology L] (hL : L ≠ ⊥) :
    ∃ v : E, v ∈ L ∧ v ≠ 0 ∧ ‖v‖ = firstMinimum L := by
  obtain ⟨v, hv, hv0, hmin⟩ := exists_shortest_lattice_vector L hL
  exact ⟨v, hv, hv0, (firstMinimum_eq_of_shortest L hv hv0 hmin).symm⟩

theorem firstMinimum_pos (L : Submodule ℤ E) [DiscreteTopology L] (hL : L ≠ ⊥) :
    0 < firstMinimum L := by
  obtain ⟨v, _, hv0, hv⟩ := firstMinimum_attained L hL
  rw [← hv]
  exact norm_pos_iff.mpr hv0

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem firstMinimum_le_norm (L : Submodule ℤ E) {v : E} (hv : v ∈ L) (hv0 : v ≠ 0) :
    firstMinimum L ≤ ‖v‖ := by
  apply csInf_le
  · exact ⟨0, by rintro _ ⟨w, _, _, rfl⟩; exact norm_nonneg w⟩
  · exact ⟨v, hv, hv0, rfl⟩

end GeometricGaussianLHL
end

end LatticeMinimum

section OrthogonalGram

/-!
## Orthogonal decomposition of a basis volume

The Gram determinant of kernel vectors followed by lifted quotient vectors
is the product of the kernel Gram determinant and the Gram determinant of
the orthogonal projections of the lifts. The lifts need not be orthogonal
to the kernel.
-/

noncomputable section

open Module
open scoped InnerProductSpace

namespace GeometricGaussianLHL

variable {E F ι κ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem det_gram_eq_sq_det_coordinates (o : OrthonormalBasis ι ℝ E) (u : ι → E) :
    (Matrix.gram ℝ u).det = (Matrix.det (fun i j => o.repr (u j) i)) ^ 2 := by
  rw [Matrix.gram_eq_conjTranspose_mul o, Matrix.det_mul, Matrix.det_conjTranspose]
  simp only [star_trivial, pow_two]
  rfl

theorem det_gram_triangular (o : OrthonormalBasis ι ℝ E) (p : OrthonormalBasis κ ℝ F)
    (u : ι → E) (v : κ → E) (w : κ → F) :
    (Matrix.gram ℝ (Sum.elim (fun i => WithLp.toLp 2 (u i, (0 : F)))
      (fun j => WithLp.toLp 2 (v j, w j)))).det =
      (Matrix.gram ℝ u).det * (Matrix.gram ℝ w).det := by
  let A : Matrix ι ι ℝ := fun i j => o.repr (u j) i
  let B : Matrix ι κ ℝ := fun i j => o.repr (v j) i
  let D : Matrix κ κ ℝ := fun i j => p.repr (w j) i
  have hc : (fun i j => (o.prod p).repr
      (Sum.elim (fun i => WithLp.toLp 2 (u i, (0 : F)))
        (fun j => WithLp.toLp 2 (v j, w j)) j) i) = Matrix.fromBlocks A B 0 D := by
    ext i j
    cases i <;> cases j <;>
      simp [OrthonormalBasis.repr_apply_apply, OrthonormalBasis.prod_apply,
        WithLp.prod_inner_apply, Matrix.fromBlocks, A, B, D]
  rw [det_gram_eq_sq_det_coordinates (o.prod p), hc, Matrix.det_fromBlocks_zero₂₁,
    det_gram_eq_sq_det_coordinates o, det_gram_eq_sq_det_coordinates p]
  change (A.det * D.det) ^ 2 = A.det ^ 2 * D.det ^ 2
  ring

omit [NormedAddCommGroup F] [InnerProductSpace ℝ F] in
theorem det_gram_orthogonal_projection [FiniteDimensional ℝ E]
    (W : Submodule ℝ E) (o : OrthonormalBasis ι ℝ W)
    (p : OrthonormalBasis κ ℝ Wᗮ) (u : ι → W) (v : κ → E) :
    (Matrix.gram ℝ (Sum.elim (fun i => (u i : E)) v)).det =
      (Matrix.gram ℝ u).det *
        (Matrix.gram ℝ (fun j => Wᗮ.orthogonalProjectionOnto (v j))).det := by
  have hu (i : ι) : W.orthogonalDecomposition (u i : E) =
      WithLp.toLp 2 (u i, (0 : Wᗮ)) := by
    rw [Submodule.orthogonalDecomposition_apply,
      Submodule.orthogonalProjectionOnto_mem_subspace_eq_self,
      Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal
        (W.le_orthogonal_orthogonal (u i).property)]
  have hg : Matrix.gram ℝ (Sum.elim (fun i => (u i : E)) v) =
      Matrix.gram ℝ (Sum.elim (fun i => WithLp.toLp 2 (u i, (0 : Wᗮ)))
        (fun j => WithLp.toLp 2 (W.orthogonalProjectionOnto (v j),
          Wᗮ.orthogonalProjectionOnto (v j)))) := by
    ext i j
    rw [Matrix.gram_apply, Matrix.gram_apply,
      ← W.orthogonalDecomposition.inner_map_map]
    cases i <;> cases j <;>
      simp only [Sum.elim_inl, Sum.elim_inr, hu, Submodule.orthogonalDecomposition_apply]
  rw [hg]
  exact det_gram_triangular o p u (fun j => W.orthogonalProjectionOnto (v j))
    (fun j => Wᗮ.orthogonalProjectionOnto (v j))

end GeometricGaussianLHL
end

end OrthogonalGram

section MinkowskiMinimum

/-!
## A quantitative Minkowski vector bound

The actual closed Euclidean ball has enough volume to contain a nonzero
lattice vector. The estimate is uniform over all dimensions at least two.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Module MeasureTheory

namespace GeometricGaussianLHL

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem exists_short_fullLattice_vector (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (hn : 2 ≤ finrank ℝ E) :
    ∃ v : E, v ∈ L ∧ v ≠ 0 ∧
      ‖v‖ ≤ (2 * Real.sqrt ((finrank ℝ E : ℝ) / 2) / Real.sqrt Real.pi) *
        ZLattice.covolume L ^ (1 / (finrank ℝ E : ℝ)) := by
  let : Nontrivial E := Module.nontrivial_of_finrank_pos (by omega : 0 < finrank ℝ E)
  let N := finrank ℝ E
  let c := ZLattice.covolume L
  let t := c ^ (1 / (N : ℝ))
  let s := Real.sqrt ((N : ℝ) / 2)
  let p := Real.sqrt Real.pi
  let R := (2 * s / p) * t
  have hc : 0 < c := ZLattice.covolume_pos L volume
  have ht : 0 < t := Real.rpow_pos_of_pos hc _
  have hN : 0 < N := by dsimp [N]; omega
  have hs : 0 < s := Real.sqrt_pos.mpr (by exact_mod_cast (show (0 : ℝ) < (N : ℝ) / 2 by positivity))
  have hp : 0 < p := Real.sqrt_pos.mpr Real.pi_pos
  have hR : 0 < R := mul_pos (div_pos (mul_pos (by norm_num) hs) hp) ht
  have htN : t ^ N = c := by
    simpa only [t, one_div] using Real.rpow_inv_natCast_pow hc.le hN.ne'
  have hRcancel : R * (p / s) = 2 * t := by
    dsimp [R]
    field_simp
  have hvol : ENNReal.ofReal c * 2 ^ N ≤ volume (Metric.closedBall (0 : E) R) := by
    have h := closedBall_volume_lower hn hR.le
    change ENNReal.ofReal ((R * (p / s)) ^ N) ≤ _ at h
    rw [hRcancel, mul_pow, htN, ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat] at h
    simpa only [mul_comm] using h
  let b := Module.Free.chooseBasis ℤ L
  let F := ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ L)
  let : Countable L.toAddSubgroup := Finsupp.Countable.of_moduleFinite (R := ℤ) (M := L)
  have hf : IsAddFundamentalDomain L.toAddSubgroup F volume := ZLattice.isAddFundamentalDomain b volume
  have hcF : ENNReal.ofReal c = volume F := by
    rw [show c = volume.real F from ZLattice.covolume_eq_measure_fundamentalDomain L volume hf]
    exact ENNReal.ofReal_toReal (ZSpan.fundamentalDomain_isBounded (b.ofZLatticeBasis ℝ L)).measure_lt_top.ne
  rw [hcF] at hvol
  obtain ⟨v, hv0, hv⟩ := exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure hf
    (fun x hx => by simpa only [Metric.mem_closedBall, dist_zero_right, norm_neg] using hx)
    (convex_closedBall (0 : E) R) (isCompact_closedBall (0 : E) R) hvol
  refine ⟨v, v.property, ?_, ?_⟩
  · exact fun h => hv0 (Subtype.ext h)
  · simpa only [Metric.mem_closedBall, dist_zero_right] using hv

end GeometricGaussianLHL
end

end MinkowskiMinimum

section KernelJacobian

/-!
## The Jacobian transverse to a kernel

A surjective map restricts to an isomorphism on its kernel's orthogonal
complement. Its volume factor is the norm determinant of the adjoint,
equivalently the square root of the determinant of `f ∘ f.adjoint`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Module
open scoped InnerProductSpace

namespace GeometricGaussianLHL

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ F] in
theorem det_gram_linearMap {ι : Type*} [Fintype ι] [DecidableEq ι]
    (o : OrthonormalBasis ι ℝ E) (f : E →ₗ[ℝ] F) (u : ι → E) :
    (Matrix.gram ℝ (fun i => f (u i))).det = f.normDet ^ 2 * (Matrix.gram ℝ u).det := by
  let g : E →ₗ[ℝ] E := o.toBasis.constr ℝ u
  have hg (i : ι) : g (o i) = u i := o.toBasis.constr_basis ℝ u i
  have h₁ := (f.comp g).normDet_sq_eq_det_gram o
  have h₂ := g.normDet_sq_eq_det_gram o
  change (f.comp g).normDet ^ 2 = (Matrix.gram ℝ (fun i => f (g (o i)))).det at h₁
  change g.normDet ^ 2 = (Matrix.gram ℝ (fun i => g (o i))).det at h₂
  simp only [hg] at h₁ h₂
  rw [← h₁, LinearMap.normDet_comp_of_finrank_eq _ _ rfl, mul_pow, h₂]

theorem normDet_adjoint_of_finrank_eq (f : E →ₗ[ℝ] F)
    (h : finrank ℝ E = finrank ℝ F) : f.adjoint.normDet = f.normDet := by
  classical
  let o := stdOrthonormalBasis ℝ E
  let p := (stdOrthonormalBasis ℝ F).reindex (finCongr h.symm)
  rw [LinearMap.normDet_eq_norm_det_toMatrix f.adjoint p o,
    LinearMap.normDet_eq_norm_det_toMatrix f o p, LinearMap.toMatrix_adjoint,
    Matrix.det_conjTranspose]
  simp

def kernelOrthogonalEquiv (f : E →ₗ[ℝ] F) (hf : Function.Surjective f) :
    f.kerᗮ ≃ₗ[ℝ] F :=
  f.ker.quotientEquivOrthogonal.symm.toLinearEquiv.trans (f.quotKerEquivOfSurjective hf)

omit [FiniteDimensional ℝ F] in
@[simp] theorem kernelOrthogonalEquiv_apply (f : E →ₗ[ℝ] F) (hf : Function.Surjective f)
    (x : f.kerᗮ) : kernelOrthogonalEquiv f hf x = f (x : E) := by
  rw [kernelOrthogonalEquiv, LinearEquiv.trans_apply]
  change f.quotKerEquivOfSurjective hf (f.ker.quotientEquivOrthogonal.symm x) = _
  rw [Submodule.quotientEquivOrthogonal_symm_eq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk]

omit [FiniteDimensional ℝ F] in
theorem map_orthogonalProjection_kernel (f : E →ₗ[ℝ] F) (x : E) :
    f (f.kerᗮ.orthogonalProjectionOnto x : E) = f x := by
  have h := f.ker.starProjection_add_starProjection_orthogonal x
  have hk : f (f.ker.orthogonalProjectionOnto x : E) = 0 :=
    (f.ker.orthogonalProjectionOnto x).property
  have hm := congrArg f h
  simpa only [map_add, Submodule.starProjection_apply, hk, zero_add] using hm

theorem kernelOrthogonalEquiv_normDet (f : E →ₗ[ℝ] F) (hf : Function.Surjective f) :
    (kernelOrthogonalEquiv f hf).toLinearMap.normDet = f.adjoint.normDet := by
  let g := (kernelOrthogonalEquiv f hf).toLinearMap
  have hr (x : F) : f.adjoint x ∈ f.kerᗮ := by
    rw [f.orthogonal_ker]
    exact ⟨x, rfl⟩
  have ha : f.adjoint.codRestrict f.kerᗮ hr = g.adjoint := by
    apply (LinearMap.eq_adjoint_iff _ _).mpr
    intro x y
    change inner ℝ (f.adjoint x) (y : E) = inner ℝ x (kernelOrthogonalEquiv f hf y)
    rw [kernelOrthogonalEquiv_apply, LinearMap.adjoint_inner_left]
  rw [← normDet_adjoint_of_finrank_eq g (kernelOrthogonalEquiv f hf).finrank_eq,
    ← ha, LinearMap.normDet_codRestrict]

theorem kernelJacobian_eq_sqrt_det (f : E →ₗ[ℝ] F) :
    f.adjoint.normDet = Real.sqrt (f.comp f.adjoint).det := by
  have h := f.adjoint.normDet_sq
  change f.adjoint.normDet ^ 2 = (f.adjoint.adjoint.comp f.adjoint).det at h
  rw [LinearMap.adjoint_adjoint] at h
  rw [← h, Real.sqrt_sq f.adjoint.normDet_nonneg]

theorem volume_kernel_lifts {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (f : E →ₗ[ℝ] F) (hf : Function.Surjective f)
    (o : OrthonormalBasis ι ℝ f.ker) (p : OrthonormalBasis κ ℝ f.kerᗮ)
    (u : ι → f.ker) (v : κ → E) :
    Real.sqrt (Matrix.gram ℝ (Sum.elim (fun i => (u i : E)) v)).det * f.adjoint.normDet =
      Real.sqrt (Matrix.gram ℝ u).det * Real.sqrt (Matrix.gram ℝ (fun j => f (v j))).det := by
  let w : κ → f.kerᗮ := fun j => f.kerᗮ.orthogonalProjectionOnto (v j)
  have hw (j : κ) : kernelOrthogonalEquiv f hf (w j) = f (v j) := by
    rw [kernelOrthogonalEquiv_apply]
    exact map_orthogonalProjection_kernel f (v j)
  have h := det_gram_linearMap p (kernelOrthogonalEquiv f hf).toLinearMap w
  change (Matrix.gram ℝ (fun j => kernelOrthogonalEquiv f hf (w j))).det = _ at h
  simp only [hw, kernelOrthogonalEquiv_normDet] at h
  rw [det_gram_orthogonal_projection f.ker o p, h,
    Real.sqrt_mul (Matrix.posSemidef_gram ℝ u).det_nonneg,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq f.adjoint.normDet_nonneg]
  ring

end GeometricGaussianLHL
end

end KernelJacobian

section LatticeKernelCovolume

/-!
## Covolume in a surjective sequence of lattices

For a map surjective on the integral lattices, an integral kernel basis
and integral lifts of a codomain basis form a domain basis. Orthogonal
projection of those lifts gives the exact intrinsic kernel covolume.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Module MeasureTheory

namespace GeometricGaussianLHL

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

def latticeKernel (L : Submodule ℤ E) (f : E →ₗ[ℝ] F) : Submodule ℤ E :=
  L ⊓ f.ker.restrictScalars ℤ

instance latticeKernel_discrete (L : Submodule ℤ E) [DiscreteTopology L]
    (f : E →ₗ[ℝ] F) : DiscreteTopology (latticeKernel L f) :=
  DiscreteTopology.of_subset (inferInstance : DiscreteTopology L)
    (show (latticeKernel L f : Set E) ⊆ L from inf_le_left)

def latticeRestriction (L : Submodule ℤ E) (M : Submodule ℤ F) (f : E →ₗ[ℝ] F)
    (hmap : ∀ x ∈ L, f x ∈ M) : L →ₗ[ℤ] M :=
  ((f.restrictScalars ℤ).comp L.subtype).codRestrict M (fun x => hmap x x.property)

def latticeRestrictionKernelEquiv (L : Submodule ℤ E) (M : Submodule ℤ F) (f : E →ₗ[ℝ] F)
    (hmap : ∀ x ∈ L, f x ∈ M) :
    (latticeRestriction L M f hmap).ker ≃ₗ[ℤ] latticeKernel L f where
  toFun x := ⟨(x : L), (x : L).property, congrArg Subtype.val x.property⟩
  invFun x := ⟨⟨x, x.property.1⟩, Subtype.ext x.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem covolume_kernel_of_lift_basis {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (M : Submodule ℤ F) [DiscreteTopology M] [IsZLattice ℝ M]
    (f : E →ₗ[ℝ] F) (hf : Function.Surjective f)
    (hspan : Submodule.span ℝ (latticeKernel L f : Set E) = f.ker)
    (b : Basis ι ℤ (latticeKernel L f)) (c : Basis κ ℤ M) (a : Basis (ι ⊕ κ) ℤ L)
    (ha : ∀ i, (a (Sum.inl i) : E) = b i)
    (hc : ∀ j, f (a (Sum.inr j) : E) = c j) :
    ZLattice.covolume L * f.adjoint.normDet = intrinsicCovolume (latticeKernel L f) * ZLattice.covolume M := by
  let u : ι → f.ker := fun i => ⟨b i, (b i).property.2⟩
  let v : κ → E := fun j => a (Sum.inr j)
  let eo : Fin (finrank ℝ f.ker) ≃ ι := Fintype.equivOfCardEq (by
    rw [Fintype.card_fin, ← hspan, ← intrinsicLattice_rank, finrank_eq_card_basis b])
  let ep : Fin (finrank ℝ f.kerᗮ) ≃ κ := Fintype.equivOfCardEq (by
    rw [Fintype.card_fin, (kernelOrthogonalEquiv f hf).finrank_eq,
      ← ZLattice.rank ℝ M, finrank_eq_card_basis c])
  let o := (stdOrthonormalBasis ℝ f.ker).reindex eo
  let p := (stdOrthonormalBasis ℝ f.kerᗮ).reindex ep
  have hb : (fun i => (a i : E)) = Sum.elim (fun i => (u i : E)) v := by
    funext i
    cases i with
    | inl i => exact ha i
    | inr j => rfl
  have hv : (fun j => f (v j)) = fun j => (c j : F) := funext hc
  rw [covolume_eq_sqrt_gram L a, intrinsicCovolume_eq_sqrt_gram _ b,
    covolume_eq_sqrt_gram M c, hb, ← hv]
  exact volume_kernel_lifts f hf o p u v

theorem latticeKernel_covolume (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (M : Submodule ℤ F) [DiscreteTopology M] [IsZLattice ℝ M]
    (f : E →ₗ[ℝ] F) (hf : Function.Surjective f)
    (hmap : ∀ x ∈ L, f x ∈ M)
    (hsurj : Function.Surjective (latticeRestriction L M f hmap))
    (hspan : Submodule.span ℝ (latticeKernel L f : Set E) = f.ker) :
    intrinsicCovolume (latticeKernel L f) =
      ZLattice.covolume L / ZLattice.covolume M * f.adjoint.normDet := by
  classical
  let q := latticeRestriction L M f hmap
  let e := latticeRestrictionKernelEquiv L M f hmap
  let b := Module.Free.chooseBasis ℤ q.ker
  let c := Module.Free.chooseBasis ℤ M
  obtain ⟨g, hg⟩ := q.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hsurj)
  have h := covolume_kernel_of_lift_basis L M f hf hspan (b.map e) c
    (kernelLiftBasis q g hg b c)
    (fun i => by rw [kernelLiftBasis_inl]; rfl)
    (fun j => by
      rw [kernelLiftBasis_inr]
      exact congrArg Subtype.val (LinearMap.congr_fun hg (c j)))
  have hM := ZLattice.covolume_pos M volume
  rw [div_mul_eq_mul_div]
  exact (eq_div_iff hM.ne').mpr h.symm

end GeometricGaussianLHL
end

end LatticeKernelCovolume

section CovolumeTransport

/-!
## Covolume under a linear change of coordinates

An integral basis identifies its lattice covolume with the norm determinant
of the coefficient map. This gives the exact Jacobian factor for a linear
isomorphism between Euclidean spaces.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Module MeasureTheory

namespace GeometricGaussianLHL

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

def basisEuclideanEquiv {ι : Type*} [Fintype ι] (b : Basis ι ℝ E) :
    EuclideanSpace ℝ ι ≃ₗ[ℝ] E := (WithLp.linearEquiv 2 ℝ (ι → ℝ)).trans b.equivFun.symm

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem basisEuclideanEquiv_basis {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℝ E) (i : ι) :
    basisEuclideanEquiv b (EuclideanSpace.basisFun ι ℝ i) = b i := by
  simp only [basisEuclideanEquiv, LinearEquiv.trans_apply, EuclideanSpace.basisFun_apply]
  change b.equivFun.symm (Pi.single i 1) = b i
  rw [Basis.equivFun_symm_apply]
  simp

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] in
theorem basisEuclideanEquiv_map {ι : Type*} [Fintype ι]
    (b : Basis ι ℝ E) (e : E ≃ₗ[ℝ] F) :
    (basisEuclideanEquiv (b.map e)).toLinearMap =
      e.toLinearMap.comp (basisEuclideanEquiv b).toLinearMap := by
  ext x
  simp only [basisEuclideanEquiv, LinearEquiv.coe_toLinearMap, LinearEquiv.trans_apply,
    LinearMap.comp_apply, Basis.equivFun_symm_apply, Basis.map_apply, map_sum, map_smul]

theorem covolume_eq_basis_normDet {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] (b : Basis ι ℤ L) :
    ZLattice.covolume L = (basisEuclideanEquiv (b.ofZLatticeBasis ℝ L)).toLinearMap.normDet := by
  let f := basisEuclideanEquiv (b.ofZLatticeBasis ℝ L)
  have hs := f.toLinearMap.normDet_sq_eq_det_gram (EuclideanSpace.basisFun ι ℝ)
  change f.toLinearMap.normDet ^ 2 = (Matrix.gram ℝ (fun i => f (EuclideanSpace.basisFun ι ℝ i))).det at hs
  have he : (fun i => f (EuclideanSpace.basisFun ι ℝ i)) = fun i => (b i : E) := by
    funext i
    rw [basisEuclideanEquiv_basis, Basis.ofZLatticeBasis_apply]
  rw [he] at hs
  rw [covolume_eq_sqrt_gram L b, ← hs, Real.sqrt_sq f.toLinearMap.normDet_nonneg]

theorem covolume_comap_equiv (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (e : F ≃L[ℝ] E) :
    ZLattice.covolume (ZLattice.comap ℝ L e.toLinearMap) =
      e.symm.toLinearMap.normDet * ZLattice.covolume L := by
  classical
  let b := Module.Free.chooseBasis ℤ L
  let b' := b.ofZLatticeComap ℝ L e.toLinearEquiv
  rw [covolume_eq_basis_normDet _ b', covolume_eq_basis_normDet _ b]
  rw [Basis.ofZLatticeBasis_comap, basisEuclideanEquiv_map,
    LinearMap.normDet_comp_of_finrank_eq _ _ (basisEuclideanEquiv (b.ofZLatticeBasis ℝ L)).finrank_eq]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] in
theorem latticeImage_equiv_eq_comap (L : Submodule ℤ E) (e : E ≃L[ℝ] F) :
    latticeImage e.toContinuousLinearMap L = ZLattice.comap ℝ L e.symm.toLinearMap := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change e.symm (e x) ∈ L
    simpa using hx
  · intro hy
    exact ⟨e.symm y, hy, e.apply_symm_apply y⟩

theorem covolume_latticeImage_equiv (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (e : E ≃L[ℝ] F) :
    ZLattice.covolume (latticeImage e.toContinuousLinearMap L) =
      e.toLinearMap.normDet * ZLattice.covolume L := by
  rw [latticeImage_equiv_eq_comap, covolume_comap_equiv]
  rfl

end GeometricGaussianLHL
end

end CovolumeTransport

section ImageDual

/-!
## Short dual vectors in linear images of the integer lattice

The inverse adjoint maps the standard basis to an ambient dual basis.
Projecting one of those vectors gives the bound for every nonzero subgroup
of the image lattice. Primitivity is not needed for this inclusion argument.
-/

noncomputable section

namespace GeometricGaussianLHL

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

def inverseAdjointEquiv (T : E ≃L[ℝ] F) : E ≃L[ℝ] F :=
  ContinuousLinearEquiv.equivOfInverse T.symm.toContinuousLinearMap.adjoint
    T.toContinuousLinearMap.adjoint
    (by
      intro x
      apply ext_inner_right ℝ
      intro y
      rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left]
      simp only [ContinuousLinearEquiv.coe_coe, T.symm_apply_apply])
    (by
      intro x
      apply ext_inner_right ℝ
      intro y
      rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left]
      simp only [ContinuousLinearEquiv.coe_coe, T.apply_symm_apply])

@[simp] theorem inverseAdjointEquiv_apply (T : E ≃L[ℝ] F) (x : E) :
    inverseAdjointEquiv T x = T.symm.toContinuousLinearMap.adjoint x := rfl

omit [FiniteDimensional ℝ E] in
theorem lattice_span_ne_bot {L : Submodule ℤ E} (hL : L ≠ ⊥) :
    Submodule.span ℝ (L : Set E) ≠ ⊥ := by
  intro h
  apply hL
  apply eq_bot_iff.mpr
  intro x hx
  have hx' := Submodule.subset_span (R := ℝ) hx
  rw [h] at hx'
  exact hx'

/-- The full short-vector statement in arbitrary image coordinates. -/
theorem exists_short_image_integer_dual {n : ℕ} (T : Euclidean n ≃L[ℝ] F)
    (L : Submodule ℤ F) (hL : L ≠ ⊥)
    (hsub : L ≤ latticeImage T.toContinuousLinearMap (integerLattice n)) :
    ∃ v : F, v ∈ latticeDual L ∧ v ≠ 0 ∧ ‖v‖ ≤ ‖T.symm.toContinuousLinearMap‖ := by
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.map (inverseAdjointEquiv T).toLinearEquiv
  apply exists_short_dual_vector L b (lattice_span_ne_bot hL)
  · intro i
    change ‖T.symm.toContinuousLinearMap.adjoint (EuclideanSpace.basisFun (Fin n) ℝ i)‖ ≤ _
    calc
      _ ≤ ‖T.symm.toContinuousLinearMap.adjoint‖ * ‖EuclideanSpace.basisFun (Fin n) ℝ i‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ = _ := by rw [LinearIsometryEquiv.norm_map, (EuclideanSpace.basisFun (Fin n) ℝ).norm_eq_one, mul_one]
  · intro i z hz
    obtain ⟨x, ⟨w, rfl⟩, rfl⟩ := hsub hz
    refine ⟨w i, ?_⟩
    change (w i : ℝ) = inner ℝ
      (T.symm.toContinuousLinearMap.adjoint (EuclideanSpace.basisFun (Fin n) ℝ i))
      (T (integerEmbedding n w))
    rw [ContinuousLinearMap.adjoint_inner_left]
    simp only [ContinuousLinearEquiv.coe_coe, T.symm_apply_apply,
      EuclideanSpace.basisFun_inner, integerEmbedding_apply]

omit [FiniteDimensional ℝ F] in
theorem image_integer_sublattice_fg {n : ℕ} (T : Euclidean n →L[ℝ] F)
    (L : Submodule ℤ F) (hsub : L ≤ latticeImage T (integerLattice n)) : L.FG := by
  apply Submodule.FG.of_le _ hsub
  exact (Submodule.FG.of_finite (N := integerLattice n)).map _

/-- The coefficient-coordinate part of Proposition 4.14 for arbitrary
nonzero sublattices, with a simultaneous statement for all positive errors. -/
theorem integer_sublattice_projected_dual {n : ℕ} (L : Submodule ℤ (Euclidean n))
    (hL : L ≠ ⊥) (hsub : L ≤ integerLattice n) :
    (∃ v : Euclidean n, v ∈ latticeDual L ∧ v ≠ 0 ∧ ‖v‖ ≤ 1) ∧
    ∀ ε : ℝ, 0 < ε → Real.sqrt (Real.log (2 / ε) / Real.pi) ≤ smoothingParameter L ε := by
  have hex : ∃ v : Euclidean n, v ∈ latticeDual L ∧ v ≠ 0 ∧ ‖v‖ ≤ 1 := by
    apply exists_short_dual_vector L (EuclideanSpace.basisFun (Fin n) ℝ).toBasis (lattice_span_ne_bot hL)
    · intro i
      exact ((EuclideanSpace.basisFun (Fin n) ℝ).norm_eq_one i).le
    · intro i z hz
      obtain ⟨w, rfl⟩ := hsub hz
      refine ⟨w i, ?_⟩
      change (w i : ℝ) = inner ℝ (EuclideanSpace.basisFun (Fin n) ℝ i) (integerEmbedding n w)
      rw [EuclideanSpace.basisFun_inner, integerEmbedding_apply]
  refine ⟨hex, ?_⟩
  intro ε hε
  obtain ⟨v, hv, hv0, hvnorm⟩ := hex
  have hfg : L.FG := Submodule.FG.of_le Submodule.FG.of_finite hsub
  have hv0' : (⟨v, hv⟩ : latticeDual L) ≠ 0 := fun h => hv0 (congrArg Subtype.val h)
  simpa only [div_one] using smoothingParameter_lower_of_dual_vector
    (exists_smoothAt_of_fg L hfg hε) hε (by norm_num : (0 : ℝ) < 1) ⟨v, hv⟩ hv0' hvnorm

end GeometricGaussianLHL
end

end ImageDual

section CanonicalLower

/-!
## The canonical projected-dual lower bound

Proposition 4.14 for actual number-field lattices, including every kernel
with more ring columns than rows. The proof also applies to nonprimitive
nonzero subgroups of the canonical ambient lattice.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Module NumberField

namespace GeometricGaussianLHL

variable (K : Type*) [Field K] [NumberField K] {d r m : ℕ}

local instance lowerEmbeddingsFintype : Fintype (K →+* ℂ) := inferInstance
local instance lowerAmbientInner : InnerProductSpace ℝ (CanonicalAmbient K) := inferInstance
local instance lowerSpaceInner : InnerProductSpace ℝ (canonicalSpace K) := inferInstance
local instance lowerPowerInner (n : ℕ) : InnerProductSpace ℝ (CanonicalPower K n) := inferInstance

def canonicalLattice (m : ℕ) : Submodule ℤ (CanonicalPower K m) :=
  LinearMap.range (canonicalPowerEmbedding K m)

theorem canonicalLattice_eq_image (b : Basis (Fin d) ℤ (𝓞 K)) (m : ℕ) :
    canonicalLattice K m = latticeImage (powerCanonicalEquiv K b m).toContinuousLinearMap
      (integerLattice (m * d)) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨integerEmbedding (m * d) (ringPowerCoordinates b m x),
      ⟨ringPowerCoordinates b m x, rfl⟩, powerCanonicalEquiv_integer K b m x⟩
  · rintro ⟨z, ⟨x, rfl⟩, rfl⟩
    refine ⟨(ringPowerCoordinates b m).symm x, ?_⟩
    change canonicalPowerEmbedding K m ((ringPowerCoordinates b m).symm x) =
      powerCanonicalEquiv K b m (integerEmbedding (m * d) x)
    simpa only [LinearEquiv.apply_symm_apply] using
      (powerCanonicalEquiv_integer K b m ((ringPowerCoordinates b m).symm x)).symm

theorem canonicalLattice_subgroup_fg (b : Basis (Fin d) ℤ (𝓞 K))
    (L : Submodule ℤ (CanonicalPower K m)) (hsub : L ≤ canonicalLattice K m) : L.FG := by
  rw [canonicalLattice_eq_image K b m] at hsub
  exact image_integer_sublattice_fg _ L hsub

omit [NumberField K] in
theorem canonicalKernel_le_lattice (X : Matrix (Fin r) (Fin m) (𝓞 K)) :
    canonicalKernel K X ≤ canonicalLattice K m := by
  rintro y ⟨x, _, rfl⟩
  exact ⟨x, rfl⟩

theorem canonicalPowerEmbedding_injective (m : ℕ) :
    Function.Injective (canonicalPowerEmbedding K m) := by
  intro x y h
  funext j
  exact canonicalIntegerEmbedding_injective K (congrArg (fun z : CanonicalPower K m => z j) h)

theorem canonicalKernel_ne_bot (b : Basis (Fin d) ℤ (𝓞 K))
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) (hmr : r < m) : canonicalKernel K X ≠ ⊥ := by
  intro h
  have hker : (ringMatrixMap X).ker = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    have he : canonicalPowerEmbedding K m x ∈ canonicalKernel K X := ⟨x, hx, rfl⟩
    rw [h] at he
    exact canonicalPowerEmbedding_injective K m (by simpa using he)
  apply coefficientKernel_ne_bot (ringCoefficientMatrix b X)
    (Nat.mul_lt_mul_of_pos_right hmr (integralBasis_dimension_pos K b))
  rw [ringCoefficientMatrix_kernel, hker, Submodule.map_bot]

/-- The canonical short-vector statement, without an unnecessary primitivity
assumption. -/
theorem exists_short_canonical_dual (b : Basis (Fin d) ℤ (𝓞 K))
    (L : Submodule ℤ (CanonicalPower K m)) (hL : L ≠ ⊥)
    (hsub : L ≤ canonicalLattice K m) :
    ∃ v : CanonicalPower K m, v ∈ latticeDual L ∧ v ≠ 0 ∧ ‖v‖ ≤ basisBeta K b := by
  rw [canonicalLattice_eq_image K b m] at hsub
  obtain ⟨v, hv, hv0, hvnorm⟩ := exists_short_image_integer_dual (powerCanonicalEquiv K b m) L hL hsub
  exact ⟨v, hv, hv0, hvnorm.trans (powerCanonicalEquiv_symm_norm_le K b m)⟩

theorem canonical_smoothing_lower (b : Basis (Fin d) ℤ (𝓞 K))
    (L : Submodule ℤ (CanonicalPower K m)) (hL : L ≠ ⊥)
    (hsub : L ≤ canonicalLattice K m) {ε : ℝ} (hε : 0 < ε) :
    Real.sqrt (Real.log (2 / ε) / Real.pi) / basisBeta K b ≤ smoothingParameter L ε := by
  obtain ⟨v, hv, hv0, hvnorm⟩ := exists_short_canonical_dual K b L hL hsub
  have hv0' : (⟨v, hv⟩ : latticeDual L) ≠ 0 := fun h => hv0 (congrArg Subtype.val h)
  exact smoothingParameter_lower_of_dual_vector
    (exists_smoothAt_of_fg L (canonicalLattice_subgroup_fg K b L hsub) hε)
    hε (basisBeta_pos K b) ⟨v, hv⟩ hv0' hvnorm

theorem canonicalKernel_projected_dual (b : Basis (Fin d) ℤ (𝓞 K))
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) (hmr : r < m) :
    (∃ v : CanonicalPower K m, v ∈ latticeDual (canonicalKernel K X) ∧ v ≠ 0 ∧ ‖v‖ ≤ basisBeta K b) ∧
    ∀ ε : ℝ, 0 < ε → Real.sqrt (Real.log (2 / ε) / Real.pi) / basisBeta K b ≤
      smoothingParameter (canonicalKernel K X) ε :=
  ⟨exists_short_canonical_dual K b _ (canonicalKernel_ne_bot K b X hmr) (canonicalKernel_le_lattice K X),
    fun _ hε => canonical_smoothing_lower K b _ (canonicalKernel_ne_bot K b X hmr)
      (canonicalKernel_le_lattice K X) hε⟩

/-- The corrected formula following Lemma 3.2, for the actual canonical
number-field kernel. -/
theorem canonicalKernel_dual_formula (b : Basis (Fin d) ℤ (𝓞 K))
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) (y : CanonicalPower K m) :
    y ∈ latticeDual (canonicalKernel K X) ↔
      ∃ v ∈ latticeDual (euclideanKernel (ringCoefficientMatrix b X)),
        (Submodule.span ℝ (canonicalKernel K X : Set (CanonicalPower K m))).starProjection
          ((powerCanonicalEquiv K b m).symm.toContinuousLinearMap.adjoint v) = y := by
  rw [canonicalKernel_eq_image K b X]
  exact mem_dual_image_iff_projected_inverse_adjoint (powerCanonicalEquiv K b m)
    (euclideanKernel (ringCoefficientMatrix b X)) y

end GeometricGaussianLHL
end

end CanonicalLower

section KernelJacobianBound

/-!
## The operator-norm bound for a kernel Jacobian

AM–GM on the Gram eigenvalues bounds the volume factor by the appropriate
power of the operator norm. The zero-dimensional case is included.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Module

namespace GeometricGaussianLHL

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ F] in
theorem normDet_le_opNorm_pow (f : E →ₗ[ℝ] F) :
    f.normDet ≤ ‖f.toContinuousLinearMap‖ ^ finrank ℝ E := by
  by_cases h0 : finrank ℝ E = 0
  · let : Subsingleton E := finrank_zero_iff.mp h0
    simp only [LinearMap.normDet_of_subsingleton, h0, pow_zero, le_refl]
  have hn : 0 < finrank ℝ E := Nat.pos_of_ne_zero h0
  have hn' : (0 : ℝ) < finrank ℝ E := by exact_mod_cast hn
  let o := stdOrthonormalBasis ℝ E
  let G := Matrix.gram ℝ (fun i => f (o i))
  have hcol (i : Fin (finrank ℝ E)) : ‖f (o i)‖ ≤ ‖f.toContinuousLinearMap‖ := by
    simpa only [LinearMap.coe_toContinuousLinearMap', o.norm_eq_one, mul_one]
      using f.toContinuousLinearMap.le_opNorm (o i)
  have ht : G.trace ≤ (finrank ℝ E : ℝ) * ‖f.toContinuousLinearMap‖ ^ 2 := by
    calc
      G.trace = ∑ i, ‖f (o i)‖ ^ 2 := by
        simp only [G, Matrix.trace, Matrix.diag, Matrix.gram_apply, real_inner_self_eq_norm_sq]
      _ ≤ ∑ _i : Fin (finrank ℝ E), ‖f.toContinuousLinearMap‖ ^ 2 :=
        Finset.sum_le_sum (fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hcol i) _)
      _ = _ := by simp
  have hd := positiveSemidefinite_det_le_mean_trace_pow hn G (Matrix.posSemidef_gram ℝ _)
  have ht' : G.trace / (finrank ℝ E : ℝ) ≤ ‖f.toContinuousLinearMap‖ ^ 2 :=
    (div_le_iff₀ hn').mpr (by simpa only [mul_comm] using ht)
  have hpow := pow_le_pow_left₀
    (div_nonneg (Matrix.posSemidef_gram ℝ (fun i => f (o i))).trace_nonneg hn'.le)
    ht' (finrank ℝ E)
  have hs := f.normDet_sq_eq_det_gram o
  change f.normDet ^ 2 = G.det at hs
  have he : (‖f.toContinuousLinearMap‖ ^ 2) ^ finrank ℝ E =
      (‖f.toContinuousLinearMap‖ ^ finrank ℝ E) ^ 2 := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  rw [he] at hpow
  nlinarith [f.normDet_nonneg, pow_nonneg (norm_nonneg f.toContinuousLinearMap) (finrank ℝ E)]

theorem kernelJacobian_le_opNorm_pow (f : E →ₗ[ℝ] F) :
    f.adjoint.normDet ≤ ‖f.toContinuousLinearMap‖ ^ finrank ℝ F := by
  have h := normDet_le_opNorm_pow f.adjoint
  simpa only [LinearMap.adjoint_toContinuousLinearMap, LinearIsometryEquiv.norm_map] using h

end GeometricGaussianLHL
end

end KernelJacobianBound

section CanonicalCovolume

/-!
## Covolume of the canonical ring lattice

The coefficient basis map has Jacobian √|disc K|, and its direct sum has
the corresponding power. Thus the actual canonical lattice on m ring
coordinates has covolume |disc K|^(m/2), in the paper's t₂ metric.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Module NumberField MeasureTheory
open scoped Kronecker

namespace GeometricGaussianLHL

instance integerLattice_isZLattice (n : ℕ) : IsZLattice ℝ (integerLattice n) :=
  ⟨integerLattice_span n⟩

theorem integerLattice_covolume (n : ℕ) : ZLattice.covolume (integerLattice n) = 1 := by
  classical
  rw [integerLattice_eq_basis_span]
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  change ZLattice.covolume (Submodule.span ℤ (Set.range b.toBasis)) = 1
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ volume (ZSpan.isAddFundamentalDomain b.toBasis volume)]
  rw [measureReal_congr (ZSpan.fundamentalDomain_ae_parallelepiped b.toBasis volume)]
  simp only [measureReal_def, OrthonormalBasis.coe_toBasis, b.volume_parallelepiped, ENNReal.toReal_one]

variable (K : Type*) [Field K] [NumberField K] {d : ℕ}

local instance covolumeEmbeddingsFintype : Fintype (K →+* ℂ) := inferInstance
local instance covolumeAmbientInner : InnerProductSpace ℝ (CanonicalAmbient K) := inferInstance
local instance covolumeSpaceInner : InnerProductSpace ℝ (canonicalSpace K) := inferInstance
local instance covolumePowerInner (n : ℕ) : InnerProductSpace ℝ (CanonicalPower K n) := inferInstance
local instance covolumePowerMeasureSpace (n : ℕ) : MeasureSpace (CanonicalPower K n) :=
  measureSpaceOfInnerProductSpace

theorem coefficientCanonicalEquiv_basis (b : Basis (Fin d) ℤ (𝓞 K)) (i : Fin d) :
    coefficientCanonicalEquiv K b (EuclideanSpace.basisFun (Fin d) ℝ i) = canonicalBasis K b i :=
  basisEuclideanEquiv_basis (canonicalBasis K b) i

theorem coefficientCanonicalEquiv_normDet (b : Basis (Fin d) ℤ (𝓞 K)) :
    (coefficientCanonicalEquiv K b).toLinearMap.normDet = Real.sqrt |(NumberField.discr K : ℝ)| := by
  have h := (coefficientCanonicalEquiv K b).toLinearMap.normDet_sq_eq_det_gram
    (EuclideanSpace.basisFun (Fin d) ℝ)
  change (coefficientCanonicalEquiv K b).toLinearMap.normDet ^ 2 =
    (Matrix.gram ℝ (fun i => coefficientCanonicalEquiv K b (EuclideanSpace.basisFun (Fin d) ℝ i))).det at h
  have hG : Matrix.gram ℝ (fun i => coefficientCanonicalEquiv K b (EuclideanSpace.basisFun (Fin d) ℝ i)) =
      canonicalGram K b := by
    ext i j
    simp only [Matrix.gram_apply, coefficientCanonicalEquiv_basis, canonicalBasis_inner]
  rw [hG, canonicalGram_det] at h
  rw [← h, Real.sqrt_sq (coefficientCanonicalEquiv K b).toLinearMap.normDet_nonneg]

theorem euclideanBlocks_basis (n d : ℕ) (i : Fin n × Fin d) (j : Fin n) :
    euclideanBlocks n d (EuclideanSpace.basisFun (Fin (n * d)) ℝ (finProdFinEquiv i)) j =
      if j = i.1 then EuclideanSpace.basisFun (Fin d) ℝ i.2 else 0 := by
  classical
  ext l
  simp only [euclideanBlocks_apply, EuclideanSpace.basisFun_apply, PiLp.single_apply,
    finProdFinEquiv.injective.eq_iff, Prod.ext_iff]
  by_cases hj : j = i.1 <;> by_cases hl : l = i.2 <;> simp [hj, hl]

theorem powerCanonicalEquiv_basis (b : Basis (Fin d) ℤ (𝓞 K)) (n : ℕ)
    (i : Fin n × Fin d) (j : Fin n) :
    powerCanonicalEquiv K b n (EuclideanSpace.basisFun (Fin (n * d)) ℝ (finProdFinEquiv i)) j =
      if j = i.1 then canonicalBasis K b i.2 else 0 := by
  rw [powerCanonicalEquiv_apply, euclideanBlocks_basis]
  split_ifs <;> simp only [coefficientCanonicalEquiv_basis, map_zero]

theorem powerCanonicalEquiv_gram (b : Basis (Fin d) ℤ (𝓞 K)) (n : ℕ) :
    Matrix.gram ℝ (fun i : Fin n × Fin d =>
      powerCanonicalEquiv K b n (EuclideanSpace.basisFun (Fin (n * d)) ℝ (finProdFinEquiv i))) =
      (1 : Matrix (Fin n) (Fin n) ℝ) ⊗ₖ canonicalGram K b := by
  ext i j
  rw [Matrix.gram_apply, PiLp.inner_apply]
  change (∑ l : Fin n, inner ℝ
    (powerCanonicalEquiv K b n (EuclideanSpace.basisFun (Fin (n * d)) ℝ (finProdFinEquiv i)) l)
    (powerCanonicalEquiv K b n (EuclideanSpace.basisFun (Fin (n * d)) ℝ (finProdFinEquiv j)) l)) = _
  simp only [powerCanonicalEquiv_basis, Matrix.kroneckerMap_apply, Matrix.one_apply]
  by_cases hij : i.1 = j.1
  · simp [hij, apply_ite, canonicalGram]
  · simp [hij, Ne.symm hij, apply_ite]

theorem powerCanonicalEquiv_normDet (b : Basis (Fin d) ℤ (𝓞 K)) (n : ℕ) :
    (powerCanonicalEquiv K b n).toLinearMap.normDet = Real.sqrt |(NumberField.discr K : ℝ)| ^ n := by
  let o := (EuclideanSpace.basisFun (Fin (n * d)) ℝ).reindex finProdFinEquiv.symm
  have hs := (powerCanonicalEquiv K b n).toLinearMap.normDet_sq_eq_det_gram o
  change (powerCanonicalEquiv K b n).toLinearMap.normDet ^ 2 = _ at hs
  simp only [o, OrthonormalBasis.reindex_apply, Equiv.symm_symm] at hs
  change (powerCanonicalEquiv K b n).toLinearMap.normDet ^ 2 =
    (Matrix.gram ℝ (fun i : Fin n × Fin d => powerCanonicalEquiv K b n
      (EuclideanSpace.basisFun (Fin (n * d)) ℝ (finProdFinEquiv i)))).det at hs
  rw [powerCanonicalEquiv_gram, Matrix.det_kronecker, Matrix.det_one, one_pow, one_mul,
    Fintype.card_fin, canonicalGram_det] at hs
  apply (sq_eq_sq₀ (powerCanonicalEquiv K b n).toLinearMap.normDet_nonneg (by positivity)).mp
  rw [hs, ← pow_mul, Nat.mul_comm n 2, pow_mul, Real.sq_sqrt (abs_nonneg _)]

theorem canonicalLattice_covolume (b : Basis (Fin d) ℤ (𝓞 K)) (n : ℕ) :
    ZLattice.covolume (canonicalLattice K n) (volume : Measure (CanonicalPower K n)) =
      Real.sqrt |(NumberField.discr K : ℝ)| ^ n := by
  rw [canonicalLattice_eq_image K b n, covolume_latticeImage_equiv,
    powerCanonicalEquiv_normDet, integerLattice_covolume, mul_one]

end GeometricGaussianLHL
end

end CanonicalCovolume

section CanonicalOperator

/-!
## The actual canonical matrix operator and kernel rank

The real operator agrees with ring-matrix multiplication on every embedded
integer vector. This characterizes it independently of the integral basis.
Its real kernel is the span of the actual canonical integer kernel.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Module NumberField

namespace GeometricGaussianLHL

variable (K : Type*) [Field K] [NumberField K] {d r m : ℕ}

local instance operatorEmbeddingsFintype : Fintype (K →+* ℂ) := inferInstance
local instance operatorAmbientInner : InnerProductSpace ℝ (CanonicalAmbient K) := inferInstance
local instance operatorSpaceInner : InnerProductSpace ℝ (canonicalSpace K) := inferInstance
local instance operatorPowerInner (n : ℕ) : InnerProductSpace ℝ (CanonicalPower K n) := inferInstance

def canonicalMatrixMap (b : Basis (Fin d) ℤ (𝓞 K)) (X : Matrix (Fin r) (Fin m) (𝓞 K)) :
    CanonicalPower K m →ₗ[ℝ] CanonicalPower K r :=
  (powerCanonicalEquiv K b r).toLinearMap.comp ((realCoefficientMap (ringCoefficientMatrix b X)).comp
    (powerCanonicalEquiv K b m).symm.toLinearMap)

theorem canonicalMatrixMap_integer (b : Basis (Fin d) ℤ (𝓞 K))
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) (x : Fin m → 𝓞 K) :
    canonicalMatrixMap K b X (canonicalPowerEmbedding K m x) = canonicalPowerEmbedding K r (X.mulVec x) := by
  have hpre : (powerCanonicalEquiv K b m).symm (canonicalPowerEmbedding K m x) =
      integerEmbedding (m * d) (ringPowerCoordinates b m x) := by
    rw [← powerCanonicalEquiv_integer K b m x, ContinuousLinearEquiv.symm_apply_apply]
  change powerCanonicalEquiv K b r
    (realCoefficientMap (ringCoefficientMatrix b X) ((powerCanonicalEquiv K b m).symm
      (canonicalPowerEmbedding K m x))) = _
  rw [hpre, realCoefficientMap_integerEmbedding, ringCoefficientMatrix_map, powerCanonicalEquiv_integer]

theorem canonicalLattice_span (b : Basis (Fin d) ℤ (𝓞 K)) (n : ℕ) :
    Submodule.span ℝ (canonicalLattice K n : Set (CanonicalPower K n)) = ⊤ := by
  rw [canonicalLattice_eq_image K b n]
  change Submodule.span ℝ ((powerCanonicalEquiv K b n).toLinearMap '' (integerLattice (n * d) : Set _)) = ⊤
  rw [Submodule.span_image, integerLattice_span, Submodule.map_top]
  exact LinearMap.range_eq_top.mpr (powerCanonicalEquiv K b n).surjective

theorem canonicalMatrixMap_basis_independent {d' : ℕ}
    (b : Basis (Fin d) ℤ (𝓞 K)) (b' : Basis (Fin d') ℤ (𝓞 K))
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) : canonicalMatrixMap K b X = canonicalMatrixMap K b' X := by
  apply LinearMap.ext_on (canonicalLattice_span K b m)
  rintro _ ⟨x, rfl⟩
  rw [canonicalMatrixMap_integer, canonicalMatrixMap_integer]

theorem canonicalMatrixMap_surjective (b : Basis (Fin d) ℤ (𝓞 K))
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) (hX : Function.Surjective X.mulVec) :
    Function.Surjective (canonicalMatrixMap K b X) :=
  (powerCanonicalEquiv K b r).surjective.comp
    ((realCoefficientMap_surjective_of_integer_surjective _
      ((ringCoefficientMatrix_surjective_iff b X).mpr hX)).comp
      (powerCanonicalEquiv K b m).symm.surjective)

theorem canonicalKernel_span_eq_ker (b : Basis (Fin d) ℤ (𝓞 K))
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) :
    Submodule.span ℝ (canonicalKernel K X : Set (CanonicalPower K m)) = (canonicalMatrixMap K b X).ker := by
  rw [canonicalKernel_eq_image K b X]
  change Submodule.span ℝ ((powerCanonicalEquiv K b m).toLinearMap ''
    (euclideanKernel (ringCoefficientMatrix b X) : Set _)) = _
  rw [Submodule.span_image, euclideanKernel_span_eq_real_ker]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change powerCanonicalEquiv K b r (realCoefficientMap (ringCoefficientMatrix b X)
      ((powerCanonicalEquiv K b m).symm (powerCanonicalEquiv K b m x))) = 0
    rw [ContinuousLinearEquiv.symm_apply_apply, show realCoefficientMap (ringCoefficientMatrix b X) x = 0 from hx,
      map_zero]
  · intro hy
    change powerCanonicalEquiv K b r (realCoefficientMap (ringCoefficientMatrix b X)
      ((powerCanonicalEquiv K b m).symm y)) = 0 at hy
    refine ⟨(powerCanonicalEquiv K b m).symm y, ?_, (powerCanonicalEquiv K b m).apply_symm_apply y⟩
    exact (powerCanonicalEquiv K b r).injective (by simpa only [map_zero] using hy)

theorem canonicalPower_finrank (b : Basis (Fin d) ℤ (𝓞 K)) (n : ℕ) :
    finrank ℝ (CanonicalPower K n) = n * d := by
  simpa only [Euclidean, finrank_euclideanSpace, Fintype.card_fin] using
    (powerCanonicalEquiv K b n).toLinearEquiv.finrank_eq.symm

theorem canonicalKernel_discrete (b : Basis (Fin d) ℤ (𝓞 K))
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) : DiscreteTopology (canonicalKernel K X) := by
  let : DiscreteTopology (euclideanKernel (ringCoefficientMatrix b X)) :=
    integerEmbedding_map_discreteTopology _
  rw [canonicalKernel_eq_image K b X, latticeImage_equiv_eq_comap]
  infer_instance

/-- The rank assertion of Proposition 3.1. -/
theorem canonicalKernel_rank (b : Basis (Fin d) ℤ (𝓞 K))
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) (hX : Function.Surjective X.mulVec) :
    finrank ℤ (canonicalKernel K X) = d * (m - r) := by
  let : DiscreteTopology (canonicalKernel K X) := canonicalKernel_discrete K b X
  rw [intrinsicLattice_rank, canonicalKernel_span_eq_ker K b X]
  have h := (canonicalMatrixMap K b X).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (canonicalMatrixMap_surjective K b X hX), finrank_top,
    canonicalPower_finrank K b r, canonicalPower_finrank K b m] at h
  rw [Nat.mul_comm d, Nat.sub_mul]
  omega

end GeometricGaussianLHL
end

end CanonicalOperator

section DualCovolume

/-!
## Covolume of a full lattice and its dual

Full lattices are actual linear images of the integer lattice. The dual
image is given by the inverse adjoint, whose Jacobian is reciprocal.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Module MeasureTheory

namespace GeometricGaussianLHL

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem latticeImage_equiv_span_top (L : Submodule ℤ E) (hL : Submodule.span ℝ (L : Set E) = ⊤)
    (T : E ≃L[ℝ] F) : Submodule.span ℝ (latticeImage T.toContinuousLinearMap L : Set F) = ⊤ := by
  change Submodule.span ℝ (T.toLinearMap '' (L : Set E)) = ⊤
  rw [Submodule.span_image, hL, Submodule.map_top]
  exact LinearMap.range_eq_top.mpr T.surjective

theorem latticeDual_image_equiv (L : Submodule ℤ E) (hL : Submodule.span ℝ (L : Set E) = ⊤)
    (T : E ≃L[ℝ] F) :
    latticeDual (latticeImage T.toContinuousLinearMap L) =
      latticeImage (inverseAdjointEquiv T).toContinuousLinearMap (latticeDual L) := by
  ext y
  rw [mem_dual_image_iff_projected_inverse_adjoint,
    latticeImage_equiv_span_top L hL T]
  simp only [Submodule.starProjection_top, ContinuousLinearMap.id_apply]
  rfl

theorem fullLattice_eq_basis_image {n : ℕ} (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L] (b : Basis (Fin n) ℤ L) :
    L = latticeImage (basisEuclideanEquiv (b.ofZLatticeBasis ℝ L)).toContinuousLinearEquiv.toContinuousLinearMap
      (integerLattice n) := by
  rw [latticeImage, integerLattice_eq_basis_span, Submodule.map_span, ← Set.range_comp]
  change L = Submodule.span ℤ (Set.range (fun i =>
    basisEuclideanEquiv (b.ofZLatticeBasis ℝ L) (EuclideanSpace.basisFun (Fin n) ℝ i)))
  simp only [basisEuclideanEquiv_basis]
  exact (b.ofZLatticeBasis_span ℝ).symm

theorem normDet_symm_mul (T : E ≃L[ℝ] F) :
    T.symm.toLinearMap.normDet * T.toLinearMap.normDet = 1 := by
  rw [← LinearMap.normDet_comp_of_finrank_eq _ _ T.toLinearEquiv.finrank_eq]
  have h : T.symm.toLinearMap.comp T.toLinearMap = LinearMap.id := by ext x; exact T.symm_apply_apply x
  rw [h, LinearMap.normDet_id]

theorem inverseAdjointEquiv_normDet (T : E ≃L[ℝ] F) :
    (inverseAdjointEquiv T).toLinearMap.normDet = T.symm.toLinearMap.normDet := by
  change T.symm.toContinuousLinearMap.adjoint.toLinearMap.normDet = _
  rw [← ContinuousLinearMap.adjoint_toLinearMap,
    normDet_adjoint_of_finrank_eq _ T.toLinearEquiv.finrank_eq.symm]
  rfl

theorem fullLattice_dual_discrete (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] :
    DiscreteTopology (latticeDual L) := by
  let b := Module.finBasis ℤ L
  rw [fullLattice_eq_basis_image L b, latticeDual_image_equiv _ (integerLattice_span _),
    integerLattice_dual_eq, latticeImage_equiv_eq_comap]
  infer_instance

theorem fullLattice_dual_span (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] :
    Submodule.span ℝ (latticeDual L : Set E) = ⊤ := by
  let b := Module.finBasis ℤ L
  rw [fullLattice_eq_basis_image L b, latticeDual_image_equiv _ (integerLattice_span _), integerLattice_dual_eq]
  exact latticeImage_equiv_span_top _ (integerLattice_span _) _

variable [MeasurableSpace E] [BorelSpace E]

theorem fullLattice_dual_covolume_mul (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] :
    ZLattice.covolume (latticeDual L) * ZLattice.covolume L = 1 := by
  let b := Module.finBasis ℤ L
  rw [fullLattice_eq_basis_image L b, latticeDual_image_equiv _ (integerLattice_span _),
    integerLattice_dual_eq, covolume_latticeImage_equiv, covolume_latticeImage_equiv,
    integerLattice_covolume, mul_one, mul_one, inverseAdjointEquiv_normDet]
  exact normDet_symm_mul _

theorem fullLattice_dual_covolume (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] :
    ZLattice.covolume (latticeDual L) = (ZLattice.covolume L)⁻¹ := by
  have h := fullLattice_dual_covolume_mul L
  rw [← one_div]
  exact (eq_div_iff (ZLattice.covolume_pos L volume).ne').mpr h

end GeometricGaussianLHL
end

end DualCovolume

section CanonicalKernelCovolume

/-!
## Covolume of the actual canonical kernel

This specializes the lattice exact-sequence formula to ring-matrix
multiplication and the paper's canonical inner product. The rank and
covolume identities do not require a positive kernel dimension.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Module NumberField MeasureTheory

namespace GeometricGaussianLHL

variable (K : Type*) [Field K] [NumberField K] {d r m : ℕ}

local instance kernelCovolumeEmbeddingsFintype : Fintype (K →+* ℂ) := inferInstance
local instance kernelCovolumeAmbientInner : InnerProductSpace ℝ (CanonicalAmbient K) := inferInstance
local instance kernelCovolumeSpaceInner : InnerProductSpace ℝ (canonicalSpace K) := inferInstance
local instance kernelCovolumePowerInner (n : ℕ) : InnerProductSpace ℝ (CanonicalPower K n) := inferInstance
local instance kernelCovolumePowerMeasureSpace (n : ℕ) : MeasureSpace (CanonicalPower K n) :=
  measureSpaceOfInnerProductSpace

theorem canonicalLattice_discrete (b : Basis (Fin d) ℤ (𝓞 K)) (n : ℕ) :
    DiscreteTopology (canonicalLattice K n) := by
  rw [canonicalLattice_eq_image K b n, latticeImage_equiv_eq_comap]
  infer_instance

theorem canonicalKernel_eq_latticeKernel (b : Basis (Fin d) ℤ (𝓞 K))
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) :
    canonicalKernel K X = latticeKernel (canonicalLattice K m) (canonicalMatrixMap K b X) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟨x, rfl⟩, ?_⟩
    change canonicalMatrixMap K b X (canonicalPowerEmbedding K m x) = 0
    rw [canonicalMatrixMap_integer, show X.mulVec x = 0 from hx, map_zero]
  · rintro ⟨⟨x, rfl⟩, hx⟩
    refine ⟨x, ?_, rfl⟩
    apply canonicalPowerEmbedding_injective K r
    change canonicalPowerEmbedding K r (X.mulVec x) = canonicalPowerEmbedding K r 0
    rw [map_zero, ← canonicalMatrixMap_integer K b X]
    exact hx

theorem canonicalMatrixMap_lattice (b : Basis (Fin d) ℤ (𝓞 K))
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) :
    ∀ x ∈ canonicalLattice K m, canonicalMatrixMap K b X x ∈ canonicalLattice K r := by
  rintro _ ⟨x, rfl⟩
  exact ⟨X.mulVec x, (canonicalMatrixMap_integer K b X x).symm⟩

theorem canonicalMatrixMap_lattice_surjective (b : Basis (Fin d) ℤ (𝓞 K))
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) (hX : Function.Surjective X.mulVec) :
    Function.Surjective (latticeRestriction (canonicalLattice K m) (canonicalLattice K r)
      (canonicalMatrixMap K b X) (canonicalMatrixMap_lattice K b X)) := by
  rintro ⟨y, ⟨z, rfl⟩⟩
  obtain ⟨x, rfl⟩ := hX z
  refine ⟨⟨canonicalPowerEmbedding K m x, ⟨x, rfl⟩⟩, ?_⟩
  exact Subtype.ext (canonicalMatrixMap_integer K b X x)

theorem canonical_surjective_rows_le (b : Basis (Fin d) ℤ (𝓞 K))
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) (hX : Function.Surjective X.mulVec) : r ≤ m := by
  have h := LinearMap.finrank_le_finrank_of_surjective (canonicalMatrixMap_surjective K b X hX)
  rw [canonicalPower_finrank K b r, canonicalPower_finrank K b m] at h
  have hd := integralBasis_dimension_pos K b
  nlinarith

/-- The exact covolume identity of Proposition 3.1. -/
theorem canonicalKernel_covolume (b : Basis (Fin d) ℤ (𝓞 K))
    (X : Matrix (Fin r) (Fin m) (𝓞 K)) (hX : Function.Surjective X.mulVec) :
    intrinsicCovolume (canonicalKernel K X) =
      Real.sqrt |(NumberField.discr K : ℝ)| ^ (m - r) *
        Real.sqrt ((canonicalMatrixMap K b X).comp (canonicalMatrixMap K b X).adjoint).det := by
  let : DiscreteTopology (canonicalLattice K m) := canonicalLattice_discrete K b m
  let : DiscreteTopology (canonicalLattice K r) := canonicalLattice_discrete K b r
  let : IsZLattice ℝ (canonicalLattice K m) := ⟨canonicalLattice_span K b m⟩
  let : IsZLattice ℝ (canonicalLattice K r) := ⟨canonicalLattice_span K b r⟩
  have h := latticeKernel_covolume (canonicalLattice K m) (canonicalLattice K r)
    (canonicalMatrixMap K b X) (canonicalMatrixMap_surjective K b X hX)
    (canonicalMatrixMap_lattice K b X) (canonicalMatrixMap_lattice_surjective K b X hX)
    (by rw [← canonicalKernel_eq_latticeKernel K b X]; exact canonicalKernel_span_eq_ker K b X)
  rw [← canonicalKernel_eq_latticeKernel K b X, canonicalLattice_covolume K b m,
    canonicalLattice_covolume K b r, kernelJacobian_eq_sqrt_det] at h
  have hD : Real.sqrt |(NumberField.discr K : ℝ)| ≠ 0 := by
    apply Real.sqrt_ne_zero'.mpr
    exact abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero K)
  rw [div_eq_mul_inv, ← pow_sub₀ _ hD (canonical_surjective_rows_le K b X hX)] at h
  exact h

end GeometricGaussianLHL
end

end CanonicalKernelCovolume

section IntrinsicDual

/-!
## Duals in their intrinsic Euclidean span

Passing from an ambient lattice to the same lattice in its real span
preserves every dual vector and its norm. This also proves discreteness,
rank preservation, and covolume reciprocity for lower-rank lattices.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Module MeasureTheory

namespace GeometricGaussianLHL

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def intrinsicDualEquiv (L : Submodule ℤ E) [DiscreteTopology L] :
    latticeDual (intrinsicLattice L) ≃ₗᵢ[ℤ] latticeDual L where
  toFun v := ⟨(v : Submodule.span ℝ (L : Set E)), mem_latticeDual.mpr ⟨(v : Submodule.span ℝ (L : Set E)).property,
    fun z hz => (mem_latticeDual.mp v.property).2
      ⟨z, Submodule.subset_span hz⟩ hz⟩⟩
  invFun v := ⟨⟨v, v.property.1⟩, mem_latticeDual.mpr ⟨by
    rw [IsZLattice.span_top (K := ℝ) (L := intrinsicLattice L)]
    trivial,
    fun z hz => (mem_latticeDual.mp v.property).2 (z : E) hz⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' _ := rfl

omit [FiniteDimensional ℝ E] in
@[simp] theorem intrinsicDualEquiv_coe (L : Submodule ℤ E) [DiscreteTopology L]
    (v : latticeDual (intrinsicLattice L)) :
    (intrinsicDualEquiv L v : E) = ((v : Submodule.span ℝ (L : Set E)) : E) := rfl

instance latticeDual_discrete (L : Submodule ℤ E) [DiscreteTopology L] :
    DiscreteTopology (latticeDual L) := by
  letI : DiscreteTopology (latticeDual (intrinsicLattice L)) := fullLattice_dual_discrete _
  exact DiscreteTopology.of_continuous_injective (intrinsicDualEquiv L).symm.continuous
    (intrinsicDualEquiv L).symm.injective

theorem latticeDual_rank (L : Submodule ℤ E) [DiscreteTopology L] :
    finrank ℤ (latticeDual L) = finrank ℤ L := by
  let : IsZLattice ℝ (latticeDual (intrinsicLattice L)) := ⟨fullLattice_dual_span _⟩
  rw [← (intrinsicDualEquiv L).toLinearEquiv.finrank_eq, ZLattice.rank ℝ _, intrinsicLattice_rank]

theorem latticeDual_span (L : Submodule ℤ E) [DiscreteTopology L] :
    Submodule.span ℝ (latticeDual L : Set E) = Submodule.span ℝ (L : Set E) := by
  apply Submodule.eq_of_le_of_finrank_le
  · exact Submodule.span_le.mpr (fun _ hx => hx.1)
  · rw [← intrinsicLattice_rank, ← intrinsicLattice_rank, latticeDual_rank]

variable [MeasurableSpace E] [BorelSpace E]

theorem intrinsicCovolume_dual (L : Submodule ℤ E) [DiscreteTopology L] :
    intrinsicCovolume (latticeDual L) = (intrinsicCovolume L)⁻¹ := by
  let : IsZLattice ℝ (latticeDual (intrinsicLattice L)) := ⟨fullLattice_dual_span _⟩
  let b := Module.finBasis ℤ (latticeDual (intrinsicLattice L))
  have h : intrinsicCovolume (latticeDual L) = ZLattice.covolume (latticeDual (intrinsicLattice L)) := by
    rw [intrinsicCovolume_eq_sqrt_gram _ (b.map (intrinsicDualEquiv L).toLinearEquiv),
      covolume_eq_sqrt_gram _ b]
    rfl
  rw [h, fullLattice_dual_covolume]
  rfl

end GeometricGaussianLHL
end

end IntrinsicDual

section KernelMinimumStretch

/-!
## The smallest transverse stretch and the kernel Jacobian

For a surjective map, the restriction to the orthogonal complement of
its kernel is an isomorphism. Its inverse operator norm defines the
smallest transverse stretch. The determinant is at least this stretch
to the power of the codomain dimension, including dimension zero.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Module

namespace GeometricGaussianLHL

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

theorem normDet_ge_inverse_opNorm_pow (T : E ≃L[ℝ] F) :
    ‖T.symm.toContinuousLinearMap‖⁻¹ ^ finrank ℝ F ≤ T.toLinearMap.normDet := by
  have h := mul_le_mul_of_nonneg_right (normDet_le_opNorm_pow T.symm.toLinearMap)
    T.toLinearMap.normDet_nonneg
  change T.symm.toLinearMap.normDet * T.toLinearMap.normDet ≤
    ‖T.symm.toContinuousLinearMap‖ ^ finrank ℝ F * T.toLinearMap.normDet at h
  rw [normDet_symm_mul] at h
  have hp : 0 < ‖T.symm.toContinuousLinearMap‖ ^ finrank ℝ F := by
    by_contra hc
    have hz := le_antisymm (le_of_not_gt hc) (pow_nonneg (norm_nonneg _) _)
    rw [hz, zero_mul] at h
    norm_num at h
  rw [inv_pow]
  rw [← one_div]
  exact (div_le_iff₀ hp).mpr (by simpa only [mul_comm] using h)

def kernelMinimumStretch (f : E →ₗ[ℝ] F) (hf : Function.Surjective f) : ℝ :=
  ‖(kernelOrthogonalEquiv f hf).symm.toContinuousLinearEquiv.toContinuousLinearMap‖⁻¹

theorem kernelMinimumStretch_nonneg (f : E →ₗ[ℝ] F) (hf : Function.Surjective f) :
    0 ≤ kernelMinimumStretch f hf := by
  unfold kernelMinimumStretch
  positivity

theorem kernelJacobian_ge_minimumStretch_pow (f : E →ₗ[ℝ] F) (hf : Function.Surjective f) :
    kernelMinimumStretch f hf ^ finrank ℝ F ≤ f.adjoint.normDet := by
  have h := normDet_ge_inverse_opNorm_pow (kernelOrthogonalEquiv f hf).toContinuousLinearEquiv
  change kernelMinimumStretch f hf ^ finrank ℝ F ≤
    (kernelOrthogonalEquiv f hf).toLinearMap.normDet at h
  rwa [kernelOrthogonalEquiv_normDet] at h

theorem kernelMinimumStretch_mul_norm_le (f : E →ₗ[ℝ] F) (hf : Function.Surjective f)
    (x : f.kerᗮ) : kernelMinimumStretch f hf * ‖x‖ ≤ ‖f (x : E)‖ := by
  let T := (kernelOrthogonalEquiv f hf).toContinuousLinearEquiv
  have h := T.symm.toContinuousLinearMap.le_opNorm (T x)
  change ‖T.symm (T x)‖ ≤ ‖T.symm.toContinuousLinearMap‖ * ‖T x‖ at h
  rw [T.symm_apply_apply] at h
  by_cases hz : ‖T.symm.toContinuousLinearMap‖ = 0
  · change ‖T.symm.toContinuousLinearMap‖⁻¹ * ‖x‖ ≤ _
    simp only [hz, inv_zero, zero_mul, norm_nonneg]
  · have hp : 0 < ‖T.symm.toContinuousLinearMap‖ :=
      lt_of_le_of_ne (norm_nonneg T.symm.toContinuousLinearMap) (Ne.symm hz)
    change ‖T.symm.toContinuousLinearMap‖⁻¹ * ‖x‖ ≤ ‖T x‖
    rw [← div_eq_inv_mul]
    exact (div_le_iff₀ hp).mpr (by simpa only [mul_comm] using h)

theorem kernelMinimumStretch_pos [Nontrivial F] (f : E →ₗ[ℝ] F)
    (hf : Function.Surjective f) : 0 < kernelMinimumStretch f hf :=
  inv_pos.mpr (kernelOrthogonalEquiv f hf).symm.toContinuousLinearEquiv.norm_pos

/-- The inverse-norm definition is the best uniform lower stretch, so it
represents the smallest nonzero singular value in a coordinate-free way. -/
theorem le_kernelMinimumStretch_iff [Nontrivial F] (f : E →ₗ[ℝ] F)
    (hf : Function.Surjective f) {c : ℝ} (hc : 0 < c) :
    c ≤ kernelMinimumStretch f hf ↔ ∀ x : f.kerᗮ, c * ‖x‖ ≤ ‖f (x : E)‖ := by
  constructor
  · intro h x
    exact (mul_le_mul_of_nonneg_right h (norm_nonneg x)).trans
      (kernelMinimumStretch_mul_norm_le f hf x)
  · intro h
    let T := (kernelOrthogonalEquiv f hf).toContinuousLinearEquiv
    have hp : 0 < ‖T.symm.toContinuousLinearMap‖ := T.symm.norm_pos
    have hb : ‖T.symm.toContinuousLinearMap‖ ≤ c⁻¹ := by
      apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hc.le)
      intro y
      change ‖T.symm y‖ ≤ c⁻¹ * ‖y‖
      have hy := h (T.symm y)
      change c * ‖T.symm y‖ ≤ ‖T (T.symm y)‖ at hy
      rw [T.apply_symm_apply] at hy
      rw [← div_eq_inv_mul]
      exact (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hy)
    change c ≤ ‖T.symm.toContinuousLinearMap‖⁻¹
    rw [← one_div]
    apply (le_div_iff₀ hp).mpr
    have hb' := mul_le_mul_of_nonneg_right hb hc.le
    simpa only [inv_mul_cancel₀ hc.ne', mul_comm] using hb'

end GeometricGaussianLHL
end

end KernelMinimumStretch

section IsometricSmoothing

/-!
## Smoothing under isometries and passage to the real span

The actual dual Gaussian sums are unchanged by isometric coordinates and
by regarding a discrete lattice inside its intrinsic real span. These are
equalities of the infinite sums, including the zero-dimensional case.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace GeometricGaussianLHL

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

def latticeImageEquiv (T : E ≃L[ℝ] F) (L : Submodule ℤ E) :
    L ≃ₗ[ℤ] latticeImage T.toContinuousLinearMap L :=
  Submodule.equivMapOfInjective (T.toLinearMap.restrictScalars ℤ) T.injective L

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
@[simp] theorem latticeImageEquiv_apply (T : E ≃L[ℝ] F) (L : Submodule ℤ E) (v : L) :
    (latticeImageEquiv T L v : F) = T (v : E) := rfl

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem latticeImage_discrete (T : E ≃L[ℝ] F) (L : Submodule ℤ E) [DiscreteTopology L] :
    DiscreteTopology (latticeImage T.toContinuousLinearMap L) := by
  rw [latticeImage_equiv_eq_comap]
  infer_instance

theorem inverseAdjointEquiv_isometry (e : E ≃ₗᵢ[ℝ] F) :
    inverseAdjointEquiv e.toContinuousLinearEquiv = e.toContinuousLinearEquiv := by
  ext x
  change e.symm.toContinuousLinearEquiv.toContinuousLinearMap.adjoint x = e x
  rw [e.symm.adjoint_eq_symm]
  rfl

theorem nonzeroDualMass_isometry (L : Submodule ℤ E)
    (hL : Submodule.span ℝ (L : Set E) = ⊤) (e : E ≃ₗᵢ[ℝ] F) (t : ℝ) :
    nonzeroDualMass (latticeImage e.toContinuousLinearEquiv.toContinuousLinearMap L) t =
      nonzeroDualMass L t := by
  classical
  rw [nonzeroDualMass, latticeDual_image_equiv L hL, inverseAdjointEquiv_isometry]
  let f := latticeImageEquiv e.toContinuousLinearEquiv (latticeDual L)
  rw [← f.toEquiv.tsum_eq]
  apply tsum_congr
  intro v
  have hz : f.toEquiv v = 0 ↔ v = 0 := f.map_eq_zero_iff
  simp only [hz]
  split_ifs
  · rfl
  · congr 1
    change gaussianWeight t (e (v : E)) = gaussianWeight t (v : E)
    simp only [gaussianWeight, e.norm_map]

theorem smoothAt_isometry_iff (L : Submodule ℤ E)
    (hL : Submodule.span ℝ (L : Set E) = ⊤) (e : E ≃ₗᵢ[ℝ] F) (ε t : ℝ) :
    SmoothAt (latticeImage e.toContinuousLinearEquiv.toContinuousLinearMap L) ε t ↔
      SmoothAt L ε t := by
  simp only [SmoothAt, nonzeroDualMass_isometry L hL e]

theorem smoothingParameter_isometry (L : Submodule ℤ E)
    (hL : Submodule.span ℝ (L : Set E) = ⊤) (e : E ≃ₗᵢ[ℝ] F) (ε : ℝ) :
    smoothingParameter (latticeImage e.toContinuousLinearEquiv.toContinuousLinearMap L) ε =
      smoothingParameter L ε := by
  simp only [smoothingParameter, smoothAt_isometry_iff L hL e]

omit [FiniteDimensional ℝ E] in
theorem nonzeroDualMass_intrinsic (L : Submodule ℤ E) [DiscreteTopology L] (t : ℝ) :
    nonzeroDualMass (intrinsicLattice L) t = nonzeroDualMass L t := by
  classical
  unfold nonzeroDualMass
  rw [← (intrinsicDualEquiv L).toEquiv.tsum_eq]
  apply tsum_congr
  intro v
  have hz : (intrinsicDualEquiv L).toEquiv v = 0 ↔ v = 0 :=
    (intrinsicDualEquiv L).map_eq_zero_iff
  simp only [hz]
  split_ifs <;> rfl

omit [FiniteDimensional ℝ E] in
theorem smoothAt_intrinsic_iff (L : Submodule ℤ E) [DiscreteTopology L] (ε t : ℝ) :
    SmoothAt (intrinsicLattice L) ε t ↔ SmoothAt L ε t := by
  simp only [SmoothAt, nonzeroDualMass_intrinsic]

omit [FiniteDimensional ℝ E] in
theorem smoothingParameter_intrinsic (L : Submodule ℤ E) [DiscreteTopology L] (ε : ℝ) :
    smoothingParameter (intrinsicLattice L) ε = smoothingParameter L ε := by
  simp only [smoothingParameter, smoothAt_intrinsic_iff]

end GeometricGaussianLHL
end

end IsometricSmoothing

section IsometricDualTransport

/-!
## Isometric transport of intrinsic duals in every rank

An isometry carries the lattice span onto the image span and preserves
every integral inner-product pairing. The intrinsic dual is transported
exactly, even for lower-rank lattices. The actual dual Gaussian mass and
smoothing infimum are therefore preserved without a full-span premise.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace GeometricGaussianLHL

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem latticeImage_real_span (T : E →L[ℝ] F) (L : Submodule ℤ E) :
    Submodule.span ℝ (latticeImage T L : Set F) =
      (Submodule.span ℝ (L : Set E)).map T.toLinearMap := by
  change Submodule.span ℝ (T.toLinearMap '' (L : Set E)) = _
  rw [Submodule.span_image]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem latticeDual_image_isometry (e : E ≃ₗᵢ[ℝ] F) (L : Submodule ℤ E) :
    latticeDual (latticeImage e.toContinuousLinearEquiv.toContinuousLinearMap L) =
      latticeImage e.toContinuousLinearEquiv.toContinuousLinearMap (latticeDual L) := by
  ext y
  constructor
  · intro hy
    have hs := (mem_latticeDual.mp hy).1
    rw [latticeImage_real_span] at hs
    obtain ⟨v, hv, rfl⟩ := hs
    refine ⟨v, mem_latticeDual.mpr ⟨hv, ?_⟩, rfl⟩
    intro w hw
    obtain ⟨k, hk⟩ := (mem_latticeDual.mp hy).2 (e w) ⟨w, hw, rfl⟩
    refine ⟨k, ?_⟩
    change (k : ℝ) = inner ℝ (e v) (e w) at hk
    simpa only [e.inner_map_map] using hk
  · rintro ⟨v, hv, rfl⟩
    apply mem_latticeDual.mpr
    constructor
    · rw [latticeImage_real_span]
      exact ⟨v, (mem_latticeDual.mp hv).1, rfl⟩
    · rintro z ⟨w, hw, rfl⟩
      obtain ⟨k, hk⟩ := (mem_latticeDual.mp hv).2 w hw
      refine ⟨k, ?_⟩
      change (k : ℝ) = inner ℝ (e v) (e w)
      rw [e.inner_map_map]
      exact hk

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem nonzeroDualMass_isometry_all (e : E ≃ₗᵢ[ℝ] F) (L : Submodule ℤ E) (t : ℝ) :
    nonzeroDualMass (latticeImage e.toContinuousLinearEquiv.toContinuousLinearMap L) t =
      nonzeroDualMass L t := by
  classical
  rw [nonzeroDualMass, latticeDual_image_isometry]
  let f := latticeImageEquiv e.toContinuousLinearEquiv (latticeDual L)
  rw [← f.toEquiv.tsum_eq]
  apply tsum_congr
  intro v
  have hz : f.toEquiv v = 0 ↔ v = 0 := f.map_eq_zero_iff
  simp only [hz]
  split_ifs
  · rfl
  · congr 1
    change gaussianWeight t (e (v : E)) = gaussianWeight t (v : E)
    simp only [gaussianWeight, e.norm_map]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem smoothAt_isometry_all_iff (e : E ≃ₗᵢ[ℝ] F) (L : Submodule ℤ E) (ε t : ℝ) :
    SmoothAt (latticeImage e.toContinuousLinearEquiv.toContinuousLinearMap L) ε t ↔
      SmoothAt L ε t := by
  simp only [SmoothAt, nonzeroDualMass_isometry_all]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem smoothingParameter_isometry_all (e : E ≃ₗᵢ[ℝ] F) (L : Submodule ℤ E) (ε : ℝ) :
    smoothingParameter (latticeImage e.toContinuousLinearEquiv.toContinuousLinearMap L) ε =
      smoothingParameter L ε := by
  simp only [smoothingParameter, smoothAt_isometry_all_iff]

end GeometricGaussianLHL
end

end IsometricDualTransport

section IsometricEmbeddingSmoothing

/-!
## Smoothing under isometric embeddings into larger spaces

Surjectivity onto the ambient target is unnecessary: the intrinsic dual
lies in the image of the lattice span. An isometric embedding therefore
preserves the dual Gaussian mass and the actual smoothing infimum.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace GeometricGaussianLHL

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

def latticeIsometricImageEquiv (e : E →ₗᵢ[ℝ] F) (L : Submodule ℤ E) :
    L ≃ₗ[ℤ] latticeImage e.toContinuousLinearMap L :=
  Submodule.equivMapOfInjective (e.toLinearMap.restrictScalars ℤ) e.injective L

theorem latticeIsometricImageEquiv_apply (e : E →ₗᵢ[ℝ] F) (L : Submodule ℤ E) (v : L) :
    (latticeIsometricImageEquiv e L v : F) = e (v : E) := rfl

theorem latticeDual_image_isometricEmbedding (e : E →ₗᵢ[ℝ] F) (L : Submodule ℤ E) :
    latticeDual (latticeImage e.toContinuousLinearMap L) =
      latticeImage e.toContinuousLinearMap (latticeDual L) := by
  ext y
  constructor
  · intro hy
    have hs := (mem_latticeDual.mp hy).1
    rw [latticeImage_real_span] at hs
    obtain ⟨v, hv, rfl⟩ := hs
    refine ⟨v, mem_latticeDual.mpr ⟨hv, ?_⟩, rfl⟩
    intro w hw
    obtain ⟨k, hk⟩ := (mem_latticeDual.mp hy).2 (e w) ⟨w, hw, rfl⟩
    refine ⟨k, ?_⟩
    change (k : ℝ) = inner ℝ (e v) (e w) at hk
    simpa only [e.inner_map_map] using hk
  · rintro ⟨v, hv, rfl⟩
    apply mem_latticeDual.mpr
    constructor
    · rw [latticeImage_real_span]
      exact ⟨v, (mem_latticeDual.mp hv).1, rfl⟩
    · rintro z ⟨w, hw, rfl⟩
      obtain ⟨k, hk⟩ := (mem_latticeDual.mp hv).2 w hw
      refine ⟨k, ?_⟩
      change (k : ℝ) = inner ℝ (e v) (e w)
      rw [e.inner_map_map]
      exact hk

theorem nonzeroDualMass_isometricEmbedding (e : E →ₗᵢ[ℝ] F) (L : Submodule ℤ E) (t : ℝ) :
    nonzeroDualMass (latticeImage e.toContinuousLinearMap L) t = nonzeroDualMass L t := by
  classical
  rw [nonzeroDualMass, latticeDual_image_isometricEmbedding]
  let f := latticeIsometricImageEquiv e (latticeDual L)
  rw [← f.toEquiv.tsum_eq]
  apply tsum_congr
  intro v
  have hz : f.toEquiv v = 0 ↔ v = 0 := f.map_eq_zero_iff
  simp only [hz]
  split_ifs
  · rfl
  · congr 1
    change gaussianWeight t (e (v : E)) = gaussianWeight t (v : E)
    simp only [gaussianWeight, e.norm_map]

theorem smoothAt_isometricEmbedding_iff (e : E →ₗᵢ[ℝ] F) (L : Submodule ℤ E) (ε t : ℝ) :
    SmoothAt (latticeImage e.toContinuousLinearMap L) ε t ↔ SmoothAt L ε t := by
  simp only [SmoothAt, nonzeroDualMass_isometricEmbedding]

theorem smoothingParameter_isometricEmbedding (e : E →ₗᵢ[ℝ] F) (L : Submodule ℤ E) (ε : ℝ) :
    smoothingParameter (latticeImage e.toContinuousLinearMap L) ε = smoothingParameter L ε := by
  simp only [smoothingParameter, smoothAt_isometricEmbedding_iff]

end GeometricGaussianLHL
end

end IsometricEmbeddingSmoothing
