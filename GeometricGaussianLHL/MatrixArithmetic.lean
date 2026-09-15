import GeometricGaussianLHL.AlgebraicInput

/-!
# Matrix arithmetic, normalization, and costs

This module collects the following proof sections, in dependency order.
- Unitary invariance of the matrix norm (`UnitaryMatrixNorm`).
- Magnitude of integer matrix products (`IntegerProductBounds`).
- Operator norm from a spectrum in the unit interval (`SpectralMatrixNorm`).
- Bit length of scaled integer matrix products (`IntegerScaledProductSize`).
- Matrices for repeated Euclidean coordinate changes (`EuclideanMatrixBlocks`).
- Error bounds for repeated matrix blocks (`EuclideanMatrixBlockBounds`).
- Stored integer matrix arithmetic with accumulated costs (`IntegerMatrixCost`).
- Costs of preparing integer numerators from stored rational matrices (`RationalInputCost`).
- Input-size lower bounds for rational positive definite matrices (`RationalSpectralConditioning`).
- Explicit normalization and conditioning from rational input size (`RationalMatrixNormalization`).
- Normalization from an unreduced integer/denominator encoding (`RepresentedMatrixNormalization`).
- Computing normalization from the finite rational input (`RationalNormalizationCost`).
- Costs of integer output rounding and rational serialization (`IntegerOutputCost`).
- Rational matrix postprocessing costs (`RationalMatrixOutputCost`).
- Rational dot products with polynomial operand growth (`RationalDotCost`).
- Stored rectangular rational matrix operations (`RationalRectCost`).
- Gram matrices and the average diagonal entry (`RationalGramCost`).
-/

section UnitaryMatrixNorm

/-!
## Unitary invariance of the matrix norm
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open scoped MatrixOrder Matrix.Norms.L2Operator

namespace GeometricGaussianLHL

theorem unitaryConj_matrix_norm {n : ℕ} (U : unitary (Matrix (Fin n) (Fin n) ℝ))
    (M : Matrix (Fin n) (Fin n) ℝ) :
    ‖Unitary.conjStarAlgAut ℝ _ U M‖ = ‖M‖ := by
  simp only [Unitary.conjStarAlgAut_apply, ← Unitary.coe_star,
    CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul]

end GeometricGaussianLHL
end

end UnitaryMatrixNorm

section IntegerProductBounds

/-!
## Magnitude of integer matrix products
-/

namespace GeometricGaussianLHL

theorem integerMatrix_partial_product_bound {n : ℕ} (s : Finset (Fin n))
    (X Y : Matrix (Fin n) (Fin n) ℤ) (P Q : ℕ)
    (hX : ∀ i j, (X i j).natAbs ≤ P) (hY : ∀ i j, (Y i j).natAbs ≤ Q)
    (i j : Fin n) : (∑ k ∈ s, X i k * Y k j).natAbs ≤ n * (P * Q) := by
  calc
    _ ≤ ∑ k ∈ s, (X i k * Y k j).natAbs := Int.natAbs_sum_le _ _
    _ ≤ ∑ _k ∈ s, P * Q := Finset.sum_le_sum fun k _ => by
      rw [Int.natAbs_mul]
      exact Nat.mul_le_mul (hX i k) (hY k j)
    _ = s.card * (P * Q) := by simp
    _ ≤ n * (P * Q) := Nat.mul_le_mul_right _ (by simpa using Finset.card_le_univ s)

theorem integerMatrix_product_bound {n : ℕ}
    (X Y : Matrix (Fin n) (Fin n) ℤ) (P Q : ℕ)
    (hX : ∀ i j, (X i j).natAbs ≤ P) (hY : ∀ i j, (Y i j).natAbs ≤ Q)
    (i j : Fin n) : ((X * Y) i j).natAbs ≤ n * (P * Q) := by
  rw [Matrix.mul_apply]
  exact integerMatrix_partial_product_bound Finset.univ X Y P Q hX hY i j

theorem integerMatrix_scalar_identity_bound {n : ℕ} (c : ℤ) (i j : Fin n) :
    ((c • (1 : Matrix (Fin n) (Fin n) ℤ)) i j).natAbs ≤ c.natAbs := by
  change (c • (if i = j then (1 : ℤ) else 0)).natAbs ≤ c.natAbs
  by_cases h : i = j <;> simp [h]

end GeometricGaussianLHL

end IntegerProductBounds

section SpectralMatrixNorm

/-!
## Operator norm from a spectrum in the unit interval
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open scoped MatrixOrder Matrix.Norms.L2Operator

namespace GeometricGaussianLHL

theorem schulzMatrix_input_norm_le {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosSemidef)
    (hhi : ∀ i, hA.isHermitian.eigenvalues i ≤ 1) : ‖A‖ ≤ 1 := by
  have hs := hA.isHermitian.spectral_theorem
  calc
    ‖A‖ = ‖Unitary.conjStarAlgAut ℝ _ hA.isHermitian.eigenvectorUnitary
        (Matrix.diagonal hA.isHermitian.eigenvalues)‖ := congrArg norm hs
    _ = ‖hA.isHermitian.eigenvalues‖ := by
      rw [unitaryConj_matrix_norm, Matrix.l2_opNorm_diagonal]
    _ ≤ 1 := by
      apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
      intro i
      rw [Real.norm_eq_abs, abs_of_nonneg (hA.eigenvalues_nonneg i)]
      exact hhi i

end GeometricGaussianLHL
end

end SpectralMatrixNorm

section IntegerScaledProductSize

/-!
## Bit length of scaled integer matrix products
-/

set_option backward.isDefEq.respectTransparency false

open scoped MatrixOrder Matrix.Norms.L2Operator

namespace GeometricGaussianLHL

theorem integerScaledProduct_size {n : ℕ} (r U V : ℕ)
    (X N : Matrix (Fin n) (Fin n) ℤ)
    (hX : ∀ i j, (X i j).natAbs ≤ 2 ^ U)
    (hN : ∀ i j, (N i j).natAbs ≤ 2 ^ V) (i j : Fin n) :
    ((X * N) i j * (2 : ℤ) ^ r).natAbs.size ≤ n + U + V + r + 1 := by
  have h : ((X * N) i j * (2 : ℤ) ^ r).natAbs ≤ 2 ^ (n + U + V + r) := by
    simp only [Int.natAbs_mul, Int.natAbs_pow]
    change ((X * N) i j).natAbs * 2 ^ r ≤ _
    calc
      _ ≤ n * (2 ^ U * 2 ^ V) * 2 ^ r :=
        Nat.mul_le_mul_right _ (integerMatrix_product_bound X N _ _ hX hN i j)
      _ ≤ 2 ^ n * (2 ^ U * 2 ^ V) * 2 ^ r :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.lt_two_pow_self (n := n)).le)
      _ = _ := by simp only [pow_add]; ring
  apply Nat.size_le.mpr
  rw [pow_succ]
  have hp : 0 < 2 ^ (n + U + V + r) := by positivity
  omega

end GeometricGaussianLHL

end IntegerScaledProductSize

section EuclideanMatrixBlocks

/-!
## Matrices for repeated Euclidean coordinate changes

The matrix consists of explicit diagonal copies of the same block. Its
operator acts on the existing flattened block coordinates, and inverses of
continuous linear equivalences correspond to nonsingular matrix inverses.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace GeometricGaussianLHL

def repeatedEuclideanMatrix {𝕜 : Type*} [Zero 𝕜] {d : ℕ} (n : ℕ) (M : Matrix (Fin d) (Fin d) 𝕜) :
    Matrix (Fin (n * d)) (Fin (n * d)) 𝕜 := fun i j =>
  if (finProdFinEquiv.symm i).1 = (finProdFinEquiv.symm j).1 then
    M (finProdFinEquiv.symm i).2 (finProdFinEquiv.symm j).2 else 0

theorem repeatedEuclideanMatrix_apply {𝕜 : Type*} [Zero 𝕜] {d : ℕ}
    (n : ℕ) (M : Matrix (Fin d) (Fin d) 𝕜)
    (i j : Fin n × Fin d) :
    repeatedEuclideanMatrix n M (finProdFinEquiv i) (finProdFinEquiv j) =
      if i.1 = j.1 then M i.2 j.2 else 0 := by simp [repeatedEuclideanMatrix]

theorem repeatedEuclideanMatrix_operator {d : ℕ} (n : ℕ) (M : Matrix (Fin d) (Fin d) ℝ)
    (x : Euclidean (n * d)) (j : Fin n) :
    euclideanBlocks n d (Matrix.toEuclideanLin (repeatedEuclideanMatrix n M) x) j =
      Matrix.toEuclideanLin M (euclideanBlocks n d x j) := by
  ext i
  change (∑ k : Fin (n * d), repeatedEuclideanMatrix n M (finProdFinEquiv (j, i)) k * x k) =
    ∑ k : Fin d, M i k * x (finProdFinEquiv (j, k))
  rw [← finProdFinEquiv.sum_comp]
  simp only [repeatedEuclideanMatrix_apply, Fintype.sum_prod_type, ite_mul, zero_mul]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]

theorem repeatedEuclideanMatrix_equiv {d : ℕ} (n : ℕ) (S : Euclidean d ≃L[ℝ] Euclidean d) :
    Matrix.toEuclideanLin (repeatedEuclideanMatrix n (Matrix.toEuclideanLin.symm S.toLinearMap)) =
      (((euclideanBlocks n d).toContinuousLinearEquiv.trans (repeatedContinuousEquiv S n)).trans
        (euclideanBlocks n d).symm.toContinuousLinearEquiv).toLinearMap := by
  ext x : 1
  apply (euclideanBlocks n d).injective
  ext j : 1
  rw [repeatedEuclideanMatrix_operator, LinearEquiv.apply_symm_apply]
  change S (euclideanBlocks n d x j) = euclideanBlocks n d ((euclideanBlocks n d).symm _) j
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

theorem euclideanEquiv_matrix_symm {d : ℕ} (S : Euclidean d ≃L[ℝ] Euclidean d) :
    Matrix.toEuclideanLin.symm S.symm.toLinearMap = (Matrix.toEuclideanLin.symm S.toLinearMap)⁻¹ := by
  apply Matrix.inv_eq_right_inv _ |>.symm
  rw [← Matrix.toLpLin_symm_comp, show S.toLinearMap.comp S.symm.toLinearMap = LinearMap.id by
    ext x : 1
    exact S.apply_symm_apply x, Matrix.toLpLin_symm_id]

end GeometricGaussianLHL
end

end EuclideanMatrixBlocks

section EuclideanMatrixBlockBounds

/-!
## Error bounds for repeated matrix blocks

Repeating a block does not increase its Euclidean operator norm. The same
bound applies to differences, so normalizing many ring coordinates incurs
no extra error factor from the number of blocks.
-/

open scoped Matrix.Norms.L2Operator

namespace GeometricGaussianLHL

theorem repeatedEuclideanMatrix_map {𝕜 𝕝 : Type*} [Zero 𝕜] [Zero 𝕝]
    {d : ℕ} (n : ℕ) (M : Matrix (Fin d) (Fin d) 𝕜) (f : 𝕜 → 𝕝) (hf : f 0 = 0) :
    (repeatedEuclideanMatrix n M).map f = repeatedEuclideanMatrix n (M.map f) := by
  ext i j
  simp only [repeatedEuclideanMatrix, Matrix.map_apply]
  split_ifs <;> simp [hf]

theorem repeatedEuclideanMatrix_sub {𝕜 : Type*} [AddGroup 𝕜] {d : ℕ}
    (n : ℕ) (M N : Matrix (Fin d) (Fin d) 𝕜) :
    repeatedEuclideanMatrix n (M - N) = repeatedEuclideanMatrix n M - repeatedEuclideanMatrix n N := by
  ext i j
  simp only [repeatedEuclideanMatrix, Matrix.sub_apply]
  split_ifs <;> simp

theorem repeatedEuclideanMatrix_norm_le {d : ℕ} (n : ℕ) (M : Matrix (Fin d) (Fin d) ℝ) :
    ‖repeatedEuclideanMatrix n M‖ ≤ ‖M‖ := by
  change ‖(Matrix.toEuclideanLin (repeatedEuclideanMatrix n M)).toContinuousLinearMap‖ ≤ ‖M‖
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  calc
    _ = ∑ j : Fin n, ‖Matrix.toEuclideanLin M (euclideanBlocks n d x j)‖ ^ 2 := by
      change ‖Matrix.toEuclideanLin (repeatedEuclideanMatrix n M) x‖ ^ 2 = _
      rw [← (euclideanBlocks n d).norm_map (Matrix.toEuclideanLin (repeatedEuclideanMatrix n M) x),
        PiLp.norm_sq_eq_of_L2]
      simp only [repeatedEuclideanMatrix_operator]
    _ ≤ ∑ j : Fin n, (‖M‖ * ‖euclideanBlocks n d x j‖) ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      exact pow_le_pow_left₀ (norm_nonneg _) ((Matrix.toEuclideanLin M).toContinuousLinearMap.le_opNorm _) 2
    _ = _ := by
      simp only [mul_pow, ← Finset.mul_sum, ← PiLp.norm_sq_eq_of_L2, LinearIsometryEquiv.norm_map]

theorem repeatedEuclideanMatrix_error {d : ℕ} (n : ℕ) (M N : Matrix (Fin d) (Fin d) ℝ) :
    ‖repeatedEuclideanMatrix n M - repeatedEuclideanMatrix n N‖ ≤ ‖M - N‖ := by
  rw [← repeatedEuclideanMatrix_sub]
  exact repeatedEuclideanMatrix_norm_le _ _

end GeometricGaussianLHL

end EuclideanMatrixBlockBounds

section IntegerMatrixCost

/-!
## Stored integer matrix arithmetic with accumulated costs

Vector construction stores the individual executions before extracting their
values and adding their costs. Dot products charge the actual integer operands
and partial sums. The matrix operations return stored vectors and refine the
matrix formulas used by the numerical proofs. Vector traversal and list
construction have explicit linear charges in this arithmetic cost model.
-/

namespace GeometricGaussianLHL

def costedVectorOfFn {α : Type*} {n : ℕ} (f : Fin n → Costed α) : Costed (Vector α n) :=
  let runs := Vector.ofFn f
  ⟨runs.map Costed.value, (runs.toList.map Costed.steps).sum + 3 * n + 1⟩

theorem costedVectorOfFn_value {α : Type*} {n : ℕ} (f : Fin n → Costed α) :
    (costedVectorOfFn f).value = Vector.ofFn (fun i => (f i).value) := by
  ext i hi
  simp [costedVectorOfFn]

theorem costedVectorOfFn_steps {α : Type*} {n : ℕ} (f : Fin n → Costed α) :
    (costedVectorOfFn f).steps = (∑ i, (f i).steps) + 3 * n + 1 := by
  simp [costedVectorOfFn, Vector.toList_ofFn, List.sum_ofFn]

theorem costedVectorOfFn_steps_le {α : Type*} {n : ℕ} (f : Fin n → Costed α)
    (B : ℕ) (hf : ∀ i, (f i).steps ≤ B) :
    (costedVectorOfFn f).steps ≤ n * (B + 3) + 1 := by
  rw [costedVectorOfFn_steps]
  have h : (∑ i, (f i).steps) ≤ n * B := by
    simpa using Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hf i)
  nlinarith

theorem integer_size_le_of_abs_bound (a : ℤ) (L : ℕ) (ha : a.natAbs ≤ 2 ^ L) :
    a.natAbs.size ≤ L + 1 := by
  apply Nat.size_le.mpr
  exact ha.trans_lt (Nat.pow_lt_pow_right (by omega) (by omega))

theorem integer_mul_size_le (a b : ℤ) (U V : ℕ)
    (ha : a.natAbs.size ≤ U) (hb : b.natAbs.size ≤ V) :
    (a * b).natAbs.size ≤ U + V + 1 := by
  apply integer_size_le_of_abs_bound
  rw [Int.natAbs_mul, pow_add]
  exact Nat.mul_le_mul (Nat.size_le.mp ha).le (Nat.size_le.mp hb).le

theorem integer_sub_size_le (a b : ℤ) (L : ℕ)
    (ha : a.natAbs.size ≤ L) (hb : b.natAbs.size ≤ L) :
    (a - b).natAbs.size ≤ L + 2 := by
  have h := (Int.natAbs_sub_le a b).trans (Nat.add_le_add (Nat.size_le.mp ha).le (Nat.size_le.mp hb).le)
  have hp : (a - b).natAbs ≤ 2 ^ (L + 1) := by simpa [pow_succ, Nat.mul_two] using h
  exact integer_size_le_of_abs_bound _ (L + 1) hp

def integerListDot (xs : List (ℤ × ℤ)) : ℤ := (xs.map (fun x => x.1 * x.2)).sum

def costedIntegerDot : List (ℤ × ℤ) → Costed ℤ
  | [] => Costed.charge 1 0
  | (a, b) :: xs =>
    (costedIntegerDot xs).bind fun s =>
      (costedIntMul a b).bind fun p =>
        (costedIntAdd p s).bind fun z => Costed.charge 1 z

@[simp] theorem costedIntegerDot_value (xs : List (ℤ × ℤ)) :
    (costedIntegerDot xs).value = integerListDot xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp [costedIntegerDot, costedIntMul, costedIntAdd, Costed.charge, integerListDot] at *
    exact ih

theorem integerListDot_abs_le (xs : List (ℤ × ℤ)) (L : ℕ)
    (hxs : ∀ x ∈ xs, x.1.natAbs.size ≤ L ∧ x.2.natAbs.size ≤ L) :
    (integerListDot xs).natAbs ≤ xs.length * 2 ^ (2 * L) := by
  induction xs with
  | nil => simp [integerListDot]
  | cons x xs ih =>
    have hx := hxs x (List.mem_cons_self ..)
    have ht := ih (fun y hy => hxs y (List.mem_cons_of_mem _ hy))
    have hm : (x.1 * x.2).natAbs ≤ 2 ^ (2 * L) := by
      rw [Int.natAbs_mul, two_mul, pow_add]
      exact Nat.mul_le_mul (Nat.size_le.mp hx.1).le (Nat.size_le.mp hx.2).le
    simpa [integerListDot, Nat.add_mul, Nat.add_comm] using
      (Int.natAbs_add_le (x.1 * x.2) (integerListDot xs)).trans (Nat.add_le_add hm ht)

theorem integerListDot_size_le (xs : List (ℤ × ℤ)) (L : ℕ)
    (hxs : ∀ x ∈ xs, x.1.natAbs.size ≤ L ∧ x.2.natAbs.size ≤ L) :
    (integerListDot xs).natAbs.size ≤ xs.length + 2 * L + 1 := by
  apply integer_size_le_of_abs_bound
  calc
    _ ≤ xs.length * 2 ^ (2 * L) := integerListDot_abs_le xs L hxs
    _ ≤ 2 ^ xs.length * 2 ^ (2 * L) := Nat.mul_le_mul_right _ (Nat.lt_two_pow_self (n := xs.length)).le
    _ = _ := (pow_add ..).symm

def integerDotStepBudget (n L : ℕ) : ℕ := (2 * L + 1) ^ 2 + n + 4 * L + 4

theorem costedIntegerDot_steps_le (xs : List (ℤ × ℤ)) (L : ℕ)
    (hxs : ∀ x ∈ xs, x.1.natAbs.size ≤ L ∧ x.2.natAbs.size ≤ L) :
    (costedIntegerDot xs).steps ≤ xs.length * integerDotStepBudget xs.length L + 1 := by
  induction xs with
  | nil => simp [costedIntegerDot, Costed.charge]
  | cons x xs ih =>
    have hx := hxs x (List.mem_cons_self ..)
    have ht := fun y hy => hxs y (List.mem_cons_of_mem _ hy)
    have hs := integerListDot_size_le xs L ht
    have hp := integer_mul_size_le x.1 x.2 L L hx.1 hx.2
    have hm : (integerOperandBits x.1 x.2) ^ 2 ≤ (2 * L + 1) ^ 2 :=
      Nat.pow_le_pow_left (by unfold integerOperandBits; omega) 2
    have ha : integerOperandBits (x.1 * x.2) (integerListDot xs) ≤ xs.length + 4 * L + 3 := by
      unfold integerOperandBits
      omega
    have hi := ih ht
    simp only [costedIntegerDot, Costed.bind_steps, costedIntegerDot_value,
      costedIntMul, costedIntAdd, Costed.charge, List.length_cons]
    unfold integerDotStepBudget at hi ⊢
    nlinarith

def costedIntegerMatrixOfFn {n : ℕ} (f : Fin n → Fin n → Costed ℤ) : Costed (IntegerMatrixData n) :=
  costedVectorOfFn (fun i => costedVectorOfFn (f i))

theorem costedIntegerMatrixOfFn_value {n : ℕ} (f : Fin n → Fin n → Costed ℤ) :
    integerMatrixOfData (costedIntegerMatrixOfFn f).value = fun i j => (f i j).value := by
  ext i j
  simp [costedIntegerMatrixOfFn, costedVectorOfFn_value, integerMatrixOfData, Vector.get]
  rfl

theorem integerMatrixData_ofData {n : ℕ} (X : IntegerMatrixData n) :
    integerMatrixData (integerMatrixOfData X) = X := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  simp [integerMatrixData, integerMatrixOfData, Vector.get]
  rfl

theorem costedIntegerMatrixOfFn_data {n : ℕ} (f : Fin n → Fin n → Costed ℤ) :
    (costedIntegerMatrixOfFn f).value = integerMatrixData (fun i j => (f i j).value) := by
  rw [← integerMatrixData_ofData (costedIntegerMatrixOfFn f).value, costedIntegerMatrixOfFn_value]

def integerMatrixTraversalBudget (n B : ℕ) : ℕ := n * (n * (B + 3) + 4) + 1

theorem costedIntegerMatrixOfFn_steps_le {n : ℕ} (f : Fin n → Fin n → Costed ℤ)
    (B : ℕ) (hf : ∀ i j, (f i j).steps ≤ B) :
    (costedIntegerMatrixOfFn f).steps ≤ integerMatrixTraversalBudget n B :=
  costedVectorOfFn_steps_le _ _ (fun i => costedVectorOfFn_steps_le _ B (hf i))

def costedIntegerMatrixMul {n : ℕ} (X Y : IntegerMatrixData n) : Costed (IntegerMatrixData n) :=
  costedIntegerMatrixOfFn fun i j =>
    (Costed.charge (n + 1) (List.ofFn (fun k => (integerMatrixOfData X i k, integerMatrixOfData Y k j)))).bind
      costedIntegerDot

theorem costedIntegerMatrixMul_value {n : ℕ} (X Y : IntegerMatrixData n) :
    integerMatrixOfData (costedIntegerMatrixMul X Y).value = integerMatrixOfData X * integerMatrixOfData Y := by
  rw [costedIntegerMatrixMul, costedIntegerMatrixOfFn_value]
  ext i j
  simp [Costed.charge, integerListDot, Matrix.mul_apply, List.sum_ofFn]

theorem costedIntegerMatrixMul_data {n : ℕ} (X Y : IntegerMatrixData n) :
    (costedIntegerMatrixMul X Y).value = integerMatrixData (integerMatrixOfData X * integerMatrixOfData Y) := by
  rw [← integerMatrixData_ofData (costedIntegerMatrixMul X Y).value, costedIntegerMatrixMul_value]

def integerMatrixMulBudget (n L : ℕ) : ℕ :=
  integerMatrixTraversalBudget n (n + 1 + (n * integerDotStepBudget n L + 1))

theorem costedIntegerMatrixMul_steps_le {n : ℕ} (X Y : IntegerMatrixData n) (L : ℕ)
    (hX : ∀ i j, (integerMatrixOfData X i j).natAbs.size ≤ L)
    (hY : ∀ i j, (integerMatrixOfData Y i j).natAbs.size ≤ L) :
    (costedIntegerMatrixMul X Y).steps ≤ integerMatrixMulBudget n L := by
  apply costedIntegerMatrixOfFn_steps_le
  intro i j
  simp only [Costed.bind_steps, Costed.charge]
  apply Nat.add_le_add_left
  have h := costedIntegerDot_steps_le (List.ofFn (fun k => (integerMatrixOfData X i k, integerMatrixOfData Y k j))) L
    (by intro x hx; obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hx; exact ⟨hX i k, hY k j⟩)
  simpa using h

theorem costedIntegerMatrixMul_size_le {n : ℕ} (X Y : IntegerMatrixData n) (L : ℕ)
    (hX : ∀ i j, (integerMatrixOfData X i j).natAbs.size ≤ L)
    (hY : ∀ i j, (integerMatrixOfData Y i j).natAbs.size ≤ L) (i j : Fin n) :
    (integerMatrixOfData (costedIntegerMatrixMul X Y).value i j).natAbs.size ≤ n + 2 * L + 1 := by
  rw [costedIntegerMatrixMul_value]
  have h := integerListDot_size_le (List.ofFn (fun k => (integerMatrixOfData X i k, integerMatrixOfData Y k j))) L
    (by intro x hx; obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hx; exact ⟨hX i k, hY k j⟩)
  simpa [integerListDot, Matrix.mul_apply, List.sum_ofFn] using h

def costedIntSub (a b : ℤ) : Costed ℤ := ⟨a - b, integerOperandBits a b⟩

def costedIntegerMatrixSub {n : ℕ} (X Y : IntegerMatrixData n) : Costed (IntegerMatrixData n) :=
  costedIntegerMatrixOfFn fun i j => costedIntSub (integerMatrixOfData X i j) (integerMatrixOfData Y i j)

theorem costedIntegerMatrixSub_value {n : ℕ} (X Y : IntegerMatrixData n) :
    integerMatrixOfData (costedIntegerMatrixSub X Y).value = integerMatrixOfData X - integerMatrixOfData Y := by
  rw [costedIntegerMatrixSub, costedIntegerMatrixOfFn_value]
  rfl

theorem costedIntegerMatrixSub_data {n : ℕ} (X Y : IntegerMatrixData n) :
    (costedIntegerMatrixSub X Y).value = integerMatrixData (integerMatrixOfData X - integerMatrixOfData Y) := by
  rw [← integerMatrixData_ofData (costedIntegerMatrixSub X Y).value, costedIntegerMatrixSub_value]

theorem costedIntegerMatrixSub_steps_le {n : ℕ} (X Y : IntegerMatrixData n) (L : ℕ)
    (hX : ∀ i j, (integerMatrixOfData X i j).natAbs.size ≤ L)
    (hY : ∀ i j, (integerMatrixOfData Y i j).natAbs.size ≤ L) :
    (costedIntegerMatrixSub X Y).steps ≤ integerMatrixTraversalBudget n (2 * L + 1) := by
  apply costedIntegerMatrixOfFn_steps_le
  intro i j
  dsimp [costedIntSub, integerOperandBits]
  have hx := hX i j
  have hy := hY i j
  omega

end GeometricGaussianLHL

end IntegerMatrixCost

section RationalInputCost

/-!
## Costs of preparing integer numerators from stored rational matrices

The common denominator is computed once by a stored list product. Each
numerator then uses one exact natural division and one integer multiplication.
The sum of the input denominator bit lengths bounds every partial product.
-/

namespace GeometricGaussianLHL

def rationalMatrixEntries {n : ℕ} (D : RationalMatrixData n) : List ℚ :=
  (List.ofFn (fun i : Fin n => List.ofFn (fun j : Fin n => rationalMatrixOfData D i j))).flatten

theorem rationalMatrixEntries_length {n : ℕ} (D : RationalMatrixData n) :
    (rationalMatrixEntries D).length = n * n := by
  simp [rationalMatrixEntries, List.sum_ofFn]

theorem rationalMatrixEntries_bits {n : ℕ} (D : RationalMatrixData n) :
    ((rationalMatrixEntries D).map rationalMagnitudeBits).sum = rationalMatrixMagnitudeBits (rationalMatrixOfData D) := by
  simp [rationalMatrixEntries, List.map_flatten, List.sum_flatten, List.sum_ofFn,
    Function.comp_def, rationalMatrixMagnitudeBits]

theorem rationalMatrixEntries_den_product {n : ℕ} (D : RationalMatrixData n) :
    ((rationalMatrixEntries D).map Rat.den).prod = rationalMatrixCommonDenominator (rationalMatrixOfData D) := by
  simp [rationalMatrixEntries, List.map_flatten, List.prod_flatten, List.prod_ofFn,
    Function.comp_def, rationalMatrixCommonDenominator]

theorem nat_list_product_le_bits (xs : List ℕ) : xs.prod ≤ 2 ^ (xs.map Nat.size).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.prod_cons, List.map_cons, List.sum_cons, pow_add]
    exact Nat.mul_le_mul (Nat.lt_size_self x).le ih

theorem nat_list_product_size (xs : List ℕ) : xs.prod.size ≤ (xs.map Nat.size).sum + 1 := by
  apply Nat.size_le.mpr
  exact (nat_list_product_le_bits xs).trans_lt (Nat.pow_lt_pow_right (by omega) (by omega))

def costedNatProduct : List ℕ → Costed ℕ
  | [] => Costed.charge 1 1
  | x :: xs => (costedNatProduct xs).bind fun p =>
      (costedNatMul x p).bind fun z => Costed.charge 1 z

@[simp] theorem costedNatProduct_value (xs : List ℕ) : (costedNatProduct xs).value = xs.prod := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [costedNatProduct, Costed.bind_value, costedNatMul, Costed.charge, List.prod_cons, ih]

def natProductBudget (m S : ℕ) : ℕ := m * ((2 * S + 2) ^ 2 + 1) + 1

theorem costedNatProduct_steps_le (xs : List ℕ) (S : ℕ) (hS : (xs.map Nat.size).sum ≤ S) :
    (costedNatProduct xs).steps ≤ natProductBudget xs.length S := by
  induction xs with
  | nil => simp [costedNatProduct, Costed.charge, natProductBudget]
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons] at hS
    have hx : x.size ≤ S := by omega
    have ht : (xs.map Nat.size).sum ≤ S := by omega
    have hp := (nat_list_product_size xs).trans (Nat.add_le_add_right ht 1)
    have hm : (x.size + xs.prod.size + 1) ^ 2 ≤ (2 * S + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have hi := ih ht
    simp only [costedNatProduct, Costed.bind_steps, costedNatProduct_value, costedNatMul, Costed.charge]
    simp only [natProductBudget, List.length_cons] at *
    nlinarith

def costedRationalCommonDenominator {n : ℕ} (D : RationalMatrixData n) : Costed ℕ :=
  (Costed.charge (2 * n * n + 1) ((rationalMatrixEntries D).map Rat.den)).bind costedNatProduct

theorem costedRationalCommonDenominator_value {n : ℕ} (D : RationalMatrixData n) :
    (costedRationalCommonDenominator D).value = rationalMatrixCommonDenominator (rationalMatrixOfData D) := by
  rw [costedRationalCommonDenominator, Costed.bind_value]
  dsimp only [Costed.charge]
  rw [costedNatProduct_value, rationalMatrixEntries_den_product]

def rationalDenominatorBudget (n S : ℕ) : ℕ := 2 * n * n + 1 + natProductBudget (n * n) S

theorem costedRationalCommonDenominator_steps_le {n : ℕ} (D : RationalMatrixData n) :
    (costedRationalCommonDenominator D).steps ≤ rationalDenominatorBudget n (rationalMatrixMagnitudeBits (rationalMatrixOfData D)) := by
  have hS : (((rationalMatrixEntries D).map Rat.den).map Nat.size).sum ≤ rationalMatrixMagnitudeBits (rationalMatrixOfData D) := by
    rw [← rationalMatrixEntries_bits D, List.map_map]
    apply List.sum_le_sum
    intro x _
    dsimp [Function.comp_def, rationalMagnitudeBits]
    omega
  have h := costedNatProduct_steps_le ((rationalMatrixEntries D).map Rat.den) _ hS
  simpa only [costedRationalCommonDenominator, Costed.bind_steps, Costed.charge,
    List.length_map, rationalMatrixEntries_length, rationalDenominatorBudget] using Nat.add_le_add_left h (2 * n * n + 1)

def costedNatDiv (a b : ℕ) : Costed ℕ := ⟨a / b, (a.size + b.size + 1) ^ 2⟩

def costedRationalNumerators {n : ℕ} (a : ℕ) (D : RationalMatrixData n) : Costed (IntegerMatrixData n) :=
  costedIntegerMatrixOfFn fun i j =>
    let x := rationalMatrixOfData D i j
    (costedNatDiv a x.den).bind fun d =>
      (Costed.charge (d.size + 1) (d : ℤ)).bind (fun z => costedIntMul x.num z)

theorem costedRationalNumerators_data {n : ℕ} (a : ℕ) (D : RationalMatrixData n) :
    (costedRationalNumerators a D).value =
      integerMatrixData (fun i j => (rationalMatrixOfData D i j).num * (a / (rationalMatrixOfData D i j).den : ℕ)) := by
  rw [costedRationalNumerators, costedIntegerMatrixOfFn_data]
  rfl

def rationalNumeratorBudget (n L : ℕ) : ℕ := integerMatrixTraversalBudget n (2 * (2 * L + 1) ^ 2 + L + 1)

theorem costedRationalNumerators_steps_le {n : ℕ} (a L : ℕ) (D : RationalMatrixData n)
    (ha : a.size ≤ L) (hD : ∀ i j, rationalMagnitudeBits (rationalMatrixOfData D i j) ≤ L) :
    (costedRationalNumerators a D).steps ≤ rationalNumeratorBudget n L := by
  apply costedIntegerMatrixOfFn_steps_le
  intro i j
  have hx := hD i j
  have hd : (a / (rationalMatrixOfData D i j).den).size ≤ L := (Nat.size_le_size (Nat.div_le_self _ _)).trans ha
  have hdiv : (a.size + (rationalMatrixOfData D i j).den.size + 1) ^ 2 ≤ (2 * L + 1) ^ 2 :=
    Nat.pow_le_pow_left (by unfold rationalMagnitudeBits at hx; omega) 2
  have hmul : (integerOperandBits (rationalMatrixOfData D i j).num (a / (rationalMatrixOfData D i j).den : ℕ)) ^ 2 ≤ (2 * L + 1) ^ 2 := by
    apply Nat.pow_le_pow_left
    unfold integerOperandBits rationalMagnitudeBits at *
    simp only [Int.natAbs_natCast]
    omega
  change (a.size + (rationalMatrixOfData D i j).den.size + 1) ^ 2 +
    ((a / (rationalMatrixOfData D i j).den).size + 1 +
      (integerOperandBits (rationalMatrixOfData D i j).num (a / (rationalMatrixOfData D i j).den : ℕ)) ^ 2) ≤ _
  omega

def costedRationalIntegerInput {n : ℕ} (D : RationalMatrixData n) : Costed (ℕ × IntegerMatrixData n) :=
  (costedRationalCommonDenominator D).bind fun a =>
    (costedRationalNumerators a D).bind fun X => Costed.pure (a, X)

theorem costedRationalIntegerInput_value {n : ℕ} (D : RationalMatrixData n) :
    (costedRationalIntegerInput D).value =
      (rationalMatrixCommonDenominator (rationalMatrixOfData D), integerMatrixData (rationalMatrixCommonNumerators (rationalMatrixOfData D))) := by
  rw [costedRationalIntegerInput, Costed.bind_value, costedRationalCommonDenominator_value,
    Costed.bind_value, costedRationalNumerators_data]
  rfl

def rationalIntegerInputBudget (n S : ℕ) : ℕ := rationalDenominatorBudget n S + rationalNumeratorBudget n (S + 1)

theorem costedRationalIntegerInput_steps_le {n : ℕ} (D : RationalMatrixData n) :
    (costedRationalIntegerInput D).steps ≤ rationalIntegerInputBudget n (rationalMatrixMagnitudeBits (rationalMatrixOfData D)) := by
  have hd := costedRationalCommonDenominator_steps_le D
  have hn := costedRationalNumerators_steps_le (rationalMatrixCommonDenominator (rationalMatrixOfData D))
    (rationalMatrixMagnitudeBits (rationalMatrixOfData D) + 1) D
    (rationalMatrixCommonDenominator_size _) (fun i j => (rationalMatrix_entry_bits_le _ i j).trans (by omega))
  rw [costedRationalIntegerInput, Costed.bind_steps, costedRationalCommonDenominator_value,
    Costed.bind_steps]
  dsimp only [Costed.pure]
  unfold rationalIntegerInputBudget
  omega

end GeometricGaussianLHL

end RationalInputCost

section RationalSpectralConditioning

/-!
## Input-size lower bounds for rational positive definite matrices

Clearing denominators gives a positive integer determinant. Its lower bound
supplies an explicit dyadic spectral gap once the spectrum is bounded by one.
The exponent is polynomial in the dimension and the reduced rational input
magnitude; no externally supplied lower-eigenvalue bound is needed here.
-/

open scoped MatrixOrder Matrix.Norms.L2Operator

namespace GeometricGaussianLHL

theorem rationalMatrix_real_det_lower {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : (A.map (fun q : ℚ => (q : ℝ))).PosDef) :
    1 / (rationalMatrixCommonDenominator A : ℝ) ^ n ≤
      (A.map (fun q : ℚ => (q : ℝ))).det := by
  have hp : 0 < (rationalMatrixCommonDenominator A : ℝ) ^ n :=
    pow_pos (by exact_mod_cast rationalMatrixCommonDenominator_pos A) _
  have hpos := hA.det_pos
  rw [rationalMatrix_real_det_common_denominator] at hpos ⊢
  have hz : (0 : ℤ) < (rationalMatrixCommonNumerators A).det := by
    exact_mod_cast (div_pos_iff_of_pos_right hp).mp hpos
  have hz1 : (1 : ℝ) ≤ ((rationalMatrixCommonNumerators A).det : ℝ) := by
    exact_mod_cast (show (1 : ℤ) ≤ (rationalMatrixCommonNumerators A).det by omega)
  exact div_le_div_of_nonneg_right hz1 hp.le

theorem rationalMatrix_real_det_dyadic_lower {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : (A.map (fun q : ℚ => (q : ℝ))).PosDef) :
    1 / (2 : ℝ) ^ (n * rationalMatrixMagnitudeBits A) ≤
      (A.map (fun q : ℚ => (q : ℝ))).det := by
  have hp : 0 < (rationalMatrixCommonDenominator A : ℝ) ^ n :=
    pow_pos (by exact_mod_cast rationalMatrixCommonDenominator_pos A) _
  have hden : (rationalMatrixCommonDenominator A : ℝ) ^ n ≤
      (2 : ℝ) ^ (n * rationalMatrixMagnitudeBits A) := by
    calc
      _ ≤ ((2 : ℝ) ^ rationalMatrixMagnitudeBits A) ^ n :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast rationalMatrixCommonDenominator_le_pow A) _
      _ = _ := by rw [← pow_mul, Nat.mul_comm]
  exact (one_div_le_one_div_of_le hp hden).trans (rationalMatrix_real_det_lower A hA)

theorem normalizedMatrix_det_le_eigenvalue {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosSemidef)
    (hhi : ∀ i, hA.isHermitian.eigenvalues i ≤ 1) (i : Fin n) :
    A.det ≤ hA.isHermitian.eigenvalues i := by
  have hp : (∏ j ∈ Finset.univ.erase i, hA.isHermitian.eigenvalues j) ≤ 1 :=
    Finset.prod_le_one (fun j _ => hA.eigenvalues_nonneg j) (fun j _ => hhi j)
  calc
    A.det = (∏ j ∈ Finset.univ.erase i, hA.isHermitian.eigenvalues j) *
        hA.isHermitian.eigenvalues i := by
      rw [hA.isHermitian.det_eq_prod_eigenvalues]
      simpa using (Finset.prod_erase_mul Finset.univ hA.isHermitian.eigenvalues (Finset.mem_univ i)).symm
    _ ≤ 1 * hA.isHermitian.eigenvalues i :=
      mul_le_mul_of_nonneg_right hp (hA.eigenvalues_nonneg i)
    _ = _ := one_mul _

theorem rationalMatrix_normalized_eigenvalue_lower {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : (A.map (fun q : ℚ => (q : ℝ))).PosDef)
    (hhi : ∀ i, hA.isHermitian.eigenvalues i ≤ 1) (i : Fin n) :
    1 / (2 : ℝ) ^ (n * rationalMatrixMagnitudeBits A) ≤ hA.isHermitian.eigenvalues i :=
  (rationalMatrix_real_det_dyadic_lower A hA).trans
    (normalizedMatrix_det_le_eigenvalue _ hA.posSemidef hhi i)

end GeometricGaussianLHL

end RationalSpectralConditioning

section RationalMatrixNormalization

/-!
## Explicit normalization and conditioning from rational input size

A dyadic scalar computed from the dimension and reduced rational magnitude
uses an even exponent to normalize every positive definite rational input,
so square roots can later be rescaled by a rational power of two. Both spectral endpoints
are then proved using an explicit polynomial exponent in those input sizes.
This file proves the numerical preprocessing specification; arithmetic cost analysis of preprocessing remains a separate obligation.
-/

open scoped MatrixOrder Matrix.Norms.L2Operator

namespace GeometricGaussianLHL

def rationalMatrixScaleExponent {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) : ℕ :=
  n + 2 * rationalMatrixMagnitudeBits A

def rationalMatrixNormalizationExponent {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) : ℕ :=
  2 * rationalMatrixScaleExponent A

def normalizedRationalMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) :
    Matrix (Fin n) (Fin n) ℚ :=
  (1 / (2 : ℚ) ^ rationalMatrixNormalizationExponent A) • A

def rationalMatrixConditionExponent {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) : ℕ :=
  n * (rationalMatrixMagnitudeBits A + rationalMatrixNormalizationExponent A)

theorem rationalMatrix_real_norm_le_input_pow {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    ‖A.map (fun q : ℚ => (q : ℝ))‖ ≤ (2 : ℝ) ^ rationalMatrixNormalizationExponent A := by
  have h := euclideanMatrix_opNorm_le_entries (A.map (fun q : ℚ => (q : ℝ)))
    (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (2 * rationalMatrixMagnitudeBits A))
    (rationalMatrix_real_entry_le_input_pow A)
  change ‖A.map (fun q : ℚ => (q : ℝ))‖ ≤ _ at h
  have hn : (n : ℝ) ≤ (2 : ℝ) ^ n := by exact_mod_cast (Nat.lt_two_pow_self (n := n)).le
  calc
    _ ≤ (n : ℝ) * (2 : ℝ) ^ (2 * rationalMatrixMagnitudeBits A) := h
    _ ≤ (2 : ℝ) ^ n * (2 : ℝ) ^ (2 * rationalMatrixMagnitudeBits A) :=
      mul_le_mul_of_nonneg_right hn (by positivity)
    _ = (2 : ℝ) ^ (n + 2 * rationalMatrixMagnitudeBits A) := by rw [pow_add]
    _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by
      unfold rationalMatrixNormalizationExponent rationalMatrixScaleExponent
      omega)

theorem normalizedRationalMatrix_real_formula {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    (normalizedRationalMatrix A).map (fun q : ℚ => (q : ℝ)) =
      (1 / (2 : ℝ) ^ rationalMatrixNormalizationExponent A) •
        A.map (fun q : ℚ => (q : ℝ)) := by
  ext i j
  simp [normalizedRationalMatrix, Matrix.map_apply, Matrix.smul_apply]

theorem normalizedRationalMatrix_posDef {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : (A.map (fun q : ℚ => (q : ℝ))).PosDef) :
    ((normalizedRationalMatrix A).map (fun q : ℚ => (q : ℝ))).PosDef := by
  rw [normalizedRationalMatrix_real_formula]
  exact hA.smul (by positivity)

theorem normalizedRationalMatrix_norm_le_one {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    ‖(normalizedRationalMatrix A).map (fun q : ℚ => (q : ℝ))‖ ≤ 1 := by
  rw [normalizedRationalMatrix_real_formula, norm_smul,
    Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 : ℝ) ^ rationalMatrixNormalizationExponent A)]
  calc
    _ ≤ (1 / (2 : ℝ) ^ rationalMatrixNormalizationExponent A) *
        (2 : ℝ) ^ rationalMatrixNormalizationExponent A :=
      mul_le_mul_of_nonneg_left (rationalMatrix_real_norm_le_input_pow A) (by positivity)
    _ = 1 := by field_simp

theorem normalizedRationalMatrix_det_lower {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : (A.map (fun q : ℚ => (q : ℝ))).PosDef) :
    1 / (2 : ℝ) ^ rationalMatrixConditionExponent A ≤
      ((normalizedRationalMatrix A).map (fun q : ℚ => (q : ℝ))).det := by
  rw [normalizedRationalMatrix_real_formula, Matrix.det_smul, Fintype.card_fin]
  have he : 1 / (2 : ℝ) ^ rationalMatrixConditionExponent A =
      (1 / (2 : ℝ) ^ rationalMatrixNormalizationExponent A) ^ n *
        (1 / (2 : ℝ) ^ (n * rationalMatrixMagnitudeBits A)) := by
    simp only [rationalMatrixConditionExponent, one_div, inv_pow, ← mul_inv, ← pow_mul, ← pow_add]
    congr 2
    ring
  rw [he]
  exact mul_le_mul_of_nonneg_left (rationalMatrix_real_det_dyadic_lower A hA) (by positivity)

theorem normalizedRationalMatrix_spectral_bounds {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : (A.map (fun q : ℚ => (q : ℝ))).PosDef) :
    let hN := normalizedRationalMatrix_posDef A hA
    (∀ i, 1 / (2 : ℝ) ^ rationalMatrixConditionExponent A ≤ hN.isHermitian.eigenvalues i) ∧
      (∀ i, hN.isHermitian.eigenvalues i ≤ 1) := by
  let hN := normalizedRationalMatrix_posDef A hA
  have hhi (i : Fin n) : hN.isHermitian.eigenvalues i ≤ 1 := by
    have : Nonempty (Fin n) := ⟨i⟩
    have hs := spectrum.norm_le_norm_of_mem (hN.isHermitian.eigenvalues_mem_spectrum_real i)
    exact (Real.le_norm_self _).trans (hs.trans (normalizedRationalMatrix_norm_le_one A))
  exact ⟨fun i => (normalizedRationalMatrix_det_lower A hA).trans
    (normalizedMatrix_det_le_eigenvalue _ hN.posSemidef hhi i), hhi⟩

theorem rationalMatrixConditionExponent_eq {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    rationalMatrixConditionExponent A = 2 * n * n + 5 * n * rationalMatrixMagnitudeBits A := by
  unfold rationalMatrixConditionExponent rationalMatrixNormalizationExponent rationalMatrixScaleExponent
  ring

end GeometricGaussianLHL

end RationalMatrixNormalization

section RepresentedMatrixNormalization

/-!
## Normalization from an unreduced integer/denominator encoding

Only a positive denominator and upper bounds on the encoded integer sizes
are needed. The even normalization exponent permits rational square-root
rescaling. Multiplying the denominator implements normalization without
reducing any fraction or changing the numerator matrix.
-/

open scoped MatrixOrder Matrix.Norms.L2Operator

namespace GeometricGaussianLHL

theorem integerMatrixQuotient_real_formula {n : ℕ} (a : ℕ)
    (X : Matrix (Fin n) (Fin n) ℤ) :
    (integerMatrixQuotient a X).map (fun q : ℚ => (q : ℝ)) =
      (a : ℝ)⁻¹ • X.map (fun z : ℤ => (z : ℝ)) := by
  ext i j
  simp [integerMatrixQuotient, integerMatrixCast, Matrix.map_apply, Matrix.smul_apply]

theorem integerMatrixQuotient_real_det {n : ℕ} (a : ℕ)
    (X : Matrix (Fin n) (Fin n) ℤ) :
    ((integerMatrixQuotient a X).map (fun q : ℚ => (q : ℝ))).det = (X.det : ℝ) / (a : ℝ) ^ n := by
  rw [integerMatrixQuotient_real_formula, Matrix.det_smul, ← Int.cast_det]
  simp only [Fintype.card_fin, inv_pow, div_eq_mul_inv, mul_comm]

theorem integerMatrixQuotient_real_det_lower {n : ℕ} (a : ℕ)
    (X : Matrix (Fin n) (Fin n) ℤ) (ha : 0 < a)
    (hX : ((integerMatrixQuotient a X).map (fun q : ℚ => (q : ℝ))).PosDef) :
    1 / (a : ℝ) ^ n ≤ ((integerMatrixQuotient a X).map (fun q : ℚ => (q : ℝ))).det := by
  have hp : 0 < (a : ℝ) ^ n := pow_pos (by exact_mod_cast ha) _
  have hpos := hX.det_pos
  rw [integerMatrixQuotient_real_det] at hpos ⊢
  have hz : (0 : ℤ) < X.det := by exact_mod_cast (div_pos_iff_of_pos_right hp).mp hpos
  have hz1 : (1 : ℝ) ≤ (X.det : ℝ) := by exact_mod_cast (show (1 : ℤ) ≤ X.det by omega)
  exact div_le_div_of_nonneg_right hz1 hp.le

theorem integerMatrixQuotient_real_det_dyadic_lower {n : ℕ} (a M : ℕ)
    (X : Matrix (Fin n) (Fin n) ℤ) (ha : 0 < a) (hM : a ≤ 2 ^ M)
    (hX : ((integerMatrixQuotient a X).map (fun q : ℚ => (q : ℝ))).PosDef) :
    1 / (2 : ℝ) ^ (n * M) ≤ ((integerMatrixQuotient a X).map (fun q : ℚ => (q : ℝ))).det := by
  have hp : 0 < (a : ℝ) ^ n := pow_pos (by exact_mod_cast ha) _
  have hden : (a : ℝ) ^ n ≤ (2 : ℝ) ^ (n * M) := by
    calc
      _ ≤ ((2 : ℝ) ^ M) ^ n := pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hM) _
      _ = _ := by rw [← pow_mul, Nat.mul_comm]
  exact (one_div_le_one_div_of_le hp hden).trans (integerMatrixQuotient_real_det_lower a X ha hX)

def representedMatrixScaleExponent (n M : ℕ) : ℕ := n + 2 * M + 1

def representedMatrixNormalizationExponent (n M : ℕ) : ℕ := 2 * representedMatrixScaleExponent n M

def representedMatrixConditionExponent (n M : ℕ) : ℕ := n * (M + representedMatrixNormalizationExponent n M)

def normalizedRepresentedMatrix {n : ℕ} (a M : ℕ) (X : Matrix (Fin n) (Fin n) ℤ) :
    Matrix (Fin n) (Fin n) ℚ := integerMatrixQuotient (a * 2 ^ representedMatrixNormalizationExponent n M) X

theorem integerMatrixQuotient_real_entry_le_encoded {n : ℕ} (a M : ℕ)
    (X : Matrix (Fin n) (Fin n) ℤ) (ha : 0 < a)
    (hU : ∀ i j, (X i j).natAbs.size ≤ 2 * M + 1) (i j : Fin n) :
    |((integerMatrixQuotient a X i j : ℚ) : ℝ)| ≤ (2 : ℝ) ^ (2 * M + 1) := by
  have hden : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hnum : |((X i j : ℤ) : ℝ)| ≤ (2 : ℝ) ^ (2 * M + 1) := by
    have h : ((X i j).natAbs : ℝ) ≤ (2 : ℝ) ^ (2 * M + 1) := by
      exact_mod_cast (Nat.size_le.mp (hU i j)).le
    simpa only [Nat.cast_natAbs, Int.cast_abs] using h
  rw [integerMatrixQuotient_apply]
  simp only [Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast, abs_div,
    abs_of_nonneg (show (0 : ℝ) ≤ (a : ℝ) from Nat.cast_nonneg a)]
  exact (div_le_div_of_nonneg_right hnum (Nat.cast_nonneg a)).trans (div_le_self (by positivity) hden)

theorem integerMatrixQuotient_real_norm_le_encoded {n : ℕ} (a M : ℕ)
    (X : Matrix (Fin n) (Fin n) ℤ) (ha : 0 < a)
    (hU : ∀ i j, (X i j).natAbs.size ≤ 2 * M + 1) :
    ‖(integerMatrixQuotient a X).map (fun q : ℚ => (q : ℝ))‖ ≤
      (2 : ℝ) ^ representedMatrixNormalizationExponent n M := by
  have h := euclideanMatrix_opNorm_le_entries ((integerMatrixQuotient a X).map (fun q : ℚ => (q : ℝ)))
    (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (2 * M + 1))
    (integerMatrixQuotient_real_entry_le_encoded a M X ha hU)
  have hn : (n : ℝ) ≤ (2 : ℝ) ^ n := by exact_mod_cast (Nat.lt_two_pow_self (n := n)).le
  calc
    _ ≤ (n : ℝ) * (2 : ℝ) ^ (2 * M + 1) := h
    _ ≤ (2 : ℝ) ^ n * (2 : ℝ) ^ (2 * M + 1) := mul_le_mul_of_nonneg_right hn (by positivity)
    _ = (2 : ℝ) ^ (n + (2 * M + 1)) := (pow_add _ n (2 * M + 1)).symm
    _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by
      dsimp [representedMatrixNormalizationExponent, representedMatrixScaleExponent]
      omega)

theorem normalizedRepresentedMatrix_rat_formula {n : ℕ} (a M : ℕ)
    (X : Matrix (Fin n) (Fin n) ℤ) :
    normalizedRepresentedMatrix a M X =
      (1 / (2 : ℚ) ^ representedMatrixNormalizationExponent n M) • integerMatrixQuotient a X := by
  simp [normalizedRepresentedMatrix, integerMatrixQuotient, Nat.cast_mul, smul_smul, mul_comm]

theorem normalizedRepresentedMatrix_real_formula {n : ℕ} (a M : ℕ)
    (X : Matrix (Fin n) (Fin n) ℤ) :
    (normalizedRepresentedMatrix a M X).map (fun q : ℚ => (q : ℝ)) =
      (1 / (2 : ℝ) ^ representedMatrixNormalizationExponent n M) •
        (integerMatrixQuotient a X).map (fun q : ℚ => (q : ℝ)) := by
  rw [normalizedRepresentedMatrix_rat_formula]
  ext i j
  simp [Matrix.map_apply, Matrix.smul_apply]

theorem normalizedRepresentedMatrix_posDef {n : ℕ} (a M : ℕ)
    (X : Matrix (Fin n) (Fin n) ℤ)
    (hX : ((integerMatrixQuotient a X).map (fun q : ℚ => (q : ℝ))).PosDef) :
    ((normalizedRepresentedMatrix a M X).map (fun q : ℚ => (q : ℝ))).PosDef := by
  rw [normalizedRepresentedMatrix_real_formula]
  exact hX.smul (by positivity)

theorem normalizedRepresentedMatrix_norm_le_one {n : ℕ} (a M : ℕ)
    (X : Matrix (Fin n) (Fin n) ℤ) (ha : 0 < a)
    (hU : ∀ i j, (X i j).natAbs.size ≤ 2 * M + 1) :
    ‖(normalizedRepresentedMatrix a M X).map (fun q : ℚ => (q : ℝ))‖ ≤ 1 := by
  rw [normalizedRepresentedMatrix_real_formula, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 : ℝ) ^ representedMatrixNormalizationExponent n M)]
  calc
    _ ≤ (1 / (2 : ℝ) ^ representedMatrixNormalizationExponent n M) *
        (2 : ℝ) ^ representedMatrixNormalizationExponent n M :=
      mul_le_mul_of_nonneg_left (integerMatrixQuotient_real_norm_le_encoded a M X ha hU) (by positivity)
    _ = 1 := by field_simp

theorem normalizedRepresentedMatrix_denominator_bound (n a M : ℕ) (hM : a ≤ 2 ^ M) :
    a * 2 ^ representedMatrixNormalizationExponent n M ≤
      2 ^ (M + representedMatrixNormalizationExponent n M) := by
  rw [pow_add]
  exact Nat.mul_le_mul_right _ hM

theorem normalizedRepresentedMatrix_spectral_bounds {n : ℕ} (a M : ℕ)
    (X : Matrix (Fin n) (Fin n) ℤ) (ha : 0 < a) (hM : a ≤ 2 ^ M)
    (hU : ∀ i j, (X i j).natAbs.size ≤ 2 * M + 1)
    (hX : ((integerMatrixQuotient a X).map (fun q : ℚ => (q : ℝ))).PosDef) :
    let hN := normalizedRepresentedMatrix_posDef a M X hX
    (∀ i, 1 / (2 : ℝ) ^ representedMatrixConditionExponent n M ≤ hN.isHermitian.eigenvalues i) ∧
      (∀ i, hN.isHermitian.eigenvalues i ≤ 1) := by
  let hN := normalizedRepresentedMatrix_posDef a M X hX
  have hhi (i : Fin n) : hN.isHermitian.eigenvalues i ≤ 1 := by
    have : Nonempty (Fin n) := ⟨i⟩
    have hs := spectrum.norm_le_norm_of_mem (hN.isHermitian.eigenvalues_mem_spectrum_real i)
    exact (Real.le_norm_self _).trans (hs.trans (normalizedRepresentedMatrix_norm_le_one a M X ha hU))
  have hd := integerMatrixQuotient_real_det_dyadic_lower
    (a * 2 ^ representedMatrixNormalizationExponent n M) (M + representedMatrixNormalizationExponent n M)
    X (by positivity) (normalizedRepresentedMatrix_denominator_bound n a M hM) hN
  exact ⟨fun i => hd.trans (normalizedMatrix_det_le_eigenvalue _ hN.posSemidef hhi i), hhi⟩

theorem normalizedRepresentedMatrix_sqrt_rescale {n : ℕ} (a M : ℕ)
    (X : Matrix (Fin n) (Fin n) ℤ)
    (hX : ((integerMatrixQuotient a X).map (fun q : ℚ => (q : ℝ))).PosDef) :
    (2 : ℝ) ^ representedMatrixScaleExponent n M •
        CFC.sqrt ((normalizedRepresentedMatrix a M X).map (fun q : ℚ => (q : ℝ))) =
      CFC.sqrt ((integerMatrixQuotient a X).map (fun q : ℚ => (q : ℝ))) := by
  have hN := normalizedRepresentedMatrix_posDef a M X hX
  apply Eq.symm
  apply CFC.sqrt_unique ?_ (smul_nonneg (by positivity) (CFC.sqrt_nonneg _))
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, CFC.sqrt_mul_sqrt_self _ hN.posSemidef.nonneg,
    normalizedRepresentedMatrix_real_formula, smul_smul]
  have hs : (2 : ℝ) ^ representedMatrixScaleExponent n M *
      (2 : ℝ) ^ representedMatrixScaleExponent n M *
        (1 / (2 : ℝ) ^ representedMatrixNormalizationExponent n M) = 1 := by
    rw [representedMatrixNormalizationExponent, two_mul, pow_add]
    field_simp
  rw [hs, one_smul]

theorem normalizedRepresentedMatrix_inverse_rescale {n : ℕ} (a M : ℕ)
    (X : Matrix (Fin n) (Fin n) ℤ)
    (hX : ((integerMatrixQuotient a X).map (fun q : ℚ => (q : ℝ))).PosDef) :
    (1 / (2 : ℝ) ^ representedMatrixNormalizationExponent n M) •
        ((normalizedRepresentedMatrix a M X).map (fun q : ℚ => (q : ℝ)))⁻¹ =
      ((integerMatrixQuotient a X).map (fun q : ℚ => (q : ℝ)))⁻¹ := by
  have hN := normalizedRepresentedMatrix_posDef a M X hX
  apply Eq.symm
  apply Matrix.inv_eq_right_inv
  rw [Matrix.mul_smul, ← Matrix.smul_mul, ← normalizedRepresentedMatrix_real_formula]
  exact Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hN.det_pos.ne')

end GeometricGaussianLHL

end RepresentedMatrixNormalization

section RationalNormalizationCost

/-!
## Computing normalization from the finite rational input

The input scan measures reduced numerator and denominator bit lengths. A
charged sum and five arithmetic operations compute the scale and conditioning
exponents. Normalization changes the single integer denominator, retaining
the stored numerators. No spectral estimates are supplied by the caller.
-/

namespace GeometricGaussianLHL

def costedNatSum : List ℕ → Costed ℕ
  | [] => Costed.charge 1 0
  | x :: xs => (costedNatSum xs).bind fun s =>
      (costedNatAdd x s).bind fun z => Costed.charge 1 z

@[simp] theorem costedNatSum_value (xs : List ℕ) : (costedNatSum xs).value = xs.sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [costedNatSum, Costed.bind_value, costedNatAdd, Costed.charge, List.sum_cons, ih]

def natSumBudget (m S : ℕ) : ℕ := m * (2 * S + 2) + 1

theorem costedNatSum_steps_le (xs : List ℕ) (S : ℕ) (hS : xs.sum ≤ S) :
    (costedNatSum xs).steps ≤ natSumBudget xs.length S := by
  induction xs with
  | nil => simp [costedNatSum, Costed.charge, natSumBudget]
  | cons x xs ih =>
    simp only [List.sum_cons] at hS
    have hx : x.size ≤ S := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega)
    have ht : xs.sum ≤ S := by omega
    have hs : xs.sum.size ≤ S := (Nat.size_le.mpr Nat.lt_two_pow_self).trans ht
    have hi := ih ht
    simp only [costedNatSum, Costed.bind_steps, costedNatSum_value, costedNatAdd, Costed.charge]
    simp only [natSumBudget, List.length_cons] at *
    nlinarith

/-- Linear scanning includes measuring the reduced integer fields and constructing their bit-count list. -/
def costedRationalMagnitude {n : ℕ} (D : RationalMatrixData n) : Costed ℕ :=
  (Costed.charge (4 * (encodeRationalMatrixData D).length + 1)
    ((rationalMatrixEntries D).map rationalMagnitudeBits)).bind costedNatSum

theorem costedRationalMagnitude_value {n : ℕ} (D : RationalMatrixData n) :
    (costedRationalMagnitude D).value = rationalMatrixMagnitudeBits (rationalMatrixOfData D) := by
  rw [costedRationalMagnitude, Costed.bind_value]
  dsimp only [Costed.charge]
  rw [costedNatSum_value, rationalMatrixEntries_bits]

def rationalMagnitudeBudget (n S : ℕ) : ℕ := 4 * (2 * n + 1 + 2 * S + n * n) + 1 + natSumBudget (n * n) S

theorem costedRationalMagnitude_steps_le {n : ℕ} (D : RationalMatrixData n) :
    (costedRationalMagnitude D).steps ≤ rationalMagnitudeBudget n (rationalMatrixMagnitudeBits (rationalMatrixOfData D)) := by
  have h := costedNatSum_steps_le ((rationalMatrixEntries D).map rationalMagnitudeBits) _ (rationalMatrixEntries_bits D).le
  simp only [List.length_map, rationalMatrixEntries_length] at h
  have hn : n.size ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self
  rw [costedRationalMagnitude, Costed.bind_steps]
  dsimp only [Costed.charge]
  rw [encodeRationalMatrixData_length]
  unfold rationalMagnitudeBudget
  omega

structure RationalNormalizationSchedule where
  scaleExponent : ℕ
  normalizationExponent : ℕ
  conditionExponent : ℕ

def rationalNormalizationSchedule (n S : ℕ) : RationalNormalizationSchedule :=
  ⟨n + 2 * S, 2 * (n + 2 * S), n * (S + 2 * (n + 2 * S))⟩

def costedRationalNormalizationSchedule (n S : ℕ) : Costed RationalNormalizationSchedule :=
  let twiceS := costedNatMul 2 S
  let scale := costedNatAdd n twiceS.value
  let exponent := costedNatMul 2 scale.value
  let sum := costedNatAdd S exponent.value
  let condition := costedNatMul n sum.value
  ⟨⟨scale.value, exponent.value, condition.value⟩,
    twiceS.steps + scale.steps + exponent.steps + sum.steps + condition.steps⟩

theorem costedRationalNormalizationSchedule_value (n S : ℕ) :
    (costedRationalNormalizationSchedule n S).value = rationalNormalizationSchedule n S := rfl

def rationalNormalizationScheduleBudget (n S : ℕ) : ℕ := 5 * (10 * (n + S + 1) + 1) ^ 2

theorem costedRationalNormalizationSchedule_steps_le (n S : ℕ) :
    (costedRationalNormalizationSchedule n S).steps ≤ rationalNormalizationScheduleBudget n S := by
  let H := 5 * (n + S + 1)
  have h₁ := costedNatMul_steps_le 2 S H (by dsimp [H]; omega) (by dsimp [H]; omega)
  have h₂ := costedNatAdd_steps_le n (2 * S) H (by dsimp [H]; omega) (by dsimp [H]; omega)
  have h₃ := costedNatMul_steps_le 2 (n + 2 * S) H (by dsimp [H]; omega) (by dsimp [H]; omega)
  have h₄ := costedNatAdd_steps_le S (2 * (n + 2 * S)) H (by dsimp [H]; omega) (by dsimp [H]; omega)
  have h₅ := costedNatMul_steps_le n (S + 2 * (n + 2 * S)) H (by dsimp [H]; omega) (by dsimp [H]; omega)
  dsimp only [costedRationalNormalizationSchedule, costedNatAdd, costedNatMul] at *
  have he : 2 * H + 1 = 10 * (n + S + 1) + 1 := by dsimp [H]; ring
  rw [he] at h₁ h₂ h₃ h₄ h₅
  unfold rationalNormalizationScheduleBudget
  omega

def costedNormalizeIntegerDenominator {n : ℕ} (E : ℕ) (I : ℕ × IntegerMatrixData n) : Costed (ℕ × IntegerMatrixData n) :=
  (Costed.charge (E + 1) (2 ^ E : ℕ)).bind fun d =>
    (costedNatMul I.1 d).bind fun a => Costed.pure (a, I.2)

theorem costedNormalizeIntegerDenominator_value {n : ℕ} (E : ℕ) (I : ℕ × IntegerMatrixData n) :
    (costedNormalizeIntegerDenominator E I).value = (I.1 * 2 ^ E, I.2) := rfl

def normalizeIntegerDenominatorBudget (L E : ℕ) : ℕ := E + 1 + (L + E + 2) ^ 2

theorem costedNormalizeIntegerDenominator_steps_le {n : ℕ} (E L : ℕ) (I : ℕ × IntegerMatrixData n)
    (hI : I.1.size ≤ L) :
    (costedNormalizeIntegerDenominator E I).steps ≤ normalizeIntegerDenominatorBudget L E := by
  have hp : (2 ^ E : ℕ).size = E + 1 := by simp [Nat.size_pow]
  change E + 1 + ((I.1.size + (2 ^ E : ℕ).size + 1) ^ 2 + 0) ≤ _
  unfold normalizeIntegerDenominatorBudget
  rw [hp, Nat.add_zero]
  exact Nat.add_le_add_left (Nat.pow_le_pow_left (by omega) 2) _

structure RationalNormalizedInput (n : ℕ) where
  scaleExponent : ℕ
  conditionExponent : ℕ
  denominator : ℕ
  numerators : IntegerMatrixData n

def rationalNormalizedInput {n : ℕ} (D : RationalMatrixData n) : RationalNormalizedInput n :=
  let A := rationalMatrixOfData D
  ⟨rationalMatrixScaleExponent A, rationalMatrixConditionExponent A,
    rationalMatrixCommonDenominator A * 2 ^ rationalMatrixNormalizationExponent A,
    integerMatrixData (rationalMatrixCommonNumerators A)⟩

def costedRationalNormalization {n : ℕ} (D : RationalMatrixData n) : Costed (RationalNormalizedInput n) :=
  (costedRationalMagnitude D).bind fun S =>
    (costedRationalNormalizationSchedule n S).bind fun P =>
      (costedRationalIntegerInput D).bind fun I =>
        (costedNormalizeIntegerDenominator P.normalizationExponent I).bind fun J =>
          Costed.pure ⟨P.scaleExponent, P.conditionExponent, J.1, J.2⟩

theorem costedRationalNormalization_value {n : ℕ} (D : RationalMatrixData n) :
    (costedRationalNormalization D).value = rationalNormalizedInput D := by
  rw [costedRationalNormalization, Costed.bind_value, costedRationalMagnitude_value,
    Costed.bind_value, costedRationalNormalizationSchedule_value,
    Costed.bind_value, costedRationalIntegerInput_value,
    Costed.bind_value, costedNormalizeIntegerDenominator_value]
  rfl

def rationalNormalizationBudget (n S : ℕ) : ℕ :=
  rationalMagnitudeBudget n S + rationalNormalizationScheduleBudget n S + rationalIntegerInputBudget n S +
    normalizeIntegerDenominatorBudget (S + 1) (2 * (n + 2 * S))

theorem costedRationalNormalization_steps_le {n : ℕ} (D : RationalMatrixData n) :
    (costedRationalNormalization D).steps ≤ rationalNormalizationBudget n (rationalMatrixMagnitudeBits (rationalMatrixOfData D)) := by
  let A := rationalMatrixOfData D
  let S := rationalMatrixMagnitudeBits A
  have hm := costedRationalMagnitude_steps_le D
  have hs := costedRationalNormalizationSchedule_steps_le n S
  have hi := costedRationalIntegerInput_steps_le D
  have hd := costedNormalizeIntegerDenominator_steps_le (2 * (n + 2 * S)) (S + 1)
    (rationalMatrixCommonDenominator A, integerMatrixData (rationalMatrixCommonNumerators A))
    (rationalMatrixCommonDenominator_size A)
  rw [costedRationalNormalization, Costed.bind_steps, costedRationalMagnitude_value,
    Costed.bind_steps, costedRationalNormalizationSchedule_value,
    Costed.bind_steps, costedRationalIntegerInput_value, Costed.bind_steps]
  dsimp only [Costed.pure, rationalNormalizationSchedule]
  change _ ≤ rationalNormalizationBudget n S
  unfold rationalNormalizationBudget
  dsimp only [S, A] at hm hs hi hd ⊢
  omega

theorem rationalNormalizedInput_reconstruct {n : ℕ} (D : RationalMatrixData n) :
    integerMatrixQuotient (rationalNormalizedInput D).denominator
      (integerMatrixOfData (rationalNormalizedInput D).numerators) = normalizedRationalMatrix (rationalMatrixOfData D) := by
  let A := rationalMatrixOfData D
  change integerMatrixQuotient (rationalMatrixCommonDenominator A * 2 ^ rationalMatrixNormalizationExponent A)
    (integerMatrixOfData (integerMatrixData (rationalMatrixCommonNumerators A))) = _
  rw [integerMatrixOfData_data]
  calc
    _ = (1 / (2 : ℚ) ^ rationalMatrixNormalizationExponent A) •
        integerMatrixQuotient (rationalMatrixCommonDenominator A) (rationalMatrixCommonNumerators A) := by
      ext i j
      simp [integerMatrixQuotient_apply, Matrix.smul_apply, div_eq_mul_inv, mul_comm, mul_assoc]
    _ = _ := by rw [rationalMatrix_common_reconstruct]; rfl

theorem rationalNormalizedInput_denominator_pos {n : ℕ} (D : RationalMatrixData n) :
    0 < (rationalNormalizedInput D).denominator :=
  Nat.mul_pos (rationalMatrixCommonDenominator_pos _) (by positivity)

theorem rationalNormalizedInput_sizes {n : ℕ} (D : RationalMatrixData n) :
    let S := rationalMatrixMagnitudeBits (rationalMatrixOfData D)
    let U := 2 * S + rationalMatrixNormalizationExponent (rationalMatrixOfData D) + 3
    (rationalNormalizedInput D).denominator.size ≤ U ∧
      ∀ i j, (integerMatrixOfData (rationalNormalizedInput D).numerators i j).natAbs.size ≤ U := by
  let A := rationalMatrixOfData D
  let S := rationalMatrixMagnitudeBits A
  let E := rationalMatrixNormalizationExponent A
  have ha := rationalMatrixCommonDenominator_size A
  have he : (2 ^ E : ℕ).size ≤ E + 1 := by simp [Nat.size_pow]
  have hprod := integer_mul_size_le (rationalMatrixCommonDenominator A : ℤ) (2 ^ E : ℕ) (S + 1) (E + 1) ha he
  simp only [← Nat.cast_mul, Int.natAbs_natCast] at hprod
  change _ ≤ 2 * S + E + 3 ∧ ∀ i j, _ ≤ 2 * S + E + 3
  constructor
  · exact hprod.trans (by omega)
  · intro i j
    change (integerMatrixOfData (integerMatrixData (rationalMatrixCommonNumerators A)) i j).natAbs.size ≤ _
    rw [integerMatrixOfData_data]
    exact (rationalMatrixCommonNumerators_size A i j).trans (by change 2 * S + 1 ≤ _; omega)

end GeometricGaussianLHL

end RationalNormalizationCost

section IntegerOutputCost

/-!
## Costs of integer output rounding and rational serialization

The square-root and inverse algorithms share a stored matrix product followed
by scalar multiplication and integer division. Rational conversion charges
normalization at the actual operand sizes, then charges the encoded output
length. These operations extend the declared arithmetic cost semantics.
-/

namespace GeometricGaussianLHL

def costedIntegerScaleDivide {n : ℕ} (s v : ℤ) (X : IntegerMatrixData n) : Costed (IntegerMatrixData n) :=
  costedIntegerMatrixOfFn fun i j =>
    (costedIntMul (integerMatrixOfData X i j) s).bind (fun z => costedIntDiv z v)

theorem costedIntegerScaleDivide_data {n : ℕ} (s v : ℤ) (X : IntegerMatrixData n) :
    (costedIntegerScaleDivide s v X).value =
      integerMatrixData ((integerMatrixOfData X).map (fun z => z * s / v)) := by
  rw [costedIntegerScaleDivide, costedIntegerMatrixOfFn_data]
  rfl

def integerScaleDivideBudget (n L : ℕ) : ℕ :=
  integerMatrixTraversalBudget n ((2 * L + 1) ^ 2 + (3 * L + 2) ^ 2)

theorem costedIntegerScaleDivide_steps_le {n : ℕ} (s v : ℤ) (X : IntegerMatrixData n) (L : ℕ)
    (hs : s.natAbs.size ≤ L) (hv : v.natAbs.size ≤ L)
    (hX : ∀ i j, (integerMatrixOfData X i j).natAbs.size ≤ L) :
    (costedIntegerScaleDivide s v X).steps ≤ integerScaleDivideBudget n L := by
  apply costedIntegerMatrixOfFn_steps_le
  intro i j
  have hx := hX i j
  have hp := integer_mul_size_le (integerMatrixOfData X i j) s L L hx hs
  have h₁ : (integerOperandBits (integerMatrixOfData X i j) s) ^ 2 ≤ (2 * L + 1) ^ 2 :=
    Nat.pow_le_pow_left (by unfold integerOperandBits; omega) 2
  have h₂ : (integerOperandBits (integerMatrixOfData X i j * s) v) ^ 2 ≤ (3 * L + 2) ^ 2 :=
    Nat.pow_le_pow_left (by unfold integerOperandBits; omega) 2
  exact Nat.add_le_add h₁ h₂

def costedIntegerProductRound {n : ℕ} (r : ℕ) (u v : ℤ) (X Y : IntegerMatrixData n) : Costed (IntegerMatrixData n) :=
  (Costed.charge (r + 1) (2 ^ r : ℤ)).bind fun s =>
    (costedIntMul u v).bind fun d =>
      (costedIntegerMatrixMul X Y).bind (costedIntegerScaleDivide s d)

theorem costedIntegerProductRound_data {n : ℕ} (r : ℕ) (u v : ℤ) (X Y : IntegerMatrixData n) :
    (costedIntegerProductRound r u v X Y).value =
      integerMatrixData ((integerMatrixOfData X * integerMatrixOfData Y).map (fun z => z * 2 ^ r / (u * v))) := by
  rw [costedIntegerProductRound, Costed.bind_value]
  dsimp only [Costed.charge]
  rw [Costed.bind_value]
  dsimp only [costedIntMul]
  rw [Costed.bind_value, costedIntegerMatrixMul_data, costedIntegerScaleDivide_data, integerMatrixOfData_data]

def integerProductRoundBudget (n L : ℕ) : ℕ :=
  L + (2 * L + 1) ^ 2 + integerMatrixMulBudget n L + integerScaleDivideBudget n (n + 2 * L + 1)

theorem costedIntegerProductRound_steps_le {n : ℕ} (r : ℕ) (u v : ℤ) (X Y : IntegerMatrixData n) (L : ℕ)
    (hr : r + 1 ≤ L) (hu : u.natAbs.size ≤ L) (hv : v.natAbs.size ≤ L)
    (hX : ∀ i j, (integerMatrixOfData X i j).natAbs.size ≤ L)
    (hY : ∀ i j, (integerMatrixOfData Y i j).natAbs.size ≤ L) :
    (costedIntegerProductRound r u v X Y).steps ≤ integerProductRoundBudget n L := by
  have hs : ((2 : ℤ) ^ r).natAbs.size ≤ L := by simpa [Int.natAbs_pow, Nat.size_pow] using hr
  have hd := integer_mul_size_le u v L L hu hv
  have hP := costedIntegerMatrixMul_size_le X Y L hX hY
  have hDs := costedIntegerScaleDivide_steps_le ((2 : ℤ) ^ r) (u * v) (costedIntegerMatrixMul X Y).value
    (n + 2 * L + 1) (hs.trans (by omega)) (hd.trans (by omega)) hP
  have hPs := costedIntegerMatrixMul_steps_le X Y L hX hY
  have hmul : (integerOperandBits u v) ^ 2 ≤ (2 * L + 1) ^ 2 :=
    Nat.pow_le_pow_left (by unfold integerOperandBits; omega) 2
  change r + 1 + ((integerOperandBits u v) ^ 2 +
    ((costedIntegerMatrixMul X Y).steps +
      (costedIntegerScaleDivide ((2 : ℤ) ^ r) (u * v) (costedIntegerMatrixMul X Y).value).steps)) ≤ _
  unfold integerProductRoundBudget
  omega

theorem costedIntegerProductRound_size {n : ℕ} (r : ℕ) (u v : ℤ) (X Y : IntegerMatrixData n) (L : ℕ)
    (hX : ∀ i j, (integerMatrixOfData X i j).natAbs.size ≤ L)
    (hY : ∀ i j, (integerMatrixOfData Y i j).natAbs.size ≤ L) (i j : Fin n) :
    (integerMatrixOfData (costedIntegerProductRound r u v X Y).value i j).natAbs.size ≤ n + 2 * L + r + 1 := by
  rw [costedIntegerProductRound_data, integerMatrixOfData_data]
  apply (Nat.size_le_size (Int.natAbs_ediv_le_natAbs _ _)).trans
  simpa [two_mul, Nat.add_assoc] using integerScaledProduct_size r L L (integerMatrixOfData X) (integerMatrixOfData Y)
    (fun i j => (Nat.size_le.mp (hX i j)).le) (fun i j => (Nat.size_le.mp (hY i j)).le) i j

theorem rational_integer_quotient_bits (z : ℤ) (a L : ℕ) (ha : 0 < a)
    (hz : z.natAbs.size ≤ L) (has : a.size ≤ L) :
    rationalMagnitudeBits ((z : ℚ) / a) ≤ 2 * L + 1 := by
  have he : (z : ℚ) / a = Rat.divInt z a := by simp [Rat.divInt_eq_div]
  rw [he]
  have hn : (Rat.divInt z a).num.natAbs ≤ z.natAbs := by
    rw [Rat.num_divInt, Int.sign_eq_one_of_pos (by exact_mod_cast ha), one_mul]
    exact Int.natAbs_ediv_le_natAbs _ _
  have hd : (Rat.divInt z a).den ≤ a := by
    rw [Rat.den_divInt, ite_eq_right (by exact_mod_cast ha.ne'), Int.natAbs_natCast]
    exact Nat.div_le_self _ _
  have hn' := (Nat.size_le_size hn).trans hz
  have hd' := (Nat.size_le_size hd).trans has
  unfold rationalMagnitudeBits
  omega

def costedRationalMatrixOfFn {n : ℕ} (f : Fin n → Fin n → Costed ℚ) : Costed (RationalMatrixData n) :=
  costedVectorOfFn (fun i => costedVectorOfFn (f i))

theorem costedRationalMatrixOfFn_value {n : ℕ} (f : Fin n → Fin n → Costed ℚ) :
    rationalMatrixOfData (costedRationalMatrixOfFn f).value = fun i j => (f i j).value := by
  ext i j
  simp [costedRationalMatrixOfFn, costedVectorOfFn_value, rationalMatrixOfData, Vector.get]
  rfl

theorem costedRationalMatrixOfFn_steps_le {n : ℕ} (f : Fin n → Fin n → Costed ℚ)
    (L : ℕ) (hf : ∀ i j, (f i j).steps ≤ L) :
    (costedRationalMatrixOfFn f).steps ≤ integerMatrixTraversalBudget n L :=
  costedVectorOfFn_steps_le _ _ (fun i => costedVectorOfFn_steps_le _ L (hf i))

def costedIntegerToRational (a : ℕ) (z : ℤ) : Costed ℚ :=
  (Costed.charge (z.natAbs.size + 1) (z : ℚ)).bind (fun q => costedRatDiv q (a : ℚ))

def costedRationalQuotient {n : ℕ} (a : ℕ) (X : IntegerMatrixData n) : Costed (RationalMatrixData n) :=
  (Costed.charge (a.size + 1) a).bind fun d =>
    (costedRationalMatrixOfFn (fun i j => costedIntegerToRational d (integerMatrixOfData X i j))).bind
      (fun D => Costed.charge (encodeRationalMatrixData D).length D)

theorem costedRationalQuotient_value {n : ℕ} (a : ℕ) (X : IntegerMatrixData n) :
    rationalMatrixOfData (costedRationalQuotient a X).value = integerMatrixQuotient a (integerMatrixOfData X) := by
  rw [costedRationalQuotient, Costed.bind_value]
  dsimp only [Costed.charge]
  rw [Costed.bind_value]
  dsimp only [Costed.charge]
  rw [costedRationalMatrixOfFn_value]
  ext i j
  simp [costedIntegerToRational, Costed.charge, costedRatDiv, integerMatrixQuotient_apply]

def rationalQuotientOutputBudget (n L : ℕ) : ℕ := 2 * n + 1 + n * n * (4 * L + 3)

theorem rationalQuotient_encoded_length {n : ℕ} (a : ℕ) (X : IntegerMatrixData n) (L : ℕ)
    (ha : 0 < a) (has : a.size ≤ L)
    (hX : ∀ i j, (integerMatrixOfData X i j).natAbs.size ≤ L) :
    (encodeRationalMatrixData (costedRationalQuotient a X).value).length ≤ rationalQuotientOutputBudget n L := by
  rw [encodeRationalMatrixData_length, costedRationalQuotient_value]
  have hs : rationalMatrixMagnitudeBits (integerMatrixQuotient a (integerMatrixOfData X)) ≤ n * n * (2 * L + 1) := by
    calc
      _ ≤ ∑ i : Fin n, ∑ j : Fin n, (2 * L + 1) := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        rw [integerMatrixQuotient_apply]
        exact rational_integer_quotient_bits _ a L ha (hX i j) has
      _ = _ := by simp; ring
  have hn : n.size ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self
  unfold rationalQuotientOutputBudget
  nlinarith

def rationalQuotientCostBudget (n L : ℕ) : ℕ :=
  L + 1 + integerMatrixTraversalBudget n (L + 1 + (2 * L + 5) ^ 3) + rationalQuotientOutputBudget n L

theorem costedRationalQuotient_steps_le {n : ℕ} (a : ℕ) (X : IntegerMatrixData n) (L : ℕ)
    (ha : 0 < a) (has : a.size ≤ L)
    (hX : ∀ i j, (integerMatrixOfData X i j).natAbs.size ≤ L) :
    (costedRationalQuotient a X).steps ≤ rationalQuotientCostBudget n L := by
  let D := costedRationalMatrixOfFn (fun i j => costedIntegerToRational a (integerMatrixOfData X i j))
  have hd : D.steps ≤ integerMatrixTraversalBudget n (L + 1 + (2 * L + 5) ^ 3) := by
    apply costedRationalMatrixOfFn_steps_le
    intro i j
    have hz := hX i j
    have hrat : rationalArithmeticCost (integerMatrixOfData X i j : ℚ) (a : ℚ) ≤ (2 * L + 5) ^ 3 := by
      unfold rationalArithmeticCost
      rw [intCast_rational_bits, show (a : ℚ) = ((a : ℤ) : ℚ) by simp, intCast_rational_bits]
      apply Nat.pow_le_pow_left
      simp only [Int.natAbs_natCast]
      omega
    change (integerMatrixOfData X i j).natAbs.size + 1 +
      rationalArithmeticCost (integerMatrixOfData X i j : ℚ) (a : ℚ) ≤ _
    exact Nat.add_le_add (by omega) hrat
  have he : (encodeRationalMatrixData D.value).length ≤ rationalQuotientOutputBudget n L :=
    rationalQuotient_encoded_length a X L ha has hX
  change a.size + 1 + (D.steps + (encodeRationalMatrixData D.value).length) ≤ _
  unfold rationalQuotientCostBudget
  omega

end GeometricGaussianLHL

end IntegerOutputCost

section RationalMatrixOutputCost

/-!
## Rational matrix postprocessing costs

Rescaling and transpose averaging operate on stored outputs. Entry-size bounds
control rational reduction and the final serialization charge.
-/

namespace GeometricGaussianLHL

theorem rationalMatrixData_ofData {n : ℕ} (D : RationalMatrixData n) :
    rationalMatrixData (rationalMatrixOfData D) = D := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  simp [rationalMatrixData, rationalMatrixOfData, Vector.get]
  rfl

theorem costedRationalMatrixOfFn_data {n : ℕ} (f : Fin n → Fin n → Costed ℚ) :
    (costedRationalMatrixOfFn f).value = rationalMatrixData (fun i j => (f i j).value) := by
  rw [← rationalMatrixData_ofData (costedRationalMatrixOfFn f).value, costedRationalMatrixOfFn_value]

theorem rationalMatrixEntryBits_le_encoded {n : ℕ} (D : RationalMatrixData n) (i j : Fin n) :
    rationalMagnitudeBits (rationalMatrixOfData D i j) ≤ (encodeRationalMatrixData D).length := by
  have h := rationalMatrix_entry_bits_le (rationalMatrixOfData D) i j
  rw [encodeRationalMatrixData_length]
  omega

def rationalMatrixEncodingBudget (n L : ℕ) : ℕ := 2 * n + 1 + n * n * (2 * L + 1)

theorem rationalMatrixEncoded_length_le {n : ℕ} (D : RationalMatrixData n) (L : ℕ)
    (hD : ∀ i j, rationalMagnitudeBits (rationalMatrixOfData D i j) ≤ L) :
    (encodeRationalMatrixData D).length ≤ rationalMatrixEncodingBudget n L := by
  have hs : rationalMatrixMagnitudeBits (rationalMatrixOfData D) ≤ n * n * L := by
    calc
      _ ≤ ∑ i : Fin n, ∑ j : Fin n, L := Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hD i j))
      _ = _ := by simp; ring
  have hn : n.size ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self
  rw [encodeRationalMatrixData_length]
  unfold rationalMatrixEncodingBudget
  nlinarith

theorem rational_mul_bits_le (x y : ℚ) (L : ℕ)
    (hx : rationalMagnitudeBits x ≤ L) (hy : rationalMagnitudeBits y ≤ L) :
    rationalMagnitudeBits (x * y) ≤ 6 * L + 3 := by
  have hd : (x * y).den ≤ 2 ^ (2 * L) := by
    apply (Nat.le_of_dvd (Nat.mul_pos x.den_pos y.den_pos) (Rat.mul_den_dvd x y)).trans
    rw [two_mul, pow_add]
    exact Nat.mul_le_mul ((rational_den_le_pow_bits x).trans (Nat.pow_le_pow_right (by omega) hx))
      ((rational_den_le_pow_bits y).trans (Nat.pow_le_pow_right (by omega) hy))
  have ha : |x * y| ≤ (2 : ℚ) ^ (2 * L) := by
    rw [abs_mul, two_mul, pow_add]
    exact mul_le_mul ((rational_abs_le_pow_bits x).trans (pow_le_pow_right₀ (by norm_num) hx))
      ((rational_abs_le_pow_bits y).trans (pow_le_pow_right₀ (by norm_num) hy)) (abs_nonneg _) (by positivity)
  have h := rational_bits_le_of_den_abs _ _ _ hd ha
  omega

def costedRationalMatrixScale {n : ℕ} (c : ℚ) (D : RationalMatrixData n) : Costed (RationalMatrixData n) :=
  costedRationalMatrixOfFn fun i j => costedRatMul c (rationalMatrixOfData D i j)

theorem costedRationalMatrixScale_data {n : ℕ} (c : ℚ) (D : RationalMatrixData n) :
    (costedRationalMatrixScale c D).value = rationalMatrixData (c • rationalMatrixOfData D) := by
  rw [costedRationalMatrixScale, costedRationalMatrixOfFn_data]
  rfl

theorem costedRationalMatrixScale_steps_le {n : ℕ} (c : ℚ) (D : RationalMatrixData n) (L : ℕ)
    (hc : rationalMagnitudeBits c ≤ L) (hD : ∀ i j, rationalMagnitudeBits (rationalMatrixOfData D i j) ≤ L) :
    (costedRationalMatrixScale c D).steps ≤ integerMatrixTraversalBudget n ((2 * L + 1) ^ 3) :=
  costedRationalMatrixOfFn_steps_le _ _ (fun i j => rationalArithmeticCost_le _ _ hc (hD i j))

theorem costedRationalMatrixScale_size {n : ℕ} (c : ℚ) (D : RationalMatrixData n) (L : ℕ)
    (hc : rationalMagnitudeBits c ≤ L) (hD : ∀ i j, rationalMagnitudeBits (rationalMatrixOfData D i j) ≤ L) (i j : Fin n) :
    rationalMagnitudeBits (rationalMatrixOfData (costedRationalMatrixScale c D).value i j) ≤ 6 * L + 3 := by
  rw [costedRationalMatrixScale_data, rationalMatrixOfData_data]
  exact rational_mul_bits_le c (rationalMatrixOfData D i j) L hc (hD i j)

def costedRationalSymmetrize {n : ℕ} (D : RationalMatrixData n) : Costed (RationalMatrixData n) :=
  costedRationalMatrixOfFn fun i j =>
    (costedRatAdd (rationalMatrixOfData D i j) (rationalMatrixOfData D j i)).bind (fun s => costedRatDiv s 2)

theorem costedRationalSymmetrize_data {n : ℕ} (D : RationalMatrixData n) :
    (costedRationalSymmetrize D).value = rationalMatrixData ((1 / 2 : ℚ) •
      (rationalMatrixOfData D + (rationalMatrixOfData D).transpose)) := by
  rw [costedRationalSymmetrize, costedRationalMatrixOfFn_data]
  congr 1
  ext i j
  simp [costedRatAdd, costedRatDiv, Matrix.smul_apply, div_eq_mul_inv, mul_comm]

def rationalSymmetrizeBudget (n L : ℕ) : ℕ := integerMatrixTraversalBudget n ((2 * L + 1) ^ 3 + (5 * L + 9) ^ 3)

theorem costedRationalSymmetrize_steps_le {n : ℕ} (D : RationalMatrixData n) (L : ℕ)
    (hD : ∀ i j, rationalMagnitudeBits (rationalMatrixOfData D i j) ≤ L) :
    (costedRationalSymmetrize D).steps ≤ rationalSymmetrizeBudget n L := by
  apply costedRationalMatrixOfFn_steps_le
  intro i j
  have hsum := rational_add_bits_le _ _ L (hD i j) (hD j i)
  have h₁ := rationalArithmeticCost_le _ _ (hD i j) (hD j i)
  have h₂ : rationalArithmeticCost (rationalMatrixOfData D i j + rationalMatrixOfData D j i) 2 ≤ (5 * L + 9) ^ 3 := by
    unfold rationalArithmeticCost
    have htwo : rationalMagnitudeBits (2 : ℚ) = 4 := by decide
    rw [htwo]
    exact Nat.pow_le_pow_left (by omega) 3
  exact Nat.add_le_add h₁ h₂

theorem costedRationalSymmetrize_size {n : ℕ} (D : RationalMatrixData n) (L : ℕ)
    (hD : ∀ i j, rationalMagnitudeBits (rationalMatrixOfData D i j) ≤ L) (i j : Fin n) :
    rationalMagnitudeBits (rationalMatrixOfData (costedRationalSymmetrize D).value i j) ≤ 15 * L + 17 := by
  rw [costedRationalSymmetrize, costedRationalMatrixOfFn_value]
  have h := rational_half_bits_le _ (5 * L + 4) (rational_add_bits_le _ _ L (hD i j) (hD j i))
  change rationalMagnitudeBits ((rationalMatrixOfData D i j + rationalMatrixOfData D j i) / 2) ≤ _
  omega

theorem rational_pow_two_bits (e : ℕ) : rationalMagnitudeBits ((2 : ℚ) ^ e) = e + 3 := by
  have h := intCast_rational_bits ((2 : ℤ) ^ e)
  simpa [Int.natAbs_pow, Nat.size_pow, Nat.add_assoc] using h

def costedRationalDyadicScalar (inverse : Bool) (e : ℕ) : Costed ℚ :=
  (Costed.charge (e + 1) (2 ^ e : ℕ)).bind fun d =>
    (Costed.charge (d.size + 1) (d : ℚ)).bind fun q =>
      if inverse then costedRatDiv 1 q else Costed.pure q

theorem costedRationalDyadicScalar_value (inverse : Bool) (e : ℕ) :
    (costedRationalDyadicScalar inverse e).value = if inverse then 1 / (2 : ℚ) ^ e else (2 : ℚ) ^ e := by
  cases inverse <;> simp [costedRationalDyadicScalar, costedRatDiv, Costed.charge, Costed.pure]

def rationalDyadicScalarBudget (e : ℕ) : ℕ := 2 * e + 3 + (e + 7) ^ 3

theorem costedRationalDyadicScalar_steps_le (inverse : Bool) (e : ℕ) :
    (costedRationalDyadicScalar inverse e).steps ≤ rationalDyadicScalarBudget e := by
  have hc : rationalArithmeticCost 1 ((2 : ℚ) ^ e) = (e + 7) ^ 3 := by
    unfold rationalArithmeticCost
    rw [rational_pow_two_bits]
    have h₁ : rationalMagnitudeBits (1 : ℚ) = 3 := by decide
    rw [h₁]
    congr 1
    omega
  cases inverse <;> simp [costedRationalDyadicScalar, Costed.charge, Costed.pure, costedRatDiv,
    Nat.size_pow, rationalDyadicScalarBudget, hc] <;> omega

theorem costedRationalDyadicScalar_size (inverse : Bool) (e : ℕ) :
    rationalMagnitudeBits (costedRationalDyadicScalar inverse e).value ≤ 2 * e + 3 := by
  rw [costedRationalDyadicScalar_value]
  cases inverse with
  | false => simpa only [Bool.false_eq_true, ite_false, rational_pow_two_bits] using (show e + 3 ≤ 2 * e + 3 by omega)
  | true =>
    have h := rational_integer_quotient_bits 1 (2 ^ e) (e + 1) (by positivity) (by simp) (by simp [Nat.size_pow])
    simpa [Nat.mul_add, Nat.add_assoc] using h

def costedRationalDyadicOutput {n : ℕ} (inverse : Bool) (e : ℕ) (D : RationalMatrixData n) : Costed (RationalMatrixData n) :=
  (costedRationalDyadicScalar inverse e).bind fun c =>
    (costedRationalMatrixScale c D).bind fun R => Costed.charge (encodeRationalMatrixData R).length R

theorem costedRationalDyadicOutput_data {n : ℕ} (inverse : Bool) (e : ℕ) (D : RationalMatrixData n) :
    (costedRationalDyadicOutput inverse e D).value = rationalMatrixData
      ((if inverse then 1 / (2 : ℚ) ^ e else (2 : ℚ) ^ e) • rationalMatrixOfData D) := by
  rw [costedRationalDyadicOutput, Costed.bind_value, costedRationalDyadicScalar_value, Costed.bind_value]
  dsimp only [Costed.charge]
  rw [costedRationalMatrixScale_data]

def rationalDyadicOutputBudget (n e L : ℕ) : ℕ :=
  let H := L + 2 * e + 3
  rationalDyadicScalarBudget e + integerMatrixTraversalBudget n ((2 * H + 1) ^ 3) + rationalMatrixEncodingBudget n (6 * H + 3)

theorem costedRationalDyadicOutput_steps_le {n : ℕ} (inverse : Bool) (e L : ℕ) (D : RationalMatrixData n)
    (hD : ∀ i j, rationalMagnitudeBits (rationalMatrixOfData D i j) ≤ L) :
    (costedRationalDyadicOutput inverse e D).steps ≤ rationalDyadicOutputBudget n e L := by
  let c := (costedRationalDyadicScalar inverse e).value
  let H := L + 2 * e + 3
  have hc : rationalMagnitudeBits c ≤ H := (costedRationalDyadicScalar_size inverse e).trans (by dsimp [H]; omega)
  have hD' : ∀ i j, rationalMagnitudeBits (rationalMatrixOfData D i j) ≤ H := fun i j => (hD i j).trans (by dsimp [H]; omega)
  have hscale := costedRationalMatrixScale_steps_le c D H hc hD'
  have hlen := rationalMatrixEncoded_length_le (costedRationalMatrixScale c D).value (6 * H + 3)
    (costedRationalMatrixScale_size c D H hc hD')
  have hscalar := costedRationalDyadicScalar_steps_le inverse e
  rw [costedRationalDyadicOutput, Costed.bind_steps, Costed.bind_steps]
  change (costedRationalDyadicScalar inverse e).steps +
    ((costedRationalMatrixScale c D).steps + (encodeRationalMatrixData (costedRationalMatrixScale c D).value).length) ≤ _
  change _ ≤ rationalDyadicScalarBudget e + integerMatrixTraversalBudget n ((2 * H + 1) ^ 3) + rationalMatrixEncodingBudget n (6 * H + 3)
  omega

theorem costedRationalDyadicOutput_length_le_steps {n : ℕ} (inverse : Bool) (e : ℕ) (D : RationalMatrixData n) :
    (encodeRationalMatrixData (costedRationalDyadicOutput inverse e D).value).length ≤ (costedRationalDyadicOutput inverse e D).steps := by
  rw [costedRationalDyadicOutput, Costed.bind_value, Costed.bind_steps, Costed.bind_value, Costed.bind_steps]
  dsimp only [Costed.charge]
  omega

end GeometricGaussianLHL

end RationalMatrixOutputCost

section RationalDotCost

/-!
## Rational dot products with polynomial operand growth

A common denominator divides the product of the input denominators. This
bounds every partial sum without repeatedly multiplying a bound on reduced
numerator/denominator lengths. The execution charges the actual products and
partial sums, including rational normalization.
-/

namespace GeometricGaussianLHL

theorem rational_inv_bits (x : ℚ) : rationalMagnitudeBits x⁻¹ = rationalMagnitudeBits x := by
  by_cases hx : x = 0
  · simp [hx]
  · unfold rationalMagnitudeBits
    rw [Rat.num_inv, Rat.den_inv_of_ne_zero hx, Int.natAbs_mul,
      Int.natAbs_sign_of_ne_zero (Rat.num_ne_zero.mpr hx), Int.natAbs_natCast, one_mul]
    omega

theorem rational_div_bits_le (x y : ℚ) (L : ℕ)
    (hx : rationalMagnitudeBits x ≤ L) (hy : rationalMagnitudeBits y ≤ L) :
    rationalMagnitudeBits (x / y) ≤ 6 * L + 3 := by
  rw [div_eq_mul_inv]
  exact rational_mul_bits_le _ _ L hx (by rw [rational_inv_bits]; exact hy)

theorem rational_neg_bits (x : ℚ) : rationalMagnitudeBits (-x) = rationalMagnitudeBits x := by
  simp [rationalMagnitudeBits]

theorem rational_sub_bits_le (x y : ℚ) (L : ℕ)
    (hx : rationalMagnitudeBits x ≤ L) (hy : rationalMagnitudeBits y ≤ L) :
    rationalMagnitudeBits (x - y) ≤ 5 * L + 4 := by
  rw [sub_eq_add_neg]
  exact rational_add_bits_le _ _ L hx (by rw [rational_neg_bits]; exact hy)

def costedRatSub (x y : ℚ) : Costed ℚ := ⟨x - y, rationalArithmeticCost x y⟩

def rationalListDot (xs : List (ℚ × ℚ)) : ℚ := (xs.map (fun x => x.1 * x.2)).sum

theorem rationalListDot_den_dvd (xs : List (ℚ × ℚ)) :
    (rationalListDot xs).den ∣ (xs.map (fun x => x.1.den * x.2.den)).prod := by
  induction xs with
  | nil => simp [rationalListDot]
  | cons x xs ih =>
    simp only [rationalListDot, List.map_cons, List.sum_cons, List.prod_cons] at *
    exact (Rat.add_den_dvd _ _).trans (Nat.mul_dvd_mul (Rat.mul_den_dvd x.1 x.2) ih)

theorem rationalListDot_den_le (xs : List (ℚ × ℚ)) (L : ℕ)
    (hxs : ∀ x ∈ xs, rationalMagnitudeBits x.1 ≤ L ∧ rationalMagnitudeBits x.2 ≤ L) :
    (rationalListDot xs).den ≤ 2 ^ (2 * L * xs.length) := by
  have hp : 0 < (xs.map (fun x => x.1.den * x.2.den)).prod := by
    apply List.prod_pos
    intro a ha
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp ha
    exact Nat.mul_pos x.1.den_pos x.2.den_pos
  apply (Nat.le_of_dvd hp (rationalListDot_den_dvd xs)).trans
  clear hp
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := hxs x (List.mem_cons_self ..)
    have ht := ih (fun y hy => hxs y (List.mem_cons_of_mem _ hy))
    have hxden := (rational_den_le_pow_bits x.1).trans (Nat.pow_le_pow_right (by omega) hx.1)
    have hyden := (rational_den_le_pow_bits x.2).trans (Nat.pow_le_pow_right (by omega) hx.2)
    have hprod := Nat.mul_le_mul (Nat.mul_le_mul hxden hyden) ht
    simpa [List.length_cons, Nat.mul_add, two_mul, pow_add, Nat.mul_assoc, Nat.mul_comm] using hprod

theorem rationalListDot_abs_le (xs : List (ℚ × ℚ)) (L : ℕ)
    (hxs : ∀ x ∈ xs, rationalMagnitudeBits x.1 ≤ L ∧ rationalMagnitudeBits x.2 ≤ L) :
    |rationalListDot xs| ≤ xs.length * (2 : ℚ) ^ (2 * L) := by
  induction xs with
  | nil => simp [rationalListDot]
  | cons x xs ih =>
    have hx := hxs x (List.mem_cons_self ..)
    have ht := ih (fun y hy => hxs y (List.mem_cons_of_mem _ hy))
    have hp : |x.1 * x.2| ≤ (2 : ℚ) ^ (2 * L) := by
      rw [abs_mul, two_mul, pow_add]
      exact mul_le_mul ((rational_abs_le_pow_bits x.1).trans (pow_le_pow_right₀ (by norm_num) hx.1))
        ((rational_abs_le_pow_bits x.2).trans (pow_le_pow_right₀ (by norm_num) hx.2)) (abs_nonneg _) (by positivity)
    change |x.1 * x.2 + rationalListDot xs| ≤ _
    have h := (abs_add_le _ _).trans (add_le_add hp ht)
    simpa [List.length_cons, Nat.cast_add, add_mul, add_comm] using h

def rationalDotOperandBudget (m L : ℕ) : ℕ := 4 * m * L + m + 6 * L + 3

theorem rationalListDot_bits (xs : List (ℚ × ℚ)) (L : ℕ)
    (hxs : ∀ x ∈ xs, rationalMagnitudeBits x.1 ≤ L ∧ rationalMagnitudeBits x.2 ≤ L) :
    rationalMagnitudeBits (rationalListDot xs) ≤ rationalDotOperandBudget xs.length L := by
  have ha : |rationalListDot xs| ≤ (2 : ℚ) ^ (xs.length + 2 * L) := by
    apply (rationalListDot_abs_le xs L hxs).trans
    rw [pow_add]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast (Nat.lt_two_pow_self (n := xs.length)).le) (by positivity)
  have h := rational_bits_le_of_den_abs _ _ _ (rationalListDot_den_le xs L hxs) ha
  unfold rationalDotOperandBudget
  nlinarith

def costedRationalDot : List (ℚ × ℚ) → Costed ℚ
  | [] => Costed.charge 1 0
  | (a, b) :: xs => (costedRationalDot xs).bind fun s =>
      (costedRatMul a b).bind fun p =>
        (costedRatAdd p s).bind fun z => Costed.charge 1 z

@[simp] theorem costedRationalDot_value (xs : List (ℚ × ℚ)) :
    (costedRationalDot xs).value = rationalListDot xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [costedRationalDot, Costed.bind_value, costedRatMul, costedRatAdd,
      Costed.charge, rationalListDot, List.map_cons, List.sum_cons] at *
    exact congrArg (fun s => x.1 * x.2 + s) ih

def rationalDotBudget (m L : ℕ) : ℕ := m * (2 * (2 * rationalDotOperandBudget m L + 1) ^ 3 + 1) + 1

theorem costedRationalDot_steps_le (xs : List (ℚ × ℚ)) (L : ℕ)
    (hxs : ∀ x ∈ xs, rationalMagnitudeBits x.1 ≤ L ∧ rationalMagnitudeBits x.2 ≤ L) :
    (costedRationalDot xs).steps ≤ rationalDotBudget xs.length L := by
  induction xs with
  | nil => simp [costedRationalDot, Costed.charge, rationalDotBudget]
  | cons x xs ih =>
    have hx := hxs x (List.mem_cons_self ..)
    have ht := fun y hy => hxs y (List.mem_cons_of_mem _ hy)
    have hs := rationalListDot_bits xs L ht
    have hp := rational_mul_bits_le x.1 x.2 L hx.1 hx.2
    let M := rationalDotOperandBudget (xs.length + 1) L
    have hL : L ≤ M := by dsimp [M, rationalDotOperandBudget]; omega
    have hM : rationalDotOperandBudget xs.length L ≤ M := by dsimp [M, rationalDotOperandBudget]; nlinarith
    have h₁ := rationalArithmeticCost_le x.1 x.2 (hx.1.trans hL) (hx.2.trans hL)
    have h₂ := rationalArithmeticCost_le (x.1 * x.2) (rationalListDot xs)
      (hp.trans (by dsimp [M, rationalDotOperandBudget]; omega)) (hs.trans hM)
    have hi := ih ht
    have hi' : (costedRationalDot xs).steps ≤ xs.length * (2 * (2 * M + 1) ^ 3 + 1) + 1 := by
      apply hi.trans
      unfold rationalDotBudget
      gcongr
    simp only [costedRationalDot, Costed.bind_steps, costedRationalDot_value, costedRatMul, costedRatAdd, Costed.charge]
    change _ ≤ (xs.length + 1) * (2 * (2 * M + 1) ^ 3 + 1) + 1
    nlinarith

theorem polyBound_rationalDotOperandBudget {m L : ℕ → ℕ}
    (hm : PolynomialCostBound m) (hL : PolynomialCostBound L) :
    PolynomialCostBound (fun x => rationalDotOperandBudget (m x) (L x)) :=
  (((((PolynomialCostBound.const 4).mul hm).mul hL).add hm).add ((PolynomialCostBound.const 6).mul hL)).add (PolynomialCostBound.const 3)

theorem polyBound_rationalDotBudget {m L : ℕ → ℕ}
    (hm : PolynomialCostBound m) (hL : PolynomialCostBound L) :
    PolynomialCostBound (fun x => rationalDotBudget (m x) (L x)) :=
  (hm.mul (((PolynomialCostBound.const 2).mul ((((PolynomialCostBound.const 2).mul
    (polyBound_rationalDotOperandBudget hm hL)).add (PolynomialCostBound.const 1)).pow 3)).add (PolynomialCostBound.const 1))).add (PolynomialCostBound.const 1)

end GeometricGaussianLHL

end RationalDotCost

section RationalRectCost

/-!
## Stored rectangular rational matrix operations

The square case is definitionally the existing rational matrix data type.
Traversal, rational arithmetic and dot-product charges compose directly.
-/

namespace GeometricGaussianLHL

abbrev RationalRectData (p q : ℕ) := Vector (Vector ℚ q) p

def rationalRectMatrixData {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℚ) : RationalRectData p q :=
  Vector.ofFn (fun i => Vector.ofFn (A i))

def rationalRectMatrixOfData {p q : ℕ} (D : RationalRectData p q) : Matrix (Fin p) (Fin q) ℚ :=
  fun i j => (D.get i).get j

theorem rationalRectMatrixOfData_data {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℚ) :
    rationalRectMatrixOfData (rationalRectMatrixData A) = A := by
  ext i j
  simp [rationalRectMatrixOfData, rationalRectMatrixData, Vector.get]
  rfl

theorem rationalRectMatrixData_ofData {p q : ℕ} (D : RationalRectData p q) :
    rationalRectMatrixData (rationalRectMatrixOfData D) = D := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  simp [rationalRectMatrixOfData, rationalRectMatrixData, Vector.get]
  rfl

def rationalRectMagnitudeBits {p q : ℕ} (D : RationalRectData p q) : ℕ :=
  ∑ i, ∑ j, rationalMagnitudeBits (rationalRectMatrixOfData D i j)

def encodeRationalRectData {p q : ℕ} (D : RationalRectData p q) : List Bool :=
  encodeNatBits p ++ encodeNatBits q ++ encodeVectorBits (encodeVectorBits encodeRatBits) D

theorem encodeRationalRectData_length {p q : ℕ} (D : RationalRectData p q) :
    (encodeRationalRectData D).length = 2 * p.size + 2 * q.size + 2 + 2 * rationalRectMagnitudeBits D + p * q := by
  simp only [encodeRationalRectData, List.length_append, encodeNatBits_length, encodeVectorBits_length_sum,
    encodeRatBits_length, rationalRectMagnitudeBits, rationalRectMatrixOfData]
  simp [Finset.sum_add_distrib, Finset.mul_sum]
  ring

theorem rationalRect_entry_bits_le {p q : ℕ} (D : RationalRectData p q) (i : Fin p) (j : Fin q) :
    rationalMagnitudeBits (rationalRectMatrixOfData D i j) ≤ rationalRectMagnitudeBits D :=
  (Finset.single_le_sum (fun k _ => Nat.zero_le (rationalMagnitudeBits (rationalRectMatrixOfData D i k))) (Finset.mem_univ j)).trans
    (Finset.single_le_sum (fun k _ => Nat.zero_le (∑ l, rationalMagnitudeBits (rationalRectMatrixOfData D k l))) (Finset.mem_univ i))

def costedRationalRectOfFn {p q : ℕ} (f : Fin p → Fin q → Costed ℚ) : Costed (RationalRectData p q) :=
  costedVectorOfFn (fun i => costedVectorOfFn (f i))

theorem costedRationalRectOfFn_data {p q : ℕ} (f : Fin p → Fin q → Costed ℚ) :
    (costedRationalRectOfFn f).value = rationalRectMatrixData (fun i j => (f i j).value) := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  simp [costedRationalRectOfFn, costedVectorOfFn_value, rationalRectMatrixData]

def rationalRectTraversalBudget (p q L : ℕ) : ℕ := p * (q * (L + 3) + 4) + 1

theorem costedRationalRectOfFn_steps_le {p q : ℕ} (f : Fin p → Fin q → Costed ℚ)
    (L : ℕ) (hf : ∀ i j, (f i j).steps ≤ L) :
    (costedRationalRectOfFn f).steps ≤ rationalRectTraversalBudget p q L :=
  costedVectorOfFn_steps_le _ _ (fun i => costedVectorOfFn_steps_le _ L (hf i))

def costedRationalRectMul {p q r : ℕ} (X : RationalRectData p q) (Y : RationalRectData q r) : Costed (RationalRectData p r) :=
  costedRationalRectOfFn fun i j =>
    (Costed.charge (q + 1) (List.ofFn (fun k => (rationalRectMatrixOfData X i k, rationalRectMatrixOfData Y k j)))).bind costedRationalDot

theorem costedRationalRectMul_data {p q r : ℕ} (X : RationalRectData p q) (Y : RationalRectData q r) :
    (costedRationalRectMul X Y).value = rationalRectMatrixData (rationalRectMatrixOfData X * rationalRectMatrixOfData Y) := by
  rw [costedRationalRectMul, costedRationalRectOfFn_data]
  congr 1
  ext i j
  simp [Costed.charge, rationalListDot, Matrix.mul_apply, List.sum_ofFn]

def rationalRectMulBudget (p q r L : ℕ) : ℕ := rationalRectTraversalBudget p r (q + 1 + rationalDotBudget q L)

theorem costedRationalRectMul_steps_le {p q r : ℕ} (X : RationalRectData p q) (Y : RationalRectData q r) (L : ℕ)
    (hX : ∀ i j, rationalMagnitudeBits (rationalRectMatrixOfData X i j) ≤ L)
    (hY : ∀ i j, rationalMagnitudeBits (rationalRectMatrixOfData Y i j) ≤ L) :
    (costedRationalRectMul X Y).steps ≤ rationalRectMulBudget p q r L := by
  apply costedRationalRectOfFn_steps_le
  intro i j
  have h := costedRationalDot_steps_le (List.ofFn (fun k => (rationalRectMatrixOfData X i k, rationalRectMatrixOfData Y k j))) L
    (by intro x hx; obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hx; exact ⟨hX i k, hY k j⟩)
  simpa only [Costed.bind_steps, Costed.charge, List.length_ofFn] using Nat.add_le_add_left h (q + 1)

theorem costedRationalRectMul_size {p q r : ℕ} (X : RationalRectData p q) (Y : RationalRectData q r) (L : ℕ)
    (hX : ∀ i j, rationalMagnitudeBits (rationalRectMatrixOfData X i j) ≤ L)
    (hY : ∀ i j, rationalMagnitudeBits (rationalRectMatrixOfData Y i j) ≤ L) (i : Fin p) (j : Fin r) :
    rationalMagnitudeBits (rationalRectMatrixOfData (costedRationalRectMul X Y).value i j) ≤ rationalDotOperandBudget q L := by
  rw [costedRationalRectMul_data, rationalRectMatrixOfData_data]
  have h := rationalListDot_bits (List.ofFn (fun k => (rationalRectMatrixOfData X i k, rationalRectMatrixOfData Y k j))) L
    (by intro x hx; obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hx; exact ⟨hX i k, hY k j⟩)
  simpa [rationalListDot, Matrix.mul_apply, List.sum_ofFn] using h

def costedRationalRectTranspose {p q : ℕ} (X : RationalRectData p q) : Costed (RationalRectData q p) :=
  costedRationalRectOfFn fun i j => Costed.charge (rationalMagnitudeBits (rationalRectMatrixOfData X j i) + 1) (rationalRectMatrixOfData X j i)

theorem costedRationalRectTranspose_data {p q : ℕ} (X : RationalRectData p q) :
    (costedRationalRectTranspose X).value = rationalRectMatrixData (rationalRectMatrixOfData X).transpose := by
  rw [costedRationalRectTranspose, costedRationalRectOfFn_data]
  rfl

theorem costedRationalRectTranspose_steps_le {p q : ℕ} (X : RationalRectData p q) (L : ℕ)
    (hX : ∀ i j, rationalMagnitudeBits (rationalRectMatrixOfData X i j) ≤ L) :
    (costedRationalRectTranspose X).steps ≤ rationalRectTraversalBudget q p (L + 1) :=
  costedRationalRectOfFn_steps_le _ _ (fun i j => Nat.add_le_add_right (hX j i) 1)

def costedRationalRectAdd {p q : ℕ} (X Y : RationalRectData p q) : Costed (RationalRectData p q) :=
  costedRationalRectOfFn fun i j => costedRatAdd (rationalRectMatrixOfData X i j) (rationalRectMatrixOfData Y i j)

def costedRationalRectSub {p q : ℕ} (X Y : RationalRectData p q) : Costed (RationalRectData p q) :=
  costedRationalRectOfFn fun i j => costedRatSub (rationalRectMatrixOfData X i j) (rationalRectMatrixOfData Y i j)

def costedRationalRectScale {p q : ℕ} (c : ℚ) (X : RationalRectData p q) : Costed (RationalRectData p q) :=
  costedRationalRectOfFn fun i j => costedRatMul c (rationalRectMatrixOfData X i j)

theorem costedRationalRectAdd_data {p q : ℕ} (X Y : RationalRectData p q) :
    (costedRationalRectAdd X Y).value = rationalRectMatrixData (rationalRectMatrixOfData X + rationalRectMatrixOfData Y) := by
  rw [costedRationalRectAdd, costedRationalRectOfFn_data]
  rfl

theorem costedRationalRectSub_data {p q : ℕ} (X Y : RationalRectData p q) :
    (costedRationalRectSub X Y).value = rationalRectMatrixData (rationalRectMatrixOfData X - rationalRectMatrixOfData Y) := by
  rw [costedRationalRectSub, costedRationalRectOfFn_data]
  rfl

theorem costedRationalRectScale_data {p q : ℕ} (c : ℚ) (X : RationalRectData p q) :
    (costedRationalRectScale c X).value = rationalRectMatrixData (c • rationalRectMatrixOfData X) := by
  rw [costedRationalRectScale, costedRationalRectOfFn_data]
  rfl

theorem costedRationalRectAdd_steps_le {p q : ℕ} (X Y : RationalRectData p q) (L : ℕ)
    (hX : ∀ i j, rationalMagnitudeBits (rationalRectMatrixOfData X i j) ≤ L)
    (hY : ∀ i j, rationalMagnitudeBits (rationalRectMatrixOfData Y i j) ≤ L) :
    (costedRationalRectAdd X Y).steps ≤ rationalRectTraversalBudget p q ((2 * L + 1) ^ 3) :=
  costedRationalRectOfFn_steps_le _ _ (fun i j => rationalArithmeticCost_le _ _ (hX i j) (hY i j))

theorem costedRationalRectSub_steps_le {p q : ℕ} (X Y : RationalRectData p q) (L : ℕ)
    (hX : ∀ i j, rationalMagnitudeBits (rationalRectMatrixOfData X i j) ≤ L)
    (hY : ∀ i j, rationalMagnitudeBits (rationalRectMatrixOfData Y i j) ≤ L) :
    (costedRationalRectSub X Y).steps ≤ rationalRectTraversalBudget p q ((2 * L + 1) ^ 3) :=
  costedRationalRectOfFn_steps_le _ _ (fun i j => rationalArithmeticCost_le _ _ (hX i j) (hY i j))

theorem costedRationalRectScale_steps_le {p q : ℕ} (c : ℚ) (X : RationalRectData p q) (L : ℕ)
    (hc : rationalMagnitudeBits c ≤ L) (hX : ∀ i j, rationalMagnitudeBits (rationalRectMatrixOfData X i j) ≤ L) :
    (costedRationalRectScale c X).steps ≤ rationalRectTraversalBudget p q ((2 * L + 1) ^ 3) :=
  costedRationalRectOfFn_steps_le _ _ (fun i j => rationalArithmeticCost_le _ _ hc (hX i j))

theorem costedRationalRectAdd_size {p q : ℕ} (X Y : RationalRectData p q) (L : ℕ)
    (hX : ∀ i j, rationalMagnitudeBits (rationalRectMatrixOfData X i j) ≤ L)
    (hY : ∀ i j, rationalMagnitudeBits (rationalRectMatrixOfData Y i j) ≤ L) (i : Fin p) (j : Fin q) :
    rationalMagnitudeBits (rationalRectMatrixOfData (costedRationalRectAdd X Y).value i j) ≤ 5 * L + 4 := by
  rw [costedRationalRectAdd_data, rationalRectMatrixOfData_data]
  exact rational_add_bits_le _ _ L (hX i j) (hY i j)

theorem costedRationalRectSub_size {p q : ℕ} (X Y : RationalRectData p q) (L : ℕ)
    (hX : ∀ i j, rationalMagnitudeBits (rationalRectMatrixOfData X i j) ≤ L)
    (hY : ∀ i j, rationalMagnitudeBits (rationalRectMatrixOfData Y i j) ≤ L) (i : Fin p) (j : Fin q) :
    rationalMagnitudeBits (rationalRectMatrixOfData (costedRationalRectSub X Y).value i j) ≤ 5 * L + 4 := by
  rw [costedRationalRectSub_data, rationalRectMatrixOfData_data]
  exact rational_sub_bits_le _ _ L (hX i j) (hY i j)

theorem costedRationalRectScale_size {p q : ℕ} (c : ℚ) (X : RationalRectData p q) (L : ℕ)
    (hc : rationalMagnitudeBits c ≤ L) (hX : ∀ i j, rationalMagnitudeBits (rationalRectMatrixOfData X i j) ≤ L) (i : Fin p) (j : Fin q) :
    rationalMagnitudeBits (rationalRectMatrixOfData (costedRationalRectScale c X).value i j) ≤ 6 * L + 3 := by
  rw [costedRationalRectScale_data, rationalRectMatrixOfData_data]
  exact rational_mul_bits_le _ _ L hc (hX i j)

def costedRationalIdentity (n : ℕ) : Costed (RationalMatrixData n) :=
  costedRationalRectOfFn fun i j => Costed.charge (n.size + 2) (if i = j then 1 else 0)

theorem costedRationalIdentity_data (n : ℕ) :
    (costedRationalIdentity n).value = rationalRectMatrixData (1 : Matrix (Fin n) (Fin n) ℚ) := by
  rw [costedRationalIdentity, costedRationalRectOfFn_data]
  rfl

theorem costedRationalIdentity_steps_le (n : ℕ) :
    (costedRationalIdentity n).steps ≤ rationalRectTraversalBudget n n (n + 2) := by
  have hn : n.size ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self
  exact costedRationalRectOfFn_steps_le _ _ (fun _ _ => Nat.add_le_add_right hn 2)

theorem costedRationalIdentity_size (n : ℕ) (i j : Fin n) :
    rationalMagnitudeBits (rationalRectMatrixOfData (costedRationalIdentity n).value i j) ≤ 3 := by
  rw [costedRationalIdentity_data, rationalRectMatrixOfData_data]
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij, rationalMagnitudeBits]

theorem polyBound_rationalRectTraversalBudget {p q L : ℕ → ℕ}
    (hp : PolynomialCostBound p) (hq : PolynomialCostBound q) (hL : PolynomialCostBound L) :
    PolynomialCostBound (fun x => rationalRectTraversalBudget (p x) (q x) (L x)) :=
  (hp.mul ((hq.mul (hL.add (PolynomialCostBound.const 3))).add (PolynomialCostBound.const 4))).add (PolynomialCostBound.const 1)

theorem polyBound_rationalRectMulBudget {p q r L : ℕ → ℕ}
    (hp : PolynomialCostBound p) (hq : PolynomialCostBound q) (hr : PolynomialCostBound r) (hL : PolynomialCostBound L) :
    PolynomialCostBound (fun x => rationalRectMulBudget (p x) (q x) (r x) (L x)) :=
  polyBound_rationalRectTraversalBudget hp hr ((hq.add (PolynomialCostBound.const 1)).add (polyBound_rationalDotBudget hq hL))

end GeometricGaussianLHL

end RationalRectCost

section RationalGramCost

/-!
## Gram matrices and the average diagonal entry

These are the repeated operations in the shaping covariance. All values are
computed from stored data, and every scalar division and matrix product is
included in the arithmetic counter.
-/

namespace GeometricGaussianLHL

theorem costedRationalRectTranspose_size {p q : ℕ} (X : RationalRectData p q) (L : ℕ)
    (hX : ∀ i j, rationalMagnitudeBits (rationalRectMatrixOfData X i j) ≤ L) (i : Fin q) (j : Fin p) :
    rationalMagnitudeBits (rationalRectMatrixOfData (costedRationalRectTranspose X).value i j) ≤ L := by
  rw [costedRationalRectTranspose_data, rationalRectMatrixOfData_data]
  exact hX j i

def costedRationalRowGram {p q : ℕ} (X : RationalRectData p q) : Costed (RationalMatrixData p) :=
  (costedRationalRectTranspose X).bind (costedRationalRectMul X)

theorem costedRationalRowGram_data {p q : ℕ} (X : RationalRectData p q) :
    (costedRationalRowGram X).value = rationalRectMatrixData
      (rationalRectMatrixOfData X * (rationalRectMatrixOfData X).transpose) := by
  rw [costedRationalRowGram, Costed.bind_value, costedRationalRectTranspose_data,
    costedRationalRectMul_data, rationalRectMatrixOfData_data]

def rationalRowGramBudget (p q L : ℕ) : ℕ := rationalRectTraversalBudget q p (L + 1) + rationalRectMulBudget p q p L

theorem costedRationalRowGram_steps_le {p q : ℕ} (X : RationalRectData p q) (L : ℕ)
    (hX : ∀ i j, rationalMagnitudeBits (rationalRectMatrixOfData X i j) ≤ L) :
    (costedRationalRowGram X).steps ≤ rationalRowGramBudget p q L :=
  Nat.add_le_add (costedRationalRectTranspose_steps_le X L hX)
    (costedRationalRectMul_steps_le X (costedRationalRectTranspose X).value L hX (costedRationalRectTranspose_size X L hX))

theorem costedRationalRowGram_size {p q : ℕ} (X : RationalRectData p q) (L : ℕ)
    (hX : ∀ i j, rationalMagnitudeBits (rationalRectMatrixOfData X i j) ≤ L) (i j : Fin p) :
    rationalMagnitudeBits (rationalMatrixOfData (costedRationalRowGram X).value i j) ≤ rationalDotOperandBudget q L := by
  rw [costedRationalRowGram, Costed.bind_value]
  exact costedRationalRectMul_size X (costedRationalRectTranspose X).value L hX (costedRationalRectTranspose_size X L hX) i j

def costedRationalTrace {n : ℕ} (D : RationalMatrixData n) : Costed ℚ :=
  (Costed.charge (n + 1) (List.ofFn (fun i => (rationalMatrixOfData D i i, (1 : ℚ))))).bind costedRationalDot

theorem costedRationalTrace_value {n : ℕ} (D : RationalMatrixData n) :
    (costedRationalTrace D).value = (rationalMatrixOfData D).trace := by
  rw [costedRationalTrace, Costed.bind_value]
  dsimp only [Costed.charge]
  rw [costedRationalDot_value]
  simp [rationalListDot, List.sum_ofFn, Matrix.trace]

def rationalTraceBudget (n L : ℕ) : ℕ := n + 1 + rationalDotBudget n (L + 3)

theorem costedRationalTrace_steps_le {n : ℕ} (D : RationalMatrixData n) (L : ℕ)
    (hD : ∀ i j, rationalMagnitudeBits (rationalMatrixOfData D i j) ≤ L) :
    (costedRationalTrace D).steps ≤ rationalTraceBudget n L := by
  have h := costedRationalDot_steps_le (List.ofFn (fun i => (rationalMatrixOfData D i i, (1 : ℚ)))) (L + 3) (by
    intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    refine ⟨(hD i i).trans (by omega), ?_⟩
    have h₁ : rationalMagnitudeBits (1 : ℚ) = 3 := by decide
    rw [h₁]; omega)
  simpa only [costedRationalTrace, Costed.bind_steps, Costed.charge, List.length_ofFn, rationalTraceBudget] using Nat.add_le_add_left h (n + 1)

theorem costedRationalTrace_size {n : ℕ} (D : RationalMatrixData n) (L : ℕ)
    (hD : ∀ i j, rationalMagnitudeBits (rationalMatrixOfData D i j) ≤ L) :
    rationalMagnitudeBits (costedRationalTrace D).value ≤ rationalDotOperandBudget n (L + 3) := by
  have h := rationalListDot_bits (List.ofFn (fun i => (rationalMatrixOfData D i i, (1 : ℚ)))) (L + 3) (by
    intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    refine ⟨(hD i i).trans (by omega), ?_⟩
    have h₁ : rationalMagnitudeBits (1 : ℚ) = 3 := by decide
    rw [h₁]; omega)
  simpa only [costedRationalTrace, Costed.bind_value, Costed.charge, costedRationalDot_value, List.length_ofFn] using h

def costedRationalTraceMean {n : ℕ} (D : RationalMatrixData n) : Costed ℚ :=
  (costedRationalTrace D).bind fun z =>
    (Costed.charge (n.size + 1) (n : ℚ)).bind (fun d => costedRatDiv z d)

theorem costedRationalTraceMean_value {n : ℕ} (D : RationalMatrixData n) :
    (costedRationalTraceMean D).value = (rationalMatrixOfData D).trace / n := by
  rw [costedRationalTraceMean, Costed.bind_value, costedRationalTrace_value, Costed.bind_value]
  rfl

def rationalTraceMeanOperandBudget (n L : ℕ) : ℕ := rationalDotOperandBudget n (L + 3) + n + 2
def rationalTraceMeanBudget (n L : ℕ) : ℕ := rationalTraceBudget n L + n + 1 + (2 * rationalTraceMeanOperandBudget n L + 1) ^ 3

theorem costedRationalTraceMean_steps_le {n : ℕ} (D : RationalMatrixData n) (L : ℕ)
    (hD : ∀ i j, rationalMagnitudeBits (rationalMatrixOfData D i j) ≤ L) :
    (costedRationalTraceMean D).steps ≤ rationalTraceMeanBudget n L := by
  have ht := costedRationalTrace_steps_le D L hD
  have hs := costedRationalTrace_size D L hD
  have hn : n.size ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self
  have hnc : rationalMagnitudeBits (n : ℚ) ≤ n + 2 := by
    simpa using (intCast_rational_bits (n : ℤ)).le.trans (Nat.add_le_add_right hn 2)
  have hdiv := rationalArithmeticCost_le (costedRationalTrace D).value (n : ℚ)
    (hs.trans (show _ ≤ rationalTraceMeanOperandBudget n L by unfold rationalTraceMeanOperandBudget; omega))
    (hnc.trans (show _ ≤ rationalTraceMeanOperandBudget n L by unfold rationalTraceMeanOperandBudget; omega))
  rw [costedRationalTraceMean, Costed.bind_steps, Costed.bind_steps]
  change (costedRationalTrace D).steps + (n.size + 1 + rationalArithmeticCost (costedRationalTrace D).value (n : ℚ)) ≤ _
  unfold rationalTraceMeanBudget
  omega

theorem costedRationalTraceMean_size {n : ℕ} (D : RationalMatrixData n) (L : ℕ)
    (hD : ∀ i j, rationalMagnitudeBits (rationalMatrixOfData D i j) ≤ L) :
    rationalMagnitudeBits (costedRationalTraceMean D).value ≤ 6 * rationalTraceMeanOperandBudget n L + 3 := by
  have hs := costedRationalTrace_size D L hD
  have hn : n.size ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self
  have hnc : rationalMagnitudeBits (n : ℚ) ≤ n + 2 := by
    simpa using (intCast_rational_bits (n : ℤ)).le.trans (Nat.add_le_add_right hn 2)
  rw [costedRationalTraceMean, Costed.bind_value, Costed.bind_value]
  exact rational_div_bits_le _ _ (rationalTraceMeanOperandBudget n L)
    (hs.trans (by unfold rationalTraceMeanOperandBudget; omega)) (hnc.trans (by unfold rationalTraceMeanOperandBudget; omega))

theorem polyBound_rationalRowGramBudget {p q L : ℕ → ℕ}
    (hp : PolynomialCostBound p) (hq : PolynomialCostBound q) (hL : PolynomialCostBound L) :
    PolynomialCostBound (fun x => rationalRowGramBudget (p x) (q x) (L x)) :=
  (polyBound_rationalRectTraversalBudget hq hp (hL.add (PolynomialCostBound.const 1))).add (polyBound_rationalRectMulBudget hp hq hp hL)

theorem polyBound_rationalTraceMeanOperandBudget {n L : ℕ → ℕ}
    (hn : PolynomialCostBound n) (hL : PolynomialCostBound L) :
    PolynomialCostBound (fun x => rationalTraceMeanOperandBudget (n x) (L x)) :=
  ((polyBound_rationalDotOperandBudget hn (hL.add (PolynomialCostBound.const 3))).add hn).add (PolynomialCostBound.const 2)

theorem polyBound_rationalTraceMeanBudget {n L : ℕ → ℕ}
    (hn : PolynomialCostBound n) (hL : PolynomialCostBound L) :
    PolynomialCostBound (fun x => rationalTraceMeanBudget (n x) (L x)) :=
  ((((hn.add (PolynomialCostBound.const 1)).add (polyBound_rationalDotBudget hn (hL.add (PolynomialCostBound.const 3)))).add hn).add
    (PolynomialCostBound.const 1)).add ((((PolynomialCostBound.const 2).mul
      (polyBound_rationalTraceMeanOperandBudget hn hL)).add (PolynomialCostBound.const 1)).pow 3)

end GeometricGaussianLHL

end RationalGramCost
