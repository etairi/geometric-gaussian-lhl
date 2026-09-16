import «SIS-to-kSIS».HintIndependence
import «SIS-to-kSIS».UniformSimulation
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Uniform public matrices over residue fields

Surjective additive maps preserve the uniform law. Counting finite-dimensional
spans bounds rank failure in each residue field; a union bound then applies to
the actual public matrix over the original quotient ring.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Module NumberField MeasureTheory GeometricGaussianLHL
open scoped ENNReal

namespace SISToKSIS

theorem uniform_span_mass {F : Type*} [Field F] [Fintype F]
    {m r : ℕ} (v : Fin r → (Fin m → F)) :
    (PMF.uniformOfFintype (Fin m → F)).toOuterMeasure
      (Submodule.span F (Set.range v)) ≤
      (Fintype.card F : ℝ≥0∞) ^ r / (Fintype.card F : ℝ≥0∞) ^ m := by
  classical
  rw [PMF.toOuterMeasure_uniformOfFintype_apply]
  have hr : Module.finrank F (Submodule.span F (Set.range v)) ≤ r := by
    simpa only [Set.finrank, Fintype.card_fin] using (finrank_range_le_card (R := F) v)
  have hc : Fintype.card (Submodule.span F (Set.range v)) ≤ Fintype.card F ^ r := by
    rw [Module.card_eq_pow_finrank (K := F)]
    exact Nat.pow_le_pow_right (Fintype.card_pos) hr
  simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
  exact ENNReal.div_le_div_right (by exact_mod_cast hc) _

theorem independentProduct_uniform {α : Type*} [Fintype α] [Nonempty α] (k : ℕ) :
    independentProduct (fun _ : Fin k => PMF.uniformOfFintype α) =
      PMF.uniformOfFintype (Fin k → α) := by
  ext x
  simp [independentProduct_apply, ENNReal.inv_pow]

theorem uniform_linearIndependent_failure {F : Type*} [Field F] [Fintype F]
    (m k : ℕ) :
    (PMF.uniformOfFintype (Fin k → Fin m → F)).toOuterMeasure
      {v | ¬ LinearIndependent F v} ≤
      ENNReal.ofReal ((k : ℝ) * (Fintype.card F : ℝ) ^ (k - 1) /
        (Fintype.card F : ℝ) ^ m) := by
  let δ := (Fintype.card F : ℝ) ^ (k - 1) / (Fintype.card F : ℝ) ^ m
  have hδ : 0 ≤ δ := by positivity
  have h := independentProduct_linearIndependent_failure (id : (Fin m → F) → _)
    hδ k (fun _ => PMF.uniformOfFintype (Fin m → F)) (by
      intro i r hr v
      have hQ : 1 ≤ (Fintype.card F : ℝ≥0∞) := by
        exact_mod_cast Fintype.card_pos (α := F)
      have hbase := uniform_span_mass v
      have hle := ENNReal.div_le_div_right
        (pow_le_pow_right₀ hQ (show r ≤ k - 1 by omega)) ((Fintype.card F : ℝ≥0∞) ^ m)
      apply hbase.trans
      simpa only [δ, ENNReal.ofReal_div_of_pos (by positivity : 0 < (Fintype.card F : ℝ) ^ m),
        ENNReal.ofReal_pow (Nat.cast_nonneg _), ENNReal.ofReal_natCast] using hle)
  rw [independentProduct_uniform] at h
  simpa only [id_eq, δ, mul_div_assoc] using h

theorem uniform_linearIndependent_failure_codimension {F : Type*} [Field F] [Fintype F]
    {m k : ℕ} (hkm : k ≤ m) :
    (PMF.uniformOfFintype (Fin k → Fin m → F)).toOuterMeasure
      {v | ¬ LinearIndependent F v} ≤
      ENNReal.ofReal ((k : ℝ) / (Fintype.card F : ℝ) ^ (m - k + 1)) := by
  have h := uniform_linearIndependent_failure (F := F) m k
  by_cases hk : k = 0
  · simpa only [hk, Nat.cast_zero, zero_mul, zero_div] using h
  have hQ : (Fintype.card F : ℝ) ≠ 0 := by positivity
  have he : (Fintype.card F : ℝ) ^ (k - 1) / (Fintype.card F : ℝ) ^ m =
      1 / (Fintype.card F : ℝ) ^ (m - k + 1) := by
    rw [show m - k + 1 = m - (k - 1) by omega, pow_sub₀ _ hQ (by omega)]
    field_simp
    rw [← pow_add, ← pow_succ']
    congr 1
    omega
  simpa only [mul_div_assoc, he, mul_one_div] using h

theorem uniform_quotient_rows_failure {R F : Type*} [AddGroup R] [Field F]
    [Fintype R] [Fintype F] (f : R →+ F) (hf : Function.Surjective f)
    {m n : ℕ} (hnm : n ≤ m) :
    (PMF.uniformOfFintype (Matrix (Fin n) (Fin m) R)).toOuterMeasure
      {A | ¬ LinearIndependent F (fun i j => f (A i j))} ≤
      ENNReal.ofReal ((n : ℝ) / (Fintype.card F : ℝ) ^ (m - n + 1)) := by
  let fRows := coordinateAddHom (ι := Fin n) (coordinateAddHom (ι := Fin m) f)
  have hsurj : Function.Surjective fRows :=
    coordinateAddHom_surjective _ (coordinateAddHom_surjective f hf)
  have hu := uniform_map_surjective_addHom fRows hsurj
  have h := uniform_linearIndependent_failure_codimension (F := F) hnm
  rw [← hu, PMF.toOuterMeasure_map_apply] at h
  exact h

theorem matrix_leftInverse_of_independent_columns {F : Type*} [Field F] {m k : ℕ}
    (H : Matrix (Fin m) (Fin k) F) (hH : LinearIndependent F H.col) :
    ∃ L : Matrix (Fin k) (Fin m) F, L * H = 1 := by
  have hinj : LinearMap.ker H.mulVecLin = ⊥ :=
    LinearMap.ker_eq_bot.mpr (Matrix.mulVec_injective_iff.mpr hH)
  obtain ⟨l, hl⟩ := H.mulVecLin.exists_leftInverse_of_injective hinj
  refine ⟨l.toMatrix', ?_⟩
  have h := congrArg LinearMap.toMatrix' hl
  change LinearMap.toMatrix' (l.comp H.toLin') = _ at h
  simpa only [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id,
    LinearMap.toMatrix'_toLin'] using h

def matrixInFactor {R ι : Type*} {F : ι → Type*} [CommRing R] [∀ j, CommRing (F j)]
    {m k : ℕ} (e : R ≃+* ∀ j, F j) (H : Matrix (Fin m) (Fin k) R) (j : ι) :
    Matrix (Fin m) (Fin k) (F j) := fun a b => e (H a b) j

/-- Inverses are chosen separately in the fields and assembled entrywise.
No common invertible row minor is required. -/
theorem matrix_leftInverse_of_factorwise_independent {R ι : Type*} {F : ι → Type*}
    [CommRing R] [∀ j, Field (F j)] {m k : ℕ} (e : R ≃+* ∀ j, F j)
    (H : Matrix (Fin m) (Fin k) R)
    (hH : ∀ j, LinearIndependent (F j) (matrixInFactor e H j).col) :
    ∃ L : Matrix (Fin k) (Fin m) R, L * H = 1 := by
  choose L hL using fun j => matrix_leftInverse_of_independent_columns (matrixInFactor e H j) (hH j)
  let C : Matrix (Fin k) (Fin m) R := fun a b => e.symm (fun j => L j a b)
  refine ⟨C, ?_⟩
  ext a b
  apply e.injective
  funext j
  have hj := congrArg (fun M : Matrix (Fin k) (Fin k) (F j) => M a b) (hL j)
  by_cases hab : a = b <;>
    simpa [Matrix.mul_apply, matrixInFactor, C, Matrix.one_apply, hab] using hj

section Quotients
variable {R : Type*} [CommRing R] {g m k : ℕ}

local instance crtResidueField (I : Ideal R) [I.IsMaximal] : Field (R ⧸ I) :=
  Ideal.Quotient.field I

/-- Factorwise column independence gives a left inverse over the full quotient. -/
theorem quotient_matrix_leftInverse (J : Ideal R) (I : Fin g → Ideal R)
    [∀ j, (I j).IsMaximal] (hI : Function.Injective I) (hfac : J = ∏ j, I j)
    (H : Matrix (Fin m) (Fin k) R)
    (hH : ∀ j, LinearIndependent (R ⧸ I j) (H.map (Ideal.Quotient.mk (I j))).col) :
    ∃ L : Matrix (Fin k) (Fin m) (R ⧸ J), L * H.map (Ideal.Quotient.mk J) = 1 := by
  have hp : Pairwise (fun a b => IsCoprime (I a) (I b)) :=
    fun a b hab => Ideal.isCoprime_of_isMaximal (hI.ne hab)
  have hJI : J = ⨅ j, I j := by
    rw [hfac, Ideal.prod_eq_iInf_of_pairwise_isCoprime]
    · simp
    · intro a _ b _ hab
      exact hp hab
  let e : (R ⧸ J) ≃+* ∀ j, R ⧸ I j :=
    (Ideal.quotEquivOfEq hJI).trans (Ideal.quotientInfRingEquivPiQuotient I hp)
  have he (x : R) (j : Fin g) : e (Ideal.Quotient.mk J x) j = Ideal.Quotient.mk (I j) x := by
    change (Ideal.quotientInfRingEquivPiQuotient I hp)
      (Ideal.quotEquivOfEq hJI (Ideal.Quotient.mk J x)) j = _
    rw [Ideal.quotEquivOfEq_mk]
    rfl
  apply matrix_leftInverse_of_factorwise_independent e (H.map (Ideal.Quotient.mk J))
  intro j
  have hM : matrixInFactor e (H.map (Ideal.Quotient.mk J)) j =
      H.map (Ideal.Quotient.mk (I j)) := by
    ext a b
    exact he (H a b) j
  rw [hM]
  exact hH j

end Quotients
section NumberFields
variable (K : Type*) [Field K] [NumberField K]

local instance publicResidueField (I : Ideal (𝓞 K)) [I.IsMaximal] :
    Field ((𝓞 K) ⧸ I) := Ideal.Quotient.field I

def primeResidueMap (q : ℕ) (I : Ideal (𝓞 K)) (hqI : (q : 𝓞 K) ∈ I) :
    ResidueRing K q →+* (𝓞 K) ⧸ I :=
  Ideal.Quotient.factor (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hqI))

omit [NumberField K] in
theorem primeResidueMap_surjective (q : ℕ) (I : Ideal (𝓞 K)) (hqI : (q : 𝓞 K) ∈ I) :
    Function.Surjective (primeResidueMap K q I hqI) := Ideal.Quotient.factor_surjective _

theorem uniform_prime_rows_failure (q : ℕ) [NeZero q]
    (I : Ideal (𝓞 K)) [I.IsMaximal] (hqI : (q : 𝓞 K) ∈ I)
    {m n : ℕ} (hnm : n ≤ m) :
    (PMF.uniformOfFintype (Matrix (Fin n) (Fin m) (ResidueRing K q))).toOuterMeasure
      {A | ¬ LinearIndependent ((𝓞 K) ⧸ I) (fun i j => primeResidueMap K q I hqI (A i j))} ≤
      ENNReal.ofReal ((n : ℝ) / (Ideal.absNorm I : ℝ) ^ (m - n + 1)) := by
  let f := primeResidueMap K q I hqI
  have hf : Function.Surjective f := primeResidueMap_surjective K q I hqI
  let : Finite ((𝓞 K) ⧸ I) := Finite.of_surjective f hf
  let : Fintype ((𝓞 K) ⧸ I) := Fintype.ofFinite _
  have hc : Fintype.card ((𝓞 K) ⧸ I) = Ideal.absNorm I :=
    Nat.card_eq_fintype_card.symm
  have h := uniform_quotient_rows_failure f.toAddMonoidHom hf hnm
  rw [hc] at h
  convert h using 1 <;> rfl

def independentPublicAtPrimes {g m n : ℕ} (q : ℕ) (I : Fin g → Ideal (𝓞 K))
    [∀ j, (I j).IsMaximal] (hqI : ∀ j, (q : 𝓞 K) ∈ I j)
    (A : Matrix (Fin n) (Fin m) (ResidueRing K q)) : Prop :=
  ∀ j, LinearIndependent ((𝓞 K) ⧸ I j)
    (fun a b => primeResidueMap K q (I j) (hqI j) (A a b))

/-- The rank-failure estimate for the actual uniform public matrix. Distinctness
of the ideals is unnecessary for this union bound. -/
theorem uniform_public_independence {g m n N : ℕ} (q : ℕ) [NeZero q]
    (I : Fin g → Ideal (𝓞 K)) [∀ j, (I j).IsMaximal]
    (hqI : ∀ j, (q : 𝓞 K) ∈ I j) (hNorm : ∀ j, Ideal.absNorm (I j) = N)
    (hnm : n ≤ m) :
    (PMF.uniformOfFintype (Matrix (Fin n) (Fin m) (ResidueRing K q))).toOuterMeasure
      {A | ¬ independentPublicAtPrimes K q I hqI A} ≤
      ENNReal.ofReal ((g : ℝ) * n / (N : ℝ) ^ (m - n + 1)) := by
  let p := PMF.uniformOfFintype (Matrix (Fin n) (Fin m) (ResidueRing K q))
  let δ := (n : ℝ) / (N : ℝ) ^ (m - n + 1)
  have hδ : 0 ≤ δ := by positivity
  have hEach (j : Fin g) : p.toOuterMeasure
      {A | ¬ LinearIndependent ((𝓞 K) ⧸ I j)
        (fun a b => primeResidueMap K q (I j) (hqI j) (A a b))} ≤ ENNReal.ofReal δ := by
    simpa only [hNorm j] using uniform_prime_rows_failure K q (I j) (hqI j) hnm
  have hEvent : {A : Matrix (Fin n) (Fin m) (ResidueRing K q) |
      ¬ independentPublicAtPrimes K q I hqI A} =
      ⋃ j : Fin g, {A | ¬ LinearIndependent ((𝓞 K) ⧸ I j)
        (fun a b => primeResidueMap K q (I j) (hqI j) (A a b))} := by
    ext A
    simp only [independentPublicAtPrimes, Set.mem_ofPred_eq, Set.mem_iUnion, not_forall]
  rw [hEvent]
  apply (measure_iUnion_fintype_le p.toOuterMeasure _).trans
  apply (Finset.sum_le_sum (fun j _ => hEach j)).trans
  rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => hδ)]
  apply ENNReal.ofReal_le_ofReal
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, δ]
  exact le_of_eq (by ring)

/-- Independence in the prime factors supplies the actual modular left inverse. -/
theorem independentHintsAtPrimes_leftInverse {g m k : ℕ} (q : ℕ)
    (I : Fin g → Ideal (𝓞 K)) [∀ j, (I j).IsMaximal]
    (hI : Function.Injective I)
    (hfac : Ideal.span ({(q : 𝓞 K)} : Set (𝓞 K)) = ∏ j, I j)
    (H : Matrix (Fin (m + k)) (Fin k) (𝓞 K)) (hH : independentHintsAtPrimes K I H) :
    ∃ L : Matrix (Fin k) (Fin (m + k)) (ResidueRing K q),
      L * H.map (residueMap K q) = 1 := by
  exact quotient_matrix_leftInverse _ I hI hfac H (fun j => hH j)

/-- The compatibility denominator in reverse sampling, proved for actual
integral hints independent in every prime residue field. -/
theorem uniform_prime_hint_compatibility {d g m n k : ℕ} (b : Basis (Fin d) ℤ (𝓞 K))
    (q : ℕ) [NeZero q] (I : Fin g → Ideal (𝓞 K)) [∀ j, (I j).IsMaximal]
    (hI : Function.Injective I)
    (hfac : Ideal.span ({(q : 𝓞 K)} : Set (𝓞 K)) = ∏ j, I j)
    (H : Matrix (Fin (m + k)) (Fin k) (𝓞 K)) (hH : independentHintsAtPrimes K I H)
    (V : Matrix (Fin n) (Fin k) (ResidueRing K q)) :
    (PMF.uniformOfFintype (Matrix (Fin n) (Fin (m + k)) (ResidueRing K q))).toOuterMeasure
      {A | A * H.map (residueMap K q) = V} =
      ((q : ℝ≥0∞) ^ (d * (k * n)))⁻¹ := by
  obtain ⟨L, hL⟩ := independentHintsAtPrimes_leftInverse K q I hI hfac H hH
  have hc : Fintype.card (ResidueRing K q) = q ^ d := by
    rw [← Nat.card_eq_fintype_card, residueRing_card K b]
  simpa only [hc, Nat.cast_pow, ← pow_mul] using
    uniform_compatibility_probability (H.map (residueMap K q)) L hL V

end NumberFields
end SISToKSIS
