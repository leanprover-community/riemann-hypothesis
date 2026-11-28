module

public import Aesop.BuiltinRules
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.IsAdjoinRoot
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.TotallySplit
import TauCeti.NumberTheory.NumberField.ComplexConjugation.MaximalRealOrCMSubfield
public import Lib.Adelic.Adeles.Basic
import Lib.Adelic.Adeles.IdeleModulus
import Lib.Adelic.Adeles.StrongApproximation

/-!
# Criteria for CM fields

An intermediate field between a totally complex field and a CM field is CM. A number field is
also CM if it contains a totally complex field and a map of the field to itself induces
conjugation under every complex embedding. This criterion applies to adjoining a root of a
suitable polynomial to a CM field. The file also describes the finite adeles of the resulting field.

We write `𝔸f K` for the ring of finite adeles of a number field `K`. For an extension `L / K` of
number fields, `𝔸f L` is an algebra over `𝔸f K`, and complex conjugation `star` of a CM field
extends to its finite adeles.

## Main definitions and results

* `New.isCMField_intermediateField`: an intermediate field of an extension of CM fields is CM.
* `New.isCMField_of_forall_exists_conj`: a number field is CM if it contains a totally complex field
  and complex conjugation is induced, in all embeddings at once, by a map of the field to itself.
* `New.isCMField_adjoinRoot_of_forall_root_mul_star_eq`: let `E` be a CM field and `P` an
  irreducible polynomial over `E`. If all complex roots of `P` have the same rational square
  absolute value `ν`, then `L = E[X]/(P)` is again CM.
* `New.aeval_root_finAdele_surjective`, `New.aeval_root_finAdele_eq_zero_iff`: for monic `P`, the
  finite adeles `𝔸f L` are obtained from `𝔸f E` by adjoining a root of `P`.
* `New.IsFinAdelePresentation`: a map from polynomials over `𝔸f E` presents `𝔸f L` as the quotient
  by `P`, compatibly with `E[X] → L` and with complex conjugation.
* `New.adjoinRoot_cm_presentation`: these facts about `L` and `𝔸f L` in one statement.
-/

@[expose] public section

/-! ## Intermediate fields of CM extensions -/

open NumberField in
/-- Every intermediate field between a totally complex field and a CM number field is CM. -/
lemma New.isCMField_intermediateField {E L : Type*} [Field E] [NumberField E] [IsTotallyComplex E]
    [Field L] [NumberField L] [IsCMField L] [Algebra E L] (K : IntermediateField E L) :
    IsCMField K := by
  have h_complex : IsTotallyComplex K := isTotallyComplex_of_algebra E K
  have h_le : K.toSubfield ≤ TauCeti.NumberField.maximalRealOrCMSubfield L := by
    rw [TauCeti.NumberField.maximalRealOrCMSubfield_eq_top_of_isCMField]
    exact le_top
  obtain h_real | h_cm := TauCeti.NumberField.le_maximalRealOrCMSubfield_iff.mp h_le
  · exact (IsTotallyComplex.not_isTotallyReal (K := K) h_real).elim
  · exact h_cm

/-! ## A CM criterion via a conjugation on the field -/

section CMCriterion

open NumberField InfinitePlace Module Fintype

/-- Let L be a number field extending a totally complex field E. If every x ∈ L has a y ∈ L with
φ(y) equal to the complex conjugate of φ(x) for all embeddings φ : L → ℂ, then L is a CM
field. -/
lemma New.isCMField_of_forall_exists_conj (E : Type*) {L : Type*} [Field E] [IsTotallyComplex E]
    [Field L] [Algebra E L] [NumberField L]
    (h_conj : ∀ x : L, ∃ y : L, ∀ φ : L →+* ℂ, φ y = star (φ x)) :
    IsCMField L := by
  have : IsTotallyComplex L := isTotallyComplex_of_algebra E L
  -- Places of `L` are determined by their restriction to `maximalRealSubfield L`.
  have h_card : card (InfinitePlace L) = card (InfinitePlace (maximalRealSubfield L)) :=
    card_of_bijective ⟨fun v w hvw ↦ ext v w fun x ↦ by
      obtain ⟨y, hy⟩ := h_conj x
      have h_eq : v (x * y) = w (x * y) :=
        DFunLike.congr_fun hvw ⟨x * y, fun φ ↦ by simp [hy φ, mul_comm]⟩
      simpa [← norm_embedding_eq, hy, ← sq] using h_eq, comap_surjective⟩
  exact { is_quadratic := ⟨by
    simpa [← sum_mult_eq, h_card] using finrank_mul_finrank ℚ (maximalRealSubfield L) L⟩ }

end CMCriterion

/-! ## CM fields obtained by adjoining a root, and their finite adeles -/

section CMAdjoinRoot

open NumberField Polynomial AdjoinRoot Algebra ComplexConjugate

namespace New

variable {E : Type*} [Field E] [NumberField E] {P : E[X]} [Fact (Irreducible P)]

/-- Adjoining a root of an irreducible polynomial to a number field `E` gives a number field. -/
instance : NumberField (AdjoinRoot P) :=
  have : Module.Finite E (AdjoinRoot P) := (powerBasis (Fact.out : Irreducible P).ne_zero).finite
  of_module_finite E (AdjoinRoot P)

omit [NumberField E] in
/-- If all complex roots of the irreducible polynomial `P`, under all embeddings of `E`, satisfy
`r * star r = ν`, then so does the image of the root of `P` under every embedding of
`E[X]/(P)`. -/
lemma adjoinRoot_embedding_root_mul_star {ν : ℚ}
    (hν : ∀ σ : E →+* ℂ, ∀ r ∈ (P.map σ).roots, r * star r = (ν : ℂ))
    (φ : AdjoinRoot P →+* ℂ) : φ (root P) * star (φ (root P)) = ν :=
  hν (φ.comp (of P)) (φ (root P))
    (by simp [← map_map, (Fact.out : Irreducible P).ne_zero, eval_map])

/-- If all complex roots of the irreducible polynomial `P` over the CM field `E` have the same
rational square absolute value `ν`, then `E[X]/(P)` is a CM field. -/
lemma isCMField_adjoinRoot_of_forall_root_mul_star_eq [IsCMField E] {ν : ℚ}
    (hν : ∀ σ : E →+* ℂ, ∀ r ∈ (P.map σ).roots, r * star r = (ν : ℂ)) :
    IsCMField (AdjoinRoot P) := by
  -- The conjugate of `q (root P)` under every embedding is the image of `q̄ (ν / root P)`.
  refine isCMField_of_forall_exists_conj E fun x ↦ ?_
  induction x using AdjoinRoot.induction_on with | ih q => ?_
  refine ⟨(q.map conj).aeval (ν / root P), fun φ ↦ ?_⟩
  have h_coeff (a : E) : φ (of P (conj a)) = conj (φ (of P a)) :=
    map_star_complex (φ.comp (of P)) a
  have h_mul : φ (root P) * conj (φ (root P)) = ν := adjoinRoot_embedding_root_mul_star hν φ
  have h_root : ν / φ (root P) = conj (φ (root P)) := by
    rcases eq_or_ne (φ (root P)) 0 with h_zero | h_ne
    · simp [h_zero]
    · rw [← h_mul, mul_div_cancel_left₀ _ h_ne]
  -- Both sides are sums over the coefficients of `q` times powers of the root.
  simp [← aeval_eq, aeval_eq_sum_range, smul_def, h_coeff, h_root]

/-- If all complex roots of the irreducible polynomial `P` have the rational square absolute value
`ν`, then the root of `P` in the CM field `E[X]/(P)` times its conjugate is `ν`. -/
lemma adjoinRoot_root_mul_star [IsCMField (AdjoinRoot P)] {ν : ℚ}
    (hν : ∀ σ : E →+* ℂ, ∀ r ∈ (P.map σ).roots, r * star r = (ν : ℂ)) :
    root P * star (root P) = ν := by
  refine canonicalEmbedding_injective (AdjoinRoot P) (funext fun φ ↦ ?_)
  simpa [map_star_complex] using adjoinRoot_embedding_root_mul_star hν φ

/-- At the root of `P`, a polynomial over `E` takes the same value whether it is evaluated in
`E[X]/(P)` or in the finite adeles of this field. -/
lemma aeval_root_finAdele_map (q : E[X]) :
    aeval (root P : 𝔸f (AdjoinRoot P)) (q.map (algebraMap E (𝔸f E))) =
      (AdjoinRoot.mk P q : 𝔸f (AdjoinRoot P)) := by
  simp [← aeval_eq, aeval_eq_sum_range, smul_def, algebraMap_eq_finAdeleIncl]

/-- For a monic irreducible `P`, the powers of its root below the degree of `P` are a basis of the
finite adeles of `E[X]/(P)` over those of `E`. -/
noncomputable def adjoinRootAdelePowerBasis (hP : P.Monic) :
    PowerBasis (𝔸f E) (𝔸f (AdjoinRoot P)) where
  gen := (root P : 𝔸f (AdjoinRoot P))
  dim := (powerBasis' hP).dim
  basis := adeleBasis (powerBasis' hP).basis
  basis_eq_pow := by simp [adeleBasis]

/-- For a monic irreducible `P`, every finite adele of `E[X]/(P)` is the value at the root of `P` of
a polynomial over the finite adeles of `E`. -/
lemma aeval_root_finAdele_surjective (hP : P.Monic) :
    Function.Surjective (aeval (R := 𝔸f E) (root P : 𝔸f (AdjoinRoot P))) := by
  rw [← AlgHom.range_eq_top, ← adjoin_singleton_eq_range_aeval]
  exact (adjoinRootAdelePowerBasis hP).adjoin_gen_eq_top

/-- A polynomial over the finite adeles of `E` vanishes at the root of a monic irreducible `P` in
the finite adeles of `E[X]/(P)` exactly when `P` divides it. -/
lemma aeval_root_finAdele_eq_zero_iff (hP : P.Monic) (q : (𝔸f E)[X]) :
    aeval (root P : 𝔸f (AdjoinRoot P)) q = 0 ↔ P.map (algebraMap E (𝔸f E)) ∣ q := by
  -- Both the minimal polynomial of the root and the image of `P` are monic of the same degree, and
  -- the first divides the second.
  let B : PowerBasis (𝔸f E) (𝔸f (AdjoinRoot P)) := adjoinRootAdelePowerBasis hP
  let A : IsAdjoinRootMonic (𝔸f (AdjoinRoot P)) (minpoly (𝔸f E) B.gen) :=
    IsAdjoinRootMonic.mkOfAdjoinEqTop' B.adjoin_gen_eq_top
  have h_aeval : aeval B.gen (P.map (algebraMap E (𝔸f E))) = 0 := by
    simp [B, adjoinRootAdelePowerBasis, aeval_root_finAdele_map]
  have minpoly_eq : P.map (algebraMap E (𝔸f E)) = minpoly (𝔸f E) B.gen := by
    refine eq_of_monic_of_dvd_of_natDegree_le A.monic (hP.map _) (A.mem_ker_map.1 h_aeval) ?_
    rw [hP.natDegree_map, B.natDegree_minpoly]
    exact (powerBasis'_dim hP).ge
  rw [minpoly_eq]
  -- The evaluation map of `A` is `aeval B.gen` by definition.
  exact (A.mem_ker_map : A.map q = 0 ↔ minpoly (𝔸f E) B.gen ∣ q)

variable [IsCMField E]

/-- Let `star` and `conj` be complex conjugation, extended to finite adeles. If `c` represents the
conjugate of the root of `P` in the CM field `E[X]/(P)`, then conjugating the coefficients of a
polynomial over `𝔸f E` and substituting `c` for `X` conjugates its value at the root, seen as a
finite adele of `E[X]/(P)`. -/
lemma aeval_root_finAdele_map_conj_comp [IsCMField (AdjoinRoot P)] {c : E[X]}
    (hc : AdjoinRoot.mk P c = star (root P)) (q : (𝔸f E)[X]) :
    aeval (root P : 𝔸f (AdjoinRoot P)) ((q.map conj).comp (c.map (algebraMap E (𝔸f E)))) =
      star (aeval (root P : 𝔸f (AdjoinRoot P)) q) := by
  have h_star : aeval (root P : 𝔸f (AdjoinRoot P)) (c.map (algebraMap E (𝔸f E))) =
      star (root P : 𝔸f (AdjoinRoot P)) := by
    rw [aeval_root_finAdele_map, hc, star_algebraMap_finAdele]
  have h_incl : algebraMap (𝔸f E) (𝔸f (AdjoinRoot P)) = adeleMap (of P) :=
    algebraMap_eq_finAdeleIncl
  induction q using Polynomial.induction_on' with
  | add p r hp hr => simp [hp, hr]
  | monomial n a => simp [h_star, h_incl, ← adeleMap_star, starRingEnd_apply]

/-- Let `L = E[X]/(P)` be a CM field. An algebra map `ε` from the polynomials over the finite adeles
`𝔸f E` to `𝔸f L` presents `𝔸f L` as `(𝔸f E)[X]/(P)`, compatibly with `E[X] → L` and with complex
conjugation. -/
structure IsFinAdelePresentation (P : E[X]) [Fact (Irreducible P)] [IsCMField (AdjoinRoot P)]
    (ε : (𝔸f E)[X] →ₐ[𝔸f E] 𝔸f (AdjoinRoot P)) : Prop where
  /-- Every finite adele of `L` is a value of `ε`. -/
  surjective : Function.Surjective ε
  /-- The kernel of `ε` consists of the multiples of `P`. -/
  eq_zero_iff (q : (𝔸f E)[X]) : ε q = 0 ↔ P.map (algebraMap E (𝔸f E)) ∣ q
  /-- On polynomials over `E`, the map `ε` agrees with `E[X] → L`. -/
  apply_map (q : E[X]) : ε (q.map (algebraMap E (𝔸f E))) = AdjoinRoot.mk P q
  /-- If `c` represents the conjugate of the root of `P`, then conjugating the coefficients of `q`
  and substituting `c` for `X` conjugates `ε q`. -/
  apply_map_conj_comp {c : E[X]} (hc : AdjoinRoot.mk P c = star (root P)) (q : (𝔸f E)[X]) :
    ε ((q.map conj).comp (c.map (algebraMap E (𝔸f E)))) = star (ε q)

/-- Let `P` be a monic irreducible polynomial over the CM field `E` such that every complex root `r`
of `P`, under every embedding of `E`, satisfies `r * star r = ν` for a fixed rational `ν`. Then
`L = E[X]/(P)` is a CM field, the root of `P` in `L` times its conjugate is `ν`, and evaluation at
the root presents the finite adeles of `L` as the polynomials over `𝔸f E` modulo `P`, compatibly
with `E[X] → L` and with complex conjugation. -/
lemma adjoinRoot_cm_presentation (hP : P.Monic) {ν : ℚ}
    (hν : ∀ σ : E →+* ℂ, ∀ r ∈ (P.map σ).roots, r * star r = (ν : ℂ)) :
    ∃ _ : IsCMField (AdjoinRoot P),
      root P * star (root P) = ν ∧
      IsFinAdelePresentation P (aeval (root P : 𝔸f (AdjoinRoot P))) := by
  have cm : IsCMField (AdjoinRoot P) := isCMField_adjoinRoot_of_forall_root_mul_star_eq hν
  exact ⟨cm, adjoinRoot_root_mul_star hν,
    { surjective := aeval_root_finAdele_surjective hP
      eq_zero_iff := aeval_root_finAdele_eq_zero_iff hP
      apply_map := aeval_root_finAdele_map
      apply_map_conj_comp := aeval_root_finAdele_map_conj_comp }⟩

end New

end CMAdjoinRoot
