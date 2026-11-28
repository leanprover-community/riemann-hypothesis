module

import TauCeti.Combinatorics.Young.OfRowLens
import TauCeti.RepresentationTheory.ClassicalGroups.DualWeylModule.Basis
import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.Bialternant
public import Lib.GLn.SchurModule.Basic

/-!
# A basis of minor products for Borel semi-invariants over any ring

Polynomials are in variables `X (a, i)`, where `a` is a row with colour `c a` and `i : ℕ` is a
column (`New.MatrixPoly`). For finitely many rows and `l = New.GL.columnWeight τ h`, the module
`New.nabla R c l` of Borel semi-invariants has a basis of products of minors that does not depend on
the ring `R`.

## Main definitions and results

* `New.GL.columnWeight`, `New.GL.ColoredTableau`, `New.GL.minorProduct`: the weight of a family of
  coloured columns, its fillings by rows, and the product of the minors of a filling.
* `New.GL.IsStdMinorFamily`: records that a finite family of fillings has minor products that are
  linearly independent and span `New.nabla R c (New.GL.columnWeight τ h)` over every commutative
  ring `R`, and satisfy the Weyl character identity when there is a single colour.
* `New.GL.exists_isStdMinorFamily`: existence of a standard family of minor products, deduced for a
  single colour from Tau Ceti's standard basis for dual Weyl modules
  (`TauCeti.DualWeylModule.linearIndependent_bideterminant_ssytFilling`,
  `TauCeti.DualWeylModule.dualWeylModule_le_span_bideterminant_ssytFilling`) and Jacobi's
  bialternant formula (`TauCeti.diagramSchurPoly_mul_alternant`), then lifted to multiple colours
  by induction on the number of active colours.

Notions from other files:
* `New.nabla`: For a row colouring `c` and weight `l`, the module of Borel semi-invariants:
  polynomials `f` with `f(yβ) = ∏ β_{τ,ii}^{l(τ,i)} f(y)` for generic upper triangular
  matrices `β_τ`, one per colour.
* `New.minor`: For an `h`-tuple `I` of rows, the polynomial determinant of the `h × h` matrix of
  variables in rows `I` and the first `h` columns.
* `New.GL.alternant`: For `x` in `ℂ^N` and `l : ℕ → ℕ`, the alternant
  `det(x_i^{l(N−1−j)+j})`, `0 ≤ i, j < N`, if `l(N) = 0`, and zero otherwise.

## Relation to the literature

Known result: The standard basis theorem for Schur (dual Weyl) modules over any ring, with their
character. Source: De Concini, Eisenbud, Procesi, Young diagrams and determinantal varieties,
Invent. Math. 56 (1980); Akin, Buchsbaum, Weyman, Schur functors and Schur complexes, Adv. Math. 44
(1982), II.2.16, II.4.11.

See also `Lib.DiscreteSeries.Character.WeylCharacterFormula`.
-/

@[expose] public section

noncomputable section

section MinorBasis

open MvPolynomial Finset Finsupp Matrix Submodule TauCeti DualWeylModule

namespace New.GL

/-! ### Columns, fillings and products of minors -/

section Defs

variable {Φ J m R : Type} [Fintype J] [CommRing R] {c : m → Φ} {τ : J → Φ} {h : J → ℕ}

/-- For finitely many columns `j` with colour `τ j` and height `h j`, the weight whose value at
`(τ, i)` counts the columns of colour `τ` with height exceeding `i`. -/
def columnWeight (τ : J → Φ) (h : J → ℕ) : Φ × ℕ →₀ ℕ :=
  ∑ j : J, ∑ i ∈ range (h j), Finsupp.single ((τ j : Φ), i) 1

/-- The type of assignments giving each column `j` an `h j`-tuple of rows, all of colour `τ j`. -/
abbrev ColoredTableau (c : m → Φ) (τ : J → Φ) (h : J → ℕ) : Type :=
  ∀ j : J, Fin (h j) → {a // c a = τ j}

/-- For a coloured column filling `I`, the polynomial over `S` that is the product over columns `j`
of the minor with rows `I j` on the first `h j` columns. -/
def minorProduct (S : Type) [CommRing S] (I : ColoredTableau c τ h) : MatrixPoly m S :=
  ∏ j : J, minor S fun s ↦ (I j s).val

/-- The weight `New.diagramWeight N κ` equals the weight `New.GL.columnWeight` of the family having
`κ τ h` columns of colour `τ` and height `h`, for every `τ` and `h < N τ`: its columns are the
triples `⟨τ, h, j⟩` with `j < κ τ h`, of colour `τ` and height `h`. -/
lemma diagramWeight_eq_columnWeight [Fintype Φ] (N : Φ → ℕ) (κ : Φ → ℕ → ℕ) :
    diagramWeight N κ =
      columnWeight (fun j : Σ τ : Φ, Σ h : Fin (N τ), Fin (κ τ h) ↦ j.fst)
        fun j : Σ τ : Φ, Σ h : Fin (N τ), Fin (κ τ h) ↦ (j.snd.fst : ℕ) := by
  -- `↓`: the sums over the sigma type must be split before the definitions unfold
  simp [↓Fintype.sum_sigma, diagramWeight, sum_range, columnWeight]

/-- For an assignment `I` of `h j` rows of colour `τ j` to each column `j`, the product of minors
`New.GL.minorProduct` of `I` is a Borel semi-invariant: it lies in `New.nabla` for the weight
`New.GL.columnWeight` of `τ, h`. -/
lemma minorProduct_mem_nabla (I : ColoredTableau c τ h) :
    minorProduct R I ∈ nabla R c (columnWeight τ h) := by
  -- each minor is a semi-invariant, and semi-invariants form a graded monoid
  rw [minorProduct, columnWeight]
  apply SetLike.prod_mem_graded
  exact fun j _ ↦ minor_mem_nabla fun s ↦ (I j s).prop

/-- A standard family of fillings `I` for rows coloured by `c` and columns `j` of colour `τ j` and
height `h j`: each `I i` (a `ColoredTableau`) gives column `j` an `h j`-tuple of rows of colour
`τ j`; `minorProduct R (I i)` is the product of the minors on these rows and the first `h j`
columns. -/
structure IsStdMinorFamily {Φ J m ι : Type} [Fintype m] [Fintype J] [Fintype ι]
    {c : m → Φ} {τ : J → Φ} {h : J → ℕ} (I : ι → ColoredTableau c τ h) : Prop where
  /-- Over every commutative ring the products of minors are linearly independent. -/
  linearIndependent (R : Type) [CommRing R] :
    LinearIndependent R fun i : ι ↦ minorProduct R (I i)
  /-- Over every commutative ring the span of the products of minors contains the
  semi-invariants of weight `columnWeight τ h`. -/
  nabla_le_span (R : Type) [CommRing R] :
    nabla R c (columnWeight τ h) ≤ span R (Set.range fun i : ι ↦ minorProduct R (I i))
  /-- If `t` is the only colour and `e` enumerates the rows, then the sum over the fillings of the
  products of the `x a` over their entries `a`, times the alternant of the zero weight, is the
  alternant of the weight `columnWeight τ h (t, ·)`. -/
  character [Subsingleton Φ] (t : Φ) (N : ℕ) (e : Fin N ≃ m) (x : m → ℂ) :
    (∑ i : ι, ∏ j : J, ∏ s : Fin (h j), x (I i j s)) * alternant (x ∘ e) 0 =
      alternant (x ∘ e) fun k : ℕ ↦ columnWeight τ h (t, k)

end Defs

/-! ### Helper lemmas for Borel action and column weights -/

section Helpers

/-- Evaluating `borelMul` on a matrix `b` that vanishes strictly above the diagonal multiplies each
variable `y (a, i)` by the diagonal entry `b (c a, i, i)`. -/
private lemma borelMul_of_diag {Φ m S : Type} [CommRing S] {c : m → Φ}
    {b : Φ × ℕ × ℕ → S} {y : m × ℕ → S} {a : m} {i : ℕ}
    (hb : ∀ j < i, b (c a, j, i) = 0) :
    borelMul c b y (a, i) = y (a, i) * b (c a, i, i) := by
  rw [borelMul, Finset.sum_eq_single i]
  · intro j hj hji
    rw [hb j (lt_of_le_of_ne (Nat.lt_succ_iff.1 (mem_range.1 hj)) hji), mul_zero]
  · intro hnot; exact absurd (mem_range.2 (Nat.lt_succ_self i)) hnot

/-- The product of powers of `g p` weighted by `columnWeight τ h` equals the double product over
columns `j` and indices `i < h j`. -/
private lemma prod_columnWeight_pow {Φ J S : Type} [Fintype J] [CommMonoid S]
    (τ : J → Φ) (h : J → ℕ) (g : Φ × ℕ → S) :
    ((columnWeight τ h).prod fun p k ↦ g p ^ k) =
      ∏ j : J, ∏ i ∈ range (h j), g (τ j, i) := by
  rw [columnWeight,
    ← Finsupp.prod_finsetSum_index (fun _ ↦ pow_zero _) (fun _ _ _ ↦ pow_add _ _ _)]
  refine prod_congr rfl fun j _ ↦ ?_
  rw [← Finsupp.prod_finsetSum_index (fun _ ↦ pow_zero _) (fun _ _ _ ↦ pow_add _ _ _)]
  exact prod_congr rfl fun i _ ↦ by simp [Finsupp.prod_single_index]

/-- The column weight of `h` at the unique colour `t` counts columns of height exceeding `i`. -/
private lemma columnWeight_apply_subsingleton {Φ J : Type} [Subsingleton Φ] [Fintype J]
    (τ : J → Φ) (h : J → ℕ) (t : Φ) (i : ℕ) :
    columnWeight τ h (t, i) = #{j : J | i < h j} := by
  classical
  change Finsupp.applyAddHom (t, i) (columnWeight τ h) = _
  simp only [columnWeight, map_sum, Finsupp.applyAddHom_apply, Finsupp.single_apply,
    Prod.mk.injEq, Subsingleton.elim _ t, true_and, Finset.sum_ite_eq', mem_range,
    Finset.sum_boole, Nat.cast_id]

/-- Build the Young diagram whose `i`-th row length is `#{j : J | i < h j}` (for `h : J → ℕ`),
together with a height-preserving bijection between `{j : J // 0 < h j}` and the columns
`Fin (μ.rowLen 0)`. -/
private lemma exists_youngDiagram_of_heights {J : Type} [Fintype J] (h : J → ℕ) :
    ∃ (n : ℕ) (μ : YoungDiagram) (_ : μ.colLen 0 ≤ n)
      (σ : {j : J // 0 < h j} ≃ Fin (μ.rowLen 0)),
      (∀ i : ℕ, μ.rowLen i = #{j : J | i < h j}) ∧
      (∀ j : {j : J // 0 < h j}, h j.val = μ.colLen (σ j)) := by
  classical
  let n : ℕ := univ.sup h
  let f : Fin n → ℕ := fun i ↦ #{j : J | (i : ℕ) < h j}
  have hf : Antitone f := fun a b hab ↦
    card_le_card fun j hj ↦ mem_filter.2 ⟨mem_univ _, lt_of_le_of_lt hab (mem_filter.1 hj).2⟩
  let μ : YoungDiagram := YoungDiagram.ofRowLensFin f hf
  have hrow (i : ℕ) : μ.rowLen i = #{j : J | i < h j} := by
    by_cases hi : i < n
    · exact YoungDiagram.rowLen_ofRowLensFin f hf ⟨i, hi⟩
    · rw [YoungDiagram.rowLen_ofRowLensFin_eq_zero_of_le f hf (not_lt.1 hi)]
      exact (card_eq_zero.2 (filter_eq_empty_iff.2 fun j _ ↦
        by have := le_sup (f := h) (mem_univ j); omega)).symm
  have hcard_add {α : Type} [Fintype α] (g : α → ℕ) (d : ℕ) :
      #{a : α | g a = d + 1} + #{a : α | d + 1 < g a} = #{a : α | d < g a} := by
    rw [← card_union_of_disjoint (disjoint_filter.2 fun _ _ h1 h2 ↦ by omega)]
    congr 1; ext a; simp; omega
  have hcount (s : ℕ) : #{r : Fin (μ.rowLen 0) | s < μ.colLen r} = μ.rowLen s := by
    rw [← Fintype.card_subtype, ← Fintype.card_fin (μ.rowLen s)]
    refine Fintype.card_congr
      ⟨fun r ↦
         ⟨r.val, YoungDiagram.mem_iff_lt_rowLen.1 (YoungDiagram.mem_iff_lt_colLen.2 r.2)⟩,
       fun k ↦ ⟨⟨k, lt_of_lt_of_le k.2 (μ.rowLen_anti 0 s (Nat.zero_le s))⟩,
         YoungDiagram.mem_iff_lt_colLen.1 (YoungDiagram.mem_iff_lt_rowLen.2 k.2)⟩,
       fun _ ↦ rfl, fun _ ↦ rfl⟩
  have hcard_fiber (k : ℕ) :
      Fintype.card {j : {j : J // 0 < h j} // h j.val = k} =
        Fintype.card {r : Fin (μ.rowLen 0) // μ.colLen r = k} := by
    rcases k with _ | d
    · have : IsEmpty {j : {j : J // 0 < h j} // h j.val = 0} :=
        ⟨fun ⟨⟨_, hj⟩, hk⟩ ↦ Nat.ne_of_gt hj hk⟩
      have : IsEmpty {r : Fin (μ.rowLen 0) // μ.colLen r = 0} :=
        ⟨fun ⟨r, hr⟩ ↦ by
          have := YoungDiagram.mem_iff_lt_colLen.1 (YoungDiagram.mem_iff_lt_rowLen.2 r.2); omega⟩
      simp
    · have hA : Fintype.card {j : {j : J // 0 < h j} // h j.val = d + 1} =
          #{j : J | h j = d + 1} := by
        rw [← Fintype.card_subtype]
        exact Fintype.card_congr
          ⟨fun a ↦ ⟨a.val.val, a.2⟩,
           fun b ↦ ⟨⟨b.val, by have := b.2; omega⟩, b.2⟩,
           fun _ ↦ rfl, fun _ ↦ rfl⟩
      have h1 := hcard_add h d
      have h2 := hcard_add (fun r : Fin (μ.rowLen 0) ↦ μ.colLen r) d
      rw [hcount d, hcount (d + 1), hrow d, hrow (d + 1)] at h2
      rw [hA, Fintype.card_subtype]; omega
  let σ : {j : J // 0 < h j} ≃ Fin (μ.rowLen 0) :=
    (Equiv.sigmaFiberEquiv (fun j : {j : J // 0 < h j} ↦ h j.val)).symm.trans <|
      (Equiv.sigmaCongrRight fun k ↦ Fintype.equivOfCardEq (hcard_fiber k)).trans <|
        Equiv.sigmaFiberEquiv (fun r : Fin (μ.rowLen 0) ↦ μ.colLen r)
  exact ⟨n, μ, YoungDiagram.colLen_zero_ofRowLensFin_le f hf, σ, hrow,
    fun j ↦ ((Fintype.equivOfCardEq (hcard_fiber (h j.val)) ⟨j, rfl⟩).prop).symm⟩

end Helpers

/-! ### Single-colour standard basis via Tau Ceti's dual Weyl module basis -/

section SingleColour

/-- For a single colour, restricting a Borel semi-invariant of weight `μ.rowLen` (with
`μ.colLen 0 ≤ n`) to the first `n` columns lands in Tau Ceti's `dualWeylModule`, and the
polynomial is recovered from its restriction by `rename (Prod.map e Fin.val)`. -/
private lemma proj_mem_dualWeylModule {Φ J m R : Type} [Subsingleton Φ] [Fintype m] [Fintype J]
    [CommRing R] {c : m → Φ} {τ : J → Φ} {h : J → ℕ} {N n : ℕ} (e : Fin N ≃ m)
    {μ : YoungDiagram} (hrow : ∀ i : ℕ, μ.rowLen i = #{j : J | i < h j})
    (hμ : μ.colLen 0 ≤ n) {f : MatrixPoly m R} (hf : f ∈ nabla R c (columnWeight τ h)) :
    let proj : MatrixPoly m R →ₐ[R] MvPolynomial (Fin N × Fin n) R :=
      aeval fun p ↦ if hi : p.2 < n then X (e.symm p.1, ⟨p.2, hi⟩) else 0
    rename (Prod.map e Fin.val) (proj f) = f ∧
      proj f ∈ dualWeylModule R N (fun s : Fin n ↦ μ.rowLen s) := by
  classical
  intro proj
  have hw_eq (t : Φ) (i : ℕ) : columnWeight τ h (t, i) = μ.rowLen i := by
    rw [columnWeight_apply_subsingleton, hrow]
  -- Step 1: `f` only involves columns `< n`, via `borelMul` with the `< n` projection matrix.
  have h_retract : rename (Prod.map e Fin.val) (proj f) = f := by
    let b : Φ × ℕ × ℕ → MatrixPoly m R :=
      fun p ↦ if p.2.1 = p.2.2 ∧ p.2.1 < n then 1 else 0
    have h1 := mem_nabla.1 hf (MatrixPoly m R) b X
    have h_prod : ((columnWeight τ h).prod fun p k ↦ b (p.1, p.2, p.2) ^ k) = 1 := by
      refine prod_eq_one fun p hp ↦ ?_
      have hpos : 0 < μ.rowLen p.2 := by
        rw [← hw_eq p.1]; exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 hp)
      simp [b, lt_of_lt_of_le (YoungDiagram.rowLen_pos_iff.1 hpos) hμ]
    have h_lhs : aeval (borelMul c b X) f = rename (Prod.map e Fin.val) (proj f) := by
      rw [rename_eq_aeval, ← AlgHom.comp_apply]
      refine AlgHom.congr_fun (MvPolynomial.algHom_ext fun p ↦ ?_) f
      simp only [AlgHom.comp_apply, aeval_X, proj]
      rw [borelMul_of_diag (fun j hj ↦ by simp [b, ne_of_lt hj])]
      by_cases hlt : p.2 < n <;> simp [b, hlt]
    rw [h_lhs, h_prod, one_mul, aeval_X_left] at h1
    exact h1
  refine ⟨h_retract, mem_dualWeylModule.2 ⟨?homog, ?unip⟩⟩
  · -- Step 2: Column homogeneity, scaling column `s` by `Polynomial.X`.
    intro d hd s
    let S := MvPolynomial (Fin N × Fin n) (Polynomial R)
    let y : m × ℕ → S := fun p ↦ if hi : p.2 < n then X (e.symm p.1, ⟨p.2, hi⟩) else 0
    let b : Φ × ℕ × ℕ → S :=
      fun p ↦ if p.2.1 = p.2.2 then (if p.2.1 = (s : ℕ) then C Polynomial.X else 1) else 0
    have h2 := mem_nabla.1 hf S b y
    have hy_eval : aeval y f = map Polynomial.C (proj f) := by
      conv_lhs => rw [← h_retract, aeval_rename]
      change aeval (y ∘ Prod.map e Fin.val) (proj f) =
        MvPolynomial.mapAlgHom (Algebra.ofId R (Polynomial R)) (proj f)
      refine AlgHom.congr_fun (MvPolynomial.algHom_ext fun p ↦ ?_) (proj f)
      simp [y, p.2.2]; exact (MvPolynomial.map_X Polynomial.C p).symm
    have h_wt : ((columnWeight τ h).prod fun p k ↦ b (p.1, p.2, p.2) ^ k) =
        C (Polynomial.X ^ μ.rowLen s) := by
      rcases isEmpty_or_nonempty Φ with hΦ | ⟨⟨t⟩⟩
      · have : IsEmpty J := ⟨fun j ↦ hΦ.false (τ j)⟩
        have h0 : μ.rowLen s = 0 := by rw [hrow]; simp
        simp [columnWeight, h0, Fintype.sum_empty]
      · rw [Finsupp.prod_eq_single (t, (s : ℕ))]
        · simp [b, hw_eq]
        · intro p _ hp
          have hne : p.2 ≠ (s : ℕ) := fun h ↦ hp (Prod.ext (Subsingleton.elim _ _) h)
          simp [b, hne]
        · intro _; simp
    have h_term (m' : Fin N × Fin n →₀ ℕ) :
        aeval (borelMul c b y ∘ Prod.map e Fin.val) (monomial m' ((proj f).coeff m')) =
          monomial m'
            (Polynomial.C ((proj f).coeff m') * Polynomial.X ^ (∑ a : Fin N, m' (a, s))) := by
      rw [aeval_monomial]
      have h_bm (p : Fin N × Fin n) :
          borelMul c b y (Prod.map e Fin.val p) =
            C (if p.2 = s then Polynomial.X else 1) * (X p : S) := by
        rcases p with ⟨a, j⟩
        rw [Prod.map_apply, borelMul_of_diag (fun k hk ↦ by simp [b, ne_of_lt hk])]
        simp only [b, y, j.2, dite_true, ite_true, Equiv.symm_apply_apply, Fin.val_inj]
        by_cases hjs : j = s <;> simp [hjs, mul_comm]
      have hpow : (m'.prod fun p k ↦
            (C (if p.2 = s then (Polynomial.X : Polynomial R) else 1) : S) ^ k) =
          C (Polynomial.X ^ (∑ a : Fin N, m' (a, s))) := by
        rw [Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _), Fintype.prod_prod_type]
        have hcol (a : Fin N) :
            ∏ j : Fin n,
              (C (if j = s then (Polynomial.X : Polynomial R) else 1) : S) ^ m' (a, j) =
              C (Polynomial.X ^ m' (a, s)) := by
          rw [Finset.prod_eq_single s]
          · simp
          · intro j _ hjs; simp [hjs]
          · intro hnot; exact absurd (mem_univ s) hnot
        simp_rw [hcol, ← map_prod, prod_pow_eq_pow_sum]
      simp only [Function.comp_apply, h_bm, mul_pow, Finsupp.prod_mul, hpow]
      rw [show (m'.prod fun p k ↦ (X p : S) ^ k) = monomial m' 1 from by
        rw [monomial_eq, map_one, one_mul], ← mul_assoc,
        show algebraMap R S ((proj f).coeff m') = C (Polynomial.C ((proj f).coeff m')) from rfl,
        ← map_mul, C_mul_monomial, mul_one]
    have h_lhs : (aeval (borelMul c b y) f).coeff d =
        Polynomial.C ((proj f).coeff d) * Polynomial.X ^ (∑ a : Fin N, d (a, s)) := by
      conv_lhs => rw [← h_retract, aeval_rename, (proj f).as_sum]
      rw [map_sum, coeff_sum]
      simp_rw [h_term, coeff_monomial]
      rw [Finset.sum_ite_eq' (proj f).support d, ite_eq_left hd]
    have hcoeff := congrArg (fun P : S ↦ (P.coeff d).coeff (∑ a : Fin N, d (a, s))) h2
    rw [h_lhs, h_wt, hy_eval, coeff_C_mul, coeff_map, mul_comm (Polynomial.X ^ _),
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X_pow, ite_eq_left rfl] at hcoeff
    by_contra hne
    rw [ite_eq_right hne] at hcoeff
    exact (Finsupp.mem_support_iff.1 hd) hcoeff
  · -- Step 3: Unipotent invariance, via `borelMul` with `I + Polynomial.X * E_{s, t'}`.
    intro s t' hst
    let S := Polynomial (MvPolynomial (Fin N × Fin n) R)
    let y : m × ℕ → S :=
      fun p ↦ if hi : p.2 < n then Polynomial.C (X (e.symm p.1, ⟨p.2, hi⟩)) else 0
    let b : Φ × ℕ × ℕ → S := fun p ↦
      if p.2.1 = p.2.2 then 1
      else if p.2.1 = (s : ℕ) ∧ p.2.2 = (t' : ℕ) then Polynomial.X else 0
    have h3 := mem_nabla.1 hf S b y
    have hy_eval : aeval y f = Polynomial.C (proj f) := by
      conv_lhs => rw [← h_retract, aeval_rename]
      change aeval (y ∘ Prod.map e Fin.val) (proj f) =
        (Polynomial.CAlgHom (R := MvPolynomial (Fin N × Fin n) R)).restrictScalars R (proj f)
      refine AlgHom.congr_fun (MvPolynomial.algHom_ext fun p ↦ ?_) (proj f)
      simp [y, p.2.2]
    have h_wt : ((columnWeight τ h).prod fun p k ↦ b (p.1, p.2, p.2) ^ k) = 1 :=
      prod_eq_one fun _ _ ↦ by simp [b]
    have h_lhs : aeval (borelMul c b y) f = columnOperation R s t' (proj f) := by
      conv_lhs => rw [← h_retract, aeval_rename]
      refine AlgHom.congr_fun (MvPolynomial.algHom_ext fun ⟨a, j⟩ ↦ ?_) (proj f)
      simp only [aeval_X, Function.comp_apply, Prod.map_apply]
      rw [columnOperation_X]
      have hst_ne : (s : ℕ) ≠ (t' : ℕ) := ne_of_lt hst
      by_cases hpt : j = t'
      · subst hpt
        have hs_mem : (s : ℕ) ∈ range ((j : ℕ) + 1) := mem_range.2 (Nat.lt_succ_of_lt hst)
        have ht_mem : (j : ℕ) ∈ range ((j : ℕ) + 1) := mem_range.2 (Nat.lt_succ_self _)
        rw [borelMul, ← Finset.add_sum_erase _ _ ht_mem,
          ← Finset.add_sum_erase _ _ (mem_erase.2 ⟨hst_ne, hs_mem⟩)]
        have hzero : ∑ i ∈ ((range ((j : ℕ) + 1)).erase j).erase s,
            y (e a, i) * b (c (e a), i, j) = 0 :=
          sum_eq_zero fun i hi ↦ by
            simp [b, (mem_erase.1 hi).1, (mem_erase.1 (mem_erase.1 hi).2).1]
        rw [hzero, add_zero]
        simp only [y, b, s.2, j.2, dite_true, ite_true, hst_ne, ite_false, and_self,
          Equiv.symm_apply_apply, mul_one]
        ring
      · have hpt_val : (j : ℕ) ≠ (t' : ℕ) := fun h ↦ hpt (Fin.ext h)
        rw [borelMul_of_diag (fun k hk ↦ by simp [b, ne_of_lt hk, hpt_val])]
        simp [y, b, j.2, hpt]
    rw [h_lhs, h_wt, one_mul, hy_eval] at h3
    exact h3

/-- Reindexing the rows of `New.GL.alternant` by a permutation multiplies it by the sign. -/
private lemma alternant_comp_perm {N : ℕ} (x : Fin N → ℂ) (l : ℕ → ℕ)
    (σ : Equiv.Perm (Fin N)) :
    alternant (x ∘ σ) l = (Equiv.Perm.sign σ : ℂ) * alternant x l := by
  simp only [alternant]
  split_ifs with h0
  · exact Matrix.det_permute σ (of fun i j : Fin N ↦ x i ^ (l j.rev + j))
  · simp

/-- `New.GL.alternant y μ.rowLen` equals `Perm.sign Fin.revPerm` times the evaluation of
Tau Ceti's `alternant (Fin N) ℂ (fun j ↦ μ.betaNumber N j)` at `y` when `μ.colLen 0 ≤ N`. -/
private lemma alternant_eq_sign_mul_eval_tauCeti_alternant {N : ℕ} (y : Fin N → ℂ)
    (μ : YoungDiagram) (hμ : μ.colLen 0 ≤ N) :
    alternant y μ.rowLen =
      (Equiv.Perm.sign (Fin.revPerm (n := N)) : ℂ) *
        eval y (TauCeti.alternant (Fin N) ℂ fun j : Fin N ↦ μ.betaNumber N j) := by
  have hN : μ.rowLen N = 0 := YoungDiagram.rowLen_eq_zero_iff.2 hμ
  rw [alternant, ite_eq_left hN, TauCeti.alternant_def, RingHom.map_det]
  have hmat : (of fun i j : Fin N ↦ y i ^ (μ.rowLen j.rev + j)) =
      ((eval y).mapMatrix (of fun i j : Fin N ↦ (X i : MvPolynomial (Fin N) ℂ) ^
        μ.betaNumber N j)).submatrix id Fin.revPerm := by
    ext i j
    simp only [of_apply, submatrix_apply, id_eq, Fin.revPerm_apply, RingHom.mapMatrix_apply,
      Matrix.map_apply, map_pow, eval_X, YoungDiagram.betaNumber_def, Fin.val_rev]
    congr 1; omega
  rw [hmat, Matrix.det_permute']

/-- Single-colour existence of a standard family of minor products, directly from Tau Ceti's
standard basis of `dualWeylModule` and Jacobi's bialternant formula. -/
private lemma exists_isStdMinorFamily_of_subsingleton {Φ J m : Type} [Subsingleton Φ]
    [Fintype m] [Fintype J] (c : m → Φ) (τ : J → Φ) (h : J → ℕ) :
    ∃ (ι : Type) (_ : Fintype ι) (I : ι → ColoredTableau c τ h), IsStdMinorFamily I := by
  classical
  let N : ℕ := Fintype.card m
  let e : Fin N ≃ m := (Fintype.equivFin m).symm
  obtain ⟨n, μ, hμ, σ, hrow, hσ⟩ := exists_youngDiagram_of_heights h
  -- Build a `ColoredTableau` from each bounded semistandard tableau `T : BoundedSSYT N μ`.
  let I : BoundedSSYT N μ → ColoredTableau c τ h := fun T j s ↦
    if hj : 0 < h j then
      ⟨e (ssytFilling T s (σ ⟨j, hj⟩)
        (by rw [YoungDiagram.mem_iff_lt_colLen, ← hσ ⟨j, hj⟩]; exact s.2)),
        Subsingleton.elim _ _⟩
    else
      False.elim (Nat.not_lt_zero _ (lt_of_lt_of_le s.2 (Nat.le_of_not_lt hj)))
  -- Under `rename (Prod.map e Fin.val)`, Tau Ceti's bideterminant of `T` is `minorProduct R (I T)`.
  have h_minor_eq (R : Type) [CommRing R] (T : BoundedSSYT N μ) :
      minorProduct R (I T) =
        rename (Prod.map e Fin.val) (bideterminant R μ hμ (ssytFilling T)) := by
    rw [bideterminant_eq_prod_range R μ hμ (ssytFilling T) le_rfl, map_prod, minorProduct,
      ← Fintype.prod_subtype_mul_prod_subtype (fun j : J ↦ 0 < h j)]
    have hzero : ∏ j : {j : J // ¬ 0 < h j}, minor R (fun s ↦ (I T j.val s).val) = 1 :=
      prod_eq_one fun j _ ↦ by
        have : IsEmpty (Fin (h j.val)) := ⟨fun s ↦ by have := s.2; have := j.2; omega⟩
        simp [minor]
    rw [hzero, mul_one]
    refine prod_bij (fun j _ ↦ (σ j : ℕ)) (fun j _ ↦ mem_range.2 (σ j).2)
      (fun _ _ _ _ heq ↦ σ.injective (Fin.ext heq))
      (fun k hk ↦ ⟨σ.symm ⟨k, mem_range.1 hk⟩, mem_univ _, by simp⟩) fun j _ ↦ ?_
    rw [columnMinor_def, Matrix.mvPolynomialMinor_eq_det_submatrix, minor, AlgHom.map_det]
    have hdet_eq : ∀ {k₁ k₂ : ℕ} (hk : k₁ = k₂)
        (A : Matrix (Fin k₁) (Fin k₁) (MatrixPoly m R))
        (B : Matrix (Fin k₂) (Fin k₂) (MatrixPoly m R)),
        (∀ a b : Fin k₁, A a b = B (a.cast hk) (b.cast hk)) → A.det = B.det := by
      rintro k _ rfl A B hAB
      exact congr_arg Matrix.det (Matrix.ext fun a b ↦ hAB a b)
    refine hdet_eq (hσ j) _ _ fun a b ↦ ?_
    simp [I, j.2, Matrix.map_apply, Matrix.mvPolynomialX]
  refine ⟨BoundedSSYT N μ, inferInstance, I, ⟨?indep, ?span, ?char⟩⟩
  case indep =>
    intro R _
    have hinj : Function.Injective (rename (R := R) (Prod.map e (Fin.val (n := n)))) :=
      rename_injective _ (e.injective.prodMap Fin.val_injective)
    have hli := (linearIndependent_bideterminant_ssytFilling (R := R) N μ hμ).map'
      (rename (R := R) (Prod.map e (Fin.val (n := n)))).toLinearMap (LinearMap.ker_eq_bot.2 hinj)
    simpa only [Function.comp_def, AlgHom.toLinearMap_apply, ← h_minor_eq R] using hli
  case span =>
    intro R _ f hf
    obtain ⟨h_retract, h_mem⟩ := proj_mem_dualWeylModule e hrow hμ hf
    have h_in_span := dualWeylModule_le_span_bideterminant_ssytFilling (R := R) N μ hμ h_mem
    have h_map := Submodule.mem_map_of_mem
      (f := (rename (R := R) (Prod.map e Fin.val)).toLinearMap) h_in_span
    rw [Submodule.map_span, ← Set.range_comp] at h_map
    simpa only [AlgHom.toLinearMap_apply, h_retract, Function.comp_def, ← h_minor_eq R]
      using h_map
  case char =>
    intro _ t N' e' x
    obtain rfl : N' = N := (Fintype.card_fin N').symm.trans (Fintype.card_congr e')
    have hw_fun : (fun k : ℕ ↦ columnWeight τ h (t, k)) = μ.rowLen := by
      ext k; rw [columnWeight_apply_subsingleton, hrow]
    rw [hw_fun]
    by_cases hμN : μ.colLen 0 ≤ N
    · -- Evaluate `diagramSchurPoly_mul_alternant` at `x ∘ e` and adjust row order to `e'`.
      have h_entry_prod (T : BoundedSSYT N μ) :
          (∏ j : J, ∏ s : Fin (h j), x (I T j s)) =
            ∏ i : Fin N, (x (e i)) ^ BoundedSSYT.weight T i := by
        rw [← Fintype.prod_subtype_mul_prod_subtype (fun j : J ↦ 0 < h j)]
        have hzero : ∏ j : {j : J // ¬ 0 < h j}, ∏ s : Fin (h j.val), x (I T j.val s) = 1 :=
          prod_eq_one fun j _ ↦ by
            have : IsEmpty (Fin (h j.val)) := ⟨fun s ↦ by have := s.2; have := j.2; omega⟩
            exact Fintype.prod_empty _
        let x' : ℕ → ℂ := fun k ↦ if hk : k < N then x (e ⟨k, hk⟩) else 1
        have h_cells : (∏ j : {j : J // 0 < h j}, ∏ s : Fin (h j.val), x (I T j.val s)) =
            ∏ p ∈ μ.cells, x' (T.val p.1 p.2) := by
          rw [show (∏ j : {j : J // 0 < h j}, ∏ s : Fin (h j.val), x (I T j.val s)) =
            ∏ p : Σ j : {j : J // 0 < h j}, Fin (h j.val), x (I T p.1.val p.2) from
            (Fintype.prod_sigma (fun p : Σ j : {j : J // 0 < h j}, Fin (h j.val) ↦
              x (I T p.1.val p.2))).symm]
          refine prod_bij (fun p _ ↦ ((p.2 : ℕ), (σ p.1 : ℕ)))
            (fun p _ ↦ (YoungDiagram.mem_cells _).2
              (by rw [YoungDiagram.mem_iff_lt_colLen, ← hσ p.1]; exact p.2.2))
            ?_ ?_ fun p _ ↦ ?_
          · intro ⟨j₁, s₁⟩ _ ⟨j₂, s₂⟩ _ heq
            have hj : j₁ = j₂ := σ.injective (Fin.ext (congrArg Prod.snd heq))
            subst hj; congr 1; exact Fin.ext (congrArg Prod.fst heq)
          · intro q hq
            have hqμ : q ∈ μ := (YoungDiagram.mem_cells _).1 hq
            have hq2 : q.2 < μ.rowLen 0 :=
              lt_of_lt_of_le (YoungDiagram.mem_iff_lt_rowLen.1 hqμ)
                (μ.rowLen_anti 0 _ (Nat.zero_le _))
            let j₀ := σ.symm ⟨q.2, hq2⟩
            have hq1 : q.1 < h j₀.val := by
              rw [hσ j₀]; simpa [j₀] using YoungDiagram.mem_iff_lt_colLen.1 hqμ
            exact ⟨⟨j₀, ⟨q.1, hq1⟩⟩, mem_univ _, Prod.ext rfl (by simp [j₀])⟩
          · have hmem : ((p.2 : ℕ), (σ p.1 : ℕ)) ∈ μ := by
              rw [YoungDiagram.mem_iff_lt_colLen, ← hσ p.1]; exact p.2.2
            simp only [I, p.1.2, dite_true, x', BoundedSSYT.entry_lt T hmem]
            congr 2; exact Fin.ext (val_ssytFilling T _ _ _)
        rw [hzero, mul_one, h_cells,
          ← Finset.prod_fiberwise_of_maps_to (t := range N) (g := fun p ↦ T.val p.1 p.2)
            (fun p hp ↦ mem_range.2 (BoundedSSYT.entry_lt T ((YoungDiagram.mem_cells _).1 hp))),
          ← Fin.prod_univ_eq_prod_range
            (fun k ↦ ∏ p ∈ μ.cells with T.val p.1 p.2 = k, x' (T.val p.1 p.2)) N]
        refine prod_congr rfl fun i _ ↦ ?_
        rw [prod_congr rfl (fun p hp ↦ by rw [(mem_filter.1 hp).2]), prod_const,
          ← SemistandardYoungTableau.content_apply]
        simp [x', i.2, BoundedSSYT.weight_apply]
      have h_schur : (∑ T : BoundedSSYT N μ, ∏ j : J, ∏ s : Fin (h j), x (I T j s)) =
          eval (x ∘ e) (diagramSchurPoly N ℂ μ) := by
        rw [eval_diagramSchurPoly]; exact sum_congr rfl fun T _ ↦ h_entry_prod T
      have h_bialt :=
        congrArg (eval (x ∘ e)) (diagramSchurPoly_mul_alternant (R := ℂ) N μ hμN)
      rw [map_mul] at h_bialt
      have h_alt0 : alternant (x ∘ e) 0 =
          (Equiv.Perm.sign (Fin.revPerm (n := N)) : ℂ) *
            eval (x ∘ e) (TauCeti.alternant (Fin N) ℂ fun j : Fin N ↦ N - 1 - (j : ℕ)) := by
        have hbot := alternant_eq_sign_mul_eval_tauCeti_alternant (x ∘ e) ⊥ (by simp)
        have hrow0 : (⊥ : YoungDiagram).rowLen = 0 := funext fun _ ↦ YoungDiagram.rowLen_bot _
        simpa only [hrow0, YoungDiagram.betaNumber_def, YoungDiagram.rowLen_bot, zero_add]
          using hbot
      have h_e : (∑ T : BoundedSSYT N μ, ∏ j : J, ∏ s : Fin (h j), x (I T j s)) *
          alternant (x ∘ e) 0 = alternant (x ∘ e) μ.rowLen := by
        rw [h_schur, h_alt0, alternant_eq_sign_mul_eval_tauCeti_alternant (x ∘ e) μ hμN]
        linear_combination (Equiv.Perm.sign (Fin.revPerm (n := N)) : ℂ) * h_bialt
      have h_perm : x ∘ e' = (x ∘ e) ∘ (e'.trans e.symm) := by ext i; simp
      rw [h_perm, alternant_comp_perm, alternant_comp_perm, mul_left_comm, h_e]
    · -- `N < μ.colLen 0`: there are no bounded SSYT of shape `μ`, and `μ.rowLen N ≠ 0`.
      have hlt : N < μ.colLen 0 := not_le.1 hμN
      have : IsEmpty (BoundedSSYT N μ) := BoundedSSYT.isEmpty_of_lt_colLen hlt
      have hpos : μ.rowLen N ≠ 0 := (YoungDiagram.rowLen_pos_iff.2 hlt).ne'
      simp [alternant, hpos, Fintype.sum_empty]

end SingleColour

/-! ### Multi-colour lift by induction on the number of active colours -/

section MultiColour

/-- Splitting the variables of `MatrixPoly m R` into rows of colour `φ₀` and the remaining
rows. -/
private def splitColourEquiv {Φ m R : Type} [DecidableEq Φ] [CommRing R] (c : m → Φ)
    (φ₀ : Φ) :
    MatrixPoly m R ≃ₐ[R]
      MatrixPoly {a : m // c a = φ₀} (MatrixPoly {a : m // c a ≠ φ₀} R) :=
  let e_row : m ≃ {a : m // c a = φ₀} ⊕ {a : m // c a ≠ φ₀} :=
    (Equiv.sumCompl (fun a : m ↦ c a = φ₀)).symm
  (renameEquiv R ((e_row.prodCongr (.refl ℕ)).trans (Equiv.sumProdDistrib _ _ _))).trans
    (sumAlgEquiv R ({a : m // c a = φ₀} × ℕ) ({a : m // c a ≠ φ₀} × ℕ))

/-- Evaluating `splitColourEquiv c φ₀ f` with coefficient homomorphism `ψ` and inner variables
`z₀` equals evaluating `f` directly at the combined variable assignment. -/
private lemma aevalTower_splitColourEquiv {Φ m R S : Type} [DecidableEq Φ] [CommRing R]
    [CommRing S] [Algebra R S] (c : m → Φ) (φ₀ : Φ)
    (ψ : MatrixPoly {a : m // c a ≠ φ₀} R →ₐ[R] S)
    (z₀ : {a : m // c a = φ₀} × ℕ → S) (f : MatrixPoly m R) :
    aevalTower ψ z₀ (splitColourEquiv c φ₀ f) =
      aeval (fun p : m × ℕ ↦ if ha : c p.1 = φ₀ then z₀ (⟨p.1, ha⟩, p.2)
        else ψ (X (⟨p.1, ha⟩, p.2))) f := by
  change (aevalTower ψ z₀).comp (splitColourEquiv c φ₀).toAlgHom f = _
  refine AlgHom.congr_fun (MvPolynomial.algHom_ext fun ⟨a, i⟩ ↦ ?_) f
  by_cases ha : c a = φ₀ <;> simp [splitColourEquiv, ha]

/-- Splitting a weighted product over `columnWeight τ h` into colour `φ₀` and other colours. -/
private lemma prod_columnWeight_split {Φ J S : Type} [DecidableEq Φ] [Fintype J] [CommMonoid S]
    (τ : J → Φ) (h : J → ℕ) (φ₀ : Φ) (g : Φ × ℕ → S) :
    ((columnWeight τ h).prod fun p k ↦ g p ^ k) =
      ((columnWeight (fun _ : {j : J // τ j = φ₀} ↦ ()) (fun j ↦ h j.val)).prod
          fun p k ↦ g (φ₀, p.2) ^ k) *
        ((columnWeight (fun j : {j : J // τ j ≠ φ₀} ↦ τ j.val) (fun j ↦ h j.val)).prod
          fun p k ↦ g p ^ k) := by
  rw [prod_columnWeight_pow, prod_columnWeight_pow, prod_columnWeight_pow,
    ← Fintype.prod_subtype_mul_prod_subtype (fun j : J ↦ τ j = φ₀)]
  congr 1
  exact prod_congr rfl fun j _ ↦ prod_congr rfl fun i _ ↦ by rw [j.2]

/-- Existence of a family of fillings whose minor products are linearly independent and span
`New.nabla R c (columnWeight τ h)` over every commutative ring `R`. -/
private lemma exists_minorBasis_multi {Φ J m : Type} [Fintype m] [Fintype J]
    (c : m → Φ) (τ : J → Φ) (h : J → ℕ) :
    ∃ (ι : Type) (_ : Fintype ι) (I : ι → ColoredTableau c τ h),
      (∀ (R : Type) [CommRing R], LinearIndependent R fun i : ι ↦ minorProduct R (I i)) ∧
      (∀ (R : Type) [CommRing R],
        nabla R c (columnWeight τ h) ≤
          span R (Set.range fun i : ι ↦ minorProduct R (I i))) := by
  classical
  induction hk : (univ.image c ∪ univ.image τ).card using Nat.strongRec
      generalizing m J c τ h with | ind k ih =>
  by_cases h_empty : (univ.image c ∪ univ.image τ) = ∅
  · have : IsEmpty m := ⟨fun a ↦ by
      have : c a ∈ (univ.image c ∪ univ.image τ) :=
        mem_union_left _ (mem_image_of_mem _ (mem_univ a))
      simp [h_empty] at this⟩
    have : IsEmpty J := ⟨fun j ↦ by
      have : τ j ∈ (univ.image c ∪ univ.image τ) :=
        mem_union_right _ (mem_image_of_mem _ (mem_univ j))
      simp [h_empty] at this⟩
    refine ⟨Unit, inferInstance, fun _ j ↦ isEmptyElim j, fun R _ ↦ ?_, fun R _ f _ ↦ ?_⟩
    · simp [Fintype.linearIndependent_iff, minorProduct, univ_eq_empty, ← C_mul',
        Unique.forall_iff]
    · rw [f.eq_C_of_isEmpty]; simp [minorProduct, univ_eq_empty, ← one_eq_span]
  obtain ⟨φ₀, hφ₀⟩ := Finset.ne_empty_iff_nonempty.1 h_empty
  -- Split rows and columns into colour `φ₀` and all other colours.
  let m₀ := {a : m // c a = φ₀}; let m' := {a : m // c a ≠ φ₀}
  let J₀ := {j : J // τ j = φ₀}; let J' := {j : J // τ j ≠ φ₀}
  let c₀ : m₀ → Unit := fun _ ↦ (); let τ₀ : J₀ → Unit := fun _ ↦ ()
  let h₀ : J₀ → ℕ := fun j ↦ h j.val
  let c' : m' → Φ := fun a ↦ c a.val; let τ' : J' → Φ := fun j ↦ τ j.val
  let h' : J' → ℕ := fun j ↦ h j.val
  obtain ⟨ι₀, _, I₀, hI₀⟩ := exists_isStdMinorFamily_of_subsingleton c₀ τ₀ h₀
  have hsub :
      (univ.image c' ∪ univ.image τ') ⊆ (univ.image c ∪ univ.image τ).erase φ₀ := by
    intro φ hφ
    rcases mem_union.1 hφ with h1 | h2
    · rcases mem_image.1 h1 with ⟨⟨a, ha⟩, _, rfl⟩
      exact mem_erase.2 ⟨ha, mem_union_left _ (mem_image_of_mem _ (mem_univ a))⟩
    · rcases mem_image.1 h2 with ⟨⟨j, hj⟩, _, rfl⟩
      exact mem_erase.2 ⟨hj, mem_union_right _ (mem_image_of_mem _ (mem_univ j))⟩
  have hlt : (univ.image c' ∪ univ.image τ').card < k :=
    hk ▸ lt_of_le_of_lt (card_le_card hsub) (card_erase_lt_of_mem hφ₀)
  obtain ⟨ι', _, I', hI'_indep, hI'_span⟩ := ih _ hlt c' τ' h' rfl
  let I : ι₀ × ι' → ColoredTableau c τ h := fun ⟨i₀, i'⟩ j s ↦
    if hj : τ j = φ₀ then
      ⟨(I₀ i₀ ⟨j, hj⟩ s).val.val, (I₀ i₀ ⟨j, hj⟩ s).val.prop.trans hj.symm⟩
    else ⟨(I' i' ⟨j, hj⟩ s).val.val, (I' i' ⟨j, hj⟩ s).prop⟩
  -- Under `splitColourEquiv`, `minorProduct R (I (i₀, i'))` factors into the two pieces.
  have h_split_prod (R : Type) [CommRing R] (i₀ : ι₀) (i' : ι') :
      splitColourEquiv c φ₀ (minorProduct R (I (i₀, i'))) =
        C (minorProduct R (I' i')) * minorProduct (MatrixPoly m' R) (I₀ i₀) := by
    rw [minorProduct, map_prod,
      ← Fintype.prod_subtype_mul_prod_subtype (fun j : J ↦ τ j = φ₀),
      mul_comm, minorProduct, map_prod, minorProduct]
    congr 1
    · refine prod_congr rfl fun j _ ↦ ?_
      simp only [minor, I, j.2, dite_false]
      change (splitColourEquiv c φ₀).toRingHom _ = _
      rw [RingHom.map_det, RingHom.map_det]
      exact congr_arg Matrix.det <| Matrix.ext fun a b ↦ by
        simp [splitColourEquiv, Matrix.map_apply, (I' i' j a).val.prop]
    · refine prod_congr rfl fun j _ ↦ ?_
      simp only [minor, I, j.2, dite_true]
      change (splitColourEquiv c φ₀).toRingHom _ = _
      rw [RingHom.map_det]
      exact congr_arg Matrix.det <| Matrix.ext fun a b ↦ by
        simp [splitColourEquiv, Matrix.map_apply, (I₀ i₀ j a).val.prop]
  refine ⟨ι₀ × ι', inferInstance, I, ?indep, ?span⟩
  case indep =>
    intro R _
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hsplit : ∑ i₀ : ι₀, (∑ i' : ι', g (i₀, i') • minorProduct R (I' i')) •
        minorProduct (MatrixPoly m' R) (I₀ i₀) = 0 := by
      have h0 := congrArg (splitColourEquiv c φ₀) hg
      simp only [map_sum, map_smul, map_zero, h_split_prod, Fintype.sum_prod_type] at h0
      rw [← h0]
      refine sum_congr rfl fun i₀ _ ↦ by
        rw [sum_smul]; exact sum_congr rfl fun i' _ ↦ by simp [Algebra.smul_def, mul_assoc]
    have hcoeff :=
      Fintype.linearIndependent_iff.1 (hI₀.linearIndependent (MatrixPoly m' R)) _ hsplit
    intro ⟨i₀, i'⟩
    exact Fintype.linearIndependent_iff.1 (hI'_indep R) (fun j' ↦ g (i₀, j')) (hcoeff i₀) i'
  case span =>
    intro R _ f hf
    let F : MatrixPoly m₀ (MatrixPoly m' R) := splitColourEquiv c φ₀ f
    -- First show `F` is a Borel semi-invariant in colour `φ₀` over `MatrixPoly m' R`.
    have hF_mem : F ∈ nabla (MatrixPoly m' R) c₀ (columnWeight τ₀ h₀) := by
      rw [mem_nabla]
      intro S _ _ b₀ y₀
      let _ : Algebra R S := Algebra.compHom S (algebraMap R (MatrixPoly m' R))
      have _ : IsScalarTower R (MatrixPoly m' R) S := IsScalarTower.of_algebraMap_eq' rfl
      let b : Φ × ℕ × ℕ → S := fun p ↦
        if p.1 = φ₀ then b₀ ((), p.2.1, p.2.2) else if p.2.1 = p.2.2 then 1 else 0
      let y : m × ℕ → S := fun p ↦
        if ha : c p.1 = φ₀ then y₀ (⟨p.1, ha⟩, p.2)
        else algebraMap (MatrixPoly m' R) S (X (⟨p.1, ha⟩, p.2))
      have h1 := mem_nabla.1 hf S b y
      have h_bm : borelMul c b y = fun p : m × ℕ ↦
          if ha : c p.1 = φ₀ then borelMul c₀ b₀ y₀ (⟨p.1, ha⟩, p.2)
          else algebraMap (MatrixPoly m' R) S (X (⟨p.1, ha⟩, p.2)) := by
        funext ⟨a, i⟩
        by_cases ha : c a = φ₀
        · simp [borelMul, ha, b, y]
        · rw [borelMul_of_diag (fun j hj ↦ by simp [b, ha, ne_of_lt hj])]; simp [ha, b, y]
      have h_wt : ((columnWeight τ h).prod fun p k ↦ b (p.1, p.2, p.2) ^ k) =
          (columnWeight τ₀ h₀).prod fun p k ↦ b₀ (p.1, p.2, p.2) ^ k := by
        rw [prod_columnWeight_split τ h φ₀ (fun p ↦ b (p.1, p.2, p.2))]
        have h2 : ((columnWeight τ' h').prod fun p k ↦ b (p.1, p.2, p.2) ^ k) = 1 := by
          rw [prod_columnWeight_pow]
          exact prod_eq_one fun j _ ↦ prod_eq_one fun _ _ ↦ by simp [b, τ', j.2]
        rw [h2, mul_one]; exact Finsupp.prod_congr fun p _ ↦ by simp [b]
      have h_ev (z₀ : m₀ × ℕ → S) :
          aeval (fun p : m × ℕ ↦ if ha : c p.1 = φ₀ then z₀ (⟨p.1, ha⟩, p.2)
            else algebraMap (MatrixPoly m' R) S (X (⟨p.1, ha⟩, p.2))) f = aeval z₀ F :=
        (aevalTower_splitColourEquiv c φ₀
          (IsScalarTower.toAlgHom R (MatrixPoly m' R) S) z₀ f).symm
      rw [h_bm, h_wt, h_ev, h_ev] at h1; exact h1
    -- Expand `F` in the standard basis `I₀` over `MatrixPoly m' R`.
    obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun (MatrixPoly m' R)).1
      (hI₀.nabla_le_span (MatrixPoly m' R) hF_mem)
    -- Each coefficient `g i₀` is a Borel semi-invariant in the remaining colours.
    have hg_mem (i₀ : ι₀) : g i₀ ∈ nabla R c' (columnWeight τ' h') := by
      rw [mem_nabla]
      intro S _ _ b' y'
      let T := MatrixPoly m₀ S
      let b : Φ × ℕ × ℕ → T := fun p ↦
        if p.1 = φ₀ then (if p.2.1 = p.2.2 then 1 else 0) else C (b' p)
      let y : m × ℕ → T := fun p ↦
        if ha : c p.1 = φ₀ then X (⟨p.1, ha⟩, p.2) else C (y' (⟨p.1, ha⟩, p.2))
      have h2 := mem_nabla.1 hf T b y
      have h_eval_g (z' : m' × ℕ → S) :
          aeval (fun p : m × ℕ ↦ if ha : c p.1 = φ₀ then (X (⟨p.1, ha⟩, p.2) : T)
            else C (z' (⟨p.1, ha⟩, p.2))) f =
          ∑ j₀ : ι₀, aeval z' (g j₀) • minorProduct S (I₀ j₀) := by
        let ψ : MatrixPoly m' R →ₐ[R] T := (IsScalarTower.toAlgHom R S T).comp (aeval z')
        have h_ev :
            aeval (fun p : m × ℕ ↦ if ha : c p.1 = φ₀ then (X (⟨p.1, ha⟩, p.2) : T)
              else C (z' (⟨p.1, ha⟩, p.2))) f = aevalTower ψ X F := by
          rw [show F = splitColourEquiv c φ₀ f from rfl, aevalTower_splitColourEquiv]
          congr 2; funext p; by_cases ha : c p.1 = φ₀
          · simp [ha]
          · simp [ha, ψ, T, MatrixPoly, algebraMap_eq]
        rw [h_ev, ← hg, map_sum]
        refine sum_congr rfl fun j₀ _ ↦ ?_
        rw [smul_eq_C_mul, map_mul, aevalTower_C]
        change C (aeval z' (g j₀)) * _ = _
        rw [smul_eq_C_mul]; congr 1
        simp only [minorProduct, map_prod, minor, AlgHom.map_det]
        refine prod_congr rfl fun j _ ↦ congr_arg Matrix.det <| Matrix.ext fun a b ↦ by
          simp [Matrix.map_apply]
      have h_bm : borelMul c b y = fun p : m × ℕ ↦
          if ha : c p.1 = φ₀ then (X (⟨p.1, ha⟩, p.2) : T)
          else C (borelMul c' b' y' (⟨p.1, ha⟩, p.2)) := by
        funext ⟨a, i⟩
        by_cases ha : c a = φ₀
        · rw [borelMul_of_diag (fun j hj ↦ by simp [b, ha, ne_of_lt hj])]; simp [ha, b, y]
        · simp [borelMul, ha, b, y, c', map_sum, map_mul]
      have h_wt : ((columnWeight τ h).prod fun p k ↦ b (p.1, p.2, p.2) ^ k) =
          C ((columnWeight τ' h').prod fun p k ↦ b' (p.1, p.2, p.2) ^ k) := by
        rw [prod_columnWeight_split τ h φ₀ (fun p ↦ b (p.1, p.2, p.2))]
        have h1' : ((columnWeight τ₀ h₀).prod fun p k ↦ b (φ₀, p.2, p.2) ^ k) = 1 :=
          prod_eq_one fun _ _ ↦ by simp [b]
        rw [h1', one_mul, prod_columnWeight_pow, prod_columnWeight_pow, map_prod]
        exact prod_congr rfl fun j _ ↦ by
          rw [map_prod]; exact prod_congr rfl fun _ _ ↦ by simp [b, j.2, τ']
      rw [h_bm, h_eval_g, h_eval_g, h_wt, Finset.mul_sum] at h2
      have hdiff : ∑ j₀ : ι₀, (aeval (borelMul c' b' y') (g j₀) -
          ((columnWeight τ' h').prod fun p k ↦ b' (p.1, p.2, p.2) ^ k) * aeval y' (g j₀)) •
          minorProduct S (I₀ j₀) = 0 := by
        simp_rw [sub_smul, sum_sub_distrib, mul_smul, smul_eq_C_mul]
        exact sub_eq_zero.2 (by simpa only [smul_eq_C_mul, mul_assoc] using h2)
      exact sub_eq_zero.1
        (Fintype.linearIndependent_iff.1 (hI₀.linearIndependent S) _ hdiff i₀)
    -- Apply the induction hypothesis to each `g i₀` and pull back along `splitColourEquiv`.
    choose r hr using fun i₀ ↦
      (Submodule.mem_span_range_iff_exists_fun R).1 (hI'_span R (hg_mem i₀))
    rw [Submodule.mem_span_range_iff_exists_fun R]
    refine ⟨fun p : ι₀ × ι' ↦ r p.1 p.2, (splitColourEquiv c φ₀).injective ?_⟩
    simp only [map_sum, map_smul, h_split_prod, Fintype.sum_prod_type]
    rw [show splitColourEquiv c φ₀ f = F from rfl, ← hg]
    refine sum_congr rfl fun i₀ _ ↦ ?_
    rw [smul_eq_C_mul, ← hr i₀, map_sum, Finset.sum_mul]
    exact sum_congr rfl fun i' _ ↦ by simp [Algebra.smul_def, mul_assoc]

/-- Take finitely many rows coloured by `c`, and finitely many columns `j` of colour `τ j` and
height `h j`. Then there is a finite type `ι` and a family `I` of fillings indexed by it that is
standard in the sense of `IsStdMinorFamily`. Each `I i` gives column `j` an `h j`-tuple of rows of
colour `τ j`, and has minor product `minorProduct R (I i)`: the product of the minors on these rows
and the first `h j` columns.

This is an existence form of the standard basis theorem for Schur modules
(Akin–Buchsbaum–Weyman), stated for products of minors with coloured rows. -/
lemma exists_isStdMinorFamily {Φ J m : Type} [Fintype m] [Fintype J] (c : m → Φ)
    (τ : J → Φ) (h : J → ℕ) :
    ∃ (ι : Type) (_ : Fintype ι) (I : ι → ColoredTableau c τ h), IsStdMinorFamily I := by
  by_cases hsub : Subsingleton Φ
  · exact exists_isStdMinorFamily_of_subsingleton c τ h
  · obtain ⟨ι, _, I, hindep, hspan⟩ := exists_minorBasis_multi c τ h
    exact ⟨ι, inferInstance, I, hindep, hspan, fun [hs : Subsingleton Φ] ↦ absurd hs hsub⟩

end MultiColour

end New.GL

end MinorBasis
