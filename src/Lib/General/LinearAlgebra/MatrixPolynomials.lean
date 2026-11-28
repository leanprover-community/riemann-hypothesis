module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.PiTensorProduct.Generators
import TauCeti.LinearAlgebra.Matrix.Charpoly.Resultant
import TauCeti.LinearAlgebra.Matrix.Polynomial

/-!
# Minors and polynomials of matrices

This file contains general lemmas on matrices over commutative rings, and three definitions used
elsewhere: a minor of a matrix of variables, a non-degeneracy condition on a trace form and a
freeness condition on a family of integers.

## Main definitions and results

* `New.Rows.variableMinor_ne_zero`: a minor of a matrix of variables with distinct rows and distinct
  columns is not zero.
* `New.IsTraceNondeg r`: the trace form is non-degenerate on the span of the matrices `r g`.
* `New.HasNoSmallRelations e`: here `e : Fin n → ℤ`, with `n` a natural number. A sum of at most
  `(n + 1) ^ 2` of the integers `e i`, together with the number of terms, determines how often each
  `e i` occurs.
* `New.det_eval_eq_zero_iff_not_linearIndependent`: over a field, finitely many functions
  `v j : X → k` are linearly dependent if and only if all the determinants `det (v j (x i))` vanish.
* `New.charpoly_dvd_charpoly_aeval_comp`, `New.isUnit_aeval_iff_isCoprime`: the characteristic
  polynomial of `Y` divides that of `q(Y)` composed with `q`, and `z(Y)` is invertible iff `z` is
  coprime to the characteristic polynomial of `Y`.
* `New.exists_gl_map_eq_of_fixed`: an invertible matrix fixed by `σ` lifts along any injective
  ring map whose image contains the fixed points of `σ`.
-/

@[expose] public section

/-! ## A nonvanishing minor of the matrix of variables -/

section LetterMinor

open Matrix MvPolynomial

variable {Φ : Type*} {l : Type*} {n n' : Type*} [Fintype l] [DecidableEq l]

/-- The minor `det (X (τ, i a, j b))`, with `a b : l`, of the matrix of variables attached to `τ`,
taken in the rows `i` and the columns `j`. -/
noncomputable def New.Rows.variableMinor (τ : Φ) (i : l → n') (j : l → n) :
    MvPolynomial (Φ × n' × n) ℂ :=
  (of fun a b : l ↦ (X (τ, i a, j b) : MvPolynomial (Φ × n' × n) ℂ)).det

/-- If the row indices `i` and the column indices `j` are injective, then the determinant
`variableMinor τ i j` of the matrix of variables `X (τ, i a, j b)` is a nonzero polynomial. -/
@[simp↓]
lemma New.Rows.variableMinor_ne_zero (τ : Φ) (i : l → n') (j : l → n) (hi : i.Injective)
    (hj : j.Injective) : variableMinor τ i j ≠ 0 := by
  -- The minor is the generic determinant, which is not zero, with variables renamed injectively.
  let f : l × l → Φ × n' × n := fun x ↦ (τ, x.map i j)
  have hf : f.Injective := (Prod.mk_right_injective τ).comp (hi.prodMap hj)
  have h_rename : variableMinor τ i j = rename f (mvPolynomialX l l ℂ).det := by
    simp [det_apply, variableMinor, f]
  rw [h_rename, map_ne_zero_iff _ (rename_injective f hf)]
  exact det_mvPolynomialX_ne_zero l ℂ

end LetterMinor

/-! ## Trace forms, free integers and vanishing minors -/

section TraceFormDefs

open Matrix

variable {k G n : Type} [Field k] [Group G] [Fintype n] [DecidableEq n]

/-- The trace form is non-degenerate on the span of the matrices `r g`: any `x` in that span with
`tr (x * r g) = 0` for all `g` is zero. -/
def New.IsTraceNondeg (r : G →* GL n k) : Prop :=
  ∀ x ∈ Submodule.span k (Set.range fun g : G ↦ (r g : Matrix n n k)),
    (∀ g : G, (x * r g).trace = 0) → x = 0

/-- The integers `e i` are free: two vectors `α`, `β` of natural numbers with
`∑ α i = ∑ β i ≤ (n + 1) ^ 2` and `∑ α i * e i = ∑ β i * e i` are equal. -/
def New.HasNoSmallRelations {n : ℕ} (e : Fin n → ℤ) : Prop :=
  ∀ d : ℕ, d ≤ (n + 1) ^ 2 → {α : Fin n →₀ ℕ | Finsupp.degree α = d}.InjOn (Finsupp.weight e)

/-- Functions `v j : X → k` to a field, indexed by the finite type `n`, are linearly dependent if
and only if, for every family of points `x : n → X`, the determinant of the square evaluation
matrix `of (flip v ∘ x)`, with entries `v j (x i)`, is zero. -/
lemma New.det_eval_eq_zero_iff_not_linearIndependent {X : Type*} {v : n → X → k} :
    (∀ x : n → X, det (of (flip v ∘ x)) = 0) ↔ ¬LinearIndependent k v := by
  refine ⟨fun h_det h_indep ↦ ?_, fun h_dep x ↦ ?_⟩
  · -- If `v` is independent, the vectors `(v i x)_i` span `n → k`, so the determinant, which is
    -- multilinear in the rows and vanishes on all families of them, would be zero.
    have h_span : Submodule.span k (Set.range (flip v)) = ⊤ :=
      span_flip_eq_top_iff_linearIndependent.2 h_indep
    have h_zero : (detRowAlternating (n := n) (R := k)).toMultilinearMap = 0 :=
      MultilinearMap.ext_of_span_eq_top (fun _ ↦ h_span) h_det
    have h_one : det (1 : Matrix n n k) = 0 := DFunLike.congr_fun h_zero (1 : Matrix n n k)
    simp at h_one
  · -- A relation among the `v i` is a relation among the columns.
    exact det_eq_zero_of_not_linearIndependent_cols fun h_cols ↦
      h_dep (.of_comp (LinearMap.funLeft k k x) h_cols)

end TraceFormDefs

/-!
## Polynomials evaluated at matrices and fixed matrices

`New.star_aeval`, `New.map_aeval_matrix` and `New.aeval_semiconj` say that `z(Y)` is compatible
with star, with ring maps and with intertwining matrices.
-/

namespace New

open Matrix Polynomial GeneralLinearGroup Finset Algebra

variable {R S n m : Type*} [CommRing R] [CommRing S] [Fintype n] [DecidableEq n] {σ : S →+* S}
  [Fintype m] {ψ : R →+* S} {c : Matrix m n R} {x Y : Matrix n n R}

/-- For an `R`-algebra `A` with compatible star structures, the star of `q(x)` is the value at
`star x` of the polynomial obtained from `q` by applying the star of `R` to its coefficients. -/
lemma star_aeval {A : Type*} [StarRing R] [Ring A] [StarRing A] [Algebra R A] [StarModule R A]
    (x : A) (q : R[X]) : star (aeval x q) = aeval (star x) (q.map (starRingEnd R)) := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial i a =>
    simp only [Polynomial.map_monomial, aeval_monomial, ← Algebra.smul_def, star_smul, star_pow,
      starRingEnd_apply]

/-- Applying the ring map `ψ` to the entries of `z(Y)` gives the value at the matrix `Y.map ψ` of
the polynomial `z.map ψ`. -/
lemma map_aeval_matrix (ψ : R →+* S) (Y : Matrix n n R) (z : R[X]) :
    (aeval Y z).map ψ = aeval (Y.map ψ) (z.map ψ) :=
  (aeval_map Y ψ z).symm

/-- If `c` intertwines the square matrices `x` and `y`, then it intertwines `q(x)` and `q(y)`. -/
lemma aeval_semiconj [DecidableEq m] {y : Matrix m m R} (h_semiconj : c * x = y * c) (q : R[X]) :
    c * aeval x q = aeval y q * c :=
  (aeval_mul_eq_mul_aeval h_semiconj.symm q).symm

/-- For a normal matrix `x`, the conjugate transpose of `w(x)` commutes with `z(x)`. -/
lemma commute_conjTranspose_aeval [StarRing R] (x : Matrix n n R) [IsStarNormal x] {w z : R[X]} :
    Commute (aeval x w)ᴴ (aeval x z) := by
  -- `star x` commutes with `x`, hence with `w(x)`; so `w(x)ᴴ` commutes with `x`, hence with `z(x)`.
  have h_star : Commute (star x) (aeval x w) := aeval_semiconj (star_comm_self' x) w
  have h_conj : Commute (aeval x w)ᴴ x := h_star.symm.star_left
  exact aeval_semiconj h_conj.eq z

/-- The characteristic polynomial of `Y` divides `χ(q(X))`, where `χ` is the characteristic
polynomial of `q(Y)`. -/
lemma charpoly_dvd_charpoly_aeval_comp (q : R[X]) : Y.charpoly ∣ (aeval Y q).charpoly.comp q := by
  -- In `R[X][X]` the polynomial `C X - X` divides `C q - q.map C`. Evaluate the outer variable at
  -- `Y`, so that `X - Y` divides `q(X) - q(Y)` as matrices over `R[X]`, and take determinants.
  have h_poly : (C X - X : R[X][X]) ∣ C q - q.map C := by
    simpa [eval_map] using ((q.map C).map C).sub_dvd_eval_sub (C X) X
  have h_mat : charmatrix Y ∣ scalar n q - (aeval Y q).map C := by
    simpa [charmatrix, algebraMap_eq_diagonal, Pi.algebraMap_def] using
      aeval_dvd (Y.map C) h_poly
  have h_det : det (scalar n q - (aeval Y q).map C) = (aeval Y q).charpoly.comp q := by
    rw [← eval_charpoly, charpoly_map, eval_map, Polynomial.comp]
  simpa only [coe_detMonoidHom, h_det, ← charpoly.eq_def] using map_dvd detMonoidHom h_mat

/-- The matrix `z(Y)` is invertible if and only if the polynomial `z` is coprime to the
characteristic polynomial of `Y`. -/
lemma isUnit_aeval_iff_isCoprime {z : R[X]} : IsUnit (aeval Y z) ↔ IsCoprime Y.charpoly z := by
  rcases subsingleton_or_nontrivial R with _ | _
  · exact iff_of_true (isUnit_of_subsingleton _) ⟨0, 0, Subsingleton.elim _ _⟩
  · rw [isUnit_iff_isUnit_det, det_aeval_eq_resultant Y z le_rfl,
      ← charpoly_natDegree_eq_dim Y, isUnit_resultant_iff_isCoprime Y.charpoly_monic]

/-- Let `σ` be a ring endomorphism of `S` and `ψ : R →+* S` an injective ring homomorphism whose
image contains every element fixed by `σ`. If applying `σ` to the entries of `g : GL n S` leaves
`g` unchanged, then `g` is obtained from an element of `GL n R` by applying `ψ` to the entries. -/
lemma exists_gl_map_eq_of_fixed (hψ_inj : Function.Injective ψ)
    (h_fixed : ∀ x : S, σ x = x → x ∈ ψ.range) {g : GL n S} (hg : g.map σ = g) :
    ∃ k : GL n R, GeneralLinearGroup.map ψ k = g := by
  -- Lift the entries of `g` and of `g⁻¹`; the lifts are inverse to each other as `ψ` is injective.
  have h_lift {u : GL n S} (hu : u.map σ = u) : ∃ N : Matrix n n R, N.map ψ = u := by
    choose N hN using fun i j : n ↦ h_fixed (u i j) ((GeneralLinearGroup.ext_iff _ _).1 hu i j)
    exact ⟨of N, Matrix.ext hN⟩
  obtain ⟨N, hN⟩ := h_lift hg
  obtain ⟨M, hM⟩ := h_lift (u := g⁻¹) (by rw [map_inv, hg])
  have h_inv : N * M = 1 := map_injective hψ_inj (by simp [hN, hM])
  exact ⟨.mkOfMulEqOne N M h_inv, Units.ext hN⟩

end New
