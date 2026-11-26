module

public import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
public import Lib.Weil.Unramified.SplitHecke
public import Lib.Adelic.Unitary.CongruenceLevels
public import Lib.ClassField.Places.ValuationSubrings
import Lib.Weil.Unramified.HeckeGL

/-!
# Weights, Hecke polynomials and eigenforms

The automorphic side concerns functions `f` on the finite adelic points `New.Gf E n` of the definite
unitary group, with values in a complex vector space, under right translation `New.rightRegular`. At
a split place `w` (one with `star w ≠ w`), `GL n (E_w)` acts through `New.ofSplitPlace`, and
`q = New.FinPlace.q w` is the order of the residue field. We define weights and their jumps, Hecke
polynomials built from the eigenvalues of the Hecke operators `New.heckeSplit`, and eigenforms.

## Main definitions and results

* `New.Weight`, `New.jumps`: weights, and the multiset of integers attached to an embedding.
* `New.heckePoly`, `New.HasHeckePolyAt`: the polynomial made from the eigenvalues of the Hecke
  operators `New.heckeSplit`, and the statement that `f` is spherical at `w` with this polynomial.
* `New.IsEigenform`, `New.IsSphericalOff`: eigenforms at almost all places of prime norm, and at all
  split places outside a finite set and its conjugate.
* `New.HasHeckePolyAt.isMonicOfDegree`: the Hecke polynomial of a nonzero spherical eigenvector
  (`New.HasHeckePolyAt`) of rank `n` is monic of degree `n`.

Notions from other files:
* `New.stdLevel`: The subgroup K_0 = G_f ∩ GL_n(Ô) of the finite adelic unitary group, the
  stabiliser of the standard lattice Ô^n.

## Relation to the literature

Known; see `Lib.GaloisRep.Main.OddRank` and `Lib.GaloisRep.LocalGlobal.LabelCompatibility` for
sources.
-/

@[expose] public section

noncomputable section

/-!
## Weights, Hecke polynomials and eigenforms on the definite unitary group

Besides the notions of the file head, this section defines `New.HasLabel`, a condition on the action
of `GL n` of the residue field at `w`.
-/

section FormDefs

open NumberField Polynomial Function

namespace New

variable {E n M : Type} [Field E] [NumberField E] [IsCMField E] [Fintype n] [DecidableEq n]
  (f : Gf E n → M → ℂ) {w : FinPlace E} (hw : star w ≠ w)

variable (E) in
/-- Weights. For `κ : Weight E` and an infinite place `v` of `E`, `κ.1 v h` is the number of columns
of height `h` of a Young diagram, and `κ.2 v` is an integer exponent of the determinant. -/
abbrev Weight : Type := (InfinitePlace E → ℕ → ℕ) × (InfinitePlace E → ℤ)

/-- For natural numbers q, N and a sequence t in a commutative ring, the polynomial Σ_{j=0}^{N}
(−1)^j q^{j(j−1)/2} t_j X^{N−j}. -/
def heckePoly {R : Type} [CommRing R] (q N : ℕ) (t : ℕ → R) : R[X] :=
  ∑ j ∈ Finset.range (N + 1), C ((-1) ^ j * q ^ j.choose 2 * t j) * X ^ (N - j)

/-- `f` is spherical at the split place `w` with Hecke polynomial `P`: the maximal compact subgroup
`maxCompactAt n w` at `w` and `star w` fixes `f`, the `j`-th Hecke operator at `w` (`heckeSplit`)
acts on `f` by a scalar `t j`, and `P = heckePoly q (Fintype.card n) t`, that is
`P = Σ_j (−1)^j q^{j(j−1)/2} t_j X^{n−j}`, with `q` the order of the residue field at `w`. -/
def HasHeckePolyAt (w : FinPlace E) (hw : star w ≠ w) (P : ℂ[X]) : Prop :=
  f ∈ levelSpace (rightRegular ℂ (Gf E n) (M → ℂ)) (maxCompactAt n w) ∧
  ∃ t : ℕ → ℂ,
    P = heckePoly w.q (Fintype.card n) t ∧
      ∀ j : ℕ, heckeSplit (rightRegular ℂ (Gf E n) (M → ℂ)) hw j f = t j • f

/-- `f` is an eigenform for the system `P` of polynomials: `f ≠ 0`, and for all but finitely many
places `w`, if the norm of `w` is prime then `w` is split (`star w ≠ w`) and `f` is spherical
at `w` with Hecke polynomial `P w` (`New.HasHeckePolyAt`). Splitting is part of the assertion. -/
def IsEigenform (P : FinPlace E → ℂ[X]) : Prop :=
  f ≠ 0 ∧
  ∀ᶠ w : FinPlace E in Filter.cofinite, w.q.Prime → ∃ hw : star w ≠ w, HasHeckePolyAt f w hw (P w)

/-- `f` is spherical off the finite set `S` of places with Hecke polynomials `P`: `f ≠ 0`, `f` is
fixed by the integral points `stdLevel E n` that are trivial at the places of `S`
(`Gf.trivialOn n S`), and `f` has Hecke polynomial `P w` (`New.HasHeckePolyAt`) at every split
place `w` with `w ∉ S` and `star w ∉ S`. -/
def IsSphericalOff (S : Finset (FinPlace E)) (f : Gf E n → M → ℂ) (P : FinPlace E → ℂ[X]) : Prop :=
  f ≠ 0 ∧
  (∀ k ∈ stdLevel E n ⊓ Gf.trivialOn n S, rightRegular ℂ (Gf E n) (M → ℂ) k f = f) ∧
  ∀ (w : FinPlace E) (hw : star w ≠ w), w ∉ S → star w ∉ S → HasHeckePolyAt f w hw (P w)

/-- `f` has the label `Ξ`, a function on `GL n (ResField w)` with `ResField w` the residue field at
the split place `w`: the kernel of the reduction `reduceGL` from the integral matrices
`intGL n Valued.v.integer` at `w` to `GL n (ResField w)` fixes `f`, and the sum over `x` of
`star (Ξ x)` times the translate of `f` by a lift of `x` is nonzero. -/
def HasLabel (Ξ : GL n (ResField w) → ℂ) : Prop :=
  (∀ k : intGL n Valued.v.integer, reduceGL k = 1 →
    rightRegular ℂ (Gf E n) (M → ℂ) (ofSplitPlace hw k.val) f = f) ∧
  ∑ᶠ x : GL n (ResField w),
    star (Ξ x) •
      rightRegular ℂ (Gf E n) (M → ℂ) (ofSplitPlace hw (surjInv reduceGL_surjective x).val) f ≠ 0

open scoped Classical in
/-- The multiset {j − 1 − λ_j} if σ is in the CM type `Φ`, that is if σ equals `Φ v`, the embedding
that `Φ` picks at the place v of σ, else {λ_j + N − j}, 1 ≤ j ≤ N, with λ the highest weight of κ at
the place v of σ: λ_j = `κ.2 v` + Σ_{j ≤ h < N} `κ.1 v h`. The index in the code is j − 1, and `u`
is λ_j + N − j. -/
def jumps {E : Type} [Field E] [CMType E] (κ : Weight E) (N : ℕ) (σ : E →+* ℂ) : Multiset ℤ :=
  (Multiset.range N).map fun j ↦
    let u : ℤ :=
      κ.2 (InfinitePlace.mk σ) + ∑ h ∈ Finset.Ioo j N, κ.1 (InfinitePlace.mk σ) h + (N - 1 - j)
    (if σ = Φ (InfinitePlace.mk σ) then N - 1 - u else u)

end New

end FormDefs

/-!
## Coefficients and monicity of Hecke polynomials; distinct jumps

* `New.coeff_heckePoly`: the coefficients of
  `New.heckePoly q N t = ∑ j, (-1) ^ j q ^ (j choose 2) t j X ^ (N - j)`.
-/

section HeckePolyMonic

open Polynomial Finset

variable {E n : Type} {M : Type} [Field E] [New.CMType E] [Fintype n]

/-- The coefficient of `X ^ j` in `heckePoly q N t` is
`(-1) ^ (N - j) q ^ (N - j choose 2) t (N - j)` for `j ≤ N`, and `0` otherwise. -/
@[simp]
lemma New.coeff_heckePoly {R : Type} [CommRing R] (q N : ℕ) (t : ℕ → R) (j : ℕ) :
    (heckePoly q N t).coeff j =
      (if j ≤ N then (-1) ^ (N - j) * q ^ (N - j).choose 2 else 0 : ℤ) * t (N - j) := by
  rw [heckePoly, finsetSum_coeff]
  simp_rw [coeff_C_mul_X_pow]
  push_cast
  -- Only the term of index `N - j` can have degree `j`.
  grind [sum_eq_single (N - j)]

/-- Let `f ≠ 0` be a function on the finite adelic unitary group `Gf E n`, and let `P` be its Hecke
polynomial at the split place `w` (`New.HasHeckePolyAt`). Then `P` is monic of degree
`Fintype.card n`. -/
lemma New.HasHeckePolyAt.isMonicOfDegree [DecidableEq n] {f : Gf E n → M → ℂ} (hf : f ≠ 0)
    {w : FinPlace E} {hw : star w ≠ w} {P : ℂ[X]} (hP : HasHeckePolyAt f w hw P) :
    P.IsMonicOfDegree (Fintype.card n) := by
  obtain ⟨hf_fix, t, rfl, ht⟩ := hP
  -- The zeroth Hecke operator is the identity on spherical vectors, so `t 0 = 1`.
  have ht_zero : t 0 = 1 := by
    rw [← smul_left_inj hf, ← ht 0, heckeSplit, heckeGL_zero ((mem_sphericalAt_iff hw).mp hf_fix),
      one_smul]
  simp +contextual [isMonicOfDegree_iff, natDegree_le_iff_coeff_eq_zero, not_le.mpr, ht_zero]

/-- The jumps of a weight at an embedding are distinct: the multiset `jumps κ N σ` has no
repetition. -/
lemma New.Weight.nodup_jumps {E : Type} [Field E] [CMType E] (κ : Weight E) (N : ℕ) (σ : E →+* ℂ) :
    (jumps κ N σ).Nodup := by
  -- `jumps κ N σ` is the image of `range N`; the map is injective since, for `i < j`, the jumps of
  -- index `i` and `j` differ.
  rw [jumps]
  refine (Multiset.nodup_range N).map (Function.Injective.of_lt_imp_ne fun i j hij ↦ ?_)
  -- For `i < j` the sum over `Ioo j N` is at most the sum over `Ioo i N`, while `N - 1 - j` is
  -- smaller than `N - 1 - i` in `ℤ`.
  have h_sum : ∑ h ∈ Ioo j N, κ.1 (.mk σ) h ≤ ∑ h ∈ Ioo i N, κ.1 (.mk σ) h :=
    sum_le_sum_of_subset (Ioo_subset_Ioo hij.le le_rfl)
  grind

end HeckePolyMonic

end
