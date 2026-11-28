module

import Mathlib.Algebra.Ring.IsFormallyReal
public import Lib.General.LinearAlgebra.TensorChains
public import Lib.Adelic.AutomorphicForms.SmoothAlgebraicForms
public import Lib.Weil.DualPair.Defs
public import Lib.Weil.Periods.Grading
import Lib.ClassField.HeckeCharacter.AlgebraicValues
import Lib.General.LinearAlgebra.HermiteForm
import Lib.Weil.DualPair.WeilAction

/-!
# Graded lattices, integrality away from q and admissible combinations of translates

This file provides tools for the computations at the finite places of the seesaw. A grading
(`New.Grading`) presents a hermitian space `V` as `X` plus a string of `s` basis vectors, and
`New.gradedLatticeBasis` is an explicit basis of a lattice in it, unimodular when `N = π π̄`.
Integrality lemmas handle numbers integral away from `q` and `l`-adic units.
`New.Seesaw.IsAdmissibleCombination v A n d p B z` says that `z = ∑ r(x) v(x)` with `r` finitely
supported in `A`, denominator `d` away from `n`, and size `B` when `p` holds. Moved vacua
(translates of the vacuum vector of the Weil representation, moved by a finite unitary element) and
the values of the operators `V.schrodingerOp` attached to functions modulo `𝔪` are such
combinations of translates.

## Main definitions and results

* `New.Seesaw.integralAway`, `New.Seesaw.IsAdmissibleCoeffs`: complex numbers integral away from
  `n`, and finite families of coefficients with bounded denominator and, on demand, bounded size.
* `New.Seesaw.weightedTranslations`, `New.Seesaw.translations`: finite adelic vectors with given
  denominators away from `q`. They index the translates that may occur in a combination.
* `New.Seesaw.isUnimodular_gradedLatticeBasis_gram`: if `N = π π̄`, the Gram matrix of
  `New.gradedLatticeBasis` is hermitian and invertible over every subring.
* `New.Seesaw.exists_conjTranspose_mul_gradedGram_mul_eq_signMatrix`: for `N > 0` the form is
  congruent over `ℂ` to a diagonal of signs, `(s + 1) / 2` of them negative.
* `New.Seesaw.IsAdmissibleCombination.bind`: substitution; denominators and sizes multiply. The
  rules for scalars, bilinear maps and pure tensors follow from it.
* `New.Seesaw.isAdmissibleCombination_weil_vacElem`,
  `New.Seesaw.isAdmissibleCombination_schrodingerOp`: moved vacua and the values of
  `V.schrodingerOp` are admissible combinations of translates.

Notions from other files:
* `New.Space`: a hermitian space with a point, given by a matrix J over E and x in GL_n(𝔸) with
  xᴴJx equal to the diagonal matrix of its signs at the infinite places and 1 at the finite places.
* `New.gradedGram e N`: the Gram matrix of X plus a string of length s: the identity on X; string
  vectors a, b with a + b = s − 1 pair to 1, or to −N if a = b.
* `New.finMultiplier`: for g in the finite adelic unitary group `New.Gf`,
  Δ_f(g) = υ(det u)|det u|^(−1/2), with υ the splitting character of the Weil data and u a chosen
  invertible matrix with uÔⁿ = Ôⁿ ∩ g⁻¹Ôⁿ.
* `New.AutChar.HasWeight`: μ has weight e and tame part ψ: almost all residue characters ψ_w are
  trivial, and μ(u) = ∏_v u_v^{e(v)} · ∏_w ψ_w(u mod w) whenever u has integral finite part.

## Relation to the literature

See `New.UpperBound.Seesaw.SeesawIdentity` for related work. See
`Lib.ClassField.Global.CMSplittingCharacters` for sources.
-/

@[expose] public section

noncomputable section

/-!
## Lattices of graded spaces and admissible coefficients

* `New.Seesaw.IsSplitSquarefree`: `N = π π̄`, where `π` is a uniformiser at the places of `P` and a
  unit elsewhere, and no place of `P` has its conjugate in `P`.

Valuations `v` are multiplicative: `v x ≤ 1` means integral, and `exp (-1)` is the value at a
uniformiser.
-/

section LatticeAndTorsionDefs

open Matrix Valued

namespace New

variable {E R X' ι : Type*} [DecidableEq X'] [Field E] [CMType E] [Fintype ι]
  [DecidableEq ι] {ε : ι → ℤˣ} {s : ℕ} {N : E} [CommRing R] [StarRing R] {V : Space E ι ε}

/-- A basis matrix (the basis vectors are its columns), for `X = X' ⊕ Unit` and a string of `s`
vectors, indexed by `ι` through `e`; write `π̄ = star π` and `ā = star a`. For odd `s`: the vectors
of `X'` are unchanged, the last vector `y` of `X` is replaced by `y / π̄ + u z / (π π̄)` with `z`
the middle vector of the string, and each string vector is multiplied by `u`. For even `s`:
diagonal, `1` on `X`, `u a⁻¹` on the first half of the string and `u ā` on the second half. -/
def gradedLatticeBasis (e : (X' ⊕ Unit) ⊕ Fin s ≃ ι) (a π : Rˣ) (u : unitary R) : Matrix ι ι R :=
  reindex e e
    (fromBlocks (if Odd s then diagonal (1 ⊕ᵥ fun _ : Unit ↦ ((star π)⁻¹ : Rˣ).val) else 1) 0
      (of fun b : Fin s ↦
        0 ⊕ᵥ fun _ : Unit ↦ if b = b.rev then (u : R) * ((star π * π)⁻¹ : Rˣ).val else 0)
      (diagonal fun b : Fin s ↦
        (u : R) * if Odd s then 1 else if 2 * (b : ℕ) < s then (a⁻¹ : Rˣ).val else star (a : R)))

/-- Let `Y` present the hermitian space `V` as `X' ⊕ Unit` plus a string of `s` vectors. The
condition says that the finite frame `V.xFin` spans the same `Ô`-lattice as the basis
`New.gradedLatticeBasis Y.indexEquiv a π u`: the two differ by some `k` in `GL(Ô)`. -/
def Grading.SpansLattice (Y : Grading V N (X' ⊕ Unit) s) (a π : (𝔸f E)ˣ) (u : unitary (𝔸f E)) :
    Prop :=
  ∃ k ∈ intGL ι (Ô E), V.xFin.val = gradedLatticeBasis Y.indexEquiv a π u * k.val

namespace Seesaw

/-- The subring of complex numbers whose image under every ring homomorphism `ℂ → ℂ_l` is
integral (has norm at most `1`), for every prime `l` coprime to `n`. -/
def integralAway (n : ℕ) : Subring ℂ where
  carrier := {z : ℂ | ∀ (l : ℕ) [Fact l.Prime], l.Coprime n → ∀ ι : ℂ →+* ℂ_[l], ‖ι z‖ ≤ 1}
  mul_mem' hx hy l _ hl ι := by
    simpa only [map_mul, norm_mul] using
      (mul_le_of_le_one_left (norm_nonneg _) (hx l hl ι)).trans (hy l hl ι)
  one_mem' := by simp only [Set.mem_ofPred_eq, map_one, norm_one, le_refl, implies_true]
  add_mem' hx hy l _ hl ι := by
    grw [map_add, IsUltrametricDist.norm_add_le_max, hx l hl ι, hy l hl ι, max_self]
  zero_mem' := by
    simp only [Set.mem_ofPred_eq, map_zero, norm_zero, zero_le_one, implies_true]
  neg_mem' := by simp only [Set.mem_ofPred_eq, map_neg, norm_neg, imp_self, implies_true]

/-- The conditions on finitely supported coefficients `r`: the support lies in `A`, each `d * r x`
is integral away from `n` (`New.Seesaw.integralAway`) and, if `p` holds, `∑ ‖σ (r x)‖ ≤ B` for
all automorphisms `σ` of `ℂ`. -/
structure IsAdmissibleCoeffs {X : Type*} (A : Set X) (n d : ℕ) (p : Prop) (B : ℝ) (r : X →₀ ℂ) :
    Prop where
  /-- The points with a nonzero coefficient lie in `A`. -/
  support_subset : ∀ x ∈ r.support, x ∈ A
  /-- Every coefficient, multiplied by `d`, is integral away from `n`. -/
  integral (x : X) : d * r x ∈ integralAway n
  /-- If `p` holds, then for every field automorphism `σ` of `ℂ` the sum of the absolute values of
  the `σ`-conjugates of the coefficients is at most `B`. -/
  sum_norm_le : p → ∀ σ : ℂ ≃+* ℂ, r.sum (fun (_ : X) (c : ℂ) ↦ ‖σ c‖) ≤ B

section

variable {E : Type*} [Field E] [NumberField E]

/-- The group of finite adelic vectors `x` such that `d i * x i` is integral at every place `w` not
dividing `q`, for every index `i`. There is no condition at the places dividing `q`. -/
def weightedTranslations (q : ℕ) (d : ι → 𝔸f E) : AddSubgroup (ι → 𝔸f E) where
  carrier := {x : ι → 𝔸f E | ∀ (i : ι) (w : FinPlace E), ↑q ∉ w.asIdeal → v ((d i * x i) w) ≤ 1}
  add_mem' {x y} hx hy i w hw := by
    simpa only [Pi.add_apply, mul_add, IsDedekindDomain.FiniteAdeleRing.add_apply,
      IsDedekindDomain.FiniteAdeleRing.mul_apply] using v.map_add_le (hx i w hw) (hy i w hw)
  zero_mem' := by
    simp only [IsDedekindDomain.FiniteAdeleRing.mul_apply, map_mul, Set.mem_ofPred_eq,
      Pi.zero_apply, IsDedekindDomain.FiniteAdeleRing.zero_apply, map_zero, mul_zero, zero_le,
      implies_true]
  neg_mem' := by
    simp only [IsDedekindDomain.FiniteAdeleRing.mul_apply, map_mul, Set.mem_ofPred_eq,
      Pi.neg_apply, finAdele_neg_apply, Valuation.map_neg, imp_self, implies_true]

/-- The group of finite adelic vectors `x` indexed by `ι` such that `d * x i` is integral at every
place `w` not dividing `q`, for every index `i`. -/
abbrev translations (ι : Type*) (q : ℕ) (d : 𝔸f E) : AddSubgroup (ι → 𝔸f E) :=
  weightedTranslations (E := E) q fun _ : ι ↦ d

end

open scoped Classical in
/-- The element `N` of `E` factors as `π π̄` for the finite idele `π`, which is a uniformiser at the
places of `P` and a unit at all other places, and no place of `P` has its conjugate in `P`. -/
structure IsSplitSquarefree (P : Finset (FinPlace E)) (N : E) (π : (𝔸f E)ˣ) : Prop where
  /-- In the finite adeles `N = π π̄`. -/
  algebraMap_eq_mul_star : algebraMap E (𝔸f E) N = π * star (π : 𝔸f E)
  /-- The idele `π` is a uniformiser at the places of `P` and a unit at the others. -/
  v_apply (w : FinPlace E) : v ((π : 𝔸f E) w) = if w ∈ P then WithZero.exp (-1) else 1
  /-- No place of `P` has its conjugate in `P`. -/
  star_notMem : ∀ w ∈ P, star w ∉ P

end Seesaw

end New

end LatticeAndTorsionDefs

/-!
## A unimodular lattice basis and the signature of the graded Gram matrix

`New.gradedGram e N` is the Gram matrix of `X ⊕ Unit` (identity) plus a string of length `s`
(antidiagonal, with `-N` in the middle if `s` is odd), and `New.gradedLatticeBasis` is a basis of
a lattice in this space.
-/

namespace New.Seesaw

open Matrix Fintype Exchange

variable {R X ι : Type _} [DecidableEq X] {s N : ℕ} [CommRing R]

/-- A form on `X ⊕ Unit` plus a string of `s` vectors, by blocks: identity on `X`; string vectors
paired antidiagonally to `1`, with `-p` in the middle; for odd `s` the vector of `Unit` has norm
`q` and pairs to `-1` with the middle vector (for even `s` it is a unit vector orthogonal to the
string). -/
def gluedGram {K : Type*} [CommRing K] (p q : K) :
    Matrix ((X ⊕ Unit) ⊕ Fin s) ((X ⊕ Unit) ⊕ Fin s) K :=
  let C : Matrix (X ⊕ Unit) (Fin s) K := of (0 ⊕ᵥ fun _ b ↦ if b = b.rev then -1 else 0)
  fromBlocks (diagonal (1 ⊕ᵥ fun _ : Unit ↦ if Odd s then q else 1)) C Cᵀ
    (of fun b c ↦ if b = c.rev then (if b = c then -p else 1) else 0)

/-- For odd `s`, the reversal `c ↦ s - 1 - c` of `Fin s` fixes exactly the middle index. -/
lemma eq_rev_iff_of_odd (hs : Odd s) (c : Fin s) : c = c.rev ↔ c = ⟨s / 2, by grind⟩ := by
  rcases hs with ⟨k, rfl⟩
  have hc : (c : ℕ) < 2 * k + 1 := c.isLt
  rw [Fin.ext_iff, Fin.ext_iff, Fin.val_rev]
  dsimp only
  omega

/-- For even `s`, the reversal `c ↦ s - 1 - c` of `Fin s` has no fixed point. -/
lemma ne_rev_of_not_odd (hs : ¬ Odd s) (c : Fin s) : c ≠ c.rev := by
  obtain ⟨k, rfl⟩ := Nat.not_odd_iff_even.mp hs
  intro h
  have hc : (c : ℕ) < k + k := c.isLt
  rw [Fin.ext_iff, Fin.val_rev] at h
  omega

/-- A ring homomorphism carries `gluedGram p q` to the form with parameters `(f p, f q)`. -/
lemma map_gluedGram {K L : Type*} [CommRing K] [CommRing L] (f : K →+* L) (p q : K) :
    (gluedGram p q).map f = gluedGram (X := X) (s := s) (f p) (f q) := by
  ext ((i | i) | b) ((j | j) | c) <;>
    simp only [gluedGram, transpose_of, map_apply, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
      fromBlocks_apply₂₁, fromBlocks_apply₂₂, diagonal_apply, of_apply, Function.swap,
      Sum.inl.injEq, Sum.elim_inl, Sum.elim_inr, Pi.one_apply, Pi.zero_apply, apply_ite f,
      map_one, map_zero, map_neg, reduceCtorEq]

/-- The matrices `gluedGram p 0` and `gluedGram 0 p` multiply to `1`. -/
lemma gluedGram_mul_eq_one [Fintype X] {K : Type*} [CommRing K] (p : K) :
    gluedGram (X := X) (s := s) p 0 * gluedGram 0 p = 1 := by
  -- Compute the block product by cases on whether `s` is odd (existence of a middle vector).
  by_cases hs : Odd s
  · simp only [gluedGram, diagonal, hs, ↓reduceIte, eq_rev_iff_of_odd hs, transpose_of,
      neg_zero, fromBlocks_multiply, ← fromBlocks_one, ← ext_iff, Sum.forall, fromBlocks_apply₁₁,
      Matrix.add_apply, Matrix.mul_apply, of_apply, mul_ite, ite_mul, zero_mul, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, Sum.elim_inl, Pi.one_apply, mul_one, Function.swap,
      Pi.zero_apply, Finset.sum_const_zero, add_zero, Sum.elim_inr, mul_neg, fromBlocks_apply₁₂,
      Finset.sum_ite_eq, Matrix.zero_apply, Sum.inl.injEq, Matrix.one_apply, implies_true,
      reduceCtorEq, and_self, ite_self, fromBlocks_apply₂₁, zero_add, fromBlocks_apply₂₂,
      ite_eq_left_iff, ite_eq_right_iff, neg_eq_zero, true_and, forall_const, neg_mul,
      one_mul, sum_sum_type, Finset.univ_unique, PUnit.default_eq_unit, Finset.sum_ite_irrel,
      Finset.sum_neg_distrib, Finset.sum_const, Finset.card_singleton, one_smul, Fin.rev_rev]
    let m : Fin s := ⟨s / 2, by obtain ⟨k, rfl⟩ := hs; omega⟩
    have hm : m = m.rev := (eq_rev_iff_of_odd hs m).2 rfl
    dsimp only [m] at hm
    refine ⟨⟨neg_neg 1, fun b h1 h2 ↦ ?_⟩, fun b ↦ ⟨?_, fun b1 ↦ ?_⟩⟩
    · exact False.elim (h1 ((eq_rev_iff_of_odd hs b).2 ((Fin.rev_eq_iff.mp h2).trans hm.symm)).symm)
    · by_cases hb : b = m
      · dsimp only [m] at hb; subst hb; simp only [← hm, ↓reduceIte, add_neg_cancel]
      · dsimp only [m] at hb
        have hbr : b ≠ (⟨s / 2, by obtain ⟨k, rfl⟩ := hs; omega⟩ : Fin s).rev :=
          fun h ↦ hb (h.trans hm.symm)
        simp only [hb, hbr, ↓reduceIte, neg_zero, add_zero]
    · by_cases hb1 : b1 = m
      · dsimp only [m] at hb1; subst hb1
        by_cases hbb1 : b = ⟨s / 2, by obtain ⟨k, rfl⟩ := hs; omega⟩
        · rw [hbb1, ← hm]; simp only [↓reduceIte, neg_neg, add_zero]
        · simp only [← hm, hbb1, ↓reduceIte, neg_zero, add_zero]
      · dsimp only [m] at hb1
        have hb1r : b1 ≠ b1.rev := fun h ↦ hb1 ((eq_rev_iff_of_odd hs b1).1 h)
        by_cases hbb1 : b = b1
        · subst hbb1; simp only [hb1, hb1r, hb1r.symm, ↓reduceIte, zero_add]
        · simp only [hb1, hb1r.symm, hbb1, ↓reduceIte, add_zero]
  · simp only [gluedGram, diagonal, hs, ↓reduceIte, ne_rev_of_not_odd hs, transpose_of,
      neg_zero, fromBlocks_multiply, ← fromBlocks_one, ← ext_iff, Sum.forall, fromBlocks_apply₁₁,
      Matrix.add_apply, Matrix.mul_apply, of_apply, mul_ite, ite_mul, zero_mul, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, Sum.elim_inl, Pi.one_apply, mul_one, Function.swap,
      Pi.zero_apply, Finset.sum_const_zero, add_zero, Sum.elim_inr, fromBlocks_apply₁₂,
      Finset.sum_ite_eq, Matrix.zero_apply, Sum.inl.injEq, Matrix.one_apply, implies_true,
      reduceCtorEq, and_self, ite_self, fromBlocks_apply₂₁, fromBlocks_apply₂₂, sum_sum_type,
      Finset.univ_unique, PUnit.default_eq_unit, Fin.rev_rev, zero_add, true_and]
    intro b c
    by_cases hbc : b = c <;> simp only [hbc, ↓reduceIte, eq_comm]
    · split_ifs with h1; exact False.elim (ne_rev_of_not_odd hs c h1); rfl
    · split_ifs with h1; exact False.elim (ne_rev_of_not_odd hs c h1); rfl

/-- A ring homomorphism carries the graded Gram matrix with parameter `r` to the one with `f r`. -/
lemma map_gradedGram (e : (X ⊕ Unit) ⊕ Fin s ≃ ι) {S : Type*} [CommRing S] (f : S →+* R) (r : S) :
    (gradedGram e r).map f = gradedGram e (f r) := by
  simp only [gradedGram, ← ext_iff, map_apply, submatrix_apply, reindex_equiv e,
    Equiv.symm_apply_apply, Sum.forall, fromBlocks_apply₁₁, Matrix.one_apply, apply_ite f,
    map_one, map_zero, implies_true, and_self, fromBlocks_apply₁₂, Matrix.zero_apply,
    fromBlocks_apply₂₁, fromBlocks_apply₂₂, of_apply, map_neg]

/-- The image of the graded Gram matrix `New.gradedGram e N`, with `N` a natural number, under a
ring homomorphism `f` into a star ring is hermitian. -/
lemma isHermitian_map_gradedGram_natCast (e : (X ⊕ Unit) ⊕ Fin s ≃ ι) {S : Type*} [CommRing S]
    [StarRing R] (f : S →+* R) :
    ((gradedGram e (N : S)).map f).IsHermitian := by
  -- The blocks are `1`, `0`, `0` and a symmetric matrix with entries fixed by `star`.
  rw [map_gradedGram, map_natCast]
  refine (isHermitian_one.fromBlocks (by simp) (.ext fun b c ↦ ?_)).submatrix e.symm
  have h_rev : c = b.rev ↔ b = c.rev := by rw [eq_comm, Fin.rev_eq_iff]
  have h_eq : c = b ↔ b = c := eq_comm
  change star (if c = b.rev then (if c = b then -(N : R) else 1) else 0) =
    if b = c.rev then (if b = c then -(N : R) else 1) else 0
  simp only [h_rev, h_eq, apply_ite star, star_neg, star_natCast, star_one, star_zero]

variable [Fintype X] [Fintype ι]

omit [Fintype X] in
/-- Let `e` index `X ⊕ Unit` and a string of `s` vectors by `ι`. Let `J = New.gradedGram e N` be the
form that is the identity on `X ⊕ Unit` and pairs string vectors `b` and `s - 1 - b` to `1`, or to
`-N` if they are equal, carried from `S` to the star ring `R` by `f`; write `π̄ = star π` and
`ā = star a`. The columns of `B = New.gradedLatticeBasis e a π u` are the basis vectors, changed as
follows. For odd `s`, the string vectors are multiplied by `u` and the vector `y` of `Unit` becomes
`y / π̄ + u z / (π π̄)`, with `z` the middle string vector. For even `s`, the first half of the
string is multiplied by `u a⁻¹` and the second half by `u ā`. If `N = π π̄` in `R`, then `Bᴴ J B`
is `gluedGram N 0`, reindexed by `e`. It agrees with `J` except that, for odd `s`, the vector of
`Unit` has norm `0` and pairs to `-1` with the middle vector. -/
lemma gram_gradedLatticeBasis_eq_gluedGram
    [Finite X] (e : (X ⊕ Unit) ⊕ Fin s ≃ ι) {S : Type*} [CommRing S]
    [StarRing R] {f : S →+* R} (a : Rˣ) {π : Rˣ} (u : unitary R)
    (hN : f (N : S) = π * star (π : R)) :
    (gradedLatticeBasis e a π u)ᴴ * (gradedGram e (N : S)).map f * gradedLatticeBasis e a π u =
      reindex e e (gluedGram (N : R) 0) := by
  have := Fintype.ofFinite X
  -- The blocks of the basis are `T`, `0`, `Z`, `D`; the form is `G` on the string.
  let T : Matrix (X ⊕ Unit) (X ⊕ Unit) R :=
    if Odd s then diagonal (1 ⊕ᵥ fun _ : Unit ↦ ((star π)⁻¹ : Rˣ).val) else 1
  let Z : Matrix (Fin s) (X ⊕ Unit) R := of fun b : Fin s ↦
    0 ⊕ᵥ fun _ : Unit ↦ if b = b.rev then (u : R) * ((star π * π)⁻¹ : Rˣ).val else 0
  let D : Matrix (Fin s) (Fin s) R := diagonal fun b : Fin s ↦
    (u : R) * if Odd s then 1 else if 2 * (b : ℕ) < s then (a⁻¹ : Rˣ).val else star (a : R)
  let G : Matrix (Fin s) (Fin s) R :=
    of fun b c ↦ f (if b = c.rev then (if b = c then -(N : S) else 1) else 0)
  let C : Matrix (X ⊕ Unit) (Fin s) R := of (0 ⊕ᵥ fun _ b ↦ if b = b.rev then -1 else 0)
  -- The unit `u` drops out as `ū u = 1`. For even `s` the factors `a⁻¹` and `ā` on partners in
  -- the string cancel; for odd `s` the last vector of `X ⊕ Unit` is glued, by `π π̄ = N`.
  have hu : star (u : R) * u = 1 := Unitary.coe_star_mul_self u
  have hu : star (u : R) * u = 1 := Unitary.coe_star_mul_self u
  have hπ1 : ((star π)⁻¹ : Rˣ).val * star (π : R) = 1 := (star π).inv_mul
  have hπ2 : (π⁻¹ : Rˣ).val * (π : R) = 1 := π.inv_mul
  have h_star_inv (z : Rˣ) : star (z⁻¹ : Rˣ).val = ((star z)⁻¹ : Rˣ).val := by
    have h : star (z⁻¹ : Rˣ).val * star (z : R) = 1 := by rw [← star_mul, z.mul_inv, star_one]
    calc star (z⁻¹ : Rˣ).val = star (z⁻¹ : Rˣ).val * 1 := (mul_one _).symm
      _ = star (z⁻¹ : Rˣ).val * (star (z : R) * ((star z)⁻¹ : Rˣ).val) := by
          rw [← (star z).mul_inv, Units.coe_star]
      _ = (star (z⁻¹ : Rˣ).val * star (z : R)) * ((star z)⁻¹ : Rˣ).val := (mul_assoc _ _ _).symm
      _ = ((star z)⁻¹ : Rˣ).val := by rw [h, one_mul]
  have h_X : Tᴴ * T + Zᴴ * G * Z = diagonal (1 ⊕ᵥ fun _ ↦ if Odd s then 0 else 1) := by
    by_cases hs : Odd s
    · simp only [hs, ↓reduceIte, diagonal, Units.coe_star_inv, eq_rev_iff_of_odd hs,
        _root_.mul_inv_rev, Units.val_mul, ← ext_iff, Matrix.add_apply, Matrix.mul_apply,
        conjTranspose_apply, of_apply, apply_ite star, star_zero, mul_ite, ite_mul, zero_mul,
        mul_zero, Finset.sum_ite_eq', Finset.mem_univ, Sum.forall, Sum.elim_inl, Pi.one_apply,
        star_one, mul_one, Pi.zero_apply, Finset.sum_const_zero, add_zero, Sum.elim_inr,
        star_star, Sum.inl.injEq, reduceCtorEq, implies_true, star_mul', forall_const,
        true_and, T, Z, G]
      refine ⟨fun a ↦ ⟨fun a1 ↦ by simp only [eq_comm], ?_⟩, ?_⟩
      · trivial
      · have hm : (⟨s / 2, by obtain ⟨k, rfl⟩ := hs; omega⟩ : Fin s).rev =
            ⟨s / 2, by obtain ⟨k, rfl⟩ := hs; omega⟩ :=
          ((eq_rev_iff_of_odd hs _).2 rfl).symm
        simp only [map_neg, hN, h_star_inv π]
        calc (π⁻¹ : Rˣ).val * ((star π)⁻¹ : Rˣ).val +
              star (u : R) * (((star π)⁻¹ : Rˣ).val * (π⁻¹ : Rˣ).val) * -((π : R) * star (π : R)) *
                ((u : R) * ((π⁻¹ : Rˣ).val * ((star π)⁻¹ : Rˣ).val))
            = (π⁻¹ : Rˣ).val * ((star π)⁻¹ : Rˣ).val - (star (u : R) * (u : R)) *
                ((π⁻¹ : Rˣ).val * (π : R)) * (((star π)⁻¹ : Rˣ).val * star (π : R)) *
                ((π⁻¹ : Rˣ).val * ((star π)⁻¹ : Rˣ).val) := by ring
          _ = 0 := by rw [hu, hπ2, hπ1]; ring
    · simp only [hs, ↓reduceIte, conjTranspose_one, mul_one, ne_rev_of_not_odd hs, diagonal,
        ← ext_iff, Matrix.add_apply, Matrix.one_apply, Matrix.mul_apply, conjTranspose_apply,
        of_apply, Sum.forall, Sum.elim_inl, Pi.zero_apply, mul_zero, Finset.sum_const_zero,
        add_zero, Sum.elim_inr, Sum.inl.injEq, Pi.one_apply, implies_true, reduceCtorEq,
        and_self, T, Z, G]
  have h_mixed : Zᴴ * G * D = C ∧ Dᴴ * G * Z = Cᵀ := by
    by_cases hs : Odd s
    · simp only [eq_rev_iff_of_odd hs, _root_.mul_inv_rev, Units.val_mul, Units.coe_star_inv,
        diagonal, hs, ↓reduceIte, mul_one, ← ext_iff, Matrix.mul_apply, conjTranspose_apply,
        of_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, Sum.forall,
        Sum.elim_inl, Pi.zero_apply, star_zero, zero_mul, Finset.sum_const_zero, implies_true,
        Sum.elim_inr, apply_ite star, star_mul', star_star, ite_mul, forall_const, true_and,
        transpose_of, Function.swap, Z, G, D, C]
      let m : Fin s := ⟨s / 2, by obtain ⟨k, rfl⟩ := hs; omega⟩
      have hm : m.rev = m := ((eq_rev_iff_of_odd hs m).2 rfl).symm
      dsimp only [m] at hm
      have h_mid : star (u : R) * (((star π)⁻¹ : Rˣ).val * (π⁻¹ : Rˣ).val) *
          -((π : R) * star (π : R)) * (u : R) = -1 := by
        calc _ = -(star (u : R) * (u : R)) *
              (((star π)⁻¹ : Rˣ).val * star (π : R)) * ((π⁻¹ : Rˣ).val * (π : R)) := by ring
          _ = -1 := by rw [hu, hπ1, hπ2]; ring
      have h_mid' : star (u : R) * -((π : R) * star (π : R)) *
          ((u : R) * ((π⁻¹ : Rˣ).val * ((star π)⁻¹ : Rˣ).val)) = -1 := by
        calc _ = -(star (u : R) * (u : R)) *
              (((star π)⁻¹ : Rˣ).val * star (π : R)) * ((π⁻¹ : Rˣ).val * (π : R)) := by ring
          _ = -1 := by rw [hu, hπ1, hπ2]; ring
      refine ⟨fun j ↦ ?_, fun i ↦ ?_⟩
      · simp only [h_star_inv π]
        by_cases hj : j = m
        · dsimp only [m] at hj; subst hj
          simp only [↓reduceIte, hm, map_neg, hN, h_mid]
        · dsimp only [m] at hj
          have hjr : (⟨s / 2, by obtain ⟨k, rfl⟩ := hs; omega⟩ : Fin s) ≠ j.rev :=
            fun h ↦ hj ((Fin.rev_eq_iff.mp h.symm).trans hm)
          simp only [hj, hjr, ↓reduceIte, map_zero, mul_zero, zero_mul]
      · simp only [h_star_inv π]
        by_cases hi : i = m
        · dsimp only [m] at hi; subst hi
          simp only [↓reduceIte, hm, map_neg, hN, h_mid']
        · dsimp only [m] at hi
          have hir : i ≠ (⟨s / 2, by obtain ⟨k, rfl⟩ := hs; omega⟩ : Fin s).rev :=
            fun h ↦ hi (h.trans hm)
          simp only [hi, hir, ↓reduceIte, map_zero, mul_zero, zero_mul]
    · simp only [ne_rev_of_not_odd hs, ↓reduceIte, ← ext_iff, Matrix.mul_apply,
        conjTranspose_apply, of_apply, Sum.forall, Sum.elim_inl, Pi.zero_apply, star_zero,
        zero_mul, Finset.sum_const_zero, implies_true, Sum.elim_inr, and_self, transpose_of,
        Function.swap, mul_zero, Z, C]
  have h_string : Dᴴ * G * D =
      of fun b c ↦ if b = c.rev then (if b = c then -(N : R) else 1) else 0 := by
    simp only [diagonal, mul_ite, mul_one, ← ext_iff, Matrix.mul_apply, conjTranspose_apply,
      of_apply, apply_ite star, star_mul', star_star, star_zero, ite_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, mul_zero, D, G]
    intro b c
    by_cases hrev : b = c.rev
    · simp only [hrev, ↓reduceIte]
      by_cases hs : Odd s
      · simp only [hs, ↓reduceIte, apply_ite f, map_neg, map_natCast, map_one]
        calc star (u : R) * (if c.rev = c then -(N : R) else 1) * (u : R)
            = (star (u : R) * (u : R)) * (if c.rev = c then -(N : R) else 1) := by ring
          _ = if c.rev = c then -(N : R) else 1 := by rw [hu, one_mul]
      · have hne : c.rev ≠ c := (ne_rev_of_not_odd hs c).symm
        have hlt : 2 * (c.rev : ℕ) < s ↔ ¬ 2 * (c : ℕ) < s := by
          obtain ⟨k, rfl⟩ := Nat.not_odd_iff_even.mp hs
          have hc := c.isLt
          rw [Fin.val_rev]; omega
        simp only [hs, ↓reduceIte, hne, map_one, hlt]
        by_cases hc : 2 * (c : ℕ) < s
        · simp only [hc, ↓reduceIte, not_true_eq_false]
          calc star (u : R) * (a : R) * 1 * ((u : R) * (a⁻¹ : Rˣ).val)
              = (star (u : R) * (u : R)) * ((a : R) * (a⁻¹ : Rˣ).val) := by ring
            _ = 1 := by rw [hu, a.mul_inv, one_mul]
        · simp only [hc, ↓reduceIte, not_false_eq_true]
          calc star (u : R) * star (a⁻¹ : Rˣ).val * 1 * ((u : R) * star (a : R))
              = (star (u : R) * (u : R)) * star ((a : R) * (a⁻¹ : Rˣ).val) := by
                rw [star_mul]; ring
            _ = 1 := by rw [hu, a.mul_inv, star_one, mul_one]
    · simp only [hrev, ↓reduceIte, map_zero, mul_zero, zero_mul, ite_self]
  have h_basis : gradedLatticeBasis e a π u = reindex e e (fromBlocks T 0 Z D) := rfl
  have h_form : (gradedGram e (N : S)).map f = reindex e e (fromBlocks 1 0 0 G) := by
    simp only [gradedGram, apply_ite f, map_neg, map_natCast, map_one, map_zero,
      reindex_apply, ← ext_iff, map_apply, submatrix_apply, reindex_equiv e,
      Equiv.symm_apply_apply, Sum.forall, fromBlocks_apply₁₁, Matrix.one_apply,
      implies_true, and_self, fromBlocks_apply₁₂, Matrix.zero_apply, fromBlocks_apply₂₁,
      fromBlocks_apply₂₂, of_apply, G]
  have h_blocks : (fromBlocks T 0 Z D)ᴴ * fromBlocks 1 0 0 G * fromBlocks T 0 Z D =
      fromBlocks (Tᴴ * T + Zᴴ * G * Z) (Zᴴ * G * D) (Dᴴ * G * Z) (Dᴴ * G * D) := by
    simp only [fromBlocks_conjTranspose, conjTranspose_zero, fromBlocks_multiply, mul_one,
      Matrix.mul_zero, add_zero, zero_add, Matrix.mul_one, Matrix.zero_mul]
  have h_gram : (fromBlocks T 0 Z D)ᴴ * fromBlocks 1 0 0 G * fromBlocks T 0 Z D =
      gluedGram (N : R) 0 := by
    simp only [h_blocks, h_X, h_mixed, h_string, gluedGram, C]
  simp only [h_basis, h_form, reindex_apply, conjTranspose_submatrix, submatrix_mul_equiv,
    ← h_gram]

variable [DecidableEq ι]

omit [Fintype X] in
/-- Let `e` index `X ⊕ Unit` and a string of `s` vectors by `ι`. Let `J = New.gradedGram e N` be the
form that is the identity on `X ⊕ Unit` and pairs string vectors `b` and `s - 1 - b` to `1`, or to
`-N` if they are equal, carried from `S` to the star ring `R` by `f`. For units `a`, `π` and a
unitary `u` of `R`, the columns of `B = New.gradedLatticeBasis e a π u` are the basis vectors,
changed as follows. For odd `s`, the string vectors are multiplied by `u` and the vector `y` of
`Unit` becomes `y / π̄ + u z / (π π̄)`, with `z` the middle string vector. For even `s`, the first
half of the string is multiplied by `u a⁻¹` and the second half by `u ā`. If `N = π π̄` in `R`,
then `Bᴴ J B` is unimodular over every subring `O` of `R`: it is hermitian and lies in `GL(O)`. -/
lemma isUnimodular_gradedLatticeBasis_gram
    [Finite X] {s N : ℕ} (e : (X ⊕ Unit) ⊕ Fin s ≃ ι) {S : Type*}
    {O : Subring R} [CommRing S] [StarRing R] {f : S →+* R} {a π : Rˣ} {u : unitary R}
    (hN : f (N : S) = π * star (π : R)) :
    IsUnimodular O ((gradedLatticeBasis e a π u)ᴴ * (gradedGram e (N : S)).map f *
      gradedLatticeBasis e a π u) := by
  let := Fintype.ofFinite X
  -- The Gram matrix is `gluedGram N 0`, reindexed by `e`; it and its inverse `gluedGram 0 N` have
  -- entries in `O`.
  let B : Matrix ι ι R := gradedLatticeBasis e a π u
  let J : Matrix ι ι R := (gradedGram e (N : S)).map f
  let H (p q : O) : Matrix ι ι O := reindex e e (gluedGram p q)
  have h_hermitian : (Bᴴ * J * B).IsHermitian :=
    isHermitian_conjTranspose_mul_mul B (isHermitian_map_gradedGram_natCast e f)
  have h_inv : H N 0 * H 0 N = 1 := by
    simp only [reindex_apply, submatrix_mul_equiv, gluedGram_mul_eq_one, submatrix_one_equiv, H]
  have h_gram : (H N 0).map O.subtype = Bᴴ * J * B := by
    simp only [B, J, H, gram_gradedLatticeBasis_eq_gluedGram e a u hN, reindex_apply,
      ← submatrix_map, map_gluedGram, map_natCast, map_zero]
  let w : GL ι O := .mkOfMulEqOne (H N 0) (H 0 N) h_inv
  exact ⟨h_hermitian, GeneralLinearGroup.map O.subtype w, ⟨w, rfl⟩, h_gram⟩

/-- The signs on a string of `s` vectors: `-1` at the first `⌊(s + 1) / 2⌋` indices and `1` at
the others. -/
def stringSign (s : ℕ) (b : Fin s) : ℤˣ := if (b : ℕ) < (s + 1) / 2 then -1 else 1

private lemma stringSign_mid {s : ℕ} (a : Fin s) (ha : a = a.rev) :
    ((stringSign s a : ℤ) : ℂ) = -1 := by
  rw [Fin.ext_iff, Fin.val_rev] at ha
  have h : (a : ℕ) < (s + 1) / 2 := by omega
  simp [stringSign, h]

private lemma rev_lt_half_iff {s : ℕ} (a : Fin s) (ha : a ≠ a.rev) :
    (a.rev : ℕ) < (s + 1) / 2 ↔ ¬ (a : ℕ) < (s + 1) / 2 := by
  have h_ne : (a : ℕ) ≠ s - 1 - a := fun h ↦ ha (Fin.ext (by rw [Fin.val_rev]; omega))
  have hlt := a.isLt
  rw [Fin.val_rev]
  omega

/-- A complex frame for a string of `s` vectors `e_b`, with `σ = stringSign s`. Column `b` is
`(σ b • e_b + e_{s - 1 - b}) / √2`. At the middle index `b = s - 1 - b` these two terms cancel,
as `σ b = -1`, and `e_b / √N` is added. -/
def stringFrame (s N : ℕ) : Matrix (Fin s) (Fin s) ℂ :=
  of fun a b : Fin s ↦
    (if a = b then ((stringSign s b / √2 : ℝ) : ℂ) else 0) +
      if a = b.rev then ((√2⁻¹ + if a = b then √N⁻¹ else 0 : ℝ) : ℂ) else 0

/-- On a string of `s` vectors `e_b`, take the form that pairs `e_b` and `e_{s - 1 - b}` to `1`, or
to `-N` if they are equal, with `N` a positive integer. Let `σ = stringSign s` be `-1` at the first
`⌊(s + 1) / 2⌋` indices and `1` at the others. The frame `stringFrame s N` has column `b` equal to
`(σ b • e_b + e_{s - 1 - b}) / √2`, or to `e_b / √N` if `b = s - 1 - b`. Its Gram matrix is the
diagonal matrix `New.signMatrix σ` of the signs `σ b`. -/
lemma gram_stringFrame_eq_signMatrix {s N : ℕ} (hN : 0 < N) :
    (stringFrame s N)ᴴ *
        (of fun a b : Fin s ↦ if a = b.rev then (if a = b then -(N : ℂ) else 1) else 0) *
        stringFrame s N =
      signMatrix (stringSign s) := by
  -- Away from the middle, columns `a` and `a.rev` span a hyperbolic plane, are orthogonal as their
  -- signs are opposite, and have norms `± 1`; the middle column has norm `-N / N = -1`.
  let σ (b : Fin s) : ℂ := stringSign s b
  let t : ℂ := (√2⁻¹ : ℝ)
  let r : ℂ := (√N⁻¹ : ℝ)
  have ht : t * t = 2⁻¹ := by
    simp only [Real.sqrt_inv, Complex.ofReal_inv, ← mul_inv, ← Complex.ofReal_mul,
      Nat.ofNat_nonneg, Real.mul_self_sqrt, Complex.ofReal_ofNat, t]
  have hr : r * r * N = 1 := by
    simp only [Real.sqrt_inv, Complex.ofReal_inv, ← mul_inv, ← Complex.ofReal_mul,
      Nat.cast_nonneg, Real.mul_self_sqrt, Complex.ofReal_natCast, ne_eq, Nat.cast_eq_zero,
      hN.ne', not_false_eq_true, inv_mul_cancel₀, r]
  have hσ_rev (a : Fin s) (ha : a ≠ a.rev) : σ a * σ a.rev = -1 := by
    simp only [σ, stringSign, rev_lt_half_iff a ha]
    by_cases h_lt : (a : ℕ) < (s + 1) / 2
    · simp only [h_lt, ↓reduceIte, Units.val_neg, Units.val_one, Int.reduceNeg, Int.cast_neg,
        Int.cast_one, not_true_eq_false, mul_one]
    · simp only [h_lt, ↓reduceIte, Units.val_one, Int.cast_one, not_false_eq_true,
        Units.val_neg, Int.reduceNeg, Int.cast_neg, mul_neg, mul_one]
  have h_col_mid (b : Fin s) (hb : b = b.rev) (i : Fin s) :
      stringFrame s N i b = if i = b then r else 0 := by
    by_cases hi : i = b
    · simp only [stringFrame, Complex.ofReal_div, Complex.ofReal_intCast, Real.sqrt_inv,
        Complex.ofReal_add, Complex.ofReal_inv, hi, of_apply, ↓reduceIte, stringSign_mid b hb,
        neg_div, one_div, ← hb, neg_add_cancel_left, r]
    · simp only [stringFrame, Complex.ofReal_div, Complex.ofReal_intCast, Real.sqrt_inv,
        Complex.ofReal_add, Complex.ofReal_inv, of_apply, hi, ↓reduceIte, ← hb, add_zero]
  have h_col (b : Fin s) (hb : b ≠ b.rev) (i : Fin s) :
      stringFrame s N i b = (if i = b then σ b * t else 0) + if i = b.rev then t else 0 := by
    by_cases hi : i = b
    · simp only [stringFrame, div_eq_mul_inv, Complex.ofReal_mul, Complex.ofReal_intCast,
        Complex.ofReal_inv, Real.sqrt_inv, Complex.ofReal_add, hi, of_apply, ↓reduceIte,
        hb, add_zero, σ, t]
    · simp only [stringFrame, div_eq_mul_inv, Complex.ofReal_mul, Complex.ofReal_intCast,
        Complex.ofReal_inv, Real.sqrt_inv, Complex.ofReal_add, of_apply, hi, ↓reduceIte,
        Complex.ofReal_zero, add_zero, zero_add, t]
  have h_star (i b : Fin s) : star (stringFrame s N i b) = stringFrame s N i b := by
    simp only [stringFrame, Complex.ofReal_div, Complex.ofReal_intCast, Real.sqrt_inv,
      Complex.ofReal_add, Complex.ofReal_inv, of_apply, star_add, apply_ite star, star_div₀,
      star_intCast, Complex.star_def, Complex.conj_ofReal, star_zero, star_inv₀]
  ext a b
  suffices h_entry : ∑ i : Fin s, stringFrame s N i a *
      ((if i = i.rev then -(N : ℂ) else 1) * stringFrame s N i.rev b) = if a = b then σ a else 0 by
    rw [Matrix.mul_assoc]
    simpa only [← Fin.rev_eq_iff, Matrix.mul_apply, conjTranspose_apply, h_star, of_apply,
      ite_mul, neg_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte,
      mul_ite, mul_neg, signMatrix, diagonal_apply] using h_entry
  have rev_eq_self (x y : Fin s) (hx : x = x.rev) (hy : y = y.rev) : x = y := by
    rw [Fin.ext_iff, Fin.val_rev] at hx hy; exact Fin.ext (by omega)
  by_cases ha : a = a.rev
  · simp only [h_col_mid a ha, ite_mul, zero_mul, Fintype.sum_ite_eq', ← ha, σ, stringSign_mid a ha]
    by_cases hb : b = b.rev
    · have hab : a = b := rev_eq_self a b ha hb
      subst hab
      simp only [h_col_mid a ha, ↓reduceIte]
      calc r * (-(N : ℂ) * r) = -(r * r * (N : ℂ)) := by ring
        _ = -1 := by rw [hr]
    · have hab : a ≠ b := fun h ↦ hb (by rw [← h]; exact ha)
      have hab' : a ≠ b.rev := fun h ↦ hb (by rw [h, Fin.rev_rev] at ha; exact ha.symm)
      simp only [h_col b hb, hab, hab', ↓reduceIte, add_zero, mul_zero]
  · simp only [h_col a ha, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul,
      Fintype.sum_ite_eq', Fin.rev_rev]
    by_cases hb : b = b.rev
    · have hab : a ≠ b := fun h ↦ ha (by rw [h]; exact hb)
      have har : a.rev ≠ b := fun h ↦ ha (by rw [← h, Fin.rev_rev] at hb; exact hb.symm)
      simp only [h_col_mid b hb, hab, har, ↓reduceIte, ite_self, mul_zero, add_zero]
    · by_cases hab : a = b
      · subst hab
        have hba : a.rev ≠ a := fun h ↦ ha h.symm
        simp only [h_col a hb, ha, hba, ↓reduceIte, add_zero, zero_add, one_mul]
        calc σ a * t * t + t * (σ a * t) = σ a * (2 * (t * t)) := by ring
          _ = σ a := by rw [ht]; ring
      · by_cases har : a = b.rev
        · subst har
          have hrne : b.rev ≠ b := fun h ↦ hb h.symm
          simp only [h_col b hb, hrne, hrne.symm, Fin.rev_rev, ↓reduceIte, zero_add,
            add_zero, one_mul]
          calc σ b.rev * t * (σ b * t) + t * t = (σ b * σ b.rev + 1) * (t * t) := by ring
            _ = 0 := by rw [hσ_rev b hb]; ring
        · have h1 : a.rev ≠ b := fun h ↦ har (by rw [← h, Fin.rev_rev])
          have h2 : a.rev ≠ b.rev := fun h ↦ hab (Fin.rev_inj.mp h)
          simp only [h_col b hb, hab, har, h1, h2, ha, ↓reduceIte, ite_self, mul_zero,
            add_zero]

/-- For `N = 1` the frame `stringFrame s N` is unitary. -/
lemma conjTranspose_stringFrame_one_mul_self : (stringFrame s 1)ᴴ * stringFrame s 1 = 1 := by
  let σ (b : Fin s) : ℂ := stringSign s b
  let t : ℂ := (√2⁻¹ : ℝ)
  have ht : t * t = 2⁻¹ := by
    simp only [Real.sqrt_inv, Complex.ofReal_inv, ← mul_inv, ← Complex.ofReal_mul,
      Nat.ofNat_nonneg, Real.mul_self_sqrt, Complex.ofReal_ofNat, t]
  have hσ_rev (a : Fin s) (ha : a ≠ a.rev) : σ a + σ a.rev = 0 := by
    simp only [σ, stringSign, rev_lt_half_iff a ha]
    by_cases h_lt : (a : ℕ) < (s + 1) / 2 <;>
      simp only [h_lt, ↓reduceIte, Units.val_neg, Units.val_one, Int.reduceNeg, Int.cast_neg,
        Int.cast_one, not_true_eq_false, not_false_eq_true, neg_add_cancel, add_neg_cancel]
  have h_col_mid (b : Fin s) (hb : b = b.rev) (i : Fin s) :
      stringFrame s 1 i b = if i = b then 1 else 0 := by
    by_cases hi : i = b <;>
      simp only [stringFrame, Complex.ofReal_div, Complex.ofReal_intCast, Real.sqrt_inv,
        Nat.cast_one, inv_one, Real.sqrt_one, Complex.ofReal_add, Complex.ofReal_inv,
        hi, of_apply, ↓reduceIte, stringSign_mid b hb, neg_div, one_div, ← hb, neg_add_cancel_left,
        add_zero, Complex.ofReal_one]
  have h_col (b : Fin s) (hb : b ≠ b.rev) (i : Fin s) :
      stringFrame s 1 i b = (if i = b then σ b * t else 0) + if i = b.rev then t else 0 := by
    by_cases hi : i = b <;>
      simp only [stringFrame, div_eq_mul_inv, Complex.ofReal_mul, Complex.ofReal_intCast,
        Complex.ofReal_inv, Real.sqrt_inv, Complex.ofReal_add, hi, of_apply, ↓reduceIte,
        hb, add_zero, Complex.ofReal_zero, zero_add, σ, t]
  have h_star (i b : Fin s) : star (stringFrame s 1 i b) = stringFrame s 1 i b := by
    simp only [stringFrame, Complex.ofReal_div, Complex.ofReal_intCast, Real.sqrt_inv,
      Complex.ofReal_add, Complex.ofReal_inv, of_apply, star_add, apply_ite star, star_div₀,
      star_intCast, Complex.star_def, Complex.conj_ofReal, star_zero, star_inv₀]
  have rev_eq_self (x y : Fin s) (hx : x = x.rev) (hy : y = y.rev) : x = y := by
    rw [Fin.ext_iff, Fin.val_rev] at hx hy; exact Fin.ext (by omega)
  ext a b
  simp only [Matrix.mul_apply, conjTranspose_apply, h_star, Matrix.one_apply]
  by_cases ha : a = a.rev
  · simp only [h_col_mid a ha, ite_mul, one_mul, zero_mul, Fintype.sum_ite_eq']
    by_cases hb : b = b.rev
    · have hab : a = b := rev_eq_self a b ha hb
      subst hab; simp only [h_col_mid a ha, ↓reduceIte]
    · have hab : a ≠ b := fun h ↦ hb (by rw [← h]; exact ha)
      have har : a ≠ b.rev := fun h ↦ hb (by rw [h, Fin.rev_rev] at ha; exact ha.symm)
      simp only [h_col b hb, hab, har, ↓reduceIte, add_zero]
  · simp only [h_col a ha, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul,
      Fintype.sum_ite_eq']
    by_cases hb : b = b.rev
    · have hab : a ≠ b := fun h ↦ ha (by rw [h]; exact hb)
      have har : a.rev ≠ b := fun h ↦ ha (by rw [← h, Fin.rev_rev] at hb; exact hb.symm)
      simp only [h_col_mid b hb, hab, har, ↓reduceIte, mul_zero, add_zero]
    · have hσ_sq (x : Fin s) : σ x * σ x = 1 := by
        simp only [σ, stringSign]; split_ifs <;> norm_num
      by_cases hab : a = b
      · subst hab
        have hba : a.rev ≠ a := fun h ↦ ha h.symm
        simp only [h_col a hb, hba, hba.symm, ↓reduceIte, add_zero, zero_add]
        calc σ a * t * (σ a * t) + t * t = (σ a * σ a + 1) * (t * t) := by ring
          _ = 1 := by rw [hσ_sq a, ht]; norm_num
      · by_cases har : a = b.rev
        · subst har
          have hrb : b.rev ≠ b := fun h ↦ hb h.symm
          simp only [h_col b hb, hrb, hrb.symm, Fin.rev_rev, ↓reduceIte, zero_add, add_zero]
          calc σ b.rev * t * t + t * (σ b * t) = (σ b.rev + σ b) * (t * t) := by ring
            _ = 0 := by rw [add_comm, hσ_rev b hb, zero_mul]
        · have h1 : a.rev ≠ b := fun h ↦ har (by rw [← h, Fin.rev_rev])
          have h2 : a.rev ≠ b.rev := fun h ↦ hab (Fin.rev_inj.mp h)
          simp only [h_col b hb, hab, har, h1, h2, ↓reduceIte, mul_zero, add_zero]

omit [Fintype X] in
/-- Let `e` index `X ⊕ Unit` and a string of `s` vectors by `ι`, and let `N` be a positive integer.
Let `J` be the image under `φ` of `New.gradedGram e N`, the form that is the identity on `X ⊕ Unit`
and pairs string vectors `b` and `s - 1 - b` to `1`, or to `-N` if they are equal. If exactly
`⌊(s + 1) / 2⌋` of the signs `ε i` are `-1`, then `yᴴ J y = diag(ε)` (`New.signMatrix ε`) for some
complex matrix `y`, which is unitary if `N = 1`. -/
lemma exists_conjTranspose_mul_gradedGram_mul_eq_signMatrix [Finite X] (e : (X ⊕ Unit) ⊕ Fin s ≃ ι)
    (φ : R →+* ℂ) (hN : 0 < N) {ε : ι → ℤˣ} (hε : negCount ε = (s + 1) / 2) :
    ∃ y : Matrix ι ι ℂ, yᴴ * (gradedGram e (N : R)).map φ * y = signMatrix ε ∧
      (N = 1 → yᴴ * y = 1) := by
  let := Fintype.ofFinite X
  -- Up to a bijection `f` of the indices the signs are `1` on `X ⊕ Unit` and `stringSign s` on
  -- the string. The frame is the identity on `X ⊕ Unit` and `stringFrame s N` on the string.
  let σ : (X ⊕ Unit) ⊕ Fin s → ℤˣ := 1 ⊕ᵥ stringSign s
  have h_card : negCount σ = (s + 1) / 2 := by
    rw [negCount_sumElim]
    simp only [negCount, Pi.one_apply, units_ne_neg_self, card_eq_zero, stringSign,
      ite_eq_left_iff, not_lt, imp_false, not_le, card_fin_lt_of_le (show (s + 1) / 2 ≤ s by lia),
      zero_add]
  obtain ⟨f, rfl⟩ : ∃ f : ι ≃ (X ⊕ Unit) ⊕ Fin s, σ ∘ f = ε :=
    exists_equiv_comp_eq_of_negCount_eq (card_congr e.symm) (hε.trans h_card.symm)
  refine ⟨gradedBlocks e f.symm 1 (stringFrame s N), ?_, fun hN1 ↦ ?_⟩
  · rw [map_gradedGram, map_natCast, gradedGram]
    simp only [conjTranspose_submatrix, fromBlocks_conjTranspose, conjTranspose_one,
      conjTranspose_zero, Equiv.symm_symm, submatrix_mul_equiv, fromBlocks_multiply, mul_one,
      Matrix.mul_zero, add_zero, Matrix.zero_mul, Matrix.mul_one, zero_add,
      gram_stringFrame_eq_signMatrix hN, signMatrix, Function.comp_apply, ← ext_iff,
      submatrix_apply, diagonal_apply, reindex_equiv f.symm, Equiv.apply_symm_apply, Sum.forall,
      EmbeddingLike.apply_eq_iff_eq, fromBlocks_apply₁₁, Matrix.one_apply, Sum.inl.injEq,
      Sum.elim_inl, Pi.one_apply, Units.val_one, Int.cast_one, implies_true, and_self,
      fromBlocks_apply₁₂, Matrix.zero_apply, reduceCtorEq, ↓reduceIte, fromBlocks_apply₂₁,
      fromBlocks_apply₂₂, Sum.inr.injEq, Sum.elim_inr, σ]
  · simp only [hN1, conjTranspose_submatrix, fromBlocks_conjTranspose, conjTranspose_one,
      conjTranspose_zero, Equiv.symm_symm, submatrix_mul_equiv, fromBlocks_multiply, mul_one,
      Matrix.mul_zero, add_zero, Matrix.zero_mul, Matrix.mul_one,
      conjTranspose_stringFrame_one_mul_self, zero_add, fromBlocks_one, submatrix_one_equiv]

end New.Seesaw

/-! ## Integrality away from q and above a prime l -/

namespace New

variable {E : Type} [Field E] [CMType E] {q l c d k : ℕ} {n : Type} [Fintype n] [DecidableEq n]
  [Fact l.Prime]

/-- For natural numbers `c`, `d`, `q` and `k`: if `c` divides `d * q ^ k`, then the complex number
`d / c` lies in `integralAway q`. -/
lemma Seesaw.div_mem_integralAway (h_dvd : c ∣ d * q ^ k) : (d / c : ℂ) ∈ integralAway q := by
  -- If `d * q ^ k = c * m` then `‖d‖ = ‖c‖ * ‖m‖` in `ℂ_[l]`, since `q` is a unit at `l`.
  -- So `‖d / c‖` is `‖m‖ ≤ 1`, or `0` if `c = 0`.
  obtain ⟨m, hm⟩ := h_dvd
  intro l _ hl ι
  have h_norm : ‖(d : ℂ_[l])‖ = ‖(c : ℂ_[l])‖ * ‖(m : ℂ_[l])‖ := by
    simpa only [Nat.cast_mul, Nat.cast_pow, norm_mul, norm_pow, hl.norm_natCast_eq_one,
      one_pow, mul_one] using congrArg (fun a : ℕ ↦ ‖(a : ℂ_[l])‖) hm
  by_cases hc : c = 0
  · simp only [hc, Nat.cast_zero, div_zero, map_zero, norm_zero, zero_le_one]
  · simp only [map_div₀, map_natCast, norm_div, h_norm, ne_eq, norm_eq_zero,
      Nat.cast_eq_zero, hc, not_false_eq_true, mul_div_cancel_left₀,
      IsUltrametricDist.norm_natCast_le_one]

omit [Fact l.Prime] in
/-- If `l` is coprime to `q`, a finite adelic unitary point that is integral at all places not
dividing `q` is integral at the places above `l`. -/
lemma Seesaw.localLevel_le_integralAbove_of_coprime (hl : l.Coprime q) :
    localLevel n {w : FinPlace E | ↑q ∉ w.asIdeal} ≤ integralAbove n l :=
  -- A place above `l` is not above `q`.
  fun _ hg w hw ↦ hg w (w.isPrime.notMem_of_isCoprime_of_mem hl.cast hw)

/-- Let `E` be a CM field with Weil data, of which only the splitting character `υ` (a Hecke
character of `E`) is used. For `g` in the finite adelic unitary group `New.Gf E n` of matrices
indexed by `n`, the multiplier `New.finMultiplier g` is `υ(det u) |det u|^(-1/2)`, where `u` is a
chosen invertible finite adelic matrix with `u Ôⁿ = Ôⁿ ∩ g⁻¹ Ôⁿ`. If `g` and `g⁻¹` are integral at
the places above the prime `l`, its image under every ring homomorphism `ι : ℂ → ℂ_l` has norm
`1`. -/
lemma Parameters.norm_finMultiplier_eq_one {ι : ℂ →+* ℂ_[l]} {g : Gf E n} [WeilData E]
    (hg : g ∈ integralAbove n l) : ‖ι (finMultiplier g)‖ = 1 := by
  -- The factor is the value of the algebraic character `υ |·|^(-1/2)` at `det u`, with `u` the
  -- saturating matrix chosen by `saturatingElem`, so it is enough that `det u` is a unit above `l`.
  -- At such a place `g` is integral, so `1` is saturating as well, and `det u` has the valuation
  -- of `det 1` (`IsSaturating.v_det_saturatingElem`).
  rw [finMultiplier, glMultiplier, ← WeilData.chiFinAlgebraic_apply]
  refine WeilData.chiFinAlgebraic.norm_padic_eq_one _ ι fun w hw ↦ ?_
  have h_one : IsSaturating (LocInt w).matrix (g.atPlace w) 1 :=
    .of_mem (mem_subring_matrix_iff.2 (mem_intGL.1 (hg w hw)).1)
  simpa only [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one, Matrix.det_one,
    map_one] using IsSaturating.v_det_saturatingElem (b := g.val) h_one

/-- Let the automorphic character `a` of the norm-one adeles have weight `e` (its exponents at the
infinite places) and tame part `ψ` (its characters of the residue fields), and let the finite adelic
unitary point `g` be integral above `l`. Then the value of `a` at `New.detFin s g`, the determinant
of `(1, g)` in the unitary group of signature `s`, has norm `1` under every ring homomorphism
`ι : ℂ → ℂ_l`. -/
lemma AutChar.HasWeight.norm_apply_detFin_eq_one {ι : ℂ →+* ℂ_[l]} {g : Gf E n} {a : AutChar E}
    {e : NumberField.InfinitePlace E → ℤ} {ψ : (w : FinPlace E) → MulChar (ResField w) ℂ}
    {s : n → ℤˣ} [ha : a.HasWeight e ψ] (hg : g ∈ integralAbove n l) :
    ‖ι (a.val (detFin s g))‖ = 1 := by
  -- By `norm_padic_eq_prod` the norm is a product of powers of the norms of `det g` at primes above
  -- `l`, where `det g` is a unit.
  have h_unit (τ : NumberField.InfinitePlace E) :
      ‖adeleExtension (ι.comp (Φ τ)) (detFin s g).val.2‖ = 1 := by
    let w : FinPlace E := placeOfEmb (ι.comp (Φ τ))
    have h_val : Valued.v ((detFin s g).val.2 w) = Valued.v ((1 : 𝔸f E) w) := by
      simp only [↓det_atPlace, mem_intGL_iff_det.1 (hg w (natCast_mem_placeOfEmb _)),
        IsDedekindDomain.FiniteAdeleRing.one_apply, map_one]
    simpa only [↓G.det_snd, map_one, norm_one] using (norm_adeleExtension_eq_iff _ 1).2 h_val
  simp only [ha.norm_padic_eq_prod ι (detFin s g) (by simp only [↓det_fst, Pi.one_apply,
      OneMemClass.coe_one, Units.val_one, Matrix.det_one, funext_iff, implies_true]),
    h_unit, one_zpow, Finset.prod_const_one]

end New

/-!
## Admissible combinations of vectors and their calculus

* `New.Seesaw.IsAdmissibleCombination.normUnit_smul`: clearing the denominator by rescaling.
-/

section AdmissibleComb

open Finsupp Function

variable {α α' Z Z' : Type*} [AddCommGroup Z] [Module ℂ Z] [AddCommGroup Z'] [Module ℂ Z']
  (v : α → Z)

/-- The statement that `z = ∑ r x • v x` for some finitely supported `r` with support in `A`,
denominator `d` away from `n` and, if `p` holds, size at most `B`
(`New.Seesaw.IsAdmissibleCoeffs`). -/
def New.Seesaw.IsAdmissibleCombination (A : Set α) (n d : ℕ) (p : Prop) (B : ℝ) (z : Z) : Prop :=
  ∃ r : α →₀ ℂ, IsAdmissibleCoeffs A n d p B r ∧ z = r.sum fun (x : α) (c : ℂ) ↦ c • v x

namespace New.Seesaw.IsAdmissibleCombination

variable {v} {A : Set α} {A' : Set α'} {n d : ℕ} {p : Prop} {B : ℝ} {z : Z}

open scoped Classical in
/-- A finite sum `∑ i ∈ s, c i • v i` is an admissible combination over `s`, with denominator `d`
away from `n` and size `B` under `p`, if each `d * c i` is integral at the primes coprime to `n`
and, if `p` holds, `∑ i ∈ s, ‖σ (c i)‖ ≤ B` for all automorphisms `σ` of `ℂ`. -/
lemma of_sum {s : Finset α} {c : α → ℂ} (hc : ∀ i ∈ s, (d : ℂ) * c i ∈ integralAway n)
    (hB : p → ∀ σ : ℂ ≃+* ℂ, ∑ i ∈ s, ‖σ (c i)‖ ≤ B) :
    IsAdmissibleCombination v s n d p B (∑ i ∈ s, c i • v i) := by
  refine ⟨indicator s fun i _ ↦ c i, ⟨support_indicator_subset _ _, fun x ↦ ?_, fun hp σ ↦ ?_⟩, ?_⟩
  · by_cases hx : x ∈ s
    · simp only [indicator_apply, hx, ↓reduceDIte, hc]
    · simp only [indicator_apply, hx, ↓reduceDIte, mul_zero, zero_mem]
  · exact (sum_indicator_index (h := fun _ x ↦ ‖σ x‖) _
      (fun _ _ ↦ by rw [map_zero, norm_zero])).trans_le (hB hp σ)
  · exact (sum_indicator_index (h := fun _ a ↦ a • v _) _ (fun _ _ ↦ zero_smul ℂ _)).symm

/-- A single term `c • v x` with `x ∈ A` is an admissible combination of size `1` if `d · c` is
integral away from `n` and, under `p`, all conjugates `σ c` have absolute value at most `1`. -/
lemma smul_single {c : ℂ} {x : α} (hx : x ∈ A) (hc_int : (d : ℂ) * c ∈ integralAway n)
    (hc_size : p → ∀ σ : ℂ ≃+* ℂ, ‖σ c‖ ≤ 1) : IsAdmissibleCombination v A n d p 1 (c • v x) := by
  classical
  refine ⟨.single x c, ⟨fun y hy ↦ ?_, fun y ↦ ?_, ?_⟩, ?_⟩
  · rwa [Finset.mem_singleton.1 (support_single_subset hy)]
  · by_cases hy : x = y
    · simp only [hy, single_eq_same, hc_int]
    · simp only [ne_eq, hy, not_false_eq_true, single_eq_of_ne', mul_zero, zero_mem]
  · simpa only [map_zero, norm_zero, sum_single_index] using hc_size
  · simp only [sum_single_index, zero_smul]

/-- Each vector `v x` with `x ∈ A` is an admissible combination of size `1`, for any
denominator `d`. -/
lemma single (x : α) (hx : x ∈ A) : IsAdmissibleCombination v A n d p 1 (v x) := by
  have hc_int : (d : ℂ) * 1 ∈ integralAway n := by
    rw [mul_one]
    exact fun l _ _ ι ↦ by rw [map_natCast]; exact IsUltrametricDist.norm_natCast_le_one _ d
  simpa only [one_smul] using smul_single (v := v) (c := 1) hx hc_int
    (by simp only [map_one, norm_one, le_refl, implies_true])

/-- Substitution. Fix a natural number `n` and a proposition `p`. A vector is an admissible
combination of the `v x`, `x ∈ A`, with denominator `d` and size `B` if it is a finite sum
`∑ r x • v x` over points of `A` in which each `d * r x` is integral at the primes coprime to `n`
and, if `p` holds, `∑ ‖σ (r x)‖ ≤ B` for all automorphisms `σ` of `ℂ`. Let `z` be such a
combination, and let each `v x`, `x ∈ A`, be an admissible combination of the `v' y`, `y ∈ A'`, with
denominator `d'` and size `B'`. Then `z` is an admissible combination of the `v' y`, `y ∈ A'`, with
any denominator `e` divisible by `d d'` and any size `C` that is at least `B |B'|` if `p` holds. -/
lemma bind {v' : α' → Z} {e : ℕ} {C : ℝ} (hz : IsAdmissibleCombination v A n d p B z) (d' : ℕ)
    (B' : ℝ) (hv : ∀ x ∈ A, IsAdmissibleCombination v' A' n d' p B' (v x)) (hd : d * d' ∣ e)
    (hB : p → B * |B'| ≤ C) : IsAdmissibleCombination v' A' n e p C z := by
  classical
  -- If `z = ∑ c x • v x` and `v x = ∑ r x y • v' y`, take the coefficients `∑ c x • r x`.
  obtain ⟨c, hc, rfl⟩ := hz
  obtain ⟨k, rfl⟩ := hd
  have h_coeffs : ∀ x ∈ c.support, ∃ r : α' →₀ ℂ, IsAdmissibleCoeffs A' n d' p B' r ∧
      v x = linearCombination ℂ v' r := fun x hx ↦ hv x (hc.support_subset x hx)
  choose! r hr hv_eq using h_coeffs
  let t : α' →₀ ℂ := ∑ x ∈ c.support, c x • r x
  refine ⟨t, ⟨fun y hy ↦ ?_, fun y ↦ ?_, fun hp σ ↦ ?_⟩, ?_⟩
  · -- A point `y` of the support lies in the support of some `r x`, so `y ∈ A'`.
    obtain ⟨x, hx, hy_mem⟩ := mem_support_finsetSum y hy
    exact (hr x hx).support_subset y (support_smul hy_mem)
  · have h_eq : ↑(d * d' * k) * t y = ∑ x ∈ c.support, k * (d * c x * (d' * r x y)) := by
      simp only [mul_assoc, Nat.cast_mul, coe_finsetSum, coe_smul, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_left_comm, t]
    rw [h_eq]
    exact sum_mem fun x hx ↦
      mul_mem (natCast_mem _ k) (mul_mem (hc.integral x) ((hr x hx).integral y))
  · -- Triangle inequality, then the size bounds of the `r x` and of `c`.
    let T : Finset α' := t.support
    have h_size (x : α) (hx : x ∈ c.support) : ∑ y ∈ T, ‖σ (r x y)‖ ≤ |B'| := by
      grw [← le_abs_self, ← (hr x hx).sum_norm_le hp σ, ← Finset.sum_filter_ne_zero, sum]
      gcongr
      simp only [ne_eq, norm_eq_zero, EmbeddingLike.map_eq_zero_iff, Finset.subset_iff,
        Finset.mem_filter, mem_support_iff, and_imp, imp_self, implies_true]
    calc ∑ y ∈ T, ‖σ (t y)‖
      _ ≤ ∑ y ∈ T, ∑ x ∈ c.support, ‖σ (c x)‖ * ‖σ (r x y)‖ :=
        T.sum_le_sum fun y _ ↦ by
          simpa only [coe_finsetSum, coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
            map_sum, map_mul, Complex.norm_mul, t] using
            norm_sum_le c.support fun x ↦ σ (c x * r x y)
      _ = ∑ x ∈ c.support, ‖σ (c x)‖ * ∑ y ∈ T, ‖σ (r x y)‖ := by
        simp only [T.sum_comm, Finset.mul_sum]
      _ ≤ ∑ x ∈ c.support, ‖σ (c x)‖ * |B'| := Finset.sum_le_sum fun x hx ↦ by grw [h_size x hx]
      _ ≤ C := by grw [← Finset.sum_mul, ← hB hp, ← hc.sum_norm_le hp σ, sum]
  · calc c.sum (fun x a ↦ a • v x)
      _ = ∑ x ∈ c.support, c x • linearCombination ℂ v' (r x) :=
        Finset.sum_congr rfl fun x hx ↦ congrArg (c x • ·) (hv_eq x hx)
      _ = t.sum fun y a ↦ a • v' y := by simp only [← linearCombination_apply, t, map_sum, map_smul]

/-- Substitution without loss: if each `v x`, `x ∈ A`, is an admissible combination of the `v' y`,
`y ∈ A'`, with denominator `1` and size `1`, then an admissible combination of the `v x` is one of
the `v' y`, with the same denominator and size. -/
lemma bind_one {v' : α' → Z} (hz : IsAdmissibleCombination v A n d p B z)
    (hv : ∀ x ∈ A, IsAdmissibleCombination v' A' n 1 p 1 (v x)) :
    IsAdmissibleCombination v' A' n d p B z :=
  hz.bind 1 1 hv (by simp only [mul_one, dvd_refl])
    (fun _ ↦ by simp only [abs_one, mul_one, le_rfl])

/-- A linear map `L` sends an admissible combination of the `v x` to one of the `L (v x)`, with the
same coefficients. -/
lemma map (hz : IsAdmissibleCombination v A n d p B z) (L : Z →ₗ[ℂ] Z') :
    IsAdmissibleCombination (L ∘ v) A n d p B (L z) := by
  obtain ⟨r, hr, rfl⟩ := hz
  exact ⟨r, hr, by simp only [sum, map_sum, map_smul, comp_apply]⟩

/-- Admissible combinations are stable under a scalar `c` that is integral away from `n` and, if
`p` holds, has all conjugates `σ c` of absolute value at most `1`. -/
lemma smul (hz : IsAdmissibleCombination v A n d p B z) {c : ℂ} (hc_int : c ∈ integralAway n)
    (hc_size : p → ∀ σ : ℂ ≃+* ℂ, ‖σ c‖ ≤ 1) : IsAdmissibleCombination v A n d p B (c • z) :=
  (hz.map (LinearMap.lsmul ℂ Z c)).bind_one fun _ hx ↦
    smul_single hx (by simpa only [Nat.cast_one, one_mul] using hc_int) hc_size

/-- Admissible combinations are stable under a scalar that is `0` or a root of unity. -/
lemma smul_of_eq_zero_or_isOfFinOrder (hz : IsAdmissibleCombination v A n d p B z) {ζ : ℂ}
    (hζ : ζ = 0 ∨ IsOfFinOrder ζ) : IsAdmissibleCombination v A n d p B (ζ • z) := by
  obtain rfl | hζ := hζ
  · exact hz.smul (zero_mem _) (by simp only [map_zero, norm_zero, zero_le_one, implies_true])
  · -- Every ring homomorphism sends a root of unity to a root of unity, which has norm `1`.
    exact hz.smul (fun l _ _ ι ↦ (ι.toMonoidHom.isOfFinOrder hζ).norm_eq_one.le)
      fun _ σ ↦ (σ.toMonoidHom.isOfFinOrder hζ).norm_eq_one.le

/-- If each `v x`, `x ∈ A`, is a root of unity times some `v' y`, `y ∈ A'`, then an admissible
combination of the `v x` is one of the `v' y`, with the same denominator and size. -/
lemma of_eq_isOfFinOrder_smul {v' : α' → Z} (hz : IsAdmissibleCombination v A n d p B z)
    (hv : ∀ x ∈ A, ∃ ζ : ℂ, IsOfFinOrder ζ ∧ ∃ y ∈ A', v x = ζ • v' y) :
    IsAdmissibleCombination v' A' n d p B z := by
  refine hz.bind_one fun x hx ↦ ?_
  obtain ⟨ζ, hζ, y, hy, hxy⟩ := hv x hx
  simpa only [hxy] using (single y hy).smul_of_eq_zero_or_isOfFinOrder (.inr hζ)

/-- Fix a natural number `n` and a proposition `p`. A vector is an admissible combination of the
`v x`, `x ∈ A`, with denominator `d` and size `B` if it is a finite sum `∑ r x • v x` over points of
`A` in which each `d * r x` is integral at the primes coprime to `n` and, if `p` holds,
`∑ ‖σ (r x)‖ ≤ B` for all automorphisms `σ` of `ℂ`. Let `z` be such a combination, and let `z'` be
one of the `v' y`, `y ∈ A'`, with denominator `d'` and size `B'`. For a bilinear map `b`, the value
`b z z'` is an admissible combination of the `b (v x) (v' y)`, `(x, y) ∈ A × A'`, with denominator
`d d'` and size `B |B'|`. -/
lemma map_bilinear {v' : α' → Z'} {d' : ℕ} {B' : ℝ} {z' : Z'}
    (hz : IsAdmissibleCombination v A n d p B z) {W : Type*} [AddCommGroup W] [Module ℂ W]
    (b : Z →ₗ[ℂ] Z' →ₗ[ℂ] W) (hz' : IsAdmissibleCombination v' A' n d' p B' z') :
    IsAdmissibleCombination (fun x : α × α' ↦ b (v x.1) (v' x.2)) (A ×ˢ A') n (d * d') p (B * |B'|)
      (b z z') := by
  -- Expand `z` in the first variable, then `z'` in the second.
  have h_left : IsAdmissibleCombination (fun x ↦ b (v x) z') A n d p B (b z z') :=
    hz.map (b.flip z')
  refine h_left.bind d' B' (fun x hx ↦ ?_) dvd_rfl fun _ ↦ le_rfl
  exact (hz'.map (b (v x))).bind_one fun y hy ↦ single (x, y) ⟨hx, hy⟩

/-- Let `z` be an admissible combination of the `v x`, `x ∈ A`, with denominator `d` away from `n`,
and let `l` be a prime coprime to `n`. Then `d z` lies in every module `M` that contains these `v x`
over `New.embValRing`, the ring of complex numbers whose image under the chosen homomorphism
`ιₚ : ℂ → ℂ_l` is integral. -/
lemma smul_mem (hz : IsAdmissibleCombination v A n d p B z) {l : ℕ} [Fact l.Prime] [PadicPlace l]
    (hl : l.Coprime n) {M : Submodule embValRing Z} (hv : ∀ x ∈ A, v x ∈ M) : (d : ℂ) • z ∈ M := by
  obtain ⟨r, hr, rfl⟩ := hz
  simp only [smul_sum, smul_smul]
  exact sum_mem fun x hx ↦
    M.smul_mem ⟨d * r x, hr.integral x l hl ιₚ⟩ (hv x (hr.support_subset x hx))

/-- Let `d ≠ 0` and let `z` be an admissible combination of the `C • v x`, `x ∈ A`, with denominator
`d` and size `B`. Then `a • z`, multiplied by `normUnit (a * C / d)` (which is `d / (a C)`, or `1`
if `a C = 0`), is an admissible combination of the `v x`, `x ∈ A`, with denominator `1` and size
`d B`. -/
lemma normUnit_smul {C : ℂ} (a : ℂ) (hd : d ≠ 0)
    (hz : IsAdmissibleCombination (fun x : α ↦ C • v x) A n d p B z) :
    IsAdmissibleCombination v A n 1 p (d * B) ((normUnit (a * C / d)).val • a • z) := by
  -- If `z` has coefficients `r`, the rescaled vector is `0` when `a * C = 0`, and otherwise the
  -- combination of the `v x` with coefficients `d • r`.
  obtain ⟨r, ⟨h_supp, h_int, h_size⟩, rfl⟩ := hz
  let z₀ : Z := r.sum fun x c ↦ c • v x
  have h_comb : IsAdmissibleCombination v A n 1 p (d * B) ((d : ℂ) • z₀) := by
    refine ⟨d • r, ⟨fun x hx ↦ h_supp x (support_smul hx), fun x ↦ ?_, fun hp σ ↦ ?_⟩, ?_⟩
    · simpa only [Nat.cast_one, coe_smul, Pi.smul_apply, nsmul_eq_mul, one_mul] using h_int x
    · simpa only [map_zero, norm_zero, implies_true, sum_smul_index', nsmul_eq_mul, map_mul,
        map_natCast, Complex.norm_mul, RCLike.norm_natCast, ← mul_sum, Nat.cast_pos, hd.pos,
        mul_le_mul_iff_right₀] using h_size hp σ
    · simp only [smul_sum, smul_smul, zero_smul, implies_true, sum_smul_index', nsmul_eq_mul,
        z₀]
  have h_vec : (normUnit (a * C / d)).val • a • (r.sum fun x c ↦ c • C • v x) =
      ((normUnit (a * C / d)).val * (a * C)) • z₀ := by
    simp only [mul_comm, smul_smul, smul_sum, mul_left_comm, mul_assoc, z₀]
  rw [h_vec]
  by_cases haC : a * C = 0
  · simpa only [haC, zero_div, normUnit_zero, Units.val_one, mul_zero, zero_smul] using
      h_comb.smul (zero_mem _) (c := 0) (by simp only [map_zero, norm_zero, zero_le_one,
        implies_true])
  · simpa only [normUnit, div_eq_zero_iff, haC, Nat.cast_eq_zero, hd, or_self, ↓reduceDIte,
      Units.val_inv_eq_inv_val, Units.val_mk0, inv_div, isUnit_iff_ne_zero, ne_eq,
      not_false_eq_true, IsUnit.div_mul_cancel] using h_comb

end New.Seesaw.IsAdmissibleCombination

end AdmissibleComb

open Function in
/-- Fix a natural number `n` and a proposition `p`. A vector is an admissible combination of vectors
`w x`, over a set of indices `x`, with denominator `d` and size `B` if it is a finite sum
`∑ r x • w x` over that set in which each `d * r x` is integral at the primes coprime to `n` and, if
`p` holds, `∑ ‖σ (r x)‖ ≤ B` for all automorphisms `σ` of `ℂ`. Let each `f i`, `i < m`, be such a
combination of the vectors `v i (s, t)` with `s ∈ A (2 i)` and `t ∈ A (2 i + 1)`. Then the pure
tensor `f (m - 1) ⊗ ⋯ ⊗ f 0` is an admissible combination, over the families `y` with all
`y j ∈ A j`, of the pure tensors of the `v i (y (2 i), y (2 i + 1))`, with denominator `d ^ m` and
size `|B| ^ m`. -/
lemma New.Seesaw.IsAdmissibleCombination.pure {n : ℕ} {p : Prop} {α : ℕ → Type*} {F : ℕ → Type}
    [∀ j : ℕ, AddGroup (α j)] [∀ j : ℕ, AddCommGroup (F j)] [∀ j : ℕ, Module ℂ (F j)]
    {v : ∀ i : ℕ, α (2 * i) × α (2 * i + 1) → F i} {A : ∀ j : ℕ, AddSubgroup (α j)}
    {f : ∀ i : ℕ, F i} (d : ℕ) (B : ℝ) (m : ℕ)
    (hf : ∀ i < m, IsAdmissibleCombination (v i) (A (2 * i) ×ˢ A (2 * i + 1)) n d p B (f i)) :
    IsAdmissibleCombination
      (fun y : ∀ j : ℕ, α j ↦ TensorChain.pure (fun i : ℕ ↦ v i (y (2 * i), y (2 * i + 1))) m)
      {y : (j : ℕ) → α j | ∀ j : ℕ, y j ∈ A j} n (d ^ m) p (|B| ^ m) (TensorChain.pure f m) := by
  induction m with
  | zero =>
    -- The empty tensor is `1` for every family, in particular for `y = 0`.
    rw [pow_zero, pow_zero]
    exact single 0 (fun j ↦ (A j).zero_mem)
  | succ m ih =>
    -- Tensor the first `m` factors with the last (`map_bilinear`), then merge a point `s` for the
    -- former and a pair `t` for the latter by updating the coordinates `2 m`, `2 m + 1` of `s`.
    let w (y : ∀ j : ℕ, α j) : TensorChain F m :=
      TensorChain.pure (fun i : ℕ ↦ v i (y (2 * i), y (2 * i + 1))) m
    have h_tensor : IsAdmissibleCombination
        (fun x : (∀ j : ℕ, α j) × α (2 * m) × α (2 * m + 1) ↦ v m x.2 ⊗ₜ[ℂ] w x.1)
        ({y | ∀ j : ℕ, y j ∈ A j} ×ˢ A (2 * m) ×ˢ A (2 * m + 1)) n (d ^ m * d) p (|B| ^ m * |B|)
        (f m ⊗ₜ[ℂ] TensorChain.pure f m) :=
      (ih fun i hi ↦ hf i (Nat.lt_succ_of_lt hi)).map_bilinear
        (TensorProduct.mk ℂ _ _).flip (hf m (Nat.lt_succ_self m))
    -- By definition, the pure tensor of length `m + 1` is `f m ⊗ₜ` the one of length `m`.
    rw [pow_succ, pow_succ]
    refine h_tensor.of_eq_isOfFinOrder_smul fun ⟨s, t⟩ ⟨hs, ht⟩ ↦ ?_
    let y : ∀ j : ℕ, α j := update (update s (2 * m) t.1) (2 * m + 1) t.2
    have h_init : w y = w s := TensorChain.pure_congr fun i hi ↦ by
      have h1 : 2 * i ≠ 2 * m := by omega
      have h2 : 2 * i ≠ 2 * m + 1 := by omega
      have h3 : 2 * i + 1 ≠ 2 * m := by omega
      have h4 : 2 * i + 1 ≠ 2 * m + 1 := by omega
      simp only [y, Function.update_of_ne h2, Function.update_of_ne h1,
        Function.update_of_ne h4, Function.update_of_ne h3]
    have hy_mem : y ∈ {y | ∀ j : ℕ, y j ∈ A j} := fun j ↦ by
      by_cases hj1 : j = 2 * m + 1
      · subst hj1; simp only [y, update_self]; exact ht.2
      · by_cases hj2 : j = 2 * m
        · subst hj2; simp only [y, update_of_ne hj1, update_self]; exact ht.1
        · simp only [y, update_of_ne hj1, update_of_ne hj2]; exact hs j
    refine ⟨1, .one, y, hy_mem, ?_⟩
    change v m t ⊗ₜ[ℂ] w s = (1 : ℂ) • v m (y (2 * m), y (2 * m + 1)) ⊗ₜ[ℂ] w y
    simp only [ne_eq, Nat.left_eq_add, one_ne_zero, not_false_eq_true, update_of_ne,
      update_self, Prod.mk.eta, h_init, one_smul, y]

/-!
## Moved vacua as admissible combinations

A translate of the vacuum moved by a finite unitary element is a multiple of a sum, over lattice
classes, of translates of the vacuum times roots of unity.
-/

section MovedVacuumComb

open Matrix Complex AddSubgroup Finset

/-- Let `E` be a CM field with Weil data, `V` a hermitian space over `E` with coordinates `n` and
signs `s`, and `ω` its Weil representation. Let `g` be a finite adelic unitary matrix, and factor as
`c * C` its multiplier `finMultiplier g = υ(det u) |det u|^(-1/2)`, with `υ` the splitting character
of the Weil data and `u Ôⁿ = Ôⁿ ∩ g⁻¹ Ôⁿ`. Translate the vacuum `vacElem` by `x`, with the
Heisenberg operator `finHeisenbergOp x`, and apply `ω (1, g)`. The result is a finite sum
`∑ r y • C • finHeisenbergOp y vacElem` over `y` in `A`, for any set `A` that contains all
`g (x + z)` with `z` in the lattice `Ôⁿ`. If `d c / ‖finMultiplier g‖ ^ 2` is integral at the primes
coprime to `q`, so is each `d * r y`. The proposition `p` is arbitrary: if under `p` all conjugates
`σ c` have absolute value at most `1`, then under `p` all `∑ ‖σ (r y)‖ ≤ 1`. -/
lemma New.Seesaw.isAdmissibleCombination_weil_vacElem {E n : Type} [Field E] [CMType E] [WeilData E]
    [Fintype n] [DecidableEq n] {s : n → ℤˣ} (V : Space E n s) {q d : ℕ} {g : Gf E n} {x : n → 𝔸f E}
    {A : Set (n → 𝔸f E)} {p : Prop} {C c : ℂ} (hcC : c * C = finMultiplier g)
    (h_mem : ∀ z ∈ stdLattice E n, (g : Matrix n n (𝔸f E)) *ᵥ (x + z) ∈ A)
    (h_int : (d : ℂ) * (c / (‖finMultiplier g‖ : ℂ) ^ 2) ∈ integralAway q)
    (h_size : p → ∀ σ : ℂ ≃+* ℂ, ‖σ c‖ ≤ 1) :
    IsAdmissibleCombination (fun y : n → 𝔸f E ↦ C • V.finHeisenbergOp y V.vacElem) A q d p 1
      (V.ω (1, g) (V.finHeisenbergOp x V.vacElem)) := by
  -- Let `H` be the group of lattice vectors that `g` keeps in the lattice. Its index is
  -- `‖finMultiplier g‖ ^ 2`, and `ω g vacElem` is a multiple of the sum of the translates of
  -- `vacElem` by `g z`, over representatives `z` of the classes modulo `H`.
  let M : Matrix n n (𝔸f E) := g
  let L : AddSubgroup (n → 𝔸f E) := stdLattice E n
  let H : AddSubgroup L := (L.comap M.mulVecLin).addSubgroupOf L
  have h_index : ‖finMultiplier g‖ ^ 2 = H.index := norm_finMultiplier_sq g
  have h_index_ne : H.index ≠ 0 := fun h_zero ↦ by
    simp only [h_zero, Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      pow_eq_zero_iff, norm_eq_zero, finMultiplier_ne_zero] at h_index
  let : Fintype (L ⧸ H) := fintypeOfIndexNeZero h_index_ne
  -- `ζ z` is the root of unity in the product of the translations by `g x` and `g z`.
  let ζ (z : L ⧸ H) : ℂ :=
    stdLattice.selfDualAddChar E (star stdLattice.traceOneAdele * star (M *ᵥ z.out) ⬝ᵥ M *ᵥ x)
  set a : ℂ := c / (‖finMultiplier g‖ : ℂ) ^ 2 with ha
  have h_sum : V.ω (1, g) (V.finHeisenbergOp x V.vacElem) =
      ∑ z : L ⧸ H, a • ζ z • C • V.finHeisenbergOp (M *ᵥ (x + z.out)) V.vacElem := by
    rw [V.omega_finHeisenbergOp, V.omega_vacElem_sum, finsum_eq_sum_of_fintype, map_smul, map_sum,
      smul_sum]
    refine sum_congr rfl fun z _ ↦ ?_
    rw [V.finHeisenbergOp_finHeisenbergOp, mulVec_add, smul_comm (ζ z), smul_smul _ C,
      div_mul_eq_mul_div c, hcC]
  -- There are `‖finMultiplier g‖ ^ 2` terms, so the absolute sum of the coefficients is `‖σ c‖`.
  have h_total (hp : p) (σ : ℂ ≃+* ℂ) : ∑ _z : L ⧸ H, ‖σ a‖ ≤ 1 := by
    calc ∑ _z : L ⧸ H, ‖σ a‖
        = H.index * (‖σ c‖ / H.index) := by
          simp only [ha, ← ofReal_pow, h_index, ofReal_natCast, map_div₀, map_natCast,
            Complex.norm_div, RCLike.norm_natCast, sum_const, card_univ,
            ← Nat.card_eq_fintype_card, ← H.index_eq_card, nsmul_eq_mul]
      _ = ‖σ c‖ := mul_div_cancel₀ _ (Nat.cast_ne_zero.2 h_index_ne)
      _ ≤ 1 := h_size hp σ
  have h_comb : IsAdmissibleCombination
      (fun z : L ⧸ H ↦ ζ z • C • V.finHeisenbergOp (M *ᵥ (x + z.out)) V.vacElem)
      (univ : Finset (L ⧸ H)) q d p 1 (V.ω (1, g) (V.finHeisenbergOp x V.vacElem)) := by
    simpa only [h_sum] using .of_sum (fun _ _ ↦ h_int) h_total
  exact h_comb.of_eq_isOfFinOrder_smul fun z _ ↦
    ⟨ζ z, isOfFinOrder_ψf _, M *ᵥ (x + z.out), h_mem _ z.out.property, rfl⟩

end MovedVacuumComb

/-!
## Values of `schrodingerOp` as admissible combinations

By finite Fourier inversion, the operator attached to a function modulo `𝔪` sends a vector to an
admissible combination of translates.
-/

namespace New.Seesaw

open Ideal Fintype NumberField Modulus

variable {E n : Type} [Field E] [CMType E] [Fintype n] [DecidableEq n]

/-- Let `𝔪` be a modulus of `E` (a nonzero ideal of `𝓞 E` prime to its conjugate) that divides
`g q`, for `g` in `𝓞 E` and a natural number `q`. Then the number of vectors over `𝓞 E / 𝔪` divides
a power of `q` times `N(g) ^ card n`, where `N(g)` is the absolute norm of the ideal `(g)`. -/
lemma card_residueRing_pi_dvd {g : 𝓞 E} {q : ℕ} (𝔪 : Modulus E) (hg : g * q ∈ 𝔪.ideal) :
    card (n → 𝔪.ResidueRing) ∣
      absNorm (span {g}) ^ card n * q ^ (Module.finrank ℤ (𝓞 E) * card n) := by
  have h_norm : absNorm (span {g * q}) = absNorm (span {g}) * q ^ Module.finrank ℤ (𝓞 E) := by
    rw [← span_singleton_mul_span_singleton, map_mul, absNorm_span_natCast]
  have h_card : card 𝔪.ResidueRing = absNorm 𝔪.ideal := by
    simp only [absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  rw [card_fun, h_card, pow_mul, ← mul_pow, ← h_norm]
  exact pow_dvd_pow_of_dvd (map_dvd absNorm (dvd_span_singleton.2 hg)) (card n)

omit [Fintype n] [DecidableEq n] in
/-- Let `𝔪` be a modulus of the CM field `E`, with `𝔪.places` the primes dividing it,
`𝔪.reduction : Ô → 𝓞 E / 𝔪` the reduction of integral finite adeles and `𝔪.generator` a chosen
finite idele generating its kernel. Divide a vector `z` of integral finite adeles by `𝔪.generator`,
set the components outside `𝔪.places` to `0` (multiplication by the idempotent `idem 𝔪.places`), and
apply complex conjugation `star`. If `d q ≡ 0` modulo `𝔪`, the result times `star d` is integral at
all places not dividing `q`. -/
lemma star_idem_smul_mem_translations {q : ℕ} (𝔪 : Modulus E) {d : Ô E}
    (hd : 𝔪.reduction (d * q) = 0) (z : n → Ô E) :
    star (idem 𝔪.places • (↑𝔪.generator⁻¹ : 𝔸f E) • (↑) ∘ z : n → 𝔸f E) ∈
      translations n q (star (d : 𝔸f E)) := by
  intro i w hw
  have h_dq : (↑𝔪.generator⁻¹ : 𝔸f E) * (d * q) ∈ Ô E := by
    simpa only [MulMemClass.coe_mul, SubringClass.coe_natCast] using
      (𝔪.reduction_eq_zero_iff_generator_inv_mul_mem (d * q)).1 hd
  -- Let `t` be `star d` times the entry. Then `q t` is the conjugate of an integral adele, and
  -- `q` is a unit at `w`.
  let t : 𝔸f E := star (d : 𝔸f E) * star (idem 𝔪.places * (↑𝔪.generator⁻¹ * (z i : 𝔸f E)))
  have h_eq : q * t = star (idem 𝔪.places * (↑𝔪.generator⁻¹ * (d * q) * (z i : 𝔸f E))) := by
    simp only [t, star_mul', star_natCast]
    ring
  have h_int : q * t ∈ Ô E := by
    simpa only [h_eq] using star_mem_Ô (mul_mem (idem_mem_Ô _) (mul_mem h_dq (z i).property))
  have h_unit : Valued.v ((q : 𝔸f E) w) = 1 :=
    by simpa only [finAdele_natCast_apply, map_natCast] using v_algebraMap_eq_one hw
  calc Valued.v (t w) = Valued.v ((q : 𝔸f E) w * t w) := by rw [map_mul, h_unit, one_mul]
    _ ≤ 1 := mem_Ô.1 h_int w

/-- Let `E` be a CM field with Weil data (the choices that fix the Weil representation), `V` a
hermitian space over `E` with coordinates `n` and signs `s`, and `𝒮 V` the space of its Weil
representation, on which a finite adelic vector `y` acts by the Heisenberg operator
`finHeisenbergOp y`. Let the modulus `𝔪` divide `g q` and `d q`. Let `v` be the image of `u` under
`projOn 𝔪.places`, the mean of the `finHeisenbergOp y` over the integral `y` supported at the primes
dividing `𝔪` and their conjugates. Let `Ψ` be a function on vectors modulo `𝔪` with values integral
away from `q`, read on finite adelic vectors by `liftFn`. The operator `V.schrodingerOp` attached to
it sends `u` to a finite sum `∑ r y • finHeisenbergOp y v` over vectors `y` with `star d • y`
integral away from `q`. Each `N(g) ^ card n * r y` is integral away from `q`, with `N(g)` the
absolute norm of `(g)`. If under the proposition `p` all `∑ ‖σ (Ψ x)‖ ≤ B`, for the automorphisms
`σ` of `ℂ`, then under `p` all `∑ ‖σ (r y)‖ ≤ B`. -/
lemma isAdmissibleCombination_schrodingerOp_of_reduction {g : 𝓞 E} {q : ℕ} [WeilData E]
    {s : n → ℤˣ} (V : Space E n s) (𝔪 : Modulus E) {Ψ : (n → 𝔪.ResidueRing) → ℂ} {p : Prop}
    {B : ℝ} {u v : 𝒮 V} (hg : g * q ∈ 𝔪.ideal)
    (hΨ_int : ∀ x : n → 𝔪.ResidueRing, Ψ x ∈ integralAway q)
    (hΨ_size : p → ∀ σ : ℂ ≃+* ℂ, ∑ x : n → 𝔪.ResidueRing, ‖σ (Ψ x)‖ ≤ B)
    (huv : V.projOn 𝔪.places u = v) {d : Ô E} (hd : 𝔪.reduction (d * q) = 0) :
    IsAdmissibleCombination (fun y : n → 𝔸f E ↦ V.finHeisenbergOp y v)
      (translations n q (star (d : 𝔸f E))) q
      (absNorm (span {g}) ^ card n) p B (V.schrodingerOp 𝔪.places (𝔪.liftFn Ψ) u) := by
  -- Expand `Ψ` in indicators of points. The vector `δ a` given by the indicator of `a` is a mean
  -- of roots of unity times translates of `v` (`schrodingerOp_single_eq_mean_translate_projOn`).
  obtain ⟨z, hz⟩ : ∃ z : (n → 𝔪.ResidueRing) → n → Ô E, ∀ b, 𝔪.reduction ∘ z b = b :=
    𝔪.reduction_surjective.comp_left.hasRightInverse
  have h_root (c : 𝔪.ResidueRing) : IsOfFinOrder (𝔪.primAddChar c) := by
    obtain ⟨x, rfl⟩ := 𝔪.reduction_surjective c
    simpa only [primAddChar_reduction, stdLattice.selfDualAddChar_apply] using isOfFinOrder_ψf _
  let δ (a : n → 𝔪.ResidueRing) : 𝒮 V := V.schrodingerOp 𝔪.places (𝔪.liftFn (Pi.single a 1)) u
  let y (b : n → 𝔪.ResidueRing) : n → 𝔸f E :=
    star (idem 𝔪.places • (↑𝔪.generator⁻¹ : 𝔸f E) • (↑) ∘ z b)
  have hy (b : n → 𝔪.ResidueRing) : y b ∈ translations n q (star (d : 𝔸f E)) :=
    star_idem_smul_mem_translations 𝔪 hd (z b)
  let c : ℂ := (card (n → 𝔪.ResidueRing) : ℂ)⁻¹
  have hc_int : ↑(absNorm (span {g}) ^ card n) * c ∈ integralAway q :=
    div_mem_integralAway (card_residueRing_pi_dvd 𝔪 hg)
  have h_point (a : n → 𝔪.ResidueRing) :
      IsAdmissibleCombination (fun y ↦ V.finHeisenbergOp y v) (translations n q (star (d : 𝔸f E))) q
        (absNorm (span {g}) ^ card n) p 1 (δ a) := by
    let w (b : n → 𝔪.ResidueRing) : 𝒮 V := 𝔪.primAddChar (-a ⬝ᵥ b) • V.finHeisenbergOp (y b) v
    have h_mean : δ a = ∑ b : n → 𝔪.ResidueRing, c • w b := by
      simp only [δ, c, w, y, 𝔪.schrodingerOp_single_eq_mean_translate_projOn V u a hz, huv]
    have h_comb : IsAdmissibleCombination w (Finset.univ : Finset (n → 𝔪.ResidueRing)) q
        (absNorm (span {g}) ^ card n) p 1 (δ a) := by
      simpa only [h_mean] using .of_sum (fun _ _ ↦ hc_int) (by
        simp only [card_pi, Finset.prod_const, Finset.card_univ, Nat.cast_pow, map_inv₀,
          map_pow, map_natCast, norm_inv, norm_pow, RCLike.norm_natCast, Finset.sum_const,
          nsmul_eq_mul, ne_eq, pow_eq_zero_iff', Nat.cast_eq_zero, card_ne_zero, false_and,
          not_false_eq_true, mul_inv_cancel₀, le_refl, implies_true, c])
    exact h_comb.of_eq_isOfFinOrder_smul fun b _ ↦
      ⟨𝔪.primAddChar (-a ⬝ᵥ b), h_root _, y b, hy b, rfl⟩
  have h_sum : V.schrodingerOp 𝔪.places (𝔪.liftFn Ψ) u = ∑ a : n → 𝔪.ResidueRing, Ψ a • δ a := by
    conv_lhs => rw [pi_eq_sum_univ' Ψ]
    simp only [map_sum, map_smul, sum_apply, smul_apply, δ]
  have h_comb : IsAdmissibleCombination δ (Finset.univ : Finset (n → 𝔪.ResidueRing)) q 1 p B
      (V.schrodingerOp 𝔪.places (𝔪.liftFn Ψ) u) := by
    simpa only [h_sum] using .of_sum
      (fun a _ ↦ by rw [Nat.cast_one, one_mul]; exact hΨ_int a) hΨ_size
  exact h_comb.bind _ 1 (fun a _ ↦ h_point a) (by simp only [one_mul, dvd_refl])
    (fun _ ↦ by simp only [abs_one, mul_one, le_rfl])

/-- The case `d = g` of `isAdmissibleCombination_schrodingerOp_of_reduction`. Let `V` be a hermitian
space over the CM field `E`, `u` a vector of its Weil representation `𝒮 V`, and `𝔪` a modulus that
divides `g q`. Let `v` be the mean `projOn 𝔪.places u` of the Heisenberg translates
`finHeisenbergOp y u` over the integral `y` supported at the primes dividing `𝔪` and their
conjugates. Let `Ψ` be a function on vectors modulo `𝔪` with values integral away from `q`. The
operator `V.schrodingerOp` attached to `Ψ` sends `u` to a finite sum `∑ r y • finHeisenbergOp y v`
over vectors `y` with `star g • y` integral away from `q`, and each `N(g) ^ card n * r y` is
integral away from `q`, with `N(g)` the absolute norm of `(g)`. If under the proposition `p` all
`∑ ‖σ (Ψ x)‖ ≤ B`, for the automorphisms `σ` of `ℂ`, then under `p` all `∑ ‖σ (r y)‖ ≤ B`. -/
lemma isAdmissibleCombination_schrodingerOp {g : 𝓞 E} {q : ℕ} [WeilData E] {s : n → ℤˣ}
    (V : Space E n s) (𝔪 : Modulus E) {Ψ : (n → 𝔪.ResidueRing) → ℂ} {p : Prop} {B : ℝ} {u v : 𝒮 V}
    (hg : g * q ∈ 𝔪.ideal) (hΨ_int : ∀ x : n → 𝔪.ResidueRing, Ψ x ∈ integralAway q)
    (hΨ_size : p → ∀ σ : ℂ ≃+* ℂ, ∑ x : n → 𝔪.ResidueRing, ‖σ (Ψ x)‖ ≤ B)
    (huv : V.projOn 𝔪.places u = v) :
    IsAdmissibleCombination (fun y : n → 𝔸f E ↦ V.finHeisenbergOp y v)
      (translations n q (star (algebraMap (𝓞 E) (Ô E) g : 𝔸f E))) q
      (absNorm (span {g}) ^ card n) p B (V.schrodingerOp 𝔪.places (𝔪.liftFn Ψ) u) :=
  isAdmissibleCombination_schrodingerOp_of_reduction V 𝔪 hg hΨ_int hΨ_size huv
    (by simpa only [map_mul, reduction_algebraMap, map_natCast] using Quotient.eq_zero_iff_mem.2 hg)

end New.Seesaw

end
