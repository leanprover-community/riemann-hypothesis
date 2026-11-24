module

public import Formalism.SatakeDualWeyl.Statement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix

namespace Formalism.UG.P

open Formalism.UG

theorem cT_conj_eq {m k : Type} (M : Matrix m k ℂ) : cT (starRingEnd ℂ) M = Mᴴ := by
  ext i j
  simp [cT, Matrix.conjTranspose_apply]

section Sig

variable {n : Type} [Fintype n] [DecidableEq n]

theorem sig_data (J : Matrix n n ℂ) (p q : ℕ) (h : HasSignature J p q) :
    Fintype.card n = p + q ∧ ∃ Q : Matrix n (Fin p ⊕ Fin q) ℂ, Qᴴ * J * Q = Jpq p q := by
  obtain ⟨e, P, hP⟩ := h
  refine ⟨by rw [Fintype.card_congr e, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin], ?_⟩
  refine ⟨(P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).submatrix e id, ?_⟩
  rw [cT_conj_eq] at hP

  have hJ : J = (J.reindex e e).submatrix e e := by
    ext i j; simp
  rw [hJ, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv,
    Matrix.submatrix_id_id]
  exact hP

theorem sig_quad {p q : ℕ} (J : Matrix n n ℂ) (Q : Matrix n (Fin p ⊕ Fin q) ℂ)
    (hQ : Qᴴ * J * Q = Jpq p q) (x : Fin p ⊕ Fin q → ℂ) :
    star (Q *ᵥ x) ⬝ᵥ (J *ᵥ (Q *ᵥ x)) =
      (∑ i, star (x (Sum.inl i)) * x (Sum.inl i)) - ∑ j, star (x (Sum.inr j)) * x (Sum.inr j) := by
  rw [Matrix.star_mulVec, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
    ← Matrix.mul_assoc, hQ, ← Matrix.dotProduct_mulVec]
  simp [Jpq, Matrix.fromBlocks_mulVec, dotProduct, Fintype.sum_sum_type, sub_eq_add_neg,
    Matrix.neg_mulVec, Finset.sum_neg_distrib]

private lemma eq_zero_of_sum_star_mul_self_add_eq_zero {ι κ : Type} [Fintype ι] [Fintype κ] (a : ι → ℂ) (b : κ → ℂ)
    (h : (∑ i, star (a i) * a i) + ∑ j, star (b j) * b j = 0) : a = 0 ∧ b = 0 := by
  have hz : ∀ z : ℂ, star z * z = ((Complex.normSq z : ℝ) : ℂ) := fun z => by
    rw [Complex.normSq_eq_conj_mul_self]; rfl
  simp only [hz] at h
  rw [← Complex.ofReal_sum, ← Complex.ofReal_sum, ← Complex.ofReal_add, Complex.ofReal_eq_zero] at h
  have h1 : 0 ≤ ∑ i, Complex.normSq (a i) := Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  have h2 : 0 ≤ ∑ j, Complex.normSq (b j) := Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _
  have hA : ∑ i, Complex.normSq (a i) = 0 := by linarith
  have hB : ∑ j, Complex.normSq (b j) = 0 := by linarith
  rw [Finset.sum_eq_zero_iff_of_nonneg fun i _ => Complex.normSq_nonneg _] at hA hB
  exact ⟨funext fun i => Complex.normSq_eq_zero.1 (hA i (Finset.mem_univ _)),
    funext fun j => Complex.normSq_eq_zero.1 (hB j (Finset.mem_univ _))⟩

theorem sig_dim {p q p' q' : ℕ} (J : Matrix n n ℂ) (Q : Matrix n (Fin p ⊕ Fin q) ℂ)
    (hQ : Qᴴ * J * Q = Jpq p q) (Q' : Matrix n (Fin p' ⊕ Fin q') ℂ)
    (hQ' : Q'ᴴ * J * Q' = Jpq p' q') :
    p + q' ≤ Fintype.card n := by
  classical

  let φ : ((Fin p → ℂ) × (Fin q' → ℂ)) →ₗ[ℂ] (n → ℂ) :=
    { toFun := fun ab => Q *ᵥ Sum.elim ab.1 (0 : Fin q → ℂ) + Q' *ᵥ Sum.elim (0 : Fin p' → ℂ) ab.2
      map_add' := by
        intro x y
        have h1 : Sum.elim (x.1 + y.1) (0 : Fin q → ℂ) = Sum.elim x.1 (0 : Fin q → ℂ) + Sum.elim y.1 (0 : Fin q → ℂ) := by
          ext (i | i) <;> simp
        have h2 : Sum.elim (0 : Fin p' → ℂ) (x.2 + y.2) = Sum.elim (0 : Fin p' → ℂ) x.2 + Sum.elim (0 : Fin p' → ℂ) y.2 := by
          ext (i | i) <;> simp
        simp only [Prod.fst_add, Prod.snd_add, h1, h2, Matrix.mulVec_add]
        abel
      map_smul' := by
        intro c x
        have h1 : Sum.elim (c • x.1) (0 : Fin q → ℂ) = c • Sum.elim x.1 (0 : Fin q → ℂ) := by
          ext (i | i) <;> simp
        have h2 : Sum.elim (0 : Fin p' → ℂ) (c • x.2) = c • Sum.elim (0 : Fin p' → ℂ) x.2 := by
          ext (i | i) <;> simp
        simp only [Prod.smul_fst, Prod.smul_snd, h1, h2, Matrix.mulVec_smul, RingHom.id_apply,
          smul_add] }
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨a, b⟩ hab
    have hw : Q *ᵥ Sum.elim a (0 : Fin q → ℂ) = Q' *ᵥ (-(Sum.elim (0 : Fin p' → ℂ) b)) := by
      rw [Matrix.mulVec_neg]
      exact eq_neg_of_add_eq_zero_left hab
    have e1 := sig_quad J Q hQ (Sum.elim a (0 : Fin q → ℂ))
    have e2 := sig_quad J Q' hQ' (-(Sum.elim (0 : Fin p' → ℂ) b))
    rw [← hw, e1] at e2
    simp only [Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, Pi.neg_apply, star_zero, mul_zero,
      Finset.sum_const_zero, sub_zero, zero_sub, star_neg, neg_mul_neg] at e2
    have := eq_zero_of_sum_star_mul_self_add_eq_zero a b (by rw [e2]; ring)
    rw [this.1, this.2]
    rfl
  have := LinearMap.finrank_le_finrank_of_injective hinj
  rwa [Module.finrank_prod, Module.finrank_fin_fun, Module.finrank_fin_fun,
    Module.finrank_fintype_fun_eq_card] at this

end Sig

theorem signature_unique : Formalism.UG.SigUnique := by
  intro n _ _ J p q p' q' h h'
  obtain ⟨hc, Q, hQ⟩ := sig_data J p q h
  obtain ⟨hc', Q', hQ'⟩ := sig_data J p' q' h'
  have d1 := sig_dim J Q hQ Q' hQ'
  have d2 := sig_dim J Q' hQ' Q hQ
  omega

end Formalism.UG.P
