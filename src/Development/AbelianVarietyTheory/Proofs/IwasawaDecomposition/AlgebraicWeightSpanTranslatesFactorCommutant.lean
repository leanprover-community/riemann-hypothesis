module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolyRep
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraicWeightPolyMatrixMultiplicativeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjugateNeSelf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanRationalPointOrbitAlgebraicWeightStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

namespace GlobalTheory.AlgWtHW

theorem span_tau_commutant : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : AlgWt L n) (ι : Type) [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ a.W) (P : ι → ι → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ), Agrees a b P → ∀ (τ : L →+* ℂ) (v : ι → ℂ), v ≠ 0 → ∀ w : ι → ℂ, w ∈ Submodule.span ℂ {x | ∃ (B : GL (Fin n) ℂ) (M : Matrix ι ι ℂ), (∀ A : GL (Fin n) ℂ, M * evM P (evPt τ A) = evM P (evPt τ A) * M) ∧ x = evM P (evPt τ B) *ᵥ (M *ᵥ v)} := by
  intro L _ _ _ n a ι _ _ b P hA τ v hv w
  classical
  have hS := GlobalTheory.T.span_rationalPoint_orbit_algebraicWeight L n a ι b P hA v hv w
  refine Submodule.span_mono ?_ hS
  rintro x ⟨γ₀, hγ, rfl⟩
  obtain ⟨_, hmul⟩ := GlobalTheory.T.algebraicWeight_polyMatrix_multiplicative L n a ι b P hA
  set B : GL (Fin n) ℂ := Matrix.GeneralLinearGroup.map τ γ₀ with hBdef
  have hBv : B.val = γ₀.val.map τ := rfl
  set R : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ := fun σ =>
    if σ = τ ∨ σ = ComplexEmbedding.conjugate τ then 1 else ratPt γ₀.val σ with hRdef
  have hU := isUPt_ratPt γ₀ hγ
  have hR : IsUPt R := by
    intro σ
    by_cases h : σ = τ ∨ σ = ComplexEmbedding.conjugate τ
    · have h' : ComplexEmbedding.conjugate σ = τ ∨ ComplexEmbedding.conjugate σ = ComplexEmbedding.conjugate τ := by
        rcases h with h | h
        · right; rw [h]
        · left; rw [h, conj_conj]
      simp only [R, if_pos h, if_pos h', Matrix.transpose_one, mul_one]
    · have h' : ¬ (ComplexEmbedding.conjugate σ = τ ∨ ComplexEmbedding.conjugate σ = ComplexEmbedding.conjugate τ) := by
        rintro (h' | h')
        · exact h (Or.inr (by rw [← h', conj_conj]))
        · exact h (Or.inl (by simpa [conj_conj] using congrArg ComplexEmbedding.conjugate h'))
      simp only [R, if_neg h, if_neg h']
      exact hU σ
  have hinv : ((B⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) = (ratPt γ₀.val (ComplexEmbedding.conjugate τ))ᵀ := by
    apply Units.inv_eq_of_mul_eq_one_right
    exact hU τ
  have hdec : ratPt γ₀.val = fun σ => tauPt τ B σ * R σ := by
    funext σ
    have hne := conjugate_ne_self τ
    by_cases h1 : σ = τ
    · subst h1
      simp [tauPt, R, hBv, ratPt]
    · by_cases h2 : σ = ComplexEmbedding.conjugate τ
      · subst h2
        simp only [tauPt, if_neg h1, if_true, R, or_true, mul_one]
        rw [hinv, Matrix.transpose_transpose]
      · simp [tauPt, R, h1, h2]
  have hcomm : ∀ A : GL (Fin n) ℂ, (fun σ => tauPt τ A σ * R σ) = (fun σ => R σ * tauPt τ A σ) := by
    intro A
    funext σ
    by_cases h : σ = τ ∨ σ = ComplexEmbedding.conjugate τ
    · simp [R, h]
    · have h1 : σ ≠ τ := fun e => h (Or.inl e)
      have h2 : σ ≠ ComplexEmbedding.conjugate τ := fun e => h (Or.inr e)
      simp [tauPt, h1, h2]
  refine ⟨B, evM P (upt R), ?_, ?_⟩
  · intro A
    rw [evPt_eq_upt, ← hmul _ _ hR (isUPt_tauPt τ A), ← hmul _ _ (isUPt_tauPt τ A) hR, hcomm A]
  · rw [hdec, hmul _ _ (isUPt_tauPt τ B) hR, evPt_eq_upt, Matrix.mulVec_mulVec]

end GlobalTheory.AlgWtHW
