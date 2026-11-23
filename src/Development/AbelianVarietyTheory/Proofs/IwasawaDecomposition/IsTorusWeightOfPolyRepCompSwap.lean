module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolyRep
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Matrix.PEquiv
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Basic.PEquiv

@[expose] public section

open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

namespace GlobalTheory

theorem isWt_comp_swap : ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ),
    IsPolyRep Φ → ∀ μ : Fin n → ℤ, IsWt Φ μ → ∀ i j : Fin n, IsWt Φ (μ ∘ Equiv.swap i j) := by
  intro n ι _ _ Φ hΦ μ ⟨w, hw0, hw⟩ i j
  set σ : Equiv.Perm (Fin n) := Equiv.swap i j with hσ
  set P : Matrix (Fin n) (Fin n) ℂ := σ.toPEquiv.toMatrix with hP
  have hσσ : ∀ k, σ (σ k) = k := fun k => Equiv.swap_apply_self _ _ _
  have hPP : P * P = 1 := by
    rw [hP, ← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans]
    have : σ.trans σ = Equiv.refl _ := by ext k; simp [hσσ]
    rw [this, Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]
  let p : GL (Fin n) ℂ := ⟨P, P, hPP, hPP⟩
  have hpp : p * p = 1 := Units.ext hPP
  refine ⟨Φ p *ᵥ w, ?_, ?_⟩
  · intro h
    apply hw0
    have : Φ p *ᵥ (Φ p *ᵥ w) = 0 := by rw [h]; simp
    rwa [mulVec_mulVec, ← hΦ.mul, hpp, hΦ.one, one_mulVec] at this
  · intro D hD
    have hent : ∀ a b, (p * D * p).val a b = D.val (σ a) (σ b) := by
      intro a b
      show (P * D.val * P) a b = _
      rw [hP, PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
      simp [hσ, Equiv.symm_swap]
    have hD' : (p * D * p).val.IsDiag := by
      intro a b hab
      rw [hent]
      exact hD (fun h => hab (σ.injective h))
    have key : Φ D * Φ p = Φ p * Φ (p * D * p) := by
      rw [← hΦ.mul, ← hΦ.mul]
      congr 1
      rw [← mul_assoc, ← mul_assoc, hpp, one_mul]
    have hprod : (∏ k, (p * D * p).val k k ^ μ k) = ∏ k, D.val k k ^ (μ ∘ σ) k := by
      simp only [hent, Function.comp]
      rw [← Equiv.prod_comp σ (fun k => D.val k k ^ μ (σ k))]
      simp [hσσ]
    rw [mulVec_mulVec, key, ← mulVec_mulVec, hw _ hD', hprod, mulVec_smul]
end GlobalTheory
