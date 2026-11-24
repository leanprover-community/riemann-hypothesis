module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.DetG

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

theorem det_genU (Ω : Type) [Field Ω] {S : Type} (r : S → ℕ) (s : S) : (genU Ω r s).det = 1 := by
  rw [det_of_lowerTriangular (genU Ω r s) fun a b h => ?_]
  · refine Finset.prod_eq_one fun a _ => ?_
    simp [genU]
  · have h' : a < b := h
    simp [genU, not_lt.2 h'.le, h'.ne]

variable (Ψ : Type) (p q : ℕ) (Ω : Type) [Field Ω] (τ : Ψ)

theorem wBlock_gMat : wBlock (gMat p q Ω τ) = genU Ω (rk Ψ p q) (.inl τ) := by
  ext a b
  have ea : (blockEquiv p q).symm (wEmb p q a) = .inr a := by
    rw [← blockEquiv_inr, Equiv.symm_apply_apply]
  have eb : (blockEquiv p q).symm (wEmb p q b) = .inr b := by
    rw [← blockEquiv_inr, Equiv.symm_apply_apply]
  change Matrix.fromBlocks (genU Ω (rk Ψ p q) (.inr τ)) 0 0 (genU Ω (rk Ψ p q) (.inl τ))
    ((blockEquiv p q).symm (wEmb p q a)) ((blockEquiv p q).symm (wEmb p q b)) = _
  rw [ea, eb]
  rfl

theorem omBlock_gMat : omBlock (gMat p q Ω τ) = genU Ω (rk Ψ p q) (.inr τ) := by
  ext a b
  have ea : (blockEquiv p q).symm (omEmb p q a) = .inl a := by
    rw [← blockEquiv_inl, Equiv.symm_apply_apply]
  have eb : (blockEquiv p q).symm (omEmb p q b) = .inl b := by
    rw [← blockEquiv_inl, Equiv.symm_apply_apply]
  change Matrix.fromBlocks (genU Ω (rk Ψ p q) (.inr τ)) 0 0 (genU Ω (rk Ψ p q) (.inl τ))
    ((blockEquiv p q).symm (omEmb p q a)) ((blockEquiv p q).symm (omEmb p q b)) = _
  rw [ea, eb]
  rfl

theorem detFac_gMat (Ψ : Type) (p q : ℕ) (Ω : Type) [Field Ω] (τ : Ψ) (i : Fin (p + q)) :
    detFac p i (gMat p q Ω τ) = 1 := by
  have hw : minorIJ (gMat p q Ω τ) (wIdx (p + q) p) (wIdx (p + q) p) = 1 := by
    rw [minorIJ_wIdx, wBlock_gMat]
    exact det_genU Ω (rk Ψ p q) (.inl τ)
  have ho : minorIJ (gMat p q Ω τ) (omIdx (p + q) p) (omIdx (p + q) p) = 1 := by
    rw [minorIJ_omIdx, omBlock_gMat]
    exact det_genU Ω (rk Ψ p q) (.inr τ)
  simp only [detFac, hw, ho, ite_self, mul_one]

end GlobalTheory.CompanionTheory.Ar.PB.FMX.DetG
