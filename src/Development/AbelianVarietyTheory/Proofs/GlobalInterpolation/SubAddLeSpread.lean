module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.BelowFiniteNonempty
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.KerT

namespace GlobalTheory.KerT

theorem sub_add_le_spread {N : ℕ} (lam : DomWeight N) (a b : Fin N) :
    lam.w a - lam.w b + (N : ℤ) ≤ lam.spread := by
  have hN : 0 < N := a.pos
  have h1 : lam.w a ≤ lam.w ⟨0, hN⟩ := lam.anti (Fin.le_def.2 (Nat.zero_le _))
  have h2 : lam.w ⟨N - 1, by omega⟩ ≤ lam.w b := lam.anti (Fin.le_def.2 (by have := b.2; simp only; omega))
  unfold DomWeight.spread
  rw [dite_eq_left hN]
  linarith

theorem alcoveAt_of_ok : ∀ (Z : Dat), Z.Ok → ∀ (u : Z.Pr.Word) (j : ℕ), j ≤ Z.R.m → AlcoveAt Z.W u j := by
  intro Z hZ u j hj τ a b
  have h1 := hZ.sizes.two_spread_lt u j hj τ
  have h2 := sub_add_le_spread (Z.W.lamTrue u j τ) a b
  linarith

end GlobalTheory.KerT
