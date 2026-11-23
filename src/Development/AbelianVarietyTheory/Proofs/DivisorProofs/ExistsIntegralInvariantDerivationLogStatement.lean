module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralInvariantDerivationLog
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

theorem _root_.GlobalTheory.T.exists_integral_invariant_derivation_log : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (d : ℕ) (G : LogFGL v d), ∃ D : Fin d → Fin d → MvPowerSeries (Fin d) C, (∀ k l, MvIsInt v (D k l)) ∧ ∀ (f : MvPowerSeries (Fin d) C) (k : Fin d) (α : Fin d →₀ ℕ), ((α k : C) + 1) * coeff (α + Finsupp.single k 1) (subst (expOf G) f) = coeff α (subst (expOf G) (∑ l, D k l * (show MvPowerSeries (Fin d) C from fun β => ((β l : C) + 1) * coeff (β + Finsupp.single l 1) f))) := by
  first | exact @GlobalTheory.LogJacobian.exists_integral_invariant_derivation | exact GlobalTheory.LogJacobian.exists_integral_invariant_derivation | (intros; apply GlobalTheory.LogJacobian.exists_integral_invariant_derivation <;> assumption)
