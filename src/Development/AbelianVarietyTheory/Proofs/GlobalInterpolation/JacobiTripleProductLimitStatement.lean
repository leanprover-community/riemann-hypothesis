module

public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MultipliableTpFactor
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.JacobiTripleProductLimit
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open Complex
open scoped Real

theorem _root_.GlobalTheory.T.jacobi_triple_product_limit : ∀ (τ : ℂ) (z : ℂ), 0 < τ.im → Filter.Tendsto (fun n : ℕ => ∑ j ∈ Finset.Icc (-(n : ℤ)) n, GlobalTheory.JacobiTriple.finCoeff (cexp (π * I * τ) ^ 2) n j * jacobiTheta₂_term j z τ) Filter.atTop (nhds (jacobiTheta₂ z τ * (GlobalTheory.JacobiTriple.qPochInf (cexp (π * I * τ) ^ 2))⁻¹)) := by
  first | exact @GlobalTheory.JacobiTriple.tendsto_finCoeff_sum_jacobiTheta₂ | exact GlobalTheory.JacobiTriple.tendsto_finCoeff_sum_jacobiTheta₂ | (intros; apply GlobalTheory.JacobiTriple.tendsto_finCoeff_sum_jacobiTheta₂ <;> assumption)
