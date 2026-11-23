module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LatticeJetsAreBoundedMomentsProdAndSum
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

open GlobalTheory.MomOne GlobalTheory.MomN PowerSeries
open scoped ComplexConjugate

theorem _root_.GlobalTheory.T.latticeJetsAreBoundedMoments_prod_and_sum : ∀ (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (ω : ℂ_[q]) (Λ : AddSubgroup V), (∀ (m : Type) [Fintype m] (G : m → V → ℂ), (∀ j, ContDiff ℂ ⊤ (G j)) → (∀ j, LatInt ι ω Λ (G j)) → LatInt ι ω Λ fun z => ∏ j, G j z) ∧ ∀ (m : Type) (s : Finset m) (c : m → ℂ) (G : m → V → ℂ), (∀ j ∈ s, ContDiff ℂ ⊤ (G j)) → (∀ j ∈ s, ‖ι (c j)‖ ≤ 1) → (∀ j ∈ s, LatInt ι ω Λ (G j)) → LatInt ι ω Λ fun z => ∑ j ∈ s, c j * G j z := by
  first | exact @GlobalTheory.MomN.latInt_prod_sum | exact GlobalTheory.MomN.latInt_prod_sum | (intros; apply GlobalTheory.MomN.latInt_prod_sum <;> assumption)
