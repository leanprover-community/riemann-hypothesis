module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatTensorMovedTensorFinsetSumLinear
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory GlobalTheory.FunObj

theorem _root_.GlobalTheory.T.flatTensor_movedTensor_finset_sum_linear : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (G : GlobalTheory.SplitFlip.Grid k) (hs : 1 ≤ G.s) (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure], Continuous ψ → ∀ (ϖ : kˣ) (e : ℕ) (keep : Bool) (g : G.VertexGroup) {ι : Type} (S : Finset ι) (x : ι → ℂ) (T : ι → G.Args → ℂ), (∀ i ∈ S, G.IsTensor ϖ e (GlobalTheory.SplitFlip.oppositePath G.m) (T i)) → ∀ X Y, flatTensor hs ψ ν (moved G keep g (fun z => ∑ i ∈ S, x i * T i z)) X Y = ∑ i ∈ S, x i * flatTensor hs ψ ν (moved G keep g (T i)) X Y := by
  first | exact @GlobalTheory.FunObj.flatTensor_moved_sum | exact GlobalTheory.FunObj.flatTensor_moved_sum | (intros; apply GlobalTheory.FunObj.flatTensor_moved_sum <;> assumption)
