module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ExponentTerms
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScaledBasisMemChainLattice

@[expose] public section

open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms GlobalTheory.RootEx.UnfoldShape

namespace GlobalTheory.RootEx.UnfoldShape

theorem isLattice_stdLat_and_act : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) [Fintype ι] [DecidableEq ι], Submodule.IsLattice k (stdLat k ι) ∧ ∀ (g : GL ι k) (L : Submodule 𝒪[k] (ι → k)), Submodule.IsLattice k L → Submodule.IsLattice k (act g L) := by
  intro k _ _ _ _ ι _ _
  refine ⟨⟨?_, ?_⟩, fun g L hL => ⟨?_, ?_⟩⟩
  · unfold stdLat
    refine Submodule.fg_pi fun _ => ?_
    rw [Submodule.one_eq_span]
    exact Submodule.fg_span_singleton _
  · intro s hs hli
    exact (LinearIndependent.iff_fractionRing _ _).mp hli
  · exact hL.fg.map _
  · intro s hs hli
    exact (LinearIndependent.iff_fractionRing _ _).mp hli

end GlobalTheory.RootEx.UnfoldShape
