module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.CompanionTheory.SegJacquet

theorem exists_isTopCut_two_of_jhMult_ne_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (Δ : Segment k) (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V), Zc.LSegJacquet k → IsLSeg Δ π →
    ∀ (x : Fin 2 → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N), (∀ a, 0 < (x a).1) → Zc.jm x hd π ≠ 0 →
    ∃ Γ : Fin 2 → Segment k, Zc.IsTopCut Δ Γ ∧ ∀ a, IsLSeg (Γ a) (x a).rep := by
  intro k _ _ _ _ Δ N V _ _ π hJ hπ x hd hpos hne
  by_contra hno
  exact hne ((hJ Δ π hπ 2 x hd hpos).2 hno)

end GlobalTheory.CompanionTheory.SegJacquet
