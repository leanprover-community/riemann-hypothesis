module

public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleClassGroupCardPos
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLocTheoryTied
public import Formalism.LocalRingCardinality.SpanPowerMembership
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism Formalism.BasicNotions
namespace GlobalTheory.MemLoc

theorem localGap_nonempty : ∀ {R : Formalism.BasicNotions.Ranks} (H : Formalism.BasicNotions.Host R),
    Nonempty (Formalism.BasicNotions.Examples₂.LocalGap H) := by
  intro R H
  obtain ⟨L, A, ⟨T⟩⟩ := exists_locTheory_tied
  exact ⟨⟨L, A, T⟩⟩

theorem record_nonempty : Nonempty Formalism.BasicNotions.D7 :=
  Formalism.BasicNotions.Examples₂.record_nonempty_of_localGap (localGap_nonempty _)

end GlobalTheory.MemLoc
