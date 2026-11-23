module

public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.LeadingExponentHomogeneous
public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.GTheta
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.IoBlockMonomial
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.MemIntPolOfCoeff
public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.SatBlock
public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.SymVarInlFst
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.TopOddNeEnd
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G

def RestKapNum : Prop := TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => KapNumAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc

theorem restBlockForm_of {D : Formalism.BasicNotions.D7} (h52 : Formalism.MainNotions.CovariantDegrees.FactorialUnitDecomposition D) (hK : RestKapNum) : RestBlockForm := by
  have h17 : TransportedAlt fun _ _ _ _ _ _ _ _ Cm _ => (17 : ℝ) ≤ Cm :=
    TransportedAlt.of_explicit (fun _ => 1) (fun _ _ => 17) (fun _ _ _ _ _ => 1)
      fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h _ _ _ _ _ _ _ _ _ _ => h
  refine TransportedAlt.mono ?_ ((thr_std.and h17).and hK)
  rintro C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc ⟨⟨⟨_, hstd⟩, hCm⟩, hKa⟩
  exact blockFormAt_of hCm hstd ioFockAt eigAt (homAt _ _ _ _ _ _ _ _ _) dvdAt satAt (gThetaAt D)
    (factAt_of h52 (kapAt_of hKa))

end Formalism.MainNotions.ColumnSystems.Pf
