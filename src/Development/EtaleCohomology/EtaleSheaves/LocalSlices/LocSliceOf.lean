module

public import Development.EtaleCohomology.EtaleSheaves.LocalSlices
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

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4 HomologicalComplex

namespace LateralTheory.E.LocSlicePf

def PullMono : Prop := ∀ (R : Type) [CommRing R] (X : Scheme.{0}),
  ((Over.forget X).sheafPullback (ModuleCat.{1} (ULift.{1} R)) (Scheme.etaleTopology.{0}.over X)
    Scheme.etaleTopology.{0}).PreservesMonomorphisms

theorem InjOver_of (hM : PullMono) : InjOver := by
  intro R _ X
  have := hM R X
  exact Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    ((Over.forget X).sheafAdjunctionContinuous (ModuleCat.{1} (ULift.{1} R)) (Scheme.etaleTopology.{0}.over X)
      Scheme.etaleTopology.{0})

theorem LocSlice_of' (hM : PullMono) : LateralTheory.E.LeafLocPf.LocSlice := LocSlice_of (InjOver_of hM)

end LateralTheory.E.LocSlicePf
