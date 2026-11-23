module

public import Formalism.SharpRestriction.Divisibility.OrbitPlaces
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitSumCount.SizeGe
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

theorem PI.SumOrbC : ∀ (D : Formalism.BasicNotions.D7) (L : Formalism.BasicNotions.SizeData₂ D) (X : Formalism.MainNotions.G.Inst D L) (K : Formalism.MainNotions.G.Consts) (ce : Formalism.BasicNotions.ErrC) (E : Formalism.MainNotions.OrbitPlaces.Ent D) (C6 C : ℝ), Formalism.MainNotions.OrbitPlaces.Shape D L X E → Formalism.MainNotions.OrbitPlaces.CLarge C6 C K ce → Formalism.MainNotions.OrbitPlaces.ValuationSumBound E L ce C :=
  fun D L X K ce E C6 C hS hC => SumOrbCW.sumOrbC D L X K ce E C6 C hS hC
