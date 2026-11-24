module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsPlaceCofactorValuationLowerBound
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CofactorLowerBoundOfPlaceBoundWitt
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical

theorem _root_.GlobalTheory.T.lowAt_of_placeCofactorValuationLowerBound : ∀ (p : ℕ) [Fact p.Prime] (X : Sys p) (Y : Pend X) (j : ℕ) (v : X.Pl) (g : ℝ), MvPowerSeries.constantCoeff Y.be = 0 → IsPlaceCofactorValuationLowerBound X Y.be j v g → Y.LowAt j v g := by
  first | exact @GlobalTheory.TwU.LowGen.cofactor_lower_bound_of_place_bound_witt | exact GlobalTheory.TwU.LowGen.cofactor_lower_bound_of_place_bound_witt | (intros; apply GlobalTheory.TwU.LowGen.cofactor_lower_bound_of_place_bound_witt <;> assumption)
