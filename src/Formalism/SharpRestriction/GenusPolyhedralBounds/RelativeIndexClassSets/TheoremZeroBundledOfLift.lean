module

public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LocalCOfLen
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LengthBaseT0
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LengthPoleInLift
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroBundledOfLengths
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps

theorem lenBase_all {D : D7} {B : Formalism.MainNotions.WeightFamilies.Prov D} {P : Formalism.MainNotions.ModuliIntegralCharts.Prov D} :
    ∀ (j : ℕ) (X : PJ D B P j) (ka wL wF : Formalism.MainNotions.WeightFamilies.Wt D j), LenBase (X := X) (ka := ka) (wL := wL) (wF := wF) :=
  fun _ _ _ _ _ => length_base_t0

theorem lenPoleL_all {D : D7} {B : Formalism.MainNotions.WeightFamilies.Prov D} {P : Formalism.MainNotions.ModuliIntegralCharts.Prov D} :
    ∀ (j : ℕ) (X : PJ D B P j) (ka wL wF : Formalism.MainNotions.WeightFamilies.Wt D j), LenPoleL (X := X) (ka := ka) (wL := wL) (wF := wF) := by
  intro j X ka wL wF G la Q S CRm T e c hOk hLift hW
  exact length_pole_t0 G la Q S CRm T e c hOk hW hLift

theorem theorem_zero_of_named_inputs {D : D7} {B : Formalism.MainNotions.WeightFamilies.Prov D} {P : Formalism.MainNotions.ModuliIntegralCharts.Prov D} : Conclusion1OfComb (D := D) (B := B) (P := P) :=
  theorem_zero_split_of_lengths lenBase_all lenPoleL_all

end Formalism.MainNotions.Gaps.EtaleWeightGaps
