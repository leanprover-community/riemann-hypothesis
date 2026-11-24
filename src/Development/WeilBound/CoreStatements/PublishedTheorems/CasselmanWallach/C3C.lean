module

public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.SmoothSeminormAndSobolevBounds
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
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.IsKUnitaryOfIsInfUnitary

@[expose] public section

namespace PositivityTheory.CW

theorem c3c : KStableHighestWeightVector := by
  intro n ε V _ _ E hgl hun S hfd hS hne
  obtain ⟨w, hw, hw0, μ, hμ⟩ := ReciprocityTheory.ChartRestriction.DS.exists_khw hgl (ReciprocityTheory.ChartRestriction.DS.isKUnitary_of_isInfUnitary hun) hfd hS hne
  exact ⟨w, μ, hw, hw0, hμ⟩

end PositivityTheory.CW
