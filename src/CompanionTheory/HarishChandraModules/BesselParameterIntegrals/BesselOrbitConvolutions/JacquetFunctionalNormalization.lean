module

public import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.BesselOrbitConvolutions.BesselNonvanishingReduction
public import CompanionTheory.AutomorphicTheory.RankOneEstimates.DecSender
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.AdmissibleOfIwasawa
public import Formalism.LocalToGlobal.SiegelLatticeTheory.BesselDiscreteSeries.DecLowPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.WeightedGaugeFactors.FactsDS
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

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

namespace CompanionTheory.D.Upq.BesselFunctionalConstruction

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

theorem inputs_holds : Inputs := by
  have hDecay := CompanionTheory.FamilyDerivativeExpansion.DecS.decay_infinite_range
  exact ⟨Formalism.L2.SG.BesselDiscreteSeries.decLow, hDecay,
    CompanionTheory.D.gk.admitted.k_finite_smooth, trivial⟩

end CompanionTheory.D.Upq.BesselFunctionalConstruction

end
