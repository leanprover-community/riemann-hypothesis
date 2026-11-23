module

public import Formalism.HermitianCurvature.PrimeToDifferent
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.FinrankLeOfMapLe
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LocalisationScaledIdealMemIff
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PeriodLatticeFactsSplitOfGeneral
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SplitPrimeToDifferent
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TwistedIsRealOrderLattice
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

namespace Formalism.FourierDecayAlt.P

theorem lattice_facts_general : Formalism.FourierDecayAlt.S6.LatticesGeneral :=
  assemble_lattice_facts degreeFacts_statement different_power_conj_stable
    unramRelative twistedLatticeBetween twistedLatticeIndex dual_lattice_subset
    traceDualGe scaledIdealNorm covolumeIndex

end Formalism.FourierDecayAlt.P
