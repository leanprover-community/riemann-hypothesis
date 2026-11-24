module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.FormalDegreeCompactDualIff
public import Development.WeilBound.RepresentationTheoryGL.FormalDegree.FormalDegreeHilbert.HlamStable
public import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.DiscreteSeriesHilbert.HilbertSpaceRealisationHolds
public import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.EquivariantSections.KeyIdentityHolds
public import Development.WeilBound.RepresentationTheoryGL.FormalDegree.FormalDegreeHilbert.ExplicitFunctionSquareIntegrable
import Development.WeilBound.RepresentationTheoryGL.FormalDegree.FormalDegreeHilbert.NormIndOfSteps
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

namespace PositivityTheory.RgFd.B

open PositivityTheory.RgDs

theorem fdAll : FdAll := fdAll_of_key K.key_identity_holds Hilb.hilbert_space_realisation_holds

theorem formalDegreeCompactDual : GlobalTheory.Published.FormalDegreeCompactDual := realMetaplectic_of_forall fdAll

end PositivityTheory.RgFd.B
