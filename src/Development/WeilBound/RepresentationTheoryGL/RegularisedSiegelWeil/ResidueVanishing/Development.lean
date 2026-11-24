module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ResidueVanishing.Leaves
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinContinuationOfDoublingMethod
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ResidueVanishing.Assembly
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ResidueVanishing.ContinuationPoleOrder
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ResidueVanishing.ContinuousInvariantCoefficients
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ResidueVanishing.LocalRepresentationSmoothness
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ResidueVanishing.ThetaContinuation
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
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm

@[expose] public section

noncomputable section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW

namespace PositivityTheory.Rg.Rsw.Kplug

theorem resKilled_of_leaves : K0 → K1 → K2 → SimplePoleRescaling → ContinuousInvariantCoefficients → KillingPolyConst → ContinuationThroughChart → K4 →
    GlobalTheory.Published.SiegelEisensteinContinuation → PositivityTheory.Rg.Rsw.ResCore → ResidueVanishing :=
  residue_vanishes_of_siegel_eisenstein

theorem k0 : K0 := mem_section_space
theorem k1 : K1 := local_representation_smoothness
theorem k2 : K2 := continuation_pole_order
theorem k2b : SimplePoleRescaling := simple_pole_rescaling
theorem k2c : ContinuousInvariantCoefficients := continuous_invariant_coefficients
theorem k3a : KillingPolyConst := continuation_chart_defined
theorem k3b : ContinuationThroughChart := continuation_through_chart
theorem k4 : K4 := theta_continuation

theorem res_killed' : GlobalTheory.Published.SiegelEisensteinContinuation → PositivityTheory.Rg.Rsw.ResCore → ResidueVanishing :=
  resKilled_of_leaves k0 k1 k2 k2b k2c k3a k3b k4

end PositivityTheory.Rg.Rsw.Kplug

end
