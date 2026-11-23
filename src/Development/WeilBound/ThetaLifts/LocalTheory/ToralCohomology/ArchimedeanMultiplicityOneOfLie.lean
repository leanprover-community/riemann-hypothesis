module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.WeilBound.ThetaLifts.LocalTheory.UnramifiedDeterminedBySpherical
public import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.EvIHalfTrace
public import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.RLActs
public import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.RLFock
public import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.RLFrame
public import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.RLLines
public import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.RLParity
public import Development.WeilBound.ThetaLifts.EigenvalueEndgame.EigenKilling.PolRange
public import Development.WeilBound.ThetaLifts.LocalTheory.ToralCohomology.ArchimedeanMultiplicityOneOf
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

namespace PositivityTheory.ThKG.CayleyTransformDarboux

theorem archimedean_multiplicity_one_of_lie (h1 : GlobalTheory.RealLift.LieFirst) (h2 : GlobalTheory.RealLift.LieSecond) : Loc.ArchimedeanMultiplicityOne :=
  archimedean_multiplicity_one_of ⟨PositivityTheory.RL.actsLaws, PositivityTheory.RL.fockEx PositivityTheory.RL.derEx,
    PositivityTheory.ThKEnd.Comp.PR.polRange_of PositivityTheory.RL.actsLaws PositivityTheory.RL.derEx (PositivityTheory.RL.vacLine PositivityTheory.RL.derEx), h1, h2,
    PositivityTheory.RL.lineEx, PositivityTheory.RL.frameEx, PositivityTheory.RL.even_im_hermitian_sub⟩

end PositivityTheory.ThKG.CayleyTransformDarboux
