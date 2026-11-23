module

public import Formalism.LocalToGlobal.InertKernelTheory.DefsRepDict
public import Formalism.LocalToGlobal.InertKernelTheory.GenusOneModelExistsLattice
public import Formalism.LocalToGlobal.InertKernelTheory.StatementAlgT
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AlgTAll
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CurveDictOfCm
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRingEquivTranscendental
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
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgStatus
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.TorStatus

@[expose] public section

namespace GlobalTheory.CurveThetaInert

theorem torsionTaylorAlgebraic_latticeExists_of_cm (h2 : Formalism.L2.Th1.CM.CM2) :
    Formalism.L2.KerInert.AlgTAll ∧ Formalism.L2.KerInert.GenusOneModelExistsLattice ∧ Formalism.L2.KerInert.Rep.CurveDict :=
  ⟨GlobalTheory.ThLoc.algTAll,
    GlobalTheory.InertGenusOne.datum_exists_lattice h2 ReciprocityTheory.ChartRestriction.L1.cmIntegralityThree ReciprocityTheory.ChartRestriction.L1.cm4,
    GlobalTheory.CurveDictionary.curveDict_of_cm h2 ReciprocityTheory.ChartRestriction.L1.cmIntegralityThree ReciprocityTheory.ChartRestriction.L1.cm4⟩

end GlobalTheory.CurveThetaInert
