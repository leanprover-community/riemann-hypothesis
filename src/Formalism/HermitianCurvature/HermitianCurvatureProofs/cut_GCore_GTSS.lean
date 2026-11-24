module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCLocalCut
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTSSCut
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCLRadT
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTSSAdj
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTSSConst
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTSSLocal
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTSSPhase
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

theorem gTSS_of_adj_radT : GTSSAdjPt → GTCLRadT → GTSS := fun hA hR =>
  gTSS_of_cut (gTSSLocal_of_radT hR) hA SSC.second_shift_constant SSPh.second_shift_phase_holds

theorem gTSS_of_adj : GTSSAdjPt → GTSS := fun hA => gTSS_of_adj_radT hA radial_torus_local_holds

theorem second_shift_gauge_holds : GTSS := gTSS_of_adj second_shift_adjoint_pointwise

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
