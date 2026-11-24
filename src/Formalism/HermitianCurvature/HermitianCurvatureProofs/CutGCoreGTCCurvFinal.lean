module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCCurvCut
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCTheta
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCCurvBlock
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCCurvPoly
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCCurvRTT
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCCurvScal
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCCurvTop
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

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

theorem curvature_polynomial_holds : GTCCurvPoly := curvature_polynomial_of_scalar curvature_scalar_holds

theorem curvature_identity_holds : GTCCurvId :=
  gTCCurvId_of_cut curvature_polynomial_holds curvature_radial_torus_holds curvature_block_form_holds

theorem top_normal_form_of_curvature : GTRTopNF := gTRTopNF_of_curvPoly curvature_polynomial_holds

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
