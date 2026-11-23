module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAStarOp2
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASASecAsm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASASecCover
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASASecRad
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SelfAdjointDescentHolds
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutMP.JA

theorem self_adjoint_section_holds : Formalism.FourierDecayAlt.P.CutMP.JA.SA.SASection :=
  Formalism.FourierDecayAlt.P.CutMP.JA.SA.sASection_of_parts Formalism.FourierDecayAlt.P.CutMP.JA.SA.radial_section_holds
    Formalism.FourierDecayAlt.P.CutMP.JA.SA.self_adjoint_descent_holds Formalism.FourierDecayAlt.P.CutMP.JA.SA.self_adjoint_cover_holds

end Formalism.FourierDecayAlt.P.CutMP.JA
