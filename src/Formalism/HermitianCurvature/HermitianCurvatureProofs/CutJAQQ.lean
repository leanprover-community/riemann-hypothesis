module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDQQ
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDGaugeQQAsm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddOp
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BoundedOperatorsSquareIntegrable
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABStar
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAIsAdj
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPhi
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDCCLower
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatBdd
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDJDJComm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TransferSquareIntegrableHolds
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

open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA

open NumberField Formalism.FourierDecayAlt.P.CutMP

noncomputable section

def JAAssembleQQ : Prop :=
  JDHatOpQQ → JDHatBdd → JDJComm → JDCCLower → TransferSquareIntegrable → BoundedOperatorsSquareIntegrable → JABddOpQQ → JABddStar → JAIsAdj → JAPhiOp →
    JAStarOp → JAGroupAdj → JALocCC → JAFFStable → JAdjTrQQ

theorem jAdjTrQQ_of_leaves (hA : JAAssembleQQ) (h1 : JDHatOpQQ) (h7 : JABddOpQQ) (h11 : JAStarOp)
    (h12 : JAGroupAdj) (h13 : JALocCC) (h14 : JAFFStable) : JAdjTrQQ :=
  hA h1 hat_bounded_decay_holds transfer_commutation_holds class_lower_decay_holds transfer_square_integrable_holds bounded_operators_square_integrable h7 transfer_star_bound_holds transfer_is_adjoint_holds phi_operator_transfer_holds h11
    h12 h13 h14

end

end Formalism.FourierDecayAlt.P.CutMP.JA
