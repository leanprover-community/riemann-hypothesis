module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.JfSmoothBuiltOfLeaves
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CayleyAlgebraicHolds
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CayleySmoothnessHolds
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ClassicalToWeakSolution
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJfSSymbolLevi
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.GroupVectorSpace
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LeftTypeActionHolds
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LieBasisHolds
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PositiveDomainIsDomain
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RightTypeActionHolds
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.StabilizerFixesTailCoords
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

theorem group_chart_holds : GChart := gChart_of lie_basis_holds cayley_algebraic_holds group_vector_space cayley_smoothness_holds

theorem unitary_capelli_holds : UCap := uCap_of positive_domain_is_domain right_type_action_holds left_type_action_holds

theorem jfSmoothBuilt_of_rest (hN : NDiff) (hP : GEqsPost) (hC : SmoothOfCoeffs) (hE : ChartEqs) (hR : EllRegW) :
    JfSmoothBuilt :=
  jfSmoothBuilt_of_leaves hN unitary_capelli_holds hP hC group_chart_holds hE classical_to_weak_solution hR JfS.symbol_nilpotent_holds lie_stabilizer_splitting

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
