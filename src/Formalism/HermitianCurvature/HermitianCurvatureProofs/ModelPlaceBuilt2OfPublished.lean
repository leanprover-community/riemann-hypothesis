module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.JfSmoothBuiltOfLeaves
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.GroupEquationsPostHolds
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.JfSmoothBuiltOfRest
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NilpotentDerivative
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SmoothOfCoefficientsHolds
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

theorem jfSmoothBuilt_of_chart (hE : ChartEqs) (hR : EllRegW) : JfSmoothBuilt :=
  jfSmoothBuilt_of_rest nilpotent_derivative group_equations_post_holds smooth_of_coefficients_holds hE hR

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

namespace Formalism.FourierDecayAlt.P.CutMP

end Formalism.FourierDecayAlt.P.CutMP
