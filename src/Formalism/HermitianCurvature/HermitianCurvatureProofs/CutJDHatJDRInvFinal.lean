module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpMRealInv
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpPRealInv
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDRInvCB
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDRInvEig
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDRInvEigAP
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDRInvMain
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

namespace Formalism.FourierDecayAlt.P.CutMP

theorem inverse_function_positive_holds : JDRInvFn :=
  jDRInvFn_of inverse_alpha_positive_holds inverse_beta_positive_holds inverse_beta_left_positive

theorem inverse_function_minus_holds : JDRInvFnM :=
  jDRInvFnM_of inverse_alpha_minus_holds inverse_alpha_left_minus inverse_beta_minus_holds

end Formalism.FourierDecayAlt.P.CutMP
