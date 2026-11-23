module

public import Formalism.HermitianCurvature.OperatorsCommuteTranslations
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ChainFirstIdentity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DpsiIsDerivation
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FirstExpansionIdentity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.IsotropicNormalFormFullStatement
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LeadingTermIdentity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ScalarInverseSimplification
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SecondExpansionIdentity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SignPermutationIdentity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ThirdPeelingMinorMemIdeal
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ThirdPolynomialExpansion
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

theorem Formalism.FourierDecayAlt.P.sign_permutation_identity : Formalism.FourierDecayAlt.C3.SignE :=
  Formalism.FourierDecayAlt.P.SignAntidiagonal.sign_permutation_identity

theorem Formalism.FourierDecayAlt.P.derivative_leading_zb : Formalism.FourierDecayAlt.C3.DleadZb :=
  Formalism.FourierDecayAlt.P.SignAntidiagonal.derivative_leading_zb

theorem Formalism.FourierDecayAlt.P.minors_first_case : Formalism.FourierDecayAlt.C3.MinorsFirstCase :=
  Formalism.FourierDecayAlt.P.SignAntidiagonal.minors_first_case

theorem Formalism.FourierDecayAlt.P.third_polynomial_expansion : Formalism.FourierDecayAlt.C3.MinorsThirdCase :=
  Formalism.FourierDecayAlt.P.SignAntidiagonal.third_polynomial_expansion

theorem Formalism.FourierDecayAlt.P.first_peeling_identity : Formalism.FourierDecayAlt.C3.PeelingOmittedColumn :=
  Formalism.FourierDecayAlt.P.SignAntidiagonal.first_peeling_identity

theorem Formalism.FourierDecayAlt.P.second_peeling_identity : Formalism.FourierDecayAlt.C3.PeelingCovector :=
  Formalism.FourierDecayAlt.P.SignAntidiagonal.second_peeling_identity

theorem Formalism.FourierDecayAlt.P.third_peeling_identity : Formalism.FourierDecayAlt.C3.PeelingDualColumn :=
  Formalism.FourierDecayAlt.P.SignAntidiagonal.third_peeling_identity

theorem Formalism.FourierDecayAlt.P.first_expansion_identity : Formalism.FourierDecayAlt.C3.ExpansionOmittedColumn :=
  Formalism.FourierDecayAlt.P.SignAntidiagonal.first_expansion_identity

theorem Formalism.FourierDecayAlt.P.second_expansion_identity : Formalism.FourierDecayAlt.C3.ExpansionDualColumn :=
  Formalism.FourierDecayAlt.P.SignAntidiagonal.second_expansion_identity

theorem Formalism.FourierDecayAlt.P.column_indicator_expansion : Formalism.FourierDecayAlt.C3.ExpansionCovector :=
  Formalism.FourierDecayAlt.P.SignAntidiagonal.column_indicator_expansion

theorem Formalism.FourierDecayAlt.P.chain_first_identity : Formalism.FourierDecayAlt.C3.LastColumnChain :=
  Formalism.FourierDecayAlt.P.SignAntidiagonal.chain_first_identity

theorem Formalism.FourierDecayAlt.P.leading_term_identity : Formalism.FourierDecayAlt.C3.LeadAA :=
  Formalism.FourierDecayAlt.P.SignAntidiagonal.leading_term_identity

theorem Formalism.FourierDecayAlt.P.leading_term_vector_identity : Formalism.FourierDecayAlt.C3.LeadAAv :=
  Formalism.FourierDecayAlt.P.SignAntidiagonal.leading_term_vector_identity

theorem Formalism.FourierDecayAlt.P.dpsi_is_derivation : Formalism.FourierDecayAlt.C3.DpsiDerivation :=
  Formalism.FourierDecayAlt.P.SignAntidiagonal.dpsi_is_derivation

theorem Formalism.FourierDecayAlt.P.isotropicNormalFormFull_statement : Formalism.FourierDecayAlt.C3.IsotropicNormalFormFull :=
  Formalism.FourierDecayAlt.P.SignAntidiagonal.isotropicNormalFormFull_statement
