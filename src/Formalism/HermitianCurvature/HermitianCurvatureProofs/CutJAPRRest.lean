module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRCoreCut
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRAlgSS
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRAsm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRCPCoreAsm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRCPLeftCov
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRCPPSCalc
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRCPRcComm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRCPRcLin
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRCPRcSmooth
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRCPRightCov
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRCPSecDeriv
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRFibStable
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRKapLine
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRPHPhaseInvOfCut
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRPHPhaseSec
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRPHRotRadSp
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRPHThtRot
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRPhaseExtract
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRTWNe
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRTransfer
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnRepThtFacts
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LowerUnipotentHasRepresentation
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LowerUnipotentRotationHolds
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
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRDatumConst

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR

theorem phase_invariance_holds : PhaseInv :=
  PH.phase_invariance_of_truncation PH.phase_section_holds PH.lower_unipotent_rotation_holds PH.rotation_radial_space_holds PH.theta_rotation_holds kappa_line_holds algebraic_shift_holds
    datum_constancy_holds fibre_stability_holds

theorem corePoly_of (hD : CP.Decomp) (hW : CP.WordPSVOfCut) : CorePoly :=
  CP.radial_polynomial_of_truncation CP.lower_unipotent_matrix_words
    (hW CP.radial_coefficient_linearity CP.radial_coefficient_smoothness CP.radial_coefficient_commutation CP.left_covariance_holds CP.right_covariance_holds CP.section_derivative_holds hD
      CP.polynomial_shift_calculation)
    CP.polynomial_shift_calculation

theorem polyRadialS_of (hD : CP.Decomp) (hW : CP.WordPSVOfCut) : PolyRadialS :=
  polynomialRadial_of_base polynomial_radial_base_holds SSn.Rep.theta_facts_hold transfer_holds datum_constancy_holds kappa_line_holds
    fibre_stability_holds algebraic_shift_holds (corePoly_of hD hW) phase_invariance_holds phase_extraction_holds word_nonvanishing_holds

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR
