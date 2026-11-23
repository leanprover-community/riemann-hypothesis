module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpPRealInv
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpMRealInv
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpMRad
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpPRad
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRDrTr
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpMBeta
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpMConseq
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpMContPf
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpMStepAPf
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpMTop
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpPBeta
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpPConseq
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpPPCommPf
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpPTop
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRModelV
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDRInvFinal
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDRStepA
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDRStepB
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatPolyOK
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

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

theorem jDRRadP_of_steps (hA : JDRStepA) (hB : JDRStepB) : JDRRadP :=
  jDRRadP_of_parts JDBeta.residue_beta_holds residue_top_holds hA hB (jDRConseq_of residue_projection_commutation residue_continuity_holds)

theorem jDRGrpP_of_invFn (hA : JDRStepA) (hB : JDRStepB) (hI : JDRInvFn) : JDRGrpP :=
  jDRGrpP_of_parts (jDRRadP_of_steps hA hB) (jDRRealInvP_of_inv hI)

theorem jDRGrpM_of_vBeta_invFnM (hvB : JDRvBeta) (hvA : JDRvStepA) (hvS : JDRvStepB) (hIM : JDRInvFnM) : JDRGrpM :=
  jDRGrpM_of_parts (jDRRadM_of_parts hvB mirror_residue_top_holds hvA hvS (jDRvConseq_of mirror_residue_continuity))
    (jDRRealInvM_of_inv hIM)

theorem jDCapR_of_halves (hP : JDRGrpP) (hM : JDRGrpM) : JDCapR :=
  jDCapR_of_parts (jDRGrp_of_halves hP hM) residue_derivative_transition mirror_residue_model_holds

theorem jDOpR_of_poly_grp (hPoly : JDPolyOK) (hP : JDRGrpP) (hM : JDRGrpM) : JDOpR :=
  jDOpR_of_parts hPoly (jDCapR_of_halves hP hM)

theorem jDOpR_of_leaves (hPoly : JDPolyOK) (hA : JDRStepA) (hI : JDRInvFn) (hvB : JDRvBeta)
    (hvA : JDRvStepA) (hvS : JDRvStepB) (hIM : JDRInvFnM) : JDOpR :=
  jDOpR_of_poly_grp hPoly (jDRGrpP_of_invFn hA residue_second_move_holds hI) (jDRGrpM_of_vBeta_invFnM hvB hvA hvS hIM)

theorem jDOpR_of_invFn (hI : JDRInvFn) (hvS : JDRvStepB) (hIM : JDRInvFnM) : JDOpR :=
  jDOpR_of_leaves polynomial_decay_admissible residue_first_move_holds hI mirror_residue_beta_holds GrpMA.mirror_residue_first_move hvS hIM

theorem jDOpR_of_vStepB (hvS : JDRvStepB) : JDOpR :=
  jDOpR_of_invFn inverse_function_positive_holds hvS inverse_function_minus_holds

end Formalism.FourierDecayAlt.P.CutMP
