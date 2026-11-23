module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadialIdentityOfQuadratic
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAFFStableAdjComm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJALocToolsTheta
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDGqRes
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDJNice
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDOpFF
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDResRad
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDStartCoord
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDWaveFF
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDWaveRad
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermMulVecMulVec
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadialOperatorLocality
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadialWaveOrbital
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SiteZeroMatrixEntry
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

namespace Formalism.FourierDecayAlt.P.CutSE

theorem radial_identity_of_spectral_data : RDRadIdOfSpec :=
  rDRadIdOfSpec_of_grpId_theta
    (rDGrpIdOfSpec_of_radIdAlg (rDRadIdAlg_of_collapse_gauge_rearr radial_collapse radial_gauge_identity radial_rearrangement)
      radial_start_coordinates radial_wave_radial Formalism.FourierDecayAlt.P5.waveCExists radial_residue_formula radial_wave_function_field radial_operator_function_field radial_group_residue)
    (Formalism.FourierDecayAlt.P.CutMP.JA.LT.thetaJ_of_adjComm Formalism.FourierDecayAlt.P.CutMP.JA.FFS.adjoint_commutation_holds)
    radial_orbital_niceness radial_wave_orbital radial_operator_locality

theorem radDecay_of_spec (h : RDIdentSpec) : RadDecay :=
  radDecay_of_ABQ (rDIdentABQ_of_spec h radial_identity_of_spectral_data)

end Formalism.FourierDecayAlt.P.CutSE
