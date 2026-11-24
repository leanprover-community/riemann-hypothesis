module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDIdentSpec
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSOpRGrpFinal
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSOpX
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSRhR
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSRhvR
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSETopR
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SpectralCompositionZero
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
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSOpR

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutSE

theorem spectral_operator_R : RDSOpR := rDSOpR_of_parts spectral_right_group_action spectral_operator_X spectral_right_rho_action spectral_composition_zero

theorem spectral_operator_R_adjoint : RDSOpRv := rDSOpRv_of_parts spectral_adjoint_right_group spectral_operator_X spectral_adjoint_rho_action spectral_composition_zero

theorem actual_compact_theorem : Formalism.FourierDecayAlt.P5.ThmPActualCpt := thmPActualCpt_of_R spectral_operator_R spectral_operator_R_adjoint

end Formalism.FourierDecayAlt.P.CutSE
