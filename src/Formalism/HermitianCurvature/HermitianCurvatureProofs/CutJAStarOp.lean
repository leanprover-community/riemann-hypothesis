module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAStarOp2
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactSupportInClassGeneral
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAFFStable
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASAPairLACSmooth
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASAPairLAsm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASAPairLExhAll
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASAPairLJCommC
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASAPairLLocal
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAStarOpOfPair
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

namespace Formalism.FourierDecayAlt.P.CutMP.JA

theorem self_adjoint_pairing_list_holds : SA.SAPairL :=
  SA.sAPairL_of_parts smooth_forms_stability_holds SA.self_adjoint_locality_holds (SA.sAExh_of_smooth SA.averaging_smoothness_holds) SA.self_adjoint_commutation_compact
    SA.compact_support_lemma_three

theorem star_operator_transfer_holds : JAStarOp := jAStarOp_of_pairL self_adjoint_pairing_list_holds

end Formalism.FourierDecayAlt.P.CutMP.JA
