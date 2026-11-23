module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnCut
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnAdmLen
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnAsm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnBesselFold
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnBetaFrame
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnCVInCC
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnFoldRev
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.L2BoundAtBuiltPlaceHolds
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

namespace Formalism.FourierDecayAlt.P.CutMP

theorem En.bessel_folding_at_built_place : En.BesselFoldBuilt := En.besselFoldBuilt_of En.coefficient_vector_in_L2_class

theorem energyTr_of_betaFrame (h : En.BetaFrame) : EnergyTr :=
  En.energyTr_of_parts En.folding_reversal_holds En.admissible_length_holds En.bessel_folding_at_built_place En.L2_bound_at_built_place_holds h

theorem energy_trace_identity_holds : EnergyTr := energyTr_of_betaFrame En.beta_frame_identity_holds

end Formalism.FourierDecayAlt.P.CutMP
