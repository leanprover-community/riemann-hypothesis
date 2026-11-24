module

public import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
public import Formalism.HermitianCurvature.HeisenbergConjugationMeasurePreserving
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsAuxiliaryXi
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LemmaBOfComponents
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace Formalism.FourierDecayAlt.P.BXiAsm
open Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem closed_of (hX : XiExists) : LemmaBClosed := Formalism.FourierDecayAlt.P.b_lemmaBClosed_of hX

theorem norm_of (hX : XiExists) : LemmaBNorm :=
  Formalism.FourierDecayAlt.Final.lemma_b_norm_of_parts (closed_of hX) Formalism.FourierDecayAlt.Final.conjugation_invariance_all Formalism.FourierDecayAlt.Final.dilation_jacobian_all
    Formalism.FourierDecayAlt.Final.integral_bound_all

theorem any_of (hX : XiExists) : LemmaBAny :=
  Formalism.FourierDecayAlt.Final.lemma_b_from_norm_bound (norm_of hX) Formalism.FourierDecayAlt.Final.integral_norm_bound_variant_b

end Formalism.FourierDecayAlt.P.BXiAsm

namespace Formalism.FourierDecayAlt.P

theorem b_any_of_xi : Formalism.FourierDecayAlt.B2.LemmaBAny := Formalism.FourierDecayAlt.P.BXiAsm.any_of exists_auxiliary_xi

end Formalism.FourierDecayAlt.P
