module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.JDomBoundOfNnMaj
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDomainMeasurable
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.JConvOfJDom
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

noncomputable section

namespace Formalism.FourierDecayAlt.P

theorem jf_jDom_of_nnMaj : Formalism.FourierDecayAlt.P.JFxDs2.NNMaj → Formalism.FourierDecayAlt.JF.JDom := fun h =>
  Formalism.FourierDecayAlt.P.JFxDs2.jDom_of_parts Formalism.FourierDecayAlt.P.JFxDs3.bessel_domain_measurable (Formalism.FourierDecayAlt.P.JFxDs2.jDomBound_of_nnMaj h)

theorem jf_jConv_of_nnMaj : Formalism.FourierDecayAlt.P.JFxDs2.NNMaj → Formalism.FourierDecayAlt.JF.JConv := fun h =>
  Formalism.FourierDecayAlt.P.JFxDs1.jConv_of_jDom (jf_jDom_of_nnMaj h)

end Formalism.FourierDecayAlt.P
