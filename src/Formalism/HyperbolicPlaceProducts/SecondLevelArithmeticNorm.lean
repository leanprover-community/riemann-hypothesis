module

public import Formalism.HyperbolicPlaceProducts.Statement
public import Formalism.HyperbolicPlaceProducts.SubgroupIndexCounts.CardEqCardRangeNsmulMulCardKer
import Formalism.HyperbolicPlaceProducts.SubgroupIndexCounts.CountO
public import Formalism.HyperbolicPlaceProducts.SubgroupIndexCounts.DedekindLFunctions
import Formalism.HyperbolicPlaceProducts.SubgroupIndexCounts.OmegaPow
public import Formalism.HyperbolicPlaceProducts.SubgroupIndexCounts.SesquilinearDeterminantHolds
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

namespace Formalism.SLP.Final

theorem torsionIndex : Formalism.SLP.TorsionIndex := Formalism.SLP.P.card_range_nsmul_mul_card_le
theorem sesqDet : Formalism.SLP.SesqDet := Formalism.SLP.P.sesquilinear_determinant_holds
theorem omegaPow : Formalism.SLP.OmegaPow := Formalism.SLP.P.pow_primeFactors_length_le
theorem submoduleIndexCountO : Formalism.SLP.SubmoduleIndexCountO := Formalism.SLP.P.card_submodules_of_index_le
theorem submoduleCountDed : Formalism.SLP.SubmoduleCountDed := Formalism.SLP.P.card_submodules_le_of_dedekind

end Formalism.SLP.Final
