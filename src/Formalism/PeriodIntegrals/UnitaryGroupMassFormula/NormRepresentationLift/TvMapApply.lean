module

public import Formalism.LocalRingCardinality.DataSpaces
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
import Formalism.SharpRestriction.CuspSpanNormBounds.Point

@[expose] public section

noncomputable section

open scoped Classical

namespace PI.NRL

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E}

def tvMap (e v : S.V) (l : E) : S.V →ₗ[E] S.V :=
  LinearMap.id + (S.hT v).smulRight e - (S.hT e).smulRight v + l • (S.hT e).smulRight e

theorem tvMap_apply (e v : S.V) (l : E) (y : S.V) :
    tvMap e v l y = y + S.hT v y • e - S.hT e y • v + (l * S.hT e y) • e := by
  simp only [tvMap, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply,
    LinearMap.smulRight_apply, LinearMap.smul_apply, smul_smul]

theorem tvMap_comp (e v : S.V) (l μ : E) (hee : S.hT e e = 0) (hev : S.hT e v = 0)
    (hve : S.hT v e = 0) (y : S.V) :
    tvMap e (-v) μ (tvMap e v l y) = y + (S.hT e y * (l + S.hT v v + μ)) • e := by
  rw [tvMap_apply, tvMap_apply]
  simp only [map_add (f := _), map_sub, map_smul, map_neg, LinearMap.neg_apply, LinearMap.add_apply,
    LinearMap.sub_apply, LinearMap.smul_apply, hee, hev, hve, smul_eq_mul, mul_zero, add_zero,
    sub_zero, smul_zero]
  module

end PI.NRL
