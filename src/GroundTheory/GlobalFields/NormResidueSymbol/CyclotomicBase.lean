module

public import GroundTheory.GlobalFields.NormResidueSymbol.RangeIdeleNormLeKerIdeleSymbol
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar

@[expose] public section

namespace GroundTheory.Global

open IsDedekindDomain NumberField IdeleGroup IntermediateField

noncomputable section

namespace CyclotomicSymbol

section Roots

variable {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)]

end Roots

section Sub

variable {K : Type*} [Field K] [NumberField K] (L M : Type*) [Field L] [NumberField L] [Field M]
  [NumberField M] [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
  [IsGalois K L] [IsGalois K M] [IsMulCommutative (L ≃ₐ[K] L)] [IsMulCommutative (M ≃ₐ[K] M)]

end Sub

section ClassSymbol

variable {K : Type*} [Field K] [NumberField K] (L : Type*) [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)]

def ideleClassSymbol (h : (diagonal K).range ≤ (ideleSymbol K L).ker) :
    IdeleClassGroup K →* (L ≃ₐ[K] L) :=
  QuotientGroup.lift _ (ideleSymbol K L) h

variable {L}

@[simp]
theorem ideleClassSymbol_mk (h : (diagonal K).range ≤ (ideleSymbol K L).ker) (x : IdeleGroup K) :
    ideleClassSymbol L h (IdeleClassGroup.mk K x) = ideleSymbol K L x :=
  rfl

theorem continuous_ideleClassSymbol (h : (diagonal K).range ≤ (ideleSymbol K L).ker) :
    Continuous (ideleClassSymbol L h) :=
  (QuotientGroup.isQuotientMap_mk _).continuous_iff.2 (continuous_ideleSymbol L)

end ClassSymbol

universe u

end CyclotomicSymbol

end

end GroundTheory.Global
