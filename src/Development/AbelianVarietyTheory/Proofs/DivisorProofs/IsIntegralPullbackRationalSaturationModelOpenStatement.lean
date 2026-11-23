module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRatPointOfFiniteType
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralPullbackRationalSaturationModelOpen
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Models GlobalTheory.UPoinc GlobalTheory.ZH

theorem _root_.GlobalTheory.T.isIntegral_pullback_rationalSaturation_model_open : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [CharZero Ω] (M : RatModel o Ω) (U₀ : M.Z.Opens) (R : Subalgebra o Ω) (u₀ : U₀.toScheme ⟶ Sp R), (U₀ : Set M.Z).Nonempty → (∀ x : Sp Ω ⟶ U₀.toScheme, x ≫ U₀.ι = M.pt → x ≫ u₀ = spMap R.val.toRingHom) → IsIntegral (pullback u₀ (spMap (toRat R))) ∧ ∃ pt : Sp Ω ⟶ pullback u₀ (spMap (toRat R)), pt ≫ pullback.fst _ _ ≫ U₀.ι = M.pt ∧ Dense (Set.range pt) := by
  first | exact @GlobalTheory.UPoinc.isIntegral_pullback_toRat | exact GlobalTheory.UPoinc.isIntegral_pullback_toRat | (intros; apply GlobalTheory.UPoinc.isIntegral_pullback_toRat <;> assumption)
