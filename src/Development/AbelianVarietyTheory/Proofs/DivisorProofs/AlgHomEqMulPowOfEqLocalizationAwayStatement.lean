module

public import Mathlib.GroupTheory.MonoidLocalization.Away
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.OreLocalization.Ring
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgHomEqMulPowOfEqLocalizationAway
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

@[expose] public section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.exists_pow_mul_eq_of_algebraMap_localizationAway_eq : ∀ (R' A S : Type) [CommRing R'] [CommRing A] [CommRing S] [Algebra R' A] [Algebra R' S]
    [Algebra.FiniteType R' A] (χ₁ χ₂ : A →ₐ[R'] S) (g : S),
    (∀ x, algebraMap S (Localization.Away g) (χ₁ x) = algebraMap S (Localization.Away g) (χ₂ x)) →
    ∃ N : ℕ, ∀ x, g ^ N * χ₁ x = g ^ N * χ₂ x := by
  first | exact @GlobalTheory.algHom_eq_mul_pow_of_eq_localizationAway | exact GlobalTheory.algHom_eq_mul_pow_of_eq_localizationAway | (intros; apply GlobalTheory.algHom_eq_mul_pow_of_eq_localizationAway <;> assumption)
