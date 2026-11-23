module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAwaySpreadPointLocalizationAtPrime
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

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.exists_away_spread_point_localization_atPrime : ∀ (B : Type) [CommRing B] (X : Scheme.{0}) (q : X ⟶ Sp B) [LocallyOfFinitePresentation q] (R : Type) [CommRing R] (β : B →+* R) (𝔭 : Ideal R) [𝔭.IsPrime] (f₀ : Sp (Localization.AtPrime 𝔭) ⟶ X), f₀ ≫ q = spMap ((algebraMap R (Localization.AtPrime 𝔭)).comp β) → ∃ r ∉ 𝔭, ∃ (j : Localization.Away r →+* Localization.AtPrime 𝔭) (f : Sp (Localization.Away r) ⟶ X), j.comp (algebraMap R (Localization.Away r)) = algebraMap R (Localization.AtPrime 𝔭) ∧ f ≫ q = spMap ((algebraMap R (Localization.Away r)).comp β) ∧ spMap j ≫ f = f₀ := by
  first | exact @GlobalTheory.SpreadPoint.exists_away | exact GlobalTheory.SpreadPoint.exists_away | (intros; apply GlobalTheory.SpreadPoint.exists_away <;> assumption)
