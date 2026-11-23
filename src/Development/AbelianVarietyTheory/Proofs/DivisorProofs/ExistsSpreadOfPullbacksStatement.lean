module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpreadOfPullbacks
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_spread_of_pullbacks_alt : ∀ (g n : ℕ) (B : Type) [CommRing B] (ζ : B) (R : Type) [CommRing R] [IsNoetherianRing R] (β : B →+* R) (𝔭 : Ideal R) [𝔭.IsPrime] (d : SiegPre g n ζ (spMap β)) (Y : Scheme.{0}) (sY : Y ⟶ Sp B) [LocallyOfFinitePresentation sY] (u : SiegPre g n ζ sY) (r₀ : R) (ι₀ : Localization.Away r₀ →+* Localization.AtPrime 𝔭) (h : Sp (Localization.Away r₀) ⟶ Y) (e : SiegPre g n ζ (spMap ((algebraMap R (Localization.AtPrime 𝔭)).comp β))), r₀ ∉ 𝔭 → ι₀.comp (algebraMap R (Localization.Away r₀)) = algebraMap R (Localization.AtPrime 𝔭) → h ≫ sY = spMap ((algebraMap R (Localization.Away r₀)).comp β) → SiegPB e d (spMap (algebraMap R (Localization.AtPrime 𝔭))) → SiegPB e u (spMap ι₀ ≫ h) → ∃ r ∉ 𝔭, ∃ (κ : Localization.Away r₀ →+* Localization.Away r) (d' : SiegPre g n ζ (spMap ((algebraMap R (Localization.Away r)).comp β))), κ.comp (algebraMap R (Localization.Away r₀)) = algebraMap R (Localization.Away r) ∧ SiegPB d' d (spMap (algebraMap R (Localization.Away r))) ∧ SiegPB d' u (spMap κ ≫ h) := by
  first | exact @GlobalTheory.SiegelSpreadLocal.exists_spread_of_pullbacks | exact GlobalTheory.SiegelSpreadLocal.exists_spread_of_pullbacks | (intros; apply GlobalTheory.SiegelSpreadLocal.exists_spread_of_pullbacks <;> assumption)
