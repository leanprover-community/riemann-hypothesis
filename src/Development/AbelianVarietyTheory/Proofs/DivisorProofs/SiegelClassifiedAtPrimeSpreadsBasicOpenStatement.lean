module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelClassifiedAtPrimeSpreadsBasicOpen
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
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.siegelClassified_at_prime_spreads_basicOpen : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n), ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (β : cycAway n →+* R) (c : SiegPre g n (zetaAway n) (spMap β)) (𝔭 : Ideal R) [𝔭.IsPrime], c.Principal → (∀ c' : SiegPre g n (zetaAway n) (spMap ((algebraMap R (Localization.AtPrime 𝔭)).comp β)), SiegPB c' c (spMap (algebraMap R (Localization.AtPrime 𝔭))) → ∃ f : Sp (Localization.AtPrime 𝔭) ⟶ F.X, f ≫ F.s = spMap ((algebraMap R (Localization.AtPrime 𝔭)).comp β) ∧ SiegPB c' F.univ f) → ∃ r ∉ 𝔭, ∀ c' : SiegPre g n (zetaAway n) (spMap ((algebraMap R (Localization.Away r)).comp β)), SiegPB c' c (spMap (algebraMap R (Localization.Away r))) → ∃ f : Sp (Localization.Away r) ⟶ F.X, f ≫ F.s = spMap ((algebraMap R (Localization.Away r)).comp β) ∧ SiegPB c' F.univ f := by
  first | exact @GlobalTheory.SiegSpread.classified_basicOpen | exact GlobalTheory.SiegSpread.classified_basicOpen | (intros; apply GlobalTheory.SiegSpread.classified_basicOpen <;> assumption)
