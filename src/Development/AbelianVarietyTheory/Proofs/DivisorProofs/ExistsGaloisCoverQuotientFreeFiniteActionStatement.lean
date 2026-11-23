module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisCoverQuotientFreeFiniteAction
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
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_galoisCover_quotient_freeFiniteAction : ∀ (K : Type) [CommRing K] [IsNoetherianRing K] (X : Scheme.{0}) (s : X ⟶ Sp K) (Ga : Type) [Group Ga] [Finite Ga] (ρ : Ga → (X ⟶ X)), IsQProjOver s → ρ 1 = 𝟙 X → (∀ a c, ρ (a * c) = ρ a ≫ ρ c) → (∀ a, ρ a ≫ s = s) → (∀ (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ X) (a : Ga), y ≫ ρ a = y → a = 1) → ∃ (Y : Scheme.{0}) (π : X ⟶ Y) (sY : Y ⟶ Sp K), π ≫ sY = s ∧ IsGaloisCover Ga ρ π ∧ IsSeparated sY ∧ LocallyOfFiniteType sY ∧ QuasiCompact sY := by
  first | exact @GlobalTheory.ZM.exists_isGaloisCover_of_isQProjOver_noetherian | exact GlobalTheory.ZM.exists_isGaloisCover_of_isQProjOver_noetherian | (intros; apply GlobalTheory.ZM.exists_isGaloisCover_of_isQProjOver_noetherian <;> assumption)
