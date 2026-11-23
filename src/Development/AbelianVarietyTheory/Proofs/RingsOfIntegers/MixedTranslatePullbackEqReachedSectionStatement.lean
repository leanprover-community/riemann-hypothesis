module

public import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.MixedTranslatePullbackEqReachedSection
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

theorem _root_.GlobalTheory.T.mixed_translate_pullback_eq_reached_section : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (N n' A Bn : ℕ) (α β : 𝓞 E), Odd N → (N : 𝓞 E) = β * α * n' → α * H.bar α = (A : 𝓞 E) → β * H.bar β = (Bn : 𝓞 E) → ∀ (s : SecN Xo x 1) (x₁ x₂ : (ptO Xo x ⟶ Xo.univ.t.G)) (F), x₁ ^ (N ^ 2) = 1 → x₂ ^ (N ^ 2) = 1 → (x₁ ≫ Xo.univ.t.act.act (α * β)) ^ (n' ^ 2) = 1 → (x₂ ≫ Xo.univ.t.act.act β) ^ (n' ^ 2 * A) = 1 → IsUUOver Xo.univ.t.G Xo.univ.t.PP N s x₁ x₂ F → N ^ 2 = n' ^ 2 * A * Bn ∧ ∃ hh : SecN Xo x (n' ^ 2 * A), Reach Xo s (n' ^ 2 * A) hh ∧ Pulls Xo β hh (sqN Xo N F) := by
  first | exact @GlobalTheory.PlaceInt.uu_eq_pull_reach | exact GlobalTheory.PlaceInt.uu_eq_pull_reach | (intros; apply GlobalTheory.PlaceInt.uu_eq_pull_reach <;> assumption)
