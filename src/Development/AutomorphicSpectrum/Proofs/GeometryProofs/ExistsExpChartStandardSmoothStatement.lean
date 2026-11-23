module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.OneLeftSpMap
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsExpChartStandardSmooth
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.NormNum.Prime
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExponentialFamilyPeriods
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeGram

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

theorem _root_.GlobalTheory.T.exists_exp_chart_standard_smooth : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] (g : ℕ) (M : LieModel G (𝟙 (Sp R)) (Fin g → R)) (φ : R →+* ℂ), Smooth G.hom →
  ∃ (V : G.left.Opens) (t : Fin g → Γ(G.left, V)) (ρ : R), IsAffineOpen V ∧ φ ρ ≠ 0 ∧ (GlobalTheory.CompanionTheory.Ar.Flat.ExpChart.cst G.hom V).IsStandardSmooth ∧
    (∀ θ : R →+* ℂ, θ ρ ≠ 0 → ⊤ ≤ (1 : Over.mk (spMap θ) ⟶ G).left ⁻¹ᵁ V ∧ (∀ c, valAt' (1 : Over.mk (spMap θ) ⟶ G).left V (t c) = 0) ∧
      ∀ a c, TrivSqZeroExt.snd (valR (spMap (dualMap θ) ≫ (M.pt (Pi.single a 1)).left) V (t c)) = if a = c then 1 else 0) ∧
    ∀ f : Γ(G.left, V), ∃ (u : R) (k : ℕ), ∀ θ : R →+* ℂ, θ ρ ≠ 0 → valAt' (1 : Over.mk (spMap θ) ⟶ G).left V f * θ ρ ^ k = θ u := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.ExpChart.Coords.exists_coords | exact GlobalTheory.CompanionTheory.Ar.Flat.ExpChart.Coords.exists_coords | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.ExpChart.Coords.exists_coords <;> assumption)
