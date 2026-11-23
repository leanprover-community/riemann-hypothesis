module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GroupPointsEquivCommonCover
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
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsGenOfIsVBOne
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LieModel

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

theorem _root_.GlobalTheory.T.group_points_equiv_common_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S₁ S₂ V : Scheme.{0}) (t₁ : SAB H S₁) (t₂ : SAB H S₂) (tV : SAB H V) (f₁ : V ⟶ S₁) (f₂ : V ⟶ S₂) (m₁ : SABMap tV t₁ f₁) (m₂ : SABMap tV t₂ f₂) (x : Sp ℂ ⟶ V) (y₁ : Sp ℂ ⟶ S₁) (y₂ : Sp ℂ ⟶ S₂), x ≫ f₁ = y₁ → x ≫ f₂ = y₂ → ∃ Φ : (Over.mk y₂ ⟶ t₂.G) ≃ (Over.mk y₁ ⟶ t₁.G), (∀ q q', Φ (q * q') = Φ q * Φ q') ∧ (∀ q, ∃ w : Sp ℂ ⟶ tV.G.left, w ≫ tV.G.hom = x ∧ w ≫ m₂.φ = q.left ∧ w ≫ m₁.φ = (Φ q).left) ∧ ∀ (N : ℕ) (q q' : Over.mk y₂ ⟶ t₂.G) (ζ : (Γ(Sp ℂ, ⊤))ˣ), GlobalTheory.UU.CubWeil t₁.cub N (Φ q) (Φ q') ζ → GlobalTheory.UU.CubWeil t₂.cub N q q' ζ := by
  exact @GlobalTheory.CompanionTheory.Ar.MarkFibre.exists_fibre_equiv
