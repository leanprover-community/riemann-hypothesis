module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.OneLeftSpMap
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DerivationVanishingConstants
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

theorem _root_.GlobalTheory.T.derivation_vanishing_constants : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] (g : ℕ) (M : LieModel G (𝟙 (Sp R)) (Fin g → R)) (φ : R →+* ℂ), Smooth G.hom → ∀ (V : G.left.Opens), IsAffineOpen V → ⊤ ≤ (1 : Over.mk (spMap φ) ⟶ G).left ⁻¹ᵁ V →
  ∀ D : Γ(G.left, V) →+ ℂ, (∀ r, D (GlobalTheory.CompanionTheory.Ar.Flat.ExpChart.cst G.hom V r) = 0) →
    (∀ f f', D (f * f') = valAt' (1 : Over.mk (spMap φ) ⟶ G).left V f * D f' + valAt' (1 : Over.mk (spMap φ) ⟶ G).left V f' * D f) →
    ∃! c : Fin g → ℂ, ∀ f, D f = ∑ a, c a * TrivSqZeroExt.snd (valR (spMap (dualMap φ) ≫ (M.pt (Pi.single a 1)).left) V f) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.ExpChart.lie_der_basis | exact GlobalTheory.CompanionTheory.Ar.Flat.ExpChart.lie_der_basis | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.ExpChart.lie_der_basis <;> assumption)
