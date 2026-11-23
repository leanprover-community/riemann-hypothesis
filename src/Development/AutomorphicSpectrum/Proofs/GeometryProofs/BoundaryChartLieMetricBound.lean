module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.QuotientUniformizationLower
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
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbBound

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.QuotUnif Metric

-- Some dependency stubs refer to this doubly qualified name when unfolding `LieModel.Lifts`.
-- Keep it definitionally equal to the actual map.
abbrev GlobalTheory.CompanionTheory.Ar.GlobalTheory.CompanionTheory.Ar.dualMap
    {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') :
    DualNumber R →+* DualNumber R' :=
  _root_.GlobalTheory.CompanionTheory.Ar.dualMap φ

theorem GlobalTheory.CompanionTheory.Ar.QuotUnif.chart_coords_le_metric : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (n a : ℕ) (C : Flat.BdryChart Xo σ n a) (X : Scheme.{0}) (t : SAB H X) (jj : Sp C.R ⟶ X) (m : SABMap C.t t jj) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (K : Type) (J : K → Type) (y : (Σ k, J k) → Ω) (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel t.G ξ Li) (h : LieMetric M y) (N : ℕ) (s : Fin N → Li) (sc : Fin N → Fin C.g → C.R) (ww : (Fin n → ℂ) → (Σ k, J k) → ℂ), ContinuousOn ww (ball 0 1) → (∀ u ∈ ball (0 : Fin n → ℂ) 1, ∃ Mz : LieModel C.t.G (spMap (C.ψ u)) (Fin C.g → ℂ), ∀ e : Fin C.g → C.R, ((Mz.pt fun i => C.ψ u (e i)).left ≫ (𝟙 _) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (_root_.GlobalTheory.CompanionTheory.Ar.dualMap (C.ψ u)) ≫ (C.M.pt e).left)) → (∀ u ∈ ball (0 : Fin n → ℂ) 1, CoordsAt ξ y (spMap (C.ψ u) ≫ jj) (ww u)) → (∀ u ∈ ball (0 : Fin n → ℂ) 1, ∀ i, ∃ v : epsAt (spMap (C.ψ u) ≫ jj) ⟶ t.G, M.ValAt (spMap (C.ψ u) ≫ jj) (s i) v ∧ v.left = spMap (_root_.GlobalTheory.CompanionTheory.Ar.dualMap (C.ψ u)) ≫ (C.M.pt (sc i)).left ≫ m.φ) → (∀ (V : Type) [AddCommGroup V] [Module ℂ V] (Mz : LieModel t.G (spMap (C.ψ 0) ≫ jj) V) (b : Fin N → V), (∀ i, M.ValAt (spMap (C.ψ 0) ≫ jj) (s i) (Mz.pt (b i))) → LinearIndependent ℂ b ∧ Submodule.span ℂ (Set.range b) = ⊤) → ∃ ρ Kc : ℝ, 0 < ρ ∧ 0 < Kc ∧ ∀ u ∈ ball (0 : Fin n → ℂ) ρ, ∀ Mz : LieModel C.t.G (spMap (C.ψ u)) (Fin C.g → ℂ), (∀ e : Fin C.g → C.R, ((Mz.pt fun i => C.ψ u (e i)).left ≫ (𝟙 _) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (_root_.GlobalTheory.CompanionTheory.Ar.dualMap (C.ψ u)) ≫ (C.M.pt e).left)) → ∀ (x : Fin C.g → ℂ) (v₀ : epsAt (spMap (C.ψ u) ≫ jj) ⟶ t.G), (Mz.pt x).left ≫ m.φ = v₀.left → ∑ i, ‖x i‖ ^ 2 ≤ Kc * (h.ip (spMap (C.ψ u) ≫ jj) v₀ v₀).re :=
  @PositivityTheory.Xgn.quotient_uniformization_lower
