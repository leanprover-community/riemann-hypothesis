module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.QuotientUniformizationChartAt
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

namespace GlobalTheory.CompanionTheory.Ar.QuotUnif

theorem exists_chart_at_of_polydisc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (n a : ℕ) (w : (Fin n → ℂ) → (Σ k, J k) → ℂ) (N : ℕ) (s : Fin N → 𝔐.Li) (z₀ : Sp ℂ ⟶ 𝔐.X), a ≤ n → DifferentiableOn ℂ w (ball 0 1) → (∀ u ∈ ball (0 : Fin n → ℂ) 1, w u ∈ mcPts (mCoordIdeal y)) → (∀ u ∈ Flat.punct n a 1, ∀ z : Sp ℂ ⟶ 𝔐.X, CoordsAt 𝔐.ξ y z (w u) → 𝔐.Interior z) → CoordsAt 𝔐.ξ y z₀ (w 0) → (∀ i, ∃ v : epsAt z₀ ⟶ 𝔐.t.G, 𝔐.M.ValAt z₀ (s i) v) → ∃ (ρ : ℝ) (τ : c.F →+* ℂ) (C : Flat.BdryChart Xo (τ.comp (IntermediateField.inclusion c.le).toRingHom) n a) (jj : Sp C.R ⟶ 𝔐.X) (m : SABMap C.t 𝔐.t jj) (sc : Fin N → Fin C.g → C.R), 0 < ρ ∧ ρ ≤ 1 ∧ ∀ u ∈ ball (0 : Fin n → ℂ) 1, CoordsAt 𝔐.ξ y (spMap (C.ψ u) ≫ jj) (w ((ρ : ℂ) • u)) ∧ spMap (C.ψ u) ≫ jj ≫ 𝔐.f ≫ Y.s = spMap (τ.comp (algebraMap (𝓞 c.F) c.F)) ∧ ∀ i, ∃ v : epsAt (spMap (C.ψ u) ≫ jj) ⟶ 𝔐.t.G, 𝔐.M.ValAt (spMap (C.ψ u) ≫ jj) (s i) v ∧ v.left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap (C.ψ u)) ≫ (C.M.pt (sc i)).left ≫ m.φ := by
  exact @PositivityTheory.Xgn.quotient_uniformization_chart_at

end GlobalTheory.CompanionTheory.Ar.QuotUnif
