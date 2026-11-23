module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalBoundaryMetricData
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraicEigenvectorCoordinatesHolomorphicUnifor
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.LieBase
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts
open scoped Topology
open ReciprocityTheory.L2DbarEstimates (V)


theorem _root_.GlobalTheory.T.algebraic_eigenvector_coordinates_holomorphic_uniformisation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (d : ℕ) (u₀ : V d) (R : Type) [CommRing R] (φR : c.F →+* R) (xR : Sp R ⟶ Z.X) (fR : EigFrame Z φR xR) (ev : V d → (R →+* ℂ)) (k : U.Comp) (G : V d → ReciprocityTheory.ChartRestriction.G.FD.Frame (U.X k).Ψ (Dw.p + Dw.q)) (τ : E →+* ℂ), (∀ t, ∀ᶠ u in 𝓝 u₀, DifferentiableAt ℂ (fun u => ev u t) u) → (∀ τ' a b, ∀ᶠ u in 𝓝 u₀, DifferentiableAt ℂ (fun u => ReciprocityTheory.ChartRestriction.G.FD.mat (G u) τ' a b) u) → (∀ᶠ u in 𝓝 u₀, (ev u).comp φR = σ) → (∀ᶠ u in 𝓝 u₀, ∃ h : G u ∈ (U.X k).dom, (cxPt Z (U.un k ⟨G u, h⟩)).1 ≫ genι Z = spMap (ev u) ≫ xR) → ∃ M : V d → Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ, (∀ a b, ∀ᶠ u in 𝓝 u₀, DifferentiableAt ℂ (fun u => M u a b) u) ∧ ∀ᶠ u in 𝓝 u₀, ∃ h : G u ∈ (U.X k).dom, ∀ i, IsCombAtG Z.t ((cxPt Z (U.un k ⟨G u, h⟩)).1 ≫ genι Z) ((cxFrame Z (U.un k ⟨G u, h⟩)).v τ) (fun b => M u b i) (spMap (Formalism.L2.Pj.dualMap (ev u)) ≫ fR.v τ i) := by
  exact GlobalTheory.HolCoordEv.coords_holomorphic
