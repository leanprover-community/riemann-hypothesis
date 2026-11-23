module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgePeriodGram
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHodgeMetricPeriodChartAtBoundaryPoint
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

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology

theorem _root_.GlobalTheory.T.exists_hodgeMetric_periodChart_at_boundaryPoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (C : FlagCpt T.Z e), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : C.Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e C X j f f₀ Eb A₀ → ∀ y : GlobalTheory.CxPts X.str (σ.comp e.toRingHom), y ∉ GlobalTheory.CxPts.ptsIn X.str (σ.comp e.toRingHom) (openPart j) → ∃ (ch : OpenPartialHomeomorph (GlobalTheory.CxPts X.str (σ.comp e.toRingHom)) (ReciprocityTheory.L2DbarEstimates.V X.dim)) (a : ℕ) (ha : a ≤ X.dim) (g rk : ℕ) (τ₀ : (Fin X.dim → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ), GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.IsPeriodChart rk τ₀ B ∧ IsHoloChart ch ∧ y ∈ ch.source ∧ ch y = 0 ∧ (∀ z ∈ ch.source, (ch z).ofLp ∈ GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.polydisc X.dim 1) ∧ (∀ z ∈ ch.source, z ∉ GlobalTheory.CxPts.ptsIn X.str (σ.comp e.toRingHom) (openPart j) ↔ ∃ i : Fin a, ch z (Fin.castLE ha i) = 0) ∧ ∃ A ∈ Eb.S (GlobalTheory.Cartier.under y), ∃ Q : ∀ τ : E →+* ℂ, (Fin X.dim → ℂ) → Matrix (Fin (Dw.mult τ)) (Fin g) ℂ, (∀ τ i k, DifferentiableOn ℂ (fun w => Q τ w i k) (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.polydisc X.dim 1)) ∧ Fintype.card (Σ τ, Fin (Dw.mult τ)) = g ∧ LinearIndependent ℂ (fun p : Σ τ, Fin (Dw.mult τ) => Q p.1 0 p.2) ∧ (∀ z ∈ ch.source, z ∈ GlobalTheory.CxPts.ptsIn X.str (σ.comp e.toRingHom) (openPart j) → ∀ τ, lieGram e U hj f₀ A₀ A z τ = Q τ (ch z).ofLp * (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B (ch z).ofLp)⁻¹ * (Q τ (ch z).ofLp)ᴴ) ∧ (∀ z ∈ ch.source, z ∈ GlobalTheory.CxPts.ptsIn X.str (σ.comp e.toRingHom) (openPart j) → ∀ τ τ', τ ≠ τ' → Q τ (ch z).ofLp * (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B (ch z).ofLp)⁻¹ * (Q τ' (ch z).ofLp)ᴴ = 0) := by
  first | exact @GlobalTheory.LieBase.HodgeChart.exists_hodge_period_chart | exact GlobalTheory.LieBase.HodgeChart.exists_hodge_period_chart | (intros; apply GlobalTheory.LieBase.HodgeChart.exists_hodge_period_chart <;> assumption)
