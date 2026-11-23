module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLatBasisZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFramedChartExponentialToroidalModel
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_framedChart_exponential_toroidalModel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (σ : c.F →+* ℂ) (x₀ : CxPts (genStr T.Z) σ), ∃ (n a g r₀ : ℕ) (e : OpenPartialHomeomorph (CxPts (genStr T.Z) σ) (Fin n → ℂ)) (ex : ExpMaps T.Z σ g) (ζ : (Fin n → ℂ) → Fin r₀ → Fin g → ℂ), x₀ ∈ e.source ∧ e x₀ = 0 ∧ IsExpChart e ex ∧ (∀ x ∈ e.source, Inner x ↔ ∀ k : Fin n, (k : ℕ) < a → e x k ≠ 0) ∧ Function.Surjective (ex x₀) ∧ AnalyticOnNhd ℂ ζ (Metric.ball 0 1) ∧ (∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, LinearIndependent ℝ (ζ z)) ∧ (∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ∀ i, ex (e.symm z) (ζ z i) = 1) ∧ IsLatBasis {w | ex x₀ w = 1} (ζ 0) ∧ (∃ C : ℝ, ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ‖ζ z‖ ≤ C) ∧ ∀ j : Fin g, ∃ i, ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ζ z i = Pi.single j 1 := by
  first | exact @GlobalTheory.ShFam.Hor.LogCh.exists_framed_chart | exact GlobalTheory.ShFam.Hor.LogCh.exists_framed_chart | (intros; apply GlobalTheory.ShFam.Hor.LogCh.exists_framed_chart <;> assumption)
