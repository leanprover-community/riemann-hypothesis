module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultOfNotMem
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricGramHolomorphicFrameForm
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
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix


theorem _root_.GlobalTheory.T.hodgeMetric_gram_holomorphic_frame_form : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ k' : U.Comp, ∃ (G : ReciprocityTheory.ChartRestriction.G.FD.Frame (U.X k').Ψ (Dw.p + Dw.q) → Mat Dw.mult ℂ) (z : ReciprocityTheory.ChartRestriction.G.FD.Frame (U.X k').Ψ (Dw.p + Dw.q) → GlobalTheory.AllWt.Psi H → Matrix (Fin Dw.p) (Fin Dw.q) ℂ) (cc : (E →+* ℂ) → ℝ), (∀ τ, 0 < cc τ) ∧ ∀ (x : ReciprocityTheory.ChartRestriction.G.FD.Frame (U.X k').Ψ (Dw.p + Dw.q)) (hx : x ∈ (U.X k').dom), (∀ τ a b, AnalyticAt ℂ (fun x' => G x' τ a b) x) ∧ (∀ τ a b, AnalyticAt ℂ (fun x' => z x' τ a b) x) ∧ (∀ τ, IsUnit (G x τ).det) ∧ InDom (z x) ∧ ∀ τ, ((hodgeMet Z U).gram (cxPt Z (U.un k' ⟨x, hx⟩)) (cxFrame Z (U.un k' ⟨x, hx⟩)) τ)ᵀ = (cc τ : ℂ) • (G x τ * modelGram H Dw (z x) τ * (G x τ)ᴴ) := by
  first | exact @GlobalTheory.HodgeGramGen.hodge_gram_frame | exact GlobalTheory.HodgeGramGen.hodge_gram_frame | (intros; apply GlobalTheory.HodgeGramGen.hodge_gram_frame <;> assumption)
