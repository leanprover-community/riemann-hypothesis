module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrbitThickSt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.NonemptyGtAnOfToric
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArcsOnFlowLinesOfAnalyticModelOnOrbit
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory GlobalTheory.ArcQ GlobalTheory.ArcCM GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.CuspFrom
open scoped LaurentSeries

theorem _root_.GlobalTheory.T.arcs_on_flow_lines_of_analytic_model_on_orbit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r) (Uw : UnfWit U) (k : U.Comp) (ξ' : Fin r → E) (x : Frame (U.X k).Ψ r) (aC : ArcIn Dw l (RingHom.id c.F) ℂ σ) (Λ : GtAn₀ aC), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → (U.X k).IsIso ξ' → x ∈ (U.X k).dom → letI := H.starRing; ∀ (gam : (Uw.F.Di (Uw.ik k)).La ≃ₗ[𝓞 E] Λ.A.La) (ξ : Module.Dual ℤ Λ.A.X), OnOrbit Uw k ξ' x Λ.A gam ξ → ξ ≠ 0 → Module.finrank (𝓞 E) Λ.A.X = 1 → (∀ v, Λ.Lifts (aC.eta v) (gam (Uw.F.t (Uw.ik k) v))) → (∀ v, Λ.Lifts (aC.etaA v) (gam (Uw.F.t (Uw.ik k) v))) → ∀ (O : Type) [CommRing O] (β : O →+* c.F), FlowTie Uw (aC.restrict β) k ξ' x := by
  first | exact @GlobalTheory.CuspFrom.flowTie_of_onOrbit | exact GlobalTheory.CuspFrom.flowTie_of_onOrbit | (intros; apply GlobalTheory.CuspFrom.flowTie_of_onOrbit <;> assumption)
