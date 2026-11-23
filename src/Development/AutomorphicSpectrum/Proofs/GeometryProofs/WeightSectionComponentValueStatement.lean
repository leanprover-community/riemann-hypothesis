module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProdZpowLe
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.WeightSectionComponentValue
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
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.DefiniteFormStabilizerFiniteAwayFromP
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ModelSmall

@[expose] public section

open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi


theorem _root_.GlobalTheory.T.weight_section_component_value : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → ∀ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Z : Comp Xo c) (u : GlobalTheory.AllWt.Weight Dw) (f : Rul Xo c), f ∈ GlobalTheory.AllWt.secZ Xo c (GlobalTheory.AllWt.exOf Dw u 0) → ∀ (B' : Finset (Om Z)) (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e₀ : ℕ), OverLa la T.V io e₀ → ∀ y : IntFr Xo c T io, y.IsAlg → (letI := io.toAlgebra; GlobalTheory.AllWt.LiesOn Z y.1) → evI y f ≠ 0 → ∃ (T' : CDVR) (io' : c.F →+* T'.Fr) (e' : ℕ) (y' : IntFr Xo c T' io') (A : Subring (Om Z)) (ev : A →+* T'.Fr), OverLa la T'.V io' e' ∧ y'.IsAlg ∧ nval T'.V e' (evI y' f) = nval T.V e₀ (evI y f) ∧ (↑B' : Set (Om Z)) ⊆ A ∧ (∀ b ∈ B', b ≠ 0 → b⁻¹ ∈ A) ∧ (∀ x, IsAlgebraic ℤ (ev x)) ∧ FinTr.RegAt h Z io' A ev y'.1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Plug.FinTr.Approx.approx_main | exact GlobalTheory.CompanionTheory.Ar.Plug.FinTr.Approx.approx_main | (intros; apply GlobalTheory.CompanionTheory.Ar.Plug.FinTr.Approx.approx_main <;> assumption)
