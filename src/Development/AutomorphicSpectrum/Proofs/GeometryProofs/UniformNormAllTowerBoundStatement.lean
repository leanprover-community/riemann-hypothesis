module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GeoRead
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ModelSmall
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.OverLaUnique
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.UniformNormAllTowerBound
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.DefiniteFormStabilizerFiniteAwayFromP

@[expose] public section

open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

theorem _root_.GlobalTheory.T.uniform_norm_all_tower_bound : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsGalois ℚ E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → Ref.UnifAll Xo c → ∀ x : ℝ, (∀ σ, GoodEmb c σ → ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = x) → ∀ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (Dw.p + Dw.q)) (o : Top.GoodOrigin Y T) (B : ℕ) (b : T.Comp) (Fr : Small.GenFrame (o.toTowerOrigin.Or B b)) (Z : Comp Xo c) (Rd : Reading Fr h Z) (_ : GeoRead Rd) (u : GlobalTheory.AllWt.Weight Dw) (R : ℝ), (∀ τ, StrictAnti (u τ)) → 0 ≤ R → ∀ s ∈ modelSmall (o.toTowerOrigin.Or B b) u R, ∃ f ∈ GlobalTheory.AllWt.cuspOn U Z (GlobalTheory.AllWt.wtOf Dw u 0), evC h Z f = trOf Rd u s ∧ (∀ σ, GoodEmb c σ → ∀ z ∈ GlobalTheory.AllWt.framesOn (U σ) Z, GlobalTheory.AllWt.homN (U σ) x (GlobalTheory.AllWt.wtOf Dw u 0) f z ≤ (o.toTowerOrigin.Or B b).Fl.deg * R) ∧ ∀ (p : ℕ) (la : HeightOneSpectrum (𝓞 c.F)), p.Prime → ((p : ℕ) : 𝓞 c.F) ∈ la.asIdeal → ∀ v ∈ (GlobalTheory.CompHt.recVals Xo c).1 la, ((-((vLa la (p : c.F) : ℝ) * (if p ∈ o.toTowerOrigin.S B then exTwo E p else 0) * GlobalTheory.CovHt.l1 u) : ℝ) : EReal) ≤ v f := by
  exact @GlobalTheory.CompanionTheory.Ar.Plug.descent_small
