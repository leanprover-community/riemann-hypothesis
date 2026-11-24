module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsLocSec
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.TwistedChartTransitionAnalytic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsBlkCover

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

theorem _root_.GlobalTheory.T.twisted_chart_transition_analytic : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a : Fin N) (k₀ : K) (ca cb : Fin N) (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (pr : RW.X → Rb.X) (x x' : RW.X) (ψ ψ' : OpenPartialHomeomorph RW.X (Fin e → ℂ)) (kb kb' : Fin Rb.A.n) (σ σ' : Fin n ↪ Fin e) (i₀ i₀' : Fin e) (V V' : Set RW.X) (u u' : RW.X → ℂ), M.blk (τ, a) = some k₀ → IsWAtlas M Rb τ a k₀ ca cb RW pr → IsLocSec M Rb τ a k₀ ca cb RW pr x ψ kb σ i₀ V u → IsLocSec M Rb τ a k₀ ca cb RW pr x' ψ' kb' σ' i₀' V' u' → ∀ w ∈ V ∩ V', ‖u w * ψ w i₀‖ / (potA M τ a k₀).h (RW.lift x w) = ‖u' w * ψ' w i₀'‖ / (potA M τ a k₀).h (RW.lift x' w) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.locSec_norm_eq | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.locSec_norm_eq | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.locSec_norm_eq <;> assumption)
