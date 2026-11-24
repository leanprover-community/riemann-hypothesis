module

public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.NefRR
public import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.OverLaUnique
public import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CInfGood
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianCmCompLawsBound
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

theorem _root_.GlobalTheory.T.abelian_cm_comp_laws_bound : GlobalTheory.CompanionTheory.Ar.Pub.NefRR → GlobalTheory.CompanionTheory.Ar.Top.Given → ArithIntersectionSystemStatement → BirationalPullbackPushforwardFormula → GlobalTheory.CompanionTheory.Ar.Top.GoodTowerExistsX → GlobalTheory.CompanionTheory.Ar.Top.VolumeTheoremX → ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → Ref.UnifAll Xo c → FnAlgClosed (Xo := Xo) (c := c) → (∀ p : ℕ, p.Prime → l.GoodAt p) → l.A = 1 → 1 ≤ Dw.q → 3 * Dw.q + 1 ≤ Dw.p + Dw.q → 2 ≤ Fintype.card (CMType H) → (Nat.primeFactors (2 * (discr E).natAbs) ∪ l.M'.primeFactors).card ≤ 4 * Fintype.card (CMType H) * (Dw.p + Dw.q) ^ 2 → ∀ x : ℝ, (∀ σ, GoodEmb c σ → ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = x) → GlobalTheory.CovHt.MeanAll U x (Real.log (hostRd E) + |hostLval H|) C := by
  exact GlobalTheory.CompanionTheory.Ar.Plug.top_meanAll
