module

public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.NefRR
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ModelSmall
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FullIntersectionHeightBound
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

theorem _root_.GlobalTheory.T.full_intersection_height_bound : GlobalTheory.CompanionTheory.Ar.Pub.NefRR → Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (Dw.p + Dw.q)) (o : Top.GoodOrigin Y T) (B : ℕ) (b : T.Comp) (II : IntersectionSystem) (u : GlobalTheory.AllWt.Weight Dw) (g : ℝ), IsFullIntersectionSystem II → T.T1 II → Top.WeightHyp T.j (reW u) g → Top.bigB0 (reW u) g < B + 1 → ∀ ε : ℝ, 0 < ε → ∃ᶠ τ : ℕ in atTop, ∃ (n : ℕ) (f : Fin n → (T.M B b).Ω), LinearIndependent ℤ f ∧ (∀ i, ∃ R, f i ∈ modelSmall (o.toTowerOrigin.Or B b) (τ • u) R) ∧ ((T.M B b).δ * (T.vol b * Top.flagDeg (reW u)) - ε) * (τ : ℝ) ^ (Top.dimFl (CMType H) (Dw.p + Dw.q)) ≤ ((Top.dimFl (CMType H) (Dw.p + Dw.q)).factorial : ℝ) * n := by
  exact @GlobalTheory.CompanionTheory.Ar.Plug.many_sections
