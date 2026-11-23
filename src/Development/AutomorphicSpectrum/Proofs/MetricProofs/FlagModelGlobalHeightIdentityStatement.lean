module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.OmHeightslockG
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelGlobalHeightIdentity
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder


theorem _root_.GlobalTheory.T.flagModel_global_height_identity : Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (M : FlagModel y (CMType H) (D.p + D.q) D.p) (𝔐 : HodgeCpt Y S M.x) (tie : FlagTie M 𝔐), ∀ (n : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (L : LocPot Rb.X) (s : Rb.X → Rb.X → ℂ) (Bat : FinHolAtlas n Rb.X), IsPotential Rb.A L → IsSection Rb.A L s → (∀ p, logNormSec L s p ≤ 0) → IsAdaptedAtlas Rb.A Bat L s → (∀ (x : Rb.X) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X), CoordsAt 𝔐.ξ M.x z (Rb.lift x x) → (x ∉ bdry s ↔ 𝔐.Interior z)) → ∀ (F : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk), M.IsFrame F → ∀ (τ : CMType H) (k : Fin Bat.n) (w₀ : Fin n → ℂ), w₀ ∈ Metric.closedBall (0 : Fin n → ℂ) (3 / 2) → M.GoodAt F (mCoordIdeal (Rb.lift ((Bat.chart k).symm w₀) ((Bat.chart k).symm w₀))) → ∃ ε c C : ℝ, 0 < ε ∧ 0 < c ∧ 0 < C ∧ ∀ w : Fin n → ℂ, ‖w - w₀‖ < ε → (Bat.chart k).symm w ∉ bdry s → (baseGram tie F τ Rb ((Bat.chart k).symm w)).PosDef ∧ ((baseGram tie F τ Rb ((Bat.chart k).symm w))⁻¹ - (c : ℂ) • (1 : Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) ℂ)).PosSemidef ∧ (((C * rW L s ((Bat.chart k).symm w) : ℝ) : ℂ) • (1 : Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) ℂ) - (baseGram tie F τ Rb ((Bat.chart k).symm w))⁻¹).PosSemidef ∧ ∀ a b, ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w' => baseGram tie F τ Rb ((Bat.chart k).symm w') a b) w ∧ ‖fderiv ℝ (fun w' => baseGram tie F τ Rb ((Bat.chart k).symm w') a b) w‖ ≤ C * Real.exp (rW L s ((Bat.chart k).symm w) / 2) := by
  exact @GlobalTheory.CompanionTheory.Ar.PB.BMx.exists_gram_logBounds_noGlobal
