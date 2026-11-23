module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.OmHeightslockG
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsLocalHoloIsPeriodGramBlockGBaseGram
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


theorem _root_.GlobalTheory.T.exists_local_holo_isPeriodGram_blockG_baseGram : Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (M : FlagModel y (CMType H) (D.p + D.q) D.p) (𝔐 : HodgeCpt Y S M.x) (tie : FlagTie M 𝔐), 1 ≤ D.p → 1 ≤ D.q → ∀ (n : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (s : Rb.X → Rb.X → ℂ), (∀ (x : Rb.X) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X), CoordsAt 𝔐.ξ M.x z (Rb.lift x x) → (x ∉ bdry s ↔ 𝔐.Interior z)) → IsClosed (bdry s) → ∀ (F : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk), M.IsFrame F → ∀ (τ : CMType H) (x : Rb.X), x ∉ bdry s → M.GoodAt F (mCoordIdeal (Rb.lift x x)) → ∃ (V : Set Rb.X) (P : Rb.X → Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) ℂ), IsOpen V ∧ x ∈ V ∧ (∀ a b, Rb.A.HoloOn V fun x' => P x' a b) ∧ ∀ x' ∈ V, IsPeriodGram D.p (P x') (blockG (baseGram tie F τ Rb x')) := by
  exact @GlobalTheory.CompanionTheory.Relay.exists_local_holo_isPeriodGram_blockG_baseGram
