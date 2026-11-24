module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.OmHeightslockG
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelFrameHeightComparison
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder


theorem _root_.GlobalTheory.T.flagModel_frame_height_comparison : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (M : FlagModel y (CMType H) (D.p + D.q) D.p) (𝔐 : HodgeCpt Y S M.x) (tie : FlagTie M 𝔐), ∀ (F : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk), M.IsFrame F → ∀ (τ : CMType H) (w : (Σ k, baseIdx ι M.blk k) → ℂ) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X), CoordsAt 𝔐.ξ M.x z w → 𝔐.Interior z → M.GoodAt F (mCoordIdeal w) → 𝔐.M.GramAt 𝔐.t.PP.L z (gb tie F τ) (HodgeMetric.gramFn 𝔐 (gb tie F τ) w) ∧ (HodgeMetric.gramFn 𝔐 (gb tie F τ) w).PosDef ∧ ∀ a b, tie.omFrame F τ a (dualFam tie F τ b) = if a = b then 1 else 0 := by
  first | exact @GlobalTheory.CompanionTheory.Relay.flagModel_frame_height_comparison | exact GlobalTheory.CompanionTheory.Relay.flagModel_frame_height_comparison | (intros; apply GlobalTheory.CompanionTheory.Relay.flagModel_frame_height_comparison <;> assumption)
