module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameMinorValuation
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

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

theorem _root_.GlobalTheory.T.hodgeCpt_frame_minor_valuation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀) (bW : WBases 𝔐) (bO : OmBases 𝔐) (n m : CMType H ⊕ CMType H → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω (EE 𝔐)), FormsOK 𝔐 bW bO m φ → CoordTie ℤ 𝔐.ξ (seg (xb (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) → ∀ h : ModelOK (aOf 𝔐 bW bO φ) x₀ m, ∀ (q : Cpt 𝔐.ξ) (F : FrameData (idx (p := D.p) (q := D.q) J₀ n) (CMType H) (D.p + D.q) Ω (blkF (CMType H) D.p D.q K₀)), (model (aOf 𝔐 bW bO φ) x₀ m h).IsFrame F → (model (aOf 𝔐 bW bO φ) x₀ m h).GoodAt F (ptIdeal 𝔐.ξ (xb (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀) q) → ∀ τ, (𝔐.V (.inl τ)).IsFrameAt (colFrame (fun a => (bW τ a : 𝔐.Li)) (wBlock (F.T τ))) q ∧ (omBundle 𝔐 τ).IsFrameAt (colFrame (bO τ) (omBlock (F.T τ))) q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.FrameAt.isFrameAt_of_goodAt | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.FrameAt.isFrameAt_of_goodAt | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.FrameAt.isFrameAt_of_goodAt <;> assumption)
