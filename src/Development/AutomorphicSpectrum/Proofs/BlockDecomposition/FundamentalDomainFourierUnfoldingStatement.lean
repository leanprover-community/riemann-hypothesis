module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FundamentalDomainFourierUnfolding
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory

theorem _root_.GlobalTheory.T.fundamental_domain_fourier_unfolding : ∀ {A X Y : Type} [AddCommGroup A] [MeasurableSpace A] [MeasurableAdd A] (lam : Measure A) [lam.IsAddLeftInvariant] (Λ : AddSubgroup A) [Countable Λ] (𝓖 : Set A) (_ : IsAddFundamentalDomain Λ 𝓖 lam) (_ : lam 𝓖 = 1) [Countable X] (c : X → Y) (y0 : Y) (F : X → A → ℂ) (F0 : A → ℂ) (ch : A → ℂ) (_ : ∀ q, AEStronglyMeasurable (F q) lam) (_ : AEStronglyMeasurable ch lam) (_ : ∀ b, ‖ch b‖ = 1) (_ : ∀ a b, ch (a + b) = ch a * ch b) (_ : ∀ l : Λ, ch l = 1) (M : ℝ) (_ : ∀ b, Summable (fun q => ‖F q b‖) ∧ ∑' q, ‖F q b‖ ≤ M) (τ : Λ → X ≃ X) (_ : ∀ (l : Λ) q b, F q ((l : A) + b) = F (τ l q) b) (_ : ∀ (l : Λ) q, c (τ l q) = c q) (e : Λ → X) (_ : Function.Injective e) (_ : ∀ q, c q = y0 ↔ q ∈ Set.range e) (_ : ∀ (l : Λ) b, F (e l) b = F0 ((l : A) + b)) (_ : ∀ y, y ≠ y0 → ∃ ν, ch ν ≠ 1 ∧ ∀ q, c q = y → ∀ b, F q (ν + b) = F q b), Integrable F0 lam ∧ ∫ b in 𝓖, (∑' q, F q b) * ch b ∂lam = ∫ b, F0 b * ch b ∂lam := by
  first | exact @GlobalTheory.CompanionTheory.UnfoldAbs.unfold_abs | exact GlobalTheory.CompanionTheory.UnfoldAbs.unfold_abs | (intros; apply GlobalTheory.CompanionTheory.UnfoldAbs.unfold_abs <;> assumption)
