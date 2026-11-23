module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsQuadOfPlane
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOscillatorActionUnitaryPolynomialBound
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory Complex Matrix GlobalTheory.RealWeil GlobalTheory.Mem.Lift
open scoped RealInnerProductSpace ContDiff Real ComplexOrder Topology

theorem _root_.GlobalTheory.T.hasDerivAt_oscillatorAction_unitaryPath_quadratic : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ), Hᴴ = H → H.det ≠ 0 → ∀ (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] (ρ : (ι → ℂ) → B →L[ℂ] B), IsHeis (fun x y => (star y ⬝ᵥ H *ᵥ x).im) ρ → ∀ (G : Type) [Group G] (m : G →* Matrix ι ι ℂ), (∀ g, (m g)ᴴ * H * m g = H) → ∃ Ω : G → B → B, IsOsc ρ (fun g v => m g *ᵥ v) Ω ∧ (∃ N : ℕ, ∀ f, Sm ρ f → ∃ C : ℝ, ∀ g, ‖Ω g f‖ ≤ C * (1 + ∑ i, ∑ j, ‖m g i j‖) ^ N) ∧ ∀ (γ : ℝ → G) (X : Matrix ι ι ℂ), γ 0 = 1 → (∀ i j, HasDerivAt (fun t => m (γ t) i j) (X i j) 0) → ∀ (κ : Type) [Fintype κ] (c : κ → ℂ) (p q : κ → ι → ℂ), IsQuadOf (fun x y => (star y ⬝ᵥ H *ᵥ x).im) (fun v => X *ᵥ v) c p q → ∃ lam : ℂ, ∀ f, Sm ρ f → HasDerivAt (fun t => Ω (γ t) f) (quad ρ c p q f + lam • f) 0 := by
  first | exact @GlobalTheory.Mem.Lift.OscBound.exists_osc_bound_deriv | exact GlobalTheory.Mem.Lift.OscBound.exists_osc_bound_deriv | (intros; apply GlobalTheory.Mem.Lift.OscBound.exists_osc_bound_deriv <;> assumption)
