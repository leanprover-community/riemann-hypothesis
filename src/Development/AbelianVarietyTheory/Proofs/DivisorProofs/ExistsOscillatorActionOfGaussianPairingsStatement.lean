module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousFourierGau
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOscillatorActionOfGaussianPairings
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

open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder

theorem _root_.GlobalTheory.T.exists_oscillatorAction_of_gaussianPairings : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] (J : V ≃ₗᵢ[ℝ] V) (ρ : V → B →L[ℂ] B), (∀ x, J (J x) = -x) → ∀ h : IsHeis (omJ J) ρ, ∀ (G : Type) [Group G] (k : G →* (V →L[ℝ] V)) (c : G → ℂ), (∀ g x y, omJ J (k g x) (k g y) = omJ J x y) → c 1 = 1 → (∀ g, star (c g) * c g * lam (k g) = 1) → (∀ g g', c g * c g' * mu J (k (g * g')) (k g) = c (g * g') * lam (k (g * g'))) → ∃ Ω : G → B → B, IsOsc ρ (fun g v => k g v) Ω ∧ (∀ (Y : Type) [TopologicalSpace Y] (γ : Y → G), Continuous (fun y => k (γ y)) → Continuous (fun y => c (γ y)) → ∀ f, Sm ρ f → Continuous fun y => Ω (γ y) f) ∧ ∀ a g, (∀ x, ‖k g x‖ = ‖x‖) → ∀ f, Sm ρ f → ∫ u, gau u • ρ (k a u) f = f → Ω (a * g * a⁻¹) f = c g • f := by
  first | exact @GlobalTheory.RealWeil.Osc.exists_isOsc | exact GlobalTheory.RealWeil.Osc.exists_isOsc | (intros; apply GlobalTheory.RealWeil.Osc.exists_isOsc <;> assumption)
