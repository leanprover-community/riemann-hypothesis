module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TrivAtOfCfEqOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSumLocalEulerFactorHeckeOperators
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

open scoped InnerProductSpace BigOperators

theorem _root_.GlobalTheory.T.hasSum_localEulerFactor_heckeOperators : ∀ (Γ : Type) [Group Γ] (K : Subgroup Γ) (c : Γ →* Γ) (H : Type) [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H] (a : Γ → ℂ) (B : Γ → (H →L[ℂ] H)) (S : ℝ), (∀ g, c (c g) = c g) → (∀ g k k', k ∈ K → k' ∈ K → a (k * g * k') = a g) → (∀ g k, k ∈ K → B (g * k) = B g) → (∀ g, ‖B g‖ ≤ 1) → (∀ C : Finset Γ, (∀ g ∈ C, c g = g ∧ g ∉ K) → (∀ g ∈ C, ∀ g' ∈ C, g⁻¹ * g' ∈ K → g = g') → ∑ g ∈ C, ‖a g‖ ≤ S) → (∀ α, c α = α → ∃ C, GlobalTheory.UpInj.DCRep c K α C) → (∀ α C, c α = α → GlobalTheory.UpInj.DCRep c K α C → ∀ γ, ∑ δ ∈ C, B (γ * δ) = B γ * ∑ δ ∈ C, B δ) → ∀ γ, HasSum (fun x : Γ ⧸ K.comap c => a (c (Quotient.out x)) • B (γ * c (Quotient.out x))) (B γ * ∑' x : Γ ⧸ K.comap c, a (c (Quotient.out x)) • B (c (Quotient.out x))) := by
  first | exact @GlobalTheory.UpInj.localSum_hasSum | exact GlobalTheory.UpInj.localSum_hasSum | (intros; apply GlobalTheory.UpInj.localSum_hasSum <;> assumption)
