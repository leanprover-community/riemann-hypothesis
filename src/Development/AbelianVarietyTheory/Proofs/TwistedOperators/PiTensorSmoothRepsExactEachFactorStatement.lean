module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmRep
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PiTensorSmoothRepsExactEachFactor
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

open scoped TensorProduct

theorem _root_.GlobalTheory.T.piTensor_smooth_reps_exact_each_factor : ∀ (α : Type) [Fintype α] [DecidableEq α] (Γ : α → Type) [∀ i, Group (Γ i)] [∀ i, TopologicalSpace (Γ i)] (A : ∀ i, GlobalTheory.SmGL.SmRep (Γ i)) (i : α) (B B₁ B₂ : GlobalTheory.SmGL.SmRep (Γ i)) (ι : B₁.ρ.IntertwiningMap B.ρ) (p : B.ρ.IntertwiningMap B₂.ρ), Function.Injective ι → Function.Surjective p → (∀ u, p (ι u) = 0) → (∀ v, p v = 0 → ∃ u, ι u = v) → ∃ (ι' : (GlobalTheory.SmGL.piTensor fun a => (Function.update A i B₁ a).ρ).IntertwiningMap (GlobalTheory.SmGL.piTensor fun a => (Function.update A i B a).ρ)) (p' : (GlobalTheory.SmGL.piTensor fun a => (Function.update A i B a).ρ).IntertwiningMap (GlobalTheory.SmGL.piTensor fun a => (Function.update A i B₂ a).ρ)), Function.Injective ι' ∧ Function.Surjective p' ∧ (∀ u, p' (ι' u) = 0) ∧ (∀ v, p' v = 0 → ∃ u, ι' u = v) := by
  first | exact @GlobalTheory.SmGL.piTensor_exact_position | exact GlobalTheory.SmGL.piTensor_exact_position | (intros; apply GlobalTheory.SmGL.piTensor_exact_position <;> assumption)
