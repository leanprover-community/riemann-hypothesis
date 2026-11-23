module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmRep
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdditiveFamilyFunctionDeterminedConstituents
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

open scoped TensorProduct

theorem _root_.GlobalTheory.T.additive_family_function_determined_constituents : ∀ (α : Type) [Fintype α] [DecidableEq α] (Γ : α → Type) [∀ i, Group (Γ i)] [∀ i, TopologicalSpace (Γ i)] [∀ i, IsTopologicalGroup (Γ i)] (Φ : (∀ i, GlobalTheory.SmGL.SmRep (Γ i)) → ℕ∞), (∀ (A : ∀ i, GlobalTheory.SmGL.SmRep (Γ i)) (i : α), Subsingleton (A i).V → Φ A = 0) → (∀ (A : ∀ i, GlobalTheory.SmGL.SmRep (Γ i)) (i : α) (B B₁ B₂ : GlobalTheory.SmGL.SmRep (Γ i)) (ι : B₁.ρ.IntertwiningMap B.ρ) (p : B.ρ.IntertwiningMap B₂.ρ), Function.Injective ι → Function.Surjective p → (∀ u, p (ι u) = 0) → (∀ v, p v = 0 → ∃ u, ι u = v) → Φ (Function.update A i B) = Φ (Function.update A i B₁) + Φ (Function.update A i B₂)) → ∀ (A : ∀ i, GlobalTheory.SmGL.SmRep (Γ i)), (∀ i, GlobalTheory.SmGL.HasFiniteLength (A i).ρ) → ∀ T : Finset (∀ i, GlobalTheory.SmGL.IrrCl (Γ i)), (∀ t ∉ T, ∃ i, GlobalTheory.SmGL.jhMult (t i).rep.ρ (A i).ρ = 0) → Φ A = ∑ t ∈ T, (∏ i, GlobalTheory.SmGL.jhMult (t i).rep.ρ (A i).ρ) * Φ (fun i => GlobalTheory.SmGL.SmRep.ofIrr (t i).rep) := by
  first | exact @GlobalTheory.SmGL.additive_family_expand | exact GlobalTheory.SmGL.additive_family_expand | (intros; apply GlobalTheory.SmGL.additive_family_expand <;> assumption)
