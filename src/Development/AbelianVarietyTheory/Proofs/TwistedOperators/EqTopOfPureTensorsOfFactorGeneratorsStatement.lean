module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SimpleOver
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqTopOfPureTensorsOfFactorGenerators
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


theorem _root_.GlobalTheory.T.eq_top_of_pure_tensors_of_factor_generators : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {M₀ : Type} [AddCommGroup M₀] [Module ℂ M₀]
    {M : ι → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
    (Op₀ : Set (Module.End ℂ M₀)) (Op : ∀ i, Set (Module.End ℂ (M i)))
    (Rel₀ : Submodule ℂ M₀) (Rel : ∀ i, Submodule ℂ (M i)) (F₀ : Finset M₀) (F : ∀ i, Finset (M i)),
    (∀ N : Submodule ℂ M₀, Rel₀ ≤ N → GlobalTheory.TensHead.Stab Op₀ N → (↑F₀ : Set M₀) ⊆ ↑N → N = ⊤) →
    (∀ i, ∀ N : Submodule ℂ (M i), Rel i ≤ N → GlobalTheory.TensHead.Stab (Op i) N →
      (↑(F i) : Set (M i)) ⊆ ↑N → N = ⊤) →
    ∀ N : Submodule ℂ (M₀ ⊗[ℂ] (⨂[ℂ] i, M i)),
      (∀ x ∈ Rel₀, ∀ y, x ⊗ₜ[ℂ] y ∈ N) →
      (∀ i, ∀ x ∈ Rel i, ∀ (x₀ : M₀) (y : ∀ j, M j),
        x₀ ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (Function.update y i x) ∈ N) →
      GlobalTheory.TensHead.Stab (GlobalTheory.TensHead.tensOps Op₀ (GlobalTheory.TensHead.piOps Op)) N →
      (∀ x₀ ∈ F₀, ∀ y : ∀ i, M i, (∀ i, y i ∈ F i) → x₀ ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ y ∈ N) →
      N = ⊤ := by
  first | exact @GlobalTheory.TensHead.eq_top_of_pure_generators | exact GlobalTheory.TensHead.eq_top_of_pure_generators | (intros; apply GlobalTheory.TensHead.eq_top_of_pure_generators <;> assumption)
