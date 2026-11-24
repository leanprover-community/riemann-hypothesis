module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SimpleOver
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open scoped TensorProduct

namespace GlobalTheory.TensHead


open scoped TensorProduct in
theorem _root_.GlobalTheory.TensHead.stab_piOps_piKer {ι : Type} [DecidableEq ι] {M : ι → Type} [∀ i, AddCommGroup (M i)]
    [∀ i, Module ℂ (M i)]
    (Op : ∀ i, Set (Module.End ℂ (M i))) (K : ∀ i, Submodule ℂ (M i))
    (h : ∀ i, _root_.GlobalTheory.TensHead.Stab (Op i) (K i)) :
    _root_.GlobalTheory.TensHead.Stab (_root_.GlobalTheory.TensHead.piOps Op) (_root_.GlobalTheory.TensHead.piKer K) := by
  unfold _root_.GlobalTheory.TensHead.Stab at h ⊢
  rintro _ ⟨i, g, hg, rfl⟩ x hx
  unfold _root_.GlobalTheory.TensHead.piKer at hx ⊢
  have hle : Submodule.span ℂ {t | ∃ y : ∀ j, M j, (∃ j, y j ∈ K j) ∧ t = PiTensorProduct.tprod ℂ y}
      ≤ (Submodule.span ℂ {t | ∃ y : ∀ j, M j, (∃ j, y j ∈ K j) ∧ t = PiTensorProduct.tprod ℂ y}).comap
        (_root_.GlobalTheory.TensHead.piOp i g) := by
    rw [Submodule.span_le]
    rintro _ ⟨y, ⟨j, hj⟩, rfl⟩
    refine Submodule.subset_span ⟨fun k => Function.update (fun _ => LinearMap.id) i g k (y k), ⟨j, ?_⟩, ?_⟩
    · by_cases hji : j = i
      · subst hji
        simpa using h j g hg _ hj
      · simpa [Function.update_of_ne hji] using hj
    · simp [_root_.GlobalTheory.TensHead.piOp]
  exact hle hx

end GlobalTheory.TensHead
